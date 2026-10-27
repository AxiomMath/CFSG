module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.Quasithin.H13.KG12617Lie

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique Equiv
open scoped commutatorElement

theorem card_mulAut_alt6 :
    720 ∣ Nat.card (MulAut ↥(alternatingGroup (Fin 6))) ∧
      Nat.card (MulAut ↥(alternatingGroup (Fin 6))) ≤ 1440 := by
  refine ⟨?_, ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le⟩
  have h := Subgroup.card_dvd_of_injective _
    (CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num))
  rw [Nat.card_perm, Nat.card_fin] at h
  exact h

theorem card_le_of_isPGroup_mulAut {H : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))}
    (hH : IsPGroup 2 ↥H) : Nat.card ↥H ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut ↥(alternatingGroup (Fin 6))) :=
    Finite.of_injective (fun f : MulAut ↥(alternatingGroup (Fin 6)) => (f : _ → _))
      DFunLike.coe_injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hH
  obtain ⟨⟨m, hm⟩, hle⟩ := card_mulAut_alt6
  have hdvd := Subgroup.card_subgroup_dvd_card H
  have hpos : 0 < Nat.card (MulAut ↥(alternatingGroup (Fin 6))) := Nat.card_pos
  rw [hk, hm] at hdvd
  rw [hm] at hle hpos
  rw [hk]
  have hm12 : m = 1 ∨ m = 2 := by omega
  have h1440 : 2 ^ k ∣ 2 ^ 5 * 45 := by
    rcases hm12 with rfl | rfl
    · exact hdvd.trans ⟨2, by norm_num⟩
    · exact (by norm_num : (720 * 2 : ℕ) = 2 ^ 5 * 45) ▸ hdvd
  have h5 : 2 ^ k ∣ 2 ^ 5 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 45)).dvd_of_dvd_mul_right h1440
  exact (Nat.le_of_dvd (by norm_num) h5).trans (by norm_num)

section Action

variable {Γ : Type*} [Group Γ] {B : Subgroup Γ} {Q : Type*} [Group Q]

noncomputable def quotAut (φ : ↥B →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker = Open.pCore 2 ↥B) (σ : MulAut ↥B) : MulAut Q :=
  (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    ((QuotientGroup.congr φ.ker φ.ker σ (by rw [hker]; exact map_pCore_mulEquiv 2 σ)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))

theorem quotAut_apply (φ : ↥B →* Q) (hφ : Function.Surjective φ) (hker : φ.ker = Open.pCore 2 ↥B)
    (σ : MulAut ↥B) (b : ↥B) : quotAut φ hφ hker σ (φ b) = φ (σ b) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ b) = (b : ↥B ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [quotAut, MulEquiv.trans_apply, h1]
  rfl

noncomputable def quotAutHom (φ : ↥B →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker = Open.pCore 2 ↥B) : MulAut ↥B →* MulAut Q where
  toFun := quotAut φ hφ hker
  map_one' := by
    ext q
    obtain ⟨b, rfl⟩ := hφ q
    rw [quotAut_apply]
    rfl
  map_mul' σ τ := by
    ext q
    obtain ⟨b, rfl⟩ := hφ q
    rw [MulAut.mul_apply, quotAut_apply, MulAut.mul_apply, quotAut_apply, quotAut_apply]

noncomputable def quotAct (φ : ↥B →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker = Open.pCore 2 ↥B) : ↥(Subgroup.normalizer (B : Set Γ)) →* MulAut Q :=
  (quotAutHom φ hφ hker).comp B.normalizerMonoidHom

theorem quotAct_apply (φ : ↥B →* Q) (hφ : Function.Surjective φ) (hker : φ.ker = Open.pCore 2 ↥B)
    (n : ↥(Subgroup.normalizer (B : Set Γ))) (b : ↥B) :
    quotAct φ hφ hker n (φ b) = φ (B.normalizerMonoidHom n b) :=
  quotAut_apply φ hφ hker _ b

theorem mem_centralizerSection_of_quotAct_eq_one (φ : ↥B →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker = Open.pCore 2 ↥B) {M : Subgroup Γ} {n : ↥(Subgroup.normalizer (B : Set Γ))}
    (hnM : (n : Γ) ∈ M) (h1 : quotAct φ hφ hker n = 1) :
    (n : Γ) ∈ centralizerSection M B (pCoreOf 2 B) := by
  refine ⟨hnM, n.2, normalizer_le_normalizer_pCoreOf 2 B n.2, fun x hx => ?_⟩
  set c : ↥B := B.normalizerMonoidHom n ⟨x⁻¹, B.inv_mem hx⟩ with hc
  have hcΓ : (c : Γ) = n * x⁻¹ * (n : Γ)⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hφc : φ c = φ ⟨x⁻¹, B.inv_mem hx⟩ := by
    have h2 := congrArg (fun f : MulAut Q => f (φ ⟨x⁻¹, B.inv_mem hx⟩)) h1
    simp only [quotAct_apply, MulAut.one_apply] at h2
    exact h2
  have hmem : (⟨x, hx⟩ : ↥B) * c ∈ Open.pCore 2 ↥B := by
    rw [← hker, MonoidHom.mem_ker, map_mul, hφc, ← map_mul]
    convert map_one φ
    exact Subtype.ext (by simp)
  refine ⟨_, hmem, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, hcΓ]
  group

end Action

section Normalized

variable {Γ : Type*} [Group Γ]

theorem conj_mem_sup {O C : Subgroup Γ} (hCO : C ≤ Subgroup.normalizer (O : Set Γ)) {b : Γ}
    (hbO : b ∈ Subgroup.normalizer (O : Set Γ)) (hbC : ∀ c ∈ C, b * c * b⁻¹ * c⁻¹ ∈ O) {w : Γ}
    (hw : w ∈ O ⊔ C) : b * w * b⁻¹ ∈ O ⊔ C := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left O C hCO] at hw ⊢
  obtain ⟨o, ho, c, hc, rfl⟩ := hw
  refine ⟨b * o * b⁻¹ * (b * c * b⁻¹ * c⁻¹),
    O.mul_mem ((Subgroup.mem_normalizer_iff.mp hbO o).mp ho) (hbC c hc), c, hc, by group⟩

theorem exists_pGroup_normalized [Finite Γ] {B P : Subgroup Γ}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) (hP : IsPGroup 2 ↥P)
    (hPN : P ≤ Subgroup.normalizer (B : Set Γ)) (hcard : 2 ^ 6 ≤ Nat.card ↥P) :
    ∃ W : Subgroup Γ, W ≠ ⊥ ∧ IsPGroup 2 ↥W ∧ W ≤ B ⊔ P ∧
      B ≤ Subgroup.normalizer (W : Set Γ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := hBiso
  set ρ : ↥P →* MulAut ↥(alternatingGroup (Fin 6)) :=
    (quotAct φ hφ hker).comp (Subgroup.inclusion hPN) with hρ
  have hr2 : IsPGroup 2 ↥ρ.range := hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hr := card_le_of_isPGroup_mulAut hr2
  have hPc : Nat.card ↥P = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := by
    rw [ρ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hk : 2 ≤ Nat.card ↥ρ.ker := by
    by_contra h
    have h1 : Nat.card ↥ρ.ker ≤ 1 := by omega
    have h2 : Nat.card ↥P ≤ 32 := by nlinarith [Nat.zero_le (Nat.card ↥ρ.range)]
    omega
  obtain ⟨p, hp, hp1⟩ : ∃ p ∈ ρ.ker, p ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : ρ.ker = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [hbot, Subgroup.card_bot] at hk
    omega
  set O := pCoreOf 2 B with hO
  set C := centralizerSection P B O with hC
  have hpC : (p : Γ) ∈ C :=
    mem_centralizerSection_of_quotAct_eq_one φ hφ hker (n := Subgroup.inclusion hPN p) p.2 hp
  have hCO : C ≤ Subgroup.normalizer (O : Set Γ) := centralizerSection_le_normalizer_right _ _ _
  have hBO : B ≤ Subgroup.normalizer (O : Set Γ) := le_normalizer_pCoreOf 2 B
  refine ⟨O ⊔ C, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have : (p : Γ) ∈ (O ⊔ C) := Subgroup.mem_sup_right hpC
    rw [hbot, Subgroup.mem_bot] at this
    exact hp1 (Subtype.ext this)
  · exact IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 B)
      (hP.to_le (centralizerSection_le_left _ _ _)) hCO
  · exact sup_le ((pCoreOf_le 2 B).trans le_sup_left)
      ((centralizerSection_le_left _ _ _).trans le_sup_right)
  · intro b hb
    have hcomm : ∀ g ∈ B, ∀ c ∈ C, g * c * g⁻¹ * c⁻¹ ∈ O := fun g hg c hc => hc.2.2.2 g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact conj_mem_sup hCO (hBO hb) (hcomm b hb)
    · intro hw
      have h := conj_mem_sup hCO (hBO (B.inv_mem hb)) (hcomm _ (B.inv_mem hb)) hw
      rwa [inv_inv, show b⁻¹ * (b * w * b⁻¹) * b = w by group] at h

end Normalized

@[expose] def d8a : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

@[expose] def d8b : Perm (Fin 6) := swap 0 2 * swap 4 5

@[expose] def d8List : List (Perm (Fin 6)) :=
  [1, d8a, d8a * d8a, d8a * d8a * d8a, d8b, d8a * d8b, d8a * d8a * d8b, d8a * d8a * d8a * d8b]

theorem d8List_mul : ∀ x ∈ d8List, ∀ y ∈ d8List, x * y ∈ d8List := by decide +kernel

theorem d8List_inv : ∀ x ∈ d8List, x⁻¹ ∈ d8List := by decide +kernel

theorem d8List_pow : ∀ x ∈ d8List, x ^ 4 = 1 := by decide +kernel

theorem d8List_sign : ∀ x ∈ d8List, Perm.sign x = 1 := by decide +kernel

@[expose] def d8 : Subgroup ↥(alternatingGroup (Fin 6)) where
  carrier := {x | (x : Perm (Fin 6)) ∈ d8List}
  mul_mem' hx hy := d8List_mul _ hx _ hy
  one_mem' := by
    show (1 : Perm (Fin 6)) ∈ d8List
    decide +kernel
  inv_mem' hx := d8List_inv _ hx

theorem d8_isPGroup : IsPGroup 2 ↥d8 := fun x =>
  ⟨2, Subtype.ext (Subtype.ext (d8List_pow _ x.2))⟩

@[expose] def d8aA : ↥(alternatingGroup (Fin 6)) :=
  ⟨d8a, Perm.mem_alternatingGroup.2 (d8List_sign _ (by decide +kernel))⟩

@[expose] def d8bA : ↥(alternatingGroup (Fin 6)) :=
  ⟨d8b, Perm.mem_alternatingGroup.2 (d8List_sign _ (by decide +kernel))⟩

theorem d8aA_mem : d8aA ∈ d8 := by
  show d8a ∈ d8List
  decide +kernel

theorem d8bA_mem : d8bA ∈ d8 := by
  show d8b ∈ d8List
  decide +kernel

theorem d8a_comm : d8a * d8b * d8a⁻¹ * d8b⁻¹ ≠ 1 := by decide +kernel

theorem d8aA_comm : ⁅d8aA, d8bA⁆ ≠ 1 := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [commutatorElement_def] at h1
  exact d8a_comm h1

theorem false_of_commutator_mem {Γ : Type*} [Group Γ] [Finite Γ] {B Q : Subgroup Γ}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) (hQ : IsPGroup 2 ↥Q)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set Γ))
    (hcomm : ∀ D : Subgroup Γ, D ≤ B → IsPGroup 2 ↥D → ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ Q) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := hBiso
  obtain ⟨x, hx⟩ := hφ d8aA
  obtain ⟨y, hy⟩ := hφ d8bA
  set D := (d8.comap φ).map B.subtype with hD
  have hD2 : IsPGroup 2 ↥D :=
    (d8_isPGroup.comap_of_ker_isPGroup φ (by rw [hker]; exact CFSG.pCore_isPGroup (p := 2))).map _
  have hxD : (x : Γ) ∈ D := ⟨x, by show φ x ∈ d8; rw [hx]; exact d8aA_mem, rfl⟩
  have hyD : (y : Γ) ∈ D := ⟨y, by show φ y ∈ d8; rw [hy]; exact d8bA_mem, rfl⟩
  have hxy := hcomm D (Subgroup.map_subtype_le _) hD2 _ hxD _ hyD
  have hBQn : B ≤ Subgroup.normalizer ((B ⊓ Q : Subgroup Γ) : Set Γ) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf,
      ← Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hb) g,
      ← Subgroup.mem_normalizer_iff.mp (hBQ hb) g]
  have hle := le_pCoreOf_of_le_normalizer 2 inf_le_left hBQn (hQ.to_le inf_le_right)
  have hmem : ⁅(x : Γ), (y : Γ)⁆ ∈ pCoreOf 2 B :=
    hle ⟨B.mul_mem (B.mul_mem (B.mul_mem x.2 y.2) (B.inv_mem x.2)) (B.inv_mem y.2), hxy⟩
  obtain ⟨z, hz, hzxy⟩ := hmem
  have hz' : z = ⁅x, y⁆ := Subtype.ext (by simpa [commutatorElement_def] using hzxy)
  have hk : ⁅x, y⁆ ∈ φ.ker := by
    rw [hker, ← hz']
    exact hz
  rw [MonoidHom.mem_ker, map_commutatorElement, hx, hy] at hk
  exact d8aA_comm hk

theorem two_pow_le_card {Γ : Type*} [Group Γ] [Finite Γ] {Y K T T₀ : Subgroup Γ} (hKY : K ≤ Y)
    (hYK : Y ≤ Subgroup.normalizer (K : Set Γ)) (hT : IsSylowTwoOf T Y) (hT₀T : T₀ ≤ T)
    (hT₀4 : T₀.relIndex T ≤ 4) {m : ℕ} (hK : 2 ^ m ∣ Nat.card ↥K) :
    IsPGroup 2 ↥(T₀ ⊓ K) ∧ 2 ^ m ≤ 4 * Nat.card ↥(T₀ ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hT.2.1.to_le (inf_le_left.trans hT₀T), ?_⟩
  have hKn : (K.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYK
  have hTK := RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hKY hKn.isSubnormal
  have hc := ((T ⊓ K).subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv] at hc
  have hodd : Odd ((T ⊓ K).subgroupOf K).index := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hTK.2.2)
  have hdvd : 2 ^ m ∣ Nat.card ↥(T ⊓ K) :=
    (Nat.coprime_two_left.2 hodd).pow_left m |>.dvd_of_dvd_mul_right (hc ▸ hK)
  have hTK0 : 0 < Nat.card ↥(T ⊓ K) := Nat.card_pos
  have hle1 : 2 ^ m ≤ Nat.card ↥(T ⊓ K) := Nat.le_of_dvd hTK0 hdvd
  have hne : T₀.relIndex T ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card T₀ T
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne h1
  have hidx : T₀.relIndex (T ⊓ K) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left hne).trans hT₀4
  have hc2 := Subgroup.relIndex_mul_card T₀ (T ⊓ K)
  have heq : T₀ ⊓ (T ⊓ K) = T₀ ⊓ K := by
    rw [← inf_assoc, inf_eq_left.2 hT₀T]
  rw [heq] at hc2
  nlinarith [Nat.zero_le (Nat.card ↥(T₀ ⊓ K))]

end CFSG.Quasithin.H13.KG12617Lie
