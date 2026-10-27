module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Field
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefModBot
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedLemma11

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.RankThree.GF2n.Tim81.Sec2
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem s1b_alpha_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : Odd n) (hK : Nat.card F = 2 ^ n) {Y : Type} [Group Y] (σ : Y → Y) (τ Φ : Y → F)
    {α : F} (hα : α ≠ 0) (hτadd : ∀ y₁ y₂, τ (y₁ * y₂) = τ y₁ + τ y₂)
    (hΦadd : ∀ y₁ y₂, Φ (y₁ * y₂) = Φ y₁ + Φ y₂) (hΦsurj : Function.Surjective Φ)
    (hker : ∀ y, τ y = 0 ↔ Φ y = 0) (hτσ : ∀ y, τ (σ y) = α ^ 2 * τ y)
    (hΦσ : ∀ y, Φ (σ y) = α⁻¹ * Φ y) : α = 1 := by
  have hτ1 : τ 1 = 0 := by
    have h := hτadd 1 1
    rw [mul_one] at h
    linear_combination -h
  have hτinv : ∀ y, τ y⁻¹ = -τ y := by
    intro y
    have h := hτadd y y⁻¹
    rw [mul_inv_cancel, hτ1] at h
    linear_combination -h
  have hΦ1 : Φ 1 = 0 := by
    have h := hΦadd 1 1
    rw [mul_one] at h
    linear_combination -h
  have hΦinv : ∀ y, Φ y⁻¹ = -Φ y := by
    intro y
    have h := hΦadd y y⁻¹
    rw [mul_inv_cancel, hΦ1] at h
    linear_combination -h
  let s : F → Y := Function.surjInv hΦsurj
  have hs : ∀ u, Φ (s u) = u := Function.surjInv_eq hΦsurj
  have hkey : ∀ y, τ y = τ (s (Φ y)) := by
    intro y
    have h0 : Φ (y * (s (Φ y))⁻¹) = 0 := by
      rw [hΦadd, hΦinv, hs]
      exact add_neg_cancel _
    have h1 := (hker _).mpr h0
    rw [hτadd, hτinv] at h1
    linear_combination h1
  let f : F →+ F := AddMonoidHom.mk' (fun u => τ (s u)) (by
    intro u₁ u₂
    show τ (s (u₁ + u₂)) = τ (s u₁) + τ (s u₂)
    have h := hkey (s u₁ * s u₂)
    rw [hΦadd, hs, hs] at h
    rw [← h, hτadd])
  have hf : Function.Injective f := by
    intro u u' h
    have h' : τ (s u) = τ (s u') := h
    have h0 : τ (s u * (s u')⁻¹) = 0 := by
      rw [hτadd, hτinv, h']
      exact add_neg_cancel _
    have h1 := (hker _).mp h0
    rw [hΦadd, hΦinv, hs, hs] at h1
    linear_combination h1
  have hfun : ∀ u, f (α⁻¹ * u) = (α⁻¹ ^ 2)⁻¹ * f u := by
    intro u
    have h1 := hkey (σ (s u))
    rw [hΦσ, hs] at h1
    have h2 := hτσ (s u)
    show τ (s (α⁻¹ * u)) = (α⁻¹ ^ 2)⁻¹ * τ (s u)
    rw [← h1, h2, inv_pow, inv_inv]
  exact inv_eq_one.mp
    (eq_one_of_injective_map_mul_eq_inv_sq hn hK f hf (inv_ne_zero hα) hfun)

private theorem s1b_uElt_mulVec_zero {F : Type} [Field F] (t : F) (w : Fin 2 → F) :
    ((uElt t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w 0 = w 0 + t * w 1 := by
  simp [coe_uElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem s1b_uElt_mulVec_one {F : Type} [Field F] (t : F) (w : Fin 2 → F) :
    ((uElt t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w 1 = w 1 := by
  simp [coe_uElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem s1b_borel_entries {F : Type} [Field F] {M : SL(2, F)} (hM : M ∈ borelSubgroup F) :
    (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (M : Matrix (Fin 2) (Fin 2) F) 1 1 = ((M : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ := by
  obtain ⟨a, b, h⟩ := (mem_borelSubgroup_iff M).mp hM
  have h00 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F) := by rw [h]; simp
  have h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by rw [h]; simp
  have h11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 = ((a⁻¹ : Fˣ) : F) := by rw [h]; simp
  refine ⟨?_, h10, ?_⟩
  · rw [h00]
    exact a.ne_zero
  · rw [h11, h00]
    simp

private theorem s1b_borel_mulVec_one {F : Type} [Field F] {M : SL(2, F)}
    (hM : M ∈ borelSubgroup F) (w : Fin 2 → F) :
    ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) 1 =
      ((M : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ * w 1 := by
  obtain ⟨-, h10, h11⟩ := s1b_borel_entries hM
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, h11]

private theorem s1b_borel_eq_uElt {F : Type} [Field F] {M : SL(2, F)} (hM : M ∈ borelSubgroup F)
    (h1 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) :
    M = uElt ((M : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  obtain ⟨-, h10, h11⟩ := s1b_borel_entries hM
  rw [h1, inv_one] at h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uElt, h1, h10, h11]

private theorem s1b_conj_mem_borel {F : Type} [Field F] {A : Subgroup SL(2, F)} {x g : SL(2, F)}
    (hx : ∀ a, a ∈ A ↔ x⁻¹ * a * x ∈ upperRootGroup F)
    (hg : g ∈ Subgroup.normalizer (A : Set SL(2, F))) : x⁻¹ * g * x ∈ borelSubgroup F := by
  have h1 : ∀ u, u ∈ upperRootGroup F ↔ x * u * x⁻¹ ∈ A := by
    intro u
    rw [hx]
    have : x⁻¹ * (x * u * x⁻¹) * x = u := by group
    rw [this]
  rw [← normalizer_upperRootGroup, Subgroup.mem_normalizer_iff]
  intro u
  rw [h1 u, h1 ((x⁻¹ * g * x) * u * (x⁻¹ * g * x)⁻¹)]
  have : x * ((x⁻¹ * g * x) * u * (x⁻¹ * g * x)⁻¹) * x⁻¹ = g * (x * u * x⁻¹) * g⁻¹ := by group
  rw [this]
  exact Subgroup.mem_normalizer_iff.mp hg (x * u * x⁻¹)

private theorem s1b_fix_iff {F : Type} [Field F] {A : Subgroup SL(2, F)} {x : SL(2, F)}
    (hx : ∀ a, a ∈ A ↔ x⁻¹ * a * x ∈ upperRootGroup F) (w : Fin 2 → F) :
    (∀ a ∈ A, a • w = w) ↔ (x⁻¹ • w) 1 = 0 := by
  constructor
  · intro h
    have hA : x * uElt (1 : F) * x⁻¹ ∈ A := by
      rw [hx]
      have : x⁻¹ * (x * uElt (1 : F) * x⁻¹) * x = uElt 1 := by group
      rw [this]
      exact (mem_upperRootGroup_iff _).mpr ⟨1, rfl⟩
    have h1 := h _ hA
    have h2 : (uElt (1 : F)) • (x⁻¹ • w) = x⁻¹ • w := by
      calc (uElt (1 : F)) • (x⁻¹ • w) = (x⁻¹ * (x * uElt (1 : F) * x⁻¹)) • w := by
            rw [smul_smul]
            congr 1
            group
        _ = x⁻¹ • ((x * uElt (1 : F) * x⁻¹) • w) := by rw [mul_smul]
        _ = x⁻¹ • w := by rw [h1]
    have h3 := congrFun h2 0
    rw [smul_eq_mulVec', s1b_uElt_mulVec_zero] at h3
    have h4 : (1 : F) * (x⁻¹ • w) 1 = 0 := by
      have := h3
      linear_combination this
    simpa using h4
  · intro h a ha
    obtain ⟨t, ht⟩ := (mem_upperRootGroup_iff _).mp ((hx a).mp ha)
    have hat : a = x * uElt t * x⁻¹ := by
      calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
        _ = x * uElt t * x⁻¹ := by rw [ht]
    have hu : (uElt t) • (x⁻¹ • w) = x⁻¹ • w := by
      rw [smul_eq_mulVec']
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, s1b_uElt_mulVec_zero, h]
        ring
      · exact s1b_uElt_mulVec_one t _
    rw [hat]
    calc (x * uElt t * x⁻¹) • w = x • ((uElt t) • (x⁻¹ • w)) := by
          rw [mul_smul, mul_smul]
      _ = x • (x⁻¹ • w) := by rw [hu]
      _ = w := smul_inv_smul _ _

private theorem s1b_eq_one_of_mul_self {M : Type} [Group M] {g : M} (hg : g * g = 1)
    (hodd : Odd (orderOf g)) : g = 1 := by
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg)
  have h1 : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

private theorem s1b_eq_one_of_mem_pCoreOf {H : Subgroup G} {b : G} (hb : b ∈ pCoreOf 2 H)
    (hodd : Odd (orderOf b)) : b = 1 := by
  have hp2 : IsPGroup 2 (pCoreOf 2 H) :=
    IsPGroup.map (pCore_isPGroup (G := ↥H) (p := 2)) (Subgroup.subtype H)
  obtain ⟨k, hk⟩ := hp2.exists_orderOf_eq_pow ⟨b, hb⟩
  have hk' : orderOf b = 2 ^ k := by
    simpa using hk
  have hoddk : Odd (2 ^ k) := hk' ▸ hodd
  have hk0 : 2 ^ k = 1 := by
    rcases k with _ | m
    · rfl
    · exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero m)) hoddk.not_two_dvd_nat
  exact orderOf_eq_one_iff.mp (hk'.trans hk0)


private theorem s1b_core {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : Odd n)
    (hK : Nat.card F = 2 ^ n) {Y : Type} [Group Y] (σ : Y → Y)
    (E : Y → SL(2, F)) (Ψ : Y → Fin 2 → F) (x g : SL(2, F))
    (hEmul : ∀ y₁ y₂, E (y₁ * y₂) = E y₁ * E y₂)
    (hEU : ∀ y, x⁻¹ * E y * x ∈ upperRootGroup F)
    (hB : x⁻¹ * g * x ∈ borelSubgroup F)
    (hEσ : ∀ y, E (σ y) = g * E y * g⁻¹)
    (hΨadd : ∀ y₁ y₂, Ψ (y₁ * y₂) = Ψ y₁ + Ψ y₂)
    (hΨsurj : Function.Surjective Ψ)
    (hΨσ : ∀ y, Ψ (σ y) = g • Ψ y)
    (hker : ∀ y, E y = 1 ↔ (x⁻¹ • Ψ y) 1 = 0) :
    g * g = 1 := by
  obtain ⟨M, hM⟩ : ∃ M : SL(2, F), M = x⁻¹ * g * x := ⟨_, rfl⟩
  rw [← hM] at hB
  obtain ⟨hα0, -, -⟩ := s1b_borel_entries hB
  obtain ⟨α, hα⟩ : ∃ α : F, α = (M : Matrix (Fin 2) (Fin 2) F) 0 0 := ⟨_, rfl⟩
  rw [← hα] at hα0
  choose τ hτu using fun y => (mem_upperRootGroup_iff _).mp (hEU y)
  have hτadd : ∀ y₁ y₂, τ (y₁ * y₂) = τ y₁ + τ y₂ := by
    intro y₁ y₂
    apply uElt_injective
    rw [uElt_add, ← hτu, ← hτu, ← hτu, hEmul]
    group
  have hτσ : ∀ y, τ (σ y) = α ^ 2 * τ y := by
    intro y
    apply uElt_injective
    rw [← hτu, hEσ]
    have h1 : x⁻¹ * (g * E y * g⁻¹) * x = M * (x⁻¹ * E y * x) * M⁻¹ := by rw [hM]; group
    rw [h1, hτu y, borel_mul_uElt M hB, mul_inv_cancel_right, hα]
  have hτker : ∀ y, τ y = 0 ↔ E y = 1 := by
    intro y
    constructor
    · intro h0
      have h1 : x⁻¹ * E y * x = 1 := by rw [hτu, h0, uElt_zero]
      calc E y = x * (x⁻¹ * E y * x) * x⁻¹ := by group
        _ = x * 1 * x⁻¹ := by rw [h1]
        _ = 1 := by group
    · intro h1
      apply uElt_injective
      rw [← hτu, h1, uElt_zero]
      group
  let Φ : Y → F := fun y => (x⁻¹ • Ψ y) 1
  have hΦadd : ∀ y₁ y₂, Φ (y₁ * y₂) = Φ y₁ + Φ y₂ := by
    intro y₁ y₂
    show (x⁻¹ • Ψ (y₁ * y₂)) 1 = (x⁻¹ • Ψ y₁) 1 + (x⁻¹ • Ψ y₂) 1
    rw [hΨadd, smul_eq_mulVec', smul_eq_mulVec', smul_eq_mulVec', Matrix.mulVec_add]
    rfl
  have hΦsurj : Function.Surjective Φ := by
    intro u
    obtain ⟨y, hy⟩ := hΨsurj (x • (Pi.single 1 u : Fin 2 → F))
    refine ⟨y, ?_⟩
    show (x⁻¹ • Ψ y) 1 = u
    rw [hy, inv_smul_smul]
    simp
  have hΦσ : ∀ y, Φ (σ y) = α⁻¹ * Φ y := by
    intro y
    show (x⁻¹ • Ψ (σ y)) 1 = α⁻¹ * (x⁻¹ • Ψ y) 1
    have h1 : x⁻¹ • Ψ (σ y) = M • (x⁻¹ • Ψ y) := by
      rw [hΨσ, smul_smul, smul_smul, hM]
      congr 1
      group
    rw [h1, smul_eq_mulVec', s1b_borel_mulVec_one hB, hα]
  have hα1 : α = 1 :=
    s1b_alpha_eq_one hn hK σ τ Φ hα0 hτadd hΦadd hΦsurj (fun y => (hτker y).trans (hker y))
      hτσ hΦσ
  obtain ⟨β, hβ⟩ : ∃ β : F, M = uElt β :=
    ⟨_, s1b_borel_eq_uElt hB (hα.symm.trans hα1)⟩
  have hMM : M * M = 1 := by
    rw [hβ, ← uElt_add, CharTwo.add_self_eq_zero, uElt_zero]
  calc g * g = x * (x⁻¹ * g * x * (x⁻¹ * g * x)) * x⁻¹ := by group
    _ = x * (M * M) * x⁻¹ := by rw [hM]
    _ = 1 := by rw [hMM]; group

theorem l2_chiefStep_eq_one_of_conj_equivariant {H Y S : Subgroup G} {n : ℕ}
    (hn : Odd n)
    (hS : IsSylowTwoOf S H) (hYH : Y ≤ H) (hV : IsElemAbelian 2 Y)
    (hstep : IsChiefStep H Y ⊥ Y) :
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
    ∀ (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 n))
      (ρ : Representation (ZMod 2) SL(2, GaloisField 2 n)
        (Additive (Ch3z.chiefMod ⊥ Y)))
      (φ : Additive (Ch3z.chiefMod ⊥ Y) ≃+ (Fin 2 → GaloisField 2 n)),
      (∀ (h : ↥H) (w : Ch3z.chiefMod ⊥ Y),
        ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
          Additive.ofMul (l2ChiefSectionAction hstep hE h w)) →
      (∀ g w, φ (ρ g w) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (φ w)) →
      ∀ b c : G, b ∈ H → b ∈ Subgroup.normalizer (S : Set G) → Odd (orderOf b) →
        (∀ y ∈ Y, c * y * c⁻¹ ∈ S) →
        (∀ y ∈ Y, c * y * c⁻¹ ∈ pCoreOf 2 H ↔ y ∈ Subgroup.centralizer (S : Set G)) →
        (∀ y ∈ Y, b * (c * y * c⁻¹) * b⁻¹ * (c * (b * y * b⁻¹) * c⁻¹)⁻¹ ∈ pCoreOf 2 H) →
        b = 1 := by
  classical
  have hn0 : n ≠ 0 := hn.pos.ne'
  let F := GaloisField 2 n
  haveI : Fintype F := Fintype.ofFinite _
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n hn0
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
  letI : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
  intro hE₀ e ρ φ hcompat hφnat b c hbH hbN hodd hcS hker hequiv
  have hρeq : ρ = l2ChiefSectionRep hstep hYH hE e := by
    refine MonoidHom.ext fun g' => LinearMap.ext fun w => ?_
    obtain ⟨h, rfl⟩ := e.surjective g'
    obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) h
    have hw : Additive.ofMul w.toMul = w := rfl
    rw [← hw, QuotientGroup.mk'_apply, hcompat h' w.toMul, l2ChiefSectionRep_apply_mk]
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  let q : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  let ψ : ↥H →* SL(2, F) := e.toMonoidHom.comp q
  let A : Subgroup SL(2, F) := (S.subgroupOf H).map ψ
  have hmap : ((S.subgroupOf H).map q).map e.toMonoidHom = A := by
    rw [Subgroup.map_map]
  let PH : Sylow 2 ↥H := (hSp.comap_subtype (K := H)).toSylow hSidx
  have hPHcoe : (PH : Subgroup ↥H) = S.subgroupOf H := IsPGroup.toSylow_coe _ _
  let Pq : Sylow 2 (oTwoQuot ↥H) :=
    PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hPqcoe : (Pq : Subgroup (oTwoQuot ↥H)) = (S.subgroupOf H).map q := by
    change ((PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _) :
      Sylow 2 (oTwoQuot ↥H)) : Subgroup (oTwoQuot ↥H)) = (S.subgroupOf H).map q
    rw [Sylow.coe_mapSurjective, hPHcoe]
  let PA : Sylow 2 (SL(2, F)) :=
    Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective)
  have hPAcoe : (PA : Subgroup (SL(2, F))) = A := by
    change ((Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective) :
      Sylow 2 (SL(2, F))) : Subgroup (SL(2, F))) = A
    rw [Sylow.coe_mapSurjective, hPqcoe, hmap]
  obtain ⟨x, hx⟩ := sylow_conj_description (p := 2) PA
  have hx' : ∀ a, a ∈ A ↔ x⁻¹ * a * x ∈ upperRootGroup F := by
    intro a
    rw [← hPAcoe]
    exact hx a
  let bH : ↥H := ⟨b, hbH⟩
  let g : SL(2, F) := ψ bH
  have hbHnorm : bH ∈ Subgroup.normalizer ((S.subgroupOf H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp hbN (x : G)).mp hx
    · intro hx
      have hx' : (bH * x * bH⁻¹ : ↥H) ∈ S.subgroupOf H := hx
      rw [Subgroup.mem_subgroupOf] at hx' ⊢
      have h2 : (bH : G)⁻¹ * ((bH : G) * (x : G) * (bH : G)⁻¹) * (bH : G) ∈ S := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN)
          (((bH * x * bH⁻¹ : ↥H) : G))).mp hx'
        simpa using h
      have h3 : (bH : G)⁻¹ * ((bH : G) * (x : G) * (bH : G)⁻¹) * (bH : G) =
          (x : G) := by group
      rwa [h3] at h2
  have hgA : g ∈ Subgroup.normalizer (A : Set (SL(2, F))) := by
    have hle := Subgroup.le_normalizer_map (f := ψ) (H := S.subgroupOf H)
    have hmem : ψ bH ∈ (Subgroup.normalizer ((S.subgroupOf H) : Set ↥H)).map ψ :=
      Subgroup.mem_map_of_mem ψ hbHnorm
    exact hle hmem
  have hB : x⁻¹ * g * x ∈ borelSubgroup F := s1b_conj_mem_borel hx' hgA
  have hψker : ∀ h : ↥H, ψ h = 1 ↔ h ∈ CFSG.Open.pCore 2 ↥H := by
    intro h
    have h1 : ψ h = e (QuotientGroup.mk h) := rfl
    rw [h1, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff h
  have hpc : ∀ h : ↥H, (h : G) ∈ pCoreOf 2 H ↔ h ∈ CFSG.Open.pCore 2 ↥H := fun h =>
    Subgroup.mem_map_iff_mem H.subtype_injective
  let cyH : ↥Y → ↥H := fun y => ⟨c * (y : G) * c⁻¹, hSH (hcS y y.2)⟩
  let E : ↥Y → SL(2, F) := fun y => ψ (cyH y)
  have hσmem : ∀ y : ↥Y, b * (y : G) * b⁻¹ ∈ Y := fun y =>
    (Subgroup.mem_normalizer_iff.mp ((D14.le_normalizer_of_isNormalIn hstep.1) hbH) (y : G)).mp y.2
  let σ : ↥Y → ↥Y := fun y => ⟨b * (y : G) * b⁻¹, hσmem y⟩
  let Ψ : ↥Y → (Fin 2 → F) := fun y => φ (Additive.ofMul (chiefModBotMulEquiv Y y))
  have hEmul : ∀ y₁ y₂ : ↥Y, E (y₁ * y₂) = E y₁ * E y₂ := by
    intro y₁ y₂
    have h1 : cyH (y₁ * y₂) = cyH y₁ * cyH y₂ := by
      apply Subtype.ext
      show c * ((y₁ : G) * (y₂ : G)) * c⁻¹ = c * (y₁ : G) * c⁻¹ * (c * (y₂ : G) * c⁻¹)
      group
    show ψ (cyH (y₁ * y₂)) = ψ (cyH y₁) * ψ (cyH y₂)
    rw [h1, map_mul]
  have hEU : ∀ y : ↥Y, x⁻¹ * E y * x ∈ upperRootGroup F := fun y =>
    (hx' _).mp (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr (hcS y y.2)))
  have hEσ : ∀ y : ↥Y, E (σ y) = g * E y * g⁻¹ := by
    intro y
    have hz := (hpc (bH * cyH y * bH⁻¹ * (cyH (σ y))⁻¹)).mp (hequiv y y.2)
    have h1 := (hψker _).mpr hz
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_one.mp h1).symm
  have hΨadd : ∀ y₁ y₂ : ↥Y, Ψ (y₁ * y₂) = Ψ y₁ + Ψ y₂ := by
    intro y₁ y₂
    show φ (Additive.ofMul (chiefModBotMulEquiv Y (y₁ * y₂))) =
      φ (Additive.ofMul (chiefModBotMulEquiv Y y₁)) + φ (Additive.ofMul (chiefModBotMulEquiv Y y₂))
    rw [map_mul, ofMul_mul, map_add]
  have hΨsurj : Function.Surjective Ψ := by
    intro u
    refine ⟨(chiefModBotMulEquiv Y).symm (Additive.toMul (φ.symm u)), ?_⟩
    show φ (Additive.ofMul (chiefModBotMulEquiv Y
      ((chiefModBotMulEquiv Y).symm (Additive.toMul (φ.symm u))))) = u
    simp
  have hΨσ : ∀ y : ↥Y, Ψ (σ y) = g • Ψ y := by
    intro y
    have h1 : chiefModBotMulEquiv Y (σ y) =
        l2ChiefSectionAction hstep hE bH (chiefModBotMulEquiv Y y) :=
      (chiefModBotMulEquiv_conj hstep hYH hE bH y).symm
    show φ (Additive.ofMul (chiefModBotMulEquiv Y (σ y))) =
      g • φ (Additive.ofMul (chiefModBotMulEquiv Y y))
    rw [h1, ← hcompat bH, hφnat]
    rfl
  have hfix : ∀ y : ↥Y,
      ((y : G) ∈ Subgroup.centralizer (S : Set G) ↔ (x⁻¹ • Ψ y) 1 = 0) := by
    intro y
    have h1 : (y : G) ∈ Subgroup.centralizer (S : Set G) ↔
        Additive.ofMul (chiefModBotMulEquiv Y y) ∈ CFSG.RankThree.FFModules.fixSub ρ A := by
      have h := mem_fixSub_chiefMod_bot_iff hstep hYH hE e (S.subgroupOf H) y
      rw [Subgroup.map_subgroupOf_eq_of_le hSH] at h
      rw [hmap, ← hρeq] at h
      exact h.symm
    rw [h1, CFSG.RankThree.FFModules.mem_fixSub, ← s1b_fix_iff hx' (Ψ y)]
    constructor
    · intro h a ha
      have h2 := h a ha
      show (a : Matrix (Fin 2) (Fin 2) F).mulVec (Ψ y) = Ψ y
      rw [← hφnat, h2]
    · intro h a ha
      apply φ.injective
      rw [hφnat]
      exact h a ha
  have hker' : ∀ y : ↥Y, E y = 1 ↔ (x⁻¹ • Ψ y) 1 = 0 := fun y =>
    ((hψker (cyH y)).trans (hpc (cyH y)).symm).trans ((hker (y : G) y.2).trans (hfix y))
  have hgg : g * g = 1 :=
    s1b_core hn hFcard σ E Ψ x g hEmul hEU hB hEσ hΨadd hΨsurj hΨσ hker'
  have hoddg : Odd (orderOf g) := by
    have hdvd : orderOf g ∣ orderOf b := by
      have h := orderOf_map_dvd ψ bH
      have h1 : orderOf (ψ bH) = orderOf g := rfl
      rw [h1] at h
      have h2 : orderOf bH = orderOf b := by
        simpa [bH] using (Subgroup.orderOf_coe bH).symm
      rwa [h2] at h
    exact Odd.of_dvd_nat hodd hdvd
  have hg1 : g = 1 := s1b_eq_one_of_mul_self hgg hoddg
  exact s1b_eq_one_of_mem_pCoreOf ((hpc bH).mpr ((hψker bH).mp hg1)) hodd

end CFSG.Quasithin.Stroth

end
