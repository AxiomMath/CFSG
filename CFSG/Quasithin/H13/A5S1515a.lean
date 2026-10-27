module

public import CFSG.Quasithin.H13.A5Inputs2
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.H13.A5S132
public import CFSG.Quasithin.H13.A5S135
public import CFSG.Quasithin.H13.A5S1514

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped Pointwise

theorem perm3_inv_conj : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 → σ ≠ 1 →
    (σ * (finRotate 3 * σ * (finRotate 3)⁻¹)) ^ 2 ≠ 1 ∧
      (σ * (finRotate 3 * σ * (finRotate 3)⁻¹)) ^ 3 = 1 := by
  decide +kernel

theorem perm3_sq_of_two_pow {σ : Equiv.Perm (Fin 3)} {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ ^ 2 = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf σ ∣ 6 := by
    have := orderOf_dvd_card (x := σ)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  rw [hjeq] at h2
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have : 2 ^ 2 ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
    have := this.trans h2
    norm_num at this
  rw [← orderOf_dvd_iff_pow_eq_one, hjeq]
  exact Nat.pow_dvd_pow 2 hj1

theorem perm3_normal_pgroup_eq_bot (N : Subgroup (Equiv.Perm (Fin 3))) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra h1
  have hsq : ∀ τ ∈ N, τ ^ 2 = 1 := fun τ hτ => by
    obtain ⟨k, hk⟩ := hN ⟨τ, hτ⟩
    exact perm3_sq_of_two_pow (k := k) (by simpa using congrArg Subtype.val hk)
  have hc : finRotate 3 * σ * (finRotate 3)⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹_› σ hσ _
  have hprod := hsq _ (N.mul_mem hσ hc)
  exact (perm3_inv_conj σ (hsq σ hσ) h1).1 hprod

theorem exists_even_moving_four :
    (Equiv.swap (0 : Fin 5) 4 * Equiv.swap 1 2 : Equiv.Perm (Fin 5)).sign = 1 ∧
      (Equiv.swap (0 : Fin 5) 4 * Equiv.swap 1 2 : Equiv.Perm (Fin 5)) 4 ≠ 4 := by
  decide

section BaerSuzuki

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_pCoreOf (H : Subgroup G) :
    (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H := CFSG.openPCoreOf_subgroupOf 2 H

theorem exists_not_isPGroup_mod_of_not_mem {H : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx2 : x ^ 2 = 1) (hxQ : x ∉ pCoreOf 2 H) :
    ∃ h ∈ H, ∃ y ∈ Subgroup.closure ({x, h * x * h⁻¹} : Set G),
      ∀ n : ℕ, y ^ 2 ^ n ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  have hmem : ∀ (a : ↥H) (n : ℕ),
      (a : ↥H ⧸ CFSG.pCore 2 ↥H) ^ n = 1 ↔ (a : G) ^ n ∈ pCoreOf 2 H := by
    intro a n
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← subgroupOf_pCoreOf,
      Subgroup.mem_subgroupOf]
    rfl
  have hpg : ∀ gb : ↥H ⧸ CFSG.pCore 2 ↥H, IsPGroup 2 ↥(Subgroup.closure
      ({((⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H),
        gb * ((⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * gb⁻¹} : Set _)) := by
    intro gb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    set K : Subgroup ↥H := Subgroup.closure ({⟨x, hxH⟩, g * ⟨x, hxH⟩ * g⁻¹} : Set ↥H)
    have himg : Subgroup.closure ({((⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H),
        (g : ↥H ⧸ CFSG.pCore 2 ↥H) * ((⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) *
          (g : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹} : Set _) ≤ K.map (QuotientGroup.mk' _) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨_, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · refine ⟨g * ⟨x, hxH⟩ * g⁻¹, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), ?_⟩
        simp
    have hKG : K ≤ (Subgroup.closure ({x, (g : G) * x * (g : G)⁻¹} : Set G)).subgroupOf H := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    refine IsPGroup.to_le ?_ himg
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    obtain ⟨n, hn⟩ := hall g g.2 k (Subgroup.mem_subgroupOf.mp (hKG hk))
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]
    exact (hmem k (2 ^ n)).2 hn
  have hxb2 : ((⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 2 = 1 :=
    (hmem _ 2).2 (by rw [show ((⟨x, hxH⟩ : ↥H) : G) = x from rfl, hx2]; exact Subgroup.one_mem _)
  have hxb : IsPGroup 2 ↥(Subgroup.zpowers ((⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxb2, one_zpow]
  have hBS := CFSG.BaerSuzuki.baer_suzuki _ hxb hpg
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at hBS
  apply hxQ
  have := (hmem ⟨x, hxH⟩ 1).1 (by rw [pow_one]; exact hBS)
  simpa using this

omit [Finite G] in
theorem le_normalizer_commutator {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ h ∈ X, ∀ y ∈ ⁅A, B⁆, h * y * h⁻¹ ∈ ⁅A, B⁆ := by
    intro h hh y hy
    have hmap := Subgroup.map_commutator A B (MulAut.conj h).toMonoidHom
    rw [map_conj_eq_of_mem_normalizer (hA hh), map_conj_eq_of_mem_normalizer (hB hh)] at hmap
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have := key h⁻¹ (X.inv_mem hh) _ hy
  simpa [mul_assoc] using this

end BaerSuzuki

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem commutator_UH_L1 {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) :
    ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H := by
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hUN : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) := le_normalizer_conjClosure _ _
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u hu l hl
    have : l * u⁻¹ * l⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hUN (hL1H hl)) _).mp (Subgroup.inv_mem _ hu)
    rw [commutatorElement_def]
    have e : u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hu this
  · have hN := le_normalizer_commutator (A := conjClosure S.V3 H) (B := S.L1) hUN hn
    refine conjClosure_le fun h hh x hx => ?_
    have hx' : x ∈ ⁅conjClosure S.V3 H, S.L1⁆ :=
      Subgroup.commutator_mono (le_conjClosure _ _) le_rfl (S.commutator_V3_L1.ge hx)
    exact (Subgroup.mem_normalizer_iff.mp (hN hh) x).mp hx'

theorem UH_le_L1 (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) : conjClosure S.V3 H ≤ S.L1 := by
  have h1 := S.commutator_UH_L1 hH hn
  refine (S.lemma_13_5_14_one h1323 hH ?_).2
  rw [h1]
  exact sup_eq_left.mpr (S.V1_le_V3.trans (le_conjClosure _ _))

theorem pCoreOf_L1_le {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) : pCoreOf 2 S.L1 ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hL1H)
    (hn.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem exists_L_not_normalizer_V1 : ∃ l ∈ L, l ∉ Subgroup.normalizer (S.V1 : Set G) := by
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L _).2 exists_even_moving_four.1
  refine ⟨g, hgL, fun hgN => exists_even_moving_four.2 ?_⟩
  rw [← hg]
  exact S.rho_four_of_conj_z g.2 (S.conj_z_of_normalizes hgN)

theorem G248_data (h1323 : Input1323Two) (hG248 : StmtG248) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (S.V1 : Set G)) :
    conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) l = L ∧ IsShort2 L ∧ IsAltType L 5 ∧
      pCoreOf 2 L = V ∧ conjClosure S.V3 H = pCoreOf 2 S.L1 ∧
      IsQ8Sq ↥(conjClosure S.V3 H) := by
  have hU : ⁅conjClosure S.V3 H, lOne L S.V1⁆ ⊔ S.V1 = conjClosure S.V3 H := by
    rw [lOne_eq_L₁Of]
    show ⁅conjClosure S.V3 H, S.L1⁆ ⊔ S.V1 = conjClosure S.V3 H
    rw [S.commutator_UH_L1 hH hn]
    exact sup_eq_left.mpr (S.V1_le_V3.trans (le_conjClosure _ _))
  have hO : pCoreOf 2 (lOne L S.V1) ≤ pCoreOf 2 H := by
    rw [lOne_eq_L₁Of]
    exact S.pCoreOf_L1_le hH hn
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    hG248 G S.V3 S.V1 L T H (S.almostSpecialA5Hyp h1323 hH hna) hU hO l hl hlN
  refine ⟨c1, c2, c3, c4.trans S.conjClosure_V1_L, ?_, c6⟩
  rw [c5, lOne_eq_L₁Of]
  rfl

theorem not_V_le_QH (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : ¬ V ≤ pCoreOf 2 H := fun h =>
  hna (((S.tfae_13_5_10 h1323 hH).out 1 2).1 h)

theorem F956_data (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    (hF956 : StmtF956i) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    ∃ h ∈ H, IsQ8Sq ↥(S.V3 ⊔ conjSub h⁻¹ S.V3) ∧
      (∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
        Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
          Equiv.Perm (Fin 3))) ∧
      (V ⊔ conjSub h⁻¹ V) ⊓ pCoreOf 2 H = S.V3 ⊔ conjSub h⁻¹ S.V3 := by
  have hF := S.hypF91 h1323 hH
  have hV := S.not_V_le_QH h1323 hH hna
  obtain ⟨v, hvV, hvQ⟩ := IsConcreteLE.not_le_iff_exists.1 hV
  obtain ⟨g, hgH, y, hy, hyQ⟩ :=
    exists_not_isPGroup_mod_of_not_mem (hF.V_le_H hvV) (S.elemAbelian_V.2 v hvV) hvQ
  have hcl : Subgroup.closure ({v, g * v * g⁻¹} : Set G) ≤ V ⊔ conjSub (g⁻¹)⁻¹ V := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_left hvV
    · refine Subgroup.mem_sup_right ?_
      rw [inv_inv, mem_conjSub]
      simpa [mul_assoc] using hvV
  have hI : ¬ (∀ x ∈ V ⊔ conjSub (g⁻¹)⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) := by
    intro hall
    obtain ⟨n, hn⟩ := hall y (hcl hy)
    exact hyQ n hn
  have hcard : Nat.card V = 2 ^ 4 := S.card_V.trans (by norm_num)
  obtain ⟨hQ8, hS3⟩ := hF956 G T V L S.V1 S.V3 H hF S.relIndex_V3 hV
    (fun g hg hlt => S.isPGroup_sup_of_lt h1323 h1326 h1336 hH hg hlt) (S.hyp_F956 h1323 H)
    hcard g⁻¹ (H.inv_mem hgH) hI
  exact ⟨g⁻¹, H.inv_mem hgH, hQ8, hS3, hF.F95_UI_eq S.relIndex_V3 hV (H.inv_mem hgH)⟩

theorem UI_le_UH {H : Subgroup G} {h : G} (hh : h ∈ H) :
    S.V3 ⊔ conjSub h⁻¹ S.V3 ≤ conjClosure S.V3 H := by
  refine sup_le (le_conjClosure _ _) fun x hx => ?_
  rw [mem_conjSub, inv_inv] at hx
  have := mem_conjClosure (H.inv_mem hh) hx
  simpa [mul_assoc] using this

theorem I_data (h1323 : Input1323Two) (hG248 : StmtG248) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {h : G} (hh : h ∈ H)
    (hQ8 : IsQ8Sq ↥(S.V3 ⊔ conjSub h⁻¹ S.V3))
    (hS3 : ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
      Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
        Equiv.Perm (Fin 3)))
    (hUI : (V ⊔ conjSub h⁻¹ V) ⊓ pCoreOf 2 H = S.V3 ⊔ conjSub h⁻¹ S.V3) :
    S.V3 ⊔ conjSub h⁻¹ S.V3 = conjClosure S.V3 H ∧
      pCoreOf 2 (V ⊔ conjSub h⁻¹ V) = conjClosure S.V3 H ∧
      Nat.card (pCoreOf 2 (V ⊔ conjSub h⁻¹ V)) = 32 ∧
      Nonempty (oTwoQuot ↥(V ⊔ conjSub h⁻¹ V) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := V ⊔ conjSub h⁻¹ V with hIdef
  obtain ⟨l, hl, hlN⟩ := S.exists_L_not_normalizer_V1
  obtain ⟨-, -, -, -, -, hUQ8⟩ := S.G248_data h1323 hG248 hH hn hna hl hlN
  have hUIeq : S.V3 ⊔ conjSub h⁻¹ S.V3 = conjClosure S.V3 H :=
    Subgroup.eq_of_le_of_card_ge (S.UI_le_UH hh) (by rw [hQ8.1, hUQ8.1])
  have hF := S.hypF91 h1323 hH
  have hIH : I ≤ H := sup_le hF.V_le_H (hF.conjSub_inv_le_H hh)
  have hO2 : pCoreOf 2 I = I ⊓ pCoreOf 2 H := by
    apply le_antisymm
    ·
      obtain ⟨hNorm, ⟨e⟩⟩ := hS3
      have hP :
          (CFSG.Open.pCore 2 ↥I).map (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) = ⊥ := by
        have hnorm : ((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).Normal :=
          Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) _
            (QuotientGroup.mk'_surjective _)
        have hpg : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))) :=
          (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
        have h1 : ((CFSG.Open.pCore 2 ↥I).map
            (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).map e.toMonoidHom = ⊥ := by
          have : ((((CFSG.Open.pCore 2 ↥I).map
              (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I))).map e.toMonoidHom)).Normal :=
            Subgroup.Normal.map hnorm _ e.surjective
          exact perm3_normal_pgroup_eq_bot _ (hpg.map _)
        rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1
        exact h1
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have hx1 : (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) x = 1 := by
        have : (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) x ∈
            (CFSG.Open.pCore 2 ↥I).map (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)) :=
          ⟨x, hx, rfl⟩
        rw [hP, Subgroup.mem_bot] at this
        exact this
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx1
      exact hx1
    · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxI, hxQ⟩
        exact ⟨I.mul_mem (I.mul_mem hy hxI) (I.inv_mem hy),
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hIH hy)) x).mp hxQ⟩
      · rintro ⟨hxI, hxQ⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hIH hy)) x).mpr
          hxQ⟩
        have := I.mul_mem (I.mul_mem (I.inv_mem hy) hxI) hy
        simpa [mul_assoc] using this
  have hO2' : pCoreOf 2 I = conjClosure S.V3 H := by rw [hO2, hUI, hUIeq]
  refine ⟨hUIeq, hO2', by rw [hO2', hUQ8.1], ?_⟩
  obtain ⟨hNorm, ⟨e⟩⟩ := hS3
  have hsub : CFSG.Open.pCore 2 ↥I = (pCoreOf 2 H).subgroupOf I := by
    have h1 : (pCoreOf 2 I).subgroupOf I = CFSG.Open.pCore 2 ↥I := by
      show ((CFSG.Open.pCore 2 ↥I).map I.subtype).subgroupOf I = _
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective I.subtype_injective]
    rw [← h1, hO2]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hsub).trans e⟩

end Setting

end CFSG.Quasithin.H13.A5
