module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CentralThreeLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22HexadLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22CoverPoints
public import CFSG.Quasithin.Background.RonanE43M22Real
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.CaseM22Dispatch
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankMat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

open CFSG.Quasithin.RonanE43 CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
theorem m22_one_sup_five : Cm 1 ⊔ Cm 5 = Cm 3 :=
  m22_join 1 5 3 (by decide +kernel)

open CFSG.Quasithin.RonanE43 CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
theorem m22_inv_one (α : MulAut ↥Mgrp)
    (hα : Ugrp.map α.toMonoidHom = Ugrp) : (Pm 1).map α.toMonoidHom = Pm 1 := by
  have hY : Ugrp ≤ (Pm 1).map α.toMonoidHom := by
    rw [← hα]
    exact Subgroup.map_mono (m22_U_le_Pm 1 (by norm_num))
  obtain ⟨j, hj, hYj⟩ := m22_overgroup _ hY
  have hcard : cert.sizes.getD j 0 = 384 := by
    rw [← m22_Pm_card j hj, ← hYj, Subgroup.card_map_of_injective α.injective,
      m22_Pm_card 1 (by norm_num)]
    rfl
  rcases m22_sizes_384 j hj hcard with rfl | rfl
  · exact hYj
  · exfalso
    have h5 : (Pm 5).map α.symm.toMonoidHom = Pm 5 :=
      m22_inv_five α.symm (m22_symm_normalizes α hα)
    have h15 : Pm 1 = Pm 5 := by
      have := congrArg (fun H => H.map α.symm.toMonoidHom) hYj
      rwa [map_map_symm, h5] at this
    have h12 : Pm 1 ≤ Pm 2 := Subgroup.subgroupOf_mono Mgrp m22_one_le_two
    have h52 : Cm 5 ≤ Cm 2 := by
      have h2 : Pm 5 ≤ Pm 2 := by rw [← h15]; exact h12
      have := Subgroup.map_mono (f := Mgrp.subtype) h2
      rwa [Subgroup.map_subgroupOf_eq_of_le (m22_Cm_le 5 (by norm_num)),
        Subgroup.map_subgroupOf_eq_of_le (m22_Cm_le 2 (by norm_num))] at this
    have h25 : Cm 2 = Cm 4 := by
      rw [m22_Cm_four, ← m22_two_sup_five, sup_eq_left.mpr h52]
    have hc24 : Nat.card (Cm 2) = Nat.card (Cm 4) := by rw [h25]
    rw [m22_Cm_card 2 (by norm_num), m22_Cm_card 4 (by norm_num)] at hc24
    exact absurd hc24 (by decide)

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB CFSG.Quasithin.RonanE43
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
theorem m22_overgroups_of_equiv {Y : Type} [Group Y] [Finite Y]
    {K S : Subgroup Y} [hK : K.Normal] (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (e : ↥K ≃* ↥Mgrp) :
    ∃ H₁ H₂ Q : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ Nat.card H₁ = 3 * Nat.card S ∧
      Nat.card H₂ = 3 * Nat.card S ∧ Q ≤ K ∧ Nat.card Q = 5760 ∧ Q ≤ H₁ ⊔ H₂ := by
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK m22_isSylow
  have hα : ∀ t ∈ S, Ugrp.map (autK e' t).toMonoidHom = Ugrp := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (SporB.le_normalizer_inf hK ht)
  have hcardSK : Nat.card ↥(S ⊓ K) = Nat.card Ugrp := by
    rw [← he', Subgroup.card_map_of_injective e'.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have step : ∀ P : Subgroup ↥Mgrp, Ugrp ≤ P →
      (∀ α : MulAut ↥Mgrp, Ugrp.map α.toMonoidHom = Ugrp → P.map α.toMonoidHom = P) →
      Nat.card P = 3 * Nat.card Ugrp →
      Nat.card ↥(S ⊔ (P.map e'.symm.toMonoidHom).map K.subtype) = 3 * Nat.card S := by
    intro P hUP hinv hP
    set H₀ : Subgroup Y := (P.map e'.symm.toMonoidHom).map K.subtype with hH₀
    have hSH₀ : S ⊓ K ≤ H₀ := (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
    have hnorm : S ≤ Subgroup.normalizer (H₀ : Set Y) := fun t ht =>
      mem_normalizer_pull e' (hinv _ (hα t ht))
    have hH₀K : H₀ ≤ K := pull_le e' P
    have hinf : S ⊓ H₀ = S ⊓ K :=
      le_antisymm (inf_le_inf_left _ hH₀K) (le_inf inf_le_left hSH₀)
    have hcardH₀ : Nat.card H₀ = Nat.card P := by
      rw [hH₀, Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective e'.symm.injective]
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      hnorm
    rw [hinf, hcardSK, hcardH₀, hP] at h
    have hU0 : 0 < Nat.card Ugrp := Nat.card_pos
    have h2 : Nat.card ↥(S ⊔ H₀) * Nat.card Ugrp = (3 * Nat.card S) * Nat.card Ugrp := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hU0 h2
  have hU : Nat.card Ugrp = 128 := by
    rw [m22_Pm_zero, m22_Pm_card 0 (by norm_num)]
    rfl
  have hc1 : Nat.card (Pm 1) = 3 * Nat.card Ugrp := by
    rw [m22_Pm_card 1 (by norm_num), hU]
    rfl
  have hc5 : Nat.card (Pm 5) = 3 * Nat.card Ugrp := by
    rw [m22_Pm_card 5 (by norm_num), hU]
    rfl
  refine ⟨_, _, ((Pm 3).map e'.symm.toMonoidHom).map K.subtype, le_sup_left, le_sup_left,
    step (Pm 1) (m22_U_le_Pm 1 (by norm_num)) m22_inv_one hc1,
    step (Pm 5) (m22_U_le_Pm 5 (by norm_num)) m22_inv_five hc5, pull_le e' _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e'.symm.injective, m22_Pm_card 3 (by norm_num)]
    rfl
  · have h135 : Pm 3 = Pm 1 ⊔ Pm 5 := by
      rw [← Subgroup.subgroupOf_sup (m22_Cm_le 1 (by norm_num)) (m22_Cm_le 5 (by norm_num)),
        m22_one_sup_five]
    rw [h135, pull_sup]
    exact sup_le_sup le_sup_right le_sup_right

theorem m22_cube_of_nine (g : ↥CFSG.Blueprint.NativeSporadic.M22)
    (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  obtain ⟨Q, hQe, hQc⟩ : ∃ Q : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22,
      IsElemAbelian 3 Q ∧ Nat.card Q = 9 :=
    CFSG.QuasithinUnique.Lin2.OddRank.Mat.hasElemAb_nine_M22
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hQc' : Nat.card Q = 3 ^ 2 := hQc
  have hidx : ¬ 3 ∣ Q.index := by
    have h1 := Subgroup.card_mul_index Q
    rw [hQc, hcard] at h1
    omega
  have hg' : g ^ (3 ^ 2) = 1 := hg
  exact pow_eq_one_of_index Q hQc' hidx (fun q hq => hQe.2 q hq) hg'

open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
theorem hexadPair_of_equiv
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} (hKY : KYForm Y K S)
    (e : ↥K ≃* ↥CFSG.Blueprint.NativeSporadic.M22) :
    ∃ E X₁ X₂ : Subgroup Y,
      E ≤ K ∧ Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
        X₁ ≤ K ∧ X₂ ≤ K ∧ Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧
          Permutes X₁ S ∧ Permutes X₂ S ∧ E ≤ X₁ ⊔ X₂ ⊔ S := by
  have hKN : K.Normal := hKY.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hKY.2.2.2.2.2
  obtain ⟨H₁, H₂, Q, hS₁, hS₂, hc₁, hc₂, hQK, hQc, hQle⟩ :=
    m22_overgroups_of_equiv hS (e.trans (MulEquiv.subgroupCongr mGens_closure.symm))
  obtain ⟨X₁, -, hX₁K, hX₁c, -, hX₁S, hX₁P⟩ := exists_permutes_of_overgroup hKN
    hKY.2.2.2.2.1 hS.2.1 hS₁ (p := 3) (n := 1) (by norm_num) (by rw [hc₁]; ring)
  obtain ⟨X₂, -, hX₂K, hX₂c, -, hX₂S, hX₂P⟩ := exists_permutes_of_overgroup hKN
    hKY.2.2.2.2.1 hS.2.1 hS₂ (p := 3) (n := 1) (by norm_num) (by rw [hc₂]; ring)
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Q) 3 (n := 2)
    (by rw [hQc]; norm_num)
  set E : Subgroup Y := E₀.map Q.subtype with hEdef
  have hEc : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective Q.subtype_injective, hE₀]
    norm_num
  have hEQ : E ≤ Q := Subgroup.map_subtype_le E₀
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have h9 : x ^ 9 = 1 := by
      have hdvd : orderOf x ∣ 9 := by simpa [hEc] using Subgroup.orderOf_dvd_natCard E hx
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hxK : x ∈ K := hQK (hEQ hx)
    have h1 : (e ⟨x, hxK⟩) ^ 9 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ 9 = 1 := Subtype.ext (by simpa using h9)
      rw [this, map_one]
    have h2 := m22_cube_of_nine _ h1
    rw [← map_pow, map_eq_one_iff _ e.injective] at h2
    simpa using congrArg Subtype.val h2
  refine ⟨E, X₁, X₂, hEQ.trans hQK, hEc, ⟨?_, hE3⟩, hX₁K, hX₂K, by rw [hX₁c]; norm_num,
    by rw [hX₂c]; norm_num, hX₁P, hX₂P, ?_⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hEc]; norm_num)
  · calc E ≤ Q := hEQ
      _ ≤ H₁ ⊔ H₂ := hQle
      _ = (X₁ ⊔ S) ⊔ (X₂ ⊔ S) := by rw [hX₁S, hX₂S]
      _ ≤ X₁ ⊔ X₂ ⊔ S := sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right)

open scoped IsMulCommutative in
open CFSG.Quasithin.RonanE43 CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
theorem hexadPair_of_center_three
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} (hKY : KYForm Y K S)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22)
    (hZ3 : Nat.card (Subgroup.center ↥K) = 3) :
    ∃ E X₁ X₂ : Subgroup Y,
      E ≤ K ∧ Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
        X₁ ≤ K ∧ X₂ ≤ K ∧ Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧
          Permutes X₁ S ∧ Permutes X₂ S ∧ E ≤ X₁ ⊔ X₂ ⊔ S := by
  classical
  have hK : K.Normal := hKY.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hKY.2.2.2.2.2
  set Z : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hZdef
  have hZn : Z.Normal := by
    have : (Subgroup.center ↥K).Characteristic := Subgroup.centerCharacteristic
    exact ConjAct.normal_of_characteristic_of_normal (H := K) (K := Subgroup.center ↥K)
  have hZK : Z ≤ K := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z := by
    rintro _ ⟨c, hc, rfl⟩ k hk
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k, hk⟩)
    simpa using h1.symm
  have hZcard : Nat.card Z = 3 := (Subgroup.card_subtype K (Subgroup.center ↥K)).trans hZ3
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf (S.map (QuotientGroup.mk' Z)) ⊤ :=
    ⟨le_top, hS.2.1.map _, by
      rw [show ((S.map (QuotientGroup.mk' Z)).subgroupOf ⊤).index =
        (S.map (QuotientGroup.mk' Z)).index from Subgroup.relIndex_top_right _]
      exact isSylowIn_map _ hπ hS⟩
  have : (K.map (QuotientGroup.mk' Z)).Normal := hK.map _ hπ
  let ψ : ↥K →* Y ⧸ Z := (QuotientGroup.mk' Z).comp K.subtype
  have hψker : ψ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' Z (x : Y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hψrange : ψ.range = K.map (QuotientGroup.mk' Z) := by
    show ((QuotientGroup.mk' Z).comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have e' : (↥K ⧸ Subgroup.center ↥K) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  let eM : (↥K ⧸ Subgroup.center ↥K) ≃* ↥Mgrp :=
    e'.trans (MulEquiv.subgroupCongr mGens_closure.symm)
  let eQ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  let e₀ : ↥(K.map (QuotientGroup.mk' Z)) ≃* ↥Mgrp :=
    (MulEquiv.subgroupCongr hψrange.symm).trans (eQ.symm.trans eM)
  obtain ⟨H₁, -, -, hSH₁, -, hH₁c, -⟩ := m22_overgroups_of_equiv hS' e₀
  have hZS : Z ⊓ S = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
    rw [hZcard, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hSc : Nat.card (S.map (QuotientGroup.mk' Z)) = Nat.card S := by
    refine card_map_of_injOn _ fun x hx h1 => ?_
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp h1
    have : x ∈ Z ⊓ S := ⟨hxZ, hx⟩
    rw [hZS] at this
    exact Subgroup.mem_bot.mp this
  have hreal : ∀ y : ↥K ⧸ Subgroup.center ↥K, y ^ 3 = 1 →
      ∃ g : ↥K ⧸ Subgroup.center ↥K, g * y * g⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨g, hg⟩ := real3_M22 (eM y) (by rw [← map_pow, hy, map_one])
    refine ⟨eM.symm g, ?_⟩
    apply eM.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  have hker9 : (QuotientGroup.mk' (Subgroup.center ↥K)).ker =
      (Subgroup.center ↥K).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  have h9K := cube_eq_one_of_real (Λ := ↥K) (Γ := ↥K ⧸ Subgroup.center ↥K)
    (Zc := ↥(Subgroup.center ↥K)) hZ3 (Subgroup.center ↥K).subtype
    (Subgroup.subtype_injective _) (fun z => z.2) (QuotientGroup.mk' (Subgroup.center ↥K))
    (QuotientGroup.mk'_surjective _) hker9 hreal
  have h9 : ∀ x ∈ K, x ^ 3 ∈ Z → x ^ 3 = 1 := by
    intro x hx hx3
    have h1 : (⟨x, hx⟩ : ↥K) ^ 3 ∈ (Subgroup.center ↥K).subtype.range := by
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx3
      refine ⟨⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      simpa using hwx
    have := h9K ⟨x, hx⟩ h1
    simpa using congrArg Subtype.val this
  obtain ⟨X, hXK, -, hXc, hXP, hXZ, -⟩ :=
    exists_permutes_three_of_lift hKY.2.2.2.2.1 hS hZK hZcard hZc h9 hSH₁ (by rw [hH₁c, hSc])
  have hcard3 : ∀ W : Subgroup Y, Nat.card W = 3 → ∀ x ∈ W, x ^ 3 = 1 := by
    intro W hW x hx
    have hdvd : orderOf x ∣ 3 := by simpa [hW] using Subgroup.orderOf_dvd_natCard W hx
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hEc : Nat.card ↥(Z ⊔ X) = 9 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := X) (K := Z) (by rw [Subgroup.normalizer_eq_top_iff.mpr hZn]; exact le_top)
    rw [hXZ, Subgroup.card_bot, mul_one, hXc, hZcard, sup_comm] at h
    exact h
  have hE3 : ∀ y ∈ Z ⊔ X, y ^ 3 = 1 := by
    intro y hy
    have hy' : y ∈ ((Z ⊔ X : Subgroup Y) : Set Y) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨z, hz, x, hx, rfl⟩ := hy'
    have hc : Commute z x := hZc z hz x (hXK hx)
    rw [hc.mul_pow, hcard3 Z hZcard z hz, hcard3 X hXc x hx, one_mul]
  have hZP : Permutes Z S := by
    show (Z : Set Y) * (S : Set Y) = (S : Set Y) * (Z : Set Y)
    rw [← Subgroup.normal_mul Z S, ← Subgroup.mul_normal S Z, sup_comm]
  refine ⟨Z ⊔ X, X, Z, sup_le hZK hXK, hEc, ⟨?_, hE3⟩, hXK, hZK, hXc, hZcard, hXP, hZP, ?_⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hEc]; norm_num)
  · exact sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)

theorem k_M22HexadPair_holds :
    K_M22HexadPair := by
  intro Y _ _ K S hKY hM22
  have : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKY.2.1.1
  obtain ⟨e₀⟩ := hM22
  rcases CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.m22_center_card_odd_cases
    hKY.2.2.1 e₀ with h1 | h3
  · have hZ : Subgroup.center ↥K = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨eN⟩ : Nonempty (↥K ≃* ↥CFSG.Blueprint.NativeSporadic.M22) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₀⟩
    exact hexadPair_of_equiv hKY eN
  · exact hexadPair_of_center_three hKY e₀ h3

theorem k_M22CoverNine_of_hexadPair (h : K_M22HexadPair) :
    K_M22CoverNine := by
  intro Y _ _ K S hKY hM22 hZne
  obtain ⟨E, X₁, X₂, -, hE9, -, hX₁K, hX₂K, hX₁3, hX₂3, hP₁, hP₂, hEle⟩ := h Y K S hKY hM22
  have hKN : K.Normal := hKY.1
  have hSylY : IsSylowIn 2 S ⊤ := hKY.2.2.2.2.2
  have hSylYcard : Nat.card S = 2 ^ (Nat.card Y).factorization 2 := by
    simpa using hSylY.card_eq
  have hZK3 : Nat.card (Subgroup.center ↥K) = 3 := by
    obtain ⟨e⟩ := hM22
    have : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKY.2.1.1
    rcases CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.m22_center_card_odd_cases
      hKY.2.2.1 e with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZne
    · exact h3
  set Z : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hZdef
  have hZn : Z.Normal := by
    have : (Subgroup.center ↥K).Characteristic := Subgroup.centerCharacteristic
    exact ConjAct.normal_of_characteristic_of_normal (H := K) (K := Subgroup.center ↥K)
  have hZcard : Nat.card Z = 3 := (Subgroup.card_subtype K (Subgroup.center ↥K)).trans hZK3
  have hZK : Z ≤ K := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hZcent : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z := by
    rintro _ ⟨c, hc, rfl⟩ k hk
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k, hk⟩)
    simpa using h1.symm
  have hcard3 : ∀ X : Subgroup Y, Nat.card X = 3 → ∀ x ∈ X, x ^ 3 = 1 := by
    intro X hX x hx
    have hdvd : orderOf x ∣ 3 := by
      simpa [hX] using Subgroup.orderOf_dvd_natCard X hx
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hZS : Z ⊓ S = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hZcard, hSylYcard]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hcardZS : Nat.card ↥(Z ⊔ S) = 3 * Nat.card S := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := S) (K := Z) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rw [sup_comm, inf_comm, hZS, Subgroup.card_bot, mul_one, mul_comm, hZcard] at h
    exact h
  have hex : ∃ X : Subgroup Y, X ≤ K ∧ Nat.card X = 3 ∧ Permutes X S ∧ ¬ X ≤ Z := by
    by_contra hcon
    push Not at hcon
    have h₁ : X₁ ≤ Z := hcon X₁ hX₁K hX₁3 hP₁
    have h₂ : X₂ ≤ Z := hcon X₂ hX₂K hX₂3 hP₂
    have hEZS : E ≤ Z ⊔ S :=
      hEle.trans (sup_le (sup_le (h₁.trans le_sup_left) (h₂.trans le_sup_left)) le_sup_right)
    have hdvd : 3 * 3 ∣ 3 * Nat.card S := by
      rw [show 3 * 3 = Nat.card E by rw [hE9], ← hcardZS]
      exact Subgroup.card_dvd_of_le hEZS
    have h3 : 3 ∣ 2 ^ (Nat.card Y).factorization 2 := by
      rw [← hSylYcard]
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
    norm_num at h32
  obtain ⟨X, hXK, hX3, hXP, hXZ⟩ := hex
  have hexp : ∀ y ∈ Z ⊔ X, y ^ 3 = 1 := by
    intro y hy
    have hy' : y ∈ ((Z ⊔ X : Subgroup Y) : Set Y) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨z, hz, x, hx, rfl⟩ := hy'
    have hc : Commute z x := hZcent z hz x (hXK hx)
    rw [hc.mul_pow, hcard3 Z hZcard z hz, hcard3 X hX3 x hx, one_mul]
  refine ⟨Z ⊔ X, sup_le hZK hXK, ?_, ?_, hexp, ?_, ?_⟩
  · intro hbot
    have hZbot : Z = ⊥ := le_bot_iff.mp (by rw [← hbot]; exact le_sup_left)
    rw [hZbot, Subgroup.card_bot] at hZcard
    norm_num at hZcard
  · intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hexp g g.2)⟩
  · intro hcyc
    have := hcyc
    have hexpdvd : Monoid.exponent ↥(Z ⊔ X) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hexp g g.2)
    rw [IsCyclic.exponent_eq_card] at hexpdvd
    have hle : Nat.card ↥(Z ⊔ X) ≤ 3 := Nat.le_of_dvd (by norm_num) hexpdvd
    have hZeq : Z = Z ⊔ X :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hZcard]; exact hle)
    exact hXZ (le_sup_right.trans hZeq.ge)
  · show ((Z ⊔ X : Subgroup Y) : Set Y) * (S : Set Y) = (S : Set Y) * ((Z ⊔ X : Subgroup Y) : Set Y)
    have h1 : ((Z ⊔ X : Subgroup Y) : Set Y) = (Z : Set Y) * (X : Set Y) := Subgroup.normal_mul Z X
    have h2 : (Z : Set Y) * (S : Set Y) = (S : Set Y) * (Z : Set Y) := by
      rw [← Subgroup.normal_mul Z S, ← Subgroup.mul_normal S Z, sup_comm]
    have hXP' : (X : Set Y) * (S : Set Y) = (S : Set Y) * (X : Set Y) := hXP
    rw [h1, mul_assoc, hXP', ← mul_assoc, h2, mul_assoc]

theorem k_M22CoverNine_holds :
    K_M22CoverNine :=
  k_M22CoverNine_of_hexadPair k_M22HexadPair_holds


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
