module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.KleinDim
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.GroupTheory.WielandtProductAux
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ElemAbelianLiftOddKernel
public import CFSG.GroupTheory.OddInversion
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open scoped Pointwise

private theorem card_le_two_of_isElementaryAbelian_two_of_noKlein
    {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {E : Subgroup Γ} (hE : CFSG.IsElementaryAbelian 2 E) : Nat.card E ≤ 2 := by
  classical
  by_contra hle
  have h3 : 3 ≤ Nat.card E := by omega
  haveI : Fintype ↥E := Fintype.ofFinite _
  have h2E : 2 < Fintype.card ↥E := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2E
  have hcases : (a ≠ 1 ∧ b ≠ 1) ∨ (a ≠ 1 ∧ c ≠ 1) ∨ (b ≠ 1 ∧ c ≠ 1) := by
    rcases eq_or_ne a 1 with ha | ha
    · subst ha
      refine Or.inr (Or.inr ⟨fun hb => hab hb.symm, fun hc => hac hc.symm⟩)
    · by_cases hb : b = 1
      · subst hb
        exact Or.inr (Or.inl ⟨ha, fun hc => hbc hc.symm⟩)
      · exact Or.inl ⟨ha, hb⟩
  obtain ⟨x, y, hx1, hy1, hxy⟩ : ∃ x y : ↥E, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
    · exact ⟨a, b, ha, hb, hab⟩
    · exact ⟨a, c, ha, hc, hac⟩
    · exact ⟨b, c, hb, hc, hbc⟩
  have hx2 : (x : Γ) ^ 2 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (x : Γ) x.2
  have hy2 : (y : Γ) ^ 2 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (y : Γ) y.2
  have hx1' : (x : Γ) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hy1' : (y : Γ) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hxy' : (x : Γ) ≠ (y : Γ) := fun h => hxy (Subtype.ext h)
  have hcomm : (x : Γ) * (y : Γ) = (y : Γ) * (x : Γ) :=
    congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥E)).comm x y)
  exact hxy' (hno (x : Γ) (y : Γ) hx2 hy2 hx1' hy1' hcomm)

private theorem exists_conj_eq_of_central_mod_odd {Γ : Type*} [Group Γ]
    {O : Subgroup Γ} (hOodd : Odd (Nat.card O)) {z w : Γ}
    (hz2 : z ^ 2 = 1) (hww : w * w = 1) (hwz : w * z⁻¹ ∈ O) :
    ∃ n ∈ O, z * n * z⁻¹ = n⁻¹ ∧ n * w * n⁻¹ = z := by
  classical
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hz2)
  have hz2' : z * z = 1 := by simpa [pow_two] using hz2
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  let m : Γ := z⁻¹ * w
  have hmO : m ∈ O := by
    have heq : m = (w * z⁻¹)⁻¹ := by
      dsimp [m]
      rw [mul_inv_rev]
      simp [hzinv, hwinv]
    rw [heq]
    exact O.inv_mem hwz
  have hw_m : w = z * m := by
    dsimp [m]
    rw [hzinv, ← mul_assoc, hz2', one_mul]
  have hzm : z * m * z⁻¹ = m⁻¹ := by
    have h := hww
    rw [hw_m] at h
    have h' : z * m * z * m = 1 := by simpa [mul_assoc] using h
    have hzmm : z * m * z = m⁻¹ := by
      calc z * m * z = (z * m * z * m) * m⁻¹ := by group
        _ = 1 * m⁻¹ := by rw [h']
        _ = m⁻¹ := one_mul _
    simpa [hzinv] using hzmm
  have hj : m ∈ CFSG.OddInversion.invertedSet O z := ⟨hmO, hzm⟩
  obtain ⟨n, hnJ, hn2⟩ := CFSG.OddInversion.exists_sq_eq_of_mem_invertedSet hOodd hj
  have hnO : n ∈ O := hnJ.1
  have hzn : z * n * z⁻¹ = n⁻¹ := hnJ.2
  have hznz : z * n * z = n⁻¹ := by simpa [hzinv] using hzn
  have hnz : n * z = z * n⁻¹ := by
    have h := congrArg (fun x => z * x) hznz
    calc n * z = (z * z) * n * z := by rw [hz2', one_mul]
      _ = z * (z * n * z) := by group
      _ = z * n⁻¹ := h
  have hnm : n * n = m := by simpa [pow_two] using hn2
  refine ⟨n, hnO, hzn, ?_⟩
  rw [hw_m, ← hnm]
  calc n * (z * (n * n)) * n⁻¹ = n * z * n := by group
    _ = (z * n⁻¹) * n := by rw [hnz]
    _ = z := by group

private theorem exists_mul_mem_centralizer_of_central_mod_odd {Γ : Type*} [Group Γ]
    {O : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O)) {z : Γ}
    (hz2 : z ^ 2 = 1) (hcomm : ∀ g : Γ, g * z * g⁻¹ * z⁻¹ ∈ O) (g : Γ) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set Γ), ∃ o ∈ O, g = c * o := by
  classical
  have hz2' : z * z = 1 := by simpa [pow_two] using hz2
  let w : Γ := g⁻¹ * z * g
  have hw_eq : w = g⁻¹ * z * g := rfl
  have hww : w * w = 1 := by
    rw [hw_eq]
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2']; group
  have h1 : z * g⁻¹ * z⁻¹ * g ∈ O := by
    have h := hOn.conj_mem (g * z * g⁻¹ * z⁻¹) (hcomm g) g⁻¹
    simpa [mul_assoc] using h
  have h2 : w * z⁻¹ ∈ O := by
    have heq : (z * g⁻¹ * z⁻¹ * g)⁻¹ = w * z⁻¹ := by
      rw [hw_eq]
      group
    rw [← heq]
    exact O.inv_mem h1
  obtain ⟨n, hnO, hzn, key⟩ :=
    exists_conj_eq_of_central_mod_odd hOodd hz2 hww h2
  have hkey' : (g * n⁻¹)⁻¹ * z * (g * n⁻¹) = z := by
    simpa [hw_eq, mul_assoc] using key
  have hcomm_c : z * (g * n⁻¹) = (g * n⁻¹) * z := by
    calc z * (g * n⁻¹) =
        (g * n⁻¹) * ((g * n⁻¹)⁻¹ * z * (g * n⁻¹)) := by group
      _ = (g * n⁻¹) * z := by rw [hkey']
  have hcz : (g * n⁻¹) * z * (g * n⁻¹)⁻¹ = z := by
    rw [← hcomm_c]
    group
  refine ⟨g * n⁻¹, ?_, n, hnO, by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (g * n⁻¹) * z = ((g * n⁻¹) * z * (g * n⁻¹)⁻¹) * (g * n⁻¹) := by group
    _ = z * (g * n⁻¹) := by rw [hcz]

private theorem exists_card_two_lift_of_elementary_abelian {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {O : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O))
    {Q : Subgroup (Γ ⧸ O)} (hQelem : CFSG.IsElementaryAbelian 2 Q) (hQne : Q ≠ ⊥) :
    ∃ S : Subgroup Γ, CFSG.IsElementaryAbelian 2 S ∧
      S.map (QuotientGroup.mk' O) = Q ∧ Nat.card S = 2 ∧ ∃ m ∈ S, m ≠ 1 := by
  obtain ⟨S, hSelem, hSmap⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_two_map_mk_eq_of_odd_card
      (H := Γ) (N := O) hOodd
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hQelem)
  have hSelem' : CFSG.IsElementaryAbelian 2 S :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hSelem
  have hSle2 : Nat.card S ≤ 2 :=
    card_le_two_of_isElementaryAbelian_two_of_noKlein hno hSelem'
  have hSne : S ≠ ⊥ := by
    intro hSbot
    apply hQne
    rw [← hSmap, hSbot, Subgroup.map_bot]
  have hSge2 : 2 ≤ Nat.card S := by
    have h1 : 1 < Nat.card S := (Subgroup.one_lt_card_iff_ne_bot S).mpr hSne
    omega
  have hScard : Nat.card S = 2 := le_antisymm hSle2 hSge2
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  obtain ⟨m, hmS, hm1⟩ := Subgroup.exists_ne_one_of_nontrivial S
  exact ⟨S, hSelem', hSmap, hScard, m, hmS, hm1⟩

private theorem exists_lift_involution_of_elementary_abelian_quotient
    {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {O M : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O)) (hOMle : O ≤ M)
    {Q : Subgroup (Γ ⧸ O)} (hQeq : Q = M.map (QuotientGroup.mk' O))
    (hQelem : CFSG.IsElementaryAbelian 2 Q) (hQne : Q ≠ ⊥) :
    ∃ m ∈ M, m ^ 2 = 1 ∧ m ≠ 1 ∧ Q = Subgroup.zpowers (QuotientGroup.mk' O m) := by
  obtain ⟨S, hSelem, hSmap, hScard, m, hmS, hm1⟩ :=
    exists_card_two_lift_of_elementary_abelian hno hOn hOodd hQelem hQne
  have hm2 : m ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian m hmS
  have hS_le_M : S ≤ M := by
    intro x hx
    have hxQ : QuotientGroup.mk' O x ∈ Q := hSmap ▸ Subgroup.mem_map_of_mem _ hx
    have hxcomap : x ∈ Q.comap (QuotientGroup.mk' O) := hxQ
    have hcomap : Q.comap (QuotientGroup.mk' O) = M := by
      rw [hQeq]
      have h := QuotientGroup.comap_map_mk' O M
      rwa [sup_eq_right.mpr hOMle] at h
    rwa [hcomap] at hxcomap
  have hmM : m ∈ M := hS_le_M hmS
  have hm_ord : orderOf m = 2 := orderOf_eq_prime hm2 hm1
  have hS_eq : S = Subgroup.zpowers m := by
    have hle : Subgroup.zpowers m ≤ S := Subgroup.zpowers_le.mpr hmS
    have hcard : Nat.card S ≤ Nat.card (Subgroup.zpowers m) := by
      rw [Nat.card_zpowers, hm_ord, hScard]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  refine ⟨m, hmM, hm2, hm1, ?_⟩
  rw [← hSmap, hS_eq, MonoidHom.map_zpowers]

private theorem exists_lift_of_central_pair {Γ : Type*} [Group Γ] [Finite Γ]
    {O : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O)) {z m : Γ}
    (hz2 : z ^ 2 = 1) (hm2 : m ^ 2 = 1)
    (hm_central : QuotientGroup.mk' O m ∈ Subgroup.center (Γ ⧸ O)) :
    ∃ T : Subgroup Γ, CFSG.IsElementaryAbelian 2 T ∧
      QuotientGroup.mk' O z ∈ T.map (QuotientGroup.mk' O) ∧
      QuotientGroup.mk' O m ∈ T.map (QuotientGroup.mk' O) := by
  classical
  let zq : Γ ⧸ O := QuotientGroup.mk' O z
  let mq : Γ ⧸ O := QuotientGroup.mk' O m
  have hzq2 : zq ^ 2 = 1 := by
    change (QuotientGroup.mk' O z) ^ 2 = 1
    rw [← map_pow, hz2, map_one]
  have hmq2 : mq ^ 2 = 1 := by
    change (QuotientGroup.mk' O m) ^ 2 = 1
    rw [← map_pow, hm2, map_one]
  have hcomm : zq * mq = mq * zq := Subgroup.mem_center_iff.mp hm_central zq
  let A : Subgroup (Γ ⧸ O) := Subgroup.closure ({zq, mq} : Set (Γ ⧸ O))
  have hAelem : CFSG.Open.IsElemAbelian 2 A := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hcomm
      · exact hcomm.symm
      · rfl
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · simpa [pow_two] using hzq2
      · simpa [pow_two] using hmq2
  have hAe : CFSG.IsElementaryAbelian 2 A :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hAelem
  obtain ⟨T, hTelem, hTmap⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_two_map_mk_eq_of_odd_card
      (H := Γ) (N := O) hOodd
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hAe)
  have hTe : CFSG.IsElementaryAbelian 2 T :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hTelem
  have hzA : zq ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have hmA : mq ∈ A :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine ⟨T, hTe, ?_, ?_⟩
  · rw [hTmap]; exact hzA
  · rw [hTmap]; exact hmA

private theorem eq_of_map_eq_of_central_of_odd {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {O : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O))
    {z m : Γ} (hz2 : z ^ 2 = 1) (hm2 : m ^ 2 = 1)
    (hzq1 : QuotientGroup.mk' O z ≠ 1) (hmq1 : QuotientGroup.mk' O m ≠ 1)
    (hm_central : QuotientGroup.mk' O m ∈ Subgroup.center (Γ ⧸ O))
    (hne : QuotientGroup.mk' O z ≠ QuotientGroup.mk' O m) : False := by
  obtain ⟨T, hTe, hzT, hmT⟩ := exists_lift_of_central_pair hOn hOodd hz2 hm2 hm_central
  obtain ⟨x, hxT, hx⟩ := Subgroup.mem_map.mp hzT
  obtain ⟨y, hyT, hy⟩ := Subgroup.mem_map.mp hmT
  have hx2 : x ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x hxT
  have hy2 : y ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian y hyT
  have hx1 : x ≠ 1 := by
    intro h
    apply hzq1
    calc QuotientGroup.mk' O z = QuotientGroup.mk' O x := hx.symm
      _ = 1 := by rw [h, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    apply hmq1
    calc QuotientGroup.mk' O m = QuotientGroup.mk' O y := hy.symm
      _ = 1 := by rw [h, map_one]
  have hxy : x ≠ y := by
    intro h
    apply hne
    calc QuotientGroup.mk' O z = QuotientGroup.mk' O x := hx.symm
      _ = QuotientGroup.mk' O y := by rw [h]
      _ = QuotientGroup.mk' O m := hy
  have hcommxy : x * y = y * x :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥T)).comm ⟨x, hxT⟩ ⟨y, hyT⟩)
  exact hxy (hno x y hx2 hy2 hx1 hy1 hcommxy)

private theorem exists_odd_normal_core {Γ : Type*} [Group Γ] [Finite Γ]
    {K : Subgroup Γ} (hKn : K.Normal) {z : Γ} (hzK : z ∈ K)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ O : Subgroup Γ, O.Normal ∧ O ≤ K ∧ Odd (Nat.card O) ∧ z ∉ O ∧
      (∀ N : Subgroup Γ, N.Normal → N ≤ K → Odd (Nat.card N) → N ≤ O) ∧ O < K := by
  classical
  haveI : K.Normal := hKn
  let O : Subgroup Γ := K ⊓ CFSG.oddCore Γ
  have hOn : O.Normal := Subgroup.normal_inf_normal K (CFSG.oddCore Γ)
  have hO_le_K : O ≤ K := inf_le_left
  have hOddCore : Odd (Nat.card (CFSG.oddCore Γ)) := by
    simpa [CFSG.oddCore, CFSG.Open.componentClassificationOddCore] using
      CFSG.ComponentClassification.OddCore.odd_card Γ
  have hOodd : Odd (Nat.card O) :=
    Odd.of_dvd_nat hOddCore (Subgroup.card_dvd_of_le inf_le_right)
  have hz_notin_O : z ∉ O := by
    intro hzO
    have hz_notin_core : z ∉ CFSG.oddCore Γ := by
      intro hzcore
      have hz_ord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
      have hdvd : orderOf z ∣ Nat.card (CFSG.oddCore Γ) :=
        Subgroup.orderOf_dvd_natCard (CFSG.oddCore Γ) hzcore
      rw [hz_ord] at hdvd
      exact hOddCore.not_two_dvd_nat hdvd
    exact hz_notin_core hzO.2
  have hO_max : ∀ N : Subgroup Γ, N.Normal → N ≤ K → Odd (Nat.card N) → N ≤ O := by
    intro N hNn hNK hNodd
    exact le_inf hNK (le_sSup ⟨hNn, hNodd⟩)
  have hOK : O < K := lt_of_le_of_ne hO_le_K (by
    intro h
    exact hz_notin_O (h ▸ hzK))
  exact ⟨O, hOn, hO_le_K, hOodd, hz_notin_O, hO_max, hOK⟩

private theorem exists_minimal_normal_above {Γ : Type*} [Group Γ] [Finite Γ]
    {O K : Subgroup Γ} (hKn : K.Normal) (hOK : O < K) :
    ∃ M : Subgroup Γ, O < M ∧ M.Normal ∧ M ≤ K ∧
      ∀ N : Subgroup Γ, O < N → N.Normal → N ≤ K → N ≤ M → N = M := by
  obtain ⟨M, hMmin⟩ :=
    (Set.toFinite {N : Subgroup Γ | O < N ∧ N.Normal ∧ N ≤ K}).exists_minimal
      ⟨K, hOK, hKn, le_rfl⟩
  refine ⟨M, hMmin.prop.1, hMmin.prop.2.1, hMmin.prop.2.2, ?_⟩
  intro N hON hNn hNK hNM
  exact le_antisymm hNM (hMmin.le_of_le ⟨hON, hNn, hNK⟩ hNM)

private theorem isMinimalNormal_map_mk_of_minimal {Γ : Type*} [Group Γ]
    {O M : Subgroup Γ} (hOn : O.Normal) (hMn : M.Normal) (hOM : O < M)
    (hMmin : ∀ N : Subgroup Γ, O < N → N.Normal → N ≤ M → N = M) :
    IsMinimalNormal (M.map (QuotientGroup.mk' O)) := by
  classical
  let π : Γ →* Γ ⧸ O := QuotientGroup.mk' O
  refine ⟨?_⟩
  intro N hNn hNQ
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    let P : Subgroup Γ := N.comap π
    have hPn : P.Normal := hNn.comap π
    have hOP : O ≤ P := by
      rw [← QuotientGroup.ker_mk' O]
      exact Subgroup.ker_le_comap π N
    have hPM : P ≤ M := by
      have hle : P ≤ (M.map π).comap π := Subgroup.comap_mono hNQ
      have hMcomap : (M.map π).comap π = M := by
        have h := QuotientGroup.comap_map_mk' O M
        rwa [sup_eq_right.mpr hOM.le] at h
      rwa [hMcomap] at hle
    have hP_ne_O : P ≠ O := by
      intro hPO
      apply hNbot
      have hNP : N = P.map π :=
        (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) N).symm
      rw [hPO, QuotientGroup.map_mk'_self] at hNP
      exact hNP
    have hPmem : O < P := lt_of_le_of_ne hOP (Ne.symm hP_ne_O)
    have hPM' : P = M := hMmin P hPmem hPn hPM
    calc N = P.map π :=
        (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) N).symm
      _ = M.map π := by rw [hPM']

private theorem isSolvable_map_mk_quotient {Γ : Type*} [Group Γ]
    {O : Subgroup Γ} (hOn : O.Normal) {M : Subgroup Γ} (hMsolv : Group.IsSolvable ↥M) :
    Group.IsSolvable ↥(M.map (QuotientGroup.mk' O)) := by
  classical
  let Q : Subgroup (Γ ⧸ O) := M.map (QuotientGroup.mk' O)
  let g : ↥M →* ↥Q :=
    { toFun := fun x => ⟨QuotientGroup.mk' O (x : Γ), Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hgsurj : Function.Surjective g := by
    intro q
    obtain ⟨m, hm, hq⟩ := Subgroup.mem_map.mp q.2
    exact ⟨⟨m, hm⟩, Subtype.ext hq⟩
  exact Group.isSolvable_of_surjective (f := g) hgsurj

private theorem card_eq_card_map_mk'_mul {Γ : Type*} [Group Γ] [Finite Γ]
    {O : Subgroup Γ} (hOn : O.Normal) {M : Subgroup Γ} (hOMle : O ≤ M) :
    Nat.card M = Nat.card (M.map (QuotientGroup.mk' O)) * Nat.card O := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf M)]
  rw [← CFSG.natCard_map_mk'_eq M O]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOMle).toEquiv

private theorem exists_central_involution_of_elementary_abelian_two
    {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {O M : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O)) (hOMle : O ≤ M)
    {Q : Subgroup (Γ ⧸ O)} (hQn : Q.Normal)
    (hQeq : Q = M.map (QuotientGroup.mk' O))
    (hQelem : CFSG.IsElementaryAbelian 2 Q) (hQne : Q ≠ ⊥) :
    ∃ m ∈ M, m ^ 2 = 1 ∧ m ≠ 1 ∧
      QuotientGroup.mk' O m ∈ Subgroup.center (Γ ⧸ O) ∧
      Q = Subgroup.zpowers (QuotientGroup.mk' O m) := by
  obtain ⟨m, hmM, hm2, hm1, hQeq_m⟩ :=
    exists_lift_involution_of_elementary_abelian_quotient
      hno hOn hOodd hOMle hQeq hQelem hQne
  have hq2 : (QuotientGroup.mk' O m) ^ 2 = 1 := by
    rw [← map_pow, hm2, map_one]
  have hq1 : QuotientGroup.mk' O m ≠ 1 := by
    intro h
    apply hQne
    rw [hQeq_m, h]
    simp
  have hQcard : Nat.card Q = 2 := by
    rw [hQeq_m, Nat.card_zpowers]
    exact orderOf_eq_prime hq2 hq1
  have hQcentral : Q ≤ Subgroup.center (Γ ⧸ O) :=
    CFSG.Semidihedral.Local.le_center_of_normal_card_two hQn hQcard
  have hm_central : QuotientGroup.mk' O m ∈ Subgroup.center (Γ ⧸ O) := by
    apply hQcentral
    rw [hQeq_m]
    exact Subgroup.mem_zpowers (QuotientGroup.mk' O m)
  exact ⟨m, hmM, hm2, hm1, hm_central, hQeq_m⟩

private theorem eq_of_central_mod_odd {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {O : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O))
    {z m : Γ} (hz2 : z ^ 2 = 1) (hm2 : m ^ 2 = 1)
    (hzq1 : QuotientGroup.mk' O z ≠ 1) (hmq1 : QuotientGroup.mk' O m ≠ 1)
    (hm_central : QuotientGroup.mk' O m ∈ Subgroup.center (Γ ⧸ O)) :
    QuotientGroup.mk' O z = QuotientGroup.mk' O m ∧
      ∀ g : Γ, g * z * g⁻¹ * z⁻¹ ∈ O := by
  have hzm_eq : QuotientGroup.mk' O z = QuotientGroup.mk' O m := by
    by_contra hne
    exact eq_of_map_eq_of_central_of_odd hno hOn hOodd hz2 hm2 hzq1 hmq1 hm_central hne
  refine ⟨hzm_eq, ?_⟩
  have hz_central : QuotientGroup.mk' O z ∈ Subgroup.center (Γ ⧸ O) := by
    rw [hzm_eq]
    exact hm_central
  intro g
  have h : (QuotientGroup.mk' O g) * (QuotientGroup.mk' O z) =
      (QuotientGroup.mk' O z) * (QuotientGroup.mk' O g) :=
    Subgroup.mem_center_iff.mp hz_central (QuotientGroup.mk' O g)
  have h1 : QuotientGroup.mk' O (g * z * g⁻¹ * z⁻¹) = 1 := by
    calc QuotientGroup.mk' O (g * z * g⁻¹ * z⁻¹)
        = QuotientGroup.mk' O g * QuotientGroup.mk' O z *
            (QuotientGroup.mk' O g)⁻¹ * (QuotientGroup.mk' O z)⁻¹ := by
          simp [map_mul, map_inv]
      _ = QuotientGroup.mk' O z * QuotientGroup.mk' O g *
            (QuotientGroup.mk' O g)⁻¹ * (QuotientGroup.mk' O z)⁻¹ := by rw [h]
      _ = QuotientGroup.mk' O z * (QuotientGroup.mk' O z)⁻¹ := by group
      _ = 1 := by group
  exact (QuotientGroup.eq_one_iff _).mp h1

private theorem centralizer_sup_eq_top_of_central_mod_odd {Γ : Type*} [Group Γ]
    {O : Subgroup Γ} (hOn : O.Normal) (hOodd : Odd (Nat.card O)) {z : Γ}
    (hz2 : z ^ 2 = 1) (hcomm : ∀ g : Γ, g * z * g⁻¹ * z⁻¹ ∈ O) :
    Subgroup.centralizer ({z} : Set Γ) ⊔ O = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨c, hc, o, ho, hg⟩ :=
    exists_mul_mem_centralizer_of_central_mod_odd hOn hOodd hz2 hcomm g
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right ho)

private theorem relIndex_sup_zpowers_dvd_three {Γ : Type*} [Group Γ] [Finite Γ]
    {C R : Subgroup Γ} (hRle : R ≤ C) (hRc_normal : (R.subgroupOf C).Normal)
    {d : Γ} (hdC : d ∈ C) (hd3 : d ^ 3 = 1) :
    R.relIndex (R ⊔ Subgroup.zpowers d) ∣ 3 := by
  let P : Subgroup Γ := Subgroup.zpowers d
  let D : Subgroup Γ := R ⊔ P
  let Rc : Subgroup ↥C := R.subgroupOf C
  let Pc : Subgroup ↥C := P.subgroupOf C
  haveI : Rc.Normal := hRc_normal
  have hPleC : P ≤ C := Subgroup.zpowers_le.mpr hdC
  have hDleC : D ≤ C := sup_le hRle hPleC
  have hsupc : Pc ⊔ Rc = D.subgroupOf C := by
    rw [← Subgroup.subgroupOf_sup hPleC hRle]
    rw [sup_comm]
  have hrel1 : R.relIndex D = Rc.relIndex (D.subgroupOf C) :=
    (Subgroup.relIndex_subgroupOf (H := R) (K := D) (L := C) hDleC).symm
  have hrel2 : Rc.relIndex (D.subgroupOf C) = Rc.relIndex Pc := by
    rw [← hsupc, Subgroup.relIndex_sup_right (H := Pc) (K := Rc)]
  have hrel3 : Rc.relIndex Pc = R.relIndex P :=
    Subgroup.relIndex_subgroupOf (H := R) (K := P) (L := C) hPleC
  have hdvd : R.relIndex D ∣ Nat.card P := by
    rw [hrel1, hrel2, hrel3]
    exact Subgroup.relIndex_dvd_card (H := R) (K := P)
  have hPcard : Nat.card P = orderOf d := Nat.card_zpowers d
  rw [hPcard] at hdvd
  exact hdvd.trans (orderOf_dvd_of_pow_eq_one hd3)

private theorem exists_elementary_abelian_quotient_of_minimal_normal
    {Γ : Type*} [Group Γ] [Finite Γ] {O M K : Subgroup Γ}
    [hOn : O.Normal] (hOM : O < M) (hMn : M.Normal) (hMK : M ≤ K)
    (hMmin : ∀ N : Subgroup Γ, O < N → N.Normal → N ≤ K → N ≤ M → N = M)
    (hMsolv : Group.IsSolvable ↥M) :
    ∃ (Q : Subgroup (Γ ⧸ O)) (r : ℕ), r.Prime ∧ CFSG.IsElementaryAbelian r Q ∧ Q ≠ ⊥ ∧
      Q = M.map (QuotientGroup.mk' O) ∧ Nat.card M = Nat.card Q * Nat.card O := by
  classical
  let Q : Subgroup (Γ ⧸ O) := M.map (QuotientGroup.mk' O)
  have hQn : Q.Normal := hMn.map _ (QuotientGroup.mk'_surjective O)
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    have hMO : M ≤ O := by
      rw [Subgroup.map_eq_bot_iff] at hQbot
      rwa [QuotientGroup.ker_mk'] at hQbot
    exact (not_lt_of_ge hMO) hOM
  have hMmin' : ∀ N : Subgroup Γ, O < N → N.Normal → N ≤ M → N = M :=
    fun N hON hNn hNM => hMmin N hON hNn (hNM.trans hMK) hNM
  have hQmin : IsMinimalNormal Q := isMinimalNormal_map_mk_of_minimal hOn hMn hOM hMmin'
  have hQsolv : Group.IsSolvable ↥Q := isSolvable_map_mk_quotient hOn hMsolv
  haveI : Q.Normal := hQn
  haveI : IsMinimalNormal Q := hQmin
  haveI : Group.IsSolvable ↥Q := hQsolv
  obtain ⟨r, hr, hQelem⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian Q
  have hMQ : Nat.card M = Nat.card Q * Nat.card O := card_eq_card_map_mk'_mul hOn hOM.le
  exact ⟨Q, r, hr, hQelem, hQne, rfl, hMQ⟩

private theorem eq_two_of_elementary_abelian_of_not_odd {r : ℕ} (hr : r.Prime)
    {Q : Type*} [Group Q] [Finite Q] (hQelem : CFSG.IsElementaryAbelian r Q)
    {m o : ℕ} (hcard : m = Nat.card Q * o) (hodd : Odd o) (hnot : ¬ Odd m) : r = 2 := by
  by_contra hr2
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hQodd : Odd (Nat.card Q) := by
    haveI : Fact (Nat.Prime r) := ⟨hr⟩
    obtain ⟨n, hn⟩ := hQelem.isPGroup.exists_card_eq
    rw [hn]
    exact hrodd.pow
  exact hnot (hcard ▸ hQodd.mul hodd)

theorem exists_odd_normal_centralizer_sup_eq_top {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {K : Subgroup Γ} (hKn : K.Normal) (hKs : Group.IsSolvable K)
    {z : Γ} (hzK : z ∈ K) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ O : Subgroup Γ, O.Normal ∧ O ≤ K ∧ Odd (Nat.card O) ∧
      (∀ g : Γ, g * z * g⁻¹ * z⁻¹ ∈ O) ∧ Subgroup.centralizer ({z} : Set Γ) ⊔ O = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : K.Normal := hKn
  haveI : Group.IsSolvable ↥K := hKs
  obtain ⟨O, hOn, hO_le_K, hOodd, hz_notin_O, hO_max, hOK⟩ :=
    exists_odd_normal_core hKn hzK hz2 hz1
  obtain ⟨M, hOM, hMn, hMK, hMmin⟩ := exists_minimal_normal_above hKn hOK
  have hMsolv : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hMK) (Subgroup.inclusion_injective hMK)
  haveI : O.Normal := hOn
  obtain ⟨Q, r, hr, hQelem, hQne, hQeq, hMQ⟩ :=
    exists_elementary_abelian_quotient_of_minimal_normal hOM hMn hMK hMmin hMsolv
  have hQn : Q.Normal := by
    rw [hQeq]
    exact hMn.map _ (QuotientGroup.mk'_surjective O)
  have hMnotOdd : ¬ Odd (Nat.card M) := fun hModd =>
    (not_lt_of_ge (hO_max M hMn hMK hModd)) hOM
  have hr2 : r = 2 := eq_two_of_elementary_abelian_of_not_odd hr hQelem hMQ hOodd hMnotOdd
  have hQelem2 : CFSG.IsElementaryAbelian 2 Q := hr2 ▸ hQelem
  obtain ⟨m, hmM, hm2, hm1, hm_central, hQeq_m⟩ :=
    exists_central_involution_of_elementary_abelian_two
      hno hOn hOodd hOM.le hQn hQeq hQelem2 hQne
  have hq1 : QuotientGroup.mk' O m ≠ 1 := by
    intro h
    apply hQne
    rw [hQeq_m, h]
    simp
  have hzq1 : QuotientGroup.mk' O z ≠ 1 := by
    intro h
    exact hz_notin_O ((QuotientGroup.eq_one_iff z).mp h)
  obtain ⟨hzm_eq, hcommO⟩ :=
    eq_of_central_mod_odd hno hOn hOodd hz2 hm2 hzq1 hq1 hm_central
  exact ⟨O, hOn, hO_le_K, hOodd, hcommO,
    centralizer_sup_eq_top_of_central_mod_odd hOn hOodd hz2 hcommO⟩

private theorem exists_commuting_involutions_alternating_five :
    ∃ a b : alternatingGroup (Fin 5), a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a * b = b * a ∧ a ≠ b := by
  decide +kernel

private theorem nonempty_mulEquiv_alternating_five_of_inf_ker_eq_bot
    {Γ T : Type*} [Group Γ] [Group T] (π : Γ →* T) {I : Subgroup Γ}
    (hbot : I ⊓ π.ker = ⊥) (hIA5 : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5))) :
    Nonempty (↥I ≃* alternatingGroup (Fin 5)) := by
  classical
  let f : ↥I →* ↥(I.map π) :=
    { toFun := fun x => ⟨π (x : Γ), ⟨(x : Γ), x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxker : (x : Γ) ∈ π.ker := congrArg Subtype.val hx
    have hxmem : (x : Γ) ∈ I ⊓ π.ker := ⟨x.2, hxker⟩
    rw [hbot] at hxmem
    exact Subtype.ext (Subgroup.mem_bot.mp hxmem)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨e5⟩ := hIA5
  exact ⟨(MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).trans e5⟩

private theorem false_of_mulEquiv_alternating_five_noKlein {Γ : Type*} [Group Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {I : Subgroup Γ} (e : ↥I ≃* alternatingGroup (Fin 5)) : False := by
  classical
  obtain ⟨a, b, ha2, hb2, ha1, hb1, hab, hne⟩ :=
    exists_commuting_involutions_alternating_five
  let s : ↥I := e.symm a
  let t : ↥I := e.symm b
  have hs2 : s ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, e.apply_symm_apply, ha2]
  have ht2 : t ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, e.apply_symm_apply, hb2]
  have hs1 : s ≠ 1 := by
    intro h
    apply ha1
    calc a = e s := (e.apply_symm_apply a).symm
      _ = e 1 := by rw [h]
      _ = 1 := map_one e
  have ht1 : t ≠ 1 := by
    intro h
    apply hb1
    calc b = e t := (e.apply_symm_apply b).symm
      _ = e 1 := by rw [h]
      _ = 1 := map_one e
  have hcomm : s * t = t * s := by
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply, hab]
  have hne' : s ≠ t := by
    intro h
    apply hne
    calc a = e s := (e.apply_symm_apply a).symm
      _ = e t := by rw [h]
      _ = b := e.apply_symm_apply b
  have hs2' : (s : Γ) ^ 2 = 1 := by
    simpa using congrArg (fun x : ↥I => (x : Γ)) hs2
  have ht2' : (t : Γ) ^ 2 = 1 := by
    simpa using congrArg (fun x : ↥I => (x : Γ)) ht2
  have hs1' : (s : Γ) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have ht1' : (t : Γ) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hcomm' : (s : Γ) * (t : Γ) = (t : Γ) * (s : Γ) := by
    simpa using congrArg (fun x : ↥I => (x : Γ)) hcomm
  exact hne' (Subtype.ext (hno (s : Γ) (t : Γ) hs2' ht2' hs1' ht1' hcomm'))

private theorem exists_involution_of_nontrivial_two_group {Γ : Type*} [Group Γ] [Finite Γ]
    {P : Subgroup Γ} (hP2 : IsPGroup 2 P) (hPne : P ≠ ⊥) :
    ∃ z ∈ P, z ^ 2 = 1 ∧ z ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_ne_one : Nat.card ↥P ≠ 1 := by
    intro h1
    exact hPne (Subgroup.card_eq_one.mp h1)
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hcard_ne_one (by simpa using hn)
  have h2dvd : 2 ∣ Nat.card ↥P := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2dvd
  refine ⟨x, x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hxord] at this
    simpa using congrArg (fun y : ↥P => (y : Γ)) this
  · intro h
    have hord : orderOf x = 1 := orderOf_eq_one_iff.mpr (Subtype.ext h)
    rw [hord] at hxord
    omega

private theorem eq_of_isInvolution_mem_of_noKlein {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {P : Subgroup Γ} (hP2 : IsPGroup 2 P)
    {z : Γ} (hzP : z ∈ P) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    {w : Γ} (hwP : w ∈ P) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) : w = z := by
  obtain ⟨S, hS⟩ := hP2.exists_le_sylow
  exact eq_of_isInvolution_of_noKlein hno S (hS hwP) (hS hzP) hw2 hz2 hw1 hz1

private theorem le_centralizer_of_unique_involution {Γ T : Type*} [Group Γ] [Group T]
    (π : Γ →* T) {I : Subgroup Γ} {z : Γ} (hzP : z ∈ I ⊓ π.ker)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (huniq : ∀ w ∈ I ⊓ π.ker, w ^ 2 = 1 → w ≠ 1 → w = z) :
    I ≤ Subgroup.centralizer ({z} : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj_mem : g * z * g⁻¹ ∈ I ⊓ π.ker := by
    refine ⟨?_, ?_⟩
    · exact I.mul_mem (I.mul_mem hg hzP.1) (I.inv_mem hg)
    · exact (MonoidHom.normal_ker π).conj_mem z hzP.2 g
  have hconj2 : (g * z * g⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [← pow_two, hz2]; group
  have hconj1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have h' := congrArg (fun w => g⁻¹ * w * g) h
    simpa [mul_assoc] using h'
  have heq := huniq (g * z * g⁻¹) hconj_mem hconj2 hconj1
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [heq]

theorem exists_involution_mem_inf_ker {Γ T : Type*} [Group Γ] [Finite Γ] [Group T] (π : Γ →* T)
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    {I : Subgroup Γ} (hIA5 : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)))
    (hI2 : IsPGroup 2 ↥(I ⊓ π.ker)) :
    ∃ z ∈ I ⊓ π.ker, z ^ 2 = 1 ∧ z ≠ 1 ∧ I ≤ Subgroup.centralizer ({z} : Set Γ) := by
  classical
  by_cases hbot : I ⊓ π.ker = ⊥
  · exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_alternating_five_of_inf_ker_eq_bot π hbot hIA5
    exact false_of_mulEquiv_alternating_five_noKlein hno e
  · obtain ⟨z, hzP, hz2, hz1⟩ := exists_involution_of_nontrivial_two_group hI2 hbot
    have huniq : ∀ w ∈ I ⊓ π.ker, w ^ 2 = 1 → w ≠ 1 → w = z :=
      fun w hw hw2 hw1 =>
        eq_of_isInvolution_mem_of_noKlein hno hI2 hzP hz2 hz1 hw hw2 hw1
    exact ⟨z, hzP, hz2, hz1, le_centralizer_of_unique_involution π hzP hz2 hz1 huniq⟩

private theorem perfectResidual_sup_odd_eq_top {Γ : Type*} [Group Γ] [Finite Γ]
    (hperf : Group.IsPerfect Γ) {C O : Subgroup Γ} [hO : O.Normal] (hCO : C ⊔ O = ⊤) :
    CFSG.inSubgroup CFSG.perfectResidual C ⊔ O = ⊤ := by
  classical
  haveI : Group.IsPerfect Γ := hperf
  let R : Subgroup Γ := CFSG.inSubgroup CFSG.perfectResidual C
  have hCmap : C.map (QuotientGroup.mk' O) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' O)) hCO
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O)] at h
  let f : ↥C →* Γ ⧸ O := (QuotientGroup.mk' O).comp C.subtype
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ C.map (QuotientGroup.mk' O) := by rw [hCmap]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hres' : (CFSG.perfectResidual ↥C).map f = ⊤ := by
    have hres :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image f hf
    rwa [show CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥C =
      CFSG.perfectResidual ↥C from rfl] at hres
  have hRmap : R.map (QuotientGroup.mk' O) = ⊤ := by
    simpa [R, CFSG.inSubgroup, f, Subgroup.map_map] using hres'
  rw [← QuotientGroup.ker_mk' O, ← Subgroup.comap_map_eq, hRmap, Subgroup.comap_top]

private theorem mem_perfectResidual_of_pow_three {Γ : Type*} [Group Γ] [Finite Γ]
    {C O : Subgroup Γ} [hO : O.Normal]
    (hsup : CFSG.inSubgroup CFSG.perfectResidual C ⊔ O = ⊤)
    (hO3 : Nat.Coprime (Nat.card O) 3) {d : Γ} (hdC : d ∈ C) (hd3 : d ^ 3 = 1) :
    d ∈ CFSG.inSubgroup CFSG.perfectResidual C := by
  classical
  let R : Subgroup Γ := CFSG.inSubgroup CFSG.perfectResidual C
  have hRle : R ≤ C := Subgroup.map_subtype_le _
  have hRc_normal : (R.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRle]
    exact (Subgroup.le_normalizer (H := C)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map C
        (CFSG.perfectResidual ↥C)
        CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic)
  have hidx_dvd_O : R.relIndex C ∣ Nat.card O :=
    (Subgroup.relIndex_dvd_index_of_le hRle).trans
      (CFSG.GroupTheory.WielandtProduct.index_dvd_card_of_sup_eq_top hsup)
  have hcop : Nat.Coprime (R.relIndex C) 3 :=
    Nat.Coprime.coprime_dvd_left hidx_dvd_O hO3
  let P : Subgroup Γ := Subgroup.zpowers d
  let D : Subgroup Γ := R ⊔ P
  have hDleC : D ≤ C := sup_le hRle (Subgroup.zpowers_le.mpr hdC)
  have hRD : R ≤ D := le_sup_left
  have hDcube : R.relIndex D ∣ 3 := by
    simpa [D, P] using relIndex_sup_zpowers_dvd_three hRle hRc_normal hdC hd3
  have hRD_dvd : R.relIndex D ∣ R.relIndex C :=
    ⟨D.relIndex C,
      (Subgroup.relIndex_mul_relIndex (H := R) (K := D) (L := C) hRD hDleC).symm⟩
  have hcopD : Nat.Coprime (R.relIndex D) 3 :=
    Nat.Coprime.coprime_dvd_left hRD_dvd hcop
  have hone : R.relIndex D = 1 := hcopD.eq_one_of_dvd hDcube
  have hDR : D ≤ R := Subgroup.relIndex_eq_one.mp hone
  exact hDR (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))

theorem mem_perfectResidual_of_sup_eq_top {Γ : Type*} [Group Γ] [Finite Γ]
    (hperf : Group.IsPerfect Γ) {C O : Subgroup Γ} (hO : O.Normal) (hCO : C ⊔ O = ⊤)
    (hO3 : Nat.Coprime (Nat.card O) 3) :
    CFSG.inSubgroup CFSG.perfectResidual C ⊔ O = ⊤ ∧
      ∀ d ∈ C, d ^ 3 = 1 → d ∈ CFSG.inSubgroup CFSG.perfectResidual C := by
  haveI : O.Normal := hO
  refine ⟨perfectResidual_sup_odd_eq_top hperf hCO, fun d hdC hd3 => ?_⟩
  exact mem_perfectResidual_of_pow_three (perfectResidual_sup_odd_eq_top hperf hCO) hO3 hdC hd3

end CFSG.RankThree.PartTwo.Sec16.Kcd166

end
