module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

import CFSG.GroupTheory.HuppertProduct.RankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

variable {X : Type} [Group X] [Finite X]

private theorem three_smul_zmod_three_pow_one (z : ZMod (3 ^ 1)) : (3 : ℕ) • z = 0 := by
  rw [nsmul_eq_mul]
  have h : ((3 : ℕ) : ZMod (3 ^ 1)) = 0 := ZMod.natCast_self (3 ^ 1)
  rw [h, zero_mul]

private theorem base_one_eq_omegaBase : base 1 = omegaBase 1 := by
  refine le_antisymm ?_ omegaBase_le_base
  intro x hx
  obtain ⟨a, b, c, rfl⟩ := exists_el_of_mem_base hx
  rw [el_mem_omegaBase_iff]
  exact ⟨three_smul_zmod_three_pow_one a, three_smul_zmod_three_pow_one b,
    three_smul_zmod_three_pow_one c⟩

private theorem el_one_zero_zero_mem_omegaBase : el 1 1 0 0 0 ∈ omegaBase 1 := by
  rw [el_mem_omegaBase_iff]
  decide

private theorem omegaBase_one_normal : (omegaBase 1).Normal := by
  rw [← base_one_eq_omegaBase]
  exact base_normal 1

private theorem center_pow_three_eq_one {z : ZWr 1} (hz : z ∈ Subgroup.center (ZWr 1)) :
    z ^ 3 = 1 := by
  have hcard : Nat.card (Subgroup.center (ZWr 1)) = 3 := by
    simpa using card_center (n := 1) le_rfl
  have h : (⟨z, hz⟩ : Subgroup.center (ZWr 1)) ^ Nat.card (Subgroup.center (ZWr 1)) = 1 :=
    pow_card_eq_one'
  rw [hcard] at h
  simpa using congrArg Subtype.val h

private theorem commutator_el_one_not_mem_center {y : ZWr 1} (hy : y ∉ base 1) :
    el 1 1 0 0 0 * y * (el 1 1 0 0 0)⁻¹ * y⁻¹ ∉ Subgroup.center (ZWr 1) := by
  intro hmem
  obtain ⟨A, B, C, s, rfl⟩ : ∃ A B C s, y = el 1 A B C s := ⟨_, _, _, _, el_eta y⟩
  have hs : s ≠ 0 := by
    intro h0
    exact hy ((el_mem_base_iff A B C s).mpr h0)
  rcases zmod3_cases s with h | h | h
  · exact hs h
  · rw [h, commutator_base_one, center_eq_diag (n := 1) le_rfl, el_mem_diagSub_iff] at hmem
    exact one_ne_neg_one_zmod (n := 1) le_rfl hmem.1
  · rw [h, commutator_base_two, center_eq_diag (n := 1) le_rfl, el_mem_diagSub_iff] at hmem
    exact one_ne_zero_zmod (n := 1) le_rfl hmem.1

private theorem le_center_of_le_omegaBase_of_isCyclic {U : Subgroup (ZWr 1)}
    (hU : U ≤ omegaBase 1) (hUn : U.Normal) (hcyc : IsCyclic ↥U) :
    U ≤ Subgroup.center (ZWr 1) := by
  have hcard3 : Nat.card U ≤ 3 :=
    CFSG.GroupTheory.HuppertProduct.card_le_three_of_isCyclic hcyc le_rfl
      (fun e he => (hU he).2)
  obtain ⟨h1, h2, huni⟩ := zwr_A_uniserial_Zwr (n := 1) le_rfl
  rcases huni U hU hUn with h | h | h | h
  · rw [h]
    exact bot_le
  · rw [h]
    exact inf_le_right
  · exfalso
    rw [h, h2] at hcard3
    omega
  · exfalso
    rw [h, card_omegaBase (n := 1) le_rfl] at hcard3
    omega

private theorem le_or_le_of_le_omegaBase_of_normal {U V : Subgroup (ZWr 1)}
    (hU : U ≤ omegaBase 1) (hV : V ≤ omegaBase 1)
    (hUn : U.Normal) (hVn : V.Normal) : U ≤ V ∨ V ≤ U := by
  have hZle : Subgroup.center (ZWr 1) ≤ Subgroup.upperCentralSeries (ZWr 1) 2 := by
    rw [← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono (ZWr 1) (by norm_num : 1 ≤ 2)
  have h12 : omegaBase 1 ⊓ Subgroup.center (ZWr 1) ≤
      omegaBase 1 ⊓ Subgroup.upperCentralSeries (ZWr 1) 2 :=
    inf_le_inf_left _ hZle
  have h1 := (zwr_A_uniserial_Zwr (n := 1) le_rfl).2.2 U hU hUn
  have h2 := (zwr_A_uniserial_Zwr (n := 1) le_rfl).2.2 V hV hVn
  rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl
  all_goals
    first
    | exact Or.inl bot_le
    | exact Or.inr bot_le
    | exact Or.inl le_rfl
    | exact Or.inl inf_le_left
    | exact Or.inr inf_le_left
    | exact Or.inl h12
    | exact Or.inr h12

private theorem le_of_le_omegaBase_of_not_le_omegaBase {M N : Subgroup (ZWr 1)}
    (hNn : N.Normal) (hc : M ≤ Subgroup.centralizer (N : Set (ZWr 1)))
    (hM : M ≤ omegaBase 1) (hN : ¬ N ≤ omegaBase 1) : M ≤ N := by
  rw [SetLike.le_def] at hN
  push Not at hN
  obtain ⟨y, hyN, hyA⟩ := hN
  have hybase : y ∉ base 1 := by rwa [← base_one_eq_omegaBase] at hyA
  have hMZ : M ≤ Subgroup.center (ZWr 1) := by
    intro z hz
    have hzcent : z ∈ Subgroup.centralizer ({y} : Set (ZWr 1)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact Subgroup.mem_centralizer_iff.mp (hc hz) y hyN
    have hzdiag := centralizer_base_le_diag hybase ⟨hzcent, omegaBase_le_base (hM hz)⟩
    rwa [center_eq_diag (n := 1) le_rfl]
  by_cases hbot : M = ⊥
  · rw [hbot]
    exact bot_le
  · have hNne : N ≠ ⊥ := by
      intro h
      have hymem : y ∈ (⊥ : Subgroup (ZWr 1)) := h ▸ hyN
      have hy1 : y = 1 := by simpa using hymem
      exact hyA (hy1 ▸ (omegaBase 1).one_mem)
    have hZle : Subgroup.center (ZWr 1) ≤ N := by
      intro z hz
      exact zwr_normal_contains_omega_center_Zwr (n := 1) le_rfl hNn hNne z hz
        (center_pow_three_eq_one hz)
    exact hMZ.trans hZle

private theorem false_of_not_le_omegaBase_of_both {M N : Subgroup (ZWr 1)}
    (hMn : M.Normal) (hc : M ≤ Subgroup.centralizer (N : Set (ZWr 1)))
    (hM : ¬ M ≤ omegaBase 1) (hN : ¬ N ≤ omegaBase 1) : False := by
  rw [SetLike.le_def] at hM hN
  push Not at hM hN
  obtain ⟨y, hyM, hyA⟩ := hM
  obtain ⟨y', hy'N, hy'A⟩ := hN
  have hybase : y ∉ base 1 := by rwa [← base_one_eq_omegaBase] at hyA
  have hy'base : y' ∉ base 1 := by rwa [← base_one_eq_omegaBase] at hy'A
  have hAn : (omegaBase 1).Normal := omegaBase_one_normal
  have hKZ : M ⊓ omegaBase 1 ≤ Subgroup.center (ZWr 1) := by
    intro z hz
    obtain ⟨hzM, hzA⟩ := Subgroup.mem_inf.mp hz
    have hzcent : z ∈ Subgroup.centralizer ({y'} : Set (ZWr 1)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact Subgroup.mem_centralizer_iff.mp (hc hzM) y' hy'N
    have hzdiag := centralizer_base_le_diag hy'base ⟨hzcent, omegaBase_le_base hzA⟩
    rwa [center_eq_diag (n := 1) le_rfl]
  have ha0 : el 1 1 0 0 0 ∈ omegaBase 1 := el_one_zero_zero_mem_omegaBase
  have hcM : el 1 1 0 0 0 * y * (el 1 1 0 0 0)⁻¹ * y⁻¹ ∈ M := by
    have h1 := hMn.conj_mem y hyM (el 1 1 0 0 0)
    exact Subgroup.mul_mem M h1 (Subgroup.inv_mem M hyM)
  have hcA : el 1 1 0 0 0 * y * (el 1 1 0 0 0)⁻¹ * y⁻¹ ∈ omegaBase 1 := by
    have h1 := hAn.conj_mem (el 1 1 0 0 0)⁻¹ (Subgroup.inv_mem _ ha0) y
    have h2 := Subgroup.mul_mem _ ha0 h1
    simpa [mul_assoc] using h2
  exact commutator_el_one_not_mem_center hybase (hKZ (Subgroup.mem_inf.mpr ⟨hcM, hcA⟩))

private theorem le_or_le_of_normal_of_le_centralizer_ZWr_one {N₁ N₂ : Subgroup (ZWr 1)}
    (hN₁ : N₁.Normal) (hN₂ : N₂.Normal)
    (hc : N₁ ≤ Subgroup.centralizer (N₂ : Set (ZWr 1))) :
    N₁ ≤ N₂ ∨ N₂ ≤ N₁ := by
  have hc' : N₂ ≤ Subgroup.centralizer (N₁ : Set (ZWr 1)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hc hy) x hx).symm
  by_cases hA₁ : N₁ ≤ omegaBase 1
  · by_cases hA₂ : N₂ ≤ omegaBase 1
    · exact le_or_le_of_le_omegaBase_of_normal hA₁ hA₂ hN₁ hN₂
    · exact Or.inl (le_of_le_omegaBase_of_not_le_omegaBase hN₂ hc hA₁ hA₂)
  · by_cases hA₂ : N₂ ≤ omegaBase 1
    · exact Or.inr (le_of_le_omegaBase_of_not_le_omegaBase hN₁ hc' hA₂ hA₁)
    · exact False.elim (false_of_not_le_omegaBase_of_both hN₁ hc hA₁ hA₂)

private theorem le_center_of_normal_of_isCyclic_inf_ZWr_one {N : Subgroup (ZWr 1)}
    (hN : N.Normal) (hcyc : IsCyclic ↥(N ⊓ omegaBase 1)) :
    N ≤ Subgroup.center (ZWr 1) := by
  have hAn : (omegaBase 1).Normal := omegaBase_one_normal
  haveI : N.Normal := hN
  haveI : (omegaBase 1).Normal := hAn
  by_cases hNA : N ≤ omegaBase 1
  · have hcyc' : IsCyclic ↥N := by rwa [inf_eq_left.mpr hNA] at hcyc
    exact le_center_of_le_omegaBase_of_isCyclic hNA hN hcyc'
  rw [SetLike.le_def] at hNA
  push Not at hNA
  obtain ⟨y, hyN, hyA⟩ := hNA
  have hybase : y ∉ base 1 := by rwa [← base_one_eq_omegaBase] at hyA
  have hKZ : N ⊓ omegaBase 1 ≤ Subgroup.center (ZWr 1) :=
    le_center_of_le_omegaBase_of_isCyclic inf_le_right inferInstance hcyc
  have ha0 : el 1 1 0 0 0 ∈ omegaBase 1 := el_one_zero_zero_mem_omegaBase
  have hcN : el 1 1 0 0 0 * y * (el 1 1 0 0 0)⁻¹ * y⁻¹ ∈ N := by
    have h1 := hN.conj_mem y hyN (el 1 1 0 0 0)
    exact Subgroup.mul_mem N h1 (Subgroup.inv_mem N hyN)
  have hcA : el 1 1 0 0 0 * y * (el 1 1 0 0 0)⁻¹ * y⁻¹ ∈ omegaBase 1 := by
    have h1 := hAn.conj_mem (el 1 1 0 0 0)⁻¹ (Subgroup.inv_mem _ ha0) y
    have h2 := Subgroup.mul_mem _ ha0 h1
    simpa [mul_assoc] using h2
  exact absurd (hKZ (Subgroup.mem_inf.mpr ⟨hcN, hcA⟩))
    (commutator_el_one_not_mem_center hybase)

private theorem le_or_le_of_normal_of_le_centralizer_mulEquiv {P : Type*} [Group P] [Finite P]
    (e : P ≃* ZWr 1) {N₁ N₂ : Subgroup P} (hN₁ : N₁.Normal) (hN₂ : N₂.Normal)
    (hc : N₁ ≤ Subgroup.centralizer (N₂ : Set P)) : N₁ ≤ N₂ ∨ N₂ ≤ N₁ := by
  have hM₁n : (N₁.map e.toMonoidHom).Normal := hN₁.map e.toMonoidHom e.surjective
  have hM₂n : (N₂.map e.toMonoidHom).Normal := hN₂.map e.toMonoidHom e.surjective
  have hc' : N₁.map e.toMonoidHom ≤
      Subgroup.centralizer ((N₂.map e.toMonoidHom : Subgroup (ZWr 1)) : Set (ZWr 1)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    simpa using congrArg e (Subgroup.mem_centralizer_iff.mp (hc ha) b hb)
  rcases le_or_le_of_normal_of_le_centralizer_ZWr_one hM₁n hM₂n hc' with h | h
  · left
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem e.toMonoidHom hx))
    have hyx' : y = x := e.injective hyx
    simpa [hyx'] using hy
  · right
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem e.toMonoidHom hx))
    have hyx' : y = x := e.injective hyx
    simpa [hyx'] using hy

private theorem le_center_of_normal_of_isCyclic_inf_mulEquiv {P : Type*} [Group P] [Finite P]
    (e : P ≃* ZWr 1) {A N : Subgroup P} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hN : N.Normal) (hcyc : IsCyclic ↥(N ⊓ A)) :
    N ≤ Subgroup.center P := by
  have hBcard : Nat.card (A.map e.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (K := A) (f := e.toMonoidHom) e.injective, hA27]
  have hB : A.map e.toMonoidHom = omegaBase 1 :=
    unique_omegaBase (n := 1) (by norm_num) (hA.map e.toMonoidHom) hBcard
  have hMn : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  have hcyc' : IsCyclic ↥(N.map e.toMonoidHom ⊓ omegaBase 1) := by
    rw [← hB, ← Subgroup.map_inf N A e.toMonoidHom e.injective]
    haveI : IsCyclic ↥(N ⊓ A) := hcyc
    let φ := Subgroup.equivMapOfInjective (N ⊓ A) e.toMonoidHom e.injective
    exact isCyclic_of_injective φ.symm.toMonoidHom φ.symm.injective
  have hMZ : N.map e.toMonoidHom ≤ Subgroup.center (ZWr 1) :=
    le_center_of_normal_of_isCyclic_inf_ZWr_one hMn hcyc'
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  have hxM : e x ∈ N.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hx
  have hcomm : e y * e x = e x * e y := Subgroup.mem_center_iff.mp (hMZ hxM) (e y)
  simpa using hcomm

theorem le_or_le_of_le_centralizer_of_zwr {P N₁ N₂ : Subgroup X}
    (hP : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (h₁ : N₁ ≤ P) (h₂ : N₂ ≤ P)
    (hn₁ : P ≤ Subgroup.normalizer (N₁ : Set X)) (hn₂ : P ≤ Subgroup.normalizer (N₂ : Set X))
    (hc : N₁ ≤ Subgroup.centralizer (N₂ : Set X)) : N₁ ≤ N₂ ∨ N₂ ≤ N₁ := by
  classical
  obtain ⟨e⟩ := hP
  have hN₁' : (N₁.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h₁).mpr hn₁
  have hN₂' : (N₂.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h₂).mpr hn₂
  have hc' : N₁.subgroupOf P ≤
      Subgroup.centralizer ((N₂.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_subgroupOf.mp hx)) y.val
      (Subgroup.mem_subgroupOf.mp hy)
  rcases le_or_le_of_normal_of_le_centralizer_mulEquiv e hN₁' hN₂' hc' with h | h
  · left
    calc N₁ = (N₁.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le h₁).symm
      _ ≤ (N₂.subgroupOf P).map P.subtype := Subgroup.map_mono h
      _ = N₂ := Subgroup.map_subgroupOf_eq_of_le h₂
  · right
    calc N₂ = (N₂.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le h₂).symm
      _ ≤ (N₁.subgroupOf P).map P.subtype := Subgroup.map_mono h
      _ = N₁ := Subgroup.map_subgroupOf_eq_of_le h₁

theorem le_centralizer_of_isCyclic_inf_of_zwr {P A N : Subgroup X}
    (hP : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hAP : A ≤ P) (hN : N ≤ P)
    (hn : P ≤ Subgroup.normalizer (N : Set X)) (hcyc : IsCyclic ↥(N ⊓ A)) :
    N ≤ Subgroup.centralizer (P : Set X) := by
  classical
  obtain ⟨e⟩ := hP
  let N' : Subgroup ↥P := N.subgroupOf P
  let A' : Subgroup ↥P := A.subgroupOf P
  have hN' : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hn
  have hA'el : CFSG.Open.IsElemAbelian 3 A' := hA.subgroupOf P
  have hA'27 : Nat.card A' = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hA27]
  have hcyc' : IsCyclic ↥(N' ⊓ A') := by
    have hinf : N' ⊓ A' = (N ⊓ A).subgroupOf P := by
      ext x
      simp [N', A', Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hinf]
    haveI : IsCyclic ↥(N ⊓ A) := hcyc
    exact isCyclic_of_injective
      (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hAP)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hAP)).injective
  have hcent' : N' ≤ Subgroup.center ↥P :=
    le_center_of_normal_of_isCyclic_inf_mulEquiv e hA'el hA'27 hN' hcyc'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hx' : (⟨x, hN hx⟩ : ↥P) ∈ N' := Subgroup.mem_subgroupOf.mpr hx
  have hcomm := Subgroup.mem_center_iff.mp (hcent' hx') (⟨y, hy⟩ : ↥P)
  exact congrArg Subtype.val hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen
