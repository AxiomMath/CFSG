module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLie
public import CFSG.Quasithin.Background.GoldschmidtB69DeepG2Aux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_three_dvd_of_isHat {X S : Type} [Group X] [Group S] (h : IsHat X S) :
    3 ∣ Nat.card X :=
  h.2.1 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center X)

private lemma s16h_card_eq_of_surjective_simple {D H : Type*} [Group D] [Group H]
    (hD : IsSimpleGroup D) (hH : Nontrivial H) (π : D →* H) (hπ : Function.Surjective π) :
    Nat.card H = Nat.card D := by
  have hker : MonoidHom.ker π = ⊥ := by
    rcases hD.eq_bot_or_eq_top_of_normal (MonoidHom.ker π) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hH.exists_pair_ne
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      have hx : x ∈ MonoidHom.ker π := by rw [h]; exact Subgroup.mem_top x
      have hy : y ∈ MonoidHom.ker π := by rw [h]; exact Subgroup.mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      exact hab (hx.trans hy.symm)
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
  exact (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)).symm

private abbrev s16h_m22A : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

private abbrev s16h_m22B : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

private abbrev s16h_m22Word : Equiv.Perm (Fin 22) :=
  s16h_m22A * s16h_m22B * s16h_m22A * s16h_m22B * s16h_m22A * s16h_m22B⁻¹ * s16h_m22A *
    s16h_m22B⁻¹

private lemma s16h_m22_word_pow_three : s16h_m22Word ^ 3 = 1 ∧ s16h_m22Word ≠ 1 := by
  decide +kernel

private lemma s16h_m22_word_mem : s16h_m22Word ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  have ha : s16h_m22A ∈ CFSG.Blueprint.NativeSporadic.M22 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : s16h_m22B ∈ CFSG.Blueprint.NativeSporadic.M22 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbi := inv_mem hb
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) ha) hb) ha) hbi)
    ha) hbi

private lemma s16h_three_dvd_card_of_mulEquiv_subgroup {α G : Type*} [Group α] [Group G]
    {H : Subgroup α} (e : G ≃* H) {w : α} (hw : w ∈ H) (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    3 ∣ Nat.card G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (⟨w, hw⟩ : H) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using h3)) fun h => h1 (congrArg Subtype.val h)
  rw [← ho, ← MulEquiv.orderOf_eq e.symm]
  exact orderOf_dvd_natCard _

theorem s16h_three_dvd_of_isSpor_m22 {X : Type} [Group X] (h : UC22.IsSpor X .M22) :
    3 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  exact s16h_three_dvd_card_of_mulEquiv_subgroup e s16h_m22_word_mem
    s16h_m22_word_pow_three.1 s16h_m22_word_pow_three.2

section Modules

variable {W : Type} [CommGroup W]

theorem s16h_three_dvd_of_g2NaturalDerived
    {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} (hH : CFSG.Open.IsQuasisimple ↥H) (h : G2NaturalDerived H U Z 1) :
    3 ∣ Nat.card ↥H := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := h
  letI := hKf
  letI := hKfin
  obtain ⟨π, hπ⟩ := hreal
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨hDsimple, hDcard⟩ := CFSG.Quasithin.B69.g2Derived_simple_card (K := K) hK2
  have hHnt : Nontrivial ↥H := s16h_nontrivial_of_isQuasisimple hH
  have hcard := s16h_card_eq_of_surjective_simple hDsimple hHnt π hπ.1
  rw [hcard, hDcard]
  norm_num

theorem s16h_three_dvd_of_tripleA6Six {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hH : CFSG.Open.IsQuasisimple ↥H) (h : TripleA6Six H U Z) : 3 ∣ Nat.card ↥H := by
  obtain ⟨K, hKf, hKfin, Γ₀, hKcard, hdet, hHat, hcenter, hreal⟩ := h
  letI := hKf
  letI := hKfin
  obtain ⟨π₀, hπ₀⟩ := hreal
  let π : ↥Γ₀ →* ↥H := π₀
  have hsurj : Function.Surjective π := hπ₀.1
  have hNnormal : (MonoidHom.ker π).Normal := MonoidHom.normal_ker π
  have hmapnormal : ((MonoidHom.ker π).map (QuotientGroup.mk' (Subgroup.center ↥Γ₀))).Normal :=
    hNnormal.map _ (QuotientGroup.mk'_surjective _)
  have hQsimple : IsSimpleGroup (↥Γ₀ ⧸ Subgroup.center ↥Γ₀) := hHat.1.2.1
  haveI := hmapnormal
  rcases hQsimple.eq_bot_or_eq_top_of_normal
      ((MonoidHom.ker π).map (QuotientGroup.mk' (Subgroup.center ↥Γ₀))) with hbot | htop
  · have hNle : MonoidHom.ker π ≤ Subgroup.center ↥Γ₀ := by
      have h : MonoidHom.ker π ≤ (QuotientGroup.mk' (Subgroup.center ↥Γ₀)).ker :=
        (Subgroup.map_eq_bot_iff (MonoidHom.ker π)).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    have hQcard : Nat.card (↥Γ₀ ⧸ Subgroup.center ↥Γ₀) = 360 := by
      obtain ⟨e⟩ := hHat.2.2
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have h1 : 3 ∣ (Subgroup.center ↥Γ₀).index := by
      rw [Subgroup.index_eq_card, hQcard]
      norm_num
    have h2 : (Subgroup.center ↥Γ₀).index ∣ (MonoidHom.ker π).index :=
      Subgroup.index_dvd_of_le hNle
    have h3 : (MonoidHom.ker π).index = Nat.card ↥H := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hsurj).toEquiv
    have h := h1.trans h2
    rwa [h3] at h
  · exfalso
    have hsup : MonoidHom.ker π ⊔ Subgroup.center ↥Γ₀ = ⊤ := by
      rw [sup_comm, ← QuotientGroup.comap_map_mk' (Subgroup.center ↥Γ₀) (MonoidHom.ker π), htop]
      simp
    have hZcomm : IsMulCommutative ↥(Subgroup.center ↥Γ₀) := inferInstance
    have hcomm : commutator ↥Γ₀ ≤ MonoidHom.ker π :=
      hNnormal.commutator_le_of_self_sup_commutative_eq_top hsup hZcomm
    have hkertop : MonoidHom.ker π = ⊤ := by
      rw [eq_top_iff, ← hHat.1.1.commutator_eq_top]
      exact hcomm
    obtain ⟨a, b, hab⟩ := (s16h_nontrivial_of_isQuasisimple hH).exists_pair_ne
    obtain ⟨x, hx⟩ := hsurj a
    obtain ⟨y, hy⟩ := hsurj b
    have hx1 : π x = 1 :=
      MonoidHom.mem_ker.mp (by rw [hkertop]; exact Subgroup.mem_top x)
    have hy1 : π y = 1 :=
      MonoidHom.mem_ker.mp (by rw [hkertop]; exact Subgroup.mem_top y)
    exact hab (by rw [← hx, hx1, ← hy, hy1])

theorem s16h_three_dvd_of_a7Four {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hH : CFSG.Open.IsQuasisimple ↥H) (h : A7Four H U Z) : 3 ∣ Nat.card ↥H := by
  obtain ⟨α, π, hπ⟩ := h
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  have hHnt : Nontrivial ↥H := s16h_nontrivial_of_isQuasisimple hH
  have hcard := s16h_card_eq_of_surjective_simple hsimple hHnt π hπ.1
  rw [hcard, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem s16h_three_dvd_of_sumOfAtMostThreeNat {A L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hc : IsComponentOf L A) (h : SumOfAtMostThreeNat L U Z) : 3 ∣ Nat.card ↥L := by
  have hq := hc.2.2
  obtain ⟨k, hk, n, h | h | h | h | h⟩ := h
  · exact s16h_three_dvd_of_isSLn hq h.1
  · exact s16h_three_dvd_of_isSpn hq h.1
  · exact s16h_three_dvd_of_isOmegaPlus hq h.1
  · exact s16h_three_dvd_of_isOmegaMinus hq h.1
  · exact s16h_three_dvd_of_isAlt hq h.1

theorem s16h_three_dvd_of_conc4_135
    {A H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {m : ℕ} (hc : IsComponentOf H A) (h : Conc4_135 H U Z m) :
    3 ∣ Nat.card ↥H := by
  have hq := hc.2.2
  rcases h with
    ⟨n, h | h | h | h⟩ | ⟨n, h | h | h | h | h⟩ | h | h | ⟨⟨S, hSgrp, hlie, hhat⟩, hm⟩ |
      ⟨n, halt, hnat⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact s16h_three_dvd_of_isSLn hq h.1
  · exact s16h_three_dvd_of_isSpn hq h.1
  · exact s16h_three_dvd_of_isOmegaPlus hq h.1
  · exact s16h_three_dvd_of_isOmegaMinus hq h.1
  · exact s16h_three_dvd_of_isSLn hq h.1
  · exact s16h_three_dvd_of_isSpn hq h.1
  · exact s16h_three_dvd_of_isOmegaPlus hq h.1
  · exact s16h_three_dvd_of_isOmegaMinus hq h.1
  · exact s16h_three_dvd_of_isSUn hq h.1
  · exact s16h_three_dvd_of_g2NaturalDerived hq h
  · exact s16h_three_dvd_of_tripleA6Six hq h
  · exact s16h_three_dvd_of_isHat hhat
  · exact s16h_three_dvd_of_isAlt hq halt
  · exact s16h_three_dvd_of_a7Four hq h
  · exact s16h_three_dvd_of_isSpn hq h
  · exact s16h_three_dvd_of_isLn h
  · exact s16h_three_dvd_of_isSpor_m22 h
  · exact s16h_three_dvd_of_isLn h
  · exact s16h_three_dvd_of_isLn (n := 3) (a := 1) h

end Modules

theorem s16h_three_dvd_of_lieFactor {K : Type} [Group K]
    (h : IsL3 K 1 ∨ UC22.IsL2 K 2 ∨ UC22.IsL2 K 3) : 3 ∣ Nat.card K := by
  rcases h with h | h | h
  · exact s16h_three_dvd_of_isLn (n := 3) (a := 1) h
  · exact s16h_three_dvd_of_isLn (n := 2) (a := 2) h
  · exact s16h_three_dvd_of_isLn (n := 2) (a := 3) h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo