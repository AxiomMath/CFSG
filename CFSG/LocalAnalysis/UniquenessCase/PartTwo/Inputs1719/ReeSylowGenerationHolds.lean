module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunRank
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman
public import CFSG.ClassicalInvolution.Orders.Ree
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.LiteratureLocal
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

theorem k_ReeSylowGeneration_holds :
    K_ReeSylowGeneration := by
  unfold K_ReeSylowGeneration
  intro X _ _ q n hRee hq hn1
  obtain ⟨n', hq', hmodel⟩ := hRee
  have hexp : 2 * n' + 1 = 2 * n + 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hq'.symm.trans hq)
  have hn' : n' = n := by omega
  rw [hn'] at hmodel
  have hR : ReeTitsModel X .twistedG2 3 (2 * n + 1) :=
    (hmodel.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨-, -, -, -, hcardX⟩ :=
    CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hR
  have hsimpleX : IsSimpleGroup X :=
    (CFSG.LieType.Simplicity.fam_2g2_simplicity X 3 (2 * n + 1) hR).2
  obtain ⟨-, hinv, hcen, hcoat, hout⟩ :=
    ward_kleidman_small_Ree_involution_centralizer_maximal n hn1 X hR
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h5 : 5 ≤ 3 ^ (2 * n + 1) := by
    calc
      5 ≤ 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have lie_of_psl : ∀ (L : Subgroup X),
      Nonempty (↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 3 (2 * n + 1))) →
      CFSG.Blueprint.LieModel ↥L .PSL 2 3 (2 * n + 1) := by
    intro L hL
    obtain ⟨e⟩ := hL
    exact Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv
        ↥L 3 (2 * n + 1) h5 e⟩
  have perf_of_psl : ∀ (L : Subgroup X),
      Nonempty (↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 3 (2 * n + 1))) → Group.IsPerfect ↥L := by
    intro L hL
    obtain ⟨e⟩ := hL
    have hcardF : 3 < Nat.card (GaloisField 3 (2 * n + 1)) := by
      rw [GaloisField.card 3 (2 * n + 1) (by omega)]
      calc
        3 < 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hPSL : Group.IsPerfect
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 (2 * n + 1))) :=
      CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three
        (GaloisField 3 (2 * n + 1)) hcardF
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have isL2_of_psl : ∀ (L : Subgroup X),
      Nonempty (↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 3 (2 * n + 1))) → IsL2Over17 ↥L q := by
    intro L hL
    exact ⟨3, 2 * n + 1, by norm_num, by norm_num, hq, by omega, lie_of_psl L hL⟩
  obtain ⟨x0, hx0⟩ := hinv.1
  obtain ⟨L0, hL0C, hL0inf, hL0sup, ⟨eL0⟩, hZL0⟩ := hcen x0 hx0
  have hZX_le : Subgroup.center X ≤ Subgroup.zpowers x0 := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer ({x0} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hz x0).symm
    have hzZ : (⟨z, hzC⟩ : Subgroup.centralizer ({x0} : Set X)) ∈
        Subgroup.center (Subgroup.centralizer ({x0} : Set X)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hz (g : X))
    have hmem : z ∈ (Subgroup.center (Subgroup.centralizer ({x0} : Set X))).map
        (Subgroup.centralizer ({x0} : Set X)).subtype :=
      Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, hzZ, rfl⟩
    rwa [hZL0] at hmem
  have hx0_not_center : x0 ∉ Subgroup.center X := by
    intro hx0Z
    have htop : Subgroup.centralizer ({x0} : Set X) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hx0Z g)
    exact (hcoat x0 hx0).1 htop
  have hZX_ne : Subgroup.center X ≠ Subgroup.zpowers x0 := by
    intro h
    exact hx0_not_center (h ▸ Subgroup.mem_zpowers x0)
  have hZX_bot : Subgroup.center X = ⊥ := by
    have hcardX0 : Nat.card (Subgroup.zpowers x0) = 2 := by
      rw [Nat.card_zpowers, hx0]
    have hfact : Fact (Nat.Prime (Nat.card (Subgroup.zpowers x0))) :=
      ⟨by rw [hcardX0]; exact Nat.prime_two⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
        ((Subgroup.center X).subgroupOf (Subgroup.zpowers x0)) with h | h
    · rw [eq_bot_iff]
      intro z hz
      have hz' : (⟨z, hZX_le hz⟩ : Subgroup.zpowers x0) ∈
          (Subgroup.center X).subgroupOf (Subgroup.zpowers x0) := hz
      rw [h, Subgroup.mem_bot] at hz'
      exact Subtype.ext_iff.mp hz'
    · exfalso
      have htop : Subgroup.zpowers x0 ≤ Subgroup.center X :=
        (Subgroup.subgroupOf_eq_top).mp h
      exact hZX_ne (le_antisymm hZX_le htop)
  have derived_eq : ∀ (z : X) (hz : orderOf z = 2) (L : Subgroup X),
      L ≤ Subgroup.centralizer ({z} : Set X) →
      Subgroup.zpowers z ⊔ L = Subgroup.centralizer ({z} : Set X) →
      Nonempty (↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 3 (2 * n + 1))) →
      ⁅Subgroup.centralizer ({z} : Set X), Subgroup.centralizer ({z} : Set X)⁆ = L := by
    intro z hz L hLC hsup hL
    have hperf : Group.IsPerfect ↥L := perf_of_psl L hL
    apply le_antisymm
    · rw [← hsup]
      have hTT : ∀ a ∈ Subgroup.zpowers z, ∀ a' ∈ Subgroup.zpowers z,
          Commute a a' := by
        intro a ha a' ha'
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
        exact Commute.zpow_zpow_self z m k
      have hTL : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ L, Commute a b := by
        intro a ha b hb
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact Commute.zpow_left
          (show Commute z b from
            (Subgroup.mem_centralizer_singleton_iff.mp (hLC hb)).symm) m
      calc
        ⁅Subgroup.zpowers z ⊔ L, Subgroup.zpowers z ⊔ L⁆ ≤ ⁅L, L⁆ :=
          CFSG.commutator_sup_le_commutator_right hTT hTL
        _ = L := Subgroup.isPerfect_iff.mp hperf
    · calc
        L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
        _ ≤ ⁅Subgroup.centralizer ({z} : Set X),
            Subgroup.centralizer ({z} : Set X)⁆ :=
          Subgroup.commutator_mono (hsup ▸ le_sup_right) (hsup ▸ le_sup_right)
  have pcore_bot_of_simple : ∀ (L : Subgroup X), IsSimpleGroup ↥L →
      Group.IsPerfect ↥L → CFSG.pCore 2 ↥L = ⊥ := by
    intro L hsimple hperf
    rcases hsimple.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥L) with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 (⊤ : Subgroup ↥L) := by
        rw [← h]
        exact CFSG.pCore_isPGroup
      have hnil : Group.IsNilpotent ↥L := (hp.of_equiv Subgroup.topEquiv).isNilpotent
      exact Group.IsPerfect.not_isNilpotent ↥L hnil
  have center_bot_of_simple : ∀ (L : Subgroup X), IsSimpleGroup ↥L →
      Group.IsPerfect ↥L → Subgroup.center ↥L = ⊥ := by
    intro L hsimple hperf
    have hnt : Nontrivial ↥L := hsimple.toNontrivial
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      have hcomm : IsMulCommutative ↥L := (Subgroup.center_eq_top_iff).mp h
      have hsub : Subsingleton ↥L := Group.IsPerfect.subsingleton_of_isMulCommutative
      exact (not_subsingleton ↥L) hsub
  have hS : ∀ P : Sylow 2 X,
      (∃ a b : X, a * b ≠ b * a) ∧ Nat.card (P : Subgroup X) = 8 ∧
        IsMulCommutative (P : Subgroup X) ∧
        ∀ t ∈ (P : Subgroup X), t ^ 2 = 1 := by
    intro P
    exact CFSG.Goldschmidt.GoldType.sylow_of_ree_or_j1 (K := X)
      (Or.inl ⟨n, hn1, hcardX⟩) P
  refine ⟨hZX_bot, hout.2.2, ?_⟩
  intro P
  have hPdata := hS P
  have hPcomm : IsMulCommutative (P : Subgroup X) := hPdata.2.2.1
  have hPsq : ∀ t ∈ (P : Subgroup X), t ^ 2 = 1 := hPdata.2.2.2
  have hPcard : Nat.card (P : Subgroup X) = 8 := hPdata.2.1
  have hPne : (P : Subgroup X) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    omega
  have hPnt : Nontrivial ↥(P : Subgroup X) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  obtain ⟨yH, hyH1⟩ := exists_ne (1 : ↥(P : Subgroup X))
  let y : X := (yH : X)
  have hyP : y ∈ (P : Subgroup X) := yH.2
  have hy1 : y ≠ 1 := by
    intro h
    exact hyH1 (Subtype.ext h)
  have hy2 : y ^ 2 = 1 := hPsq y hyP
  have hyord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  obtain ⟨Ly, hLyC, hLyinf, hLysup, ⟨eLy⟩, hZCy⟩ := hcen y hyord
  have hPleC : (P : Subgroup X) ≤ Subgroup.centralizer ({y} : Set X) := by
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (CFSG.commute_of_mem_of_isMulCommutative hPcomm hp hyP).eq
  have hcommYL : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ Ly, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact Commute.zpow_left
      (show Commute y b from
        (Subgroup.mem_centralizer_singleton_iff.mp (hLyC hb)).symm) m
  have hP_eq : (P : Subgroup X) = ((P : Subgroup X) ⊓ Ly) ⊔ Subgroup.zpowers y := by
    apply le_antisymm
    · intro p hp
      have hpC : p ∈ Subgroup.centralizer ({y} : Set X) := hPleC hp
      rw [← hLysup] at hpC
      obtain ⟨a, ha, l, hl, hal⟩ := (CFSG.mem_sup_of_commute hcommYL).mp hpC
      have haP : a ∈ (P : Subgroup X) := (Subgroup.zpowers_le).mpr hyP ha
      have hlP : l ∈ (P : Subgroup X) := by
        have h := (P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem haP) hp
        simpa [← hal, mul_assoc] using h
      have hcomm_la : Commute l a :=
        CFSG.commute_of_mem_of_isMulCommutative hPcomm hlP haP
      have hm : l * a ∈ ((P : Subgroup X) ⊓ Ly) ⊔ Subgroup.zpowers y :=
        Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hlP, hl⟩) ha
      rwa [hcomm_la.eq, hal] at hm
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hyP)
  have hcommPL : ∀ a ∈ (P : Subgroup X) ⊓ Ly,
      ∀ b ∈ Subgroup.zpowers y, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (CFSG.commute_of_mem_of_isMulCommutative hPcomm ha.1 hyP).zpow_right m
  have hdisjPL : ((P : Subgroup X) ⊓ Ly) ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzY : z ∈ Subgroup.zpowers y := hz.2
    have hzL : z ∈ Ly := hz.1.2
    have hzinf : z ∈ Subgroup.zpowers y ⊓ Ly := ⟨hzY, hzL⟩
    rw [hLyinf, Subgroup.mem_bot] at hzinf
    exact hzinf
  have hcardPL : Nat.card ↥((P : Subgroup X) ⊓ Ly) = 4 := by
    have hcard := CFSG.card_sup_eq_mul_of_commute ((P : Subgroup X) ⊓ Ly)
      (Subgroup.zpowers y) hcommPL hdisjPL
    rw [← hP_eq, hPcard, Nat.card_zpowers, hyord] at hcard
    omega
  have hPLne : ((P : Subgroup X) ⊓ Ly) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardPL
    omega
  have hPLnt : Nontrivial ↥((P : Subgroup X) ⊓ Ly) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hPLne
  obtain ⟨xH, hxH1⟩ := exists_ne (1 : ↥((P : Subgroup X) ⊓ Ly))
  let x : X := (xH : X)
  have hxP : x ∈ (P : Subgroup X) := xH.2.1
  have hxLy : x ∈ Ly := xH.2.2
  have hx1 : x ≠ 1 := by
    intro h
    exact hxH1 (Subtype.ext h)
  have hx2 : x ^ 2 = 1 := hPsq x hxP
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hyNotLy : y ∉ Ly := by
    intro hyL
    have hmem : y ∈ Subgroup.zpowers y ⊓ Ly := ⟨Subgroup.mem_zpowers y, hyL⟩
    rw [hLyinf, Subgroup.mem_bot] at hmem
    exact hy1 hmem
  have hxy : x ≠ y := by
    intro h
    exact hyNotLy (h ▸ hxLy)
  obtain ⟨Lx, hLxC, hLxinf, hLxsup, ⟨eLx⟩, hZCx⟩ := hcen x hxord
  have hKx_eq : ⁅Subgroup.centralizer ({x} : Set X),
      Subgroup.centralizer ({x} : Set X)⁆ = Lx :=
    derived_eq x hxord Lx hLxC hLxsup ⟨eLx⟩
  have hKy_eq : ⁅Subgroup.centralizer ({y} : Set X),
      Subgroup.centralizer ({y} : Set X)⁆ = Ly :=
    derived_eq y hyord Ly hLyC hLysup ⟨eLy⟩
  have hlieLx : CFSG.Blueprint.LieModel ↥Lx .PSL 2 3 (2 * n + 1) :=
    lie_of_psl Lx ⟨eLx⟩
  have hlieLy : CFSG.Blueprint.LieModel ↥Ly .PSL 2 3 (2 * n + 1) :=
    lie_of_psl Ly ⟨eLy⟩
  have hsimpleLx : IsSimpleGroup ↥Lx :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hlieLx
  have hsimpleLy : IsSimpleGroup ↥Ly :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hlieLy
  have hperfLx : Group.IsPerfect ↥Lx := perf_of_psl Lx ⟨eLx⟩
  have hperfLy : Group.IsPerfect ↥Ly := perf_of_psl Ly ⟨eLy⟩
  refine ⟨⟨hPcomm, hPsq⟩, hPcard, ?_⟩
  refine ⟨x, y, hxP, hyP, hxy, hxord, hyord, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hKx_eq]
    exact isL2_of_psl Lx ⟨eLx⟩
  · rw [hKy_eq]
    exact isL2_of_psl Ly ⟨eLy⟩
  · rw [hKx_eq]
    exact pcore_bot_of_simple Lx hsimpleLx hperfLx
  · rw [hKy_eq]
    exact pcore_bot_of_simple Ly hsimpleLy hperfLy
  · rw [hKy_eq]
    exact center_bot_of_simple Ly hsimpleLy hperfLy
  · rw [hKx_eq]
    exact hLxsup.symm.trans (sup_comm _ _)
  · rw [hKy_eq]
    exact hLysup.symm.trans (sup_comm _ _)
  · exact hcoat x hxord
  · exact hcoat y hyord
  · rw [hKy_eq]
    exact hxLy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
