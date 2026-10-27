module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.PSLTwoFstar
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.GroupTheory.CommutingConjugatePair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenC
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.LiteratureLocal
  (ward_kleidman_small_Ree_involution_centralizer_maximal)

private theorem le_of_mem_aSet_two_of_outer_odd {W : Type} [CommGroup W] [Finite W]
    {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hF : Fstar Y = L) (hOut : Odd (Nat.card (Outer ↥L))) (hA : A ∈ E3.aSet 2 Y) :
    A ≤ L := by
  classical
  let L' : Subgroup ↥Y := L.subgroupOf Y
  have : L'.Normal := hLn
  let e : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  let ψ : ↥Y →* MulAut ↥L :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (G := ↥Y) (H := L'))
  let φ : ↥Y →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp ψ
  have : Finite (Outer ↥L) := inferInstance
  let fA : ↥A →* Outer ↥L := φ.comp (Subgroup.inclusion hA.1)
  have hA2 : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hmap2 : IsPGroup 2 fA.range :=
    IsPGroup.of_surjective hA2 fA.rangeRestrict fA.rangeRestrict_surjective
  have hbot : fA.range = ⊥ := by
    have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
      (G := Outer ↥L) (H := fA.range) (K := ⊤) hmap2 (by simpa using hOut)
    simpa using h
  intro a ha
  have hone : fA ⟨a, ha⟩ = 1 := by
    have hmem : fA ⟨a, ha⟩ ∈ fA.range := MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hone' : (QuotientGroup.mk' (inner ↥L)) (ψ ⟨a, hA.1 ha⟩) = 1 := hone
  have hinner : ψ ⟨a, hA.1 ha⟩ ∈ inner ↥L := (QuotientGroup.eq_one_iff _).mp hone'
  obtain ⟨l, hl⟩ := hinner
  let lY : ↥Y := ⟨(l : MulAut W), hLY l.2⟩
  let aY : ↥Y := ⟨a, hA.1 ha⟩
  let lL : ↥L' := ⟨lY, Subgroup.mem_subgroupOf.mpr l.2⟩
  have hlL : (lL : ↥Y) = lY := rfl
  have hconjEq : MulAut.conjNormal (G := ↥Y) (H := L') lL =
      MulAut.conjNormal (G := ↥Y) (H := L') aY := by
    apply (MulAut.congr e).injective
    calc (MulAut.congr e) (MulAut.conjNormal (G := ↥Y) (H := L') lL)
        = MulAut.conj (e lL) := by
          rw [MulAut.conjNormal_val]
          exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e lL
      _ = MulAut.conj l := by rfl
      _ = ψ aY := hl
      _ = (MulAut.congr e) (MulAut.conjNormal (G := ↥Y) (H := L') aY) := rfl
  have hxL : (lY⁻¹ * aY : ↥Y).1 ∈ L := by
    apply W4Row.mem_of_mem_centralizer_of_fstar_eq (G := MulAut W) hLY hF
      (Y := Y) (L := L) (lY⁻¹ * aY).2
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let zY : ↥Y := ⟨z, hLY hz⟩
    have hz' : zY ∈ L' := Subgroup.mem_subgroupOf.mpr hz
    have h := congrArg (fun f : MulAut ↥L' => f ⟨zY, hz'⟩) hconjEq
    have hY : ((MulAut.conjNormal (G := ↥Y) (H := L') lL) ⟨zY, hz'⟩ : ↥Y) =
        ((MulAut.conjNormal (G := ↥Y) (H := L') aY) ⟨zY, hz'⟩ : ↥Y) :=
      congrArg Subtype.val h
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply] at hY
    have hW : (l : MulAut W) * z * (l : MulAut W)⁻¹ = a * z * a⁻¹ := by
      simpa using congrArg (fun y : ↥Y => (y : MulAut W)) hY
    have hconj : ((l : MulAut W)⁻¹ * a) * z * ((l : MulAut W)⁻¹ * a)⁻¹ = z := by
      calc ((l : MulAut W)⁻¹ * a) * z * ((l : MulAut W)⁻¹ * a)⁻¹
          = (l : MulAut W)⁻¹ * (a * z * a⁻¹) * l := by group
        _ = (l : MulAut W)⁻¹ * ((l : MulAut W) * z * (l : MulAut W)⁻¹) * l := by rw [hW]
        _ = z := by group
    calc z * ((l : MulAut W)⁻¹ * a)
        = (((l : MulAut W)⁻¹ * a) * z * ((l : MulAut W)⁻¹ * a)⁻¹) *
            ((l : MulAut W)⁻¹ * a) := by rw [hconj]
      _ = ((l : MulAut W)⁻¹ * a) * z := by group
  have haeq : a = (l : MulAut W) * ((lY⁻¹ * aY : ↥Y) : MulAut W) := by
    rw [show ((lY⁻¹ * aY : ↥Y) : MulAut W) = (l : MulAut W)⁻¹ * a from rfl]
    group
  rw [haeq]
  exact L.mul_mem l.2 hxL

private theorem commutator_zpowers_sup_eq_of_isPerfect {G : Type} [Group G] {t : G}
    {K : Subgroup G} (hTK : ∀ k ∈ K, t * k = k * t) (hperf : Group.IsPerfect ↥K) :
    ⁅Subgroup.zpowers t ⊔ K, Subgroup.zpowers t ⊔ K⁆ = K := by
  have hTT : ∀ a ∈ Subgroup.zpowers t, ∀ a' ∈ Subgroup.zpowers t, Commute a a' := by
    intro a ha a' ha'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    exact Commute.zpow_zpow_self t m n
  have hTL : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ K, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hTK b hb) m)
  apply le_antisymm
  · calc ⁅Subgroup.zpowers t ⊔ K, Subgroup.zpowers t ⊔ K⁆ ≤ ⁅K, K⁆ :=
        CFSG.commutator_sup_le_commutator_right hTT hTL
      _ = K := Subgroup.isPerfect_iff.mp hperf
  · calc K = ⁅K, K⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
      _ ≤ ⁅Subgroup.zpowers t ⊔ K, Subgroup.zpowers t ⊔ K⁆ :=
        Subgroup.commutator_mono le_sup_right le_sup_right

private theorem four_le_card_of_mem_aSet_two {W : Type} [CommGroup W] [Finite W]
    {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X) : 4 ≤ Nat.card A := by
  have h2 : 2 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  have hA2 : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hcard : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
    simpa using E3.card_eq_two_pow_mul (G := MulAut W) (V := A) (U := ⊥) hA2 bot_le
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ E3.mQuot A ⊥ := Nat.pow_le_pow_right (by norm_num) h2
    _ = Nat.card A := hcard.symm


theorem aSet_two_eq_empty_of_ree {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {m : ℕ} (hm : 1 ≤ m) (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L)
    (hRee : LieModel ↥L .twistedG2 0 3 (2 * m + 1)) : E3.aSet 2 Y = ∅ := by
  classical
  have hR : CFSG.Blueprint.ReeTitsModel ↥L .twistedG2 3 (2 * m + 1) :=
    (hRee.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨-, -, hcen, -, -, -, hoddOut⟩ :=
    ward_kleidman_small_Ree_involution_centralizer_maximal m hm ↥L hR
  have hFcard : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have hF4 : 4 ≤ Nat.card (GaloisField 3 (2 * m + 1)) := by
    rw [hFcard]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF3 : 3 < Nat.card (GaloisField 3 (2 * m + 1)) := by omega
  have hF9 : 9 < Nat.card (GaloisField 3 (2 * m + 1)) := by
    rw [hFcard]
    calc 9 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hF2 : (2 : GaloisField 3 (2 * m + 1)) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := GaloisField 3 (2 * m + 1)) (p := 3)
      Nat.prime_two (by norm_num)
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  have hAL : A ≤ L := le_of_mem_aSet_two_of_outer_odd hLY hLn hF hoddOut hA
  obtain ⟨t, htA, htord⟩ := E3.exists_orderOf_two_of_isPGroup
    (E3.isPGroup_of_isElemAbelian2 hA.2.2.1) hA.2.1
  let tL : ↥L := ⟨t, hAL htA⟩
  have htL2 : orderOf tL = 2 := by
    change orderOf (⟨t, hAL htA⟩ : ↥L) = 2
    rw [Subgroup.orderOf_mk]
    exact htord
  obtain ⟨K, hKC, hKinf, hKsup, ⟨eK⟩, hZcent⟩ := hcen tL htL2
  let KW : Subgroup (MulAut W) := K.map L.subtype
  let eMap : ↥K ≃* ↥KW := Subgroup.equivMapOfInjective K L.subtype L.subtype_injective
  let eKW : ↥KW ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 3 (2 * m + 1)) := eMap.symm.trans eK
  have hqPSL : CFSG.IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 3 (2 * m + 1))) :=
    CFSG.RankThree.PartTwo.KFacts.isQuasisimple_psl2_of_four_le_card hF4
  have hqK : CFSG.IsQuasisimple ↥KW :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eKW.symm hqPSL
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 3 (2 * m + 1))) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
  have : IsSimpleGroup ↥KW := eKW.isSimpleGroup
  have hperfK : Group.IsPerfect ↥K := by
    have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 3 (2 * m + 1))) :=
      CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three _ hF3
    exact Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hTK : ∀ k ∈ K, tL * k = k * tL := by
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm
  let C : Subgroup ↥L := Subgroup.centralizer ({tL} : Set ↥L)
  let AG : Subgroup ↥L := A.subgroupOf L
  have hAGC : AG ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hA.2.2.1.1 (a : MulAut W) (Subgroup.mem_subgroupOf.mp ha) t htA
  have hAGC' : AG ≤ Subgroup.centralizer ({tL} : Set ↥L) := hAGC
  have hcommC : ⁅Subgroup.centralizer ({tL} : Set ↥L),
      Subgroup.centralizer ({tL} : Set ↥L)⁆ = K := by
    rw [← hKsup]
    exact commutator_zpowers_sup_eq_of_isPerfect hTK hperfK
  have hKnC : (K.subgroupOf (Subgroup.centralizer ({tL} : Set ↥L))).Normal := by
    rw [← hcommC]
    have h := Subgroup.normal_subgroupOf_commutator_sup
      (H₁ := Subgroup.centralizer ({tL} : Set ↥L))
      (H₂ := Subgroup.centralizer ({tL} : Set ↥L))
    rwa [sup_idem] at h
  have hCnormK : Subgroup.centralizer ({tL} : Set ↥L) ≤
      Subgroup.normalizer (K : Set ↥L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKnC
  have hAGnormK : AG ≤ Subgroup.normalizer (K : Set ↥L) := hAGC'.trans hCnormK
  have hAN : A ≤ Subgroup.normalizer (KW : Set (MulAut W)) := by
    intro a ha
    have haL : a ∈ L := hAL ha
    have haG : (⟨a, haL⟩ : ↥L) ∈ AG := Subgroup.mem_subgroupOf.mpr ha
    have hnorm := hAGnormK haG
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      obtain ⟨kG, hkG, rfl⟩ := Subgroup.mem_map.mp hk
      have h1 := (Subgroup.mem_normalizer_iff.mp hnorm kG).mp hkG
      refine Subgroup.mem_map.mpr ⟨(⟨a, haL⟩ : ↥L) * kG * (⟨a, haL⟩ : ↥L)⁻¹, h1, ?_⟩
      simp
    · intro hk
      obtain ⟨kG, hkG, hk_eq⟩ := Subgroup.mem_map.mp hk
      have hnorminv := hAGnormK (AG.inv_mem haG)
      have h1 := (Subgroup.mem_normalizer_iff.mp hnorminv kG).mp hkG
      refine Subgroup.mem_map.mpr ⟨(⟨a, haL⟩ : ↥L)⁻¹ * kG * (⟨a, haL⟩ : ↥L), h1, ?_⟩
      have hk_eq' : (kG : MulAut W) = (a : MulAut W) * k * (a : MulAut W)⁻¹ := hk_eq
      show (a : MulAut W)⁻¹ * (kG : MulAut W) * (a : MulAut W) = k
      rw [hk_eq']
      group
  have hZK : Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hmem : eK z ∈ Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 3 (2 * m + 1))) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨v, rfl⟩ := eK.surjective w
      rw [← map_mul, ← map_mul, hz v]
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot] at hmem
    rw [Subgroup.mem_bot] at hmem
    exact eK.injective (by rw [hmem, map_one])
  have hcommTK : ∀ x ∈ Subgroup.zpowers tL, ∀ k ∈ K, x * k = k * x := by
    intro x hx k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute tL k from hTK k hk).zpow_left n).eq
  have hAC : ¬ A ≤ Subgroup.centralizer (KW : Set (MulAut W)) := by
    intro hAcent
    have hAGcentK : AG ≤ Subgroup.centralizer (K : Set ↥L) := by
      intro aG haG
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hAcent (Subgroup.mem_subgroupOf.mp haG))
        (k : MulAut W) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
    have hAGleZ : AG ≤ Subgroup.zpowers tL := by
      intro aG haG
      have haGsup : aG ∈ Subgroup.zpowers tL ⊔ K := by
        rw [hKsup]
        exact hAGC' haG
      obtain ⟨y, hy, k, hk, hdec⟩ :=
        (CFSG.SignalizerFunctorTheorem.McBride.mem_sup_iff_of_commute hcommTK).mp haGsup
      have hycent : y ∈ Subgroup.centralizer (K : Set ↥L) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (hcommTK y hy l hl).symm
      have hkcent : k ∈ Subgroup.centralizer (K : Set ↥L) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hk_eq : k = y⁻¹ * aG := by
          rw [← hdec]
          group
        rw [hk_eq]
        have h1 : Commute l y := Subgroup.mem_centralizer_iff.mp hycent l hl
        have h2 : Commute l aG := Subgroup.mem_centralizer_iff.mp (hAGcentK haG) l hl
        exact (h1.inv_right.mul_right h2).eq
      have hkZ : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        simpa using Subgroup.mem_centralizer_iff.mp hkcent l l.2
      rw [hZK, Subgroup.mem_bot] at hkZ
      have hk1 : k = 1 := congrArg Subtype.val hkZ
      have haeq : aG = y := by
        rw [← hdec, hk1, mul_one]
      rw [haeq]
      exact hy
    have hcardAG : Nat.card AG = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
    have hdvd : Nat.card A ∣ Nat.card (Subgroup.zpowers tL) := by
      rw [← hcardAG]
      exact Subgroup.card_dvd_of_le hAGleZ
    rw [Nat.card_zpowers, htL2] at hdvd
    have hle2 : Nat.card A ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have h4 := four_le_card_of_mem_aSet_two hA
    omega
  have hA' : A ∈ E3.aSet 2 (KW ⊔ A) := ⟨le_sup_right, hA.2⟩
  obtain ⟨U₁, hU₁c, hU₁f, hU₁exp, Y₁, hLn₁, hq₁, ⟨f, hf_surj⟩, hk₁⟩ :=
    SevenSevenC.caseB_data_of_normalizes (U := W) hW hqK hAN hA' hAC
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hker | hker
    · have hx' : x ∈ f.ker := MonoidHom.mem_ker.mpr hx
      rw [hker, Subgroup.mem_bot] at hx'
      exact hx'
    · exfalso
      have hbot : f.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨y, rfl⟩
        have hy : y ∈ f.ker := by rw [hker]; exact Subgroup.mem_top y
        rw [MonoidHom.mem_ker] at hy
        rw [Subgroup.mem_bot]
        simp [hy]
      have htop : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf_surj
      have htopbot : (⊤ : Subgroup ↥(fstarSubOf Y₁)) = ⊥ := htop.symm.trans hbot
      have hsub : Subsingleton ↥(fstarSubOf Y₁) := by
        refine ⟨fun a b => ?_⟩
        have ha : a = 1 := by
          have hmem : a ∈ (⊥ : Subgroup ↥(fstarSubOf Y₁)) := htopbot ▸ Subgroup.mem_top a
          simpa using hmem
        have hb : b = 1 := by
          have hmem : b ∈ (⊥ : Subgroup ↥(fstarSubOf Y₁)) := htopbot ▸ Subgroup.mem_top b
          simpa using hmem
        rw [ha, hb]
      have hnt : Nontrivial ↥(fstarSubOf Y₁) := by
        obtain ⟨a, b, hab⟩ := hq₁.2.2
        have habne : a ≠ b := fun h => hab (by rw [h])
        obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
          (Subgroup.center ↥(fstarSubOf Y₁)) a
        obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
          (Subgroup.center ↥(fstarSubOf Y₁)) b
        exact ⟨x, y, fun hxy => habne (by rw [← hx, ← hy, hxy])⟩
      have := hnt
      exact not_subsingleton _ hsub
  let eSurj : ↥KW ≃* ↥(fstarSubOf Y₁) := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hFs_le : Fstar Y₁ ≤ Y₁ := by
    simpa [Fstar] using
      Subgroup.map_subtype_le (H := Y₁) (K := CFSG.Open.genFittingFStar ↥Y₁)
  let eSub : ↥(fstarSubOf Y₁) ≃* ↥(Fstar Y₁) :=
    Subgroup.subgroupOfEquivOfLe hFs_le
  let e₁ : ↥(Fstar Y₁) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 3 (2 * m + 1)) := (eSub.symm.trans eSurj.symm).trans eKW
  have hle1 : E3.aParam Y₁ ≤ 1 :=
    (aParam_le_of_fstar_psl2 (W := U₁) (F := GaloisField 3 (2 * m + 1)) hU₁exp hF2 hF3
      hFs_le hLn₁ rfl e₁).1 hF9
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
