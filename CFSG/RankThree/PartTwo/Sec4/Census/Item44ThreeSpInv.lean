module

public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
import CFSG.Adapters.Involutions
import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem isSolvable_of_plane_decomposition {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G : Subgroup (GL σ (ZMod 3))} {W W' : Submodule (ZMod 3) (σ → ZMod 3)}
    (hW : SubgroupLists.IsInvariant G W) (hW' : SubgroupLists.IsInvariant G W') (h2 : Module.finrank (ZMod 3) W = 2)
    (h2' : Module.finrank (ZMod 3) W' = 2) (hsup : W ⊔ W' = ⊤) : Group.IsSolvable G := by
  let b₁ := Module.finBasisOfFinrankEq (ZMod 3) _ ((finrank_section_bot W).trans h2)
  let b₂ := Module.finBasisOfFinrankEq (ZMod 3) _ ((finrank_section_bot W').trans h2')
  have hρ₁ := sectionRep_bot_eq_one_iff G hW b₁
  have hρ₂ := sectionRep_bot_eq_one_iff G hW' b₂
  have : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := by
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 4) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [Fintype.card_eq_nat_card, Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  refine Group.isSolvable_of_isSolvable_injective
    (f := (sectionRep G (isInvariant_bot G) hW b₁).prod (sectionRep G (isInvariant_bot G) hW' b₂))
    ((injective_iff_map_eq_one _).mpr fun g hg => ?_)
  have h1 : sectionRep G (isInvariant_bot G) hW b₁ g = 1 := congrArg Prod.fst hg
  have h1' : sectionRep G (isInvariant_bot G) hW' b₂ g = 1 := congrArg Prod.snd hg
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hv : v ∈ W ⊔ W' := hsup ▸ Submodule.mem_top
  obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add, (hρ₁ g).mp h1 w hw, (hρ₂ g).mp h1' w' hw', OneMemClass.coe_one,
    Units.val_one, Matrix.one_mulVec]

theorem isSolvable_centralizer_involution {t : GL V₄ (ZMod 3)} (ht : t ∈ StatedSp 2 (ZMod 3))
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    Group.IsSolvable (Subgroup.centralizer ({t} : Set (GL V₄ (ZMod 3)))) := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have htt : (t : Matrix V₄ V₄ (ZMod 3)) * t = 1 := by rw [← Units.val_mul, ht2, Units.val_one]
  have hm2 := finrank_eig_neg_one_eq_two h2 ht ht2 ht1 htm
  have hsum := finrank_eig_add_finrank_eig h2 htt
  have hinv : ∀ μ : ZMod 3, SubgroupLists.IsInvariant (Subgroup.centralizer ({t} : Set (GL V₄ (ZMod 3))))
      (eigSp (t : Matrix V₄ V₄ (ZMod 3)) μ) := by
    intro μ x hx v hv
    rw [mem_eigSp] at hv ⊢
    have hxt : (x : Matrix V₄ V₄ (ZMod 3)) * t = t * x := by
      rw [← Units.val_mul, ← Units.val_mul, Subgroup.mem_centralizer_singleton_iff.mp hx]
    rw [Matrix.mulVec_mulVec, ← hxt, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  exact isSolvable_of_plane_decomposition (hinv 1) (hinv (-1)) (by omega) hm2
    (eig_sup_eig h2 htt)

theorem neg_one_mem_of_isPerfect {H : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 3))}
    (hHS : H ≤ StatedSp 2 (ZMod 3)) (hH : Group.IsPerfect H) (hne : H ≠ ⊥) :
    (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ∈ H := by
  by_contra hneg
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  apply Group.IsPerfect.not_isSolvable H
  have hev : 2 ∣ Nat.card H := by
    by_contra hodd
    exact Group.IsPerfect.not_isSolvable H
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)))
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  have : Nontrivial (S : Subgroup H) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (S.ne_bot_of_dvd_card hev)
  have hZ : Nontrivial (Subgroup.center (S : Subgroup H)) := S.isPGroup'.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := (S.isPGroup'.to_subgroup _).nontrivial_iff_card.mp hZ
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 (by omega) :
    2 ∣ Nat.card (Subgroup.center (S : Subgroup H)))
  set z : (S : Subgroup H) := (x : (S : Subgroup H))
  have hzZ : z ∈ Subgroup.center (S : Subgroup H) := x.2
  have hz : orderOf z = 2 := (Subgroup.orderOf_coe x).trans hx
  set t : H := (z : H) with ht_def
  have htord : orderOf (t : GL V₄ (ZMod 3)) = 2 := by
    rw [Subgroup.orderOf_coe, ht_def, Subgroup.orderOf_coe, hz]
  have htsq : (t : GL V₄ (ZMod 3)) * t = 1 := by
    have := pow_orderOf_eq_one (t : GL V₄ (ZMod 3))
    rwa [htord, sq] at this
  have htsqH : t * t = 1 := Subtype.ext htsq
  have ht1 : (t : GL V₄ (ZMod 3)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    exact absurd htord (by norm_num)
  have htm : (t : GL V₄ (ZMod 3)) ≠ -1 := fun h => hneg (h ▸ t.2)
  have htS : (t : GL V₄ (ZMod 3)) ∈ StatedSp 2 (ZMod 3) := hHS t.2
  have hwc : ∀ g : H, g⁻¹ * t * g ∈ (S : Subgroup H) → g⁻¹ * t * g = t := by
    intro g hg
    by_contra hyz
    set y : H := g⁻¹ * t * g with hy_def
    have hyy : y * y = 1 := by
      rw [hy_def]
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htsqH]; group
    have hy1 : y ≠ 1 := by
      intro h
      apply ht1
      have : t = 1 := by
        calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
          _ = 1 := by rw [← hy_def, h]; group
      rw [this, OneMemClass.coe_one]
    have hcomm : t * y = y * t := by
      have := Subgroup.mem_center_iff.mp hzZ ⟨y, hg⟩
      exact (congrArg Subtype.val this).symm
    rcases neg_one_mem_of_commute_involutions h2 htS (hHS y.2) htsq
        (by rw [← Subgroup.coe_mul, hyy, OneMemClass.coe_one])
        (by rw [← Subgroup.coe_mul, hcomm, Subgroup.coe_mul]) ht1
        (fun h => hy1 (Subtype.ext h)) (fun h => hyz (Subtype.ext h).symm) with h | h | h
    · exact hneg (h ▸ t.2)
    · exact hneg (h ▸ y.2)
    · exact hneg (h ▸ H.mul_mem t.2 y.2)
  obtain ⟨hdec, -⟩ := CFSG.Adapters.glauberman_zStar S z hzZ hz hwc
  have hCsolv : Group.IsSolvable (Subgroup.centralizer ({t} : Set H)) := by
    have := isSolvable_centralizer_involution htS htsq ht1 htm
    let φ : Subgroup.centralizer ({t} : Set H) →*
        Subgroup.centralizer ({(t : GL V₄ (ZMod 3))} : Set (GL V₄ (ZMod 3))) :=
      { toFun := fun c => ⟨((c : H) : GL V₄ (ZMod 3)), by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := φ) fun a b hab => ?_
    have hab' := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext hab')
  have hKodd : Odd (Nat.card (CFSG.oddCore H)) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2K
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 h2K
    have hodd := CFSG.Adapters.odd_orderOf_of_mem_oddCore k.2
    rw [Subgroup.orderOf_coe, hk] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hKsolv : Group.IsSolvable (CFSG.oddCore H) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
  have hQsolv : Group.IsSolvable (H ⧸ CFSG.oddCore H) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (CFSG.oddCore H)).comp (Subgroup.centralizer ({t} : Set H)).subtype)
      fun q => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) q
    obtain ⟨c, hc, k, hk, rfl⟩ := hdec g
    refine ⟨⟨c, hc⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, inv_mul_cancel_left]
    exact hk
  exact Group.isSolvable_of_subgroup_quotient (CFSG.oddCore H)

theorem three_dvd_card_of_isPerfect {H : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 3))}
    (hHS : H ≤ StatedSp 2 (ZMod 3)) (hH : Group.IsPerfect H) (hne : H ≠ ⊥) : 3 ∣ Nat.card H := by
  classical
  by_contra h3
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  apply Group.IsPerfect.not_isSolvable H
  have hcard : Nat.card (StatedSp 2 (ZMod 3)) = 3 ^ 4 * (2 ^ 7 * 5) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
    decide
  have hdvd : Nat.card H ∣ 3 ^ 4 * (2 ^ 7 * 5) := hcard ▸ Subgroup.card_dvd_of_le hHS
  have hcop : Nat.Coprime (Nat.card H) (3 ^ 4) :=
    Nat.Coprime.pow_right 4 (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).mpr h3))
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.mp (hcop.dvd_of_dvd_mul_left hdvd)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk₁
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
    (by rwa [pow_one] : k₂ ∣ 5 ^ 1)
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    (by norm_num : Nat.Prime 5) (by norm_num) (by rw [Fintype.card_eq_nat_card, hk])

end CFSG.RankThree.PartTwo.Sec4.Census
