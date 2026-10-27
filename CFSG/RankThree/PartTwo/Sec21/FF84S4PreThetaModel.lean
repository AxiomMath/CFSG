module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreTheta
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalM12
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14113Layer
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S1469Three
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.EmptyFaithful.S146zQLists
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.SBc15R3G
public import CFSG.Quasithin.EmptyFaithful.SBc16SComp
public import CFSG.Quasithin.EmptyFaithful.SBc16SWr
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent1
public import CFSG.Quasithin.EmptyFaithful.SBc17L45
public import CFSG.Quasithin.EmptyFaithful.SBc17Out5L
public import CFSG.Quasithin.EmptyFaithful.T1515Der2
public import CFSG.Quasithin.EmptyFaithful.T1515Der3
public import CFSG.Quasithin.SteinbergOuterPrimeControl
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartTwo.Sec21.FF84S22
public import CFSG.RankThree.PartTwo.Sec21.FF84S3T0
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Inputs
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreModel
public import CFSG.Sporadic.Schreier.J4SThree
public import Certificates.Certificate8026Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin]
  decide

theorem theta_model {b b₁ b₂ : G} {L B K : Subgroup G}
    (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂) :
    ∃ θ : ↥(Nor L) →* Equiv.Perm (Fin 8),
      (∀ n : ↥(Nor L), θ n = 1 ↔ (n : G) ∈ CenS L) ∧
      (∀ x : ↥L, θ ⟨(x : G), Subgroup.le_normalizer x.2⟩ ∈ alternatingGroup (Fin 8)) ∧
      (∀ a ∈ alternatingGroup (Fin 8),
        ∃ x : ↥L, θ ⟨(x : G), Subgroup.le_normalizer x.2⟩ = a) ∧
      θ ⟨b₁, Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₁).2⟩ = a8c ∧
      θ ⟨b₂, Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₂).2⟩ = a8d := by
  obtain ⟨⟨e⟩, hZc⟩ := hA
  have hyp := h.hyp
  obtain ⟨θ₀, hθconj, hθx, hθker⟩ := S3.T0_thetaBar L (perfect_L hyp) e
  have hZ : ∀ z ∈ Subgroup.center ↥L, z ^ 2 = 1 := by
    intro z hz
    have h1 : orderOf (⟨z, hz⟩ : Subgroup.center ↥L) ∣ 2 :=
      (orderOf_dvd_natCard _).trans hZc
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
    exact congrArg Subtype.val h2
  let ρ : ↥L →* A8 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hρ : Function.Surjective ρ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center ↥L := by
    ext y
    simp [ρ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  obtain ⟨hb₁B, hb₁L⟩ := Subgroup.mem_inf.1 h.hb₁
  obtain ⟨hb₂B, hb₂L⟩ := Subgroup.mem_inf.1 h.hb₂
  obtain ⟨h13, h23, hcomm, hne1, hne2, hind, m, hmb, hmb₁⟩ :=
    mono_facts hyp.ord hb₁B hb₂B h.mono
  set u : ↥L := ⟨b₁, hb₁L⟩ with hu
  set v : ↥L := ⟨b₂, hb₂L⟩ with hv
  have hu3 : u ^ 3 = 1 := Subtype.ext h13
  have hv3 : v ^ 3 = 1 := Subtype.ext h23
  have huv : u * v = v * u := Subtype.ext hcomm
  have hu1 : u ≠ 1 := fun h => hne1 (congrArg Subtype.val h)
  have hv1 : v ≠ 1 := fun h => hne2 (congrArg Subtype.val h)
  have hmN : m ∈ Nor L := hyp.hLN (Subgroup.mem_centralizer_singleton_iff.2 (by
    calc m * b = (m * b * m⁻¹) * m := by group
      _ = b * m := by rw [hmb]))
  have hcardCu : Nat.card ↥(L ⊓ Cen b₁) = Nat.card ↥(L ⊓ Cen b₂) :=
    card_inf_cen_eq_of_conj hmN hmb₁
  have hZpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
  have hcu' : Nat.card ↥(L ⊓ Cen b₁) = Nat.card (Subgroup.centralizer ({u} : Set ↥L)) :=
    card_inf_cen hb₁L
  have hcv' : Nat.card ↥(L ⊓ Cen b₂) = Nat.card (Subgroup.centralizer ({v} : Set ↥L)) :=
    card_inf_cen hb₂L
  have hcu := card_cent ρ hρ hker hZ hu3
  have hcv := card_cent ρ hρ hker hZ hv3
  rw [← hcu'] at hcu
  rw [← hcv'] at hcv
  have hcard : Nat.card (Subgroup.centralizer ({ρ u} : Set A8)) =
      Nat.card (Subgroup.centralizer ({ρ v} : Set A8)) := by
    apply Nat.eq_of_mul_eq_mul_left hZpos
    rw [← hcu, ← hcv]; exact hcardCu
  have hx3 : ρ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hy3 : ρ v ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
  have hc : ρ u * ρ v = ρ v * ρ u := by rw [← map_mul, ← map_mul, huv]
  have hx1 : ρ u ≠ 1 := fun h => hu1 (ker_one ρ hker hZ h hu3)
  have hy1 : ρ v ≠ 1 := fun h => hv1 (ker_one ρ hker hZ h hv3)
  have hyx : ρ v ∉ Subgroup.zpowers (ρ u) := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    have hρk : ρ (v * (u ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk]; simp
    have hcomm' : Commute v (u ^ k)⁻¹ :=
      ((show Commute u v from huv).symm.zpow_right k).inv_right
    have hz3 : (v * (u ^ k)⁻¹) ^ 3 = 1 := by
      rw [hcomm'.mul_pow, hv3, one_mul, inv_pow, zpow_cube hu3 k, inv_one]
    have hz1 := ker_one ρ hker hZ hρk hz3
    have hvu : v = u ^ k := mul_inv_eq_one.1 hz1
    exact hind k (by simpa using congrArg Subtype.val hvu)
  obtain ⟨-, hKmod, hKsup, -, -⟩ := h.hK
  have hKle : K ≤ L ⊓ Cen b₁ := hKsup ▸ le_sup_right
  obtain ⟨e5⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_equiv_a5_of_psl hKmod
  have hK60 : 60 ≤ Nat.card K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
    have h2 : Nat.card (↥K ⧸ Subgroup.center ↥K) = 60 := by
      rw [Nat.card_congr e5.toEquiv, card_alt5]
    rw [h1, h2]
    have : 0 < Nat.card (Subgroup.center ↥K) := Nat.card_pos
    omega
  have hKcard : Nat.card K ≤ Nat.card (Subgroup.center ↥L) *
      Nat.card (Subgroup.centralizer ({ρ u} : Set A8)) := by
    rw [← hcu]; exact Subgroup.card_le_of_le hKle
  have hZle : Nat.card (Subgroup.center ↥L) ≤ 2 := Nat.le_of_dvd (by norm_num) hZc
  have hcx : Nat.card (Subgroup.centralizer ({ρ u} : Set A8)) ≠ 18 := by
    intro h18
    rw [h18] at hKcard
    nlinarith
  have hcy : Nat.card (Subgroup.centralizer ({ρ v} : Set A8)) ≠ 18 := hcard ▸ hcx
  obtain ⟨τ, hτ1, hτ2⟩ := pair_conj hx3 hy3 hc hx1 hy1 hyx hcx hcy
  have hθu : θ₀ ⟨b₁, Subgroup.le_normalizer hb₁L⟩ = ((ρ u : A8) : Equiv.Perm (Fin 8)) :=
    hθx u
  have hθv : θ₀ ⟨b₂, Subgroup.le_normalizer hb₂L⟩ = ((ρ v : A8) : Equiv.Perm (Fin 8)) :=
    hθx v
  refine ⟨(MulAut.conj τ).toMonoidHom.comp θ₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [← hθker n, MonoidHom.comp_apply]
    simp
  · intro x
    rw [MonoidHom.comp_apply, hθx x, mem_alternatingGroup]
    have h1 : sign ((e (QuotientGroup.mk x) : alternatingGroup (Fin 8)) :
        Equiv.Perm (Fin 8)) = 1 := mem_alternatingGroup.1 (e (QuotientGroup.mk x)).2
    simp [h1, ← mul_assoc, Int.units_mul_self]
  · intro a ha
    have ha' : τ⁻¹ * a * τ ∈ alternatingGroup (Fin 8) := by
      rw [mem_alternatingGroup] at ha ⊢
      simp [ha]
    obtain ⟨q, hq⟩ := e.surjective ⟨_, ha'⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨x, ?_⟩
    rw [MonoidHom.comp_apply, hθx x]
    have hq' : ((e (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        τ⁻¹ * a * τ := congrArg Subtype.val hq
    show τ * _ * τ⁻¹ = a
    rw [hq']; group
  · rw [MonoidHom.comp_apply, hθu]
    exact hτ1
  · rw [MonoidHom.comp_apply, hθv]
    exact hτ2

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
