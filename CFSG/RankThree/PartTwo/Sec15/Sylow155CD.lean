module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Con
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDAct
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDCore
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDR4
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDX
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOCP
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Conf
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
public import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Twin

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155CD

private theorem mem_of_quot {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {C Y : Subgroup G}
    (hAC : A ≤ C) (hYC : Y ≤ C) (hCY : C ≤ Subgroup.normalizer (Y : Set G))
    (hOY : pPrimeCoreOf 3 C ≤ Y) [((pPrimeCoreOf 3 Y).subgroupOf C).Normal]
    {J₁ J₂ : Subgroup (↥C ⧸ (pPrimeCoreOf 3 Y).subgroupOf C)}
    (hJsup : J₁ ⊔ J₂ = (Y.subgroupOf C).map (QuotientGroup.mk' _)) (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    {g : G} (hgC : g ∈ C) (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (hodd : Odd (orderOf g)) (hg3 : ¬ 3 ∣ orderOf g) : g ∈ pPrimeCoreOf 3 Y := by
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  have hA27 : Nat.card A = 27 := h.isE27.2
  set θ := pPrimeCoreOf 3 Y with hθ
  set π := QuotientGroup.mk' (θ.subgroupOf C) with hπ
  have hθ3 : Nat.Coprime 3 (Nat.card θ) := coprime_card_pPrimeCoreOf 3 Y
  have hAθ : A ⊓ θ = ⊥ := Subgroup.inf_eq_bot_of_coprime (by
    rw [hA27]
    simpa using Nat.Coprime.pow_left 3 hθ3)
  have hinj : Function.Injective (π.comp (A.subgroupOf C).subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : ↥C) ∈ θ.subgroupOf C := by
      rw [← QuotientGroup.eq_one_iff]
      exact ha
    have h2 : ((a : ↥C) : G) ∈ A ⊓ θ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp a.2, Subgroup.mem_subgroupOf.mp h1⟩
    rw [hAθ, Subgroup.mem_bot] at h2
    exact Subtype.ext (Subtype.ext h2)
  have hĀ27 : Nat.card ↥((A.subgroupOf C).map π) = 27 := by
    have e1 : (π.comp (A.subgroupOf C).subtype).range = (A.subgroupOf C).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA27]
  have hĀc : ∀ a ∈ (A.subgroupOf C).map π, ∀ b ∈ (A.subgroupOf C).map π, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : (a : G) * b = b * a := congrArg Subtype.val (hAab.is_comm.comm
      ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩)
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext h1]
  have hĀ3 : ∀ a ∈ (A.subgroupOf C).map π, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ 3 = 1 := Subtype.ext (by
      simpa using h.toSec13Data.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [← map_pow, h1, map_one]
  have hθC3 : ¬ 3 ∣ Nat.card ↥(θ.subgroupOf C) := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe ((pPrimeCoreOf_le 3 Y).trans hYC)).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hθ3
  have hĀC : ∀ q ∈ Subgroup.centralizer (((A.subgroupOf C).map π : Subgroup _) :
      Set (↥C ⧸ θ.subgroupOf C)), q ^ 3 = 1 → q ∈ (A.subgroupOf C).map π :=
    fun q hq hq3 => Sylow155T.mem_map_of_mem_centralizer h.mem_partTwoF hAC hθC3 hq hq3
  have hnorm : ∀ x : ↥C, (x : G) ∈ Subgroup.normalizer (Y : Set G) →
      x ∈ Subgroup.normalizer ((Y.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp hx (y : G)
    simpa [Subgroup.mem_subgroupOf] using h1
  have hĀY : (A.subgroupOf C).map π ≤
      Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup _) : Set (↥C ⧸ θ.subgroupOf C)) := by
    rw [hJsup]
    refine (Subgroup.map_mono fun a ha => hnorm a ?_).trans (Subgroup.le_normalizer_map π)
    exact hCY (hAC (Subgroup.mem_subgroupOf.mp ha))
  have hgY : π ⟨g, hgC⟩ ∈
      Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup _) : Set (↥C ⧸ θ.subgroupOf C)) := by
    rw [hJsup]
    exact Subgroup.le_normalizer_map π ⟨⟨g, hgC⟩, hnorm _ (hCY hgC), rfl⟩
  have hgĀ : π ⟨g, hgC⟩ ∈ Subgroup.centralizer
      (((A.subgroupOf C).map π : Subgroup _) : Set (↥C ⧸ θ.subgroupOf C)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (a : G) * g = g * a :=
      Subgroup.mem_centralizer_iff.mp hgA _ (Subgroup.mem_subgroupOf.mp ha)
    rw [← map_mul, ← map_mul, show a * ⟨g, hgC⟩ = ⟨g, hgC⟩ * a from Subtype.ext h1]
  have hdvd : orderOf (π ⟨g, hgC⟩) ∣ orderOf g := by
    have h1 := orderOf_map_dvd π ⟨g, hgC⟩
    rwa [Subgroup.orderOf_mk] at h1
  have hg3' : ¬ 3 ∣ orderOf (π ⟨g, hgC⟩) := fun h3' => hg3 (h3'.trans hdvd)
  have hgJ := mem_centralizer_of_commute hĀc hĀ3 hĀ27 hĀC hĀY hJ h3 hT₁ hT₂ hgĀ hgY
    (Odd.of_dvd_nat hodd hdvd) hg3'
  have hX : (J₁ ⊔ J₂).Normal := by
    rw [hJsup]
    exact (Subgroup.normal_subgroupOf_of_le_normalizer hCY).map π
      (QuotientGroup.mk'_surjective _)
  have h1 := eq_one_of_mem_centralizer hJ h3 hT₁ hT₂ hX
    (fun N hN hN3 => eq_bot_of_normal_quot hYC hOY hN hN3)
    (fun E T hE hE81 hT hT1 hET => false_of_elemAbelian_quot h hθC3 hE hE81 hT hT1 hET) hgJ hg3'
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem mem_pPrimeCoreOf_of_cp {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {d : G}
    (hdA : d ∈ A) {X : Subgroup G} (hXC : X ≤ Subgroup.centralizer ({d} : Set G))
    (hinv : Ronan148Q.Inv143Q A d d X)
    (hcp : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) {g : G}
    (hg : g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) (hodd : Odd (orderOf g)) :
    g ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  set C := Subgroup.centralizer ({d} : Set G) with hCdef
  set Y := pPrimeCoreOf 3 C ⊔ X with hYdef
  have hCY : C ≤ Subgroup.normalizer (Y : Set G) :=
    Sylow155NO.centralizer_le_normalizer_of_cp hinv hcp
  have hYC : Y ≤ C := sup_le (pPrimeCoreOf_le 3 C) hXC
  have hθX : inSubgroup (aschbacherSolvableCore 3) X ≤ pPrimeCoreOf 3 C :=
    Proof15Res11.theta_le_pPrimeCoreOf hXC hCY
  haveI : ((pPrimeCoreOf 3 Y).subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hCY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y))
  obtain ⟨J₁, J₂, hJsup, hJc, hJ3, hJ₁, hJ₂⟩ :=
    Sylow155NO.exists_cp_quot hXC (pPrimeCoreOf_le 3 C) hθX
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C))
      (le_normalizer_pPrimeCoreOf 3 C) hcp
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hg
  have hgC : g ∈ C := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA) hgA
  have hAC : A ≤ C := (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA))
  have hg3 : ¬ 3 ∣ orderOf g := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Subgroup.orderOf_dvd_natCard _ hg))
  exact pPrimeCoreOf_le_of_le_normalizer hYC hCY
    (mem_of_quot h hAC hYC hCY le_sup_left hJsup hJc hJ3 hJ₁ hJ₂ hgC hgA hodd hg3)

end Sylow155CD

theorem step155BalCompW_of_j2
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h3 : 3 < (omegaA A).ncard) (h9 : (omegaA A).ncard ≤ 9) : Step155BalCompW A c L := by
  intro h _ _ _ M _ _ _ _ _ _ _ _ _ g hg _ hodd B hBA hfree _
  have hD := hR.toSec13Data
  have hA := h.isE27'
  obtain ⟨d, hdA, hd1, hdZ⟩ : ∃ d ∈ A, d ≠ 1 ∧ IsZCentral L d := by
    obtain ⟨d, hdA, hd1, hdL, S, hdS, hSd⟩ := exists_three_central_of_j2 hD hJ
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    obtain ⟨hS, hZ⟩ :=
      center_sylow_eq_zpowers_of_quot_j2 Sec4.Sporadic.rank3II_4_15 hθ3 hJ hdL hd1 S hdS hSd
    exact ⟨d, hdA, hd1, _, hS, hZ⟩
  have hcd : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    Proof15Res11.isLBConfig_of hR hJ hdZ
  obtain ⟨hdL, -⟩ := hcd.2.2.2.2
  have hBcd : IsHyperplane A (Subgroup.closure {c, d}) :=
    Proof15Res11.isHyperplane_of hR hJ hdA hd1 hdL
  obtain ⟨-, -, -, -, -, -, -, -, -, hdc⟩ := Ronan152SL25.lbConfig_facts hA hBcd hcd
  have hdB : d ∈ Subgroup.closure {c, d} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K, hK, hLK⟩ := Desc143X.exists_mem_le_residual h48 h hBcd hcd hdB hd1 hdc
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K hK hLK with
    ⟨-, -, hΩ1⟩ | ⟨-, -, -, -, -, -, hΩ⟩ | ⟨-, -, -, h12⟩
  · rw [hΩ1, Set.ncard_singleton] at h3
    omega
  · rcases hΩ with ⟨-, h3'⟩ | ⟨-, -, -, -, a, ha, had, hΩa, h6, La, hLa, hJa⟩
    · omega
    · have haΩ : Subgroup.zpowers a ∈ omegaA A := by
        rw [hΩa]
        refine Or.inr ⟨1, one_mem _, ?_⟩
        rw [map_one]
        exact (Subgroup.map_id _).symm
      have hΩc : omegaA A ≠ {Subgroup.zpowers c} := fun h1 => by
        rw [h1, Set.ncard_singleton] at h6
        omega
      obtain ⟨X, hXC, hinv, hcp⟩ := Sylow155CD.exists_cp_of_ncard_six h134 h48 hR hJ hdZ hdA hd1
        hK hLK (Subgroup.mem_inf.mp ha).2 (Subgroup.mem_inf.mp ha).1 had haΩ h6 hLa hJa
      have hgd := Sylow155CD.mem_pPrimeCoreOf_of_cp h hdA hXC hinv hcp
        (Subgroup.mem_inf.mp hg).1 hodd
      have hdF : d ∈ B :=
        Sylow155CD.mem_of_forall_not_mem_omegaA h134 h48 h hBcd hcd hΩc hBA hfree
      have hBd : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({d} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdF)
      have hgB : g ∈ Subgroup.centralizer (B : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBA.1)
          (pPrimeCoreOf_le 3 _ (Subgroup.mem_inf.mp hg).1)
      have hle : pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊓
          Subgroup.centralizer (B : Set G) ≤
            pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
        le_pPrimeCoreOf inf_le_right
          (Late.le_normalizer_inf (hBd.trans (le_normalizer_pPrimeCoreOf 3 _))
            Subgroup.le_normalizer)
          (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
            (coprime_card_pPrimeCoreOf 3 _))
      have hgO : Subgroup.zpowers g ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
        Subgroup.zpowers_le.mpr (hle (Subgroup.mem_inf.mpr ⟨hgd, hgB⟩))
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have hyO := hgO hy
      have h1 : v * y * v⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
        (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pPrimeCoreOf 3 _ (Subgroup.mem_inf.mp hv).2) y).mp hyO
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hyO)
  · omega

end CFSG.RankThree.PartTwo.Sec15
