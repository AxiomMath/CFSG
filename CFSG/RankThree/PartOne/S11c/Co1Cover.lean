module

public import CFSG.RankThree.PartOne.S11c.Co1TernaryModule
public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.Sporadic.Schreier.Co1OuterImage
public import CFSG.RankThree.GroupTheory.SteinbergCECentralOddKernelLift
public import CFSG.RankThree.Chevalley.SteinbergBNHigherExceptionalSmallField

public section

namespace CFSG.RankThree.PartOne

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped IsMulCommutative

theorem co1_E_le_GA : E ≤ GA := E_le_A.trans A_le_GA

theorem co1_c_mem_GA (i : Fin 2) : c i ∈ GA := A_le_GA (c_mem_A i)

instance co1_E_isElementaryAbelian : CFSG.IsElementaryAbelian 3 E where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (E_comm _ a.2 _ b.2).eq⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (E_pow_three _ x.2)

theorem co1_c_mem_normalizer (i : Fin 2) : c i ∈ Subgroup.normalizer (E : Set GL24) :=
  mem_normalizer_E fun j => by
    rw [co1_c_conj_a]
    exact eProd_mem _

@[expose] noncomputable def co1PhiS : Multiplicative (Fin 6 → ZMod 3) ≃* (E.subgroupOf GA) :=
  eEquiv.trans (Subgroup.subgroupOfEquivOfLe co1_E_le_GA).symm

@[expose] noncomputable def co1CS (i : Fin 2) : GA := ⟨c i, co1_c_mem_GA i⟩

theorem co1_CS_mem_normalizer (i : Fin 2) :
    co1CS i ∈ Subgroup.normalizer ((E.subgroupOf GA : Subgroup GA) : Set GA) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (co1_c_mem_normalizer i) (h : GL24)

theorem co1_CS_conj (i : Fin 2) (b : Fin 6 → ZMod 3) :
    co1CS i * ((co1PhiS (Multiplicative.ofAdd b) : E.subgroupOf GA) : GA) * (co1CS i)⁻¹ =
      ((co1PhiS (Multiplicative.ofAdd ((![co1M0, co1M1] i) *ᵥ b)) : E.subgroupOf GA) : GA) :=
  Subtype.ext (co1_c_conj_eProd i b)

theorem co1_commute_of_mem_comap {Y : Type*} [Group Y] (π : Y →* GA)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y) :
    ∀ u ∈ (E.subgroupOf GA).comap π, ∀ v ∈ (E.subgroupOf GA).comap π, u * v = v * u := by
  have : CFSG.IsElementaryAbelian 3 (E.subgroupOf GA) :=
    CFSG.IsElementaryAbelian.subgroupOf co1_E_le_GA
  have hCE : Subgroup.closure (Set.range co1CS) ≤
      Subgroup.normalizer ((E.subgroupOf GA : Subgroup GA) : Set GA) :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact co1_CS_mem_normalizer i)
  refine CFSG.RankThree.GroupTheory.commute_of_mem_comap_of_forms (p := 3) hπ hker hCE ?_
  intro B halt hinv
  refine co1_bilin_zero (E.subgroupOf GA) co1PhiS co1CS co1_CS_mem_normalizer co1_CS_conj B halt
    fun i x y => ?_
  exact hinv ⟨co1CS i, Subgroup.subset_closure ⟨i, rfl⟩⟩ x y

theorem co1ActualArbitraryCentralCoversForceTwoLocalRankFour :
    Co1ActualArbitraryCentralCoversForceTwoLocalRankFour := by
  intro X _ _ Y T _ π hπ hT hker
  obtain ⟨e⟩ := hT
  let ψ : T ≃* GA := e.trans co1GAEquiv
  let π' : Y →* GA := (ψ : T →* GA).comp π
  have hπ' : Function.Surjective π' := ψ.surjective.comp hπ
  have hker' : π'.ker ≤ Subgroup.center Y := by
    intro y hy
    apply hker
    have h1 : ψ (π y) = 1 := MonoidHom.mem_ker.mp hy
    exact MonoidHom.mem_ker.mpr (ψ.injective (h1.trans (map_one ψ).symm))
  have hcomm := co1_commute_of_mem_comap π' hπ' hker'
  set D : Subgroup GA := (E ⊓ Subgroup.centralizer {c 0}).subgroupOf GA with hD
  have hDle : D ≤ E.subgroupOf GA := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hDcard : 3 ^ 4 ≤ Nat.card D := by
    rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans co1_E_le_GA)).toEquiv, co1_card_centralizer]
  have hDp : ∀ x ∈ D, x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact E_pow_three _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1)
  have hF : ∀ x ∈ D.comap π', ∀ y ∈ D.comap π', x * y = y * x := fun x hx y hy =>
    hcomm x (Subgroup.comap_mono hDle hx) y (Subgroup.comap_mono hDle hy)
  have hz : orderOf (co1CS 0) = 2 := by
    rw [co1CS, Subgroup.orderOf_mk]
    exact co1_orderOf_c_zero
  have hzD : ∀ x ∈ D, Commute (co1CS 0) x := fun x hx => by
    have := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact Subtype.ext this.symm
  obtain ⟨-, -, -, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.central_cover_involution_witness Y hπ' hker' Nat.prime_three
      (by norm_num) hDp hF hDcard hz hzD
  exact CFSG.RankThree.Chevalley.four_le_twoLocalOddRank_of_four_le_localRank Nat.prime_three
    (by norm_num) hrank

end CFSG.RankThree.PartOne
