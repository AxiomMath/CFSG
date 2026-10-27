module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828SMB
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.EmptyFaithful.R3c9Bnd
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)

private theorem sylow822VB_relIndex_eq_card_star {G : Type} [Group G] (M V J : Subgroup G)
    (hVJ : V ≤ J) (hk : CFSG.Quasithin.kerIn M J = pCoreOf 2 J) :
    (V ⊓ pCoreOf 2 J).relIndex V = Nat.card (CFSG.Quasithin.E2.star M J V) := by
  set ψ : ↥V →* CFSG.Quasithin.E2.StarQuot M J :=
    (CFSG.Quasithin.E2P.starMap M J).comp (Subgroup.inclusion hVJ)
  have key : ∀ x : ↥V, ψ x = 1 ↔ (x : G) ∈ CFSG.Quasithin.kerIn M J := by
    intro x
    have hx : ψ x = CFSG.Quasithin.E2P.starMap M J (Subgroup.inclusion hVJ x) := rfl
    rw [hx, ← MonoidHom.mem_ker, CFSG.Quasithin.E2P.ker_starMap, Subgroup.mem_subgroupOf]
    rfl
  have hker : ψ.ker = (V ⊓ pCoreOf 2 J).subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, key, Subgroup.mem_subgroupOf, hk, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : ψ.range = CFSG.Quasithin.E2.star M J V := by
    ext y
    rw [MonoidHom.mem_range, CFSG.Quasithin.E2P.star_def, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hVJ x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, hzy⟩
  unfold Subgroup.relIndex
  rw [← hker, Subgroup.index_ker, hrange]

private theorem sylow822VB_card_two_of_dihedral {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : Odd m) (hm1 : 1 < m) (e : X ≃* DihedralGroup m) {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) : Nat.card T = 2 := by
  have hm0 : m ≠ 0 := by omega
  haveI : NeZero m := ⟨hm0⟩
  have hXcard : Nat.card X = 2 * m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have h2 : (2 * m).factorization 2 = 1 := by
    have hodd : ¬ 2 ∣ m := by
      rintro ⟨c, hc⟩
      obtain ⟨d, hd⟩ := hm
      omega
    rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]
  rw [hT.card_eq]
  unfold CFSG.QuasithinUnique.twoPart
  rw [Subgroup.card_top, hXcard, h2]
  norm_num

private theorem sylow822VB_card_sylowCenter_of_card_two {X : Type} [Group X] {T : Subgroup X}
    (hT : Nat.card T = 2) : Nat.card (sylowCenter T) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic T := isCyclic_of_prime_card hT
  letI : CommGroup T := IsCyclic.commGroup
  have heq : sylowCenter T = T := by
    ext z
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter]
    refine ⟨fun hz => hz.1, fun hz => ⟨hz, fun t ht => ?_⟩⟩
    have hc := mul_comm (⟨t, ht⟩ : T) ⟨z, hz⟩
    exact congrArg Subtype.val hc
  rw [heq, hT]

private theorem sylow822VB_core {G : Type} [Group G] [Finite G]
    (M V J T : Subgroup G) (k : ℕ)
    (hVJ : V ≤ J) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ J) J)
    (hker : CFSG.Quasithin.kerIn M J = pCoreOf 2 J)
    (hcase : (k = 1 ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧
        Nonempty (CFSG.Quasithin.E2.StarQuot M J ≃* DihedralGroup m)) ∨
      CFSG.Quasithin.IsPSL 2 2 k (CFSG.Quasithin.E2.StarQuot M J) ∨
      CFSG.Quasithin.IsSz k (CFSG.Quasithin.E2.StarQuot M J))
    (hV6 : CFSG.Quasithin.E2.star M J V = CFSG.Quasithin.E2.star M J (T ⊓ J) ⊓
      Subgroup.centralizer (CFSG.Quasithin.E2.star M J (T ⊓ J) :
        Set (CFSG.Quasithin.E2.StarQuot M J))) :
    padicValNat 2 ((V ⊓ pCoreOf 2 J).relIndex V) = k := by
  haveI : Finite (CFSG.Quasithin.E2.StarQuot M J) := CFSG.Quasithin.E2P.finite_starQuot M J
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf (CFSG.Quasithin.E2.star M J (T ⊓ J)) ⊤ := by
    have h1 := CFSG.Quasithin.E2P.isSylowTwoOf_map_hom hSyl (CFSG.Quasithin.E2P.starMap M J)
    rw [MonoidHom.range_eq_top.mpr (CFSG.Quasithin.E2P.starMap_surjective M J)] at h1
    exact h1
  have hdvd : ¬ 2 ∣ (CFSG.Quasithin.E2.star M J (T ⊓ J)).index := by
    have h2 := hTsyl.2.2
    rwa [← Subgroup.relIndex_top_right]
  let P : Sylow 2 (CFSG.Quasithin.E2.StarQuot M J) := hTsyl.isPGroup.toSylow hdvd
  have hPcoe : (P : Subgroup (CFSG.Quasithin.E2.StarQuot M J)) =
      CFSG.Quasithin.E2.star M J (T ⊓ J) := IsPGroup.toSylow_coe _ _
  have hV6' : CFSG.Quasithin.E2.star M J V = sylowCenter (CFSG.Quasithin.E2.star M J (T ⊓ J)) :=
    hV6
  rw [sylow822VB_relIndex_eq_card_star M V J hVJ hker, hV6']
  rcases hcase with ⟨hk1, m, hm, hm1, ⟨e⟩⟩ | hpsl | hsz
  · have hcard : Nat.card (CFSG.Quasithin.E2.star M J (T ⊓ J)) = 2 :=
      sylow822VB_card_two_of_dihedral hm hm1 e hTsyl
    rw [sylow822VB_card_sylowCenter_of_card_two hcard, hk1]
    exact padicValNat_self
  · have hcen := CFSG.Quasithin.R3c9.card_sylowCenter_of_isPSL hpsl P
    rw [hPcoe] at hcen
    rw [hcen, padicValNat.prime_pow]
  · obtain ⟨-, -, -, -, hcen, -, -⟩ := CFSG.Quasithin.SBc2.exists_data hsz P
    rw [hPcoe] at hcen
    rw [hcen, padicValNat.prime_pow]

theorem sylow822VB_828_holds :
    Sylow822VB_828 := by
  intro G _ _ T L I _ _ _ _ _ H h k _ _ hC
  obtain ⟨-, -, -, -, -, hSyl, -, hker, -, hcase, hV6, -, -, -, -, -, -, -, -, -, -⟩ := hC
  exact sylow822VB_core (CFSG.Quasithin.H13.fsuM T L ⊓ ch82I (CFSG.Quasithin.H13.fsuV T I) h)
    (CFSG.Quasithin.H13.fsuV T I) (ch82I (CFSG.Quasithin.H13.fsuV T I) h) T k le_sup_left hSyl
    hker hcase hV6

end CFSG.Quasithin.H13
