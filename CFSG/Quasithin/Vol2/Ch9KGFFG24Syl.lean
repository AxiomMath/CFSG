module

public import CFSG.Quasithin.Vol2.Ch9KGFFG24U
public import CFSG.Quasithin.Background.KGRankG24
public import CFSG.LieType.Chevalley.ChevalleySplitBN

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.G24

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K]

theorem exists_conj_le_posUnipotent
    [Finite K] [CharP K 2] {E : Subgroup ↥(adjointGroup .G2 K)} (hE : IsPGroup 2 ↥E) :
    ∃ g : ↥(adjointGroup .G2 K), ∀ x ∈ E,
      (((MulAut.conj g) x : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈ posUnipotent .G2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUcard : Nat.card (posUnipotent .G2 K) =
      Nat.card K ^ {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}.ncard :=
    card_posUnipotent
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) hUcard
  set P : Sylow 2 ↥(adjointGroup .G2 K) := hUp.toSylow hUi with hP
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(adjointGroup .G2 K) Q P
  refine ⟨g, fun x hx => ?_⟩
  have hmem : MulAut.conj g • x ∈ (P : Subgroup ↥(adjointGroup .G2 K)) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ hx)
  rw [hP, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf, MulAut.smul_def] at hmem
  exact hmem

end CFSG.Quasithin.H13.Ch9.KGFF.G24

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open H13.Ch9.KGFF.G24
open scoped IsMulCommutative

theorem rankG24Fact_holds :
    RankG24Fact := by
  intro K _ hK E hE
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hEp : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_posUnipotent hEp
  set E' : Subgroup (ModGL .G2 K) :=
    (E.map (MulAut.conj g).toMonoidHom).map (adjointGroup .G2 K).subtype with hE'
  have hE'U : E' ≤ posUnipotent .G2 K := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hg x hx
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    have := hE.1
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hxy : x * y = y * x := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩)
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, ← Subgroup.coe_mul, ← map_mul, hxy]
  have hsq : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx2 : x * x = 1 := by rw [← sq]; exact hE.2 x hx
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, ← Subgroup.coe_mul, ← map_mul, hx2,
      map_one, Subgroup.coe_one]
  have h := card_le_cube (S := Set.univ) hE'U hcomm hsq
    (fun _ _ _ _ _ _ _ => ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have hcard : Nat.card E' = Nat.card E := by
    rw [hE', Subgroup.card_map_of_injective (adjointGroup .G2 K).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [hcard, Nat.card_univ, hK] at h
  exact h.trans (by norm_num)

end CFSG.Quasithin
