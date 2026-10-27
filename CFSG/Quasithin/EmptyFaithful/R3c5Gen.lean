module

public import CFSG.Quasithin.EmptyFaithful.R3c5Star
public import CFSG.Quasithin.EmptyFaithful.R3c3Base

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Transport

variable {A B : Type} [Group A] [Group B]

theorem map_oTwoUpper_of_injective (f : A →* B) (hf : Function.Injective f) (X : Subgroup A) :
    (oTwoUpper X).map f = oTwoUpper (X.map f) := by
  unfold oTwoUpper
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [orderOf_injective f hf x]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hodd⟩
    exact ⟨x, ⟨hx, by rwa [← orderOf_injective f hf x]⟩, rfl⟩

end Transport

section SubgroupOf

variable {G : Type} [Group G]

theorem map_oTwoUpper_subgroupOf {I X : Subgroup G} (hXI : X ≤ I) :
    (oTwoUpper (X.subgroupOf I)).map I.subtype = oTwoUpper X := by
  rw [map_oTwoUpper_of_injective _ I.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hXI]

theorem map_pCoreOf_subgroupOf {I X : Subgroup G} (hXI : X ≤ I) (p : ℕ) :
    (pCoreOf p (X.subgroupOf I)).map I.subtype = pCoreOf p X := by
  set e : ↥(X.subgroupOf I) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXI
  have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl


theorem OTwoQuot_pow_three_subgroupOf {I Y : Subgroup G} (hYI : Y ≤ I)
    (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) : ∀ z : OTwoQuot (Y.subgroupOf I), z ^ 3 = 1 := by
  set e : ↥(Y.subgroupOf I) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYI
  have hle : CFSG.Open.pCore 2 ↥(Y.subgroupOf I) ≤ (CFSG.Open.pCore 2 ↥Y).comap e.toMonoidHom := by
    rw [← Subgroup.map_le_iff_le_comap, CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e]
  let ρ : OTwoQuot (Y.subgroupOf I) →* OTwoQuot Y :=
    QuotientGroup.map _ _ e.toMonoidHom hle
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    have : (e z') ∈ CFSG.Open.pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp hz
    have h2 : z' ∈ (CFSG.Open.pCore 2 ↥Y).comap e.toMonoidHom := this
    have h3 : (CFSG.Open.pCore 2 ↥Y).comap e.toMonoidHom = CFSG.Open.pCore 2 ↥(Y.subgroupOf I) := by
      have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e.symm
      ext x
      constructor
      · intro hx
        have hx' : e x ∈ CFSG.Open.pCore 2 ↥Y := hx
        have := Subgroup.mem_map_of_mem e.symm.toMonoidHom hx'
        rw [CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e.symm] at this
        simpa using this
      · intro hx
        have := Subgroup.mem_map_of_mem e.toMonoidHom hx
        rwa [CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e] at this
    rw [h3] at h2
    exact (QuotientGroup.eq_one_iff _).mpr h2
  intro z
  apply hρ
  rw [map_pow, map_one]
  obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : ρ (QuotientGroup.mk z') = (QuotientGroup.mk (e z') : OTwoQuot Y) := rfl
  rw [h1]
  exact hYe _

theorem isSylowTwoOf_subgroupOf {I Q A : Subgroup G} (hAI : A ≤ I) (h : IsSylowTwoOf Q A) :
    IsSylowTwoOf (Q.subgroupOf I) (A.subgroupOf I) := by
  refine ⟨Subgroup.comap_mono h.1, ?_, ?_⟩
  · exact h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (h.1.trans hAI)).symm
  · have h1 : ((Q.subgroupOf I).subgroupOf (A.subgroupOf I)).index =
        (Q.subgroupOf I).relIndex (A.subgroupOf I) := rfl
    rw [h1, Subgroup.relIndex_subgroupOf hAI]
    exact h.2.2

end SubgroupOf

section StarEquiv

variable {H : Type} [Group H] [Finite H]

theorem nonempty_starImage_equiv_quotCenter {L : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) (hXs : IsSimpleGroup ↥(starImage 3 L)) :
    Nonempty (↥(starImage 3 L) ≃* (↥L ⧸ Subgroup.center ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperfL : Group.IsPerfect ↥L := hQ.1
  set π : ↥L →* ↥(starImage 3 L) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).subgroupMap L with hπ
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).subgroupMap_surjective L
  have hperfX : Group.IsPerfect ↥(starImage 3 L) := Group.IsPerfect.ofSurjective (f := π) hπs
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    constructor
    · intro hx
      have hx1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (x : H) = 1 := congrArg Subtype.val hx
      exact mem_center_of_mem_pPrimeCore hQ h3 x ((QuotientGroup.eq_one_iff _).mp hx1)
    · intro hx
      have hc : π x ∈ Subgroup.center ↥(starImage 3 L) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := hπs g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g']
      rw [R3c3.center_eq_bot_of_simple_perfect hXs hperfX] at hc
      exact Subgroup.mem_bot.mp hc
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

end StarEquiv

end CFSG.Quasithin.R3c5
