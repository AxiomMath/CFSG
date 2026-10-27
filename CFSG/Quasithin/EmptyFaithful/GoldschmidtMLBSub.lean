module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBComap
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBLevel

public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem leviCent_map_subtype_le (B : Subgroup ↥L) :
    (leviCent B).map L.subtype ≤ leviCent (B.map L.subtype) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' := mem_leviCent.mp hc
  refine mem_leviCent.mpr ⟨Subgroup.mem_map_of_mem _ hc'.1, fun y hy => ?_⟩
  rw [← map_perfectCore] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have := Subgroup.mem_map_of_mem L.subtype (hc'.2 y₀ hy₀)
  rw [pCoreOf_map_subtype, map_perfectCore, map_commutatorElement] at this
  exact this

theorem le_leviCent_map_subtype (B : Subgroup ↥L) :
    leviCent (B.map L.subtype) ≤ (leviCent B).map L.subtype := by
  intro x hx
  have hx' := mem_leviCent.mp hx
  obtain ⟨x₀, hx₀, rfl⟩ := hx'.1
  refine ⟨x₀, mem_leviCent.mpr ⟨hx₀, fun y hy => ?_⟩, rfl⟩
  have h1 : L.subtype y ∈ perfectCore (B.map L.subtype) := by
    rw [← map_perfectCore]
    exact Subgroup.mem_map_of_mem _ hy
  have h2 := hx'.2 _ h1
  rw [← map_commutatorElement, ← map_perfectCore, ← pCoreOf_map_subtype] at h2
  obtain ⟨z, hz, hzz⟩ := h2
  rwa [← L.subtype_injective hzz]

theorem LieLevel.of_subtype {S : Subgroup G} (hSL : S ≤ L) {Pt : Fin 2 → Subgroup ↥L}
    (h : LieLevel (⊤ : Subgroup ↥L) (S.subgroupOf L) Pt) :
    LieLevel L S (fun j => (Pt j).map L.subtype) := by
  have hinj : Function.Injective L.subtype := L.subtype_injective
  have hsub : ∀ A : Subgroup G, A ≤ L → (A.subgroupOf L).map L.subtype = A := fun A hA =>
    Subgroup.map_subgroupOf_eq_of_le hA
  have hsub' : ∀ B : Subgroup ↥L, (B.map L.subtype).subgroupOf L = B := fun B =>
    Subgroup.comap_map_eq_self_of_injective hinj B
  have hle : ∀ A : Subgroup G, ∀ B : Subgroup ↥L, A ≤ L → (A ≤ B.map L.subtype ↔
      A.subgroupOf L ≤ B) := fun A B hA => by
    constructor
    · intro h1
      have := Subgroup.comap_mono (f := L.subtype) h1
      rwa [Subgroup.comap_map_eq_self_of_injective hinj B] at this
    · intro h1
      rw [← hsub A hA]
      exact Subgroup.map_mono h1
  have hmapL : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hne : ∀ A : Subgroup G, A ≤ L → A ≠ L → A.subgroupOf L ≠ ⊤ := fun A hA hAL he => hAL (by
    rw [← hsub A hA, he, hmapL])
  refine
    { le_L := fun j => Subgroup.map_subtype_le _
      S_le := fun j => (hle S _ hSL).mpr (h.S_le j)
      ne := fun he => h.ne (Subgroup.map_injective hinj he)
      ne_L := fun j he => h.ne_L j (Subgroup.map_injective hinj (he.trans hmapL.symm))
      cover := fun A hSA hAL hA => ?_
      maxl := fun j A hPA hAL => ?_
      solv01 := ?_
      nonsolv := fun A hSA hAL hA hns => ?_
      norm_le := fun j x hx => ?_
      solv := fun A hSA hAL hs x hx => ?_
      charTwo := fun j => Rk2.charTwo_of_equiv
        (Subgroup.equivMapOfInjective (Pt j) L.subtype hinj) (h.charTwo j)
      split := fun j g hg => ?_
      hall := fun j x hx k hk => ?_ }
  ·
    have hS' : S.subgroupOf L ≤ A.subgroupOf L := Subgroup.comap_mono hSA
    rcases h.cover (A.subgroupOf L) hS' le_top (hne A hAL hA) with h1 | h1
    · exact Or.inl ((hle A _ hAL).mpr h1)
    · exact Or.inr ((hle A _ hAL).mpr h1)
  ·
    have h1 : Pt j ≤ A.subgroupOf L := Subgroup.map_le_iff_le_comap.mp hPA
    rcases h.maxl j (A.subgroupOf L) h1 le_top with h2 | h2
    · left
      rw [← hsub A hAL, h2]
    · right
      rw [← hsub A hAL, h2, hmapL]
  ·
    have h1 : (Pt 0).map L.subtype ⊓ (Pt 1).map L.subtype = (Pt 0 ⊓ Pt 1).map L.subtype :=
      (Subgroup.map_inf_eq (Pt 0) (Pt 1) L.subtype hinj).symm
    rw [h1]
    exact isSolvable_map L.subtype h.solv01
  ·
    have hS' : S.subgroupOf L ≤ A.subgroupOf L := Subgroup.comap_mono hSA
    have hns' : ¬ Group.IsSolvable ↥(A.subgroupOf L) := fun hs =>
      hns (by rw [← hsub A hAL]; exact isSolvable_map L.subtype hs)
    obtain ⟨j, hjk, hj⟩ := h.nonsolv (A.subgroupOf L) hS' le_top (hne A hAL hA) hns'
    refine ⟨j, fun k => ?_, ?_⟩
    · rw [hle A _ hAL]
      exact hjk k
    · rw [← map_perfectCore, ← hsub A hAL]
      exact Subgroup.map_mono hj
  ·
    have hx' : (⟨x, hx.1⟩ : ↥L) ∈
        Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [← C2A3Orbits.mem_normalizer_map_subtype L (S.subgroupOf L) ⟨x, hx.1⟩,
        Subgroup.map_subgroupOf_eq_of_le hSL]
      exact hx.2
    exact ⟨⟨x, hx.1⟩, h.norm_le j ⟨Subgroup.mem_top _, hx'⟩, rfl⟩
  ·
    have hs' : Group.IsSolvable ↥(A.subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hAL).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hAL).injective
    have hS' : S.subgroupOf L ≤ A.subgroupOf L := Subgroup.comap_mono hSA
    have hxA : (⟨x, hAL hx⟩ : ↥L) ∈ A.subgroupOf L := hx
    have hx' := h.solv (A.subgroupOf L) hS' le_top hs' hxA
    have := (C2A3Orbits.mem_normalizer_map_subtype L (S.subgroupOf L) ⟨x, hAL hx⟩).mpr hx'
    rwa [Subgroup.map_subgroupOf_eq_of_le hSL] at this
  ·
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨a, ha, c, hc, rfl⟩ := h.split j g₀ hg₀
    refine ⟨L.subtype a, ?_, L.subtype c, leviCent_map_subtype_le _ (Subgroup.mem_map_of_mem _ hc),
      map_mul _ _ _⟩
    rw [← map_perfectCore]
    exact Subgroup.mem_map_of_mem _ ha
  ·
    have hx' := le_leviCent_map_subtype (Pt j) hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx'
    have hk' : x₀ ^ 2 ^ k = 1 := hinj (by rw [map_pow, map_one]; exact hk)
    have := h.hall j x₀ hx₀ k hk'
    rw [← pCoreOf_map_subtype]
    exact Subgroup.mem_map_of_mem _ this

end CFSG.Quasithin.GoldMLB
