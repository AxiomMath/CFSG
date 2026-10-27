module

public import CFSG.Monster.GMS.Leech.Module
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Sporadic.MI301Three

open CFSG.Open CFSG.Monster.GMS

theorem exists_elemAbelian_lift_leech {G : Type} [Group G] [Finite G] {t : G}
    (L : CFSG.Monster.GMS.LeechSystem t)
    (hQ : Nat.card ↥(CFSG.Monster.GMS.leechQ t) = 2 ^ 25) {ζ : G}
    (hζ : ζ ∈ Subgroup.centralizer ({t} : Set G)) (hζ3 : orderOf ζ = 3)
    {E : Subgroup CFSG.Blueprint.NativeSporadic.Co1} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEc : Nat.card ↥E = 3 ^ 6) (hζE : L.φ ⟨ζ, hζ⟩ ∈ E) :
    ∃ B₁ : Subgroup G, B₁ ≤ Subgroup.centralizer ({t} : Set G) ∧ CFSG.Open.IsElemAbelian 3 B₁ ∧
      Nat.card ↥B₁ = 3 ^ 6 ∧ ζ ∈ B₁ := by
  set Y : Subgroup ↥(Subgroup.centralizer ({t} : Set G)) := E.comap L.φ
  set f : Y →* E := (L.φ.comp Y.subtype).codRestrict E fun y => y.2
  have hfs : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨c, rfl⟩ := L.φ_surj e
    exact ⟨⟨c, Subgroup.mem_comap.2 he⟩, rfl⟩
  have hEp : IsPGroup 3 (⊤ : Subgroup E) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hE.2 _ g.1.2))⟩
  have hζY : (⟨ζ, hζ⟩ : ↥(Subgroup.centralizer ({t} : Set G))) ∈ Y := Subgroup.mem_comap.2 hζE
  have hζo : orderOf (⟨⟨ζ, hζ⟩, hζY⟩ : Y) = 3 ^ 1 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hζ3, pow_one]
  obtain ⟨S, hζS⟩ := (IsPGroup.of_card (by rw [Nat.card_zpowers, hζo]) :
    IsPGroup 3 (Subgroup.zpowers (⟨⟨ζ, hζ⟩, hζY⟩ : Y))).exists_le_sylow
  have hSE : (S : Subgroup Y).map f = ⊤ := ((S.mapSurjective hfs).is_maximal' hEp le_top).symm
  have hdisj : Disjoint (((S : Subgroup Y).map Y.subtype).map
      (Subgroup.centralizer ({t} : Set G)).subtype) (leechQ t) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ ((S.isPGroup'.map _).map _)
      (IsPGroup.of_card hQ)
  have hinj : Function.Injective (f.comp (S : Subgroup Y).subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyQ : (((y : Y) : ↥(Subgroup.centralizer ({t} : Set G))) : G) ∈ leechQ t :=
      (L.φ_ker _).1 (congrArg Subtype.val hy)
    exact Subtype.ext (Subtype.ext (Subtype.ext (Subgroup.disjoint_def.1 hdisj
      (Subgroup.mem_map.2 ⟨_, Subgroup.mem_map.2 ⟨_, y.2, rfl⟩, rfl⟩) hyQ)))
  have hcard : Nat.card (S : Subgroup Y) = 3 ^ 6 := by
    have e1 : (S : Subgroup Y).map f = (f.comp (S : Subgroup Y).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← e1, hSE, Subgroup.card_top, hEc]
  have hab : IsElemAbelian 3 (S : Subgroup Y) := by
    haveI := hE.1
    refine ⟨⟨⟨fun a b => hinj ?_⟩⟩, fun y hy => ?_⟩
    · rw [map_mul, map_mul]
      exact mul_comm' _ _
    · have h1 : (f.comp (S : Subgroup Y).subtype) (⟨y, hy⟩ ^ 3) = 1 := by
        rw [map_pow]
        exact Subtype.ext (hE.2 _ ((f.comp (S : Subgroup Y).subtype) ⟨y, hy⟩).2)
      exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))
  refine ⟨((S : Subgroup Y).map Y.subtype).map (Subgroup.centralizer ({t} : Set G)).subtype,
    Subgroup.map_subtype_le _, (hab.map _).map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective Y.subtype_injective, hcard]
  · exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_map.2 ⟨_, hζS (Subgroup.mem_zpowers _), rfl⟩, rfl⟩

end CFSG.Sporadic.MI301Three

end
