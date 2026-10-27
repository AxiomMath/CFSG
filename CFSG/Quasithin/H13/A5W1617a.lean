module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Core
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem smul_eq_of_perfect {K X : Type*} [Group K] [MulAction K X] [Finite X]
    (hK : commutator K = ⊤) (hX : Nat.card X ≤ 4) (k : K) (x : X) : k • x = x := by
  have hs : Group.IsSolvable (Equiv.Perm X) := Equiv.Perm.isSolvable hX
  set f := MulAction.toPermHom K X with hf
  have hrp : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hK]
  have hrs : Group.IsSolvable ↥f.range := inferInstance
  have hr : f.range = ⊥ := by
    have h1 := (isSolvable_iff_perfectCore_eq_bot f.range).mp hrs
    rwa [perfectCore_eq_self_of_perfect hrp] at h1
  have hk : f k = 1 := by
    have : f k ∈ f.range := ⟨k, rfl⟩
    rw [hr, Subgroup.mem_bot] at this
    exact this
  have := congrArg (fun e : Equiv.Perm X => e x) hk
  simpa [hf] using this

theorem commutator_eq_top_of_perfect {G : Type*} [Group G] {K : Subgroup G} (hKp : ⁅K, K⁆ = K) :
    commutator ↥K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    hKp]

theorem le_normalizer_conj_of_perfect {G : Type*} [Group G] [Finite G] {K O : Subgroup G}
    (hKp : ⁅K, K⁆ = K) (hKO : K ≤ Subgroup.normalizer (O : Set G))
    (hidx : (O ⊓ Subgroup.normalizer (K : Set G)).relIndex O ≤ 4) {o : G} (ho : o ∈ O) :
    K ≤ Subgroup.normalizer ((K.map (MulAut.conj o).toMonoidHom : Subgroup G) : Set G) := by
  classical
  set X : Set (Subgroup G) := {Y | ∃ p ∈ O, Y = K.map (MulAut.conj p).toMonoidHom} with hX
  have hconj : ∀ {p q : G}, p⁻¹ * q ∈ Subgroup.normalizer (K : Set G) →
      K.map (MulAut.conj q).toMonoidHom = K.map (MulAut.conj p).toMonoidHom := by
    intro p q h
    have e : q = p * (p⁻¹ * q) := by group
    have hK' : K.map (MulAut.conj (p⁻¹ * q)).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp h
    rw [e, show (MulAut.conj (p * (p⁻¹ * q))).toMonoidHom =
        (MulAut.conj p).toMonoidHom.comp (MulAut.conj (p⁻¹ * q)).toMonoidHom by
      ext x; simp [MulAut.conj_apply, mul_assoc], ← Subgroup.map_map, hK']
  set N' := (O ⊓ Subgroup.normalizer (K : Set G)).subgroupOf O with hN'
  let f : ↥O ⧸ N' → ↥X := Quotient.lift (fun p : ↥O => (⟨K.map (MulAut.conj (p : G)).toMonoidHom,
      p, p.2, rfl⟩ : ↥X)) (by
    intro p q hpq
    have h : p⁻¹ * q ∈ N' := QuotientGroup.leftRel_apply.mp hpq
    rw [hN', Subgroup.mem_subgroupOf] at h
    exact Subtype.ext (hconj h.2).symm)
  have hfs : Function.Surjective f := by
    rintro ⟨Y, p, hp, rfl⟩
    exact ⟨QuotientGroup.mk ⟨p, hp⟩, rfl⟩
  have hcard : Nat.card ↥X ≤ 4 :=
    (Nat.card_le_card_of_surjective f hfs).trans hidx
  have hmem : ∀ k ∈ K, ∀ Y ∈ X, Y.map (MulAut.conj k).toMonoidHom ∈ X := by
    rintro k hk Y ⟨p, hp, rfl⟩
    refine ⟨k * p * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hKO hk) p).mp hp, ?_⟩
    rw [Subgroup.map_map]
    have := hconj (p := k * p * k⁻¹) (q := k * p) (by
      rw [show (k * p * k⁻¹)⁻¹ * (k * p) = k by group]
      exact Subgroup.le_normalizer hk)
    rw [← this]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  let act : MulAction ↥K ↥X :=
    { smul := fun k Y => ⟨(Y : Subgroup G).map (MulAut.conj (k : G)).toMonoidHom,
        hmem k k.2 Y Y.2⟩
      one_smul := fun Y => Subtype.ext (by
        show (Y : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = Y
        rw [map_one]
        exact Subgroup.map_id _)
      mul_smul := fun k l Y => Subtype.ext (by
        show (Y : Subgroup G).map (MulAut.conj ((k : G) * l)).toMonoidHom =
          ((Y : Subgroup G).map (MulAut.conj (l : G)).toMonoidHom).map
            (MulAut.conj (k : G)).toMonoidHom
        rw [Subgroup.map_map, map_mul]
        rfl) }
  have : Finite ↥X := Set.toFinite X |>.to_subtype
  intro k hk
  have h := @smul_eq_of_perfect ↥K ↥X _ act _ (commutator_eq_top_of_perfect hKp) hcard ⟨k, hk⟩
    ⟨K.map (MulAut.conj o).toMonoidHom, o, ho, rfl⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact congrArg Subtype.val h

end CFSG.Quasithin.H13.A5
