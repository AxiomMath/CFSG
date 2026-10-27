module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.ClassicalInvolution.Models.LinearPairs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

section Orb

variable {G : Type} [Group G] [Finite G]

@[expose] def GGOrbAt (X Bs : Subgroup G) {ι : Type} {A : Subgroup (MulAut ↥Bs)}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) {m : ℕ} (e' : Fin m ≃ ι) (T : Finset (Fin m)) :
    Prop :=
  ∃ w : M.Group, ∀ t ∈ T,
    ((e (w * M.simple (e' t) * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs

theorem exists_lift_of_mem_ggAutomizerJoin {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {a : MulAut ↥Bs} (ha : a ∈ ggAutomizerJoin L Bs 𝒦) :
    ∃ g ∈ L ⊔ ⨆ K ∈ 𝒦, K, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹ :=
  mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦 ha)

theorem ggRankOne_conj_of_mem_ggAutomizerJoin {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {a : MulAut ↥Bs} (ha : a ∈ ggAutomizerJoin L Bs 𝒦) (r : MulAut ↥Bs) :
    ∃ g ∈ L ⊔ ⨆ K ∈ 𝒦, K, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (ggRankOne Bs r).map (MulAut.conj g).toMonoidHom = ggRankOne Bs (a * r * a⁻¹) ∧
      ∀ r' : MulAut ↥Bs, (ggRankTwo Bs r r').map (MulAut.conj g).toMonoidHom =
        ggRankTwo Bs (a * r * a⁻¹) (a * r' * a⁻¹) := by
  obtain ⟨g, hgY, hgN, hg⟩ := exists_lift_of_mem_ggAutomizerJoin ha
  exact ⟨g, hgY, hgN, ggRankOne_map_conj hg r, fun r' => ggRankTwo_map_conj hg r r'⟩

theorem coe_conj_simple {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (w : M.Group) (t : ι) :
    ((e w : ↥A) : MulAut ↥Bs) * ((e (M.simple t) : ↥A) : MulAut ↥Bs) *
        ((e w : ↥A) : MulAut ↥Bs)⁻¹ = ((e (w * M.simple t * w⁻¹) : ↥A) : MulAut ↥Bs) := by
  rw [map_mul, map_mul, map_inv]
  rfl

end Orb

section Conj

variable {X : Type} [Group X]

theorem UnitaryBlockStandardPair.map_conj {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    {W U V : Subgroup X} (g : X) (h : UnitaryBlockStandardPair K 2 f W U V) :
    UnitaryBlockStandardPair K 2 f (W.map (MulAut.conj g).toMonoidHom)
      (U.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨θ, c, hrange, hker, hUV⟩ := h
  refine ⟨(MulAut.conj g).toMonoidHom.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective]
    exact hker
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem UnitaryBlockStandardPair.of_map_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} {W U V : Subgroup X} (g : X)
    (h : UnitaryBlockStandardPair K 2 f (W.map (MulAut.conj g).toMonoidHom)
      (U.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom)) :
    UnitaryBlockStandardPair K 2 f W U V := by
  have h' := UnitaryBlockStandardPair.map_conj (K := K) (f := f) g⁻¹ h
  have hc : ∀ S : Subgroup X, (S.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = S := by
    intro S
    rw [Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id X := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  rwa [hc, hc, hc] at h'

theorem exists_su_four_hom_map_conj {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    {S T : Subgroup X} (g : X) (h : ∃ θ : Su K 2 f 4 →* X, θ.range = S ⊔ T) :
    ∃ θ : Su K 2 f 4 →* X, θ.range =
      S.map (MulAut.conj g).toMonoidHom ⊔ T.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨θ, hθ⟩ := h
  exact ⟨(MulAut.conj g).toMonoidHom.comp θ, by rw [MonoidHom.range_comp, hθ, Subgroup.map_sup]⟩

theorem commute_map_conj_iff {S T : Subgroup X} (g : X) :
    (∀ x ∈ S.map (MulAut.conj g).toMonoidHom, ∀ y ∈ T.map (MulAut.conj g).toMonoidHom,
        x * y = y * x) ↔ ∀ x ∈ S, ∀ y ∈ T, x * y = y * x := by
  constructor
  · intro h x hx y hy
    have := h _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    have h2 := congrArg (fun z => g⁻¹ * z * g) this
    simpa [mul_assoc] using h2
  · intro h x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
      _ = g * (y' * x') * g⁻¹ := by rw [h x' hx' y' hy']
      _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group

end Conj

section SU

noncomputable def sl2MulEquivOfRingEquiv {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') :
    SL(2, F) ≃* SL(2, F') :=
  { Matrix.SpecialLinearGroup.map e.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
    left_inv := fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp
    right_inv := fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp }

theorem qtwo_su_two_equiv_sl2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nonempty (Su (GaloisField 2 2) 2 1 2 ≃* SL(2, F)) := by
  have hK : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two
    (K := GaloisField 2 2) (p := 2) (f := 1) hK
  have hcard : Nat.card (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 2) 2 1) = 2 := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
    norm_num
  haveI : Fintype F := Fintype.ofFinite F
  letI : Fintype (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 2) 2 1) :=
    Fintype.ofFinite _
  let ε : CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 2) 2 1 ≃+* F :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, hF])
  exact ⟨e.symm.trans (sl2MulEquivOfRingEquiv ε)⟩

end SU

end CFSG.StandardType.QTwo

end
