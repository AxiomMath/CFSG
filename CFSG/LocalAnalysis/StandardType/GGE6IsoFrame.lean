module

public import CFSG.LocalAnalysis.StandardType.GGE6IsoOrbit
public import CFSG.LocalAnalysis.StandardType.GGKGAutDict

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem range_iff_of_card {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} (hinj : Function.Injective Φ)
    (hr : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ hypE6)
    (h5 : Nat.card A = 3 ^ 5) :
    ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ hypE6 := by
  rcases hr with htop | h
  · exfalso
    have hsurj : Function.Surjective Φ := fun y => by
      have hy : y ∈ Φ.range := by rw [htop]; exact Subgroup.mem_top y
      exact MonoidHom.mem_range.mp hy
    have hAcard : Nat.card A = 3 ^ 6 := by
      rw [Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)]
      rw [Nat.card_congr Multiplicative.toAdd]
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have h36 : (3 : ℕ) ^ 5 = 3 ^ 6 := h5.symm.trans hAcard
    norm_num at h36
  · exact h

private theorem conj_mem_normalizer {L' : Type} [Group L'] {A : Subgroup (MulAut L')} [Finite A]
    (m : L') (h : ∀ a : A, ∃ b : A,
      MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ = (b : MulAut L')) :
    MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  let c : MulAut L' := MulAut.conj m
  rw [Subgroup.mem_set_normalizer_iff]
  intro v
  constructor
  · intro hv
    obtain ⟨b, hb⟩ := h ⟨v, hv⟩
    rw [hb]
    exact b.2
  · intro hv
    have hmaple : A.map (MulAut.conj c).toMonoidHom ≤ A := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨b, hb⟩ := h ⟨w, hw⟩
      rw [show (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ from MulAut.conj_apply c w, hb]
      exact b.2
    have hcard : Nat.card (A.map (MulAut.conj c).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have hEq : A.map (MulAut.conj c).toMonoidHom = A :=
      Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)
    have hmem : (MulAut.conj c).toMonoidHom v ∈ A.map (MulAut.conj c).toMonoidHom := by
      rw [hEq]
      exact hv
    obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.1 hmem
    have huv' : u = v := (MulAut.conj c).injective huv
    rwa [← huv']

theorem kgAutFrame_of_model {L' : Type} [Group L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}
    (hM : GGE6ThreeWeylModelWith Z A Φ T w) (hA : Nat.card A = 3 ^ 5) : KGAutFrame A Φ := by
  obtain ⟨h1, h2, -, -, -, -, -, h8, -, h10, -, -⟩ := hM
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  refine ⟨hA, h1, range_iff_of_card h1 h2 hA, h10, ?_⟩
  intro i
  refine ⟨w i, conj_mem_normalizer (w i) (fun a => (h8 i a).imp fun b hb => hb.1), ?_⟩
  intro a b hab
  obtain ⟨b', hb', hΦ⟩ := h8 i a
  have hbb : b = b' := Subtype.ext (hab.trans hb')
  rw [hbb]
  exact hΦ

private noncomputable def isoCoord {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (κ : A →* Multiplicative (Fin 6 → ZMod 3)) (a : A) : Fin Tag.E6.rank → ZMod 3 :=
  Multiplicative.toAdd (κ a)

private theorem image_isoCoord_orbit {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)} (hF : KGAutFrame A κ)
    (a : A) :
    isoCoord κ '' ((fun φ : MulAut ↥A => φ a) '' (ggTorusAut A : Set (MulAut ↥A))) =
      Set.range fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u (isoCoord κ a) := by
  ext y
  constructor
  · rintro ⟨-, ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := hF.exists_weyl_of_mem hφ
    exact ⟨u, (hu a).symm⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨φ, hφ, hu⟩ := hF.exists_mem_of_weyl u
    exact ⟨φ a, ⟨φ, hφ, rfl⟩, hu a⟩

private theorem ncard_orbit_isoCoord {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)} (hF : KGAutFrame A κ)
    (a : A) :
    (Set.range fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u (isoCoord κ a)).ncard =
      ((fun φ : MulAut ↥A => φ a) '' (ggTorusAut A : Set (MulAut ↥A))).ncard := by
  have hinj : Function.Injective (isoCoord κ) := by
    intro x y hxy
    have hxy' : Multiplicative.toAdd (κ x) = Multiplicative.toAdd (κ y) := hxy
    exact hF.injective (Multiplicative.toAdd.injective hxy')
  rw [← image_isoCoord_orbit hF a]
  exact Set.ncard_image_of_injective _ hinj

theorem ggE6IsoPt_iff_of_kgAutFrame {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    {κ κ' : A →* Multiplicative (Fin 6 → ZMod 3)} (hF : KGAutFrame A κ) (hF' : KGAutFrame A κ')
    (a : A) :
    GGE6IsoPt (Multiplicative.toAdd (κ a)) ↔ GGE6IsoPt (Multiplicative.toAdd (κ' a)) := by
  show GGE6IsoPt (isoCoord κ a) ↔ GGE6IsoPt (isoCoord κ' a)
  by_cases ha : a = 1
  · rw [ha]
    have h1 : isoCoord κ (1 : A) = 0 := by
      change Multiplicative.toAdd (κ 1) = 0
      rw [map_one, toAdd_one]
    have h2 : isoCoord κ' (1 : A) = 0 := by
      change Multiplicative.toAdd (κ' 1) = 0
      rw [map_one, toAdd_one]
    rw [h1, h2]
  · have hneκ : isoCoord κ a ≠ 0 := by
      intro h0
      exact ha (hF.injective (by
        apply Multiplicative.toAdd.injective
        rw [show Multiplicative.toAdd (κ a) = 0 from h0, map_one κ, toAdd_one]))
    have hneκ' : isoCoord κ' a ≠ 0 := by
      intro h0
      exact ha (hF'.injective (by
        apply Multiplicative.toAdd.injective
        rw [show Multiplicative.toAdd (κ' a) = 0 from h0, map_one κ', toAdd_one]))
    have hκH : isoCoord κ a ∈ hypE6 := hF.toAdd_mem_hypE6 a
    have hκ'H : isoCoord κ' a ∈ hypE6 := hF'.toAdd_mem_hypE6 a
    rw [← ggE6IsoOrbit_ncard_eq_eighty_iff hκH hneκ,
      ← ggE6IsoOrbit_ncard_eq_eighty_iff hκ'H hneκ']
    rw [ncard_orbit_isoCoord hF a, ncard_orbit_isoCoord hF' a]

theorem exists_conj_kappa_eq_ggE6IsoBase {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin 6 → ZMod 3)} (hF : KGAutFrame A κ)
    {a : A} (ha : GGE6IsoPt (Multiplicative.toAdd (κ a))) :
    ∃ (m : L') (b : A), (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ ∧
      Multiplicative.toAdd (κ b) = ggE6IsoBase := by
  obtain ⟨u, hu⟩ := exists_adAct_eq_ggE6IsoBase ha
  obtain ⟨φ, hφ, hφu⟩ := hF.exists_mem_of_weyl u
  obtain ⟨g, hgH, -, hg⟩ := (mem_ggAutomizer_iff.1 hφ :
    ∃ g ∈ (MulAut.conj : L' →* MulAut L').range,
      g ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        ∀ b : A, ((φ b : A) : MulAut L') = g * b * g⁻¹)
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hgH
  refine ⟨m, φ a, ?_, ?_⟩
  · rw [hg a, hm]
  · exact (hφu a).trans hu

end CFSG.StandardType.KGL

end
