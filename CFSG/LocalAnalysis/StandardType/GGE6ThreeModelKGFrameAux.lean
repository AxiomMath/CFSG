module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelBody
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame

public section


namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem kgFrame_exists_conj_diag {K : Type} [Field K] [Finite K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {γ : MulAut ↥(adjointGroup Tag.E6 K)} (hγ : γ ∈ (hatAut Tag.E6 K).range) :
    ∃ g ∈ adjointGroup Tag.E6 K, ∀ (x : Fin Tag.E6.rank → ZMod 3) (r : ↥(adjointGroup Tag.E6 K)),
      (((γ⁻¹ * NoOffE6Three.diag3 ζ hζ (Multiplicative.ofAdd x) * γ) r : ↥(adjointGroup Tag.E6 K)) :
          ModGL Tag.E6 K) =
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) * (r : ModGL Tag.E6 K) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹)⁻¹ := by
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hγ
  obtain ⟨g₀, hg₀, b, hy⟩ := y.2
  let g : ModGL Tag.E6 K := (y : ModGL Tag.E6 K)⁻¹ * rootDiagUnit Tag.E6 b
  have hb : rootDiagUnit Tag.E6 b = (rootDiagUnit Tag.E6 b⁻¹)⁻¹ := by
    rw [← rootDiagUnit_inv b]
    group
  have hg_eq : g = rootDiagUnit Tag.E6 b⁻¹ * g₀⁻¹ * (rootDiagUnit Tag.E6 b⁻¹)⁻¹ := by
    dsimp only [g]
    rw [hy, hb]
    group
  refine ⟨g, ?_, ?_⟩
  · rw [hg_eq]
    exact conj_rootDiagUnit_mem_adjointGroup b⁻¹ (inv_mem hg₀)
  · intro x r
    have hcomm : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * rootDiagUnit Tag.E6 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hede : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
        (rootDiagUnit Tag.E6 b)⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ x) := by
      rw [hcomm]
      group
    have hgd : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ =
        (y : ModGL Tag.E6 K)⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
          (y : ModGL Tag.E6 K) := by
      have hg : g = (y : ModGL Tag.E6 K)⁻¹ * rootDiagUnit Tag.E6 b := rfl
      rw [hg]
      calc (y : ModGL Tag.E6 K)⁻¹ * rootDiagUnit Tag.E6 b *
              rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
              ((y : ModGL Tag.E6 K)⁻¹ * rootDiagUnit Tag.E6 b)⁻¹
            = (y : ModGL Tag.E6 K)⁻¹ * (rootDiagUnit Tag.E6 b *
                rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * (rootDiagUnit Tag.E6 b)⁻¹) *
                (y : ModGL Tag.E6 K) := by group
        _ = (y : ModGL Tag.E6 K)⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
                (y : ModGL Tag.E6 K) := by rw [hede]
    rw [hgd]
    simp only [← map_inv (hatAut Tag.E6 K) y, MulAut.mul_apply, coe_hatAut_apply,
      NoOffE6Three.diag3_apply, Subgroup.coe_inv, inv_inv]
    group

theorem kgFrame_range_eq_hyp {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)} (hinj : Function.Injective Φ)
    (hr : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6)
    (h5 : Nat.card A = 3 ^ 5) :
    ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6 := by
  rcases hr with htop | h
  · exfalso
    have hsurj : Function.Surjective Φ := fun y => by
      have hy : y ∈ Φ.range := by rw [htop]; exact Subgroup.mem_top y
      exact MonoidHom.mem_range.mp hy
    have hAcard : Nat.card A = 3 ^ 6 := by
      rw [Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)]
      rw [Nat.card_congr Multiplicative.toAdd]
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rfl
    have h36 : (3 : ℕ) ^ 5 = 3 ^ 6 := h5.symm.trans hAcard
    norm_num at h36
  · exact h

theorem kgFrame_conj_mem_normalizer {L' : Type} [Group L'] {A : Subgroup (MulAut L')} [Finite A]
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

end CFSG.StandardType.E6ThreeModel
