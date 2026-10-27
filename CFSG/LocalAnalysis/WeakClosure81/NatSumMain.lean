module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.LocalAnalysis.WeakClosure81.NatSumIso
public import CFSG.LocalAnalysis.WeakClosure81.NatSumProj
public import CFSG.LocalAnalysis.WeakClosure81.NatSumTwo
public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NatSum

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Open

theorem isNatSL2Section_of_isSumNatSection_of_line {X : Type} [Group X]
    (hX : CFSG.Quasithin.IsPSL 2 2 2 X)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : X →* LGL 2 W)
    {B F : Subgroup X} {Z : Submodule (ZMod 2) W} (hB : B.index = 5)
    (hstab : ∀ g : X, g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z) (hF : IsElemAbelian 2 F) (hFc : Nat.card F = 4)
    (hFB : F ≤ B) (hFZ : ∀ f ∈ F, ∀ z ∈ Z, ρ f z = z) (hZ : Module.finrank (ZMod 2) Z = 2)
    (hreg : ∀ x ∈ B, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0)
    (hgen : ⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W) = ⊤)
    (hsum : IsSumNatSection ρ ⊥ ⊤ (fixSub ((⊤ : Subgroup X).map ρ)) 2) :
    IsNatSL2Section ρ ⊥ ⊤ (fixSub ((⊤ : Subgroup X).map ρ)) 2 := by
  set W₂ : Submodule (ZMod 2) W := fixSub ((⊤ : Subgroup X).map ρ) with hW₂def
  have hW₂ : ∀ g : X, ∀ w ∈ W₂, ρ g w ∈ W₂ := by
    intro g w hw
    have hmem : ρ g ∈ (⊤ : Subgroup X).map ρ :=
      Subgroup.mem_map.mpr ⟨g, Subgroup.mem_top g, rfl⟩
    have hw' : w ∈ fixSub ((⊤ : Subgroup X).map ρ) := by
      rw [← hW₂def]; exact hw
    have hfix : (ρ g) w = w :=
      (mem_fixSub ((⊤ : Subgroup X).map ρ)).mp hw' (ρ g) hmem
    rw [hfix]
    exact hw
  unfold IsSumNatSection at hsum
  obtain ⟨s, hs, hsup, hind⟩ := hsum
  have hSL2 : ∀ U ∈ s, IsNatSL2Section ρ ⊥ U W₂ 2 := by
    intro U hU
    obtain ⟨-, -, hnat⟩ := hs U hU
    unfold IsNatSection at hnat
    rcases hnat with h | h
    · exact h
    · exfalso
      unfold IsNatSzSection at h
      obtain ⟨a, K, hKf, hKfin, φ, ψ, ha, hn, _⟩ := h
      omega
  have hsle : ∀ U ∈ s, W₂ ≤ U := fun U hU => (hSL2 U hU).1
  have hsinv : ∀ U ∈ s, ∀ g : X, ∀ u ∈ U, ρ g u ∈ U := fun U hU => (hSL2 U hU).2.1
  have hcard_le : s.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro U₁ hU₁ U₂ hU₂
    by_contra hne
    have hSL1 := hSL2 U₁ hU₁
    have hSL2' := hSL2 U₂ hU₂
    unfold IsNatSL2Section at hSL1 hSL2'
    obtain ⟨-, -, -, K₁, hK₁f, hK₁fin, φ₁, ψ₁, hcard₁, hφ₁surj, hφ₁ker,
      hψ₁surj, hψ₁ker, hψ₁eq⟩ := hSL1
    obtain ⟨-, -, -, K₂, hK₂f, hK₂fin, φ₂, ψ₂, hcard₂, hφ₂surj, hφ₂ker,
      hψ₂surj, hψ₂ker, hψ₂eq⟩ := hSL2'
    have h₁ : Nat.card K₁ = 4 := by rw [hcard₁]; norm_num
    have h₂ : Nat.card K₂ = 4 := by rw [hcard₂]; norm_num
    have hφ₁inj : Function.Injective φ₁ := (MonoidHom.ker_eq_bot_iff φ₁).mp hφ₁ker
    have hφ₁bij : Function.Bijective φ₁ := ⟨hφ₁inj, hφ₁surj⟩
    have hφ₂inj : Function.Injective φ₂ := (MonoidHom.ker_eq_bot_iff φ₂).mp hφ₂ker
    have hφ₂bij : Function.Bijective φ₂ := ⟨hφ₂inj, hφ₂surj⟩
    obtain ⟨Ψ₁, hΨ₁ext, hΨ₁zero, hΨ₁eq⟩ :=
      exists_projection_onto_summand ρ W₂ hW₂ s hsinv hsle hsup hind hU₁ φ₁ ψ₁ hψ₁ker hψ₁eq
    obtain ⟨Ψ₂, hΨ₂ext, hΨ₂zero, hΨ₂eq⟩ :=
      exists_projection_onto_summand ρ W₂ hW₂ s hsinv hsle hsup hind hU₂ φ₂ ψ₂ hψ₂ker hψ₂eq
    obtain ⟨T, hT⟩ := exists_equiv_of_natural hX h₁ h₂ hφ₁bij hφ₂bij
    have hΨ₁surj : Function.Surjective Ψ₁ := by
      intro v
      obtain ⟨u, hu⟩ := hψ₁surj v
      exact ⟨u, by rw [hΨ₁ext u, hu]⟩
    have hne0 : (Pi.single 0 (1 : K₂) : Fin 2 → K₂) ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp only [Pi.single_eq_same, Pi.zero_apply] at h0
      exact one_ne_zero h0
    obtain ⟨u₂, hu₂⟩ := hψ₂surj (Pi.single 0 (1 : K₂))
    have hu₂_ne : ψ₂ u₂ ≠ 0 := by rw [hu₂]; exact hne0
    have hmem_erase : U₂ ∈ s.erase U₁ := by
      rw [Finset.mem_erase]
      exact ⟨fun h => hne h.symm, hU₂⟩
    have hw₁ : (u₂ : W) ∈ (s.erase U₁).sup id ⊔ W₂ := by
      apply Submodule.mem_sup_left
      exact (Finset.le_sup (f := id) (s := s.erase U₁) hmem_erase) u₂.2
    have hΨ₁w : Ψ₁ (u₂ : W) = 0 := hΨ₁zero (u₂ : W) hw₁
    have hΨ₂w : Ψ₂ (u₂ : W) = ψ₂ u₂ := hΨ₂ext u₂
    exact false_of_two_projections hX ρ hB hstab hFc hFZ hZ hreg hgen hφ₁inj
      Ψ₁ Ψ₂ hΨ₁surj hΨ₁eq hΨ₂eq T hT
      ⟨(u₂ : W), hΨ₁w, by rw [hΨ₂w]; exact hu₂_ne⟩
  have hcard_eq : s.card = 1 := by
    have hpos : 0 < s.card := by
      rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
      intro hs0
      have hsup0 : s.sup id = ⊥ := by rw [hs0, Finset.sup_empty]
      rw [hsup0, bot_sup_eq] at hsup
      have htriv : ∀ g : X, ∀ z ∈ Z, ρ g z ∈ Z := by
        intro g z hz
        have hzW : z ∈ W₂ := by rw [hsup]; exact Submodule.mem_top
        have hmem : ρ g ∈ (⊤ : Subgroup X).map ρ :=
          Subgroup.mem_map.mpr ⟨g, Subgroup.mem_top g, rfl⟩
        have hzW' : z ∈ fixSub ((⊤ : Subgroup X).map ρ) := by
          rw [← hW₂def]; exact hzW
        have hfix : (ρ g) z = z :=
          (mem_fixSub ((⊤ : Subgroup X).map ρ)).mp hzW' (ρ g) hmem
        rw [hfix]
        exact hz
      have hBtop : B = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro g
        exact (hstab g).mpr (htriv g)
      rw [hBtop, Subgroup.index_top] at hB
      omega
    omega
  obtain ⟨U, hUeq⟩ := Finset.card_eq_one.mp hcard_eq
  have hU_mem : U ∈ s := by rw [hUeq]; exact Finset.mem_singleton_self U
  have hsupU : U ⊔ W₂ = ⊤ := by
    rw [hUeq, Finset.sup_singleton] at hsup
    exact hsup
  have hle : W₂ ≤ U := hsle U hU_mem
  have hUtop : U = ⊤ := by
    rw [sup_eq_left.mpr hle] at hsupU
    exact hsupU
  have hU := hSL2 U hU_mem
  rw [hUtop] at hU
  exact hU

end CFSG.LocalAnalysis.WeakClosure81.NatSum

end
