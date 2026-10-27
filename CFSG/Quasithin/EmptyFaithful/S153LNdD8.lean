module

public import CFSG.Quasithin.Background.B5FinS8Core
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace S153L

private def nd8Wt (v : Fin 8 → ZMod 2) : ℕ := ∑ i, if v i = 0 then 0 else 1

private def nd8Cls (v : Fin 8 → ZMod 2) : ℕ := min (nd8Wt v) (8 - nd8Wt v)

private def nd8Rep (c : ℕ) : Finset (Fin 8 → ZMod 2) :=
  Finset.univ.filter fun v => v 0 = 0 ∧ ∑ i, v i = 0 ∧ nd8Cls v = c

private theorem nd8Cls_cases :
    ∀ m : Fin 8 → ZMod 2, ∑ i, m i = 0 → nd8Cls m = 0 ∨ nd8Cls m = 2 ∨ nd8Cls m = 4 := by
  decide +kernel

private theorem nd8Rep_zero : (nd8Rep 0).card = 1 := by decide +kernel

private theorem nd8Rep_two : (nd8Rep 2).card = 28 := by decide +kernel

private theorem nd8Rep_four : (nd8Rep 4).card = 35 := by decide +kernel

private theorem nd8Cls_add_one :
    ∀ v : Fin 8 → ZMod 2, nd8Cls (fun i => v i + 1) = nd8Cls v := by
  decide +kernel

private theorem nd8Sum_add_one :
    ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ∑ i, (v i + 1) = 0 := by
  decide +kernel

private theorem nd8Rep_card_le (m : Fin 8 → ZMod 2) (hm : ∑ i, m i = 0) :
    (nd8Rep (nd8Cls m)).card ≤ 35 := by
  rcases nd8Cls_cases m hm with h | h | h <;> rw [h]
  · rw [nd8Rep_zero]
    norm_num
  · rw [nd8Rep_two]
    norm_num
  · rw [nd8Rep_four]

private theorem nd8Cls_perm (σ : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) :
    nd8Cls (fun i => v (σ⁻¹ i)) = nd8Cls v := by
  have : nd8Wt (fun i => v (σ⁻¹ i)) = nd8Wt v :=
    Equiv.sum_comp σ⁻¹ (fun i => if v i = 0 then 0 else 1)
  unfold nd8Cls
  rw [this]

private def nd8Elt (v : Fin 8 → ZMod 2) (h : ∑ i, v i = 0) : ↥(FFModel.symDn 8).sec :=
  ⟨Multiplicative.ofAdd v, (G6.mem_coreMod).2 h⟩

private def nd8Mk (v : Fin 8 → ZMod 2) (h : ∑ i, v i = 0) : (FFModel.symDn 8).Mod :=
  QuotientGroup.mk (nd8Elt v h)

private theorem nd8Mk_add_one (v : Fin 8 → ZMod 2) (h : ∑ i, v i = 0)
    (h' : ∑ i, (v i + 1) = 0) : nd8Mk (fun i => v i + 1) h' = nd8Mk v h := by
  unfold nd8Mk
  symm
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hone : ((nd8Elt v h)⁻¹ * nd8Elt (fun i => v i + 1) h' : ↥(FFModel.symDn 8).sec).1 =
      G6.allOnes 8 := by
    apply Multiplicative.toAdd.injective
    funext i
    show -(v i) + (v i + 1) = 1
    abel
  change _ ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8
  rw [hone]
  exact ⟨Subgroup.mem_zpowers _, (G6.mem_coreMod).2 (by decide +kernel)⟩

private theorem nd8_exists_cover (x : (FFModel.symDn 8).Mod) :
    ∃ S : Finset (FFModel.symDn 8).Mod, S.card ≤ 35 ∧
      ∀ σ : Equiv.Perm (Fin 8), (FFModel.symDn_isActionModel 8).modAct σ x ∈ S := by
  classical
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  set m₀ : Fin 8 → ZMod 2 := Multiplicative.toAdd (m.1 : G6.PermMod 8) with hm₀def
  have hm₀ : ∑ i, m₀ i = 0 := (G6.mem_coreMod).1 m.2
  let mkE : (Fin 8 → ZMod 2) → (FFModel.symDn 8).Mod := fun v =>
    if h : ∑ i, v i = 0 then nd8Mk v h else 1
  refine ⟨(nd8Rep (nd8Cls m₀)).image mkE, Finset.card_image_le.trans (nd8Rep_card_le m₀ hm₀), ?_⟩
  intro σ
  have hvs : ∑ i, m₀ (σ⁻¹ i) = 0 := (Equiv.sum_comp σ⁻¹ m₀).trans hm₀
  have hσ : (FFModel.symDn_isActionModel 8).modAct σ (QuotientGroup.mk m) =
      nd8Mk (fun i => m₀ (σ⁻¹ i)) hvs := rfl
  rw [hσ, Finset.mem_image]
  by_cases h0 : m₀ (σ⁻¹ 0) = 0
  · refine ⟨fun i => m₀ (σ⁻¹ i), ?_, ?_⟩
    · rw [nd8Rep, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h0, hvs, nd8Cls_perm σ m₀⟩
    · exact dite_eq_left hvs
  · have hws : ∑ i, (m₀ (σ⁻¹ i) + 1) = 0 := nd8Sum_add_one _ hvs
    refine ⟨fun i => m₀ (σ⁻¹ i) + 1, ?_, ?_⟩
    · rw [nd8Rep, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hws, ?_⟩
      · have key : ∀ a : ZMod 2, a ≠ 0 → a + 1 = 0 := by decide
        exact key _ h0
      · rw [nd8Cls_add_one (fun i => m₀ (σ⁻¹ i))]
        exact nd8Cls_perm σ m₀
    · exact (dite_eq_left hws).trans (nd8Mk_add_one _ hvs hws)

theorem d8_stab {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hL : Nat.card ↥L = 20160) (_hZ : Z ≤ fixV L ⊓ U) (hZ2 : Nat.card ↥Z ≤ 2)
    (hd8 : SLExteriorTwo L U Z 4) :
    ∀ u ∈ U, ∃ H : Subgroup (MulAut V), H ≤ L ∧ (∀ g ∈ H, (g : MulAut V) u = u) ∧
      288 ≤ Nat.card ↥H := by
  classical
  intro u hu
  obtain ⟨π, hπs, -, -, hUinv, -, hsec, -, β, -, hβk, hβe⟩ := hd8
  have hE := FFModel.extSq_isActionModel (ZMod 2) 4
  let ρ : Equiv.Perm (Fin 8) →* MulAut (FFModel.symDn 8).Mod :=
    (FFModel.symDn_isActionModel 8).modAct
  have hβmod : ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (w : ↥U)
      (hw : ((π γ : ↥L) : MulAut V) (w : V) ∈ U),
      β ⟨((π γ : ↥L) : MulAut V) (w : V), hw⟩ = hE.modAct γ (β w) := by
    intro γ w hw
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β w)
    rw [← hm]
    exact hβe γ w m hw (hsec γ m m.2) hm.symm
  have hξ : ∀ (σ : alternatingGroup (Fin 8)) (w : ↥U)
      (hw : ((π (B5FinS8.alpha σ) : ↥L) : MulAut V) (w : V) ∈ U),
      B5FinS8.G8.symm (β ⟨((π (B5FinS8.alpha σ) : ↥L) : MulAut V) (w : V), hw⟩) =
        ρ (σ : Equiv.Perm (Fin 8)) (B5FinS8.G8.symm (β w)) := by
    intro σ w hw
    rw [hβmod (B5FinS8.alpha σ) w hw]
    have h1 := B5FinS8.G8_modAct σ (B5FinS8.G8.symm (β w))
    rw [MulEquiv.apply_symm_apply] at h1
    rw [MulEquiv.symm_apply_eq]
    exact h1.symm
  obtain ⟨S, hS35, hS⟩ := nd8_exists_cover (B5FinS8.G8.symm (β ⟨u, hu⟩))
  let ξ : V → (FFModel.symDn 8).Mod := fun a =>
    if ha : a ∈ U then B5FinS8.G8.symm (β ⟨a, ha⟩) else 1
  let O : Finset V := (Set.toFinite (MulAction.orbit ↥L u)).toFinset
  have hO : ∀ a ∈ O, ∃ g : ↥L, (g : MulAut V) u = a := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    obtain ⟨g, rfl⟩ := ha
    exact ⟨g, rfl⟩
  have hOU : ∀ a ∈ O, a ∈ U := by
    intro a ha
    obtain ⟨g, rfl⟩ := hO a ha
    exact hUinv g u hu
  have hOS : ∀ a ∈ O, ξ a ∈ S := by
    intro a ha
    obtain ⟨g, rfl⟩ := hO a ha
    obtain ⟨γ, hγ⟩ := hπs g
    obtain ⟨σ, rfl⟩ := B5FinS8.alpha_surjective γ
    subst hγ
    have hw : ((π (B5FinS8.alpha σ) : ↥L) : MulAut V) u ∈ U := hUinv _ u hu
    have e : ξ (((π (B5FinS8.alpha σ) : ↥L) : MulAut V) u) =
        ρ (σ : Equiv.Perm (Fin 8)) (B5FinS8.G8.symm (β ⟨u, hu⟩)) := by
      simp only [ξ]
      rw [dite_eq_left hw]
      exact hξ σ ⟨u, hu⟩ hw
    rw [e]
    exact hS _
  have hfib : ∀ b ∈ S, (O.filter fun a => ξ a = b).card ≤ 2 := by
    intro b _
    by_cases hne : (O.filter fun a => ξ a = b).Nonempty
    · obtain ⟨w₀, hw₀⟩ := hne
      rw [Finset.mem_filter] at hw₀
      have hw₀U := hOU w₀ hw₀.1
      have hZf : (Set.toFinite (Z : Set V)).toFinset.card ≤ 2 := by
        rw [← Nat.card_eq_card_finite_toFinset]
        exact hZ2
      refine (Finset.card_le_card_of_injOn (fun w => w * w₀⁻¹) ?_ ?_).trans hZf
      · intro w hw
        rw [Finset.mem_coe, Finset.mem_filter] at hw
        have hwU := hOU w hw.1
        have e1 : B5FinS8.G8.symm (β ⟨w, hwU⟩) = B5FinS8.G8.symm (β ⟨w₀, hw₀U⟩) := by
          have a1 := hw.2
          have a2 := hw₀.2
          simp only [ξ, dite_eq_left hwU, dite_eq_left hw₀U] at a1 a2
          rw [a1, a2]
        have e2 : β ⟨w, hwU⟩ = β ⟨w₀, hw₀U⟩ := B5FinS8.G8.symm.injective e1
        have e3 : β (⟨w, hwU⟩ * ⟨w₀, hw₀U⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, e2, mul_inv_cancel]
        have e4 : w * w₀⁻¹ ∈ Z := (hβk _).1 e3
        simpa using e4
      · intro w _ w' _ hww
        simpa using hww
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hOcard : O.card ≤ 70 := by
    have h1 := Finset.card_le_mul_card_image_of_maps_to hOS 2 hfib
    omega
  have hos : Nat.card (MulAction.orbit ↥L u) * Nat.card (MulAction.stabilizer ↥L u) =
      Nat.card ↥L := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥L u)
  have horb : Nat.card (MulAction.orbit ↥L u) = O.card := Nat.card_eq_card_finite_toFinset _
  refine ⟨(MulAction.stabilizer ↥L u).map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact hg
  · rw [Subgroup.card_subtype]
    rw [horb, hL] at hos
    have h2 : 20160 ≤ 70 * Nat.card (MulAction.stabilizer ↥L u) :=
      calc 20160 = O.card * Nat.card (MulAction.stabilizer ↥L u) := hos.symm
        _ ≤ 70 * Nat.card (MulAction.stabilizer ↥L u) := Nat.mul_le_mul_right _ hOcard
    omega

end S153L

end CFSG.Quasithin
