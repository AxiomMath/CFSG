module

public import CFSG.Quasithin.Background.SmithB51LnAut
public import CFSG.Quasithin.Background.SmithB51LnSum
public import CFSG.Quasithin.Background.B4HypCore

public section

namespace CFSG.Quasithin

namespace B42Ln

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln

theorem exists_statedSL_of_model {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) {n : ℕ}
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL n 2 1) :
    Nonempty (X ≃* ↥(StatedSL n (ZMod 2))) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  let e₁ : X ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hZK : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ :=
    center_eq_bot_of_equiv hK2 (specialLinearGroupEquivStatedSL n K)
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  obtain ⟨ι⟩ := exists_equiv_zmod_two hK2 n
  exact ⟨(e₁.trans e).trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    ((e₂.trans (specialLinearGroupEquivStatedSL n K)).trans ι.symm))⟩

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem le_G_core (h : B4HypCore G L) : L ≤ G := by
  rw [h.1]
  exact quasithinGenFitting_le G

theorem le_G (h : B4Hyp G L) : L ≤ G :=
  le_G_core h.core

theorem conj_mem_core (h : B4HypCore G L) {g : MulAut V} (hg : g ∈ G) {x : MulAut V}
    (hx : x ∈ L) : g * x * g⁻¹ ∈ L := by
  have hN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [h.1]
    exact le_normalizer_quasithinGenFitting G
  exact (Subgroup.mem_normalizer_iff.1 (hN hg) x).1 hx

theorem conj_mem_core' (h : B4HypCore G L) {g : MulAut V} (hg : g ∈ G) {x : MulAut V}
    (hx : x ∈ L) : g⁻¹ * x * g ∈ L := by
  have := conj_mem_core h (G.inv_mem hg) hx
  rwa [inv_inv] at this

theorem eq_one_of_commute_core (h : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥) {g : MulAut V}
    (hg : g ∈ G) (hc : ∀ x ∈ L, g * x = x * g) : g = 1 := by
  have hF : L = CFSG.Open.quasithinGenFitting G := h.1
  have h1 : g ∈ G ⊓ Subgroup.centralizer (CFSG.Open.quasithinGenFitting G : Set (MulAut V)) := by
    refine ⟨hg, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    rw [← hF] at hl
    exact (hc l hl).symm
  have h2 := centralizer_quasithinGenFitting_le G h1
  rw [← hF] at h2
  have h3 : (⟨g, h2⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.2).symm
  rw [hZ, Subgroup.mem_bot] at h3
  exact congrArg Subtype.val h3

theorem mem_of_inner_core (h : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥) {g : MulAut V}
    (hg : g ∈ G) {l : MulAut V} (hl : l ∈ L) (hinner : ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) :
    g ∈ L := by
  have hc : l⁻¹ * g = 1 := by
    refine eq_one_of_commute_core h hZ (G.mul_mem (G.inv_mem (le_G_core h hl)) hg) fun x hx => ?_
    have := hinner x hx
    calc l⁻¹ * g * x = l⁻¹ * (g * x * g⁻¹) * g := by group
      _ = l⁻¹ * (l * x * l⁻¹) * g := by rw [this]
      _ = x * (l⁻¹ * g) := by group
  have : g = l := by
    have := congrArg (l * ·) hc
    simpa [mul_assoc] using this
  rw [this]
  exact hl

theorem mem_of_inner (h : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥) {g : MulAut V} (hg : g ∈ G)
    {l : MulAut V} (hl : l ∈ L) (hinner : ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) : g ∈ L :=
  mem_of_inner_core h.core hZ hg hl hinner

variable {n : ℕ}

@[expose] noncomputable def piOf (e : ↥L ≃* ↥(StatedSL n (ZMod 2))) :
    ↥(StatedSL n (ZMod 2)) →* ↥L :=
  e.symm.toMonoidHom

omit [Finite V] in
theorem piOf_bijective (e : ↥L ≃* ↥(StatedSL n (ZMod 2))) : Function.Bijective (piOf e) :=
  e.symm.bijective

@[expose] noncomputable def conjAut_core (h : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL n (ZMod 2)))
    {g : MulAut V} (hg : g ∈ G) : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2)) :=
  conjSL (piOf_bijective e) (fun _ hx => conj_mem_core h hg hx)
    (fun _ hx => conj_mem_core' h hg hx)

@[expose] noncomputable def conjAut (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL n (ZMod 2)))
    {g : MulAut V} (hg : g ∈ G) : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2)) :=
  conjAut_core h.core e hg

theorem conjAut_spec_core (h : B4HypCore G L) (e : ↥L ≃* ↥(StatedSL n (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (γ : ↥(StatedSL n (ZMod 2))) :
    ((e.symm (conjAut_core h e hg γ) : ↥L) : MulAut V) = g * ((e.symm γ : ↥L) : MulAut V) * g⁻¹ :=
  conjSL_spec (piOf_bijective e) _ _ γ

theorem conjAut_spec (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL n (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (γ : ↥(StatedSL n (ZMod 2))) :
    ((e.symm (conjAut h e hg γ) : ↥L) : MulAut V) = g * ((e.symm γ : ↥L) : MulAut V) * g⁻¹ :=
  conjAut_spec_core h.core e hg γ

theorem outer_of_not_mem_core (h : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥) (hn : 3 ≤ n)
    (e : ↥L ≃* ↥(StatedSL n (ZMod 2))) {g : MulAut V} (hg : g ∈ G) (hgL : g ∉ L) :
    ∃ P : GL (Fin n) (ZMod 2), ∀ γ, mat (conjAut_core h e hg γ) =
      (P : Matrix (Fin n) (Fin n) (ZMod 2)) * dmat γ *
        ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  obtain ⟨P, hP | hP⟩ := aut_cases hn (conjAut_core h e hg)
  · exfalso
    apply hgL
    set l : ↥L := e.symm (ofGL P) with hl
    refine mem_of_inner_core h hZ hg l.2 fun x hx => ?_
    obtain ⟨γ, hγ⟩ := e.symm.surjective ⟨x, hx⟩
    have hx' : x = ((e.symm γ : ↥L) : MulAut V) := by rw [hγ]
    rw [hx', ← conjAut_spec_core h e hg γ]
    have hσ : conjAut_core h e hg γ = ofGL P * γ * (ofGL P)⁻¹ := by
      apply mat_injective
      rw [hP γ]
      rfl
    rw [hσ, map_mul, map_mul, map_inv]
    rfl
  · exact ⟨P, hP⟩

theorem outer_of_not_mem (h : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥) (hn : 3 ≤ n)
    (e : ↥L ≃* ↥(StatedSL n (ZMod 2))) {g : MulAut V} (hg : g ∈ G) (hgL : g ∉ L) :
    ∃ P : GL (Fin n) (ZMod 2), ∀ γ, mat (conjAut h e hg γ) =
      (P : Matrix (Fin n) (Fin n) (ZMod 2)) * dmat γ *
        ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  outer_of_not_mem_core h.core hZ hn e hg hgL

end B42Ln

end CFSG.Quasithin
