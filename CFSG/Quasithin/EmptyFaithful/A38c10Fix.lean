module

public import CFSG.Quasithin.Background.FLc2Simple
public import CFSG.Quasithin.Background.FLcAbs
public import CFSG.Quasithin.Background.FLcNat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Fix

variable {V : Type} [CommGroup V]

@[expose] def fixSub (u : V) : Subgroup (MulAut V) where
  carrier := {a | a u = u}
  one_mem' := rfl
  mul_mem' := fun {a b} ha hb => by
    show a (b u) = u
    rw [show b u = u from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    have h : a u = u := ha
    show a⁻¹ u = u
    calc a⁻¹ u = a⁻¹ (a u) := by rw [h]
      _ = u := by simp

theorem borelIso_with_g {A : Type} [Group A] [Finite A] {L B : Subgroup A} {n : ℕ} (hn : 1 ≤ n)
    (hB : IsSylowTwoOf B L) (e₀ : ↥L ≃* SLt n) :
    ∃ (g : SLt n) (D : BorelIso n L B), ∀ x : ↥L, D.e x = g⁻¹ * e₀ x * g := by
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hB
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective (f := e₀.toMonoidHom) e₀.surjective P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup ↥L).map e₀.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e₀.toMonoidHom) e₀.surjective P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular hn Q
  refine ⟨g, ⟨e₀.trans (MulAut.conj g⁻¹), ?_⟩, fun x => ?_⟩
  · have h1 : (B.subgroupOf L).map e₀.toMonoidHom = conjSub g (Ut n) := by
      rw [← hP, ← hQ, hg]
      rfl
    have h2 : (B.subgroupOf L).map (e₀.trans (MulAut.conj g⁻¹)).toMonoidHom =
        conjSub g⁻¹ ((B.subgroupOf L).map e₀.toMonoidHom) := by
      rw [conjSub, Subgroup.map_map]
      rfl
    rw [h2, h1, conjSub_inv_conjSub]
  · simp

theorem exists_borelIso_of_rho [Finite V] {Ls : Subgroup (MulAut V)} {UL' : Subgroup V} {R : Set ℕ} {n : ℕ}
    {ρ : SLt n →* MulAut V} (hn3 : 3 ≤ n) (hmem : ∀ g, ρ g ∈ Ls) (hsurj : ∀ k ∈ Ls, ∃ g, ρ g = k)
    (hfix : ∀ g : SLt n, ∀ v ∈ UL', (∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v) →
      ∀ i, ∀ hi : IsNode n i, i ∈ R → (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v)
    (hne : Ls ≠ ⊥) {B : Subgroup (MulAut V)} (hB : IsSylowTwoOf B Ls) :
    ∃ (g : SLt n) (D : BorelIso n Ls B),
      (∀ x : ↥Ls, ρ (g * D.e x * g⁻¹) = (x : MulAut V)) ∧
      (∀ y : SLt n, D.e ⟨ρ y, hmem y⟩ = g⁻¹ * y * g) ∧
      ∀ u ∈ UL', (∀ b ∈ B, (b : MulAut V) u = u) →
        D.cutsOf (Ls ⊓ fixSub u) ⊆ {i | IsNode n i ∧ i ∉ R} := by
  have hsimple : IsSimpleGroup (SLt n) := isSimpleGroup_SLt hn3
  have hinj : Function.Injective ρ := by
    refine injective_of_ne_one ρ ?_
    by_contra hall
    push Not at hall
    apply hne
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨g, rfl⟩ := hsurj k hk
    rw [hall g]
    exact Subgroup.one_mem _
  let ρ' : SLt n →* ↥Ls := ρ.codRestrict Ls hmem
  have hρ'b : Function.Bijective ρ' :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun k => by
      obtain ⟨g, hg⟩ := hsurj k.1 k.2
      exact ⟨g, Subtype.ext hg⟩⟩
  let e₀ : ↥Ls ≃* SLt n := (MulEquiv.ofBijective ρ' hρ'b).symm
  have he₀ : ∀ g : SLt n, e₀ (ρ' g) = g := fun g => (MulEquiv.ofBijective ρ' hρ'b).symm_apply_apply g
  have hρe₀ : ∀ x : ↥Ls, ρ (e₀ x) = (x : MulAut V) := fun x => by
    have h2' : ρ' (e₀ x) = x := (MulEquiv.ofBijective ρ' hρ'b).apply_symm_apply x
    exact congrArg Subtype.val h2'
  obtain ⟨g, D, hD⟩ := borelIso_with_g (by omega : 1 ≤ n) hB e₀
  have hρDe : ∀ x : ↥Ls, ρ (g * D.e x * g⁻¹) = (x : MulAut V) := by
    intro x
    have : g * D.e x * g⁻¹ = e₀ x := by
      rw [hD]
      group
    rw [this, hρe₀]
  refine ⟨g, D, hρDe, fun y => ?_, fun u hu huB => ?_⟩
  · rw [hD]
    have : e₀ ⟨ρ y, hmem y⟩ = y := he₀ y
    rw [this]
  have hBL : B ≤ Ls := hB.1
  set X : Subgroup (MulAut V) := Ls ⊓ fixSub u with hX
  have hBX : B ≤ X := fun b hb => ⟨hBL hb, huB b hb⟩
  have hUJ : Ut n ≤ D.model X := (D.Ut_le_model_iff hBL).2 hBX
  have hJ : D.model X = QI n (cuts (D.model X)) := eq_QI_cuts hUJ
  have hs : ∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) u = u := by
    intro s hs
    rw [← D.model_B] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    have hxB : (x : MulAut V) ∈ B := Subgroup.mem_subgroupOf.1 hx
    show (ρ (g * D.e x * g⁻¹)) u = u
    rw [hρDe]
    exact huB _ hxB
  intro i hic
  change i ∈ cuts (D.model X) at hic
  have hin : IsNode n i := isNode_of_mem_cuts hic
  refine ⟨hin, fun hiR => ?_⟩
  have hfx := hfix g u hu hs i hin hiR
  have hyL : ρ (g * reflection n (ZMod 2) i hin.1 hin.2 * g⁻¹) ∈ Ls := hmem _
  have hye : D.e ⟨ρ (g * reflection n (ZMod 2) i hin.1 hin.2 * g⁻¹), hyL⟩ =
      reflection n (ZMod 2) i hin.1 hin.2 := by
    rw [hD]
    have : e₀ ⟨ρ (g * reflection n (ZMod 2) i hin.1 hin.2 * g⁻¹), hyL⟩ =
        g * reflection n (ZMod 2) i hin.1 hin.2 * g⁻¹ := he₀ _
    rw [this]
    group
  have hrX : reflection n (ZMod 2) i hin.1 hin.2 ∈ D.model X := by
    rw [← hye]
    exact (D.mem_model _).2 ⟨hyL, hfx⟩
  rw [hJ] at hrX
  exact (reflection_mem_QI hin).1 hrX hic

end Fix

end CFSG.Quasithin.A38c10
