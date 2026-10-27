module

public import CFSG.RankThree.PartOne.TCX.LayerEngineG
public import CFSG.RankThree.PartOne.TCX.NormSeq
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.TCX.F4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX

section Shintani

variable {C : Type} [Group C] {L : Type} [Field L]

structure IsShintani (p : ℕ) (ι : C →* ModGL TwistTag.D4.tag L)
    (F₀ Φ : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L) (α₀ : MulAut C) : Prop where
  inj : Function.Injective ι
  mem : ∀ y, ι y ∈ adjointGroup TwistTag.D4.tag L
  iter : ∀ u, Φ u = (⇑F₀)^[p] u
  actor : ∀ y, ι (α₀ y) = F₀ (ι y)
  fix : ∀ y, Φ (ι y) = ι y
  range : ∀ u ∈ adjointGroup TwistTag.D4.tag L, Φ u = u → u ∈ ι.range

variable {p : ℕ} {ι : C →* ModGL TwistTag.D4.tag L}
  {F₀ Φ : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

theorem IsShintani.fix_mem_range (h : IsShintani p ι F₀ Φ α₀) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ adjointGroup TwistTag.D4.tag L) (hF : F₀ u = u) : u ∈ ι.range :=
  h.range u hu (by rw [h.iter, Function.iterate_fixed hF])

theorem IsShintani.actor_fixed_iff (h : IsShintani p ι F₀ Φ α₀) (y : C) :
    α₀ y = y ↔ F₀ (ι y) = ι y := by
  rw [← h.actor y]
  exact ⟨fun hy => by rw [hy], fun hy => h.inj hy⟩

end Shintani

section Layer

variable {C : Type} [Group C] [Finite C] {L : Type} [Field L] {p : ℕ}
  {ι : C →* ModGL TwistTag.D4.tag L}
  {F₀ Φ : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

theorem hstab_D4 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (a : Fin TwistTag.D4.tag.rank → Lˣ)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup TwistTag.D4.tag)) :=
  rootCharStabilizer_subset_closure hp (not_dvd_card_weylGroup_D4 hp hp3) hap ha1

theorem twistedTorusOf_le_nseq {τ : Tag} {n₀ : ModGL τ L}
    {F₀ Φ : ModGL τ L →* ModGL τ L} (p : ℕ) (hΦ : ∀ u, Φ u = (⇑F₀)^[p] u) :
    twistedTorusOf n₀ F₀ ≤ twistedTorusOf (nseq n₀ F₀ p) Φ := by
  intro u hu
  obtain ⟨hH, hfix⟩ := mem_twistedTorusOf.1 hu
  refine mem_twistedTorusOf.2 ⟨hH, ?_⟩
  rw [hΦ]
  exact nseq_conj_fixed hfix p

theorem tri_layer_of_frame (h : IsShintani p ι F₀ Φ α₀) (hp : p.Prime) (hp3 : 3 < p)
    (hodd : ∀ t ∈ torusGroup TwistTag.D4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    {n₀ g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : F₀ g₀ = g₀ * n₀)
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α)
    (hSn : ∀ α ∈ S, -α ∈ S) (P : Unit → Subgroup (ModGL TwistTag.D4.tag L))
    (hfam : IsSigmaFamilyΦ (nseq n₀ F₀ p) Φ S P)
    (hjoin : rootSpan TwistTag.D4.tag L S ⊓ twistedFixedPoints (nseq n₀ F₀ p) Φ ≤ P ())
    {x : C} (hx : orderOf x = p) {c : C} (hcα : α₀ c = c)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g₀⁻¹ * ι (c * x * c⁻¹) * g₀)
    (hbT : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf n₀ F₀)
    (hbS : rootCharKernel b ⊆ S)
    (hbc : rootDiagUnit TwistTag.D4.tag b ∈
      Subgroup.centralizer (rootSpan TwistTag.D4.tag L S : Set (ModGL TwistTag.D4.tag L)))
    (hmodel : ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL TwistTag.D4.tag L) (τ' : D →* D),
      Function.Injective ρ' ∧ ρ'.range = P () ∧
      (∀ d, n₀ * F₀ (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaimsF4 p α Q) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  have hΦg₀ : Φ g₀ = g₀ * nseq n₀ F₀ p := by
    rw [h.iter, iterate_lang_nseq hg₀]
  have hc : c * x * c⁻¹ ∈ subtorusImage ι g₀ (subtorusSigma (nseq n₀ F₀ p) Φ S) := by
    rw [mem_subtorusImage_iff, ← hb]
    exact Subgroup.mem_inf.2 ⟨twistedTorusOf_le_nseq p h.iter hbT, hbc⟩
  have hkerZ : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ → rootCharKernel a ⊆ S := by
    intro a ha
    have hab : a = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) (ha.trans hb.symm)
    rw [hab]
    exact hbS
  exact singleLayerData_of_engineG ι h.inj h.mem F₀ Φ α₀ h.actor hp h.fix hodd n₀
    (nseq n₀ F₀ p) g₀ hg₀C hg₀ hΦg₀
    (fun P' _ hP'C hP'F _ u hu => h.range u (hP'C hu) (hP'F u hu))
    (fun a hap ha1 _ => hstab_D4 hp hp3 a hap ha1) hS hSn P hfam hjoin hx c hcα hc hkerZ hmodel

omit [Finite C] in
theorem tri_regular_of_frame (h : IsShintani p ι F₀ Φ α₀) (hp : p.Prime) (hp3 : 3 < p)
    {n₀ g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : F₀ g₀ = g₀ * n₀) {x : C} (hx : orderOf x = p) {c : C}
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g₀⁻¹ * ι (c * x * c⁻¹) * g₀)
    (hbT : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf n₀ F₀)
    (hbE : rootCharKernel b = ∅) :
    ∃ ψ : Subgroup.centralizer ({x} : Set C) →* ModGL TwistTag.D4.tag L,
      Function.Injective ψ ∧ (∀ y, ψ y = g₀⁻¹ * ι (c * (y : C) * c⁻¹) * g₀) ∧
      (∀ y, ψ y ∈ torusGroup TwistTag.D4.tag L) ∧
      ∀ y, ψ y ∈ twistedTorusOf (nseq n₀ F₀ p) Φ := by
  have hΦg₀ : Φ g₀ = g₀ * nseq n₀ F₀ p := by
    rw [h.iter, iterate_lang_nseq hg₀]
  have hspan : rootSpan TwistTag.D4.tag L (∅ : Set (Fin TwistTag.D4.tag.rank → ℤ)) = ⊥ := by
    simp [rootSpan]
  have hc : c * x * c⁻¹ ∈ subtorusImage ι g₀ (subtorusSigma (nseq n₀ F₀ p) Φ ∅) := by
    rw [mem_subtorusImage_iff, ← hb]
    refine Subgroup.mem_inf.2 ⟨twistedTorusOf_le_nseq p h.iter hbT, ?_⟩
    rw [hspan]
    exact fun g hg => by
      have : g = 1 := hg
      rw [this, one_mul, mul_one]
  have hkerZ : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ → rootCharKernel a ⊆ ∅ := by
    intro a ha
    have hab : a = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) (ha.trans hb.symm)
    rw [hab, hbE]
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψfix, -, -, -⟩ := sigma_embedding_data_of_stab ι h.inj h.mem Φ
    h.fix (nseq n₀ F₀ p) g₀ hg₀C hΦg₀
    (fun P' _ hP'C hP'F _ u hu => h.range u (hP'C hu) (hP'F u hu)) hp
    (fun a hap ha1 _ => hstab_D4 hp hp3 a hap ha1) (S := ∅) (by simp)
    (by simp) (ι' := Empty) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun y hy hyR _ => by
      rw [hspan, sup_bot_eq] at hy
      refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, mem_twistedFixedPoints.1 hyR⟩, ?_⟩
      rw [hspan]
      exact fun g hg => by
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
    hx c hc hkerZ
  have hψt : ∀ y, ψ y ∈ torusGroup TwistTag.D4.tag L := fun y => by
    have := hψHQ y
    rwa [hspan, sup_bot_eq] at this
  exact ⟨ψ, hψinj, hψ, hψt, fun y => mem_twistedTorusOf.2 ⟨hψt y, hψfix y⟩⟩

end Layer

end CFSG.RankThree.PartOne.TCX.Tri
