module

public import CFSG.LocalAnalysis.StandardType.GGKSmall7Defs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6Consumer
public import CFSG.LocalAnalysis.StandardType.GGDepED4Align
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpOf
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpClose

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGE6IndepFrame {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin 6 ≃ Λ),
    M = CoxeterMatrix.E₆.reindex e ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      Nonempty (M.Group ≃* ↥(ggAutomizer X Bs)) ∧ LinearIndependent (ZMod p) h

theorem ggTwoNodeIndepAtL_e6_of_frame
    (hAll : LR6E6All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K) (hBs : Nat.card ↥Bs ≤ 3 ^ 7)
    (hL : GGE6IndepFrame 3 Bs L) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  unfold GGE6IndepFrame at hL
  obtain ⟨Λ, hΛf, hΛd, M, C, V, hVadd, hVmod, ι, φ, h, α, e, hMeq, hC, hφ, hrefl, hpair,
    hAL, hfL, hind⟩ := hL
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  exact ggTwoNodeIndepAtL_e6 hAll hOrb hFix hFixK rfl hH hx hBs e hMeq hC hφ hrefl hpair
    hfL.some hAL hind

theorem ggDepED4UpCfg_of_aligned_dep (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K) (hCard : Nat.card ↥Bs = 3 ^ 7)
    (hXL : GGResXDatumE6Core 3 Bs L) (hno : ¬ GGE6IndepFrame 3 Bs L)
    (hA : GGDepED4Aligned 3 2 Bs L J K) : GGDepED4UpCfg 3 2 Bs L J K := by
  classical
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hML, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let ΦK : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hAKrange : Set.range ΦK =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hAK' : ggAutomizer K Bs = Subgroup.closure (Set.range ΦK) := by
    rw [hAK, ← hAKrange]
  have hcart := l05nEU_cartan_of_reindex e hCLcartan hML
  have hdep : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)) := by
    intro hli
    apply hno
    obtain ⟨Λ₁, hΛ₁f, hΛ₁d, M₁, C₁, V₁, hV₁add, hV₁mod, ι₁, φ₁, h₁, α₁, e₁,
      hM₁, hWM₁, hC₁, hlin₁, hrefl₁, hpair₁, f₁ex, hclos₁⟩ := hXL
    obtain ⟨f₁, hf₁⟩ := f₁ex
    refine ⟨Λ, hΛf, hΛd, ML, CL, V, hVadd, hVmod, ι, (fun i => φ (Sum.inl i)),
      (fun i => h (Sum.inl i)), (fun i => α (Sum.inl i)), e, hML, hCLcartan, ?_, ?_, ?_, hAL,
      ?_, hli⟩
    · exact fun i w => hform (Sum.inl i) w
    · exact fun i => hrefl (Sum.inl i)
    · exact fun i j => hpairL i j
    · subst hML
      subst hM₁
      exact ⟨(((CoxeterMatrix.E₆).reindexGroupEquiv e).trans
        (((CoxeterMatrix.E₆).reindexGroupEquiv e₁).symm)).trans f₁⟩
  have hx1 : (⟨x, hx⟩ : ↥Bs) ≠ 1 := by
    intro h1
    exact l05nDD1_x_ne_one hH (by simpa using congrArg Subtype.val h1)
  have hxVne : xV ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := ι.injective (by simpa [xV] using h0)
    have h2 : (⟨x, hx⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  let φ₀ : Option Λ → MulAut ↥Bs := fun o => φ (Sum.inl (o.getD b₁))
  let h₀ : Option Λ → V := fun o => h (Sum.inl (o.getD b₁))
  let α₀ : Option Λ → Module.Dual (ZMod 3) V := fun o => α (Sum.inl (o.getD b₁))
  have hform₀ : ∀ o w, ggLin (p := 3) ι (φ₀ o) w = w - α₀ o w • h₀ o :=
    fun o w => hform (Sum.inl (o.getD b₁)) w
  have hpair₀ : ∀ i j : Λ, α₀ (some i) (h₀ (some j)) = (CL i j : ZMod 3) := fun i j => hpairL i j
  have hAL₀ : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ₀ (some i)) := by
    simpa [φ₀] using hAL
  have hαx : ∀ i : Fin 6, α (Sum.inl (e i)) xV = 0 := by
    intro i
    have h := l05nDD1_alpha_x (p := 3) hp2 hH hx hform₀ hpair₀ hCLcartan hAL₀ (e i)
    simpa [α₀, xV] using h
  have hframe : GGDepEFrame 3 (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV :=
    { p3 := rfl
      pair := fun i j => by
        rw [hpairL (e i) (e j), hcart i j]
      x_ne := hxVne
      x_ker := hαx
      fix := fun v hv =>
        l05nDD1_fix hFix hH hx hform₀ hAL₀ v (fun j => by
          have hj := hv (e.symm j)
          simpa [α₀] using hj)
      dep := fun hli => hdep ((linearIndependent_equiv (R := ZMod 3) e).mp hli) }
  have hxker : ∀ i : Λ, α (Sum.inl i) xV = 0 := by
    intro i
    have h := hframe.x_ker (e.symm i)
    simpa using h
  have hfinrank : Module.finrank (ZMod 3) V = 7 := by
    haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
    have hVcard : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 7 := by
      rw [← hVcard, hcardV, hCard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq
  refine ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, MK, CK, V, hVadd, hVmod, ι, e, φ, h, α,
    xV, ?_⟩
  refine ⟨⟨hb1, hb2, hcardΛa, hMKweyl, hCKcartan, hk2, hform, hframe, hpairK, ?_, ?_, ?_,
    hAJ⟩, hfinrank⟩
  · intro g hg
    obtain ⟨ψ, hψ, hψg⟩ := l05nEU_exists_psi (p := 3) ι φ g hg
    rw [← hψg]
    exact ggTT_nt_sup hH ι (by rw [l05nEU_sup_eq φ hAL hAK]; exact hψ)
  · by_contra hnoK
    push Not at hnoK
    have hfixgen : ∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa, ΦK o ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro o
      apply (ggLin_fix_iff (p := 3) ι (ΦK o) (⟨x, hx⟩ : ↥Bs)).mpr
      cases o with
      | inl j =>
          show ggLin (p := 3) ι (φ (Sum.inl j.1)) xV = xV
          rw [hform (Sum.inl j.1) xV, hxker j.1, zero_smul, sub_zero]
      | inr a =>
          show ggLin (p := 3) ι (φ (Sum.inr a)) xV = xV
          rw [hform (Sum.inr a) xV, hnoK a, zero_smul, sub_zero]
    have hfix : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro ψ hψ
      rw [hAK'] at hψ
      exact ggFixed_of_mem_closure ΦK (⟨x, hx⟩ : ↥Bs) hfixgen ψ hψ
    exact ggTT_not_fixed hFixK hH hx hfix
  · exact l05nEU_sup_eq φ hAL hAK

theorem ggKSmall7_e6_weyl
    (hAll : LR6E6All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K) (h7 : Nat.card ↥Bs = 3 ^ 7)
    (hXL : GGResXDatumE6Core 3 Bs L) (hXK : GGResXDatumE6Core 3 Bs K)
    (hLd : GGResTwoNodeSideDatum 3 Bs L J) (hKd : GGResTwoNodeSideDatum 3 Bs K J)
    (hJ : Nat.card ↥(ggAutomizer J Bs) = 192) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hA : GGDepED4Aligned 3 2 Bs L J K := ggDepED4_align_two_core hp2 hXL hXK hLd hKd hJ
  by_cases hL : GGE6IndepFrame 3 Bs L
  · exact ggTwoNodeIndepAtL_e6_of_frame hAll hOrb hFix hFixK hH (le_of_eq h7) hL
  · exact (ggDepED4Up_false_two
      (ggDepED4UpCfg_of_aligned_dep hFix hFixK hH h7 hXL hL hA)).elim

end CFSG.StandardType

end
