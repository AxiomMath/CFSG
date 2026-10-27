module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nLO_exists_psi {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {Λ Λa : Type} (φ : Λ ⊕ Λa → MulAut ↥Bs) :
    ∀ g ∈ Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)),
      ∃ ψ ∈ Subgroup.closure (Set.range φ), ggLin (p := p) ι ψ = g := by
  intro g hg
  have himg : Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)) =
      (ggLin (p := p) ι) '' Set.range φ := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      exact ⟨φ o, ⟨o, rfl⟩, rfl⟩
    · rintro ⟨ψ, ⟨o, rfl⟩, rfl⟩
      exact ⟨o, rfl⟩
  rw [himg, ← MonoidHom.map_closure] at hg
  exact Subgroup.mem_map.mp hg

private theorem l05nLO_sup_eq {G : Type} [Group G] {Bs L K : Subgroup G}
    {Λ Λa : Type} {b₁ b₂ : Λ} (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range fun a : Λa => φ (Sum.inr a))) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) := by
  rw [hAL, hAK, ← Subgroup.closure_union]
  congr 1
  ext z
  constructor
  · rintro (⟨i, rfl⟩ | h)
    · exact ⟨Sum.inl i, rfl⟩
    · rcases h with ⟨j, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨Sum.inl j.1, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  · rintro ⟨o, rfl⟩
    cases o with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr a => exact Or.inr (Or.inr ⟨a, rfl⟩)

theorem ggTWLowCfg_of_aligned (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hxL : x ∉ L) {N k : ℕ} (hk : k = 1 ∨ k = 2) (hp : 3 ≤ p) (hN : N = 5 ∨ N = 6 ∨ N = 9)
    (hpN : p ∣ N) (hCard : Nat.card ↥Bs = p ^ (N - 1)) (hHL : GGTWHLAt p Bs L x)
    (hHK : GGTWHLAt p Bs K y) (hA : GGTWAligned p N k Bs L J K) :
    GGTWLowCfg p N k Bs L J K x y := by
  classical
  obtain ⟨pos, Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb12, hcardΛa, hpos, hMLeq, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := by omega
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hN5 : 5 ≤ N := by rcases hN with h' | h' | h' <;> omega
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let yV : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
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
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) :=
    l05nLO_sup_eq φ hAL hAK
  have hdep : ¬ LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    ggXDatumA_dep hFix hp2 hH hx hxL hN5 hpN e hMLeq hCLcartan
      (ι := ι) (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hform (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hAL)
  have hframe : GGDepAFrame p N (fun i : Fin (N - 1) => h (Sum.inl (e i)))
      (fun i : Fin (N - 1) => α (Sum.inl (e i))) xV :=
    ggXDatumA_frame hFix hp2 hH hx hN5 hpN e hMLeq hCLcartan
      (ι := ι) (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hform (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hAL) (hdep := hdep)
  have hxker : ∀ i : Λ, α (Sum.inl i) xV = 0 := by
    intro i
    simpa using hframe.x_ker (e.symm i)
  have hfixy : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ :=
    ggRC_automizer_fixes_y hy hKy
  have hfinrank : Module.finrank (ZMod p) V = N - 1 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : p ^ Module.finrank (ZMod p) V = p ^ (N - 1) := by
      rw [← hVcard, hcardV, hCard]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le heq
  refine ⟨pos, Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, MK, CK, V, hVadd, hVmod, ι, e, φ, h, α,
    xV, yV, hx, hy, rfl, rfl, ?_, hfinrank, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hb12, hcardΛa, hpos, hMKweyl, hCKcartan, hk2, hform, hframe, hpairK, ?_, ?_, hsup,
      hAJ⟩
    · intro g hg
      obtain ⟨ψ, hψ, hψg⟩ := l05nLO_exists_psi (p := p) ι φ g hg
      rw [← hψg]
      exact ggTT_nt_sup hH ι (by rw [hsup]; exact hψ)
    · by_contra hno
      push Not at hno
      have hfixgen : ∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa, ΦK o ⟨x, hx⟩ = ⟨x, hx⟩ := by
        intro o
        apply (ggLin_fix_iff (p := p) ι (ΦK o) (⟨x, hx⟩ : ↥Bs)).mpr
        cases o with
        | inl j =>
            show ggLin (p := p) ι (φ (Sum.inl j.1)) xV = xV
            rw [hform (Sum.inl j.1) xV, hxker j.1, zero_smul, sub_zero]
        | inr a =>
            show ggLin (p := p) ι (φ (Sum.inr a)) xV = xV
            rw [hform (Sum.inr a) xV, hno a, zero_smul, sub_zero]
      have hfix : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
        intro ψ hψ
        rw [hAK'] at hψ
        exact ggFixed_of_mem_closure ΦK (⟨x, hx⟩ : ↥Bs) hfixgen ψ hψ
      exact ggTT_not_fixed hFixK hH hx hfix
  · intro g hg hgref hgx
    obtain ⟨ψ, hψ, hψg⟩ := l05nLO_exists_psi (p := p) ι φ g hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
        sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
      have hmem : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
        rw [hsup]
        exact hψ
      have hmem' := hle hmem
      rwa [ggAutomizer_eq] at hmem'
    have hψrefl : GGIsReflection p ψ := by
      rw [ggIsReflection_iff_ggLinRefl hp2 ι ψ]
      rw [hψg]
      exact hgref
    have hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [ggLin_fix_iff (p := p) ι ψ ⟨x, hx⟩]
      rw [hψg]
      exact hgx
    obtain ⟨hxB, hHLbody⟩ := hHL
    have hb_eq : (⟨x, hxB⟩ : ↥Bs) = ⟨x, hx⟩ := Subtype.ext rfl
    have hψx' : ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by rw [hb_eq]; exact hψx
    have hlines := hHLbody (M := ML) (C := CL) hMLweyl hCLcartan ι
      (fun i : Λ => φ (Sum.inl i)) (fun i : Λ => h (Sum.inl i)) (fun i : Λ => α (Sum.inl i))
      (fun i w => hform (Sum.inl i) w) (fun i => hrefl (Sum.inl i))
      (fun i j => hpairL i j) hAL ψ hψind hψrefl hψx'
    simpa only [hb_eq, hψg] using hlines
  · intro hyV0
    apply ggRC_y_ne_one hH
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := by
      apply ι.injective
      simpa only [yV, map_zero] using hyV0
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h1
    exact congrArg Subtype.val h2
  · intro i
    have hmem : φ (Sum.inl i.1) ∈ ggAutomizer K Bs := by
      rw [hAK']
      exact Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
    exact (ggLin_fix_iff (p := p) ι (φ (Sum.inl i.1)) (⟨y, hy⟩ : ↥Bs)).mp
      (hfixy (φ (Sum.inl i.1)) hmem)
  · intro a
    have hmem : φ (Sum.inr a) ∈ ggAutomizer K Bs := by
      rw [hAK']
      exact Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
    exact (ggLin_fix_iff (p := p) ι (φ (Sum.inr a)) (⟨y, hy⟩ : ↥Bs)).mp
      (hfixy (φ (Sum.inr a)) hmem)
  · intro g hg hgref hgy
    obtain ⟨ψ, hψ, hψg⟩ := l05nLO_exists_psi (p := p) ι φ g hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
        sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
      have hmem : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
        rw [hsup]
        exact hψ
      have hmem' := hle hmem
      rwa [ggAutomizer_eq] at hmem'
    have hψrefl : GGIsReflection p ψ := by
      rw [ggIsReflection_iff_ggLinRefl hp2 ι ψ]
      rw [hψg]
      exact hgref
    have hψy : ψ ⟨y, hy⟩ = ⟨y, hy⟩ := by
      rw [ggLin_fix_iff (p := p) ι ψ ⟨y, hy⟩]
      rw [hψg]
      exact hgy
    obtain ⟨hyB, hHKbody⟩ := hHK
    have hb_eq : (⟨y, hyB⟩ : ↥Bs) = ⟨y, hy⟩ := Subtype.ext rfl
    have hψy' : ψ ⟨y, hyB⟩ = ⟨y, hyB⟩ := by rw [hb_eq]; exact hψy
    have hlines := hHKbody (M := MK) (C := CK) hMKweyl hCKcartan ι
      ΦK (fun o => h (o.map Subtype.val id)) (fun o => α (o.map Subtype.val id))
      (fun o w => hform (o.map Subtype.val id) w) (fun o => hrefl (o.map Subtype.val id))
      (fun o o' => hpairK o o') hAK' ψ hψind hψrefl hψy'
    simpa only [ΦK, hb_eq, hψg] using hlines

end CFSG.StandardType

end
