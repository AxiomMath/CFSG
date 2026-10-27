module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpOf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nLOE_sup_eq {G : Type} [Group G] {Bs L K : Subgroup G}
    {Λ Λa : Type} {b₁ b₂ : Λ} (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range fun a : Λa => φ (Sum.inr a))) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) := by
  rw [hAL, hAK, ← Subgroup.closure_union]
  congr 1
  ext γ
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inl j.1, rfl⟩
    · exact ⟨Sum.inr a, rfl⟩
  · rintro ⟨o, rfl⟩
    cases o with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr a => exact Or.inr (Or.inr ⟨a, rfl⟩)

private theorem l05nLOE_exists_psi {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
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

private theorem l05nLO_cartan_of_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1]
    fin_cases i <;> decide
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    have h₂ : GGIntCartan ML (Matrix.reindex e e (CartanMatrix.E 6)) := by
      rw [hML]
      exact GGIntCartan.reindex e ggIntCartan_E₆
    have hMle : ML.M (e i) (e j) ≤ 3 := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases i <;> fin_cases j <;> decide
    have h1 := (hCL.pair h₂ heij).2 hMle
    rw [h1.1]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem ggDepED4LowCfg_of_aligned (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hxL : x ∉ L) {k : ℕ} (hk : k = 1 ∨ k = 2) (hp3 : p = 3) (hCard : Nat.card ↥Bs = 3 ^ 6)
    (hHL : k = 1 → GGTWHLAt p Bs L x) (hHK : k = 1 → GGTWHLAt p Bs K y)
    (hA : GGDepED4Aligned p k Bs L J K) : GGDepED4LowCfg p k Bs L J K x y := by
  classical
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hML, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
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
  have hcart := l05nLO_cartan_of_reindex e hCLcartan hML
  have hdep : ¬ LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    l05nEU_dep hFix hp2 hp3 hH hx hxL e hCLcartan hML
      (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hform (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hAL)
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
  let α₀ : Option Λ → Module.Dual (ZMod p) V := fun o => α (Sum.inl (o.getD b₁))
  have hform₀ : ∀ o w, ggLin (p := p) ι (φ₀ o) w = w - α₀ o w • h₀ o :=
    fun o w => hform (Sum.inl (o.getD b₁)) w
  have hpair₀ : ∀ i j : Λ, α₀ (some i) (h₀ (some j)) = (CL i j : ZMod p) := fun i j => hpairL i j
  have hAL₀ : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ₀ (some i)) := by
    simpa [φ₀] using hAL
  have hαx : ∀ i : Fin 6, α (Sum.inl (e i)) xV = 0 := by
    intro i
    have h := l05nDD1_alpha_x (p := p) hp2 hH hx hform₀ hpair₀ hCLcartan hAL₀ (e i)
    simpa [α₀, xV] using h
  have hframe : GGDepEFrame p (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV :=
    { p3 := hp3
      pair := fun i j => by
        rw [hpairL (e i) (e j), hcart i j]
      x_ne := hxVne
      x_ker := hαx
      fix := fun v hv =>
        l05nDD1_fix hFix hH hx hform₀ hAL₀ v (fun j => by
          have hj := hv (e.symm j)
          simpa [α₀] using hj)
      dep := fun hli => hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli) }
  have hxker : ∀ i : Λ, α (Sum.inl i) xV = 0 := by
    intro i
    have h := hframe.x_ker (e.symm i)
    simpa using h
  have hfinrank : Module.finrank (ZMod p) V = 6 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : p ^ Module.finrank (ZMod p) V = 3 ^ 6 := by
      rw [← hVcard, hcardV, hCard]
    have heq3 : 3 ^ Module.finrank (ZMod p) V = 3 ^ 6 := by
      simpa [hp3] using heq
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq3
  have hfixy : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ :=
    ggRC_automizer_fixes_y hy hKy
  refine ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, MK, CK, V, hVadd, hVmod, ι, e, φ, h, α,
    xV, yV, hx, hy, rfl, rfl, ?_, hfinrank, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hb1, hb2, hcardΛa, hMKweyl, hCKcartan, hk2, hform, hframe, hpairK, ?_, ?_, ?_,
      hAJ⟩
    · intro g hg
      obtain ⟨ψ, hψ, hψg⟩ := l05nLOE_exists_psi (p := p) ι φ g hg
      rw [← hψg]
      exact ggTT_nt_sup hH ι (by rw [l05nLOE_sup_eq φ hAL hAK]; exact hψ)
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
    · exact l05nLOE_sup_eq φ hAL hAK
  · intro hk1 g hg hgref hgx
    obtain ⟨ψ, hψ, hψg⟩ := l05nLOE_exists_psi (p := p) ι φ g hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
        sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
      have hmem : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
        rw [l05nLOE_sup_eq φ hAL hAK]
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
    obtain ⟨hxB, hHLbody⟩ := hHL hk1
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
  · intro hk1 g hg hgref hgy
    obtain ⟨ψ, hψ, hψg⟩ := l05nLOE_exists_psi (p := p) ι φ g hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
        sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
      have hmem : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
        rw [l05nLOE_sup_eq φ hAL hAK]
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
    obtain ⟨hyB, hHKbody⟩ := hHK hk1
    have hb_eq : (⟨y, hyB⟩ : ↥Bs) = ⟨y, hy⟩ := Subtype.ext rfl
    have hψy' : ψ ⟨y, hyB⟩ = ⟨y, hyB⟩ := by rw [hb_eq]; exact hψy
    have hlines := hHKbody (M := MK) (C := CK) hMKweyl hCKcartan ι
      ΦK (fun o => h (o.map Subtype.val id)) (fun o => α (o.map Subtype.val id))
      (fun o w => hform (o.map Subtype.val id) w) (fun o => hrefl (o.map Subtype.val id))
      (fun o o' => hpairK o o') hAK' ψ hψind hψrefl hψy'
    simpa only [ΦK, hb_eq, hψg] using hlines

end CFSG.StandardType

end
