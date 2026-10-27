module

public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGP3LineNormalizer
public import CFSG.LocalAnalysis.StandardType.GGNbrCan
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {B Bs L D J K : Subgroup G} {x y : G} {Λ : Type} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]
  {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V}

@[expose] def ggResVec {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    (ι : Additive ↥Bs ≃+ V) (x : G) (hx : x ∈ Bs) : V :=
  ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))

theorem ggResQTwo_coroot_ne_zero
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o)) (o : Option Λ) : h o ≠ 0 := by
  intro h0
  have hid : φ o = 1 := by
    apply ggLin_injective (p := p) ι
    ext w
    rw [hφ o w, h0, smul_zero, sub_zero]
    simp
  exact l6tr_refl_ne_one (hrefl o) hid

theorem ggResQTwo_alpha_none_x_ne_zero {b : Λ}
    (hH : GGResHyp p B Bs x L D J y K) (ha0 : GGLNoncyclicInput)
    (hx : x ∈ Bs)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hind : LinearIndependent (ZMod p) h)
    (hsome : ∃ j : Λ, α none (h (some j)) ≠ 0) :
    α none (ggResVec ι x hx) ≠ 0 := by
  classical
  intro hx0
  obtain ⟨j, hj⟩ := hsome
  have hmemAK : φ none ∈ ggAutomizer K Bs := by
    rw [hAK]
    exact Subgroup.subset_closure (Or.inr (by simp))
  have ht : φ none ∈ ggAutomizer ⊤ Bs :=
    ggAutomizer_mono Bs le_top hmemAK
  have hxfix : φ none ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [ggLin_fix_iff (p := p) ι (φ none) ⟨x, hx⟩]
    change ggLin (p := p) ι (φ none) (ggResVec ι x hx) = ggResVec ι x hx
    rw [hφ none (ggResVec ι x hx), hx0, zero_smul, sub_zero]
  have hpres := ggAutomizer_preserves_span_coroot (ha₀ := ha0) (hcfg := hH.1) (hx := hx)
    (φ := fun i : Λ => φ (some i)) (h := fun i : Λ => h (some i))
    (α := fun i : Λ => α (some i))
    (fun i w => hφ (some i) w) (fun i => hrefl (some i)) hAL ht hxfix
  let U : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) (Set.range fun i : Λ => h (some i))
  have hmemj : h (some j) ∈ U := Submodule.subset_span (Set.mem_range_self j)
  have hmoved : ggLin (p := p) ι (φ none) (h (some j)) ∈ U := hpres _ hmemj
  rw [hφ none (h (some j))] at hmoved
  have hmul : α none (h (some j)) • h none ∈ U := by
    have hsub := Submodule.sub_mem U hmemj hmoved
    have heq : h (some j) - (h (some j) - α none (h (some j)) • h none) =
        α none (h (some j)) • h none := by abel
    rwa [heq] at hsub
  have hnone_mem : h none ∈ U := (Submodule.smul_mem_iff (p := U) hj).mp hmul
  exact (linearIndependent_option.mp hind).2 hnone_mem

theorem ggResQTwo_ker_roots_eq_bot
    (hH : GGResHyp p B Bs x L D J y K) (hFix : GGTBFixInput)
    (hx : x ∈ Bs)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hno : α none (ggResVec ι x hx) ≠ 0) :
    (Submodule.span (ZMod p) (Set.range α)).dualCoannihilator = ⊥ := by
  classical
  refine (Submodule.eq_bot_iff _).mpr ?_
  intro w hw
  rw [Submodule.mem_dualCoannihilator] at hw
  have hwL : ∀ i : Λ, α (some i) w = 0 := fun i =>
    hw (α (some i)) (Submodule.subset_span (Set.mem_range_self (some i)))
  have hwspan := ggResI_fixSpan hFix hH hx ι hφ hAL w hwL
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwspan
  have hz : α none w = 0 :=
    hw (α none) (Submodule.subset_span (Set.mem_range_self none))
  rw [← hc, map_smul, smul_eq_mul] at hz
  have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_right hno
  rw [← hc, hc0, zero_smul]

theorem ggResQTwo_linearIndependent_roots [Fintype Λ] {b : Λ}
    (hH : GGResHyp p B Bs x L D J y K) (hFix : GGTBFixInput) (ha0 : GGLNoncyclicInput)
    (hx : x ∈ Bs)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hind : LinearIndependent (ZMod p) h)
    (hsome : ∃ j : Λ, α none (h (some j)) ≠ 0) :
    LinearIndependent (ZMod p) α := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  have hno : α none (ggResVec ι x hx) ≠ 0 :=
    ggResQTwo_alpha_none_x_ne_zero hH ha0 hx hφ hrefl hAL hAK hind hsome
  have hbot : (Submodule.span (ZMod p) (Set.range α)).dualCoannihilator = ⊥ :=
    ggResQTwo_ker_roots_eq_bot hH hFix hx hφ hAL hno
  have hspan := ggResI_span_top hFix hH ι hφ hAL hind
  have hdimV : Module.finrank (ZMod p) V = Fintype.card Λ + 1 :=
    ggResI_finrank hspan hind
  have hdimW : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range α)) =
      Fintype.card Λ + 1 := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span (ZMod p) (Set.range α))
    rw [hbot, finrank_bot, hdimV] at h
    omega
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, Fintype.card_option]
  exact hdimW.symm

theorem ggResQTwo_fixK_eq_span_y [Fintype Λ] {b : Λ}
    (hH : GGResHyp p B Bs x L D J y K) (hFix : GGTBFixInput)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hind : LinearIndependent (ZMod p) h)
    (hα : LinearIndependent (ZMod p) α) :
    (Submodule.span (ZMod p) (Set.range fun o : Option {i : Λ // i ≠ b} =>
      α (o.map Subtype.val))).dualCoannihilator =
    Submodule.span (ZMod p) {ggResVec ι y (hH.1.2.1.1 hH.2.2.2.2.1.1.2.1)} := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  set hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1 with hhy
  set yV : V := ggResVec ι y hy with hyV
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hfixy : ∀ ψ ∈ ggAutomizer K Bs, ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggResI_automizer_fix hy hKy
  have hαKy : ∀ o : Option {i : Λ // i ≠ b}, α (o.map Subtype.val) yV = 0 := by
    intro o
    have hmem : φ (o.map Subtype.val) ∈ ggAutomizer K Bs := by
      rw [hAK]
      cases o with
      | none => exact Subgroup.subset_closure (Or.inr (by simp))
      | some j => exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
    have hfix := (ggLin_fix_iff (p := p) ι (φ (o.map Subtype.val))
      (⟨y, hy⟩ : ↥Bs)).mp (hfixy _ hmem)
    have hlin := hφ (o.map Subtype.val) yV
    rw [show ggLin (p := p) ι (φ (o.map Subtype.val)) yV = yV from hfix] at hlin
    have hzero : α (o.map Subtype.val) yV • h (o.map Subtype.val) = 0 :=
      sub_eq_self.mp hlin.symm
    exact (smul_eq_zero.mp hzero).resolve_right
      (ggResQTwo_coroot_ne_zero hφ hrefl (o.map Subtype.val))
  have hy1 : y ≠ 1 := hH.2.2.2.2.1.1.2.2.1
  have hyV0 : yV ≠ 0 := by
    intro h0
    apply hy1
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := by
      apply ι.injective
      simpa [yV, ggResVec] using h0
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h1
    exact congrArg Subtype.val h2
  let WK : Submodule (ZMod p) (Module.Dual (ZMod p) V) :=
    Submodule.span (ZMod p) (Set.range fun o : Option {i : Λ // i ≠ b} =>
      α (o.map Subtype.val))
  have hαK : LinearIndependent (ZMod p)
      (fun o : Option {i : Λ // i ≠ b} => α (o.map Subtype.val)) :=
    hα.comp (fun o : Option {i : Λ // i ≠ b} => o.map Subtype.val)
      (Option.map_injective Subtype.val_injective)
  have hcard : Fintype.card (Option {i : Λ // i ≠ b}) = Fintype.card Λ := by
    rw [Fintype.card_option]
    have hc : Fintype.card {i : Λ // i ≠ b} + 1 = Fintype.card Λ := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      have : 0 < Fintype.card Λ := Fintype.card_pos_iff.mpr ⟨b⟩
      omega
    omega
  have hfinK : Module.finrank (ZMod p) WK = Fintype.card Λ := by
    rw [show WK = Submodule.span (ZMod p) (Set.range fun o : Option {i : Λ // i ≠ b} =>
      α (o.map Subtype.val)) from rfl, finrank_span_eq_card hαK, hcard]
  have hspan := ggResI_span_top hFix hH ι hφ hAL hind
  have hdimV : Module.finrank (ZMod p) V = Fintype.card Λ + 1 :=
    ggResI_finrank hspan hind
  have hdimK : Module.finrank (ZMod p) WK.dualCoannihilator = 1 := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq WK
    rw [hfinK, hdimV] at h
    omega
  have hyker : yV ∈ WK.dualCoannihilator := by
    rw [Submodule.mem_dualCoannihilator]
    intro f hf
    refine Submodule.span_induction (p := fun f _ => f yV = 0) ?_ ?_ ?_ ?_ hf
    · rintro f ⟨o, rfl⟩
      exact hαKy o
    · simp
    · intro f g _ _ ihf ihg
      change f yV + g yV = 0
      rw [ihf, ihg, add_zero]
    · intro c f _ ihf
      change c • f yV = 0
      rw [ihf, smul_zero]
  have hker : WK.dualCoannihilator = Submodule.span (ZMod p) {yV} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdimK hyker hyV0
  exact hker

theorem ggResQTwo_mem_span_y_of_fixK [Fintype Λ] {b : Λ}
    (hH : GGResHyp p B Bs x L D J y K) (hFix : GGTBFixInput)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hind : LinearIndependent (ZMod p) h)
    (hα : LinearIndependent (ZMod p) α) :
    ∀ w : V, (∀ o : Option {i : Λ // i ≠ b}, α (o.map Subtype.val) w = 0) →
      w ∈ Submodule.span (ZMod p) {ggResVec ι y (hH.1.2.1.1 hH.2.2.2.2.1.1.2.1)} := by
  intro w hw
  rw [← ggResQTwo_fixK_eq_span_y (b := b) hH hFix hφ hrefl hAL hAK hind hα]
  rw [Submodule.mem_dualCoannihilator]
  intro f hf
  exact Submodule.span_induction (p := fun f _ => f w = 0)
    (fun f hf' => by rcases hf' with ⟨o, rfl⟩; exact hw o)
    (by simp) (fun f g _ _ ihf ihg => by
      change f w + g w = 0
      rw [ihf, ihg, add_zero])
    (fun c f _ ihf => by
      change c • f w = 0
      rw [ihf, smul_zero]) hf

theorem ggResQTwo_inf_centralizer_le_zpowers [Fintype Λ] {b : Λ}
    (hH : GGResHyp p B Bs x L D J y K) (hFix : GGTBFixInput)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hind : LinearIndependent (ZMod p) h)
    (hα : LinearIndependent (ZMod p) α) :
    Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
  classical
  set hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1 with hhy
  intro c hc
  obtain ⟨hcBs, hcK⟩ := hc
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    have hdC : c ∈ Subgroup.centralizer (K : Set G) := hcK
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ((Subgroup.mem_centralizer_iff.mp hdC) g hg).symm
  have hfixc : ∀ ψ ∈ ggAutomizer K Bs, ψ (⟨c, hcBs⟩ : ↥Bs) = ⟨c, hcBs⟩ :=
    ggResI_automizer_fix hcBs hKc
  have hαKc : ∀ o : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (ggResVec ι c hcBs) = 0 := by
    intro o
    have hmem : φ (o.map Subtype.val) ∈ ggAutomizer K Bs := by
      rw [hAK]
      cases o with
      | none => exact Subgroup.subset_closure (Or.inr (by simp))
      | some j => exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
    have hfix := (ggLin_fix_iff (p := p) ι (φ (o.map Subtype.val))
      (⟨c, hcBs⟩ : ↥Bs)).mp (hfixc _ hmem)
    have hlin := hφ (o.map Subtype.val) (ggResVec ι c hcBs)
    rw [show ggLin (p := p) ι (φ (o.map Subtype.val))
      (ggResVec ι c hcBs) = ggResVec ι c hcBs from hfix] at hlin
    have hzero : α (o.map Subtype.val) (ggResVec ι c hcBs) •
        h (o.map Subtype.val) = 0 := sub_eq_self.mp hlin.symm
    exact (smul_eq_zero.mp hzero).resolve_right
      (ggResQTwo_coroot_ne_zero hφ hrefl (o.map Subtype.val))
  have hcspan := ggResQTwo_mem_span_y_of_fixK (b := b) hH hFix hφ hrefl hAL hAK hind hα
    (ggResVec ι c hcBs) hαKc
  rw [Submodule.mem_span_singleton] at hcspan
  obtain ⟨a, ha⟩ := hcspan
  let k : ℤ := a.val
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have hcast : ((k : ℤ) : ZMod p) = a := by
    dsimp [k]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hc_eq : (⟨c, hcBs⟩ : ↥Bs) = (⟨y, hy⟩ : ↥Bs) ^ k := by
    apply ι.injective
    show ggResVec ι c hcBs =
      ι (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ k))
    rw [ofMul_zpow, map_zsmul]
    change ggResVec ι c hcBs = k • ggResVec ι y hy
    rw [← Int.cast_smul_eq_zsmul (ZMod p) k (ggResVec ι y hy), hcast]
    exact ha.symm
  have hval := congrArg (fun z : ↥Bs => (z : G)) hc_eq
  simpa [Subgroup.coe_zpow] using hval.symm

theorem ggResQTwo_mem_normalizer_automizer_K {b : Λ}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer ⊤ Bs)
    (hfix : t ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1⟩ =
      ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1⟩) :
    t ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) := by
  classical
  set hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1 with hhy
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hnt : ggAutomizer K Bs ≠ ⊥ := by
    intro hbot
    have hmem : φ none ∈ ggAutomizer K Bs := by
      rw [hAK]
      exact Subgroup.subset_closure (Or.inr (by simp))
    rw [hbot] at hmem
    exact l6tr_refl_ne_one (hrefl none) (Subgroup.mem_bot.mp hmem)
  have hN : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    intro g hg
    obtain ⟨hgN, hgC⟩ := hg
    have hgy : g * y * g⁻¹ = y := by
      have hcomm : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [hcomm]
        _ = y := by group
    exact ggNbr_mem_normalizer hH hCent hnt hgN hgy
  have htC : t ∈ ggAutomizer (Subgroup.centralizer ({y} : Set G)) Bs :=
    mem_ggAutomizer_centralizer_of_apply_eq hy ht hfix
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    exact ggAutomizer_conj_mem_of_normalizer_le hKy le_rfl hN htC hψ
  · intro hψ
    have htC' : t⁻¹ ∈ ggAutomizer (Subgroup.centralizer ({y} : Set G)) Bs :=
      Subgroup.inv_mem _ htC
    have hψ' : t * ψ * t⁻¹ ∈ ggAutomizer K Bs := hψ
    have hχ := ggAutomizer_conj_mem_of_normalizer_le hKy le_rfl hN htC' hψ'
    have hEq : t⁻¹ * (t * ψ * t⁻¹) * (t⁻¹)⁻¹ = ψ := by group
    simpa only [hEq] using hχ

end CFSG.StandardType
