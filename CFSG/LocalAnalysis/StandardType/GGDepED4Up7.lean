module

public import CFSG.LocalAnalysis.StandardType.GGDepED4Align
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpOf
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpClose
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4AlignedW {G : Type} [Group G] [Finite G] (p k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (e : Fin 6 ≃ Λ),
    b₁ = e 0 ∧ b₂ = e 5 ∧ Nat.card Λa = k ∧
      ML = CoxeterMatrix.E₆.reindex e ∧ GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧ (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1))

@[expose] def GGDepED4Core7 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b₁ b₂ : Λ) {Λa : Type}
    [Fintype Λa] [DecidableEq Λa] (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (e : Fin 6 ≃ Λ)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (xV : V) : Prop :=
  b₁ = e 0 ∧ b₂ = e 5 ∧ Nat.card Λa = 2 ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
    (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
    GGDepEFrame p (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV ∧
    (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
    (∀ g ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
    (∃ a : Λa, α (Sum.inr a) xV ≠ 0) ∧
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) ∧
    ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1))

@[expose] def GGDepED4Up7Cfg {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (e : Fin 6 ≃ Λ) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V) (xV : V),
    GGDepED4Core7 p Bs L J K b₁ b₂ MK CK ι e φ h α xV ∧ Module.finrank (ZMod p) V = 7

theorem ggDepED4_align_two_weyl {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L J K : Subgroup G} (hXL : GGResXDatumE6Core p Bs L)
    (hLd : GGResTwoNodeSideDatum p Bs L J) (hKd : GGResTwoNodeSideDatum p Bs K J)
    (hJ : Nat.card ↥(ggAutomizer J Bs) = 192) : GGDepED4AlignedW p 2 Bs L J K := by
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hb, hcard, hWML, hCL, hWMK, hCK, hlin, hrefl, hpairL, hpairK, fLex, fKex,
    hclosL, hclosK, hconn, hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_two ggWeylSimpleSystemsConjInput_holds hp2 hLd hKd
  obtain ⟨Λ₁, iΛ₁f, iΛ₁d, M₁, C₁, V₁, iV₁add, iV₁mod, ι₁, φ₁, h₁, α₁, e₁,
    hM₁, hWM₁, hC₁, hlin₁, hrefl₁, hpair₁, f₁ex, hclos₁⟩ := hXL
  obtain ⟨f₁, hf₁⟩ := f₁ex
  obtain ⟨fL, hfL⟩ := fLex
  letI := i1; letI := i2; letI := i1a; letI := i2a; letI := i3; letI := i4
  letI := iΛ₁f; letI := iΛ₁d; letI := iV₁add; letI := iV₁mod
  haveI : Finite V₁ := Finite.of_injective ι₁.toEquiv.symm ι₁.toEquiv.symm.injective
  have hRC₁ : GGReflClosed (fun i => ggLin (p := p) ι₁ (φ₁ i)) :=
    l05nEA_reflClosed_of_datum hp2 e₁ hM₁ hWM₁ hC₁ (ι := ι₁) φ₁ h₁ α₁ hlin₁ hpair₁ hclos₁ f₁ hf₁
  have hconj : ∀ k : Λ, ∃ (w : ↥(ggAutomizer L Bs)) (i : Λ₁),
      fL (ML.simple k) = w * f₁ (M₁.simple i) * w⁻¹ :=
    l05nEA_conj_of_reflClosed (p := p) ι₁ φ₁ hclos₁ hRC₁ f₁ hf₁ fL
      (fun i => φ (Sum.inl i)) hfL (fun i => hrefl (Sum.inl i))
  obtain ⟨e₂, hML₂⟩ := l05nEA_typeE6_of_datum (p := p) e₁ hM₁ hWM₁ hWML f₁ fL hconj
  obtain ⟨MJ, hJM, hcardMJ⟩ :=
    l05nEA_card_MJ (p := p) b₁ b₂ ML hWML hCL fL (fun i => φ (Sum.inl i)) hfL hclosJ hJ
  obtain ⟨e', hML', hb1, hb2⟩ := ggDepED4_positions hb e₂ hML₂ hconn MJ hJM hcardMJ
  exact ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, e',
    hb1, hb2, hcard, hML', hWML, hCL, hWMK, hCK,
    hlin, hrefl, hpairL, hpairK, fKex, hclosL, hclosK, hclosJ⟩

theorem ggDepED4Up7Cfg_of_alignedW (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hxL : x ∉ L) (hp3 : p = 3) (hCard : Nat.card ↥Bs = 3 ^ 7)
    (hA : GGDepED4AlignedW p 2 Bs L J K) : GGDepED4Up7Cfg p Bs L J K := by
  classical
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hML, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hform, hrefl, hpairL, hpairK, -, hAL, hAK, hAJ⟩ := hA
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := by
    have hβ : p ∈ LargeEvenBeta 4 G := hH.1.1.2.2.2.2.2.1
    exact hβ.2.1
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
  have hfinrank : Module.finrank (ZMod p) V = 7 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : p ^ Module.finrank (ZMod p) V = 3 ^ 7 := by
      rw [← hVcard, hcardV, hCard]
    have heq3 : 3 ^ Module.finrank (ZMod p) V = 3 ^ 7 := by
      simpa [hp3] using heq
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq3
  refine ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, MK, CK, V, hVadd, hVmod, ι, e, φ, h, α,
    xV, ?_⟩
  refine ⟨⟨hb1, hb2, hcardΛa, hMKweyl, hCKcartan, hform, hframe, hpairK, ?_, ?_, ?_,
    hAJ⟩, hfinrank⟩
  · intro g hg
    obtain ⟨ψ, hψ, hψg⟩ := l05nEU_exists_psi (p := p) ι φ g hg
    rw [← hψg]
    exact ggTT_nt_sup hH ι (by rw [l05nEU_sup_eq φ hAL hAK]; exact hψ)
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
  · exact l05nEU_sup_eq φ hAL hAK

theorem ggDepED4Up7Cfg_false {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (hcfg : GGDepED4Up7Cfg p Bs L J K) : False := by
  classical
  obtain ⟨Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, h, α, xV,
    hcore, hdim⟩ := hcfg
  obtain ⟨hb₁, hb₂, hcardk, hWMK, hCK, hφeq, hF, hpairK, hntCore, hex, _hAuto, _hJauto⟩ := hcore
  have hp3 : p = 3 := hF.p3
  subst hp3
  letI := iΛ1
  letI := iΛ2
  letI := iΛa1
  letI := iΛa2
  letI := iV1
  letI := iV2
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  let eJ := l05nEC_eJ b₁ b₂ e hb₁ hb₂
  let ee : ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) :=
    Equiv.sumCongr eJ (Equiv.refl Λa)
  let MK' : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := MK.reindex ee.symm
  let CK' : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)
      ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ := CK.submatrix ee ee
  have hWMK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hWMK ee.symm
  have hCK' : GGIntCartan MK' CK' := by
    have hh := GGIntCartan.reindex (e := ee.symm) hCK
    simpa [MK', CK', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] using hh
  have hJ' : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK' (Sum.inl i) (Sum.inl j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3) := by
    intro i j
    have hpk := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at hpk
    have hck : CK' (Sum.inl i) (Sum.inl j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.refl_apply]
    have hgoal : α (Sum.inl (eJ i).1) (h (Sum.inl (eJ j).1)) =
        (CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) : ZMod 3) := hpk
    rw [hck, ← hgoal]
    exact hF.pair i.1 j.1
  let hE : Fin 6 → V := fun i => h (Sum.inl (e i))
  let αE : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let rE : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (Sum.inl (e i)))
  let rA : Λa → (V ≃ₗ[ZMod 3] V) := fun a => ggLin (p := 3) ι (φ (Sum.inr a))
  have hrE : ∀ i v, rE i v = v - αE i v • hE i := fun i v => hφeq (Sum.inl (e i)) v
  have hrA : ∀ (a : Λa) v, rA a v = v - α (Sum.inr a) v • h (Sum.inr a) :=
    fun a v => hφeq (Sum.inr a) v
  have hαdiag : ∀ a : Λa, α (Sum.inr a) (h (Sum.inr a)) = 2 := by
    intro a
    have hpk := hpairK (Sum.inr a) (Sum.inr a)
    simp only [Sum.map_inr, id_eq] at hpk
    have hgoal : α (Sum.inr a) (h (Sum.inr a)) = (CK (Sum.inr a) (Sum.inr a) : ZMod 3) := hpk
    rw [hgoal, hCK.1 (Sum.inr a)]
    norm_num
  have hcast : ∀ j c : Fin 6, (((if j = c then (-1 : ℤ) else 0 : ℤ)) : ZMod 3) =
      if j = c then (-1 : ZMod 3) else 0 := by
    intro j c
    split_ifs <;> simp
  have hpairGen : ∀ (a : Λa) (t : Fin 6 → ℤ),
      (∀ j : {c : Fin 6 // GGDepED4In c},
        CK' (Sum.inr a) (Sum.inl j) = t j.1 ∧ CK' (Sum.inl j) (Sum.inr a) = t j.1) →
      ∀ j : Fin 6, GGDepED4In j →
        α (Sum.inr a) (hE j) = (t j : ZMod 3) ∧ αE j (h (Sum.inr a)) = (t j : ZMod 3) := by
    intro a t ht j hj
    have hb := ht ⟨j, hj⟩
    constructor
    · have hck : CK' (Sum.inr a) (Sum.inl ⟨j, hj⟩) = CK (Sum.inr a) (Sum.inl (eJ ⟨j, hj⟩)) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
          Sum.map_inr, Equiv.refl_apply]
      have hpk := hpairK (Sum.inr a) (Sum.inl (eJ ⟨j, hj⟩))
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : α (Sum.inr a) (hE j) = (CK (Sum.inr a) (Sum.inl (eJ ⟨j, hj⟩)) : ZMod 3) := hpk
      rw [hgoal, ← hck, hb.1]
    · have hck : CK' (Sum.inl ⟨j, hj⟩) (Sum.inr a) = CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
          Sum.map_inr, Equiv.refl_apply]
      have hpk := hpairK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a)
      simp only [Sum.map_inr, Sum.map_inl, id_eq] at hpk
      have hgoal : αE j (h (Sum.inr a)) = (CK (Sum.inl (eJ ⟨j, hj⟩)) (Sum.inr a) : ZMod 3) := hpk
      rw [hgoal, ← hck, hb.2]
  have hnt : ∀ S : Set (V ≃ₗ[ZMod 3] V), S ⊆ Subgroup.closure (Set.range fun o : Λ ⊕ Λa =>
        ggLin (p := 3) ι (φ o)) →
      ∀ g ∈ Subgroup.closure (Set.range rE ∪ S),
        ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro S hS g hg
    refine hntCore g ?_
    refine (Subgroup.closure_le _).mpr ?_ hg
    rintro x (⟨i, rfl⟩ | hx)
    · exact Subgroup.subset_closure ⟨Sum.inl (e i), rfl⟩
    · exact hS hx
  have hall : ∀ b : Λa, ∀ a₁ a₂ : Λa, a₁ ≠ a₂ → b = a₁ ∨ b = a₂ := by
    intro b a₁ a₂ hane
    obtain ⟨y, _hy_ne, hy_all⟩ := (Nat.card_eq_two_iff' a₁).mp hcardk
    have hy_eq : y = a₂ := (hy_all a₂ (Ne.symm hane)).symm
    by_cases hb' : b = a₁
    · exact Or.inl hb'
    · right
      rw [← hy_eq]
      exact hy_all b hb'
  have hgen : ∀ a : Λa, rA a ∈ Subgroup.closure (Set.range fun o : Λ ⊕ Λa =>
      ggLin (p := 3) ι (φ o)) := fun a => Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
  rcases ggDepED4_pattern6 hcardk hWMK' hCK' hJ' with
    ⟨a₁, a₂, c, c', hane, hleafc, hleafc', _hcc', hpairJ, _h12, _h21, _h11, _h22⟩ |
    ⟨a₁, a₂, c, hane, hleafc, hpairJ, h12, h21, _h11, _h22⟩
  ·
    have hw : α (Sum.inr a₁) xV ≠ 0 ∨ α (Sum.inr a₂) xV ≠ 0 := by
      obtain ⟨b, hb'⟩ := hex
      rcases hall b a₁ a₂ hane with rfl | rfl
      · exact Or.inl hb'
      · exact Or.inr hb'
    have hp1 := hpairGen a₁ (fun j => if j = c then (-1 : ℤ) else 0)
      (fun j => ⟨(hpairJ j).1, (hpairJ j).2.1⟩)
    have hp2 := hpairGen a₂ (fun j => if j = c' then (-1 : ℤ) else 0)
      (fun j => ⟨(hpairJ j).2.2.1, (hpairJ j).2.2.2⟩)
    exact ggDepED4_false_two ggDepED4_cells1 (h := hE) (α := αE) (x := xV) hF hdim rE hrE
      (rA a₁) (rA a₂) (h (Sum.inr a₁)) (h (Sum.inr a₂)) (α (Sum.inr a₁)) (α (Sum.inr a₂))
      (hrA a₁) (hrA a₂) (hαdiag a₁) (hαdiag a₂) hw c c' hleafc hleafc'
      (fun j hj => by
        have := hp1 j hj
        rwa [hcast] at this)
      (fun j hj => by
        have := hp2 j hj
        rwa [hcast] at this)
      (hnt {rA a₁, rA a₂} (by
        rintro x (rfl | rfl)
        · exact hgen a₁
        · exact hgen a₂))
  ·
    have hp1 := hpairGen a₁ (fun j => if j = c then (-1 : ℤ) else 0)
      (fun j => ⟨(hpairJ j).1, (hpairJ j).2.1⟩)
    have hp2 := hpairGen a₂ (fun _ => (0 : ℤ)) (fun j => ⟨(hpairJ j).2.2.1, (hpairJ j).2.2.2⟩)
    have h12' : α (Sum.inr a₁) (h (Sum.inr a₂)) = -1 := by
      have hpk := hpairK (Sum.inr a₁) (Sum.inr a₂)
      simp only [Sum.map_inr, id_eq] at hpk
      have hck : CK' (Sum.inr a₁) (Sum.inr a₂) = CK (Sum.inr a₁) (Sum.inr a₂) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.refl_apply]
      rw [hpk, ← hck, h12]
      simp
    have h21' : α (Sum.inr a₂) (h (Sum.inr a₁)) = -1 := by
      have hpk := hpairK (Sum.inr a₂) (Sum.inr a₁)
      simp only [Sum.map_inr, id_eq] at hpk
      have hck : CK' (Sum.inr a₂) (Sum.inr a₁) = CK (Sum.inr a₂) (Sum.inr a₁) := by
        simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.refl_apply]
      rw [hpk, ← hck, h21]
      simp
    let ra2' : V ≃ₗ[ZMod 3] V := rA a₁ * rA a₂ * rA a₁
    let ha2' : V := h (Sum.inr a₁) + h (Sum.inr a₂)
    let αa2' : Module.Dual (ZMod 3) V := α (Sum.inr a₁) + α (Sum.inr a₂)
    have hra2' : ∀ v, ra2' v = v - αa2' v • ha2' := by
      intro v
      have e1 := hrA a₁ v
      have e2 := hrA a₂ (rA a₁ v)
      have e3 := hrA a₁ (rA a₂ (rA a₁ v))
      simp only [ra2', LinearEquiv.mul_apply] at e1 e2 e3 ⊢
      rw [e3, e2, e1]
      simp only [map_sub, map_smul, smul_eq_mul, h12', h21', hαdiag a₁, hαdiag a₂,
        LinearMap.add_apply, αa2', ha2']
      module
    have hαa2' : αa2' ha2' = 2 := by
      simp only [αa2', ha2', LinearMap.add_apply, map_add, h12', h21', hαdiag a₁, hαdiag a₂]
      ring
    have hw : α (Sum.inr a₁) xV ≠ 0 ∨ αa2' xV ≠ 0 := by
      obtain ⟨b, hb'⟩ := hex
      rcases hall b a₁ a₂ hane with rfl | rfl
      · exact Or.inl hb'
      · by_cases h1 : α (Sum.inr a₁) xV = 0
        · right
          simp only [αa2', LinearMap.add_apply, h1, zero_add]
          exact hb'
        · exact Or.inl h1
    exact ggDepED4_false_two ggDepED4_cells1 (h := hE) (α := αE) (x := xV) hF hdim rE hrE
      (rA a₁) ra2' (h (Sum.inr a₁)) ha2' (α (Sum.inr a₁)) αa2'
      (hrA a₁) hra2' (hαdiag a₁) hαa2' hw c c hleafc hleafc
      (fun j hj => by
        have := hp1 j hj
        rwa [hcast] at this)
      (fun j hj => by
        have h1 := hp1 j hj
        have h2 := hp2 j hj
        simp only [Int.cast_zero] at h2
        rw [hcast] at h1
        constructor
        · simp only [αa2', ha2', LinearMap.add_apply, h1.1, h2.1, add_zero]
        · simp only [αa2', ha2', map_add, h1.2, h2.2, add_zero])
      (hnt {rA a₁, ra2'} (by
        rintro x (rfl | rfl)
        · exact hgen a₁
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgen a₁) (hgen a₂)) (hgen a₁)))

theorem ggDepED4Up7_false (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hxL : x ∉ L) (hp3 : p = 3)
    (hCard : Nat.card ↥Bs = 3 ^ 7) (hA : GGDepED4AlignedW p 2 Bs L J K) : False :=
  ggDepED4Up7Cfg_false (ggDepED4Up7Cfg_of_alignedW hFix hFixK hH hxL hp3 hCard hA)

end CFSG.StandardType

end
