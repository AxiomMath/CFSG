module

public import CFSG.LocalAnalysis.StandardType.GGTWHLCover
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrRest
public import CFSG.LocalAnalysis.StandardType.GGDepED4L58Rest
public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGReflNormLine
public import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrCanCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Span

variable {p : ℕ} [Fact p.Prime] {E : Type} [Group E]

theorem ggLin_sub_mem_span_of_mem_closure {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive E ≃+ V) {Λ : Type} (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {a : MulAut E} (ha : a ∈ Subgroup.closure (Set.range φ)) (v : V) :
    ggLin (p := p) ι a v - v ∈ Submodule.span (ZMod p) (Set.range h) := by
  refine Subgroup.closure_induction
    (p := fun a _ => ∀ v, ggLin (p := p) ι a v - v ∈ Submodule.span (ZMod p) (Set.range h))
    ?_ ?_ ?_ ?_ ha v
  · rintro _ ⟨i, rfl⟩ v
    rw [hlin, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · intro v
    simp
  · intro a b _ _ iha ihb v
    rw [map_mul, LinearEquiv.mul_apply]
    have h1 := Submodule.add_mem _ (iha (ggLin (p := p) ι b v)) (ihb v)
    rwa [sub_add_sub_cancel] at h1
  · intro a _ iha v
    have h1 := iha (ggLin (p := p) ι a⁻¹ v)
    have h2 : ggLin (p := p) ι a (ggLin (p := p) ι a⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [h2] at h1
    rw [← neg_sub]
    exact Submodule.neg_mem _ h1

theorem ggLin_transport {V₀ V : Type} [AddCommGroup V₀] [Module (ZMod p) V₀] [AddCommGroup V]
    [Module (ZMod p) V] (ι₀ : Additive E ≃+ V₀) (ι : Additive E ≃+ V) (a : MulAut E) (v : V₀) :
    ι (ι₀.symm (ggLin (p := p) ι₀ a v)) = ggLin (p := p) ι a (ι (ι₀.symm v)) := by
  simp only [ggLin_apply, AddEquiv.symm_apply_apply]

theorem finrank_span_le_card_of_mem_closure [Finite E] (hp2 : p ≠ 2) {V₀ V : Type}
    [AddCommGroup V₀] [Module (ZMod p) V₀] [AddCommGroup V] [Module (ZMod p) V]
    (ι₀ : Additive E ≃+ V₀) {Λ₀ : Type} (φ₀ : Λ₀ → MulAut E) (h₀ : Λ₀ → V₀)
    (α₀ : Λ₀ → Module.Dual (ZMod p) V₀)
    (hlin₀ : ∀ i w, ggLin (p := p) ι₀ (φ₀ i) w = w - α₀ i w • h₀ i) (hα₀ : ∀ i, α₀ i (h₀ i) = 2)
    (ι : Additive E ≃+ V) {Λ : Type} [Fintype Λ] (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hmem : ∀ i, φ₀ i ∈ Subgroup.closure (Set.range φ)) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h₀)) ≤ Fintype.card Λ := by
  classical
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  let θ : V₀ ≃ₗ[ZMod p] V := LinearEquiv.ofBijective
    ((ι₀.symm.trans ι).toAddMonoidHom.toZModLinearMap p) (ι₀.symm.trans ι).bijective
  have hθ : ∀ v, θ v = ι (ι₀.symm v) := fun _ => rfl
  have hθh : ∀ i, θ (h₀ i) ∈ Submodule.span (ZMod p) (Set.range h) := by
    intro i
    have h1 := ggLin_sub_mem_span_of_mem_closure ι φ h α hlin (hmem i) (θ (h₀ i))
    have h3 : ggLin (p := p) ι (φ₀ i) (θ (h₀ i)) = θ (h₀ i) - (2 : ZMod p) • θ (h₀ i) := by
      have h4 : θ (ggLin (p := p) ι₀ (φ₀ i) (h₀ i)) = ggLin (p := p) ι (φ₀ i) (θ (h₀ i)) :=
        ggLin_transport ι₀ ι (φ₀ i) (h₀ i)
      rw [hlin₀, hα₀, map_sub, map_smul] at h4
      exact h4.symm
    rw [h3, sub_sub_cancel_left, Submodule.neg_mem_iff,
      Submodule.smul_mem_iff _ (zmod_two_ne_zero hp2)] at h1
    exact h1
  have hle : (Submodule.span (ZMod p) (Set.range h₀)).map (θ : V₀ →ₗ[ZMod p] V) ≤
      Submodule.span (ZMod p) (Set.range h) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hθh i
  calc Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h₀))
      = Module.finrank (ZMod p)
          ((Submodule.span (ZMod p) (Set.range h₀)).map (θ : V₀ →ₗ[ZMod p] V)) :=
        (LinearEquiv.finrank_map_eq θ _).symm
    _ ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card Λ := finrank_range_le_card h

theorem ggIntCartan_three_le_rank (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h3 : 3 ≤ Fintype.card Λ) : 3 ≤ Matrix.rank (C.map (Int.castRingHom (ZMod p))) := by
  have hr0 := ggIntCartan_card_le_rank_add_one hM hC p hp2
  by_cases h4 : 4 ≤ Fintype.card Λ
  · omega
  · rw [ggIntCartan_rank_eq_three hp2 hM hC (by omega)]

end Span

section Lines

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

@[expose] def GGAutWeylThree (p : ℕ) [Fact p.Prime] (Bs X : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
    GGIsWeylMatrix M ∧ GGIntCartan M C ∧ (∀ i, φ i ∈ ggAutomizer X Bs) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ 3 ≤ Fintype.card Λ

theorem GGAutWeylThree.three_le_card {Bs X : Subgroup G} (hp2 : p ≠ 2)
    (hW : GGAutWeylThree p Bs X) {Λ : Type} [Fintype Λ] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hgen : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) : 3 ≤ Fintype.card Λ := by
  classical
  obtain ⟨Λ₀, _, _, M₀, C₀, V₀, _, _, ι₀, φ₀, h₀, α₀, hM₀, hC₀, hφ₀, hpair₀, hlin₀, h3⟩ := hW
  have : Finite V₀ := Finite.of_equiv _ ι₀.toEquiv
  let W := Submodule.span (ZMod p) (Set.range h₀)
  let hW : Λ₀ → W := fun i => ⟨h₀ i, Submodule.subset_span ⟨i, rfl⟩⟩
  let αW : Λ₀ → Module.Dual (ZMod p) W := fun i => (α₀ i).comp W.subtype
  have hpairW : ∀ i j, αW i (hW j) = (C₀ i j : ZMod p) := hpair₀
  have hrank := LevTwo.levTwoS4a_rank_core_add (V := W) (C := C₀) (h := hW) (α := αW) hpairW
    (T := ⊥) (by simp)
  rw [finrank_bot, add_zero] at hrank
  have hα₀ : ∀ i, α₀ i (h₀ i) = 2 := fun i => by rw [hpair₀, hC₀.1 i]; norm_num
  have hcard : Module.finrank (ZMod p) W ≤ Fintype.card Λ :=
    finrank_span_le_card_of_mem_closure hp2 ι₀ φ₀ h₀ α₀ hlin₀ hα₀ ι φ h α hlin
      (fun i => hgen ▸ hφ₀ i)
  have := ggIntCartan_three_le_rank hp2 hM₀ hC₀ h3
  omega

theorem ggTWHLAt_of_normalizer (hp2 : p ≠ 2) {Bs X : Subgroup G} {z : G} (hzB : z ∈ Bs)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G))
    (hN : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (X : Set G))
    (hW : GGAutWeylThree p Bs X) : GGTWHLAt p Bs X z := by
  refine ⟨hzB, ?_⟩
  intro Λ _ _ M C hMw hC V _ _ ι φ h α hlin hrefl hpair hgen t ht _ htz
  have htA : t ∈ ggAutomizer ⊤ Bs := Subgroup.subset_closure ht
  have htC := mem_ggAutomizer_centralizer_of_apply_eq hzB htA htz
  have htN : t ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro ψ
    constructor
    · intro hψ
      exact ggAutomizer_conj_mem_of_normalizer_le hXz le_rfl hN htC hψ
    · intro hψ
      have h1 := ggAutomizer_conj_mem_of_normalizer_le hXz le_rfl hN (Subgroup.inv_mem _ htC) hψ
      convert h1 using 1
      group
  set s : Λ → V ≃ₗ[ZMod p] V := fun i => ggLin (p := p) ι (φ i) with hs
  have hWs : (ggAutomizer X Bs).map (ggLin (p := p) ι) = Subgroup.closure (Set.range s) := by
    rw [hgen, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hT : ggLin (p := p) ι t ∈
      Subgroup.normalizer (Subgroup.closure (Set.range s) : Set (V ≃ₗ[ZMod p] V)) := by
    rw [← hWs]
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ htN)
  have hα : ∀ i, α i (h i) = 2 := fun i => by rw [hpair, hC.1 i]; norm_num
  have h0 : ∀ i, h i ≠ 0 := by
    intro i hi
    have h1 := hα i
    rw [hi, map_zero] at h1
    exact zmod_two_ne_zero hp2 h1.symm
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hRC : GGReflClosed s :=
    ggReflClosed_of_weylMatrix hp2 hMw (hW.three_le_card hp2 ι φ h α hlin hgen) hC h α hpair s
      hlin
  have hsq : ∀ i, (s i)⁻¹ = s i := by
    intro i
    have h1 : φ i * φ i = 1 := by rw [← pow_two]; exact (hrefl i).1
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hs]
    simp only
    rw [← map_mul, h1, map_one]
  have hinv : (Set.range s)⁻¹ ⊆ Set.range s := by
    rintro x ⟨i, hi⟩
    exact ⟨i, by rw [← hsq i, hi, inv_inv]⟩
  intro v hv
  obtain ⟨w, hw, i, rfl⟩ := hv
  have hwG : w ∈ Subgroup.closure (Set.range s) :=
    (Submonoid.closure_le (S := (Subgroup.closure (Set.range s)).toSubmonoid)).mpr
      Subgroup.subset_closure hw
  obtain ⟨u, hu, m, r, hr, hTu⟩ := ggNormalizer_orbit_mem hp2 s h α hlin hα h0 hRC hT hwG i
  have huM : u ∈ Submonoid.closure (Set.range s) := by
    have h1 : u ∈ (Subgroup.closure (Set.range s)).toSubmonoid := hu
    rw [Subgroup.closure_toSubmonoid] at h1
    exact Submonoid.closure_mono (Set.union_subset le_rfl hinv) h1
  exact ⟨u (h m), ⟨u, huM, m, rfl⟩, r, 0, hr, by rw [hTu, zero_smul, add_zero]⟩

end Lines

section Cells

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem GGAutWeylThree.card_inf {Bs X : Subgroup G} (hp2 : p ≠ 2) (hW : GGAutWeylThree p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X) := by
  obtain ⟨Λ, _, _, M, C, V, _, _, ι, φ, h, α, hM, hC, hφ, hpair, hlin, h3⟩ := hW
  exact ggCard_inf_of_weyl_rank_three hp2 hN hM hC ι φ h α hφ hpair hlin h3

theorem ggBase_normalizer_le_of_card_inf {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hcard : p ^ 2 ≤ Nat.card ↥(Bs ⊓ L)) :
    Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have hp : p.Prime := Fact.out
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hP : IsPGroup p ↥(Bs ⊓ L) := fun g => ⟨1, Subtype.ext (by simpa using hBs.2 g g.2.1)⟩
  have hnc : ¬ IsCyclic ↥(Bs ⊓ L) := by
    intro hcyc
    have := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Bs ⊓ L))
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hBs.2 g g.2.1)
    have hle : Nat.card ↥(Bs ⊓ L) ≤ p := by
      rw [← hg]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
    have h2 := hp.two_le
    have hlt : p < p ^ 2 := by nlinarith
    omega
  intro g hg
  refine mem_normalizer_of_sstar' hS ⟨Bs ⊓ L, inf_le_right, hP, hnc⟩ ?_
  apply CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
  have he : g * x * g⁻¹ = x := by rw [hgx]; group
  rw [he]
  exact Subgroup.mem_zpowers x

theorem ggTWHLAt_base_of_autWeylThree {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hW : GGAutWeylThree p Bs L) :
    GGTWHLAt p Bs L x := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hxB : x ∈ Bs := hH.1.2.1.1 hH.1.1.2.2.2.2.2.2.1.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hcard := hW.card_inf hp2 hH.2.2.1.1.le_normalizer
  refine ggTWHLAt_of_normalizer hp2 hxB hLx (ggBase_normalizer_le_of_card_inf hH ?_) hW
  calc p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by norm_num)
    _ ≤ _ := hcard

theorem ggTWHLAt_nbr_of_autWeylThree {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hW : GGAutWeylThree p Bs K) :
    GGTWHLAt p Bs K y := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyB : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hcard := hW.card_inf hp2 (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  refine ggTWHLAt_of_normalizer hp2 hyB hKy ?_ hW
  intro g hg
  apply ggNbr_mem_normalizer_of_card_inf hH hcard hg.1
  apply CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem
  have hgy : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
  have he : g * y * g⁻¹ = y := by rw [hgy]; group
  rw [he]
  exact Subgroup.mem_zpowers y

private theorem card_ne_pair {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} (hb : b₁ ≠ b₂) :
    Fintype.card {i : Λ // i ≠ b₁ ∧ i ≠ b₂} = Fintype.card Λ - 2 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Λ => i ≠ b₁ ∧ i ≠ b₂) = Finset.univ \ {b₁, b₂} := by
    ext i
    simp [not_or]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_pair hb]

omit [Finite G] in
theorem ggAutWeylThree_of_aligned_part {Bs K : Subgroup G} {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (h3 : 3 ≤ Fintype.card ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)) :
    GGAutWeylThree p Bs K := by
  refine ⟨{i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa, inferInstance, inferInstance, MK, CK, V, inferInstance,
    inferInstance, ι, fun o => φ (o.map Subtype.val id), fun o => h (o.map Subtype.val id),
    fun o => α (o.map Subtype.val id), hMK, hCK, ?_, hpairK, fun o w => hlin _ w, h3⟩
  intro o
  rw [hK]
  apply Subgroup.subset_closure
  cases o with
  | inl j => exact Or.inl ⟨j, rfl⟩
  | inr a => exact Or.inr ⟨a, rfl⟩

omit [Finite G] in
theorem ggAutWeylThree_of_aligned_frame {Bs L : Subgroup G} {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {Λa : Type} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (h3 : 3 ≤ Fintype.card Λ) : GGAutWeylThree p Bs L := by
  refine ⟨Λ, inferInstance, inferInstance, ML, CL, V, inferInstance, inferInstance, ι,
    fun i => φ (Sum.inl i), fun i => h (Sum.inl i), fun i => α (Sum.inl i), hML, hCL, ?_, hpairL,
    fun i w => hlin _ w, h3⟩
  intro i
  rw [hL]
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem GGTWAligned.autWeylThree_K {Bs L J K : Subgroup G} {N k : ℕ}
    (hA : GGTWAligned p N k Bs L J K) (hN : 5 ≤ N) (hk : 1 ≤ k) : GGAutWeylThree p Bs K := by
  obtain ⟨-, Λ, _, _, b₁, b₂, Λa, _, _, ML, CL, MK, CK, V, _, _, ι, φ, h, α, e, hb, hΛa, -, -,
    -, -, hMK, hCK, -, hlin, -, -, hpairK, -, hK, -⟩ := hA
  refine ggAutWeylThree_of_aligned_part hMK hCK hlin hpairK hK ?_
  have hΛ : Fintype.card Λ = N - 1 := by rw [← Fintype.card_congr e, Fintype.card_fin]
  have hΛa' : Fintype.card Λa = k := by rw [← Nat.card_eq_fintype_card, hΛa]
  rw [Fintype.card_sum, card_ne_pair hb, hΛ, hΛa']
  omega

theorem GGTWAligned.autWeylThree_L {Bs L J K : Subgroup G} {N k : ℕ}
    (hA : GGTWAligned p N k Bs L J K) (hN : 4 ≤ N) : GGAutWeylThree p Bs L := by
  obtain ⟨-, Λ, _, _, b₁, b₂, Λa, _, _, ML, CL, MK, CK, V, _, _, ι, φ, h, α, e, -, -, -, -,
    hML, hCL, -, -, -, hlin, -, hpairL, -, hL, -, -⟩ := hA
  refine ggAutWeylThree_of_aligned_frame hML hCL hlin hpairL hL ?_
  rw [← Fintype.card_congr e, Fintype.card_fin]
  omega

theorem GGDepED4Aligned.autWeylThree_K {Bs L J K : Subgroup G} {k : ℕ}
    (hA : GGDepED4Aligned p k Bs L J K) : GGAutWeylThree p Bs K := by
  obtain ⟨Λ, _, _, b₁, b₂, Λa, _, _, ML, CL, MK, CK, V, _, _, ι, φ, h, α, e, hb₁, hb₂, -, -,
    -, -, hMK, hCK, -, hlin, -, -, hpairK, -, hK, -⟩ := hA
  refine ggAutWeylThree_of_aligned_part hMK hCK hlin hpairK hK ?_
  have hb : b₁ ≠ b₂ := by
    rw [hb₁, hb₂]
    exact fun h => absurd (e.injective h) (by decide)
  have hΛ : Fintype.card Λ = 6 := by rw [← Fintype.card_congr e, Fintype.card_fin]
  rw [Fintype.card_sum, card_ne_pair hb, hΛ]
  omega

theorem GGDepED4Aligned.autWeylThree_L {Bs L J K : Subgroup G} {k : ℕ}
    (hA : GGDepED4Aligned p k Bs L J K) : GGAutWeylThree p Bs L := by
  obtain ⟨Λ, _, _, b₁, b₂, Λa, _, _, ML, CL, MK, CK, V, _, _, ι, φ, h, α, e, -, -, -, -,
    hML, hCL, -, -, -, hlin, -, hpairL, -, hL, -, -⟩ := hA
  refine ggAutWeylThree_of_aligned_frame hML hCL hlin hpairL hL ?_
  rw [← Fintype.card_congr e, Fintype.card_fin]
  omega

theorem ggTWHLSmall_holds : GGTWHLSmall := by
  intro G _ _ p N _ B Bs x L D J y K hH _ _ _ hN _ hA
  exact ggTWHLAt_base_of_autWeylThree hH (hA.autWeylThree_K (by omega) le_rfl)

theorem ggHL58BaseRestInput_holds : GGHL58BaseRestInput :=
  ggHL58BaseRestInput_of_hHL ggTWHLSmall_holds

theorem ggHL58NbrRestInput_holds : GGHL58NbrRestInput := by
  intro G _ _ p N k _ B Bs x L D J y K hH _ _ hk _ _ hN _ hA _ _
  exact ggTWHLAt_nbr_of_autWeylThree hH (hA.autWeylThree_K (by omega) (by omega))

theorem ggHL58NbrTorRestInput_holds : GGHL58NbrTorRestInput :=
  ggHL58NbrTorRestInput_of_rest ggHL58NbrRestInput_holds

theorem ggDepED4L58NbrRestInput_holds : GGDepED4L58NbrRestInput := by
  intro G _ _ p k _ B Bs x L D J y K hH _ _
  exact ⟨fun _ _ _ hA _ _ => ⟨fun _ => ggTWHLAt_base_of_autWeylThree hH hA.autWeylThree_L,
      fun _ _ => ggTWHLAt_nbr_of_autWeylThree hH hA.autWeylThree_K⟩,
    fun _ hA _ => ⟨fun _ => ggTWHLAt_base_of_autWeylThree hH hA.autWeylThree_K,
      fun _ _ => ggTWHLAt_nbr_of_autWeylThree hH hA.autWeylThree_L⟩⟩

end Cells

end CFSG.StandardType
