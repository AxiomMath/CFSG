module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.GLTransport
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLCaseA
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj
public import CFSG.Quasithin.Vol2.Ch11SecGOdd2
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecBBasic
public import CFSG.Quasithin.Vol2.Ch11SecD551D
public import CFSG.Quasithin.Vol2.Ch11SecGOdd1
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.OutcomeLocal
open Module
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem rk_eq_finrank_additive (U : Type) [CommGroup U] [ExpTwo U] [Finite U] :
    rk U = Module.finrank (ZMod 2) (Additive U) := by
  have hcard : Nat.card (Additive U) = Nat.card U := Nat.card_congr Additive.toMul
  have hpow : Nat.card U = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    rw [← hcard]
    simpa [ZMod.card] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
  unfold rk
  rw [hpow, padicValNat.prime_pow]

theorem false_of_obstruction
    {U : Type} [CommGroup U] [ExpTwo U]
    [Finite U] (h3 : 3 ≤ rk U)
    {Mbar : Subgroup (Additive U ≃ₗ[ZMod 2] Additive U)}
    (hMbar : Mbar = ⊤)
    {K : Subgroup (Additive U ≃ₗ[ZMod 2] Additive U)}
    (hKsub : CFSG.Open.IsSubnormal K Mbar) (hKne : K ≠ ⊥)
    {U₀ : Subgroup U} (hU₀ne : U₀ ≠ ⊥) (hU₀lt : U₀ ≠ ⊤)
    (hN : ∀ k ∈ K, ∀ u ∈ U₀,
      Additive.toMul ((k : Additive U →ₗ[ZMod 2] Additive U) (Additive.ofMul u)) ∈ U₀) :
    False := by
  have h3' : 3 ≤ Module.finrank (ZMod 2) (Additive U) := by
    rw [← rk_eq_finrank_additive U]
    exact h3
  haveI : IsSimpleGroup Mbar := hMbar ▸
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_top_of_three_le h3'
  have hKtop : K = Mbar := by
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hKsub inferInstance with h | h
    · exact absurd h hKne
    · exact h
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU₀ne
  have hxU₀ : (x : U) ∈ U₀ := x.2
  have hx0 : Additive.ofMul (x : U) ≠ 0 := by
    intro h
    exact hx1 (by simpa using Additive.ofMul.injective h)
  have hyU₀ : ¬ (Set.univ : Set U) ⊆ U₀ := by
    intro h
    exact hU₀lt (eq_top_iff.mpr fun y _ => h trivial)
  obtain ⟨y, -, hyU₀⟩ := Set.not_subset.mp hyU₀
  have hy0 : Additive.ofMul y ≠ 0 := by
    intro h
    exact hyU₀ (by simpa [Additive.ofMul.injective h] using U₀.one_mem)
  obtain ⟨φ, d, hφd, hgd⟩ :=
    CFSG.GroupTheory.GLnTwoSplitting.exists_transvection_apply_eq hx0 hy0
  have hmemK : LinearEquiv.transvection hφd ∈ K := by
    have htop : LinearEquiv.transvection hφd ∈
        (⊤ : Subgroup (Additive U ≃ₗ[ZMod 2] Additive U)) := Subgroup.mem_top _
    simpa [hKtop, hMbar] using htop
  have hmem : Additive.toMul ((LinearEquiv.transvection hφd) (Additive.ofMul (x : U))) ∈ U₀ :=
    hN (LinearEquiv.transvection hφd) hmemK (x : U) hxU₀
  rw [hgd] at hmem
  exact hyU₀ (by simpa using hmem)

theorem image_eq_top
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (h3 : 3 ≤ finrank (ZMod 2) V)
    (Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hgen : GenByTransvections Y) (hirr : IsIrreducibleOn Y)
    {W₁ W₂ : Submodule (ZMod 2) V} {φ ψ : Dual (ZMod 2) V}
    (hker₁ : ∀ v, φ v = 0 ↔ v ∈ W₁) (hker₂ : ∀ v, ψ v = 0 ↔ v ∈ W₂)
    (hW₁ : W₁ ≠ ⊤) (hW₂ : W₂ ≠ ⊤) (hsep : ∃ b, b ∈ W₂ ∧ b ∉ W₁)
    (hfull₁ : ∀ a ∈ W₁, InG Y φ a) (hfull₂ : ∀ b ∈ W₂, InG Y ψ b) :
    Y = ⊤ := by
  have hφ : φ ≠ 0 := by
    intro h0
    apply hW₁
    rw [eq_top_iff]
    intro v _
    rw [← hker₁ v, h0]
    rfl
  have hψ : ψ ≠ 0 := by
    intro h0
    apply hW₂
    rw [eq_top_iff]
    intro v _
    rw [← hker₂ v, h0]
    rfl
  have hker₁' : LinearMap.ker φ = W₁ := Submodule.ext hker₁
  have hker₂' : LinearMap.ker ψ = W₂ := Submodule.ext hker₂
  have hdim : 1 ≤ finrank (ZMod 2) ↥(W₁ ⊓ W₂) := by
    have h := CFSG.GroupTheory.GLnTwoSplitting.finrank_ker_inf_ker_add_two_ge φ ψ
    rw [hker₁', hker₂'] at h
    omega
  obtain ⟨a, ha, ha0⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_ne_zero_mem_of_finrank_pos hdim
  have haW₁ : a ∈ W₁ := ha.1
  have haW₂ : a ∈ W₂ := ha.2
  obtain ⟨b, hbW₂, hbW₁⟩ := hsep
  have hφa : InG Y φ a := hfull₁ a haW₁
  have hψb : InG Y ψ b := hfull₂ b hbW₂
  have hφb : φ b = 1 := by
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one (φ b) with h0 | h1
    · exact absurd ((hker₁ b).mp h0) hbW₁
    · exact h1
  have hψa : ψ a = 0 := (hker₂ a).mpr haW₂
  exact eq_top_of_dihedral hgen hirr ha0 hψ hφa hψb hφb hψa

private theorem sup_span_eq_top_of_ker_eq
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {W : Submodule (ZMod 2) V} {φ : Dual (ZMod 2) V}
    (hker : ∀ v, φ v = 0 ↔ v ∈ W) {x : V} (hxW : x ∉ W) :
    W ⊔ Submodule.span (ZMod 2) {x} = ⊤ := by
  have hφx : φ x = 1 := by
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one (φ x) with h0 | h1
    · exact absurd ((hker x).mp h0) hxW
    · exact h1
  rw [eq_top_iff]
  intro y _
  have hyW : y + φ y • x ∈ W := by
    rw [← hker]
    have hzero : φ y + φ y * φ x = 0 := by
      rw [hφx, mul_one]
      exact CFSG.GroupTheory.GLnTwoSplitting.zmod_two_add_self (φ y)
    simpa [map_add, map_smul, hzero] using hzero
  have hdecomp : y = (y + φ y • x) + φ y • x := by
    have ha : φ y • x + φ y • x = 0 := by
      rw [← two_smul (ZMod 2) (φ y • x)]
      rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [add_assoc, ha, add_zero]
  rw [hdecomp]
  exact (W ⊔ Submodule.span (ZMod 2) {x}).add_mem (Submodule.mem_sup_left hyW)
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))

private theorem le_axis_of_isInvariant
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {W : Submodule (ZMod 2) V} {φ : Dual (ZMod 2) V}
    (hker : ∀ v, φ v = 0 ↔ v ∈ W) (hφ : φ ≠ 0)
    (hfull : ∀ a ∈ W, InG Y φ a)
    {X : Submodule (ZMod 2) V} (hX : IsGInvariant Y X) (hXlt : X ≠ ⊤) :
    X ≤ W := by
  intro x hxX
  by_contra hxW
  have hφx : φ x = 1 := by
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one (φ x) with h0 | h1
    · exact absurd ((hker x).mp h0) hxW
    · exact h1
  have htop := sup_span_eq_top_of_ker_eq hker hxW
  have hWnot : ¬ W ≤ X := by
    intro hWX
    have hXtop : (⊤ : Submodule (ZMod 2) V) ≤ X := by
      rw [← htop]
      exact sup_le hWX (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxX))
    exact hXlt (top_le_iff.mp hXtop)
  obtain ⟨a, haW, haX⟩ := Set.not_subset.mp hWnot
  obtain ⟨hφa, htv⟩ := hfull a haW
  have hmemX : ((tv φ a hφa : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) x ∈ X :=
    hX (tv φ a hφa) htv x hxX
  rw [tv_apply, hφx, one_smul] at hmemX
  refine haX ?_
  have hthis : x + a + x ∈ X := by
    simpa [sub_eq_add_neg, CFSG.GroupTheory.GLnTwoSplitting.two_neg] using
      X.sub_mem hmemX hxX
  rw [show x + a + x = a by
    rw [add_assoc, add_comm a x, ← add_assoc,
      CFSG.ComponentClassification.OutcomeLocal.zmod2_add_self, zero_add]] at hthis
  exact hthis

private theorem map_invariant_of_normal
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Mbar Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hnormal : Mbar ≤ Subgroup.normalizer (Y : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)))
    {X : Submodule (ZMod 2) V} (hX : IsGInvariant Y X)
    (m : Mbar) : IsGInvariant Y
      (X.map ((m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) := by
  intro y hy z hz
  obtain ⟨x, hxX, rfl⟩ := Submodule.mem_map.mp hz
  have hy' : (m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ * y *
      (m : LinearMap.GeneralLinearGroup (ZMod 2) V) ∈ Y :=
    (Subgroup.mem_normalizer_iff''.1 (hnormal m.2) y).1 hy
  refine ⟨((((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ * y *
    (m : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) x,
    hX ((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ * y *
      (m : LinearMap.GeneralLinearGroup (ZMod 2) V)) hy' x hxX, ?_⟩
  change (((m : LinearMap.GeneralLinearGroup (ZMod 2) V) * ((m :
    LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ * y * (m :
      LinearMap.GeneralLinearGroup (ZMod 2) V)) :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x =
    ((y * (m : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x
  have hgroup : (m : LinearMap.GeneralLinearGroup (ZMod 2) V) * ((m :
      LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ * y * (m :
        LinearMap.GeneralLinearGroup (ZMod 2) V)) =
      y * (m : LinearMap.GeneralLinearGroup (ZMod 2) V) := by group
  rw [hgroup]

private theorem map_ne_top_of_ne_top
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {X : Submodule (ZMod 2) V} {m : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hX : X ≠ ⊤) : X.map ((m : V →ₗ[ZMod 2] V)) ≠ ⊤ := by
  intro htop
  apply hX
  let e : V ≃ₗ[ZMod 2] V := m.toLinearEquiv
  have hcomp : ((e.symm : V →ₗ[ZMod 2] V)).comp (e : V →ₗ[ZMod 2] V) = LinearMap.id := by
    ext x
    simp
  have htop' : X.map (e : V →ₗ[ZMod 2] V) = ⊤ := by
    change X.map ((m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = ⊤
    exact htop
  have hmap := congrArg (Submodule.map (e.symm : V →ₗ[ZMod 2] V)) htop'
  rw [← Submodule.map_comp, hcomp, Submodule.map_id, Submodule.map_top] at hmap
  have hrange : LinearMap.range (e.symm : V →ₗ[ZMod 2] V) = ⊤ := LinearEquiv.range e.symm
  rwa [hrange] at hmap

private theorem map_map_inv_eq_self
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (X : Submodule (ZMod 2) V) (m : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    (X.map ((m : V →ₗ[ZMod 2] V))).map
      (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) : V →ₗ[ZMod 2] V) = X := by
  let e : V ≃ₗ[ZMod 2] V := m.toLinearEquiv
  have hcomp : ((e.symm : V →ₗ[ZMod 2] V)).comp (e : V →ₗ[ZMod 2] V) = LinearMap.id := by
    ext x
    simp
  change (X.map (e : V →ₗ[ZMod 2] V)).map (e.symm : V →ₗ[ZMod 2] V) = X
  rw [← Submodule.map_comp, hcomp, Submodule.map_id]

private theorem iInf_conj_axes_invariant
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Mbar : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {W : Submodule (ZMod 2) V} :
    IsGInvariant Mbar (⨅ m : Mbar, W.map
      (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) : V →ₗ[ZMod 2] V)) := by
  intro n hn z hz
  rw [Submodule.mem_iInf] at hz ⊢
  intro m
  have hzm : z ∈ W.map ((((m * ⟨n, hn⟩ : Mbar) :
      LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) : V →ₗ[ZMod 2] V) :=
    hz (m * ⟨n, hn⟩)
  have hgroup : (n : LinearMap.GeneralLinearGroup (ZMod 2) V) *
      (((m * ⟨n, hn⟩ : Mbar) :
        LinearMap.GeneralLinearGroup (ZMod 2) V))⁻¹ =
      (m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ := by
    have hcoe : ((m * ⟨n, hn⟩ : Mbar) :
        LinearMap.GeneralLinearGroup (ZMod 2) V) =
        (m : LinearMap.GeneralLinearGroup (ZMod 2) V) *
          (n : LinearMap.GeneralLinearGroup (ZMod 2) V) := rfl
    rw [hcoe, mul_inv_rev]
    group
  have hcomp : (W.map ((((m * ⟨n, hn⟩ : Mbar) :
      LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) : V →ₗ[ZMod 2] V)).map
      ((n : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) =
      W.map (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) :
        V →ₗ[ZMod 2] V) := by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp]
    congr 1
    exact congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V)) hgroup
  rw [← hcomp]
  exact Submodule.mem_map.mpr ⟨z, hzm, rfl⟩

private theorem iInf_conj_axes_le
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Mbar : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {W : Submodule (ZMod 2) V} :
    (⨅ m : Mbar, W.map (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) :
      V →ₗ[ZMod 2] V)) ≤ W := by
  have h := iInf_le (fun m : Mbar => W.map
    (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) : V →ₗ[ZMod 2] V))
    (⟨1, Mbar.one_mem⟩ : Mbar)
  have hmap1 : W.map ((((⟨1, Mbar.one_mem⟩ : Mbar) :
      LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) : V →ₗ[ZMod 2] V) = W := by
    ext x
    simp
  rwa [hmap1] at h

theorem irreducible_transvection_subgroup
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Mbar Y : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hnormal : Mbar ≤ Subgroup.normalizer (Y : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)))
    (hirr : IsIrreducibleOn Mbar)
    {W : Submodule (ZMod 2) V} {φ : Dual (ZMod 2) V}
    (hW : W ≠ ⊤) (hker : ∀ v, φ v = 0 ↔ v ∈ W) (hφ : φ ≠ 0)
    (hfull : ∀ a ∈ W, InG Y φ a) :
    IsIrreducibleOn Y := by
  intro X hX
  by_cases hXtop : X = ⊤
  · exact Or.inr hXtop
  set J : Submodule (ZMod 2) V :=
    ⨅ m : Mbar, W.map (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) :
      V →ₗ[ZMod 2] V) with hJ
  have hXleJ : X ≤ J := by
    rw [hJ]
    refine le_iInf fun m => ?_
    have hmXinv := map_invariant_of_normal hnormal hX m
    have hmXlt := map_ne_top_of_ne_top (X := X)
      (m := (m : LinearMap.GeneralLinearGroup (ZMod 2) V)) hXtop
    have hle := le_axis_of_isInvariant (Y := Y) hker hφ hfull hmXinv hmXlt
    calc
      X = (X.map ((m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)).map
          (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) : V →ₗ[ZMod 2] V) :=
        (map_map_inv_eq_self X (m : LinearMap.GeneralLinearGroup (ZMod 2) V)).symm
      _ ≤ W.map (((m : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : _) :
          V →ₗ[ZMod 2] V) := Submodule.map_mono hle
  have hJinv : IsGInvariant Mbar J := hJ ▸ iInf_conj_axes_invariant (Mbar := Mbar) (W := W)
  have hJleW : J ≤ W := hJ ▸ iInf_conj_axes_le (Mbar := Mbar) (W := W)
  have hJne : J ≠ ⊤ := by
    intro htop
    have htopW : (⊤ : Submodule (ZMod 2) V) ≤ W := htop ▸ hJleW
    exact hW (top_le_iff.mp htopW)
  have hJbot : J = ⊥ := by
    rcases hirr J hJinv with h | h
    · exact h
    · exact absurd h hJne
  exact Or.inl (le_bot_iff.mp (hXleJ.trans_eq hJbot))

private theorem mQuot_conj_eq_one_of_InCalO {U M : Subgroup G} {g : G}
    (hU : IsElemAbelian 2 U) (hO : InCalO 1 M ⊥ U g) :
    E3.mQuot (conjSubgroup U g) M = 1 ∧ E3.mQuot U (conjSubgroup M g) = 1 := by
  set Ug : Subgroup G := conjSubgroup U g with hUg
  set Mg : Subgroup G := conjSubgroup M g with hMg
  have hUgP : IsPGroup 2 Ug := by
    rw [hUg]
    exact IsPGroup.map (IsElemAbelian.isPGroup hU) _
  have hmE : E3.mQuot Ug M = 1 := by
    have hle : E3.mQuot Ug M ≤ 1 := hO.2.2.1
    have hne : E3.mQuot Ug M ≠ 0 := by
      intro h0
      have hzero : E3.mQuot Ug (Ug ⊓ M) = 0 := by
        rw [CFSG.Quasithin.Vol2.Ch11.SecG.mQuot_inf_left]
        exact h0
      exact hO.1.1 (inf_eq_left.mp ((E3.mQuot_eq_zero_iff hUgP inf_le_left).mp hzero))
    omega
  have hmW : E3.mQuot U Mg = 1 := by
    have hle : E3.mQuot U Mg ≤ 1 := hO.1.2.1
    have hne : E3.mQuot U Mg ≠ 0 := by
      intro h0
      have hzero : E3.mQuot U (U ⊓ Mg) = 0 := by
        rw [CFSG.Quasithin.Vol2.Ch11.SecG.mQuot_inf_left]
        exact h0
      exact hO.2.1 (inf_eq_left.mp
        ((E3.mQuot_eq_zero_iff (IsElemAbelian.isPGroup hU) inf_le_left).mp hzero))
    omega
  exact ⟨hmE, hmW⟩

private theorem two_pow_rk_eq_two_mul {U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hne : U ≠ ⊥) : 2 ^ rk U = 2 * 2 ^ (rk U - 1) := by
  have hcardU : Nat.card U = 2 ^ rk U :=
    card_eq_two_pow_of_isPGroup (IsElemAbelian.isPGroup hU)
  have h2 : 2 ≤ Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).mpr hne
  rw [hcardU] at h2
  have hr : 1 ≤ rk U := by
    by_contra hr
    have : rk U = 0 := by omega
    rw [this] at h2
    norm_num at h2
  rw [show rk U = rk U - 1 + 1 by omega, pow_succ, Nat.mul_comm]
  rw [show rk U - 1 + 1 - 1 = rk U - 1 by omega]

private theorem card_conj_inter_left_of_InCalO {U M : Subgroup G} {g : G}
    (hU : IsElemAbelian 2 U) (hO : InCalO 1 M ⊥ U g) :
    Nat.card ↥(conjSubgroup U g ⊓ M) = 2 ^ (rk U - 1) := by
  set Ug : Subgroup G := conjSubgroup U g with hUg
  have hmE := (mQuot_conj_eq_one_of_InCalO hU hO).1
  have hUgP : IsPGroup 2 Ug := by
    rw [hUg]
    exact IsPGroup.map (IsElemAbelian.isPGroup hU) _
  have hcardU : Nat.card U = 2 ^ rk U :=
    card_eq_two_pow_of_isPGroup (IsElemAbelian.isPGroup hU)
  have hcardUg : Nat.card Ug = Nat.card U := by
    rw [hUg]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hUne : U ≠ ⊥ := by
    intro hbot
    refine hO.1.1 ?_
    rw [hbot]
    simpa [CFSG.Quasithin.conjSubgroup] using (bot_le : (⊥ : Subgroup G) ≤ M)
  have hrel : M.relIndex Ug = 2 := by
    rw [E3.relIndex_eq_two_pow hUgP M, hmE]
    norm_num
  have h := Subgroup.relIndex_mul_card (H := M) (K := Ug)
  rw [hrel, inf_comm] at h
  have h' : 2 * Nat.card ↥(Ug ⊓ M) = 2 * 2 ^ (rk U - 1) := by
    rw [h, hcardUg, hcardU, two_pow_rk_eq_two_mul hU hUne]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

private theorem card_conj_inter_right_of_InCalO {U M : Subgroup G} {g : G}
    (hU : IsElemAbelian 2 U) (hO : InCalO 1 M ⊥ U g) :
    Nat.card ↥(U ⊓ conjSubgroup M g) = 2 ^ (rk U - 1) := by
  set Mg : Subgroup G := conjSubgroup M g with hMg
  have hmW := (mQuot_conj_eq_one_of_InCalO hU hO).2
  have hcardU : Nat.card U = 2 ^ rk U :=
    card_eq_two_pow_of_isPGroup (IsElemAbelian.isPGroup hU)
  have hUne : U ≠ ⊥ := by
    intro hbot
    refine hO.1.1 ?_
    rw [hbot]
    simpa [CFSG.Quasithin.conjSubgroup] using (bot_le : (⊥ : Subgroup G) ≤ M)
  have hrel : Mg.relIndex U = 2 := by
    rw [E3.relIndex_eq_two_pow (IsElemAbelian.isPGroup hU) Mg, hmW]
    norm_num
  have h := Subgroup.relIndex_mul_card (H := Mg) (K := U)
  rw [hrel, inf_comm] at h
  have h' : 2 * Nat.card ↥(U ⊓ Mg) = 2 * 2 ^ (rk U - 1) := by
    rw [h, hcardU, two_pow_rk_eq_two_mul hU hUne]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

private theorem conj_inter_fixes_axis {U M : Subgroup G} {g : G}
    (hUM : U ≤ M) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hTI : U ⊓ conjSubgroup U g = ⊥)
    {e w : G} (he : e ∈ conjSubgroup U g ⊓ M) (hw : w ∈ U ⊓ conjSubgroup M g) :
    e * w * e⁻¹ = w := by
  set Ug : Subgroup G := conjSubgroup U g with hUg
  set Mg : Subgroup G := conjSubgroup M g with hMg
  have hMgN : Mg ≤ Subgroup.normalizer (Ug : Set G) := by
    rw [hMg, hUg, ← CFSG.Quasithin.E3.conjSubgroup_normalizer]
    exact CFSG.QuasithinUnique.C5.conjSubgroup_mono hMU g
  have heUg : e ∈ Ug := he.1
  have heM : e ∈ M := he.2
  have hwU : w ∈ U := hw.1
  have hwMg : w ∈ Mg := hw.2
  have hw_e_inv_Ug : w⁻¹ * e⁻¹ * w ∈ Ug := by
    have h1 : w⁻¹ * e * w ∈ Ug :=
      (Subgroup.mem_normalizer_iff''.1 (hMgN hwMg) e).1 heUg
    simpa only [mul_assoc, mul_inv_rev, inv_inv] using Ug.inv_mem h1
  have hwe_U : w⁻¹ * (e⁻¹ * w * e) ∈ U := by
    have h1 : e⁻¹ * w * e ∈ U :=
      (Subgroup.mem_normalizer_iff''.1 (hMU heM) w).1 hwU
    exact U.mul_mem (U.inv_mem hwU) h1
  have hcomm_mem : w⁻¹ * e⁻¹ * w * e ∈ Ug ⊓ U := by
    refine ⟨?_, ?_⟩
    · exact Ug.mul_mem hw_e_inv_Ug heUg
    · rw [show w⁻¹ * e⁻¹ * w * e = w⁻¹ * (e⁻¹ * w * e) from by group]
      exact hwe_U
  have hcomm : w⁻¹ * e⁻¹ * w * e = 1 := by
    have hbot : Ug ⊓ U = ⊥ := by rw [inf_comm, hUg]; exact hTI
    rw [hbot] at hcomm_mem
    exact Subgroup.mem_bot.mp hcomm_mem
  have h1 : w * e = e * w := by
    have h2 : e⁻¹ * w * e = w := by
      have := congrArg (fun x => w * x) hcomm
      simpa [mul_assoc] using this
    have := congrArg (fun x => e * x) h2
    simpa [mul_assoc] using this
  calc e * w * e⁻¹ = (w * e) * e⁻¹ := by rw [h1]
    _ = w := by group

private theorem conj_inter_faithful {U M : Subgroup G} {g : G}
    (hO : InCalO 1 M ⊥ U g)
    (hC : ∀ e ∈ conjSubgroup U g ⊓ M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup M g)
    {e : G} (he : e ∈ conjSubgroup U g ⊓ M) :
    (∀ u ∈ U, e * u * e⁻¹ = u) → e = 1 := by
  intro hfix
  by_contra he1
  have hu : U ≤ Subgroup.centralizer ({e} : Set G) := by
    intro u huU
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix u huU
    have h2 : e⁻¹ * u * e = u := by
      calc e⁻¹ * u * e = e⁻¹ * (e * u * e⁻¹) * e := by rw [h]
        _ = u := by group
    calc u * e = e * (e⁻¹ * u * e) := by group
      _ = e * u := by rw [h2]
  exact hO.2.1 (hu.trans (hC e he he1))

theorem full_transvections
    {U M : Subgroup G} {g : G}
    (hU : IsElemAbelian 2 U)
    (hUM : U ≤ M)
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hTI : U ⊓ conjSubgroup U g = ⊥)
    (hO : InCalO 1 M ⊥ U g)
    (hC : ∀ e ∈ conjSubgroup U g ⊓ M, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) ≤ conjSubgroup M g) :
    Nat.card ↥(conjSubgroup U g ⊓ M) = 2 ^ (rk U - 1) ∧
      Nat.card ↥(U ⊓ conjSubgroup M g) = 2 ^ (rk U - 1) ∧
      (∀ e ∈ conjSubgroup U g ⊓ M, e * e = 1) ∧
      (∀ e ∈ conjSubgroup U g ⊓ M, ∀ w ∈ U ⊓ conjSubgroup M g, e * w * e⁻¹ = w) ∧
      (∀ e ∈ conjSubgroup U g ⊓ M, (∀ u ∈ U, e * u * e⁻¹ = u) → e = 1) ∧
      (∀ e ∈ conjSubgroup U g ⊓ M, e ≠ 1 →
        ∃ u ∈ U, e * u * e⁻¹ ≠ u) := by
  have hUe : IsElemAbelian 2 (conjSubgroup U g) :=
    IsElemAbelian.map hU (MulAut.conj g⁻¹).toMonoidHom
  refine ⟨card_conj_inter_left_of_InCalO hU hO, card_conj_inter_right_of_InCalO hU hO,
    ?_, ?_, ?_, ?_⟩
  · intro e he
    simpa [pow_two] using hUe.2 e he.1
  · intro e he w hw
    exact conj_inter_fixes_axis hUM hMU hTI he hw
  · intro e he
    exact conj_inter_faithful hO hC he
  · intro e he he1
    by_contra hnone
    refine he1 (conj_inter_faithful hO hC he ?_)
    intro u huU
    by_contra hne
    exact hnone ⟨u, huU, hne⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
