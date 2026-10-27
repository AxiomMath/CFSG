module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112AModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2xKDb_finite_of_span {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin n → U) (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) : Finite U := by
  have hsurj : Function.Surjective (fun c : Fin n → ZMod 3 => ∑ i, c i • h i) := by
    intro x
    have hx : x ∈ Submodule.span (ZMod 3) (Set.range h) := by rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, hc⟩
  exact Finite.of_surjective _ hsurj

private lemma ggQ2xKDb_range_simpleRefl {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {ι : Type} (h : ι → U) (α : ι → Module.Dual (ZMod 3) U) (s : ι → U ≃ₗ[ZMod 3] U)
    (hs : ∀ i v, s i v = v - α i v • h i) :
    Set.range s = {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, hs i⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, LinearEquiv.ext fun v => by rw [hj v, hs j v]⟩

private lemma ggQ2xKDb_isReflLin_form {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (t : U ≃ₗ[ZMod 3] U) (ht : IsReflLin t) :
    ∃ (v : U) (f : Module.Dual (ZMod 3) U), ∀ x, t x = x - f x • v := by
  obtain ⟨c, φ, hφ, rfl⟩ := ht
  exact ⟨c, φ, fun x => Module.reflection_apply x hφ⟩

private lemma ggQ2xKDb_sq_of_isReflLin {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (t : U ≃ₗ[ZMod 3] U) (ht : IsReflLin t) : t ^ 2 = 1 := by
  obtain ⟨c, φ, hφ, rfl⟩ := ht
  ext x
  rw [pow_two, LinearEquiv.mul_apply]
  simpa using Module.involutive_reflection hφ x

private lemma ggQ2xKDb_reflection_ne_one {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (c : U) (f : Module.Dual (ZMod 3) U) (hf : f c = 2) : Module.reflection hf ≠ 1 := by
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact (by decide : (2 : ZMod 3) ≠ 0) hf.symm
  intro h1
  have h2 : Module.reflection hf c = c := by rw [h1]; rfl
  rw [Module.reflection_apply, hf] at h2
  have h3 : (2 : ZMod 3) • c = 0 := sub_eq_self.mp h2
  exact hc ((smul_eq_zero.mp h3).resolve_left (by decide))

private lemma ggQ2xKDb_reflClosed {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Finite U] (h : Fin n → U) (hb : LinearIndependent (ZMod 3) h)
    (α : Fin n → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A n i j : ℤ) : ZMod 3))
    (s : Fin n → U ≃ₗ[ZMod 3] U) (hs : ∀ i v, s i v = v - α i v • h i) :
    GGReflClosed s :=
  ggReflClosed_of_indep (p := 3) (by norm_num) (TauCeti.isFiniteType_cartanMatrix_A n)
    (ggIntCartan_A n) h α (fun i j => by simpa using hα i j) hb s hs

private lemma ggQ2xKDb_transp_conj {k : ℕ} (x : Equiv.Perm (Fin k)) {t : Equiv.Perm (Fin k)}
    (ht : t ∈ ggTransp k) : x * t * x⁻¹ ∈ ggTransp k := by
  obtain ⟨a, b, hab, rfl⟩ := ht
  rw [← Equiv.swap_apply_apply]
  exact ⟨x a, x b, fun hh => hab (x.injective hh), rfl⟩

private lemma ggQ2xKDb_conj_hom {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Φ : Equiv.Perm (Fin (n+1)) →* (U ≃ₗ[ZMod 3] U)) (hinj : Function.Injective Φ)
    (T : U ≃ₗ[ZMod 3] U) (W : Subgroup (U ≃ₗ[ZMod 3] U)) (hW : W = Φ.range)
    (hTmem : ∀ x ∈ W, T * x * T⁻¹ ∈ W) :
    ∃ π : Equiv.Perm (Fin (n+1)) →* Equiv.Perm (Fin (n+1)),
      (∀ σ, Φ (π σ) = T * Φ σ * T⁻¹) ∧ Function.Injective π := by
  classical
  have hpre : ∀ σ : Equiv.Perm (Fin (n+1)), ∃ τ, Φ τ = T * Φ σ * T⁻¹ := by
    intro σ
    have hmem : T * Φ σ * T⁻¹ ∈ W :=
      hTmem (Φ σ) (by rw [hW]; exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
    rw [hW] at hmem
    exact MonoidHom.mem_range.mp hmem
  let π₀ : Equiv.Perm (Fin (n+1)) → Equiv.Perm (Fin (n+1)) := fun σ => Classical.choose (hpre σ)
  have hπ₀ : ∀ σ, Φ (π₀ σ) = T * Φ σ * T⁻¹ := fun σ => Classical.choose_spec (hpre σ)
  have hmul : ∀ σ τ, π₀ (σ * τ) = π₀ σ * π₀ τ := by
    intro σ τ
    apply hinj
    calc Φ (π₀ (σ * τ)) = T * Φ (σ * τ) * T⁻¹ := hπ₀ _
      _ = T * (Φ σ * Φ τ) * T⁻¹ := by rw [map_mul]
      _ = (T * Φ σ * T⁻¹) * (T * Φ τ * T⁻¹) := by group
      _ = Φ (π₀ σ) * Φ (π₀ τ) := by rw [hπ₀ σ, hπ₀ τ]
      _ = Φ (π₀ σ * π₀ τ) := by rw [map_mul]
  let π : Equiv.Perm (Fin (n+1)) →* Equiv.Perm (Fin (n+1)) := MonoidHom.mk' π₀ hmul
  have hπ : ∀ σ, Φ (π σ) = T * Φ σ * T⁻¹ := fun σ => hπ₀ σ
  refine ⟨π, hπ, ?_⟩
  intro σ τ hστ
  have h3 : MulAut.conj T (Φ σ) = MulAut.conj T (Φ τ) := by
    rw [MulAut.conj_apply, MulAut.conj_apply, ← hπ σ, ← hπ τ, hστ]
  exact hinj ((MulAut.conj T).injective h3)

private lemma ggQ2xKDb_adj_mem {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin n → U) (α : Fin n → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A n i j : ℤ) : ZMod 3))
    (Φ : Equiv.Perm (Fin (n+1)) →* (U ≃ₗ[ZMod 3] U)) (hinj : Function.Injective Φ)
    (s : Fin n → U ≃ₗ[ZMod 3] U) (hs : ∀ i v, s i v = v - α i v • h i)
    (hsΦ : ∀ i, s i = Φ (Equiv.swap i.castSucc i.succ))
    (hclosed : GGReflClosed s) (hclosure : Subgroup.closure (Set.range s) = Φ.range)
    (T : U ≃ₗ[ZMod 3] U) (π : Equiv.Perm (Fin (n+1)) →* Equiv.Perm (Fin (n+1)))
    (hπ : ∀ σ, Φ (π σ) = T * Φ σ * T⁻¹)
    (hTmem : ∀ x ∈ Subgroup.closure (Set.range s),
      T * x * T⁻¹ ∈ Subgroup.closure (Set.range s))
    (i : Fin n) : π (Equiv.swap i.castSucc i.succ) ∈ ggTransp (n+1) := by
  have hself : α i (h i) = 2 := by rw [hα i i, ggQ2xKDa_coeff_self n i]; decide
  have hsk : s i = Module.reflection hself :=
    LinearEquiv.ext fun v => by rw [hs i v, Module.reflection_apply]
  have hrefl : IsReflLin (T * s i * T⁻¹) :=
    ggQ2_isReflLin_conj T (s i) ⟨h i, α i, hself, hsk⟩
  have hsq : (T * s i * T⁻¹) ^ 2 = 1 := ggQ2xKDb_sq_of_isReflLin _ hrefl
  have hne : T * s i * T⁻¹ ≠ 1 := by
    have hsi1 : s i ≠ 1 := by
      rw [hsk]; exact ggQ2xKDb_reflection_ne_one (h i) (α i) hself
    intro h1
    apply hsi1
    apply (MulAut.conj T).injective
    rw [MulAut.conj_apply, h1, map_one]
  have hmem : T * s i * T⁻¹ ∈ Subgroup.closure (Set.range s) :=
    hTmem (s i) (Subgroup.subset_closure ⟨i, rfl⟩)
  obtain ⟨u, hu, j, huj⟩ := hclosed _ hmem hsq hne (ggQ2xKDb_isReflLin_form _ hrefl)
  rw [hclosure] at hu
  obtain ⟨τ, hτ⟩ := MonoidHom.mem_range.mp hu
  have hkey : Φ (π (Equiv.swap i.castSucc i.succ)) =
      Φ (τ * Equiv.swap j.castSucc j.succ * τ⁻¹) := by
    calc Φ (π (Equiv.swap i.castSucc i.succ))
        = T * Φ (Equiv.swap i.castSucc i.succ) * T⁻¹ := hπ _
      _ = T * s i * T⁻¹ := by rw [hsΦ i]
      _ = u * s j * u⁻¹ := huj
      _ = Φ τ * Φ (Equiv.swap j.castSucc j.succ) * (Φ τ)⁻¹ := by rw [← hτ, hsΦ j]
      _ = Φ (τ * Equiv.swap j.castSucc j.succ * τ⁻¹) := by rw [map_mul, map_mul, map_inv]
  have hπeq : π (Equiv.swap i.castSucc i.succ) = τ * Equiv.swap j.castSucc j.succ * τ⁻¹ :=
    hinj hkey
  exact ⟨τ j.castSucc, τ j.succ, fun hh => Fin.castSucc_lt_succ.ne (τ.injective hh),
    hπeq.trans (Equiv.swap_apply_apply τ j.castSucc j.succ).symm⟩

private lemma ggQ2xKDb_transp_mem {n : ℕ} (hn : 4 ≤ n)
    (π : Equiv.Perm (Fin (n+1)) →* Equiv.Perm (Fin (n+1)))
    (hπadj : ∀ i : Fin n, π (Equiv.swap i.castSucc i.succ) ∈ ggTransp (n+1)) :
    ∀ t ∈ ggTransp (n+1), π t ∈ ggTransp (n+1) := by
  intro t ht
  obtain ⟨a, b, hab, rfl⟩ := ht
  let i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨σ, hσ⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_swap (w := i₀.castSucc) (x := i₀.succ) (y := a) (z := b)
      Fin.castSucc_lt_succ.ne hab)
  rw [hσ.symm, map_mul, map_mul, map_inv]
  exact ggQ2xKDb_transp_conj (π σ) (hπadj i₀)

theorem ggQ2WeylInner_A {n : ℕ} (hn : 4 ≤ n) :
    GGQ2WeylInner n (CartanMatrix.A n) := by
  intro U _ _ h hb hspan α hα T hT
  classical
  obtain ⟨Φ, hinj, hΦswap⟩ := ggQ2xKD_A_model hn h hb hspan α hα
  let s : Fin n → U ≃ₗ[ZMod 3] U := fun i => Φ (Equiv.swap i.castSucc i.succ)
  have hs : ∀ i v, s i v = v - α i v • h i := fun i v => hΦswap i v
  have hWdef : ggQ2WeylOf h α = Subgroup.closure (Set.range s) := by
    rw [ggQ2WeylOf, ggQ2xKDb_range_simpleRefl h α s hs]
  have hclosure : Subgroup.closure (Set.range s) = Φ.range := by
    have hgen : Subgroup.closure
        (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) = ⊤ :=
      Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
    have himage : Φ '' (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) =
        Set.range s := by
      rw [← Set.range_comp]; rfl
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, himage]
  have hTmem : ∀ x ∈ Subgroup.closure (Set.range s),
      T * x * T⁻¹ ∈ Subgroup.closure (Set.range s) := by
    intro x hx
    rw [← hWdef] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp hT x).mp hx
  haveI : Finite U := ggQ2xKDb_finite_of_span h hspan
  have hclosed : GGReflClosed s := ggQ2xKDb_reflClosed h hb α hα s hs
  obtain ⟨π, hπ, hπinj⟩ :=
    ggQ2xKDb_conj_hom Φ hinj T (Subgroup.closure (Set.range s)) hclosure hTmem
  have hπadj : ∀ i : Fin n, π (Equiv.swap i.castSucc i.succ) ∈ ggTransp (n+1) :=
    fun i => ggQ2xKDb_adj_mem h α hα Φ hinj s hs (fun j => rfl) hclosed hclosure T π hπ hTmem i
  have hπT : ∀ t ∈ ggTransp (n+1), π t ∈ ggTransp (n+1) :=
    ggQ2xKDb_transp_mem hn π hπadj
  have hinjOn : Set.InjOn π (ggTransp (n+1)) := fun a _ b _ hh => hπinj hh
  have hπconj : ∀ u ∈ ggTransp (n+1), ∀ v ∈ ggTransp (n+1),
      π (u * v * u⁻¹) = π u * π v * (π u)⁻¹ := by
    intro u _ v _
    rw [map_mul, map_mul, map_inv]
  obtain ⟨g, hg⟩ := ggQ2_quandle_aut_sym (n+1) (by omega) π hπT hinjOn hπconj
  have hπg : ∀ σ, π σ = g * σ * g⁻¹ := by
    intro σ
    refine Equiv.Perm.swap_induction_on σ ?_ ?_
    · rw [map_one]; group
    · intro f x y hxy ih
      rw [map_mul, ih, hg (Equiv.swap x y) ⟨x, y, hxy, rfl⟩]
      group
  refine ⟨Φ g, ?_, ?_⟩
  · rw [hWdef, hclosure]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  · intro x hx
    rw [hWdef, hclosure] at hx
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← hπ σ, hπg σ, map_mul, map_mul, map_inv]
end CFSG.StandardType

end
