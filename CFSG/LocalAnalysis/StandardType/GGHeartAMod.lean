module

public import CFSG.LocalAnalysis.StandardType.GGHeartAPerm
public import CFSG.LocalAnalysis.StandardType.GGWAutSym
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggHAM_A_offdiag (r : ℕ) {i j : Fin r} (hne : i ≠ j)
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : CartanMatrix.A r i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne, if_pos h]

private lemma ggHAM_A_self (r : ℕ) (i : Fin r) : CartanMatrix.A r i i = 2 := by
  simp [CartanMatrix.A]

private noncomputable def ggHAM_refl {H : Type} [AddCommGroup H] [Module (ZMod 3) H] {r : ℕ}
    {h : Fin r → H} {α : Fin r → Module.Dual (ZMod 3) H} (hα2 : ∀ i, α i (h i) = 2) :
    Fin r → (H ≃ₗ[ZMod 3] H) :=
  fun i => Module.reflection (hα2 i)

private lemma ggHAM_refl_apply {H : Type} [AddCommGroup H] [Module (ZMod 3) H] {r : ℕ}
    {h : Fin r → H} {α : Fin r → Module.Dual (ZMod 3) H} (hα2 : ∀ i, α i (h i) = 2)
    (i : Fin r) (v : H) : ggHAM_refl hα2 i v = v - α i v • h i := by
  rw [ggHAM_refl, Module.reflection_apply]

private lemma ggHAM_rtg_adj {r : ℕ} (hr : 4 ≤ r) (rel : Fin r → Fin r → Prop)
    (hsymm : ∀ a b, rel a b → rel b a)
    (hadj : ∀ i (hi : i.val + 1 < r), rel i ⟨i.val + 1, hi⟩) :
    ∀ i j : Fin r, Relation.ReflTransGen rel i j := by
  have h0 : 0 < r := by omega
  let o : Fin r := ⟨0, h0⟩
  have rtg_symm : ∀ {a b : Fin r}, Relation.ReflTransGen rel a b →
      Relation.ReflTransGen rel b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih
  have hup : ∀ (n : ℕ) (hn : n < r), Relation.ReflTransGen rel o ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ n ih =>
        intro hn
        have hnr : n < r := by omega
        exact (ih hnr).tail (hadj ⟨n, hnr⟩ hn)
  have hdown : ∀ (n : ℕ) (hn : n < r), Relation.ReflTransGen rel ⟨n, hn⟩ o := by
    intro n
    induction n with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ n ih =>
        intro hn
        have hnr : n < r := by omega
        exact Relation.ReflTransGen.head (hsymm _ _ (hadj ⟨n, hnr⟩ hn)) (ih hnr)
  intro i j
  rcases le_total i.val j.val with hle | hle
  · exact (hdown i.val i.isLt).trans (hup j.val j.isLt)
  · exact rtg_symm ((hdown j.val j.isLt).trans (hup i.val i.isLt))

theorem ggWAut_sym_norm' {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    {N : ℕ} (hN : 5 ≤ N) (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (e : R ≃* Equiv.Perm (Fin N))
    (he : ∀ r : R, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    {t₀ : V ≃ₗ[ZMod 3] V} (ht₀R : t₀ ∈ R) (ht₀ : IsReflLin t₀)
    {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  classical
  have ht₀G : GGLinRefl t₀ := (ggLinRefl_iff_isReflLin t₀).mpr ht₀
  let T₀ : R := ⟨t₀, ht₀R⟩
  obtain ⟨i₀, j₀, hij₀, he₀⟩ := he T₀ ht₀G
  have hsym_refl : ∀ t ∈ ggTransp N, IsReflLin (((e.symm t : R) : V ≃ₗ[ZMod 3] V)) := by
    intro t ht
    obtain ⟨p, q, hpq, ht'⟩ := ht
    obtain ⟨u, hu⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hij₀ hpq)
    have ht_eq : t = u * (e T₀) * u⁻¹ := by
      rw [ht', he₀, hu]
    have hsym : e.symm t = e.symm u * T₀ * (e.symm u)⁻¹ := by
      rw [ht_eq]
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [hsym]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, T₀] using
      ggQ2_isReflLin_conj ((e.symm u : R) : V ≃ₗ[ZMod 3] V) t₀ ht₀
  let conjA : R ≃* R :=
    { toFun := fun x => ⟨a * (x : V ≃ₗ[ZMod 3] V) * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp ha (x : V ≃ₗ[ZMod 3] V)).mp x.2⟩
      invFun := fun x => ⟨a⁻¹ * (x : V ≃ₗ[ZMod 3] V) * a,
        (Subgroup.mem_normalizer_iff''.mp ha (x : V ≃ₗ[ZMod 3] V)).mp x.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change a⁻¹ * (a * (x : V ≃ₗ[ZMod 3] V) * a⁻¹) * a = (x : V ≃ₗ[ZMod 3] V)
        group
      right_inv := by
        intro x
        apply Subtype.ext
        change a * (a⁻¹ * (x : V ≃ₗ[ZMod 3] V) * a) * a⁻¹ = (x : V ≃ₗ[ZMod 3] V)
        group
      map_mul' := by
        intro x y
        apply Subtype.ext
        change a * ((x : V ≃ₗ[ZMod 3] V) * (y : V ≃ₗ[ZMod 3] V)) * a⁻¹ =
          (a * (x : V ≃ₗ[ZMod 3] V) * a⁻¹) * (a * (y : V ≃ₗ[ZMod 3] V) * a⁻¹)
        group }
  let π : Equiv.Perm (Fin N) → Equiv.Perm (Fin N) := fun s => e (conjA (e.symm s))
  have hπe : ∀ x : R, π (e x) = e (conjA x) := by
    intro x
    dsimp only [π]
    rw [MulEquiv.symm_apply_apply]
  have hπT : ∀ t ∈ ggTransp N, π t ∈ ggTransp N := by
    intro t ht
    show e (conjA (e.symm t)) ∈ ggTransp N
    have hrefl : IsReflLin (((e.symm t : R) : V ≃ₗ[ZMod 3] V)) := hsym_refl t ht
    have hrefl' : IsReflLin (((conjA (e.symm t) : R) : V ≃ₗ[ZMod 3] V)) := by
      simpa [conjA] using
        ggQ2_isReflLin_conj a ((e.symm t : R) : V ≃ₗ[ZMod 3] V) hrefl
    have hG : GGLinRefl (((conjA (e.symm t) : R) : V ≃ₗ[ZMod 3] V)) :=
      (ggLinRefl_iff_isReflLin _).mpr hrefl'
    obtain ⟨i, j, hij, heq⟩ := he (conjA (e.symm t)) hG
    exact ⟨i, j, hij, heq⟩
  have hinj : Set.InjOn π (ggTransp N) := by
    intro s hs t ht hst
    have hst' : e (conjA (e.symm s)) = e (conjA (e.symm t)) := hst
    have h1 : conjA (e.symm s) = conjA (e.symm t) := e.injective hst'
    have h2 : e.symm s = e.symm t := conjA.injective h1
    exact e.symm.injective h2
  have hπ : ∀ s ∈ ggTransp N, ∀ t ∈ ggTransp N,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹ := by
    intro s hs t ht
    show e (conjA (e.symm (s * t * s⁻¹))) =
      e (conjA (e.symm s)) * e (conjA (e.symm t)) * (e (conjA (e.symm s)))⁻¹
    simp only [map_mul, map_inv]
  obtain ⟨g, hg⟩ := ggQ2_quandle_aut_sym N hN π hπT hinj hπ
  let w : R := e.symm g
  have hconj_eq : ∀ r ∈ R, IsReflLin r →
      a * r * a⁻¹ = (w : V ≃ₗ[ZMod 3] V) * r * (w : V ≃ₗ[ZMod 3] V)⁻¹ := by
    intro r hrR hrrefl
    let Rr : R := ⟨r, hrR⟩
    have hRrG : GGLinRefl r := (ggLinRefl_iff_isReflLin r).mpr hrrefl
    have htr : e Rr ∈ ggTransp N := by
      obtain ⟨i, j, hij, heq⟩ := he Rr hRrG
      exact ⟨i, j, hij, heq⟩
    have hgtr : π (e Rr) = g * e Rr * g⁻¹ := hg (e Rr) htr
    rw [hπe Rr] at hgtr
    have hw_eq : conjA Rr = w * Rr * w⁻¹ := by
      apply e.injective
      rw [hgtr]
      simp only [map_mul, map_inv]
      rw [show e w = g from MulEquiv.apply_symm_apply e g]
    have hcoe := congrArg (fun x : R => (x : V ≃ₗ[ZMod 3] V)) hw_eq
    simpa [conjA, Rr, w, Subgroup.coe_mul, Subgroup.coe_inv] using hcoe
  let S : V ≃ₗ[ZMod 3] V := ((w : V ≃ₗ[ZMod 3] V))⁻¹ * a
  have hS_refl : ∀ r ∈ R, IsReflLin r → S * r = r * S := by
    intro r hr hrrefl
    have h := hconj_eq r hr hrrefl
    calc S * r = ((w : V ≃ₗ[ZMod 3] V))⁻¹ * (a * r * a⁻¹) * a := by
          simp only [S]
          group
      _ = ((w : V ≃ₗ[ZMod 3] V))⁻¹ *
            ((w : V ≃ₗ[ZMod 3] V) * r * ((w : V ≃ₗ[ZMod 3] V))⁻¹) * a := by rw [h]
      _ = r * S := by
          simp only [S]
          group
  have hS_comm : ∀ r ∈ R, S * r = r * S := by
    intro r hr
    have hG : e ⟨r, hr⟩ ∈ Subgroup.closure {σ : Equiv.Perm (Fin N) | σ.IsSwap} := by
      rw [Equiv.Perm.closure_isSwap]
      exact Subgroup.mem_top _
    have hcomm : S * ((e.symm (e ⟨r, hr⟩) : R) : V ≃ₗ[ZMod 3] V) =
        ((e.symm (e ⟨r, hr⟩) : R) : V ≃ₗ[ZMod 3] V) * S :=
      Subgroup.closure_induction
        (p := fun σ (_ : σ ∈ Subgroup.closure {τ : Equiv.Perm (Fin N) | τ.IsSwap}) =>
          S * ((e.symm σ : R) : V ≃ₗ[ZMod 3] V) =
            ((e.symm σ : R) : V ≃ₗ[ZMod 3] V) * S)
        (fun σ hσ => by
          obtain ⟨i, j, hij, rfl⟩ := hσ
          exact hS_refl _ (e.symm (Equiv.swap i j)).2
            (hsym_refl (Equiv.swap i j) ⟨i, j, hij, rfl⟩))
        (by simp)
        (fun x y _ _ ihx ihy => by
          rw [map_mul, Subgroup.coe_mul]
          calc S * ((e.symm x : R) * (e.symm y : R) : V ≃ₗ[ZMod 3] V)
              = (S * (e.symm x : R)) * (e.symm y : R) := by group
            _ = ((e.symm x : R) * S) * (e.symm y : R) := by rw [ihx]
            _ = (e.symm x : R) * (S * (e.symm y : R)) := by group
            _ = (e.symm x : R) * ((e.symm y : R) * S) := by rw [ihy]
            _ = ((e.symm x : R) * (e.symm y : R)) * S := by group)
        (fun x _ ihx => by
          rw [map_inv, Subgroup.coe_inv]
          calc S * ((e.symm x : R) : V ≃ₗ[ZMod 3] V)⁻¹
              = ((e.symm x : R) : V ≃ₗ[ZMod 3] V)⁻¹ *
                  (((e.symm x : R) : V ≃ₗ[ZMod 3] V) * S) *
                  ((e.symm x : R) : V ≃ₗ[ZMod 3] V)⁻¹ := by group
            _ = ((e.symm x : R) : V ≃ₗ[ZMod 3] V)⁻¹ *
                  (S * ((e.symm x : R) : V ≃ₗ[ZMod 3] V)) *
                  ((e.symm x : R) : V ≃ₗ[ZMod 3] V)⁻¹ := by rw [ihx]
            _ = ((e.symm x : R) : V ≃ₗ[ZMod 3] V)⁻¹ * S := by group)
        hG
    simpa using hcomm
  rcases ggWAut_schur_pm R habs S hS_comm with h1 | h1
  · refine ⟨(w : V ≃ₗ[ZMod 3] V), w.2, Or.inl ?_⟩
    intro v
    have hwS : a = (w : V ≃ₗ[ZMod 3] V) * S := by
      simp only [S]
      group
    calc a v = ((w : V ≃ₗ[ZMod 3] V) * S) v := by rw [hwS]
      _ = (w : V ≃ₗ[ZMod 3] V) (S v) := by rw [LinearEquiv.mul_apply]
      _ = (w : V ≃ₗ[ZMod 3] V) v := by rw [h1 v]
  · refine ⟨(w : V ≃ₗ[ZMod 3] V), w.2, Or.inr ?_⟩
    intro v
    have hwS : a = (w : V ≃ₗ[ZMod 3] V) * S := by
      simp only [S]
      group
    calc a v = ((w : V ≃ₗ[ZMod 3] V) * S) v := by rw [hwS]
      _ = (w : V ≃ₗ[ZMod 3] V) (S v) := by rw [LinearEquiv.mul_apply]
      _ = (w : V ≃ₗ[ZMod 3] V) (-v) := by rw [h1 v]
      _ = -((w : V ≃ₗ[ZMod 3] V) v) := by simp

theorem ggHA_mod {H : Type} [AddCommGroup H] [Module (ZMod 3) H] {r : ℕ} (hr : 4 ≤ r)
    (h : Fin r → H) (α : Fin r → Module.Dual (ZMod 3) H)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A r i j : ℤ) : ZMod 3))
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hker : ∀ v : H, (∀ i, α i v = 0) → v = 0) (T : H ≃ₗ[ZMod 3] H)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (H ≃ₗ[ZMod 3] H))) :
    ∃ w ∈ ggQ2WeylOf h α, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v : H, T v = ε • w v := by
  classical
  have hfin : Module.Finite (ZMod 3) H := by
    have hFG : (Submodule.span (ZMod 3) (Set.range h)).FG :=
      Submodule.fg_span (Set.finite_range h)
    rw [hspan] at hFG
    have htop : Module.Finite (ZMod 3) ↥(⊤ : Submodule (ZMod 3) H) :=
      Module.Finite.iff_fg.mpr hFG
    exact Module.Finite.equiv (Submodule.topEquiv (R := ZMod 3) (M := H))
  have hα2 : ∀ i, α i (h i) = 2 := by
    intro i
    rw [hα i i, ggHAM_A_self r i]
    norm_num
  obtain ⟨Ψ, hΨinj, hΨswap, hΨrefl⟩ := ggHA_perm hr h α hα
  let W : Subgroup (H ≃ₗ[ZMod 3] H) := ggQ2WeylOf h α
  let s : Fin r → (H ≃ₗ[ZMod 3] H) := ggHAM_refl hα2
  have hs_apply : ∀ i v, s i v = v - α i v • h i := by
    intro i v
    change ggHAM_refl hα2 i v = v - α i v • h i
    exact ggHAM_refl_apply hα2 i v
  have hrange_s : Set.range s = {t : H ≃ₗ[ZMod 3] H | ∃ j, ∀ v, t v = v - α j v • h j} := by
    ext t
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, fun v => hs_apply j v⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, LinearEquiv.ext fun v => by rw [hj v, hs_apply j v]⟩
  have hWclosure : W = Subgroup.closure (Set.range s) := by
    change ggQ2WeylOf h α = Subgroup.closure (Set.range s)
    rw [ggQ2WeylOf, hrange_s]
  let τ : Fin r → Equiv.Perm (Fin (r + 1)) := fun i => Equiv.swap i.castSucc i.succ
  have hΦ : ∀ i, s i = Ψ (τ i) := by
    intro i
    ext v
    change s i v = Ψ (Equiv.swap i.castSucc i.succ) v
    rw [hs_apply i v, hΨswap i v]
  have hrange_Ψ : Set.range s = Ψ '' Set.range τ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨τ i, ⟨i, rfl⟩, (hΦ i).symm⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, hΦ i⟩
  have hclosure_τ : Subgroup.closure (Set.range τ) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ r)
  have hWrange : W = Ψ.range := by
    rw [hWclosure, hrange_Ψ, ← MonoidHom.map_closure Ψ, hclosure_τ, Subgroup.map_top]
  have hconn : ∀ i j : Fin r, Relation.ReflTransGen
      (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j := by
    refine ggHAM_rtg_adj hr _ (fun a b hab => ⟨hab.2, hab.1⟩) ?_
    intro i hi
    constructor
    · have hne : i ≠ (⟨i.val + 1, hi⟩ : Fin r) := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only at hv
        omega
      rw [hα i ⟨i.val + 1, hi⟩, ggHAM_A_offdiag r hne (Or.inl rfl)]
      norm_num
    · have hne : (⟨i.val + 1, hi⟩ : Fin r) ≠ i := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only at hv
        omega
      rw [hα ⟨i.val + 1, hi⟩ i, ggHAM_A_offdiag r hne (Or.inr rfl)]
      norm_num
  have habsW : ZS.AbsIrred 3 W := by
    refine ggRC_absIrred_of_connected (p := 3) (by norm_num) s h α
      (fun i v => hs_apply i v) hα2 hspan hker hconn W ?_
    exact hWclosure
  have habs : ZS.AbsIrred 3 Ψ.range := by
    rw [← hWrange]
    exact habsW
  let Φ : Equiv.Perm (Fin (r + 1)) ≃* Ψ.range := MonoidHom.ofInjective (f := Ψ) hΨinj
  let e : Ψ.range ≃* Equiv.Perm (Fin (r + 1)) := Φ.symm
  have he : ∀ r : Ψ.range, GGLinRefl (r : H ≃ₗ[ZMod 3] H) →
      ∃ i j, i ≠ j ∧ e r = Equiv.swap i j := by
    intro r hr
    have hrrange : (r : H ≃ₗ[ZMod 3] H) ∈ Ψ.range := r.2
    obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hrrange
    have hGr : GGLinRefl (Ψ σ) := by rw [hσ]; exact hr
    obtain ⟨i, j, hij, hswap⟩ := hΨrefl σ hGr
    refine ⟨i, j, hij, ?_⟩
    have hΦσ : Φ σ = r := Subtype.ext hσ
    have her : e r = σ := by
      change Φ.symm r = σ
      rw [← hΦσ, MulEquiv.symm_apply_apply]
    rw [her, hswap]
  let i₀ : Fin r := ⟨0, by omega⟩
  let t₀ : H ≃ₗ[ZMod 3] H := Ψ (τ i₀)
  have ht₀R : t₀ ∈ Ψ.range := ⟨τ i₀, rfl⟩
  have ht₀ : IsReflLin t₀ := ⟨h i₀, α i₀, hα2 i₀, (hΦ i₀).symm⟩
  have hTnorm : T ∈ Subgroup.normalizer (Ψ.range : Set (H ≃ₗ[ZMod 3] H)) := by
    rw [← hWrange]
    exact hT
  obtain ⟨w, hw, hpm⟩ :=
    ggWAut_sym_norm' (N := r + 1) (by omega) Ψ.range habs e he (t₀ := t₀) ht₀R ht₀
      (a := T) hTnorm
  have hwW : w ∈ W := by
    rw [hWrange]
    exact hw
  rcases hpm with hpm | hpm
  · exact ⟨w, hwW, 1, Or.inl rfl, fun v => by rw [hpm v, one_smul]⟩
  · exact ⟨w, hwW, -1, Or.inr rfl, fun v => by rw [hpm v, neg_one_smul]⟩

end CFSG.StandardType

end
