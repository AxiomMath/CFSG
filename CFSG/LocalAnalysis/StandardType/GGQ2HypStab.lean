module

public import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentreLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V ι : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem ggQ2Hyp_sup_span_eq_top [Module.Finite (ZMod 3) V] (H : Submodule (ZMod 3) V)
    (hhyp : Module.finrank (ZMod 3) H + 1 = Module.finrank (ZMod 3) V) {v₀ : V}
    (hv₀ : v₀ ∉ H) : H ⊔ Submodule.span (ZMod 3) {v₀} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [Submodule.finrank_sup_span_singleton hv₀, hhyp]

private theorem ggQ2Hyp_decomp [Module.Finite (ZMod 3) V] {H : Submodule (ZMod 3) V}
    (hhyp : Module.finrank (ZMod 3) H + 1 = Module.finrank (ZMod 3) V) {v₀ : V}
    (hv₀ : v₀ ∉ H) (v : V) : ∃ h ∈ H, ∃ μ : ZMod 3, v = h + μ • v₀ := by
  have hsup : H ⊔ Submodule.span (ZMod 3) {v₀} = ⊤ := ggQ2Hyp_sup_span_eq_top H hhyp hv₀
  have hv : v ∈ H ⊔ Submodule.span (ZMod 3) {v₀} := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨h, hh, w, hw, hvw⟩ := Submodule.mem_sup.mp hv
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hw
  exact ⟨h, hh, μ, by rw [← hvw, hμ]⟩

private theorem ggQ2Hyp_proj [Module.Finite (ZMod 3) V] (H : Submodule (ZMod 3) V)
    (hhyp : Module.finrank (ZMod 3) H + 1 = Module.finrank (ZMod 3) V) {v₀ : V}
    (hv₀ : v₀ ∉ H) :
    ∃ f : Module.Dual (ZMod 3) V, f v₀ = 1 ∧ (∀ h ∈ H, f h = 0) ∧
      ∀ v, v - f v • v₀ ∈ H := by
  obtain ⟨f, hfv, hfH⟩ := Submodule.exists_le_ker_of_notMem hv₀
  refine ⟨(f v₀)⁻¹ • f, ?_, ?_, ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfv]
  · intro h hh
    rw [LinearMap.smul_apply, LinearMap.mem_ker.mp (hfH hh), smul_zero]
  · intro v
    obtain ⟨h, hh, μ, hv⟩ := ggQ2Hyp_decomp hhyp hv₀ v
    have hfh : ((f v₀)⁻¹ • f) h = 0 := by
      rw [LinearMap.smul_apply, LinearMap.mem_ker.mp (hfH hh), smul_zero]
    have hfv' : ((f v₀)⁻¹ • f) v₀ = 1 := by
      rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfv]
    have hμ : ((f v₀)⁻¹ • f) v = μ := by
      rw [hv, map_add, map_smul, hfh, hfv']
      simp
    have hsub : h + μ • v₀ - μ • v₀ = h := add_sub_cancel_right _ _
    rw [hμ, hv, hsub]
    exact hh

private theorem ggQ2Hyp_two_smul (x : V) : (2 : ZMod 3) • x = -x := by
  rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul]

private theorem ggQ2Hyp_exists_notMem [Module.Finite (ZMod 3) V] {H : Submodule (ZMod 3) V}
    (hhyp : Module.finrank (ZMod 3) H + 1 = Module.finrank (ZMod 3) V) : ∃ v, v ∉ H := by
  have hHne : H ≠ ⊤ := by
    intro htop
    have hfr : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V := by
      rw [htop]
      exact finrank_top _ _
    omega
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hHne)
  exact ⟨v, hv⟩

theorem ggQ2Hyp_eq_one [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (H : Submodule (ZMod 3) V)
    (hhyp : Module.finrank (ZMod 3) H + 1 = Module.finrank (ZMod 3) V)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ A) (hH : ∀ h ∈ H, g h = h) (hV : ∀ v, g v - v ∈ H) :
    ∀ v, g v = v := by
  classical
  have hHne : H ≠ ⊤ := by
    intro htop
    have hfr : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V := by
      rw [htop]
      exact finrank_top _ _
    omega
  obtain ⟨v₀, -, hv₀⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hHne)
  obtain ⟨f, hfv₀, hfH, hfv⟩ := ggQ2Hyp_proj H hhyp hv₀
  have huH : g v₀ - v₀ ∈ H := hV v₀
  have hform : ∀ v, g v = v + f v • (g v₀ - v₀) := by
    intro v
    have hv : v = (v - f v • v₀) + f v • v₀ := by abel
    calc
      g v = g ((v - f v • v₀) + f v • v₀) := congrArg g hv
      _ = g (v - f v • v₀) + f v • g v₀ := by rw [map_add, map_smul]
      _ = (v - f v • v₀) + f v • g v₀ := by rw [hH _ (hfv v)]
      _ = v + f v • (g v₀ - v₀) := by rw [smul_sub]; abel
  by_cases hu0 : g v₀ - v₀ = 0
  · intro v
    rw [hform v, hu0, smul_zero, add_zero]
  · exact absurd ⟨g v₀ - v₀, f, hu0,
      (fun hf0 => by rw [hf0] at hfv₀; exact zero_ne_one hfv₀),
      hfH _ huH, fun v => hform v⟩ (hTF g hg)

theorem ggQ2Hyp_A_stab [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c)) :
    ∀ a ∈ A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      a h ∈ Submodule.span (ZMod 3) (Set.range c) := by
  classical
  set H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c) with hH
  intro a ha h hh
  let U : Submodule (ZMod 3) V := H.map (a : V →ₗ[ZMod 3] V)
  have hU : ∀ i, ∀ u ∈ U, α i u • c i ∈ U := by
    intro i u hu
    have hsu : s i u ∈ U := by
      obtain ⟨z, hz, hzu⟩ := Submodule.mem_map.mp hu
      refine Submodule.mem_map.mpr ⟨(a⁻¹ * s i * a) z, ?_, ?_⟩
      · exact hRH (a⁻¹ * s i * a) (ggWAut_reflGp_conj A (A.inv_mem ha) (hsR i)) z hz
      · rw [← hzu]
        simp [mul_assoc]
    have hsub : α i u • c i = u - s i u := by rw [hs i u]; abel
    rw [hsub]
    exact U.sub_mem hu hsu
  have hUfin : Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) H :=
    LinearEquiv.finrank_map_eq a H
  rcases ggQ2Mix_stable_dichotomy c α x hfix hconn U hU with hHU | hUx
  · have hUH : H = U := Submodule.eq_of_le_of_finrank_eq hHU hUfin.symm
    have hmemU : a h ∈ U := Submodule.mem_map.mpr ⟨h, hh, rfl⟩
    rw [← hUH] at hmemU
    exact hmemU
  · have hUle : Module.finrank (ZMod 3) U ≤ 1 := by
      have h1 : Module.finrank (ZMod 3) U ≤
          Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {x}) :=
        Submodule.finrank_mono hUx
      have hxle : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {x}) ≤ 1 := by
        simpa using finrank_span_le_card (R := ZMod 3) ({x} : Set V)
      omega
    have h2U : 2 ≤ Module.finrank (ZMod 3) U := by rw [hUfin]; exact h2
    omega

theorem ggQ2Hyp_no_refl_ker
    [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ t ∈ A, IsReflLin t → ¬ ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), t h = h := by
  classical
  set H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c) with hH
  intro t htA htRefl htH
  obtain ⟨c₀, φ, hφ, ht⟩ := htRefl
  have htv : ∀ v, t v = v - φ v • c₀ := by
    intro v
    rw [ht, Module.reflection_apply]
  have htwo : (2 : ZMod 3) ≠ 0 := by decide
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφ
    exact htwo hφ.symm
  have hφH : ∀ h ∈ H, φ h = 0 := by
    intro h hh
    have h1 := htH h hh
    rw [htv h] at h1
    have h2' : φ h • c₀ = 0 := sub_eq_self.mp h1
    exact (smul_eq_zero.mp h2').resolve_right hc₀
  have hc₀H : c₀ ∉ H := by
    intro hc
    exact htwo (hφ.symm.trans (hφH c₀ hc))
  have htform : ∀ h ∈ H, ∀ μ : ZMod 3,
      t (h + μ • c₀) = h - μ • c₀ := by
    intro h hh μ
    rw [htv, map_add, map_smul, hφH h hh, zero_add, hφ]
    have hcoef : (μ • (2 : ZMod 3)) = -μ := by
      rw [show (2 : ZMod 3) = -1 by decide, smul_eq_mul, mul_neg, mul_one]
    rw [hcoef, neg_smul]
    calc h + μ • c₀ - -(μ • c₀) = h + (μ • c₀ + μ • c₀) := by abel
      _ = h + (2 : ZMod 3) • (μ • c₀) := by rw [two_smul]
      _ = h + -(μ • c₀) := by rw [ggQ2Hyp_two_smul]
      _ = h - μ • c₀ := by abel
  have htneg : ∀ v, t v + v ∈ H := by
    intro v
    obtain ⟨h, hh, μ, hv⟩ := ggQ2Hyp_decomp (H := H) hhyp hc₀H v
    rw [hv, htform h hh μ]
    have hsum : (h - μ • c₀) + (h + μ • c₀) = -h := by
      calc (h - μ • c₀) + (h + μ • c₀) = h + h := by abel
        _ = (2 : ZMod 3) • h := (two_smul _ _).symm
        _ = -h := ggQ2Hyp_two_smul h
    rw [hsum]
    exact H.neg_mem hh
  have htinv : t⁻¹ = t := by
    rw [ht]
    exact Module.reflection_inv hφ
  have hcomm : ∀ a ∈ A, a * t = t * a := by
    intro a ha
    let t' : V ≃ₗ[ZMod 3] V := a * t * a⁻¹
    have ht'A : t' ∈ A := A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha)
    have ht'Refl : IsReflLin t' :=
      ggQ2_isReflLin_conj a t ⟨c₀, φ, hφ, ht⟩
    have ht'H : ∀ h ∈ H, t' h = h := by
      intro h hh
      have h1 : a⁻¹ h ∈ H :=
        ggQ2Hyp_A_stab A c α s hs hsR x hfix hconn h2 hRH a⁻¹ (A.inv_mem ha) h hh
      show a (t (a⁻¹ h)) = h
      rw [htH (a⁻¹ h) h1]
      simp
    have ht'neg : ∀ v, t' v + v ∈ H := by
      intro v
      have h2' : t (a⁻¹ v) + a⁻¹ v ∈ H := htneg (a⁻¹ v)
      have h3 : a (t (a⁻¹ v) + a⁻¹ v) ∈ H :=
        ggQ2Hyp_A_stab A c α s hs hsR x hfix hconn h2 hRH a ha _ h2'
      rw [map_add] at h3
      change a (t (a⁻¹ v)) + v ∈ H
      simpa using h3
    have hkA : (t)⁻¹ * t' ∈ A := A.mul_mem (A.inv_mem htA) ht'A
    have hkH : ∀ h ∈ H, ((t)⁻¹ * t') h = h := by
      intro h hh
      show (t)⁻¹ (t' h) = h
      rw [ht'H h hh, htinv, htH h hh]
    have hkV : ∀ v, ((t)⁻¹ * t') v - v ∈ H := by
      intro v
      change t⁻¹ (t' v) - v ∈ H
      have h1 : (t)⁻¹ (t' v) + t' v ∈ H := by
        rw [htinv]
        exact htneg (t' v)
      have h2' : t' v + v ∈ H := ht'neg v
      have h3 : (t)⁻¹ (t' v) - v =
          ((t)⁻¹ (t' v) + t' v) - (t' v + v) := by abel
      rw [h3]
      exact H.sub_mem h1 h2'
    have hk1 := ggQ2Hyp_eq_one A hTF H hhyp hkA hkH hkV
    have hkeq : (t)⁻¹ * t' = 1 := LinearEquiv.ext hk1
    have ht'eq : t' = t := by
      have h4 := congrArg (fun e : V ≃ₗ[ZMod 3] V => t * e) hkeq
      simpa [t', mul_assoc] using h4
    show a * t = t * a
    calc a * t
        = a * t * 1 := (mul_one _).symm
      _ = a * t * (a⁻¹ * a) := by rw [inv_mul_cancel]
      _ = (a * t * a⁻¹) * a := by group
      _ = t * a := by
        change t' * a = t * a
        rw [ht'eq]
  have htc₀ : t c₀ = -c₀ := by
    rw [htv, hφ, ggQ2Hyp_two_smul]
    calc c₀ - -c₀ = c₀ + c₀ := by abel
      _ = (2 : ZMod 3) • c₀ := (two_smul _ _).symm
      _ = -c₀ := ggQ2Hyp_two_smul c₀
  have heig : ∀ a ∈ A, a c₀ ∈ Submodule.span (ZMod 3) {c₀} := by
    intro a ha
    have hfixed : t (a c₀) = -(a c₀) := by
      have h1 : t (a c₀) = a (t c₀) := by
        have h4 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e c₀) (hcomm a ha)
        simpa using h4.symm
      rw [h1, htc₀, map_neg]
    have h2' : (2 : ZMod 3) • (a c₀) = φ (a c₀) • c₀ := by
      have h3 := htv (a c₀)
      rw [hfixed] at h3
      have h5 : (a c₀ + a c₀) - φ (a c₀) • c₀ = 0 := by
        have h6 : ((a c₀) - φ (a c₀) • c₀) + (a c₀) = 0 := by
          have h7 := congrArg (fun x => x + (a c₀)) h3.symm
          rwa [neg_add_cancel] at h7
        rwa [show (a c₀ + a c₀) - φ (a c₀) • c₀ =
          ((a c₀) - φ (a c₀) • c₀) + (a c₀) by abel]
      rw [two_smul]
      exact sub_eq_zero.mp h5
    have h22 : (2 : ZMod 3) * 2 = 1 := by decide
    have hv : a c₀ = ((2 : ZMod 3) * φ (a c₀)) • c₀ := by
      calc a c₀ = (1 : ZMod 3) • (a c₀) := (one_smul _ _).symm
        _ = ((2 : ZMod 3) * 2) • (a c₀) := by rw [h22]
        _ = (2 : ZMod 3) • ((2 : ZMod 3) • (a c₀)) := by rw [smul_smul]
        _ = (2 : ZMod 3) • (φ (a c₀) • c₀) := by rw [h2']
        _ = ((2 : ZMod 3) * φ (a c₀)) • c₀ := by rw [smul_smul]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c₀)
  have hc_ne : ∀ i, c i ≠ 0 := by
    intro i h0
    have h1 := hαc i
    rw [h0, map_zero] at h1
    exact htwo h1.symm
  have hdisj : Submodule.span (ZMod 3) {c₀} ⊓ H = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hz1
    by_contra hz0
    apply hc₀H
    have hμ0 : μ ≠ 0 := by
      intro h0
      apply hz0
      rw [← hμ, h0, zero_smul]
    have hcz : c₀ = μ⁻¹ • z := by
      rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    rw [hcz]
    exact H.smul_mem _ hz2
  have hαc₀ : ∀ i, α i c₀ = 0 := by
    intro i
    have hsiA : s i ∈ A := ggWAut_reflGp_le A (hsR i)
    have h1 : s i c₀ ∈ Submodule.span (ZMod 3) {c₀} := heig (s i) hsiA
    have hsub : c₀ - s i c₀ = α i c₀ • c i := by rw [hs i c₀]; abel
    have h2' : c₀ - s i c₀ ∈ H := by
      rw [hsub]
      exact H.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have h3 : c₀ - s i c₀ ∈ Submodule.span (ZMod 3) {c₀} :=
      Submodule.sub_mem _ (Submodule.mem_span_singleton_self c₀) h1
    have h4 : c₀ - s i c₀ = 0 := by
      have h5 : c₀ - s i c₀ ∈ Submodule.span (ZMod 3) {c₀} ⊓ H :=
        Submodule.mem_inf.mpr ⟨h3, h2'⟩
      rw [hdisj] at h5
      exact h5
    have h6 : α i c₀ • c i = 0 := by rw [← hsub]; exact h4
    exact (smul_eq_zero.mp h6).resolve_right (hc_ne i)
  have hc₀x : c₀ ∈ Submodule.span (ZMod 3) {x} := hfix c₀ hαc₀
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hc₀x
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact hc₀ hμ.symm
  have hxmem : x ∈ Submodule.span (ZMod 3) {c₀} := by
    rw [Submodule.mem_span_singleton]
    exact ⟨μ⁻¹, by rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]⟩
  have hsp : Submodule.span (ZMod 3) {c₀} = Submodule.span (ZMod 3) {x} := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem]; exact hc₀x
    · rw [Submodule.span_singleton_le_iff_mem]; exact hxmem
  have hxeq : x = μ⁻¹ • c₀ := by
    rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  apply hRx
  intro r hr
  have hrA : r ∈ A := ggWAut_reflGp_le A hr
  have h1 : r c₀ ∈ Submodule.span (ZMod 3) {c₀} := heig r hrA
  rw [hsp] at h1
  have hx1 : r x = μ⁻¹ • r c₀ := by rw [hxeq, map_smul]
  rw [hx1]
  exact Submodule.smul_mem _ _ h1

theorem ggQ2Hyp_refl_move
    [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ t ∈ A, IsReflLin t → ∀ v, t v - v ∈ Submodule.span (ZMod 3) (Set.range c) := by
  classical
  set H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c) with hH
  intro t htA htRefl v
  obtain ⟨c₀, φ, hφ, ht⟩ := htRefl
  have htv : ∀ w, t w = w - φ w • c₀ := by
    intro w
    rw [ht, Module.reflection_apply]
  by_cases hc₀H : c₀ ∈ H
  · rw [htv v]
    have hsub : v - φ v • c₀ - v = -(φ v • c₀) := by abel
    rw [hsub]
    exact H.neg_mem (H.smul_mem _ hc₀H)
  · exfalso
    apply ggQ2Hyp_no_refl_ker A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx t htA
      ⟨c₀, φ, hφ, ht⟩
    intro h hh
    have hthH : t h ∈ H :=
      ggQ2Hyp_A_stab A c α s hs hsR x hfix hconn h2 hRH t htA h hh
    have hφh : φ h = 0 := by
      have h1 : φ h • c₀ = h - t h := by
        rw [htv h]
        abel
      by_contra hne
      have hcz : c₀ ∈ H := by
        have h2' : c₀ = (φ h)⁻¹ • (φ h • c₀) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        rw [h2', h1]
        exact H.smul_mem _ (H.sub_mem hh hthH)
      exact hc₀H hcz
    rw [htv h, hφh, zero_smul, sub_zero]

theorem ggQ2Hyp_R_move
    [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ r ∈ reflGp A, ∀ v, r v - v ∈ Submodule.span (ZMod 3) (Set.range c) := by
  classical
  set H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c) with hH
  intro r hr v
  rw [reflGp] at hr
  refine Subgroup.closure_induction (p := fun x _ => ∀ w, x w - w ∈ H) ?_ ?_ ?_ ?_ hr v
  · rintro t ⟨htA, htRefl⟩ w
    exact ggQ2Hyp_refl_move A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx t htA htRefl w
  · intro w
    change w - w ∈ H
    rw [sub_self]
    exact H.zero_mem
  · intro x y hx hy ihx ihy w
    have hxy : (x * y) w - w = (x (y w) - y w) + (y w - w) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [hxy]
    exact H.add_mem (ihx (y w)) (ihy w)
  · intro x hx ih w
    have hxv : x⁻¹ w - w = -(x (x⁻¹ w) - x⁻¹ w) := by
      have hxx : x (x⁻¹ w) = w := by simp
      rw [hxx]
      abel
    rw [hxv]
    exact H.neg_mem (ih (x⁻¹ w))

theorem ggQ2Hyp_one
    [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ g ∈ A, (∀ h ∈ Submodule.span (ZMod 3) (Set.range c), g h = h) → ∀ v, g v = v := by
  classical
  set H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c) with hH
  intro g hg hfixH v
  obtain ⟨v₀, hv₀⟩ := ggQ2Hyp_exists_notMem (H := H) hhyp
  obtain ⟨f, hfv₀, hfH, hfv⟩ := ggQ2Hyp_proj H hhyp hv₀
  obtain ⟨h₀, hh₀, lam, hgv₀⟩ := ggQ2Hyp_decomp (H := H) hhyp hv₀ (g v₀)
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hgv₀' : g v₀ = h₀ := by rw [hgv₀, h0, zero_smul, add_zero]
    have hfix₀ : g h₀ = h₀ := hfixH h₀ hh₀
    have h1 : g (g v₀) = g v₀ := by rw [hgv₀', hfix₀]
    have h2' : g v₀ = v₀ := g.injective h1
    have hv₀H : v₀ ∈ H := by rw [← h2', hgv₀']; exact hh₀
    exact hv₀ hv₀H
  have hunits : lam = 1 ∨ lam = -1 :=
    (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) lam hlam0
  rcases hunits with h1 | h1
  · have hform : ∀ w, g w - w ∈ H := by
      intro w
      obtain ⟨h, hh, μ, hw⟩ := ggQ2Hyp_decomp (H := H) hhyp hv₀ w
      rw [hw, map_add, map_smul, hfixH h hh, hgv₀, h1, one_smul]
      have hsub : h + μ • (h₀ + v₀) - (h + μ • v₀) = μ • h₀ := by
        rw [smul_add]
        abel
      rw [hsub]
      exact H.smul_mem _ hh₀
    exact ggQ2Hyp_eq_one A hTF H hhyp hg hfixH hform v
  · exfalso
    let c₀ : V := v₀ + h₀
    have hc₀def : c₀ = v₀ + h₀ := rfl
    have hgc₀ : g c₀ = -c₀ := by
      rw [hc₀def, map_add, hfixH h₀ hh₀, hgv₀, h1, neg_one_smul]
      calc h₀ + -v₀ + h₀ = h₀ + h₀ - v₀ := by abel
        _ = (2 : ZMod 3) • h₀ - v₀ := by rw [two_smul]
        _ = (-1 : ZMod 3) • h₀ - v₀ := by rw [show (2 : ZMod 3) = -1 by decide]
        _ = -h₀ - v₀ := by rw [neg_one_smul]
        _ = -(v₀ + h₀) := by abel
    have hc₀H : c₀ ∉ H := by
      intro hc
      have hvc : v₀ = c₀ - h₀ := by rw [hc₀def]; abel
      exact hv₀ (by rw [hvc]; exact H.sub_mem hc hh₀)
    have hfc₀ : f c₀ = 1 := by
      rw [hc₀def, map_add, hfH h₀ hh₀, add_zero, hfv₀]
    have h2f_c₀ : ((2 : ZMod 3) • f) c₀ = 2 := by
      rw [LinearMap.smul_apply, hfc₀, smul_eq_mul, mul_one]
    have hfvc : ∀ w, w - f w • c₀ ∈ H := by
      intro w
      obtain ⟨h, hh, μ, hw⟩ := ggQ2Hyp_decomp (H := H) hhyp hc₀H w
      have hμ : f w = μ := by
        rw [hw, map_add, map_smul, hfH h hh, zero_add, hfc₀, smul_eq_mul, mul_one]
      have hsub : w - f w • c₀ = h := by
        rw [hμ, hw, add_sub_cancel_right]
      rw [hsub]
      exact hh
    have hgform : ∀ w, g w = w - ((2 : ZMod 3) • f) w • c₀ := by
      intro w
      have hw : w = (w - f w • c₀) + f w • c₀ := by abel
      have hhH : w - f w • c₀ ∈ H := hfvc w
      calc g w = g ((w - f w • c₀) + f w • c₀) := congrArg g hw
        _ = g (w - f w • c₀) + f w • g c₀ := by rw [map_add, map_smul]
        _ = (w - f w • c₀) + f w • (-c₀) := by rw [hfixH _ hhH, hgc₀]
        _ = w - ((2 : ZMod 3) • f) w • c₀ := by
          rw [LinearMap.smul_apply, smul_eq_mul, ← smul_smul, two_smul, smul_neg]
          abel
    have hrefl : IsReflLin g := by
      refine ⟨c₀, (2 : ZMod 3) • f, h2f_c₀, ?_⟩
      ext w
      rw [hgform w, Module.reflection_apply]
    exact ggQ2Hyp_no_refl_ker A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx g hg hrefl hfixH

theorem ggQ2Hyp_neg
    [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ g ∈ A, (∀ h ∈ Submodule.span (ZMod 3) (Set.range c), g h = -h) → ∀ v, g v = -v := by
  classical
  set H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c) with hH
  intro g hg hnegH v
  have hstab : ∀ a ∈ A, ∀ h ∈ H, a h ∈ H :=
    ggQ2Hyp_A_stab A c α s hs hsR x hfix hconn h2 hRH
  obtain ⟨v₀, hv₀⟩ := ggQ2Hyp_exists_notMem (H := H) hhyp
  obtain ⟨f, hfv₀, hfH, hfv⟩ := ggQ2Hyp_proj H hhyp hv₀
  obtain ⟨h₀, hh₀, lam, hgv₀⟩ := ggQ2Hyp_decomp (H := H) hhyp hv₀ (g v₀)
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hgv₀H : g v₀ ∈ H := by rw [hgv₀, h0, zero_smul, add_zero]; exact hh₀
    have hinv : g⁻¹ (g v₀) ∈ H := hstab g⁻¹ (A.inv_mem hg) (g v₀) hgv₀H
    have hgv : g⁻¹ (g v₀) = v₀ := by simp
    rw [hgv] at hinv
    exact hv₀ hinv
  have hunits : lam = -1 ∨ lam = 1 := by
    rcases (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) lam hlam0 with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hunits with h1 | h1
  · have hsqH : ∀ h ∈ H, (g * g) h = h := by
      intro h hh
      show g (g h) = h
      rw [hnegH h hh, map_neg, hnegH h hh, neg_neg]
    have hsqv₀ : (g * g) v₀ = v₀ + h₀ := by
      show g (g v₀) = v₀ + h₀
      rw [hgv₀, h1, neg_one_smul, show h₀ + -v₀ = h₀ - v₀ by abel, map_sub,
        hnegH h₀ hh₀, hgv₀, h1, neg_one_smul]
      calc -h₀ - (h₀ + -v₀) = -(h₀ + h₀) + v₀ := by abel
        _ = -((2 : ZMod 3) • h₀) + v₀ := by rw [two_smul]
        _ = (-2 : ZMod 3) • h₀ + v₀ := by rw [neg_smul]
        _ = (1 : ZMod 3) • h₀ + v₀ := by rw [show (-2 : ZMod 3) = 1 by decide]
        _ = h₀ + v₀ := by rw [one_smul]
        _ = v₀ + h₀ := by abel
    have hsqform : ∀ w, (g * g) w - w ∈ H := by
      intro w
      obtain ⟨h, hh, μ, hw⟩ := ggQ2Hyp_decomp (H := H) hhyp hv₀ w
      rw [hw, map_add, map_smul, hsqH h hh, hsqv₀]
      have hsub : h + μ • (v₀ + h₀) - (h + μ • v₀) = μ • h₀ := by
        rw [smul_add]
        abel
      rw [hsub]
      exact H.smul_mem _ hh₀
    have hsq1 : ∀ w, (g * g) w = w :=
      ggQ2Hyp_eq_one A hTF H hhyp (A.mul_mem hg hg) hsqH hsqform
    have hh₀0 : h₀ = 0 := by
      have hval := hsq1 v₀
      rw [hsqv₀] at hval
      have hval' : v₀ + h₀ = v₀ + 0 := by
        rw [add_zero]
        exact hval
      exact add_left_cancel hval'
    have hgv₀neg : g v₀ = -v₀ := by
      rw [hgv₀, h1, neg_one_smul, hh₀0, zero_add]
    obtain ⟨h, hh, μ, hv⟩ := ggQ2Hyp_decomp (H := H) hhyp hv₀ v
    rw [hv, map_add, map_smul, hnegH h hh, hgv₀neg, smul_neg]
    abel
  · exfalso
    have hcomm : ∀ a ∈ A, g * a = a * g := by
      intro a ha
      have hkA : g * a * g⁻¹ * a⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem hg ha) (A.inv_mem hg)) (A.inv_mem ha)
      have hkH : ∀ h ∈ H, (g * a * g⁻¹ * a⁻¹) h = h := by
        intro h hh
        show g (a (g⁻¹ (a⁻¹ h))) = h
        have h1' : a⁻¹ h ∈ H := hstab a⁻¹ (A.inv_mem ha) h hh
        have h2' : g⁻¹ (a⁻¹ h) = -(a⁻¹ h) := by
          have h3 : g (-(a⁻¹ h)) = a⁻¹ h := by
            rw [map_neg, hnegH (a⁻¹ h) h1', neg_neg]
          calc g⁻¹ (a⁻¹ h) = g⁻¹ (g (-(a⁻¹ h))) := by rw [h3]
            _ = -(a⁻¹ h) := by simp
        rw [h2']
        have h3 : a (-(a⁻¹ h)) = -h := by
          rw [map_neg]
          simp
        rw [h3, map_neg, hnegH h hh, neg_neg]
      have hk1 := ggQ2Hyp_one A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx
        (g * a * g⁻¹ * a⁻¹) hkA hkH
      have hkeq : g * a * g⁻¹ * a⁻¹ = 1 := LinearEquiv.ext hk1
      have h4 : g * a * g⁻¹ = a := by
        have h5 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e * a) hkeq
        simpa [mul_assoc] using h5
      calc g * a = g * a * 1 := (mul_one _).symm
        _ = g * a * (g⁻¹ * g) := by rw [inv_mul_cancel]
        _ = (g * a * g⁻¹) * g := by group
        _ = a * g := by rw [h4]
    let c₀ : V := v₀ - h₀
    have hc₀def : c₀ = v₀ - h₀ := rfl
    have hgc₀ : g c₀ = c₀ := by
      rw [hc₀def, map_sub, hnegH h₀ hh₀, hgv₀, h1, one_smul]
      calc h₀ + v₀ - -h₀ = v₀ + (h₀ + h₀) := by abel
        _ = v₀ + (2 : ZMod 3) • h₀ := by rw [two_smul]
        _ = v₀ + (-1 : ZMod 3) • h₀ := by rw [show (2 : ZMod 3) = -1 by decide]
        _ = v₀ + -h₀ := by rw [neg_one_smul]
        _ = v₀ - h₀ := by abel
    have hc₀ : c₀ ≠ 0 := by
      intro h0
      have hvc : v₀ = h₀ := sub_eq_zero.mp (hc₀def.symm.trans h0)
      exact hv₀ (by rw [hvc]; exact hh₀)
    have hc₀H : c₀ ∉ H := by
      intro hc
      have hvc : v₀ = c₀ + h₀ := by rw [hc₀def]; abel
      exact hv₀ (by rw [hvc]; exact H.add_mem hc hh₀)
    have hfc₀ : f c₀ = 1 := by
      rw [hc₀def, map_sub, hfH h₀ hh₀, sub_zero, hfv₀]
    have hfixed : ∀ w, g w = w → w ∈ Submodule.span (ZMod 3) {c₀} := by
      intro w hw
      have hw' : w = (w - f w • c₀) + f w • c₀ := by abel
      have hhH : w - f w • c₀ ∈ H := by
        obtain ⟨h, hh, μ, hww⟩ := ggQ2Hyp_decomp (H := H) hhyp hc₀H w
        have hμ : f w = μ := by
          rw [hww, map_add, map_smul, hfH h hh, zero_add, hfc₀, smul_eq_mul, mul_one]
        have hsub : w - f w • c₀ = h := by
          rw [hμ, hww, add_sub_cancel_right]
        rw [hsub]
        exact hh
      have h1' : g w = -(w - f w • c₀) + f w • c₀ := by
        calc g w = g ((w - f w • c₀) + f w • c₀) := congrArg g hw'
          _ = g (w - f w • c₀) + f w • g c₀ := by rw [map_add, map_smul]
          _ = -(w - f w • c₀) + f w • c₀ := by rw [hnegH _ hhH, hgc₀]
      have h2' : -(w - f w • c₀) = w - f w • c₀ := by
        have h3 : (-(w - f w • c₀) + f w • c₀) = (w - f w • c₀) + f w • c₀ := by
          rw [← h1', ← hw']
          exact hw
        exact add_right_cancel h3
      have h3 : (2 : ZMod 3) • (w - f w • c₀) = 0 := by
        have h4 := congrArg (fun y => y + (w - f w • c₀)) h2'
        rw [neg_add_cancel] at h4
        rw [two_smul]
        exact h4.symm
      have h4 : w - f w • c₀ = 0 :=
        (smul_eq_zero.mp h3).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
      have h5 : w = f w • c₀ := by
        calc w = (w - f w • c₀) + f w • c₀ := hw'
          _ = 0 + f w • c₀ := by rw [h4]
          _ = f w • c₀ := zero_add _
      rw [h5]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c₀)
    have hline : ∀ a ∈ A, a c₀ ∈ Submodule.span (ZMod 3) {c₀} := by
      intro a ha
      apply hfixed
      have h4 : g (a c₀) = a (g c₀) := by
        have h5 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e c₀) (hcomm a ha)
        simpa using h5
      rw [h4, hgc₀]
    have hc_ne : ∀ i, c i ≠ 0 := by
      intro i h0
      have h1' := hαc i
      rw [h0, map_zero] at h1'
      exact (by decide : (2 : ZMod 3) ≠ 0) h1'.symm
    have hdisj : Submodule.span (ZMod 3) {c₀} ⊓ H = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro z hz
      obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hz1
      by_contra hz0
      apply hc₀H
      have hμ0 : μ ≠ 0 := by
        intro h0
        apply hz0
        rw [← hμ, h0, zero_smul]
      have hcz : c₀ = μ⁻¹ • z := by
        rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      rw [hcz]
      exact H.smul_mem _ hz2
    have hαc₀ : ∀ i, α i c₀ = 0 := by
      intro i
      have hsiA : s i ∈ A := ggWAut_reflGp_le A (hsR i)
      have h1' : s i c₀ ∈ Submodule.span (ZMod 3) {c₀} := hline (s i) hsiA
      have hsub : c₀ - s i c₀ = α i c₀ • c i := by rw [hs i c₀]; abel
      have h2' : c₀ - s i c₀ ∈ H := by
        rw [hsub]
        exact H.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
      have h3 : c₀ - s i c₀ ∈ Submodule.span (ZMod 3) {c₀} :=
        Submodule.sub_mem _ (Submodule.mem_span_singleton_self c₀) h1'
      have h4 : c₀ - s i c₀ = 0 := by
        have h5 : c₀ - s i c₀ ∈ Submodule.span (ZMod 3) {c₀} ⊓ H :=
          Submodule.mem_inf.mpr ⟨h3, h2'⟩
        rw [hdisj] at h5
        exact h5
      have h6 : α i c₀ • c i = 0 := by rw [← hsub]; exact h4
      exact (smul_eq_zero.mp h6).resolve_right (hc_ne i)
    have hc₀x : c₀ ∈ Submodule.span (ZMod 3) {x} := hfix c₀ hαc₀
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hc₀x
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hμ
      exact hc₀ hμ.symm
    have hxmem : x ∈ Submodule.span (ZMod 3) {c₀} := by
      rw [Submodule.mem_span_singleton]
      exact ⟨μ⁻¹, by rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]⟩
    have hsp : Submodule.span (ZMod 3) {c₀} = Submodule.span (ZMod 3) {x} := by
      apply le_antisymm
      · rw [Submodule.span_singleton_le_iff_mem]; exact hc₀x
      · rw [Submodule.span_singleton_le_iff_mem]; exact hxmem
    have hxeq : x = μ⁻¹ • c₀ := by
      rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    apply hRx
    intro r hr
    have hrA : r ∈ A := ggWAut_reflGp_le A hr
    have h1' : r c₀ ∈ Submodule.span (ZMod 3) {c₀} := hline r hrA
    rw [hsp] at h1'
    have hx1 : r x = μ⁻¹ • r c₀ := by rw [hxeq, map_smul]
    rw [hx1]
    exact Submodule.smul_mem _ _ h1'

theorem ggQ2Hyp_R_not_neg
    [Module.Finite (ZMod 3) V] (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (hhyp : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
      Module.finrank (ZMod 3) V)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c))
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ r ∈ reflGp A, ¬ ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), r h = -h := by
  classical
  set H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c) with hH
  intro r hr hneg
  have hrA : r ∈ A := ggWAut_reflGp_le A hr
  have hnegall : ∀ v, r v = -v :=
    ggQ2Hyp_neg A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx r hrA hneg
  have hmove : ∀ v, r v - v ∈ H :=
    ggQ2Hyp_R_move A hTF c α hαc s hs hsR x hfix hconn h2 hhyp hRH hRx r hr
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have h1 := hmove w
    rw [hnegall w] at h1
    have h2' : -w - w = w := by
      calc -w - w = -(w + w) := by abel
        _ = -((2 : ZMod 3) • w) := by rw [two_smul]
        _ = (-2 : ZMod 3) • w := by rw [neg_smul]
        _ = (1 : ZMod 3) • w := by rw [show (-2 : ZMod 3) = 1 by decide]
        _ = w := one_smul _ _
    rwa [h2'] at h1
  have hfr : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V := by
    rw [htop]
    exact finrank_top _ _
  omega

end CFSG.StandardType

end
