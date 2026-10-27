module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmCore
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFrame

public section

namespace CFSG.StandardType

namespace RootPlaneD4

open Module QuadraticMap Multiplicative NoOffOm SUTB CFSG.ClassicalGroups.Orthogonal

section Quad

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_quad_ne_zero {W : Submodule K V} (hW : NondegOn (polarBilin Q) W) (hne : W ≠ ⊥) :
    ∃ u ∈ W, Q u ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine hu0 (hW u hu fun n hn => ?_)
  rw [polarBilin_apply_apply, polar, h _ (W.add_mem hn hu), h n hn, h u hu]
  ring

theorem commute_eichler {h : V ≃ₗ[K] V} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {w₁ w₂ : V} (hw₁ : Q w₁ = 0) (hw₂ : Q w₂ = 0) (hw : polar Q w₁ w₂ = 0) {α β γ δ : K}
    (h₁ : h w₁ = α • w₁ + β • w₂) (h₂ : h w₂ = γ • w₁ + δ • w₂) (hdet : α * δ - β * γ = 1)
    (c : K) : h * eichler Q w₂ (c • w₁) = eichler Q w₂ (c • w₁) * h := by
  have hw' : polar Q w₂ w₁ = 0 := by rw [polar_comm]; exact hw
  have hQ : ∀ x y : K, Q (x • w₁ + y • w₂) = 0 := fun x y => by
    rw [OrdPNsOm.quad_smul_add_smul, hw₁, hw₂, hw]
    ring
  have hu : Q (γ • w₁ + δ • w₂) = 0 := hQ γ δ
  have hpu : polar Q (γ • w₁ + δ • w₂) (c • (α • w₁ + β • w₂)) = 0 := by
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
      hw, hw', polar_self_eq_zero hw₁, polar_self_eq_zero hw₂]
    ring
  have hpw : polar Q w₂ (c • w₁) = 0 := by rw [polar_smul_right, hw', smul_zero]
  have hQw : Q (c • (α • w₁ + β • w₂)) = 0 := by
    rw [QuadraticMap.map_smul, hQ α β, smul_zero]
  have hQcw : Q (c • w₁) = 0 := by rw [QuadraticMap.map_smul, hw₁, smul_zero]
  have hE : h * eichler Q w₂ (c • w₁) * h⁻¹ = eichler Q w₂ (c • w₁) := by
    rw [eichler_conj hh, map_smul, h₁, h₂]
    refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply hu hpu, eichler_apply hw₂ hpw, hQw, hQcw]
    simp only [polar_add_right, polar_smul_right, smul_eq_mul, zero_mul, add_zero]
    linear_combination (norm := module) (c * polar Q x w₂) • hdet • w₁ -
      (c * polar Q x w₁) • hdet • w₂
  calc h * eichler Q w₂ (c • w₁) = h * eichler Q w₂ (c • w₁) * h⁻¹ * h := by group
    _ = eichler Q w₂ (c • w₁) * h := by rw [hE]

end Quad

section Witt

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [Finite V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_pair_of_charSum {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Uk Ul : Submodule K V}
    (hk : NondegOn (polarBilin Q) Uk) (hl : NondegOn (polarBilin Q) Ul)
    (hdk : finrank K Uk = 2) (hdl : finrank K Ul = 2)
    (horth : ∀ u ∈ Uk, ∀ v ∈ Ul, polar Q u v = 0)
    (hSk : OrdPNsOm.charSum Q Uk ≡ 1 [ZMOD p]) (hSl : OrdPNsOm.charSum Q Ul ≡ 1 [ZMOD p]) :
    ∃ ak ∈ Uk, ∃ bk ∈ Uk, ∃ al ∈ Ul, ∃ bl ∈ Ul, Q (ak + al) = 0 ∧ Q (bk + bl) = 0 ∧
      polar Q (ak + al) (bk + bl) = 0 ∧ LinearIndependent K ![ak + al, bk + bl] := by
  obtain ⟨c₀, hc₀⟩ := OrdPNsOm.exists_not_mem_range_wp (K := K)
  obtain ⟨τk, ak, bk, hak, hbk, hFk, hSk'⟩ := OrdPNsOm.exists_frame_plane hc₀ hk hdk
  obtain ⟨τl, al, bl, hal, hbl, hFl, hSl'⟩ := OrdPNsOm.exists_frame_plane hc₀ hl hdl
  have hτ : τk = τl := OrdPNsOm.tau_eq_of_modEq (K := K) hp hp2 (m := 0)
    (by rw [pow_zero, one_mul, ← hSk']; exact hSk) (by rw [pow_zero, one_mul, ← hSl']; exact hSl)
  subst hτ
  have hkl : ∀ {x y : V}, x ∈ Uk → y ∈ Ul → polar Q y x = 0 := fun hx hy => by
    rw [polar_comm]
    exact horth _ hx _ hy
  refine ⟨ak, hak, bk, hbk, al, hal, bl, hbl, ?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, hFk.qa, hFl.qa, horth ak hak al hal, add_zero,
      CharTwo.add_self_eq_zero]
  · rw [QuadraticMap.map_add Q, hFk.qb, hFl.qb, horth bk hbk bl hbl, add_zero,
      CharTwo.add_self_eq_zero]
  · rw [polar_add_left, polar_add_right, polar_add_right, hFk.pab, hFl.pab,
      horth ak hak bl hbl, hkl hbk hal, add_zero, zero_add, CharTwo.add_self_eq_zero]
  · rw [LinearIndependent.pair_iff]
    intro x y hxy
    have h1 := congrArg (fun w => polar Q w bk) hxy
    have h2 := congrArg (fun w => polar Q w ak) hxy
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left] at h1 h2
    rw [hFk.pab, hkl hbk hal, OrdPNsOm.polar_self_charTwo, hkl hbk hbl] at h1
    rw [OrdPNsOm.polar_self_charTwo, hkl hak hal, polar_comm Q bk ak, hFk.pab,
      hkl hak hbl] at h2
    constructor
    · simpa using h1
    · simpa using h2

end Witt

section Frame

variable {K : Type} [Field K] {d : ℕ}

structure Frame4 (Q : QuadraticForm K (Fin d → K)) (p : ℕ)
    (ι₀ : Multiplicative (Fin 4 → ZMod p) →* GL (Fin d) K)
    (U : Fin 4 → Submodule K (Fin d → K)) : Prop where
  nd : ∀ i, NondegOn (polB Q) (U i)
  ne : ∀ i, U i ≠ ⊥
  orth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0
  fix : ∀ (s : Multiplicative (Fin 4 → ZMod p)) (v : Fin d → K),
    glin (ι₀ s) v = v ↔ ∀ j, toAdd s j ≠ 0 → v ∈ (U j).orthogonalBilin (polB Q)
  inv : ∀ s i, ∀ u ∈ U i, glin (ι₀ s) u ∈ U i
  iso : ∀ s v, Q (glin (ι₀ s) v) = Q v
  dim : ∀ i, finrank K (U i) = 2
  span : ∀ v : Fin d → K, ∃ x : Fin 4 → Fin d → K, (∀ i, x i ∈ U i) ∧ v = ∑ i, x i

variable {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {ι₀ : Multiplicative (Fin 4 → ZMod p) →* GL (Fin d) K} {U : Fin 4 → Submodule K (Fin d → K)}

theorem glin_apply_inv (g : GL (Fin d) K) (v : Fin d → K) : glin g (glin g⁻¹ v) = v := by
  have h := glin_inv_apply g⁻¹ v
  rwa [inv_inv] at h

theorem glin_pow_eq_one (ι₀ : Multiplicative (Fin 4 → ZMod p) →* GL (Fin d) K)
    (s : Multiplicative (Fin 4 → ZMod p)) : glin (ι₀ s) ^ p = 1 := by
  have h : s ^ p = 1 := by
    apply toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← glin_pow, ← map_pow, h, map_one, glin_one]

namespace Frame4

variable (hF : Frame4 Q p ι₀ U)
include hF

theorem apply_eq_self {s : Multiplicative (Fin 4 → ZMod p)} {k : Fin 4} (hs : toAdd s k = 0)
    {v : Fin d → K} (hv : v ∈ U k) : glin (ι₀ s) v = v := by
  refine (hF.fix s v).mpr fun j hj => ?_
  have hjk : j ≠ k := fun h => hj (by rw [h]; exact hs)
  exact Submodule.mem_orthogonalBilin.mpr fun m hm => hF.orth j k hjk m hm v hv

theorem eq_zero_of_apply_eq_self {s : Multiplicative (Fin 4 → ZMod p)} {k : Fin 4}
    (hs : toAdd s k ≠ 0) {v : Fin d → K} (hv : v ∈ U k) (hfv : glin (ι₀ s) v = v) : v = 0 :=
  hF.nd k v hv fun n hn => Submodule.mem_orthogonalBilin.mp ((hF.fix s v).mp hfv k hs) n hn

theorem apply_eq_of_eq {s s' : Multiplicative (Fin 4 → ZMod p)} {k : Fin 4}
    (hss' : toAdd s k = toAdd s' k) {v : Fin d → K} (hv : v ∈ U k) :
    glin (ι₀ s) v = glin (ι₀ s') v := by
  have h2 : toAdd (s'⁻¹ * s) k = 0 := by
    rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, hss', neg_add_cancel]
  calc glin (ι₀ s) v = glin (ι₀ (s' * (s'⁻¹ * s))) v := by rw [mul_inv_cancel_left]
    _ = glin (ι₀ s') v := by
      rw [map_mul, glin_mul, Module.End.mul_apply, hF.apply_eq_self h2 hv]

theorem polar_sum {x : Fin 4 → Fin d → K} (hx : ∀ i, x i ∈ U i) {l : Fin 4} {n : Fin d → K}
    (hn : n ∈ U l) : polar Q n (∑ i, x i) = polar Q n (x l) := by
  rw [← polarBilin_apply_apply, map_sum, Finset.sum_eq_single l]
  · rfl
  · intro i _ hil
    rw [polarBilin_apply_apply]
    exact hF.orth l i (Ne.symm hil) n hn (x i) (hx i)
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem eq_zero_of_sum_eq_zero {x : Fin 4 → Fin d → K} (hx : ∀ i, x i ∈ U i)
    (h0 : ∑ i, x i = 0) (l : Fin 4) : x l = 0 :=
  hF.nd l (x l) (hx l) fun n hn => by
    rw [polB_apply, ← hF.polar_sum hx hn, h0, polar_zero_right]

theorem eq_zero_of_add_eq_zero {k l : Fin 4} (hkl : k ≠ l) {a b : Fin d → K} (ha : a ∈ U k)
    (hb : b ∈ U l) (h0 : a + b = 0) : a = 0 :=
  hF.nd k a ha fun n hn => by
    rw [polB_apply, eq_neg_of_add_eq_zero_left h0, polar_neg_right, hF.orth k l hkl n hn b hb,
      neg_zero]

theorem polar_apply (s : Multiplicative (Fin 4 → ZMod p)) (x y : Fin d → K) :
    polar Q (glin (ι₀ s) x) (glin (ι₀ s) y) = polar Q x y := by
  rw [polar, polar, ← map_add, hF.iso, hF.iso, hF.iso]

section CharTwo

variable [CharP K 2]

theorem linearIndependent_apply {s : Multiplicative (Fin 4 → ZMod p)} {k : Fin 4}
    (hs : toAdd s k ≠ 0) {u : Fin d → K} (hu : u ∈ U k) (hQu : Q u ≠ 0) :
    LinearIndependent K ![u, glin (ι₀ s) u] := by
  have hu0 : u ≠ 0 := fun h => hQu (by rw [h, QuadraticMap.map_zero])
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hu0, rfl⟩
  · exfalso
    have hzu : glin (ι₀ s) u = (-(b⁻¹ * a)) • u := by
      have h1 : b • glin (ι₀ s) u = -(a • u) := eq_neg_of_add_eq_zero_right hab
      calc glin (ι₀ s) u = b⁻¹ • (b • glin (ι₀ s) u) := by
            rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = (-(b⁻¹ * a)) • u := by rw [h1, smul_neg, smul_smul, neg_smul]
    set c := -(b⁻¹ * a) with hc
    have hQ := hF.iso s u
    rw [hzu, QuadraticMap.map_smul, smul_eq_mul] at hQ
    have hc1 : c * c = 1 := mul_right_cancel₀ hQu (hQ.trans (one_mul (Q u)).symm)
    have hc2 : (c + 1) * (c + 1) = 0 := by
      linear_combination hc1 + (c + 1) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have hc3 : c = 1 := by
      linear_combination mul_self_eq_zero.mp hc2 - (CharTwo.two_eq_zero : (2 : K) = 0)
    rw [hc3, one_smul] at hzu
    exact hu0 (hF.eq_zero_of_apply_eq_self hs hu hzu)

theorem span_eq {s : Multiplicative (Fin 4 → ZMod p)} {k : Fin 4} (hs : toAdd s k ≠ 0)
    {u : Fin d → K} (hu : u ∈ U k) (hQu : Q u ≠ 0) :
    Submodule.span K {u, glin (ι₀ s) u} = U k := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
  · rintro _ (rfl | rfl)
    exacts [hu, hF.inv s k _ hu]
  · have h := finrank_span_eq_card (hF.linearIndependent_apply hs hu hQu)
    rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at h
    rw [h, hF.dim k]

theorem exists_sqRel (s : Multiplicative (Fin 4 → ZMod p)) (k : Fin 4) :
    ∃ t : K, ∀ u ∈ U k, glin (ι₀ s) (glin (ι₀ s) u) = t • glin (ι₀ s) u + u := by
  by_cases hs : toAdd s k = 0
  · refine ⟨0, fun u hu => ?_⟩
    rw [hF.apply_eq_self hs hu, hF.apply_eq_self hs hu, zero_smul, zero_add]
  obtain ⟨u₀, hu₀, hQu₀⟩ := exists_quad_ne_zero (hF.nd k) (hF.ne k)
  have hspan := hF.span_eq hs hu₀ hQu₀
  set z := glin (ι₀ s) with hz
  have hzzu₀ : z (z u₀) ∈ Submodule.span K {u₀, z u₀} := by
    rw [hspan]
    exact hF.inv s k _ (hF.inv s k _ hu₀)
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hzzu₀
  have hpol0 : polar Q u₀ (z u₀) ≠ 0 := by
    intro h0
    refine hQu₀ ?_
    have hu₀0 : u₀ = 0 := hF.nd k u₀ hu₀ fun n hn => by
      rw [← hspan] at hn
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hn
      rw [polB_apply, polar_add_left, polar_smul_left, polar_smul_left,
        OrdPNsOm.polar_self_charTwo, polar_comm Q (z u₀) u₀, h0, smul_zero, smul_zero, add_zero]
    rw [hu₀0, QuadraticMap.map_zero]
  have hα : α = 1 := by
    have h1 := hF.polar_apply s u₀ (z u₀)
    rw [← hz, ← hαβ, polar_add_right, polar_smul_right, polar_smul_right,
      OrdPNsOm.polar_self_charTwo, smul_zero, add_zero, smul_eq_mul,
      polar_comm Q (z u₀) u₀] at h1
    exact mul_right_cancel₀ hpol0 (h1.trans (one_mul _).symm)
  have h2 : z (z u₀) = u₀ + β • z u₀ := by rw [← hαβ, hα, one_smul]
  refine ⟨β, fun u hu => ?_⟩
  rw [← hspan] at hu
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  simp only [map_add, map_smul, h2]
  module

omit [CharP K 2] in
theorem toAdd_eq_zero_of_sq (hp : p.Prime) (hp2 : p ≠ 2) {s : Multiplicative (Fin 4 → ZMod p)}
    {l : Fin 4} (h : ∀ v ∈ U l, glin (ι₀ s) (glin (ι₀ s) v) = v) : toAdd s l = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hs
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp h3))
  have hss : toAdd (s * s) l ≠ 0 := by
    rw [toAdd_mul, Pi.add_apply, ← two_mul]
    exact mul_ne_zero h2 hs
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hF.ne l)
  refine hv0 (hF.eq_zero_of_apply_eq_self hss hv ?_)
  rw [map_mul, glin_mul, Module.End.mul_apply, h v hv]

omit [CharP K 2] in
theorem eq_zero_of_sqRel {s : Multiplicative (Fin 4 → ZMod p)} {k : Fin 4} (hs : toAdd s k = 0)
    {t : K} (h : ∀ u ∈ U k, glin (ι₀ s) (glin (ι₀ s) u) = t • glin (ι₀ s) u + u) : t = 0 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hF.ne k)
  have h1 := h u hu
  rw [hF.apply_eq_self hs hu, hF.apply_eq_self hs hu] at h1
  exact (smul_eq_zero.mp (add_eq_right.mp h1.symm)).resolve_right hu0

theorem polar_apply_eq {s : Multiplicative (Fin 4 → ZMod p)} {u : Fin d → K} {t : K}
    (ht : t ≠ 0) (h : glin (ι₀ s) (glin (ι₀ s) u) = t • glin (ι₀ s) u + u) :
    polar Q u (glin (ι₀ s) u) = t * Q u := by
  have h1 : Q (glin (ι₀ s) (glin (ι₀ s) u)) = Q u := by rw [hF.iso, hF.iso]
  rw [h, QuadraticMap.map_add Q, QuadraticMap.map_smul, hF.iso, polar_smul_left, smul_eq_mul,
    smul_eq_mul] at h1
  have h2 : t * (t * Q u + polar Q (glin (ι₀ s) u) u) = 0 := by linear_combination h1
  have h3 := (mul_eq_zero.mp h2).resolve_left ht
  rw [polar_comm]
  linear_combination h3 - t * Q u * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem exists_eq_smul_add_smul {s : Multiplicative (Fin 4 → ZMod p)} {k : Fin 4}
    (hs : toAdd s k ≠ 0) {g : Module.End K (Fin d → K)} (hgU : ∀ u ∈ U k, g u ∈ U k)
    (hgz : ∀ u ∈ U k, g (glin (ι₀ s) u) = glin (ι₀ s) (g u)) :
    ∃ α β : K, ∀ u ∈ U k, g u = α • u + β • glin (ι₀ s) u := by
  obtain ⟨u₀, hu₀, hQu₀⟩ := exists_quad_ne_zero (hF.nd k) (hF.ne k)
  have hspan := hF.span_eq hs hu₀ hQu₀
  have hgu₀ : g u₀ ∈ Submodule.span K {u₀, glin (ι₀ s) u₀} := by
    rw [hspan]
    exact hgU u₀ hu₀
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hgu₀
  refine ⟨α, β, fun u hu => ?_⟩
  rw [← hspan] at hu
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  simp only [map_add, map_smul]
  rw [hgz u₀ hu₀, ← hαβ]
  simp only [map_add, map_smul]
  module

end CharTwo

section Matched

variable [CharP K 2] [Finite K]

theorem charSum_modEq (hp : p.Prime) (k : Fin 4) :
    OrdPNsOm.charSum Q (U k) ≡ 1 [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hk : toAdd (ofAdd (Pi.single k (1 : ZMod p)) : Multiplicative (Fin 4 → ZMod p)) k ≠ 0 := by
    rw [toAdd_ofAdd, Pi.single_eq_same]
    exact one_ne_zero
  exact OrdPNsOm.charSum_modEq (y := glin (ι₀ (ofAdd (Pi.single k 1)))) (hF.inv _ k)
    (hF.iso _) (glin_pow_eq_one ι₀ _) fun u hu hyu => hF.eq_zero_of_apply_eq_self hk hu hyu

theorem exists_pair_of_matched (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup (Multiplicative (Fin 4 → ZMod p))} {k l : Fin 4} (hkl : k ≠ l)
    (hm : ∀ s ∈ S, ∃ t : K, (∀ u ∈ U k, glin (ι₀ s) (glin (ι₀ s) u) = t • glin (ι₀ s) u + u) ∧
      ∀ v ∈ U l, glin (ι₀ s) (glin (ι₀ s) v) = t • glin (ι₀ s) v + v)
    {s₀ : Multiplicative (Fin 4 → ZMod p)} (hs₀ : s₀ ∈ S) (hs₀k : toAdd s₀ k ≠ 0) :
    ∃ w₁ w₂ : Fin d → K, Q w₁ = 0 ∧ Q w₂ = 0 ∧ polar Q w₁ w₂ = 0 ∧
      LinearIndependent K ![w₁, w₂] ∧ ∀ s ∈ S, ∃ α β γ δ : K,
        glin (ι₀ s) w₁ = α • w₁ + β • w₂ ∧ glin (ι₀ s) w₂ = γ • w₁ + δ • w₂ ∧
          α * δ - β * γ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t₀, hk₀, hl₀⟩ := hm s₀ hs₀
  have ht₀ : t₀ ≠ 0 := by
    rintro rfl
    refine hs₀k (hF.toAdd_eq_zero_of_sq hp hp2 fun u hu => ?_)
    rw [hk₀ u hu, zero_smul, zero_add]
  obtain ⟨u, hu, hQu⟩ := exists_quad_ne_zero (hF.nd k) (hF.ne k)
  obtain ⟨v₀, hv₀, hQv₀⟩ := exists_quad_ne_zero (hF.nd l) (hF.ne l)
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q u / Q v₀)
  have hv : c • v₀ ∈ U l := (U l).smul_mem c hv₀
  have hQv : Q (c • v₀) = Q u := by
    rw [QuadraticMap.map_smul, smul_eq_mul, ← hc, div_mul_cancel₀ _ hQv₀]
  have hzu : glin (ι₀ s₀) u ∈ U k := hF.inv s₀ k u hu
  have hzv : glin (ι₀ s₀) (c • v₀) ∈ U l := hF.inv s₀ l _ hv
  have hw₂ : glin (ι₀ s₀) (u + c • v₀) = glin (ι₀ s₀) u + glin (ι₀ s₀) (c • v₀) :=
    map_add _ u _
  have hzw₂ : glin (ι₀ s₀) (glin (ι₀ s₀) u + glin (ι₀ s₀) (c • v₀)) =
      (u + c • v₀) + t₀ • (glin (ι₀ s₀) u + glin (ι₀ s₀) (c • v₀)) := by
    rw [map_add, hk₀ u hu, hl₀ _ hv]
    module
  have key : ∀ n : ℕ, ∃ α β γ δ : K,
      (glin (ι₀ s₀) ^ n) (u + c • v₀) =
        α • (u + c • v₀) + β • (glin (ι₀ s₀) u + glin (ι₀ s₀) (c • v₀)) ∧
      (glin (ι₀ s₀) ^ n) (glin (ι₀ s₀) u + glin (ι₀ s₀) (c • v₀)) =
        γ • (u + c • v₀) + δ • (glin (ι₀ s₀) u + glin (ι₀ s₀) (c • v₀)) ∧
      α * δ - β * γ = 1 := by
    intro n
    induction n with
    | zero => exact ⟨1, 0, 0, 1, by simp, by simp, by ring⟩
    | succ n ih =>
      obtain ⟨α, β, γ, δ, h₁, h₂, hdet⟩ := ih
      refine ⟨β, α + β * t₀, δ, γ + δ * t₀, ?_, ?_, ?_⟩
      · rw [pow_succ', Module.End.mul_apply, h₁, map_add, map_smul, map_smul, hw₂, hzw₂]
        module
      · rw [pow_succ', Module.End.mul_apply, h₂, map_add, map_smul, map_smul, hw₂, hzw₂]
        module
      · linear_combination (-1 : K) * hdet - (CharTwo.two_eq_zero : (2 : K) = 0)
  refine ⟨u + c • v₀, glin (ι₀ s₀) u + glin (ι₀ s₀) (c • v₀), ?_, ?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, hQv, hF.orth k l hkl u hu _ hv, add_zero,
      CharTwo.add_self_eq_zero]
  · rw [← hw₂, hF.iso, QuadraticMap.map_add Q, hQv, hF.orth k l hkl u hu _ hv, add_zero,
      CharTwo.add_self_eq_zero]
  · rw [polar_add_left, polar_add_right, polar_add_right, hF.polar_apply_eq ht₀ (hk₀ u hu),
      hF.orth k l hkl u hu _ hzv, hF.orth l k (Ne.symm hkl) _ hv _ hzu,
      hF.polar_apply_eq ht₀ (hl₀ _ hv), hQv]
    linear_combination t₀ * Q u * (CharTwo.two_eq_zero : (2 : K) = 0)
  · rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 : (a • u + b • glin (ι₀ s₀) u) + (a • (c • v₀) + b • glin (ι₀ s₀) (c • v₀)) = 0 := by
      rw [← hab]
      module
    have h2 := hF.eq_zero_of_add_eq_zero hkl
      ((U k).add_mem ((U k).smul_mem a hu) ((U k).smul_mem b hzu))
      ((U l).add_mem ((U l).smul_mem a hv) ((U l).smul_mem b hzv)) h1
    exact LinearIndependent.pair_iff.mp (hF.linearIndependent_apply hs₀k hu hQu) a b h2
  · intro s hs
    set n : ℕ := (toAdd s k / toAdd s₀ k).val with hn
    have hnk : toAdd (s₀ ^ n) k = toAdd s k := by
      rw [toAdd_pow, Pi.smul_apply, nsmul_eq_mul, hn, ZMod.natCast_zmod_val,
        div_mul_cancel₀ _ hs₀k]
    have hs' : s * (s₀ ^ n)⁻¹ ∈ S := S.mul_mem hs (S.inv_mem (S.pow_mem hs₀ n))
    have hs'k : toAdd (s * (s₀ ^ n)⁻¹) k = 0 := by
      rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, hnk, add_neg_cancel]
    obtain ⟨t', hk', hl'⟩ := hm _ hs'
    obtain rfl : t' = 0 := hF.eq_zero_of_sqRel hs'k hk'
    have hs'l : toAdd (s * (s₀ ^ n)⁻¹) l = 0 := hF.toAdd_eq_zero_of_sq hp hp2 fun w hw => by
      rw [hl' w hw, zero_smul, zero_add]
    have hnl : toAdd s l = toAdd (s₀ ^ n) l := by
      rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply] at hs'l
      exact add_neg_eq_zero.mp hs'l
    have hagree : ∀ w, w ∈ U k ∨ w ∈ U l → glin (ι₀ s) w = (glin (ι₀ s₀) ^ n) w := by
      rintro w (hw | hw)
      · rw [hF.apply_eq_of_eq hnk.symm hw, map_pow, glin_pow]
      · rw [hF.apply_eq_of_eq hnl hw, map_pow, glin_pow]
    obtain ⟨α, β, γ, δ, h₁, h₂, hdet⟩ := key n
    refine ⟨α, β, γ, δ, ?_, ?_, hdet⟩
    · rw [map_add, hagree u (Or.inl hu), hagree _ (Or.inr hv), ← map_add, h₁]
    · rw [map_add, hagree _ (Or.inl hzu), hagree _ (Or.inr hzv), ← map_add, h₂]

end Matched

section NotMatched

variable [CharP K 2]

theorem exists_commute_of_not_matched {S : Subgroup (Multiplicative (Fin 4 → ZMod p))}
    (hnm : ∀ k l, k ≠ l → ¬ ∀ s ∈ S, ∃ t : K,
      (∀ u ∈ U k, glin (ι₀ s) (glin (ι₀ s) u) = t • glin (ι₀ s) u + u) ∧
        ∀ v ∈ U l, glin (ι₀ s) (glin (ι₀ s) v) = t • glin (ι₀ s) v + v)
    {H : Subgroup (GL (Fin d) K)} (hH : ⁅H, H⁆ = H)
    (hHS : ∀ h ∈ H, ∀ s ∈ S, h * ι₀ s = ι₀ s * h) :
    ∃ k₀ : Fin 4, ∀ h ∈ H, ∀ s : Multiplicative (Fin 4 → ZMod p), toAdd s k₀ = 0 →
      h * ι₀ s = ι₀ s * h := by
  classical
  choose t ht using fun s k => hF.exists_sqRel s k
  have hHz : ∀ h ∈ H, ∀ s ∈ S, ∀ v, glin h (glin (ι₀ s) v) = glin (ι₀ s) (glin h v) := by
    intro h hh s hs v
    rw [← Module.End.mul_apply, ← glin_mul, hHS h hh s hs, glin_mul, Module.End.mul_apply]
  have hpres : ∀ h ∈ H, ∀ k, ∀ u ∈ U k, glin h u ∈ U k := by
    intro h hh k u hu
    obtain ⟨x, hx, hxs⟩ := hF.span (glin h u)
    have hrel : ∀ s ∈ S, glin (ι₀ s) (glin (ι₀ s) (glin h u)) =
        t s k • glin (ι₀ s) (glin h u) + glin h u := by
      intro s hs
      rw [← hHz h hh s hs, ← hHz h hh s hs, ht s k u hu, map_add, map_smul, hHz h hh s hs]
    have hxi : ∀ i, i ≠ k → x i = 0 := by
      intro i hik
      have hnm' := hnm k i (Ne.symm hik)
      push Not at hnm'
      obtain ⟨s, hs', hst⟩ := hnm'
      have hne : t s i ≠ t s k := by
        intro heq
        obtain ⟨v, hv, hv'⟩ := hst (t s k) (ht s k)
        refine hv' ?_
        rw [← heq]
        exact ht s i v hv
      have h0 : ∑ j, ((t s j - t s k) • glin (ι₀ s) (x j)) = 0 := by
        have h1 := hrel s hs'
        rw [hxs] at h1
        simp only [map_sum] at h1
        have h2 : ∑ j, glin (ι₀ s) (glin (ι₀ s) (x j)) =
            ∑ j, (t s j • glin (ι₀ s) (x j) + x j) :=
          Finset.sum_congr rfl fun j _ => ht s j (x j) (hx j)
        rw [h2, Finset.sum_add_distrib, Finset.smul_sum] at h1
        rw [← sub_eq_zero] at h1
        rw [← h1]
        simp only [sub_smul, Finset.sum_sub_distrib]
        abel
      have h3 := hF.eq_zero_of_sum_eq_zero (fun j => (U j).smul_mem _ (hF.inv s j _ (hx j))) h0 i
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact absurd (sub_eq_zero.mp h4) hne
      · have h5 := congrArg (glin (ι₀ s)⁻¹) h4
        rwa [glin_inv_apply, map_zero] at h5
    have hsum : glin h u = x k := by
      rw [hxs, Finset.sum_eq_single k (fun i _ hik => hxi i hik)
        (fun h' => absurd (Finset.mem_univ k) h')]
    rw [hsum]
    exact hx k
  have htriv : ∀ k, (∃ s ∈ S, toAdd s k ≠ 0) → ∀ h ∈ H, ∀ u ∈ U k, glin h u = u := by
    rintro k ⟨s₀, hs₀, hs₀k⟩
    have hab : ∀ h ∈ H, ∃ α β : K, ∀ u ∈ U k, glin h u = α • u + β • glin (ι₀ s₀) u :=
      fun h hh => hF.exists_eq_smul_add_smul hs₀k (hpres h hh k)
        fun u _ => hHz h hh s₀ hs₀ u
    have hcomm : ∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ u ∈ U k, glin h₁ (glin h₂ u) = glin h₂ (glin h₁ u) := by
      intro h₁ hh₁ h₂ hh₂ u hu
      obtain ⟨α₁, β₁, e₁⟩ := hab h₁ hh₁
      obtain ⟨α₂, β₂, e₂⟩ := hab h₂ hh₂
      have hzu := hF.inv s₀ k u hu
      rw [e₂ u hu, e₁ u hu, map_add, map_smul, map_smul, map_add, map_smul, map_smul,
        e₁ u hu, e₁ _ hzu, e₂ u hu, e₂ _ hzu]
      module
    have hle : ⁅H, H⁆ ≤ (genFixOn d K (U k : Set (Fin d → K))) := by
      rw [Subgroup.commutator_le]
      intro h₁ hh₁ h₂ hh₂ u hu
      have hu₂ : glin h₂⁻¹ u ∈ U k := hpres _ (H.inv_mem hh₂) k u hu
      have hu₁ : glin h₁⁻¹ (glin h₂⁻¹ u) ∈ U k := hpres _ (H.inv_mem hh₁) k _ hu₂
      rw [commutatorElement_def, glin_mul, glin_mul, glin_mul, Module.End.mul_apply,
        Module.End.mul_apply, Module.End.mul_apply, hcomm h₁ hh₁ h₂ hh₂ _ hu₁, glin_apply_inv,
        glin_apply_inv]
    intro h hh u hu
    exact (hle (hH.symm ▸ hh : h ∈ ⁅H, H⁆)) u hu
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin 4, ∀ k, k ≠ k₀ → ∃ s ∈ S, toAdd s k ≠ 0 := by
    by_cases hT : ∃ k₀, ∀ s ∈ S, toAdd s k₀ = 0
    · obtain ⟨k₀, hk₀⟩ := hT
      refine ⟨k₀, fun k hk => ?_⟩
      by_contra hcon
      push Not at hcon
      refine hnm k₀ k (Ne.symm hk) fun s hs => ⟨0, fun u hu => ?_, fun v hv => ?_⟩
      · rw [hF.apply_eq_self (hk₀ s hs) hu, hF.apply_eq_self (hk₀ s hs) hu, zero_smul,
          zero_add]
      · rw [hF.apply_eq_self (hcon s hs) hv, hF.apply_eq_self (hcon s hs) hv, zero_smul,
          zero_add]
    · push Not at hT
      exact ⟨0, fun k _ => hT k⟩
  refine ⟨k₀, fun h hh s hs => glin_injective ?_⟩
  rw [glin_mul, glin_mul]
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, hx, rfl⟩ := hF.span v
  simp only [Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = k₀
  · subst hi
    rw [hF.apply_eq_self hs (hx i), hF.apply_eq_self hs (hpres h hh i _ (hx i))]
  · rw [htriv i (hk₀ i hi) h hh _ (hF.inv s i _ (hx i)), htriv i (hk₀ i hi) h hh _ (hx i)]

end NotMatched

end Frame4

end Frame

end RootPlaneD4

end CFSG.StandardType
