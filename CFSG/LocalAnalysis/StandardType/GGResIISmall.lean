module

public import CFSG.LocalAnalysis.StandardType.GGResIISmallDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrWA
public import CFSG.LocalAnalysis.StandardType.GGRCLatticeTriple
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
import CFSG.LocalAnalysis.StandardType.GGTBFix

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Lattice

variable {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ}

private theorem ggResII_dot_symm (hQ : GGLatForm Q) (v w : Fin m → ℤ) :
    dotProduct w (Q.mulVec v) = dotProduct v (Q.mulVec w) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ.1, dotProduct_comm]

private theorem ggResII_dot_sq_le (hQ : GGLatForm Q) (v w : Fin m → ℤ) :
    (dotProduct v (Q.mulVec w)) ^ 2 ≤ dotProduct v (Q.mulVec v) * dotProduct w (Q.mulVec w) := by
  set B := dotProduct v (Q.mulVec w)
  set Nv := dotProduct v (Q.mulVec v)
  set Nw := dotProduct w (Q.mulVec w)
  have hpos : ∀ z : Fin m → ℤ, 0 ≤ dotProduct z (Q.mulVec z) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · exact (hQ.2 z hz).le
  have hBw : dotProduct w (Q.mulVec v) = B := ggResII_dot_symm hQ v w
  have hz : dotProduct (Nw • v - B • w) (Q.mulVec (Nw • v - B • w)) = Nw * (Nw * Nv - B ^ 2) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hBw]
    ring
  have h0 := hpos (Nw • v - B • w)
  rw [hz] at h0
  by_cases hw : w = 0
  · have hB : B = 0 := by simp [B, hw]
    rw [hB]
    have := hpos v
    have := hpos w
    nlinarith
  · have hNw : 0 < Nw := hQ.2 w hw
    nlinarith

theorem ggResII_latCartan_mul_mem (hQ : GGLatForm Q) {v w : Fin m → ℤ} (hv : GGLatRoot Q v)
    (hw : GGLatRoot Q w) :
    0 ≤ ggLatCartan Q v w * ggLatCartan Q w v ∧ ggLatCartan Q v w * ggLatCartan Q w v ≤ 4 := by
  have hNv : 0 < dotProduct v (Q.mulVec v) := hQ.2 v hv.1
  have hNw : 0 < dotProduct w (Q.mulVec w) := hQ.2 w hw.1
  have h1 : ggLatCartan Q v w * dotProduct w (Q.mulVec w) = 2 * dotProduct v (Q.mulVec w) :=
    Int.ediv_mul_cancel (hw.2 v)
  have h2 : ggLatCartan Q w v * dotProduct v (Q.mulVec v) = 2 * dotProduct v (Q.mulVec w) := by
    rw [← ggResII_dot_symm hQ v w]
    exact Int.ediv_mul_cancel (hv.2 w)
  have hP : (ggLatCartan Q v w * ggLatCartan Q w v) *
      (dotProduct v (Q.mulVec v) * dotProduct w (Q.mulVec w)) =
        4 * (dotProduct v (Q.mulVec w)) ^ 2 := by
    calc (ggLatCartan Q v w * ggLatCartan Q w v) *
          (dotProduct v (Q.mulVec v) * dotProduct w (Q.mulVec w))
        = (ggLatCartan Q v w * dotProduct w (Q.mulVec w)) *
            (ggLatCartan Q w v * dotProduct v (Q.mulVec v)) := by ring
      _ = 4 * (dotProduct v (Q.mulVec w)) ^ 2 := by rw [h1, h2]; ring
  have hCS := ggResII_dot_sq_le hQ v w
  have hprod : 0 < dotProduct v (Q.mulVec v) * dotProduct w (Q.mulVec w) := mul_pos hNv hNw
  constructor <;> nlinarith

end Lattice

section Refl

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggResII_pair_of_comm (hp2 : p ≠ 2) {s t : V ≃ₗ[ZMod p] V} {hs ht : V}
    {αs αt : Module.Dual (ZMod p) V} (hsw : ∀ w, s w = w - αs w • hs)
    (htw : ∀ w, t w = w - αt w • ht) (h2s : αs hs = 2) (h2t : αt ht = 2) (hc : t * s = s * t) :
    αs ht * αt hs = 0 ∨ αs ht * αt hs = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have key : ∀ w, (αs w * αt hs) • ht = (αt w * αs ht) • hs := by
    intro w
    have h := congrArg (fun f : V ≃ₗ[ZMod p] V => f w) hc
    simp only [LinearEquiv.mul_apply] at h
    rw [hsw, htw, htw, hsw, map_sub, map_sub, map_smul, map_smul] at h
    simp only [smul_eq_mul] at h
    linear_combination (norm := module) h
  by_cases hP : αs ht * αt hs = 0
  · exact Or.inl hP
  · right
    have hst : αt hs ≠ 0 := right_ne_zero_of_mul hP
    have k1 := key hs
    rw [h2s] at k1
    have k2 := congrArg αt k1
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, h2t] at k2
    have k3 : αt hs * (αs ht * αt hs - 4) = 0 := by linear_combination -k2
    rcases mul_eq_zero.mp k3 with h0 | h0
    · exact absurd h0 hst
    · exact sub_eq_zero.mp h0

end Refl

private theorem ggResII_mem_ggInduced_top {G : Type} [Group G] {L Bs K : Subgroup G}
    {ψ : MulAut ↥Bs} (h : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) : ψ ∈ ggInduced ⊤ Bs := by
  have hsub : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs := by
    apply sup_le <;> apply Subgroup.closure_mono <;> rintro φ ⟨g, -, hgN, hg⟩ <;>
      exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  exact mem_ggAutomizer_iff.mp (hsub h)

private theorem ggResII_automizer_fix {G : Type} [Group G] {Bs X : Subgroup G} {z : G}
    (hzBs : z ∈ Bs) (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) :
    ∀ φ ∈ ggAutomizer X Bs, φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := by
  intro φ hφ
  obtain ⟨g, hgX, _, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  apply Subtype.ext
  rw [hφg]
  have hzg : z * g = g * z :=
    (Subgroup.mem_centralizer_iff.mp (hXz hgX)) z (Set.mem_singleton z)
  rw [← hzg]
  group

private theorem ggResII_alpha_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {r : V ≃ₗ[ZMod p] V} {hv w : V}
    {αv : Module.Dual (ZMod p) V} (hr : ∀ w, r w = w - αv w • hv) (h2 : αv hv = 2)
    (hfix : r w = w) : αv w = 0 := by
  have hne : hv ≠ 0 := by
    rintro rfl
    rw [map_zero] at h2
    exact zmod_two_ne_zero hp2 h2.symm
  rw [hr, sub_eq_self] at hfix
  exact (smul_eq_zero.mp hfix).resolve_right hne

theorem ggResCaseIISmallInput_of_lin (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hLin : GGResIILinInput) : GGResCaseIISmallInput := by
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := hP
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let g : Option Λ → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
  let xv : V := ι (Additive.ofMul ⟨x, hxBs⟩)
  let yv : V := ι (Additive.ofMul ⟨y, hyBs⟩)
  have hα2 : ∀ o : Option Λ, α o (h o) = 2 := by
    intro o
    cases o with
    | none =>
      have h1 := hK none none
      rw [hCK.1 none] at h1
      simpa using h1
    | some i =>
      have h1 := hL i i
      rw [hCL.1 i] at h1
      simpa using h1
  have hA' : ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) := by
    rw [hAL, hAK, ← Subgroup.closure_union]
    congr 1
    ext γ
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr (Or.inr rfl)
      | some i => exact Or.inl ⟨i, rfl⟩
  have hAV : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range g) := by
    rw [hA', MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hxfix : ∀ i : Λ, α (some i) xv = 0 := by
    intro i
    have hmem : φ (some i) ∈ ggAutomizer L Bs := by
      rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩
    have hf := ggResII_automizer_fix hxBs hLx _ hmem
    exact ggResII_alpha_eq_zero hp2 (hφ (some i)) (hα2 (some i))
      ((ggLin_fix_iff ι (φ (some i)) _).mp hf)
  have hspan : ∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {xv} := by
    intro w hw
    set bb : ↥Bs := Additive.toMul (ι.symm w) with hbb
    have hwbb : ι (Additive.ofMul bb) = w := by simp [hbb]
    have hgen : ∀ i : Λ, φ (some i) bb = bb := by
      intro i
      rw [ggLin_fix_iff (p := p) ι, hwbb, hφ, hw i, zero_smul, sub_zero]
    have hall : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
      rw [hAL]
      exact ggFixed_of_mem_closure (fun i : Λ => φ (some i)) bb hgen
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1 hH.2.2.2.2.2.1
        hH.2.2.2.2.2.2 bb hall)
    have hbk : bb = (⟨x, hxBs⟩ : ↥Bs) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [← hwbb, hbk, ofMul_zpow, map_zsmul]
    exact Submodule.mem_span_singleton.mpr ⟨(k : ZMod p), by rw [Int.cast_smul_eq_zsmul]⟩
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hx1 : x ≠ 1 := by
    intro hx1
    have hyp : y ^ p = 1 := hH.1.2.2.1.2.1.2 y hyD
    have hDle : D ≤ Subgroup.zpowers y := by
      rw [hDgen, hx1, Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | ha
      · exact Subgroup.one_mem _
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact Subgroup.mem_zpowers y
    have hcon : p ^ 2 ≤ p := by
      calc p ^ 2 = Nat.card D := hDcard.symm
        _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
        _ ≤ p := by
          rw [Nat.card_zpowers]
          exact orderOf_le_of_pow_eq_one hp.pos hyp
    nlinarith [hcon, hp.two_le]
  have hxa : α none xv ≠ 0 := by
    intro h0
    have hgen : ∀ γ ∈ Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none},
        γ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      rintro γ (⟨j, rfl⟩ | hγ)
      · rw [ggLin_fix_iff (p := p) ι, hφ, hxfix j, zero_smul, sub_zero]
      · rw [Set.mem_singleton_iff] at hγ
        rw [hγ, ggLin_fix_iff (p := p) ι, hφ, h0, zero_smul, sub_zero]
    have hle : Subgroup.closure (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}) ≤
        MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
      rw [Subgroup.closure_le]
      exact fun γ hγ => hgen γ hγ
    refine hx1 (hWA G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 ⟨x, hxBs⟩ (Subgroup.mem_zpowers x) fun ψ hψ => ?_)
    rw [hAK] at hψ
    exact hle hψ
  have hyfix : ∀ o : Option {i : Λ // i ≠ b}, α (o.map Subtype.val) yv = 0 := by
    intro o
    have hmem : φ (o.map Subtype.val) ∈ ggAutomizer K Bs := by
      rw [hAK]
      cases o with
      | none => exact Subgroup.subset_closure (Or.inr rfl)
      | some j => exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
    have hf := ggResII_automizer_fix hyBs hKy _ hmem
    exact ggResII_alpha_eq_zero hp2 (hφ _) (hα2 _) ((ggLin_fix_iff ι _ _).mp hf)
  have hyx : yv ∉ Submodule.span (ZMod p) {xv} := by
    intro hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    have hc' : (⟨y, hyBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs) ^ c.val := by
      apply Additive.ofMul.injective
      apply ι.injective
      rw [ofMul_pow, map_nsmul]
      change yv = c.val • xv
      rw [← hc, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    have hyz : y ∈ Subgroup.zpowers x := by
      have hyx' : y = x ^ c.val := by
        have := congrArg Subtype.val hc'
        simpa using this
      rw [hyx']
      exact Subgroup.npow_mem_zpowers x c.val
    have hx : x ^ p = 1 := hH.1.tableB_facts.2.1.2 x hxBs
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hDgen, Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | ha
      · exact Subgroup.mem_zpowers a
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact hyz
    have hcon : p ^ 2 ≤ p := by
      calc p ^ 2 = Nat.card D := hDcard.symm
        _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
        _ ≤ p := by
          rw [Nat.card_zpowers]
          exact orderOf_le_of_pow_eq_one hp.pos hx
    nlinarith [hcon, hp.two_le]
  have hcard : Fintype.card Λ < 9 := by
    have hh := htyp
    rw [ggTypRankLt, Nat.card_eq_fintype_card] at hh
    exact hh
  rcases hLin p Λ b ML CL MK CK V g h α xv yv hp2 hcard hWL hCL hWK hCK hdel hφ hL hK hsel.1
      hsel.2 hxfix hspan hxa hyfix hyx with
    ⟨t, ht, htv⟩ | ⟨hp5, ψ, hψ, j, j', hj, hj', hpair⟩ | hW
  ·
    exfalso
    rw [← hAV] at ht
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp ht
    exact hH.2.2.2.1 ψ (ggResII_mem_ggInduced_top hψA) (ggRC_isTransvection_of_lin ι ψ htv)
  ·
    exfalso
    rw [← hAV, hA'] at hψ
    obtain ⟨ψ₀, hψ₀, rfl⟩ := Subgroup.mem_map.mp hψ
    let ht : V := ggLin (p := p) ι ψ₀ (h (some j))
    let αt : Module.Dual (ZMod p) V :=
      (α (some j)).comp ((ggLin (p := p) ι ψ₀)⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap
    have hpp : α (some j') ht * αt (h (some j')) =
        α (some j') (ggLin (p := p) ι ψ₀ (h (some j))) *
          α (some j) ((ggLin (p := p) ι ψ₀)⁻¹ (h (some j'))) := rfl
    rw [← hpp] at hpair
    have hαt : αt ht = 2 := by
      change α (some j) ((ggLin (p := p) ι ψ₀)⁻¹ (ggLin (p := p) ι ψ₀ (h (some j)))) = 2
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
      exact hα2 (some j)
    have htl : ∀ w, ggLin (p := p) ι (ψ₀ * φ (some j) * ψ₀⁻¹) w = w - αt w • ht := by
      intro w
      rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hφ, map_sub,
        map_smul, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
      rfl
    have hnc : ψ₀ * φ (some j) * ψ₀⁻¹ * φ (some j') ≠
        φ (some j') * (ψ₀ * φ (some j) * ψ₀⁻¹) := by
      intro hc
      have hc' : ggLin (p := p) ι (ψ₀ * φ (some j) * ψ₀⁻¹) * ggLin (p := p) ι (φ (some j')) =
          ggLin (p := p) ι (φ (some j')) * ggLin (p := p) ι (ψ₀ * φ (some j) * ψ₀⁻¹) := by
        rw [← map_mul, ← map_mul, hc]
      rcases ggResII_pair_of_comm hp2 (hφ (some j')) htl (hα2 (some j')) hαt hc' with h0 | h4
      · exact hpair (by rw [h0]; simp)
      · exact hpair (by rw [h4]; simp)
    obtain ⟨m, Q, v, μ, hQ, hroot, hμ, hcongr⟩ := ggRC_lattice_triple hJr hPump hLB hSP hp5 hH
      hφ (hα2 (some j)) (hα2 (some j')) hAL hAK hJ hj hj' hψ₀ hαt htl hnc
    have h12 : α (some j') ht * μ 2 = μ 1 * (ggLatCartan Q (v 2) (v 1) : ZMod p) := hcongr 1 2
    have h21 : αt (h (some j')) * μ 1 = μ 2 * (ggLatCartan Q (v 1) (v 2) : ZMod p) := hcongr 2 1
    have hprod : α (some j') ht * αt (h (some j')) =
        ((ggLatCartan Q (v 2) (v 1) * ggLatCartan Q (v 1) (v 2) : ℤ) : ZMod p) := by
      have hμ12 : μ 1 * μ 2 ≠ 0 := mul_ne_zero (hμ 1) (hμ 2)
      apply mul_left_cancel₀ hμ12
      push_cast
      linear_combination (αt (h (some j')) * μ 1) * h12 +
        (μ 1 * (ggLatCartan Q (v 2) (v 1) : ZMod p)) * h21
    obtain ⟨hlo, hhi⟩ := ggResII_latCartan_mul_mem hQ (hroot 2) (hroot 1)
    generalize ggLatCartan Q (v 2) (v 1) * ggLatCartan Q (v 1) (v 2) = n at hlo hhi hprod
    apply hpair
    rw [hprod]
    interval_cases n <;> simp
  ·
    rw [← hAV] at hW
    exact ggRC_weylReflGroup_of_linWeyl ι _ hW

end CFSG.StandardType
