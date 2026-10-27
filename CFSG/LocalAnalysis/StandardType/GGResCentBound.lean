module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
import CFSG.LocalAnalysis.StandardType.GGResCentBoundLin
import CFSG.LocalAnalysis.StandardType.GGWeylMatrixAut
import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes
import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGTBFix

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose, instance_reducible]
def ggResCentConjAction {G : Type} [Group G] {Λ : Type} {Bs : Subgroup G}
    (H : Subgroup (MulAut ↥Bs)) : MulAction ↥H (Λ → MulAut ↥Bs) where
  smul n g := fun i => MulAut.conj (n : MulAut ↥Bs) (g i)
  one_smul g := by
    funext i
    change MulAut.conj (1 : MulAut ↥Bs) (g i) = g i
    rw [MulAut.conj_apply, one_mul, inv_one, mul_one]
  mul_smul n m g := by
    funext i
    change MulAut.conj (((n * m : ↥H) : MulAut ↥Bs)) (g i) =
      MulAut.conj ((n : ↥H) : MulAut ↥Bs) (MulAut.conj ((m : ↥H) : MulAut ↥Bs) (g i))
    rw [Subgroup.coe_mul, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group

theorem ggWeylDatum_rootKernel_le_line_of_fix {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x : G} {Λ : Type} [Fintype Λ]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hx : x ∈ Bs)
    (hfix : ∀ b : Bs, (∀ i, φ i b = b) → (b : G) ∈ Subgroup.zpowers x) :
    ∀ v : V, (∀ i, α i v = 0) →
      v ∈ Submodule.span (ZMod p) {(ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) : V)} := by
  intro v hv
  classical
  let xx : ↥Bs := ⟨x, hx⟩
  let bb : ↥Bs := Additive.toMul (ι.symm v)
  have hbbw : ι (Additive.ofMul bb) = v := by
    simp [bb]
  have hbb : ∀ i, φ i bb = bb := by
    intro i
    have h1 := hφ i v
    rw [hv i, zero_smul, sub_zero] at h1
    exact (ggLin_fix_iff (p := p) ι (φ i) bb).mpr (by rw [hbbw]; exact h1)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hfix bb hbb)
  have hbbk : bb = xx ^ k := Subtype.ext (by simpa [xx] using hk.symm)
  have hvk : v = k • (ι (Additive.ofMul xx) : V) := by
    calc v = ι (Additive.ofMul bb) := hbbw.symm
      _ = ι (k • Additive.ofMul xx) := by rw [hbbk, ofMul_zpow]
      _ = k • (ι (Additive.ofMul xx) : V) := map_zsmul ι k _
  refine Submodule.mem_span_singleton.mpr ⟨(k : ZMod p), ?_⟩
  rw [Int.cast_smul_eq_zsmul]
  exact hvk.symm

theorem ggResCent_conj_decomp {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {W : Subgroup (MulAut ↥Bs)} {φ : Λ → MulAut ↥Bs}
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hRC : GGReflConjSimple p W φ)
    (f : M.Group ≃* ↥W) (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    {n : MulAut ↥Bs} (hnW : n ∈ Subgroup.normalizer (W : Set (MulAut ↥Bs))) :
    ∃ (σ : Λ ≃ Λ) (w : ↥W),
      (∀ i j, M (σ i) (σ j) = M i j) ∧
      (∀ j, n * φ j * n⁻¹ = (w : MulAut ↥Bs) * φ (σ.symm j) * (w : MulAut ↥Bs)⁻¹) := by
  classical
  let conjW : ↥W ≃* ↥W :=
  { toFun := fun w =>
      ⟨n * (w : MulAut ↥Bs) * n⁻¹,
        (Subgroup.mem_normalizer_iff.mp hnW (w : MulAut ↥Bs)).mp w.2⟩
    invFun := fun w =>
      ⟨n⁻¹ * (w : MulAut ↥Bs) * n,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnW) (w : MulAut ↥Bs)).mp w.2⟩
    left_inv := fun w =>
      Subtype.ext (by simp only; group)
    right_inv := fun w =>
      Subtype.ext (by simp only; group)
    map_mul' := fun w w' =>
      Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let f' : M.Group ≃* ↥W := f.trans conjW
  have hf' : ∀ i, (f' (M.simple i) : MulAut ↥Bs) = n * φ i * n⁻¹ := by
    intro i
    simp [f', conjW, hf i]
  have hconj : ∀ k, ∃ (w : ↥W) (i : Λ), f' (M.simple k) = w * f (M.simple i) * w⁻¹ := by
    intro k
    have hmem : n * φ k * n⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hnW (φ k)).mp (by rw [← hf k]; exact (f (M.simple k)).2)
    have hreflk : GGIsReflection p (n * φ k * n⁻¹) := (hrefl k).conj n
    obtain ⟨w0, hw0, i, hi⟩ := hRC (n * φ k * n⁻¹) hmem hreflk
    refine ⟨⟨w0, hw0⟩, i, Subtype.ext ?_⟩
    rw [hf' k, hi]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf i]
  obtain ⟨σ, w, hσ⟩ :=
    ggWeylSimpleSystemsConjInput_holds Λ Λ M M hM hM (↥W) f f' hconj
  have hMσ : ∀ i j, M (σ i) (σ j) = M i j := by
    intro i j
    have hordσ : orderOf (M.simple (σ i) * M.simple (σ j)) = M.M (σ i) (σ j) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem (σ i) (σ j)
    have hordij : orderOf (M.simple i * M.simple j) = M.M i j := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
    have hmap : f' (M.simple (σ i) * M.simple (σ j)) =
        w * f (M.simple i * M.simple j) * w⁻¹ := by
      rw [map_mul, map_mul, hσ i, hσ j]
      group
    have hord : orderOf (M.simple (σ i) * M.simple (σ j)) =
        orderOf (M.simple i * M.simple j) := by
      calc orderOf (M.simple (σ i) * M.simple (σ j))
          = orderOf (f' (M.simple (σ i) * M.simple (σ j))) :=
            (MulEquiv.orderOf_eq f' _).symm
        _ = orderOf (w * f (M.simple i * M.simple j) * w⁻¹) := by rw [hmap]
        _ = orderOf (f (M.simple i * M.simple j)) := by
            rw [show w * f (M.simple i * M.simple j) * w⁻¹ =
              MulAut.conj w (f (M.simple i * M.simple j)) from rfl, MulEquiv.orderOf_eq]
        _ = orderOf (M.simple i * M.simple j) := MulEquiv.orderOf_eq f _
    rw [← hordσ, hord, hordij]
  refine ⟨σ, w, hMσ, fun j => ?_⟩
  have h := congrArg Subtype.val (hσ (σ.symm j))
  rw [σ.apply_symm_apply, hf' j] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hf (σ.symm j)] using h

theorem ggResCent_conj_orbit_bound_inner {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {W H : Subgroup (MulAut ↥Bs)} {φ : Λ → MulAut ↥Bs}
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hRC : GGReflConjSimple p W φ)
    (f : M.Group ≃* ↥W) (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hnorm : ∀ n : H, n.1 ∈ Subgroup.normalizer (W : Set (MulAut ↥Bs))) {d : ℕ}
    (hcard : Nat.card {σ : Λ ≃ Λ // ∀ i j, M (σ i) (σ j) = M i j} ≤ d) :
    Nat.card (Set.range (fun n : H => (ggResCentConjAction H).smul n φ)) ≤
      Nat.card (MulAut.conj : W →* MulAut W).range * d := by
  classical
  let F : ↥H → (Λ → MulAut ↥Bs) := fun n => (ggResCentConjAction H).smul n φ
  let I := (MulAut.conj : W →* MulAut W).range
  let P := ↥I × {σ : Λ ≃ Λ // ∀ i j, M (σ i) (σ j) = M i j}
  let Gfun : P → (Λ → MulAut ↥Bs) :=
    fun a j => ((a.1.1 (f (M.simple (a.2.1.symm j)))) : MulAut ↥Bs)
  have hsub : Set.range F ⊆ Set.range Gfun := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨σ, w, hMσ, hEq⟩ := ggResCent_conj_decomp hM hrefl hRC f hf (hnorm n)
    refine ⟨(⟨MulAut.conj w,w,rfl⟩, ⟨σ, hMσ⟩), ?_⟩
    funext j
    change ((MulAut.conj w (f (M.simple (σ.symm j)))) : MulAut Bs) = F n j
    rw [MulAut.conj_apply]
    change (w : MulAut Bs) * (f (M.simple (σ.symm j)) : MulAut Bs) * (w : MulAut Bs)⁻¹ =
      (n : MulAut Bs) * φ j * (n : MulAut Bs)⁻¹
    rw [hf]
    exact (hEq j).symm
  have hcard1 : Nat.card (Set.range F) ≤ Nat.card (Set.range Gfun) :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  have hcard2 : Nat.card (Set.range Gfun) ≤ Nat.card P := by
    refine Nat.card_le_card_of_surjective
      (fun a : P => (⟨Gfun a, Set.mem_range_self a⟩ : Set.range Gfun)) ?_
    rintro ⟨y, a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  change Nat.card (Set.range F) ≤ Nat.card I * d
  calc Nat.card (Set.range F) ≤ Nat.card (Set.range Gfun) := hcard1
    _ ≤ Nat.card P := hcard2
    _ = Nat.card I * Nat.card {σ : Λ ≃ Λ // ∀ i j, M (σ i) (σ j) = M i j} := Nat.card_prod _ _
    _ ≤ Nat.card I * d := Nat.mul_le_mul_left _ hcard

theorem ggResCent_conj_orbit_bound {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {W H : Subgroup (MulAut ↥Bs)} {φ : Λ → MulAut ↥Bs}
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hRC : GGReflConjSimple p W φ)
    (f : M.Group ≃* ↥W) (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hnorm : ∀ n : H, n.1 ∈ Subgroup.normalizer (W : Set (MulAut ↥Bs))) {d : ℕ}
    (hcard : Nat.card {σ : Λ ≃ Λ // ∀ i j, M (σ i) (σ j) = M i j} ≤ d) :
    Nat.card (Set.range (fun n : H => (ggResCentConjAction H).smul n φ)) ≤
      Nat.card W * d := by
  have h := ggResCent_conj_orbit_bound_inner hM hrefl hRC f hf hnorm hcard
  have hi : Nat.card (MulAut.conj : W →* MulAut W).range ≤ Nat.card W :=
    Nat.card_le_card_of_surjective _ (MulAut.conj : W →* MulAut W).rangeRestrict_surjective
  exact h.trans (Nat.mul_le_mul_right d hi)

theorem ggResCent_ker_card {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) (hx : x ∈ Bs) (hx1 : x ≠ 1)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Module.Finite (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hker : ∀ v : V, (∀ i, α i v = 0) →
      v ∈ Submodule.span (ZMod p) {ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))})
    (hΛ : Nonempty Λ) (hfin4 : 4 ≤ Module.finrank (ZMod p) V)
    {Cx : Subgroup (MulAut ↥Bs)} {Z : Subgroup ↥Cx}
    (hCx_top : Cx ≤ ggAutomizer ⊤ Bs)
    (hCx_stab : Cx ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs))
    (hZ : ∀ c : ↥Z, ∀ i, (c.1.1 : MulAut ↥Bs) * φ i = φ i * c.1.1) :
    Nat.card Z ≤ p - 1 := by
  classical
  let xx : ↥Bs := ⟨x, hx⟩
  let T (c : ↥Z) : V ≃ₗ[ZMod p] V := ggLin (p := p) ι c.1.1
  have hT (c : ↥Z) : ∀ i w, T c (w - α i w • h i) = T c w - α i (T c w) • h i := by
    intro i w
    have hcomm := hZ c i
    calc
      T c (w - α i w • h i) = T c (ggLin (p := p) ι (φ i) w) := by rw [hφ i w]
      _ = ggLin (p := p) ι (c.1.1 * φ i) w := by
          simp only [T, map_mul, LinearEquiv.mul_apply]
      _ = ggLin (p := p) ι (φ i * c.1.1) w := by rw [hcomm]
      _ = ggLin (p := p) ι (φ i) (T c w) := by
          simp only [T, map_mul, LinearEquiv.mul_apply]
      _ = T c w - α i (T c w) • h i := by rw [hφ i (T c w)]
  have hex (c : ↥Z) : ∃ μ : ZMod p, ∀ i w, α i (T c w) = μ * α i w :=
    ggWeylDatum_commutant_scalar hp2 hM hC h α hpair (T c).toLinearMap (hT c)
  let μ (c : ↥Z) : ZMod p := Classical.choose (hex c)
  have hμ (c : ↥Z) : ∀ i w, α i (T c w) = μ c * α i w := Classical.choose_spec (hex c)
  have hμ_unique (c : ↥Z) {μ' : ZMod p}
      (hμ' : ∀ i w, α i (T c w) = μ' * α i w) : μ' = μ c := by
    obtain ⟨i0⟩ := hΛ
    have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
    have hα : α i0 (h i0) = (2 : ZMod p) := by
      rw [hpair i0 i0, hC.1 i0]
      norm_num
    have h1 := hμ' i0 (h i0)
    have h2 := hμ c i0 (h i0)
    rw [hα] at h1 h2
    exact mul_right_cancel₀ htwo (h1.symm.trans h2)
  have hμ_mul (c d : ↥Z) : μ (c * d) = μ c * μ d := by
    have hcomp : ∀ w, T (c * d) w = T c (T d w) := by
      intro w
      show ggLin (p := p) ι ((c * d).1.1) w =
        ggLin (p := p) ι c.1.1 (ggLin (p := p) ι d.1.1 w)
      rw [show (c * d).1.1 = c.1.1 * d.1.1 from rfl, map_mul, LinearEquiv.mul_apply]
    refine (hμ_unique (c * d) ?_).symm
    intro i w
    rw [hcomp w, hμ c i (T d w), hμ d i w, mul_assoc]
  have hμ_one : μ 1 = 1 := by
    refine (hμ_unique 1 ?_).symm
    intro i w
    simp [T]
  have hμ_inv (c : ↥Z) : μ c⁻¹ = (μ c)⁻¹ := by
    have h := hμ_mul c c⁻¹
    rw [mul_inv_cancel, hμ_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hμ_ne (c : ↥Z) : μ c ≠ 0 := by
    intro h0
    have htop : Submodule.span (ZMod p) ({ι (Additive.ofMul xx)} : Set V) = ⊤ := by
      refine eq_top_iff.mpr fun v _ => ?_
      have hv : T c ((T c).symm v) = v := (T c).apply_symm_apply v
      rw [← hv]
      exact hker (T c ((T c).symm v)) (fun i => by rw [hμ c i, h0, zero_mul])
    have hle1 : Module.finrank (ZMod p) V ≤ 1 := by
      refine finrank_le_one (ι (Additive.ofMul xx)) ?_
      intro w
      have hw : w ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul xx)} : Set V) := by
        rw [htop]
        exact Submodule.mem_top
      exact Submodule.mem_span_singleton.mp hw
    omega
  have hμ_inj : Function.Injective μ := by
    intro c d hcd
    let e : ↥Z := d⁻¹ * c
    have hμe : μ e = 1 := by
      have h1 : μ (d⁻¹ * c) = μ d⁻¹ * μ c := hμ_mul d⁻¹ c
      rw [h1, hμ_inv d, hcd, inv_mul_cancel₀ (hμ_ne d)]
    have he1 : e.1.1 = 1 := by
      refine ggEq_one_of_mod_zpowers hBs hNT hx hx1 ?_ ?_ ?_
      · have hmem : e.1.1 ∈ ggAutomizer ⊤ Bs := hCx_top e.1.2
        rwa [ggAutomizer_eq] at hmem
      · simpa [MulAut.smul_def] using
          (MulAction.mem_stabilizer_iff.mp (hCx_stab e.1.2))
      · intro b
        let w : V := ι (Additive.ofMul b)
        have hT_apply : T e w = ι (Additive.ofMul (e.1.1 b)) :=
          ggLin_apply_ofMul (p := p) ι e.1.1 b
        have hzero : ∀ i, α i (T e w - w) = 0 := by
          intro i
          rw [map_sub, hμ e i w, hμe, one_mul, sub_self]
        have hspan := hker (T e w - w) hzero
        rw [Submodule.mem_span_singleton] at hspan
        obtain ⟨μ0, hμ0⟩ := hspan
        obtain ⟨k, hk⟩ := ZMod.intCast_surjective μ0
        have hdiff : T e w - w = ι (Additive.ofMul (e.1.1 b / b)) := by
          rw [hT_apply]
          show ι (Additive.ofMul (e.1.1 b)) - ι (Additive.ofMul b) = _
          rw [← map_sub, ← ofMul_div]
        have hkeq : ι (Additive.ofMul (e.1.1 b / b)) = ι (Additive.ofMul (xx ^ k)) := by
          calc ι (Additive.ofMul (e.1.1 b / b)) = T e w - w := hdiff.symm
            _ = μ0 • ι (Additive.ofMul xx) := hμ0.symm
            _ = (k : ZMod p) • ι (Additive.ofMul xx) := by rw [← hk]
            _ = k • ι (Additive.ofMul xx) := by rw [Int.cast_smul_eq_zsmul]
            _ = ι (k • Additive.ofMul xx) := by rw [map_zsmul]
            _ = ι (Additive.ofMul (xx ^ k)) := by rw [ofMul_zpow]
        have hb_eq : e.1.1 b / b = xx ^ k :=
          Additive.ofMul.injective (ι.injective hkeq)
        have hb_eq' : b⁻¹ * e.1.1 b = xx ^ k := by
          rw [← hb_eq, div_eq_mul_inv]
          exact hBs.1.is_comm.comm b⁻¹ (e.1.1 b)
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨k, ?_⟩
        rw [hb_eq', Subgroup.coe_zpow]
    have heq : e = 1 := Subtype.ext (Subtype.ext he1)
    have hd : d⁻¹ * c = 1 := by simpa [e] using heq
    calc c = d * (d⁻¹ * c) := by group
      _ = d * 1 := by rw [hd]
      _ = d := by group
  have hcard : Nat.card ↥Z ≤ Nat.card {μ : ZMod p // μ ≠ 0} :=
    Nat.card_le_card_of_injective
      (fun c : ↥Z => (⟨μ c, hμ_ne c⟩ : {μ : ZMod p // μ ≠ 0}))
      (fun a b hab => hμ_inj (congrArg Subtype.val hab))
  have hcard' : Nat.card {μ : ZMod p // μ ≠ 0} = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun μ : ZMod p => μ = 0),
      Fintype.card_subtype_eq, ZMod.card]
  rwa [hcard'] at hcard

theorem ggResCentBound_of_xDatum (ha₀ : GGLNoncyclicInput) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) (hL : GGResXDatum p Bs L) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := by
  classical
  obtain ⟨hp, hBs, hxB, hLx, hp4⟩ := hH.1.tableB_facts
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hNT : GGNoTransvection p Bs := hH.2.2.2.1
  have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨Λ, iΛF, iΛD, M, C, V, iVadd, iVmod, ι, φ, h, α, hM, hC, hφ, hrefl, hpair,
    ⟨f, hf⟩, hAL⟩ := hL
  let := iΛF
  let := iΛD
  let := iVadd
  let := iVmod
  let W : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let S : Subgroup (MulAut ↥Bs) := MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)
  let Cx : Subgroup (MulAut ↥Bs) := A ⊓ S
  change Nat.card ↥Cx ≤ (p - 1) * 6 * Nat.card ↥W
  have hAtop : A ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hCx_top : Cx ≤ ggAutomizer ⊤ Bs := fun c hc => hAtop hc.1
  have hCx_stab : Cx ≤ S := fun _ hc => hc.2
  have hVfin : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let : Finite V := hVfin
  let : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcardV : Nat.card V = Nat.card ↥Bs := by
    have h1 : Nat.card (Additive ↥Bs) = Nat.card V := Nat.card_congr ι.toEquiv
    exact h1.symm.trans (Nat.card_congr Additive.toMul)
  have hpow : p ^ Module.finrank (ZMod p) V = Nat.card V :=
    FiniteField.pow_finrank_eq_natCard p V
  have h1p : 1 < p := hp.one_lt
  have hfin4 : 4 ≤ Module.finrank (ZMod p) V := by
    have hle : p ^ 4 ≤ p ^ Module.finrank (ZMod p) V := by
      rw [hpow, hcardV]
      exact hp4
    exact (Nat.pow_le_pow_iff_right h1p).mp hle
  have hker : ∀ v : V, (∀ i, α i v = 0) →
      v ∈ Submodule.span (ZMod p) {ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} :=
    ggWeylDatum_rootKernel_le_line_of_fix hφ hx (by
      intro b hb
      have hbL : ∀ ψ ∈ ggAutomizer L Bs, ψ b = b := by
        rw [hAL]
        exact ggFixed_of_mem_closure φ b hb
      exact hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
        hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 b hbL)
  have hfin_le : Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 :=
    ggWeylDatum_finrank_le α (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) hker
  have h3 : 3 ≤ Fintype.card Λ := by omega
  have hΛ : Nonempty Λ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card Λ)
  have hRC : GGReflConjSimple p W φ :=
    ggReflConjSimple_of_weylMatrix hp2 (by exact hM) h3 hC ι φ h α hpair hφ hAL
  have hnorm : ∀ n : ↥Cx, (n.1 : MulAut ↥Bs) ∈
      Subgroup.normalizer (W : Set (MulAut ↥Bs)) := by
    intro n
    have hnTop : (n.1 : MulAut ↥Bs) ∈ ggAutomizer ⊤ Bs := hAtop n.2.1
    have hfix : (n.1 : MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs) ∈
        Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
      have hstab := MulAction.mem_stabilizer_iff.mp (n.2.2 : (n.1 : MulAut ↥Bs) ∈ S)
      have hfixeq : (n.1 : MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
        simpa [MulAut.smul_def] using hstab
      rw [hfixeq]
      exact Subgroup.mem_zpowers _
    exact ggAutomizer_mem_normalizer_of_zpowers ha₀ hH.1.1 hx hnTop hfix
  let act : MulAction ↥Cx (Λ → MulAut ↥Bs) := ggResCentConjAction Cx
  let : SMul ↥Cx (Λ → MulAut ↥Bs) := act.toSMul
  let : MulAction ↥Cx (Λ → MulAut ↥Bs) := act
  let r : Λ → MulAut ↥Bs := φ
  let F : ↥Cx → (Λ → MulAut ↥Bs) := fun n i => act.smul n r i
  let Z : Subgroup ↥Cx := MulAction.stabilizer ↥Cx r
  have hcardRange : Nat.card (Set.range F) ≤ Nat.card W * 6 :=
    ggResCent_conj_orbit_bound hM hrefl hRC f hf hnorm
      (GGIsWeylMatrix.card_autPerm_le_six hM)
  let : Fintype ↥Cx := Fintype.ofFinite ↥Cx
  let : Fintype ↥(MulAction.orbit ↥Cx r) := Fintype.ofFinite _
  let : Fintype ↥(MulAction.stabilizer ↥Cx r) := Fintype.ofFinite _
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥Cx) r
  simp only [← Nat.card_eq_fintype_card] at hOS
  have hOS' : Nat.card ↥Cx = Nat.card (Set.range F) * Nat.card Z := by
    rw [← hOS]
    rfl
  have hZcomm : ∀ c : ↥Z, ∀ i, (c.1.1 : MulAut ↥Bs) * φ i = φ i * c.1.1 := by
    intro c i
    have hc : act.smul c.1 r = r := c.2
    have hci := congrFun hc i
    change MulAut.conj (c.1.1 : MulAut ↥Bs) (r i) = r i at hci
    have hconj : (c.1.1 : MulAut ↥Bs) * φ i * (c.1.1 : MulAut ↥Bs)⁻¹ = φ i := by
      simpa [MulAut.conj_apply, r] using hci
    calc (c.1.1 : MulAut ↥Bs) * φ i
        = ((c.1.1 : MulAut ↥Bs) * φ i * (c.1.1 : MulAut ↥Bs)⁻¹) *
            (c.1.1 : MulAut ↥Bs) := by group
      _ = φ i * (c.1.1 : MulAut ↥Bs) := by rw [hconj]
  have hcardZ : Nat.card Z ≤ p - 1 :=
    ggResCent_ker_card hp2 hBs hNT hx hx1 hM hC hpair hφ hker hΛ hfin4 hCx_top hCx_stab hZcomm
  calc Nat.card ↥Cx = Nat.card (Set.range F) * Nat.card Z := hOS'
    _ ≤ (Nat.card ↥W * 6) * (p - 1) := Nat.mul_le_mul hcardRange hcardZ
    _ = (p - 1) * 6 * Nat.card ↥W := by ring

theorem ggResCentBoundInput_of_xDichotomy (ha₀ : GGLNoncyclicInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hFix : GGTBFixInput) : GGResCentBoundInput := by
  intro G _ _ p B Bs x L D J y K hH _ hx
  rcases (hX G p B Bs x L D J y K hH).1 with hXL | hXL
  · exact ggResCentBound_of_xDatum ha₀ hFix hH hx hXL
  · exfalso
    obtain ⟨labJ, labX, -, hΛX, -, hLabX, hp7, h5⟩ := hXL
    exact ggSeven_L_absurd hTCJ hRig hH.1 hp7 hH.2.2.2.2.1 hΛX hLabX h5

end CFSG.StandardType

end
