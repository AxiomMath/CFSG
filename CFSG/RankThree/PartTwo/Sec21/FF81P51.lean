module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81P51Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import Certificates.Certificate43

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Matrix
open P51 (V Mat GL4 e)
open scoped IsMulCommutative

namespace P51T

variable {G : Type} [Group G] [Finite G] {B : Subgroup G}

def conjB (n : Nor B) : B →* B where
  toFun x := ⟨(n : G) * x * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 x).mp x.2⟩
  map_one' := by ext; simp
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjB_coe (n : Nor B) (x : B) : (conjB n x : G) = (n : G) * x * (n : G)⁻¹ := rfl

variable [IsElementaryAbelian 3 B]

def conjL (n : Nor B) : Additive B →ₗ[ZMod 3] Additive B :=
  (MonoidHom.toAdditive (conjB n)).toZModLinearMap 3

theorem conjL_apply (n : Nor B) (x : B) :
    conjL n (Additive.ofMul x) = Additive.ofMul (conjB n x) := rfl

variable (β : Module.Basis (Fin 4) (ZMod 3) (Additive B))

noncomputable def ρM (n : Nor B) : Mat := LinearMap.toMatrix β β (conjL n)

noncomputable def ρ : Nor B →* Mat where
  toFun := ρM β
  map_one' := by
    have : conjL (B := B) 1 = LinearMap.id := LinearMap.ext fun x => by
      change Additive.ofMul (conjB 1 (Additive.toMul x)) = x
      apply Additive.toMul.injective
      ext; simp [conjB_coe]
    rw [ρM, this, LinearMap.toMatrix_id]
  map_mul' n m := by
    have : conjL (n * m) = (conjL n).comp (conjL m) := LinearMap.ext fun x => by
      change Additive.ofMul (conjB (n * m) (Additive.toMul x)) =
        Additive.ofMul (conjB n (conjB m (Additive.toMul x)))
      apply Additive.toMul.injective
      ext; simp only [toMul_ofMul, conjB_coe, Subgroup.coe_mul, _root_.mul_inv_rev]; group
    rw [ρM, ρM, ρM, this, LinearMap.toMatrix_comp β β β]

noncomputable def ρU : Nor B →* GL4 := (ρ β).toHomUnits

theorem coe_ρU (n : Nor B) : ((ρU β n : GL4) : Mat) = ρM β n := rfl

noncomputable def cv (x : B) : V := β.equivFun (Additive.ofMul x)

theorem ρM_mulVec (n : Nor B) (x : B) : ρM β n *ᵥ cv β x = cv β (conjB n x) := by
  have := LinearMap.toMatrix_mulVec_repr β β (conjL n) (Additive.ofMul x)
  unfold ρM
  simpa [cv, Module.Basis.equivFun_apply, conjL_apply] using this

theorem cv_mul (x y : B) : cv β (x * y) = cv β x + cv β y := by
  simp [cv, ofMul_mul]

theorem cv_inv (x : B) : cv β x⁻¹ = -cv β x := by
  simp only [cv, ofMul_inv, map_neg]

theorem cv_one : cv β 1 = 0 := by simp [cv]

theorem cv_zpow (x : B) (k : ℤ) : cv β (x ^ k) = k • cv β x := by simp [cv, ofMul_zpow]

theorem cv_inj : Function.Injective (cv β) :=
  β.equivFun.injective.comp Additive.ofMul.injective

noncomputable def vB (v : V) : B := Additive.toMul (β.equivFun.symm v)

theorem cv_vB (v : V) : cv β (vB β v) = v := by
  simp only [cv, vB, ofMul_toMul, LinearEquiv.apply_symm_apply]

theorem vB_cv (x : B) : vB β (cv β x) = x := cv_inj β (cv_vB β _)

theorem cv_basis (i : Fin 4) : cv β (Additive.toMul (β i)) = e i := by
  ext j
  simp only [cv, ofMul_toMul, Module.Basis.equivFun_self, e, Pi.single_apply]
  split_ifs <;> simp_all [eq_comm]

theorem exists_basis {b₀ b₁ b₂ b₃ : G} (hcard : Nat.card B = 3 ^ 4)
    (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) :
    ∃ β : Module.Basis (Fin 4) (ZMod 3) (Additive B),
      ∀ i, ((Additive.toMul (β i) : B) : G) = ![b₀, b₁, b₂, b₃] i := by
  have hmem : ∀ i, ![b₀, b₁, b₂, b₃] i ∈ B := by
    intro i; rw [hcl]; apply Subgroup.subset_closure; fin_cases i <;> simp
  let f : Fin 4 → Additive B := fun i => Additive.ofMul ⟨_, hmem i⟩
  let K : Subgroup G :=
    { carrier := {g | ∃ h : g ∈ B, Additive.ofMul (⟨g, h⟩ : B) ∈ Submodule.span (ZMod 3) (Set.range f)}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        exact ⟨B.mul_mem hx hy, by
          have := Submodule.add_mem _ hx' hy'
          rwa [← ofMul_mul] at this⟩
      one_mem' := ⟨B.one_mem, by
        have := Submodule.zero_mem (Submodule.span (ZMod 3) (Set.range f))
        rwa [← ofMul_one] at this⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        exact ⟨B.inv_mem hx, by
          have := Submodule.neg_mem _ hx'
          rwa [← ofMul_inv] at this⟩ }
  have hK : B ≤ K := by
    rw [hcl, Subgroup.closure_le]
    intro g hg
    have : ∃ i, ![b₀, b₁, b₂, b₃] i = g := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
    obtain ⟨i, rfl⟩ := this
    exact ⟨hmem i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hsp : ⊤ ≤ Submodule.span (ZMod 3) (Set.range f) := by
    rintro x -
    have hx : ∃ h : ((Additive.toMul x : B) : G) ∈ B,
        Additive.ofMul (⟨_, h⟩ : B) ∈ Submodule.span (ZMod 3) (Set.range f) :=
      hK (Additive.toMul x).2
    obtain ⟨_, hx⟩ := hx
    exact hx
  haveI : Module.Finite (ZMod 3) (Additive B) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 3) (Additive B) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive B)
    rw [Nat.card_zmod, show Nat.card (Additive B) = Nat.card B from rfl, hcard] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have hli : LinearIndependent (ZMod 3) f :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by rw [hfin]; rfl)
  exact ⟨Module.Basis.mk hli hsp, fun i => by rw [Module.Basis.mk_apply]; rfl⟩

theorem ker_ρU : (ρU β).ker = (CenS B).subgroupOf (Nor B) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hn x hx
    have h1 : ρM β n = 1 := by rw [← coe_ρU, hn]; rfl
    have := ρM_mulVec β n ⟨x, hx⟩
    rw [h1, Matrix.one_mulVec] at this
    have h2 := congrArg Subtype.val (cv_inj β this)
    simp only [conjB_coe] at h2
    calc x * n = (n : G) * x * (n : G)⁻¹ * n := by rw [← h2]
      _ = n * x := by group
  · intro hn
    apply Units.ext
    rw [coe_ρU, Units.val_one]
    have : conjL (B := B) n = LinearMap.id := LinearMap.ext fun x => by
      change Additive.ofMul (conjB n (Additive.toMul x)) = x
      apply Additive.toMul.injective
      ext
      simp only [toMul_ofMul, conjB_coe, LinearMap.id_apply]
      rw [← hn _ (Additive.toMul x).2]; group
    rw [ρM, this, LinearMap.toMatrix_id]

theorem autOrder_eq : autOrder B = Nat.card (ρU β).range := by
  rw [autOrder, Subgroup.relIndex, ← ker_ρU β, Subgroup.index_ker]

noncomputable def cvG (g : G) : V := by
  classical exact if h : g ∈ B then cv β ⟨g, h⟩ else 0

theorem cvG_of_mem {g : G} (h : g ∈ B) : cvG β g = cv β ⟨g, h⟩ := by
  classical simp [cvG, h]

theorem cvG_inj {g g' : G} (hg : g ∈ B) (hg' : g' ∈ B) (h : cvG β g = cvG β g') : g = g' := by
  rw [cvG_of_mem β hg, cvG_of_mem β hg'] at h
  exact congrArg Subtype.val (cv_inj β h)

theorem cvG_mul {g g' : G} (hg : g ∈ B) (hg' : g' ∈ B) :
    cvG β (g * g') = cvG β g + cvG β g' := by
  rw [cvG_of_mem β (B.mul_mem hg hg'), cvG_of_mem β hg, cvG_of_mem β hg', ← cv_mul]; rfl

theorem cvG_inv {g : G} (hg : g ∈ B) : cvG β g⁻¹ = -cvG β g := by
  rw [cvG_of_mem β (B.inv_mem hg), cvG_of_mem β hg, ← cv_inv]; rfl

theorem cvG_one : cvG β (1 : G) = 0 := by
  rw [cvG_of_mem β B.one_mem, ← cv_one β]; rfl

theorem ρM_col (n : Nor B) (i : Fin 4) :
    ρM β n *ᵥ e i = cvG β ((n : G) * ((Additive.toMul (β i) : B) : G) * (n : G)⁻¹) := by
  rw [← cv_basis β i, ρM_mulVec]
  exact (cvG_of_mem β (conjB n (Additive.toMul (β i))).2).symm

noncomputable def Lv (v : V) : Subgroup G := Subgroup.zpowers (vB β v : G)

theorem Lv_neg (v : V) : Lv β (-v) = Lv β v := by
  have : (vB β (-v) : G) = (vB β v : G)⁻¹ := by
    have h := cv_inv β (vB β v)
    rw [cv_vB, ← cv_vB β (-v)] at h
    rw [← cv_inj β h]; rfl
  rw [Lv, Lv, this, Subgroup.zpowers_inv]

theorem smul_cases (c : ZMod 3) (v : V) : c • v = 0 ∨ c • v = v ∨ c • v = -v := by
  have : c = 0 ∨ c = 1 ∨ c = -1 := by revert c; decide
  rcases this with rfl | rfl | rfl
  · simp
  · simp
  · exact Or.inr (Or.inr (neg_one_smul (ZMod 3) v))

theorem Lv_eq {v w : V} (hw : w ≠ 0) (h : Lv β v = Lv β w) : w = v ∨ w = -v := by
  have hmem : (vB β w : G) ∈ Subgroup.zpowers (vB β v : G) := by
    rw [← Lv, h]; exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : vB β v ^ k = vB β w := Subtype.ext (by simpa using hk)
  have := cv_zpow β (vB β v) k
  rw [hk', cv_vB, cv_vB] at this
  replace this : w = (k : ZMod 3) • v := by
    rw [this]; ext i; simp [zsmul_eq_mul]
  rcases smul_cases (k : ZMod 3) v with h0 | h1 | h2
  · exact absurd (this.trans h0) hw
  · exact Or.inl (this.trans h1)
  · exact Or.inr (this.trans h2)

end P51T

open P51T P51 in
theorem P51T.hyp_of {G : Type} [Group G] [Finite G]
    {B : Subgroup G} [IsElementaryAbelian 3 B] {b b₁ b₂ b₃ : G} (hH0 : HasH0 B b b₁ b₂ b₃)
    (hstab : ∀ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b →
      n * b * n⁻¹ ∈ ({b, b⁻¹} : Set G) ∧ ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G))
    (hmeet : ∃ n ∈ Nor B, n * b * n⁻¹ ∈ Subgroup.closure {b₁, b₂, b₃})
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B))
    (hβ : ∀ i, ((Additive.toMul (β i) : B) : G) = ![b, b₁, b₂, b₃] i) :
    Hyp (ρU β).range := by
  obtain ⟨hE, hcl, ⟨n0, hn0, h00, h01, h02, h03⟩, ⟨n1, hn1, h10, h11, h12, h13⟩,
    ⟨n2, hn2, h20, h21, h22, h23⟩, ⟨n3, hn3, h30, h31, h32, h33⟩⟩ := hH0
  set bs : Fin 4 → G := ![b, b₁, b₂, b₃] with hbs
  have hbB : ∀ i, bs i ∈ B := fun i => hβ i ▸ (Additive.toMul (β i)).2
  have hcvb : ∀ i, cvG β (bs i) = e i := fun i => by
    rw [← hβ i, cvG_of_mem β (Additive.toMul (β i)).2]
    exact cv_basis β i
  have hcvbi : ∀ i, cvG β (bs i)⁻¹ = -e i := fun i => by rw [cvG_inv β (hbB i), hcvb]
  have hcol : ∀ (n : G) (hn : n ∈ Nor B) (i : Fin 4),
      ρM β ⟨n, hn⟩ *ᵥ e i = cvG β (n * bs i * n⁻¹) := fun n hn i => by
    rw [ρM_col, hβ i]
  have hconj : ∀ n ∈ Nor B, ∀ x ∈ B, n * x * n⁻¹ ∈ B := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have hmat : ∀ (n : G) (hn : n ∈ Nor B) (c : Fin 4 → V),
      (∀ i, cvG β (n * bs i * n⁻¹) = c i) → ρM β ⟨n, hn⟩ = ofCols c := fun n hn c hc => by
    rw [← ofCols_cols (ρM β ⟨n, hn⟩)]
    congr 1
    funext i
    fin_cases i
    exacts [(hcol n hn 0).trans (hc 0), (hcol n hn 1).trans (hc 1), (hcol n hn 2).trans (hc 2),
      (hcol n hn 3).trans (hc 3)]
  set Γ := (ρU β).range with hΓdef
  have hΓ : ∀ g ∈ Γ, ∃ (n : G) (hn : n ∈ Nor B), (g : Mat) = ρM β ⟨n, hn⟩ := by
    rintro g ⟨⟨n, hn⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  have hρΓ : ∀ (n : G) (hn : n ∈ Nor B), ρU β ⟨n, hn⟩ ∈ Γ := fun n hn => ⟨_, rfl⟩
  have hzp : ∀ n : G, conjBy n (Subgroup.zpowers b) = Subgroup.zpowers (n * b * n⁻¹) := by
    intro n
    rw [conjBy, MonoidHom.map_zpowers]
    rfl
  have hSU : ∀ y ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G), cvG β y ∈ SU := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h | h | h <;> rw [h]
    · rw [show b₁ = bs 1 from rfl, hcvb]; simp [SU]
    · rw [show b₁ = bs 1 from rfl, hcvbi]; simp [SU]
    · rw [show b₂ = bs 2 from rfl, hcvb]; simp [SU]
    · rw [show b₂ = bs 2 from rfl, hcvbi]; simp [SU]
    · rw [show b₃ = bs 3 from rfl, hcvb]; simp [SU]
    · rw [show b₃ = bs 3 from rfl, hcvbi]; simp [SU]
  have hcl0 : ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), y ∈ B ∧ cvG β y 0 = 0 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h <;> rw [h]
      · exact ⟨hbB 1, by rw [show b₁ = bs 1 from rfl, hcvb]; exact e_succ_zero 1 (by decide)⟩
      · exact ⟨hbB 2, by rw [show b₂ = bs 2 from rfl, hcvb]; exact e_succ_zero 2 (by decide)⟩
      · exact ⟨hbB 3, by rw [show b₃ = bs 3 from rfl, hcvb]; exact e_succ_zero 3 (by decide)⟩
    | one => exact ⟨B.one_mem, by rw [cvG_one]; rfl⟩
    | mul x y _ _ hx hy =>
      exact ⟨B.mul_mem hx.1 hy.1, by rw [cvG_mul β hx.1 hy.1, Pi.add_apply, hx.2, hy.2, add_zero]⟩
    | inv x _ hx =>
      exact ⟨B.inv_mem hx.1, by rw [cvG_inv β hx.1, Pi.neg_apply, hx.2]; exact neg_zero⟩
  refine ⟨⟨_, hρΓ n0 hn0, ?_⟩, ⟨_, hρΓ n1 hn1, ?_⟩, ⟨_, hρΓ n2 hn2, ?_⟩, ⟨_, hρΓ n3 hn3, ?_⟩,
    ?_, ?_⟩
  · rw [coe_ρU, hmat n0 hn0 ![-e 0, e 1, e 2, e 3], T0_cols]
    intro i; fin_cases i
    · change cvG β (n0 * b * n0⁻¹) = -e 0; rw [h00]; exact hcvbi 0
    · change cvG β (n0 * b₁ * n0⁻¹) = e 1; rw [h01]; exact hcvb 1
    · change cvG β (n0 * b₂ * n0⁻¹) = e 2; rw [h02]; exact hcvb 2
    · change cvG β (n0 * b₃ * n0⁻¹) = e 3; rw [h03]; exact hcvb 3
  · rw [coe_ρU, hmat n1 hn1 ![e 0, -e 1, e 2, e 3], S1_cols]
    intro i; fin_cases i
    · change cvG β (n1 * b * n1⁻¹) = e 0; rw [h10]; exact hcvb 0
    · change cvG β (n1 * b₁ * n1⁻¹) = -e 1; rw [h11]; exact hcvbi 1
    · change cvG β (n1 * b₂ * n1⁻¹) = e 2; rw [h12]; exact hcvb 2
    · change cvG β (n1 * b₃ * n1⁻¹) = e 3; rw [h13]; exact hcvb 3
  · rw [coe_ρU, hmat n2 hn2 ![e 0, e 2, e 1, e 3], Tau_cols]
    intro i; fin_cases i
    · change cvG β (n2 * b * n2⁻¹) = e 0; rw [h20]; exact hcvb 0
    · change cvG β (n2 * b₁ * n2⁻¹) = e 2; rw [h21]; exact hcvb 2
    · change cvG β (n2 * b₂ * n2⁻¹) = e 1; rw [h22]; exact hcvb 1
    · change cvG β (n2 * b₃ * n2⁻¹) = e 3; rw [h23]; exact hcvb 3
  · rw [coe_ρU, hmat n3 hn3 ![e 0, e 2, e 3, e 1], Cyc_cols]
    intro i; fin_cases i
    · change cvG β (n3 * b * n3⁻¹) = e 0; rw [h30]; exact hcvb 0
    · change cvG β (n3 * b₁ * n3⁻¹) = e 2; rw [h31]; exact hcvb 2
    · change cvG β (n3 * b₂ * n3⁻¹) = e 3; rw [h32]; exact hcvb 3
    · change cvG β (n3 * b₃ * n3⁻¹) = e 1; rw [h33]; exact hcvb 1
  · intro g hg h0
    obtain ⟨n, hn, hgn⟩ := hΓ g hg
    rw [hgn, hcol] at h0 ⊢
    rw [hcol, hcol]
    have hnb : n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹ := by
      rcases h0 with h0 | h0
      · left
        exact cvG_inj β (hconj n hn b (hbB 0)) (hbB 0) (h0.trans (hcvb 0).symm)
      · right
        exact cvG_inj β (hconj n hn b (hbB 0)) (B.inv_mem (hbB 0)) (h0.trans (hcvbi 0).symm)
    have hz : conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b := by
      rw [hzp]
      rcases hnb with h | h <;> rw [h]
      exact Subgroup.zpowers_inv
    obtain ⟨-, hU⟩ := hstab n hn hz
    exact ⟨hSU _ (hU b₁ (by simp)), hSU _ (hU b₂ (by simp)), hSU _ (hU b₃ (by simp))⟩
  · obtain ⟨n, hn, hc⟩ := hmeet
    refine ⟨_, hρΓ n hn, ?_⟩
    rw [coe_ρU, hcol]
    exact (hcl0 _ hc).2

open P51T P51 in
theorem kf_prop51 : KF_Prop51 := by
  intro G _ _ B b b₁ b₂ b₃ hH0 _hodd hstab hmeet
  obtain ⟨hE, hcl, ⟨n0, hn0, h00, h01, h02, h03⟩, ⟨n1, hn1, h10, h11, h12, h13⟩,
    ⟨n2, hn2, h20, h21, h22, h23⟩, ⟨n3, hn3, h30, h31, h32, h33⟩⟩ := hH0
  haveI : IsElementaryAbelian 3 B := hE.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) hE.2 hcl
  set bs : Fin 4 → G := ![b, b₁, b₂, b₃] with hbs
  have hbB : ∀ i, bs i ∈ B := fun i => hβ i ▸ (Additive.toMul (β i)).2
  have hcvb : ∀ i, cvG β (bs i) = e i := fun i => by
    rw [← hβ i, cvG_of_mem β (Additive.toMul (β i)).2]
    exact cv_basis β i
  have hcvbi : ∀ i, cvG β (bs i)⁻¹ = -e i := fun i => by rw [cvG_inv β (hbB i), hcvb]
  have hcol : ∀ (n : G) (hn : n ∈ Nor B) (i : Fin 4),
      ρM β ⟨n, hn⟩ *ᵥ e i = cvG β (n * bs i * n⁻¹) := fun n hn i => by
    rw [ρM_col, hβ i]
  have hconj : ∀ n ∈ Nor B, ∀ x ∈ B, n * x * n⁻¹ ∈ B := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have hmat : ∀ (n : G) (hn : n ∈ Nor B) (c : Fin 4 → V),
      (∀ i, cvG β (n * bs i * n⁻¹) = c i) → ρM β ⟨n, hn⟩ = ofCols c := fun n hn c hc => by
    rw [← ofCols_cols (ρM β ⟨n, hn⟩)]
    congr 1
    funext i
    fin_cases i
    exacts [(hcol n hn 0).trans (hc 0), (hcol n hn 1).trans (hc 1), (hcol n hn 2).trans (hc 2),
      (hcol n hn 3).trans (hc 3)]
  set Γ := (ρU β).range with hΓdef
  have hΓ : ∀ g ∈ Γ, ∃ (n : G) (hn : n ∈ Nor B), (g : Mat) = ρM β ⟨n, hn⟩ := by
    rintro g ⟨⟨n, hn⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  have hρΓ : ∀ (n : G) (hn : n ∈ Nor B), ρU β ⟨n, hn⟩ ∈ Γ := fun n hn => ⟨_, rfl⟩
  have hzp : ∀ n : G, conjBy n (Subgroup.zpowers b) = Subgroup.zpowers (n * b * n⁻¹) := by
    intro n
    rw [conjBy, MonoidHom.map_zpowers]
    rfl
  have hyp : Hyp Γ := P51T.hyp_of ⟨hE, hcl, ⟨n0, hn0, h00, h01, h02, h03⟩,
    ⟨n1, hn1, h10, h11, h12, h13⟩, ⟨n2, hn2, h20, h21, h22, h23⟩, ⟨n3, hn3, h30, h31, h32, h33⟩⟩
    hstab hmeet β hβ
  have hgood := cfgOf_good hyp
  have hcard := card_eq hyp
  have haut : autOrder B = Nat.card Γ := autOrder_eq β
  have homneg : ∀ v ∈ Om Γ, -v ∈ Om Γ := by
    rintro v ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htT⟩ := hyp.t0
    refine ⟨g * t, Γ.mul_mem hg ht, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, htT, T0_e0, Matrix.mulVec_neg]
  have hOm : ∀ m : Fin 7 → Bool, (cfgOf Γ).1 = m →
      Om Γ = ↑((nonzeroL.filter fun v => m (tab v).1).toFinset) := by
    intro m hm
    ext v
    rw [om_iff hyp, hm]
    simp
  have hlines : {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D} = Lv β '' Om Γ := by
    ext D
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨ρM β ⟨n, hn⟩ *ᵥ e 0, ⟨_, hρΓ n hn, rfl⟩, ?_⟩
      rw [hcol, Lv, hzp, cvG_of_mem β (hconj n hn _ (hbB 0)), vB_cv]
      rfl
    · rintro ⟨v, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨n, hn, hgn⟩ := hΓ g hg
      refine ⟨n, hn, ?_⟩
      rw [hgn, hcol, Lv, hzp, cvG_of_mem β (hconj n hn _ (hbB 0)), vB_cv]
      rfl
  have hncard : ∀ m : Fin 7 → Bool, (cfgOf Γ).1 = m →
      {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D}.ncard = lineCount m := by
    intro m hm
    rw [hlines]
    have himg : Lv β '' Om Γ = Lv β '' (Om Γ ∩ {v | pos v = true}) := by
      apply le_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        have hn := mem_nonzeroL _ (ne_zero_of_mem_Om hv)
        rcases pos_or v hn with hp | hp
        · exact ⟨v, ⟨hv, hp⟩, rfl⟩
        · exact ⟨-v, ⟨homneg v hv, hp⟩, Lv_neg β v⟩
      · exact Set.image_mono Set.inter_subset_left
    have hinj : Set.InjOn (Lv β) (Om Γ ∩ {v | pos v = true}) := by
      rintro v ⟨hv, hpv⟩ w ⟨hw, hpw⟩ hvw
      rcases Lv_eq β (ne_zero_of_mem_Om hw) hvw with h | h
      · exact h.symm
      · exfalso
        exact not_pos_and v (mem_nonzeroL _ (ne_zero_of_mem_Om hv)) ⟨hpv, h ▸ hpw⟩
    rw [himg, hinj.ncard_image, lineCount]
    have : Om Γ ∩ {v | pos v = true} =
        ↑((nonzeroL.filter fun v => m (tab v).1 && pos v).toFinset) := by
      rw [hOm m hm]
      ext v
      simp [and_assoc]
    rw [this, Set.ncard_coe_finset]
  have hautm : ∀ m : Fin 7 → Bool, (m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE) →
      (cfgOf Γ).1 = m → autOrder B = 96 * lineCount m := by
    intro m hm hcm
    rw [haut, hcard, hOm m hcm, Set.ncard_coe_finset, vecCount m hm]
    ring
  have hfromMat : ∀ A ∈ GM Γ, ∀ σ : Fin 4 → Fin 4, (∀ j, A *ᵥ e j = e (σ j)) →
      ∃ n ∈ Nor B, ∀ j, n * bs j * n⁻¹ = bs (σ j) := by
    intro A hA σ hσ
    obtain ⟨g, hg, rfl⟩ := mem_GM.1 hA
    obtain ⟨n, hn, hgn⟩ := hΓ g hg
    refine ⟨n, hn, fun j => ?_⟩
    have := hσ j
    rw [hgn, hcol, ← hcvb (σ j)] at this
    exact cvG_inj β (hconj n hn _ (hbB j)) (hbB _) this
  have hmono : Sig01 ∈ GM Γ → HasMonomial4 B b b₁ b₂ b₃ := by
    intro hs
    obtain ⟨ns, hns, hs'⟩ := hfromMat _ hs ![1, 0, 2, 3] fun j => by
      fin_cases j
      exacts [Sig01_cols.1, Sig01_cols.2.1, Sig01_cols.2.2.1, Sig01_cols.2.2.2]
    obtain ⟨nc, hnc, hc'⟩ := hfromMat _ (cyc4_of_sig01 hyp hs) ![1, 2, 3, 0] fun j => by
      fin_cases j
      exacts [Cyc4_cols.1, Cyc4_cols.2.1, Cyc4_cols.2.2.1, Cyc4_cols.2.2.2]
    exact ⟨hE, hcl, ⟨n0, hn0, h00, h01, h02, h03⟩, ⟨ns, hns, hs' 0, hs' 1, hs' 2, hs' 3⟩,
      ⟨nc, hnc, hc' 0, hc' 1, hc' 2, hc' 3⟩⟩
  have hq8 : ∀ m : Fin 7 → Bool, (cfgOf Γ).1 = m → m 6 = true →
      ∃ n ∈ Nor B, n * b * n⁻¹ = b * b₁ * b₂ * b₃ := by
    intro m hm h6
    have hr : rep 6 ∈ Om Γ := by
      rw [om_iff hyp, tab_rep, hm]
      exact ⟨mem_nonzeroL _ (rep_ne_zero 6), h6⟩
    obtain ⟨g, hg, hge⟩ := hr
    obtain ⟨n, hn, hgn⟩ := hΓ g hg
    refine ⟨n, hn, ?_⟩
    rw [hgn, hcol, rep_six] at hge
    have hm1 := B.mul_mem (B.mul_mem (hbB 0) (hbB 1)) (hbB 2)
    refine cvG_inj β (hconj n hn _ (hbB 0)) (B.mul_mem hm1 (hbB 3)) ?_
    change cvG β (n * bs 0 * n⁻¹) = cvG β (bs 0 * bs 1 * bs 2 * bs 3)
    rw [hge, cvG_mul β hm1 (hbB 3), cvG_mul β (B.mul_mem (hbB 0) (hbB 1)) (hbB 2),
      cvG_mul β (hbB 0) (hbB 1)]
    change e 0 + e 1 + e 2 + e 3 = cvG β (bs 0) + cvG β (bs 1) + cvG β (bs 2) + cvG β (bs 3)
    rw [hcvb, hcvb, hcvb, hcvb]
  rcases hgood with hA | ⟨hB', hW⟩ | ⟨hC, hW⟩ | hD | hE'
  ·
    left
    have hFr : ∀ y ∈ B, cvG β y ∈ Fr8 →
        y ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
      intro y hy hc
      simp only [Fr8, List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hc with hc | hc | hc | hc | hc | hc | hc | hc
      · exact Or.inl (cvG_inj β hy (hbB 0) (hc.trans (hcvb 0).symm))
      · exact Or.inr (Or.inl (cvG_inj β hy (B.inv_mem (hbB 0)) (hc.trans (hcvbi 0).symm)))
      · exact Or.inr (Or.inr (Or.inl (cvG_inj β hy (hbB 1) (hc.trans (hcvb 1).symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (cvG_inj β hy (B.inv_mem (hbB 1)) (hc.trans (hcvbi 1).symm)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (cvG_inj β hy (hbB 2) (hc.trans (hcvb 2).symm))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (cvG_inj β hy (B.inv_mem (hbB 2)) (hc.trans (hcvbi 2).symm)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (cvG_inj β hy (hbB 3) (hc.trans (hcvb 3).symm))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (cvG_inj β hy (B.inv_mem (hbB 3)) (hc.trans (hcvbi 3).symm))))))))
    have hmon : ∀ n ∈ Nor B, ∀ j : Fin 4,
        n * bs j * n⁻¹ ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
      intro n hn j
      have := mon_of_mA hyp hA (hρΓ n hn) j
      rw [coe_ρU, hcol] at this
      exact hFr _ (hconj n hn _ (hbB j)) this
    refine ⟨⟨hmono (sig01_of_mA hyp hA), fun n hn x hx => ?_⟩, ?_, fun n hn D hD => ?_⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [hmon n hn 0, hmon n hn 1, hmon n hn 2, hmon n hn 3]
    · rw [hautm mA (Or.inl rfl) hA, lineCount_mA]
    · rw [hD, hzp]
      have := hmon n hn 0
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
      rcases this with h | h | h | h | h | h | h | h <;> rw [show bs 0 = b from rfl] at h <;>
        rw [h] <;> simp [Subgroup.zpowers_inv]
  · right; left
    exact ⟨hmono (sig01_of_W hyp hW), by rw [hautm mB (by simp) hB', lineCount_mB],
      by rw [hncard mB hB', lineCount_mB], hq8 mB hB' rfl⟩
  · right; right; left
    exact ⟨hmono (sig01_of_W hyp hW), by rw [hautm mC (by simp) hC, lineCount_mC],
      by rw [hncard mC hC, lineCount_mC], hq8 mC hC rfl⟩
  · right; right; right; left
    exact ⟨by rw [hautm mD (by simp) hD, lineCount_mD], by rw [hncard mD hD, lineCount_mD]⟩
  · right; right; right; right
    exact ⟨by rw [hautm mE (by simp) hE', lineCount_mE], by rw [hncard mE hE', lineCount_mE]⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
