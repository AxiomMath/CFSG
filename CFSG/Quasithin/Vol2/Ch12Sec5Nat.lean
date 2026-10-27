module

public import CFSG.Quasithin.Vol2.Ch12Sec5L2G
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.Background.SmithB51LnReal
public import CFSG.Quasithin.Background.F918F1
public import CFSG.Quasithin.Background.JonesParshallNatural
public import CFSG.Quasithin.Background.SmithB51LnAut
public import CFSG.Quasithin.Background.SmithB51SL3Common

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125Tr2 S125Tr3 S125W Matrix
open CFSG.LieType.SteinbergBR.BlockPar
open scoped IsMulCommutative

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125Nat

theorem mulVec_apply_of_supp (N : Matrix (Fin 10) (Fin 10) (ZMod 2)) {m : ℕ} {c : Fin m → Fin 10}
    (hc : Function.Injective c) {S : Finset (Fin 10)} (hSc : ∀ k ∈ S, ∃ i, c i = k)
    {x : Fin 10 → ZMod 2} (hx : ∀ k ∉ S, x k = 0) (k : Fin 10) :
    (N *ᵥ x) k = ∑ i, N k (c i) * x (c i) := by
  rw [Matrix.mulVec, dotProduct, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image c)),
    Finset.sum_image fun i _ j _ h => hc h]
  intro l _ hl
  have hlS : l ∉ S := fun hlS => by
    obtain ⟨i, rfl⟩ := hSc l hlS
    exact hl (Finset.mem_image_of_mem c (Finset.mem_univ i))
  rw [hx l hlS, mul_zero]

theorem wedgeMat_mulVec_congr {M M' : Matrix (Fin 5) (Fin 5) (ZMod 2)} {S : Finset (Fin 10)}
    {x : Fin 10 → ZMod 2} (hx : ∀ k ∉ S, x k = 0)
    (h : ∀ k, ∀ l ∈ S, JonesParshall.wedgeMat M k l = JonesParshall.wedgeMat M' k l) :
    JonesParshall.wedgeMat M *ᵥ x = JonesParshall.wedgeMat M' *ᵥ x := by
  funext k
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ S
  · rw [h k l hl]
  · rw [hx l hl, mul_zero, mul_zero]

theorem wedgeMat_eq_of_cols {M M' : Matrix (Fin 5) (Fin 5) (ZMod 2)} {d : ℕ}
    (h : ∀ a b : Fin 5, b.val < d → M a b = M' a b) (k l : Fin 10)
    (hl : (JonesParshall.pr5 l).2.val < d) :
    JonesParshall.wedgeMat M k l = JonesParshall.wedgeMat M' k l := by
  have hl1 : (JonesParshall.pr5 l).1.val < d :=
    lt_trans (show (JonesParshall.pr5 l).1.val < (JonesParshall.pr5 l).2.val from pr5_lt l) hl
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, h _ _ hl, h _ _ hl1]

theorem wedgeMat_eq_of_col0 {M M' : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (h0 : ∀ a, M a 0 = M' a 0) (hz : ∀ a : Fin 5, a ≠ 0 → M a 0 = 0)
    (h1 : ∀ a b : Fin 5, a ≠ 0 → b ≠ 0 → M a b = M' a b) (k l : Fin 10)
    (hl : (JonesParshall.pr5 l).1 = 0) :
    JonesParshall.wedgeMat M k l = JonesParshall.wedgeMat M' k l := by
  have hk := pr5_lt k
  have hl2 := pr5_lt l
  have hk2 : (JonesParshall.pr5 k).2 ≠ 0 := fun h => by
    rw [h] at hk
    exact absurd hk (Fin.not_lt_zero _)
  have hl2' : (JonesParshall.pr5 l).2 ≠ 0 := fun h => by
    rw [h, hl] at hl2
    exact absurd hl2 (lt_irrefl _)
  have e1 : M (JonesParshall.pr5 k).2 0 = 0 := hz _ hk2
  have e2 : M' (JonesParshall.pr5 k).2 0 = 0 := (h0 _).symm.trans e1
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, hl]
  rw [e1, e2, h0 (JonesParshall.pr5 k).1, h1 _ _ hk2 hl2', mul_zero, mul_zero]

theorem reindex_apply {d e : ℕ} (hde : d + e = 5)
    (g : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) (a b : Fin 5) :
    (reindexSL (ZMod 2) hde g).val a b =
      g.val ((sumEquiv hde).symm a) ((sumEquiv hde).symm b) := by
  rw [reindexSL_val, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem reindex_castLE {d e : ℕ} (hde : d + e = 5) (hd : d ≤ 5)
    (g : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) (a b : Fin d) :
    (reindexSL (ZMod 2) hde g).val (Fin.castLE hd a) (Fin.castLE hd b) =
      g.val (Sum.inl a) (Sum.inl b) := by
  rw [reindex_apply, sumEquiv_symm_of_lt hde (show (Fin.castLE hd a).val < d from a.2),
    sumEquiv_symm_of_lt hde (show (Fin.castLE hd b).val < d from b.2)]
  rfl

theorem reindex_col_eq {d e : ℕ} (hde : d + e = 5)
    {g g' : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)}
    (hg : g ∈ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))))
    (hg' : g' ∈ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))))
    (h11 : g.val.toBlocks₁₁ = g'.val.toBlocks₁₁) (a b : Fin 5) (hb : b.val < d) :
    (reindexSL (ZMod 2) hde g).val a b = (reindexSL (ZMod 2) hde g').val a b := by
  rw [reindex_apply, reindex_apply, sumEquiv_symm_of_lt hde hb]
  by_cases ha : a.val < d
  · rw [sumEquiv_symm_of_lt hde ha]
    exact congrFun₂ h11 ⟨a.val, ha⟩ ⟨b.val, hb⟩
  · rw [sumEquiv_symm_of_le hde (not_lt.1 ha)]
    have h1 : g.val.toBlocks₂₁ = 0 := hg
    have h2 : g'.val.toBlocks₂₁ = 0 := hg'
    exact (congrFun₂ h1 ⟨a.val - d, by omega⟩ ⟨b.val, hb⟩).trans
      (congrFun₂ h2 ⟨a.val - d, by omega⟩ ⟨b.val, hb⟩).symm

theorem sumEquiv14_zero : (sumEquiv (show 1 + 4 = 5 by norm_num)).symm 0 = Sum.inl 0 :=
  sumEquiv_symm_of_lt _ (show (0 : Fin 5).val < 1 by decide)

theorem sumEquiv14_succ (i : Fin 4) :
    (sumEquiv (show 1 + 4 = 5 by norm_num)).symm i.succ = Sum.inr i := by
  rw [sumEquiv_symm_of_le _ (show 1 ≤ i.succ.val by simp)]
  exact congrArg Sum.inr (Fin.ext (by simp))

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def coordHomV (F : Frame125 T L V) {m : ℕ} (c : Fin m → Fin 10) :
    ↥V →* Multiplicative (Fin m → ZMod 2) where
  toFun v := Multiplicative.ofAdd fun i => Multiplicative.toAdd (F.e v) (c i)
  map_one' := by
    rw [map_one]
    rfl
  map_mul' v w := by
    rw [map_mul]
    rfl

omit [Finite G] in
theorem isMulCommutative_sub (hV : IsMulCommutative ↥V) {W : Subgroup G} (hWV : W ≤ V) :
    IsMulCommutative ↥W :=
  ⟨⟨fun a b => Subtype.ext (by
    have := congrArg Subtype.val (hV.is_comm.comm ⟨a, hWV a.2⟩ ⟨b, hWV b.2⟩)
    exact this)⟩⟩

theorem realizes_sub_coord {D : FFModel} (hs : D.sec = ⊤) (hk : D.ker = ⊥)
    (hact : ∀ γ, D.act γ 1 = 1) (F : Frame125 T L V) (hf : S125Ex.Facts125 G T L V)
    {S : Finset (Fin 10)} {d e : ℕ} (hde : d + e = 5) (hstab : F.IsStab (mi T L (F.sub S)) d)
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))}
    (hres : (CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2)))).map parQ.subtype = J)
    [IsMulCommutative ↥(F.sub S)] {m : ℕ} (c : Fin m → Fin 10) (hc : Function.Injective c)
    (hcS : ∀ i, c i ∈ S) (hSc : ∀ k ∈ S, ∃ i, c i = k)
    (ψ : Multiplicative (Fin m → ZMod 2) ≃* D.Amb) (φ : D.Gam →* ↥J)
    (hequiv : ∀ γ (x : Fin 10 → ZMod 2), (∀ k ∉ S, x k = 0) →
      ψ (Multiplicative.ofAdd fun i => (JonesParshall.wedgeMat
        ((reindexSL (ZMod 2) hde (φ γ : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) :
          SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) (c i)) =
        D.act γ (ψ (Multiplicative.ofAdd fun i => x (c i))))
    (hsurj : ∀ j ∈ J, ∃ γ, ∀ x : Fin 10 → ZMod 2, (∀ k ∉ S, x k = 0) →
      JonesParshall.wedgeMat ((reindexSL (ZMod 2) hde j : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2))
        *ᵥ x = JonesParshall.wedgeMat ((reindexSL (ZMod 2) hde
          (φ γ : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) : SL5) :
            Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) :
    D.Realizes (V := ↥(F.sub S)) (autOn (li L (F.sub S)) (F.sub S)) ⊤ ⊥ := by
  set W := F.sub S with hW
  have hWV : W ≤ V := sub_le F S
  have hXL : li L W ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXV : li L W ≤ Subgroup.normalizer (V : Set G) := hXL.trans hf.normalizes
  have hXW : li L W ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hLb := lbar_eq F hf.normalizes hf.T_le hde hstab hres
  let πV : ↥J →* ↥(autOn (li L W) V) :=
    { toFun := fun j => ⟨theta F hde j, by rw [hLb]; exact ⟨j, j.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  let res := Vol2.Ch11.SecC.B51.resAutOn hXV hXW hWV
  let π : D.Gam →* ↥(autOn (li L W) W) := res.comp (πV.comp φ)
  have hπ : ∀ γ (u : ↥W), ((((π γ : ↥(autOn (li L W) W)) : MulAut ↥W) u : ↥W) : G) =
      ((theta F hde (φ γ : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))
        ⟨u, hWV u.2⟩ : ↥V) : G) := fun γ u =>
    Vol2.Ch11.SecC.B51.resAutOn_apply hXV hXW hWV _ u
  let βV : ↥V →* D.Amb := ψ.toMonoidHom.comp (coordHomV F c)
  have hβV : ∀ v : ↥V,
      βV v = ψ (Multiplicative.ofAdd fun i => Multiplicative.toAdd (F.e v) (c i)) :=
    fun _ => rfl
  have hsupp : ∀ v : ↥V, (v : G) ∈ W → ∀ k ∉ S, Multiplicative.toAdd (F.e v) k = 0 :=
    fun v hv => (mem_sub_iff F S v).1 hv
  let β : ↥(⊤ : Subgroup ↥W) →* D.Amb :=
    (βV.comp (Subgroup.inclusion hWV)).comp (⊤ : Subgroup ↥W).subtype
  have hβ : ∀ u : ↥(⊤ : Subgroup ↥W), β u = βV ⟨((u : ↥W) : G), hWV (u : ↥W).2⟩ := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro σ
    obtain ⟨τ, rfl⟩ := Vol2.Ch11.SecC.B51.resAutOn_surjective hXV hXW hWV σ
    have hτ : (τ : MulAut ↥V) ∈ J.map (theta F hde) := hLb ▸ τ.2
    obtain ⟨j, hj, hjτ⟩ := hτ
    obtain ⟨γ, hγ⟩ := hsurj j hj
    refine ⟨γ, Subtype.ext (MulEquiv.ext fun u => Subtype.ext ?_)⟩
    rw [hπ, Vol2.Ch11.SecC.B51.resAutOn_apply hXV hXW hWV τ u, ← hjτ]
    congr 1
    apply F.e.injective
    rw [e_theta_apply, e_theta_apply, hγ _ (hsupp _ u.2)]
  have hβs : Function.Surjective β := by
    intro y
    set z := Multiplicative.toAdd (ψ.symm y)
    let x : Fin 10 → ZMod 2 := fun k => ∑ i, if c i = k then z i else 0
    have hxc : ∀ i, x (c i) = z i := by
      intro i
      change (∑ i', if c i' = c i then z i' else 0) = z i
      rw [Finset.sum_eq_single i (fun i' _ hi' => ite_eq_right fun h => hi' (hc h))
        (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl]
    have hxS : ∀ k ∉ S, x k = 0 := by
      intro k hk
      exact Finset.sum_eq_zero fun i _ => ite_eq_right fun (h : c i = k) => hk (h ▸ hcS i)
    let v : ↥V := F.e.symm (Multiplicative.ofAdd x)
    have hvW : (v : G) ∈ W := (mem_sub_iff F S v).2 (by
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact hxS)
    refine ⟨⟨⟨v, hvW⟩, trivial⟩, ?_⟩
    rw [hβ, hβV]
    change ψ (Multiplicative.ofAdd fun i => Multiplicative.toAdd (F.e v) (c i)) = y
    have : (fun i => Multiplicative.toAdd (F.e v) (c i)) = z := by
      funext i
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, hxc]
    rw [this, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hβk : ∀ u : ↥(⊤ : Subgroup ↥W), β u = 1 ↔ (u : ↥W) ∈ (⊥ : Subgroup ↥W) := by
    intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h1
      rw [hβ, hβV, ← map_one ψ, ψ.injective.eq_iff] at h1
      have h2 : ∀ i, Multiplicative.toAdd (F.e ⟨((u : ↥W) : G), hWV (u : ↥W).2⟩) (c i) = 0 :=
        fun i => congrFun (congrArg Multiplicative.toAdd h1) i
      have h3 : F.e ⟨((u : ↥W) : G), hWV (u : ↥W).2⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        funext k
        by_cases hkS : k ∈ S
        · obtain ⟨i, rfl⟩ := hSc k hkS
          rw [h2 i]
          rfl
        · rw [hsupp _ (u : ↥W).2 k hkS]
          rfl
      have h4 : (⟨((u : ↥W) : G), hWV (u : ↥W).2⟩ : ↥V) = 1 := by
        rw [← map_one F.e.symm, ← h3, MulEquiv.symm_apply_apply]
      exact Subtype.ext (congrArg (fun z : ↥V => (z : G)) h4)
    · intro h1
      rw [hβ]
      have : (⟨((u : ↥W) : G), hWV (u : ↥W).2⟩ : ↥V) = 1 := Subtype.ext (by rw [h1]; rfl)
      rw [this, map_one]
  have hβe : ∀ (γ : D.Gam) (u : ↥(⊤ : Subgroup ↥W))
      (hu : ((π γ : ↥(autOn (li L W) W)) : MulAut ↥W) (u : ↥W) ∈ (⊤ : Subgroup ↥W)),
      β ⟨((π γ : ↥(autOn (li L W) W)) : MulAut ↥W) (u : ↥W), hu⟩ = D.act γ (β u) := by
    intro γ u hu
    rw [hβ, hβ]
    have e1 : (⟨((((π γ : ↥(autOn (li L W) W)) : MulAut ↥W) (u : ↥W) : ↥W) : G),
        hWV (((π γ : ↥(autOn (li L W) W)) : MulAut ↥W) (u : ↥W)).2⟩ : ↥V) =
        theta F hde (φ γ : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))
          ⟨((u : ↥W) : G), hWV (u : ↥W).2⟩ := Subtype.ext (hπ γ u)
    rw [e1, hβV, hβV, e_theta_apply, toAdd_ofAdd]
    exact hequiv γ _ (hsupp _ (u : ↥W).2)
  refine ⟨π, B5.Ln.realizesVia_of_coord hs hk hact hπs bot_le (fun _ _ _ => trivial) ?_ β hβs
    hβk hβe⟩
  intro h z hz
  rw [Subgroup.mem_bot] at hz ⊢
  rw [hz, map_one]

noncomputable abbrev eSL (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) :=
  CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)

theorem coe_eSL_symm (n : ℕ) (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) :
    (((eSL n).symm γ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = B5.Ln.mat γ := by
  conv_rhs => rw [← (eSL n).apply_symm_apply γ]
  rfl

theorem natAct_one (n : ℕ) (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) :
    natAct (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) γ 1 = 1 := by
  show Multiplicative.ofAdd (_ *ᵥ Multiplicative.toAdd (1 : Multiplicative _)) = 1
  rw [toAdd_one, Matrix.mulVec_zero]
  rfl

@[expose] def c4 : Fin 4 → Fin 10 := ![0, 1, 2, 3]

theorem c4_injective : Function.Injective c4 := by decide

theorem c4_mem : ∀ i, c4 i ∈ ({0, 1, 2, 3} : Finset (Fin 10)) := by decide

theorem c4_surj : ∀ k ∈ ({0, 1, 2, 3} : Finset (Fin 10)), ∃ i, c4 i = k := by decide

theorem pr5_c4 : ∀ i, JonesParshall.pr5 (c4 i) = (0, i.succ) := by decide

theorem pr5_S4 : ∀ l ∈ ({0, 1, 2, 3} : Finset (Fin 10)), (JonesParshall.pr5 l).1 = 0 := by decide

theorem levR14_apply (D : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ((reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5) (levR (ZMod 2) (Fin 1) D) : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0 = 1 ∧
    (∀ l : Fin 4, ((reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5) (levR (ZMod 2) (Fin 1) D) : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 l.succ = 0) ∧
    (∀ i : Fin 4, ((reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5) (levR (ZMod 2) (Fin 1) D) : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) i.succ 0 = 0) ∧
    ∀ i l : Fin 4, ((reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5) (levR (ZMod 2) (Fin 1) D) :
      SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) i.succ l.succ = D.val i l := by
  refine ⟨?_, fun l => ?_, fun i => ?_, fun i l => ?_⟩ <;>
    simp only [reindex_apply, sumEquiv14_zero, sumEquiv14_succ, levR_val,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq, Matrix.zero_apply]

@[expose] noncomputable def phi4 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) →*
    ↥(parJR (ZMod 2) (Fin 1) (Fin 4)) :=
  ((levR (ZMod 2) (Fin 1)).comp (eSL 4).symm.toMonoidHom).codRestrict _
    fun _ => levR_mem_parJR _

theorem wedge_c4 (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) (i l : Fin 4) :
    JonesParshall.wedgeMat ((reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5)
      (phi4 γ : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 4) (ZMod 2)) : SL5) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) (c4 i) (c4 l) = B5.Ln.mat γ i l := by
  obtain ⟨h00, h0l, hi0, hil⟩ := levR14_apply ((eSL 4).symm γ)
  change JonesParshall.wedgeMat ((reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5)
    (levR (ZMod 2) (Fin 1) ((eSL 4).symm γ)) : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      (c4 i) (c4 l) = _
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, pr5_c4]
  rw [h00, h0l, hi0, hil, coe_eSL_symm, one_mul, mul_zero, sub_zero]

theorem part3_nat (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ∃ _ : IsMulCommutative ↥F.V4,
      BinaryNaturalSL (V := ↥F.V4) (autOn (li L F.V4) F.V4) ⊤ ⊥ 4 1 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V4 F hf.normalizes hf.T_le
  have hres := S125L2G.hres_of parJR_le_parQ S125Pb.perfectResidual_parQ14
  have hcomm : IsMulCommutative ↥(F.sub {0, 1, 2, 3}) := isMulCommutative_sub hf.comm (sub_le F _)
  refine ⟨hcomm, ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ?_⟩
  refine realizes_sub_coord (D := FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)))
    rfl rfl (natAct_one 4) F hf (by norm_num : 1 + 4 = 5) hst hres c4 c4_injective c4_mem c4_surj
    (MulEquiv.refl _) phi4 (fun γ x hx => ?_) (fun j hj => ?_)
  · change Multiplicative.ofAdd (fun i => (JonesParshall.wedgeMat ((reindexSL (ZMod 2) _
        (levR (ZMod 2) (Fin 1) ((eSL 4).symm γ)) : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x)
          (c4 i)) = Multiplicative.ofAdd (B5.Ln.mat γ *ᵥ fun i => x (c4 i))
    refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
    rw [mulVec_apply_of_supp _ c4_injective c4_surj hx, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun l _ => congrArg (· * x (c4 l)) (wedge_c4 γ i l)
  · obtain ⟨hQ, h11⟩ := mem_parJR.1 hj
    have hdet := det_eq_of_mem_parQ hQ
    rw [h11, Matrix.det_one, one_mul] at hdet
    set D : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨j.val.toBlocks₂₂, hdet⟩ with hD
    refine ⟨eSL 4 D, fun x hx => ?_⟩
    change JonesParshall.wedgeMat ((reindexSL (ZMod 2) _ j : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x = JonesParshall.wedgeMat ((reindexSL (ZMod 2) _
        (levR (ZMod 2) (Fin 1) ((eSL 4).symm (eSL 4 D))) : SL5) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x
    rw [MulEquiv.symm_apply_apply]
    refine wedgeMat_mulVec_congr hx fun k l hl => ?_
    obtain ⟨h00, h0l, hi0, hil⟩ := levR14_apply D
    have h21 : j.val.toBlocks₂₁ = 0 := hQ
    refine wedgeMat_eq_of_col0 (fun a => ?_) (fun a ha => ?_) (fun a b ha hb => ?_) k l
      (pr5_S4 l hl)
    · by_cases ha : a = 0
      · rw [ha, h00, reindex_apply, sumEquiv14_zero]
        exact congrFun₂ h11 0 0
      · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
        rw [hi0, reindex_apply, sumEquiv14_succ, sumEquiv14_zero]
        exact congrFun₂ h21 i 0
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
      rw [reindex_apply, sumEquiv14_succ, sumEquiv14_zero]
      exact congrFun₂ h21 i 0
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
      obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.2 hb
      rw [hil, reindex_apply, sumEquiv14_succ, sumEquiv14_succ]
      rfl

@[expose] def c6 : Fin 6 → Fin 10 := ![0, 1, 2, 4, 5, 7]

theorem c6_injective : Function.Injective c6 := by decide

theorem c6_mem : ∀ i, c6 i ∈ ({0, 1, 2, 4, 5, 7} : Finset (Fin 10)) := by decide

theorem c6_surj : ∀ k ∈ ({0, 1, 2, 4, 5, 7} : Finset (Fin 10)), ∃ i, c6 i = k := by decide

theorem pr5_c6 : ∀ i, JonesParshall.pr5 (c6 i) =
    (Fin.castLE (by norm_num) (JonesParshall.pr4 i).1,
      Fin.castLE (by norm_num) (JonesParshall.pr4 i).2) := by decide

theorem pr5_S6 : ∀ l ∈ ({0, 1, 2, 4, 5, 7} : Finset (Fin 10)),
    (JonesParshall.pr5 l).2.val < 4 := by decide

@[expose] noncomputable def phi6 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) →*
    ↥(parJL (ZMod 2) (Fin 4) (Fin 1)) :=
  ((levL (ZMod 2) (Fin 1)).comp (eSL 4).symm.toMonoidHom).codRestrict _
    fun _ => levL_mem_parJL _

theorem wedge_c6 (A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (i l : Fin 6) :
    JonesParshall.wedgeMat ((reindexSL (ZMod 2) (by norm_num : 4 + 1 = 5)
      (levL (ZMod 2) (Fin 1) A) : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) (c6 i) (c6 l) =
      JonesParshall.wedgeMat4 A.val i l := by
  simp only [JonesParshall.wedgeMat, JonesParshall.wedgeMat4, Matrix.of_apply, pr5_c6,
    reindex_castLE, levL_val, Matrix.fromBlocks_apply₁₁]

theorem extSqAct_one (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) :
    extSqAct (ZMod 2) 4 γ 1 = 1 := by
  show Multiplicative.ofAdd (exteriorPower.map 2 _ (Multiplicative.toAdd 1)) = 1
  rw [toAdd_one, map_zero]
  rfl

@[expose] noncomputable def psi6 : Multiplicative (Fin 6 → ZMod 2) ≃*
    Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) :=
  AddEquiv.toMultiplicative (JonesParshall.wedgeEquiv4 (ZMod 2)).symm.toAddEquiv

theorem part4_ext (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ∃ _ : IsMulCommutative ↥F.V6, SLExteriorTwo (V := ↥F.V6) (autOn (li L F.V6) F.V6) ⊤ ⊥ 4 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V6 F hf.normalizes hf.T_le
  have hres := S125L2G.hres_of parJL_le_parQ S125Pb.perfectResidual_parQ41
  have hcomm : IsMulCommutative ↥(F.sub {0, 1, 2, 4, 5, 7}) :=
    isMulCommutative_sub hf.comm (sub_le F _)
  refine ⟨hcomm, ?_⟩
  refine realizes_sub_coord (D := FFModel.extSq (ZMod 2) 4) rfl rfl extSqAct_one F hf
    (by norm_num : 4 + 1 = 5) hst hres c6 c6_injective c6_mem c6_surj psi6 phi6
    (fun γ x hx => ?_) (fun j hj => ?_)
  · change Multiplicative.ofAdd ((JonesParshall.wedgeEquiv4 (ZMod 2)).symm
      (fun i => (JonesParshall.wedgeMat ((reindexSL (ZMod 2) _
        (levL (ZMod 2) (Fin 1) ((eSL 4).symm γ)) : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x)
          (c6 i))) = Multiplicative.ofAdd (exteriorPower.map 2 (Matrix.toLin' (B5.Ln.mat γ))
            ((JonesParshall.wedgeEquiv4 (ZMod 2)).symm fun i => x (c6 i)))
    refine congrArg Multiplicative.ofAdd ((JonesParshall.wedgeEquiv4 (ZMod 2)).injective ?_)
    rw [LinearEquiv.apply_symm_apply, JonesParshall.wedgeEquiv4_apply,
      JonesParshall.wedgeCoord_map4, ← JonesParshall.wedgeEquiv4_apply,
      LinearEquiv.apply_symm_apply]
    funext i
    rw [mulVec_apply_of_supp _ c6_injective c6_surj hx, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun l _ => congrArg (· * x (c6 l)) ?_
    rw [wedge_c6]
    exact congrArg (fun M => JonesParshall.wedgeMat4 M i l) (coe_eSL_symm 4 γ)
  · obtain ⟨hQ, h22⟩ := mem_parJL.1 hj
    have hdet := det_eq_of_mem_parQ hQ
    rw [h22, Matrix.det_one, mul_one] at hdet
    set A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨j.val.toBlocks₁₁, hdet⟩ with hA
    refine ⟨eSL 4 A, fun x hx => ?_⟩
    change JonesParshall.wedgeMat ((reindexSL (ZMod 2) _ j : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x = JonesParshall.wedgeMat ((reindexSL (ZMod 2) _
        (levL (ZMod 2) (Fin 1) ((eSL 4).symm (eSL 4 A))) : SL5) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x
    rw [MulEquiv.symm_apply_apply]
    have h11 : j.val.toBlocks₁₁ = (levL (ZMod 2) (Fin 1) A).val.toBlocks₁₁ := by
      rw [levL_val, Matrix.toBlocks_fromBlocks₁₁]
    exact wedgeMat_mulVec_congr hx fun k l hl => wedgeMat_eq_of_cols (d := 4)
      (fun a b hb => reindex_col_eq _ hQ (parJL_le_parQ (levL_mem_parJL A)) h11 a b hb) k l
      (pr5_S6 l hl)

@[expose] def c3 : Fin 3 → Fin 10 := ![4, 1, 0]

@[expose] def r1 : Fin 3 → Fin 3 := ![1, 0, 0]

@[expose] def r2 : Fin 3 → Fin 3 := ![2, 2, 1]

theorem c3_injective : Function.Injective c3 := by decide

theorem c3_mem : ∀ i, c3 i ∈ ({0, 1, 4} : Finset (Fin 10)) := by decide

theorem c3_surj : ∀ k ∈ ({0, 1, 4} : Finset (Fin 10)), ∃ i, c3 i = k := by decide

theorem pr5_c3 : ∀ i, JonesParshall.pr5 (c3 i) =
    (Fin.castLE (by norm_num) (r1 i), Fin.castLE (by norm_num) (r2 i)) := by decide

theorem pr5_S3 : ∀ l ∈ ({0, 1, 4} : Finset (Fin 10)), (JonesParshall.pr5 l).2.val < 3 := by
  decide

theorem minor3_eq_adjugate (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i l : Fin 3) :
    B (r1 i) (r1 l) * B (r2 i) (r2 l) - B (r1 i) (r2 l) * B (r2 i) (r1 l) = B.adjugate l i := by
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases l <;> simp [r1, r2, CharTwo.sub_eq_add, CharTwo.neg_eq]

@[expose] noncomputable def phi3 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) →*
    ↥(parJL (ZMod 2) (Fin 3) (Fin 2)) :=
  ((levL (ZMod 2) (Fin 2)).comp ((JonesParshall.invTransposeSL 3 (ZMod 2)).toMonoidHom.comp
    (eSL 3).symm.toMonoidHom)).codRestrict _ fun _ => levL_mem_parJL _

theorem wedge_c3 (P : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (i l : Fin 3) :
    JonesParshall.wedgeMat ((reindexSL (ZMod 2) (by norm_num : 3 + 2 = 5)
      (levL (ZMod 2) (Fin 2) (JonesParshall.invTransposeSL 3 (ZMod 2) P)) : SL5) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) (c3 i) (c3 l) = P.val i l := by
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, pr5_c3, reindex_castLE, levL_val,
    Matrix.fromBlocks_apply₁₁]
  rw [minor3_eq_adjugate, JonesParshall.invTransposeSL_coe, ← Matrix.adjugate_transpose,
    ← Matrix.SpecialLinearGroup.coe_inv, inv_inv, Matrix.transpose_apply]

theorem part2_nat (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ∃ _ : IsMulCommutative ↥F.V3,
      BinaryNaturalSL (V := ↥F.V3) (autOn (li L F.V3) F.V3) ⊤ ⊥ 3 1 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hst := isStab_V3 F hf.normalizes hf.T_le
  have hres := S125L2G.hres_of parJL_le_parQ S125Pb.perfectResidual_parQ32
  have hcomm : IsMulCommutative ↥(F.sub {0, 1, 4}) := isMulCommutative_sub hf.comm (sub_le F _)
  refine ⟨hcomm, ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ?_⟩
  refine realizes_sub_coord (D := FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)))
    rfl rfl (natAct_one 3) F hf (by norm_num : 3 + 2 = 5) hst hres c3 c3_injective c3_mem c3_surj
    (MulEquiv.refl _) phi3 (fun γ x hx => ?_) (fun j hj => ?_)
  · change Multiplicative.ofAdd (fun i => (JonesParshall.wedgeMat ((reindexSL (ZMod 2) _
        (levL (ZMod 2) (Fin 2) (JonesParshall.invTransposeSL 3 (ZMod 2) ((eSL 3).symm γ))) :
          SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) (c3 i)) =
        Multiplicative.ofAdd (B5.Ln.mat γ *ᵥ fun i => x (c3 i))
    refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
    rw [mulVec_apply_of_supp _ c3_injective c3_surj hx, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun l _ => congrArg (· * x (c3 l)) ?_
    rw [wedge_c3]
    exact congrFun₂ (coe_eSL_symm 3 γ) i l
  · obtain ⟨hQ, h22⟩ := mem_parJL.1 hj
    have hdet := det_eq_of_mem_parQ hQ
    rw [h22, Matrix.det_one, mul_one] at hdet
    set A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨j.val.toBlocks₁₁, hdet⟩ with hA
    refine ⟨eSL 3 ((JonesParshall.invTransposeSL 3 (ZMod 2)).symm A), fun x hx => ?_⟩
    change JonesParshall.wedgeMat ((reindexSL (ZMod 2) _ j : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x = JonesParshall.wedgeMat ((reindexSL (ZMod 2) _
        (levL (ZMod 2) (Fin 2) (JonesParshall.invTransposeSL 3 (ZMod 2) ((eSL 3).symm
          (eSL 3 ((JonesParshall.invTransposeSL 3 (ZMod 2)).symm A))))) : SL5) :
            Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x
    rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
    have h11 : j.val.toBlocks₁₁ = (levL (ZMod 2) (Fin 2) A).val.toBlocks₁₁ := by
      rw [levL_val, Matrix.toBlocks_fromBlocks₁₁]
    exact wedgeMat_mulVec_congr hx fun k l hl => wedgeMat_eq_of_cols (d := 3)
      (fun a b hb => reindex_col_eq _ hQ (parJL_le_parQ (levL_mem_parJL A)) h11 a b hb) k l
      (pr5_S3 l hl)

end S125Nat

end CFSG.Quasithin.H13
