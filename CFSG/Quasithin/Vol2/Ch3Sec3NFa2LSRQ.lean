module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Out
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Alpha
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Ext2
public import CFSG.Quasithin.Background.MulAutTwo

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative

section P2Numerics

open Matrix

open Matrix

def P2blkA (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => M (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)) (finSumFinEquiv (m := 2) (n := 2) (Sum.inl j))

def P2blkB (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => M (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)) (finSumFinEquiv (m := 2) (n := 2) (Sum.inr j))

def P2blkD (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => M (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)) (finSumFinEquiv (m := 2) (n := 2) (Sum.inr j))

theorem P2_det_block (M : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h0 : ∀ i j : Fin 2, M (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)) (finSumFinEquiv (m := 2) (n := 2) (Sum.inl j)) = 0) :
    M.det = (P2blkA M).det * (P2blkD M).det := by
  have e : M.submatrix (finSumFinEquiv (m := 2) (n := 2)) (finSumFinEquiv (m := 2) (n := 2)) =
      Matrix.fromBlocks (P2blkA M) (P2blkB M) 0 (P2blkD M) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [P2blkA, P2blkB, P2blkD, Matrix.fromBlocks, h0]
  have hd : (M.submatrix (finSumFinEquiv (m := 2) (n := 2)) (finSumFinEquiv (m := 2) (n := 2))).det = M.det :=
    Matrix.det_submatrix_equiv_self _ _
  rw [← hd, e, Matrix.det_fromBlocks_zero₂₁]

theorem P2_card_detNZ : Nat.card {A : Matrix (Fin 2) (Fin 2) (ZMod 2) // A.det ≠ 0} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem P2_card_mat2 : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod 2)) = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem P2_h0 (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (hg : g ∈ L3321.P2) (i j : Fin 2) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i))
      (finSumFinEquiv (m := 2) (n := 2) (Sum.inl j)) = 0 := by
  refine (L3321.mem_P2_iff g).1 hg _ _ ?_ ?_
  · have e : ((finSumFinEquiv (m := 2) (n := 2) (Sum.inl j) : Fin 4) : ℕ) = j := rfl
    have := j.isLt
    omega
  · have e : ((finSumFinEquiv (m := 2) (n := 2) (Sum.inr i) : Fin 4) : ℕ) = 2 + i := rfl
    omega

theorem P2_det_blkA_ne (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (hg : g ∈ L3321.P2) :
    (P2blkA g).det ≠ 0 := by
  intro h0
  have hdet := P2_det_block (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (P2_h0 g hg)
  rw [Matrix.SpecialLinearGroup.det_coe, h0, zero_mul] at hdet
  exact one_ne_zero hdet

theorem P2_det_blkD_ne (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (hg : g ∈ L3321.P2) :
    (P2blkD g).det ≠ 0 := by
  intro h0
  have hdet := P2_det_block (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (P2_h0 g hg)
  rw [Matrix.SpecialLinearGroup.det_coe, h0, mul_zero] at hdet
  exact one_ne_zero hdet

noncomputable def P2_blocks (g : ↥L3321.P2) :
    {A : Matrix (Fin 2) (Fin 2) (ZMod 2) // A.det ≠ 0} × Matrix (Fin 2) (Fin 2) (ZMod 2) ×
      {D : Matrix (Fin 2) (Fin 2) (ZMod 2) // D.det ≠ 0} :=
  (⟨P2blkA (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)), P2_det_blkA_ne g.1 g.2⟩,
    P2blkB (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)),
    ⟨P2blkD (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)), P2_det_blkD_ne g.1 g.2⟩)

theorem P2_blocks_injective : Function.Injective P2_blocks := by
  intro g g' hgg
  have hA := congrArg (fun p => p.1.1) hgg
  have hB := congrArg (fun p => p.2.1) hgg
  have hD := congrArg (fun p => p.2.2.1) hgg
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  obtain ⟨a, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective k
  obtain ⟨b, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective l
  rcases a with a | a <;> rcases b with b | b
  · have := congrFun (congrFun hA a) b
    simpa [P2_blocks, P2blkA] using this
  · have := congrFun (congrFun hB a) b
    simpa [P2_blocks, P2blkB] using this
  · rw [P2_h0 g.1 g.2 a b, P2_h0 g'.1 g'.2 a b]
  · have := congrFun (congrFun hD a) b
    simpa [P2_blocks, P2blkD] using this

theorem card_P2_le : Nat.card ↥L3321.P2 ≤ 576 := by
  have h := Nat.card_le_card_of_injective P2_blocks P2_blocks_injective
  have hX : Nat.card ({A : Matrix (Fin 2) (Fin 2) (ZMod 2) // A.det ≠ 0} × Matrix (Fin 2) (Fin 2) (ZMod 2) ×
      {D : Matrix (Fin 2) (Fin 2) (ZMod 2) // D.det ≠ 0}) = 576 := by
    rw [Nat.card_prod, Nat.card_prod, P2_card_detNZ, P2_card_mat2]
  omega

theorem P2_index_ge : 35 ≤ L3321.P2.index := by
  have h1 := Subgroup.card_mul_index (H := L3321.P2)
  rw [Ln2.card_specialLinear 4 (Or.inl rfl)] at h1
  have h2 := card_P2_le
  simp only [if_true] at h1
  by_contra hlt
  have h3 : L3321.P2.index ≤ 34 := by omega
  have h4 : Nat.card ↥L3321.P2 * L3321.P2.index ≤ 576 * 34 := Nat.mul_le_mul h2 h3
  omega

theorem card_wreath : Nat.card ↥CFSG.Quasithin.H13.wreathS3Z2 = 72 := by
  rw [← Nat.card_congr CFSG.Quasithin.H13.Wreath.wreathEquiv.toEquiv,
    RegularWreathProduct.card]
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)), Fintype.card_perm, Fintype.card_fin]
  rw [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2))]
  decide +kernel

end P2Numerics

section GroupLemmas

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

variable {G : Type} [Group G] [Finite G]

theorem lsrq_le_normalizer_L {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer hTL

theorem lsrq_le_normalizer_O2 {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
  sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))

@[expose] def lsrqActSub (L T : Subgroup G) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup G where
  carrier := {c | c ∈ L ⊔ T ∧ ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L}
  mul_mem' := by
    rintro c₁ c₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
    refine ⟨Subgroup.mul_mem _ h₁ h₂, fun x hx => ?_⟩
    have e : c₁ * c₂ * x * (c₁ * c₂)⁻¹ * x⁻¹ =
        (c₁ * (c₂ * x * c₂⁻¹ * x⁻¹) * c₁⁻¹) * (c₁ * x * c₁⁻¹ * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _
      ((Subgroup.mem_normalizer_iff.mp (lsrq_le_normalizer_O2 hTL h₁) _).mp (k₂ x hx)) (k₁ x hx)
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
  inv_mem' := by
    rintro c ⟨hc, k⟩
    refine ⟨Subgroup.inv_mem _ hc, fun x hx => ?_⟩
    have hy : c⁻¹ * x * c ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (lsrq_le_normalizer_L hTL hc)) x).mp hx
      simpa using this
    have e : c⁻¹ * x * c⁻¹⁻¹ * x⁻¹ = (c * (c⁻¹ * x * c) * c⁻¹ * (c⁻¹ * x * c)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (k _ hy)

theorem lsrq_mem_actSub {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) {c : G} :
    c ∈ lsrqActSub L T hTL ↔ c ∈ L ⊔ T ∧ ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L := Iff.rfl

theorem lsrq_actSub_inf_le {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) {c : G}
    (hc : c ∈ lsrqActSub L T hTL) (hcL : c ∈ L) : c ∈ pCoreOf 2 L := by
  have hk := ((lsrq_mem_actSub hTL).1 hc).2
  have hcent : α ⟨c, hcL⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := hαs g
    have h1 : (⟨c, hcL⟩ : ↥L) * x * (⟨c, hcL⟩ : ↥L)⁻¹ * x⁻¹ ∈ α.ker := by
      rw [hαk]
      exact (Lem3328.mem_pCore_iff _).2 (hk x x.2)
    have h2 := MonoidHom.mem_ker.1 h1
    simp only [map_mul, map_inv] at h2
    have h3 : α ⟨c, hcL⟩ * α x = α x * α ⟨c, hcL⟩ := by
      calc α ⟨c, hcL⟩ * α x
          = (α ⟨c, hcL⟩ * α x * (α ⟨c, hcL⟩)⁻¹ * (α x)⁻¹) * (α x * α ⟨c, hcL⟩) := by group
        _ = α x * α ⟨c, hcL⟩ := by rw [h2, one_mul]
    exact h3.symm
  have h4 : α ⟨c, hcL⟩ = 1 := by
    have h := hcent
    rw [MulAutTwo.center_SL_eq_bot (n := 4) (by norm_num), Subgroup.mem_bot] at h
    exact h
  have h5 : (⟨c, hcL⟩ : ↥L) ∈ α.ker := MonoidHom.mem_ker.2 h4
  rw [hαk] at h5
  exact (Lem3328.mem_pCore_iff _).1 h5

theorem lsrq_actSub_conj_mem {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) {g c : G}
    (hg : g ∈ L ⊔ T) (hc : c ∈ lsrqActSub L T hTL) : g * c * g⁻¹ ∈ lsrqActSub L T hTL := by
  obtain ⟨hcLT, hk⟩ := (lsrq_mem_actSub hTL).1 hc
  refine (lsrq_mem_actSub hTL).2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcLT) (Subgroup.inv_mem _ hg),
    fun x hx => ?_⟩
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := lsrq_le_normalizer_L hTL hg
  have hx' : g⁻¹ * x * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) x).mp hx
    simpa using this
  have hu := hk _ hx'
  have e : g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ * x⁻¹ =
      g * (c * (g⁻¹ * x * g) * c⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (lsrq_le_normalizer_O2 hTL hg) _).mp hu

theorem lsrq_le_normalizer_actSub {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer ((lsrqActSub L T hTL : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact lsrq_actSub_conj_mem hTL hg hh
  · intro hh
    have := lsrq_actSub_conj_mem hTL (Subgroup.inv_mem _ hg) hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e] at this
    exact this

theorem lsrq_S_le_LQ {L T S : Subgroup G} {α : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hT2 : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) (hST : S ≤ T)
    (hconj : ∀ s ∈ S, ∃ y : ↥L, ∀ (x : ↥L) (hx : s * (x : G) * s⁻¹ ∈ L),
      α ⟨s * x * s⁻¹, hx⟩ = α y * α x * (α y)⁻¹) :
    S ≤ L ⊔ pCoreOf 2 (L ⊔ T) := by
  have hCLT : lsrqActSub L T hTL ≤ L ⊔ T := fun c hc => ((lsrq_mem_actSub hTL).1 hc).1
  have hCL : IsPGroup 2 ↥(lsrqActSub L T hTL ⊓ L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le (fun x hx =>
      lsrq_actSub_inf_le hTL hαs hαk (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hx).2)
  have hC2 : IsPGroup 2 ↥(lsrqActSub L T hTL) :=
    isPGroup_two_of_le_sup hT2 hTL hCLT hCL
  have hcore : lsrqActSub L T hTL ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCLT (lsrq_le_normalizer_actSub hTL) hC2
  intro s hs
  obtain ⟨y, hy⟩ := hconj s hs
  have hsT : s ∈ L ⊔ T := (le_sup_right : T ≤ L ⊔ T) (hST hs)
  have hc : (y : G)⁻¹ * s ∈ lsrqActSub L T hTL := by
    refine (lsrq_mem_actSub hTL).2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ((le_sup_left : L ≤ L ⊔ T) y.2)) hsT,
      fun x hx => ?_⟩
    have hw : s * x * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL (hST hs)) x).mp hx
    have hyx : α ⟨s * x * s⁻¹, hw⟩ = α y * α ⟨x, hx⟩ * (α y)⁻¹ := hy ⟨x, hx⟩ hw
    have hmem : (y : G)⁻¹ * (s * x * s⁻¹) * (y : G) ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem y.2) hw) y.2
    have hα : α ⟨(y : G)⁻¹ * (s * x * s⁻¹) * (y : G), hmem⟩ = α ⟨x, hx⟩ := by
      have e : (⟨(y : G)⁻¹ * (s * x * s⁻¹) * (y : G), hmem⟩ : ↥L) =
          (y : ↥L)⁻¹ * ⟨s * x * s⁻¹, hw⟩ * y := rfl
      rw [e, map_mul, map_mul, map_inv, hyx]
      group
    have hkerm : (⟨(y : G)⁻¹ * (s * x * s⁻¹) * (y : G), hmem⟩ : ↥L) * (⟨x, hx⟩ : ↥L)⁻¹ ∈
        α.ker := MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hα, mul_inv_cancel])
    rw [hαk] at hkerm
    have hP := (Lem3328.mem_pCore_iff _).1 hkerm
    have e2 : ((y : G)⁻¹ * s) * x * ((y : G)⁻¹ * s)⁻¹ * x⁻¹ =
        (y : G)⁻¹ * (s * x * s⁻¹) * (y : G) * x⁻¹ := by group
    rw [e2]
    exact hP
  have hcP := hcore hc
  have e3 : (y : G) * ((y : G)⁻¹ * s) = s := by group
  rw [← e3]
  exact Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ pCoreOf 2 (L ⊔ T)) y.2)
    ((le_sup_right : pCoreOf 2 (L ⊔ T) ≤ L ⊔ pCoreOf 2 (L ⊔ T)) hcP)

theorem lsrq_cover {L T S : Subgroup G} {t₀ : G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ht₀ : t₀ ∈ T) (hSLQ : S ≤ L ⊔ pCoreOf 2 (L ⊔ T))
    (hdich : ∀ x ∈ T, x ∈ S ∨ x * t₀⁻¹ ∈ S)
    (hN : L ⊔ T ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G))
    (x : G) (hx : x ∈ L ⊔ T) :
    x ∈ L ⊔ pCoreOf 2 (L ⊔ T) ∨ t₀⁻¹ * x ∈ L ⊔ pCoreOf 2 (L ⊔ T) := by
  have hx' : x ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]; exact hx
  obtain ⟨l, hl, t, ht, rfl⟩ := hx'
  rcases hdich t ht with h | h
  · exact Or.inl (Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ pCoreOf 2 (L ⊔ T)) hl) (hSLQ h))
  · right
    have hls : l * (t * t₀⁻¹) ∈ L ⊔ pCoreOf 2 (L ⊔ T) :=
      Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ pCoreOf 2 (L ⊔ T)) hl) (hSLQ h)
    have hinv : t₀⁻¹ ∈ Subgroup.normalizer ((L ⊔ pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) :=
      hN (Subgroup.inv_mem _ ((le_sup_right : T ≤ L ⊔ T) ht₀))
    have e : t₀⁻¹ * (l * t) = t₀⁻¹ * (l * (t * t₀⁻¹)) * t₀⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hinv _).mp hls

theorem lsrq_LQ_relIndex_le_two {L T : Subgroup G} {t₀ : G} (ht₀ : t₀ ∈ T)
    (hcov : ∀ x ∈ L ⊔ T, x ∈ L ⊔ pCoreOf 2 (L ⊔ T) ∨ t₀⁻¹ * x ∈ L ⊔ pCoreOf 2 (L ⊔ T)) :
    (L ⊔ pCoreOf 2 (L ⊔ T)).relIndex (L ⊔ T) ≤ 2 := by
  have hcov' : ⋃ i ∈ (Finset.univ : Finset (Fin 2)),
      (![(1 : ↥(L ⊔ T)), ⟨t₀, (le_sup_right : T ≤ L ⊔ T) ht₀⟩] i) •
        (((L ⊔ pCoreOf 2 (L ⊔ T)).subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)) =
      Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_iUnion₂]
    rcases hcov x x.2 with h | h
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      rw [mem_leftCoset_iff]
      simpa [Subgroup.mem_subgroupOf] using h
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      rw [mem_leftCoset_iff]
      simpa [Subgroup.mem_subgroupOf] using h
  have h := Subgroup.index_le_of_leftCoset_cover_const hcov'
  simpa [Subgroup.relIndex] using h

theorem lsrq_relIndex_le_ker_index {N Q : Subgroup G}
    {α : ↥N →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) (hαs : Function.Surjective α)
    (hker : ∀ l : ↥N, α l = 1 → (l : G) ∈ Q) :
    Q.relIndex (N ⊔ Q) ≤ α.ker.index := by
  have hN' : N ⊔ Q ≤ Subgroup.normalizer (Q : Set G) := sup_le hNQ Subgroup.le_normalizer
  haveI : (Q.subgroupOf (N ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hN'
  let φ : ↥N →* ↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q) :=
    (QuotientGroup.mk' (Q.subgroupOf (N ⊔ Q))).comp
      (Subgroup.inclusion (le_sup_left : N ≤ N ⊔ Q))
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : (y : G) ∈ (N : Set G) * (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right N Q hNQ]; exact y.2
    obtain ⟨l, hl, q, hq, hlq⟩ := hy
    refine ⟨⟨l, hl⟩, ?_⟩
    show (QuotientGroup.mk _ : ↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q)) = QuotientGroup.mk y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (l : G)⁻¹ * (y : G) ∈ Q
    rw [← hlq]
    simpa using hq
  have hφk : φ.ker.index = Q.relIndex (N ⊔ Q) := by
    have h1 := Subgroup.index_comap_of_surjective
      (H := (⊥ : Subgroup (↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q)))) hφs
    rw [Subgroup.index_bot, ← Subgroup.index_eq_card] at h1
    exact h1
  have hle : α.ker ≤ φ.ker := by
    intro l hl
    have hq : (l : G) ∈ Q := hker l (MonoidHom.mem_ker.1 hl)
    refine MonoidHom.mem_ker.2 ?_
    show (QuotientGroup.mk _ : ↥(N ⊔ Q) ⧸ Q.subgroupOf (N ⊔ Q)) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq
  rw [← hφk]
  exact Subgroup.index_antitone hle

end GroupLemmas

theorem mem_liftPre_iff' {G : Type} [Group G] {L : Subgroup G}
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)}
    {Q : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))} (x : ↥L) :
    (x : G) ∈ CFSG.Quasithin.H13.L3316.liftPre α Q ↔ α x ∈ Q := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  · intro h
    exact Subgroup.mem_map.2 ⟨x, h, rfl⟩

theorem leaf_LSRQ_of (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → mIdx (a2R H) (a2Q L T) ≤ 4 := by
  intro G _ _ T M L D H K q c
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, ⟨e⟩, hc, hmodE, hout, -⟩ := c.site
  obtain ⟨α, hαs, hαk, hαU, hCZ⟩ :=
    L3321.exists_alpha_ext_of_TL h9 hGA c.nf.hyp c.mPlus_eq hTL e hmodE
  obtain ⟨S, hST, -, -, -, hconj₀, ⟨t₀, ht₀, -, u₀, hu₀, -, hdich⟩⟩ :=
    L3321.exists_inner_noD c.nf.hyp hTL hαs hαk hαU hout
  have hconj : ∀ s ∈ S, ∃ y : ↥L, ∀ (x : ↥L) (hx : s * (x : G) * s⁻¹ ∈ L),
      α ⟨s * x * s⁻¹, hx⟩ = α y * α x * (α y)⁻¹ := fun s hs => by
    obtain ⟨y, -, hy⟩ := hconj₀ s hs
    exact ⟨y, hy⟩
  have hT2 : IsPGroup 2 T := c.nf.hyp.sylow.1
  have hQN : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := lsrq_le_normalizer_L hTL
  have hLQN : L ⊔ T ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.1 (hLN hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hQN hg)]
  have hSLQ : S ≤ L ⊔ pCoreOf 2 (L ⊔ T) := lsrq_S_le_LQ hT2 hTL hαs hαk hST hconj
  have hcov : ∀ x ∈ L ⊔ T, x ∈ L ⊔ pCoreOf 2 (L ⊔ T) ∨
      t₀⁻¹ * x ∈ L ⊔ pCoreOf 2 (L ⊔ T) :=
    fun x hx => lsrq_cover hTL ht₀ hSLQ hdich hLQN x hx
  have hLQ2 := lsrq_LQ_relIndex_le_two ht₀ hcov
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hker : ∀ l : ↥L, α l = 1 → (l : G) ∈ pCoreOf 2 (L ⊔ T) := fun l hl =>
    hOL ((Lem3328.mem_pCore_iff l).1 (by rw [← hαk]; exact MonoidHom.mem_ker.2 hl))
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := le_sup_left.trans hQN
  have hkerIdx : α.ker.index = 20160 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hαs, Subgroup.card_top,
      Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have hQLQ : (pCoreOf 2 (L ⊔ T)).relIndex (L ⊔ pCoreOf 2 (L ⊔ T)) ≤ 20160 := by
    rw [← hkerIdx]
    exact lsrq_relIndex_le_ker_index hLQ hαs hker
  have hQLT : (pCoreOf 2 (L ⊔ T)).relIndex (L ⊔ T) ≤ 40320 := by
    have h := Subgroup.relIndex_mul_relIndex (H := pCoreOf 2 (L ⊔ T))
      (K := L ⊔ pCoreOf 2 (L ⊔ T)) (L := L ⊔ T) le_sup_right
      (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T)))
    rw [← h]
    calc (pCoreOf 2 (L ⊔ T)).relIndex (L ⊔ pCoreOf 2 (L ⊔ T)) *
          (L ⊔ pCoreOf 2 (L ⊔ T)).relIndex (L ⊔ T) ≤ 20160 * 2 := Nat.mul_le_mul hQLQ hLQ2
      _ = 40320 := by norm_num
  have hRH : 72 ≤ (pCoreOf 2 H).relIndex H := by
    have hsub2 : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H := by
      ext x
      rw [Subgroup.mem_subgroupOf, Lem3328.mem_pCore_iff]
    obtain ⟨ew⟩ := c.nf.wreath
    have hi : (pCoreOf 2 H).relIndex H = Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) := by
      unfold Subgroup.relIndex
      rw [hsub2, Subgroup.index_eq_card]
    rw [hi, Nat.card_congr ew.toEquiv, card_wreath]
  have hmemH : ∀ x : ↥L, (x : G) ∈ H ↔ α x ∈ L3321.P2 := by
    intro x
    have hC : (x : G) ∈ H ↔
        (x : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [c.Heq]
      constructor
      · intro h
        exact Subgroup.mem_inf.2 ⟨x.2, (Subgroup.mem_inf.1 h).2⟩
      · intro h
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left h.1, h.2⟩
    rw [hC, hCZ, mem_liftPre_iff']
  have hsub : H.subgroupOf L = (L3321.P2).comap α := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hmemH x
  have hHLidx : H.relIndex L = L3321.P2.index := by
    unfold Subgroup.relIndex
    rw [hsub, Subgroup.index_comap_of_surjective (H := L3321.P2) hαs]
  have hHLT : 35 ≤ H.relIndex (L ⊔ T) := by
    haveI : H.IsFiniteRelIndex (L ⊔ T) := Subgroup.isFiniteRelIndex_of_finiteIndex
    have h1 := Subgroup.relIndex_le_of_le_right (H := H) (K := L) (L := L ⊔ T) le_sup_left
      Subgroup.relIndex_ne_zero
    have h2 := P2_index_ge
    omega
  have hQR : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 H := c.Q_le_R
  have hRH' : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHLT' : H ≤ L ⊔ T := c.nf.HLT
  have hmul : (pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) *
      ((pCoreOf 2 H).relIndex H * H.relIndex (L ⊔ T)) =
      (pCoreOf 2 (L ⊔ T)).relIndex (L ⊔ T) := by
    rw [Subgroup.relIndex_mul_relIndex (H := pCoreOf 2 H) (K := H) (L := L ⊔ T) hRH' hHLT',
      Subgroup.relIndex_mul_relIndex (H := pCoreOf 2 (L ⊔ T)) (K := pCoreOf 2 H) (L := L ⊔ T)
        hQR (hRH'.trans hHLT')]
  have hx16 : (pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) ≤ 16 := by
    have h1 : 72 * 35 ≤ (pCoreOf 2 H).relIndex H * H.relIndex (L ⊔ T) :=
      Nat.mul_le_mul hRH hHLT
    have h2 := Nat.mul_le_mul_left ((pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H)) h1
    rw [hmul] at h2
    have h3 : (pCoreOf 2 (L ⊔ T)).relIndex (pCoreOf 2 H) * 2520 ≤ 40320 :=
      le_trans (le_of_eq (by ring)) (h2.trans hQLT)
    omega
  have hR2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hpow := CFSG.Quasithin.HypF98.relIndex_eq_two_pow_mIdx
    (X := pCoreOf 2 H) (Y := pCoreOf 2 (L ⊔ T)) hR2
  show CFSG.Quasithin.mIdx (pCoreOf 2 H) (pCoreOf 2 (L ⊔ T)) ≤ 4
  by_contra hm
  have h5 : 5 ≤ CFSG.Quasithin.mIdx (pCoreOf 2 H) (pCoreOf 2 (L ⊔ T)) := by omega
  have h6 := Nat.pow_le_pow_right (show 2 > 0 by norm_num) h5
  rw [← hpow] at h6
  norm_num at h6
  omega

end CFSG.Quasithin.H13.NFa2
