module

public import CFSG.Timmesfeld.Transvection.OddModelBlock
import CFSG.Timmesfeld.Transvection.OddModelBC2
public import CFSG.Timmesfeld.Transvection.OddModelWeyl
public import CFSG.Timmesfeld.Transvection.OddModelPairs
import CFSG.RankThree.CentralLiftU.BlockMat

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {r : ℕ} (hr : 2 ≤ r)

local notation "X" γ:max => CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1) γ
private lemma bcLastIdx_eq : bcLastIdx r (by omega) =
    (⟨r - 1, by omega⟩ : Fin ((2 * r + 1) / 2)) := rfl
private lemma bcLastIdx_ne_bcPrevIdx :
    (⟨r - 1, by omega⟩ : Fin ((2 * r + 1) / 2)) ≠ bcPrevIdx r hr := by
  rw [show bcPrevIdx r hr = (⟨r - 2, by omega⟩ : Fin ((2 * r + 1) / 2)) from rfl]
  apply Fin.ne_of_val_ne
  simp only [Fin.val_mk]
  omega

@[expose] noncomputable def bc2Q0 : Subgroup (SU σ (2 * r + 1)) :=
  X (Pi.single (bcPrevIdx r hr) 1) ⊔
    X (Pi.single (bcPrevIdx r hr) 1 + 2 • Pi.single (bcLastIdx r (by omega)) 1) ⊔
      X (2 • Pi.single (bcPrevIdx r hr) 1 + 2 • Pi.single (bcLastIdx r (by omega)) 1)

@[expose] noncomputable def bc2Qe1 : Subgroup (SU σ (2 * r + 1)) :=
  bc2Q0 hσ hr ⊔ X (Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (by omega)) 1)

theorem bc2Q0_le_range_oddEmb : bc2Q0 hσ hr ≤ (oddEmb σ r).range := by
  refine sup_le (sup_le ?_ ?_) ?_
  · refine rootGroup_le_range_oddEmb (r := r) hσ (by omega) ?_
    have h1 : (Pi.single (bcPrevIdx r hr) (1 : ℤ) : Fin ((2 * r + 1) / 2) → ℤ)
        (⟨r - 1, by omega⟩ : Fin ((2 * r + 1) / 2)) = 0 := by
      rw [Pi.single_apply, if_neg (bcLastIdx_ne_bcPrevIdx hr)]
    rw [h1]
    exact ⟨0, rfl⟩
  · refine rootGroup_le_range_oddEmb (r := r) hσ (by omega) ?_
    have h1 : (Pi.single (bcPrevIdx r hr) (1 : ℤ) +
        2 • Pi.single (bcLastIdx r (by omega)) (1 : ℤ) : Fin ((2 * r + 1) / 2) → ℤ)
        (⟨r - 1, by omega⟩ : Fin ((2 * r + 1) / 2)) = 2 := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
        if_neg (bcLastIdx_ne_bcPrevIdx hr), if_pos (bcLastIdx_eq hr).symm]
      norm_num
    rw [h1]
    exact ⟨1, by norm_num⟩
  · refine rootGroup_le_range_oddEmb (r := r) hσ (by omega) ?_
    have h1 : (2 • Pi.single (bcPrevIdx r hr) (1 : ℤ) +
        2 • Pi.single (bcLastIdx r (by omega)) (1 : ℤ) : Fin ((2 * r + 1) / 2) → ℤ)
        (⟨r - 1, by omega⟩ : Fin ((2 * r + 1) / 2)) = 2 := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
        if_neg (bcLastIdx_ne_bcPrevIdx hr), if_pos (bcLastIdx_eq hr).symm]
      norm_num
    rw [h1]
    exact ⟨1, by norm_num⟩
private lemma rootGroup_le_centralizer_heisP_of_toStd_rt
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    {a b : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (hab : idx a ≠ idx b) (hγ : toStd (2 * r + 1) γ = rt a b)
    (hca : Sum.inl (bcPrevIdx r hr) ≠ Sum.swap a)
    (hcb : Sum.inl (bcPrevIdx r hr) ≠ Sum.swap b) :
    X γ ≤ Subgroup.centralizer
      (X (Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (by omega)) 1) : Set _) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨t, rfl⟩ := (mem_rootGroup_iff_suElt_odd hσ hab hγ g).mp hg
  obtain ⟨u, v, _huv, rfl⟩ :=
    (mem_rootGroup_iff_suHeis hσ (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.2.2.1 k).mp hk
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (suHeis_comm_suElt hσ (Nat.not_even_two_mul_add_one r) hab hca hcb u v t)
private lemma rootGroup_le_centralizer_heisP_of_toStd_rt_self
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (hγ : toStd (2 * r + 1) γ = rt a a)
    (hca : Sum.inl (bcPrevIdx r hr) ≠ Sum.swap a) :
    X γ ≤ Subgroup.centralizer
      (X (Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (by omega)) 1) : Set _) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨t, _ht, rfl⟩ := (mem_rootGroup_iff_suLong_odd hσ a hγ g).mp hg
  obtain ⟨u, v, _huv, rfl⟩ :=
    (mem_rootGroup_iff_suHeis hσ (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.2.2.1 k).mp hk
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (suHeis_comm_suLong hσ (Nat.not_even_two_mul_add_one r) hca u v t)

theorem heisP_le_centralizer :
    X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ≤
      Subgroup.centralizer (bc2Q0 hσ hr : Set _) := by
  rw [Subgroup.le_centralizer_iff, bc2Q0]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine rootGroup_le_centralizer_heisP_of_toStd_rt hσ hr ?_ (toStd_bc2 hr).1 ?_ ?_
    · simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
    · exact Sum.inl_ne_inr
    · simpa [Sum.swap, Sum.inl.injEq, bcLastIdx] using
      (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
  · refine rootGroup_le_centralizer_heisP_of_toStd_rt hσ hr ?_
      (toStd_bc2 hr).2.2.2.2.1 ?_ ?_
    · simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
    · exact Sum.inl_ne_inr
    · exact Sum.inl_ne_inr
  · refine rootGroup_le_centralizer_heisP_of_toStd_rt_self hσ hr (toStd_bc2 hr).2.2.2.2.2 ?_
    · exact Sum.inl_ne_inr

theorem heisP_inf_bc2Q0 :
    X (Pi.single (bcPrevIdx r hr) 1 +
        Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ⊓ bc2Q0 hσ hr ≤
      X (2 • Pi.single (bcPrevIdx r hr) 1 +
        2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
  intro x hx
  obtain ⟨hxP, hxQ⟩ := hx
  obtain ⟨u, v, huv, rfl⟩ :=
    (mem_rootGroup_iff_suHeis hσ (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.2.2.1 x).mp hxP
  obtain ⟨g, hg⟩ := bc2Q0_le_range_oddEmb hσ hr hxQ
  have h1 : mat σ (2 * r + 1) (oddEmb σ r g)
      (crd (Sum.inl (bcPrevIdx r hr))) (midIdx (2 * r + 1)
        (Nat.not_even_two_mul_add_one r)) = 0 :=
    mat_oddEmb_apply_mid (r := r) g (crd_ne_midIdx (Nat.not_even_two_mul_add_one r)
      (Sum.inl (bcPrevIdx r hr)))
  rw [hg, mat_suHeis_apply_mid hσ (Nat.not_even_two_mul_add_one r) huv] at h1
  subst u
  rw [suHeis_zero_left hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcPrevIdx r hr)) v]
  exact suLong_mem hσ (Sum.inl (bcPrevIdx r hr)) (toStd_bc2 hr).2.2.2.2.2 v
private lemma rootGroup_le_flagSubgroup_of_toStd_rt
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    {b : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (hab : idx (Sum.inl (bcPrevIdx r hr)) ≠ idx b)
    (hγ : toStd (2 * r + 1) γ = rt (Sum.inl (bcPrevIdx r hr)) b) :
    X γ ≤ flagSubgroup σ (Sum.inl (bcPrevIdx r hr)) := by
  intro g hg
  obtain ⟨t, rfl⟩ := (mem_rootGroup_iff_suElt_odd hσ hab hγ g).mp hg
  exact suElt_mem_flagSubgroup hσ hab t
private lemma rootGroup_le_flagSubgroup_of_toStd_rt_self
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : toStd (2 * r + 1) γ = rt (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcPrevIdx r hr))) :
    X γ ≤ flagSubgroup σ (Sum.inl (bcPrevIdx r hr)) := by
  intro g hg
  obtain ⟨t, _ht, rfl⟩ :=
    (mem_rootGroup_iff_suLong_odd hσ (Sum.inl (bcPrevIdx r hr)) hγ g).mp hg
  exact suLong_mem_flagSubgroup (Sum.inl (bcPrevIdx r hr)) t
private lemma rootGroup_heisP_le_flagSubgroup :
    X (Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (by omega)) 1) ≤
      flagSubgroup σ (Sum.inl (bcPrevIdx r hr)) := by
  intro g hg
  obtain ⟨u, v, _huv, rfl⟩ :=
    (mem_rootGroup_iff_suHeis hσ (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.2.2.1 g).mp hg
  exact suHeis_mem_flagSubgroup hσ (Nat.not_even_two_mul_add_one r)
    (Sum.inl (bcPrevIdx r hr)) u v
private lemma bc2Qe1_le_flagSubgroup :
    bc2Qe1 hσ hr ≤ flagSubgroup σ (Sum.inl (bcPrevIdx r hr)) := by
  rw [bc2Qe1]
  refine sup_le ?_ ?_
  · rw [bc2Q0]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine rootGroup_le_flagSubgroup_of_toStd_rt hσ hr ?_ (toStd_bc2 hr).1
      simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
    · refine rootGroup_le_flagSubgroup_of_toStd_rt hσ hr ?_ (toStd_bc2 hr).2.2.2.2.1
      simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
    · exact rootGroup_le_flagSubgroup_of_toStd_rt_self hσ hr (toStd_bc2 hr).2.2.2.2.2
  · exact rootGroup_heisP_le_flagSubgroup hσ hr

theorem heisL_inf_bc2Qe1 :
    X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ⊓ bc2Qe1 hσ hr = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxL, hxQ⟩ := hx
  obtain ⟨u, v, huv, rfl⟩ :=
    (mem_rootGroup_iff_suHeis hσ (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.1 x).mp hxL
  have hflag := bc2Qe1_le_flagSubgroup hσ hr hxQ
  have huv' : u = 0 ∧ v = 0 :=
    (suHeis_mem_flagSubgroup_iff hσ (Nat.not_even_two_mul_add_one r) ?_ huv).mp hflag
  · rw [huv'.1, huv'.2, suHeis_zero_left hσ (Nat.not_even_two_mul_add_one r)
      (Sum.inl (bcLastIdx r (by omega))) 0, suLong_zero]
    exact one_mem ⊥
  · simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
private lemma suElt_alphaP_mem_bc2Qe1 (t : F) :
    suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (by omega))) t ∈
      bc2Qe1 hσ hr := by
  have hab : idx (Sum.inl (bcPrevIdx r hr)) ≠
      idx (Sum.inr (bcLastIdx r (by omega))) := by
    simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
  have h := suElt_mem hσ hab (toStd_bc2 hr).1 t
  rw [bc2Qe1, bc2Q0]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left h))
private lemma suElt_alphaP_two_mem_bc2Qe1 (t : F) :
    suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (by omega))) t ∈
      bc2Qe1 hσ hr := by
  have hab : idx (Sum.inl (bcPrevIdx r hr)) ≠
      idx (Sum.inl (bcLastIdx r (by omega))) := by
    simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
  have h := suElt_mem hσ hab (toStd_bc2 hr).2.2.2.2.1 t
  rw [bc2Qe1, bc2Q0]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right h))
private lemma suLong_alphaP_two_mem_bc2Qe1 (t : F) :
    suLong σ (Sum.inl (bcPrevIdx r hr)) t ∈ bc2Qe1 hσ hr := by
  have h := suLong_mem hσ (Sum.inl (bcPrevIdx r hr)) (toStd_bc2 hr).2.2.2.2.2 t
  rw [bc2Qe1, bc2Q0]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h)
private lemma suHeis_alphaP_mem_bc2Qe1 (u v : F) :
    suHeis σ hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcPrevIdx r hr)) u v ∈
      bc2Qe1 hσ hr := by
  have h := suHeis_mem hσ (Nat.not_even_two_mul_add_one r) (toStd_bc2 hr).2.2.2.1 u v
  rw [bc2Qe1, bc2Q0]
  exact Subgroup.mem_sup_right h
private lemma idx_inl_ne_idx_inl :
    idx (Sum.inl (bcPrevIdx r hr)) ≠ idx (Sum.inl (bcLastIdx r (by omega))) := by
  simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
private lemma idx_inl_ne_idx_inr :
    idx (Sum.inl (bcPrevIdx r hr)) ≠ idx (Sum.inr (bcLastIdx r (by omega))) := by
  simpa [idx, bcLastIdx] using (Ne.symm (bcLastIdx_ne_bcPrevIdx (r := r) hr))
private lemma conj_suElt_alphaP_mem_bc2Qe1 (u v t : F)
    (h : v + σ v + σ u * u = 0) :
    suHeis σ hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcLastIdx r (by omega))) u v *
        suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (by omega))) t *
        (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v)⁻¹ ∈ bc2Qe1 hσ hr := by
  have hform := conj_suHeis_suElt_swap hσ (Nat.not_even_two_mul_add_one r)
    (a := Sum.inl (bcPrevIdx r hr)) (b := Sum.inl (bcLastIdx r (by omega)))
    (idx_inl_ne_idx_inl (r := r) hr) t h
  rw [show Sum.swap (Sum.inl (bcLastIdx r (by omega))) =
    Sum.inr (bcLastIdx r (by omega)) from rfl] at hform
  rw [hform]
  exact mul_mem
    (inv_mem (mul_mem (suHeis_alphaP_mem_bc2Qe1 hσ hr (t * u) (σ t * t * v))
      (suElt_alphaP_two_mem_bc2Qe1 hσ hr (t * σ v))))
    (suElt_alphaP_mem_bc2Qe1 hσ hr t)
private lemma conj_suElt_alphaP_two_mem_bc2Qe1 (u v t : F) :
    suHeis σ hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcLastIdx r (by omega))) u v *
        suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (by omega))) t *
        (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v)⁻¹ ∈ bc2Qe1 hσ hr := by
  have hcomm : suHeis σ hσ (Nat.not_even_two_mul_add_one r)
        (Sum.inl (bcLastIdx r (by omega))) u v *
        suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (by omega))) t =
      suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (by omega))) t *
        suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v :=
    commutatorElement_eq_one_iff_mul_comm.mp
      (suHeis_comm_suElt hσ (Nat.not_even_two_mul_add_one r)
        (idx_inl_ne_idx_inl (r := r) hr) Sum.inl_ne_inr Sum.inl_ne_inr u v t)
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact suElt_alphaP_two_mem_bc2Qe1 hσ hr t
private lemma conj_suLong_alphaP_two_mem_bc2Qe1 (u v t : F) :
    suHeis σ hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcLastIdx r (by omega))) u v *
        suLong σ (Sum.inl (bcPrevIdx r hr)) t *
        (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v)⁻¹ ∈ bc2Qe1 hσ hr := by
  have hcomm : suHeis σ hσ (Nat.not_even_two_mul_add_one r)
        (Sum.inl (bcLastIdx r (by omega))) u v *
        suLong σ (Sum.inl (bcPrevIdx r hr)) t =
      suLong σ (Sum.inl (bcPrevIdx r hr)) t *
        suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v :=
    commutatorElement_eq_one_iff_mul_comm.mp
      (suHeis_comm_suLong hσ (Nat.not_even_two_mul_add_one r) Sum.inl_ne_inr u v t)
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact suLong_alphaP_two_mem_bc2Qe1 hσ hr t
private lemma conj_suHeis_alphaP_mem_bc2Qe1 (u v u' v' : F)
    (h : v + σ v + σ u * u = 0) (h' : v' + σ v' + σ u' * u' = 0) :
    suHeis σ hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcLastIdx r (by omega))) u v *
        suHeis σ hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcPrevIdx r hr)) u' v' *
        (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v)⁻¹ ∈ bc2Qe1 hσ hr := by
  rw [conj_suHeis_suHeis hσ (Nat.not_even_two_mul_add_one r)
    (idx_inl_ne_idx_inl (r := r) hr) h h']
  exact mul_mem (suElt_alphaP_two_mem_bc2Qe1 hσ hr (σ u * u'))
    (suHeis_alphaP_mem_bc2Qe1 hσ hr u' v')
private lemma conj_mem_bc2Qe1 {x : SU σ (2 * r + 1)}
    (hx : x ∈ X (Pi.single (bcLastIdx r (by omega)) 1))
    {y : SU σ (2 * r + 1)} (hy : y ∈ bc2Qe1 hσ hr) :
    x * y * x⁻¹ ∈ bc2Qe1 hσ hr := by
  obtain ⟨u, v, h, rfl⟩ :=
    (mem_rootGroup_iff_suHeis hσ (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.1 x).mp hx
  have hmap : Subgroup.map (MulAut.conj (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
      (Sum.inl (bcLastIdx r (by omega))) u v)).toMonoidHom (bc2Qe1 hσ hr) ≤ bc2Qe1 hσ hr := by
    rw [bc2Qe1, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [bc2Q0, Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨t, rfl⟩ :=
          (mem_rootGroup_iff_suElt_odd hσ (idx_inl_ne_idx_inr (r := r) hr)
            (toStd_bc2 hr).1 g).mp hg
        change MulAut.conj (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v)
          (suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inr (bcLastIdx r (by omega))) t) ∈
          bc2Qe1 hσ hr
        rw [MulAut.conj_apply]
        exact conj_suElt_alphaP_mem_bc2Qe1 hσ hr u v t h
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨t, rfl⟩ :=
          (mem_rootGroup_iff_suElt_odd hσ (idx_inl_ne_idx_inl (r := r) hr)
            (toStd_bc2 hr).2.2.2.2.1 g).mp hg
        change MulAut.conj (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v)
          (suElt σ hσ (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcLastIdx r (by omega))) t) ∈
          bc2Qe1 hσ hr
        rw [MulAut.conj_apply]
        exact conj_suElt_alphaP_two_mem_bc2Qe1 hσ hr u v t
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨t, _ht, rfl⟩ :=
          (mem_rootGroup_iff_suLong_odd hσ (Sum.inl (bcPrevIdx r hr))
            (toStd_bc2 hr).2.2.2.2.2 g).mp hg
        change MulAut.conj (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
          (Sum.inl (bcLastIdx r (by omega))) u v)
          (suLong σ (Sum.inl (bcPrevIdx r hr)) t) ∈ bc2Qe1 hσ hr
        rw [MulAut.conj_apply]
        exact conj_suLong_alphaP_two_mem_bc2Qe1 hσ hr u v t
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨u', v', h', rfl⟩ :=
        (mem_rootGroup_iff_suHeis hσ (Nat.not_even_two_mul_add_one r)
          (toStd_bc2 hr).2.2.2.1 g).mp hg
      change MulAut.conj (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
        (Sum.inl (bcLastIdx r (by omega))) u v)
        (suHeis σ hσ (Nat.not_even_two_mul_add_one r) (Sum.inl (bcPrevIdx r hr)) u' v') ∈
        bc2Qe1 hσ hr
      rw [MulAut.conj_apply]
      exact conj_suHeis_alphaP_mem_bc2Qe1 hσ hr u v u' v' h h'
  have hy' : MulAut.conj (suHeis σ hσ (Nat.not_even_two_mul_add_one r)
      (Sum.inl (bcLastIdx r (by omega))) u v) y ∈ bc2Qe1 hσ hr :=
    hmap (Subgroup.mem_map_of_mem _ hy)
  rw [← MulAut.conj_apply]
  exact hy'

theorem heisL_le_normalizer :
    X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ≤
      Subgroup.normalizer (bc2Qe1 hσ hr : Set (SU σ (2 * r + 1))) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_bc2Qe1 hσ hr hx hy
  · intro hy
    have h := conj_mem_bc2Qe1 hσ hr (inv_mem hx) hy
    simpa only [MulAut.conj_apply, mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left]
      using h

omit [CharP F 2] in
private lemma rootGroup_two_smul_single_L_le :
    X (2 • Pi.single (bcLastIdx r (by omega)) 1) ≤
      X (Pi.single (bcLastIdx r (by omega)) 1) := by
  intro x hx
  obtain ⟨c, _hc, rfl⟩ :=
    (mem_rootGroup_iff_suLong_odd hσ (Sum.inl (bcLastIdx r (by omega)))
      (toStd_bc2 hr).2.2.1 x).mp hx
  rw [← suHeis_zero_left hσ (Nat.not_even_two_mul_add_one r)
    (Sum.inl (bcLastIdx r (by omega))) c]
  exact suHeis_mem hσ (Nat.not_even_two_mul_add_one r) (toStd_bc2 hr).2.1 0 c

omit [CharP F 2] in
private lemma X_alphaP_le_bc2Q0 :
    X (Pi.single (bcPrevIdx r hr) 1) ≤ bc2Q0 hσ hr := by
  rw [bc2Q0]
  exact le_sup_of_le_left (le_sup_of_le_left le_rfl)

omit [CharP F 2] in
private lemma X_alphaP_two_le_bc2Q0 :
    X (Pi.single (bcPrevIdx r hr) 1 + 2 • Pi.single (bcLastIdx r (by omega)) 1) ≤
      bc2Q0 hσ hr := by
  rw [bc2Q0]
  exact le_sup_of_le_left (le_sup_of_le_right le_rfl)

omit [CharP F 2] in
private lemma X_alphaP_two_two_le_bc2Q0 :
    X (2 • Pi.single (bcPrevIdx r hr) 1 + 2 • Pi.single (bcLastIdx r (by omega)) 1) ≤
      bc2Q0 hσ hr := by
  rw [bc2Q0]
  exact le_sup_of_le_right le_rfl

omit [CharP F 2] in
private lemma bc2Q0_le_bc2Qe1 : bc2Q0 hσ hr ≤ bc2Qe1 hσ hr := le_sup_left

omit [CharP F 2] in
private lemma X_heisP_le_bc2Qe1 :
    X (Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (by omega)) 1) ≤
      bc2Qe1 hσ hr := by
  rw [bc2Qe1]
  exact le_sup_right

theorem rootGroup_le_bc2U {p f : ℕ} [Finite F] [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcPrevIdx r hr)
      (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
      (CFSG.LieType.Steinberg.RootSystem.ofCartan (isFiniteType_cartan (2 * r + 1))
        (divisible (2 * r + 1))).pos) :
    X γ ≤ bc2Qe1 hσ hr ⊔ X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
  obtain ⟨x, y, hxy, hγeq⟩ := (mem_pairRoots_bc2_pos hF hr).mp hγ
  rw [hγeq]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [one_smul, zero_smul, add_zero]
    exact ((X_alphaP_le_bc2Q0 hσ hr).trans (bc2Q0_le_bc2Qe1 hσ hr)).trans le_sup_left
  · simp only [one_smul, zero_smul, zero_add]
    exact (le_sup_right : X (Pi.single (bcLastIdx r (by omega)) 1) ≤
      bc2Qe1 hσ hr ⊔ X (Pi.single (bcLastIdx r (by omega)) 1))
  · simp only [zero_smul, zero_add]
    exact (rootGroup_two_smul_single_L_le hσ hr).trans
      (le_sup_right : X (Pi.single (bcLastIdx r (by omega)) 1) ≤
        bc2Qe1 hσ hr ⊔ X (Pi.single (bcLastIdx r (by omega)) 1))
  · simp only [one_smul]
    exact (X_heisP_le_bc2Qe1 hσ hr).trans le_sup_left
  · simp only [one_smul]
    exact ((X_alphaP_two_le_bc2Q0 hσ hr).trans (bc2Q0_le_bc2Qe1 hσ hr)).trans le_sup_left
  · exact ((X_alphaP_two_two_le_bc2Q0 hσ hr).trans (bc2Q0_le_bc2Qe1 hσ hr)).trans le_sup_left

theorem rootGroup_unitaryLongRoot_odd (h : 2 ≤ 2 * r + 1) (h' : 2 ≤ 2 * r) :
    X (unitaryLongRoot (2 * r + 1) h) =
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r)
        (unitaryLongRoot (2 * r) h')).map (oddEmb σ r) ∧
    X (unitaryLongRoot (2 * r + 1) h) ≤
      X (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
  have hodd : unitaryLongRoot (2 * r + 1) h = 2 • Pi.single (bcLastIdx r (by omega)) 1 :=
    unitaryLongRoot_odd h
  have hmap := map_rootGroup_oddEmb (r := r) hσ (unitaryLongRoot (2 * r) h')
  rw [rootCast_unitaryLongRoot (r := r) hr] at hmap
  constructor
  · rw [hodd, hmap, unitaryLongRoot_odd (by omega)]
  · rw [hodd]
    exact rootGroup_two_smul_single_L_le (r := r) hσ hr
private lemma levelPerm_comp_lastIdxOdd {n : ℕ} (hn : ¬ Even n) {k : Fin (n / 2)}
    (hk : k.val + 1 < n / 2) :
    levelPerm k ∘ lastIdxOdd ⟨k.val + 1, hk⟩ hn = lastIdxOdd k hn := by
  have hnodd : n = 2 * (n / 2) + 1 := by
    rw [Nat.not_even_iff_odd] at hn
    obtain ⟨r, hr⟩ := hn
    omega
  have hklt : k.val < n / 2 := k.isLt
  have hmid_low : midIdx n hn ≠ lowIdx k := by
    apply Fin.ne_of_val_ne
    simp only [midIdx, val_lowIdx]
    omega
  have hmid_low' : midIdx n hn ≠ lowIdx ⟨k.val + 1, hk⟩ := by
    apply Fin.ne_of_val_ne
    simp only [midIdx, val_lowIdx]
    omega
  have hmid_rev : midIdx n hn ≠ Fin.rev (lowIdx k) := by
    apply Fin.ne_of_val_ne
    simp only [midIdx, lowIdx, Fin.val_rev, Fin.val_mk]
    omega
  have hmid_rev' : midIdx n hn ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := by
    apply Fin.ne_of_val_ne
    simp only [midIdx, lowIdx, Fin.val_rev, Fin.val_mk]
    omega
  funext i
  fin_cases i
  · change levelPerm k (lowIdx ⟨k.val + 1, hk⟩) = lowIdx k
    rw [levelPerm, dif_pos hk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (a := (lowIdx k).rev)
        (b := (lowIdx ⟨k.val + 1, hk⟩).rev) (x := lowIdx ⟨k.val + 1, hk⟩)
        (lowIdx_ne_rev (n := n) ⟨k.val + 1, hk⟩ k)
        (lowIdx_ne_rev (n := n) ⟨k.val + 1, hk⟩ ⟨k.val + 1, hk⟩),
      Equiv.swap_apply_right]
  · change levelPerm k (midIdx n hn) = midIdx n hn
    rw [levelPerm, dif_pos hk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (a := (lowIdx k).rev)
        (b := (lowIdx ⟨k.val + 1, hk⟩).rev) (x := midIdx n hn) hmid_rev hmid_rev',
      Equiv.swap_apply_of_ne_of_ne (a := lowIdx k) (b := lowIdx ⟨k.val + 1, hk⟩)
        (x := midIdx n hn) hmid_low hmid_low']
  · change levelPerm k (Fin.rev (lowIdx ⟨k.val + 1, hk⟩)) = Fin.rev (lowIdx k)
    rw [levelPerm, dif_pos hk, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (a := lowIdx k) (b := lowIdx ⟨k.val + 1, hk⟩)
        (x := (lowIdx k).rev)
        (lowIdx_ne_rev (n := n) k k).symm
        (lowIdx_ne_rev (n := n) ⟨k.val + 1, hk⟩ k).symm]
private lemma extendMat_eq_blockMat {n : ℕ} (e : Fin 3 → Fin n) (he : Function.Injective e)
    (M : Matrix (Fin 3) (Fin 3) F) :
    CFSG.AGLEmbedding.LeviBlock.extendMat he M =
      CFSG.RankThree.CentralLiftU.blockMat e M := by
  symm
  refine eq_extendMat_of_isBlkOn he ?_ ?_
  · intro a b h
    rcases h with ha | hb
    · exact CFSG.RankThree.CentralLiftU.blockMat_apply_of_notMem_left M
        (fun i hi => ha ⟨i, hi⟩) b
    · exact CFSG.RankThree.CentralLiftU.blockMat_apply_of_notMem_right M
        (fun i hi => hb ⟨i, hi⟩) a
  · ext i j
    rw [Matrix.submatrix_apply, CFSG.RankThree.CentralLiftU.blockMat_apply_e he M i j]

theorem levelWeyl_one_conj_su3Emb {n : ℕ} (hn : ¬ Even n) {k : Fin (n / 2)}
    (hk : k.val + 1 < n / 2) (A : SU σ 3) :
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ k * su3Emb σ hn ⟨k.val + 1, hk⟩ A *
      (levelWeyl hσ ⟨1, one_mem_traceZero⟩ k)⁻¹ = su3Emb σ hn k A := by
  apply mat_injective
  rw [levelWeyl_one_inv]
  rw [map_mul, map_mul]
  have hsu3 : ∀ {j : Fin (n / 2)}, mat σ n (su3Emb σ hn j A) =
      CFSG.AGLEmbedding.LeviBlock.extendMat (lastIdxOdd_injective' hn j) (mat σ 3 A) := by
    intro j
    rw [show su3Emb σ hn j = suEmbed σ (lastIdxOdd_injective' hn j) (lastIdxOdd_rev hn)
      from rfl]
    exact mat_suEmbed σ (lastIdxOdd_injective' hn j) (lastIdxOdd_rev hn) A
  have hw : mat σ n (levelWeyl hσ ⟨1, one_mem_traceZero⟩ k) =
      CFSG.LieType.Universal.SpecialLinear.signedPerm (levelPerm k) (1 : Fin n → F) := by
    rw [mat_apply, coe_levelWeyl hσ (show ((⟨1, one_mem_traceZero⟩ : traceZero σ) : F) ≠ 0
      from one_ne_zero) k, levelSign_one]
  rw [hsu3, hsu3, hw]
  rw [extendMat_eq_blockMat (lastIdxOdd ⟨k.val + 1, hk⟩ hn)
      (lastIdxOdd_injective' hn ⟨k.val + 1, hk⟩) (mat σ 3 A),
    extendMat_eq_blockMat (lastIdxOdd k hn) (lastIdxOdd_injective' hn k) (mat σ 3 A)]
  have hconj := CFSG.RankThree.CentralLiftU.conj_signedPerm_blockMat
    (lastIdxOdd ⟨k.val + 1, hk⟩ hn) (σ := levelPerm k)
    (s := (1 : Fin n → F)) (t := (1 : Fin n → F)) (by intro x; simp) (mat σ 3 A)
  rw [CFSG.LieType.Universal.Unitary.levelPerm_symm] at hconj
  rw [hconj, levelPerm_comp_lastIdxOdd hn hk]
  have hdiag : diagonal ((1 : Fin n → F) ∘ lastIdxOdd ⟨k.val + 1, hk⟩ hn) = 1 := by
    have hone : ((1 : Fin n → F) ∘ lastIdxOdd ⟨k.val + 1, hk⟩ hn) = 1 := by
      funext a
      rfl
    rw [hone]
    exact diagonal_one
  rw [hdiag, one_mul]
  have hdiag2 : (fun a => (1 : Fin n → F)
      ((levelPerm k) (lastIdxOdd ⟨k.val + 1, hk⟩ hn a))) = 1 := rfl
  rw [hdiag2]
  change CFSG.RankThree.CentralLiftU.blockMat (lastIdxOdd k hn)
      ((mat σ 3 A) * diagonal (fun _ => (1 : F))) =
    CFSG.RankThree.CentralLiftU.blockMat (lastIdxOdd k hn) ((mat σ 3 A))
  rw [diagonal_one, mul_one]

end CFSG.Timmesfeld.Transvection.Pres
