module

public import CFSG.Sporadic.Th.Recog.MFactsB.CentT
public import CFSG.Sporadic.Th.Recog.MFactsB.Complement
public import CFSG.Quasithin.H13.L32NQ8Pow
public import CFSG.Quasithin.EmptyFaithful.S143UA
public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped commutatorElement MatrixGroups

section Basic


@[expose] noncomputable def B₁ : Subgroup ↥Max3.M := Subgroup.closure {x₁, y₁}

@[expose] noncomputable def B₂ : Subgroup ↥Max3.M := Subgroup.closure {x₂, y₂}

@[expose] noncomputable def H₁ : Subgroup ↥Max3.M := B₁ ⊔ Subgroup.zpowers ω₁

@[expose] noncomputable def H₂ : Subgroup ↥Max3.M := B₂ ⊔ Subgroup.zpowers ω₂

private theorem q8_square_commutator {x y ω z : ↥Max3.M}
    (hx2 : x * x = z) (hzz : z * z = 1) (hω3 : ω ^ 3 = 1)
    (hy : y = ω * x * ω⁻¹) (h1 : y * x = x ^ 3 * y) (h2 : ω * y = y * x * ω) :
    y * y = z ∧ ⁅x, y⁆ = z := by
  have hωy : ω * y * ω⁻¹ = y * x := by rw [h2]; group
  have hx4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = (x * x) * (x * x) := by rw [pow_two, pow_two]
      _ = 1 := by rw [hx2, hzz]
  have hx3 : x ^ 3 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show 3 + 1 = 4 by norm_num, hx4]
  have hyx : y * x = x⁻¹ * y := by rw [h1, hx3]
  have hyxy : y * x * y⁻¹ = x⁻¹ := by rw [hyx]; group
  have hω2 : ω ^ 2 = ω * ω := pow_two ω
  have hω2x : ω ^ 2 * x * (ω ^ 2)⁻¹ = y * x := by
    rw [hω2]
    calc (ω * ω) * x * (ω * ω)⁻¹ = ω * (ω * x * ω⁻¹) * ω⁻¹ := by group
      _ = ω * y * ω⁻¹ := by rw [← hy]
      _ = y * x := hωy
  have hω3pow : ω ^ 3 = (ω * ω) * ω := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  have hω3x : ω ^ 3 * x * (ω ^ 3)⁻¹ = y * x * y := by
    rw [hω3pow]
    calc ((ω * ω) * ω) * x * ((ω * ω) * ω)⁻¹ =
          ω * (ω ^ 2 * x * (ω ^ 2)⁻¹) * ω⁻¹ := by
            rw [← hω2]
            group
      _ = ω * (y * x) * ω⁻¹ := by rw [hω2x]
      _ = (ω * y * ω⁻¹) * (ω * x * ω⁻¹) := by group
      _ = (y * x) * y := by rw [hωy, ← hy]
  have hx_eq : x = y * x * y := by
    calc x = ω ^ 3 * x * (ω ^ 3)⁻¹ := by rw [hω3]; group
      _ = y * x * y := hω3x
  have hx_eq' : x = x⁻¹ * (y * y) := by
    calc x = y * x * y := hx_eq
      _ = (x⁻¹ * y) * y := by rw [hyx]
      _ = x⁻¹ * (y * y) := by group
  have hxx : x * x = y * y := by
    have h := congrArg (fun t => x * t) hx_eq'
    simpa [mul_assoc] using h
  have hyy : y * y = z := hxx.symm.trans hx2
  have hyx' : y * x⁻¹ * y⁻¹ = x := by
    have := congrArg Inv.inv hyxy
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  have hcomm : ⁅x, y⁆ = z := by
    rw [commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      _ = x * x := by rw [hyx']
      _ = z := hx2
  exact ⟨hyy, hcomm⟩

private theorem ne_of_relation {G : Type*} [Group G] {x y z : G}
    (hx2 : x * x = z) (hzz : z * z = 1) (hz : z ≠ 1)
    (h1 : y * x = x ^ 3 * y) : y ≠ x := by
  intro h
  have hx4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = (x * x) * (x * x) := by rw [pow_two, pow_two]
      _ = 1 := by rw [hx2, hzz]
  rw [h] at h1
  rw [← pow_succ, show 3 + 1 = 4 by norm_num, hx4] at h1
  exact hz (hx2.symm.trans h1)

private theorem zM_conj_uM : uM * zM * uM⁻¹ = zM := by
  have hz : zM ∈ Subgroup.center ↥Max3.M := by
    simpa only [zM] using Max3.z_mem_center_M
  have hcomm : Commute zM uM := (Subgroup.mem_center_iff.mp hz uM).symm
  rw [hcomm.symm.eq]
  group

private theorem dM_conj_y₁ : (MulAut.conj dM) y₁ = ω₁⁻¹ * x₁⁻¹ * ω₁ := by
  have hω : (MulAut.conj dM) ω₁ = ω₁⁻¹ := by
    rw [MulAut.conj_apply, dM_inv, dM_conj_ω₁]
  have hx : (MulAut.conj dM) x₁ = x₁⁻¹ := by
    rw [MulAut.conj_apply, dM_inv, dM_conj_x₁]
  rw [y₁, map_mul, map_mul, map_inv, hω, hx, inv_inv]

private theorem x₂_pow_two : x₂ * x₂ = zM := by
  calc x₂ * x₂ = (uM * x₁ * uM⁻¹) * (uM * x₁ * uM⁻¹) := by rw [x₂]
    _ = uM * (x₁ * x₁) * uM⁻¹ := by group
    _ = uM * zM * uM⁻¹ := by rw [← pow_two, x₁_pow_two]
    _ = zM := zM_conj_uM

private theorem ω₂_pow_three : ω₂ ^ 3 = 1 := by
  calc ω₂ ^ 3 = (uM * ω₁ * uM⁻¹) ^ 3 := by rw [ω₂]
    _ = uM * ω₁ ^ 3 * uM⁻¹ := by
          rw [show uM * ω₁ * uM⁻¹ = (MulAut.conj uM) ω₁ by rw [MulAut.conj_apply]]
          rw [← map_pow, MulAut.conj_apply]
    _ = uM * 1 * uM⁻¹ := by rw [ω₁_pow_three]
    _ = 1 := by group

private theorem orderOf_ω₂ : orderOf ω₂ = 3 := by
  have h : orderOf ((MulAut.conj uM) ω₁) = orderOf ω₁ := (MulAut.conj uM).orderOf_eq ω₁
  rw [MulAut.conj_apply] at h
  rw [ω₂, h, orderOf_ω₁]

private theorem y₂_eq_conj : y₂ = ω₂ * x₂ * ω₂⁻¹ := by
  rw [y₂, ω₂, x₂, y₁]
  group

private theorem y₂_mul_x₂ (h1 : y₁ * x₁ = x₁ ^ 3 * y₁) :
    y₂ * x₂ = x₂ ^ 3 * y₂ := by
  have h := congrArg (MulAut.conj uM) h1
  rw [map_mul, map_mul, map_pow, MulAut.conj_apply] at h
  rw [y₂, x₂]
  exact h

private theorem ω₂_mul_y₂ (h2 : ω₁ * y₁ = y₁ * x₁ * ω₁) :
    ω₂ * y₂ = y₂ * x₂ * ω₂ := by
  have h := congrArg (MulAut.conj uM) h2
  rw [map_mul, map_mul, map_mul, MulAut.conj_apply] at h
  rw [ω₂, y₂, x₂]
  exact h

private theorem iso_B₁ (hyy : y₁ * y₁ = zM) (hcomm : ⁅x₁, y₁⁆ = zM) :
    Nonempty (↥B₁ ≃* QuaternionGroup 2) := by
  have hxx : x₁ * x₁ = zM := by simpa only [pow_two] using x₁_pow_two
  have hmain :=
    CFSG.Quasithin.H13.Q8Pow.nonempty_closure_mulEquiv_q8 (x := x₁) (y := y₁) (z := zM)
      hxx hyy zM_ne_one zM_mul_self hcomm
  change Nonempty (↥(Subgroup.closure {x₁, y₁}) ≃* QuaternionGroup 2)
  exact hmain

private theorem iso_B₂ (hyy : y₂ * y₂ = zM) (hcomm : ⁅x₂, y₂⁆ = zM) :
    Nonempty (↥B₂ ≃* QuaternionGroup 2) := by
  have hxx : x₂ * x₂ = zM := x₂_pow_two
  have hmain :=
    CFSG.Quasithin.H13.Q8Pow.nonempty_closure_mulEquiv_q8 (x := x₂) (y := y₂) (z := zM)
      hxx hyy zM_ne_one zM_mul_self hcomm
  change Nonempty (↥(Subgroup.closure {x₂, y₂}) ≃* QuaternionGroup 2)
  exact hmain

private theorem conj_ω₁_le_B₁ (hωy : ω₁ * y₁ * ω₁⁻¹ = y₁ * x₁) :
    B₁.map (MulAut.conj ω₁) ≤ B₁ := by
  rw [B₁, MonoidHom.map_closure, Subgroup.closure_le]
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases hw with rfl | hw
  · have h : (MulAut.conj ω₁) x₁ = y₁ := by rw [MulAut.conj_apply, y₁]
    change (MulAut.conj ω₁) x₁ ∈ B₁
    rw [h]
    exact Subgroup.subset_closure (by simp)
  · rw [Set.mem_singleton_iff] at hw
    subst hw
    have h : (MulAut.conj ω₁) y₁ = y₁ * x₁ := by rw [MulAut.conj_apply, hωy]
    change (MulAut.conj ω₁) y₁ ∈ B₁
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

private theorem conj_ω₂_le_B₂ (hy₂ : y₂ = ω₂ * x₂ * ω₂⁻¹)
    (hωy : ω₂ * y₂ * ω₂⁻¹ = y₂ * x₂) :
    B₂.map (MulAut.conj ω₂) ≤ B₂ := by
  rw [B₂, MonoidHom.map_closure, Subgroup.closure_le]
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases hw with rfl | hw
  · have h : (MulAut.conj ω₂) x₂ = y₂ := by rw [MulAut.conj_apply, ← hy₂]
    change (MulAut.conj ω₂) x₂ ∈ B₂
    rw [h]
    exact Subgroup.subset_closure (by simp)
  · rw [Set.mem_singleton_iff] at hw
    subst hw
    have h : (MulAut.conj ω₂) y₂ = y₂ * x₂ := by rw [MulAut.conj_apply, hωy]
    change (MulAut.conj ω₂) y₂ ∈ B₂
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

private theorem iso_H₁ (hyy : y₁ * y₁ = zM) (hcomm : ⁅x₁, y₁⁆ = zM)
    (hne : y₁ ≠ x₁) (hωy : ω₁ * y₁ * ω₁⁻¹ = y₁ * x₁) :
    Nonempty (↥H₁ ≃* SL(2, ZMod 3)) := by
  have hB := iso_B₁ hyy hcomm
  have hn : ∀ b ∈ B₁, ω₁ * b * ω₁⁻¹ ∈ B₁ := by
    intro b hb
    have hb' : (MulAut.conj ω₁).toMonoidHom b ∈
        B₁.map (MulAut.conj ω₁).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj ω₁).toMonoidHom hb
    have h := conj_ω₁_le_B₁ hωy hb'
    change ω₁ * b * ω₁⁻¹ ∈ B₁ at h
    exact h
  have hnt : ∃ b ∈ B₁, ω₁ * b * ω₁⁻¹ ≠ b :=
    ⟨x₁, Subgroup.subset_closure (by simp), by simpa only [y₁] using hne⟩
  change Nonempty (↥(B₁ ⊔ Subgroup.zpowers ω₁) ≃* CFSG.Quasithin.S143.SL23.SL3)
  exact CFSG.Quasithin.S143.SL23.nonempty_mulEquiv_sl23 (B := B₁) (ω := ω₁)
    hB orderOf_ω₁ hn hnt

private theorem iso_H₂ (hyy : y₂ * y₂ = zM) (hcomm : ⁅x₂, y₂⁆ = zM)
    (hne : y₂ ≠ x₂) (hωy : ω₂ * y₂ * ω₂⁻¹ = y₂ * x₂) :
    Nonempty (↥H₂ ≃* SL(2, ZMod 3)) := by
  have hB := iso_B₂ hyy hcomm
  have hn : ∀ b ∈ B₂, ω₂ * b * ω₂⁻¹ ∈ B₂ := by
    intro b hb
    have hb' : (MulAut.conj ω₂).toMonoidHom b ∈
        B₂.map (MulAut.conj ω₂).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj ω₂).toMonoidHom hb
    have h := conj_ω₂_le_B₂ y₂_eq_conj hωy hb'
    change ω₂ * b * ω₂⁻¹ ∈ B₂ at h
    exact h
  have hnt : ∃ b ∈ B₂, ω₂ * b * ω₂⁻¹ ≠ b :=
    ⟨x₂, Subgroup.subset_closure (by simp), by simpa only [← y₂_eq_conj] using hne⟩
  change Nonempty (↥(B₂ ⊔ Subgroup.zpowers ω₂) ≃* CFSG.Quasithin.S143.SL23.SL3)
  exact CFSG.Quasithin.S143.SL23.nonempty_mulEquiv_sl23 (B := B₂) (ω := ω₂)
    hB orderOf_ω₂ hn hnt

private theorem commute_conj {a b c : ↥Max3.M} (hab : Commute a b) (hcb : Commute c b) :
    Commute (c * a * c⁻¹) b := by
  rw [commute_iff_eq]
  have hcib : c⁻¹ * b = b * c⁻¹ := by
    have h := congrArg (fun z => c⁻¹ * z * c⁻¹) hcb.eq
    rw [show c⁻¹ * (c * b) * c⁻¹ = b * c⁻¹ by group,
      show c⁻¹ * (b * c) * c⁻¹ = c⁻¹ * b by group] at h
    exact h.symm
  calc (c * a * c⁻¹) * b = c * a * (c⁻¹ * b) := by group
    _ = c * a * (b * c⁻¹) := by rw [hcib]
    _ = c * (a * b) * c⁻¹ := by group
    _ = c * (b * a) * c⁻¹ := by rw [hab.eq]
    _ = (c * b) * a * c⁻¹ := by group
    _ = (b * c) * a * c⁻¹ := by rw [hcb.eq]
    _ = b * (c * a * c⁻¹) := by group

private theorem H₁_le_centralizer_singleton {g : ↥Max3.M}
    (hx : Commute x₁ g) (hy : Commute y₁ g) (hω : Commute ω₁ g) :
    H₁ ≤ Subgroup.centralizer ({g} : Set ↥Max3.M) := by
  rw [H₁]
  refine sup_le ?_ ?_
  · rw [B₁, Subgroup.closure_le]
    intro s hs
    rcases hs with rfl | hs
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx.eq
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact Subgroup.mem_centralizer_singleton_iff.mpr hy.eq
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hω.eq

private theorem H₂_le_centralizer_singleton {g : ↥Max3.M}
    (hx : Commute x₂ g) (hy : Commute y₂ g) (hω : Commute ω₂ g) :
    H₂ ≤ Subgroup.centralizer ({g} : Set ↥Max3.M) := by
  rw [H₂]
  refine sup_le ?_ ?_
  · rw [B₂, Subgroup.closure_le]
    intro s hs
    rcases hs with rfl | hs
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx.eq
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact Subgroup.mem_centralizer_singleton_iff.mpr hy.eq
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hω.eq

private theorem commute_H₁_H₂ (h₃ : x₁ * x₂ = x₂ * x₁) (h₄ : x₁ * ω₂ = ω₂ * x₁)
    (h₅ : ω₁ * x₂ = x₂ * ω₁) (h₆ : ω₁ * ω₂ = ω₂ * ω₁)
    (hy₂ : y₂ = ω₂ * x₂ * ω₂⁻¹) :
    ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := by
  have hx1x2 : Commute x₁ x₂ := h₃
  have hx1ω2 : Commute x₁ ω₂ := h₄
  have hω1x2 : Commute ω₁ x₂ := h₅
  have hω1ω2 : Commute ω₁ ω₂ := h₆
  have hy1x2 : Commute y₁ x₂ := by
    simpa only [y₁] using commute_conj hx1x2 hω1x2
  have hy1ω2 : Commute y₁ ω₂ := by
    simpa only [y₁] using commute_conj hx1ω2 hω1ω2
  have hx1y2 : Commute x₁ y₂ := by
    have h := commute_conj hx1x2.symm hx1ω2.symm
    rw [← hy₂] at h
    exact h.symm
  have hω1y2 : Commute ω₁ y₂ := by
    have h := commute_conj hω1x2.symm hω1ω2.symm
    rw [← hy₂] at h
    exact h.symm
  have hy1y2 : Commute y₁ y₂ := by
    have h := commute_conj hy1x2.symm hy1ω2.symm
    rw [← hy₂] at h
    exact h.symm
  have hB₂ : B₂ ≤ Subgroup.centralizer (H₁ : Set ↥Max3.M) := by
    rw [B₂, Subgroup.closure_le]
    intro b hb
    change b ∈ Subgroup.centralizer (H₁ : Set ↥Max3.M)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases hb with rfl | hb
    · exact Subgroup.mem_centralizer_singleton_iff.mp
        (H₁_le_centralizer_singleton hx1x2 hy1x2 hω1x2 ha)
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (H₁_le_centralizer_singleton hx1y2 hy1y2 hω1y2 ha)
  have hZ₂ : Subgroup.zpowers ω₂ ≤ Subgroup.centralizer (H₁ : Set ↥Max3.M) := by
    rw [Subgroup.zpowers_le]
    change ω₂ ∈ Subgroup.centralizer (H₁ : Set ↥Max3.M)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (H₁_le_centralizer_singleton hx1ω2 hy1ω2 hω1ω2 ha)
  have hH₂ : H₂ ≤ Subgroup.centralizer (H₁ : Set ↥Max3.M) := by
    rw [H₂]
    exact sup_le hB₂ hZ₂
  intro a ha b hb
  exact Subgroup.mem_centralizer_iff.mp (hH₂ hb) a ha

private theorem dM_mem_normalizer_H₁ : dM ∈ Subgroup.normalizer (H₁ : Set ↥Max3.M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hx_mem : x₁ ∈ H₁ := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hy_mem : y₁ ∈ H₁ := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hω_mem : ω₁ ∈ H₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers ω₁)
  have hmap_le : H₁.map (MulAut.conj dM) ≤ H₁ := by
    rw [H₁, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [B₁, MonoidHom.map_closure, Subgroup.closure_le]
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      rcases hw with rfl | hw
      · have h : (MulAut.conj dM) x₁ = x₁⁻¹ := by
          rw [MulAut.conj_apply, dM_inv, dM_conj_x₁]
        change (MulAut.conj dM) x₁ ∈ H₁
        rw [h]
        exact H₁.inv_mem hx_mem
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        have h : (MulAut.conj dM) y₁ = ω₁⁻¹ * x₁⁻¹ * ω₁ := dM_conj_y₁
        change (MulAut.conj dM) y₁ ∈ H₁
        rw [h]
        exact H₁.mul_mem (H₁.mul_mem (H₁.inv_mem hω_mem) (H₁.inv_mem hx_mem)) hω_mem
    · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have h : (MulAut.conj dM) ω₁ = ω₁⁻¹ := by
        rw [MulAut.conj_apply, dM_inv, dM_conj_ω₁]
      change (MulAut.conj dM) ω₁ ∈ H₁
      rw [h]
      exact H₁.inv_mem hω_mem
  have hd2 : MulAut.conj dM * MulAut.conj dM = 1 := by
    rw [← map_mul, dM_mul_self, map_one]
  have hd2_apply (x : ↥Max3.M) : (MulAut.conj dM) ((MulAut.conj dM) x) = x := by
    have h := congrArg (fun f : MulAut ↥Max3.M => f x) hd2
    simpa using h
  apply le_antisymm hmap_le
  intro h hh
  rw [Subgroup.mem_map]
  exact ⟨(MulAut.conj dM) h, hmap_le (Subgroup.mem_map_of_mem _ hh), hd2_apply h⟩

private theorem H₁_le_centralizer_t :
    H₁ ≤ Subgroup.centralizer ({tLetter} : Set ↥Max3.M) :=
  H₁_le_centralizer_singleton x₁_comm_tLetter y₁_comm_tLetter ω₁_comm_tLetter

private theorem H₂_le_centralizer_t :
    H₂ ≤ Subgroup.centralizer ({tLetter} : Set ↥Max3.M) :=
  H₂_le_centralizer_singleton x₂_comm_tLetter y₂_comm_tLetter ω₂_comm_tLetter

private theorem H₂_le_centralizer_H₁ (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    H₂ ≤ Subgroup.centralizer (H₁ : Set ↥Max3.M) := by
  intro b hb
  change b ∈ Subgroup.centralizer (H₁ : Set ↥Max3.M)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hcomm a ha b hb

private theorem B₂_le_centralizer_H₁ (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    B₂ ≤ Subgroup.centralizer (H₁ : Set ↥Max3.M) :=
  le_trans le_sup_left (H₂_le_centralizer_H₁ hcomm)

private theorem ω₂_mem_centralizer_H₁ (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    ω₂ ∈ Subgroup.centralizer (H₁ : Set ↥Max3.M) :=
  H₂_le_centralizer_H₁ hcomm (Subgroup.mem_sup_right (Subgroup.mem_zpowers ω₂))

private theorem tLetter_mem_centralizer_H₁
    (hH : H₁ ≤ Subgroup.centralizer ({tLetter} : Set ↥Max3.M)) :
    tLetter ∈ Subgroup.centralizer (H₁ : Set ↥Max3.M) := by
  change tLetter ∈ Subgroup.centralizer (H₁ : Set ↥Max3.M)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hH ha)

private theorem centralizer_le_normalizer_H₁ (hCQt : CQt = B₁ ⊔ B₂)
    (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    Subgroup.centralizer ({tLetter} : Set ↥Max3.M) ≤
      Subgroup.normalizer (H₁ : Set ↥Max3.M) := by
  rw [← D₀_sup_zpowers]
  refine sup_le ?_ ?_
  · rw [D₀, hCQt]
    refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
    · exact le_trans le_sup_left Subgroup.le_normalizer
    · exact (B₂_le_centralizer_H₁ hcomm).trans (Subgroup.centralizer_le_normalizer _)
    · exact le_trans le_sup_right Subgroup.le_normalizer
    · exact (Subgroup.zpowers_le.mpr (ω₂_mem_centralizer_H₁ hcomm)).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact Subgroup.zpowers_le.mpr dM_mem_normalizer_H₁
  · rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (H₁ : Set ↥Max3.M)
      (tLetter_mem_centralizer_H₁ H₁_le_centralizer_t)

private theorem card_B₁ (hiso : Nonempty (↥B₁ ≃* QuaternionGroup 2)) :
    Nat.card ↥B₁ = 8 := by
  obtain ⟨e⟩ := hiso
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem card_B₂ (hiso : Nonempty (↥B₂ ≃* QuaternionGroup 2)) :
    Nat.card ↥B₂ = 8 := by
  obtain ⟨e⟩ := hiso
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem mem_CQt_of_mem_Q {g : ↥Max3.M} (hgQ : (g : J) ∈ Max3.Q)
    (hgt : g * tLetter = tLetter * g) : g ∈ CQt := by
  rw [CQt, Subgroup.mem_inf]
  exact ⟨Subgroup.mem_subgroupOf.mpr hgQ,
    Subgroup.mem_centralizer_singleton_iff.mpr hgt⟩

private theorem B₁_le_CQt : B₁ ≤ CQt := by
  rw [B₁, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact mem_CQt_of_mem_Q x₁_mem_Q x₁_comm_tLetter
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact mem_CQt_of_mem_Q y₁_mem_Q y₁_comm_tLetter

private theorem B₂_le_CQt : B₂ ≤ CQt := by
  rw [B₂, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact mem_CQt_of_mem_Q x₂_mem_Q x₂_comm_tLetter
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact mem_CQt_of_mem_Q y₂_mem_Q y₂_comm_tLetter

private theorem x₁_mem_H₁ : x₁ ∈ H₁ := by
  have h : x₁ ∈ B₁ := Subgroup.subset_closure (Set.mem_insert x₁ {y₁})
  exact (show B₁ ≤ B₁ ⊔ Subgroup.zpowers ω₁ from le_sup_left) h

private theorem x₂_mem_H₂ : x₂ ∈ H₂ := by
  have h : x₂ ∈ B₂ := Subgroup.subset_closure (Set.mem_insert x₂ {y₂})
  exact (show B₂ ≤ B₂ ⊔ Subgroup.zpowers ω₂ from le_sup_left) h

private theorem zM_mem_inf : zM ∈ H₁ ⊓ H₂ := by
  refine ⟨?_, ?_⟩
  · change zM ∈ H₁
    have h : zM = x₁ * x₁ := by rw [← x₁_pow_two, pow_two]
    rw [h]
    exact Subgroup.mul_mem _ x₁_mem_H₁ x₁_mem_H₁
  · change zM ∈ H₂
    have h : zM = x₂ * x₂ := x₂_pow_two.symm
    rw [h]
    exact Subgroup.mul_mem _ x₂_mem_H₂ x₂_mem_H₂

private theorem center_card_H₁ (hiso : Nonempty (↥H₁ ≃* SL(2, ZMod 3))) :
    Nat.card ↥(Subgroup.center H₁) = 2 := by
  obtain ⟨e⟩ := hiso
  have hcenter : ↥(Subgroup.center H₁) ≃ ↥(Subgroup.center (SL(2, ZMod 3))) :=
    { toFun := fun z =>
        ⟨e z, by
          rw [Subgroup.mem_center_iff]
          intro h
          obtain ⟨k, rfl⟩ := e.surjective h
          rw [← map_mul, ← map_mul]
          exact congrArg e (Subgroup.mem_center_iff.mp z.2 k)⟩
      invFun := fun z =>
        ⟨e.symm z, by
          rw [Subgroup.mem_center_iff]
          intro h
          apply e.injective
          rw [map_mul, map_mul, e.apply_symm_apply]
          exact Subgroup.mem_center_iff.mp z.2 (e h)⟩
      left_inv := fun z => Subtype.ext (e.symm_apply_apply z)
      right_inv := fun z => Subtype.ext (e.apply_symm_apply z) }
  rw [Nat.card_congr hcenter,
    CFSG.ClassicalInvolution.Q3.Q3T6.Aut.natCard_center_sl2Three]

private theorem card_inf_H₁_H₂ (hiso : Nonempty (↥H₁ ≃* SL(2, ZMod 3)))
    (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    Nat.card ↥(H₁ ⊓ H₂) = 2 := by
  obtain ⟨e⟩ := hiso
  haveI : Finite ↥H₁ := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_congr e.toEquiv, CFSG.ClassicalInvolution.Q3.Q3T6.Aut.sl2Three_natCard]
    norm_num
  have hcard_center : Nat.card ↥(Subgroup.center H₁) = 2 := center_card_H₁ ⟨e⟩
  have hle : H₁ ⊓ H₂ ≤ H₁ ⊓ Subgroup.centralizer (H₁ : Set ↥Max3.M) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer (H₁ : Set ↥Max3.M)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx.2
  have hle' : H₁ ⊓ H₂ ≤ (Subgroup.center H₁).map H₁.subtype := by
    rw [← CFSG.GroupTheory.inf_centralizer_eq_map_center H₁]
    exact hle
  have hcardMap : Nat.card ↥((Subgroup.center H₁).map H₁.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective H₁.subtype_injective, hcard_center]
  haveI : Finite ↥((Subgroup.center H₁).map H₁.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcardMap]; norm_num)
  have hupper : Nat.card ↥(H₁ ⊓ H₂) ≤ 2 := by
    calc Nat.card ↥(H₁ ⊓ H₂) ≤ Nat.card ↥((Subgroup.center H₁).map H₁.subtype) :=
          Subgroup.card_le_of_le hle'
      _ = 2 := hcardMap
  haveI : Finite ↥(H₁ ⊓ H₂) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  have hlower : 2 ≤ Nat.card ↥(H₁ ⊓ H₂) := by
    have h := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr zM_mem_inf)
    rwa [Nat.card_zpowers, orderOf_zM] at h
  exact le_antisymm hupper hlower

private theorem CQt_eq_sup (hisoB₁ : Nonempty (↥B₁ ≃* QuaternionGroup 2))
    (hisoB₂ : Nonempty (↥B₂ ≃* QuaternionGroup 2))
    (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a)
    (hcardInf : Nat.card ↥(H₁ ⊓ H₂) = 2) : CQt = B₁ ⊔ B₂ := by
  haveI : Finite ↥Max3.M :=
    Nat.finite_of_card_ne_zero (by rw [Max3.card_M]; norm_num)
  have hle : B₁ ⊔ B₂ ≤ CQt := sup_le B₁_le_CQt B₂_le_CQt
  have hcardC : Nat.card ↥CQt = 32 := by
    simpa only [CQt] using card_Q_inf_centralizer_t
  have hcardB₁ : Nat.card ↥B₁ = 8 := card_B₁ hisoB₁
  have hcardB₂ : Nat.card ↥B₂ = 8 := card_B₂ hisoB₂
  haveI : Finite ↥(H₁ ⊓ H₂) := Nat.finite_of_card_ne_zero (by rw [hcardInf]; norm_num)
  have hcardSup_ge : 32 ≤ Nat.card ↥(B₁ ⊔ B₂) := by
    have hXY := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₁ B₂
      (fun a ha b hb => hcomm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_left hb))).1
    rw [hcardB₁, hcardB₂] at hXY
    have hinf : Nat.card ↥(B₁ ⊓ B₂) ≤ 2 := by
      have hleInf : B₁ ⊓ B₂ ≤ H₁ ⊓ H₂ :=
        inf_le_inf (show B₁ ≤ H₁ from le_sup_left) (show B₂ ≤ H₂ from le_sup_left)
      calc Nat.card ↥(B₁ ⊓ B₂) ≤ Nat.card ↥(H₁ ⊓ H₂) := Subgroup.card_le_of_le hleInf
        _ = 2 := hcardInf
    have h64 : 64 ≤ Nat.card ↥(B₁ ⊔ B₂) * 2 := by
      calc 64 = Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(B₁ ⊓ B₂) := hXY.symm
        _ ≤ Nat.card ↥(B₁ ⊔ B₂) * 2 := Nat.mul_le_mul_left _ hinf
    have h32 : 32 * 2 ≤ Nat.card ↥(B₁ ⊔ B₂) * 2 := by
      calc 32 * 2 = 64 := by norm_num
        _ ≤ Nat.card ↥(B₁ ⊔ B₂) * 2 := h64
    exact Nat.le_of_mul_le_mul_right h32 (by norm_num)
  have hcardSup_le : Nat.card ↥(B₁ ⊔ B₂) ≤ 32 := by
    haveI : Finite ↥CQt := Nat.finite_of_card_ne_zero (by rw [hcardC]; norm_num)
    calc Nat.card ↥(B₁ ⊔ B₂) ≤ Nat.card ↥CQt := Subgroup.card_le_of_le hle
      _ = 32 := hcardC
  have hcardSup : Nat.card ↥(B₁ ⊔ B₂) = 32 := le_antisymm hcardSup_le hcardSup_ge
  haveI : Finite ↥CQt := Nat.finite_of_card_ne_zero (by rw [hcardC]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardC, hcardSup])).symm

private theorem H₁_sup_H₂_le_D₀ : H₁ ⊔ H₂ ≤ D₀ := by
  have hCQt_le : CQt ≤ D₀ := by
    rw [D₀]
    exact (le_sup_left.trans le_sup_left).trans le_sup_left
  have hZω₁_le : Subgroup.zpowers ω₁ ≤ D₀ := by
    rw [D₀]
    exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hZω₂_le : Subgroup.zpowers ω₂ ≤ D₀ := by
    rw [D₀]
    exact le_sup_right.trans le_sup_left
  rw [H₁, H₂]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact B₁_le_CQt.trans hCQt_le
  · exact hZω₁_le
  · exact B₂_le_CQt.trans hCQt_le
  · exact hZω₂_le

private theorem map_conj_uM_H₁ : H₁.map (MulAut.conj uM) = H₂ := by
  rw [H₁, H₂, B₁, B₂, Subgroup.map_sup]
  have hBmap : (Subgroup.closure {x₁, y₁}).map (MulAut.conj uM) =
      Subgroup.closure {x₂, y₂} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hZmap : (Subgroup.zpowers ω₁).map (MulAut.conj uM) = Subgroup.zpowers ω₂ := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hBmap, hZmap]

private theorem tLetter_mul_uM_inv : tLetter * uM⁻¹ = uM⁻¹ * tLetter⁻¹ := by
  calc tLetter * uM⁻¹ = uM⁻¹ * (uM * tLetter) * uM⁻¹ := by group
    _ = uM⁻¹ * (tLetter⁻¹ * uM) * uM⁻¹ := by rw [uM_mul_tLetter]
    _ = uM⁻¹ * tLetter⁻¹ := by group

private theorem conj_inv_mem_centralizer {g : ↥Max3.M}
    (hg : g ∈ Subgroup.centralizer ({tLetter} : Set ↥Max3.M)) :
    uM⁻¹ * g * uM ∈ Subgroup.centralizer ({tLetter} : Set ↥Max3.M) := by
  have hgt : g * tLetter = tLetter * g := by
    have := (Subgroup.mem_centralizer_iff.mp hg) tLetter (by simp)
    exact this.symm
  have hgti : g * tLetter⁻¹ = tLetter⁻¹ * g := by
    calc g * tLetter⁻¹ = tLetter⁻¹ * (tLetter * g) * tLetter⁻¹ := by group
      _ = tLetter⁻¹ * (g * tLetter) * tLetter⁻¹ := by rw [hgt]
      _ = tLetter⁻¹ * g := by group
  have h2 : (uM⁻¹ * g * uM) * tLetter = tLetter * (uM⁻¹ * g * uM) := by
    calc (uM⁻¹ * g * uM) * tLetter
        = uM⁻¹ * g * (uM * tLetter) := by group
      _ = uM⁻¹ * g * (tLetter⁻¹ * uM) := by rw [uM_mul_tLetter]
      _ = uM⁻¹ * (g * tLetter⁻¹) * uM := by group
      _ = uM⁻¹ * (tLetter⁻¹ * g) * uM := by rw [hgti]
      _ = (tLetter * uM⁻¹) * g * uM := by rw [tLetter_mul_uM_inv]; group
      _ = tLetter * (uM⁻¹ * g * uM) := by group
  exact Subgroup.mem_centralizer_singleton_iff.mpr h2

private theorem centralizer_le_normalizer_H₂ (hCQt : CQt = B₁ ⊔ B₂)
    (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    Subgroup.centralizer ({tLetter} : Set ↥Max3.M) ≤
      Subgroup.normalizer (H₂ : Set ↥Max3.M) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  let g' : ↥Max3.M := uM⁻¹ * g * uM
  have hg' : g' ∈ Subgroup.centralizer ({tLetter} : Set ↥Max3.M) :=
    conj_inv_mem_centralizer hg
  have hmapψ : H₁.map (MulAut.conj g') = H₁ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      (centralizer_le_normalizer_H₁ hCQt hcomm hg')
  let φg : ↥Max3.M →* ↥Max3.M := (MulAut.conj g).toMonoidHom
  let φu : ↥Max3.M →* ↥Max3.M := (MulAut.conj uM).toMonoidHom
  let ψ : ↥Max3.M →* ↥Max3.M := (MulAut.conj g').toMonoidHom
  have hcomp : φg.comp φu = φu.comp ψ := by
    apply MonoidHom.ext
    intro x
    dsimp only [φg, φu, ψ]
    change (MulAut.conj g) ((MulAut.conj uM) x) =
      (MulAut.conj uM) ((MulAut.conj g') x)
    simp only [MulAut.conj_apply, g']
    group
  calc H₂.map (MulAut.conj g)
      = (H₁.map (MulAut.conj uM)).map (MulAut.conj g) := by rw [← map_conj_uM_H₁]
    _ = H₁.map (φg.comp φu) := by
          change (H₁.map φu).map φg = H₁.map (φg.comp φu)
          apply SetLike.coe_injective
          rw [Subgroup.coe_map, Subgroup.coe_map, Subgroup.coe_map, Set.image_image]
          rfl
    _ = H₁.map (φu.comp ψ) := by rw [hcomp]
    _ = (H₁.map ψ).map φu := by
          change H₁.map (φu.comp ψ) = (H₁.map ψ).map φu
          apply SetLike.coe_injective
          rw [Subgroup.coe_map, Subgroup.coe_map, Subgroup.coe_map, Set.image_image]
          rfl
    _ = H₂ := by
          rw [show H₁.map ψ = H₁ from hmapψ]
          exact map_conj_uM_H₁

theorem mg1_of (h₁ : y₁ * x₁ = x₁ ^ 3 * y₁) (h₂ : ω₁ * y₁ = y₁ * x₁ * ω₁)
    (h₃ : x₁ * x₂ = x₂ * x₁) (h₄ : x₁ * ω₂ = ω₂ * x₁) (h₅ : ω₁ * x₂ = x₂ * ω₁)
    (h₆ : ω₁ * ω₂ = ω₂ * ω₁) : MG1 tLetter H₁ H₂ := by
  have hxx₁ : x₁ * x₁ = zM := by simpa only [pow_two] using x₁_pow_two
  have hy₁ : y₁ = ω₁ * x₁ * ω₁⁻¹ := rfl
  obtain ⟨hyy₁, hcomm₁⟩ :=
    q8_square_commutator (x := x₁) (y := y₁) (ω := ω₁) (z := zM)
      hxx₁ zM_mul_self ω₁_pow_three hy₁ h₁ h₂
  have hne₁ : y₁ ≠ x₁ := ne_of_relation (x := x₁) (y := y₁) (z := zM)
    hxx₁ zM_mul_self zM_ne_one h₁
  have hωy₁ : ω₁ * y₁ * ω₁⁻¹ = y₁ * x₁ := by rw [h₂]; group
  have h1₂ : y₂ * x₂ = x₂ ^ 3 * y₂ := y₂_mul_x₂ h₁
  have h2₂ : ω₂ * y₂ = y₂ * x₂ * ω₂ := ω₂_mul_y₂ h₂
  obtain ⟨hyy₂, hcomm₂⟩ :=
    q8_square_commutator (x := x₂) (y := y₂) (ω := ω₂) (z := zM)
      x₂_pow_two zM_mul_self ω₂_pow_three y₂_eq_conj h1₂ h2₂
  have hne₂ : y₂ ≠ x₂ := ne_of_relation (x := x₂) (y := y₂) (z := zM)
    x₂_pow_two zM_mul_self zM_ne_one h1₂
  have hωy₂ : ω₂ * y₂ * ω₂⁻¹ = y₂ * x₂ := by rw [h2₂]; group
  have hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a :=
    commute_H₁_H₂ h₃ h₄ h₅ h₆ y₂_eq_conj
  have hisoB₁ : Nonempty (↥B₁ ≃* QuaternionGroup 2) := iso_B₁ hyy₁ hcomm₁
  have hisoB₂ : Nonempty (↥B₂ ≃* QuaternionGroup 2) := iso_B₂ hyy₂ hcomm₂
  have hiso₁ : Nonempty (↥H₁ ≃* SL(2, ZMod 3)) := iso_H₁ hyy₁ hcomm₁ hne₁ hωy₁
  have hiso₂ : Nonempty (↥H₂ ≃* SL(2, ZMod 3)) := iso_H₂ hyy₂ hcomm₂ hne₂ hωy₂
  have hcardInf : Nat.card ↥(H₁ ⊓ H₂) = 2 := card_inf_H₁_H₂ hiso₁ hcomm
  have hCQt : CQt = B₁ ⊔ B₂ := CQt_eq_sup hisoB₁ hisoB₂ hcomm hcardInf
  refine ⟨H₁_le_centralizer_t, H₂_le_centralizer_t,
    centralizer_le_normalizer_H₁ hCQt hcomm, centralizer_le_normalizer_H₂ hCQt hcomm,
    hiso₁, hiso₂, zM_mem_inf, hcardInf,
    fun h => tLetter_not_mem_D₀ (H₁_sup_H₂_le_D₀ h)⟩

end Basic

end CFSG.Sporadic.Th.Recog.MFactsB
