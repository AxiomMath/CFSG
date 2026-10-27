module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise IsMulCommutative

variable {W : Type} [CommGroup W]

private lemma t8_exists_pow_eq_of_card_four [Finite W] {S : Subgroup W} {c : MulAut W}
    (hc3 : c ^ 3 = 1) (hcS : ∀ s ∈ S, c s ∈ S) (hfix : fixV (Subgroup.zpowers c) ⊓ S = ⊥)
    (hcard : Nat.card S = 4) {t : W} (ht : t ∈ S) (ht1 : t ≠ 1) :
    ∀ w ∈ S, w ≠ 1 → ∃ k : ℕ, w = (c ^ k) t := by
  have hct : c t ∈ S := hcS t ht
  have hc2t : c (c t) ∈ S := hcS (c t) hct
  have hfixed : ∀ {v : W}, v ∈ S → c v = v → v = 1 := by
    intro v hv hcv
    have hcstab : c ∈ MulAction.stabilizer (MulAut W) v := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hcv
    have hvfix : v ∈ fixV (Subgroup.zpowers c) :=
      mem_fixV.mpr fun x hx => by
        have hxstab : x ∈ MulAction.stabilizer (MulAut W) v :=
          (Subgroup.zpowers_le.mpr hcstab) hx
        rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hxstab
    have : v ∈ fixV (Subgroup.zpowers c) ⊓ S := Subgroup.mem_inf.mpr ⟨hvfix, hv⟩
    rw [hfix] at this
    exact Subgroup.mem_bot.mp this
  have hc3t : c (c (c t)) = t := by
    have h := congrArg (fun φ : MulAut W => φ t) hc3
    simp only [MulAut.one_apply] at h
    rw [show c ^ 3 = c * (c * c) from by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, show (2 : ℕ) = 1 + 1 from rfl,
        pow_succ, pow_one, mul_assoc]] at h
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    exact h
  have h1t : (1 : W) ≠ t := fun h => ht1 h.symm
  have h1ct : (1 : W) ≠ c t := fun h => ht1 (by
    have := congrArg (fun v => c⁻¹ v) h
    simpa using this.symm)
  have h1c2t : (1 : W) ≠ c (c t) := fun h => ht1 (by
    have := congrArg (fun v => c⁻¹ (c⁻¹ v)) h
    simpa using this.symm)
  have htct : t ≠ c t := fun h => ht1 (hfixed ht h.symm)
  have ht2 : c t ≠ c (c t) := fun h => htct (by
    have := congrArg (fun v => c⁻¹ v) h
    simpa using this)
  have ht3 : t ≠ c (c t) := fun h => htct (by
    have := congrArg (fun v => c v) h
    rw [hc3t] at this
    exact this.symm)
  let f : Fin 4 → W := ![1, t, c t, c (c t)]
  have hfinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, h1t, h1ct, h1c2t, htct, ht2, ht3, Ne.symm]
  have hrange_card : (Set.range f).ncard = 4 := by
    rw [Set.ncard_range_of_injective hfinj, Nat.card_fin]
  have hsub : Set.range f ⊆ (S : Set W) := by
    rintro v ⟨i, rfl⟩
    fin_cases i <;> simp [f, S.one_mem, ht, hct, hc2t]
  have hS_card : (S : Set W).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  have hEq : Set.range f = (S : Set W) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hrange_card, hS_card]))
  intro w hw hw1
  have hwrange : w ∈ Set.range f := hEq ▸ hw
  obtain ⟨i, hi⟩ := hwrange
  fin_cases i
  · exact absurd (by rw [← hi]; simp [f]) hw1
  · exact ⟨0, by rw [← hi]; simp [f]⟩
  · exact ⟨1, by rw [← hi]; simp [f]⟩
  · exact ⟨2, by rw [← hi]; simp [f, pow_two, MulAut.mul_apply]⟩

private lemma t8_commSub_zpowers_fix_bot [Finite W] (hW : ∀ w : W, w * w = 1)
    {Y : Subgroup W} {c : MulAut W} (hc3 : c ^ 3 = 1) (hcY : ∀ y ∈ Y, c y ∈ Y) :
    fixV (Subgroup.zpowers c) ⊓ commSub Y (Subgroup.zpowers c) = ⊥ := by
  have hc3v : ∀ v : W, c (c (c v)) = v := by
    intro v
    have h := congrArg (fun φ : MulAut W => φ v) hc3
    simp only [MulAut.one_apply] at h
    rw [show c ^ 3 = c * (c * c) from by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, show (2 : ℕ) = 1 + 1 from rfl,
        pow_succ, pow_one, mul_assoc]] at h
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    exact h
  let N : W →* W :=
    { toFun := fun w => w * c w * c (c w)
      map_one' := by simp
      map_mul' := by intro u v; simp only [map_mul]; ac_rfl }
  have hNc : ∀ v : W, c (N v) = N v := by
    intro v
    show c (v * c v * c (c v)) = v * c v * c (c v)
    rw [map_mul, map_mul, hc3v]
    ac_rfl
  have hNx : ∀ x ∈ Subgroup.zpowers c, ∀ v : W, N (x v) = x (N v) := by
    intro x hx v
    have hc_cen : c ∈ Subgroup.centralizer ({c} : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]; intro h hh; rw [Set.mem_singleton_iff.mp hh]
    have hcx : c * x = x * c :=
      (Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hc_cen) hx)) c (by simp)
    have hcxa : ∀ w : W, c (x w) = x (c w) := by
      intro w
      rw [← MulAut.mul_apply, hcx, MulAut.mul_apply]
    show x v * c (x v) * c (c (x v)) = x (v * c v * c (c v))
    rw [hcxa v, hcxa (c v), ← map_mul, ← map_mul]
  have hNker : commSub Y (Subgroup.zpowers c) ≤ N.ker := by
    unfold commSub
    rw [Subgroup.closure_le]
    rintro d ⟨x, hx, y, hy, rfl⟩
    have hxv : x (N y) = N y := by
      have hcy : c (N y) = N y := hNc y
      have hcstab : c ∈ MulAction.stabilizer (MulAut W) (N y) := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hcy
      have hxstab : x ∈ MulAction.stabilizer (MulAut W) (N y) :=
        (Subgroup.zpowers_le.mpr hcstab) hx
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hxstab
    change N (x y * y⁻¹) = 1
    rw [map_mul, map_inv, hNx x hx y, hxv]
    simp
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hwfix, hwS⟩ := hw
  have hNw : N w = 1 := hNker hwS
  have hcw : c w = w := (mem_fixV.mp hwfix) c (Subgroup.mem_zpowers c)
  have hww : w * w * w = w := by rw [hW w, one_mul]
  dsimp [N] at hNw
  rw [hcw, hcw, hww] at hNw
  exact hNw

private lemma t8_commSub_zpowers_le [Finite W] {Y : Subgroup W} {c : MulAut W} {U : Subgroup W}
    (hc3 : c ^ 3 = 1) (hcY : ∀ y ∈ Y, c y ∈ Y) (hcU : ∀ y ∈ Y, c y * y⁻¹ ∈ U) :
    commSub Y (Subgroup.zpowers c) ≤ U := by
  have hc3v : ∀ v : W, c (c (c v)) = v := by
    intro v
    have h := congrArg (fun φ : MulAut W => φ v) hc3
    simp only [MulAut.one_apply] at h
    rw [show c ^ 3 = c * (c * c) from by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, show (2 : ℕ) = 1 + 1 from rfl,
        pow_succ, pow_one, mul_assoc]] at h
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    exact h
  have hVmem : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Y, x y * y⁻¹ ∈ U := by
    let V : Subgroup (MulAut W) :=
      { carrier := {x | x ∈ stabSub Y ∧ ∀ y ∈ Y, x y * y⁻¹ ∈ U}
        one_mem' := by
          refine ⟨(stabSub Y).one_mem, fun y hy => ?_⟩
          simp
        mul_mem' := by
          intro x₁ x₂ hx₁ hx₂
          refine ⟨(stabSub Y).mul_mem hx₁.1 hx₂.1, fun y hy => ?_⟩
          have hx₂y : x₂ y ∈ Y := (mem_stabSub.mp hx₂.1 y).mpr hy
          have h1 : x₁ (x₂ y) * (x₂ y)⁻¹ ∈ U := hx₁.2 (x₂ y) hx₂y
          have h2 : x₂ y * y⁻¹ ∈ U := hx₂.2 y hy
          have hsplit : (x₁ * x₂) y * y⁻¹ = x₁ (x₂ y) * y⁻¹ := rfl
          have hassoc : x₁ (x₂ y) * y⁻¹ = (x₁ (x₂ y) * (x₂ y)⁻¹) * (x₂ y * y⁻¹) := by
            group
          rw [hsplit, hassoc]
          exact U.mul_mem h1 h2
        inv_mem' := by
          intro x hx
          refine ⟨(stabSub Y).inv_mem hx.1, fun y hy => ?_⟩
          have hxinv : x⁻¹ y ∈ Y := by
            have hy' : x (x⁻¹ y) ∈ Y := by simpa using hy
            exact (mem_stabSub.mp hx.1 (x⁻¹ y)).mp hy'
          have h1 : x (x⁻¹ y) * (x⁻¹ y)⁻¹ ∈ U := hx.2 (x⁻¹ y) hxinv
          have h1' : y * (x⁻¹ y)⁻¹ ∈ U := by
            rwa [show x (x⁻¹ y) = y from by simp] at h1
          have := U.inv_mem h1'
          rwa [show (y * (x⁻¹ y)⁻¹)⁻¹ = x⁻¹ y * y⁻¹ from by group] at this }
    have hcV : c ∈ V := by
      refine ⟨?_, hcU⟩
      refine mem_stabSub.mpr (fun y => ⟨fun h => ?_, fun h => hcY y h⟩)
      rw [← hc3v y]
      exact hcY (c (c y)) (hcY (c y) h)
    intro x hx y hy
    exact ((Subgroup.zpowers_le.mpr hcV) hx).2 y hy
  unfold commSub
  rw [Subgroup.closure_le]
  rintro d ⟨x, hx, y, hy, rfl⟩
  exact hVmem x hx y hy

private lemma t8_commSub_zpowers_map {Y : Subgroup W} {c τ : MulAut W}
    (hcτ : τ * c * τ⁻¹ = c⁻¹) (hτY : ∀ y ∈ Y, τ y ∈ Y) :
    ∀ s ∈ commSub Y (Subgroup.zpowers c), τ s ∈ commSub Y (Subgroup.zpowers c) := by
  have hτx : ∀ x ∈ Subgroup.zpowers c, τ * x * τ⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h := map_zpow (MulAut.conj τ) c k
    rw [MulAut.conj_apply, MulAut.conj_apply, hcτ] at h
    rw [h, inv_zpow]
  have hτx' : ∀ x ∈ Subgroup.zpowers c, τ * x = x⁻¹ * τ := by
    intro x hx
    have h := hτx x hx
    calc τ * x = τ * x * τ⁻¹ * τ := by group
      _ = x⁻¹ * τ := by rw [h]
  intro s hs
  refine Subgroup.closure_induction (p := fun s _ => τ s ∈ commSub Y (Subgroup.zpowers c))
    ?_ ?_ ?_ ?_ hs
  · rintro d ⟨x, hx, y, hy, rfl⟩
    have hxy : τ (x y) = x⁻¹ (τ y) := by
      rw [← MulAut.mul_apply, hτx' x hx, MulAut.mul_apply]
    rw [map_mul, map_inv, hxy]
    exact Subgroup.subset_closure ⟨x⁻¹, Subgroup.inv_mem _ hx, τ y, hτY y hy, rfl⟩
  · simp
  · intro u v _ _ hu hv
    rw [map_mul]
    exact (commSub Y (Subgroup.zpowers c)).mul_mem hu hv
  · intro u _ hu
    rw [map_inv]
    exact (commSub Y (Subgroup.zpowers c)).inv_mem hu

private lemma t8_conj_mem_sup_map {Y : Subgroup W} {b τ c : MulAut W} (hτ2 : τ * τ = 1)
    (hc : c = b * τ * b⁻¹ * τ⁻¹) (hbY : ∀ y ∈ Y, b y ∈ Y) (hbYinv : ∀ y ∈ Y, b⁻¹ y ∈ Y)
    (hτY : ∀ y ∈ Y, τ y ∈ Y) :
    ∀ y ∈ Y, c y * y⁻¹ ∈ commSub Y (Subgroup.zpowers τ) ⊔
      (commSub Y (Subgroup.zpowers τ)).map b.toMonoidHom := by
  have hτinv : τ⁻¹ = τ := by rw [inv_eq_iff_mul_eq_one]; exact hτ2
  intro y hy
  have hcy : c y = (b * τ * b⁻¹) (τ y) := by
    rw [hc, hτinv, MulAut.mul_apply]
  have hzY : τ y ∈ Y := hτY y hy
  have hb1 : (b * τ * b⁻¹) (τ y) * (τ y)⁻¹ ∈
      (commSub Y (Subgroup.zpowers τ)).map b.toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨τ (b⁻¹ (τ y)) * (b⁻¹ (τ y))⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, b⁻¹ (τ y),
        hbYinv (τ y) hzY, rfl⟩
    · show b (τ (b⁻¹ (τ y)) * (b⁻¹ (τ y))⁻¹) = (b * τ * b⁻¹) (τ y) * (τ y)⁻¹
      rw [map_mul, map_inv, MulAut.apply_inv_self, MulAut.mul_apply, MulAut.mul_apply]
  have hsplit : c y * y⁻¹ = ((b * τ * b⁻¹) (τ y) * (τ y)⁻¹) * (τ y * y⁻¹) := by
    rw [hcy]; group
  rw [hsplit]
  refine (commSub Y (Subgroup.zpowers τ) ⊔ (commSub Y (Subgroup.zpowers τ)).map
    b.toMonoidHom).mul_mem (Subgroup.mem_sup_right hb1) (Subgroup.mem_sup_left ?_)
  exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, y, hy, rfl⟩

private lemma t8_commSub_zpowers_map_of_conj {Y : Subgroup W} {c τ : MulAut W}
    (hτc : τ * c * τ⁻¹ = c) (hτY : ∀ y ∈ Y, τ y ∈ Y) :
    ∀ s ∈ commSub Y (Subgroup.zpowers c), τ s ∈ commSub Y (Subgroup.zpowers c) := by
  have hcx : ∀ x ∈ Subgroup.zpowers c, τ * x * τ⁻¹ = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h := map_zpow (MulAut.conj τ) c k
    rw [MulAut.conj_apply, MulAut.conj_apply] at h
    rw [hτc] at h
    exact h
  have hcx' : ∀ x ∈ Subgroup.zpowers c, τ * x = x * τ := by
    intro x hx
    calc τ * x = τ * x * τ⁻¹ * τ := by group
      _ = x * τ := by rw [hcx x hx]
  intro s hs
  refine Subgroup.closure_induction (p := fun s _ => τ s ∈ commSub Y (Subgroup.zpowers c))
    ?_ ?_ ?_ ?_ hs
  · rintro d ⟨x, hx, y, hy, rfl⟩
    have hxy : τ (x y) = x (τ y) := by
      rw [← MulAut.mul_apply, hcx' x hx, MulAut.mul_apply]
    rw [map_mul, map_inv, hxy]
    exact Subgroup.subset_closure ⟨x, hx, τ y, hτY y hy, rfl⟩
  · simp
  · intro u v _ _ hu hv
    rw [map_mul]
    exact (commSub Y (Subgroup.zpowers c)).mul_mem hu hv
  · intro u _ hu
    rw [map_inv]
    exact (commSub Y (Subgroup.zpowers c)).inv_mem hu

structure T8Blocks [Finite W] (Mb : Subgroup (MulAut W)) (B : Fin 4 → Subgroup (MulAut W))
    (Y : Fin 4 → Subgroup W) (r : ℕ) : Prop where
  sq : ∀ w : W, w * w = 1
  two_le : 2 ≤ r
  le : ∀ j, B j ≤ Mb
  comm : ∀ j, IsMulCommutative (B j)
  cube : ∀ j, ∀ c ∈ B j, c ^ 3 = 1
  card : ∀ j, Nat.card (B j) = 3 ^ r
  commute : ∀ i j, i ≠ j → ∀ c ∈ B i, ∀ c' ∈ B j, c * c' = c' * c
  indep : ∀ j, B j ⊓ (⨆ i ∈ {i | i ≠ j}, B i) = ⊥
  trans : ∀ j, ∃ q ∈ Mb, B j = (B 0).map (MulAut.conj q).toMonoidHom
  normal : ∀ q ∈ Mb, ∀ x ∈ ⨆ j, B j, q * x * q⁻¹ ∈ ⨆ j, B j
  triv : ∀ i j, i ≠ j → ∀ c ∈ B i, ∀ y ∈ Y j, c y = y
  stab : ∀ j, ∀ c ∈ B j, ∀ y ∈ Y j, c y ∈ Y j
  faith : ∀ j, ∀ c ∈ B j, (∀ y ∈ Y j, c y = y) → c = 1

structure T8Action [Finite W] (B : Fin 4 → Subgroup (MulAut W)) (Y : Fin 4 → Subgroup W)
    (u : MulAut W) (z : W) (J : Finset (Fin 4)) : Prop where
  sq : u * u = 1
  card_le : J.card ≤ 3
  norm : ∀ j, ∀ c ∈ B j, u * c * u⁻¹ ∈ B j
  stab : ∀ j, ∀ y ∈ Y j, u y ∈ Y j
  triv : ∀ j, j ∉ J → ∀ y ∈ Y j, u y = y
  transv : ∀ j ∈ J, rk ↥(commSub (Y j) (Subgroup.zpowers u)) ≤ 1
  z_mem : z ∈ ⨆ j ∈ J, commSub (Y j) (Subgroup.zpowers u)

theorem s15_T8_comm_card [Finite W] (hW : ∀ w : W, w * w = 1) {Y : Subgroup W}
    {B : Subgroup (MulAut W)} (hBc : IsMulCommutative B) (hB3 : ∀ c ∈ B, c ^ 3 = 1)
    (hBY : ∀ c ∈ B, ∀ y ∈ Y, c y ∈ Y) (hfaith : ∀ c ∈ B, (∀ y ∈ Y, c y = y) → c = 1)
    {τ : MulAut W} (hτ2 : τ * τ = 1) (hτY : ∀ y ∈ Y, τ y ∈ Y)
    (hτB : ∀ c ∈ B, τ * c * τ⁻¹ ∈ B) (hrk : rk ↥(commSub Y (Subgroup.zpowers τ)) ≤ 1) :
    Nat.card B ≤ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer ({τ} : Set (MulAut W))) := by
  classical
  haveI : IsMulCommutative B := hBc
  have hττ : ∀ y : W, τ (τ y) = y := by
    intro y
    have := congrArg (fun φ : MulAut W => φ y) hτ2
    simpa [MulAut.mul_apply] using this
  set T : Subgroup W := commSub Y (Subgroup.zpowers τ) with hTdef
  have hτ_stab : τ ∈ stabSub Y :=
    mem_stabSub.mpr (fun y => ⟨fun hy => by
      have := hτY (τ y) hy
      rwa [hττ y] at this, fun hy => hτY y hy⟩)
  have hT_le_Y : T ≤ Y := by
    refine commSub_le_of_invariant (X := Subgroup.zpowers τ) (W := Y) (fun x hx y hy => ?_)
    exact (mem_stabSub.mp ((Subgroup.zpowers_le.mpr hτ_stab) hx) y).mpr hy
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hT_card : Nat.card T ≤ 2 := by
    calc Nat.card T = 2 ^ rk T := card_eq_two_pow hW2 T
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 2 := by norm_num
  let φ : B →* B :=
    { toFun := fun b => ⟨τ * (b : MulAut W) * τ⁻¹, hτB b b.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext x
        simp only [Subgroup.coe_mul, MulAut.mul_apply, MulAut.inv_apply_self] }
  let f : B →* B :=
    { toFun := fun b => b * (φ b)⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        show a * b * (φ (a * b))⁻¹ = a * (φ a)⁻¹ * (b * (φ b)⁻¹)
        rw [map_mul, mul_inv_rev]
        rw [mul_assoc]
        rw [← mul_assoc b]
        rw [mul_comm (b * (φ b)⁻¹)]
        rw [← mul_assoc] }
  have hker : f.ker = (B ⊓ Subgroup.centralizer ({τ} : Set (MulAut W))).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    have h1 : f b = 1 ↔ b = φ b := by
      constructor
      · intro h
        have := congrArg (fun x : B => x * φ b) h
        simpa [f, mul_assoc] using this
      · intro h
        show b * (φ b)⁻¹ = 1
        rw [← h]
        simp
    have h2 : b = φ b ↔ τ * (b : MulAut W) = (b : MulAut W) * τ := by
      constructor
      · intro h
        have hb : (b : MulAut W) = τ * (b : MulAut W) * τ⁻¹ := by
          have := congrArg (fun x : B => (x : MulAut W)) h
          simpa [φ] using this
        have := congrArg (fun x : MulAut W => x * τ) hb
        simpa [mul_assoc] using this.symm
      · intro h
        apply Subtype.ext
        show (b : MulAut W) = τ * (b : MulAut W) * τ⁻¹
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
    constructor
    · intro h
      refine ⟨b.2, fun hh hhh => ?_⟩
      rw [Set.mem_singleton_iff.mp hhh]
      exact h2.mp (h1.mp h)
    · rintro ⟨-, hcomm⟩
      exact h1.mpr (h2.mpr (hcomm τ (by simp)))
  have hcardB : Nat.card B =
      Nat.card f.range * Nat.card ↥(B ⊓ Subgroup.centralizer ({τ} : Set (MulAut W))) := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    rw [mul_comm] at h
    exact h.symm
  have hR_le : Nat.card f.range ≤ 3 := by
    by_contra hle
    push Not at hle
    have hRne : f.range ≠ ⊥ := by
      intro hbot
      have : Nat.card f.range = 1 := by rw [hbot]; exact Subgroup.card_bot
      omega
    obtain ⟨c₁, hc₁ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
    have hc₁ne' : (c₁ : B) ≠ 1 := fun h => hc₁ne (Subtype.ext h)
    have hex : ∃ c₂ : ↥f.range, c₂ ∉ Subgroup.zpowers c₁ := by
      by_contra h
      push Not at h
      have htop : (⊤ : Subgroup ↥f.range) ≤ Subgroup.zpowers c₁ := fun x _ => h x
      have hEq : Subgroup.zpowers c₁ = ⊤ := le_antisymm le_top htop
      have hcard1 : Nat.card ↥(Subgroup.zpowers c₁) = Nat.card ↥f.range := by
        rw [hEq, Subgroup.card_top]
      have hc1cube : c₁ ^ 3 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hB3 (c₁ : B) (c₁ : B).2
      have hdvd : orderOf c₁ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hc1cube
      have hle3 : orderOf c₁ ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
      have : Nat.card ↥f.range ≤ 3 := by
        rw [← hcard1, Nat.card_zpowers]
        exact hle3
      omega
    obtain ⟨c₂, hc₂⟩ := hex
    have hτinv : ∀ c : B, c ∈ f.range → τ * (c : MulAut W) * τ⁻¹ = (c : MulAut W)⁻¹ := by
      intro c hc
      obtain ⟨b, rfl⟩ := hc
      have hτinv' : τ⁻¹ = τ := by rw [inv_eq_iff_mul_eq_one]; exact hτ2
      have hcf_eq : ((f b : B) : MulAut W) = (b : MulAut W) * τ * (b : MulAut W)⁻¹ * τ⁻¹ := by
        show (b : MulAut W) * ((φ b : B) : MulAut W)⁻¹ = _
        rw [show ((φ b : B) : MulAut W) = τ * (b : MulAut W) * τ⁻¹ from rfl]
        group
      rw [hcf_eq, hτinv']
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hτinv']
      calc τ * ((b : MulAut W) * τ * (b : MulAut W)⁻¹ * τ) * τ
          = (τ * (b : MulAut W) * τ * (b : MulAut W)⁻¹) * (τ * τ) := by group
        _ = τ * (b : MulAut W) * τ * (b : MulAut W)⁻¹ := by rw [hτ2]; group
    have hprod : ∀ c : B, c ∈ f.range → c ≠ 1 →
        Nat.card ↥(commSub Y (Subgroup.zpowers (c : MulAut W))) = 4 ∧
        fixV (Subgroup.zpowers (c : MulAut W)) ⊓ commSub Y (Subgroup.zpowers (c : MulAut W)) = ⊥ ∧
        ∃ t ∈ T, t ≠ 1 ∧ t ∈ commSub Y (Subgroup.zpowers (c : MulAut W)) := by
      intro c hc hcne
      obtain ⟨b, rfl⟩ := hc
      have hf_cube : ((f b : B) : MulAut W) ^ 3 = 1 := by
        simpa using hB3 (f b) (f b).2
      have hfY : ∀ y ∈ Y, ((f b : B) : MulAut W) y ∈ Y := hBY (f b) (f b).2
      have hfτ : τ * ((f b : B) : MulAut W) * τ⁻¹ = ((f b : B) : MulAut W)⁻¹ :=
        hτinv (f b) ⟨b, rfl⟩
      have hSfix := t8_commSub_zpowers_fix_bot hW hf_cube hfY
      have hcSstab : ∀ s ∈ commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)),
          ((f b : B) : MulAut W) s ∈ commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) :=
        t8_commSub_zpowers_map_of_conj (c := ((f b : B) : MulAut W))
          (τ := ((f b : B) : MulAut W)) (by group) hfY
      have hbY : ∀ y ∈ Y, (b : MulAut W) y ∈ Y := hBY b b.2
      have hbYinv : ∀ y ∈ Y, (b : MulAut W)⁻¹ y ∈ Y := hBY b⁻¹ (B.inv_mem b.2)
      have hcf_eq : ((f b : B) : MulAut W) = (b : MulAut W) * τ * (b : MulAut W)⁻¹ * τ⁻¹ := by
        show (b : MulAut W) * ((φ b : B) : MulAut W)⁻¹ = _
        rw [show ((φ b : B) : MulAut W) = τ * (b : MulAut W) * τ⁻¹ from rfl]
        group
      have hcU : ∀ y ∈ Y, ((f b : B) : MulAut W) y * y⁻¹ ∈
          T ⊔ T.map (b : MulAut W).toMonoidHom := by
        rw [hcf_eq]
        exact t8_conj_mem_sup_map hτ2 rfl hbY hbYinv hτY
      have hSle : commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) ≤
          T ⊔ T.map (b : MulAut W).toMonoidHom :=
        t8_commSub_zpowers_le hf_cube hfY hcU
      have hmap_card : Nat.card (T.map (b : MulAut W).toMonoidHom) = Nat.card T :=
        Subgroup.card_map_of_injective (b : MulAut W).injective
      have hU_card : Nat.card ↥(T ⊔ T.map (b : MulAut W).toMonoidHom) ≤ 4 := by
        have hprod' := card_sup_mul_card_inf T (T.map (b : MulAut W).toMonoidHom)
        calc Nat.card ↥(T ⊔ T.map (b : MulAut W).toMonoidHom)
            ≤ Nat.card ↥(T ⊔ T.map (b : MulAut W).toMonoidHom) *
              Nat.card ↥(T ⊓ T.map (b : MulAut W).toMonoidHom) :=
              Nat.le_mul_of_pos_right _ Nat.card_pos
          _ = Nat.card T * Nat.card ↥(T.map (b : MulAut W).toMonoidHom) := hprod'
          _ = Nat.card T * Nat.card T := by rw [hmap_card]
          _ ≤ 2 * 2 := Nat.mul_le_mul hT_card hT_card
          _ = 4 := by norm_num
      have hS_le4 : Nat.card ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) ≤ 4 :=
        le_trans (Subgroup.card_le_of_le hSle) hU_card
      have hy : ∃ y ∈ Y, ((f b : B) : MulAut W) y ≠ y := by
        by_contra h
        push Not at h
        exact hcne (Subtype.ext (hfaith (f b) (f b).2 h))
      obtain ⟨y, hy, hyc⟩ := hy
      have hgS : ((f b : B) : MulAut W) y * y⁻¹ ∈
          commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) :=
        Subgroup.subset_closure ⟨(f b : B), Subgroup.mem_zpowers ((f b : B) : MulAut W), y, hy, rfl⟩
      have hg1 : ((f b : B) : MulAut W) y * y⁻¹ ≠ 1 := by
        intro h
        exact hyc (mul_inv_eq_one.mp h)
      have hcgS : ((f b : B) : MulAut W) (((f b : B) : MulAut W) y * y⁻¹) ∈
          commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) := hcSstab _ hgS
      have hcg_ne : ((f b : B) : MulAut W) (((f b : B) : MulAut W) y * y⁻¹) ≠
          ((f b : B) : MulAut W) y * y⁻¹ := by
        intro h
        have hmem : ((f b : B) : MulAut W) y * y⁻¹ ∈
            fixV (Subgroup.zpowers ((f b : B) : MulAut W)) := by
          rw [mem_fixV]
          intro x hx
          have hcstab : ((f b : B) : MulAut W) ∈
              MulAction.stabilizer (MulAut W) (((f b : B) : MulAut W) y * y⁻¹) := by
            rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact h
          have hxstab := (Subgroup.zpowers_le.mpr hcstab) hx
          rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hxstab
        have : ((f b : B) : MulAut W) y * y⁻¹ ∈
            fixV (Subgroup.zpowers ((f b : B) : MulAut W)) ⊓
              commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) :=
          Subgroup.mem_inf.mpr ⟨hmem, hgS⟩
        rw [hSfix] at this
        exact hg1 (Subgroup.mem_bot.mp this)
      have hcg1 : ((f b : B) : MulAut W) (((f b : B) : MulAut W) y * y⁻¹) ≠ 1 := by
        intro h
        have h2 := congrArg (fun v => ((f b : B) : MulAut W)⁻¹ v) h
        simp only [map_one] at h2
        exact hg1 (by rw [← h2]; simp)
      have hge3 : 3 ≤ Nat.card ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) := by
        have hdist : ({1, ((f b : B) : MulAut W) y * y⁻¹,
            ((f b : B) : MulAut W) (((f b : B) : MulAut W) y * y⁻¹)} : Set W).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                exact ⟨hg1.symm, hcg1.symm⟩),
              Set.ncard_insert_of_notMem (by
                simp only [Set.mem_singleton_iff]
                exact hcg_ne.symm),
              Set.ncard_singleton]
        have hsub : ({1, ((f b : B) : MulAut W) y * y⁻¹,
            ((f b : B) : MulAut W) (((f b : B) : MulAut W) y * y⁻¹)} : Set W) ⊆
            (commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) : Set W) := by
          intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl | rfl
          · exact (commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))).one_mem
          · exact hgS
          · exact hcgS
        have hle3' := Set.ncard_le_ncard hsub
        rw [hdist] at hle3'
        have hcard_eq : Nat.card ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) =
            (commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) : Set W).ncard := by
          rw [← _root_.Nat.card_coe_set_eq, SetLike.coe_sort_coe]
        rw [hcard_eq]
        exact hle3'
      have hpow : Nat.card ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) =
          2 ^ rk ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) :=
        card_eq_two_pow hW2 _
      have hge4 : 4 ≤ Nat.card ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) := by
        by_contra h
        push Not at h
        rw [hpow] at h hge3
        have hrk : rk ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) ≤ 1 := by
          by_contra hr
          push Not at hr
          have : 4 ≤ 2 ^ rk ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ rk _ := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have h2 : 2 ^ rk ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) ≤ 2 := by
          calc 2 ^ rk ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)))
              ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrk
            _ = 2 := by norm_num
        omega
      have hScard : Nat.card ↥(commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))) = 4 :=
        le_antisymm hS_le4 hge4
      have hSne : commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) ≠ ⊥ := by
        intro hbot
        rw [commSub_eq_bot_iff] at hbot
        have hfixY : ∀ y ∈ Y, ((f b : B) : MulAut W) y = y := fun y hy =>
          (mem_fixV.mp (hbot hy)) (f b) (Subgroup.mem_zpowers ((f b : B) : MulAut W))
        exact hcne (Subtype.ext (hfaith (f b) (f b).2 hfixY))
      have hc3v : ∀ v : W, ((f b : B) : MulAut W) (((f b : B) : MulAut W)
          (((f b : B) : MulAut W) v)) = v := by
        intro v
        have h := congrArg (fun ψ : MulAut W => ψ v) hf_cube
        simp only [MulAut.one_apply] at h
        rw [show ((f b : B) : MulAut W) ^ 3 =
            ((f b : B) : MulAut W) * (((f b : B) : MulAut W) * ((f b : B) : MulAut W)) from by
            rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, show (2 : ℕ) = 1 + 1 from rfl,
              pow_succ, pow_one, mul_assoc]] at h
        rw [MulAut.mul_apply, MulAut.mul_apply] at h
        exact h
      have hτnotfix : ¬ ∀ s ∈ commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)),
          τ s = s := by
        intro hall
        have hcS2 : ∀ s ∈ commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)),
            ((f b : B) : MulAut W) (((f b : B) : MulAut W) s) = s := by
          intro s hs
          have hcs : ((f b : B) : MulAut W) s ∈
              commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) := hcSstab s hs
          have h1 : τ (((f b : B) : MulAut W) s) = ((f b : B) : MulAut W)⁻¹ s := by
            have hτc : τ * ((f b : B) : MulAut W) =
                ((f b : B) : MulAut W)⁻¹ * τ := by
              calc τ * ((f b : B) : MulAut W) =
                  τ * ((f b : B) : MulAut W) * τ⁻¹ * τ := by group
                _ = ((f b : B) : MulAut W)⁻¹ * τ := by rw [hfτ]
            rw [← MulAut.mul_apply, hτc, MulAut.mul_apply, hall s hs]
          rw [hall _ hcs] at h1
          have h3 := congrArg (fun v => ((f b : B) : MulAut W) v) h1
          rwa [MulAut.apply_inv_self] at h3
        have hc_fix : ∀ s ∈ commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)),
            ((f b : B) : MulAut W) s = s := by
          intro s hs
          have h2 := hcS2 s hs
          have h3 := congrArg (fun v => ((f b : B) : MulAut W) v) h2
          rw [hc3v s] at h3
          exact h3.symm
        have hSle' : commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) ≤
            fixV (Subgroup.zpowers ((f b : B) : MulAut W)) := by
          intro w hw
          rw [mem_fixV]
          intro x hx
          have hcstab : ((f b : B) : MulAut W) ∈
              MulAction.stabilizer (MulAut W) w := by
            rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
            exact hc_fix w hw
          have hxstab := (Subgroup.zpowers_le.mpr hcstab) hx
          rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hxstab
        have : commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) ≤ ⊥ := by
          rw [← hSfix]
          exact le_inf hSle' le_rfl
        exact hSne (le_bot_iff.mp this)
      have hSτ := t8_commSub_zpowers_map hfτ hτY
      have hS_le_Y : commSub Y (Subgroup.zpowers ((f b : B) : MulAut W)) ≤ Y :=
        t8_commSub_zpowers_le hf_cube hfY (fun y hy => Y.mul_mem (hfY y hy) (Y.inv_mem hy))
      push Not at hτnotfix
      obtain ⟨s, hsS, hs_ne⟩ := hτnotfix
      exact ⟨hScard, hSfix, τ s * s⁻¹,
        Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, s, hS_le_Y hsS, rfl⟩,
        fun h => hs_ne (mul_inv_eq_one.mp h),
        (commSub Y (Subgroup.zpowers ((f b : B) : MulAut W))).mul_mem
          (hSτ s hsS) ((commSub _ _).inv_mem hsS)⟩
    obtain ⟨hS₁card, hS₁fix, t, htT, ht1, htS₁⟩ := hprod (c₁ : B) c₁.2 hc₁ne'
    have ht_uniq : ∀ u ∈ T, u ≠ 1 → u = t := by
      intro u hu hu1
      by_contra huv
      have hdist : ({1, t, u} : Set W).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨ht1.symm, hu1.symm⟩),
            Set.ncard_insert_of_notMem (by
              simp only [Set.mem_singleton_iff]
              exact fun h => huv h.symm),
            Set.ncard_singleton]
      have hsub : ({1, t, u} : Set W) ⊆ (T : Set W) := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · exact T.one_mem
        · exact htT
        · exact hu
      have hle3' := Set.ncard_le_ncard hsub
      rw [hdist] at hle3'
      have hcardT : Nat.card ↥T = (T : Set W).ncard := by
        rw [← _root_.Nat.card_coe_set_eq, SetLike.coe_sort_coe]
      have : 3 ≤ Nat.card T := by rw [hcardT]; exact hle3'
      omega
    have htS : ∀ c : B, c ∈ f.range → c ≠ 1 → t ∈ commSub Y (Subgroup.zpowers (c : MulAut W)) := by
      intro c hc hcne
      obtain ⟨-, -, t', ht'T, ht'1, ht'S⟩ := hprod c hc hcne
      rwa [ht_uniq t' ht'T ht'1] at ht'S
    have hc₂ne : (c₂ : B) ≠ 1 := by
      intro h
      apply hc₂
      have : c₂ = 1 := Subtype.ext h
      rw [this]
      exact Subgroup.one_mem _
    have hc₂Y : ∀ y ∈ Y, (c₂ : MulAut W) y ∈ Y := hBY (c₂ : B) (c₂ : B).2
    have hc₂c₁ : (c₂ : MulAut W) * (c₁ : MulAut W) = (c₁ : MulAut W) * (c₂ : MulAut W) :=
      congrArg (fun x : B => (x : MulAut W)) (hBc.is_comm.comm (c₂ : B) (c₁ : B))
    have hc₂c₁' : (c₂ : MulAut W) * (c₁ : MulAut W) * (c₂ : MulAut W)⁻¹ = (c₁ : MulAut W) := by
      rw [hc₂c₁]; group
    have hc₂S₁ : ∀ s ∈ commSub Y (Subgroup.zpowers (c₁ : MulAut W)),
        (c₂ : MulAut W) s ∈ commSub Y (Subgroup.zpowers (c₁ : MulAut W)) :=
      t8_commSub_zpowers_map_of_conj hc₂c₁' hc₂Y
    have hc₂tS : (c₂ : MulAut W) t ∈ commSub Y (Subgroup.zpowers (c₁ : MulAut W)) :=
      hc₂S₁ t (htS (c₁ : B) c₁.2 hc₁ne')
    have hc₂t_ne : (c₂ : MulAut W) t ≠ 1 := by
      intro h
      have := congrArg (fun v => (c₂ : MulAut W)⁻¹ v) h
      simp only [map_one] at this
      exact ht1 (by rwa [MulAut.inv_apply_self] at this)
    have hc₁cube' : (c₁ : MulAut W) ^ 3 = 1 := by
      simpa using hB3 (c₁ : B) (c₁ : B).2
    have hc₁stab : ∀ s ∈ commSub Y (Subgroup.zpowers (c₁ : MulAut W)),
        (c₁ : MulAut W) s ∈ commSub Y (Subgroup.zpowers (c₁ : MulAut W)) :=
      t8_commSub_zpowers_map_of_conj (c := (c₁ : MulAut W)) (τ := (c₁ : MulAut W))
        (by group) (hBY (c₁ : B) (c₁ : B).2)
    obtain ⟨k, hk⟩ := t8_exists_pow_eq_of_card_four
      (S := commSub Y (Subgroup.zpowers (c₁ : MulAut W)))
      hc₁cube' hc₁stab hS₁fix hS₁card (htS (c₁ : B) c₁.2 hc₁ne') ht1
      ((c₂ : MulAut W) t) hc₂tS hc₂t_ne
    let c' : ↥f.range := (c₁ ^ k)⁻¹ * c₂
    have hc'ne : c' ≠ 1 := by
      intro h
      apply hc₂
      have hc₂eq : c₂ = c₁ ^ k := by
        have := congrArg (fun x : ↥f.range => (c₁ ^ k) * x) h
        simpa [c', mul_assoc] using this
      rw [hc₂eq]
      exact Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by rw [zpow_natCast]⟩
    have hc'ne' : (c' : B) ≠ 1 := fun h => hc'ne (Subtype.ext h)
    have hc'_t : (c' : MulAut W) t = t := by
      have hco : (c' : MulAut W) = ((c₁ : MulAut W) ^ k)⁻¹ * (c₂ : MulAut W) := by
        simp only [c', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hco, MulAut.mul_apply, hk, MulAut.inv_apply_self]
    obtain ⟨-, hS'fix, -⟩ := hprod (c' : B) c'.2 hc'ne'
    have htS' : t ∈ commSub Y (Subgroup.zpowers (c' : MulAut W)) :=
      htS (c' : B) c'.2 hc'ne'
    have htfixed : t ∈ fixV (Subgroup.zpowers (c' : MulAut W)) := by
      rw [mem_fixV]
      intro x hx
      have hc'stab : (c' : MulAut W) ∈ MulAction.stabilizer (MulAut W) t := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hc'_t
      have hxstab := (Subgroup.zpowers_le.mpr hc'stab) hx
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hxstab
    have : t ∈ fixV (Subgroup.zpowers (c' : MulAut W)) ⊓
        commSub Y (Subgroup.zpowers (c' : MulAut W)) :=
      Subgroup.mem_inf.mpr ⟨htfixed, htS'⟩
    rw [hS'fix] at this
    exact ht1 (Subgroup.mem_bot.mp this)
  rw [hcardB]
  exact Nat.mul_le_mul_right _ hR_le

private lemma t8_fix_of_card_le_two [Finite W] (hW : ∀ w : W, w * w = 1) {S : Subgroup W}
    {c : MulAut W} (hcS : ∀ s ∈ S, c s ∈ S) (hcard : Nat.card S ≤ 2) :
    S ≤ fixV (Subgroup.zpowers c) := by
  intro w hw
  rw [mem_fixV]
  intro a ha
  rcases Subgroup.bot_or_exists_ne_one S with hbot | ⟨s, hsS, hs1⟩
  · rw [hbot] at hw
    rw [Subgroup.mem_bot.mp hw]
    simp
  · have hcs : c s = s := by
      by_contra hne
      have hne1 : c s ≠ 1 := by
        intro h
        apply hs1
        have h2 := congrArg (fun v => c⁻¹ v) h
        simpa using h2
      have hdist : ({1, s, c s} : Set W).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨hs1.symm, hne1.symm⟩),
            Set.ncard_insert_of_notMem (by
              simp only [Set.mem_singleton_iff]
              exact fun h => hne h.symm),
            Set.ncard_singleton]
      have hsub : ({1, s, c s} : Set W) ⊆ (S : Set W) := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · exact S.one_mem
        · exact hsS
        · exact hcS s hsS
      have hle3 := Set.ncard_le_ncard hsub
      rw [hdist] at hle3
      have hcardS : Nat.card ↥S = (S : Set W).ncard := by
        rw [← _root_.Nat.card_coe_set_eq, SetLike.coe_sort_coe]
      rw [hcardS] at hcard
      omega
    have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact hW s
    have horder : orderOf s = 2 := by
      have hdvd : orderOf s ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hs2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h (orderOf_eq_one_iff.not.mpr hs1)
      · exact h
    have h2 : 2 ≤ Nat.card S := by
      have hzp_le : Subgroup.zpowers s ≤ S := Subgroup.zpowers_le.mpr hsS
      have hle : Nat.card ↥(Subgroup.zpowers s) ≤ Nat.card ↥S := Subgroup.card_le_of_le hzp_le
      simpa [Nat.card_zpowers, horder] using hle
    have hcard2 : Nat.card S = 2 := le_antisymm hcard h2
    have hzp : Subgroup.zpowers s = S := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsS) ?_
      rw [Nat.card_zpowers, horder, hcard2]
    have hw' : w ∈ Subgroup.zpowers s := by rwa [hzp]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    have hcstab : c ∈ MulAction.stabilizer (MulAut W) (s ^ k) := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, map_zpow, hcs]
    have hastab := (Subgroup.zpowers_le.mpr hcstab) ha
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hastab

private lemma t8_card_iSup_prod [Finite W] {ι : Type*} [Fintype ι]
    (A : ι → Subgroup (MulAut W))
    (hcomm : Pairwise fun i j => ∀ x y : MulAut W, x ∈ A i → y ∈ A j → Commute x y)
    (hind : iSupIndep A) :
    Nat.card ↥(⨆ i, A i) = ∏ i, Nat.card (A i) := by
  let f := Subgroup.noncommPiCoprod hcomm
  have hf : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : f.range = ⨆ i, A i := Subgroup.noncommPiCoprod_range
  calc Nat.card ↥(⨆ i, A i) = Nat.card ↥f.range := by rw [hrange]
    _ = Nat.card (∀ i, A i) := (Nat.card_congr (Equiv.ofInjective f hf)).symm
    _ = ∏ i, Nat.card (A i) := Nat.card_pi

theorem s15_T8_fix_count [Finite W] {Mb : Subgroup (MulAut W)} {B : Fin 4 → Subgroup (MulAut W)}
    {Y : Fin 4 → Subgroup W} {r : ℕ} (hB : T8Blocks Mb B Y r) {u : MulAut W} {z : W}
    {J : Finset (Fin 4)} (hA : T8Action B Y u z J) :
    3 ^ (4 * r - 3) ≤ Nat.card ↥((⨆ j, B j) ⊓ MulAction.stabilizer (MulAut W) z) := by
  classical
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hB.sq w
  have hr2 : 2 ≤ r := hB.two_le
  have hr1 : 1 ≤ r := by omega
  have hJle : J.card ≤ 3 := hA.card_le
  let A : Fin 4 → Subgroup (MulAut W) := fun j =>
    if j ∈ J then B j ⊓ Subgroup.centralizer ({u} : Set (MulAut W)) else B j
  have hAle : ∀ j, A j ≤ B j := by
    intro j
    by_cases hj : j ∈ J
    · simp only [A, if_pos hj]; exact inf_le_left
    · simp only [A, if_neg hj]; exact le_rfl
  have hAcomm : Pairwise fun i j => ∀ x y : MulAut W, x ∈ A i → y ∈ A j → Commute x y := by
    intro i j hij x y hx hy
    exact hB.commute i j hij x (hAle i hx) y (hAle j hy)
  have hindB : iSupIndep B := by
    rw [iSupIndep_def]
    intro j
    rw [disjoint_iff]
    simpa only [Set.mem_setOf_eq] using hB.indep j
  have hindA : iSupIndep A := hindB.mono hAle
  have hu_stab : ∀ i ∈ J, u ∈ stabSub (Y i) := by
    intro i hi
    have huτ : ∀ y : W, u (u y) = y := by
      intro y
      have := congrArg (fun φ : MulAut W => φ y) hA.sq
      simpa [MulAut.mul_apply] using this
    exact mem_stabSub.mpr (fun y => ⟨fun h => by rw [← huτ y]; exact hA.stab i (u y) h,
      fun h => hA.stab i y h⟩)
  have hAfix : ∀ j, A j ≤ MulAction.stabilizer (MulAut W) z := by
    intro j c hc
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    have hcB : c ∈ B j := hAle j hc
    have hcz : ∀ i ∈ J, commSub (Y i) (Subgroup.zpowers u) ≤ fixV (Subgroup.zpowers c) := by
      intro i hi
      by_cases hij : i = j
      · subst i
        have hcu : c ∈ Subgroup.centralizer ({u} : Set (MulAut W)) := by
          have hh : c ∈ B j ⊓ Subgroup.centralizer ({u} : Set (MulAut W)) := by
            simpa only [A, if_pos hi] using hc
          exact hh.2
        have hcu' : c * u * c⁻¹ = u := by
          have hcomm : u * c = c * u := hcu u (by simp)
          rw [← hcomm]; group
        have hcS : ∀ s ∈ commSub (Y j) (Subgroup.zpowers u),
            c s ∈ commSub (Y j) (Subgroup.zpowers u) :=
          t8_commSub_zpowers_map_of_conj hcu' (hB.stab j c hcB)
        have hcardS : Nat.card ↥(commSub (Y j) (Subgroup.zpowers u)) ≤ 2 := by
          have h2 : Nat.card ↥(commSub (Y j) (Subgroup.zpowers u)) =
              2 ^ rk ↥(commSub (Y j) (Subgroup.zpowers u)) := card_eq_two_pow hW2 _
          rw [h2]
          calc 2 ^ rk ↥(commSub (Y j) (Subgroup.zpowers u)) ≤ 2 ^ 1 :=
                Nat.pow_le_pow_right (by norm_num) (hA.transv j hi)
            _ = 2 := by norm_num
        exact t8_fix_of_card_le_two hB.sq hcS hcardS
      · have htriv : ∀ y ∈ Y i, c y = y := hB.triv j i (Ne.symm hij) c hcB
        unfold commSub
        rw [Subgroup.closure_le]
        rintro d ⟨x, hx, y, hy, rfl⟩
        change ∀ a ∈ Subgroup.zpowers c, a (x y * y⁻¹) = x y * y⁻¹
        intro a ha
        have haY : ∀ w ∈ Y i, a w = w :=
          mem_centSub.mp ((Subgroup.zpowers_le.mpr (mem_centSub.mpr htriv)) ha)
        have hxy : x y ∈ Y i :=
          (mem_stabSub.mp ((Subgroup.zpowers_le.mpr (hu_stab i hi)) hx) y).mpr hy
        rw [map_mul, map_inv, haY _ hxy, haY y hy]
    have hzmem : z ∈ fixV (Subgroup.zpowers c) := by
      have hle : (⨆ i ∈ J, commSub (Y i) (Subgroup.zpowers u)) ≤ fixV (Subgroup.zpowers c) :=
        iSup_le fun i => iSup_le fun hi => hcz i hi
      exact hle hA.z_mem
    exact (mem_fixV.mp hzmem) c (Subgroup.mem_zpowers c)
  have hj0 : ∃ j₀ : Fin 4, j₀ ∉ J := by
    by_contra h
    push Not at h
    have hJ : J = Finset.univ := by
      ext j
      simp [h j]
    have hcard : J.card = 4 := by rw [hJ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j₀, hj₀⟩ := hj0
  have hAn : ∀ j, 3 ^ (r - 1) ≤ Nat.card (A j) := by
    intro j
    by_cases hj : j ∈ J
    · have hc := s15_T8_comm_card hB.sq (hB.comm j) (hB.cube j) (hB.stab j) (hB.faith j)
          hA.sq (hA.stab j) (hA.norm j) (hA.transv j hj)
      have hAj : A j = B j ⊓ Subgroup.centralizer ({u} : Set (MulAut W)) := by
        simp only [A, if_pos hj]
      rw [hAj]
      have h3r : Nat.card (B j) = 3 ^ r := hB.card j
      have hthis : 3 ^ r = 3 * 3 ^ (r - 1) := by
        calc 3 ^ r = 3 ^ ((r - 1) + 1) := by
              rw [Nat.sub_add_cancel hr1]
          _ = 3 ^ (r - 1) * 3 := by rw [pow_succ]
          _ = 3 * 3 ^ (r - 1) := by ring
      rw [h3r, hthis] at hc
      exact Nat.le_of_mul_le_mul_left hc (by norm_num)
    · have hAj : A j = B j := by simp only [A, if_neg hj]
      rw [hAj, hB.card j]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le r 1)
  have hAj0 : Nat.card (A j₀) = 3 ^ r := by
    have hAj : A j₀ = B j₀ := by simp only [A, if_neg hj₀]
    rw [hAj, hB.card j₀]
  have hprod_bound : 3 ^ (4 * r - 3) ≤ ∏ j : Fin 4, Nat.card (A j) := by
    have hP : (3 ^ (r - 1)) ^ 3 ≤ ∏ j ∈ Finset.univ.erase j₀, Nat.card (A j) := by
      have hle : ∏ j ∈ Finset.univ.erase j₀, 3 ^ (r - 1) ≤
          ∏ j ∈ Finset.univ.erase j₀, Nat.card (A j) :=
        Finset.prod_le_prod (fun j _ => hAn j)
      have hcard : (Finset.univ.erase j₀).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_const, hcard] at hle
      exact hle
    have hsplit : (∏ j : Fin 4, Nat.card (A j)) =
        Nat.card (A j₀) * ∏ j ∈ Finset.univ.erase j₀, Nat.card (A j) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => Nat.card (A j)) (Finset.mem_univ j₀)]
    rw [hsplit, hAj0]
    calc 3 ^ (4 * r - 3) = 3 ^ r * (3 ^ (r - 1)) ^ 3 := by
          rw [← pow_mul, ← pow_add]
          congr 1
          omega
      _ ≤ 3 ^ r * ∏ j ∈ Finset.univ.erase j₀, Nat.card (A j) := Nat.mul_le_mul_left _ hP
  have hcard_join : Nat.card ↥(⨆ j, A j) = ∏ j, Nat.card (A j) :=
    t8_card_iSup_prod A hAcomm hindA
  have hle_join : (⨆ j, A j) ≤ (⨆ j, B j) ⊓ MulAction.stabilizer (MulAut W) z :=
    le_inf (iSup_le fun j => le_trans (hAle j) (le_iSup B j)) (iSup_le hAfix)
  rw [← hcard_join] at hprod_bound
  exact le_trans hprod_bound (Subgroup.card_le_of_le hle_join)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
