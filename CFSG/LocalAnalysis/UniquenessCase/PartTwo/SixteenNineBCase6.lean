module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7A5
public import CFSG.Quasithin.Background.FFC4Small1
public import CFSG.CGT.PushingUpLit.BHS6.SymAltFacts
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16n9b_commSub_sup_direct {T : Type*} [CommGroup T]
    {U V : Subgroup T} {e : MulAut T} (hU : ∀ u ∈ U, e u ∈ U) (hV : ∀ v ∈ V, e v ∈ V) :
    commSub (U ⊔ V) (Subgroup.zpowers e) =
      commSub U (Subgroup.zpowers e) ⊔ commSub V (Subgroup.zpowers e) := by
  refine le_antisymm ?_ (sup_le (commSub_mono le_sup_left le_rfl)
    (commSub_mono le_sup_right le_rfl))
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hw
  have h1 : x (u * v) * (u * v)⁻¹ = (x u * u⁻¹) * (x v * v⁻¹) := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  rw [h1]
  exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩)
    (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩)

private theorem s16n9b_mem_stabSub_of_map_eq {T : Type*} [CommGroup T] {W : Subgroup T}
    {e : MulAut T} (h : W.map e.toMonoidHom = W) : e ∈ stabSub W := by
  intro u
  constructor
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := e.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rwa [h] at hu'

private theorem s16n9b_sq_eq_one_on {T : Type*} [CommGroup T] [Finite T]
    (hexp : ∀ t : T, t ^ 2 = 1) {U : Subgroup T} {e : MulAut T}
    (heU : ∀ u ∈ U, e u ∈ U)
    (hrk : rk ↥(commSub U (Subgroup.zpowers e)) ≤ 1) :
    ∀ u ∈ U, e (e u) = u := by
  intro u hu
  have hmap : ∀ c ∈ commSub U (Subgroup.zpowers e), e c ∈ commSub U (Subgroup.zpowers e) := by
    rw [commSub]
    intro c hc
    refine Subgroup.closure_induction
      (p := fun c _ => e c ∈ Subgroup.closure
        {d | ∃ x ∈ Subgroup.zpowers e, ∃ w ∈ U, x w * w⁻¹ = d}) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨x, hx, w, hw, rfl⟩
      have hcomm : e * x = x * e := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← hn]
        exact (Commute.self_zpow e n).eq
      have h1 : e (x w * w⁻¹) = x (e w) * (e w)⁻¹ := by
        rw [map_mul, map_inv]
        have h2 : e (x w) = x (e w) := by
          have := congrArg (fun z : MulAut T => z w) hcomm
          simpa [MulAut.mul_apply] using this
        rw [h2]
      rw [h1]
      exact Subgroup.subset_closure ⟨x, hx, e w, heU w hw, rfl⟩
    · simp
    · intro a b _ _ ha hb
      have h : e (a * b) = e a * e b := map_mul e a b
      rw [h]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have h : e a⁻¹ = (e a)⁻¹ := map_inv e a
      rw [h]
      exact Subgroup.inv_mem _ ha
  have hcard : Nat.card ↥(commSub U (Subgroup.zpowers e)) ≤ 2 := by
    calc Nat.card ↥(commSub U (Subgroup.zpowers e)) =
        2 ^ rk ↥(commSub U (Subgroup.zpowers e)) := card_eq_two_pow hexp _
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 2 := by norm_num
  have hfix := s15_Core_map_eq_self_of_card_le_two (commSub U (Subgroup.zpowers e)) e hcard hmap
  set c : T := e u * u⁻¹ with hcdef
  have hcC : c ∈ commSub U (Subgroup.zpowers e) :=
    Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, u, hu, rfl⟩
  have hec : e c = c := hfix c hcC
  have heu : e u = c * u := by
    rw [hcdef]
    group
  calc e (e u) = e (c * u) := by rw [heu]
    _ = e c * e u := map_mul e c u
    _ = c * (c * u) := by rw [hec, heu]
    _ = 1 * u := by
      have hc2 : c * c = 1 := by rw [← pow_two]; exact hexp c
      rw [← mul_assoc, hc2, one_mul]
    _ = u := one_mul u

private theorem s16n9b_small_rank_sq {T : Type*} [CommGroup T] [Finite T]
    (hexp : ∀ t : T, t ^ 2 = 1) {A : Subgroup (MulAut T)} {W : Subgroup T}
    {I : Fin 2 → Subgroup T} (hW : I 0 ⊔ I 1 = W) (h01 : I 0 ⊓ I 1 = ⊥)
    (hIinv : ∀ i : Fin 2, ∀ a ∈ A, ∀ u ∈ I i, a u ∈ I i)
    (hIfaith : ∀ i : Fin 2, ∀ a ∈ A, (∀ u ∈ I i, a u = u) → a = 1)
    (hWfaith : ∀ a ∈ A, (∀ w ∈ W, a w = w) → a = 1)
    {e : MulAut T} (he : e ∈ A) :
    rk ↥(commSub W (Subgroup.zpowers e)) ≤ 2 → e ^ 2 = 1 := by
  intro hrk
  by_cases he1 : e = 1
  · rw [he1, one_pow]
  · have hC0 : commSub (I 0) (Subgroup.zpowers e) ≠ ⊥ := by
      intro hbot
      exact he1 (hIfaith 0 e he fun u hu =>
        mem_fixV_zpowers_iff_apply.mp ((commSub_eq_bot_iff.mp hbot) hu))
    have hC1 : commSub (I 1) (Subgroup.zpowers e) ≠ ⊥ := by
      intro hbot
      exact he1 (hIfaith 1 e he fun u hu =>
        mem_fixV_zpowers_iff_apply.mp ((commSub_eq_bot_iff.mp hbot) hu))
    have hstabI : ∀ i : Fin 2, Subgroup.zpowers e ≤ stabSub (I i) := by
      intro i
      refine (Subgroup.zpowers_le).2 (s16n9b_mem_stabSub_of_map_eq ?_)
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨u, hu, rfl⟩
        exact hIinv i e he u hu
      · rw [Subgroup.card_map_of_injective e.injective]
    have hle0 : commSub (I 0) (Subgroup.zpowers e) ≤ I 0 :=
      commSub_le_of_invariant fun x hx u hu => (mem_stabSub.1 (hstabI 0 hx) u).2 hu
    have hle1 : commSub (I 1) (Subgroup.zpowers e) ≤ I 1 :=
      commSub_le_of_invariant fun x hx u hu => (mem_stabSub.1 (hstabI 1 hx) u).2 hu
    have hinf : commSub (I 0) (Subgroup.zpowers e) ⊓
        commSub (I 1) (Subgroup.zpowers e) = ⊥ := by
      rw [eq_bot_iff]
      exact le_trans (inf_le_inf hle0 hle1) (le_of_eq h01)
    have hsum : commSub W (Subgroup.zpowers e) =
        commSub (I 0) (Subgroup.zpowers e) ⊔ commSub (I 1) (Subgroup.zpowers e) := by
      rw [← hW]
      exact s16n9b_commSub_sup_direct (fun u hu => hIinv 0 e he u hu)
        (fun u hu => hIinv 1 e he u hu)
    have hrank := rk_sup_add_rk_inf (commSub (I 0) (Subgroup.zpowers e))
      (commSub (I 1) (Subgroup.zpowers e))
    rw [hinf, rk_bot, ← hsum] at hrank
    have hz0 : rk ↥(commSub (I 0) (Subgroup.zpowers e)) ≠ 0 := by
      intro h0
      exact hC0 (rk_eq_zero_iff hexp |>.mp h0)
    have hz1 : rk ↥(commSub (I 1) (Subgroup.zpowers e)) ≠ 0 := by
      intro h0
      exact hC1 (rk_eq_zero_iff hexp |>.mp h0)
    have h0 : rk ↥(commSub (I 0) (Subgroup.zpowers e)) = 1 := by omega
    have h1 : rk ↥(commSub (I 1) (Subgroup.zpowers e)) = 1 := by omega
    have hsq0 : ∀ u ∈ I 0, e (e u) = u :=
      s16n9b_sq_eq_one_on hexp (fun u hu => hIinv 0 e he u hu) (by omega)
    have hsq1 : ∀ u ∈ I 1, e (e u) = u :=
      s16n9b_sq_eq_one_on hexp (fun u hu => hIinv 1 e he u hu) (by omega)
    apply hWfaith (e ^ 2) (A.pow_mem he 2)
    intro w hw
    rw [← hW] at hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
    show (e ^ 2) (x * y) = x * y
    rw [pow_two, MulAut.mul_apply, map_mul, map_mul, hsq0 x hx, hsq1 y hy]

private theorem s16n9b_fix_pointwise_eq_one {T : Type*} [CommGroup T] {D : FFModel}
    (hD : D.Faithful) {A : Subgroup (MulAut T)} {U : Subgroup T}
    {π : D.Gam →* ↥A} (h : D.RealizesVia A U ⊥ π) {a : ↥A}
    (ha : ∀ u ∈ U, (a : MulAut T) u = u) : a = 1 := by
  obtain ⟨hπs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  obtain ⟨γ, hγ⟩ := hπs a
  have hγ1 : γ = 1 := by
    apply hD
    intro m hm
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    have huU : ((π γ : ↥A) : MulAut T) (u : T) ∈ U := by
      rw [hγ]
      rw [ha u u.2]
      exact u.2
    have h1 := hβe γ u ⟨m, hm⟩ huU (hsec γ m hm) hu
    have h2 : (⟨((π γ : ↥A) : MulAut T) (u : T), huU⟩ : ↥U) = u := by
      apply Subtype.ext
      show ((π γ : ↥A) : MulAut T) (u : T) = (u : T)
      rw [hγ]
      exact ha u u.2
    rw [h2, hu] at h1
    have h3 := QuotientGroup.eq.mp h1
    rw [mul_comm]
    exact h3
  rw [← hγ, hγ1, map_one]

private theorem s16n9b_fixV_altDn_five {T : Type} [CommGroup T] {A : Subgroup (MulAut T)}
    {U : Subgroup T} (h : AlternatingNatural A U ⊥ 5) : fixV A ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨huFix, huU⟩
  obtain ⟨π, ε, -, hHU, hε⟩ := s15_T7_exists_iso h
  have hε1 : ε ⟨u, huU⟩ = 1 := by
    apply CFSG.CGT.PushingUpLit.BHS6.eq_one_of_fixed_alt (n := 5) (by norm_num) (by norm_num)
    intro σ hσ
    have hmem : ((π ⟨σ, hσ⟩ : ↥A) : MulAut T) u ∈ U := hHU (π ⟨σ, hσ⟩) u huU
    have heq : (⟨((π ⟨σ, hσ⟩ : ↥A) : MulAut T) u, hmem⟩ : ↥U) = ⟨u, huU⟩ :=
      Subtype.ext (huFix _ (π ⟨σ, hσ⟩).2)
    have h1 := hε ⟨σ, hσ⟩ ⟨u, huU⟩ hmem
    rw [heq] at h1
    exact h1.symm
  have hu1 : u = 1 := by
    have hsub : (⟨u, huU⟩ : ↥U) = 1 := ε.injective (by rw [hε1, map_one])
    exact congrArg Subtype.val hsub
  exact Subgroup.mem_bot.mpr hu1

private theorem s16n9b_not_comm_of_simple {X : Type*} [Group X] [Finite X]
    (hS : IsSimpleGroup X) (hcard : ¬ (Nat.card X).Prime) : ¬ IsMulCommutative X := by
  intro hc
  haveI : IsMulCommutative X := hc
  exact hcard (Group.is_simple_iff_prime_card.mp hS)

private theorem s16n9b_rk_map {T : Type*} [CommGroup T] (e : MulAut T) (U : Subgroup T) :
    rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  unfold rk
  rw [Subgroup.card_map_of_injective e.injective]

private noncomputable def s16n9bComOn {T : Type*} [CommGroup T] (W : Subgroup T)
    (e : MulAut T) : ↥W →* T where
  toFun w := e (w : T) * (w : T)⁻¹
  map_one' := by simp
  map_mul' w1 w2 := by
    change e ((w1 : T) * (w2 : T)) * ((w1 : T) * (w2 : T))⁻¹ =
      (e (w1 : T) * (w1 : T)⁻¹) * (e (w2 : T) * (w2 : T)⁻¹)
    rw [map_mul, mul_inv]
    simpa only [mul_assoc] using
      mul_mul_mul_comm' (e (w1 : T)) (e (w2 : T)) ((w1 : T)⁻¹) ((w2 : T)⁻¹)

private theorem s16n9b_commSub_eq_range {T : Type*} [CommGroup T] [Finite T] {W : Subgroup T}
    {e : MulAut T} (heW : ∀ w ∈ W, e w ∈ W) :
    commSub W (Subgroup.zpowers e) = (s16n9bComOn W e).range := by
  have hmapW : W.map e.toMonoidHom = W := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨w, hw, rfl⟩
      exact heW w hw
    · rw [Subgroup.card_map_of_injective e.injective]
  have hstab : e ∈ stabSub W := s16n9b_mem_stabSub_of_map_eq hmapW
  have hzpow : Subgroup.zpowers e ≤ stabSub W := (Subgroup.zpowers_le).2 hstab
  have heWpow : ∀ n : ℤ, ∀ w ∈ W, (e ^ n) w ∈ W := by
    intro n w hw
    exact (mem_stabSub.1 (hzpow (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)) w).2 hw
  have key_nat : ∀ k : ℕ, ∀ w : ↥W,
      (e ^ (k : ℤ)) (w : T) * (w : T)⁻¹ ∈ (s16n9bComOn W e).range := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      have h1 : (e ^ ((k : ℤ) + 1)) (w : T) * (w : T)⁻¹ =
          (s16n9bComOn W e) ⟨(e ^ (k : ℤ)) (w : T), heWpow _ w w.2⟩ *
            ((e ^ (k : ℤ)) (w : T) * (w : T)⁻¹) := by
        change (e ^ ((k : ℤ) + 1)) (w : T) * (w : T)⁻¹ =
          (e ((e ^ (k : ℤ)) (w : T)) * ((e ^ (k : ℤ)) (w : T))⁻¹) *
            ((e ^ (k : ℤ)) (w : T) * (w : T)⁻¹)
        rw [show (k : ℤ) + 1 = 1 + (k : ℤ) by ring, zpow_one_add]
        simp only [MulAut.mul_apply]
        group
      rw [Nat.cast_succ, h1]
      exact (s16n9bComOn W e).range.mul_mem ⟨_, rfl⟩ (ih w)
  have key : ∀ n : ℤ, ∀ w : ↥W,
      (e ^ n) (w : T) * (w : T)⁻¹ ∈ (s16n9bComOn W e).range := by
    intro n
    by_cases hn : 0 ≤ n
    · rw [show n = (n.toNat : ℤ) by omega]
      exact key_nat n.toNat
    · intro w
      set m : ℕ := (-n).toNat with hmdef
      have hmn : (m : ℤ) + n = 0 := by
        have : (m : ℤ) = -n := by omega
        omega
      have hX : (e ^ n) (w : T) ∈ W := heWpow n w w.2
      have h1 : (e ^ (m : ℤ)) ((e ^ n) (w : T)) * ((e ^ n) (w : T))⁻¹ ∈
          (s16n9bComOn W e).range := key_nat m ⟨(e ^ n) (w : T), hX⟩
      have h3 : (e ^ (m : ℤ)) ((e ^ n) (w : T)) = (w : T) := by
        rw [← MulAut.mul_apply, ← zpow_add, hmn, zpow_zero, MulAut.one_apply]
      have h2 : ((e ^ (m : ℤ)) ((e ^ n) (w : T)) * ((e ^ n) (w : T))⁻¹)⁻¹ =
          (e ^ n) (w : T) * (w : T)⁻¹ := by
        rw [h3]
        group
      rw [← h2]
      exact (s16n9bComOn W e).range.inv_mem h1
  refine le_antisymm ?_ ?_
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact key k ⟨w, hw⟩
  · rintro _ ⟨w, rfl⟩
    exact Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, w, w.2, rfl⟩

private theorem s16n9b_commSub_zpowers_mul_le {T : Type} [CommGroup T] [Finite T]
    {W : Subgroup T} {x y : MulAut T} (hxW : ∀ w ∈ W, x w ∈ W)
    (hyW : ∀ w ∈ W, y w ∈ W) :
    commSub W (Subgroup.zpowers (x * y)) ≤
      commSub W (Subgroup.zpowers x) ⊔ commSub W (Subgroup.zpowers y) := by
  have hxy : commSub W (Subgroup.zpowers (x * y)) = (s16n9bComOn W (x * y)).range :=
    s16n9b_commSub_eq_range (fun w hw => hxW (y w) (hyW w hw))
  have hx : commSub W (Subgroup.zpowers x) = (s16n9bComOn W x).range :=
    s16n9b_commSub_eq_range hxW
  have hy : commSub W (Subgroup.zpowers y) = (s16n9bComOn W y).range :=
    s16n9b_commSub_eq_range hyW
  calc commSub W (Subgroup.zpowers (x * y))
      = (s16n9bComOn W (x * y)).range := hxy
    _ ≤ (s16n9bComOn W x).range ⊔ (s16n9bComOn W y).range := by
        rintro _ ⟨w, rfl⟩
        show (x * y) (w : T) * (w : T)⁻¹ ∈
          (s16n9bComOn W x).range ⊔ (s16n9bComOn W y).range
        have hyw : y (w : T) ∈ W := hyW w w.2
        have h1 : (x * y) (w : T) * (w : T)⁻¹ =
            (x (y (w : T)) * (y (w : T))⁻¹) * (y (w : T) * (w : T)⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [h1]
        exact Subgroup.mul_mem_sup
          (MonoidHom.mem_range.mpr ⟨⟨y (w : T), hyw⟩, rfl⟩)
          (MonoidHom.mem_range.mpr ⟨w, rfl⟩)
    _ = commSub W (Subgroup.zpowers x) ⊔ commSub W (Subgroup.zpowers y) := by rw [hx, hy]

private theorem s16n9b_rk_sup_le {T : Type*} [CommGroup T] [Finite T]
    (U V : Subgroup T) : rk ↥(U ⊔ V) ≤ rk ↥U + rk ↥V := by
  have h := rk_sup_add_rk_inf U V
  omega

private theorem s16n9b_isMulCommutative_closure {X : Type*} [Group X] {S : Set X}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    IsMulCommutative ↥(Subgroup.closure S) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxcomm : ∀ s ∈ S, (x : X) * s = s * (x : X) := by
    refine Subgroup.closure_induction
      (p := fun z _ => ∀ s ∈ S, z * s = s * z) ?_ ?_ ?_ ?_ x.2
    · intro z hz s hs
      exact hS z hz s hs
    · intro s hs
      rw [one_mul, mul_one]
    · intro a b _ _ ha hb s hs
      rw [mul_assoc, hb s hs, ← mul_assoc, ha s hs, mul_assoc]
    · intro a _ ha s hs
      calc a⁻¹ * s = a⁻¹ * (s * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * s) * a⁻¹ := by rw [ha s hs]
        _ = s * a⁻¹ := by group
  apply Subtype.ext
  change (x : X) * (y : X) = (y : X) * (x : X)
  refine Subgroup.closure_induction
    (p := fun z _ => (x : X) * z = z * (x : X)) ?_ ?_ ?_ ?_ y.2
  · intro z hz
    exact hxcomm z hz
  · rw [mul_one, one_mul]
  · intro a b _ _ ha hb
    rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  · intro a _ ha
    calc (x : X) * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * x := by group

private theorem s16n9b_commute_of_sq {X : Type*} [Group X] {x y : X}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

private theorem s16n9b_mul_comm_mul {X : Type*} [Group X] {x y z w : X}
    (hxz : x * z = z * x) (hxw : x * w = w * x) (hyz : y * z = z * y)
    (hyw : y * w = w * y) : (x * y) * (z * w) = (z * w) * (x * y) := by
  calc (x * y) * (z * w) = x * (y * (z * w)) := by group
    _ = x * ((y * z) * w) := by group
    _ = x * ((z * y) * w) := by rw [hyz]
    _ = x * (z * (y * w)) := by group
    _ = x * (z * (w * y)) := by rw [hyw]
    _ = (x * z) * (w * y) := by group
    _ = (z * x) * (w * y) := by rw [hxz]
    _ = z * (x * (w * y)) := by group
    _ = z * ((x * w) * y) := by group
    _ = z * ((w * x) * y) := by rw [hxw]
    _ = z * (w * (x * y)) := by group
    _ = (z * w) * (x * y) := by group

private theorem s16n9b_no_small_rank {T : Type} [CommGroup T] [Finite T]
    (hexp : ∀ t : T, t ^ 2 = 1)
    {A : Subgroup (MulAut T)} {W : Subgroup T}
    (hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hAs : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A)
    (hWfaith : ∀ a ∈ A, (∀ w ∈ W, a w = w) → a = 1)
    (hM3 : ∀ v ∈ W, (∀ a ∈ A, a v = v) → v = 1)
    (hstep3 : ∀ e ∈ A, rk ↥(commSub W (Subgroup.zpowers e)) ≤ 2 → e ^ 2 = 1)
    {φ : MulAut T} (hφA : A.map (MulAut.conj φ).toMonoidHom = A)
    (hφW : ∀ w ∈ W, φ w ∈ W)
    (hrkφ : rk ↥(commSub W (Subgroup.zpowers φ)) ≤ 1)
    (hnotcent : ¬ ∀ w ∈ W, φ w = w) : False := by
  have hφsq : ∀ w ∈ W, φ (φ w) = w := s16n9b_sq_eq_one_on hexp hφW hrkφ
  have hstabφ : φ ∈ stabSub W := by
    intro u
    constructor
    · intro hu
      have h1 : φ (φ (φ u)) = φ u := hφsq (φ u) hu
      have h2 : φ (φ u) = u := φ.injective h1
      rw [← h2]
      exact hφW (φ u) hu
    · intro hu
      exact hφW u hu
  have hstabA : A ≤ stabSub W := by
    intro a ha u
    constructor
    · intro hu
      have h := hAW a⁻¹ (A.inv_mem ha) (a u) hu
      simpa using h
    · intro hu
      exact hAW a ha u hu
  let r : ↥A →* ↥(autSub A W) :=
    { toFun := fun a => ⟨resHom W ⟨(a : MulAut T), hstabA a.2⟩,
        mem_autSub.mpr ⟨⟨(a : MulAut T), hstabA a.2⟩, a.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul (resHom W) ⟨(a : MulAut T), hstabA a.2⟩
          ⟨(b : MulAut T), hstabA b.2⟩ }
  have rsurj : Function.Surjective r := by
    intro y
    obtain ⟨g, hg, hgy⟩ := mem_autSub.mp y.2
    exact ⟨⟨(g : MulAut T), hg⟩, Subtype.ext hgy⟩
  have rinj : Function.Injective r := by
    intro a b hab
    have h1 : resHom W ⟨(a : MulAut T), hstabA a.2⟩ =
        resHom W ⟨(b : MulAut T), hstabA b.2⟩ := congrArg Subtype.val hab
    have hres : resHom W ⟨((a⁻¹ * b : ↥A) : MulAut T), hstabA (a⁻¹ * b).2⟩ = 1 := by
      rw [show (⟨((a⁻¹ * b : ↥A) : MulAut T), hstabA (a⁻¹ * b).2⟩ : stabSub W) =
          ⟨(a : MulAut T), hstabA a.2⟩⁻¹ * ⟨(b : MulAut T), hstabA b.2⟩
          from Subtype.ext rfl,
        map_mul, map_inv]
      rw [h1]
      rw [inv_mul_cancel]
    have hfix : ∀ w ∈ W, ((a⁻¹ * b : ↥A) : MulAut T) w = w := by
      intro w hw
      have h2 : (resHom W ⟨((a⁻¹ * b : ↥A) : MulAut T), hstabA (a⁻¹ * b).2⟩)
          ⟨w, hw⟩ = (1 : MulAut W) ⟨w, hw⟩ := by
        rw [hres]
      have := congrArg (fun z : W => (z : T)) h2
      simpa [resHom_apply] using this
    have h1' : (a⁻¹ * b : ↥A) = 1 :=
      Subtype.ext (hWfaith ((a⁻¹ * b : ↥A) : MulAut T) (a⁻¹ * b).2 hfix)
    exact inv_mul_eq_one.mp h1'
  let eAW : ↥A ≃* ↥(autSub A W) := MulEquiv.ofBijective r ⟨rinj, rsurj⟩
  have hBsimple : IsSimpleGroup ↥(autSub A W) := by
    haveI : IsSimpleGroup ↥A := hAs
    exact MulEquiv.isSimpleGroup eAW.symm
  have hBnoncomm : ¬ IsMulCommutative ↥(autSub A W) := by
    intro hc
    haveI : IsMulCommutative ↥(autSub A W) := hc
    apply hAn
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eAW.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  let ι : MulAut W := resHom W ⟨φ, hstabφ⟩
  have hιN : ∀ b ∈ autSub A W, ι * b * ι⁻¹ ∈ autSub A W := by
    intro b hb
    obtain ⟨g, hg, hgb⟩ := mem_autSub.mp hb
    have hmemA : φ * (g : MulAut T) * φ⁻¹ ∈ A := by
      have h : (MulAut.conj φ) (g : MulAut T) ∈ A.map (MulAut.conj φ).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hg
      rwa [hφA] at h
    have hmemStab : (⟨φ, hstabφ⟩ * g * ⟨φ, hstabφ⟩⁻¹ : stabSub W) ∈
        A.subgroupOf (stabSub W) := by
      rw [Subgroup.mem_subgroupOf]
      exact hmemA
    have hthis := mem_autSub.mpr
      ⟨⟨φ, hstabφ⟩ * g * ⟨φ, hstabφ⟩⁻¹, hmemStab, rfl⟩
    rwa [map_mul, map_mul, map_inv, hgb] at hthis
  let f : ↥(autSub A W) → ↥(autSub A W) := fun b =>
    ⟨(b : MulAut W) * (ι * (b : MulAut W)⁻¹ * ι⁻¹), by
      have h1 : ι * (b : MulAut W)⁻¹ * ι⁻¹ ∈ autSub A W :=
        hιN (b : MulAut W)⁻¹ ((autSub A W).inv_mem b.2)
      exact (autSub A W).mul_mem b.2 h1⟩
  let K : Subgroup ↥(autSub A W) := Subgroup.closure (Set.range f)
  have hKnormal : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hconj : ∀ x : ↥(autSub A W), g * f x * g⁻¹ = f (g * x) * (f g)⁻¹ := by
      intro x
      apply Subtype.ext
      show (g : MulAut W) * ((x : MulAut W) * (ι * (x : MulAut W)⁻¹ * ι⁻¹)) *
          (g : MulAut W)⁻¹ =
        (((g * x : ↥(autSub A W)) : MulAut W) *
            (ι * (((g * x : ↥(autSub A W)) : MulAut W))⁻¹ * ι⁻¹)) *
          (((g : MulAut W) * (ι * (g : MulAut W)⁻¹ * ι⁻¹))⁻¹)
      simp only [Subgroup.coe_mul]
      group
    rw [show K = Subgroup.closure (Set.range f) from rfl] at hn ⊢
    refine Subgroup.closure_induction
      (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure (Set.range f)) ?_ ?_ ?_ ?_ hn
    · rintro _ ⟨x, rfl⟩
      rw [hconj x]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨g * x, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g, rfl⟩))
    · simp
    · intro a b _ _ ha hb
      have h : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have h : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ha
  have hKbot_top : K = ⊥ ∨ K = ⊤ := by
    haveI : K.Normal := hKnormal
    exact hBsimple.eq_bot_or_eq_top_of_normal K
  rcases hKbot_top with hKbot | hKtop
  ·
    have hf1 : ∀ b : ↥(autSub A W), f b = 1 := by
      intro b
      have : f b ∈ K := Subgroup.subset_closure ⟨b, rfl⟩
      rw [hKbot] at this
      exact Subgroup.mem_bot.mp this
    have hcomm : ∀ b : ↥(autSub A W), (b : MulAut W) * ι = ι * b := by
      intro b
      have h := hf1 b
      have h1 : (b : MulAut W) * (ι * (b : MulAut W)⁻¹ * ι⁻¹) = 1 := by
        have := congrArg Subtype.val h
        simpa [f] using this
      have h2 : (b : MulAut W) * ι * (b : MulAut W)⁻¹ = ι := by
        calc (b : MulAut W) * ι * (b : MulAut W)⁻¹
            = ((b : MulAut W) * (ι * (b : MulAut W)⁻¹ * ι⁻¹)) * ι := by group
          _ = 1 * ι := by rw [h1]
          _ = ι := one_mul ι
      calc (b : MulAut W) * ι = ((b : MulAut W) * ι * (b : MulAut W)⁻¹) * b := by group
        _ = ι * b := by rw [h2]
    have hCinv : ∀ a ∈ A, ∀ c ∈ commSub W (Subgroup.zpowers φ),
        a c ∈ commSub W (Subgroup.zpowers φ) := by
      intro a ha c hc
      rw [s16n9b_commSub_eq_range hφW] at hc ⊢
      obtain ⟨w, rfl⟩ := hc
      have hcomm_a : (a : MulAut T) (φ (w : T)) = φ ((a : MulAut T) w) := by
        have h := hcomm (r ⟨a, ha⟩)
        have h2 := congrArg (fun z : MulAut W => z ⟨w, w.2⟩) h
        have h3 := congrArg (fun z : W => (z : T)) h2
        simpa [r, ι, MulAut.mul_apply, resHom_apply] using h3
      refine ⟨⟨(a : MulAut T) w, hAW a ha w w.2⟩, ?_⟩
      change φ ((a : MulAut T) w) * ((a : MulAut T) w)⁻¹ =
        (a : MulAut T) (φ (w : T) * (w : T)⁻¹)
      rw [map_mul, map_inv, hcomm_a]
    have hCne : commSub W (Subgroup.zpowers φ) ≠ ⊥ := by
      intro hbot
      exact hnotcent fun w hw =>
        mem_fixV_zpowers_iff_apply.mp ((commSub_eq_bot_iff.mp hbot) hw)
    have hcardC : Nat.card ↥(commSub W (Subgroup.zpowers φ)) = 2 := by
      have h0 : rk ↥(commSub W (Subgroup.zpowers φ)) ≠ 0 := by
        intro hz
        exact hCne (rk_eq_zero_iff hexp |>.mp hz)
      have h1 : rk ↥(commSub W (Subgroup.zpowers φ)) = 1 := by omega
      rw [card_eq_two_pow hexp, h1, pow_one]
    have hcardC2 : Nat.card ↥(commSub W (Subgroup.zpowers φ)) ≤ 2 := by omega
    obtain ⟨v, hvne, -⟩ := (Nat.card_eq_two_iff'
      (1 : ↥(commSub W (Subgroup.zpowers φ)))).1 hcardC
    have hvC : (v : T) ∈ commSub W (Subgroup.zpowers φ) := v.2
    have hv1 : (v : T) ≠ 1 := fun h => hvne (Subtype.ext h)
    have hCW : commSub W (Subgroup.zpowers φ) ≤ W :=
      commSub_le_of_invariant fun x hx u hu =>
        (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstabφ hx) u).2 hu
    have hvW : (v : T) ∈ W := hCW hvC
    refine hv1 (hM3 (v : T) hvW fun a ha => ?_)
    exact s15_Core_map_eq_self_of_card_le_two _ a hcardC2
      (fun c hc => hCinv a ha c hc) (v : T) hvC
  ·
    have hfsq : ∀ b : ↥(autSub A W), f b * f b = 1 := by
      intro b
      obtain ⟨a, rfl⟩ := rsurj b
      let e : MulAut T := (a : MulAut T) * φ * (a : MulAut T)⁻¹ * φ⁻¹
      have heA : e ∈ A := by
        have h : (MulAut.conj φ) ((a : MulAut T)⁻¹) ∈
            A.map (MulAut.conj φ).toMonoidHom :=
          Subgroup.mem_map_of_mem _ (A.inv_mem a.2)
        rw [hφA] at h
        have h2 : (a : MulAut T) * (φ * (a : MulAut T)⁻¹ * φ⁻¹) ∈ A := A.mul_mem a.2 h
        convert h2 using 1
        show ((a : MulAut T) * φ * (a : MulAut T)⁻¹ * φ⁻¹) =
          (a : MulAut T) * (φ * (a : MulAut T)⁻¹ * φ⁻¹)
        group
      have hxW : ∀ w ∈ W, ((a : MulAut T) * φ * (a : MulAut T)⁻¹) w ∈ W := by
        intro w hw
        have h1 : (a : MulAut T)⁻¹ w ∈ W := hAW a⁻¹ (A.inv_mem a.2) w hw
        have h2 : φ ((a : MulAut T)⁻¹ w) ∈ W := hφW _ h1
        exact hAW a a.2 _ h2
      have hxinvW : ∀ w ∈ W, φ⁻¹ w ∈ W := fun w hw =>
        (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstabφ
          ((Subgroup.zpowers φ).inv_mem (Subgroup.mem_zpowers φ))) w).2 hw
      have hrank_e : rk ↥(commSub W (Subgroup.zpowers e)) ≤ 2 := by
        have hmul := s16n9b_commSub_zpowers_mul_le (W := W)
          (x := (a : MulAut T) * φ * (a : MulAut T)⁻¹) (y := φ⁻¹) hxW hxinvW
        have heq : e = ((a : MulAut T) * φ * (a : MulAut T)⁻¹) * φ⁻¹ := rfl
        rw [heq]
        have hφinv : commSub W (Subgroup.zpowers φ⁻¹) =
            commSub W (Subgroup.zpowers φ) := by rw [Subgroup.zpowers_inv]
        rw [hφinv] at hmul
        have hxrk : rk ↥(commSub W (Subgroup.zpowers
            ((a : MulAut T) * φ * (a : MulAut T)⁻¹))) ≤ 1 := by
          have hWa : W.map (a : MulAut T).toMonoidHom = W := by
            apply Subgroup.eq_of_le_of_card_ge
            · rintro _ ⟨w, hw, rfl⟩
              exact hAW a a.2 w hw
            · rw [Subgroup.card_map_of_injective (a : MulAut T).injective]
          have hWai : W.map ((a : MulAut T)⁻¹).toMonoidHom = W := by
            apply Subgroup.eq_of_le_of_card_ge
            · rintro _ ⟨w, hw, rfl⟩
              exact hAW a⁻¹ (A.inv_mem a.2) w hw
            · rw [Subgroup.card_map_of_injective ((a : MulAut T)⁻¹).injective]
          have hconj := s15_Core_commSub_map_conj (W.map ((a : MulAut T)⁻¹).toMonoidHom)
            (Subgroup.zpowers φ) (a : MulAut T)
          have hmapz : (Subgroup.zpowers φ).map (MulAut.conj (a : MulAut T)).toMonoidHom =
              Subgroup.zpowers ((a : MulAut T) * φ * (a : MulAut T)⁻¹) := by
            rw [MonoidHom.map_zpowers]
            rfl
          rw [hWai, hWa] at hconj
          rw [← hmapz, hconj, s16n9b_rk_map]
          exact hrkφ
        have hle := s16n9b_rk_sup_le (commSub W (Subgroup.zpowers
          ((a : MulAut T) * φ * (a : MulAut T)⁻¹))) (commSub W (Subgroup.zpowers φ))
        have hmono := rk_mono hmul
        omega
      have he2 : e * e = 1 := by
        have := hstep3 e heA hrank_e
        simpa [pow_two] using this
      have hcoe : resHom W ⟨e, hstabA heA⟩ =
          (r ⟨a, a.2⟩ : MulAut W) * ι * (r ⟨a, a.2⟩ : MulAut W)⁻¹ * ι⁻¹ := by
        have hprod : (⟨e, hstabA heA⟩ : stabSub W) =
            ⟨(a : MulAut T), hstabA a.2⟩ * ⟨φ, hstabφ⟩ *
              ⟨(a : MulAut T), hstabA a.2⟩⁻¹ * ⟨φ, hstabφ⟩⁻¹ := Subtype.ext rfl
        rw [hprod, map_mul, map_mul, map_mul, map_inv, map_inv]
        rfl
      have hfa : f (r ⟨a, a.2⟩) = r ⟨e, heA⟩ := by
        apply Subtype.ext
        show (r ⟨a, a.2⟩ : MulAut W) * (ι * (r ⟨a, a.2⟩ : MulAut W)⁻¹ * ι⁻¹) =
          resHom W ⟨e, hstabA heA⟩
        rw [hcoe]
        group
      rw [hfa, ← map_mul]
      rw [show (⟨e, heA⟩ : ↥A) * ⟨e, heA⟩ = 1 from Subtype.ext he2, map_one]
    have hι2 : ι * ι = 1 := by
      ext w
      exact hφsq w w.2
    have hιinv : ι⁻¹ = ι := inv_eq_of_mul_eq_one_right hι2
    have hβι : ∀ b : ↥(autSub A W),
        ((b : MulAut W) * ι * (b : MulAut W)⁻¹) * ι =
          ι * ((b : MulAut W) * ι * (b : MulAut W)⁻¹) := by
      intro b
      have hβ2 : ((b : MulAut W) * ι * (b : MulAut W)⁻¹) *
          ((b : MulAut W) * ι * (b : MulAut W)⁻¹) = 1 := by
        calc ((b : MulAut W) * ι * (b : MulAut W)⁻¹) *
              ((b : MulAut W) * ι * (b : MulAut W)⁻¹)
            = (b : MulAut W) * (ι * ι) * (b : MulAut W)⁻¹ := by group
          _ = 1 := by rw [hι2]; group
      have hf_eq : f b = ((b : MulAut W) * ι * (b : MulAut W)⁻¹) * ι := by
        show (b : MulAut W) * (ι * (b : MulAut W)⁻¹ * ι⁻¹) =
          ((b : MulAut W) * ι * (b : MulAut W)⁻¹) * ι
        rw [hιinv]
        group
      have hfsq_b : (f b : MulAut W) * (f b : MulAut W) = 1 := by
        simpa using congrArg Subtype.val (hfsq b)
      rw [hf_eq] at hfsq_b
      exact s16n9b_commute_of_sq hβ2 hι2 hfsq_b
    have hβcomm : ∀ b₁ b₂ : ↥(autSub A W),
        ((b₁ : MulAut W) * ι * (b₁ : MulAut W)⁻¹) *
            ((b₂ : MulAut W) * ι * (b₂ : MulAut W)⁻¹) =
          ((b₂ : MulAut W) * ι * (b₂ : MulAut W)⁻¹) *
            ((b₁ : MulAut W) * ι * (b₁ : MulAut W)⁻¹) := by
      intro b₁ b₂
      have h := hβι (b₂⁻¹ * b₁)
      have hconj := congrArg (fun z : MulAut W =>
        (b₂ : MulAut W) * z * (b₂ : MulAut W)⁻¹) h
      have hL : (b₂ : MulAut W) *
            (((b₂⁻¹ * b₁ : ↥(autSub A W)) : MulAut W) * ι *
              ((b₂⁻¹ * b₁ : ↥(autSub A W)) : MulAut W)⁻¹ * ι) *
            (b₂ : MulAut W)⁻¹ =
          ((b₁ : MulAut W) * ι * (b₁ : MulAut W)⁻¹) *
            ((b₂ : MulAut W) * ι * (b₂ : MulAut W)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hR : (b₂ : MulAut W) *
            (ι * (((b₂⁻¹ * b₁ : ↥(autSub A W)) : MulAut W) * ι *
              ((b₂⁻¹ * b₁ : ↥(autSub A W)) : MulAut W)⁻¹)) *
            (b₂ : MulAut W)⁻¹ =
          ((b₂ : MulAut W) * ι * (b₂ : MulAut W)⁻¹) *
            ((b₁ : MulAut W) * ι * (b₁ : MulAut W)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hL, hR] at hconj
      exact hconj
    have hfcomm : ∀ x ∈ Set.range f, ∀ y ∈ Set.range f, x * y = y * x := by
      rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩
      have h1 := hβcomm b₁ b₂
      have h2 := hβι b₁
      have h3 := hβι b₂
      have hf_eq : ∀ b : ↥(autSub A W),
          f b = ((b : MulAut W) * ι * (b : MulAut W)⁻¹) * ι := by
        intro b
        show (b : MulAut W) * (ι * (b : MulAut W)⁻¹ * ι⁻¹) =
          ((b : MulAut W) * ι * (b : MulAut W)⁻¹) * ι
        rw [hιinv]
        group
      apply Subtype.ext
      show (f b₁ : MulAut W) * (f b₂ : MulAut W) =
        (f b₂ : MulAut W) * (f b₁ : MulAut W)
      rw [hf_eq b₁, hf_eq b₂]
      exact s16n9b_mul_comm_mul (hβcomm b₁ b₂) (hβι b₁) (hβι b₂).symm rfl
    have hBcomm : IsMulCommutative ↥(autSub A W) := by
      have h := s16n9b_isMulCommutative_closure (S := Set.range f) hfcomm
      have hK : Subgroup.closure (Set.range f) = (⊤ : Subgroup ↥(autSub A W)) := by
        rw [← hKtop]
      rw [hK] at h
      refine ⟨⟨fun x y => ?_⟩⟩
      have hc := h.is_comm.comm ((Subgroup.topEquiv).symm x)
        ((Subgroup.topEquiv).symm y)
      calc x * y = (Subgroup.topEquiv) ((Subgroup.topEquiv).symm x) *
            (Subgroup.topEquiv) ((Subgroup.topEquiv).symm y) := by
            rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        _ = (Subgroup.topEquiv) ((Subgroup.topEquiv).symm x *
              (Subgroup.topEquiv).symm y) := (map_mul _ _ _).symm
        _ = (Subgroup.topEquiv) ((Subgroup.topEquiv).symm y *
              (Subgroup.topEquiv).symm x) := by rw [hc]
        _ = (Subgroup.topEquiv) ((Subgroup.topEquiv).symm y) *
              (Subgroup.topEquiv) ((Subgroup.topEquiv).symm x) := map_mul _ _ _
        _ = y * x := by rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hBnoncomm hBcomm


private theorem s16n9b_rank_of_summands {T : Type} [CommGroup T] [Finite T]
    (hexp : ∀ t : T, t ^ 2 = 1)
    {A : Subgroup (MulAut T)} {W : Subgroup T}
    {N : Subgroup (MulAut T) → Subgroup T → Subgroup T → Prop}
    (hWdef : W = commSub ⊤ A)
    (hSum : SumOfNat N A W ⊥ 2)
    (hAs : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A)
    (hIinv : ∀ I : Subgroup T, N A I ⊥ → ∀ a ∈ A, ∀ u ∈ I, a u ∈ I)
    (hIfaith : ∀ I : Subgroup T, N A I ⊥ → ∀ a ∈ A, (∀ u ∈ I, a u = u) → a = 1)
    (hIfix : ∀ I : Subgroup T, N A I ⊥ → fixV A ⊓ I = ⊥)
    (hrkI : ∀ I : Subgroup T, N A I ⊥ → 3 ≤ rk ↥I) :
    3 < rk ↥W ∧ ∀ φ : MulAut T, (∃ k : ℕ, orderOf φ = 2 ^ k) →
      A.map (MulAut.conj φ).toMonoidHom = A →
      (∀ w ∈ W, φ w = w) ∨ 2 ≤ rk ↥(commSub W (Subgroup.zpowers φ)) := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := hSum
  have h01 : I 0 ⊓ I 1 = ⊥ := by
    have h0 := hind 0
    have hle : I 1 ≤ ⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_sup_of_le_right (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
    exact le_bot_iff.mp (le_trans (inf_le_inf_left _ hle) h0)
  have hW_eq : I 0 ⊔ I 1 = W := by
    rw [← hsup, bot_sup_eq]
    refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
    fin_cases i <;> simp
  have hinv : ∀ i, ∀ a ∈ A, ∀ u ∈ I i, a u ∈ I i := fun i => hIinv (I i) (hnat i)
  have hfaith : ∀ i, ∀ a ∈ A, (∀ u ∈ I i, a u = u) → a = 1 := fun i => hIfaith (I i) (hnat i)
  have hfix : ∀ i, fixV A ⊓ I i = ⊥ := fun i => hIfix (I i) (hnat i)
  have hrk : ∀ i, 3 ≤ rk ↥(I i) := fun i => hrkI (I i) (hnat i)
  have hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
    rw [hWdef]
    intro a ha
    exact commSub_inv_H A ⊤ a ha
  have hWfaith : ∀ a ∈ A, (∀ w ∈ W, a w = w) → a = 1 := by
    intro a ha hfixW
    refine hfaith 0 a ha fun u hu => hfixW u ?_
    rw [← hW_eq]
    exact Subgroup.mem_sup_left hu
  have hM3 : ∀ v ∈ W, (∀ a ∈ A, a v = v) → v = 1 := by
    intro v hv hfixv
    have hv' : v ∈ I 0 ⊔ I 1 := by rw [hW_eq]; exact hv
    obtain ⟨x0, hx0, x1, hx1, rfl⟩ := Subgroup.mem_sup.1 hv'
    have hx0fix : x0 ∈ fixV A := by
      rw [mem_fixV]
      intro a ha
      have h1 : a (x0 * x1) = x0 * x1 := hfixv a ha
      rw [map_mul] at h1
      have heq : (a x0)⁻¹ * x0 = a x1 * x1⁻¹ := by
        calc (a x0)⁻¹ * x0
            = (a x0)⁻¹ * (x0 * x1) * x1⁻¹ := by group
          _ = (a x0)⁻¹ * (a x0 * a x1) * x1⁻¹ := by rw [← h1]
          _ = a x1 * x1⁻¹ := by group
      have hmem : (a x0)⁻¹ * x0 ∈ I 0 ⊓ I 1 := by
        constructor
        · exact (I 0).mul_mem ((I 0).inv_mem (hinv 0 a ha x0 hx0)) hx0
        · rw [heq]
          exact (I 1).mul_mem (hinv 1 a ha x1 hx1) ((I 1).inv_mem hx1)
      have hz : (a x0)⁻¹ * x0 = 1 := by
        rw [h01] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact inv_mul_eq_one.mp hz
    have hx1fix : x1 ∈ fixV A := by
      rw [mem_fixV]
      intro a ha
      have h1 : a (x0 * x1) = x0 * x1 := hfixv a ha
      rw [map_mul] at h1
      have heq : (a x1)⁻¹ * x1 = a x0 * x0⁻¹ := by
        have h2 : a x0 * x0⁻¹ = x1 * (a x1)⁻¹ := by
          calc a x0 * x0⁻¹ = (a x0 * a x1) * (a x1)⁻¹ * x0⁻¹ := by group
            _ = (x0 * x1) * (a x1)⁻¹ * x0⁻¹ := by rw [h1]
            _ = (x1 * (a x1)⁻¹) * (x0 * x0⁻¹) := by ac_rfl
            _ = x1 * (a x1)⁻¹ := by rw [mul_inv_cancel, mul_one]
        calc (a x1)⁻¹ * x1 = x1 * (a x1)⁻¹ := by rw [mul_comm]
          _ = a x0 * x0⁻¹ := h2.symm
      have hmem : (a x1)⁻¹ * x1 ∈ I 0 ⊓ I 1 := by
        constructor
        · rw [heq]
          exact (I 0).mul_mem (hinv 0 a ha x0 hx0) ((I 0).inv_mem hx0)
        · exact (I 1).mul_mem ((I 1).inv_mem (hinv 1 a ha x1 hx1)) hx1
      have hz : (a x1)⁻¹ * x1 = 1 := by
        rw [h01] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact inv_mul_eq_one.mp hz
    have hx0bot : x0 ∈ fixV A ⊓ I 0 := ⟨hx0fix, hx0⟩
    have hx1bot : x1 ∈ fixV A ⊓ I 1 := ⟨hx1fix, hx1⟩
    rw [hfix 0] at hx0bot
    rw [hfix 1] at hx1bot
    rw [Subgroup.mem_bot] at hx0bot hx1bot
    rw [hx0bot, hx1bot, one_mul]
  have hstep3 : ∀ e ∈ A, rk ↥(commSub W (Subgroup.zpowers e)) ≤ 2 → e ^ 2 = 1 :=
    fun e he => s16n9b_small_rank_sq hexp hW_eq h01 hinv hfaith hWfaith he
  have hrkW : 3 < rk ↥W := by
    have h := rk_sup_add_rk_inf (I 0) (I 1)
    rw [h01, rk_bot, hW_eq] at h
    have h0 := hrk 0
    have h1 := hrk 1
    omega
  refine ⟨hrkW, fun φ _ hφA => ?_⟩
  by_cases hcent : ∀ w ∈ W, φ w = w
  · exact Or.inl hcent
  · right
    by_contra hlt
    have hrkφ : rk ↥(commSub W (Subgroup.zpowers φ)) ≤ 1 := by omega
    have hWmap : W.map φ.toMonoidHom = W := by
      rw [hWdef, ← s15_Infra_commSub_top_map_conj A φ, hφA]
    have hstab : φ ∈ stabSub W := s16n9b_mem_stabSub_of_map_eq hWmap
    have hφW : ∀ w ∈ W, φ w ∈ W := fun w hw => (mem_stabSub.1 hstab w).2 hw
    exact s16n9b_no_small_rank hexp hAW hAs hAn hWfaith hM3 hstep3 hφA hφW hrkφ hcent

private theorem s16n9b_rank_of_alt {T : Type} [CommGroup T] [Finite T]
    (hexp : ∀ t : T, t ^ 2 = 1) {A : Subgroup (MulAut T)} {W : Subgroup T}
    (hWdef : W = commSub ⊤ A) (hAlt : UC22.IsAlt ↥A 5)
    (hSum : SumOfNat (fun H U Z => AlternatingNatural H U Z 5) A W ⊥ 2) :
    3 < rk ↥W ∧ ∀ φ : MulAut T, (∃ k : ℕ, orderOf φ = 2 ^ k) →
      A.map (MulAut.conj φ).toMonoidHom = A →
      (∀ w ∈ W, φ w = w) ∨ 2 ≤ rk ↥(commSub W (Subgroup.zpowers φ)) := by
  have hsimple : IsSimpleGroup ↥A := by
    obtain ⟨e⟩ := hAlt
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    exact MulEquiv.isSimpleGroup e
  have hcard : Nat.card ↥A = 60 := by
    obtain ⟨e⟩ := hAlt
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hnoncomm : ¬ IsMulCommutative ↥A :=
    s16n9b_not_comm_of_simple hsimple (by rw [hcard]; norm_num)
  refine s16n9b_rank_of_summands (hexp := hexp) hWdef hSum hsimple hnoncomm ?_ ?_ ?_ ?_
  · intro I hI a ha u hu
    obtain ⟨π, hπ⟩ := hI
    exact hπ.2.2.2.1 ⟨a, ha⟩ u hu
  · intro I hI a ha hfix
    obtain ⟨π, hπ⟩ := hI
    have := s16n9b_fix_pointwise_eq_one (U := I) (a := ⟨a, ha⟩)
      (FFC.altDn_faithful (by norm_num : 5 ≤ 5)) hπ hfix
    exact congrArg Subtype.val this
  · intro I hI
    exact s16n9b_fixV_altDn_five hI
  · intro I hI
    have hc := s16c1610_card_alternatingNatural_odd (n := 5) (by norm_num) hI
    have hr := s16c1610_rk_of_card_two_pow hc
    omega

private theorem s16n9b_rank_of_l3 {T : Type} [CommGroup T] [Finite T]
    (hexp : ∀ t : T, t ^ 2 = 1) {A : Subgroup (MulAut T)} {W : Subgroup T}
    (hWdef : W = commSub ⊤ A) (hL3 : IsL3 ↥A 1)
    (hSum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) A W ⊥ 2) :
    3 < rk ↥W ∧ ∀ φ : MulAut T, (∃ k : ℕ, orderOf φ = 2 ^ k) →
      A.map (MulAut.conj φ).toMonoidHom = A →
      (∀ w ∈ W, φ w = w) ∨ 2 ≤ rk ↥(commSub W (Subgroup.zpowers φ)) := by
  have hSum' := hSum
  obtain ⟨I, -, -, -, hnat⟩ := hSum
  have hsimple : IsSimpleGroup ↥A :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
  obtain ⟨K, hK, hfin, hcardK, π, hπ⟩ := hnat 0
  have hK2 : Nat.card K = 2 := by simpa using hcardK
  have hπinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have he : ↥(StatedSL 3 K) ≃* ↥A := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  have hcardA : Nat.card ↥A = 168 := by
    rw [← Nat.card_congr he.toEquiv]
    exact CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hK2
  have hnoncomm : ¬ IsMulCommutative ↥A :=
    s16n9b_not_comm_of_simple hsimple (by rw [hcardA]; norm_num)
  refine s16n9b_rank_of_summands (hexp := hexp) hWdef hSum' hsimple hnoncomm ?_ ?_ ?_ ?_
  · intro I hI a ha u hu
    obtain ⟨K, hK, hfin, hc, π, hπ⟩ := hI
    exact hπ.2.2.2.1 ⟨a, ha⟩ u hu
  · intro I hI a ha hfix
    obtain ⟨K, hK, hfin, hc, π, hπ⟩ := hI
    have := s16n9b_fix_pointwise_eq_one (U := I) (a := ⟨a, ha⟩)
      (FFModel.nat_faithful _) hπ hfix
    exact congrArg Subtype.val this
  · intro I hI
    obtain ⟨K, hK, hfin, hc, π, hπ⟩ := hI
    exact FFC.fixV_inf_eq_bot_of_nat (d := 3) (by norm_num) hπ
  · intro I hI
    have := s16c1610_rk_binaryNaturalSL (n := 3) (a := 1) hI
    omega

theorem s16n9b_case6_rank (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h6 : Case168_6 D V₀ V hV L) :
    3 < rk ↥(wTil V₀ V hV L) ∧
      ∀ φ ∈ Mbar D.M V₀ V hV, (∃ a : ℕ, orderOf φ = 2 ^ a) →
        (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom = lBar V₀ V hV L →
        (∀ w ∈ wTil V₀ V hV L, φ w = w) ∨
          2 ≤ rk ↥(commSub (wTil V₀ V hV L) (Subgroup.zpowers φ)) := by
  have hexp : ∀ t : Vtil V₀ V hV, t ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  rcases h6.2.1 with ⟨hAlt, hSum⟩ | ⟨hL3, hSum⟩
  · obtain ⟨hi, hii⟩ := s16n9b_rank_of_alt (T := Vtil V₀ V hV) (A := lBar V₀ V hV L)
      (W := wTil V₀ V hV L) hexp rfl hAlt hSum
    exact ⟨hi, fun φ _ h2 h3 => hii φ h2 h3⟩
  · obtain ⟨hi, hii⟩ := s16n9b_rank_of_l3 (T := Vtil V₀ V hV) (A := lBar V₀ V hV L)
      (W := wTil V₀ V hV L) hexp rfl hL3 hSum
    exact ⟨hi, fun φ _ h2 h3 => hii φ h2 h3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
