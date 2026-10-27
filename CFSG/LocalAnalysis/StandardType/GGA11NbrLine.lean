module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private lemma a11nl_fPow_mem {G : Type} [Group G] (f : Fin 4 → G) (w : Fin 4 → ZMod 7) :
    fPow f w ∈ Subgroup.closure (Set.range f) := by
  unfold fPow
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self 0)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self 1)) _))
    (Subgroup.pow_mem _ (Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self 2)) _))
    (Subgroup.pow_mem _ (Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self 3)) _)

private lemma a11nl_fPow_zero {G : Type} [Group G] (f : Fin 4 → G) : fPow f 0 = 1 := by
  unfold fPow
  simp

private lemma a11nl_fPow_add {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, f i * f j = f j * f i) (hford : ∀ i, orderOf (f i) = 7)
    (u v : Fin 4 → ZMod 7) : fPow f (u + v) = fPow f u * fPow f v := by
  let Bs := Subgroup.closure (Set.range f)
  letI : CommGroup ↥Bs := Subgroup.closureCommGroupOfComm (k := Set.range f) (by
    intro a ha b hb _
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    exact hfcomm i j)
  have hFG : ∀ w : Fin 4 → ZMod 7,
      ((∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ (w i).val : ↥Bs) : G) = fPow f w := by
    intro w
    rw [Fin.prod_univ_four]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_pow]
    rfl
  have hfinal : (∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ ((u + v) i).val : ↥Bs) =
      (∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ (u i).val) *
      (∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ (v i).val) := by
    rw [← Finset.prod_mul_distrib (s := Finset.univ)]
    apply Finset.prod_congr rfl
    intro i _
    rw [Pi.add_apply, ← pow_add]
    rw [pow_eq_pow_iff_modEq, Subgroup.orderOf_mk, hford i, ← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  calc fPow f (u + v) = ((∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ ((u + v) i).val : ↥Bs) : G) := (hFG (u + v)).symm
    _ = ((∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ (u i).val) * (∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ (v i).val) : ↥Bs) := by rw [hfinal]
    _ = ((∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ (u i).val : ↥Bs) : G) * ((∏ i : Fin 4, (⟨f i, Subgroup.subset_closure (k := Set.range f) (Set.mem_range_self i)⟩ : ↥Bs) ^ (v i).val : ↥Bs) : G) := Subgroup.coe_mul ..
    _ = fPow f u * fPow f v := by rw [hFG u, hFG v]

private noncomputable def a11nl_fPowHom {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, f i * f j = f j * f i) (hford : ∀ i, orderOf (f i) = 7) :
    Multiplicative (Fin 4 → ZMod 7) →* G where
  toFun := fun v => fPow f (Multiplicative.toAdd v)
  map_one' := a11nl_fPow_zero f
  map_mul' := fun u v => a11nl_fPow_add f hfcomm hford (Multiplicative.toAdd u) (Multiplicative.toAdd v)

private lemma a11nl_fPowHom_range {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, f i * f j = f j * f i) (hford : ∀ i, orderOf (f i) = 7) :
    (a11nl_fPowHom f hfcomm hford).range = Subgroup.closure (Set.range f) := by
  apply le_antisymm
  · rintro x ⟨w, rfl⟩
    exact a11nl_fPow_mem f (Multiplicative.toAdd w)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨i, rfl⟩
    refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
    show fPow f (Pi.single i 1) = f i
    fin_cases i <;> simp [fPow, Pi.single_eq_same, Pi.single_eq_of_ne, ZMod.val_zero,
      (show ZMod.val (1 : ZMod 7) = 1 from rfl)]

private lemma a11nl_fPowHom_injective {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, f i * f j = f j * f i) (hford : ∀ i, orderOf (f i) = 7)
    (hcard : Nat.card ↥(Subgroup.closure (Set.range f)) = 7 ^ 4) :
    Function.Injective (a11nl_fPowHom f hfcomm hford) := by
  let φ := a11nl_fPowHom f hfcomm hford
  have hrange := a11nl_fPowHom_range f hfcomm hford
  have hker : Nat.card ↥φ.ker = 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := Multiplicative (Fin 4 → ZMod 7)) φ.ker
    have hdom : Nat.card (Multiplicative (Fin 4 → ZMod 7)) = 7 ^ 4 := by
      change Nat.card (Fin 4 → ZMod 7) = 7 ^ 4
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rw [hdom] at h1
    have h2 : Nat.card (Multiplicative (Fin 4 → ZMod 7) ⧸ φ.ker) = 7 ^ 4 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      rw [hrange, hcard]
    rw [h2] at h1
    have hpos : 0 < 7 ^ 4 := by norm_num
    have := Nat.eq_of_mul_eq_mul_left hpos (show 7 ^ 4 * 1 = 7 ^ 4 * Nat.card ↥φ.ker by rw [mul_one, h1.symm])
    exact this.symm
  have hbot : φ.ker = ⊥ := Subgroup.card_eq_one.mp hker
  exact (MonoidHom.ker_eq_bot_iff φ).mp hbot

private lemma a11nl_fPow_zsmul {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, f i * f j = f j * f i) (hford : ∀ i, orderOf (f i) = 7)
    (m : ℤ) (v : Fin 4 → ZMod 7) : fPow f (m • v) = (fPow f v) ^ m := by
  have h := map_zpow (a11nl_fPowHom f hfcomm hford) (Multiplicative.ofAdd v) m
  simpa [a11nl_fPowHom] using h

private lemma a11nl_fPow_nsmul {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, f i * f j = f j * f i) (hford : ∀ i, orderOf (f i) = 7)
    (k : ℕ) (v : Fin 4 → ZMod 7) : fPow f (k • v) = (fPow f v) ^ k := by
  induction k with
  | zero => simp [a11nl_fPow_zero]
  | succ k ih => rw [succ_nsmul, a11nl_fPow_add f hfcomm hford, ih, pow_succ]

private lemma a11nl_fPow_one_vec {G : Type} [Group G] (f : Fin 4 → G) :
    fPow f (fun _ : Fin 4 => (1 : ZMod 7)) = f 0 * f 1 * f 2 * f 3 := by
  unfold fPow
  simp [(show ZMod.val (1 : ZMod 7) = 1 from rfl)]

private lemma a11nl_fPow_single {G : Type} [Group G] (f : Fin 4 → G) :
    fPow f (Pi.single 3 1) = f 3 := by
  unfold fPow
  simp [Pi.single_eq_same, Pi.single_eq_of_ne, ZMod.val_zero,
    (show ZMod.val (1 : ZMod 7) = 1 from rfl)]

private lemma a11nl_fPow_ell {G : Type} [Group G] (f : Fin 4 → G) (c : ZMod 7) :
    fPow f (fun i : Fin 4 => if i = 3 then c else 1) = ell f c := by
  unfold fPow ell
  simp [ZMod.val_zero, (show ZMod.val (1 : ZMod 7) = 1 from rfl)]

private lemma a11nl_mem_closure_pair_of_commute {G : Type} [Group G] {x y z : G} (hxy : Commute x y)
    (hz : z ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ m n : ℤ, x ^ m * y ^ n = z := by
  revert hz
  refine Subgroup.closure_induction ?hgen ?hone ?hmul ?hinv
  · intro z hz
    rcases hz with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · exact ⟨0, 0, by simp⟩
  · intro a b ha hb iha ihb
    obtain ⟨m, n, rfl⟩ := iha
    obtain ⟨m', n', rfl⟩ := ihb
    refine ⟨m + m', n + n', ?_⟩
    have hcomm : y ^ n * x ^ m' = x ^ m' * y ^ n := (hxy.symm.zpow_zpow n m').eq
    rw [_root_.zpow_add, _root_.zpow_add]
    calc (x ^ m * x ^ m') * (y ^ n * y ^ n')
        = x ^ m * (x ^ m' * y ^ n) * y ^ n' := by group
      _ = x ^ m * (y ^ n * x ^ m') * y ^ n' := by rw [← hcomm]
      _ = (x ^ m * y ^ n) * (x ^ m' * y ^ n') := by group
  · intro a ha iha
    obtain ⟨m, n, rfl⟩ := iha
    refine ⟨-m, -n, ?_⟩
    have hcomm : y ^ (-n) * x ^ (-m) = x ^ (-m) * y ^ (-n) := (hxy.symm.zpow_zpow (-n) (-m)).eq
    rw [_root_.mul_inv_rev, ← _root_.zpow_neg, ← _root_.zpow_neg]
    exact hcomm.symm

private lemma a11nl_zpowers_eq_of_mem {G : Type} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    {y z : G} (hpow : y ^ p = 1) (hz : z ≠ 1) (hzy : z ∈ Subgroup.zpowers y) :
    Subgroup.zpowers z = Subgroup.zpowers y := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hy_ne : y ≠ 1 := by
    intro hy
    have : z ∈ (⊥ : Subgroup G) := by simpa [hy] using hzy
    exact hz (Subgroup.mem_bot.mp this)
  have hordy : orderOf y = p := orderOf_eq_prime hpow hy_ne
  have hordz : orderOf z = p := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzy
    have hzp : z ^ p = 1 := by
      rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hpow, _root_.one_zpow]
    exact orderOf_eq_prime hzp hz
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hzy) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hordy, hordz]

private lemma a11nl_f3_not_mem_zpowers {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, f i * f j = f j * f i) (hford : ∀ i, orderOf (f i) = 7)
    (hcard : Nat.card ↥(Subgroup.closure (Set.range f)) = 7 ^ 4) :
    f 3 ∉ Subgroup.zpowers (f 0 * f 1 * f 2 * f 3) := by
  intro hmem
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨m, hm⟩ := hmem
  have hx1 : f 0 * f 1 * f 2 * f 3 = fPow f (fun _ : Fin 4 => 1) := by
    unfold fPow
    simp [(show ZMod.val (1 : ZMod 7) = 1 from rfl)]
  have he3 : f 3 = fPow f (Pi.single 3 1) := by
    unfold fPow
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, ZMod.val_zero, (show ZMod.val (1 : ZMod 7) = 1 from rfl)]
  have heq : Multiplicative.ofAdd (Pi.single 3 1) = (Multiplicative.ofAdd (fun _ : Fin 4 => (1 : ZMod 7)))^m := by
    apply a11nl_fPowHom_injective f hfcomm hford hcard
    rw [map_zpow]
    change fPow f (Pi.single 3 1) = (fPow f (fun _ : Fin 4 => 1))^m
    rw [← he3, ← hx1]
    exact hm.symm
  have hfun : Pi.single 3 1 = m • (fun _ : Fin 4 => (1 : ZMod 7)) := by
    have := congrArg Multiplicative.toAdd heq
    simpa using this
  have h0 := congrFun hfun 0
  have h3 := congrFun hfun 3
  rw [Pi.single_eq_of_ne (show (0 : Fin 4) ≠ 3 by decide), Pi.smul_apply] at h0
  rw [Pi.single_eq_same, Pi.smul_apply] at h3
  exact (by decide : (1 : ZMod 7) ≠ 0) (h3.trans h0.symm)

theorem a11NbrLineInput_holds : A11NbrLineInput := by
  intro G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨hrest, hcfg, hframe, hextra, hcoh, hrho⟩ := hctx
  obtain ⟨hglue, hφK, hnbK, hBs, hx, hy, hD, hnL, hJK, hJ9, hL⟩ := hframe
  obtain ⟨hfinj, hfcast, hfcomm, hford, hfcard, hn3, hnconj, hcomp⟩ := hglue
  have hD' : D = Subgroup.closure ({x, y'} : Set G) := hnb.2.1
  have hx_eq : x = fPow f (fun _ : Fin 4 => (1 : ZMod 7)) := hx.trans (a11nl_fPow_one_vec f).symm
  have hf3_eq : f 3 = fPow f (Pi.single 3 1) := (a11nl_fPow_single f).symm
  have hf3_not : f 3 ∉ Subgroup.zpowers x := by
    rw [hx]
    exact a11nl_f3_not_mem_zpowers f hfcomm hford hfcard
  have hy'_not : y' ∉ Subgroup.zpowers x := by
    intro hyx
    have hle : Subgroup.closure ({x, y'} : Set G) ≤ Subgroup.zpowers x := by
      refine (Subgroup.closure_le _).mpr ?_
      intro z hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_zpowers x
      · rw [hz]; exact hyx
    have hf3mem : f 3 ∈ Subgroup.zpowers x := by
      have hf3D : f 3 ∈ D := by rw [hD]; exact Subgroup.subset_closure (by simp)
      rw [hD'] at hf3D
      exact hle hf3D
    exact hf3_not hf3mem
  have hy'_ne : y' ≠ 1 := by
    intro hy1
    have hDx : D = Subgroup.zpowers x := by
      rw [hD', hy1]
      have hset : ({x, 1} : Set G) = {x} ∪ {1} := by
        ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure x, ← Subgroup.zpowers_eq_closure 1,
        Subgroup.zpowers_eq_bot.mpr rfl, sup_bot_eq]
    have hf3mem : f 3 ∈ Subgroup.zpowers x := by
      have hf3D : f 3 ∈ D := by rw [hD]; exact Subgroup.subset_closure (by simp)
      rwa [hDx] at hf3D
    exact hf3_not hf3mem
  have hcomm_xf3 : Commute x (f 3) := by
    rw [hx]
    exact Commute.mul_left (Commute.mul_left (Commute.mul_left (hfcomm 0 3) (hfcomm 1 3)) (hfcomm 2 3)) (Commute.refl (f 3))
  have hy'D : y' ∈ D := by
    rw [hD']
    exact Subgroup.subset_closure (by simp)
  have hy'_closure : y' ∈ Subgroup.closure ({x, f 3} : Set G) := by
    rwa [← hD]
  obtain ⟨m, n, hmn⟩ := a11nl_mem_closure_pair_of_commute hcomm_xf3 hy'_closure
  have hx_m : x ^ m = fPow f (m • (fun _ : Fin 4 => (1 : ZMod 7))) := by
    rw [hx_eq, ← a11nl_fPow_zsmul f hfcomm hford m (fun _ : Fin 4 => (1 : ZMod 7))]
  have hf3_n : f 3 ^ n = fPow f (n • Pi.single 3 1) := by
    rw [hf3_eq, ← a11nl_fPow_zsmul f hfcomm hford n (Pi.single 3 1)]
  have hy'_eq : y' = fPow f (m • (fun _ : Fin 4 => (1 : ZMod 7)) + n • Pi.single 3 1) := by
    rw [← hmn, hx_m, hf3_n, a11nl_fPow_add f hfcomm hford]
  by_cases ha : (m : ZMod 7) = 0
  · left
    have hw_eq : m • (fun _ : Fin 4 => (1 : ZMod 7)) + n • Pi.single 3 1 = n • Pi.single 3 1 := by
      funext i
      fin_cases i <;> simp [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, ha]
    have hy'_f3 : y' = f 3 ^ n := by
      rw [hy'_eq, hw_eq, a11nl_fPow_zsmul f hfcomm hford n (Pi.single 3 1), a11nl_fPow_single f]
    have hmem : y' ∈ Subgroup.zpowers (f 3) := by
      rw [hy'_f3]
      exact Subgroup.zpow_mem (Subgroup.zpowers (f 3)) (Subgroup.mem_zpowers (f 3)) n
    have hf3pow : (f 3) ^ 7 = 1 := by
      rw [← hford 3]
      exact pow_orderOf_eq_one (f 3)
    exact a11nl_zpowers_eq_of_mem Nat.prime_seven hf3pow hy'_ne hmem
  · right
    let a : ZMod 7 := (m : ZMod 7)
    let b : ZMod 7 := (n : ZMod 7)
    let c : ZMod 7 := 1 + b * a⁻¹
    let u : Fin 4 → ZMod 7 := fun i => if i = 3 then c else 1
    have hac : a * c = a + b := by
      show a * (1 + b * a⁻¹) = a + b
      rw [mul_add, mul_one]
      rw [← mul_assoc, mul_comm a b, mul_assoc, mul_inv_cancel₀ (a := a) (by simpa [a] using ha), mul_one]
    have hw_eq : m • (fun _ : Fin 4 => (1 : ZMod 7)) + n • Pi.single 3 1 = (a.val) • u := by
      funext i
      fin_cases i <;> simp [u, a, b, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, nsmul_eq_mul, hac]
    have hy'_ell : y' = (ell f c) ^ (a.val) := by
      rw [hy'_eq, hw_eq, a11nl_fPow_nsmul f hfcomm hford a.val u, a11nl_fPow_ell f c]
    have hmem : y' ∈ Subgroup.zpowers (ell f c) := by
      rw [hy'_ell]
      exact Subgroup.pow_mem (Subgroup.zpowers (ell f c)) (Subgroup.mem_zpowers (ell f c)) a.val
    have hellpow : (ell f c) ^ 7 = 1 := by
      rw [← a11nl_fPow_ell f c, ← a11nl_fPow_nsmul f hfcomm hford 7 u]
      have h70 : (7 : ZMod 7) = 0 := ZMod.natCast_self 7
      have h7u : (7 : ℕ) • u = 0 := by
        funext i
        fin_cases i <;> simp [u, nsmul_eq_mul, h70]
      rw [h7u, a11nl_fPow_zero]
    have hc : c ≠ 1 := by
      intro hc1
      apply hy'_not
      have hell1 : ell f c = x := by
        rw [← a11nl_fPow_ell f c, hc1]
        have hu : (fun i : Fin 4 => if i = 3 then (1 : ZMod 7) else 1) = (fun _ : Fin 4 => 1) := by
          funext i; by_cases hi : i = 3 <;> simp [hi]
        rw [hu, a11nl_fPow_one_vec, hx]
      rw [hy'_ell, hell1]
      exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) a.val
    exact ⟨c, hc, a11nl_zpowers_eq_of_mem Nat.prime_seven hellpow hy'_ne hmem⟩

end CFSG.StandardType.A11
end
