module

public import CFSG.Walter.W67.JR.ThreeMultE
public import CFSG.Walter.W67.JR.ThreeMultStep
public import CFSG.Walter.W67.JR.Ree
public import CFSG.Walter.ReeOrder.WardLocal.Two
public import CFSG.Walter.ReeOrder.JTFinal

public section

namespace CFSG.Walter.W67

namespace ThreeMult

open scoped commutatorElement Pointwise

variable {E L : Type*} [Group E] [Group L]

theorem comap_mem_normalizer {π : E →* L} {P : Subgroup L} {a : L}
    (ha : a ∈ Subgroup.normalizer (P : Set L)) {g : E} (hga : π g = a) :
    g ∈ Subgroup.normalizer ((P.comap π : Subgroup E) : Set E) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_comap, map_mul, map_inv, hga]
  exact (Subgroup.mem_normalizer_iff.mp ha (π x))

theorem eq_bot_of_layers [Finite E] [Finite L] {π : E →* L} (hπ : Function.Surjective π)
    {Z : Subgroup E} (hker : π.ker = Z) (hZc : Z ≤ Subgroup.center E) (hZ3 : IsPGroup 3 Z)
    (hperf : commutator E = ⊤) (P : Sylow 3 L) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card (P : Subgroup L) = (3 ^ n) ^ 3)
    (hcard₁ : Nat.card (⁅(P : Subgroup L), (P : Subgroup L)⁆ : Subgroup L) = (3 ^ n) ^ 2)
    (hexp : ∀ y ∈ (P : Subgroup L), y ^ 3 ∈ ⁅(P : Subgroup L), (P : Subgroup L)⁆)
    (hclass : (P : Subgroup L).lowerCentralSeries 3 = ⊥)
    {a : L} (ha : a ∈ Subgroup.normalizer ((P : Subgroup L) : Set L)) (hao : orderOf a = 3 ^ n - 1)
    (hodd : ∀ w ∈ Subgroup.zpowers a, w ≠ 1 → Odd (orderOf w) →
      ∀ x ∈ (P : Subgroup L), w * x * w⁻¹ = x → x = 1)
    (hinv : ∀ w ∈ Subgroup.zpowers a, orderOf w = 2 →
      ∀ x ∈ (P : Subgroup L), w * x * w⁻¹ = x → x ∈ ⁅(P : Subgroup L), (P : Subgroup L)⁆) :
    Z = ⊥ := by
  classical
  set Pg : Subgroup L := (P : Subgroup L) with hPg
  set Pt : Subgroup E := Pg.comap π with hPt
  have hZPt : Z ≤ Pt := by
    intro z hz
    change π z ∈ Pg
    rw [show π z = 1 by rw [← MonoidHom.mem_ker, hker]; exact hz]
    exact Pg.one_mem
  have hidx : ¬ 3 ∣ Pt.index := by
    rw [hPt, Subgroup.index_comap_of_surjective _ hπ]
    exact P.not_dvd_index
  have hZ1 : Z ≤ γ Pt 1 := le_commutator_of_perfect hZc hZ3 hZPt hidx hperf
  have hker1 : π.ker ≤ γ Pt 1 := hker ▸ hZ1
  have hγ3 : γ Pt 3 ≤ Z := by
    intro x hx
    have h1 : π x ∈ (γ Pt 3).map π := ⟨x, hx, rfl⟩
    rw [map_γ hπ, hclass, Subgroup.mem_bot] at h1
    rw [← hker]
    exact h1
  have hγ4 : γ Pt 4 = ⊥ := by
    rw [eq_bot_iff, γ_succ]
    calc ⁅γ Pt 3, Pt⁆ ≤ ⁅Z, Pt⁆ := Subgroup.commutator_mono hγ3 le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (hZc.trans (Subgroup.center_le_centralizer _))
  obtain ⟨g, hga⟩ := hπ a
  have hgN : g ∈ Subgroup.normalizer ((Pt : Subgroup E) : Set E) := comap_mem_normalizer ha hga
  have hq3 : 27 ≤ 3 ^ n := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hgq : g ^ (3 ^ n - 1) ∈ Subgroup.center E := by
    apply hZc
    rw [← hker, MonoidHom.mem_ker, map_pow, hga, ← hao, pow_orderOf_eq_one]
  have hθ : ∀ (i : ℕ) (m : LayerQ Pt i), (layerConj g hgN i)^[3 ^ n - 1] m = m := by
    intro i m
    rw [← layerConj_pow hgN i]
    exact layerConj_of_mem_center _ hgq i m
  have ha3 : ¬ 3 ∣ orderOf a := by
    rw [hao]
    intro h
    have h1 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
    have h2 := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self (by omega)] at h2
    omega
  have hfree : ∀ j, 0 < j → j < 3 ^ n - 1 → ∀ v : LayerQ Pt 0,
      (layerConj g hgN 0)^[j] v = v → v = 1 := by
    intro j hj0 hj v hv
    have haj : a ^ j ≠ 1 := by
      intro h
      have := orderOf_le_of_pow_eq_one hj0 h
      omega
    exact layerConj_free hπ hker hZ3 P.isPGroup' hZ1 ha3 hodd hinv hgN hga haj v hv
  have hexpV : ∀ v : LayerQ Pt 0, v ^ 3 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
    change lmk Pt x ^ 3 = 1
    rw [← QuotientGroup.mk_pow, ← lmk, lmk_eq_one_iff]
    refine mem_γ_of_map_mem hπ hker1 ?_
    rw [Subgroup.coe_pow, map_pow]
    exact hexp _ (γ_le Pt 0 x.2)
  have hcardV : Nat.card (LayerQ Pt 0) = 3 ^ n := by
    have h0 := card_eq_card_map_mul_card_inf_ker π (γ Pt 0)
    have h1 := card_eq_card_map_mul_card_inf_ker π (γ Pt 1)
    rw [map_γ hπ] at h0 h1
    have hk0 : γ Pt 0 ⊓ π.ker = Z := by rw [hker]; exact inf_eq_right.mpr hZPt
    have hk1 : γ Pt 1 ⊓ π.ker = Z := by rw [hker]; exact inf_eq_right.mpr hZ1
    rw [hk0] at h0
    rw [hk1] at h1
    have hl0 : Pg.lowerCentralSeries 0 = Pg := rfl
    have hl1 : Pg.lowerCentralSeries 1 = ⁅Pg, Pg⁆ := rfl
    rw [hl0, hcard] at h0
    rw [hl1, hcard₁] at h1
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup ((γ Pt 1).subgroupOf (γ Pt 0))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (γ_succ_le Pt 0)).toEquiv, h0, h1] at hq
    have hZpos : 0 < (3 ^ n) ^ 2 * Nat.card Z := Nat.mul_pos (by positivity) Nat.card_pos
    have h2 : 3 ^ n * ((3 ^ n) ^ 2 * Nat.card Z) =
        Nat.card (LayerQ Pt 0) * ((3 ^ n) ^ 2 * Nat.card Z) := by
      rw [← hq]
      ring
    exact (Nat.eq_of_mul_eq_mul_right hZpos h2).symm
  let modV : Module (ZMod 3) (Additive (LayerQ Pt 0)) :=
    AddCommGroup.zmodModule (n := 3) (fun v => by
      rw [← ofMul_toMul v, ← ofMul_pow, hexpV, ofMul_one])
  let fintV : Fintype (Additive (LayerQ Pt 0)) := Fintype.ofFinite _
  have hV : Fintype.card (Additive (LayerQ Pt 0)) = 3 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact hcardV
  have hexpL : ∀ (i : ℕ) (m : LayerQ Pt (i + 1)), m ^ 3 = 1 := by
    intro i m
    let S : Subgroup (LayerQ Pt (i + 1)) :=
      { carrier := {m | m ^ 3 = 1}
        one_mem' := one_pow 3
        mul_mem' := fun {a b} ha hb => by
          change (a * b) ^ 3 = 1
          rw [mul_pow, ha, hb, one_mul]
        inv_mem' := fun {a} ha => by
          change a⁻¹ ^ 3 = 1
          rw [inv_pow, ha, inv_one] }
    have hle : Subgroup.closure (Set.range fun uy : LayerQ Pt i × LayerQ Pt 0 =>
        pair Pt i uy.1 uy.2) ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨u, y⟩, rfl⟩
      change (pair Pt i u y) ^ 3 = 1
      rw [← map_pow, hexpV, map_one]
    rw [closure_range_pair] at hle
    exact hle (Subgroup.mem_top m)
  have hmodL : ∀ i : ℕ, ∀ x : Additive (LayerQ Pt (i + 1)), 3 • x = 0 := fun i x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexpL, ofMul_one]
  let mod1 : Module (ZMod 3) (Additive (LayerQ Pt 1)) := AddCommGroup.zmodModule (hmodL 0)
  let mod2 : Module (ZMod 3) (Additive (LayerQ Pt 2)) := AddCommGroup.zmodModule (hmodL 1)
  let mod3 : Module (ZMod 3) (Additive (LayerQ Pt 3)) := AddCommGroup.zmodModule (hmodL 2)
  let f₂ := addPair (pair Pt 0)
  let f₃ := (AddMonoidHom.compHom (addPair (pair Pt 1))).comp f₂
  let f₄ := (AddMonoidHom.compHom (AddMonoidHom.compHom (addPair (pair Pt 2)))).comp f₃
  let c₁ : MultilinearMap (ZMod 3) (fun _ : Fin 2 => Additive (LayerQ Pt 0))
      (Additive (LayerQ Pt 1)) := ml2 f₂
  let c₂ : MultilinearMap (ZMod 3) (fun _ : Fin 3 => Additive (LayerQ Pt 0))
      (Additive (LayerQ Pt 2)) := ml3 f₃
  let c₃ : MultilinearMap (ZMod 3) (fun _ : Fin 4 => Additive (LayerQ Pt 0))
      (Additive (LayerQ Pt 3)) := ml4 f₄
  have hc₁ : ∀ x, c₁ (fun j => addConj Pt g hgN 0 (x j)) = addConj Pt g hgN 1 (c₁ x) := by
    intro x
    exact (addConj_addPair Pt g hgN 0 (x 0) (x 1)).symm
  have hc₂ : ∀ x, c₂ (fun j => addConj Pt g hgN 0 (x j)) = addConj Pt g hgN 2 (c₂ x) := by
    intro x
    change addPair (pair Pt 1) (addPair (pair Pt 0) (addConj Pt g hgN 0 (x 0))
      (addConj Pt g hgN 0 (x 1))) (addConj Pt g hgN 0 (x 2)) =
      addConj Pt g hgN (1 + 1) (addPair (pair Pt 1) (addPair (pair Pt 0) (x 0) (x 1)) (x 2))
    rw [addConj_addPair, addConj_addPair]
  have hc₃ : ∀ x, c₃ (fun j => addConj Pt g hgN 0 (x j)) = addConj Pt g hgN 3 (c₃ x) := by
    intro x
    change addPair (pair Pt 2) (addPair (pair Pt 1) (addPair (pair Pt 0)
      (addConj Pt g hgN 0 (x 0)) (addConj Pt g hgN 0 (x 1))) (addConj Pt g hgN 0 (x 2)))
      (addConj Pt g hgN 0 (x 3)) = addConj Pt g hgN (2 + 1) (addPair (pair Pt 2)
        (addPair (pair Pt 1) (addPair (pair Pt 0) (x 0) (x 1)) (x 2)) (x 3))
    rw [addConj_addPair, addConj_addPair, addConj_addPair]
  have hgen₁ : Subgroup.closure (Set.range fun x => Additive.toMul (c₁ x)) = ⊤ := by
    rw [eq_top_iff, ← closure_range_pair Pt 0]
    apply Subgroup.closure_mono
    rintro _ ⟨⟨u, y⟩, rfl⟩
    exact ⟨![Additive.ofMul u, Additive.ofMul y], rfl⟩
  have hgen₂ : Subgroup.closure (Set.range fun x => Additive.toMul (c₂ x)) = ⊤ := by
    rw [eq_top_iff, ← closure_pair_of_closure Pt _ hgen₁]
    apply Subgroup.closure_mono
    rintro _ ⟨⟨s, y⟩, ⟨⟨x, rfl⟩, -⟩, rfl⟩
    exact ⟨![x 0, x 1, Additive.ofMul y], rfl⟩
  have hgen₃ : Subgroup.closure (Set.range fun x => Additive.toMul (c₃ x)) = ⊤ := by
    rw [eq_top_iff, ← closure_pair_of_closure Pt _ hgen₂]
    apply Subgroup.closure_mono
    rintro _ ⟨⟨s, y⟩, ⟨⟨x, rfl⟩, -⟩, rfl⟩
    exact ⟨![x 0, x 1, x 2, Additive.ofMul y], rfl⟩
  have hfixZ : ∀ (i : ℕ) (z : E) (hz : z ∈ Z) (hzi : z ∈ γ Pt i),
      layerConj g hgN i (lmk Pt (⟨z, hzi⟩ : γ Pt i)) = lmk Pt (⟨z, hzi⟩ : γ Pt i) := by
    intro i z hz hzi
    rw [layerConj_lmk]
    congr 1
    apply Subtype.ext
    change g * z * g⁻¹ = z
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
  have hZ2 : Z ≤ γ Pt 2 := by
    intro z hz
    have h := eq_one_of_fixed Pt hV hgN (hθ 0) hfree (by norm_num) (by omega) c₁ hc₁ (hθ 1)
      hgen₁ _ (hfixZ 1 z hz (hZ1 hz))
    exact (lmk_eq_one_iff Pt).mp h
  have hZ3' : Z ≤ γ Pt 3 := by
    intro z hz
    have h := eq_one_of_fixed Pt hV hgN (hθ 0) hfree (by norm_num) (by omega) c₂ hc₂ (hθ 2)
      hgen₂ _ (hfixZ 2 z hz (hZ2 hz))
    exact (lmk_eq_one_iff Pt).mp h
  have hZ4 : Z ≤ γ Pt 4 := by
    intro z hz
    have h := eq_one_of_fixed Pt hV hgN (hθ 0) hfree (by norm_num) (by omega) c₃ hc₃ (hθ 3)
      hgen₃ _ (hfixZ 3 z hz (hZ3' hz))
    exact (lmk_eq_one_iff Pt).mp h
  rw [hγ4] at hZ4
  exact eq_bot_iff.mpr hZ4

theorem mem_zpowers_sq_of_odd {G : Type*} [Group G] {a w : G} {m : ℕ} (hm : Odd m)
    (ha : orderOf a = 2 * m) (hw : w ∈ Subgroup.zpowers a) (hwo : Odd (orderOf w)) :
    w ∈ Subgroup.zpowers (a ^ 2) := by
  have hdvd : orderOf w ∣ 2 * m := ha ▸ orderOf_dvd_of_mem_zpowers hw
  have hdm : orderOf w ∣ m :=
    (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hwo) hdvd)
  have hwm : w ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp hdm
  obtain ⟨j, hj⟩ := hm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine Subgroup.mem_zpowers_iff.mpr ⟨k * (j + 1), ?_⟩
  have h1 : (a ^ k) ^ m = 1 := hwm
  calc (a ^ 2) ^ (k * ((j : ℤ) + 1)) = (a ^ k) ^ (m + 1) := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, hj]
        congr 1
        push_cast
        ring
    _ = a ^ k := by rw [pow_succ, h1, one_mul]

end ThreeMult

open ThreeMult in
theorem rGroup_threeMultiplier :
    ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L),
    hL.q ≠ 5 → 3 < hL.q →
    ∀ (E : Type) [Group E] [Finite E] (Z : Subgroup E) [Z.Normal], Z ≤ Subgroup.center E →
      IsPGroup 3 Z → commutator E = ⊤ → Nonempty ((E ⧸ Z) ≃* L) → Z = ⊥ := by
  intro L _ _ hL hq5 hq3 E _ _ Z _ hZc hZ3 hperf ⟨e⟩
  classical
  have hq := hL.five_lt_q hq5 hq3
  have hJT : JTThreeHyp := CFSG.Walter.jtThreeHyp
  obtain ⟨hfodd, hf1⟩ := hL.odd_f hJT hq
  have hn3 : 3 ≤ hL.f := by
    obtain ⟨k, hk⟩ := hfodd
    omega
  have hqn : hL.q = 3 ^ hL.f := hL.q_eq_three_pow hJT hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 L) := inferInstance
  have hw := WardLocal.ward_two (hL.toReeTypeHyp hJT hq) P
  simp only [JRGroup.toReeTypeHyp_q] at hw
  obtain ⟨hPcard, -, -, -, -, hP₁c, -, -, -, hP₁P, -, hP₁e, hP₁card, hZP₁, -, -, hcubes, W,
    hWcyc, hWcard, -, hNP, hWt, hWR⟩ := hw
  set Pg : Subgroup L := (P : Subgroup L) with hPg
  set P₁ : Subgroup L := (commutator ↥Pg).map Pg.subtype with hP₁def
  set ZP : Subgroup L := (Subgroup.center ↥Pg).map Pg.subtype with hZPdef
  have hcard : Nat.card Pg = (3 ^ hL.f) ^ 3 := by rw [hPcard, hqn]
  have hcard₁ : Nat.card (⁅Pg, Pg⁆ : Subgroup L) = (3 ^ hL.f) ^ 2 := by
    rw [← hP₁c, hP₁card, hqn]
  have hexp : ∀ y ∈ Pg, y ^ 3 ∈ ⁅Pg, Pg⁆ := by
    intro y hy
    rw [← hP₁c]
    by_cases hy1 : y ∈ P₁
    · have : y ^ 3 = 1 := by
        have : IsElementaryAbelian 3 P₁ := hP₁e
        exact elemPow_eq_one_of_isElementaryAbelian y hy1
      rw [this]
      exact P₁.one_mem
    · have h : y ^ 3 ∈ (fun x : L => x ^ 3) '' {x : L | x ∈ Pg ∧ x ∉ P₁} := ⟨y, ⟨hy, hy1⟩, rfl⟩
      rw [hcubes] at h
      exact hZP₁ h.1
  have hclass : Pg.lowerCentralSeries 3 = ⊥ := by
    have h1 : Pg.lowerCentralSeries 1 = P₁ := hP₁c.symm
    have h2 : Pg.lowerCentralSeries 2 = ZP := by
      rw [Subgroup.lowerCentralSeries_succ, h1]
      exact hP₁P
    rw [Subgroup.lowerCentralSeries_succ, h2, Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩))
  obtain ⟨⟨a, haW⟩, hgen⟩ := hWcyc.exists_generator
  have hao : orderOf a = 3 ^ hL.f - 1 := by
    rw [← Subgroup.orderOf_mk a haW, orderOf_eq_card_of_forall_mem_zpowers hgen, hWcard, hqn]
  have hWa : W = Subgroup.zpowers a := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact haW
  have ha : a ∈ Subgroup.normalizer (Pg : Set L) := by
    rw [hNP]
    exact Subgroup.mem_sup_right haW
  have hm : 3 ^ hL.f - 1 = 2 * ((3 ^ hL.f - 1) / 2) ∧ Odd ((3 ^ hL.f - 1) / 2) := by
    have h8 : 3 ^ hL.f % 8 = 3 := by
      have h := (hL.toJTHyp hq).q_mod_eight_of_eq_three (hL.p_eq_three hJT hq)
      change hL.q % 8 = 3 at h
      rw [hqn] at h
      exact h
    exact ⟨by omega, Nat.odd_iff.mpr (by omega)⟩
  have hR : orderOf (a ^ 2) = (3 ^ hL.f - 1) / 2 := by
    rw [orderOf_pow' _ (by norm_num), hao, hm.1, Nat.gcd_mul_right_left]
  have hodd : ∀ w ∈ Subgroup.zpowers a, w ≠ 1 → Odd (orderOf w) →
      ∀ x ∈ Pg, w * x * w⁻¹ = x → x = 1 := by
    intro w hw hw1 hwo x hx hwx
    have hwR : w ∈ Subgroup.zpowers (a ^ 2) := mem_zpowers_sq_of_odd hm.2 (hao.trans hm.1) hw hwo
    have hRW : a ^ 2 ∈ W := Subgroup.pow_mem _ haW 2
    have h := hWR (a ^ 2) hRW (by rw [hR, hqn]) w hwR hw1
    have hxC : x ∈ Pg ⊓ Subgroup.centralizer ({w} : Set L) := by
      refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * w = w * x * w⁻¹ * w := by rw [hwx]
        _ = w * x := by group
    rw [h] at hxC
    exact hxC
  have hinv : ∀ w ∈ Subgroup.zpowers a, orderOf w = 2 →
      ∀ x ∈ Pg, w * x * w⁻¹ = x → x ∈ ⁅Pg, Pg⁆ := by
    intro w hw hw2 x hx hwx
    have hwW : w ∈ W := hWa ▸ hw
    have h := (hWt w hwW hw2).1
    have hxC : x ∈ Pg ⊓ Subgroup.centralizer ({w} : Set L) := by
      refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * w = w * x * w⁻¹ * w := by rw [hwx]
        _ = w * x := by group
    rw [h] at hxC
    rw [← hP₁c]
    exact hxC.1
  let π : E →* L := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e (QuotientGroup.mk' Z x) = e 1 := by rw [map_one]; exact hx
      exact (QuotientGroup.eq_one_iff x).mp (e.injective h1)
    · intro hx
      change e (x : E ⧸ Z) = 1
      rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]
  exact eq_bot_of_layers hπ hker hZc hZ3 hperf P hn3 hcard hcard₁ hexp hclass ha hao hodd hinv

end CFSG.Walter.W67
