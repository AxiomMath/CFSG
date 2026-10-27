module

public import CFSG.Quasithin.Background.D2Y2
public import CFSG.Quasithin.Background.D2Y1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def centR (X : Subgroup (MulAut V)) (x : MulAut V) : Subgroup (MulAut V) :=
  pCoreOf 3 X ⊓ Subgroup.centralizer ({x} : Set (MulAut V))

structure InvPair (X : Subgroup (MulAut V)) (t x : MulAut V) : Prop where
  ht : t ∈ TInv X
  hx : x ∈ pCoreOf 3 X
  hx1 : x ≠ 1
  hinv : t * x * t⁻¹ = x⁻¹

omit [Finite V] in
theorem mem_centR {X : Subgroup (MulAut V)} {x p : MulAut V} :
    p ∈ centR X x ↔ p ∈ pCoreOf 3 X ∧ p * x = x * p := by
  unfold centR
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

section Basic

variable {X : Subgroup (MulAut V)}

theorem four_le_rk_commV (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) {S : Subgroup (MulAut V)} (hS : S ≤ pCoreOf 3 X)
    (hcard : Nat.card S = 3) : 4 ≤ rk (commV S) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, -, -, hev⟩ := commV_card_three hV hcard
  obtain ⟨d, -, hd1, hdz, -⟩ := exists_generator_of_prime_card (p := 3) hcard
  have h1 : 1 ≤ rk (commV S) := by
    rw [← hdz]
    exact one_le_rk_commV_zpowers hV hd1
  have h2 : rk (commV S) ≠ 2 := fun h =>
    hX1 S ⟨by rw [c.fittingOf_eq hV]; exact hS, by rw [hcard], by rw [h]⟩
  obtain ⟨m, hm⟩ := hev
  omega

theorem odd_orderOf_of_mem_pCoreOf {g : MulAut V} (hg : g ∈ pCoreOf 3 X) : Odd (orderOf g) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_orderOf_eq_pow (pCoreOf_isPGroup 3 X) hg
  rw [ha]
  exact (show Odd 3 from ⟨1, rfl⟩).pow

theorem exists_mem_normalizer_of_ne {p : ℕ} [Fact p.Prime] {N H : Subgroup (MulAut V)}
    (hN : IsPGroup p N) (hHN : H ≤ N) (hne : H ≠ N) :
    ∃ g ∈ N, g ∈ Subgroup.normalizer (H : Set (MulAut V)) ∧ g ∉ H := by
  have hnil : Group.IsNilpotent ↥N := hN.isNilpotent
  have hlt : H.subgroupOf N < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm hHN fun g hg => ?_
    have : (⟨g, hg⟩ : ↥N) ∈ H.subgroupOf N := by rw [htop]; exact Subgroup.mem_top _
    exact this
  obtain ⟨g, hgN, hgH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨g, g.2, ?_, fun h => hgH h⟩
  rw [Subgroup.mem_normalizer_iff] at hgN ⊢
  intro h
  constructor
  · intro hh
    exact (hgN ⟨h, hHN hh⟩).mp hh
  · intro hh
    have hhN : g * h * g⁻¹ ∈ N := hHN hh
    have hh' : h ∈ N := by
      have := N.mul_mem (N.mul_mem (N.inv_mem g.2) hhN) g.2
      simpa [mul_assoc] using this
    exact (hgN ⟨h, hh'⟩).mpr hh

end Basic

theorem mem_zpowers_of_cube {G : Type*} [Group G] [Finite G] [IsCyclic G] {z z₁ : G}
    (hz : z ^ 3 = 1) (hz₁ : z₁ ^ 3 = 1) (h1 : z₁ ≠ 1) : z ∈ Subgroup.zpowers z₁ := by
  classical
  have := Fintype.ofFinite G
  by_contra hzn
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  have hz₁2 : z₁ ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc z₁ = z₁ ^ 3 * (z₁ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz₁, h]; simp
  have hz₁z₁2 : z₁ ≠ z₁ ^ 2 := by
    intro h
    apply h1
    calc z₁ = z₁ ^ 2 * z₁⁻¹ := by group
      _ = z₁ * z₁⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel z₁
  have hz1 : z ≠ 1 := fun h => hzn (by rw [h]; exact Subgroup.one_mem _)
  have hzz₁ : z ≠ z₁ := fun h => hzn (by rw [h]; exact Subgroup.mem_zpowers z₁)
  have hzz₁2 : z ≠ z₁ ^ 2 := fun h =>
    hzn (by rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z₁) 2)
  have hsub : ({1, z₁, z₁ ^ 2, z} : Finset G) ⊆ Finset.univ.filter (fun a : G => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact hz₁
    · rw [h, ← pow_mul, mul_comm, pow_mul, hz₁, one_pow]
    · rw [h]; exact hz
  have hcard := Finset.card_le_card hsub
  have hC : z₁ ^ 2 ∉ ({z} : Finset G) := by
    rw [Finset.mem_singleton]; exact hzz₁2.symm
  have hB : z₁ ∉ ({z₁ ^ 2, z} : Finset G) := by
    rw [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hz₁z₁2, hzz₁.symm⟩
  have hA : (1 : G) ∉ ({z₁, z₁ ^ 2, z} : Finset G) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or]
    exact ⟨h1.symm, hz₁2.symm, hz1.symm⟩
  have h4 : ({1, z₁, z₁ ^ 2, z} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
      Finset.card_insert_of_notMem hC, Finset.card_singleton]
  omega

section Basic2

variable {X : Subgroup (MulAut V)}

omit [Finite V] in
theorem conj_comm_of_inverting {G : Type*} [Group G] {t x p : G} (ht2 : t ^ 2 = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) (hp : p * x = x * p) :
    (t * p * t⁻¹) * x = x * (t * p * t⁻¹) := by
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h1 : t * x * t = x⁻¹ := by rw [htinv] at hinv; exact hinv
  have hxt : x * t = t * x⁻¹ := by
    calc x * t = t⁻¹ * (t * x * t) := by group
      _ = t⁻¹ * x⁻¹ := by rw [h1]
      _ = t * x⁻¹ := by rw [htinv]
  have htx : t * x = x⁻¹ * t := by
    calc t * x = (t * x * t) * t⁻¹ := by group
      _ = x⁻¹ * t⁻¹ := by rw [h1]
      _ = x⁻¹ * t := by rw [htinv]
  have hpx : p * x⁻¹ = x⁻¹ * p := by
    have := hp
    calc p * x⁻¹ = x⁻¹ * (x * p) * x⁻¹ := by group
      _ = x⁻¹ * (p * x) * x⁻¹ := by rw [this]
      _ = x⁻¹ * p := by group
  rw [htinv]
  calc t * p * t * x = t * p * (t * x) := by group
    _ = t * p * (x⁻¹ * t) := by rw [htx]
    _ = t * (p * x⁻¹) * t := by group
    _ = t * (x⁻¹ * p) * t := by rw [hpx]
    _ = (t * x⁻¹) * p * t := by group
    _ = (x * t) * p * t := by rw [← hxt]
    _ = x * (t * p * t) := by group

omit [Finite V] in
theorem conj_mem_centR {t x p : MulAut V} (ht : t ∈ TInv X) (hinv : t * x * t⁻¹ = x⁻¹)
    (hp : p ∈ centR X x) : t * p * t⁻¹ ∈ centR X x := by
  obtain ⟨hpR, hpx⟩ := mem_centR.mp hp
  refine mem_centR.mpr ⟨?_, conj_comm_of_inverting ht.2.2.1 hinv hpx⟩
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X ht.1) p).mp hpR

theorem isCyclic_pCoreOf_inf_centralizer (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) {t : MulAut V}
    (ht : t ∈ TInv X) :
    IsCyclic ↥(pCoreOf 3 X ⊓ Subgroup.centralizer ({t} : Set (MulAut V))) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have hnorm : ∀ b ∈ Subgroup.zpowers t, ∀ y ∈ pCoreOf 3 X, b * y * b⁻¹ ∈ pCoreOf 3 X := by
    intro b hb y hy
    have hbX : b ∈ X := Subgroup.zpowers_le.mpr ht.1 hb
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hbX) y).mp hy
  have hfaith : ∀ b ∈ Subgroup.zpowers t, (∀ y ∈ pCoreOf 3 X, b * y = y * b) → b = 1 := by
    intro b hb hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rcases zpow_involution ht2 k with e | e
    · exact e
    · exfalso
      rw [e] at hc
      obtain ⟨y, hy, hne⟩ := c.faithful_three hV ht
      exact hne (hc y hy)
  exact isCyclic_inf_centralizer_of_faithful (X := X) (P := pCoreOf 3 X)
    (A := Subgroup.zpowers t) (p := 3) (by norm_num) (pCoreOf_le 3 X) (pCoreOf_isPGroup 3 X)
    ⟨fun u hu v hv => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact ((Commute.refl t).zpow_zpow i j).eq,
      fun u hu => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
        simp [ht2]⟩
    (Subgroup.zpowers_le.mpr ht.1) hnorm c.hyp.sqtk hfaith (Subgroup.mem_zpowers t) ht.2.1

theorem inverted_mem_zpowers (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) {t x y : MulAut V} (h : InvPair X t x) (hy : y ∈ centR X x)
    (hy1 : y ≠ 1) (hinvy : t * y * t⁻¹ = y⁻¹) : y ∈ Subgroup.zpowers x := by
  by_contra hyx
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hyR, hyc⟩ := mem_centR.mp hy
  obtain ⟨hxord, hrk4, hfix, -, -⟩ := inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv
  obtain ⟨hyord, -, -, -, -⟩ := inverted_data hV c hX1 h.ht hyR hy1 hinvy
  have hxc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hyc3 : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyord]
  have hne : Subgroup.zpowers x ≠ Subgroup.zpowers y := by
    intro heq
    apply hyx
    rw [heq]
    exact Subgroup.mem_zpowers y
  have hcomm_xy : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute x y from hyc.symm) m n).eq
  obtain ⟨hEcard, hEprod⟩ := sup_structure hxc hyc3 hne hcomm_xy
  have hEcomm := sup_comm_elements hxc hyc3 hne hcomm_xy
  have hy3 : y ^ 3 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hyfix : ∀ v ∈ fixV (Subgroup.zpowers x), y v = v := by
    intro v hv
    have htv : t v = v := hfix v hv
    have hyv : y v ∈ fixV (Subgroup.zpowers x) := by
      refine fixV_smul_mem (fun p hp => ?_) hv
      rw [mul_assoc, hcomm_xy p hp y (Subgroup.mem_zpowers y), inv_mul_cancel_left]
      exact hp
    have htyv : t (y v) = y v := hfix _ hyv
    have e : (t * y * t⁻¹) v = y⁻¹ v := by rw [hinvy]
    have htinvv : t⁻¹ v = v := by
      calc t⁻¹ v = t⁻¹ (t v) := by rw [htv]
        _ = v := MulAut.inv_apply_self _ t v
    have e2 : t (y (t⁻¹ v)) = y⁻¹ v := e
    rw [htinvv, htyv] at e2
    have e3 : (y * y) v = v := by
      show y (y v) = v
      rw [e2]
      exact MulAut.apply_inv_self _ y v
    have e4 : (y * (y * y)) v = y v := by
      show y ((y * y) v) = y v
      rw [e3]
    have e5 : y * (y * y) = 1 := by rw [← pow_three]; exact hy3
    rw [e5] at e4
    simpa using e4.symm
  have hEU : ∀ g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, ∀ u ∈ commV (Subgroup.zpowers x),
      g u ∈ commV (Subgroup.zpowers x) := by
    intro g hg u hu
    refine commV_smul_mem (fun p hp => ?_) hu
    have hpE : p ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left hp
    rw [hEcomm g hg p hpE, mul_inv_cancel_right]
    exact hp
  have hEC : ∀ g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, ∀ v ∈ fixV (Subgroup.zpowers x),
      g v = v := by
    intro g hg v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hEprod g hg
    have hbv : b v = v := by
      have hs : Subgroup.zpowers y ≤ MulAction.stabilizer (MulAut V) v :=
        Subgroup.zpowers_le.mpr (hyfix v hv)
      exact hs hb
    show a (b v) = v
    rw [hbv]
    exact hv a ha
  obtain ⟨Y, hY⟩ := exists_Xk_of_card_nine hV c (E := Subgroup.zpowers x ⊔ Subgroup.zpowers y)
    (sup_le (Subgroup.zpowers_le.mpr h.hx) (Subgroup.zpowers_le.mpr hyR)) hEcard
    (U := commV (Subgroup.zpowers x)) (C := fixV (Subgroup.zpowers x))
    ⟨(commV_card_three hV hxc).1, (commV_card_three hV hxc).2.1⟩ hrk4 hEU hEC
  exact hX1 Y hY

theorem exists_zpow_commute (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) {t x p : MulAut V} (h : InvPair X t x) (hp : p ∈ centR X x) :
    ∃ k : ℤ, t * (p * x ^ k) = (p * x ^ k) * t := by
  have ht2 : t ^ 2 = 1 := h.ht.2.2.1
  have hxord := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).1
  have hx3 : x ^ (3 : ℤ) = 1 := by
    have : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    exact_mod_cast this
  have hyc : p⁻¹ * (t * p * t⁻¹) ∈ centR X x :=
    (centR X x).mul_mem ((centR X x).inv_mem hp) (conj_mem_centR h.ht h.hinv hp)
  have hinvy : t * (p⁻¹ * (t * p * t⁻¹)) * t⁻¹ = (p⁻¹ * (t * p * t⁻¹))⁻¹ :=
    inv_conj_of_involution p ht2
  by_cases hy1 : p⁻¹ * (t * p * t⁻¹) = 1
  · refine ⟨0, ?_⟩
    have h1 : p = t * p * t⁻¹ := inv_mul_eq_one.mp hy1
    have h2 : t * p = p * t := mul_inv_eq_iff_eq_mul.mp h1.symm
    simpa using h2
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (inverted_mem_zpowers hV c hX1 h hyc hy1 hinvy)
    refine ⟨2 * k, ?_⟩
    have h1 : t * p * t⁻¹ = p * x ^ k := by
      rw [hk]
      group
    have h2 : t * x ^ (2 * k) * t⁻¹ = (x ^ (2 * k))⁻¹ := by
      rw [← conj_zpow, h.hinv, inv_zpow]
    have h3k : x ^ (3 * k) = 1 := by rw [zpow_mul, hx3, one_zpow]
    have h4 : x ^ (2 * k) = x ^ (-k) := by
      calc x ^ (2 * k) = x ^ (-k + 3 * k) := by congr 1; ring
        _ = x ^ (-k) * x ^ (3 * k) := zpow_add _ _ _
        _ = x ^ (-k) := by rw [h3k, mul_one]
    have h3 : t * (p * x ^ (2 * k)) * t⁻¹ = p * x ^ (2 * k) := by
      calc t * (p * x ^ (2 * k)) * t⁻¹ = (t * p * t⁻¹) * (t * x ^ (2 * k) * t⁻¹) := by group
        _ = (p * x ^ k) * (x ^ (2 * k))⁻¹ := by rw [h1, h2]
        _ = p * (x ^ k * (x ^ (2 * k))⁻¹) := by rw [mul_assoc]
        _ = p * x ^ (-k) := by
          congr 1
          rw [← zpow_neg, ← zpow_add]
          congr 1
          ring
        _ = p * x ^ (2 * k) := by rw [h4]
    exact mul_inv_eq_iff_eq_mul.mp h3

theorem Yinv_data (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {Y : Subgroup (MulAut V)} (hY : Y ∈ Yinv X) :
    ∃ y t : MulAut V, InvPair X t y ∧ Subgroup.zpowers y = Y ∧ orderOf y = 3 ∧
      rk (commV Y) = 4 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hYR, hcard, t, ht, hinv⟩ := hY
  obtain ⟨y, hyY, hy1, hyz, hyord⟩ := exists_generator_of_prime_card (p := 3) hcard
  have hp : InvPair X t y := ⟨ht, hYR hyY, hy1, hinv y hyY⟩
  refine ⟨y, t, hp, hyz, hyord, ?_⟩
  have := (inverted_data hV c hX1 ht (hYR hyY) hy1 (hinv y hyY)).2.1
  rwa [hyz] at this

theorem exists_second_inverted (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) {t x : MulAut V} (h : InvPair X t x)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) :
    ∃ Y ∈ Yinv X, Y ≤ centR X x ∧ Y ≠ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hX₀ : Subgroup.zpowers x ∈ Yinv X := zpowers_mem_Yinv hV h.ht h.hx h.hx1 h.hinv
  have hxord := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).1
  obtain ⟨Y', hY', hY'ne⟩ : ∃ Y' ∈ Yinv X, Y' ≠ Subgroup.zpowers x := by
    obtain ⟨Y₁, h₁, Y₂, h₂, hne⟩ := htwo
    by_cases e : Y₁ = Subgroup.zpowers x
    · exact ⟨Y₂, h₂, fun e2 => hne (e.trans e2.symm)⟩
    · exact ⟨Y₁, h₁, e⟩
  by_cases hPR : centR X x = pCoreOf 3 X
  · exact ⟨Y', hY', by rw [hPR]; exact hY'.1, hY'ne⟩
  · obtain ⟨g, hgR, hgN, hgP⟩ := exists_mem_normalizer_of_ne (pCoreOf_isPGroup 3 X)
      (inf_le_left : centR X x ≤ pCoreOf 3 X) hPR
    have hgX : g ∈ X := pCoreOf_le 3 X hgR
    refine ⟨conjBy g (Subgroup.zpowers x), Yinv_conj hX₀ hgX, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      have haP : a ∈ centR X x := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact mem_centR.mpr ⟨(pCoreOf 3 X).zpow_mem h.hx k, (Commute.zpow_left (Commute.refl x) k).eq⟩
      have := (Subgroup.mem_normalizer_iff.mp hgN a).mp haP
      show g * a * g⁻¹ ∈ centR X x
      exact this
    · intro heq
      have hodd : Odd (orderOf g) := odd_orderOf_of_mem_pCoreOf hgR
      have hcomm := commute_of_normalizes_three_odd (A := Subgroup.zpowers x)
        (by rw [Nat.card_zpowers, hxord]) hodd
        (fun a ha => by
          have := mem_conjBy_of_mem (g := g) ha
          rwa [heq] at this)
        (fun a ha => by
          have h1 : a ∈ conjBy g (Subgroup.zpowers x) := by rw [heq]; exact ha
          exact mem_conjBy_iff.mp h1)
      exact hgP (mem_centR.mpr ⟨hgR, hcomm x (Subgroup.mem_zpowers x)⟩)

end Basic2

end CFSG.Quasithin
