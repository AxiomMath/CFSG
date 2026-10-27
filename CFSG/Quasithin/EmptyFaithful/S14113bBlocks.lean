module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxCases2
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommute
public import CFSG.Quasithin.EmptyFaithful.S14113Layer
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S14110 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace S14110.A4Data

variable {X W : Subgroup G} {c : G}

omit [Finite G] in
theorem mem_W_of_commute (h : A4Data X W c) {x w : G} (hx : x ∈ X) (hw : w ∈ W) (hw1 : w ≠ 1)
    (hxw : x * w = w * x) : x ∈ W := by
  obtain ⟨w', hw', i, rfl⟩ := h.mem_decomp hx
  have hci : c ^ i ∈ normalizer (W : Set G) := zpow_mem h.mem_normalizer i
  have hcw : c ^ i * w = w * c ^ i := by
    have h1 : w' * (c ^ i * w) = w * (w' * c ^ i) := by
      calc w' * (c ^ i * w) = w' * c ^ i * w := by group
        _ = w * (w' * c ^ i) := hxw
    have h2 : w' * w = w * w' := h.comm w' hw' w hw
    have h3 : w' * (c ^ i * w) = w' * (w * c ^ i) := by
      calc w' * (c ^ i * w) = w * (w' * c ^ i) := h1
        _ = (w * w') * c ^ i := by group
        _ = (w' * w) * c ^ i := by rw [h2]
        _ = w' * (w * c ^ i) := by group
    exact mul_left_cancel h3
  have hmod : c ^ (i % 3) = c ^ i := by
    have := zpow_mod_orderOf c i
    rw [h.order_c] at this
    simpa using this
  have hc3 : c ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact h.c_pow_three
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hcfix : c * w * c⁻¹ ≠ w := h.fpf w hw hw1
  have h1 : c ^ i = 1 := by
    rcases hcases with h0 | h1 | h2
    · rw [← hmod, h0]; simp
    · exfalso
      rw [← hmod, h1, zpow_one] at hcw
      apply hcfix
      calc c * w * c⁻¹ = (w * c) * c⁻¹ := by rw [hcw]
        _ = w := by group
    · exfalso
      rw [← hmod, h2] at hcw
      apply hcfix
      calc c * w * c⁻¹ = c * (c ^ (2 : ℤ) * w * (c ^ (2 : ℤ))⁻¹) * c⁻¹ := by
            rw [show c ^ (2 : ℤ) * w = w * c ^ (2 : ℤ) from hcw]; group
        _ = c ^ (3 : ℤ) * w * (c ^ (3 : ℤ))⁻¹ := by group
        _ = w := by rw [hc3]; simp
  rw [h1, mul_one]
  exact hw'

omit [Finite G] in
theorem centralizes_of_odd_of_fixed (h : A4Data X W c) {g : G}
    (hgX : g ∈ normalizer (X : Set G)) (hodd : Odd (orderOf g)) {w : G} (hw : w ∈ W)
    (hw1 : w ≠ 1) (hgw : g * w = w * g) : ∀ x ∈ X, g * x = x * g := by
  have hgm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  obtain ⟨x, hxX, hxk⟩ := h.exists_mem_mul_centralizer_of_odd hgX hodd
    (by rw [hgm]; exact one_mem _)
  set k : G := x⁻¹ * g with hk
  have hkc : ∀ l ∈ X, k * l = l * k := fun l hl => (mem_centralizer_iff.mp hxk l hl).symm
  have hgxk : g = x * k := by rw [hk]; group
  have hxw : x * w = w * x := by
    have h1 : x * k * w = w * (x * k) := by rw [← hgxk]; exact hgw
    have h2 : k * w = w * k := hkc w (h.le hw)
    have h3 : x * w * k = w * x * k := by
      calc x * w * k = x * (w * k) := by group
        _ = x * (k * w) := by rw [h2]
        _ = x * k * w := by group
        _ = w * (x * k) := h1
        _ = w * x * k := by group
    exact mul_right_cancel h3
  have hxW : x ∈ W := h.mem_W_of_commute hxX hw hw1 hxw
  have hx2 : x ^ 2 = 1 := h.sq_eq_one x hxW
  have hxkc : Commute x k := (hkc x hxX).symm
  have hxm : x ^ orderOf g = 1 := by
    have h1 : (x * k) ^ orderOf g = x ^ orderOf g * k ^ orderOf g := hxkc.mul_pow _
    rw [← hgxk, hgm] at h1
    have h2 : x ^ orderOf g = (k ^ orderOf g)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
    refine h.center _ (pow_mem hxX _) fun l hl => ?_
    have hkl : Commute (k ^ orderOf g) l := Commute.pow_left (show Commute k l from hkc l hl) _
    rw [h2]
    exact hkl.inv_left.eq
  have hx1 : x = 1 := by
    obtain ⟨j, hj⟩ := hodd
    have hxo : x ^ (2 * j + 1) = 1 := by rw [← hj]; exact hxm
    calc x = x ^ (2 * j + 1) * (x ^ 2) ^ (-(j : ℤ)) := by
          rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add]
          norm_num
      _ = 1 := by rw [hxo, hx2]; simp
  intro l hl
  rw [hgxk, hx1, one_mul]
  exact hkc l hl

end S14110.A4Data

@[expose] def IsA4Blk (M X : Subgroup G) : Prop :=
  X ≤ M ∧ (X.subgroupOf M).IsSubnormal ∧ ∃ (W : Subgroup G) (c : G), A4Data X W c

namespace IsA4Blk

variable {M X Y : Subgroup G}

omit [Finite G] in
theorem cj (hX : IsA4Blk M X) {m : G} (hm : m ∈ M) : IsA4Blk M (S14110.cj m X) := by
  obtain ⟨hXM, hXs, W, c, hA⟩ := hX
  exact ⟨S14110.cj_le hXM hm, isSubnormal_cj hXs hm, S14110.cj m W, m * c * m⁻¹,
    hA.map (MulAut.conj m)⟩

theorem commute_of_ne {M X Y : Subgroup G} (hcharM : CharTwo M) (hX : IsA4Blk M X)
    (hY : IsA4Blk M Y) (hne : X ≠ Y) : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  obtain ⟨hXM, hXs, W, c, hA⟩ := hX
  obtain ⟨hYM, hYs, W', c', hB⟩ := hY
  exact (commute_or_eq_of_isSubnormal hcharM hXM hYM hXs hYs hA hB).resolve_left hne

theorem normalizes_of_odd (hcharM : CharTwo M) (hrank : CFSG.Open.pRank 3 M ≤ 2)
    (hX : IsA4Blk M X) {g : G} (hg : g ∈ M) (hodd : Odd (orderOf g)) :
    g ∈ normalizer (X : Set G) := by
  by_contra hgX
  rw [mem_normalizer_iff_cj] at hgX
  have hgg : g * g ∈ M := M.mul_mem hg hg
  have hX₁ : IsA4Blk M (S14110.cj g X) := hX.cj hg
  have hX₂ : IsA4Blk M (S14110.cj (g * g) X) := hX.cj hgg
  have hne01 : X ≠ S14110.cj g X := fun e => hgX e.symm
  have hne12 : S14110.cj g X ≠ S14110.cj (g * g) X := by
    intro e
    apply hgX
    have : S14110.cj g (S14110.cj g X) = S14110.cj g X := by rw [S14110.cj_cj]; exact e.symm
    exact S14110.cj_injective g this
  have hne02 : X ≠ S14110.cj (g * g) X := by
    intro e
    apply hgX
    have hg2 : g * g ∈ normalizer (X : Set G) := mem_normalizer_iff_cj.2 e.symm
    obtain ⟨k, hk⟩ := hodd
    have hgn : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    have hgeq : g = (g * g) ^ (k + 1) := by
      have h1 : (g * g) ^ (k + 1) = g ^ (2 * k + 1) * g := by
        rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
      rw [h1, hgn, one_mul]
    have : g ∈ normalizer (X : Set G) := by
      rw [hgeq]; exact Subgroup.pow_mem _ hg2 _
    exact mem_normalizer_iff_cj.1 this
  obtain ⟨W₀, c₀, hA₀⟩ := hX.2.2
  obtain ⟨W₁, c₁, hA₁⟩ := hX₁.2.2
  obtain ⟨W₂, c₂, hA₂⟩ := hX₂.2.2
  exact false_of_three_commuting hrank hA₀ hA₁ hA₂ hX.1 hX₁.1 hX₂.1
    (commute_of_ne hcharM hX hX₁ hne01) (commute_of_ne hcharM hX hX₂ hne02)
    (commute_of_ne hcharM hX₁ hX₂ hne12)

end IsA4Blk

@[expose] def blockSet (M : Subgroup G) : Set G := {x | ∃ X, IsA4Blk M X ∧ x ∈ X}

@[expose] def blockCentralizer (M : Subgroup G) : Subgroup G :=
  M ⊓ Subgroup.centralizer (blockSet M)

omit [Finite G] in
theorem mem_blockCentralizer {M : Subgroup G} {k : G} :
    k ∈ blockCentralizer M ↔ k ∈ M ∧ ∀ X, IsA4Blk M X → ∀ x ∈ X, x * k = k * x := by
  unfold blockCentralizer
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact and_congr_right fun _ => ⟨fun h X hX x hx => h x ⟨X, hX, hx⟩,
    fun h x ⟨X, hX, hx⟩ => h X hX x hx⟩

omit [Finite G] in
theorem blockCentralizer_le {M : Subgroup G} : blockCentralizer M ≤ M := inf_le_left

omit [Finite G] in
theorem le_normalizer_blockCentralizer (M : Subgroup G) :
    M ≤ normalizer (blockCentralizer M : Set G) := by
  have key : ∀ m ∈ M, ∀ k ∈ blockCentralizer M, m * k * m⁻¹ ∈ blockCentralizer M := by
    intro m hm k hk
    obtain ⟨hkM, hkc⟩ := mem_blockCentralizer.mp hk
    refine mem_blockCentralizer.mpr ⟨M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm), ?_⟩
    intro X hX x hx
    have hX' : IsA4Blk M (S14110.cj m⁻¹ X) := hX.cj (M.inv_mem hm)
    have hx' : m⁻¹ * x * m ∈ S14110.cj m⁻¹ X := by
      rw [S14110.mem_cj]
      have : m⁻¹⁻¹ * (m⁻¹ * x * m) * m⁻¹ = x := by group
      rw [this]; exact hx
    have := hkc _ hX' _ hx'
    calc x * (m * k * m⁻¹) = m * ((m⁻¹ * x * m) * k) * m⁻¹ := by group
      _ = m * (k * (m⁻¹ * x * m)) * m⁻¹ := by rw [this]
      _ = m * k * m⁻¹ * x := by group
  intro m hm
  rw [mem_normalizer_iff]
  intro k
  exact ⟨key m hm k, fun hk => by simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ hk⟩

section Odd

variable {T Mc M : Subgroup G}

theorem pCoreOf_two_le_T_of_inM (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) :
    pCoreOf 2 M ≤ T := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have := pCoreOf_two_le_sylow M S (hS ▸ hM.2)
  rwa [hS] at this

theorem S14110.A4Data.W_le_pCoreOf {M X W : Subgroup G} {c : G} (hA : A4Data X W c) (hXM : X ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal) : W ≤ pCoreOf 2 M :=
  le_pCoreOf_of_isSubnormal hXM hXs
    (fun u => ⟨1, by
      have := hA.sq_eq_one u u.2
      simpa [Subtype.ext_iff] using this⟩) hA.le hA.le_normalizer

omit [Finite G] in
theorem S14110.A4Data.ne_bot {X W : Subgroup G} {c : G} (hA : A4Data X W c) : W ≠ ⊥ := by
  intro hb
  have := hA.card_W
  rw [hb, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem omegaOneCenter_comm (T : Subgroup G) :
    ∀ z ∈ quasithinOmegaOneCenter T, ∀ t ∈ T, t * z = z * t := by
  intro z hz
  have hle : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
    unfold quasithinOmegaOneCenter
    rw [Subgroup.closure_le]
    exact fun w hw => hw.1.2
  intro t ht
  exact Subgroup.mem_centralizer_iff.mp (hle hz) t ht

theorem IsA4Blk.centralizes_of_odd (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    {X : Subgroup G} (hX : IsA4Blk M X) {g : G} (hg : g ∈ M) (hodd : Odd (orderOf g))
    (hgZ : g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ∀ x ∈ X, g * x = x * g := by
  have hcharM : CharTwo M := charTwo_of_inM h hM
  have hrank : CFSG.Open.pRank 3 M ≤ 2 :=
    pRank_le_two_of_isTwoLocal h.qtke hM.1.1 Nat.prime_three (by norm_num)
  have hTM : T ≤ M := hM.2
  have hQT : pCoreOf 2 M ≤ T := pCoreOf_two_le_T_of_inM h hM
  have hgN : g ∈ normalizer (X : Set G) := hX.normalizes_of_odd hcharM hrank hg hodd
  obtain ⟨hXM, hXs, W, c, hA⟩ := hX
  have hWT : W ≤ T := (S14110.A4Data.W_le_pCoreOf hA hXM hXs).trans hQT
  have hW1 : W ≠ ⊥ := S14110.A4Data.ne_bot hA
  by_cases hTN : T ≤ normalizer (X : Set G)
  ·
    have hTW : T ≤ normalizer (W : Set G) := hTN.trans hA.normalizer_le_normalizer_W
    obtain ⟨z, hzW, hz1, hzZ⟩ :=
      exists_mem_omegaOneCenter_of_normalized h.sylow.1 hWT hW1 hTW
    have hgz : g * z = z * g := ((mem_centralizer_iff.mp hgZ) z hzZ).symm
    exact hA.centralizes_of_odd_of_fixed hgN hodd hzW hz1 hgz
  ·
    obtain ⟨t, htT, htn⟩ : ∃ t ∈ T, t ∉ normalizer (X : Set G) := by
      by_contra hcon
      exact hTN fun t ht => by_contra fun hn => hcon ⟨t, ht, hn⟩
    have htM : t ∈ M := hTM htT
    have hne : S14110.cj t X ≠ X := fun e => htn (mem_normalizer_iff_cj.2 e)
    have hX' : IsA4Blk M (S14110.cj t X) := (show IsA4Blk M X from ⟨hXM, hXs, W, c, hA⟩).cj htM
    have hDC : ∀ m ∈ M, S14110.cj m X = X ∨
        ∀ x ∈ X, ∀ y ∈ S14110.cj m X, x * y = y * x := fun m hm =>
      (commute_or_eq_of_isSubnormal hcharM hXM (S14110.cj_le hXM hm) hXs
        (isSubnormal_cj hXs hm) hA (hA.map (MulAut.conj m))).imp_left Eq.symm
    have htwo := two_conj hA hXM hDC hrank htM hne
    have hTC : TwoConj M X (S14110.cj t X) := ⟨hne, ⟨t, htM, rfl⟩, htwo⟩
    have hW' : A4Data (S14110.cj t X) (S14110.cj t W) (t * c * t⁻¹) := hA.map (MulAut.conj t)
    have hUn : M ≤ normalizer ((W ⊔ S14110.cj t W : Subgroup G) : Set G) :=
      hTC.le_normalizer_W_sup hA hW'
    have hW'T : S14110.cj t W ≤ T := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := S14110.mem_cj_iff.1 hy
      exact T.mul_mem (T.mul_mem htT (hWT hu)) (T.inv_mem htT)
    have hUT : W ⊔ S14110.cj t W ≤ T := sup_le hWT hW'T
    have hU1 : W ⊔ S14110.cj t W ≠ ⊥ := fun hb => hW1 (le_bot_iff.1 (hb ▸ le_sup_left))
    obtain ⟨z, hzU, hz1, hzZ⟩ :=
      exists_mem_omegaOneCenter_of_normalized h.sylow.1 hUT hU1 (hTM.trans hUn)
    have hXY : ∀ x ∈ X, ∀ y ∈ S14110.cj t X, x * y = y * x :=
      (hDC t htM).resolve_left hne
    have hWW' : ∀ a ∈ W, ∀ b ∈ S14110.cj t W, a * b = b * a := fun a ha b hb =>
      hXY a (hA.le ha) b (hW'.le hb)
    have hWW'1 : ∀ u ∈ W, u ∈ S14110.cj t W → u = 1 := fun u hu hu' =>
      hA.center u (hA.le hu) fun l hl => (hXY l hl u (hW'.le hu')).symm
    have hzset : z ∈ (W : Set G) * (S14110.cj t W : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right W (S14110.cj t W)
        (le_normalizer_of_comm hWW')]
      exact hzU
    obtain ⟨w, hw, w', hw', hzeq⟩ := hzset
    have hzeq' : w * w' = z := hzeq
    have hw1 : w ≠ 1 := by
      intro hw1
      rw [hw1, one_mul] at hzeq'
      have htz : t * w' * t⁻¹ = w' := by
        have := omegaOneCenter_comm T z hzZ t htT
        rw [← hzeq'] at this
        rw [this]; group
      have hcjtt : S14110.cj (t * t) X = X := by
        rcases htwo (t * t) (M.mul_mem htM htM) with h1 | h1
        · exact h1
        · exfalso
          apply hne
          have : S14110.cj t (S14110.cj t X) = S14110.cj t X := by
            rw [S14110.cj_cj]; exact h1
          exact S14110.cj_injective t this
      have hcjW : S14110.cj (t * t) W = W := hA.cj_W hA hcjtt
      have hw'W : t * w' * t⁻¹ ∈ W := by
        rw [← hcjW, S14110.cj_mul]
        exact S14110.conj_mem_cj hw'
      rw [htz] at hw'W
      have : w' = 1 := hWW'1 w' hw'W hw'
      apply hz1
      rw [← hzeq', this]
    have hgN' : g ∈ normalizer (S14110.cj t X : Set G) :=
      hX'.normalizes_of_odd hcharM hrank hg hodd
    have hgW : g ∈ normalizer (W : Set G) := hA.normalizer_le_normalizer_W hgN
    have hgW' : g ∈ normalizer (S14110.cj t W : Set G) := hW'.normalizer_le_normalizer_W hgN'
    have hgz : g * (w * w') * g⁻¹ = w * w' := by
      rw [hzeq']
      have := (mem_centralizer_iff.mp hgZ) z hzZ
      rw [← this]; group
    have hgw1 : g * w * g⁻¹ ∈ W := (mem_normalizer_iff.mp hgW w).mp hw
    have hgw2 : g * w' * g⁻¹ ∈ S14110.cj t W := (mem_normalizer_iff.mp hgW' w').mp hw'
    have hgwfix : g * w * g⁻¹ = w := by
      have hprod : (g * w * g⁻¹) * (g * w' * g⁻¹) = w * w' := by
        calc (g * w * g⁻¹) * (g * w' * g⁻¹) = g * (w * w') * g⁻¹ := by group
          _ = w * w' := hgz
      have h1 : w⁻¹ * (g * w * g⁻¹) = w' * (g * w' * g⁻¹)⁻¹ := by
        calc w⁻¹ * (g * w * g⁻¹)
            = w⁻¹ * ((g * w * g⁻¹) * (g * w' * g⁻¹)) * (g * w' * g⁻¹)⁻¹ := by group
          _ = w⁻¹ * (w * w') * (g * w' * g⁻¹)⁻¹ := by rw [hprod]
          _ = w' * (g * w' * g⁻¹)⁻¹ := by group
      have h2 : w⁻¹ * (g * w * g⁻¹) ∈ W := W.mul_mem (W.inv_mem hw) hgw1
      have h3 : w⁻¹ * (g * w * g⁻¹) ∈ S14110.cj t W := by
        rw [h1]
        exact (S14110.cj t W).mul_mem hw' ((S14110.cj t W).inv_mem hgw2)
      have h4 : w⁻¹ * (g * w * g⁻¹) = 1 := hWW'1 _ h2 h3
      calc g * w * g⁻¹ = w * (w⁻¹ * (g * w * g⁻¹)) := by group
        _ = w := by rw [h4]; group
    have hgwc : g * w = w * g := by
      calc g * w = (g * w * g⁻¹) * g := by group
        _ = w * g := by rw [hgwfix]
    exact hA.centralizes_of_odd_of_fixed hgN hodd hw hw1 hgwc

theorem exists_mul_blockCentralizer_of_mem_centralizer (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hCM : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M) :
    ∀ m ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      ∃ k ∈ blockCentralizer M, ∃ t ∈ T, m = k * t := by
  set N₀ : Subgroup G := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hN₀
  have hTN₀ : T ≤ N₀ := fun t ht => by
    rw [hN₀, Subgroup.mem_centralizer_iff]
    intro z hz
    exact (omegaOneCenter_comm T z hz t ht).symm
  have hNK : blockCentralizer M ⊓ N₀ ≤ N₀ := inf_le_right
  have hnormK : M ≤ normalizer (blockCentralizer M : Set G) := le_normalizer_blockCentralizer M
  have hN₀n : N₀ ≤ normalizer ((blockCentralizer M ⊓ N₀ : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hnormK (hCM hg), Subgroup.le_normalizer hg⟩
  have hodd : ∀ g ∈ N₀, Odd (orderOf g) → g ∈ blockCentralizer M ⊓ N₀ := by
    intro g hg hord
    refine ⟨mem_blockCentralizer.mpr ⟨hCM hg, fun X hX x hx => ?_⟩, hg⟩
    exact (hX.centralizes_of_odd h hM (hCM hg) hord hg x hx).symm
  intro m hm
  obtain ⟨n, hn, t, ht, rfl⟩ := exists_mul_of_odd_mem hNK hN₀n hTN₀
    (not_two_dvd_index_subgroupOf h.sylow hTN₀) hodd m hm
  exact ⟨n, hn.1, t, ht, rfl⟩

end Odd

end CFSG.Quasithin
