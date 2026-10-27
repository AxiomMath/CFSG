module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Quad
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4QuadTools
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Divides

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

namespace QuadSetup

variable {k m : ℕ} {F : Type} [Field F] [Finite F] {ut : V → Prop}

private theorem not_hasThirdFix_three_of_not_one [Finite H]
    (hM : MoufangCondition H Γ 4) (hW : WeissFree H Γ 4)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (W : ClosedGoodPath H Γ) (h1 : ¬ W.HasThirdFix (W.kernelAt 0) 1) :
    ¬ W.HasThirdFix (W.kernelAt 0) 3 := by
  intro hthree
  have hKW : W.kernelAt 0 ≤ W.stab := inf_le_right
  have h0 : W.HasThirdFix (W.kernelAt 0) 0 := by
    have hadj : Γ.Adj (W.x 0) (W.x (-1)) := by
      have h := W.adj (-1)
      rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
      exact h.symm
    obtain ⟨z, hzadj, hz1, hz2⟩ := h3 (W.x 0) (W.x (-1)) (W.x 1) hadj (W.adj 0)
    exact ⟨z, hzadj, by simpa using hz1, by simpa using hz2,
      fun g hg => (mem_fixingSubgroup_iff H).mp hg.1 z hzadj⟩
  have hrefl := W.hasThirdFix_reflect (n := 4) (by norm_num) hM hW hKW
    (i := 0) (j := 3) h0 hthree
  have hneg : W.HasThirdFix (W.kernelAt 0) (-3) := by simpa using hrefl
  have hadd := (W.hasThirdFix_add_iff (n := 4) (by norm_num) hM hW hKW (-3)).mp hneg
  exact h1 (by simpa using hadd)

private theorem not_hasThirdFix_two_of_odd_fix [Finite V] [Finite H]
    (hk : 2 ≤ k) (hm : 3 ≤ m) (hF : Nat.card F = (2 ^ k) ^ 2)
    (hS : QuadSetup H Γ k m F ut)
    {x₀ x₁ x₁' y : V} (h1 : Γ.Adj x₀ x₁) (h1' : Γ.Adj x₀ x₁')
    (h11 : x₁ ≠ x₁') (hy0 : y ≠ x₀) (hy1 : Γ.Adj x₁ y)
    {a : H} (haG1 : a ∈ fixingSubgroup H (Γ.neighborSet y))
    (ha0 : a • x₀ = x₀) (ha1 : a • x₁ = x₁) (ha1' : a • x₁' = x₁')
    (haOdd : Odd (orderOf a))
    (haTwo : ∀ z, Γ.Adj x₀ z → z ≠ x₁ → z ≠ x₁' → a • z ≠ z)
    (W : ClosedGoodPath H Γ) (htype : ut (W.x 0) ↔ ut y) :
    ¬ W.HasThirdFix (W.kernelAt 0) 2 := by
  classical
  have hLF := localFacts hk hm hF hS
  have hKle : Subgroup.zpowers a ≤
      MulAction.stabilizer H x₁' ⊓ MulAction.stabilizer H x₀ := by
    rw [Subgroup.zpowers_le, Subgroup.mem_inf]
    exact ⟨MulAction.mem_stabilizer_iff.mpr ha1', MulAction.mem_stabilizer_iff.mpr ha0⟩
  have hKodd : ∀ z, Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex
      (Subgroup.zpowers a)) := by
    intro z
    exact Odd.of_dvd_nat (by rw [Nat.card_zpowers]; exact haOdd)
      (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨u₄, hu₄adj, hu₄ne, hu₄fix⟩ :=
    (hLF x₁').oddFix x₀ h1'.symm (Subgroup.zpowers a) hKle (hKodd x₁')
  have hu₄a : a • u₄ = u₄ := hu₄fix a (Subgroup.mem_zpowers a)
  have hKle' : Subgroup.zpowers a ≤
      MulAction.stabilizer H u₄ ⊓ MulAction.stabilizer H x₁' := by
    rw [Subgroup.zpowers_le, Subgroup.mem_inf]
    exact ⟨MulAction.mem_stabilizer_iff.mpr hu₄a, MulAction.mem_stabilizer_iff.mpr ha1'⟩
  obtain ⟨u₅, hu₅adj, hu₅ne, hu₅fix⟩ :=
    (hLF u₄).oddFix x₁' hu₄adj.symm (Subgroup.zpowers a) hKle' (hKodd u₄)
  let p4 : GPath Γ 4 := path5 y x₁ x₀ x₁' u₄ hy1.symm h1.symm h1' hu₄adj
  have hp4nb : p4.NoBack :=
    path5_noBack hy1.symm h1.symm h1' hu₄adj hy0 h11 hu₄ne.symm
  let p : GPath Γ 5 := p4.snoc u₅ hu₅adj
  have hpnb : p.NoBack := GPath.noBack_snoc hp4nb hu₅adj (fun _ => hu₅ne)
  have hpv : p 0 = y ∧ p 1 = x₁ ∧ p 2 = x₀ ∧ p 3 = x₁' ∧
      p 4 = u₄ ∧ p 5 = u₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [p, p4, path5, GPath.snoc_of_le, GPath.snoc_last]
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5⟩ := hpv
  have haStabPath : a ∈ GPath.stabPath (H := H) p := by
    rw [GPath.mem_stabPath_iff]
    intro j hj
    interval_cases j
    · rw [hp0]
      exact MulAction.mem_stabilizer_iff.mp ((hLF y).kernel_le haG1)
    · rw [hp1]
      exact ha1
    · rw [hp2]
      exact ha0
    · rw [hp3]
      exact ha1'
    · rw [hp4]
      exact hu₄a
    · rw [hp5]
      exact hu₅fix a (Subgroup.mem_zpowers a)
  have haMem : a ∈ fixingSubgroup H (Γ.neighborSet (p 0)) ⊓ GPath.stabPath (H := H) p :=
    Subgroup.mem_inf.mpr ⟨by rwa [hp0], haStabPath⟩
  have hfix : ∀ z, Γ.Adj (p 2) z → z ≠ p (2 - 1) → z ≠ p (2 + 1) → a • z ≠ z := by
    intro z hz hz1 hz2
    refine haTwo z ?_ ?_ ?_
    · rwa [hp2] at hz
    · rwa [show (2 : ℕ) - 1 = 1 by norm_num, hp1] at hz1
    · rwa [hp3] at hz2
  have hW0 : ∃ h : H, h • p 0 = W.x 0 := by
    obtain ⟨g, hg⟩ := hS.conj y (W.x 0) htype.symm
    exact ⟨g, by rwa [hp0]⟩
  exact ClosedGoodPath.not_hasThirdFix_of_mem (n := 4) (by norm_num) hS.moufang hS.weissFree
    hS.ne hLF hS.loc hpnb (i := 2) (by norm_num) (by norm_num) haMem hfix W hW0

private theorem not_hasThirdFix_two_of_ut [Finite V] [Finite H]
    (hk : 2 ≤ k) (hm : 3 ≤ m) (hF : Nat.card F = (2 ^ k) ^ 2)
    (hS : QuadSetup H Γ k m F ut) (W : ClosedGoodPath H Γ) (hu : ut (W.x 0)) :
    ¬ W.HasThirdFix (W.kernelAt 0) 2 := by
  classical
  have hLF := localFacts hk hm hF hS
  have hRF := rootFacts hk hm hF hS
  have hx1L : ¬ ut (W.x 1) := (hS.adj (W.x 0) (W.x 1) (W.adj 0)).mp hu
  have hx1' : Γ.Adj (W.x 0) (W.x (-1)) := by simpa using (W.adj (-1)).symm
  have h11 : W.x 1 ≠ W.x (-1) := by simpa using (W.ne_add_two (-1)).symm
  have hUF₀ : UnitaryFacts H Γ (W.x 0) (2 ^ k) :=
    (vertexFacts_of_isLocalU3 hk F hF (hS.kernel_le (W.x 0)) (hS.u3 (W.x 0) hu)).2.2
  obtain ⟨t, htT, htNot⟩ := hUF₀.exists_pow (W.x 1) (W.x (-1)) (W.adj 0) hx1' h11
  have hC : ∀ g : H, CenterFacts H Γ (g • W.x 0) (2 ^ k + 1) := by
    intro g
    exact (vertexFacts_of_isLocalU3 hk F hF (hS.kernel_le (g • W.x 0))
      (isLocalU3_smul (hS.u3 (W.x 0) hu) g)).2.1
  have hsecond : secondKernel H Γ (W.x 0) ≠ ⊥ := secondKernel_ne_bot hk hF hS hu
  obtain ⟨y, hyadj, hyne, a, haG1y, haFix0, haFix1, haFix1', haOdd, haConj⟩ :=
    exists_odd_mem_fixingSubgroup_of_secondKernel_ne_bot (e := 2 ^ k + 1)
      hS.moufang hS.weissFree hS.ne hS.val hS.loc hLF hRF hC hsecond
      (W.adj 0) hx1' h11 htT
  have htStab : t ^ (2 ^ k + 1) ∈ MulAction.stabilizer H (W.x 0) :=
    Subgroup.pow_mem _
      (socleAt_le_stabilizer (hLF (W.x 0)).kernel_le
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htT)).1.1) _
  have haTwo : ∀ z, Γ.Adj (W.x 0) z → z ≠ W.x 1 → z ≠ W.x (-1) → a • z ≠ z := by
    intro z hz hz1 hz1' hfix
    have hkz : t ^ (2 ^ k + 1) • z = z := by
      have heq : a = (a * (t ^ (2 ^ k + 1))⁻¹) * t ^ (2 ^ k + 1) := by group
      have hkz_adj : Γ.Adj (W.x 0) (t ^ (2 ^ k + 1) • z) := by
        have h := (GraphAction.adj_smul (t ^ (2 ^ k + 1)) (W.x 0) z).mpr hz
        rwa [MulAction.mem_stabilizer_iff.mp htStab] at h
      have hfix' : (a * (t ^ (2 ^ k + 1))⁻¹) • (t ^ (2 ^ k + 1) • z) =
          t ^ (2 ^ k + 1) • z :=
        (mem_fixingSubgroup_iff H).mp haConj _ hkz_adj
      rw [heq, mul_smul] at hfix
      exact hfix'.symm.trans hfix
    rcases hUF₀.fix_two (W.x 1) (W.x (-1)) (W.adj 0) hx1' h11 (t ^ (2 ^ k + 1))
      (Subgroup.pow_mem _ htT _) htNot z hz hkz with h | h
    · exact hz1 h
    · exact hz1' h
  have hyU : ut y := by
    by_contra hy
    exact hx1L ((hS.adj (W.x 1) y hyadj).mpr hy)
  have htype : ut (W.x 0) ↔ ut y := ⟨fun _ => hyU, fun _ => hu⟩
  exact not_hasThirdFix_two_of_odd_fix hk hm hF hS (W.adj 0) hx1' h11 hyne hyadj
    haG1y haFix0 haFix1 haFix1' haOdd haTwo W htype

theorem not_hasThirdFix_of_ut [Finite V] [Finite H] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2) (hS : QuadSetup H Γ k m F ut) (W : ClosedGoodPath H Γ)
    (hu : ut (W.x 0)) {i : ℤ} (hi0 : 0 < i) (hi4 : i < 4) :
    ¬ W.HasThirdFix (W.kernelAt 0) i := by
  classical
  have hLF := localFacts hk hm hF hS
  have hx1L : ¬ ut (W.x 1) := (hS.adj (W.x 0) (W.x 1) (W.adj 0)).mp hu
  have h2 : ¬ W.HasThirdFix (W.kernelAt 0) 2 := not_hasThirdFix_two_of_ut hk hm hF hS W hu
  have h1 : ¬ W.HasThirdFix (W.kernelAt 0) 1 := by
    intro hF1
    have hZ1 : ZassenhausFacts H Γ (W.x 1) :=
      (vertexFacts_of_isLocalL2 (by omega : 2 ≤ m) (hS.kernel_le (W.x 1))
        (hS.l2 (W.x 1) hx1L)).2.1
    have hKG : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x 1)) :=
      (W.hasThirdFix_iff_le (n := 4) (by norm_num) hS.weissFree hLF hS.three 0 1 hZ1).mp hF1
    have hbot : W.kernelAt 0 = ⊥ :=
      W.kernelAt_eq_bot_of_le_succ (n := 4) hS.weissFree 0 (by simpa using hKG)
    have hthird : W.HasThirdFix (⊥ : Subgroup H) 2 := by
      obtain ⟨z, hzadj, hz1, hz2⟩ := hS.three (W.x 2) (W.x 1) (W.x 3)
        (W.adj 1).symm (W.adj 2)
      exact ⟨z, hzadj, hz1, hz2, fun g hg => by
        rw [Subgroup.mem_bot.mp hg, one_smul]⟩
    rw [← hbot] at hthird
    exact h2 hthird
  have h3 : ¬ W.HasThirdFix (W.kernelAt 0) 3 :=
    not_hasThirdFix_three_of_not_one hS.moufang hS.weissFree hS.three W h1
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

private theorem exists_zpow_mul_of_mem_sup {F : Subgroup H} {g x : H}
    (hgn : g ∈ Subgroup.normalizer (F : Set H))
    (hx : x ∈ Subgroup.zpowers g ⊔ F) :
    ∃ i : ℤ, ∃ f ∈ F, x = g ^ i * f := by
  have hnorm : Subgroup.zpowers g ≤ Subgroup.normalizer (F : Set H) :=
    Subgroup.zpowers_le.mpr hgn
  have hx' : x ∈ (↑(Subgroup.zpowers g) * ↑F : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact hx
  obtain ⟨p, hp, f, hf, hpf⟩ := hx'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp
  exact ⟨i, f, hf, by rw [← hpf, ← hi]⟩

private theorem pow_mul_eq_zpow_mul_pow {F : Subgroup H} {g : H}
    (hgn : g ∈ Subgroup.normalizer (F : Set H)) {f : H} (hf : f ∈ F) (i : ℤ) (n : ℕ) :
    ∃ f' ∈ F, (g ^ i * f) ^ n = g ^ (i * n) * f' := by
  induction n with
  | zero => exact ⟨1, F.one_mem, by simp⟩
  | succ n ih =>
      obtain ⟨f', hf', ih'⟩ := ih
      have hconj : g ^ (-i) * f' * g ^ i ∈ F := by
        have hinv : g ^ (-i) ∈ Subgroup.normalizer (F : Set H) := by
          simpa using Subgroup.inv_mem _ (Subgroup.zpow_mem _ hgn i)
        simpa using (Subgroup.mem_normalizer_iff.mp hinv f').mp hf'
      refine ⟨(g ^ (-i) * f' * g ^ i) * f, F.mul_mem hconj hf, ?_⟩
      rw [pow_succ, ih']
      rw [show i * ((n + 1 : ℕ) : ℤ) = i * (n : ℤ) + i by push_cast; ring, zpow_add]
      group

private theorem pow_mul_mem_of_le_zpowers_sup {F : Subgroup H} {g : H}
    (hgn : g ∈ Subgroup.normalizer (F : Set H)) {a b : H} {n : ℕ}
    (ha : a ∈ Subgroup.zpowers g ⊔ F) (hb : b ∈ Subgroup.zpowers g ⊔ F)
    (han : a ^ n ∈ F) (hbn : b ^ n ∈ F) : (a * b) ^ n ∈ F := by
  obtain ⟨i, f, hf, rfl⟩ := exists_zpow_mul_of_mem_sup hgn ha
  obtain ⟨j, f', hf', rfl⟩ := exists_zpow_mul_of_mem_sup hgn hb
  obtain ⟨f₁, hf₁, h₁⟩ := pow_mul_eq_zpow_mul_pow hgn hf i n
  obtain ⟨f₂, hf₂, h₂⟩ := pow_mul_eq_zpow_mul_pow hgn hf' j n
  have hgin : g ^ (i * n) ∈ F := by
    have hmem : g ^ (i * n) * f₁ ∈ F := by rwa [h₁] at han
    have heq : g ^ (i * n) = (g ^ (i * n) * f₁) * f₁⁻¹ := by group
    rw [heq]
    exact F.mul_mem hmem (F.inv_mem hf₁)
  have hgjn : g ^ (j * n) ∈ F := by
    have hmem : g ^ (j * n) * f₂ ∈ F := by rwa [h₂] at hbn
    have heq : g ^ (j * n) = (g ^ (j * n) * f₂) * f₂⁻¹ := by group
    rw [heq]
    exact F.mul_mem hmem (F.inv_mem hf₂)
  have hconj : g ^ (-j) * f * g ^ j ∈ F := by
    have hinv : g ^ (-j) ∈ Subgroup.normalizer (F : Set H) := by
      simpa using Subgroup.inv_mem _ (Subgroup.zpow_mem _ hgn j)
    simpa using (Subgroup.mem_normalizer_iff.mp hinv f).mp hf
  have hA : (g ^ (-j) * f * g ^ j) * f' ∈ F := F.mul_mem hconj hf'
  have hab : (g ^ i * f) * (g ^ j * f') =
      g ^ (i + j) * ((g ^ (-j) * f * g ^ j) * f') := by
    rw [zpow_add]
    group
  obtain ⟨f₃, hf₃, h₃⟩ := pow_mul_eq_zpow_mul_pow hgn hA (i + j) n
  have hsum : g ^ ((i + j) * n) ∈ F := by
    rw [show (i + j) * (n : ℤ) = i * (n : ℤ) + j * (n : ℤ) by ring, zpow_add]
    exact F.mul_mem hgin hgjn
  rw [hab, h₃]
  exact F.mul_mem hsum hf₃

private theorem conj_mem_zpowers_sup_of_mem_zpowers_sup {F : Subgroup H} {g : H}
    (hgn : g ∈ Subgroup.normalizer (F : Set H)) {t c : H}
    (ht : t ∈ Subgroup.zpowers g ⊔ F) (hc : c ∈ Subgroup.zpowers g ⊔ F) :
    t * c * t⁻¹ ∈ Subgroup.zpowers c ⊔ F := by
  obtain ⟨i, f, hf, rfl⟩ := exists_zpow_mul_of_mem_sup hgn ht
  obtain ⟨j, f', hf', rfl⟩ := exists_zpow_mul_of_mem_sup hgn hc
  have hconj₁ : g ^ (-j) * f * g ^ j ∈ F := by
    have hinv : g ^ (-j) ∈ Subgroup.normalizer (F : Set H) := by
      simpa using Subgroup.inv_mem _ (Subgroup.zpow_mem _ hgn j)
    simpa using (Subgroup.mem_normalizer_iff.mp hinv f).mp hf
  have hconj₂ : g ^ (-i) * f' * g ^ i ∈ F := by
    have hinv : g ^ (-i) ∈ Subgroup.normalizer (F : Set H) := by
      simpa using Subgroup.inv_mem _ (Subgroup.zpow_mem _ hgn i)
    simpa using (Subgroup.mem_normalizer_iff.mp hinv f').mp hf'
  have hA : (g ^ (-j) * f * g ^ j) * f' ∈ F := F.mul_mem hconj₁ hf'
  have hB : (g ^ (-i) * f' * g ^ i) * f ∈ F := F.mul_mem hconj₂ hf
  have h1 : (g ^ i * f) * (g ^ j * f') =
      g ^ (i + j) * ((g ^ (-j) * f * g ^ j) * f') := by
    rw [zpow_add]
    group
  have h2 : (g ^ j * f') * (g ^ i * f) =
      g ^ (i + j) * ((g ^ (-i) * f' * g ^ i) * f) := by
    rw [show i + j = j + i by ring, zpow_add]
    group
  have hcomm : (g ^ i * f) * (g ^ j * f') * (g ^ i * f)⁻¹ * (g ^ j * f')⁻¹ ∈ F := by
    have hify : (g ^ i * f) * (g ^ j * f') * (g ^ i * f)⁻¹ * (g ^ j * f')⁻¹ =
        (g ^ (i + j) * ((g ^ (-j) * f * g ^ j) * f')) *
          (g ^ (i + j) * ((g ^ (-i) * f' * g ^ i) * f))⁻¹ := by
      have hsplit : (g ^ i * f) * (g ^ j * f') * (g ^ i * f)⁻¹ * (g ^ j * f')⁻¹ =
          ((g ^ i * f) * (g ^ j * f')) * ((g ^ j * f') * (g ^ i * f))⁻¹ := by
        group
      rw [hsplit, h1, h2]
    rw [hify]
    have hnorm : g ^ (i + j) ∈ Subgroup.normalizer (F : Set H) :=
      Subgroup.zpow_mem _ hgn (i + j)
    have heq : (g ^ (i + j) * ((g ^ (-j) * f * g ^ j) * f')) *
        (g ^ (i + j) * ((g ^ (-i) * f' * g ^ i) * f))⁻¹ =
        g ^ (i + j) * (((g ^ (-j) * f * g ^ j) * f') *
          ((g ^ (-i) * f' * g ^ i) * f)⁻¹) * (g ^ (i + j))⁻¹ := by group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp (F.mul_mem hA (F.inv_mem hB))
  have he : (g ^ i * f) * (g ^ j * f') * (g ^ i * f)⁻¹ =
      ((g ^ i * f) * (g ^ j * f') * (g ^ i * f)⁻¹ * (g ^ j * f')⁻¹) * (g ^ j * f') := by
    group
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem not_hasThirdFix_of_not_ut [Finite V] [Finite H] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2) (hS : QuadSetup H Γ k m F ut) (W : ClosedGoodPath H Γ)
    (hu : ¬ ut (W.x 0)) {i : ℤ} (hi0 : 0 < i) (hi4 : i < 4) :
    ¬ W.HasThirdFix (W.kernelAt 0) i := by
  classical
  have hLF := localFacts hk hm hF hS
  have hRF := rootFacts hk hm hF hS
  have hx1U : ut (W.x 1) := by
    by_contra h
    exact hu ((hS.adj (W.x 0) (W.x 1) (W.adj 0)).mpr h)
  have hx2L : ¬ ut (W.x 2) := (hS.adj (W.x 1) (W.x 2) (W.adj 1)).mp hx1U
  have hx0x1' : Γ.Adj (W.x 0) (W.x (-1)) := by simpa using (W.adj (-1)).symm
  have h11 : W.x 1 ≠ W.x (-1) := by simpa using (W.ne_add_two (-1)).symm
  let W₀ : ClosedGoodPath H Γ := W.shift 1
  have hW₀0 : W₀.x 0 = W.x 1 := by simp [W₀]
  have hW₀1 : W₀.x 1 = W.x 2 := by show W.x (1 + 1) = W.x 2; norm_num
  have hu₀ : ut (W₀.x 0) := by rw [hW₀0]; exact hx1U
  obtain ⟨m₀, hm₀K, hm₀Soc, hm₀Pow, hm₀Not⟩ := exists_mem_kernelAt hk hm hF hS W₀ hu₀
  have hm₀fix : ∀ j : ℤ, m₀ • W₀.x j = W₀.x j := ClosedGoodPath.mem_stab_iff.mp hm₀K.2
  have hm₀fix1 : m₀ • W₀.x 1 = W₀.x 1 := hm₀fix 1
  have hex : ∃ h ∈ W₀.kernelAt 0, h ∈ socleAt H Γ (W₀.x 1) ∧
      h ∈ socleAt H Γ (W₀.x 2) ∧
      h ^ (2 ^ k - 1) ∈ fixingSubgroup H (Γ.neighborSet (W₀.x 2)) ∧
      h ∉ fixingSubgroup H (Γ.neighborSet (W₀.x 2)) := by
    by_cases hm₁ : m₀ ∈ socleAt H Γ (W₀.x 1)
    · exact ⟨m₀, hm₀K, hm₁, hm₀Soc, hm₀Pow, hm₀Not⟩
    · have hz1L : ¬ ut (W₀.x 1) := by rw [hW₀1]; exact hx2L
      have hZ1 : ZassenhausFacts H Γ (W₀.x 1) :=
        (vertexFacts_of_isLocalL2 (by omega : 2 ≤ m) (hS.kernel_le (W₀.x 1))
          (hS.l2 (W₀.x 1) hz1L)).2.1
      have htriple : m₀ ∈ MulAction.stabilizer H (W₀.x 1) ⊓
          MulAction.stabilizer H (W₀.x 0) ⊓ MulAction.stabilizer H (W₀.x 2) := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
        · exact MulAction.mem_stabilizer_iff.mpr (hm₀fix 1)
        · exact MulAction.mem_stabilizer_iff.mpr (hm₀fix 0)
        · exact MulAction.mem_stabilizer_iff.mpr (hm₀fix 2)
      have hexcomm : ∃ t ∈ socTorus H Γ (W₀.x 1) (W₀.x 0) (W₀.x 2),
          m₀ * t * m₀⁻¹ * t⁻¹ ∉ fixingSubgroup H (Γ.neighborSet (W₀.x 1)) := by
        by_contra h
        push Not at h
        exact hm₁ (hZ1.centralizer_le (W₀.x 0) (W₀.x 2) (W₀.adj 0).symm (W₀.adj 1)
          (W₀.ne_add_two 0) m₀ htriple h)
      obtain ⟨t, htT, htcomm⟩ := hexcomm
      have hgood : socTorus H Γ (W₀.x 1) (W₀.x 0) (W₀.x 2) ≤
          (W₀.stab ⊓ socleAt H Γ (W₀.x 1)) ⊔
            fixingSubgroup H (Γ.neighborSet (W₀.x 1)) := by
        have hgp : IsGoodPath H (W₀.window 0 5) :=
          W₀.good 0 5 (W₀.window 0 5) (fun j hj => ClosedGoodPath.window_apply W₀ 0 hj)
        have h := hgp.2 1 (by norm_num) (by norm_num)
        have h0 : W₀.window 0 5 0 = W₀.x 0 := by
          rw [ClosedGoodPath.window_apply W₀ 0 (by norm_num)]; norm_num
        have h1 : W₀.window 0 5 1 = W₀.x 1 := by
          rw [ClosedGoodPath.window_apply W₀ 0 (by norm_num)]; norm_num
        have h2 : W₀.window 0 5 2 = W₀.x 2 := by
          rw [ClosedGoodPath.window_apply W₀ 0 (by norm_num)]; norm_num
        have hstab : GPath.stabPath (H := H) (W₀.window 0 5) = W₀.stab :=
          ClosedGoodPath.stabPath_window (n := 4) (by norm_num) hS.weissFree hLF W₀ 0
        rw [h0, h1, h2, hstab] at h
        exact h
      let F₁ : Subgroup H := fixingSubgroup H (Γ.neighborSet (W₀.x 1))
      let A : Subgroup H := W₀.stab ⊓ socleAt H Γ (W₀.x 1)
      have hAnorm : A ≤ Subgroup.normalizer (F₁ : Set H) :=
        (inf_le_right.trans (socleAt_le_stabilizer (hLF (W₀.x 1)).kernel_le)).trans
          stabilizer_le_normalizer_fixingSubgroup
      have htmem : t ∈ (↑(A ⊔ F₁) : Set H) := hgood htT
      rw [Subgroup.coe_mul_of_left_le_normalizer_right A F₁ hAnorm] at htmem
      obtain ⟨g, hgA, kf, hkF, hgk⟩ := htmem
      have hgstab : g ∈ W₀.stab := hgA.1
      have hgsoc : g ∈ socleAt H Γ (W₀.x 1) := hgA.2
      have hgfix : ∀ j : ℤ, g • W₀.x j = W₀.x j := ClosedGoodPath.mem_stab_iff.mp hgstab
      let c : H := g * m₀ * g⁻¹ * m₀⁻¹
      have hcK : c ∈ W₀.kernelAt 0 := by
        have hgm : g * m₀ * g⁻¹ ∈ W₀.kernelAt 0 := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h := conj_mem_fixingSubgroup_neighborSet (Γ := Γ) g m₀ (W₀.x 0) hm₀K.1
            rwa [hgfix 0] at h
          · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgstab hm₀K.2)
              (Subgroup.inv_mem _ hgstab)
        have := Subgroup.mul_mem _ hgm (Subgroup.inv_mem _ hm₀K)
        simpa [c] using this
      have hc1soc : c ∈ socleAt H Γ (W₀.x 1) := by
        have hconj : m₀ * g⁻¹ * m₀⁻¹ ∈ socleAt H Γ (W₀.x 1) :=
          conj_mem_socleAt hm₀fix1 (Subgroup.inv_mem _ hgsoc)
        have := Subgroup.mul_mem _ hgsoc hconj
        simpa [c, mul_assoc] using this
      have hgm₀g_soc : g * m₀ * g⁻¹ ∈ socleAt H Γ (W₀.x 2) :=
        conj_mem_socleAt (hgfix 2) hm₀Soc
      have hc2soc : c ∈ socleAt H Γ (W₀.x 2) := by
        have := Subgroup.mul_mem _ hgm₀g_soc (Subgroup.inv_mem _ hm₀Soc)
        simpa [c] using this
      have hc1not : c ∉ F₁ := by
        intro hcF
        have hmk : m₀ * kf * m₀⁻¹ * kf⁻¹ ∈ F₁ := by
          have h1 : m₀ * kf * m₀⁻¹ ∈ F₁ := by
            have h := conj_mem_fixingSubgroup_neighborSet (Γ := Γ) m₀ kf (W₀.x 1) hkF
            rwa [hm₀fix1] at h
          exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hkF)
        have hconjF : g * (m₀ * kf * m₀⁻¹ * kf⁻¹) * g⁻¹ ∈ F₁ := by
          have h := conj_mem_fixingSubgroup_neighborSet (Γ := Γ) g
            (m₀ * kf * m₀⁻¹ * kf⁻¹) (W₀.x 1) hmk
          rwa [hgfix 1] at h
        have hprod : c * (m₀ * t * m₀⁻¹ * t⁻¹) ∈ F₁ := by
          have heq : c * (m₀ * t * m₀⁻¹ * t⁻¹) =
              g * (m₀ * kf * m₀⁻¹ * kf⁻¹) * g⁻¹ := by
            rw [show t = g * kf from hgk.symm]
            simp only [c]
            group
          rw [heq]
          exact hconjF
        have hmem : m₀ * t * m₀⁻¹ * t⁻¹ ∈ F₁ := by
          have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hcF) hprod
          have heq : c⁻¹ * (c * (m₀ * t * m₀⁻¹ * t⁻¹)) = m₀ * t * m₀⁻¹ * t⁻¹ := by
            group
          rwa [heq] at h
        exact htcomm hmem
      have hb₀data := (hLF (W₀.x 2)).torusGen (W₀.x 1) (W₀.x 3)
        (W₀.adj 1).symm (W₀.adj 2) (W₀.ne_add_two 1)
        (socTorus H Γ (W₀.x 2) (W₀.x 1) (W₀.x 3)) le_rfl le_sup_left
      obtain ⟨b₀, hb₀T, -, hb₀gen0⟩ := hb₀data
      have hb₀gen : socTorus H Γ (W₀.x 2) (W₀.x 1) (W₀.x 3) ≤
          Subgroup.zpowers b₀ ⊔ fixingSubgroup H (Γ.neighborSet (W₀.x 2)) := by
        rw [Subgroup.zpowers_eq_closure]
        exact hb₀gen0
      have hb₀norm : b₀ ∈ Subgroup.normalizer
          (fixingSubgroup H (Γ.neighborSet (W₀.x 2)) : Set H) :=
        stabilizer_le_normalizer_fixingSubgroup
          (socleAt_le_stabilizer (hLF (W₀.x 2)).kernel_le
            (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb₀T)).1.1)
      have haT : g * m₀ * g⁻¹ ∈ socTorus H Γ (W₀.x 2) (W₀.x 1) (W₀.x 3) := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgm₀g_soc, ?_⟩, ?_⟩
        · rw [MulAction.mem_stabilizer_iff]
          have hginv : g⁻¹ • W₀.x 1 = W₀.x 1 := by
            have h := congrArg (fun v => g⁻¹ • v) (hgfix 1)
            simpa using h.symm
          calc (g * m₀ * g⁻¹) • W₀.x 1 = g • (m₀ • (g⁻¹ • W₀.x 1)) := by
                rw [mul_smul, mul_smul]
            _ = g • (m₀ • W₀.x 1) := by rw [hginv]
            _ = g • W₀.x 1 := by rw [hm₀fix1]
            _ = W₀.x 1 := hgfix 1
        · rw [MulAction.mem_stabilizer_iff]
          have hginv : g⁻¹ • W₀.x 3 = W₀.x 3 := by
            have h := congrArg (fun v => g⁻¹ • v) (hgfix 3)
            simpa using h.symm
          calc (g * m₀ * g⁻¹) • W₀.x 3 = g • (m₀ • (g⁻¹ • W₀.x 3)) := by
                rw [mul_smul, mul_smul]
            _ = g • (m₀ • W₀.x 3) := by rw [hginv]
            _ = g • W₀.x 3 := by rw [hm₀fix 3]
            _ = W₀.x 3 := hgfix 3
      have hbT : m₀⁻¹ ∈ socTorus H Γ (W₀.x 2) (W₀.x 1) (W₀.x 3) := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.inv_mem _ hm₀Soc, ?_⟩, ?_⟩
        · rw [MulAction.mem_stabilizer_iff]
          exact (MulAction.stabilizer H (W₀.x 1)).inv_mem
            (MulAction.mem_stabilizer_iff.mpr (hm₀fix 1))
        · rw [MulAction.mem_stabilizer_iff]
          exact (MulAction.stabilizer H (W₀.x 3)).inv_mem
            (MulAction.mem_stabilizer_iff.mpr (hm₀fix 3))
      have haPow : (g * m₀ * g⁻¹) ^ (2 ^ k - 1) ∈
          fixingSubgroup H (Γ.neighborSet (W₀.x 2)) := by
        have h := conj_mem_fixingSubgroup_neighborSet (Γ := Γ) g (m₀ ^ (2 ^ k - 1)) (W₀.x 2)
          hm₀Pow
        rw [hgfix 2] at h
        have heq : (g * m₀ * g⁻¹) ^ (2 ^ k - 1) = g * m₀ ^ (2 ^ k - 1) * g⁻¹ := by
          rw [show g * m₀ * g⁻¹ = (MulAut.conj g) m₀ by simp [MulAut.conj_apply],
            ← map_pow]
          simp [MulAut.conj_apply]
        rw [heq]
        exact h
      have hbPow : (m₀⁻¹) ^ (2 ^ k - 1) ∈
          fixingSubgroup H (Γ.neighborSet (W₀.x 2)) := by
        rw [inv_pow]
        exact (fixingSubgroup H (Γ.neighborSet (W₀.x 2))).inv_mem hm₀Pow
      have hcPow : c ^ (2 ^ k - 1) ∈ fixingSubgroup H (Γ.neighborSet (W₀.x 2)) := by
        have h := pow_mul_mem_of_le_zpowers_sup hb₀norm (hb₀gen haT) (hb₀gen hbT) haPow hbPow
        simpa [c] using h
      have hnc : ∀ q : GPath Γ 4, q.NoBack → q 4 = W₀.x 0 →
          ∃ a ∈ pathRootGroup H Γ q, ∃ b ∈ pathRootGroup H Γ q, a * b ≠ b * a := by
        intro q hq hq4
        exact exists_not_comm_pathRootGroup_of_isLocalU3 (n := 4) (by norm_num)
          hS.moufang hS.weissFree hS.ne hS.val hS.kernel_le hk F hF hq
          (by rw [hq4]; exact hS.u3 (W₀.x 0) hu₀)
      have hc2not : c ∉ fixingSubgroup H (Γ.neighborSet (W₀.x 2)) := by
        intro hc2F
        exact ClosedGoodPath.false_of_mem_socleAt hS.moufang hS.weissFree hS.ne hS.three
          hS.val hLF hRF W₀ hZ1 hnc hcK hc2F hc1soc hc1not
      exact ⟨c, hcK, hc1soc, hc2soc, hcPow, hc2not⟩
  have h1 : ¬ W.HasThirdFix (W.kernelAt 0) 1 := by
    intro hF1
    obtain ⟨h, hhK, hh1soc, hh2soc, hhq, hhn⟩ := hex
    obtain ⟨p, g₁, hpnb, hp0, hgmem, hgfix⟩ :=
      exists_twoFix_of_claimA hk hm hF hS W₀ hu₀ hhK hh1soc hh2soc hhq hhn
    have htype : ut (W.x 0) ↔ ut (W₀.x 1) := by
      rw [hW₀1]
      exact ⟨fun h => (hu h).elim, fun h => (hx2L h).elim⟩
    have hW0 : ∃ h : H, h • p 0 = W.x 0 := by
      obtain ⟨g₂, hg₂⟩ := hS.conj (W₀.x 1) (W.x 0) htype.symm
      exact ⟨g₂, by rwa [hp0]⟩
    have hfix1 : ∀ z, Γ.Adj (p 1) z → z ≠ p (1 - 1) → z ≠ p (1 + 1) → g₁ • z ≠ z := by
      intro z hz hz1 hz2
      exact hgfix z hz (by simpa using hz1) (by simpa using hz2)
    exact (ClosedGoodPath.not_hasThirdFix_of_mem (n := 4) (by norm_num) hS.moufang
      hS.weissFree hS.ne hLF hS.loc hpnb (i := 1) (by norm_num) (by norm_num) hgmem hfix1
      W hW0) hF1
  have h3 : ¬ W.HasThirdFix (W.kernelAt 0) 3 :=
    not_hasThirdFix_three_of_not_one hS.moufang hS.weissFree hS.three W h1
  have h2 : ¬ W.HasThirdFix (W.kernelAt 0) 2 := by
    intro hF2
    have hZ2 : ZassenhausFacts H Γ (W.x 2) :=
      (vertexFacts_of_isLocalL2 (by omega : 2 ≤ m) (hS.kernel_le (W.x 2))
        (hS.l2 (W.x 2) hx2L)).2.1
    have hKG : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x 2)) :=
      (W.hasThirdFix_iff_le (n := 4) (by norm_num) hS.weissFree hLF hS.three 0 2 hZ2).mp hF2
    have hsecond : secondKernel H Γ (W.x 0) ≠ ⊥ :=
      W.secondKernel_ne_bot_of_le hS.moufang hS.weissFree hS.three h3 hKG
    have htorus : ∃ t ∈ socTorus H Γ (W.x 0) (W.x 1) (W.x (-1)),
        t ∉ fixingSubgroup H (Γ.neighborSet (W.x 0)) := by
      by_contra h
      push Not at h
      obtain ⟨u, huadj, hu1, hu2⟩ := hS.three (W.x 0) (W.x 1) (W.x (-1))
        (W.adj 0) hx0x1'
      have hfixu : ∀ t ∈ socTorus H Γ (W.x 0) (W.x 1) (W.x (-1)), t • u = u :=
        fun t ht => (mem_fixingSubgroup_iff H).mp (h t ht) u huadj
      rcases (hLF (W.x 0)).torusFix (W.x 1) (W.x (-1)) u (W.adj 0) hx0x1' h11 huadj
        hfixu with h1 | h1
      · exact hu1 h1
      · exact hu2 h1
    obtain ⟨t, htT, htNot⟩ := htorus
    have hC : ∀ g : H, CenterFacts H Γ (g • W.x 0) 1 := by
      intro g
      exact (vertexFacts_of_isLocalL2 (by omega : 2 ≤ m) (hS.kernel_le (g • W.x 0))
        (isLocalL2_smul (hS.l2 (W.x 0) hu) g)).2.2.1
    obtain ⟨x₂, hx₂adj, hx₂ne, a, haG1, ha0, ha1, ha1', haOdd, haConj⟩ :=
      exists_odd_mem_fixingSubgroup_of_secondKernel_ne_bot (e := 1)
        hS.moufang hS.weissFree hS.ne hS.val hS.loc hLF hRF hC hsecond
        (W.adj 0) hx0x1' h11 htT
    have haConj' : a * t⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x 0)) := by
      simpa using haConj
    have htStab : t ∈ MulAction.stabilizer H (W.x 0) :=
      socleAt_le_stabilizer (hLF (W.x 0)).kernel_le
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htT)).1.1
    have haTwo : ∀ z, Γ.Adj (W.x 0) z → z ≠ W.x 1 → z ≠ W.x (-1) → a • z ≠ z := by
      intro z hz hz1 hz2 hfix
      have hkz : t • z = z := by
        have heq : a = (a * t⁻¹) * t := by group
        have hkz_adj : Γ.Adj (W.x 0) (t • z) := by
          have h := (GraphAction.adj_smul t (W.x 0) z).mpr hz
          rwa [MulAction.mem_stabilizer_iff.mp htStab] at h
        have hfix' : (a * t⁻¹) • (t • z) = t • z :=
          (mem_fixingSubgroup_iff H).mp haConj' _ hkz_adj
        rw [heq, mul_smul] at hfix
        exact hfix'.symm.trans hfix
      obtain ⟨b₀, hb₀T, -, hb₀gen0⟩ := (hLF (W.x 0)).torusGen (W.x 1) (W.x (-1))
        (W.adj 0) hx0x1' h11 (socTorus H Γ (W.x 0) (W.x 1) (W.x (-1))) le_rfl le_sup_left
      have hb₀gen : socTorus H Γ (W.x 0) (W.x 1) (W.x (-1)) ≤
          Subgroup.zpowers b₀ ⊔ fixingSubgroup H (Γ.neighborSet (W.x 0)) := by
        rw [Subgroup.zpowers_eq_closure]
        exact hb₀gen0
      have hb₀norm : b₀ ∈ Subgroup.normalizer
          (fixingSubgroup H (Γ.neighborSet (W.x 0)) : Set H) :=
        stabilizer_le_normalizer_fixingSubgroup
          (socleAt_le_stabilizer (hLF (W.x 0)).kernel_le
            (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb₀T)).1.1)
      have hnorm : ∀ s ∈ socTorus H Γ (W.x 0) (W.x 1) (W.x (-1)),
          ∀ m ∈ Subgroup.zpowers t, s * m * s⁻¹ ∈
            Subgroup.zpowers t ⊔ fixingSubgroup H (Γ.neighborSet (W.x 0)) := by
        intro s hs m hm
        have h := conj_mem_zpowers_sup_of_mem_zpowers_sup hb₀norm (hb₀gen hs)
          ((Subgroup.zpowers_le.mpr (hb₀gen htT)) hm)
        exact (sup_le_sup (Subgroup.zpowers_le.mpr hm) le_rfl) h
      have hMle : Subgroup.zpowers t ≤ MulAction.stabilizer H (W.x 0) ⊓
          MulAction.stabilizer H (W.x 1) ⊓ MulAction.stabilizer H (W.x (-1)) := by
        refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩)
        · rw [MulAction.mem_stabilizer_iff]
          exact htStab
        · rw [MulAction.mem_stabilizer_iff]
          exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp
            (Subgroup.mem_inf.mp htT)).1.2
        · rw [MulAction.mem_stabilizer_iff]
          exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp htT).2
      have hone : ∀ u, Γ.Adj (W.x 0) u →
          (∀ m ∈ Subgroup.zpowers t, m • u = u) → u = W.x 1 ∨ u = W.x (-1) := by
        have hZ0 : ZassenhausFacts H Γ (W.x 0) :=
          (vertexFacts_of_isLocalL2 (by omega : 2 ≤ m) (hS.kernel_le (W.x 0))
            (hS.l2 (W.x 0) hu)).2.1
        rcases hZ0.dichotomy (W.x 1) (W.x (-1)) (W.adj 0) hx0x1' h11
          (Subgroup.zpowers t) hMle hnorm with hle | hfix
        · exact absurd (hle (Subgroup.mem_zpowers t)) htNot
        · exact hfix
      rcases hone z hz (fun m hm => smul_eq_self_of_mem_zpowers hm hkz) with h | h
      · exact hz1 h
      · exact hz2 h
    have hyL : ¬ ut x₂ := (hS.adj (W.x 1) x₂ hx₂adj).mp hx1U
    have htype : ut (W.x 0) ↔ ut x₂ := ⟨fun h => (hu h).elim, fun h => (hyL h).elim⟩
    exact (not_hasThirdFix_two_of_odd_fix hk hm hF hS (W.adj 0) hx0x1' h11 hx₂ne hx₂adj
      haG1 ha0 ha1 ha1' haOdd haTwo W htype) hF2
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem weissLemma4' [Finite V] [Finite H] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2) (hS : QuadSetup H Γ k m F ut) :
    WeissLemma4' H Γ 4 := by
  classical
  have hLF := localFacts hk hm hF hS
  intro w hw j hj0 hj4 z hzad hj1 hj2
  obtain ⟨W, hW⟩ := ClosedGoodPath.exists_of_noBack (n := 4) (by norm_num) hS.moufang
    hS.weissFree hS.ne hLF hw
  have hwin : W.window 0 5 = w := by
    apply GPath.ext'
    intro t ht
    rw [ClosedGoodPath.window_apply W 0 ht, zero_add]
    exact hW t ht
  have hstab : GPath.stabPath (H := H) w = W.stab := by
    rw [← hwin]
    exact ClosedGoodPath.stabPath_window (n := 4) (by norm_num) hS.weissFree hLF W 0
  have hW0 : W.x 0 = w 0 := hW 0 (by norm_num)
  have hker : W.kernelAt 0 = fixingSubgroup H (Γ.neighborSet (w 0)) ⊓
      GPath.stabPath (H := H) w := by
    rw [ClosedGoodPath.kernelAt, hW0, hstab]
  have hWi : W.x (j : ℤ) = w j := hW j (by omega)
  have hWim1 : W.x ((j : ℤ) - 1) = w (j - 1) := by
    rw [show (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) by omega]
    exact hW (j - 1) (by omega)
  have hWip1 : W.x ((j : ℤ) + 1) = w (j + 1) := by
    rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega]
    exact hW (j + 1) (by omega)
  have hno : ¬ W.HasThirdFix (W.kernelAt 0) (j : ℤ) := by
    by_cases hU : ut (W.x 0)
    · exact not_hasThirdFix_of_ut hk hm hF hS W hU (by exact_mod_cast hj0)
        (by exact_mod_cast hj4)
    · exact not_hasThirdFix_of_not_ut hk hm hF hS W hU (by exact_mod_cast hj0)
        (by exact_mod_cast hj4)
  by_contra hcon
  push Not at hcon
  have hthird : W.HasThirdFix (W.kernelAt 0) (j : ℤ) := by
    refine ⟨z, ?_, ?_, ?_, fun g hg => hcon g ?_⟩
    · rwa [hWi]
    · rw [hWim1]; exact hj1
    · rw [hWip1]; exact hj2
    · rw [hker] at hg
      exact hg
  exact hno hthird

end QuadSetup

end CFSG.Quasithin.Stroth.WeissDelta

end
