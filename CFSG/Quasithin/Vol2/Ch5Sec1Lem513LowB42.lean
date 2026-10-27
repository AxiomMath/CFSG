module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowSet
public import CFSG.Quasithin.Vol2.Ch12Sec2NatA5
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Background.InternalSecAlt
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512FFProof

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Natural

theorem exists_sl2_mulVec_eq_of_ne_zero {F : Type} [Field F] {u : Fin 2 → F} (hu : u ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq' {F : Type} [Field F] {u v : Fin 2 → F} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).mulVec u = v := by
  obtain ⟨a, ha⟩ := exists_sl2_mulVec_eq_of_ne_zero hu
  obtain ⟨b, hb⟩ := exists_sl2_mulVec_eq_of_ne_zero hv
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec u =
      ![1, 0] := by
    rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hb]

variable {V : Type} [CommGroup V]

theorem isIrrSec_of_binaryNaturalSL {H : Subgroup (MulAut V)} {a : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ 2 a) : XMod.IsIrrSec ↥H (⊥ : Subgroup V) ⊤ := by
  obtain ⟨F, _, _, -, π, -, -, -, -, -, -, -, β, hβs, hβ1, hβeq⟩ := h
  have hmk : ∀ m₁ m₂ : ↥(FFModel.nat (StatedSL 2 F)).sec,
      (QuotientGroup.mk m₁ : ↥(FFModel.nat (StatedSL 2 F)).sec ⧸
        (FFModel.nat (StatedSL 2 F)).ker.subgroupOf (FFModel.nat (StatedSL 2 F)).sec) =
        QuotientGroup.mk m₂ → m₁ = m₂ := by
    intro m₁ m₂ h12
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h12
    exact inv_mul_eq_one.mp (Subtype.ext (Subgroup.mem_bot.mp h12))
  have hβinj : ∀ u w : ↥(⊤ : Subgroup V), β u = β w → u = w := by
    intro u w huw
    have h1 : β (u * w⁻¹) = 1 := by rw [map_mul, map_inv, huw, mul_inv_cancel]
    have h2 := (hβ1 _).mp h1
    rw [Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp (Subtype.ext h2)
  let vec : ↥(FFModel.nat (StatedSL 2 F)).sec → Fin 2 → F :=
    fun m => Multiplicative.toAdd (show Multiplicative (Fin 2 → F) from m.1)
  have hvec_inj : ∀ m₁ m₂, vec m₁ = vec m₂ → m₁ = m₂ :=
    fun m₁ m₂ h12 => Subtype.ext (Multiplicative.toAdd.injective h12)
  have hcoord : ∀ v : V, ∃ m, β ⟨v, trivial⟩ = QuotientGroup.mk m := fun v => by
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, trivial⟩)
    exact ⟨m, hm.symm⟩
  have hne0 : ∀ (w : V) (m : ↥(FFModel.nat (StatedSL 2 F)).sec), w ≠ 1 →
      β ⟨w, trivial⟩ = QuotientGroup.mk m → vec m ≠ 0 := by
    intro w m hw hm h0
    apply hw
    have hm1 : m = 1 := hvec_inj _ _ (by rw [h0]; rfl)
    have h1 : β ⟨w, trivial⟩ = 1 := by rw [hm, hm1]; rfl
    exact Subgroup.mem_bot.mp ((hβ1 _).mp h1)
  refine ⟨?_, fun J hJ _ _ => ?_⟩
  ·
    set m₁ : ↥(FFModel.nat (StatedSL 2 F)).sec :=
      ⟨Multiplicative.ofAdd ![1, 0], Subgroup.mem_top _⟩ with hm₁
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m₁)
    refine bot_lt_iff_ne_bot.mpr fun hb => ?_
    have hmem : ∀ x : V, x ∈ (⊥ : Subgroup V) := fun x => hb ▸ Subgroup.mem_top x
    have hu' : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (hmem u))
    have h1 : (QuotientGroup.mk m₁ : ↥(FFModel.nat (StatedSL 2 F)).sec ⧸
        (FFModel.nat (StatedSL 2 F)).ker.subgroupOf (FFModel.nat (StatedSL 2 F)).sec) =
        QuotientGroup.mk 1 := by
      rw [← hu, hu', map_one]
      rfl
    have h2 : vec m₁ 0 = vec 1 0 := congrArg (fun m => vec m 0) (hmk _ _ h1)
    have h3 : vec m₁ 0 = 1 := rfl
    have h4 : vec 1 0 = 0 := rfl
    exact one_ne_zero (h3.symm.trans (h2.trans h4))
  · by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · right
      obtain ⟨⟨j, hjJ⟩, hj1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJ0
      have hj1' : j ≠ 1 := fun h1 => hj1 (Subtype.ext h1)
      rw [eq_top_iff]
      intro v _
      by_cases hv : v = 1
      · rw [hv]
        exact J.one_mem
      obtain ⟨m₀, hm₀⟩ := hcoord j
      obtain ⟨m, hm⟩ := hcoord v
      obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq' (hne0 j m₀ hj1' hm₀) (hne0 v m hv hm)
      have hgmem : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) F) ∈ StatedSL 2 F :=
        Subgroup.subset_closure (by simp)
      set γ : ↥(StatedSL 2 F) := ⟨_, hgmem⟩ with hγ
      have key := hβeq γ ⟨j, trivial⟩ m₀ trivial (Subgroup.mem_top _) hm₀
      have hact : (⟨(FFModel.nat (StatedSL 2 F)).act γ
          (m₀ : (FFModel.nat (StatedSL 2 F)).Amb), Subgroup.mem_top _⟩ :
            ↥(FFModel.nat (StatedSL 2 F)).sec) = m := by
        apply hvec_inj
        show (((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)).mulVec (vec m₀) = vec m
        simpa using hg
      have h2 : β ⟨((π γ : ↥H) : MulAut V) j, trivial⟩ = β ⟨v, trivial⟩ := by
        rw [key, hm, hact]
      have h3 := congrArg Subtype.val (hβinj _ _ h2)
      simp only at h3
      rw [← h3]
      exact hJ (π γ) j hjJ

end Natural

theorem false_of_l2Order_mul {n e a o : ℕ} (hn : 1 ≤ n) (ho : Odd o)
    (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) * 2 ^ e = 2 ^ a * o) (hno : ∀ k : ℕ, (2 ^ k) ^ 2 - 1 ≠ o) :
    False := by
  have h' : 2 ^ (n + e) * ((2 ^ n) ^ 2 - 1) = 2 ^ a * o := by
    rw [pow_add, ← h]
    ring
  obtain ⟨-, h2⟩ := two_pow_mul_odd_inj (odd_two_pow_pow_sub_one hn (by norm_num)) ho h'
  exact hno n h2

theorem two_pow_sq_sub_one_ne_45 (k : ℕ) : (2 ^ k) ^ 2 - 1 ≠ 45 := by
  intro h
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> simp at h
  · have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have : 64 ≤ (2 ^ k) ^ 2 := by nlinarith
    omega

theorem two_pow_sq_sub_one_ne_189 (k : ℕ) : (2 ^ k) ^ 2 - 1 ≠ 189 := by
  intro h
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> simp at h
  · have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have : 256 ≤ (2 ^ k) ^ 2 := by nlinarith
    omega

namespace L2Set

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)} {n : ℕ}

theorem le_ffJ (h : L2Set V X K n) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    K ≤ ffJ X := by
  by_contra hK
  have h1 := h.eq_bot_of_normal (B6.ffJ_le X)
    (fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hx) y).mp hy) hK
  exact hA.2.1 (le_bot_iff.mp (h1 ▸ B6.le_ffJ hA))

theorem exists_card_ffJ (h : L2Set V X K n) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : ∃ e : ℕ, Nat.card (ffJ X) = Nat.card K * 2 ^ e :=
  exists_card_eq_mul_two_pow (h.le_ffJ hA) ((B6.ffJ_le X).trans h.norm)
    fun j hj => h.two j (B6.ffJ_le X hj)

theorem false_of_ffJ_sp4 (h : L2Set V X K n) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hSp : BinaryNaturalSp4 (ffJ X) ⊤ ⊥ 1) : False := by
  obtain ⟨F, _, _, hF, hR⟩ := hSp
  obtain ⟨e, he⟩ := h.exists_card_ffJ hA
  have h1 := card_eq_card_gam (FFModel.nat_faithful _) hR
  have h2 : Nat.card (FFModel.nat (StatedSp 2 F)).Gam =
      Nat.card F ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, (Nat.card F ^ (2 * j) - 1) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 2
  rw [h2, hF, he, h.card] at h1
  have h3 : (2 ^ 1) ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, ((2 ^ 1) ^ (2 * j) - 1) = 2 ^ 4 * 45 := by
    decide
  rw [h3] at h1
  exact false_of_l2Order_mul (by have := h.two_le; omega) (by decide) h1
    two_pow_sq_sub_one_ne_45

theorem false_of_ffJ_g2 (h : L2Set V X K n) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hG : G2Natural (ffJ X) ⊤ ⊥ 1) : False := by
  obtain ⟨F, _, _, hF, hR⟩ := hG
  have := charP_two_of_card hF
  obtain ⟨e, he⟩ := h.exists_card_ffJ hA
  obtain ⟨eG⟩ := Ch3Sec3.nonempty_mulEquiv_of_realizes (zornQ_faithful le_rfl) hR
  have h1 : Nat.card (ffJ X) = Nat.card ↥(quasithinG2 F) := Nat.card_congr eG.toEquiv
  rw [Bridge.Alt57Model.quasithinG2_eq_cayleyGroup, CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup,
    hF, he, h.card] at h1
  have h3 : (2 ^ 1) ^ 6 * (((2 ^ 1) ^ 6 - 1) * ((2 ^ 1) ^ 2 - 1)) = 2 ^ 6 * 189 := by decide
  rw [h3] at h1
  exact false_of_l2Order_mul (by have := h.two_le; omega) (by decide) h1
    two_pow_sq_sub_one_ne_189

theorem card_mul_card_fixV_le (h42 : AsB42) (h : L2Set V X K n)
    (hirr : XMod.IsIrrSec ↥K (⊥ : Subgroup V) ⊤) {A : Subgroup (MulAut V)} (hAX : A ≤ X)
    (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) : Nat.card A * Nat.card (fixV A) ≤ Nat.card V := by
  by_contra hlt
  push Not at hlt
  have hstrong : IsStrongFFModule X := ⟨A, hAX, hA1, hA2, hlt⟩
  have hAA : IsA2 X A := ⟨hAX, hA1, hA2⟩
  obtain ⟨B, -, hB, -⟩ := B1_4_4_lt h.sq hAA ((rAV_lt_one_iff h.sq hAA).2 hlt)
  have hn1 : 1 ≤ n := by have := h.two_le; omega
  apply not_isStrongFFModule_of_one_le_qOf h.sq (X := X) _ hstrong
  rcases h42 V h.sq X K (h.b4Hyp hirr) B hB with c | c | c | c | c | c | c | c | c | c | c
  · exact c.2.2.2.ge
  · obtain ⟨-, ⟨m, F, _, _, hF, hR⟩, -⟩ := c
    exact (false_of_natSL3 h.card hn1 hF hR).elim
  · obtain ⟨⟨m, hSp, hJ⟩, -⟩ := c
    exfalso
    rcases Nat.lt_or_ge 1 m with hm | hm
    · rw [hJ hm] at hSp
      obtain ⟨F, _, _, hF, hR⟩ := hSp
      exact false_of_natSp4 h.card hn1 hF hR
    · have hm1 : m = 1 := le_antisymm hm (B5.one_le_of_binaryNaturalSp4 hSp)
      subst hm1
      exact h.false_of_ffJ_sp4 hB hSp
  · exact c.2.ge
  · exact c.2.ge
  · exact c.2.2.2.1.ge
  · exact c.2.2.2.2.1.ge
  · exact c.2.2.1.ge
  · obtain ⟨-, m, hm, ⟨F, _, _, hF, hR⟩, -⟩ := c
    exfalso
    exact false_of_natSL_two h.card (by omega) (by rw [hF, pow_one]) hR
  · exact (false_of_extSq h.card (Or.inl rfl) c.1).elim
  · exact c.2.2.2.1.ge

theorem isSylowTwoOf_of_natural (h42 : AsB42) (h : L2Set V X K n)
    (hnat : BinaryNaturalSL K ⊤ ⊥ 2 n) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    IsSylowTwoOf A K := by
  have hirr := isIrrSec_of_binaryNaturalSL hnat
  have hB := h.b4Hyp hirr
  have hn1 : 1 ≤ n := by have := h.two_le; omega
  obtain ⟨eK⟩ := h.iso
  rcases h42 V h.sq X K hB A hA with c | c | c | c | c | c | c | c | c | c | c
  · exact c.2.2.1
  · obtain ⟨-, ⟨m, F, _, _, hF, hR⟩, -⟩ := c
    exact (false_of_natSL3 h.card hn1 hF hR).elim
  · obtain ⟨⟨m, hSp, hJ⟩, -⟩ := c
    exfalso
    rcases Nat.lt_or_ge 1 m with hm | hm
    · rw [hJ hm] at hSp
      obtain ⟨F, _, _, hF, hR⟩ := hSp
      exact false_of_natSp4 h.card hn1 hF hR
    · have hm1 : m = 1 := le_antisymm hm (B5.one_le_of_binaryNaturalSp4 hSp)
      subst hm1
      exact h.false_of_ffJ_sp4 hA hSp
  · obtain ⟨⟨m, hG, -, hJ⟩, -⟩ := c
    exfalso
    rcases Nat.lt_or_ge 1 m with hm | hm
    · rw [hJ hm] at hG
      exact false_of_g2 h.two_le eK hG
    · have hm1 : m = 1 := le_antisymm hm (B5.one_le_of_g2Natural hG)
      subst hm1
      exact h.false_of_ffJ_g2 hA hG
  · exfalso
    obtain ⟨k, hk, halt, -⟩ := InternalSec.alternatingNatural_of_b42Case5 h.sq hB c
    rcases hk with rfl | rfl
    · obtain ⟨x, hxK, hx3, hfree⟩ := exists_pow_three_fixedPointFree_of_binaryNaturalSL hnat
      obtain ⟨w, hw⟩ := exists_ne_one_of_alternatingNatural_five halt
      have hx1 : x ≠ 1 := fun h1 => hw (hfree w (by rw [h1]; rfl))
      obtain ⟨v, hv1, hvx⟩ := exists_fixed_of_alternatingNatural_five halt hxK hx3 hx1
      exact hv1 (hfree v hvx)
    · exact false_of_alt h.card (Or.inr (Or.inl rfl)) halt
  · exact (false_of_alt h.card (Or.inl rfl) c.2.1).elim
  · exact (false_of_a7Four h.card c.2.2.1).elim
  · obtain ⟨-, -, -, F, hF1, hF2, Γ₀, hc, hdet, hhat, hcen, π, hπ, -⟩ := c
    exact (false_of_tripleA6 h.card ⟨F, hF1, hF2, Γ₀, hc, hdet, hhat, hcen, ⟨π, hπ⟩⟩).elim
  · obtain ⟨-, m, hm, ⟨F, _, _, hF, hR⟩, -⟩ := c
    exfalso
    exact false_of_natSL_two h.card (by omega) (by rw [hF, pow_one]) hR
  · exact (false_of_extSq h.card (Or.inl rfl) c.1).elim
  · obtain ⟨-, -, -, -, π, hπ, -⟩ := c
    exact (false_of_extSq h.card (Or.inr rfl) ⟨π, hπ⟩).elim

end L2Set

end CFSG.Quasithin.H13
