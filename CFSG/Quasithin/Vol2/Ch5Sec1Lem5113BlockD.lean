module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113M4F
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section Natural

variable {G : Type} [Group G]

theorem IsNatQuotCh5.mem_centralizer_of_conj_eq_of_odd {L V : Subgroup G} {n : ℕ}
    (h : IsNatQuotCh5 L V n) {d : G} (hdL : d ∈ L) (hodd : Odd (orderOf d))
    (hdV : d ∉ Subgroup.centralizer (V : Set G)) {v : G} (hv : v ∈ V)
    (hdv : d * v * d⁻¹ = v) : v ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hLV, hc, K, hKf, hKfin, hK, π, hπs, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  by_contra hvL
  have hn1 : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  set a : ↥(autOn L V) := ⟨A4.actionOn V L hLV ⟨d, hdL⟩,
    (A4.mem_autOn_iff hLV).mpr ⟨⟨d, hdL⟩, rfl⟩⟩ with ha
  obtain ⟨γ, hγ⟩ := hπs a
  set u : ↥(⊤ : Subgroup ↥V) := ⟨⟨v, hv⟩, Subgroup.mem_top _⟩ with hu
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hu' : ((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V) ∈ (⊤ : Subgroup ↥V) :=
    Subgroup.mem_top _
  have he := hβe γ u m hu' (Subgroup.mem_top _) hm.symm
  have hfix : (⟨((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V), hu'⟩ : ↥(⊤ : Subgroup ↥V)) = u := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hγ]
    show ((A4.actionOn V L hLV ⟨d, hdL⟩ ⟨v, hv⟩ : ↥V) : G) = v
    rw [A4.actionOn_apply_coe]
    exact hdv
  rw [hfix, ← hm, QuotientGroup.eq] at he
  have hm1 : m ≠ 1 := by
    intro hm1
    apply hvL
    have h1 : β u = 1 := by rw [← hm, hm1]; rfl
    have h2 := (hβk u).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  obtain ⟨x, hx⟩ : ∃ x : Multiplicative (Fin 2 → K), x = m.1 := ⟨m.1, rfl⟩
  have hfixm : natAct (Assembly.LowTwoRank.StatedSL 2 K) γ x = x := by
    have h2 := Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp he)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_one] at h2
    rw [hx]
    exact h2.symm
  have hmv : ((Subtype.val γ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd x) = Multiplicative.toAdd x :=
    congrArg Multiplicative.toAdd hfixm
  have hm0 : Multiplicative.toAdd x ≠ 0 := by
    intro h0
    apply hm1
    apply Subtype.ext
    rw [← hx]
    exact toAdd_eq_zero.mp h0
  have hdet := Vol2.Ch10.SecA.det_eq_one_of_mem_statedSL (Subtype.prop γ)
  have hsq := sl2_mul_self_eq_one_of_fixed hdet hm0 hmv
  have hγ2 : γ * γ = 1 := Subtype.ext (Units.ext hsq)
  have ha2 : a * a = 1 := by rw [← hγ, ← map_mul, hγ2, map_one]
  have hd2 : d * d ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : A4.actionOn V L hLV (⟨d, hdL⟩ * ⟨d, hdL⟩) = 1 := by
      rw [map_mul]
      exact congrArg Subtype.val ha2
    exact (A4.actionOn_eq_one_iff hLV _).mp h1
  apply hdV
  obtain ⟨k, hk⟩ := hodd
  have h4 : d = (d * d) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf d + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h4]
  exact Subgroup.pow_mem _ hd2 _

end Natural

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem le_normalizer_baum_of_nat (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    {V' : Subgroup G} (hV' : IsCh5Module T L V') (hZV' : quasithinOmegaOneCenter T ≤ V')
    (hnat : IsNatQuotCh5 L V' n)
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    D ≤ Subgroup.normalizer (baum T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hD := m.nota.2.1
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hred := hV'.isTwoReducedIn
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V' : Set G) ≤ T :=
    (h.setting516 hD hV').sup_inf_centralizer_le hred.2.1 fun hle => hV'.2.2
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle))
  have hDo : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hd)
  have hTo : ∀ x ∈ T, ∃ k : ℕ, orderOf x ∣ 2 ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx⟩
    exact ⟨k, orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)⟩
  have hodd1 : ∀ x ∈ T, Odd (orderOf x) → x = 1 := by
    intro x hx ho
    obtain ⟨k, hk⟩ := hTo x hx
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ho)) hk)
  have hT1 : T ≠ ⊥ := by
    intro hT
    apply h.maximal.1.2.2.2
    exact le_bot_iff.mp ((CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf
      (h.isSylowTwoOf le_sup_right)).trans hT.le)
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot hT2 hT1)
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hDZ : ∀ d ∈ D, (∀ y ∈ quasithinOmegaOneCenter T, d * y = y * d) → d = 1 := by
    intro d hd hc
    by_contra hd1
    have hdV : d ∉ Subgroup.centralizer (V' : Set G) := fun hdc =>
      hd1 (hodd1 d (hCV ⟨Subgroup.mem_sup_left (hDL hd), hdc⟩) (hDo d hd))
    have h1 := hnat.mem_centralizer_of_conj_eq_of_odd (hDL hd) (hDo d hd) hdV (hZV' hzZ)
      (by rw [hc z hzZ, mul_inv_cancel_right])
    have h2 : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, h1⟩
    rw [hZL] at h2
    exact hz1' (Subgroup.mem_bot.mp h2)
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hZT : quasithinOmegaOneCenter T ≤ T := fun y hy => (mem_quasithinOmegaOneCenter_iff.mp hy).1
  have hZe : IsElemAbelian 2 (quasithinOmegaOneCenter T) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (mem_quasithinOmegaOneCenter_iff.mp b.2).2.1 a
          (mem_quasithinOmegaOneCenter_iff.mp a.2).1)⟩⟩,
      fun y hy => (mem_quasithinOmegaOneCenter_iff.mp hy).2.2⟩
  have hJZ : thompsonJ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun j hj => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hy).2.1 j (hJT hj)).symm
  have hZE := le_omegaOneCenterOf_thompsonJ hZe hZT hJZ
  have hDE : D ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
    (m.le_normalizer_thompsonJ_of_nat hV' hnat).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ T))
  have hTE : T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) := fun t ht =>
    A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ T)
      (mem_normalizer_thompsonJ_of_mem_normalizer (Subgroup.le_normalizer ht))
  have hYE : D ⊔ T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
    sup_le hDE hTE
  have hDT : ∀ t ∈ T, ∀ d ∈ D, ∃ d' ∈ D, ∃ t' ∈ T, t * d = d' * t' := by
    intro t ht d hd
    have hBT := Subgroup.coe_mul_of_right_le_normalizer_left (borelL T L) T
      h.T_le_normalizer_borel
    have hDS := Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L)
      (hD.1.trans inf_le_right)
    have h1 : t * d ∈ ((borelL T L ⊔ T : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hD.1 hd))
    rw [hBT] at h1
    obtain ⟨y, hy, s, hs, hys⟩ := h1
    have hys' : y * s = t * d := hys
    have hy' : y ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
      rw [h.borelL_eq_sup hD]
      exact hy
    rw [hDS] at hy'
    obtain ⟨d', hd', r, hr, hdr⟩ := hy'
    have hdr' : d' * r = y := hdr
    exact ⟨d', hd', r * s, T.mul_mem (Subgroup.mem_inf.mp hr).1 hs,
      by rw [← hys', ← hdr', mul_assoc]⟩
  have key : ∀ d ∈ D, ∀ b ∈ baum T, d * b * d⁻¹ ∈ baum T := by
    intro d hd b hb
    have hbT : b ∈ T := hb.1
    have hbE : b ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) := hb.2
    have hcE : d * b * d⁻¹ ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer hDE hd) b).mp hbE
    obtain ⟨d', hd', t', ht', he⟩ := hDT b hbT d⁻¹ (D.inv_mem hd)
    have hd'' : d * d' ∈ D := D.mul_mem hd hd'
    have hdbd : d * b * d⁻¹ = d * d' * t' := by rw [mul_assoc d b, he, mul_assoc]
    set φ := A4.actionOn (omegaOneCenterOf (thompsonJ T)) (D ⊔ T) hYE with hφ
    have hφeq : φ ⟨d * d', Subgroup.mem_sup_left hd''⟩ =
        φ ⟨t'⁻¹, Subgroup.mem_sup_right (T.inv_mem ht')⟩ := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      have hx' : t'⁻¹ * (x : G) * t'⁻¹⁻¹ ∈ omegaOneCenterOf (thompsonJ T) :=
        (Subgroup.mem_normalizer_iff.mp (hTE (T.inv_mem ht')) x).mp x.2
      have h1 : d * d' = d * b * d⁻¹ * t'⁻¹ := by rw [hdbd, mul_inv_cancel_right]
      have h2 := Subgroup.mem_centralizer_iff.mp hcE _ hx'
      show d * d' * x * (d * d')⁻¹ = t'⁻¹ * x * t'⁻¹⁻¹
      calc d * d' * x * (d * d')⁻¹ =
          (d * b * d⁻¹) * (t'⁻¹ * x * t'⁻¹⁻¹) * (d * b * d⁻¹)⁻¹ := by rw [h1]; group
        _ = (t'⁻¹ * x * t'⁻¹⁻¹) * (d * b * d⁻¹) * (d * b * d⁻¹)⁻¹ := by rw [h2]
        _ = t'⁻¹ * x * t'⁻¹⁻¹ := by group
    have hord : orderOf (φ ⟨d * d', Subgroup.mem_sup_left hd''⟩) = 1 := by
      have h1 : orderOf (φ ⟨d * d', Subgroup.mem_sup_left hd''⟩) ∣ orderOf (d * d') := by
        have := orderOf_map_dvd φ ⟨d * d', Subgroup.mem_sup_left hd''⟩
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨k, hk⟩ := hTo _ (T.inv_mem ht')
      have h2 : orderOf (φ ⟨d * d', Subgroup.mem_sup_left hd''⟩) ∣ 2 ^ k := by
        rw [hφeq]
        have := orderOf_map_dvd φ ⟨t'⁻¹, Subgroup.mem_sup_right (T.inv_mem ht')⟩
        rw [Subgroup.orderOf_mk] at this
        exact this.trans hk
      have hcop : Nat.Coprime (orderOf (d * d')) (2 ^ k) :=
        Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hDo _ hd''))
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    have hcE' : d * d' ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
      (A4.actionOn_eq_one_iff hYE _).mp (orderOf_eq_one_iff.mp hord)
    have h1 : d * d' = 1 := hDZ _ hd'' fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hcE' y (hZE hy)).symm
    have ht'eq : d * b * d⁻¹ = t' := by rw [hdbd, h1, one_mul]
    rw [ht'eq] at hcE
    rw [ht'eq]
    exact ⟨ht', hcE⟩
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key d hd b, fun hb => ?_⟩
  have h1 := key d⁻¹ (D.inv_mem hd) _ hb
  simpa [mul_assoc] using h1

end Main513

@[expose] def Stmt5_1_13_four_block_bc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n →
      (C126Third (L ⊔ T) T ∨ C126Third H T) →
      ¬ C126Third H T ∧ 2 < n

theorem stmt5_1_13_four_block_bcd_of (hbc : Stmt5_1_13_four_block_bc) :
    Stmt5_1_13_four_block_bcd := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat C _ hCB
    hCch hdich _ _
  obtain ⟨hnb, hn⟩ := hbc G T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat
    hdich
  refine ⟨hnb, hn, ?_⟩
  have hBC : Subgroup.normalizer (baum T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := baum T)
      (C.subgroupOf (baum T))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at this
  refine sup_le ((m.le_normalizer_baum_of_nat hV' hZV' hnat hZL).trans hBC) ?_
  exact (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)).trans hBC

end CFSG.Quasithin.H13
