module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZQ
public import CFSG.Quasithin.Vol2.Ch10SecQ3CF

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_centralizes_mod {X : Subgroup G} {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m)
    (he : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    {y : G} (hyX : y ∈ X) (hyo : Odd (orderOf y))
    (hyC : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 X) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hc : e (π ⟨y, hyX⟩) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) w
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    set z := ((x * ⟨y, hyX⟩)⁻¹ * (⟨y, hyX⟩ * x) : ↥X) with hz
    have hzv : (z : G) = (y⁻¹ * (y * (x : G)⁻¹ * y⁻¹ * (x : G)⁻¹⁻¹) * y⁻¹⁻¹)⁻¹ := by
      rw [hz]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h1 := hyC _ (X.inv_mem x.2)
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (X.inv_mem hyX)) _).mp h1
    have h3 : (z : G) ∈ pCoreOf 2 X := by
      rw [hzv]
      exact (pCoreOf 2 X).inv_mem h2
    exact (C10P34.mem_pCoreOf_iff z.2).mp h3
  rw [center_sl2_eq_bot, Subgroup.mem_bot, ← map_one e, e.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  have hyO := (C10P34.mem_pCoreOf_iff hyX).mpr hc
  exact eq_one_of_mem_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hyO hyo

omit [Finite G] in
theorem nonempty_quot_of_isLin2Type {X : Subgroup G} {n : ℕ} (h : IsLin2Type X n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := h
  exact ⟨F, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hF],
    ⟨(QuotientGroup.quotientMulEquivOfEq hαk).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩⟩

omit [Finite G] in
theorem blk_map_conj {X : Subgroup G} {n : ℕ} (t : G)
    (h : IsShort2 X ∧ IsLin2Type X n ∧ blockZ X = ⊥ ∧ blockQ X = blockU X) :
    IsShort2 (X.map (MulAut.conj t).toMonoidHom) ∧
      IsLin2Type (X.map (MulAut.conj t).toMonoidHom) n ∧
      blockZ (X.map (MulAut.conj t).toMonoidHom) = ⊥ ∧
      blockQ (X.map (MulAut.conj t).toMonoidHom) = blockU (X.map (MulAut.conj t).toMonoidHom) :=
  ⟨(Lin2.isShort2_map_equiv_iff (MulAut.conj t) X).mpr h.1,
    (Lin2.isLin2Type_map_equiv_iff (MulAut.conj t) X n).mpr h.2.1,
    by rw [Lin2.blockZ_map_equiv, h.2.2.1, Subgroup.map_bot],
    by rw [Lin2.blockQ_map_equiv, Lin2.blockU_map_equiv, h.2.2.2]⟩

theorem exists_noncomm_of_mem_cComp {X Y : Subgroup G} (hY : Y ∈ cComp X) :
    ∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact not_isSolvable_of_mem_cComp hY (Group.isSolvable_of_comm fun a b =>
    Subtype.ext (h a a.2 b b.2))

variable {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}
  {c : Ctx T L I H K n k b hel I' K₀} {t : G} {L₁ : Subgroup G}

namespace Ctx9

variable (d : Ctx9 c t L₁)
include d

theorem false : False := by
  have := c.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat c.hyp.fsu.nonabelian c.hyp.fsu.qtke).1
  set L₂ := L₁.map (MulAut.conj t).toMonoidHom with hL₂
  set K₂ := K.map (MulAut.conj t).toMonoidHom with hK₂
  set M₁ := mOne L₁ T b with hM₁
  have hM₁O := d.pCoreOf_M₁_ne_bot
  have hT₁ := d.isSylowTwoOf_T1
  have hn2 : 2 ≤ n := c.h1.1
  have hT₁L0 : T1 T L ≤ fsuL0 T L ⊔ T := inf_le_left.trans le_sup_right
  have hL₂F : L₂ ∈ lFamily (T1 T L) :=
    cComp_mem_of_le d.L₂_mem_cComp le_sup_left (sup_le (le_of_mem_cComp d.L₂_mem_cComp) hT₁L0)
  have hK₂F : K₂ ∈ lFamily (T1 T L) :=
    cComp_mem_of_le d.K₂_mem_cComp le_sup_left
      (sup_le (le_of_mem_cComp d.K₂_mem_cComp) (inf_le_left.trans c.T_le_H))
  obtain ⟨Lp, hLp, hL₂Lp⟩ := Vol2Native.lemma_1_2_4_exists hloc c.h37 d.h39 hM₁O hT₁ d.L₂_le_M₁ hL₂F
  obtain ⟨Lp', hLp', hK₂Lp'⟩ :=
    Vol2Native.lemma_1_2_4_exists hloc c.h37 d.h39 hM₁O hT₁ d.K₂_le_M₁ hK₂F
  obtain ⟨F, _, _, hF, he⟩ := c.hKF_n
  have hb₂K₂ : t * b * t⁻¹ ∈ K₂ := ⟨b, c.hbK, rfl⟩
  have hLeq : Lp' = Lp := by
    by_contra hne
    have hc := Vol2Native.lemma_1_2_1_two hloc c.h37 hM₁O hLp' hLp hne
    have hK₂N : K₂ ≤ Subgroup.normalizer (pCoreOf 2 Lp' : Set G) :=
      hK₂Lp'.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lp')
    have hb1 := eq_one_of_centralizes_mod hF ⟨(C10P34.conjQuot K K₂ t rfl).symm.trans he.some⟩
      hb₂K₂ (odd_orderOf_conj c.hbo) fun x hx => by
        have hmem : t * b * t⁻¹ * x * (t * b * t⁻¹)⁻¹ * x⁻¹ ∈ K₂ ⊓ pCoreOf 2 Lp' := by
          refine ⟨K₂.mul_mem (K₂.mul_mem (K₂.mul_mem hb₂K₂ hx) (K₂.inv_mem hb₂K₂))
            (K₂.inv_mem hx), ?_⟩
          have h1 : ⁅x, t * b * t⁻¹⁆ ∈ ⁅Lp', Lp⁆ :=
            Subgroup.commutator_mem_commutator (hK₂Lp' hx) (hL₂Lp d.b₂_mem_L₂)
          have h2 := (hc.1 h1).1
          rw [commutatorElement_def] at h2
          have e : t * b * t⁻¹ * x * (t * b * t⁻¹)⁻¹ * x⁻¹ =
              (x * (t * b * t⁻¹) * x⁻¹ * (t * b * t⁻¹)⁻¹)⁻¹ := by group
          rw [e]
          exact (pCoreOf 2 Lp').inv_mem h2
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lp').to_le inf_le_right) hmem
        exact fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hy, hK₂N hy⟩
    have ho := c.orderOf_b
    rw [show b = t⁻¹ * (t * b * t⁻¹) * t by group, hb1, mul_one, inv_mul_cancel,
      orderOf_one] at ho
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  rw [hLeq] at hK₂Lp'
  have hL₂K₂ : L₂ ≠ K₂ := by
    intro h
    have h1 : L₁ = K := Subgroup.map_injective (MulAut.conj t).injective h
    apply c.hH.2.1
    rw [c.hHK, ← h1]
    refine sup_le ?_ (fun x hx => SecA.le_fsuM T L hx)
    rcases d.hL₁ with h2 | h2 <;> rw [h2]
    · exact (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)
    · exact (SecA.conjugate_le_fsuL0 d.ht).trans (SecA.fsuL0_le_fsuM T L)
  have hSL3 := d.hKF9 G M₁ (T1 T L) Lp L₂ K₂ n hn2 (InternalSec.sqtkGroup_of_localSQTK hloc hM₁O)
    hT₁ hLp hL₂F hK₂F hL₂K₂ hL₂Lp hK₂Lp' (blk_map_conj t d.hL₁blk) (blk_map_conj t d.hKblk)
  have hna : ∃ a b : ↥Lp, a * b ≠ b * a := by
    obtain ⟨a, ha, b', hb', hab⟩ := exists_noncomm_of_mem_cComp d.L₂_mem_cComp
    exact ⟨⟨a, hL₂Lp ha⟩, ⟨b', hL₂Lp hb'⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hLpq : CFSG.Open.IsQuasisimple ↥Lp := by
    rcases hSL3 with h | h | ⟨-, -, -, h, -⟩
    · exact open_isQuasisimple_of_sl3 (Or.inl h) hna
    · exact open_isQuasisimple_of_sl3 (Or.inr h) hna
    · exact h
  have hnorm : ∀ g ∈ M₁, g ∈ Subgroup.normalizer (L₂ : Set G) →
      g ∈ Subgroup.normalizer (Lp : Set G) := by
    intro g hg hgL
    have hc := H13.LocDbl.map_conj_mem_cComp hLp (Subgroup.le_normalizer hg)
    have hle : L₂ ≤ Lp.map (MulAut.conj g).toMonoidHom := by
      rw [← A38.map_conj_eq_iff.mpr hgL]
      exact Subgroup.map_mono hL₂Lp
    exact A38.map_conj_eq_iff.mp (Vol2Native.lemma_1_2_4_unique hloc c.h37 hM₁O hL₂F hLp hc
      hL₂Lp hle).symm
  have hBN : bOne L₁ T b ≤ Subgroup.normalizer (Lp : Set G) := by
    rw [d.B₁_eq]
    refine sup_le (fun s hs => ?_) (Subgroup.zpowers_le.mpr ?_)
    · have hsT : s ∈ T1 T L := c.baum_le_T1 d.h1012 (c.sOne_le_baum hs)
      exact hnorm s (d.T1_le_M₁ hsT) (d.T1_le_normalizer_L₂ hsT)
    · refine hnorm b (B₁_le_M₁ ⟨d.hbL₁, c.b_mem_normalizer_sOne⟩) ?_
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      exact (Subgroup.mem_centralizer_iff.mp (d.L₂_le_centralizer hy) b d.hbL₁).symm
  have hLpB : Lp ≤ Subgroup.normalizer (bOne L₁ T b : Set G) := fun x hx =>
    (le_of_mem_cComp hLp hx).2
  have hnle : ¬ Lp ≤ bOne L₁ T b := by
    intro h
    obtain ⟨a, ha, b', hb', hab⟩ := exists_noncomm_of_mem_cComp d.L₂_mem_cComp
    exact hab (Subgroup.mem_centralizer_iff.mp (d.L₂_le_centralizer hb') a
      (h (hL₂Lp ha)).1)
  have hcomm := commutator_eq_bot_of_quasisimple hLpq hLpB hBN hnle
  have hBC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  obtain ⟨E, hEL, hEab, hEc⟩ :
      ∃ E : Subgroup G, E ≤ Lp ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
    rcases hSL3 with h | h | ⟨hn, -, -, -, hE⟩
    · exact factRankSL3_holds G Lp n p hn2 hp hp2 hpd (Or.inl h)
    · exact factRankSL3_holds G Lp n p hn2 hp hp2 hpd (Or.inr h)
    ·
      have h3 : p ∣ 3 := by
        rw [hn] at hpd
        simpa using hpd
      rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3]
      exact hE
  set x := b ^ ((2 ^ n - 1) / p) with hx
  have hk : (2 ^ n - 1) / p ∣ orderOf b := by
    rw [c.orderOf_b]
    exact Nat.div_dvd_of_dvd hpd
  have hxo : orderOf x = p := by
    rw [hx, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hp.pos).ne' hk,
      c.orderOf_b, Nat.div_div_self hpd (by omega)]
  have hbB : b ∈ bOne L₁ T b := ⟨d.hbL₁, c.b_mem_normalizer_sOne⟩
  have hxB : x ∈ bOne L₁ T b := (bOne L₁ T b).pow_mem hbB _
  have hxE : x ∉ E := by
    intro hxE
    have hxLp := hEL hxE
    obtain ⟨F₁, _, _, hF₁, he₁⟩ := nonempty_quot_of_isLin2Type d.hL₁blk.2.1
    have hxL₁ : x ∈ L₁ := L₁.pow_mem d.hbL₁ _
    have hxS : ∀ s ∈ sOne T b, x * s * x⁻¹ = s := by
      intro s hs
      have h1 := Subgroup.mem_centralizer_iff.mp
        (hBC ⟨d.hS₁L₁.1 hs, Subgroup.le_normalizer hs⟩) x hxLp
      rw [h1, mul_inv_cancel_right]
    have hxo' : Odd (orderOf x) := by
      rw [hxo]
      exact hp.odd_of_ne_two hp2
    have hx1 := eq_one_of_centralizes hF₁ he₁ hxL₁ hxo'
      (centralizes_of_sylow hF₁ he₁ d.hS₁L₁ (Subgroup.le_normalizer hxL₁) hxo' hxS)
    rw [hx1, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hE3, hE3c⟩ := exists_elemAbelian_sup_zpowers hEab hxo (fun e he =>
    Subgroup.mem_centralizer_iff.mp (hBC hxB) e (hEL he)) hxE
  have h3 : 3 ≤ CFSG.Open.pRank p M₁ := le_pRank hp
    (sup_le (hEL.trans (le_of_mem_cComp hLp)) (Subgroup.zpowers_le.mpr (B₁_le_M₁ hxB))) hE3
    (by rw [hE3c, hEc]; ring)
  have h2 : CFSG.Open.pRank p M₁ ≤ 2 := pRank_le_two_of_pCoreOf_ne_bot c.hyp.fsu.qtke hM₁O hp hp2
  omega

end Ctx9

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
