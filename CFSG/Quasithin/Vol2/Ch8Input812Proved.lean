module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Vol2.Ch7Lem734Mod
public import CFSG.Quasithin.Vol2.Ch4Sec4Rem442
public import CFSG.Quasithin.Background.E6TwentySevenMain
public import CFSG.Quasithin.Vol2.Ch4Sec4HypPrime

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section Offender

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_mul_card_autI {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : IsElemAbelian 2 A) (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (h : Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ≤ 2 * Nat.card A) :
    Nat.card V ≤
      2 * Nat.card (autI hV A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  set C := A ⊓ Subgroup.centralizer (V : Set G) with hCdef
  have hc : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c := fun c hc v hv =>
    (Subgroup.mem_centralizer_iff.1 hc.2 v hv).symm
  have h1 := B2F.card_sup_mul_card_inf_of_commute hc
  have h2 := card_autI_mul_card_inf hV hAN
  have h4 : Nat.card ↥(C ⊓ V) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have := hA.1
    exact setLike_mul_comm ha hx.1.1
  have key : Nat.card C * Nat.card V ≤ Nat.card C *
      (2 * Nat.card (autI hV A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by
    calc Nat.card C * Nat.card V = Nat.card ↥(C ⊔ V) * Nat.card ↥(C ⊓ V) := h1.symm
      _ ≤ (2 * Nat.card A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
          Nat.mul_le_mul h h4
      _ = 2 * (Nat.card (autI hV A) * Nat.card C) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by rw [h2]
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left key Nat.card_pos

theorem isFOneOffender_autI {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : IsElemAbelian 2 A) (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hA1 : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (h : Nat.card V ≤
      2 * Nat.card (autI hV A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) :
    IsFOneOffender (autI hV ⊤) (autI hV A) := by
  have hW2 : IsPGroup 2 (IntMod V hV) := isPGroup_two_of_sq_eq_one IntMod.sq_eq_one
  have hel := isElemAbelian2_autI hV hA hAN
  refine ⟨⟨autI_mono hV le_top, (autI_eq_bot_iff hV hAN).not.2 hA1, hel⟩, ?_⟩
  have hpA : IsPGroup 2 ↥(autI hV A) := fun x => ⟨1, Subtype.ext (by simpa using hel.2 x x.2)⟩
  have hAc : Nat.card ↥(autI hV A) = 2 ^ rk ↥(autI hV A) := card_eq_two_pow_of_isPGroup hpA
  have h1 := (fixV (autI hV A)).card_mul_index
  rw [index_eq_two_pow_rkIdx hW2, card_fixV_autI hV hAN] at h1
  have hVc : Nat.card (IntMod V hV) = Nat.card V := rfl
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have h2 : 2 ^ rkIdx (fixV (autI hV A)) ≤ 2 ^ (rk ↥(autI hV A) + 1) := by
    have h3 : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ rkIdx (fixV (autI hV A)) ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ (rk ↥(autI hV A) + 1) := by
      rw [h1, hVc, pow_succ]
      calc Nat.card V ≤
          2 * Nat.card (autI hV A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := h
        _ = _ := by rw [hAc]; ring
    exact Nat.le_of_mul_le_mul_left h3 hpos
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

omit [Finite G] in
theorem leFixI_of_le_autI {V U K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKU : K ≤ Subgroup.centralizer (U : Set G)) {X : Subgroup (MulAut (IntMod V hV))}
    (hX : X ≤ autI hV K) : LeFixI hV U X := by
  intro v hvU x hx
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 (hX hx)
  apply IntMod.val_injective
  rw [convI_apply_val]
  have := Subgroup.mem_centralizer_iff.1 (hKU hgK) v.val hvU
  rw [← this, mul_inv_cancel_right]

omit [Finite G] in
theorem inf_centralizer_eq_bot_of_fanoCoreModule {K V : Subgroup G} [IsMulCommutative ↥V]
    (h : FanoCoreModule (V := ↥V) (autOn K V) ⊤ ⊥) :
    V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  obtain ⟨e, π, -, he⟩ := Fano.FanoCoreModule.exists_equiv h
  rw [eq_bot_iff]
  intro v hv
  set w : ↥V := ⟨v, hv.1⟩ with hw
  have hfix : ∀ φ ∈ autOn K V, φ w = w := by
    intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := Subgroup.mem_map.1 hφ
    apply Subtype.ext
    rw [show ((conjAct V g w : ↥V) : G) = (g : G) * v * (g : G)⁻¹ from
      Subgroup.normalizerMonoidHom_apply_apply_coe V _ w]
    have := Subgroup.mem_centralizer_iff.1 hv.2 g (Subgroup.mem_subgroupOf.1 hgK)
    rw [this, mul_inv_cancel_right]
  have h1 := he Fano.y7 w
  rw [hfix _ (π Fano.y7).2] at h1
  have h2 : ((e w : ↥fanoCore) : Fano.PMod) = 1 := Fano.eq_one_of_fix (e w).2 h1.symm
  have h3 : w = 1 := e.injective (by rw [map_one]; exact Subtype.ext h2)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h3)

end Offender

section Hyp

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem two_le_mParam_autI (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    2 ≤ mParam (autI hV ⊤) := by
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hnFF := not_isFFModule_of_hyp702 hyp hV hNM
  have hW2 : IsPGroup 2 (IntMod (fsuV T I) hV) := isPGroup_two_of_sq_eq_one IntMod.sq_eq_one
  unfold mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autI hV ⊤)) 2
      (even_iff_two_dvd.1 hev)
    refine le_csInf ⟨_, (t : MulAut (IntMod (fsuV T I) hV)), t.2,
      by rw [Subgroup.orderOf_coe, ht], rfl⟩ ?_
    rintro n ⟨s, hs, hso, rfl⟩
    by_contra hlt
    push Not at hlt
    apply hnFF
    have hs1 : s ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hso
      exact absurd hso (by decide)
    refine ⟨Subgroup.zpowers s, Subgroup.zpowers_le.2 hs,
      fun h1 => hs1 (Subgroup.zpowers_eq_bot.1 h1), ⟨fun a ha b hb => ?_, fun a ha => ?_⟩, ?_⟩
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨k, rfl⟩ := hb
      exact (Commute.zpow_zpow_self s i k).eq
    · obtain ⟨i, rfl⟩ := ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hso,
        pow_orderOf_eq_one, one_zpow]
    · have h1 := (fixV (Subgroup.zpowers s)).card_mul_index
      rw [index_eq_two_pow_rkIdx hW2] at h1
      rw [Nat.card_zpowers, hso, ← h1, mul_comm]
      refine Nat.mul_le_mul_right _ ?_
      calc 2 ^ rkIdx (fixV (Subgroup.zpowers s)) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
  · by_contra hlt
    push Not at hlt
    have hcard := card_eq_two_pow_of_isPGroup hW2
    have hV1 := fsuV_ne_bot hyp.fsu
    have hle : Nat.card ↥(fsuV T I) ≤ 2 := by
      have h1 : Nat.card (IntMod (fsuV T I) hV) ≤ 2 := by
        rw [hcard]
        calc 2 ^ rk (IntMod (fsuV T I) hV) ≤ 2 ^ 1 :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      exact h1
    have hge : 2 ≤ Nat.card ↥(fsuV T I) := by
      have : Nontrivial ↥(fsuV T I) := (Subgroup.nontrivial_iff_ne_bot _).2 hV1
      exact Finite.one_lt_card
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV T I))).1 (le_antisymm hle hge)
    have hLV : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
    have hLC : fsuL0 T L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1, one_mul, mul_one]
      have hlv : l * v * l⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.1 (hLV hl) v).1 hv
      have hlv1 : l * v * l⁻¹ ≠ 1 := by
        intro h1
        apply hv1
        calc v = l⁻¹ * (l * v * l⁻¹) * l := by group
          _ = 1 := by rw [h1]; group
      have e1 := huniq ⟨v, hv⟩ (fun h1 => hv1 (congrArg Subtype.val h1))
      have e2 := huniq ⟨l * v * l⁻¹, hlv⟩ (fun h1 => hlv1 (congrArg Subtype.val h1))
      have e3 : l * v * l⁻¹ = v := congrArg Subtype.val (e2.trans e1.symm)
      calc v * l = (l * v * l⁻¹) * l := by rw [e3]
        _ = l * v := by group
    apply hV1
    rw [← commutator_fsuV_fsuL0 hyp.fsu hN, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.1 hLC

omit [Finite G] in
private theorem le_normalizer_conjugate_of {X J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hXJ : X ≤ Subgroup.normalizer (J : Set G)) :
    X ≤ Subgroup.normalizer (CFSG.conjugate J g : Set G) := by
  have hmem : ∀ {K : Subgroup G} {x : G}, x ∈ CFSG.conjugate K g ↔ g * x * g⁻¹ ∈ K := by
    intro K x
    unfold CFSG.conjugate
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hmem, hmem]
  have hgl : g * l * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
  have e : g * (l * x * l⁻¹) * g⁻¹ = (g * l * g⁻¹) * (g * x * g⁻¹) * (g * l * g⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (hXJ hgl) _

theorem not_fano_of_fixedPointFree (h325 : Stmt3_2_5) (hyp : Hyp7_0_2 G T L I)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (h : ∃ _ : IsMulCommutative ↥(fsuV T I),
      FanoCoreModule (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥) : False := by
  obtain ⟨hc, h⟩ := h
  have hcard : Nat.card ↥(fsuV T I) = 64 := Fano.FanoCoreModule.card h
  have hLV : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have hCV := inf_centralizer_eq_bot_of_fanoCoreModule h
  have hCI : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    exact inf_le_inf_right _ (le_fsuV I T)
  have hirr := irr_of_inf_centralizer hyp.fsu hCI
  have hIN : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hyp.fsu.irrPlus.2.2.1
  have hIV : I ≤ fsuV T I := le_fsuV I T
  have hcardI : ∀ {X : Subgroup G}, X ≤ fsuV T I →
      Nat.card ↥(X.subgroupOf (fsuV T I)) = Nat.card ↥X := fun hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rcases fsuV_cases_of_normal h325 hyp hTL with hIVeq | ⟨t, ht, hsum, hinf, -, -⟩
  ·
    obtain ⟨X, hX, hX8⟩ := Fano.FanoCoreModule.exists_card_eight h
    have hirr' := InternalSec.irr_subgroupOf hLV fun J hJ hJN => hirr J hJ hJN
    have htop : I.subgroupOf (fsuV T I) = ⊤ := by
      rw [← hIVeq] at hIV ⊢
      exact Subgroup.subgroupOf_self _
    rcases hirr' X (htop ▸ le_top) hX with h0 | h0
    · rw [h0, Subgroup.card_bot] at hX8
      norm_num at hX8
    · rw [h0, htop, Subgroup.card_top, hcard] at hX8
      norm_num at hX8
  ·
    have hItV : CFSG.conjugate I t ≤ fsuV T I := hsum ▸ le_sup_right
    have hItN : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate I t : Set G) :=
      le_normalizer_conjugate_of (le_normalizer_conjClosure L T ht) hIN
    have hsum' := InternalSec.sup_subgroupOf_eq_top hIV hItV hsum.symm
    have hinf' := InternalSec.inf_subgroupOf_eq_bot (V := fsuV T I) hinf
    have hct : Nat.card ↥(CFSG.conjugate I t) = Nat.card ↥I :=
      Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective
    have hprod : Nat.card ↥(fsuV T I) = Nat.card ↥I * Nat.card ↥I := by
      rw [← Nat.card_congr (InternalSec.sumEquiv hsum' hinf').toEquiv, Nat.card_prod,
        hcardI hIV, hcardI hItV, hct]
    have hI8 : Nat.card ↥I = 8 := by
      rw [hcard] at hprod
      exact le_antisymm (by nlinarith) (by nlinarith)
    have heq := Fano.FanoCoreModule.eq_of_card_eight h
      (InternalSec.autOn_inv_subgroupOf hIN) (InternalSec.autOn_inv_subgroupOf hItN)
      (by rw [hcardI hIV, hI8]) (by rw [hcardI hItV, hct, hI8])
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hIV, inf_eq_left.mpr hItV] at heq
    apply hyp.fsu.irrPlus.2.1
    rw [← hinf, ← heq, inf_idem]

end Hyp

variable {G : Type} [Group G] [Finite G]

theorem input8_1_2_of
    (hPT : E6.ParabolicTorusFact) (h732 : Stmt7_3_2) (h325 : Stmt3_2_5)
    (h443 : Stmt4_4_3Orbit') : Input8_1_2 := by
  intro G _ _ T L I hyp h731 hML hV U hUV hU1 hCU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h37 := a37ForSQTK_proved
  have h38 := a38ForSQTK_proved
  have h39 := a39ForSQTK_proved
  have h3228 : Stmt3_2_2_eight := stmt3_2_2_eight_proved
  have hmod : StmtFSUModule := stmtFSUModule_of_eight h3228
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  have hTM : T ≤ fsuM T L := le_sup_right.trans hU.1.2
  have hLM : L ≤ fsuM T L := le_sup_left.trans hU.1.2
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTM.trans hML
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hTI := isTISetUnder_of_stmt3_2_5_of_le_normalizer h325 hyp.fsu hTL
  have hE := hypE61_of_ti h37 h38 h39 hmod h3228 hyp hTI
  have hCN : fsuM T L ⊓ Subgroup.centralizer (U : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := E6.inf_centralizer_le_normalizer_of_le hE hU1 hUV
  have hVC : fsuV T I ≤ Subgroup.centralizer (U : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun u hu => by
      have := hV.1
      exact setLike_mul_comm (hUV hu) hv
  by_contra hneg
  obtain ⟨hnA, hny⟩ := not_or.1 hneg
  apply hCU
  refine E6.e6_27 hPT hE hU1 hUV (j := 1) Nat.one_pos ?_ ?_ ?_ ?_
  ·
    have hm2 := two_le_mParam_autI h37 h38 h39 hyp hV hN
    have hr := h732 G T L I hyp h731 hV
    calc ((1 : ℕ) : ℕ∞) < 2 := by norm_num
      _ ≤ (mParam (autI hV ⊤) : ℕ∞) := by exact_mod_cast hm2
      _ ≤ rParam (fsuV T I) := hr
  ·
    by_contra hJ
    obtain ⟨A, ⟨hAX, hAel, hAmax⟩, hAV⟩ : ∃ A : Subgroup G,
        (A ≤ fsuM T L ⊓ Subgroup.centralizer (U : Set G) ∧ IsElemAbelian 2 A ∧
          ∀ B : Subgroup G, B ≤ fsuM T L ⊓ Subgroup.centralizer (U : Set G) →
            IsElemAbelian 2 B → Nat.card B ≤ 2 ^ 1 * Nat.card A) ∧
        ¬ A ≤ Subgroup.centralizer (fsuV T I : Set G) := by
      by_contra hall
      push Not at hall
      exact hJ (iSup₂_le fun A hA => le_inf (hA.1.trans inf_le_left) (hall A hA))
    have hAN : A ≤ Subgroup.normalizer (fsuV T I : Set G) := hAX.trans hCN
    have hVX : fsuV T I ≤ fsuM T L ⊓ Subgroup.centralizer (U : Set G) := le_inf hE.tiSet.1 hVC
    have hsup : (A ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊔ fsuV T I ≤
        fsuM T L ⊓ Subgroup.centralizer (U : Set G) := sup_le (inf_le_left.trans hAX) hVX
    have hsupel : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊔ fsuV T I) :=
      B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left hAel) hV
        fun c hc v hv => (Subgroup.mem_centralizer_iff.1 hc.2 v hv).symm
    have hcard := card_le_two_mul_card_autI hV hAel hAN (by
      have h1 := hAmax _ hsup hsupel
      rwa [pow_one] at h1)
    exact hnA ⟨_, isFOneOffender_autI hV hAel hAN hAV hcard,
      leFixI_of_le_autI hV (hAX.trans inf_le_right) (autI_mono hV le_rfl)⟩
  ·
    refine csSup_le' fun c hc => ?_
    obtain ⟨Y, B, S, hYB, hBX, hYc, hYcard, -, -, -, -⟩ := hc
    by_contra hc1
    push Not at hc1
    obtain ⟨y, hy⟩ := hYc.exists_generator
    have hyo : orderOf (y : MulAut (IntMod (fsuV T I) hV)) = 2 ^ c - 1 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYcard]
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    have hk1 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    have hyX : (y : MulAut (IntMod (fsuV T I) hV)) ∈
        autI hV (fsuM T L ⊓ Subgroup.centralizer (U : Set G)) := hBX (hYB y.2)
    refine hny ⟨_, autI_mono hV le_top hyX, ?_, ?_,
      leFixI_of_le_autI hV inf_le_right (Subgroup.zpowers_le.2 hyX)⟩
    · intro h1
      rw [h1, orderOf_one, hpow] at hyo
      omega
    · rw [hyo, hpow]
      exact ⟨2 ^ k - 1, by omega⟩
  ·
    intro X hXM hX1 hXab hXodd
    obtain ⟨hVX, hred, -⟩ := h3228 G T L I hyp.fsu
    have hLL : conjClosure L T = L := hL0
    rw [hLL] at hVX hred
    have hcomm := commutator_fsuV_fsuL0 hyp.fsu hN
    rw [hL0] at hcomm
    have hXc : IsMulCommutative ↥X := ⟨⟨fun a b => Subtype.ext (hXab a a.2 b b.2)⟩⟩
    have hHyp := remark_4_4_2 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      hU.1.1 hTM hyp.fsu.maximal hyp.fsu.faithful hLM hyp.fsu.quasisimple hML hVX hred
      hcomm.symm (fsuV_ne_bot hyp.fsu) (hXM.trans inf_le_left) (hXM.trans inf_le_right) hX1 hXc
      hXodd
    rcases stmt4_4_3Orbit_iff'.1 h443 G T (fsuM T L) L X ⊥ (fsuV T I) hHyp with
      hNX | ⟨-, -, hcases⟩
    · exact hNX
    · exfalso
      rcases hcases with ⟨⟨hc, hFF⟩, -⟩ | ⟨m, hm1, -, hc, horth⟩ | ⟨-, hc, hfano⟩
      · obtain ⟨hc', hnFF⟩ := not_isFFModule_autOn_sup h37 h38 h39 hyp hV hN
        rw [hL0] at hnFF
        exact hnFF hFF
      · exact not_orth hyp hm1 ⟨hc, by rw [hL0]; exact horth⟩
      · exact not_fano_of_fixedPointFree h325 hyp hTL hN ⟨hc, by rw [hL0]; exact hfano⟩

end CFSG.Quasithin.H13
