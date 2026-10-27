module

public import CFSG.Milestones.ASVolI.C137.SJ
public import CFSG.Milestones.ASVolI.C137.A6Ent
public import CFSG.Milestones.ASVolI.C135.WMain
public import CFSG.Milestones.ASVolI.C137.Cases
public import CFSG.Milestones.ASVolI.C137.Setup
public import CFSG.Quasithin.H13.GoldschmidtC137L32Blk
public import CFSG.Quasithin.H13.GoldschmidtC137L32Lie
public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.Quasithin.H13.GoldschmidtC137Tail

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.ASVolI.ChC
open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137

variable {G : Type} [Group G]

theorem burnsideC137_card_sumNat {A V Z : Subgroup G} {F : Type} [Field F] [Fintype F]
    {Γ' : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ'} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModulesVia A V Z α dual k) :
    Nat.card V = Nat.card Z * Fintype.card F ^ (3 * k) := by
  obtain ⟨-, hZV, β, hβ, hker, -⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at h1
  rw [h1, mul_comm]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]

theorem burnsideC137_card_field {L : Subgroup G} (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) :
    Fintype.card F = 2 := by
  have : Finite F := Finite.of_fintype F
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα.1).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hα.2).toEquiv]
    exact card_of_psl32 hlie
  rw [← Nat.card_eq_fintype_card]
  exact card_eq_two_of_card_SL3 hSL

theorem burnsideC137_rkIdx_of_card {W : Type} [CommGroup W] [Finite W] (H : Subgroup W) {a : ℕ}
    (hW : Nat.card W = 2 ^ 6) (hH : Nat.card H = 2 ^ a) : rkIdx H = 6 - a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := rk_add_rkIdx H
  unfold rk at h
  rw [hW, hH, padicValNat.prime_pow, padicValNat.prime_pow] at h
  omega

namespace burnsideC137_SCtx

variable [Finite G] {X T L P U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (h : burnsideC137_SCtx X T L P U α U₁ U₂ β₁ β₂)
include h

theorem hLC : L ⊓ centralizer (U : Set G) = pCoreOf 2 L := by
  refine le_antisymm (fun l hl => ?_) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) h.hOLC)
  have hk : (⟨l, hl.1⟩ : ↥L) ∈ (C124.starHom h.hU L (burnsideC137_LN h.hs)).ker := by
    rw [C124.ker_starHom, Subgroup.mem_subgroupOf]
    exact hl
  rw [burnsideC137_ker_starHom h.hs h.hU, h.hs.alpha_ker] at hk
  exact ⟨_, hk, rfl⟩

theorem baumCtx (hL2 : CharTwo L) : BaumCtx X T U L P where
  hT := h.hT
  hprod := h.hprod
  hL := h.hL
  hL2 := hL2
  hLq := Or.inl (isQuasisimple_L32 h.lie)
  hLie := isRankTwoLie2Derived_L32 h.lie
  hTP := h.hTP
  hPX := h.hPX
  hred := h.hred
  hVL := h.hVL
  hB := by
    rw [h.hLC, ← pCoreOf_subgroupOf_eq h.hLX]
    exact pCoreOf_le_oTwoPhi _

theorem fixV_L : fixV (autI h.hU L) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  exact burnsideC137_fixL h.hs h.hU m fun l hl => hm _ (convI_mem_autI h.hU l.2 hl)

theorem hC (hRL : autI h.hU (pCoreOf 2 P) ≤ autI h.hU L) :
    ∀ B, ¬ IsStrongFFStarOffender (autI h.hU (pCoreOf 2 P)) B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro B ⟨hoff, hlt⟩
  have hBL : B ≤ autI h.hU L := hoff.1.trans hRL
  have hsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact hoff.2.2.1.2 b hb
  have hc : Nat.card (IntMod U h.hU) ≤ Nat.card B * Nat.card (fixV B) := by
    have := hoff.2.2.2 ⊥ bot_le
    rw [Subgroup.card_bot, one_mul, B5.fixV_bot_eq_top, Subgroup.card_top] at this
    exact this
  obtain ⟨-, -, -, h4, h16⟩ := burnsideC137_offender h.hs h.hU hBL hoff.2.1 hsq hc
  have hrk : rk B = 2 := by
    unfold rk
    rw [h4, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hrkI : rkIdx (fixV B) = 2 :=
    burnsideC137_rkIdx_of_card _ (by rw [burnsideC137_card_U h.hs h.hU]; norm_num)
      (a := 4) (by rw [h16]; norm_num)
  unfold rAV at hlt
  rw [hrk, hrkI] at hlt
  norm_num at hlt

theorem hDE (hL2 : CharTwo L) {A₀ : Subgroup G} (hA₀ : IsMaxElemAbelian (pCoreOf 2 P) A₀)
    {S : Finset Vec} (hS : IsPlane S)
    (hAS : ∀ a : ↥(autI h.hU L), (a : MulAut (IntMod U h.hU)) ∈ autI h.hU A₀ ↔
      burnsideC137_ψ h.hs h.hU a ∈ BS S)
    (h16 : Nat.card (fixV (autI h.hU A₀)) = 16)
    (hRA : autI h.hU (pCoreOf 2 P) = autI h.hU A₀) :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod U h.hU))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI h.hU L, B1.conjAut g (Y i) ≤ autI h.hU (pCoreOf 2 P)) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn h.hU (L ⊔ pCoreOf 2 P) (Y i))) ∧
      (∀ i, Y i = autI h.hU (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 (pCoreOf 2 P)) ∧
      autI h.hU L ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI h.hU L)) ∧
      ∀ A, IsFFStarOffender (autI h.hU (pCoreOf 2 P)) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod U h.hU))), A = ⨆ k, Ai k ∧
          ∀ k, IsFFStarOffender (autI h.hU (pCoreOf 2 P)) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI h.hU L, Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI h.hU (pCoreOf 2 P) := by
  have hA2 := (h.baumCtx hL2).hA2
  obtain ⟨t₀, ht₀B, ht₀⟩ : ∃ t ∈ BS S, IsInvol t := by
    obtain ⟨t, ht, htS⟩ := exists_invol_fixS S hS
    exact ⟨t, burnsideC137_mem_BS.2 fun v hv => by
      rw [← htS] at hv
      exact burnsideC137_mem_fixS.1 hv, ht⟩
  obtain ⟨g₂, g₃, hgen⟩ := exists_gen_conjΓ t₀ ht₀
  set c : Fin 3 → Γ := ![1, g₂, g₃] with hc
  choose ℓ hℓ using fun i => h.hs.alpha_onto (c i)
  set cs : Fin 3 → MulAut (IntMod U h.hU) := fun i => convI h.hU ⟨ℓ i, h.hLN (ℓ i).2⟩ with hcs
  have hcsL : ∀ i, cs i ∈ autI h.hU L := fun i => convI_mem_autI h.hU (ℓ i).2 _
  have hψc : ∀ i, burnsideC137_ψ h.hs h.hU ⟨cs i, hcsL i⟩ = c i := fun i => by
    rw [burnsideC137_ψ_conv h.hs h.hU (ℓ i)]
    exact hℓ i
  set Y₀ := autI h.hU A₀ with hY₀
  have hpieces := fun i => exists_Dpiece h.hU h.hXN h.hLX h.hRX h.hR2 hA2 hA₀ (ℓ i).2
  have hY0R : Y₀ ≤ autI h.hU (pCoreOf 2 P) := hRA.ge
  have hfixY : ∀ i, rkIdx (fixV (B1.conjAut (cs i) Y₀)) = 2 := by
    intro i
    refine burnsideC137_rkIdx_of_card _ (a := 4)
      (by rw [burnsideC137_card_U h.hs h.hU]; norm_num) ?_
    rw [B1.fixV_conjAut, Subgroup.card_map_of_injective (f := (cs i).toMonoidHom)
      (by exact (cs i).injective), h16]
    norm_num
  have hfixL : rkIdx (fixV (autI h.hU L)) = 6 := by
    refine burnsideC137_rkIdx_of_card _ (a := 0)
      (by rw [burnsideC137_card_U h.hs h.hU]; norm_num) ?_
    rw [h.fixV_L, Subgroup.card_bot]
    norm_num
  refine ⟨3, fun i => B1.conjAut (cs i) Y₀,
    fun i => cjSub (ℓ i) (starPreIn h.hU (pCoreOf 2 P) Y₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(cs i)⁻¹, Subgroup.inv_mem _ (hcsL i), ?_⟩
    rw [B1.conjAut_inv_conjAut]
    exact hY0R
  · intro i
    exact ⟨(hpieces i).1, (hpieces i).2.1⟩
  · intro i
    exact (hpieces i).2.2.1
  · intro i
    exact (hpieces i).2.2.2
  · intro φ hφ
    set H := ⨆ i, B1.conjAut (cs i) Y₀ with hH
    have hgens : ∀ i : Fin 3, (((burnsideC137_ψ h.hs h.hU).symm (c i * t₀ * (c i)⁻¹) :
        ↥(autI h.hU L)) : MulAut (IntMod U h.hU)) ∈ H := by
      intro i
      refine (le_iSup (fun i => B1.conjAut (cs i) Y₀) i) ?_
      rw [B1.mem_conjAut]
      have hx : (burnsideC137_ψ h.hs h.hU).symm (c i * t₀ * (c i)⁻¹) =
          ⟨cs i, hcsL i⟩ * (burnsideC137_ψ h.hs h.hU).symm t₀ * (⟨cs i, hcsL i⟩)⁻¹ := by
        rw [MulEquiv.symm_apply_eq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hψc]
      rw [hx]
      have e : (cs i)⁻¹ * ((⟨cs i, hcsL i⟩ * (burnsideC137_ψ h.hs h.hU).symm t₀ *
          (⟨cs i, hcsL i⟩)⁻¹ : ↥(autI h.hU L)) : MulAut (IntMod U h.hU)) * cs i =
          (((burnsideC137_ψ h.hs h.hU).symm t₀ : ↥(autI h.hU L)) : MulAut (IntMod U h.hU)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact (hAS _).2 (by rw [MulEquiv.apply_symm_apply]; exact ht₀B)
    have hclos : Subgroup.closure ({t₀, g₂ * t₀ * g₂⁻¹, g₃ * t₀ * g₃⁻¹} : Set Γ) ≤
        (H.subgroupOf (autI h.hU L)).map (burnsideC137_ψ h.hs h.hU).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx <;> rw [hx]
      · refine Subgroup.mem_map.2
          ⟨(burnsideC137_ψ h.hs h.hU).symm (c 0 * t₀ * (c 0)⁻¹), hgens 0, ?_⟩
        simp [hc]
      · refine Subgroup.mem_map.2
          ⟨(burnsideC137_ψ h.hs h.hU).symm (c 1 * t₀ * (c 1)⁻¹), hgens 1, ?_⟩
        simp [hc]
      · refine Subgroup.mem_map.2
          ⟨(burnsideC137_ψ h.hs h.hU).symm (c 2 * t₀ * (c 2)⁻¹), hgens 2, ?_⟩
        simp [hc]
    rw [hgen] at hclos
    obtain ⟨a, ha, hae⟩ := hclos (Subgroup.mem_top (burnsideC137_ψ h.hs h.hU ⟨φ, hφ⟩))
    have : a = ⟨φ, hφ⟩ := (burnsideC137_ψ h.hs h.hU).injective hae
    rw [this] at ha
    exact ha
  · rw [Fin.sum_univ_three, hfixY, hfixY, hfixY, hfixL]
  · intro A hA
    refine ⟨1, fun _ => A, by rw [iSup_const], fun _ => ⟨hA, 0, (cs 0)⁻¹,
      Subgroup.inv_mem _ (hcsL 0), ?_, ?_⟩⟩
    · rw [B1.conjAut_inv_conjAut, ← hRA]
      exact hA.1
    · rw [B1.conjAut_inv_conjAut, ← hRA]

theorem hUL' : U ≤ L := by
  rw [← h.hUL]
  refine Subgroup.commutator_le.2 fun w hw l hl => ?_
  have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.hn (h.hUX hw)) l).1 hl
  have : w * l * w⁻¹ * l⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem hl)
  simpa [commutatorElement_def] using this

theorem hUO : U ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.hUL' (h.hLX.trans h.hXN)
    (B2F.isPGroup_of_isElemAbelian h.hU)

theorem pCoreOf_le_sup {S : Subgroup G} (hSX : S ≤ X) : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := by
  have hSnOL : S ≤ normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    hSX.trans (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hSnOL)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem pCoreOf_sup_le_centralizer {S : Subgroup G} (hSX : S ≤ X) :
    pCoreOf 2 (L ⊔ S) ≤ centralizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pCoreOf 2 (L ⊔ S) with hN
  have hLSX : L ⊔ S ≤ X := sup_le h.hLX hSX
  have hNX : N ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hLSX
  have hNL : N ⊓ L ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun l hl => H13.U3.GC137.mem_normalizer_inf_gc
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ S) ((le_sup_left : L ≤ L ⊔ S) hl))
        (Subgroup.le_normalizer hl))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ S)).to_le inf_le_left)
  intro n hn
  refine h.mem_cent (hNX hn) fun l hl => h.hOLC (hNL ⟨?_, ?_⟩)
  · have h1 : l * n⁻¹ * l⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ S) ((le_sup_left : L ≤ L ⊔ S) hl))
        n⁻¹).1
        (N.inv_mem hn)
    have := N.mul_mem hn h1
    simpa [mul_assoc] using this
  · have hnL : n ∈ normalizer (L : Set G) := h.hn (hNX hn)
    have h1 : n * l * n⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hnL l).1 hl
    exact L.mul_mem h1 (L.inv_mem hl)

theorem zFacts {S : Subgroup G} (hSX : S ≤ X) : ZFacts L (pCoreOf 2 (L ⊔ S)) U 1 1 :=
  ⟨le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ S)),
    isPerfect_of_commutator_eq_gc (perfect_of_mem_cComp h.hL), one_mem _,
    fun n _ => by group, h.hUO.trans (h.pCoreOf_le_sup hSX), fun n hn w hw =>
      (Subgroup.mem_centralizer_iff.1 (h.pCoreOf_sup_le_centralizer hSX hn) w hw).symm,
    h.hUL, one_mem _⟩

theorem eq_c134Q {S : Subgroup G} (hSX : S ≤ X) {i : ℕ}
    (hi : MS93.burnsideC134w_CaseWeak i (L ⊔ S) S L) : U = c134Q (L ⊔ S) L := by
  have D := h.zFacts hSX
  have hU64 : Nat.card U = 64 := h.card_U
  have hUQ : U ≤ c134Q (L ⊔ S) L := D.hWQ
  rcases hi with ⟨hi4, hi'⟩ | ⟨rfl, hi'⟩
  · rcases i with _ | _ | _ | _ | _ | _ | i
    · exact (hi' : False).elim
    ·
      exfalso
      obtain ⟨-, n, F, hF, hFin, -, hnat⟩ := hi'
      rw [isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le] at hnat
      obtain ⟨α', hα', hker, hsum⟩ := hnat
      have hF2 := burnsideC137_card_field h.lie (α := α') ⟨hα', hker⟩
      have hc := burnsideC137_card_sumNat hsum
      rw [Subgroup.card_bot, hF2] at hc
      have := Subgroup.card_le_of_le hUQ
      rw [hc, hU64] at this
      norm_num at this
    ·
      obtain ⟨⟨n, F, hF, hFin, α', -, hα', hsum⟩, -⟩ := hi'
      have hF2 := burnsideC137_card_field h.lie hα'
      have hc := burnsideC137_card_sumNat hsum
      rw [Subgroup.card_bot, hF2] at hc
      exact Subgroup.eq_of_le_of_card_ge hUQ (by rw [hc, hU64]; norm_num)
    ·
      exfalso
      obtain ⟨⟨n, F, hF, hFin, α', -, hα', hsum, -⟩, -⟩ := hi'
      have hF2 := burnsideC137_card_field h.lie hα'
      have hc := burnsideC137_card_sumNat hsum
      rw [Subgroup.card_bot, hF2] at hc
      have hUZ : U ≤ centerOf (c134Q (L ⊔ S) L) := D.hWZ
      have := Subgroup.card_le_of_le hUZ
      rw [hc, hU64] at this
      norm_num at this
    · exact absurd rfl hi4
    ·
      exfalso
      obtain ⟨⟨α', -, h2, hsum⟩, -⟩ := hi'
      have hc := burnsideC137_card_sumNat hsum
      rw [h2, ZMod.card] at hc
      have := Subgroup.card_le_of_le hUQ
      rw [hc, hU64] at this
      norm_num at this
    · exact (hi' : False).elim
  ·
    exfalso
    obtain ⟨⟨n, F, hF, hFin, α', -, hα', -, -, hsum⟩, -, -⟩ := hi'
    have hF2 := burnsideC137_card_field h.lie hα'
    have hc := burnsideC137_card_sumNat hsum
    rw [Subgroup.card_bot, hF2] at hc
    have hUZ : U ≤ ⁅centerOf (c134Q (L ⊔ S) L), L⁆ := D.hWU
    have := Subgroup.card_le_of_le hUZ
    rw [hc, hU64] at this
    norm_num at this

theorem eq_comm_pCore {S : Subgroup G} (hSX : S ≤ X) (hQ : U = c134Q (L ⊔ S) L) :
    U = ⁅pCoreOf 2 L, L⁆ := by
  refine le_antisymm ?_ ?_
  · rw [← h.hUL]
    exact Subgroup.commutator_mono h.hUO le_rfl
  · rw [hQ]
    exact Subgroup.commutator_mono (h.pCoreOf_le_sup hSX) le_rfl

theorem core (hSQ : SQTKGroup ↥X) (hL2 : CharTwo L)
    (hC134 : MS93.burnsideC134w_AS_C_1_34_corrOneWeak) :
    (∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum (pCoreOf 2 P) ∧
        (D.subgroupOf (baum (pCoreOf 2 P))).Characteristic ∧ X ≤ normalizer (D : Set G)) ∨
    (U = ⁅pCoreOf 2 L, L⁆ ∧
      ∃ (ℓ : Submodule (ZMod 2) Vec)
        (coordinates : ∀ I : {I : Subgroup G // I ∈ internalIrrPlus L U},
          ↥I.val →* Multiplicative Vec),
        Module.finrank (ZMod 2) ℓ = 2 ∧ (∀ I, IsNatVia L I.val ⊥ α (coordinates I)) ∧
        P = X ⊓ ⨅ I : {I : Subgroup G // I ∈ internalIrrPlus L U},
          normalizer (preimageIn I.val (coordinates I) ℓ : Set G)) := by
  set R := pCoreOf 2 P with hR
  by_cases hCN : ∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum R ∧ (D.subgroupOf (baum R)).Characteristic ∧
      X ≤ normalizer (D : Set G)
  · exact Or.inl hCN
  right
  have hn1 : ∀ C : Subgroup G, C ≤ baum R → C ≠ ⊥ → (C.subgroupOf (baum R)).Characteristic →
      ¬ X ≤ normalizer (C : Set G) := fun C hCS hC0 hCc hCn => hCN ⟨C, hC0, hCS, hCc, hCn⟩
  obtain ⟨⟨-, hQC⟩, -, -, hbranch⟩ := h.hb2102
  rcases hbranch with hbq | ⟨hst, -, -⟩
  · exact absurd (C124.concl1_of_baum_eq h.hT h.hred h.hQR h.hRT h.hVL hbq) hCN
  by_cases hJ : thompsonJ R ≤ centralizer (U : Set G)
  · refine absurd (C124.concl1_of_baum_eq h.hT h.hred h.hQR h.hRT h.hVL ?_) hCN
    have hJR : thompsonJ R ≤ R ⊓ centralizer (U : Set G) := le_inf (thompsonJ_le_self R) hJ
    rw [← hQC] at hJR
    rw [baum_eq_baum_centralizer h.hU h.hUR (hQC ▸ hJR), hQC]
  obtain ⟨A₀, S, hA₀, hS, hBL, hAS, h16, hJeq⟩ := h.jStruct hst hJ
  have hstab := fun x (hx : x ∈ P) => h.pStab hS hAS hJeq hx
  obtain ⟨hc3, hLP⟩ := h.concl3 hS hstab
  have hRle := h.autR_le hS hAS hstab hLP
  have hRA : autI h.hU R = autI h.hU A₀ := le_antisymm hRle (autI_mono h.hU hA₀.1)
  have hRS : autI h.hU R ≤ autI h.hU (baum R) := by
    rw [hRA, ← hJeq]
    exact autI_mono h.hU (B2F.thompsonJ_le_baum R)
  have hC := h.hC (hRA ▸ hBL)
  have hDE := h.hDE hL2 hA₀ hS hAS h16 hRA
  obtain ⟨hMS, hLcomp, hset, -, -, -⟩ := (h.baumCtx hL2).ms_tail hSQ hn1 hRS hC hDE
  obtain ⟨α', hα'⟩ := exists_modO2Surj_L32 h.lie
  obtain ⟨i, hi⟩ := hC134 G (L ⊔ baum R) (baum R) L hMS hLcomp hset
    ⟨ZMod 2, inferInstance, inferInstance, α', by simp, hα'⟩
  have hSX : baum R ≤ X := (inf_le_left : baum R ≤ R).trans h.hRX
  exact ⟨h.eq_comm_pCore hSX (h.eq_c134Q hSX hi), hc3⟩

end burnsideC137_SCtx

section Canonical

set_option linter.unusedSectionVars false


theorem burnsideC137_caseL32Sum
    : burnsideC137_CaseL32Sum := by
  intro G _ _ X T L P M V hyp hpsl hsum
  obtain ⟨α, U₁, U₂, β₁, β₂, hs⟩ := hsum
  obtain ⟨hXLT, hT, hL, hX, -, hdyn, hTP, hPM, hM, hPeq, hred, hVL, -⟩ := hyp
  have hprod := burnsideC137_prod hXLT
  have hL2 := burnsideC137_charTwo_L hL hX
  have hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  obtain ⟨hMX, hmax⟩ := burnsideC137_max hM
  have hP : P = M := hPeq.resolve_right fun h =>
    not_hatA6_of_psl32 hlie ⟨h.1.1.1, h.1.2.1, h.1.2.2⟩
  subst hP
  have hSQ : SQTKGroup ↥X := c137SQTKSupply_holds G X T L hX hT hprod hL hL2 (Or.inl hlie)
  obtain ⟨hred', hUL, -⟩ :=
    burnsideC137_a6_reduce hred hT hprod hL (isQuasisimple_L32 hlie) hVL
  have ctx : burnsideC137_SCtx X T L P ⁅V, L⁆ α U₁ U₂ β₁ β₂ :=
    ⟨hT, hprod, hL, hlie, hTP, hMX, hmax, hred', hUL, hs, hdyn.2.1 hpsl⟩
  rcases ctx.core hSQ hL2 MS93.burnsideC134w_corrOneWeak with hc1 | ⟨hQ, ℓ, crd, hℓ, hnat, hPeq'⟩
  · exact Or.inl hc1
  · exact Or.inr (Or.inr (Or.inl ⟨hpsl, hQ, α, U₁, U₂, β₁, β₂, hs, ℓ, crd, hℓ, hnat, hPeq'⟩))

end Canonical

end CFSG.ASVolI
