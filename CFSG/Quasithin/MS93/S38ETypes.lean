module

public import CFSG.Quasithin.MS93.S38EFFHyp
public import CFSG.Quasithin.MS93.S32Types
public import CFSG.Quasithin.MS93.SkItems
public import CFSG.Quasithin.EmptyFaithful.S151S9P2A
public import CFSG.Quasithin.MS93.S32U

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem card_lstar_of_surjective (h : PUHyp M T L) {Q : Type} [Group Q] (f : ↥L →* Q)
    (hf : Function.Surjective f) (hO : CFSG.pCore 2 ↥L ≤ f.ker) (hQ : ∃ x : Q, x ≠ 1) :
    Nat.card (S32.Lstar L) = Nat.card (Q ⧸ Subgroup.center Q) := by
  set fb : ↥L ⧸ CFSG.pCore 2 ↥L →* Q := QuotientGroup.lift _ f hO
  have hfbs : Function.Surjective fb := by
    intro y
    obtain ⟨l, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hfbn : ∃ k, fb k ≠ 1 := by
    obtain ⟨x, hx⟩ := hQ
    obtain ⟨k, rfl⟩ := hfbs x
    exact ⟨k, hx⟩
  exact Nat.card_congr (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple
    h.quasisimple hfbs (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple
      hfbn)).toEquiv

theorem pCore_centralizes_of_le_Xq (h : PUHyp M T L) {U : Subgroup G} (hU : U ≤ Xq M)
    {o : ↥L} (ho : o ∈ CFSG.pCore 2 ↥L) {u : G} (hu : u ∈ U) : (o : G) * u * (o : G)⁻¹ = u := by
  have hoM : (o : G) ∈ pCoreOf 2 M :=
    pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer (mem_pCoreOf_of_mem_pCore_two ho)
  have hc := Subgroup.mem_centralizer_iff.mp
    (((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right) (hU hu)) _ hoM
  rw [hc, mul_inv_cancel_right]

omit [Finite G] in
theorem eq_one_of_isSumOfNaturalModulesVia {A V Z : Subgroup G} {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ} {k : ℕ} (hk : 0 < k)
    (hnat : IsSumOfNaturalModulesVia A V Z α false k) {a : ↥A}
    (ha : ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ = v) : α a = 1 := by
  obtain ⟨-, -, β, hβ, -, heq⟩ := hnat
  have hfix : ∀ w : Fin 3 → F, (((α a : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)).mulVec w = w := by
    intro w
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ => w)
    have h1 := heq a u u (by rw [Subgroup.coe_inv, ha u u.2]) ⟨0, hk⟩
    simp only [moduleAct, Bool.false_eq_true, ↓reduceIte, hu, toAdd_ofAdd] at h1
    exact h1.symm
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (hfix (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simp only [Matrix.col_apply] at this
  rw [this]
  simp [Matrix.one_apply, Pi.single_apply]

theorem card_lstar_of_isHatA6U (h : PUHyp M T L) (hX : IsHatA6U M T L) :
    Nat.card (S32.Lstar L) = 360 := by
  obtain ⟨-, -, hU, hhat⟩ := hX
  exact S32.card_lstar_of_hat (S32.isSecW_Uq h) h hhat

theorem card_lstar_of_isAltSix (h : PUHyp M T L)
    (hX : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) : Nat.card (S32.Lstar L) = 360 := by
  rcases hX with ⟨-, N, hA⟩ | ⟨hk, -⟩
  · obtain ⟨-, α, hα, -, -⟩ := hA
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hO : CFSG.pCore 2 ↥L ≤ α.ker := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
      have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
      have hN : ((CFSG.pCore 2 ↥L).map α).Normal := hn.map α hα
      have := hs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map α) with hb | ht
      · exact (Subgroup.map_eq_bot_iff _).mp hb
      · exfalso
        have h2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥L).map α) := hp.map α
        rw [ht] at h2
        have h2' : IsPGroup 2 ↥(alternatingGroup (Fin 6)) :=
          h2.of_equiv Subgroup.topEquiv
        have hcard := H13.card_alternatingGroup_fin 6 (by norm_num)
        obtain ⟨n, hn⟩ := h2'.exists_card_eq
        rw [hcard] at hn
        have h5 : (5 : ℕ) ∣ 2 ^ n := by
          rw [← hn]
          norm_num
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
          ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h5))
        omega
    have hnt : Nontrivial ↥(alternatingGroup (Fin 6)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        rw [H13.card_alternatingGroup_fin 6 (by norm_num)]
        norm_num)
    rw [card_lstar_of_surjective h α hα hO (exists_ne 1)]
    exact card_quot_of_equiv_alt6 (MulEquiv.refl _)
  · omega

theorem pCore_le_ker_of_nat (h : PUHyp M T L) {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥L →* ↥Γ} {k : ℕ} (hk : 0 < k)
    {Z : Subgroup G} (hnat : IsSumOfNaturalModulesVia L (Uq M T L) Z α false k) :
    CFSG.pCore 2 ↥L ≤ α.ker := fun _ ho =>
  eq_one_of_isSumOfNaturalModulesVia hk hnat fun _ hu =>
    pCore_centralizes_of_le_Xq h h.Uq_le_Xq ho hu

theorem card_lstar_of_nat (h : PUHyp M T L) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) {k : ℕ}
    (hk : 0 < k) {Z : Subgroup G} (hnat : IsSumOfNaturalModulesVia L (Uq M T L) Z α false k) :
    1 ≤ n ∧ Nat.card (S32.Lstar L) = CFSG.Open.ordA 2 (2 ^ n) := by
  obtain ⟨hn, -, hc⟩ := isPSL_quot_of_equiv_statedSL_three hF (MulEquiv.refl _)
  have hnt : Nontrivial ↥(StatedSL 3 F) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have h1 : Nat.card (↥(StatedSL 3 F) ⧸ Subgroup.center ↥(StatedSL 3 F)) = 1 :=
      Nat.card_unique
    have h3 : 8 ≤ CFSG.Open.ordA 2 (2 ^ n) := by
      obtain ⟨r, hr, hr'⟩ := two_part_ordA_two hn
      rw [hr']
      have : 2 ^ 3 ≤ 2 ^ (n * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 1 ≤ r := hr.pos
      nlinarith
    omega
  exact ⟨hn, (card_lstar_of_surjective h α hα (pCore_le_ker_of_nat h hk hnat)
    (exists_ne 1)).trans hc⟩

theorem card_lstar_of_isDoubleSL3U (h : PUHyp M T L) (hX : IsDoubleSL3U M T L) :
    ∃ n, 1 ≤ n ∧ Nat.card (S32.Lstar L) = CFSG.Open.ordA 2 (2 ^ n) := by
  obtain ⟨-, -, n, F, _, _, α, hF, hα, hnat⟩ := hX
  exact ⟨n, card_lstar_of_nat h (by rw [Nat.card_eq_fintype_card, hF]) hα (by norm_num) hnat⟩

theorem card_lstar_of_isSL3TwoZ (h : PUHyp M T L) (hX : IsSL3TwoZ M T L) :
    Nat.card (S32.Lstar L) = CFSG.Open.ordA 2 (2 ^ 1) := by
  obtain ⟨-, -, -, α, hα, hnat⟩ := hX
  exact (card_lstar_of_nat h (by simp) hα (by norm_num) hnat).2

theorem card_lstar_of_isSL3TwoU (h : PUHyp M T L) (hX : IsSL3TwoU M T L) :
    Nat.card (S32.Lstar L) = CFSG.Open.ordA 2 (2 ^ 1) := by
  obtain ⟨-, -, ⟨α, hα, hnat⟩, -, -⟩ := hX
  have hs := HSRuLoc.Lift.isSimpleGroup_statedSL3
  set α' : ↥L →* ↥(StatedSL 3 (ZMod 2)) := α.comp (Subgroup.inclusion h.L_le)
  have hα' : Function.Surjective α' := by
    have hN : α'.range.Normal := by
      refine ⟨fun x hx y => ?_⟩
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hα y
      refine ⟨⟨(m : G) * l * (m : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (h.le_normalizer m.2) l).mp l.2⟩, ?_⟩
      simp only [α', MonoidHom.comp_apply, ← map_mul, ← map_inv]
      congr 1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α'.range with hb | ht
    · exfalso
      apply HSRuLoc.Lift.not_isPGroup_statedSL3
      intro y
      obtain ⟨m, rfl⟩ := hα y
      obtain ⟨e, he⟩ := h.exists_pow_mem_L m.2
      refine ⟨e, ?_⟩
      have h1 : α' ⟨(m : G) ^ 2 ^ e, he⟩ ∈ α'.range := ⟨_, rfl⟩
      rw [hb, Subgroup.mem_bot] at h1
      rw [← map_pow]
      have : m ^ 2 ^ e = Subgroup.inclusion h.L_le ⟨(m : G) ^ 2 ^ e, he⟩ := Subtype.ext (by simp)
      rw [this]
      exact h1
    · exact MonoidHom.range_eq_top.mp ht
  have hO : CFSG.pCore 2 ↥L ≤ α'.ker := fun o ho =>
    eq_one_of_isSumOfNaturalModulesVia (A := M) (by norm_num) hnat
      (a := Subgroup.inclusion h.L_le o) fun _ hu =>
        pCore_centralizes_of_le_Xq h h.Uq_le_Xq ho hu
  obtain ⟨-, -, hc⟩ := isPSL_quot_of_equiv_statedSL_three (F := ZMod 2) (n := 1)
    (by simp) (MulEquiv.refl _)
  have hnt : Nontrivial ↥(StatedSL 3 (ZMod 2)) := hs.toNontrivial
  exact (card_lstar_of_surjective h α' hα' hO (exists_ne 1)).trans hc

section Module

variable {F : Type} [CommGroup F] {ρ : ↥M →* MulAut F}

theorem IsIrrRep.card_quot_center (hρ : IsIrrRep L ρ) (h : PUHyp M T L) :
    Nat.card (↥(IsIrrRep.imL L ρ) ⧸ Subgroup.center ↥(IsIrrRep.imL L ρ)) =
      Nat.card (S32.Lstar L) :=
  (Nat.card_congr (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple
    (hρ.quotHom_surjective h) (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      h.quasisimple (hρ.quotHom_ne_one h))).toEquiv).symm

variable (hρ : IsIrrRep L ρ) (h : PUHyp M T L)
include hρ h

theorem card_lstar_of_ffCaseSL3 (hK : FFCaseSL3 (IsIrrRep.imL L ρ)) :
    ∃ n, 1 ≤ n ∧ Nat.card (S32.Lstar L) = CFSG.Open.ordA 2 (2 ^ n) := by
  obtain ⟨n, F', _, _, hn, hF, ⟨e⟩, -, -⟩ := hK
  exact ⟨n, hn, (hρ.card_quot_center h).symm.trans
    (isPSL_quot_of_equiv_statedSL_three hF e.symm).2.2⟩

theorem card_lstar_of_ffCaseHatA6 (hK : FFCaseHatA6 (IsIrrRep.imL L ρ)) :
    Nat.card (S32.Lstar L) = 360 :=
  (hρ.card_quot_center h).symm.trans (card_quot_of_isHat hK.2.1)

theorem card_lstar_of_altNat (hK : AlternatingNatural (IsIrrRep.imL L ρ) ⊤ ⊥ 6) :
    Nat.card (S32.Lstar L) = 360 := by
  obtain ⟨π, hπ⟩ := hK
  exact (hρ.card_quot_center h).symm.trans
    (card_quot_of_equiv_alt6 (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ))

theorem card_lstar_of_sp4Nat {n : ℕ} (hn : 2 ≤ n)
    (hK : BinaryNaturalSp4 (IsIrrRep.imL L ρ) ⊤ ⊥ n) :
    Nat.card (S32.Lstar L) = CFSG.Open.ordBC 2 (2 ^ n) := by
  obtain ⟨F', _, _, hF, π, hπ⟩ := hK
  exact (hρ.card_quot_center h).symm.trans
    (card_quot_of_equiv_statedSp hF hn (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ))

theorem card_lstar_of_ffCaseG2 (hT : S32.TypeFacts)
    (hK : FFCaseG2 ρ.range (IsIrrRep.imL L ρ)) :
    (∃ n, 2 ≤ n ∧ Nat.card (S32.Lstar L) = CFSG.Open.ordG2 (2 ^ n)) ∨
      Nat.card (S32.Lstar L) = 6048 := by
  rcases hK with ⟨n, hn, F', _, _, hF, π, hπ⟩ | ⟨⟨F', _, _, hF, π, hπ⟩, -, -⟩
  · have : CharP F' 2 := FFC.charP_two_of_card_pow hF
    left
    exact ⟨n, hn, (hρ.card_quot_center h).symm.trans
      (hT.g2 _ F' n hF hn (FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ))⟩
  · have : CharP F' 2 := FFC.charP_two_of_card_pow hF
    right
    exact (hρ.card_quot_center h).symm.trans (hT.g2d _ F' (hF.trans (pow_one 2))
      (FFC.equivOfRealizes (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ))

end Module

section Orders

theorem lt_div_of_le {X D Y : ℕ} (hD1 : 1 ≤ D) (hD3 : D ≤ 3) (h : 3 * Y + 3 ≤ X) : Y < X / D := by
  have h1 : Y + 1 ≤ X / 3 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
  have h2 : X / 3 ≤ X / D := Nat.div_le_div_left hD3 hD1
  omega

theorem gcd_three_le (q : ℕ) : 1 ≤ Nat.gcd 3 (q - 1) ∧ Nat.gcd 3 (q - 1) ≤ 3 :=
  ⟨Nat.pos_of_ne_zero (fun h => by simp [Nat.gcd_eq_zero_iff] at h),
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)⟩

theorem ordBC_two_ne_ordA_two {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    CFSG.Open.ordBC 2 (2 ^ n) ≠ CFSG.Open.ordA 2 (2 ^ m) := by
  by_cases h43 : n * 4 = m * 3
  ·
    intro he
    obtain ⟨k, rfl⟩ : 3 ∣ n := by
      have : 3 ∣ n * 4 := ⟨m, by omega⟩
      exact (Nat.Coprime.dvd_mul_right (by norm_num)).mp this
    have hm' : m = 4 * k := by omega
    subst hm'
    have hk : 1 ≤ k := by omega
    rw [ordBC_two_two_pow hn, ordA_two_eq] at he
    obtain ⟨hD1, hD3⟩ := gcd_three_le (2 ^ (4 * k))
    set a : ℕ := 2 ^ (2 * k) with ha
    have ha4 : 4 ≤ a := by
      rw [ha]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : (2 ^ (3 * k)) ^ 4 = a ^ 6 := by rw [ha, ← pow_mul, ← pow_mul]; ring_nf
    have e2 : (2 ^ (3 * k)) ^ 2 = a ^ 3 := by rw [ha, ← pow_mul, ← pow_mul]; ring_nf
    have e3 : (2 ^ (4 * k)) ^ 3 = a ^ 6 := by rw [ha, ← pow_mul, ← pow_mul]; ring_nf
    have e4 : (2 ^ (4 * k)) ^ 2 = a ^ 4 := by rw [ha, ← pow_mul, ← pow_mul]; ring_nf
    rw [e1, e2, e3, e4] at he
    refine absurd he (Nat.ne_of_lt (lt_div_of_le hD1 hD3 ?_))
    have h6 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h4 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h6, h3, h4]
    have ha' : (4 : ℤ) ≤ a := by exact_mod_cast ha4
    have hpos : (0 : ℤ) ≤ (a : ℤ) ^ 6 - 1 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 4) ha' 6]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 4) ha' 3,
      pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 4) ha' 6, mul_nonneg hpos hpos,
      mul_nonneg (mul_nonneg hpos hpos) (show (0:ℤ) ≤ (a : ℤ) ^ 3 * ((a : ℤ) - 3) by
        have : (0 : ℤ) ≤ (a : ℤ) ^ 3 := by positivity
        nlinarith)]
  · exact ne_of_two_part (two_part_ordBC_two hn) (two_part_ordA_two hm) h43

theorem ordG2_ne_ordA_two {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    CFSG.Open.ordG2 (2 ^ n) ≠ CFSG.Open.ordA 2 (2 ^ m) := by
  by_cases h63 : n * 6 = m * 3
  · intro he
    have hm' : m = 2 * n := by omega
    subst hm'
    unfold CFSG.Open.ordG2 at he
    rw [ordA_two_eq] at he
    obtain ⟨hD1, hD3⟩ := gcd_three_le (2 ^ (2 * n))
    set a : ℕ := 2 ^ n with ha
    have ha2 : 2 ≤ a := by
      rw [ha]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have e3 : (2 ^ (2 * n)) ^ 3 = a ^ 6 := by rw [ha, ← pow_mul, ← pow_mul]; ring_nf
    have e2 : (2 ^ (2 * n)) ^ 2 = a ^ 4 := by rw [ha, ← pow_mul, ← pow_mul]; ring_nf
    rw [e3, e2] at he
    refine absurd he (Nat.ne_of_lt (lt_div_of_le hD1 hD3 ?_))
    have h6 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h4 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h6, h2, h4]
    have ha' : (2 : ℤ) ≤ a := by exact_mod_cast ha2
    have hp6 : (0 : ℤ) ≤ (a : ℤ) ^ 6 - 1 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 2) ha' 6]
    have hp2 : (0 : ℤ) ≤ (a : ℤ) ^ 2 - 1 := by nlinarith
    have key : (a : ℤ) ^ 4 - 1 = ((a : ℤ) ^ 2 - 1) * ((a : ℤ) ^ 2 + 1) := by ring
    rw [key]
    have h5 : (5 : ℤ) ≤ (a : ℤ) ^ 2 + 1 := by nlinarith
    have hA : (0 : ℤ) ≤ (a : ℤ) ^ 6 * ((a : ℤ) ^ 6 - 1) * ((a : ℤ) ^ 2 - 1) := by positivity
    have hA1 : (2 : ℤ) ≤ (a : ℤ) ^ 6 * ((a : ℤ) ^ 6 - 1) * ((a : ℤ) ^ 2 - 1) := by
      have : (1 : ℤ) ≤ (a : ℤ) ^ 6 - 1 := by
        nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 2) ha' 6]
      have : (1 : ℤ) ≤ (a : ℤ) ^ 2 - 1 := by nlinarith
      have : (2 : ℤ) ≤ (a : ℤ) ^ 6 := by
        nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 2) ha' 6]
      calc (2 : ℤ) = 2 * 1 * 1 := by norm_num
        _ ≤ _ := by gcongr
    have e : (a : ℤ) ^ 6 * (((a : ℤ) ^ 2 - 1) * ((a : ℤ) ^ 2 + 1) * ((a : ℤ) ^ 6 - 1)) =
        (a : ℤ) ^ 6 * ((a : ℤ) ^ 6 - 1) * ((a : ℤ) ^ 2 - 1) * ((a : ℤ) ^ 2 + 1) := by ring
    rw [e]
    nlinarith
  · exact ne_of_two_part (two_part_ordG2 hn) (two_part_ordA_two hm) h63

end Orders

end CFSG.Quasithin.MS93.S38E
