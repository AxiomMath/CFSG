module

public import CFSG.Quasithin.H13.L32A767f
public import CFSG.Quasithin.H13.L32A764d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem mem_normalizer_oTwoUpper_of_forall {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, Odd (orderOf x) → g * x * g⁻¹ ∈ oTwoUpper X) :
    g ∈ Subgroup.normalizer (oTwoUpper X : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h x hx.1 hx.2
  | one => simp
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using (oTwoUpper X).mul_mem ihx ihy
  | inv x _ ih => simpa [mul_assoc] using (oTwoUpper X).inv_mem ih

omit [Finite G] in
theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem pCoreOf_L_le_T (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two) : pCoreOf 2 L ≤ T :=
  (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 L)
      ((h.normalizes h13322).trans (normalizer_le_normalizer_pCoreOf 2 L)))
    (pCoreOf_isPGroup 2 L)).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right))

omit [Finite G] in
theorem pCoreOf_kz_le_dK : pCoreOf 2 (kz T V) ≤ dK T V := by
  intro o ho
  refine ⟨kz_le_mK (pCoreOf_le 2 _ ho), fun k hk => ?_⟩
  have hk' : k * o⁻¹ * k⁻¹ ∈ pCoreOf 2 (kz T V) :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hk) _).mp (inv_mem ho)
  rw [show o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) by group]
  exact mul_mem ho hk'

theorem pCoreOf_kz_ne_bot (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    pCoreOf 2 (kz T V) ≠ ⊥ := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hH : CharTwo (hz T V) := charTwo_of_inH h.fsu.qtke.2.1 S
    ⟨by rw [hS]; exact T_le_hz h h63, (h63 G T L V h).1.1.2⟩
  have hK : CharTwo (kz T V) := A4.charTwo_of_normal (oTwoUpper_le _) (le_normalizer_oTwoUpper _) hH
  intro h0
  obtain ⟨-, π, -, hπs, -, -⟩ := isL24Section_u0 h hMod h63
  have hKb : kz T V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ kz T V ⊓ Subgroup.centralizer (pCoreOf 2 (kz T V) : Set G) := by
      refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : w ∈ pCoreOf 2 (kz T V) := hw
      rw [h0, Subgroup.mem_bot] at hw'
      rw [hw', one_mul, mul_one]
    have h2 := hK h1
    rwa [h0] at h2
  have hc := Nat.card_le_card_of_surjective π hπs
  rw [card_sl24, hKb, Subgroup.card_bot] at hc
  omega

theorem eq_one_of_mem_dK_of_odd (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (h13322 : Stmt13_3_2_two) {y : G} (hyD : y ∈ dK T V)
    (hyM : y ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf y)) : y = 1 := by
  by_contra hy1
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Y := oTwoUpper (dK T V ⊓ M) with hYdef
  have hyY : y ∈ Y := mem_oTwoUpper_of_odd ⟨hyD, hyM⟩ hodd
  have hTH := T_le_hz h h63
  have hTL : T ≤ M := h.normalizes h13322
  have hHK : hz T V ≤ mK T V := le_normalizer_oTwoUpper _
  have hOT := pCoreOf_kz_le_T h h63
  have hODM : pCoreOf 2 (kz T V) ≤ dK T V ⊓ M := le_inf pCoreOf_kz_le_dK (hOT.trans hTL)
  have hXN : mK T V ⊓ M ≤ Subgroup.normalizer ((dK T V ⊓ M : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf_of_mem (mK_le_normalizer_dK hg.1)
      (Subgroup.le_normalizer hg.2)
  have hXY : mK T V ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    hXN.trans (normalizer_le_normalizer_oTwoUpper _)
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := (le_inf (hTH.trans hHK) hTL).trans hXY
  have hKY : kz T V ≤ Subgroup.normalizer (Y : Set G) := by
    intro k hk
    refine mem_normalizer_oTwoUpper_of_forall fun x hx hxo => ?_
    refine mem_oTwoUpper_of_odd ?_ (by rwa [orderOf_conj_eq])
    have hc : x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ ∈ pCoreOf 2 (kz T V) := (inv_mem hx.1 : x⁻¹ ∈ dK T V).2 k hk
    rw [inv_inv] at hc
    rw [show k * x * k⁻¹ = x * (x⁻¹ * k * x * k⁻¹) by group]
    exact mul_mem hx (hODM hc)
  have hP : pCoreOf 2 L ≤ Subgroup.normalizer (Y : Set G) :=
    (pCoreOf_L_le_T h h13322).trans hTY
  have hPY : oTwoUpper (pCoreOf 2 L ⊔ Y) ≤ Y := by
    refine oTwoUpper_le_of_pow_mem fun w hw => ?_
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hP] at hw
    obtain ⟨p, hp, y', hy', rfl⟩ := hw
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 L) ⟨p, hp⟩
    have hpn : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨y'', hy'', e⟩ := pow_mul_mem_of_le_normalizer (hP hp) hy' (2 ^ n)
    exact ⟨n, by rw [e, hpn, one_mul]; exact hy''⟩
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    refine mem_normalizer_oTwoUpper_of_forall fun x hx hxo => ?_
    have hc := comm_mem_pCoreOf_L_of_odd h hMod h63 h13322 (inv_mem hx.1) (inv_mem hx.2)
      (by rwa [orderOf_inv]) l hl
    rw [inv_inv] at hc
    refine hPY (mem_oTwoUpper_of_odd ?_ (by rwa [orderOf_conj_eq]))
    rw [show l * x * l⁻¹ = x * (x⁻¹ * l * x * l⁻¹) by group]
    exact mul_mem (Subgroup.mem_sup_right (mem_oTwoUpper_of_odd hx hxo))
      (Subgroup.mem_sup_left hc)
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hOX : pCoreOf 2 (kz T V) ≤ pCoreOf 2 (mK T V ⊓ M) :=
    le_pCoreOf_of_le_normalizer 2 (le_inf (kz_le_mK.trans' (pCoreOf_le 2 _)) (hOT.trans hTL))
      (inf_le_left.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hX2 : CharTwo (mK T V ⊓ M) := charTwo_of_inH h.fsu.qtke.2.1 S
    ⟨by rw [hS]; exact le_inf (hTH.trans hHK) hTL, fun h0 =>
      pCoreOf_kz_ne_bot h hMod h63 (le_bot_iff.mp (h0 ▸ hOX))⟩
  have hYX : Y ≤ mK T V ⊓ M :=
    (oTwoUpper_le _).trans (inf_le_inf (fun d hd => hd.1) le_rfl)
  have hY2 : CharTwo Y := A4.charTwo_of_normal hYX hXY hX2
  have hYO : pCoreOf 2 Y ≠ ⊥ := by
    intro h0
    have h1 : y ∈ Y ⊓ Subgroup.centralizer (pCoreOf 2 Y : Set G) := by
      refine ⟨hyY, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : w ∈ pCoreOf 2 Y := hw
      rw [h0, Subgroup.mem_bot] at hw'
      rw [hw', one_mul, mul_one]
    have h2 := hY2 h1
    rw [h0, Subgroup.mem_bot] at h2
    exact hy1 h2
  have hNY := normalizer_le_normalizer_pCoreOf 2 Y
  have hNM : Subgroup.normalizer (pCoreOf 2 Y : Set G) ≤ M := by
    obtain ⟨M', hM', hNM'⟩ := exists_quasithinIsMaxTwoLocal_ge
      (⟨pCoreOf 2 Y, hYO, pCoreOf_isPGroup 2 Y, rfl⟩ :
        IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)))
    have hM'' : quasithinIsMaxTwoLocal M' := ⟨hM'.1, fun H hH hMH => hM'.2 H hH hMH⟩
    have he := (h13322 G T L h.hyp.h13 L h.fsu.faithful).2.2.2 M' hM''
      (((sup_le hLY hTY).trans hNY).trans hNM')
    rw [hMdef, ← he]
    exact hNM'
  apply (h63 G T L V h).1.2.1
  rw [(h63 G T L V h).2.2.1]
  exact sup_le ((hKY.trans hNY).trans hNM) hTL

theorem inf_dK_le_T (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h13322 : Stmt13_3_2_two) : dK T V ⊓ Subgroup.normalizer (L : Set G) ≤ T := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hTH := T_le_hz h h63
  have hTL : T ≤ M := h.normalizes h13322
  have hHK : hz T V ≤ mK T V := le_normalizer_oTwoUpper _
  have hp : IsPGroup 2 ↥(dK T V ⊓ M) := by
    refine IsPGroup.of_card_dvd_pow (n := Nat.card ↥(dK T V ⊓ M))
      (Nat.dvd_pow_self_iff Nat.card_pos.ne' two_ne_zero |>.mpr fun q hq => ?_)
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqp⟩) hqdvd
    by_cases hq2 : q = 2
    · rw [hq2]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_refl 2, two_ne_zero⟩
    exfalso
    have hodd : Odd (orderOf (x : G)) := by
      rw [Subgroup.orderOf_coe, hx]
      exact hqp.odd_of_ne_two hq2
    have hx1 := eq_one_of_mem_dK_of_odd h hMod h63 h13322 (Subgroup.mem_inf.mp x.2).1
      (Subgroup.mem_inf.mp x.2).2 hodd
    have : orderOf x = 1 := by rw [← Subgroup.orderOf_coe, hx1, orderOf_one]
    rw [this] at hx
    exact hqp.one_lt.ne hx
  have hXN : mK T V ⊓ M ≤ Subgroup.normalizer ((dK T V ⊓ M : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf_of_mem (mK_le_normalizer_dK hg.1)
      (Subgroup.le_normalizer hg.2)
  have hDO : dK T V ⊓ M ≤ pCoreOf 2 (mK T V ⊓ M) :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_inf (fun d hd => hd.1) le_rfl) hXN hp
  exact hDO.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_le h (le_inf (hTH.trans hHK) hTL)))

end CFSG.Quasithin.H13.L32A
