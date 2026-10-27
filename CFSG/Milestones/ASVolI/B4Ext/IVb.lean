module

public import CFSG.Milestones.ASVolI.B4Ext.IVa
public import CFSG.Milestones.ASVolI.B4Ext.Main
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Milestones.ASVolI.B4Ext.Psi

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section IVb

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Type} [Field K]
  [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL 5 K) →* ↥G}

include hV in
theorem burnsideB49x_five_rAV_ge (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 5 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {B : Subgroup (MulAut V)}
    (hB : IsFFStarOffender G B) : ((5 / 6 : ℚ)) ≤ rAV B := by
  set hG := burnsideB49_hG hreal with hGdef
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  obtain ⟨-, hcases, -, hup⟩ := burnsideB49x_five_quad hV hK hreal hdual hB.1 hB.2.2.1 hB.2.1
    (burnsideB49x_offender_card hB)
  have hfix := burnsideB49x_card_fixV_le_dual hV hK hreal hdual B
  have hcardV := burnsideB49x_card_V_W hV hK hreal hquot
  set c := finrank (ZMod 2) (burnsideB49x_wfix (burnsideB49x_hatW hV U G hG B)) with hcdef
  set b := finrank (ZMod 2) (burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG B)) with hbdef
  have hBr : Nat.card B = 2 ^ rk B := B1.card_elemAbelian hB.2.2.1
  have hidx : (fixV B).index = 2 ^ rkIdx (fixV B) := B1.index_eq_two_pow hV _
  have hVi : Nat.card V = (fixV B).index * Nat.card (fixV B) := B1.card_eq_index_mul B
  have hrk : rk B ≤ (5 - c) * b := by
    rw [hBr] at hup
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hup
  have hidx' : (5 - c) + b ≤ rkIdx (fixV B) := by
    have hb5 : b ≤ 5 ∧ c ≤ 5 := by
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have h1 : 2 ^ (2 * 5) ≤ 2 ^ rkIdx (fixV B) * (2 ^ (5 - b) * 2 ^ c) := by
      rw [← hcardV, hVi, hidx]
      exact Nat.mul_le_mul_left _ hfix
    have e : 2 * 5 = ((5 - c) + b) + ((5 - b) + c) := by omega
    rw [e, pow_add, ← pow_add (2 : ℕ) (5 - b) c] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1
      (Nat.le_of_mul_le_mul_right h1 (by positivity))
  have hpos : 0 < rk B := hB.isA2.rk_pos
  unfold rAV
  rw [le_div_iff₀ (by exact_mod_cast hpos)]
  have key : 5 * rk B ≤ 6 * rkIdx (fixV B) := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hrk hidx'
      omega
    · rw [h1, h2] at hrk hidx'
      omega
    · rw [h1, h2] at hrk hidx'
      omega
  have key' : (5 : ℚ) * rk B ≤ 6 * rkIdx (fixV B) := by exact_mod_cast key
  linarith

end IVb

section PreW

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)

@[expose] noncomputable def burnsideB49x_preW
    (Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) : Subgroup (MulAut V) :=
  (Q.comap (burnsideB49_iota hV U G hG)).map G.subtype

theorem burnsideB49x_hatW_preW (hsurj : Function.Surjective (burnsideB49_iota hV U G hG))
    (Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) :
    burnsideB49x_hatW hV U G hG (burnsideB49x_preW hV U G hG Q) = Q := by
  unfold burnsideB49x_hatW burnsideB49x_preW
  rw [show ((Q.comap (burnsideB49_iota hV U G hG)).map G.subtype).subgroupOf G =
      Q.comap (burnsideB49_iota hV U G hG) from
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) _]
  exact Subgroup.map_comap_eq_self_of_surjective hsurj Q

theorem burnsideB49x_preW_le (Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) :
    burnsideB49x_preW hV U G hG Q ≤ G :=
  Subgroup.map_subtype_le _

theorem burnsideB49x_preW_elem (hinj : Function.Injective (burnsideB49_iota hV U G hG))
    {Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)}
    (hc : ∀ e ∈ Q, ∀ e' ∈ Q, e * e' = e' * e) (h2 : ∀ e ∈ Q, e * e = 1) :
    IsElemAbelian2 (burnsideB49x_preW hV U G hG Q) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    have h := hc _ hg _ hg'
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hinj h)
  · rintro _ ⟨g, hg, rfl⟩
    have h := h2 _ hg
    rw [← map_mul, ← map_one (burnsideB49_iota hV U G hG)] at h
    have h' := hinj h
    rw [pow_two]
    exact congrArg Subtype.val h'

end PreW

section IVc

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Type} [Field K]
  [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL 5 K) →* ↥G}

include hV in
theorem burnsideB49x_five_hex (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 5 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) :
    ∃ A, IsFFStarOffender G A ∧ rAV A ≤ ((5 / 6 : ℚ)) := by
  set hG := burnsideB49_hG hreal with hGdef
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  have hbij := burnsideB49_iota_bijective hV hK hreal hquot
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = 5 := burnsideB49_finrank_W hV hK hreal hquot
  obtain ⟨s, hs3, hsind⟩ := exists_finset_linearIndependent_of_le_finrank (R := ZMod 2)
    (M := burnsideB49_W hV U) (n := 3) (by rw [hn]; norm_num)
  set X : Submodule (ZMod 2) (burnsideB49_W hV U) := Submodule.span (ZMod 2) (s : Set _) with hXdef
  have hX : finrank (ZMod 2) X = 3 := by
    rw [hXdef, finrank_span_finset_eq_card hsind, hs3]
  have hX0 : X ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hX
    omega
  have hXT : X ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hn] at hX
    omega
  set Q := burnsideB49x_gl_Q X with hQdef
  have hQc : Nat.card Q = 64 := by
    rw [hQdef, burnsideB49x_gl_card_Q hX hn]
    norm_num
  set B₀ := burnsideB49x_preW hV U G hG Q with hB₀def
  have hhat : burnsideB49x_hatW hV U G hG B₀ = Q := burnsideB49x_hatW_preW hV U G hG hbij.2 Q
  have hB₀G : B₀ ≤ G := burnsideB49x_preW_le hV U G hG Q
  have hB₀card : Nat.card B₀ = 64 := by
    rw [← burnsideB49x_card_hatW hV U G hG hbij.1 hB₀G, hhat, hQc]
  have hB₀el : IsElemAbelian2 B₀ := burnsideB49x_preW_elem hV U G hG hbij.1
    (fun e he e' he' => burnsideB49x_gl_Q_mul_comm he he') (fun e he => burnsideB49x_gl_Q_mul_self he)
  have hB₀ne : B₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB₀card
    omega
  have hA2 : IsA2 G B₀ := ⟨hB₀G, hB₀ne, hB₀el⟩
  have hfixU : Nat.card ↥(fixV B₀ ⊓ U) = 4 := by
    rw [burnsideB49x_card_fixU_dual hV hK hreal hdual hB₀G, hhat, burnsideB49x_wcomm_eq,
      burnsideB49x_gl_comm_Q hXT, hX]
    norm_num
  obtain ⟨U', hU'inv, hUU', hUU'top⟩ := burnsideB49x_split_dual hV le_rfl hK hreal hdual
  have hfixU' : 8 ≤ Nat.card ↥(fixV B₀ ⊓ U') := by
    have hlift : ∀ x : burnsideB49_W hV U, ∃ u' : V, u' ∈ U' ∧
        F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk u') = x := by
      intro x
      obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) x)
      have hvt : v ∈ U ⊔ U' := by rw [hUU'top]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hvt
      refine ⟨b, hb, ?_⟩
      have : (QuotientGroup.mk (a * b) : V ⧸ U) = QuotientGroup.mk b := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).2 ha, one_mul]
      rw [← this, hv, F2Vec.ofV_toV]
    choose lift hliftU' hliftx using hlift
    have hfixX : ∀ x ∈ X, lift x ∈ fixV B₀ := by
      intro x hx b hb
      obtain ⟨g, hg, rfl⟩ := hb
      have hgQ : burnsideB49_iota hV U G hG g ∈ Q := hg
      have h1 : burnsideB49_iota hV U G hG g x = x := by
        have := burnsideB49x_gl_fix_Q hX0 ▸ (show x ∈ X from hx)
        exact this _ hgQ
      have h2 : F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk ((g : MulAut V) (lift x))) =
          F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk (lift x)) := by
        rw [← burnsideB49x_iota_mk hV U G hG, hliftx, h1]
      have h3 : (g : MulAut V) (lift x) * (lift x)⁻¹ ∈ U := by
        have h4 : (QuotientGroup.mk ((g : MulAut V) (lift x)) : V ⧸ U) = QuotientGroup.mk (lift x) :=
          congrArg (F2Vec.toV (burnsideB49_hW hV U)) h2
        rw [QuotientGroup.eq] at h4
        have := U.inv_mem h4
        simpa [mul_comm] using this
      have h5 : (g : MulAut V) (lift x) * (lift x)⁻¹ ∈ U' :=
        U'.mul_mem (hU'inv _ g.2 _ (hliftU' x)) (U'.inv_mem (hliftU' x))
      have h6 : (g : MulAut V) (lift x) * (lift x)⁻¹ ∈ U ⊓ U' := ⟨h3, h5⟩
      rw [hUU', Subgroup.mem_bot, mul_inv_eq_one] at h6
      exact h6
    have hXcard : Nat.card ↥X = 8 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hX]
      norm_num
    rw [← hXcard]
    refine Nat.card_le_card_of_injective (fun x : ↥X => (⟨lift x, hfixX x x.2, hliftU' x⟩ :
      ↥(fixV B₀ ⊓ U'))) ?_
    intro x y h
    have h' : lift x = lift y := congrArg (fun z : ↥(fixV B₀ ⊓ U') => (z : V)) h
    have := congrArg (fun v => F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v : V ⧸ U)) h'
    simp only [hliftx] at this
    exact Subtype.ext this
  have hfix32 : 32 ≤ Nat.card ↥(fixV B₀) := by
    have hinj : Function.Injective (fun p : ↥(fixV B₀ ⊓ U) × ↥(fixV B₀ ⊓ U') =>
        (⟨(p.1 : V) * p.2, (fixV B₀).mul_mem (Subgroup.mem_inf.1 p.1.2).1
          (Subgroup.mem_inf.1 p.2.2).1⟩ : ↥(fixV B₀))) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' : (a : V) * b = a' * b' := congrArg Subtype.val h
      have h1 : (a' : V)⁻¹ * a = b' * (b : V)⁻¹ := by
        calc (a' : V)⁻¹ * a = (a' : V)⁻¹ * (a * b) * (b : V)⁻¹ := by group
          _ = (a' : V)⁻¹ * (a' * b') * (b : V)⁻¹ := by rw [h']
          _ = b' * (b : V)⁻¹ := by group
      have hmem : (a' : V)⁻¹ * a ∈ U ⊓ U' := by
        refine ⟨U.mul_mem (U.inv_mem (Subgroup.mem_inf.1 a'.2).2) (Subgroup.mem_inf.1 a.2).2, ?_⟩
        rw [h1]
        exact U'.mul_mem (Subgroup.mem_inf.1 b'.2).2 (U'.inv_mem (Subgroup.mem_inf.1 b.2).2)
      rw [hUU', Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hb : (b : V) = b' := by
        rw [← hmem] at h'
        exact mul_left_cancel h'
      exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hfixU] at this
    omega
  have hr : rAV B₀ ≤ ((5 / 6 : ℚ)) := by
    have hBr : Nat.card B₀ = 2 ^ rk B₀ := B1.card_elemAbelian hB₀el
    have hrk : rk B₀ = 6 := by
      rw [hB₀card] at hBr
      have : (2 : ℕ) ^ 6 = 2 ^ rk B₀ := by
        rw [← hBr]
        norm_num
      exact (Nat.pow_right_injective le_rfl this).symm
    have hidx : (fixV B₀).index = 2 ^ rkIdx (fixV B₀) := B1.index_eq_two_pow hV _
    have hVi : Nat.card V = (fixV B₀).index * Nat.card (fixV B₀) := B1.card_eq_index_mul B₀
    have hcardV := burnsideB49x_card_V_W hV hK hreal hquot
    have hidx5 : rkIdx (fixV B₀) ≤ 5 := by
      have h1 : 2 ^ rkIdx (fixV B₀) * 32 ≤ 2 ^ (2 * 5) := by
        rw [← hcardV, hVi, hidx]
        exact Nat.mul_le_mul_left _ hfix32
      have h2 : 2 ^ rkIdx (fixV B₀) ≤ 2 ^ 5 := by
        have : (2 : ℕ) ^ (2 * 5) = 2 ^ 5 * 32 := by norm_num
        rw [this] at h1
        exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    unfold rAV
    rw [hrk, div_le_iff₀ (by norm_num)]
    have : (rkIdx (fixV B₀) : ℚ) ≤ 5 := by exact_mod_cast hidx5
    linarith
  obtain ⟨B, -, hB, hrB⟩ := exists_offender_rAV_le hV hA2 (hr.trans (by norm_num))
  exact ⟨B, hB, hrB.trans hr⟩

include hV in
theorem burnsideB49x_five_q (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 5 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) :
    qOf G = (((5 / 6 : ℚ)) : WithTop ℚ) :=
  qOf_eq_of_offenders hV (by norm_num) (fun B hB => burnsideB49x_five_rAV_ge hV hK hreal hdual hB)
    (burnsideB49x_five_hex hV hK hreal hdual)

end IVc

end CFSG.ASVolI
