module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E7
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem sup_zpowers_inf_E_ne_bot {t : G} (htA : t ∈ m.A) (htZ : t ∉ m.Z) :
    (m.Z ⊔ zpowers t) ⊓ m.E ≠ ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hel := m.isElemAbelian_A
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ m.Z.one_mem)
  have htcard : Nat.card (zpowers t) = m.r := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hel.2 t htA) ht1
  have hZt : m.Z ⊓ zpowers t = ⊥ := by
    have h := inf_eq_bot_of_not_le_of_card_prime m.hr htcard
      (fun h => htZ (h (mem_zpowers t)))
    rw [inf_comm] at h
    exact h
  have hXA : m.Z ⊔ zpowers t ≤ m.A := sup_le m.Z_le_A (zpowers_le.2 htA)
  have hcommZt : ∀ z ∈ m.Z, ∀ s ∈ zpowers t, z * s = s * z := fun z hz s hs =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨z, m.Z_le_A hz⟩ ⟨s, zpowers_le.2 htA hs⟩)
  have hX : Nat.card ↥(m.Z ⊔ zpowers t) = m.r ^ 2 := by
    rw [card_sup_of_commute_of_disjoint hcommZt hZt, m.card_Z, htcard, pow_two]
  intro hbot
  have hcomm : ∀ a ∈ m.Z ⊔ zpowers t, ∀ e ∈ m.E, a * e = e * a := fun a ha e he =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, hXA ha⟩ ⟨e, m.E_le_A he⟩)
  have hcard := card_sup_of_commute_of_disjoint hcomm hbot
  rw [hX, m.d.E_card] at hcard
  have hle : Nat.card ↥(m.Z ⊔ zpowers t ⊔ m.E) ≤ Nat.card ↥m.A :=
    Subgroup.card_le_of_le (sup_le hXA m.E_le_A)
  rw [hcard, m.card_A] at hle
  have : m.r ^ 3 < m.r ^ 2 * m.r ^ 2 := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right m.hr.one_lt (by norm_num)
  omega

theorem mem_M_of_conj_le {W : Subgroup G} (hWA : W ≤ m.A) (hZW : m.Z ≤ W) (hWZ : ¬ W ≤ m.Z)
    {y : G} (hy : ∀ w ∈ W, y * w * y⁻¹ ∈ N588.rCore m.r m.L ⊔ W) : y ∈ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set O := N588.rCore m.r m.L with hO
  set P := O ⊔ W with hP
  have hWp : IsPGroup m.r W := m.isPGroup_A.to_le hWA
  have hWn : W ≤ normalizer ((O : Subgroup G) : Set G) :=
    (hWA.trans m.A_le_H).trans m.H_le_normalizer_rCoreL
  have hOc : Nat.Coprime m.r (Nat.card O) := N588.coprime_card_rCore m.r m.L
  have hOW : O ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hx.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hWp ⟨x, hx.2⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at h1
    have h2 : m.r ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hOc) h1
    rw [h2] at hk
    exact (mem_bot).2 (orderOf_eq_one_iff.1 hk)
  have hWsyl : IsSylowOf m.r W P := by
    apply isSylowOf_of_card le_sup_right
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.Mz614.N588.card_sup_of_le_normalizer hWn hOW]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWp
    rw [hk, Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero k m.hr.ne_zero),
      Finsupp.add_apply, Nat.Prime.factorization_pow m.hr, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd m.hr).1 hOc),
      zero_add]
  set W' : Subgroup G := W.map (MulAut.conj y).toMonoidHom with hW'
  have hW'P : W' ≤ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact hy w hw
  have hW'syl : IsSylowOf m.r W' P := by
    apply isSylowOf_of_card hW'P
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hWsyl.card_eq]
  obtain ⟨k, hkP, hk⟩ := hWsyl.exists_mem_conj hW'syl
  have hkP' : k ∈ ((O ⊔ W : Subgroup G) : Set G) := hkP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O W hWn] at hkP'
  obtain ⟨o, ho, w, hw, rfl⟩ := hkP'
  have hN : o⁻¹ * y ∈ normalizer (W : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 : y * x * y⁻¹ ∈ W' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have h2 := (hk _).1 h1
    have h3 : w * ((o * w)⁻¹ * (y * x * y⁻¹) * (o * w)) * w⁻¹ ∈ W :=
      W.mul_mem (W.mul_mem hw h2) (W.inv_mem hw)
    have : o⁻¹ * y * x * (o⁻¹ * y)⁻¹ = w * ((o * w)⁻¹ * (y * x * y⁻¹) * (o * w)) * w⁻¹ := by
      group
    rw [this]
    exact h3
  obtain ⟨t, htW, htZ⟩ := Set.not_subset.1 hWZ
  have hWE : W ⊓ m.E ≠ ⊥ := fun h => m.sup_zpowers_inf_E_ne_bot (hWA htW) htZ
    (le_bot_iff.1 (h ▸ inf_le_inf_right _ (sup_le hZW (zpowers_le.2 htW))))
  have hNM := m.d.normalizer_le_of_le_pGroup m.hC (X := W ⊓ m.E) (S := W) inf_le_right hWE
    inf_le_left hWp
  have : y = o * (o⁻¹ * y) := by group
  rw [this]
  exact m.M.mul_mem (m.rCoreL_le_M ho) (hNM hN)

variable (hKM : UCK.KMult) (hK3 : UCK.KMult3) (h69 : R6_9 Dat)
include hKM hK3 h69

theorem conj_mem_of_sig_eq (hSch : UCK.KSch) {y w w' : ↥m.LA}
    (h : m.sig y * m.sig w * (m.sig y)⁻¹ = m.sig w') :
    ∃ u ∈ N588.rCore m.r m.L ⊔ m.Z, (y : G) * w * (y : G)⁻¹ = w' * u := by
  have h1 : m.sig (w'⁻¹ * (y * w * y⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, h, inv_mul_cancel]
  refine ⟨_, m.mem_rCore_sup_Z_of_sig_eq_one hKM hK3 h69 hSch h1, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem isStronglyPEmbedded_star_M (hSch : UCK.KSch) :
    IsStronglyPEmbedded m.r (m.star m.M) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI : Finite (MulAut m.Lbar) := MulEquiv.finite_left
  have hel := m.isElemAbelian_star_A
  have hcardA := m.card_star_A hKM hK3 h69 hSch
  have hSyl : IsSylowOf m.r (m.star m.R) (m.star m.M) :=
    (m.star_R_sylow h69).of_le m.star_R_le_star_M le_top
  have hAZ : ¬ m.A ≤ m.Z := by
    intro h
    have h1 := Subgroup.card_le_of_le h
    rw [m.card_A, m.card_Z] at h1
    have : m.r < m.r ^ 3 := by
      calc m.r = m.r ^ 1 := (pow_one _).symm
        _ < m.r ^ 3 := Nat.pow_lt_pow_right m.hr.one_lt (by norm_num)
    omega
  refine CFSG.LocalAnalysis.StronglyEmbedded.isStronglyPEmbedded_of_weaklyClosed
    (m.star_M_ne_top hKM hK3 h69 hSch) hSyl m.star_A_le_star_R ?_
    (fun a ha b hb => hel.comm ha hb) ?_ ?_ ?_ ?_
  ·
    intro h
    rw [h, Subgroup.card_bot] at hcardA
    exact (Nat.one_lt_pow two_ne_zero m.hr.one_lt).ne hcardA
  ·
    intro g hg
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨b, hb, rfl⟩
      exact m.mem_star_A_of_pow hKM hK3 h69 hSch (hg ⟨b, hb, rfl⟩)
        (by rw [← map_pow, hel.2 b hb, map_one])
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  ·
    intro x hx hxo
    have hxp : IsPGroup m.r (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
    obtain ⟨T, hT, hxT⟩ := exists_isSylowOf_ge (zpowers_le.2 hx) hxp
    obtain ⟨k, hkM, hk⟩ := hSyl.exists_mem_conj hT
    refine ⟨k⁻¹, (m.star m.M).inv_mem hkM, ?_⟩
    rw [inv_inv]
    have hx1 : x ^ m.r = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hxo] at h
    have hpow : (k⁻¹ * x * k) ^ m.r = 1 := by
      have h := map_pow (MulAut.conj k⁻¹) x m.r
      rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv] at h
      rw [← h, hx1, mul_one, inv_mul_cancel]
    exact m.mem_star_A_of_pow hKM hK3 h69 hSch ((hk x).1 (hxT (mem_zpowers x))) hpow
  ·
    rintro _ ⟨a, ha, rfl⟩ hbo c hc
    have ha' : (a : G) ∈ m.A := ha
    obtain ⟨y, rfl⟩ := m.sigX_surjective c
    have hcomm : m.sigX a * m.sigX y = m.sigX y * m.sigX a :=
      mem_centralizer_iff.1 hc (m.sigX a) rfl
    have haZ : (a : G) ∉ m.Z := by
      intro h
      have h1 : m.sigX a = 1 := m.sigX_eq_one_iff.2 (m.sig_Z h)
      rw [h1, orderOf_one] at hbo
      exact m.hr.one_lt.ne hbo
    set W := m.Z ⊔ zpowers (a : G) with hW
    have hya : (y : G) * a * (y : G)⁻¹ ∈ N588.rCore m.r m.L ⊔ W := by
      have h1 : m.sig y * m.sig a * (m.sig y)⁻¹ = m.sig a := by
        have h2 : m.sig a * m.sig y = m.sig y * m.sig a := congrArg Subtype.val hcomm
        rw [← h2, mul_inv_cancel_right]
      obtain ⟨u, hu, hue⟩ := m.conj_mem_of_sig_eq hKM hK3 h69 hSch h1
      rw [hue]
      exact mul_mem (mem_sup_right (mem_sup_right (mem_zpowers _)))
        ((sup_le_sup_left (le_sup_left : m.Z ≤ W) (N588.rCore m.r m.L)) hu)
    have hWle : W ≤ (N588.rCore m.r m.L ⊔ W).comap (MulAut.conj (y : G)).toMonoidHom := by
      refine sup_le (fun z hz => ?_) (zpowers_le.2 ?_)
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have : (y : G) * z * (y : G)⁻¹ = z := by
          rw [← mem_centralizer_iff.1 (m.LA_le_H y.2) z hz, mul_inv_cancel_right]
        rw [this]
        exact mem_sup_right (mem_sup_left hz)
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hya
    refine m.sigX_mem_star (m.mem_M_of_conj_le (W := W) (sup_le m.Z_le_A (zpowers_le.2 ha'))
      le_sup_left (fun h => haZ (h (mem_sup_right (mem_zpowers _)))) fun w hw => ?_)
    have h1 := hWle hw
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    exact h1
  ·
    intro c hc
    obtain ⟨y, rfl⟩ := m.sigX_surjective c
    refine m.sigX_mem_star (m.mem_M_of_conj_le (W := m.A) le_rfl m.Z_le_A hAZ fun w hw => ?_)
    have h1 : m.sigX y * m.sigX ⟨w, m.A_le_LA hw⟩ * (m.sigX y)⁻¹ ∈ m.star m.A :=
      (mem_normalizer_iff.1 hc _).1 (m.sigX_mem_star hw)
    obtain ⟨a', ha', hae⟩ := h1
    have h2 : m.sig y * m.sig ⟨w, m.A_le_LA hw⟩ * (m.sig y)⁻¹ = m.sig a' :=
      (congrArg Subtype.val hae).symm
    obtain ⟨u, hu, hue⟩ := m.conj_mem_of_sig_eq hKM hK3 h69 hSch h2
    show (y : G) * w * (y : G)⁻¹ ∈ _
    rw [hue]
    exact mul_mem (mem_sup_right ha') ((sup_le_sup_left m.Z_le_A (N588.rCore m.r m.L)) hu)

theorem k35_Xs (hSch : UCK.KSch) (hK35 : UCK.K35Ω) :
    IsSimpleGroup ↥m.Xs ∧ (LieModel ↥m.Xs .PSL 2 m.r 2 ∨ IsAlt ↥m.Xs (2 * m.r) ∨
      (m.r = 3 ∧ (IsSpor ↥m.Xs .M11 ∨ LieModel ↥m.Xs .PSL 3 2 2)) ∨
      (m.r = 5 ∧ (LieModel ↥m.Xs .Tits 0 2 1 ∨ IsSpor ↥m.Xs .Fi22))) := by
  haveI : Finite (MulAut m.Lbar) := MulEquiv.finite_left
  exact hK35 ↥m.Xs m.isKGroup_Xs m.r m.hr m.d.odd m.Opp_Xs (m.pPrimeCore_Xs hKM hK3 h69 hSch)
    (m.star m.M) (m.isStronglyPEmbedded_star_M hKM hK3 h69 hSch) (m.star m.R) (m.star m.A)
    (m.star_R_sylow h69) m.star_A_le_star_R m.isElemAbelian_star_A
    (m.card_star_A hKM hK3 h69 hSch) (fun _ hx hxr => m.mem_star_A_of_pow hKM hK3 h69 hSch hx hxr)
    (fun _ hb _ hy => m.star_A_comm h69 hb hy)

theorem innX_range_eq_top (hSch : UCK.KSch) (hK35 : UCK.K35Ω) : m.innX.range = ⊤ := by
  haveI := (m.k35_Xs hKM hK3 h69 hSch hK35).1
  haveI := m.innX_range_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal m.innX.range with h | h
  · exfalso
    haveI := m.isSimpleGroup_Lbar_of_inputs hKM hK3 h69 hSch
    obtain ⟨u, hu⟩ := exists_ne (1 : m.Lbar)
    apply hu
    apply m.innX_injective hKM hK3 h69 hSch
    have h1 : m.innX u ∈ m.innX.range := ⟨u, rfl⟩
    rw [h, mem_bot] at h1
    rw [h1, map_one]
  · exact h

theorem A_le_Z_sup_L (hSch : UCK.KSch) (hK35 : UCK.K35Ω) : m.A ≤ m.Z ⊔ m.L := by
  intro a ha
  have h1 : m.sigX ⟨a, m.A_le_LA ha⟩ ∈ m.innX.range := by
    rw [m.innX_range_eq_top hKM hK3 h69 hSch hK35]
    exact mem_top _
  obtain ⟨u, hu⟩ := h1
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective u
  rw [← m.sigX_L] at hu
  have h2 : m.sig ((Subgroup.inclusion m.L_le_LA ℓ)⁻¹ * ⟨a, m.A_le_LA ha⟩) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact congrArg Subtype.val hu
  have h3 := m.mem_rCore_sup_Z_of_sig_eq_one hKM hK3 h69 hSch h2
  have hle : N588.rCore m.r m.L ⊔ m.Z ≤ m.Z ⊔ m.L :=
    sup_le ((N588.rCore_le _ _).trans le_sup_right) le_sup_left
  have h4 : (ℓ : G)⁻¹ * a ∈ m.Z ⊔ m.L := hle h3
  have : a = (ℓ : G) * ((ℓ : G)⁻¹ * a) := by group
  rw [this]
  exact mul_mem (mem_sup_right ℓ.2) h4

theorem nonempty_mulEquiv_Xs (hSch : UCK.KSch) (hK35 : UCK.K35Ω) :
    Nonempty (m.Lbar ≃* ↥m.Xs) :=
  ⟨MulEquiv.ofBijective m.innX ⟨m.innX_injective hKM hK3 h69 hSch,
    MonoidHom.range_eq_top.1 (m.innX_range_eq_top hKM hK3 h69 hSch hK35)⟩⟩

theorem c620_list_of_inputs (hSch : UCK.KSch) (hK35 : UCK.K35Ω) :
    m.C620 ∧ (LieModel m.Lbar .PSL 2 m.r 2 ∨ IsAlt m.Lbar (2 * m.r) ∨
      (m.r = 3 ∧ (IsSpor m.Lbar .M11 ∨ LieModel m.Lbar .PSL 3 2 2)) ∨
      (m.r = 5 ∧ (LieModel m.Lbar .Tits 0 2 1 ∨ IsSpor m.Lbar .Fi22))) := by
  refine ⟨⟨m.A_le_Z_sup_L hKM hK3 h69 hSch hK35, m.not_Z_le_L_of_inputs hKM hK3 h69 hSch⟩, ?_⟩
  obtain ⟨e⟩ := m.nonempty_mulEquiv_Xs hKM hK3 h69 hSch hK35
  have hL : ∀ {t n p f}, LieModel ↥m.Xs t n p f → LieModel m.Lbar t n p f := fun h =>
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm h
  have hS : ∀ {s}, IsSpor ↥m.Xs s → IsSpor m.Lbar s := fun h => by
    obtain ⟨e'⟩ := h
    exact ⟨e.trans e'⟩
  rcases (m.k35_Xs hKM hK3 h69 hSch hK35).2 with h | h | ⟨hr, h | h⟩ | ⟨hr, h | h⟩
  · exact Or.inl (hL h)
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, Or.inl (hS h)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hr, Or.inr (hL h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hr, Or.inl (hL h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hr, Or.inr (hS h)⟩))

theorem l620_of_exc (hSch : UCK.KSch) (hK35 : UCK.K35Ω)
    (hexc : ¬ ((∃ n : ℕ, 13 ≤ n ∧ IsAlt m.Lbar n) ∨ IsSpor m.Lbar .Fi22)) : m.L620 := by
  obtain ⟨h620, hlist⟩ := m.c620_list_of_inputs hKM hK3 h69 hSch hK35
  refine ⟨h620, ?_⟩
  rcases hlist with h | h | h | ⟨hr5, h | h⟩
  · exact Or.inl h
  · by_cases hr3 : m.r = 3
    ·
      have h6 : IsAlt m.Lbar 6 := by
        have e : 2 * m.r = 6 := by omega
        rw [e] at h
        exact h
      have h9 : LieModel m.Lbar .PSL 2 3 2 := Or.inl ⟨by decide,
        CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six
          m.Lbar h6⟩
      exact Or.inl (cast (congrArg (fun p => LieModel m.Lbar .PSL 2 p 2) hr3).symm h9)
    · by_cases hr5 : m.r = 5
      · have h10 : IsAlt m.Lbar 10 := by
          have e : 2 * m.r = 10 := by omega
          rw [e] at h
          exact h
        exact Or.inr (Or.inr ⟨hr5, Or.inr h10⟩)
      · exfalso
        have h5 := m.five_le_r hr3
        have h7 : 7 ≤ m.r := by
          rcases (show m.r = 6 ∨ 7 ≤ m.r by omega) with h6 | h6
          · exact absurd (h6 ▸ m.hr) (by decide)
          · exact h6
        exact hexc (Or.inl ⟨2 * m.r, by omega, h⟩)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hr5, Or.inl h⟩)
  · exact absurd (Or.inr h) hexc

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
