module

public import CFSG.Quasithin.EmptyFaithful.S151TBNorm
public import CFSG.Quasithin.EmptyFaithful.S151TBExc
public import CFSG.Quasithin.EmptyFaithful.S151TBTyp
public import CFSG.Quasithin.EmptyFaithful.S151TBA7Glue

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem pCore_le_mZ (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (hN : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 L ≤ mZ1516 Mc Z₁ := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have h1 : pCoreOf 2 L ≤ pCoreOf 2 (g1_1516 Z₁) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLG)
      (hN.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have h2 : pCoreOf 2 (g1_1516 Z₁) ≤ s1516 T Z₁ :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hc.h18.four
  exact (h1.trans h2).trans (s_le_mZ hc)

theorem stab_le_mZ (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (hsh : IsShort2 L) (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G))
    {α : ↥L →* alternatingGroup (Fin 7)} (hα : IsAltBlockTypeWith L 7 α) :
    ∃ v : ↥(evenWeight 7), ∀ x : ↥L, permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v →
      (x : G) ∈ mZ1516 Mc Z₁ := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hB : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := sylow_inf hc
  have hS2 : IsPGroup 2 ↥(s1516 T Z₁) := hc.h18.four.2.1
  obtain ⟨W, hWb, hWfix, -, hWz⟩ :=
    exists_zU hsh.2.1 hperf hS2 hSN hB (omegaOneCenter_le hc)
  have hnot := not_le_centralizer hc hLG
  obtain ⟨l₀, hl₀L, hl₀⟩ : ∃ l ∈ L, l ∉ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G) := by
    by_contra h
    push Not at h
    exact hnot h
  rw [Subgroup.mem_centralizer_iff] at hl₀
  push Not at hl₀
  obtain ⟨z, hz, hl₀z⟩ := hl₀
  obtain ⟨w, hw, hwiff⟩ := hWz z hz
  have hwU : w ∈ blockU L := hWb hw
  have hz1 : z ≠ 1 := by
    intro h
    apply hl₀z
    rw [h]
    simp
  have hwB : ∀ s ∈ s1516 T Z₁ ⊓ L, s * w * s⁻¹ = w := hWfix w hw
  obtain ⟨-, -, β, -, hβk, hβeq⟩ := hα
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨w, hwU⟩))
  refine ⟨v, fun x hx => ?_⟩
  have hβ1 : β ⟨w, hwU⟩ =
      β ⟨(x : G) * w * (x : G)⁻¹, s151u_conj_mem_U x ⟨w, hwU⟩⟩ := by
    have h := hβeq x ⟨w, hwU⟩ ⟨(x : G) * w * (x : G)⁻¹, s151u_conj_mem_U x ⟨w, hwU⟩⟩ rfl v hv
    rw [hx, hv] at h
    exact Multiplicative.toAdd.injective h
  have hker1 : (⟨w, hwU⟩ : ↥(blockU L))⁻¹ *
      ⟨(x : G) * w * (x : G)⁻¹, s151u_conj_mem_U x ⟨w, hwU⟩⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hβ1]
    simp
  rw [hβk, Subgroup.mem_subgroupOf] at hker1
  have hmk : ((⟨w, hwU⟩ : ↥(blockU L)) : BlockN L) =
      ((⟨(x : G) * w * (x : G)⁻¹, s151u_conj_mem_U x ⟨w, hwU⟩⟩ : ↥(blockU L)) : BlockN L) :=
    (s151u_mk_eq_iff _ _).2 hker1
  have hfix : x • ((⟨w, hwU⟩ : ↥(blockU L)) : BlockN L) =
      ((⟨w, hwU⟩ : ↥(blockU L)) : BlockN L) :=
    (s151u_smul_mk L x ⟨w, hwU⟩).trans hmk.symm
  have hcomm := commute_of_smul_fixed hsh hB hwU hwB x hfix
  have hxw : (x : G) * w = w * (x : G) := by
    calc (x : G) * w = ((x : G) * w * (x : G)⁻¹) * (x : G) := by group
      _ = w * (x : G) := by rw [hcomm]
  exact centralizer_le_mZ hc hz hz1 (hLG x.2) ((hwiff x x.2).2 hxw)

omit [Finite G] in
theorem card_lstar_of_altBlock {n : ℕ} {α : ↥L →* alternatingGroup (Fin n)}
    (h : IsAltBlockTypeWith L n α) :
    Nat.card (LStar L) = Nat.card (alternatingGroup (Fin n)) :=
  Nat.card_congr (((QuotientGroup.quotientMulEquivOfEq h.2.1.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α h.1)).toEquiv)

omit [Finite G] in
theorem false_of_alt_six_seven {α₆ : ↥L →* alternatingGroup (Fin 6)}
    (h6 : IsAltBlockTypeWith L 6 α₆) {α₇ : ↥L →* alternatingGroup (Fin 7)}
    (h7 : IsAltBlockTypeWith L 7 α₇) : False := by
  have e6 := card_lstar_of_altBlock h6
  have e7 := card_lstar_of_altBlock h7
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 6 (by norm_num)] at e6
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 7 (by norm_num)] at e7
  have : (6 : ℕ).factorial / 2 = (7 : ℕ).factorial / 2 := e6.symm.trans e7
  revert this
  decide

@[expose] def Input15120A7Weight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    ∀ α : ↥L →* alternatingGroup (Fin 7), IsAltBlockTypeWith L 7 α →
      ∃ v : ↥(evenWeight 7), HasWeightTwo (v : Fin 7 → ZMod 2) ∧
        (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ → permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v) ∧
        ∀ x : ↥L, (x : G) ∈ mZ1516 Mc Z₁ ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v

theorem input15120A7Weight_of_c27
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) : Input15120A7Weight := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp α hα
  have hq := hc.hL.quasi
  have hQ : LStar L ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hα.2.1.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (LStar L) := hQ.isSimpleGroup
  have hcen : Subgroup.center (LStar L) = ⊥ := center_eq_bot_of_simple hs hq
  have hD : ListD' L := Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot).trans hQ⟩
  have hN := g1_le_normalizer h37 h38 hc hcomp hD
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans hN)
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := (s1516_le_g1 T Z₁).trans hN
  have hMR : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := fun x hx => by
    have : x ∈ g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := hc.h18.five.2.1 ▸ hx
    exact this.2
  have hO2M := pCore_le_mZ hc hcomp hN
  have hcard7 : Nat.card (LStar L) = 2520 := by
    rw [Nat.card_congr hQ.toEquiv, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 7 (by norm_num)]
    decide
  obtain ⟨h1, -, h3⟩ := hC27 G (g1_1516 Z₁) (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) L
    (omegaOneCenterOf (pCoreOf 2 (L ⊔ q1_1516 Mc Z₁))) hc.h18.five.2.2 hcomp hq hchar
    hc.hL.not_le hRN rfl
  suffices key : ∃ v : ↥(evenWeight 7), HasWeightTwo (v : Fin 7 → ZMod 2) ∧
      ∀ x : ↥L, (x : G) ∈ mZ1516 Mc Z₁ ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v by
    obtain ⟨v, hv2, hv⟩ := key
    exact ⟨v, hv2, fun x hx => (hv x).1 (s_le_mZ hc hx), hv⟩
  rcases h3 with ⟨hchi, hcases⟩ | ⟨⟨n, α', hn5, hn8, hsh, hα', t, htR, htV, hRact, -, σ, hσ, hconj⟩,
    hMK⟩ | ⟨hHat, -⟩ | ⟨hexc, hidx⟩ | ⟨hAS, -⟩ | ⟨hg, -, -⟩ |
    ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ | ⟨hh, -, -⟩
  · rcases hcases with ⟨⟨n, hn, hlin⟩, -⟩ | ⟨hA5, -⟩ | ⟨-, hD8, e, P, hP, hMap⟩ |
      ⟨-, hE8, e, P, hP, hMap⟩
    · exact (listD'_false_of_lin2 hq hn hlin hD).elim
    · obtain ⟨α5, hα5⟩ := (isAltType_iff_exists_isAltBlockTypeWith (by decide)).1 hA5
      exact (listD'_false_of_alt hq (Or.inl rfl) hα5 hD).elim
    · exact (false_of_case_iii hMR hD8 e hP hMap).elim
    · obtain ⟨v, hv⟩ := stab_le_mZ hc hcomp hchi.1.1 hSN hα
      exact (false_of_case_iv hRN h1 hcen hα e hP hMap v hv).elim
  · have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl
    · exact (listD'_false_of_alt hq (Or.inl rfl) hα' hD).elim
    · exact (false_of_alt_six_seven hα' hα).elim
    · obtain ⟨p, q, hpq, rfl⟩ := hσ
      exact weight_two_of_case_b hRN h1 hcen hO2M hα hα' htR htV hRact hpq hconj hMK
    · exact (listD'_false_of_alt hq (Or.inr rfl) hα' hD).elim
  · have h3 := hHat.2.1.2.1
    rw [hcen] at h3
    simp at h3
  · exact (not_excA7_index hc hcomp hSN hexc hidx).elim
  · rcases hAS with ⟨-, α6, hα6⟩ | hsp4
    · exact (false_of_alt_six_seven hα6 hα).elim
    · exact (listD'_false_of_sp4 hq hsp4 hD).elim
  · have h6048 := CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three hg.2.1
    rw [hcard7] at h6048
    exact absurd h6048 (by norm_num)
  · obtain ⟨ψ₀, hψ₀, hO2, hker⟩ := exists_epi_autOn hRN h1
    exact (listD'_false_of_sl3 hq hn1 hF (e.toMonoidHom.comp ψ₀)
      (e.surjective.comp hψ₀) (fun x hx => by
        have := hO2 hx
        simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
        simpa using hx)) hD).elim
  · obtain ⟨ψ₀, hψ₀, hO2, hker⟩ := exists_epi_autOn hRN h1
    rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact (listD'_false_of_sl4 hq (e.toMonoidHom.comp ψ₀) (e.surjective.comp hψ₀)
        (fun x hx => by
          have := hO2 hx
          simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
          simpa using hx)) hD).elim
    · exact (listD'_false_of_sl5 hq (e.toMonoidHom.comp ψ₀) (e.surjective.comp hψ₀)
        (fun x hx => by
          have := hO2 hx
          simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
          simpa using hx)) hD).elim

end CFSG.Quasithin.S151TB
