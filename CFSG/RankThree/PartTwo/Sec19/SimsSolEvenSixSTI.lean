module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTI
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4b

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixS

theorem barLen_le_three (v : permBar 6) : barLen v ≤ 3 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barLen_mk]
  omega

theorem card_barLen_zero : Nat.card {v : permBar 6 // barLen v = 0} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨0, Comb.barLen_zero⟩, fun v => Subtype.ext (eq_zero_of_barLen_eq_zero v.2)⟩

theorem card_barLen_one : Nat.card {v : permBar 6 // barLen v = 1} = 6 := by
  rw [Comb.card_barLen (by norm_num)]
  decide

theorem card_barLen_two : Nat.card {v : permBar 6 // barLen v = 2} = 15 := by
  rw [Comb.card_barLen (by norm_num)]
  decide

theorem card_barLen_three : Nat.card {v : permBar 6 // barLen v = 3} = 10 := by
  classical
  haveI : Fintype (permBar 6) := Fintype.ofFinite _
  have htot : Fintype.card (permBar 6) = 32 := by
    rw [← Nat.card_eq_fintype_card, Comb.card_permBar (by norm_num)]
    norm_num
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (permBar 6)))
    (t := Finset.range 4) (f := barLen)
    (fun v _ => Finset.mem_range.2 (by have := barLen_le_three v; omega))
  have hc : ∀ l : ℕ, (Finset.univ.filter fun v : permBar 6 => barLen v = l).card =
      Nat.card {v : permBar 6 // barLen v = l} := by
    intro l
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_univ, htot] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc, card_barLen_zero, card_barLen_one,
    card_barLen_two] at hsum
  omega

theorem card_barLen_cases (v : permBar 6) :
    (barLen v = 0 ∧ Nat.card {u : permBar 6 // barLen u = barLen v} = 1) ∨
    (barLen v = 1 ∧ Nat.card {u : permBar 6 // barLen u = barLen v} = 6) ∨
    (barLen v = 2 ∧ Nat.card {u : permBar 6 // barLen u = barLen v} = 15) ∨
    (barLen v = 3 ∧ Nat.card {u : permBar 6 // barLen u = barLen v} = 10) := by
  have h3 := barLen_le_three v
  rcases (show barLen v = 0 ∨ barLen v = 1 ∨ barLen v = 2 ∨ barLen v = 3 by omega) with
    h | h | h | h <;> rw [h]
  · exact Or.inl ⟨rfl, card_barLen_zero⟩
  · exact Or.inr (Or.inl ⟨rfl, card_barLen_one⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, card_barLen_two⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, card_barLen_three⟩))

theorem exists_alt_barAct_eq {u v : permBar 6} (h : barLen u = barLen v) :
    ∃ σ ∈ alternatingGroup (Fin 6), barAct σ u = v := by
  obtain ⟨I, hI, rfl⟩ := exists_supp_of_len u
  obtain ⟨J, hJ, rfl⟩ := exists_supp_of_len v
  obtain ⟨σ, hσ, hσI⟩ := Comb.exists_alt_map_eq (by norm_num) (hI.trans (h.trans hJ.symm))
  refine ⟨σ, hσ, ?_⟩
  rw [barAct_barInd, ← hσI, Finset.map_eq_image]
  rfl

end SixS

section Orbit

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

namespace Cfg

theorem orbit_eq_barLen_six (C : Cfg G M X 6) (v : permBar 6) :
    {u : permBar 6 | ∃ m : ↥M, barAct (C.θ m) v = u} = {u : permBar 6 | barLen u = barLen v} := by
  ext u
  constructor
  · rintro ⟨m, rfl⟩
    exact barLen_barAct _ _
  · intro hu
    obtain ⟨σ, hσA, hσ⟩ := SixS.exists_alt_barAct_eq (u := v) (v := u) (Eq.symm hu)
    obtain ⟨c, hc⟩ := C.exists_lift hσA
    exact ⟨⟨(c : G), C.S.le c.2⟩, by rw [hc]; exact hσ⟩

theorem card_M_eq_six (C : Cfg G M X 6) (v : permBar 6) :
    Nat.card ↥M = Nat.card {u : permBar 6 // barLen u = barLen v} *
      Nat.card ↥(H4b.barStab C v) := by
  rw [H4b.card_M_eq_orbit_mul C v, orbit_eq_barLen_six C v, ← Nat.card_coe_set_eq]
  rfl

end Cfg

namespace Cfg.PiData

variable {C : Cfg G M X 6} (D : C.PiData)

theorem card_M_eq_CMOf_six (hR : Nat.card ↥(Rc X) ≤ 2) (y : ↥(CFSG.Open.pCoreOf 2 M)) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ Nat.card ↥M =
      Nat.card {u : permBar 6 // barLen u = barLen (Multiplicative.toAdd (D.piQ y))} * k *
        Nat.card ↥(CMOf M (y : G)) := by
  set v := Multiplicative.toAdd (D.piQ y) with hv
  have h2 := H4b.card_barStab_le D hR y
  have hdvd : Nat.card ↥(CMOf M (y : G)) ∣ Nat.card ↥(H4b.barStab C v) := by
    have hle : (CMOf M (y : G)).subgroupOf M ≤ H4b.barStab C v := by
      intro m hm
      have hc : (m : G) * (y : G) * (m : G)⁻¹ = y :=
        mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hm)).2
      exact (D.piQ_conj m y y hc.symm).symm
    have e : Nat.card ↥((CMOf M (y : G)).subgroupOf M) = Nat.card ↥(CMOf M (y : G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [← e]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card ↥(CMOf M (y : G)) := Nat.card_pos
  have hpos' : 0 < Nat.card ↥(H4b.barStab C v) := Nat.card_pos
  have hk2 : k ≤ 2 := by
    have : Nat.card ↥(CMOf M (y : G)) * k ≤ Nat.card ↥(CMOf M (y : G)) * 2 := by
      rw [← hk]
      linarith
    exact Nat.le_of_mul_le_mul_left this hpos
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  refine ⟨k, by omega, ?_⟩
  rw [C.card_M_eq_six v, hk]
  ring

end Cfg.PiData

end Orbit

section TIStep

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

namespace Cfg.PiData

variable {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem conj_eq_of_inf_ne_bot_sym (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) {g : G}
    (hne : CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ ⊥) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  refine TI.conj_eq_of_mem_M ?_
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haQ : a ∈ Q := (Subgroup.mem_inf.1 ha).1
  have hbQ : g⁻¹ * a * g ∈ Q := mem_conjSubgroup.1 (Subgroup.mem_inf.1 ha).2
  set b : G := g⁻¹ * a * g with hb
  have hab : a = g * b * g⁻¹ := by rw [hb]; group
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1'
    rw [hab, h]
    group
  have hQab := C.Q_comm hR
  have hCa : CGOf a ≤ M := by
    have := hH a haQ ha1'
    rwa [centralizer_singleton_eq_zpowers] at this
  have hCb : CGOf b ≤ M := by
    have := hH b hbQ hb1
    rwa [centralizer_singleton_eq_zpowers] at this
  have hcardC : Nat.card ↥(CGOf a) = Nat.card ↥(CGOf b) := by
    rw [hab, H4b.CGOf_conj]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hCMa : CMOf M a = CGOf a := inf_eq_right.2 hCa
  have hCMb : CMOf M b = CGOf b := inf_eq_right.2 hCb
  by_cases h2 : barLen (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩)) = 2 ∧
      barLen (Multiplicative.toAdd (D.piQ ⟨b, hbQ⟩)) = 2
  ·
    obtain ⟨σ, hσA, hσ⟩ := SixS.exists_alt_barAct_eq
      (u := Multiplicative.toAdd (D.piQ ⟨b, hbQ⟩)) (v := Multiplicative.toAdd (D.piQ ⟨a, haQ⟩))
      (h2.2.trans h2.1.symm)
    obtain ⟨c, hcθ⟩ := C.exists_lift hσA
    have hcM : (c : G) ∈ M := C.S.le c.2
    have hcbQ : (c : G) * b * (c : G)⁻¹ ∈ Q := pCoreOf_normalized M hcM hbQ
    have hπ : D.piQ ⟨(c : G) * b * (c : G)⁻¹, hcbQ⟩ = D.piQ ⟨a, haQ⟩ := by
      apply Multiplicative.toAdd.injective
      rw [D.piQ_conj ⟨(c : G), hcM⟩ ⟨b, hbQ⟩ _ rfl,
        show C.θ ⟨(c : G), hcM⟩ = σ from hcθ, hσ]
    set h : G := (c : G) * g⁻¹ with hh
    have hha : h * a * h⁻¹ = (c : G) * b * (c : G)⁻¹ := by rw [hh, hb]; group
    have hgh : g = h⁻¹ * (c : G) := by rw [hh]; group
    suffices hhM : h ∈ M by
      rw [hgh]
      exact M.mul_mem (M.inv_mem hhM) hcM
    set ρ : G := a⁻¹ * (h * a * h⁻¹) with hρdef
    have hρR : ρ ∈ Rc X := by
      have h1 : D.piQ (⟨a, haQ⟩⁻¹ * ⟨(c : G) * b * (c : G)⁻¹, hcbQ⟩) = 1 := by
        rw [map_mul, map_inv, hπ, inv_mul_cancel]
      have h2' := (D.piQ_eq_one_iff _).1 h1
      have e : ((⟨a, haQ⟩⁻¹ * ⟨(c : G) * b * (c : G)⁻¹, hcbQ⟩ : ↥Q) : G) = ρ := by
        rw [hρdef, hha]
        rfl
      rwa [e] at h2'
    have hhaρ : h * a * h⁻¹ = a * ρ := by rw [hρdef]; group
    by_cases hρ1 : ρ = 1
    ·
      have hc : h * a * h⁻¹ = a := by rw [hhaρ, hρ1, mul_one]
      exact hCa (mem_centralizer_zpowers_iff.2 hc)
    ·
      have hRQ : Rc X ≤ Q := by
        rw [C.S.R_eq_inf]
        exact inf_le_left
      have hρQ : ρ ∈ Q := hRQ hρR
      have haρQ : a * ρ ∈ Q := Q.mul_mem haQ hρQ
      have haρ1 : a * ρ ≠ 1 := by
        rw [← hhaρ]
        intro h0
        apply ha1'
        have : a = h⁻¹ * (h * a * h⁻¹) * h := by group
        rw [this, h0]
        group
      have hCaρ : CGOf (a * ρ) ≤ M := by
        have := hH _ haρQ haρ1
        rwa [centralizer_singleton_eq_zpowers] at this
      have hCeq : CGOf (a * ρ) = CGOf a :=
        H4b.CGOf_eq_of_mem_R (C := C) hR hCa hCaρ hρR rfl
      have hnorm : conjSubgroup h (CGOf a) = CGOf a := by
        rw [← H4b.CGOf_conj, hhaρ, hCeq]
      set P : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf a) with hP
      have hhP : ∀ p ∈ P, h * p * h⁻¹ ∈ P := by
        intro p hp
        have h1 : h * p * h⁻¹ ∈ conjSubgroup h P := by
          rw [mem_conjSubgroup]
          have : h⁻¹ * (h * p * h⁻¹) * h = p := by group
          rw [this]
          exact hp
        have h2'' := H4b.conj_pCoreOf_le h (CGOf a) h1
        rwa [hnorm] at h2''
      have hQP : Q ≤ P := by
        have := Q_le_TOf hQab haQ
        have e : TOf M a = P := by
          show CFSG.Open.pCoreOf 2 (CMOf M a) = _
          rw [hCMa]
        rwa [e] at this
      have hconjP : conjSubgroup h P = P := by
        have hle : conjSubgroup h P ≤ P := by
          intro w hw
          have h1 := hhP _ (mem_conjSubgroup.1 hw)
          have e : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
          rwa [e] at h1
        exact Subgroup.eq_of_le_of_card_ge hle
          (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
      have hhinv : ∀ p ∈ P, h⁻¹ * p * h ∈ P := by
        intro p hp
        have h1 : p ∈ conjSubgroup h P := by rw [hconjP]; exact hp
        exact mem_conjSubgroup.1 h1
      set ρ' : G := h * ρ * h⁻¹ with hρ'
      have hρ'Q : ρ' ∈ Q := by
        have hCQ := C.centralizer_Q_eq hR
        rw [← hQ] at hCQ
        rw [← hCQ, Subgroup.mem_centralizer_iff]
        intro q hq
        have hq' : h⁻¹ * q * h ∈ P := hhinv q (hQP hq)
        have hqM : h⁻¹ * q * h ∈ M := hCa (pCoreOf_le_self _ hq')
        have hc := C.R_central hR _ hqM ρ hρR
        calc q * ρ' = h * ((h⁻¹ * q * h) * ρ * (h⁻¹ * q * h)⁻¹) * h⁻¹ * q := by
              rw [hρ']; group
          _ = h * ρ * h⁻¹ * q := by rw [hc]
          _ = ρ' * q := by rw [hρ']
      have hρ'1 : ρ' ≠ 1 := by
        intro h0
        apply hρ1
        have : ρ = h⁻¹ * ρ' * h := by rw [hρ']; group
        rw [this, h0]
        group
      have hCρ : Subgroup.centralizer ({ρ} : Set G) = M := by
        refine le_antisymm (C.S.centralizer_le_of_mem_R hρR hρ1) fun m hm => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := C.R_central hR m hm ρ hρR
        calc m * ρ = (m * ρ * m⁻¹) * m := by group
          _ = ρ * m := by rw [this]
      have hCρ' : Subgroup.centralizer ({ρ'} : Set G) = M := by
        have hle := hH ρ' hρ'Q hρ'1
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        have e : Subgroup.centralizer ({ρ'} : Set G) =
            conjSubgroup h (Subgroup.centralizer ({ρ} : Set G)) := by
          rw [centralizer_singleton_eq_zpowers, centralizer_singleton_eq_zpowers, hρ']
          exact H4b.CGOf_conj h ρ
        rw [e, hCρ]
        exact (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
      have hρ'R : ρ' ∈ Rc X := by
        rw [C.S.R_eq_inf]
        refine Subgroup.mem_inf.2 ⟨hρ'Q, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
        have hxC : x ∈ Subgroup.centralizer ({ρ'} : Set G) := by
          rw [hCρ']
          exact C.S.le hx
        exact Subgroup.mem_centralizer_singleton_iff.1 hxC
      have heq : ρ' = ρ := by
        have hne1 : (⟨ρ', hρ'R⟩ : ↥(Rc X)) ≠ 1 := fun h0 => hρ'1 (congrArg Subtype.val h0)
        have hne2 : (⟨ρ, hρR⟩ : ↥(Rc X)) ≠ 1 := fun h0 => hρ1 (congrArg Subtype.val h0)
        exact congrArg Subtype.val (eq_of_card_le_two hR hne1 hne2)
      have hhρ : h ∈ Subgroup.centralizer ({ρ} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : h * ρ * h⁻¹ = ρ := heq
        calc h * ρ = (h * ρ * h⁻¹) * h := by group
          _ = ρ * h := by rw [this]
      rw [hCρ] at hhρ
      exact hhρ
  ·
    have hboth : barLen (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩)) ≠ 2 ∧
        barLen (Multiplicative.toAdd (D.piQ ⟨b, hbQ⟩)) ≠ 2 := by
      obtain ⟨ka, hka, hMa⟩ := D.card_M_eq_CMOf_six hR ⟨a, haQ⟩
      obtain ⟨kb, hkb, hMb⟩ := D.card_M_eq_CMOf_six hR ⟨b, hbQ⟩
      have hcard : Nat.card ↥(CMOf M a) = Nat.card ↥(CMOf M b) := by
        rw [hCMa, hCMb, hcardC]
      have hpos : 0 < Nat.card ↥(CMOf M a) := Nat.card_pos
      simp only at hMa hMb
      rw [← hcard] at hMb
      have hprod : Nat.card {u : permBar 6 // barLen u =
            barLen (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩))} * ka =
          Nat.card {u : permBar 6 // barLen u =
            barLen (Multiplicative.toAdd (D.piQ ⟨b, hbQ⟩))} * kb :=
        Nat.eq_of_mul_eq_mul_right hpos (hMa.symm.trans hMb)
      rcases SixS.card_barLen_cases (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩)) with
          ⟨hla, hoa⟩ | ⟨hla, hoa⟩ | ⟨hla, hoa⟩ | ⟨hla, hoa⟩ <;>
        rcases SixS.card_barLen_cases (Multiplicative.toAdd (D.piQ ⟨b, hbQ⟩)) with
          ⟨hlb, hob⟩ | ⟨hlb, hob⟩ | ⟨hlb, hob⟩ | ⟨hlb, hob⟩ <;>
        rw [hoa, hob] at hprod <;> omega
    have h4a : barLen (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩)) ≠ 4 := by
      have := SixS.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩))
      omega
    have h4b : barLen (Multiplicative.toAdd (D.piQ ⟨b, hbQ⟩)) ≠ 4 := by
      have := SixS.barLen_le_three (Multiplicative.toAdd (D.piQ ⟨b, hbQ⟩))
      omega
    exact D.mem_of_conj_of_len hR (x := ⟨b, hbQ⟩) (y := ⟨a, haQ⟩) hb1 ha1' ⟨hboth.2, h4b⟩
      ⟨hboth.1, h4a⟩ hab

theorem four_le_card_qB_six (hR : Nat.card ↥(Rc X) ≤ 2) : 4 ≤ Nat.card ↥C.qB := by
  have h1 : Nat.card ↥(blockU X) ≤ Nat.card ↥C.qB :=
    Subgroup.card_le_of_le (C.blockU_le_qB (C.Q_comm hR))
  have h2 := C.S.sixteen_le_card_blockU
  omega

include D in
theorem qB_ne_bot_sym (hR : Nat.card ↥(Rc X) ≤ 2) : C.qB ≠ ⊥ := by
  intro h
  have h4 := four_le_card_qB_six (C := C) hR
  rw [h, Subgroup.card_bot] at h4
  omega

include D in
theorem qB_isTI_sym (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    IsTI C.qB := by
  intro g
  by_cases hbot : C.qB ⊓ conjSubgroup g C.qB = ⊥
  · exact Or.inl hbot
  · right
    have hne : CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ ⊥ := by
      intro h
      apply hbot
      refine le_bot_iff.1 ?_
      rw [← h]
      exact inf_le_inf C.qB_le_Q fun e he =>
        mem_conjSubgroup.2 (C.qB_le_Q (mem_conjSubgroup.1 he))
    have hQg := D.conj_eq_of_inf_ne_bot_sym hR hH hne
    have hgM : g ∈ M := by
      rw [← C.S.normalizer_Q_eq]
      exact TI.mem_normalizer_iff_conj.2 hQg
    have hgB : g ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) := by
      rw [C.normalizer_qB_eq hR]
      exact hgM
    rw [TI.mem_normalizer_iff_conj.1 hgB, inf_idem]

include D in
theorem qB_weaklyClosed_sym (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    WeaklyClosedIn C.qB (Subgroup.normalizer ((C.qB : Subgroup G) : Set G)) := by
  have hQ := C.Q_comm hR
  refine TI.weaklyClosed_of_cent C.qB_le_Q (D.qB_ne_bot_sym hR) (isPGroup_pCoreOf' M) ?_
    ((C.normalizer_qB_eq hR).trans C.S.normalizer_Q_eq.symm)
    (fun _ hg => D.conj_eq_of_inf_ne_bot_sym hR hH hg)
  intro c hc
  have hcN : c ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer ((C.qB : Subgroup G) : Set G)
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hc b hb).symm)
  have hcM : c ∈ M := by
    rw [← C.normalizer_qB_eq hR]
    exact hcN
  have hcK : c ∈ C.K :=
    C.mem_K_of_comm_W hcM fun w hw => hc w (C.blockU_le_qB hQ hw)
  rw [C.K_eq_Q hR] at hcK
  exact hcK

end Cfg.PiData

namespace Cfg.PiData

theorem inCatalog_of_centInM_sym
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (C : Cfg G M X 6) (D : C.PiData)
    (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    CFSG.Assembly.InCatalog G :=
  CFSG.CGT.Hall82.inCatalog_of_isTI_of_weaklyClosedIn hNode C.S.simple C.S.nonab
    (C.isElemAbelian_qB (C.Q_comm hR)) (D.qB_ne_bot_sym hR) (D.qB_isTI_sym hR hH)
    (D.qB_weaklyClosed_sym hR hH)

end Cfg.PiData

end TIStep

end CFSG.RankThree.PartTwo.Sec19.SolEven
