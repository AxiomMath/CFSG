module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSNorm

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem exists_piQ_eq_uvec_six (a b : Fin 6) :
    ∃ q : ↥(CFSG.Open.pCoreOf 2 M), (q : G) ∈ blockU X ∧
      Multiplicative.toAdd (D.piQ q) = uvec a b := by
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd (pairEW a b : altHeart 6))
  refine ⟨⟨(w : G), C.S.W_le_Q w.2⟩, w.2, ?_⟩
  rw [D.piQ_W w _ rfl, hw, toAdd_ofAdd, heartToBar_pairEW_eq_uvec]

variable
  (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M)
include hR hsurj hQ16 hij hπ hK

theorem sup_eq_cases :
    CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = C.T2 i j ∨
      CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = C.T1 i j ∨
      CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x := by
  classical
  set P : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf x) with hP
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have hx1 : x ≠ 1 := D.ne_one_of_len_two hx (Finset.card_pair hij) hπ
  have hH2 : IsPGroup 2 (P ⊔ Q : Subgroup G) := H4b.isPGroup_sup C hR hx
  have hUT : (P ⊔ Q) ⊓ M ≤ TOf M x := H4b.sup_inf_le_TOf C hR hx
  have hPQ : ¬ P ≤ Q := H4b.not_P_le_Q C hR hx hx1 hK
  have hQU : Q ≤ (P ⊔ Q) ⊓ M := le_inf le_sup_right (pCoreOf_le_self M)
  have hUn : ∀ k ∈ CMOf M x, ∀ u ∈ (P ⊔ Q) ⊓ M, k * u * k⁻¹ ∈ (P ⊔ Q) ⊓ M := fun k hk u hu =>
    ⟨sup_norm hk hu.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.1 hk).1 hu.2)
      (M.inv_mem (Subgroup.mem_inf.1 hk).1)⟩
  have key : ∀ {N : Subgroup G}, (P ⊔ Q) ⊓ M = N → Subgroup.normalizer (N : Set G) ≤ M →
      P ⊔ Q = N := by
    intro N hN hNM
    have hNH : N ≤ P ⊔ Q := hN ▸ inf_le_left
    by_contra hne
    obtain ⟨h, hhH, hhN', hhN⟩ := exists_mem_normalizer_of_lt hH2 hNH (Ne.symm hne)
    apply hhN'
    rw [← hN]
    exact ⟨hhH, hNM hhN⟩
  rcases D.normal_cases hR hsurj hx hij hπ hQU hUT hUn with h | h | h | h
  · exfalso
    have hQH : Q ≠ P ⊔ Q := fun h' => hPQ (by rw [h']; exact le_sup_left)
    obtain ⟨t, htH, htQ, htN⟩ := exists_mem_normalizer_of_lt hH2 le_sup_right hQH
    have htM : t ∈ M := by rw [← C.S.normalizer_Q_eq]; exact htN
    apply htQ
    rw [hQ, ← h]
    exact ⟨htH, htM⟩
  · exact Or.inl (key h (normalizer_T2_le (C := C) hR hsurj hQ16 hij))
  · exact Or.inr (Or.inl (key h (normalizer_T1_le (C := C) hR hij)))
  · exact Or.inr (Or.inr (key h (D.normalizer_TOf_le hR hsurj hQ16 hx hij hπ)))

theorem false_of_sup_eq_T1
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = C.T1 i j) : False := by
  classical
  set P : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf x) with hP
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  set J : Finset (Fin 6) := {i, j}ᶜ with hJdef
  have hJ : J.card = 4 := SixS.card_compl_pair hij
  have hx1 : x ≠ 1 := D.ne_one_of_len_two hx (Finset.card_pair hij) hπ
  have hPT1 : P ≤ C.T1 i j := h ▸ le_sup_left
  have hPM : P ≤ M := hPT1.trans (C.thetaPre_le_M _)
  have hQK : Q ≤ CGOf x := H4b.Q_le_CGOf C hR hx
  have hcons := H4b.twoConstrained_P C hR hx hx1
  have hθP : ((P.subgroupOf M).map C.θ) = klein4 J := by
    have h1 : ((C.T1 i j).subgroupOf M).map C.θ = klein4 J := C.theta_thetaPre hsurj _
    rw [← h, Subgroup.subgroupOf_sup hPM (pCoreOf_le_self M), Subgroup.map_sup] at h1
    have h2 : (Q.subgroupOf M).map C.θ = ⊥ :=
      (Subgroup.map_eq_bot_iff _).2 (le_of_eq (C.theta_ker_eq hR).symm)
    rw [h2, sup_bot_eq] at h1
    exact h1
  have hZQ : ∀ z ∈ P, (∀ p ∈ P, p * z = z * p) → z ∈ Q := by
    intro z hzP hz
    by_contra hzQ
    have hzM : z ∈ M := hPM hzP
    have hθz : C.θ ⟨z, hzM⟩ ≠ 1 := fun h' => hzQ (by
      have hK' : z ∈ C.K := C.mem_K.2 ⟨hzM, h'⟩
      rwa [C.K_eq_Q hR] at hK')
    have hF := klein4_fourGroup hJ
    have hzN : C.θ ⟨z, hzM⟩ ∈ klein4 J := by
      rw [← hθP]
      exact Subgroup.mem_map.2 ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.2 hzP, rfl⟩
    have hNne : klein4 J ≠ ⊥ := fun h' => hθz (Subgroup.mem_bot.1 (h' ▸ hzN))
    obtain ⟨σ', hσ'N, hσ'1, hσ'z⟩ := hF.exists_ne hJ hNne (C.θ ⟨z, hzM⟩)
    have hσ'P : σ' ∈ (P.subgroupOf M).map C.θ := by
      rw [hθP]
      exact hσ'N
    obtain ⟨pm, hpm, hpmσ⟩ := Subgroup.mem_map.1 hσ'P
    have hpP : (pm : G) ∈ P := Subgroup.mem_subgroupOf.1 hpm
    obtain ⟨a, haJ⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
    have hiJ : i ∉ J := by simp [hJdef]
    have hd'fix : σ' i = i := hF.fix σ' hσ'N i hiJ
    obtain ⟨q, -, hq⟩ := D.exists_piQ_eq_uvec_six a i
    have hqK : (q : G) ∈ CGOf x := hQK q.2
    have hpq : (pm : G) * (q : G) * (pm : G)⁻¹ ∈ Q := pCoreOf_normalized M pm.2 q.2
    have hconj := D.piQ_conj pm q ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩ rfl
    let cq : ↥(CFSG.Open.pCoreOf 2 M) := q⁻¹ * ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩
    have hπc : Multiplicative.toAdd (D.piQ cq) = uvec a (σ' a) := by
      simp only [cq, map_mul, map_inv, toAdd_mul, toAdd_inv]
      rw [hconj, hpmσ, hq, barAct_uvec, hd'fix]
      exact neg_uvec_add_uvec a (σ' a) i
    have hcP : (cq : G) ∈ P := by
      have e : (cq : G) = ((q : G)⁻¹ * (pm : G) * (q : G)) * (pm : G)⁻¹ := by
        show (q : G)⁻¹ * ((pm : G) * (q : G) * (pm : G)⁻¹) = _
        group
      have h3 : (q : G)⁻¹ * (pm : G) * (q : G) ∈ P := by
        have := pCoreOf_normalized _ ((CGOf x).inv_mem hqK) hpP
        simpa using this
      rw [e]
      exact P.mul_mem h3 (P.inv_mem hpP)
    have hzc : (cq : G) = z * (cq : G) * z⁻¹ := by
      have h1 := hz _ hcP
      calc (cq : G) = ((cq : G) * z) * z⁻¹ := by group
        _ = (z * (cq : G)) * z⁻¹ := by rw [h1]
    have h2 := D.piQ_conj ⟨z, hzM⟩ cq cq hzc
    rw [hπc] at h2
    exact Six.FourGroup_barAct_uvec_ne hF hJ hzN hθz hσ'N hσ'1 (Ne.symm hσ'z) haJ h2.symm
  obtain ⟨z₀, hz₀P, hz₀c, hz₀Q, hz₀1, hz₀l⟩ : ∃ z₀ ∈ P, (∀ p ∈ P, p * z₀ = z₀ * p) ∧
      ∃ hz : z₀ ∈ Q, z₀ ≠ 1 ∧ barLen (Multiplicative.toAdd (D.piQ ⟨z₀, hz⟩)) ≠ 2 := by
    by_cases hRb : Rc X = ⊥
    · have hbij := D.piQ_bijective_of_bot hRb hQ16
      obtain ⟨s, hs⟩ := hbij.2 (Multiplicative.ofAdd (barInd ({i} : Finset (Fin 6))))
      have hsQ : (s : G) ∈ Q := s.2
      have hsc : ∀ t ∈ C.T1 i j, t * (s : G) * t⁻¹ = s := by
        intro t ht
        obtain ⟨htM, htθ⟩ := C.mem_thetaPre.1 ht
        have hts : t * (s : G) * t⁻¹ ∈ Q := pCoreOf_normalized M htM hsQ
        have h1 := D.piQ_conj ⟨t, htM⟩ s ⟨_, hts⟩ rfl
        have hfix : barAct (C.θ ⟨t, htM⟩) (barInd ({i} : Finset (Fin 6))) =
            barInd ({i} : Finset (Fin 6)) := by
          rw [barAct_barInd, Finset.image_singleton, (SixS.klein4_fix hij htθ).1]
        rw [hs, toAdd_ofAdd, hfix] at h1
        have h2 : D.piQ ⟨_, hts⟩ = D.piQ s := by
          apply Multiplicative.toAdd.injective
          rw [h1, hs, toAdd_ofAdd]
        exact congrArg Subtype.val (hbij.1 h2)
      have hsP : (s : G) ∈ P := hcons (Subgroup.mem_inf.2 ⟨hQK hsQ,
        Subgroup.mem_centralizer_iff.2 fun p hp => by
          have := hsc p (hPT1 hp)
          calc p * (s : G) = (p * (s : G) * p⁻¹) * p := by group
            _ = (s : G) * p := by rw [this]⟩)
      refine ⟨s, hsP, fun p hp => ?_, hsQ, fun h1 => ?_, ?_⟩
      · have := hsc p (hPT1 hp)
        calc p * (s : G) = (p * (s : G) * p⁻¹) * p := by group
          _ = (s : G) * p := by rw [this]
      · have : s = 1 := Subtype.ext h1
        rw [this, map_one] at hs
        have h0 := congrArg Multiplicative.toAdd hs
        rw [toAdd_one, toAdd_ofAdd] at h0
        have h00 := congrArg barLen h0
        rw [barLen_barInd, Finset.card_singleton, Comb.barLen_zero] at h00
        norm_num at h00
      · show barLen (Multiplicative.toAdd (D.piQ s)) ≠ 2
        rw [hs, toAdd_ofAdd, barLen_barInd, Finset.card_singleton]
        norm_num
    · obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRb
      have hr1' : r ≠ 1 := fun h' => hr1 (Subtype.ext h')
      have hrQ : r ∈ Q := by
        rw [C.S.R_eq_inf] at hr
        exact hr.1
      have hrc : ∀ p ∈ P, p * r = r * p := fun p hp => by
        have := C.R_central hR p (hPM hp) r hr
        calc p * r = (p * r * p⁻¹) * p := by group
          _ = r * p := by rw [this]
      have hrP : r ∈ P := hcons (Subgroup.mem_inf.2 ⟨hQK hrQ,
        Subgroup.mem_centralizer_iff.2 fun p hp => hrc p hp⟩)
      refine ⟨r, hrP, hrc, hrQ, hr1', ?_⟩
      have h1 : D.piQ ⟨r, hrQ⟩ = 1 := (D.piQ_eq_one_iff _).2 hr
      rw [h1, toAdd_one, Comb.barLen_zero]
      norm_num
  apply hK
  intro k hk
  have hkz : k * z₀ * k⁻¹ ∈ H4b.centerP x := by
    have hz₀Z : z₀ ∈ H4b.centerP x := Subgroup.mem_inf.2 ⟨hz₀P,
      Subgroup.mem_centralizer_iff.2 fun p hp => hz₀c p hp⟩
    exact (Subgroup.mem_normalizer_iff.1 (H4b.mem_normalizer_centerP hk) z₀).1 hz₀Z
  obtain ⟨hkzP, hkzc⟩ := Subgroup.mem_inf.1 hkz
  have hkzQ : k * z₀ * k⁻¹ ∈ Q :=
    hZQ _ hkzP fun p hp => Subgroup.mem_centralizer_iff.1 hkzc p hp
  exact D.mem_M_of_conj_len_ne_two hR hsurj hz₀Q hz₀1 hz₀l hkzQ

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
