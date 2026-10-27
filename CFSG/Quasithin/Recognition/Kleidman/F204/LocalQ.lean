module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Offender

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin
  CFSG.Quasithin.FA5

section Abstract

variable {H : Type*} [Group H]

theorem commute_comm_of_normalizes {ξ σ δ : H} (hδ : Commute δ ξ)
    (hσ : σ⁻¹ * ξ * σ ∈ Subgroup.zpowers ξ) : Commute (δ * σ * δ⁻¹ * σ⁻¹) ξ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have e1 : σ⁻¹ * ξ * σ = ξ ^ k := hk.symm
  have hξ : ξ = σ * ξ ^ k * σ⁻¹ := by rw [hk]; group
  have hck : δ * ξ ^ k = ξ ^ k * δ := (hδ.zpow_right k).eq
  have e2 : δ⁻¹ * ξ ^ k * δ = ξ ^ k := by
    calc δ⁻¹ * ξ ^ k * δ = δ⁻¹ * (ξ ^ k * δ) := by group
      _ = δ⁻¹ * (δ * ξ ^ k) := by rw [hck]
      _ = ξ ^ k := by group
  have e3 : δ * ξ * δ⁻¹ = ξ := by
    have := hδ.eq
    calc δ * ξ * δ⁻¹ = (ξ * δ) * δ⁻¹ := by rw [this]
      _ = ξ := by group
  have key : (δ * σ * δ⁻¹ * σ⁻¹) * ξ * (δ * σ * δ⁻¹ * σ⁻¹)⁻¹ = ξ := by
    calc (δ * σ * δ⁻¹ * σ⁻¹) * ξ * (δ * σ * δ⁻¹ * σ⁻¹)⁻¹
        = δ * σ * (δ⁻¹ * (σ⁻¹ * ξ * σ) * δ) * σ⁻¹ * δ⁻¹ := by group
      _ = δ * σ * (δ⁻¹ * ξ ^ k * δ) * σ⁻¹ * δ⁻¹ := by rw [e1]
      _ = δ * (σ * ξ ^ k * σ⁻¹) * δ⁻¹ := by rw [e2]; group
      _ = δ * ξ * δ⁻¹ := by rw [← hξ]
      _ = ξ := e3
  exact mul_inv_eq_iff_eq_mul.mp key

end Abstract

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem comm_D_S_mem_Q1 (F : Frame L1 L2 S D X) {d s : G} (hd : d ∈ D) (hs : s ∈ S) :
    d * s * d⁻¹ * s⁻¹ ∈ Q1 L1 L2 S := by
  obtain ⟨x0, hx0, hx05, hx01, hgen⟩ := F.exists_gen
  have hdB : d ∈ bigB L1 L2 S := F.D_le_B hd
  have hdP : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hdB
  have hsP : s ∈ P1 L1 L2 S := F.mem_P1_of_mem_S hs
  have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  have hu : d * s * d⁻¹ * s⁻¹ ∈ S :=
    S.mul_mem (F.normalizes_S d hd s hs) (S.inv_mem hs)
  set π := Frame.pi1 L1 L2 S with hπ
  set d' : ↥(P1 L1 L2 S) := ⟨d, hdP⟩ with hd'
  set s' : ↥(P1 L1 L2 S) := ⟨s, hsP⟩ with hs'
  set x' : ↥(P1 L1 L2 S) := ⟨x0, hx0P⟩ with hx'
  set ξ := π x' with hξ
  have hxj : ∀ j : ℤ, x0 ^ j ∈ P1 L1 L2 S := fun j => (P1 L1 L2 S).zpow_mem hx0P j
  have hπx : ∀ j : ℤ, π ⟨x0 ^ j, hxj j⟩ = ξ ^ j := by
    intro j
    rw [hξ, ← map_zpow]
    rfl
  have hdx : Commute (π d') ξ := by
    have hc : x0 * d = d * x0 := Subgroup.mem_centralizer_iff.mp (F.D_cent hd) x0 hx0
    have : d' * x' = x' * d' := Subtype.ext hc.symm
    show π d' * π x' = π x' * π d'
    rw [← map_mul, ← map_mul, this]
  have hsx : (π s')⁻¹ * ξ * π s' ∈ Subgroup.zpowers ξ := by
    have hsB : s⁻¹ ∈ bigB L1 L2 S := (bigB L1 L2 S).inv_mem (F.mem_B_of_mem_S hs)
    obtain ⟨y, hy, o, ho, h⟩ := F.conj_mem_X_mul hsB hx0
    obtain ⟨j, hj⟩ := hgen y hy
    refine ⟨j, ?_⟩
    show ξ ^ j = _
    rw [← hπx j]
    have hg : (π s')⁻¹ * ξ * π s' = π (s'⁻¹ * x' * s') := by
      rw [hξ, map_mul, map_mul, map_inv]
    rw [hg, eq_comm, Frame.pi1_eq_iff]
    show ((s⁻¹ * x0 * s : G))⁻¹ * x0 ^ j ∈ Q1 L1 L2 S
    have h1 : s⁻¹ * x0 * s = y * o := by simpa using h
    rw [h1, ← hj]
    have h2 : (y * o)⁻¹ * y = o⁻¹ := by group
    rw [h2]
    exact (Q1 L1 L2 S).inv_mem (F.pCore_L1_le_Q1 ho)
  have hcomm : Commute (π (d' * s' * d'⁻¹ * s'⁻¹)) ξ := by
    have := commute_comm_of_normalizes hdx hsx
    simpa [map_mul, map_inv] using this
  refine F.mem_Q1_of_commute (u := d' * s' * d'⁻¹ * s'⁻¹) hu (fun z hz => ?_)
  obtain ⟨j, hj⟩ := hgen z hz
  have hzz : z = ⟨x0 ^ j, hxj j⟩ := Subtype.ext hj
  rw [hzz, hπx j]
  exact (hcomm.zpow_right j).eq


omit [Finite G] in
theorem relIndex_pCoreOf_eq_card_quot' (L : Subgroup G) :
    (pCoreOf 2 L).relIndex L = Nat.card (OTwoQuot L) := by
  have h3 : (pCoreOf 2 L).subgroupOf L = CFSG.Open.pCore 2 ↥L := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  show ((pCoreOf 2 L).subgroupOf L).index = _
  rw [h3, Subgroup.index]

theorem relIndex_Q2_S (F : Frame L1 L2 S D X) : (Q2 L1 L2 S).relIndex S = 4 := by
  obtain ⟨e⟩ := F.pair.alt2
  set T : Subgroup G := S ⊓ L2 with hT
  set R : Subgroup G := pCoreOf 2 L2 with hR
  have h60 : R.relIndex L2 = 60 := by
    rw [hR, relIndex_pCoreOf_eq_card_quot', FA5.card_oTwoQuot_alt5 e]
    norm_num
  have h15 : T.relIndex L2 = 15 := F.pair.relIndex_sylow_right
  have hRQ : R ≤ Q2 L1 L2 S := F.pCore_L2_le_Q2
  have hRT : R ≤ T := le_inf (hRQ.trans F.Q2_le_S) (pCoreOf_le 2 L2)
  have hmul := Subgroup.relIndex_mul_relIndex R T L2 hRT inf_le_right
  have hRT4 : R.relIndex T = 4 := by rw [h60, h15] at hmul; omega
  have hTQ : T ⊓ Q2 L1 L2 S = R := by
    apply le_antisymm
    · have : L2 ⊓ Q2 L1 L2 S ≤ R := Frame.inf_Q2_le
      exact fun x hx => this ⟨hx.1.2, hx.2⟩
    · exact le_inf hRT hRQ
  have hSeq : T ⊔ Q2 L1 L2 S = S := by
    apply le_antisymm
    · exact sup_le inf_le_left F.Q2_le_S
    · intro s hs
      obtain ⟨l, hl, q, hq, hsq, hlS⟩ := F.exists_factor hs
      rw [hsq]
      exact Subgroup.mul_mem_sup ⟨hlS, hl⟩ hq
  have hTN : T ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    inf_le_left.trans ((show S ≤ bigB L1 L2 S from le_sup_right).trans
      ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans (P2_le_normalizer_Q2 L1 L2 S)))
  have h1 := F1.relIndex_sup_eq_of_le_normalizer hTN
  rw [hSeq] at h1
  rw [h1, ← Subgroup.inf_relIndex_right, inf_comm, hTQ, hRT4]

theorem eq_or_eq_of_D_invariant (F : Frame L1 L2 S D X) {M : Subgroup G}
    (hQM : Q2 L1 L2 S ≤ M) (hMS : M ≤ S) (hD : ∀ d ∈ D, ∀ m ∈ M, d * m * d⁻¹ ∈ M) :
    M = Q2 L1 L2 S ∨ M = S := by
  by_contra hcon
  obtain ⟨hMQ, hMS'⟩ := not_or.mp hcon
  have hmul := Subgroup.relIndex_mul_relIndex (Q2 L1 L2 S) M S hQM hMS
  rw [relIndex_Q2_S F] at hmul
  have ha1 : (Q2 L1 L2 S).relIndex M ≠ 1 := by
    intro h
    exact hMQ (le_antisymm (Subgroup.relIndex_eq_one.mp h) hQM)
  have hb1 : M.relIndex S ≠ 1 := by
    intro h
    exact hMS' (le_antisymm hMS (Subgroup.relIndex_eq_one.mp h))
  have ha0 : (Q2 L1 L2 S).relIndex M ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hb0 : M.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  have ha2 : (Q2 L1 L2 S).relIndex M = 2 := by
    generalize (Q2 L1 L2 S).relIndex M = a at *
    generalize M.relIndex S = b at *
    have hbge : 2 ≤ b := by omega
    have hage : 2 ≤ a := by omega
    have hale : a ≤ 2 := by nlinarith
    omega
  have hidx : ((Q2 L1 L2 S).subgroupOf M).index = 2 := ha2
  obtain ⟨d, hd, hd1⟩ := F.exists_ne_one_D
  obtain ⟨m, hm, hmQ⟩ : ∃ m ∈ M, m ∉ Q2 L1 L2 S := by
    by_contra h
    apply hMQ
    refine le_antisymm (fun m hm => ?_) hQM
    by_contra hmQ
    exact h ⟨m, hm, hmQ⟩
  have hdP : d ∈ P2 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (F.D_le_B hd)
  have hNQ := P2_le_normalizer_Q2 L1 L2 S
  have hdmQ : d * m * d⁻¹ ∉ Q2 L1 L2 S := by
    intro h
    apply hmQ
    have h' := (Subgroup.mem_normalizer_iff.mp (hNQ ((P2 L1 L2 S).inv_mem hdP)) _).mp h
    simpa [mul_assoc] using h'
  have hA : (⟨d * m * d⁻¹, hD d hd m hm⟩ : M) ∉ (Q2 L1 L2 S).subgroupOf M := hdmQ
  have hB : (⟨m⁻¹, M.inv_mem hm⟩ : M) ∉ (Q2 L1 L2 S).subgroupOf M := by
    intro h
    exact hmQ (by simpa using (Q2 L1 L2 S).inv_mem (show m⁻¹ ∈ Q2 L1 L2 S from h))
  have hprod := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hA hB)
  have hc : d * m * d⁻¹ * m⁻¹ ∈ Q2 L1 L2 S := hprod
  exact hmQ (F.fpf hd hd1 (hMS hm) hc)


omit [Finite G] in
theorem not_L2_le_normalizer_S (F : Frame L1 L2 S D X) :
    ¬ L2 ≤ Subgroup.normalizer (S : Set G) := by
  intro h
  apply F.pair.hyp.r2.borel_ne
  exact inf_eq_left.mpr (le_normalizer_inf h Subgroup.le_normalizer)

omit [Finite G] in
theorem not_L1_le_normalizer_S (F : Frame L1 L2 S D X) :
    ¬ L1 ≤ Subgroup.normalizer (S : Set G) := by
  intro h
  apply F.pair.hyp.r1.borel_ne
  exact inf_eq_left.mpr (le_normalizer_inf h Subgroup.le_normalizer)

theorem not_Q1_le_Q2 (F : Frame L1 L2 S D X) : ¬ Q1 L1 L2 S ≤ Q2 L1 L2 S := by
  intro hle
  obtain ⟨d, hd, hd1⟩ := F.exists_ne_one_D
  have hSQ : S ≤ Q2 L1 L2 S := fun s hs =>
    F.fpf hd hd1 hs (hle (comm_D_S_mem_Q1 F hd hs))
  have hQS : Q2 L1 L2 S = S := le_antisymm F.Q2_le_S hSQ
  apply not_L2_le_normalizer_S F
  have h := P2_le_normalizer_Q2 L1 L2 S
  rw [hQS] at h
  exact (le_sup_left : L2 ≤ P2 L1 L2 S).trans h

theorem Q1_sup_Q2 (F : Frame L1 L2 S D X) : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S := by
  have hDN : D ≤ Subgroup.normalizer ((Q1 L1 L2 S ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
    have hB : D ≤ bigB L1 L2 S := F.D_le_B
    exact F1.le_normalizer_sup
      (hB.trans ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (P1_le_normalizer_Q1 L1 L2 S)))
      (hB.trans ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans (P2_le_normalizer_Q2 L1 L2 S)))
  rcases eq_or_eq_of_D_invariant F (le_sup_right : Q2 L1 L2 S ≤ Q1 L1 L2 S ⊔ Q2 L1 L2 S)
    (sup_le F.Q1_le_S F.Q2_le_S) (fun d hd m hm =>
      (Subgroup.mem_normalizer_iff.mp (hDN hd) m).mp hm) with h | h
  · exact absurd (le_sup_left.trans h.le) (not_Q1_le_Q2 F)
  · exact h

theorem not_Q2_le_Q1 (F : Frame L1 L2 S D X) : ¬ Q2 L1 L2 S ≤ Q1 L1 L2 S := by
  intro hle
  have hDN : D ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    F.D_le_B.trans ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      (P1_le_normalizer_Q1 L1 L2 S))
  rcases eq_or_eq_of_D_invariant F hle F.Q1_le_S (fun d hd m hm =>
      (Subgroup.mem_normalizer_iff.mp (hDN hd) m).mp hm) with h | h
  ·
    have hP1 : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := P1_le_normalizer_Q1 L1 L2 S
    have hP2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
      rw [h]; exact P2_le_normalizer_Q2 L1 L2 S
    have hSP : S ≤ P1 L1 L2 S := fun s hs => F.mem_P1_of_mem_S hs
    have hG0 : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
      sup_le (sup_le ((le_sup_left : L1 ≤ P1 L1 L2 S).trans hP1)
        ((le_sup_left : L2 ≤ P2 L1 L2 S).trans hP2)) (hSP.trans hP1)
    have hBG0 : bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S :=
      sup_le (sup_le ((F1.borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
        ((F1.borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right
    have hP1G0 : P1 L1 L2 S ≤ L1 ⊔ L2 ⊔ S :=
      sup_le (le_sup_left.trans le_sup_left) hBG0
    have hQle : Q1 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 (P1 L1 L2 S)).trans hP1G0) hG0
        (pCoreOf_isPGroup 2 _)
    have hQbot : Q1 L1 L2 S = ⊥ :=
      le_bot_iff.mp (hQle.trans (le_of_eq F.pair.hyp.hyp.o2))
    obtain ⟨x0, hx0, -, hx01, -⟩ := F.exists_gen
    have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
    have hcent : x0 ∈ Subgroup.centralizer ((pCoreOf 2 (P1 L1 L2 S) : Subgroup G) : Set G) := by
      have h1 : pCoreOf 2 (P1 L1 L2 S) = ⊥ := hQbot
      rw [h1, Subgroup.mem_centralizer_iff]
      intro h hh
      have : h = 1 := by simpa using hh
      subst this
      simp
    have hmem : x0 ∈ pCoreOf 2 (P1 L1 L2 S) := F.charTwo_P1 ⟨hx0P, hcent⟩
    have h1 : pCoreOf 2 (P1 L1 L2 S) = ⊥ := hQbot
    rw [h1] at hmem
    exact hx01 (Subgroup.mem_bot.mp hmem)
  · exact not_L1_le_normalizer_S F (by
      have := P1_le_normalizer_Q1 L1 L2 S
      rw [h] at this
      exact (le_sup_left : L1 ≤ P1 L1 L2 S).trans this)

end CFSG.Quasithin.Kleidman.F204
