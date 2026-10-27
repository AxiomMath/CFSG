module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTI
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightLen2

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace Eight

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 8) (D : C.PiData)

theorem four_le_card_qB (hR : Nat.card ↥(Rc X) ≤ 2) : 4 ≤ Nat.card ↥C.qB := by
  have h1 : Nat.card ↥(blockU X) ≤ Nat.card ↥C.qB :=
    Subgroup.card_le_of_le (C.blockU_le_qB (C.Q_comm hR))
  have h2 : 2 ^ (8 - 2) ≤ Nat.card ↥(blockU X) := C.S.card_blockU_ge
  have h3 : (2 : ℕ) ^ (8 - 2) = 64 := by norm_num
  omega

theorem qB_ne_bot (hR : Nat.card ↥(Rc X) ≤ 2) : C.qB ≠ ⊥ := by
  intro h
  have h4 := four_le_card_qB C hR
  rw [h, Subgroup.card_bot] at h4
  omega

theorem card_le_two_mul_of_len_two (hR : Nat.card ↥(Rc X) ≤ 2) {a : G}
    (ha : a ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨a, ha⟩) = barInd I) {U : Subgroup G}
    (hUT : U ≤ TOf M a) : Nat.card ↥U ≤ 2 * Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) := by
  classical
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hI
  have hUM : U ≤ M := hUT.trans (TOf_le_M M a)
  have h1 := Cfg.card_eq_card_inf_mul (C := C) hR hUM
  have hval : ∀ σ ∈ (U.subgroupOf M).map C.θ, σ = 1 ∨ σ = swap i j := by
    rintro σ ⟨u, hu, rfl⟩
    exact theta_TOf_len_two D ha hij hπ (hUT (Subgroup.mem_subgroupOf.1 hu))
  have h2 : Nat.card ↥((U.subgroupOf M).map C.θ) ≤ 2 := by
    have hinj : Function.Injective (fun σ : ↥((U.subgroupOf M).map C.θ) =>
        decide ((σ : Perm (Fin 8)) = 1)) := by
      intro σ τ h
      simp only [decide_eq_decide] at h
      have hsw : swap i j ≠ 1 := fun e => hij.symm (by
        have := congrArg (fun f : Perm (Fin 8) => f i) e
        simpa using this)
      rcases hval σ σ.2 with h1 | h1 <;> rcases hval τ τ.2 with h2 | h2
      · exact Subtype.ext (h1.trans h2.symm)
      · exact absurd (h.1 h1) (by rw [h2]; exact hsw)
      · exact absurd (h.2 h2) (by rw [h1]; exact hsw)
      · exact Subtype.ext (h1.trans h2.symm)
    have h5 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h5
  calc Nat.card ↥U = Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) *
        Nat.card ↥((U.subgroupOf M).map C.θ) := h1
    _ ≤ Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) := mul_comm _ _

theorem mem_M_of_len_ne_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M)
    {g h : G} (hh : h ∈ CFSG.Open.pCoreOf 2 M) (hh1 : h ≠ 1)
    (hhg : g⁻¹ * h * g ∈ CFSG.Open.pCoreOf 2 M)
    (hlen : barLen (Multiplicative.toAdd (D.piQ ⟨h, hh⟩)) ≠ 2) : g ∈ M := by
  have hQ := C.Q_comm hR
  have hle := TI.conj_le_TOf hQ hH hh hh1 hhg
  have hcardg : Nat.card ↥(conjSubgroup g (CFSG.Open.pCoreOf 2 M)) =
      Nat.card ↥(CFSG.Open.pCoreOf 2 M) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  by_cases hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨h, hh⟩)) = 4
  · obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨h, hh⟩))
    rw [hl4] at hIc
    have hET : conjSubgroup g C.qB ≤ TOf M h := fun e he =>
      hle (mem_conjSubgroup.2 (C.qB_le_Q (mem_conjSubgroup.1 he)))
    exact mem_M_of_conj_qB_le_TOf D hR hh hIc hI hET
  · have hcent := centralizer_singleton_eq_zpowers h
    have hTQ : TOf M h ≤ CFSG.Open.pCoreOf 2 M := by
      have h1 := D.pCore_centralizer_le_Q_of_len hR ⟨h, hh⟩ ⟨hlen, hl4⟩
      have h2 : CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({h} : Set G)) ≤
          CFSG.Open.pCoreOf 2 M := h1
      rw [hcent] at h2
      exact h2
    have hEq : conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M :=
      Subgroup.eq_of_le_of_card_ge (hle.trans hTQ) hcardg.ge
    rw [← C.S.normalizer_Q_eq]
    exact TI.mem_normalizer_iff_conj.2 hEq

include C D in
theorem conj_eq_of_inf_ne_bot (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) {g : G}
    (hne : CFSG.Open.pCoreOf 2 M ⊓ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ ⊥) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  classical
  by_contra hQg
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  set Qg : Subgroup G := conjSubgroup g Q with hQg'
  have hQab := C.Q_comm hR
  have hgM : g ∉ M := fun hg => hQg (TI.conj_eq_of_mem_M hg)
  have hall : ∀ (h : G) (hh : h ∈ Q ⊓ Qg), h ≠ 1 →
      barLen (Multiplicative.toAdd (D.piQ ⟨h, (Subgroup.mem_inf.1 hh).1⟩)) = 2 := by
    intro h hh hh1
    by_contra hlen
    exact hgM (mem_M_of_len_ne_two C D hR hH (Subgroup.mem_inf.1 hh).1 hh1
      (mem_conjSubgroup.1 (Subgroup.mem_inf.1 hh).2) hlen)
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haQ : a ∈ Q := (Subgroup.mem_inf.1 ha).1
  have haQg : g⁻¹ * a * g ∈ Q := mem_conjSubgroup.1 (Subgroup.mem_inf.1 ha).2
  have hlen2 := hall a ha ha1'
  obtain ⟨I, hIc, hIπ⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨a, haQ⟩))
  rw [hlen2] at hIc
  have hle : Qg ≤ TOf M a := TI.conj_le_TOf hQab hH haQ ha1' haQg
  have hcard1 : Nat.card ↥Qg ≤ 2 * Nat.card ↥(Qg ⊓ Q) :=
    card_le_two_mul_of_len_two C D hR haQ hIc hIπ hle
  have hcardg : Nat.card ↥Qg = Nat.card ↥Q :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hH2 : Nat.card ↥Q ≤ 2 * Nat.card ↥(Q ⊓ Qg) :=
    calc Nat.card ↥Q = Nat.card ↥Qg := hcardg.symm
      _ ≤ 2 * Nat.card ↥(Qg ⊓ Q) := hcard1
      _ = 2 * Nat.card ↥(Q ⊓ Qg) := by rw [inf_comm]
  have hP4 : Nat.card ↥(((Q ⊓ Qg).subgroupOf Q).map D.piQ) ≤ 4 := by
    set P : Subgroup (Multiplicative (permBar 8)) := ((Q ⊓ Qg).subgroupOf Q).map D.piQ with hP
    have hV : ∀ v ∈ Subgroup.toAddSubgroup' P, v ≠ 0 → barLen v = 2 := by
      intro v hv hv0
      obtain ⟨k, hk, hkv⟩ := Subgroup.mem_map.1 ((Subgroup.mem_toAddSubgroup' P v).1 hv)
      have hkH : (k : G) ∈ Q ⊓ Qg := Subgroup.mem_subgroupOf.1 hk
      have hv' : Multiplicative.toAdd (D.piQ k) = v := by rw [hkv]; rfl
      have hk1 : (k : G) ≠ 1 := by
        intro h1
        apply hv0
        rw [← hv', show k = 1 from Subtype.ext h1, map_one]
        rfl
      rw [← hv']
      exact hall (k : G) hkH hk1
    have h4 := Comb.card_le_four_of_len_two (by norm_num) (Subgroup.toAddSubgroup' P) hV
    rw [card_toAddSubgroup'] at h4
    exact h4
  have hcardH := D.card_eq_card_inf_R_mul (inf_le_left : Q ⊓ Qg ≤ Q)
  have hRle : Nat.card ↥((Q ⊓ Qg) ⊓ Rc X) ≤ 2 :=
    (Subgroup.card_le_of_le inf_le_right).trans hR
  have hH8 : Nat.card ↥(Q ⊓ Qg) ≤ 8 := by
    refine hcardH.trans_le ?_
    calc Nat.card ↥((Q ⊓ Qg) ⊓ Rc X) * Nat.card ↥(((Q ⊓ Qg).subgroupOf Q).map D.piQ)
        ≤ 2 * 4 := Nat.mul_le_mul hRle hP4
      _ = 8 := by norm_num
  have hcardW : 2 ^ (8 - 2) ≤ Nat.card ↥(blockU X) := C.S.card_blockU_ge
  have hWQ : Nat.card ↥(blockU X) ≤ Nat.card ↥Q := Subgroup.card_le_of_le C.S.W_le_Q
  have h64 : (2 : ℕ) ^ (8 - 2) = 64 := by norm_num
  omega

include C D in
theorem qB_isTI (hR : Nat.card ↥(Rc X) ≤ 2)
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
    have hQg := conj_eq_of_inf_ne_bot C D hR hH hne
    have hgM : g ∈ M := by
      rw [← C.S.normalizer_Q_eq]
      exact TI.mem_normalizer_iff_conj.2 hQg
    have hgB : g ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) := by
      rw [C.normalizer_qB_eq hR]
      exact hgM
    rw [TI.mem_normalizer_iff_conj.1 hgB, inf_idem]

include C D in
theorem qB_weaklyClosed (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    WeaklyClosedIn C.qB (Subgroup.normalizer ((C.qB : Subgroup G) : Set G)) := by
  have hQ := C.Q_comm hR
  refine TI.weaklyClosed_of_cent C.qB_le_Q (qB_ne_bot C hR) (isPGroup_pCoreOf' M) ?_
    ((C.normalizer_qB_eq hR).trans C.S.normalizer_Q_eq.symm)
    (fun _ hg => conj_eq_of_inf_ne_bot C D hR hH hg)
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

include C D in
theorem inCatalog_of_centInM
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (hR : Nat.card ↥(Rc X) ≤ 2)
    (hH : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    CFSG.Assembly.InCatalog G :=
  CFSG.CGT.Hall82.inCatalog_of_isTI_of_weaklyClosedIn hNode C.S.simple C.S.nonab
    (C.isElemAbelian_qB (C.Q_comm hR)) (qB_ne_bot C hR) (qB_isTI C D hR hH)
    (qB_weaklyClosed C D hR hH)

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
