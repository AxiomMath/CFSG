module

public import CFSG.Quasithin.EmptyFaithful.F918C11
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

section Transport

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem autIH_ne_bot (h : HypF918 T V L V₁ Vp H K) : autIH V₁ Vp H K ≠ ⊥ := by
  intro hbot
  have hF := factElem h (le_conjClosure Vp H)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKQ : K ≤ pCoreOf 2 H := by
    intro k hk
    refine mem_pCoreOf_of_actH_eq_one h (x := ⟨k, hKH hk⟩) ?_
    have hmem : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) ⟨k, hKH hk⟩ ∈
        autIH V₁ Vp H K := by
      rw [autIH_eq_map h hKH]
      exact ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 ↥K := (pCoreOf_isPGroup 2 H).to_le hKQ
  have : Group.IsNilpotent ↥K := hKp.isNilpotent
  exact not_isSolvable_of_mem_cComp h.K_cComp inferInstance

theorem nonempty_kbar_mulEquiv_aut (h : HypF918 T V L V₁ Vp H K) (hS : IsSimpleGroup (KBar K)) :
    Nonempty (KBar K ≃* ↥(autIH V₁ Vp H K)) := by
  have hF := factElem h (le_conjClosure Vp H)
  have hSq : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := MulEquiv.isSimpleGroup (kbarEquiv K).symm
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_autI h (le_conjClosure Vp H) hSq (autIH_ne_bot h)
  exact ⟨(kbarEquiv K).trans e⟩

theorem nonempty_kbar_mulEquiv_autQuot (h : HypF918 T V L V₁ Vp H K) (hS : IsSimpleGroup (KBar K)) :
    Nonempty (KBar K ≃* ↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K)) := by
  obtain ⟨e⟩ := nonempty_kbar_mulEquiv_aut h hS
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.K_cComp)
  have hperfQ : Group.IsPerfect (KBar K) :=
    Group.IsPerfect.ofSurjective (G := ↥K) (G' := KBar K)
      (f := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) (QuotientGroup.mk'_surjective _)
  have hSA : IsSimpleGroup ↥(autIH V₁ Vp H K) := MulEquiv.isSimpleGroup e.symm
  have hperfA : Group.IsPerfect ↥(autIH V₁ Vp H K) :=
    Group.IsPerfect.ofSurjective (G := KBar K) (G' := ↥(autIH V₁ Vp H K)) (f := e.toMonoidHom)
      e.surjective
  have hZ : Subgroup.center ↥(autIH V₁ Vp H K) = ⊥ := center_eq_bot_of_simple_perfect hperfA
  exact ⟨e.trans (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))⟩

theorem fourList_kbar (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T = K)
    (hS : IsSimpleGroup (KBar K)) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) :
    FourList (KBar K) := by
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU h
  have h4 := (F918_4' h hH hK hV₁I hIU W hW hirrU hD310 hD391 hI4).1
  obtain ⟨e⟩ := nonempty_kbar_mulEquiv_autQuot h hS
  exact fourList_congr e.symm h4

theorem fiveShape_kbar (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H)
    (hK : conjClosure K T ≠ K) (hS : IsSimpleGroup (KBar K)) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) : FiveShape (KBar K) := by
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU h
  have h5 := (F918_5' h hH hK hV₁I hIU W hW hirrU hD36 hD37 hD321 hI5 hA37 hA38).1
  obtain ⟨e⟩ := nonempty_kbar_mulEquiv_aut h hS
  exact fiveShape_congr e.symm h5

end Transport

section Rank

variable {G : Type} [Group G] [Finite G]

@[expose] def SecExt (A Q : Subgroup G) (PV PY : ∀ (V : Type) [Group V], Prop) : Prop :=
  ∃ _ : (Q.subgroupOf A).Normal, IsExt (↥A ⧸ Q.subgroupOf A) PV PY

theorem two_le_pRank_of_secExt {A Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (h : SecExt A Q (IsE2 4) (IsAlt 6)) : 2 ≤ CFSG.Open.pRank 3 A := by
  obtain ⟨hN, V, hV, hVE, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNp : IsPGroup 2 ↥(Q.subgroupOf A) := by
    let ϕ : ↥(Q.subgroupOf A) →* ↥Q :=
      ((A.subtype).comp (Q.subgroupOf A).subtype).codRestrict Q (fun x => x.2)
    refine hQ.of_injective ϕ ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥Q => (z : G)) hxy
  have hN3 : ¬ 3 ∣ Nat.card ↥(Q.subgroupOf A) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hNp
    rw [hj]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hV3 : ¬ 3 ∣ Nat.card ↥V := by
    obtain ⟨e'⟩ := hVE
    rw [Nat.card_congr e'.toEquiv]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
      ZMod.card, Fintype.card_fin]
    norm_num
  have h1 := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three (Q.subgroupOf A) hN3
  have h2 := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three V hV3
  have h3 : 2 ≤ CFSG.pRank 3 ((↥A ⧸ Q.subgroupOf A) ⧸ V) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top
      (CFSG.SectionRank.isElemAbelian_sylowThreeAlt (n := 6) le_rfl)
      (CFSG.SectionRank.card_sylowThreeAlt (n := 6) le_rfl)
  have h4 : CFSG.pRank 3 ↥A = CFSG.Open.pRank 3 A := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact pRank_top_subtype (p := 3) A
  rw [← h4, ← h1, ← h2]
  exact h3

end Rank

end CFSG.Quasithin
