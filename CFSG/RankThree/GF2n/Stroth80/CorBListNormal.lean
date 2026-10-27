module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCorBList

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem corBN_pPrimeCore_eq_bot {Y : Type} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hO : ∀ P : Subgroup Y, P.Normal → P ≤ S → Odd (Nat.card P) → P = ⊥) :
    CFSG.pPrimeCore 2 ↥S = ⊥ := by
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 ↥S)) := CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card ↥((CFSG.pPrimeCore 2 ↥S).map S.subtype) =
      Nat.card ↥(CFSG.pPrimeCore 2 ↥S) :=
    (Nat.card_congr ((CFSG.pPrimeCore 2 ↥S).equivMapOfInjective S.subtype
      S.subtype_injective).toEquiv).symm
  have hP : (CFSG.pPrimeCore 2 ↥S).map S.subtype = ⊥ :=
    hO ((CFSG.pPrimeCore 2 ↥S).map S.subtype) inferInstance (Subgroup.map_subtype_le _) (by
      rw [hcard]
      exact Nat.coprime_two_left.1 hcop)
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 hP

theorem corBN_pCore_eq_bot {Y : Type} [Group Y] (S : Subgroup Y) [S.Normal]
    (hO2 : ∀ P : Subgroup Y, P.Normal → P ≤ S → IsPGroup 2 P → P = ⊥) :
    CFSG.pCore 2 ↥S = ⊥ := by
  have hpg : IsPGroup 2 ↥((CFSG.pCore 2 ↥S).map S.subtype) :=
    IsPGroup.map (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥S)) S.subtype
  have hP : (CFSG.pCore 2 ↥S).map S.subtype = ⊥ :=
    hO2 ((CFSG.pCore 2 ↥S).map S.subtype) inferInstance (Subgroup.map_subtype_le _) hpg
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 hP

theorem corBN_oddCore_quotBot_eq_bot {Y : Type} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hO : ∀ P : Subgroup Y, P.Normal → P ≤ S → Odd (Nat.card P) → P = ⊥) :
    fusionOddCore (↥S ⧸ (⊥ : Subgroup ↥S)) = ⊥ := by
  rw [corB_fusionOddCore_eq, CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  let e : (↥S ⧸ (⊥ : Subgroup ↥S)) ≃* ↥S := QuotientGroup.quotientBot
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hKn : (K.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hK e.toMonoidHom e.surjective
  have hcard : Nat.card ↥(K.map e.toMonoidHom) = Nat.card ↥K :=
    (Nat.card_congr (K.equivMapOfInjective e.toMonoidHom hinj).toEquiv).symm
  have hmem : K.map e.toMonoidHom ∈
      {L : Subgroup ↥S | L.Normal ∧ Nat.Coprime 2 (Nat.card L)} := by
    refine ⟨hKn, ?_⟩
    rw [hcard]
    exact hcop
  have hle : K.map e.toMonoidHom ≤ CFSG.pPrimeCore 2 ↥S := le_sSup hmem
  rw [corBN_pPrimeCore_eq_bot S hO, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hle

theorem corBN_center_eq_bot {Y : Type} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hO : ∀ P : Subgroup Y, P.Normal → P ≤ S → Odd (Nat.card P) → P = ⊥)
    (hO2 : ∀ P : Subgroup Y, P.Normal → P ≤ S → IsPGroup 2 P → P = ⊥) :
    Subgroup.center ↥S = ⊥ := by
  have hpc : CFSG.pPrimeCore 2 ↥S = ⊥ := corBN_pPrimeCore_eq_bot S hO
  have hP : ((Subgroup.center ↥S).map S.subtype).Normal := inferInstance
  have hpgS : IsPGroup 2 ↥(Subgroup.center ↥S) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center ↥S) inferInstance inferInstance hpc
  have hpg : IsPGroup 2 ↥((Subgroup.center ↥S).map S.subtype) :=
    hpgS.of_equiv ((Subgroup.center ↥S).equivMapOfInjective S.subtype S.subtype_injective)
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1
    (hO2 _ hP (Subgroup.map_subtype_le _) hpg)

theorem corBN_main {Y : Type} [Group Y] [Finite Y] (T S : Subgroup Y) [hSn : S.Normal]
    (hT : T ≠ ⊥) (hTp : IsPGroup 2 T) (hTS : T ≤ S)
    (hmin : ∀ Q : Subgroup Y, Q.Normal → T ≤ Q → S ≤ Q)
    (hThm : ∃ N : Subgroup ↥S, ∃ _ : N.Normal, IsElemAbelian 2 N ∧
      (ZStarCase (↥S ⧸ N) ∨ IsCoveringOfList (↥S ⧸ N)))
    (hO2 : ∀ P : Subgroup Y, P.Normal → P ≤ S → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → P ≤ S → Odd (Nat.card P) → P = ⊥) :
    ListGroup ↥S := by
  obtain ⟨N, hNn, hN2, hcase⟩ := hThm
  have hpc : CFSG.pCore 2 ↥S = ⊥ := corBN_pCore_eq_bot S hO2
  have hmemN : N ∈ {K : Subgroup ↥S | K.Normal ∧ IsPGroup 2 K} :=
    ⟨hNn, corB_isPGroup_of_isElemAbelian N hN2⟩
  have hNle : N ≤ CFSG.pCore 2 ↥S := le_sSup hmemN
  have hN_bot : N = ⊥ := le_bot_iff.1 (hNle.trans hpc.le)
  subst hN_bot
  rcases hcase with hZ | hcov
  · exfalso
    have hcomm : ∀ a b : ↥S, a * b = b * a := by
      intro a b
      have hO' := corBN_oddCore_quotBot_eq_bot S hO
      have key := corB_comm_of_zStarCase hO' hZ (QuotientGroup.mk a) (QuotientGroup.mk b)
      have hq : ((a * b : ↥S) : ↥S ⧸ (⊥ : Subgroup ↥S)) =
          ((b * a : ↥S) : ↥S ⧸ (⊥ : Subgroup ↥S)) := key
      have hmem := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_bot, inv_mul_eq_one] at hmem
      exact hmem
    have hab : ∀ a : Y, a ∈ S → ∀ b : Y, b ∈ S → a * b = b * a := by
      intro a ha b hb
      have := congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
      simpa using this
    have hP2 : IsPGroup 2 ↥S := corB_isPGroup_of_abelian T S hTp hTS hmin hab
    have hSbot : S = ⊥ := hO2 S hSn le_rfl hP2
    exact hT (le_bot_iff.1 (hTS.trans hSbot.le))
  · obtain ⟨-, Z, hZc, hZn, hlist⟩ := hcov
    have hZbot : Z = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      let e : (↥S ⧸ (⊥ : Subgroup ↥S)) ≃* ↥S := QuotientGroup.quotientBot
      have hcen : e z ∈ Subgroup.center ↥S := by
        rw [Subgroup.mem_center_iff]
        intro s
        have h1 := Subgroup.mem_center_iff.1 (hZc hz) (e.symm s)
        have h2 := congrArg (⇑e) h1
        simpa [map_mul] using h2
      rw [corBN_center_eq_bot S hO hO2, Subgroup.mem_bot] at hcen
      exact e.injective (hcen.trans (map_one e).symm)
    subst hZbot
    have e2 : ((↥S ⧸ (⊥ : Subgroup ↥S)) ⧸ (⊥ : Subgroup (↥S ⧸ (⊥ : Subgroup ↥S))))
        ≃* ↥S :=
      QuotientGroup.quotientBot.trans QuotientGroup.quotientBot
    exact ListGroup.of_mulEquiv e2 hlist

theorem corB_listGroup_of_normal {Y : Type} [Group Y] [Finite Y] {T : Subgroup Y} (hT : T ≠ ⊥)
    (hTp : IsPGroup 2 T) (hThm : ThmAConclusion T)
    (hO2 : ∀ P : Subgroup Y, P.Normal → P ≤ Subgroup.normalClosure (T : Set Y) →
      IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → P ≤ Subgroup.normalClosure (T : Set Y) →
      Odd (Nat.card P) → P = ⊥) :
    ListGroup ↥(Subgroup.normalClosure (T : Set Y)) :=
  corBN_main T (Subgroup.normalClosure (T : Set Y)) hT hTp Subgroup.le_normalClosure
    (fun Q _ hTQ => Subgroup.normalClosure_le_normal (fun _ ht => hTQ ht)) hThm hO2 hO

theorem corB_listGroup_of_normal_sub {Y : Type} [Group Y] [Finite Y] {T H : Subgroup Y}
    [H.Normal] (hTH : T ≤ H) (hT : T ≠ ⊥) (hTp : IsPGroup 2 T) (hThm : ThmAConclusion T)
    (hO2 : ∀ P : Subgroup Y, P ≤ H → (∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set Y)) →
      IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P ≤ H → (∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set Y)) →
      Odd (Nat.card P) → P = ⊥) :
    ListGroup ↥(Subgroup.normalClosure (T : Set Y)) := by
  have hSH : Subgroup.normalClosure (T : Set Y) ≤ H :=
    Subgroup.normalClosure_le_normal (fun _ ht => hTH ht)
  have hnorm : ∀ P : Subgroup Y, P.Normal → ∀ h : Y, h ∈ Subgroup.normalizer (P : Set Y) :=
    fun P hP h => Subgroup.mem_normalizer_fintype fun y hy => hP.conj_mem y hy h
  exact corB_listGroup_of_normal hT hTp hThm
    (fun P hP hPS hP2 => hO2 P (hPS.trans hSH) (fun h _ => hnorm P hP h) hP2)
    (fun P hP hPS hPo => hO P (hPS.trans hSH) (fun h _ => hnorm P hP h) hPo)

end CFSG.RankThree.GF2n.Stroth80
