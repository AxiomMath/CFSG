module

public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.NodeAux
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem corB_isPGroup_of_isElemAbelian {G : Type} [Group G] (E : Subgroup G)
    (hE : IsElemAbelian 2 E) : IsPGroup 2 E := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hE.2 (x : G) x.2

theorem corB_fusionOddCore_eq (K : Type) [Group K] :
    fusionOddCore K = CFSG.pPrimeCore 2 K := by
  unfold fusionOddCore CFSG.pPrimeCore
  congr 1
  ext N
  exact and_congr Iff.rfl Nat.coprime_two_left.symm

theorem corB_pPrimeCore_top_eq_bot {Y : Type} [Group Y]
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) :
    CFSG.pPrimeCore 2 Y = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  exact hO K hK (Nat.coprime_two_left.1 hcop)

theorem corB_pPrimeCore_sub_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) (S : Subgroup Y) [S.Normal] :
    CFSG.pPrimeCore 2 ↥S = ⊥ := by
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 ↥S)) := CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card ↥((CFSG.pPrimeCore 2 ↥S).map S.subtype) =
      Nat.card ↥(CFSG.pPrimeCore 2 ↥S) :=
    (Nat.card_congr ((CFSG.pPrimeCore 2 ↥S).equivMapOfInjective S.subtype
      S.subtype_injective).toEquiv).symm
  have hP : (CFSG.pPrimeCore 2 ↥S).map S.subtype = ⊥ :=
    hO ((CFSG.pPrimeCore 2 ↥S).map S.subtype) inferInstance (by
      rw [hcard]
      exact Nat.coprime_two_left.1 hcop)
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 hP

theorem corB_pCore_sub_eq_bot {Y : Type} [Group Y]
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥) (S : Subgroup Y) [S.Normal] :
    CFSG.pCore 2 ↥S = ⊥ := by
  have hpg : IsPGroup 2 ↥((CFSG.pCore 2 ↥S).map S.subtype) :=
    IsPGroup.map (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥S)) S.subtype
  have hP : (CFSG.pCore 2 ↥S).map S.subtype = ⊥ :=
    hO2 ((CFSG.pCore 2 ↥S).map S.subtype) inferInstance hpg
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 hP

theorem corB_oddCore_quotBot_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) (S : Subgroup Y) [S.Normal] :
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
  rw [corB_pPrimeCore_sub_eq_bot hO S, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hle

theorem corB_comm_of_zStarCase {H : Type} [Group H] (hO : fusionOddCore H = ⊥)
    (hZ : ZStarCase H) (a b : H) : a * b = b * a := by
  have hZ' : fusionZStar H = ⊤ := hZ
  have ha : QuotientGroup.mk' (fusionOddCore H) a ∈ Subgroup.center (H ⧸ fusionOddCore H) := by
    have h : a ∈ fusionZStar H := hZ' ▸ Subgroup.mem_top a
    exact h
  have hcomm := Subgroup.mem_center_iff.1 ha (QuotientGroup.mk' (fusionOddCore H) b)
  have hq : ((b * a : H) : H ⧸ fusionOddCore H) = ((a * b : H) : H ⧸ fusionOddCore H) := hcomm
  have hmem := QuotientGroup.eq.1 hq
  rw [hO, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

theorem corB_center_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥)
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥) (S : Subgroup Y) [S.Normal] :
    Subgroup.center ↥S = ⊥ := by
  have hpc : CFSG.pPrimeCore 2 Y = ⊥ := corB_pPrimeCore_top_eq_bot hO
  have hP : ((Subgroup.center ↥S).map S.subtype).Normal := inferInstance
  have hnilP : Group.IsNilpotent ↥((Subgroup.center ↥S).map S.subtype) :=
    Group.nilpotent_of_mulEquiv
      ((Subgroup.center ↥S).equivMapOfInjective S.subtype S.subtype_injective)
  have hpg : IsPGroup 2 ↥((Subgroup.center ↥S).map S.subtype) :=
    CFSG.isPGroup_of_nilpotent_normal ((Subgroup.center ↥S).map S.subtype) hP hnilP hpc
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 (hO2 _ hP hpg)

theorem corB_isPGroup_of_abelian {Y : Type} [Group Y] (T S : Subgroup Y) [hSn : S.Normal]
    (hTp : IsPGroup 2 T) (hTS : T ≤ S)
    (hmin : ∀ Q : Subgroup Y, Q.Normal → T ≤ Q → S ≤ Q)
    (hab : ∀ a : Y, a ∈ S → ∀ b : Y, b ∈ S → a * b = b * a) :
    IsPGroup 2 ↥S := by
  let Q : Subgroup Y :=
    { carrier := {x | x ∈ S ∧ ∃ n : ℕ, x ^ 2 ^ n = 1}
      mul_mem' := by
        rintro a b ⟨ha, m, hm⟩ ⟨hb, n, hn⟩
        refine ⟨S.mul_mem ha hb, m + n, ?_⟩
        have hc : Commute a b := hab a ha b hb
        have h1 : a ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm, one_pow]
        have h2 : b ^ 2 ^ (m + n) = 1 := by rw [pow_add, mul_comm, pow_mul, hn, one_pow]
        rw [hc.mul_pow, h1, h2, one_mul]
      one_mem' := by
        show (1 : Y) ∈ S ∧ ∃ n : ℕ, (1 : Y) ^ 2 ^ n = 1
        exact ⟨S.one_mem, 0, by simp⟩
      inv_mem' := by
        intro a ha
        obtain ⟨haS, n, hn⟩ := ha
        exact ⟨S.inv_mem haS, n, by rw [inv_pow, hn, inv_one]⟩ }
  have hmemQ : ∀ x : Y, x ∈ Q ↔ x ∈ S ∧ ∃ n : ℕ, x ^ 2 ^ n = 1 := fun x => Iff.rfl
  have hQn : Q.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxS, n, hn⟩ := (hmemQ x).1 hx
    refine (hmemQ (g * x * g⁻¹)).2 ⟨hSn.conj_mem x hxS g, n, ?_⟩
    rw [conj_pow, hn, mul_one, mul_inv_cancel]
  have hTQ : T ≤ Q := by
    intro t ht
    obtain ⟨k, hk⟩ := hTp ⟨t, ht⟩
    refine (hmemQ t).2 ⟨hTS ht, k, ?_⟩
    simpa using congrArg Subtype.val hk
  have hSQ : S ≤ Q := hmin Q hQn hTQ
  intro x
  obtain ⟨_, k, hk⟩ := (hmemQ (x : Y)).1 (hSQ x.2)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem corB_main {Y : Type} [Group Y] [Finite Y] (T S : Subgroup Y) [hSn : S.Normal]
    (hT : T ≠ ⊥) (hTp : IsPGroup 2 T) (hTS : T ≤ S)
    (hmin : ∀ Q : Subgroup Y, Q.Normal → T ≤ Q → S ≤ Q)
    (hThm : ∃ N : Subgroup ↥S, ∃ _ : N.Normal, IsElemAbelian 2 N ∧
      (ZStarCase (↥S ⧸ N) ∨ IsCoveringOfList (↥S ⧸ N)))
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) :
    ListGroup ↥S := by
  obtain ⟨N, hNn, hN2, hcase⟩ := hThm
  have hpc : CFSG.pCore 2 ↥S = ⊥ := corB_pCore_sub_eq_bot hO2 S
  have hmemN : N ∈ {K : Subgroup ↥S | K.Normal ∧ IsPGroup 2 K} :=
    ⟨hNn, corB_isPGroup_of_isElemAbelian N hN2⟩
  have hNle : N ≤ CFSG.pCore 2 ↥S := le_sSup hmemN
  have hN_bot : N = ⊥ := le_bot_iff.1 (hNle.trans hpc.le)
  subst hN_bot
  rcases hcase with hZ | hcov
  · exfalso
    have hcomm : ∀ a b : ↥S, a * b = b * a := by
      intro a b
      have hO' := corB_oddCore_quotBot_eq_bot hO S
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
    have hSbot : S = ⊥ := hO2 S hSn hP2
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
      rw [corB_center_eq_bot hO hO2 S, Subgroup.mem_bot] at hcen
      exact e.injective (hcen.trans (map_one e).symm)
    subst hZbot
    have e2 : ((↥S ⧸ (⊥ : Subgroup ↥S)) ⧸ (⊥ : Subgroup (↥S ⧸ (⊥ : Subgroup ↥S))))
        ≃* ↥S :=
      QuotientGroup.quotientBot.trans QuotientGroup.quotientBot
    exact ListGroup.of_mulEquiv e2 hlist

theorem corB_listGroup {Y : Type} [Group Y] [Finite Y] {T : Subgroup Y} (hT : T ≠ ⊥)
    (hTp : IsPGroup 2 T) (hThm : ThmAConclusion T)
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) :
    ListGroup ↥(Subgroup.normalClosure (T : Set Y)) :=
  corB_main T (Subgroup.normalClosure (T : Set Y)) hT hTp Subgroup.le_normalClosure
    (fun Q _ hTQ => Subgroup.normalClosure_le_normal (fun _ ht => hTQ ht)) hThm hO2 hO

end CFSG.RankThree.GF2n.Stroth80
