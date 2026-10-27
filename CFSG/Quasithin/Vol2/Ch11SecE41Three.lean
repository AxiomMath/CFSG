module

public import CFSG.Quasithin.Vol2.Ch11SecE41R
public import CFSG.Quasithin.Vol2.Ch11SecD556F
public import CFSG.Quasithin.Vol2.Ch11SecE41Two

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup_of {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply A4.mem_normalizer_of_conj_mem
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
  exact fun x hx => hle hx

theorem mem_normalizer_sup_of_comm {A B : Subgroup G} {g : G}
    (hB : g ∈ Subgroup.normalizer (B : Set G)) (hc : ∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ B) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply A4.mem_normalizer_of_conj_mem
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · show g * a * g⁻¹ ∈ A ⊔ B
      have e : g * a * g⁻¹ = (a * g * a⁻¹ * g⁻¹)⁻¹ * a := by group
      rw [e]
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_right (B.inv_mem (hc a ha)))
        (Subgroup.mem_sup_left ha)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
  exact fun x hx => hle hx

theorem inf_sectionCentralizer_le_pCoreOf_sup {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    T ⊓ sectionCentralizer K (pCoreOf 2 K) ≤ pCoreOf 2 (K ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 K with hQ
  set C := T ⊓ sectionCentralizer K Q with hC
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hN2 : IsPGroup 2 ↥(C ⊔ Q) := (hT.to_le inf_le_left).to_sup_of_normal_right'
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) (inf_le_left.trans hTQ)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    SecD.mem_normalizer_inf (Subgroup.le_normalizer ht)
      (SecD.mem_normalizer_sectionCentralizer (hTK ht) (hTQ ht))
  have hKN : K ≤ Subgroup.normalizer ((C ⊔ Q : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup_of_comm (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hg)
      fun c hc => hc.2.2.2 g hg
  have hNn : K ⊔ T ≤ Subgroup.normalizer ((C ⊔ Q : Subgroup G) : Set G) :=
    sup_le hKN fun t ht => mem_normalizer_sup_of (hTC ht) (hTQ ht)
  have hNle : C ⊔ Q ≤ K ⊔ T :=
    sup_le (inf_le_left.trans le_sup_right)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf 2 hNle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hNn) hN2)

theorem pCoreOf_le_solvRad (H : Subgroup G) : pCoreOf 2 H ≤ solvRad H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(pCoreOf 2 H) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).isNilpotent
  exact le_solvRad (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) inferInstance

structure Facts41 : Prop where
  vecTrans : VecTransFacts
  nat : SecA.NatFacts
  r2Gen : SecB.FactR2Gen
  sp4R2Big : FactSp4R2Big
  g2LongRoot : FactG2LongRoot
  g2Adjoint : SecA.FactG2AdjointOrder
  g2Derived : SecA.FactG2DerivedOrder
  parIn : ParInFacts
  l2pSig : SecD.L2pSignalizerFact
  sl2pSig : SL2pSignalizerFact
  case1Comm : FactCase1Comm

structure In41 : Prop where
  s331 : Stmt3_3_1
  s3228 : Ch10.TmpL6_3_2_2_eight
  s1100 : Stmt11_0_0
  s1102 : Stmt11_0_2
  s1103 : Stmt11_0_3
  s1110 : Stmt11_1_0
  s1111 : Stmt11_1_1
  s1112 : Stmt11_1_2
  s1122 : Stmt11_2_2
  s1132 : Stmt11_3_2

variable {T L I : Subgroup G} {n : ℕ}

theorem stmt11_4_1_three (hF : Facts41) (hI : In41) (h : Hyp11 G T L I n) {V₁ X : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    ∀ K : Subgroup G, quasithinIsCComponent K (Subgroup.centralizer (V₁ : Set G)) →
      LOf L V₁ ≤ K → ROf T L V₁ ≤ solvRad (K ⊔ T) ∧ ⁅ROf T L V₁, X⁆ ≤ pCoreOf 2 (K ⊔ T) := by
  intro K hK hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcV := cV_eq_bot hI.s331 hF.g2Derived hI.s1103 hI.s1132 h hV₁
  have hXR := cartan_le_normalizer_rOf hF.nat hF.parIn hI.s1102 h hcV hV₁ hX
  have hRT : ROf T L V₁ ≤ T := SecD.ROf_le_T h V₁
  have hR2 : IsPGroup 2 ↥(ROf T L V₁) := h.fsu.sylow.1.to_le hRT
  have hcommR : ⁅ROf T L V₁, X⁆ ≤ ROf T L V₁ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hXR
  have hKeq := cComp_centralizer_eq_kOf hI.s1110 hI.s1112 h hV₁ hK hle
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact SecD.normalizer_le_normalizer_kOf L V₁ V₁
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTN.trans hNK
  have key : ROf T L V₁ ≤ pCoreOf 2 (K ⊔ T) →
      ROf T L V₁ ≤ solvRad (K ⊔ T) ∧ ⁅ROf T L V₁, X⁆ ≤ pCoreOf 2 (K ⊔ T) := fun hRO =>
    ⟨hRO.trans (pCoreOf_le_solvRad _), hcommR.trans hRO⟩
  have hsc : ∀ c ∈ T, (∀ y ∈ K, c * y * c⁻¹ * y⁻¹ ∈ pCoreOf 2 K) → c ∈ pCoreOf 2 (K ⊔ T) :=
    fun c hc hcK => inf_sectionCentralizer_le_pCoreOf_sup h.fsu.sylow.1 hTK
      ⟨hc, hTK hc, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hTK hc), hcK⟩
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    exact key le_rfl
  obtain ⟨hn2, h1 | h2⟩ := cases_of_lt hF.nat hF.r2Gen hF.sp4R2Big hF.g2LongRoot hF.g2Adjoint
    hF.g2Derived hI.s331 hI.s3228 hI.s1100 hI.s1102 hI.s1103 hI.s1110 hI.s1112 hI.s1122 hI.s1132 h
    hV₁ hK hlt
  · obtain ⟨p, hp, hp5, φ, hφs, hφk⟩ := h1
    subst hn2
    have hL₁4 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥(LOf L V₁) ⧸ CFSG.pCore 2 ↥(LOf L V₁) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F) := by
      obtain ⟨F, hF1, hF2, hF3, hF4⟩ := (hI.s1110 G T L I 2 h).2.1 1 (Or.inl rfl) V₁ hV₁
      exact ⟨F, hF1, hF2, by rw [hF3]; norm_num, hF4⟩
    have hTL₁ : T ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun t ht =>
      SecD.mem_normalizer_lOf (h.normal ht) (hTN ht)
    have hcK : ⁅ROf T L V₁, K⁆ ≤ oTwoTwoPrime K :=
      hF.sl2pSig G K (LOf L V₁) (ROf T L V₁) p hp hp5 ⟨φ, hφs, hφk⟩ hle (perfectCore_perfect _)
        hL₁4 (hRT.trans hTK) (hRT.trans hTL₁) (SecD.commutator_ROf_lOf_le h hV₁)
    have hcK' : ∀ r ∈ ROf T L V₁, ∀ y ∈ K, r * y * r⁻¹ * y⁻¹ ∈ oTwoTwoPrime K :=
      fun r hr y hy => by
        have := hcK (Subgroup.commutator_mem_commutator hr hy)
        rwa [commutatorElement_def] at this
    have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
        (Subgroup.normalizer (V₁ : Set G)) := by
      rw [inf_eq_left.mpr hTN]
      exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
    obtain ⟨K', hLK', hK', hNK', hcase'⟩ := hI.s1111 G T L I 2 1 V₁ V₁ h hV₁
      (Or.inl ⟨rfl, SecA.IsVi.ne_bot h hV₁ le_rfl, le_rfl, hsyl⟩)
    have hKN : quasithinIsCComponent K (Subgroup.normalizer (V₁ : Set G)) :=
      cComp_of_normal (Subgroup.centralizer_le_normalizer (V₁ : Set G))
        (fun t ht => SecA.mem_normalizer_centralizer ht) hK
    have hKK' : K = K' := cComp_eq_of_normal hKN hK' hNK' (SecD.lOf_ne_bot hI.s1110 h hV₁)
      (perfectCore_perfect _) hle hLK'
    have hlists : List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) 2 ∨
        (2 = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K)) := by
      rw [hKK']
      rcases hcase' with heq | hl | hl
      · exact absurd (heq.trans hKK'.symm) (ne_of_lt hlt)
      · exact Or.inl hl
      · exact Or.inr hl
    refine ⟨?_, ?_⟩
    · have hRN : ROf T L V₁ ≤ Subgroup.normalizer (oTwoTwoPrime K : Set G) :=
        (hRT.trans hTK).trans (SecD.normalizer_le_normalizer_oTwoTwoPrime K)
      have hsolv := SecD.isSolvable_sup_of_isPGroup hR2 hRN (SecD.isSolvable_oTwoTwoPrime K)
      have hTR : T ≤ Subgroup.normalizer (ROf T L V₁ : Set G) :=
        le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      have hNn : K ⊔ T ≤
          Subgroup.normalizer ((ROf T L V₁ ⊔ oTwoTwoPrime K : Subgroup G) : Set G) :=
        sup_le (fun g hg => mem_normalizer_sup_of_comm
            (SecD.normalizer_le_normalizer_oTwoTwoPrime K (Subgroup.le_normalizer hg))
            fun r hr => hcK' r hr g hg)
          fun t ht => mem_normalizer_sup_of (hTR ht)
            (SecD.normalizer_le_normalizer_oTwoTwoPrime K (hTK ht))
      have hNle : ROf T L V₁ ⊔ oTwoTwoPrime K ≤ K ⊔ T :=
        sup_le (hRT.trans le_sup_right) ((SecD.oTwoTwoPrime_le K).trans le_sup_left)
      exact le_sup_left.trans (le_solvRad hNle
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hNn) hsolv)
    · rw [Subgroup.commutator_le]
      intro r hr x hx
      have hcR : ⁅r, x⁆ ∈ ROf T L V₁ := hcommR (Subgroup.commutator_mem_commutator hr hx)
      rw [commutatorElement_def] at hcR ⊢
      obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hR2 hcR
      have hxK : x ∈ Subgroup.normalizer (K : Set G) :=
        hNK (SecD.cartan_le_normalizer_V₁ hF.nat hI.s1102 h hV₁ hX hx)
      exact hsc _ (hRT hcR) (hF.case1Comm G K 2 hlists ⟨p, hp, hp5, φ, hφs, hφk⟩ hK.2.1 r x
        (hTK (hRT hr)) hxK (hcK' r hr) ⟨k, hk⟩)
  · have hc := SecD.commutator_ROf_kOf_le_of_case_two hF.l2pSig hI.s1110 h hV₁ (hKeq ▸ h2)
    rw [← hKeq] at hc
    refine key fun r hr => hsc r (hRT hr) fun y hy => ?_
    have := hc (Subgroup.commutator_mem_commutator hr hy)
    rwa [commutatorElement_def] at this

theorem stmt11_4_1_of (hF : Facts41) (hI : In41) : Stmt11_4_1 := by
  intro G _ _ T L I n V₁ X h hV₁ hX
  exact ⟨stmt11_4_1_one hF.vecTrans hI.s331 hF.g2Derived hI.s1102 hI.s1103 hI.s1132 h hV₁,
    stmt11_4_1_two hF.nat hF.r2Gen hF.sp4R2Big hF.g2LongRoot hF.g2Adjoint hF.g2Derived hI.s331
      hI.s3228 hI.s1100 hI.s1102 hI.s1103 hI.s1110 hI.s1112 hI.s1122 hI.s1132 h hV₁,
    stmt11_4_1_three hF hI h hV₁ hX⟩

end CFSG.Quasithin.Vol2.Ch11.SecE
