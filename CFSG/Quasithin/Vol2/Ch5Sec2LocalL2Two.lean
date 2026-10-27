module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Bar

variable {Γ : Type} [Group Γ] {H : Subgroup Γ}

theorem modO2Image_inf_of_pCoreOf_le {T A : Subgroup Γ} (hOT : pCoreOf 2 H ≤ T) :
    modO2Image H T ⊓ modO2Image H A = modO2Image H (T ⊓ A) := by
  refine le_antisymm ?_ (le_inf (Subgroup.map_mono fun x hx => hx.1)
    (Subgroup.map_mono fun x hx => hx.2))
  rintro _ ⟨⟨t, ht, rfl⟩, ⟨a, ha, hat⟩⟩
  have hat' := hat
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hat'
  have h2 : ((a⁻¹ * t : ↥H) : Γ) ∈ pCoreOf 2 H := by
    rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
    exact ⟨_, hat', rfl⟩
  have haT : (a : Γ) ∈ T := by
    have := T.mul_mem (Subgroup.mem_subgroupOf.mp ht) (T.inv_mem (hOT h2))
    simpa using this
  exact ⟨a, ⟨haT, Subgroup.mem_subgroupOf.mp ha⟩, hat⟩

theorem mem_normalizer_sup_pCoreOf {A : Subgroup Γ} (hAH : A ≤ H) {y : ↥H}
    (hy : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈
      Subgroup.normalizer (modO2Image H A : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    (y : Γ) ∈ Subgroup.normalizer ((A ⊔ pCoreOf 2 H : Subgroup Γ) : Set Γ) := by
  have h1 : y ∈ Subgroup.normalizer (((modO2Image H A).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) : Subgroup ↥H) : Set ↥H) :=
    Subgroup.le_normalizer_comap _ hy
  have h2 := Subgroup.le_normalizer_map H.subtype ⟨y, h1, rfl⟩
  rwa [Vol2.Ch11.SecS.map_comap_modO2Image hAH] at h2

end Bar

structure TwoComp {G : Type} [Group G] (T H K₁ K₂ : Subgroup G) : Prop where
  cK₂ : K₂ ∈ cComp H
  conj : ∃ t ∈ T, K₂ = K₁.map (MulAut.conj t).toMonoidHom
  ne : K₂ ≠ K₁
  sup : oTwoUpper H = K₁ ⊔ K₂
  cK : ∀ Q ∈ cComp (oTwoUpper H), Q = K₁ ∨ Q = K₂
  comm : ∀ x ∈ modO2Image H K₁, ∀ y ∈ modO2Image H K₂, x * y = y * x
  inf : modO2Image H K₁ ⊓ modO2Image H K₂ = ⊥

theorem exists_twoComp (h38 : Vol2Native.A38ForSQTKCat) {G : Type} [Group G] [Finite G]
    {T H K₁ : Subgroup G} (hloc : LocalSQTK G) (hHO : pCoreOf 2 H ≠ ⊥)
    (hTH : IsSylowTwoOf T H) (hK₁ : K₁ ∈ cComp H) (hKeq : oTwoUpper H = conjClosure K₁ T)
    (hlt : K₁ < oTwoUpper H) : ∃ K₂, TwoComp T H K₁ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKN : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hK₁H : K₁ ≤ H := le_of_mem_cComp hK₁
  have hK₁K : K₁ ≤ oTwoUpper H := hlt.le
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hHO
  have hTb : IsSylowTwoOf (modO2Image H T) ⊤ := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTH
  rcases ((h38 _ hQ) _ (modO2Image_mem_cComp hK₁)).2 _ hTb with
    ⟨hn, -, -⟩ | ⟨tb, htb, htbN, hconj, hcC, hcomm, hinf, -, -⟩
  ·
    exfalso
    have hn' : (K₁.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hK₁) hn
    have hHK₁ : H ≤ Subgroup.normalizer (K₁ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁H).mp hn'
    apply hlt.ne'
    rw [hKeq]
    exact le_antisymm (conjClosure_le fun s hs y hy =>
      (Subgroup.mem_normalizer_iff.mp (hHK₁ (hTH.1 hs)) y).mp hy) (le_conjClosure K₁ T)
  obtain ⟨t', ht', rfl⟩ := htb
  set K₂ := K₁.map (MulAut.conj (t' : G)).toMonoidHom with hK₂def
  have hK₂ : K₂ ∈ cComp H := map_conj_mem_cComp hK₁ t'.2
  have hK₂b : modO2Image H K₂ = (modO2Image H K₁).map
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t')).toMonoidHom := modO2Image_conj t'
  have hTconj : ∀ s ∈ T, K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj s).toMonoidHom = K₂ := by
    intro s hs
    have hsH := hTH.1 hs
    have hKs := map_conj_mem_cComp hK₁ hsH
    have hb : modO2Image H (K₁.map (MulAut.conj s).toMonoidHom) ∈
        conjSubgroupsBy (modO2Image H T) (modO2Image H K₁) :=
      ⟨_, ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, modO2Image_conj ⟨s, hsH⟩⟩
    rw [hconj] at hb
    rcases hb with hb | hb
    · exact Or.inl (modO2Image_injOn H hKs hK₁ hb)
    · exact Or.inr (modO2Image_injOn H hKs hK₂ (hb.trans hK₂b.symm))
  have hK₂K : K₂ ≤ oTwoUpper H := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hKeq]
    simpa [MulAut.conj_apply] using mem_conjClosure (Subgroup.mem_subgroupOf.mp ht') hy
  have hKeq2 : oTwoUpper H = K₁ ⊔ K₂ := by
    refine le_antisymm ?_ (sup_le hK₁K hK₂K)
    rw [hKeq]
    refine conjClosure_le fun s hs y hy => ?_
    have hm : s * y * s⁻¹ ∈ K₁.map (MulAut.conj s).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rcases hTconj s hs with h1 | h1
    · rw [h1] at hm
      exact Subgroup.mem_sup_left hm
    · rw [h1] at hm
      exact Subgroup.mem_sup_right hm
  have hKsn : IsSubnormal (oTwoUpper H) H :=
    A3.subnormal_of_normal hKH ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN)
  have hCK : ∀ Q ∈ cComp (oTwoUpper H), Q = K₁ ∨ Q = K₂ := by
    intro Q hQ
    have hQH : Q ∈ cComp H := cComp_mem_of_subnormal hKsn hQ
    have hQle : modO2Image H Q ≤ modO2Image H K₁ ⊔ modO2Image H T := by
      have h1 : Q ≤ K₁ ⊔ T := (le_of_mem_cComp hQ).trans (hKeq ▸ A3.conjClosure_le_sup K₁ T)
      rw [← modO2Image_sup hK₁H hTH.1]
      exact Subgroup.map_mono fun x hx => h1 hx
    have hQc := cComp_mem_of_le (modO2Image_mem_cComp hQH) hQle le_top
    rw [hcC] at hQc
    rcases hQc with h1 | h1
    · exact Or.inl (modO2Image_injOn H hQH hK₁ h1)
    · exact Or.inr (modO2Image_injOn H hQH hK₂ (h1.trans hK₂b.symm))
  refine ⟨K₂, hK₂, ⟨t', Subgroup.mem_subgroupOf.mp ht', rfl⟩, fun he => htbN ?_, hKeq2, hCK,
    fun x hx y hy => ?_, ?_⟩
  · apply A38.map_conj_eq_iff.mp
    rw [← hK₂b, he]
  · rw [hK₂b] at hy
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · rw [hK₂b]
    exact hinf

theorem TwoComp.symm {G : Type} [Group G] {T H K₁ K₂ : Subgroup G} (tc : TwoComp T H K₁ K₂)
    (hK₁ : K₁ ∈ cComp H) : TwoComp T H K₂ K₁ := by
  obtain ⟨t, ht, rfl⟩ := tc.conj
  refine ⟨hK₁, ⟨t⁻¹, T.inv_mem ht, ?_⟩, tc.ne.symm, by rw [tc.sup, sup_comm],
    fun Q hQ => (tc.cK Q hQ).symm, fun x hx y hy => (tc.comm y hy x hx).symm,
    by rw [inf_comm]; exact tc.inf⟩
  rw [Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem TwoComp.borelOf_le {G : Type} [Group G] [Finite G] {T H K₁ K₂ : Subgroup G}
    (tc : TwoComp T H K₁ K₂) (hK₁ : K₁ ∈ cComp H) (hTH : IsSylowTwoOf T H) :
    borelOf K₁ T ≤
      oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hOT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hTH
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKN : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hK₁H : K₁ ≤ H := le_of_mem_cComp hK₁
  have hK₁K : K₁ ≤ oTwoUpper H := tc.sup ▸ le_sup_left
  have hK₂H : K₂ ≤ H := (tc.sup ▸ le_sup_right : K₂ ≤ oTwoUpper H).trans hKH
  have hTb : IsSylowTwoOf (modO2Image H T) ⊤ := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTH
  have hKb : modO2Image H (oTwoUpper H) = modO2Image H K₁ ⊔ modO2Image H K₂ := by
    rw [tc.sup]
    exact modO2Image_sup hK₁H hK₂H
  have hKnorm : (modO2Image H (oTwoUpper H)).Normal := by
    have : ((oTwoUpper H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)
  have hS : IsSylowTwoOf (modO2Image H T ⊓ modO2Image H (oTwoUpper H))
      (modO2Image H (oTwoUpper H)) :=
    A4.isSylowTwoOf_inf_normal hTb le_top (Subgroup.normalizer_eq_top_iff.mpr hKnorm).ge
  intro y hy
  have hyH : y ∈ H := hK₁H hy.1
  have hm : π ⟨y, hyH⟩ ∈ modO2Image H K₁ := ⟨⟨y, hyH⟩, hy.1, rfl⟩
  have hmN : π ⟨y, hyH⟩ ∈ Subgroup.normalizer
      ((modO2Image H T ⊓ modO2Image H (oTwoUpper H) ⊓ modO2Image H K₁ :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have hK₁b : modO2Image H K₁ ≤ modO2Image H (oTwoUpper H) :=
      Subgroup.map_mono fun x hx => hK₁K hx
    rw [inf_assoc, inf_eq_right.mpr hK₁b, modO2Image_inf_of_pCoreOf_le hOT]
    exact Vol2.Ch11.SecS.modO2Image_le_normalizer (A := T ⊓ K₁) (B := borelOf K₁ T)
      inf_le_right ⟨⟨y, hyH⟩, hy, rfl⟩
  have h1 := mem_normalizer_of_commute hKb tc.comm tc.inf hS hm hmN
  rw [modO2Image_inf_of_pCoreOf_le hOT] at h1
  have h2 := mem_normalizer_sup_pCoreOf (inf_le_right.trans hKH) h1
  have hyK : y ∈ oTwoUpper H := hK₁K hy.1
  have h3 : ((T ⊓ oTwoUpper H) ⊔ pCoreOf 2 H) ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
    le_antisymm (le_inf ((inf_le_left.trans (sup_le inf_le_left hOT))) inf_le_right)
      (le_inf le_sup_left inf_le_right)
  refine ⟨hyK, ?_⟩
  have h4 := Subgroup.inf_normalizer_le_normalizer_inf ⟨h2, Subgroup.le_normalizer hyK⟩
  rwa [h3] at h4

theorem stmt5_2_L2Two_of (h38 : Vol2Native.A38ForSQTKCat) (hRL : RankOneListedFacts.{0})
    (hU3 : FactU3Cover) (h515 : Stmt5_1_5) (h510 : Stmt5_1_10) : Stmt5_2_L2Two := by
  intro G _ _ T M L H B D K₁ n hyp hN hK₁ hKeq hlt hbend
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hK₁H : K₁ ≤ H := le_of_mem_cComp hK₁
  have hK₁K : K₁ ≤ oTwoUpper H := hlt.le
  obtain ⟨-, -, hBorel, -⟩ := h510 G T M L H B D n hyp hN
  have hMK := hyp.borel_eq hBorel
  obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁ hKeq hlt
  have hK₂ := tc.cK₂
  have hKeq2 := tc.sup
  have hCK := tc.cK
  have hK₁c : K₁ ∈ cComp (oTwoUpper H) := cComp_mem_of_le hK₁ hK₁K hKH
  have hborel := tc.borelOf_le hK₁ hTH
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · have hy' : y ∈ M ⊓ oTwoUpper H := by
      rw [hMK]
      exact hborel hy
    exact hy'.1
  ·
    intro X hXK _ hXodd x hx
    have hxodd : Odd (orderOf x) := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : X)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hXodd this
    refine mem_normalizer_of_odd_of_pair (p := fun Q => Q ∈ cComp (oTwoUpper H)) hK₁c
      (fun P₁ P₂ P₃ h₁ h₂ h₃ => ?_) hxodd fun Q hQ => ?_
    · rcases hCK P₁ h₁ with e₁ | e₁ <;> rcases hCK P₂ h₂ with e₂ | e₂ <;>
        rcases hCK P₃ h₃ with e₃ | e₃ <;>
        first
        | exact Or.inl (e₁.trans e₂.symm)
        | exact Or.inr (Or.inl (e₂.trans e₃.symm))
        | exact Or.inr (Or.inr (e₁.trans e₃.symm))
    · have h1 := cComp_map_mulEquiv (MulAut.conj x) hQ
      rwa [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hXK hx)] at h1
  ·
    intro X hXK hXP
    set Bk := oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)
      with hBk
    have hBkH : Bk ≤ H := inf_le_left.trans hKH
    have hBks : Group.IsSolvable ↥Bk := by
      have hs := ((h515 G T M L H D n h hyp.hStar hN.2.1).2.2 hyp.lieQuot).1
      have hle : Bk ≤ H ⊓ M := by
        rw [← hMK]
        exact le_inf (inf_le_right.trans hKH) inf_le_left
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    have hBkN : Bk ≤ Subgroup.normalizer (K₁ : Set G) := by
      refine inf_le_left.trans ?_
      rw [hKeq2]
      exact sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hK₁ hK₂)
    set P₁ := K₁ ⊔ Bk with hP₁
    have hP₁N : P₁ ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hBkN
    have hcore : perfectCore P₁ = K₁ :=
      le_antisymm (perfectCore_le_of_sup_solvable le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hP₁N) rfl hBks)
        (le_perfectCore_of_perfect le_sup_left hK₁.2.1)
    have hTK₁ : IsSylowTwoOf (T ⊓ K₁) K₁ := A312.isSylowTwoOf_inf_of_subnormal hK₁.2.2.1 hTH
    have hOK₁ : pCoreOf 2 K₁ ≤ T ⊓ K₁ := F7.isSylowTwoOf_pCoreOf_le hTK₁
    have hTK₁Bk : T ⊓ K₁ ≤ Bk :=
      le_inf (inf_le_right.trans hK₁K) ((inf_le_inf_left T hK₁K).trans Subgroup.le_normalizer)
    have hRS := hRL _ (isRankOneListed_of_isBenderAny hU3 hbend)
    have hTt := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK₁
    have hidx : ¬ 2 ∣ (modO2Image K₁ (T ⊓ K₁)).index := by
      have := hTt.2.2
      rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
    obtain ⟨-, hmax, -⟩ := hRS _ hTt.2.1 hidx
    have hP₁r : IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P₁ := by
      refine ⟨lt_of_le_of_ne le_sup_right fun he => not_isSolvable_of_mem_cComp hK₁ ?_,
        sup_le hK₁K inf_le_left, fun Q hBQ hQP => ?_⟩
      · have hK₁B : K₁ ≤ Bk := le_sup_left.trans he.ge
        exact Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hK₁B) (Subgroup.inclusion_injective _)
      · have hQeq : Q = Bk ⊔ (Q ⊓ K₁) :=
          A3.eq_sup_inf_of_le_sup hBkN hBQ.le (hQP.trans (sup_comm K₁ Bk).le)
        have hTQ : T ⊓ K₁ ≤ Q ⊓ K₁ := le_inf (hTK₁Bk.trans hBQ.le) inf_le_right
        by_cases hQ₁ : modO2Image K₁ (Q ⊓ K₁) = ⊤
        · have h1 := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top inf_le_right hQ₁
          rw [sup_eq_left.mpr (hOK₁.trans hTQ)] at h1
          have hK₁Q : K₁ ≤ Q := h1.trans inf_le_left
          rw [hQeq, inf_eq_right.mpr hK₁Q, sup_comm Bk K₁]
        · exfalso
          have h1 := hmax _ (Subgroup.map_mono fun x hx => hTQ hx) hQ₁
          have h2 := h1.trans (normalizer_modO2Image_le (P := K₁ ⊓ Subgroup.normalizer
            ((T ⊓ K₁ : Subgroup G) : Set G)) inf_le_right hOK₁ le_rfl)
          have h3 := le_sup_of_modO2Image_le inf_le_right inf_le_left h2
          rw [sup_eq_left.mpr (hOK₁.trans (le_inf inf_le_right Subgroup.le_normalizer))] at h3
          have h4 : Q ⊓ K₁ ≤ Bk := h3.trans hborel
          rw [hQeq, sup_eq_left.mpr h4] at hBQ
          exact lt_irrefl _ hBQ
    rw [← hcore]
    exact (hXP P₁ hP₁r).trans (normalizer_le_normalizer_perfectCore P₁)

theorem a38ForSQTKCat_holds :
    Vol2Native.A38ForSQTKCat :=
  Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
    Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved

theorem stmt5_2_L2Lie_of_inputs
    (hU3 : FactU3Cover) (hF : FactL2LieParabolic) (hRL : RankOneListedFacts.{0})
    (h515 : Stmt5_1_5) (h510 : Stmt5_1_10) : Stmt5_2_L2Lie :=
  stmt5_2_L2Lie_of hU3 hF (stmt5_2_L2Two_of a38ForSQTKCat_holds hRL hU3 h515 h510) h510

theorem stmt5_2_1_par_of_inputs
    (hU3 : FactU3Cover) (hF : FactL2LieParabolic) (hRL : RankOneListedFacts.{0})
    (h515 : Stmt5_1_5) (h510 : Stmt5_1_10) : Stmt5_2_1_par :=
  stmt5_2_1_par_of hF (stmt5_2_L2Two_of a38ForSQTKCat_holds hRL hU3 h515 h510) h510

theorem rankTwoParabolicFact_of (hF : FactL2LieParabolic) : RankTwoParabolicFact := by
  intro X _ _ k hk htype S P hS hNP hPne hPmax hsolv
  obtain ⟨Pj, -, hiff, hj, -⟩ := hF X k hk htype S hS
  have hcov : P ⋖ ⊤ :=
    ⟨lt_top_iff_ne_top.mpr hPne, fun Q hPQ hQ => hPQ.ne (hPmax Q hPQ.le hQ.ne).symm⟩
  obtain ⟨j, rfl⟩ := (hiff _ hNP).mp hcov
  have hs : IsSimpleGroup (ModO2 (perfectCore (Pj j))) :=
    isSimpleGroup_of_lieModel_PSL2 (Or.inl ⟨by simp [classicalTags], (hj j).2.2⟩)
  have hbot : perfectCore (Pj j) = ⊥ := (isSolvable_iff_perfectCore_eq_bot _).mp hsolv
  rw [hbot] at hs
  have : Subsingleton (ModO2 (⊥ : Subgroup X)) := by
    have : Subsingleton ↥(⊥ : Subgroup X) := inferInstance
    infer_instance
  obtain ⟨a, b, hab⟩ := exists_pair_ne (ModO2 (⊥ : Subgroup X))
  exact hab (Subsingleton.elim a b)

theorem ch5L2ChoiceExists_of_inputs (h510 : Stmt5_1_10) (hF : FactL2LieParabolic) :
    Ch5L2ChoiceExists :=
  ch5L2ChoiceExists_of h510 (rankTwoParabolicFact_of hF)

end CFSG.Quasithin.H13
