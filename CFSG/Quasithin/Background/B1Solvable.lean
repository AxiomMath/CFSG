module

public import CFSG.Quasithin.Background.B1Offender
public import CFSG.Quasithin.Background.B1NaturalL2
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem normal_two_subgroups_trivial_of_pCoreOf_eq_bot {X : Subgroup (MulAut V)}
    (h : CFSG.Open.pCoreOf 2 X = ⊥) :
    ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥ := by
  intro Q hQX hQn hQp
  have := CFSG.LieType.BorelTits.le_pCoreOf 2 hQX hQn hQp
  rw [h] at this
  exact le_bot_iff.1 this

namespace B1

theorem sylowTwo_conj {G : Type*} [Group G] [Finite G] {H S₁ S₂ : Subgroup G}
    (h₁ : CFSG.QuasithinUnique.IsSylowTwoOf S₁ H) (h₂ : CFSG.QuasithinUnique.IsSylowTwoOf S₂ H) :
    ∃ h ∈ H, S₂ = S₁.map (MulAut.conj h).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp₁ : IsPGroup 2 (S₁.subgroupOf H) :=
    h₁.2.1.of_injective (Subgroup.subgroupOfEquivOfLe h₁.1).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe h₁.1).injective
  have hp₂ : IsPGroup 2 (S₂.subgroupOf H) :=
    h₂.2.1.of_injective (Subgroup.subgroupOfEquivOfLe h₂.1).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe h₂.1).injective
  let P₁ : Sylow 2 ↥H := hp₁.toSylow h₁.2.2
  let P₂ : Sylow 2 ↥H := hp₂.toSylow h₂.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) P₁ P₂
  refine ⟨g, g.2, ?_⟩
  have h1 : (g • P₁ : Sylow 2 ↥H).toSubgroup = P₂.toSubgroup := by rw [hg]
  have h2 : (g • P₁ : Sylow 2 ↥H).toSubgroup =
      (S₁.subgroupOf H).map (MulAut.conj g).toMonoidHom := rfl
  have e1 : (S₂.subgroupOf H).map H.subtype = S₂ := Subgroup.map_subgroupOf_eq_of_le h₂.1
  have e2 : (S₁.subgroupOf H).map H.subtype = S₁ := Subgroup.map_subgroupOf_eq_of_le h₁.1
  have e3 : S₂.subgroupOf H = (S₁.subgroupOf H).map (MulAut.conj g).toMonoidHom := by
    rw [← h2, h1]
    rfl
  have hcomp : H.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by
    ext x
    simp
  rw [← e1, e3, Subgroup.map_map, hcomp, ← Subgroup.map_map, e2]

end B1

namespace IsTransvectionBlocks

variable {J : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))} {H : Subgroup (MulAut V)}

theorem isSylowTwoOf_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) {t : MulAut V} (htr : t ∈ transvectionsIn H) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Subgroup.zpowers t) H := by
  obtain ⟨htH, ht1, w, htw⟩ := htr
  have hsq : t ^ 2 = 1 := by rw [pow_two]; exact B1.tv_sq hV htw ht1
  have hord : orderOf t = 2 := orderOf_eq_prime hsq ht1
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hord]
  refine ⟨Subgroup.zpowers_le.2 htH, IsPGroup.of_card (n := 1) (by rw [hcard]; simp), ?_⟩
  have h1 : (Subgroup.zpowers t).relIndex H * Nat.card ↥(Subgroup.zpowers t ⊓ H) = Nat.card H :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.2 (Subgroup.zpowers_le.2 htH), hcard, hb.card_eq H hH] at h1
  have h3 : (Subgroup.zpowers t).relIndex H = 3 := by omega
  show ¬ 2 ∣ (Subgroup.zpowers t).relIndex H
  rw [h3]
  decide

theorem exists_transvection (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) :
    ∃ t, t ∈ transvectionsIn H := by
  by_contra hcon
  push Not at hcon
  have h1 : transvectionsIn H = ∅ := Set.eq_empty_iff_forall_notMem.2 hcon
  have h2 := hb.closure_eq H hH
  rw [h1, Subgroup.closure_empty] at h2
  have h3 := hb.card_eq H hH
  rw [← h2, Subgroup.card_bot] at h3
  omega

theorem exists_transvection_of_isSylowTwoOf [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) {S : Subgroup (MulAut V)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S H) :
    ∃ t ∈ transvectionsIn H, S = Subgroup.zpowers t := by
  obtain ⟨t₀, ht₀⟩ := hb.exists_transvection hH
  obtain ⟨h, hhH, hSeq⟩ := B1.sylowTwo_conj (hb.isSylowTwoOf_zpowers hV hH ht₀) hS
  refine ⟨h * t₀ * h⁻¹, ⟨H.mul_mem (H.mul_mem hhH ht₀.1) (H.inv_mem hhH),
    B1.isTransvection_conj ht₀.2 h⟩, ?_⟩
  rw [hSeq, MonoidHom.map_zpowers]
  rfl


theorem offender_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    {𝓗 : Finset (Subgroup (MulAut V))}
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    (A : Subgroup (MulAut V)) :
    IsFFStarOffender X A ↔ ∃ a : Subgroup (MulAut V) → Subgroup (MulAut V),
      (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧
        (∃ H ∈ 𝓗, a H ≠ ⊥) ∧ A = ⨆ H ∈ 𝓗, a H := by
  constructor
  · intro hA
    obtain ⟨a, ha, haeq⟩ := hb.offender_structure hV hsolv hO2 (Nat.card A) A hA le_rfl
    refine ⟨a, fun H hH => ?_, ?_, haeq⟩
    · rcases (ha H hH).2 with h | ⟨t, htr, h⟩
      · exact Or.inl h
      · exact Or.inr (h ▸ hb.isSylowTwoOf_zpowers hV hH htr)
    · by_contra hcon
      push Not at hcon
      apply hA.2.1
      rw [haeq]
      refine le_bot_iff.1 (iSup₂_le fun H hH => ?_)
      rw [hcon H hH]
  · rintro ⟨a, ha, hne, rfl⟩
    have ha' : ∀ H ∈ 𝓗, a H ≤ H ∧
        (a H = ⊥ ∨ ∃ t ∈ transvectionsIn H, a H = Subgroup.zpowers t) := by
      intro H hH
      rcases ha H hH with h | h
      · exact ⟨by rw [h]; exact bot_le, Or.inl h⟩
      · exact ⟨h.1, Or.inr (hb.exists_transvection_of_isSylowTwoOf hV hH h)⟩
    exact hb.offender_of_product hV hsolv hO2 a ha' hne

theorem stable_decomposition [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    {𝓗 : Finset (Subgroup (MulAut V))}
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    {P : Set (Subgroup (MulAut V))} (hP : IsStableFF X P) :
    ∃ I : Finset (Subgroup (MulAut V)), I ⊆ 𝓗 ∧ ffJP P X = ⨆ H ∈ I, H ∧
      (∀ H ∈ I, ∀ S, CFSG.QuasithinUnique.IsSylowTwoOf S H → S ∈ P) ∧
      (∀ A, IsFFStarMin X A → (A ∈ P ↔ A ≤ ffJP P X)) := by
  classical
  obtain ⟨-, hPoff, hPconj, hPle⟩ := hP
  have hHX : ∀ H ∈ 𝓗, H ≤ X := fun H hH =>
    (hb.le_J hH).trans (B1.closure_transvectionsIn_le X)
  have hle_ffJP : ∀ A ∈ P, A ≤ ffJP P X := fun A hA =>
    le_iSup₂_of_le (f := fun (A : Subgroup (MulAut V)) (_ : A ∈ P) => ⨆ (_ : A ≤ X), A) A hA
      (le_iSup (fun _ : A ≤ X => A) (hPoff A hA).1)
  let I : Finset (Subgroup (MulAut V)) :=
    𝓗.filter fun H => ∃ t ∈ transvectionsIn H, Subgroup.zpowers t ∈ P
  have hIsub : I ⊆ 𝓗 := Finset.filter_subset _ _
  have hsyl : ∀ H ∈ I, ∀ S, CFSG.QuasithinUnique.IsSylowTwoOf S H → S ∈ P := by
    intro H hHI S hS
    obtain ⟨hH, t, htr, htP⟩ := Finset.mem_filter.1 hHI
    obtain ⟨h, hhH, hSeq⟩ := B1.sylowTwo_conj (hb.isSylowTwoOf_zpowers hV hH htr) hS
    rw [hSeq]
    exact hPconj _ htP h (hHX H hH hhH)
  have hIJ : ∀ H ∈ I, H ≤ ffJP P X := by
    intro H hHI
    obtain ⟨hH, -⟩ := Finset.mem_filter.1 hHI
    rw [← hb.closure_eq H hH]
    refine (Subgroup.closure_le _).2 fun t ht => ?_
    exact hle_ffJP _ (hsyl H hHI _ (hb.isSylowTwoOf_zpowers hV hH ht)) (Subgroup.mem_zpowers t)
  have hactive : ∀ A ∈ P, ∀ a : Subgroup (MulAut V) → Subgroup (MulAut V),
      (∀ H ∈ 𝓗, a H ≤ H ∧ (a H = ⊥ ∨ ∃ t ∈ transvectionsIn H, a H = Subgroup.zpowers t)) →
      A = ⨆ H ∈ 𝓗, a H → ∀ H ∈ 𝓗, a H ≠ ⊥ → H ∈ I := by
    intro A hA a ha haeq H hH hne
    obtain ⟨t, htr, hat⟩ := (ha H hH).2.resolve_left hne
    refine Finset.mem_filter.2 ⟨hH, t, htr, ?_⟩
    have htX : t ∈ X := hHX H hH htr.1
    have hzoff : IsFFStarOffender X (Subgroup.zpowers t) :=
      B1.isFFStarOffender_zpowers hV hsolv hO2 htX htr.2
    have hzA : Subgroup.zpowers t ≤ A := by
      rw [haeq, ← hat]
      exact le_iSup₂ (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => a K) H hH
    refine hPle A hA _ ⟨hzoff.isA2, (hPoff A hA).isA2, hzA, ?_⟩
    rw [B1.card_mul_card_fixV_of_isFFStarOffender hV hsolv hO2 hzoff,
      B1.card_mul_card_fixV_of_isFFStarOffender hV hsolv hO2 (hPoff A hA)]
  have hJeq : ffJP P X = ⨆ H ∈ I, H := by
    apply le_antisymm
    · unfold ffJP
      refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
      obtain ⟨a, ha, haeq⟩ :=
        hb.offender_structure hV hsolv hO2 (Nat.card A) A (hPoff A hA) le_rfl
      rw [haeq]
      refine iSup₂_le fun H hH => ?_
      by_cases hbot : a H = ⊥
      · rw [hbot]
        exact bot_le
      · exact (ha H hH).1.trans
          (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ I) => K) H
            (hactive A hA a ha haeq H hH hbot) le_rfl)
    · exact iSup₂_le fun H hHI => hIJ H hHI
  refine ⟨I, hIsub, hJeq, hsyl, ?_⟩
  intro A hA
  constructor
  · exact fun hAP => hle_ffJP A hAP
  · intro hAJ
    obtain ⟨t, htX, htr, hAt⟩ := B1.exists_transvection_of_isFFStarMin hV hsolv hO2 hA
    have htJ : t ∈ Subgroup.closure (transvectionsIn X) := Subgroup.subset_closure ⟨htX, htr⟩
    obtain ⟨H₀, hH₀, htH₀⟩ := hb.cover t ⟨htJ, htr⟩
    have htA : t ∈ A := hAt ▸ Subgroup.mem_zpowers t
    have htI : t ∈ ⨆ H ∈ I, H := hJeq ▸ hAJ htA
    have hH₀I : H₀ ∈ I := by
      by_contra hnot
      have hle : (⨆ H ∈ I, H) ≤ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H₀), H' :=
        iSup₂_le fun H hHI =>
          le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut V)) (_ : H' ∈ 𝓗) =>
            ⨆ (_ : H' ≠ H₀), H') H (hIsub hHI)
            (le_iSup (fun _ : H ≠ H₀ => H) (fun h => hnot (h ▸ hHI)))
      have hmem : t ∈ H₀ ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H₀), H' := ⟨htH₀, hle htI⟩
      rw [hb.inf_biSup_ne_eq_bot hH₀, Subgroup.mem_bot] at hmem
      exact htr.1 hmem
    rw [hAt]
    exact hsyl H₀ hH₀I _ (hb.isSylowTwoOf_zpowers hV hH₀ ⟨htH₀, htr⟩)

end IsTransvectionBlocks

theorem B1_8_3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hFF : IsFFModule X) : qOf X = 1 ∧ ∀ A, ¬ IsStrongFFStarOffender X A := by
  refine ⟨?_, fun A hA => ?_⟩
  · have h1 : qOf X ≤ 1 := ((B1_4_5 hV X).out 1 3).1 hFF
    have h2 : (1 : WithTop ℚ) ≤ qOf X := by
      have h3 : ((1 : ℚ) : WithTop ℚ) ≤ qOf X := by
        unfold qOf
        refine le_kq_iff.2 fun A hA2 _ => ?_
        by_contra hlt
        push Not at hlt
        obtain ⟨B, -, hB, hrB⟩ := B1_4_4_lt hV hA2 hlt
        have h4 := (rAV_lt_one_iff hV hB.isA2).1 hrB
        have h5 := B1.card_mul_card_fixV_of_isFFStarOffender hV hsolv hO2 hB
        omega
      simpa using h3
    exact le_antisymm h1 h2
  · have h1 := (rAV_lt_one_iff hV hA.1.isA2).1 hA.2
    have h2 := B1.card_mul_card_fixV_of_isFFStarOffender hV hsolv hO2 hA.1
    omega

theorem B1_8 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hFF : IsFFModule X) :
    ∃ 𝓗 : Finset (Subgroup (MulAut V)),
      (∀ H ∈ 𝓗, H ≤ X) ∧
      ffJ X = ⨆ H ∈ 𝓗, H ∧
      (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a) ∧
      (∀ H ∈ 𝓗, H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H' = ⊥) ∧
      commV (ffJ X) = ⨆ H ∈ 𝓗, commV H ∧
      (∀ H ∈ 𝓗, commV H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commV H' = ⊥) ∧
      (∀ H ∈ 𝓗, ActsAsNaturalL2 H (commV H)) ∧
      (qOf X = 1 ∧ ∀ A, ¬ IsStrongFFStarOffender X A) ∧
      (∀ A : Subgroup (MulAut V), IsFFStarOffender X A ↔
        ∃ a : Subgroup (MulAut V) → Subgroup (MulAut V),
          (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧
            (∃ H ∈ 𝓗, a H ≠ ⊥) ∧ A = ⨆ H ∈ 𝓗, a H) ∧
      (∀ P : Set (Subgroup (MulAut V)), IsStableFF X P →
        ∃ I : Finset (Subgroup (MulAut V)), I ⊆ 𝓗 ∧ ffJP P X = ⨆ H ∈ I, H ∧
          (∀ H ∈ I, ∀ S, CFSG.QuasithinUnique.IsSylowTwoOf S H → S ∈ P) ∧
          (∀ A, IsFFStarMin X A → (A ∈ P ↔ A ≤ ffJP P X))) := by
  have hJX := B1.closure_transvectionsIn_le X
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn X)) :=
    B1.solvable_of_le hJX hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn X))) =
      Subgroup.closure (transvectionsIn X) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hV hsolvJ hOJ hcl
  refine ⟨𝓗, fun H hH => (hb.le_J hH).trans hJX, hb.ffJ_eq hV hsolv hO2, hb.comm,
    fun H hH => hb.inf_biSup_ne_eq_bot hH, ?_, ?_, ?_, B1_8_3 hV hsolv hO2 hFF,
    fun A => hb.offender_iff hV hsolv hO2 A, fun P hP => hb.stable_decomposition hV hsolv hO2 hP⟩
  · rw [hb.ffJ_eq hV hsolv hO2]
    simp only [commV_eq_commSub]
    apply le_antisymm
    · exact B1.commSub_biSup_le 𝓗 (fun H => H) _ fun H hH =>
        le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) =>
          commSub (⊤ : Subgroup V) K) H hH le_rfl
    · exact iSup₂_le fun H hH => commSub_mono le_rfl
        (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) H hH le_rfl)
  · intro H hH
    simp only [commV_eq_commSub]
    exact hb.commSub_inf_biSup_ne_eq_bot hV hH
  · intro H hH
    rw [commV_eq_commSub]
    exact actsAsNaturalL2_of_full hV (hb.card_comm H hH) (hb.le_stabSub hH)
      (hb.inf_centSub hH) (hb.autSub_eq_top H hH)

end CFSG.Quasithin
