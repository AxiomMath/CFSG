module

public import CFSG.Quasithin.EmptyFaithful.E111L2C
public import CFSG.Quasithin.EmptyFaithful.E111L2R
public import CFSG.Quasithin.EmptyFaithful.E22QRes
public import CFSG.Quasithin.EmptyFaithful.S143Aux

public section

namespace CFSG.Quasithin.E2.E22N.E111L

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

variable {G : Type} [Group G] [Finite G]

theorem member_central {X T A S : Subgroup G} (hR : E111Reduced G X T) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hS : IsComp X S) (hAS : ¬ A ≤ Subgroup.centralizer (S : Set G))
    (hV : A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) :
    ∃ K, E1.IsE 1 ⊤ T A K ∧
      ∀ x ∈ S, ∃ y ∈ K, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G) := by
  set V := A ⊓ Subgroup.normalizer (S : Set G)
  obtain ⟨Z, hZA, hZV, hZVA⟩ := exists_compl hA (inf_le_left : V ≤ A)
  have hZ1 : Z ≠ ⊥ := by
    intro hZ
    rw [hZ, bot_sup_eq] at hZVA
    exact hAS (hZVA ▸ hV)
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hZ1 ((Subgroup.eq_bot_iff_forall Z).mpr hc)
  have hZe := isElemAbelian_of_le hA hZA
  obtain ⟨C, hCZ, hCz, hCzZ⟩ := exists_compl hZe (Subgroup.zpowers_le.mpr hzZ)
  have hidx := relIndex_eq_two hA hZA hZV inf_le_left hzZ hz1 hCZ hCz hCzZ hZVA
  have hset : DiagSetting X T A S C :=
    ⟨hR, hAT, hA, hS, hCZ.trans hZA, le_bot_iff.mp ((inf_le_inf_right _ hCZ).trans hZV.le)⟩
  let _ : Fintype ↥C := Fintype.ofFinite _
  exact ⟨_, hset.isE_diagK le_rfl (Or.inr ⟨hV, hidx⟩), fun x hx => by
    obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
    exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩⟩

omit [Finite G] in
theorem card_mul_relIndex' {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  rw [Subgroup.relIndex, ← (H.subgroupOf K).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

omit [Finite G] in
theorem card_sup_of_comm {A Z V₀ : Subgroup G} (hA : IsElemAbelian 2 A) (hZA : Z ≤ A)
    (hVA : V₀ ≤ A) (hZV : Z ⊓ V₀ = ⊥) : Nat.card ↥(Z ⊔ V₀) = Nat.card Z * Nat.card V₀ := by
  have hcomm : ∀ a ∈ V₀, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, hVA ha⟩ ⟨b, hZA hb⟩)
  have h := CFSG.Quasithin.S143.card_sup_mul_card_inf_of_le_normalizer
    (R := Z) (U := V₀) (le_normalizer_of_comm hcomm)
  rw [hZV, Subgroup.card_bot, mul_one] at h
  exact h

theorem member_two {X T A S : Subgroup G} (hR : E111Reduced G X T) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hS : IsComp X S)
    (h2 : (A ⊓ Subgroup.centralizer (S : Set G)).relIndex (A ⊓ Subgroup.normalizer (S : Set G)) =
      2) :
    ∃ K, E1.IsE 1 ⊤ T A K ∧
      ∀ x ∈ S, ∃ y ∈ K, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G) := by
  set V := A ⊓ Subgroup.normalizer (S : Set G) with hVdef
  set V₀ := A ⊓ Subgroup.centralizer (S : Set G) with hV₀def
  have hV₀V : V₀ ≤ V :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hVc : ¬ V ≤ Subgroup.centralizer (S : Set G) := by
    intro h
    have : V₀.relIndex V = 1 := Subgroup.relIndex_eq_one.mpr (le_inf inf_le_left h)
    omega
  obtain ⟨Z, hZA, hZV, hZVA⟩ := exists_compl hA (inf_le_left : V ≤ A)
  have hset : DiagSetting X T A S Z := ⟨hR, hAT, hA, hS, hZA, hZV⟩
  let _ : Fintype ↥Z := Fintype.ofFinite _
  set K := diagK T A S Z hset.diagComm
  have hZE : Z ⊔ V₀ ≤ Subgroup.centralizer (diagE T A S Z hset.diagComm : Set G) ⊓ A := by
    refine le_inf (sup_le
      (fun c hc => hset.inf_centralizer_le ⟨hZA hc, hset.le_centralizer_diag hc⟩)
      fun v hv => hset.inf_centralizer_le ⟨hv.1,
        hset.le_centralizer_diag_of_le (hV₀V hv) hv.2⟩) (sup_le hZA inf_le_left)
  have hidx : (Z ⊔ V₀).relIndex A = 2 := by
    have hA1 : Nat.card A = Nat.card Z * Nat.card V := by
      rw [← card_sup_of_comm hA hZA inf_le_left hZV, hZVA]
    have hA2 : Nat.card ↥(Z ⊔ V₀) = Nat.card Z * Nat.card V₀ :=
      card_sup_of_comm hA hZA (hV₀V.trans inf_le_left)
        (le_bot_iff.mp ((inf_le_inf_left _ hV₀V).trans hZV.le))
    have e1 := card_mul_relIndex' (sup_le hZA (hV₀V.trans inf_le_left))
    have e2 := card_mul_relIndex' hV₀V
    rw [h2] at e2
    rw [hA2, hA1, ← e2] at e1
    have hZp : 0 < Nat.card Z := Nat.card_pos
    have hVp : 0 < Nat.card V₀ := Nat.card_pos
    have e3 : Nat.card Z * Nat.card V₀ * (Z ⊔ V₀).relIndex A =
        Nat.card Z * Nat.card V₀ * 2 := by rw [e1]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hZp hVp) e3
  have hcard : Nat.card ↥(E1.barRad ↥K (A.subgroupOf K)) ≤ 2 ^ 1 := by
    have hc : Subgroup.centralizer (((diagE T A S Z hset.diagComm).subgroupOf K : Subgroup ↥K) :
        Set ↥K) = (Subgroup.centralizer (diagE T A S Z hset.diagComm : Set G)).subgroupOf K := by
      ext x
      rw [mem_centralizer_subgroupOf_iff hset.diagE_le_diagK, Subgroup.mem_subgroupOf]
    unfold E1.barRad
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hset.solvableRadical_diagK, hc,
      Subgroup.relIndex_subgroupOf hset.A_le_diagK, ← Subgroup.inf_relIndex_right]
    have hd := Subgroup.relIndex_dvd_of_le_left A hZE
    rw [hidx] at hd
    exact (Nat.le_of_dvd (by norm_num) hd).trans (by norm_num)
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ K :=
    (E111R.tauOf_le (E111R.pCoreOf_two_eq_bot hset.red) T A).trans
      (le_inf inf_le_left hset.le_diagK)
  refine ⟨K, ⟨le_top, hτ, hset.isSylowIn_diagK, Or.inr
    ⟨hset.eTwo_diagK (Or.inl (hset.diag_eq_commutator hZVA hVc)), hcard⟩⟩, fun x hx => ?_⟩
  obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
  exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩

theorem relIndex_two_or_four {H K : Subgroup G} (hK : IsPGroup 2 K) (h1 : H.relIndex K ≠ 1) :
    H.relIndex K = 2 ∨ 4 ≤ H.relIndex K := by
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  have hd : H.relIndex K ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card H K
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rcases j with _ | _ | j
  · exact absurd (by simpa using hj) h1
  · left; simpa using hj
  · right
    rw [hj, pow_succ, pow_succ]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    nlinarith


theorem e111CoreMultiL2_of
    (hin : ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → KleinMemberInner p)
    (hout : ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → KleinMemberOuter p) :
    E111CoreMultiL2 := by
  intro p hp hp8
  have : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := by have := hp.two_le; omega
  intro G _ _ X T _ hsec _ hR _
  have hQ : ∀ S : Subgroup G, IsComp X S → IsPSL 2 p 1 ↥S := by
    intro S hS
    have hsub : S.IsSubnormal :=
      Subgroup.IsSubnormal.trans hS.le hS.2.1.isSubnormal hR.1.isSubnormal
    have := hS.simple
    have hq : IsSimpleGroup (↥S ⧸ (⊥ : Subgroup ↥S)) :=
      (MulEquiv.isSimpleGroup_congr QuotientGroup.quotientBot).mpr this
    have hP := hsec S ⊥ hsub hq (nonabelian_of_mulEquiv QuotientGroup.quotientBot hS.nonabelian)
    exact isoInv_isPSL_two p _ _ QuotientGroup.quotientBot.symm hP
  intro Ω hΩ
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧ A ≠ ⊥
  · obtain ⟨A, hAΩ, hAT, hA1⟩ := hex
    have hAab := hΩ.isElemAbelian A hAΩ
    obtain ⟨S, hS, hAS⟩ := exists_isComp_not_le hR hA1
    have hTG := le_gOne (T := T) hΩ
    have hKG : ∀ K, E1.IsE 1 ⊤ T A K →
        K ≤ E1.eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) :=
      fun K hK => (E1.le_eGen hAΩ hAT hK).trans le_sup_left
    by_cases hNU : Nat.card ↥(T ⊓ S) = 8 ∧ ∀ t ∈ T ⊓ Subgroup.normalizer (S : Set G),
        ∀ W : Subgroup G, W ≤ T ⊓ S → IsKleinFour ↥W → A1b.conjSub t W = W
    · exact caseNU hp7 hp8 hR hS (hQ S hS) hNU.1 hNU.2 hΩ
    have hTS := isSylowIn_inf hR hS
    obtain ⟨m, hm, ⟨eP⟩⟩ := sub_dihedral hp7 hp8 (hQ S hS) hTS
    obtain ⟨z, hzP, hz2, hzc, -, -⟩ := CFSG.Quasithin.E22L2.dihedral_sylow_data hm eP
    have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
    have hcover : ∀ K, E1.IsE 1 ⊤ T A K →
        (∀ x ∈ S, ∃ y ∈ K, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G)) →
        E1.eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) = ⊤ := by
      intro K hK hd
      refine top_of_comp_le hR hS hTG (le_of_diag hS.simple ?_ hTG fun x hx => ?_)
      · intro h0
        apply hz1
        have : z ∈ T ⊓ S := hzP
        rw [h0] at this
        exact this
      · obtain ⟨y, hy, hc⟩ := hd x hx
        exact ⟨y, hKG K hK hy, hc⟩
    have hmoves : ∀ K, E1.IsE 1 ⊤ T A K →
        (∃ g ∈ K, g ∈ Subgroup.normalizer (S : Set G) ∧ g * z ≠ z * g) →
        E1.eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) = ⊤ := by
      rintro K hK ⟨g, hgK, hgN, hgz⟩
      exact top_of_comp_le hR hS hTG
        (le_of_moves hp7 hp8 hR hS (hQ S hS) hNU hTG hzP hz2 hzc (hKG K hK hgK) hgN hgz)
    by_cases hV : A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)
    · obtain ⟨K, hK, hd⟩ := member_central hR hAT hAab hS hAS hV
      exact hcover K hK hd
    have h1 : (A ⊓ Subgroup.centralizer (S : Set G)).relIndex
        (A ⊓ Subgroup.normalizer (S : Set G)) ≠ 1 := by
      intro h
      apply hV
      intro v hv
      exact (Subgroup.relIndex_eq_one.mp h hv).2
    have hV2 : IsPGroup 2 ↥(A ⊓ Subgroup.normalizer (S : Set G)) :=
      hR.2.2.2.2.2.1.isPGroup.to_le (inf_le_left.trans hAT)
    rcases relIndex_two_or_four hV2 h1 with h2 | h4
    · obtain ⟨K, hK, hd⟩ := member_two hR hAT hAab hS h2
      exact hcover K hK hd
    · by_cases hinner : ∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
          s⁻¹ * a ∈ Subgroup.centralizer (S : Set G)
      · obtain ⟨K, hK, hmv⟩ := hin p hp hp8 G X T A S hR hQ hAT hAab hS h4 hinner z hzP hz2 hzc
        exact hmoves K hK hmv
      · push Not at hinner
        obtain ⟨K, hK, hmv⟩ := hout p hp hp8 G X T A S hR hQ hAT hAab hS h4 hinner z hzP hz2 hzc
        exact hmoves K hK hmv
  · push Not at hex
    have hW : E1.weakClosure T Ω = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => (hex A hA hAT).le)
    rw [hW, Subgroup.normalizer_eq_top, inf_top_eq, sup_top_eq]

end CFSG.Quasithin.E2.E22N.E111L
