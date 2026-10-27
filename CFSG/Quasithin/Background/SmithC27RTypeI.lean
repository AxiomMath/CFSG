module

public import CFSG.Quasithin.Background.SmithC27RTypeDefs
public import CFSG.Quasithin.Background.SmithC27RTypeAlt
public import CFSG.Quasithin.Background.SmithC27RTypeU33
public import CFSG.Quasithin.Background.SmithC27B51
public import CFSG.Quasithin.EmptyFaithful.R3c2Types

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem not_isPerfect_of_card_eq_six {X : Type} [Group X] [Finite X] (h6 : Nat.card X = 6) :
    ¬ Group.IsPerfect X := by
  intro hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 1 ∣ Nat.card X by rw [h6]; norm_num)
  have hidx : P.index = 2 := by
    have h1 := P.card_mul_index
    rw [hP, h6] at h1
    omega
  have : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (X ⧸ P) := isCyclic_of_prime_card (p := 2) hidx
  have hle : commutator X ≤ P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcyc.commGroup.mul_comm _ _
  rw [Group.IsPerfect.commutator_eq_top] at hle
  have h2 : Nat.card P = 6 := by rw [top_le_iff.1 hle, Subgroup.card_top, h6]
  rw [hP] at h2
  norm_num at h2

theorem not_isQuasisimple_statedSL_two_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {X : Type} [Group X] (e : X ≃* ↥(Assembly.LowTwoRank.StatedSL 2 F)) :
    ¬ CFSG.IsQuasisimple X := by
  intro hq
  have h6 : Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 F) = 6 := by
    rw [C124.card_statedSL_two_pow (n := 1) (by rw [hF]; norm_num)]
    norm_num
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Group.IsPerfect X := hq.1
  exact not_isPerfect_of_card_eq_six ((Nat.card_congr e.toEquiv).trans h6) this

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

omit [Finite G] in
theorem thompsonJ_le_jPStar (hs : StarHyp R K V) (hV : IsElemAbelian 2 V) :
    autI hV (thompsonJ R) ≤ jPStar hV R K := by
  have hRN := hs.R_le_normalizer_V
  have hJ : autI hV (thompsonJ R) = ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian R A), autI hV A :=
    autI_iSup₂ hV fun A hA => hA.1.trans hRN
  rw [hJ]
  refine iSup₂_le fun A hA => ?_
  by_cases hAV : A ≤ Subgroup.centralizer (V : Set G)
  · rw [autI_eq_bot_of_le_centralizer hV hAV]
    exact bot_le
  · exact le_iSup₂_of_le (autI hV A) (autI_mem_offenders (X := K ⊔ R) hV hRN hA hAV)
      (le_iSup_of_le (autI_mono hV (hA.1.trans le_sup_right)) le_rfl)

theorem residueTypeI_of_case1ii (hV : IsElemAbelian 2 V)
    (hii : B51Case1ii (jPStar hV R K) (autI hV K)) : ResidueTypeI K V := by
  obtain ⟨-, n, F, iF, fF, hF, I, π, hind, hsup, hreal, -, -⟩ := hii
  let e := FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal 0)
  have := Fintype.ofFinite F
  exact Or.inr (Or.inl (Or.inl ⟨n, F, iF, inferInstance, R3c2.one_le_of_natCard_eq_two_pow hF,
    by rw [Fintype.card_eq_nat_card, hF], ⟨e.symm⟩, hV, Or.inr ⟨I, π, hind, hsup, hreal⟩⟩))

omit [Finite G] in
theorem residueTypeI_of_case1iii (hV : IsElemAbelian 2 V) {m : ℕ}
    (hiii : B51Case1iii (jPStar hV R K) (autI hV K) m) : ResidueTypeI K V := by
  obtain ⟨-, hsum⟩ := hiii
  obtain ⟨hm, π, U₁, U₂, -, h1, -⟩ := id hsum
  let e := FFC.equivOfRealizes (FFModel.nat_faithful _) h1
  exact Or.inr (Or.inr ⟨m, hm, ⟨e.symm⟩, hV, Or.inr (Or.inr (Or.inl hsum))⟩)

omit [Finite G] in
theorem residueTypeI_of_case1iv (hV : IsElemAbelian 2 V)
    (hiv : B51Case1iv (jPStar hV R K) (autI hV K)) : ResidueTypeI K V := by
  obtain ⟨-, n, hn, k, hk1, hkn, hds⟩ := hiv
  obtain ⟨I, π, -, -, -, hreal⟩ := id hds
  let e := FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩)
  exact Or.inr (Or.inr ⟨n, hn, ⟨e.symm⟩, hV, Or.inr (Or.inr (Or.inr ⟨k, hk1, hkn, hds⟩))⟩)

section Pair


theorem residueTypeI_of_pair (hI : B5.B51IrrInputs) (hC124 : C124StatementSQTK (G := G))
    (h : Hyp27 H R M K) (hs : StarHyp R K V) (hnchi : ¬ IsChiBlock2 H K)
    (hnexc : ¬ IsExcA7Block K) (hV : IsElemAbelian 2 V)
    (hHyp : B51Hyp (jPStar hV R K) (autI hV K)) (hGL : jPStar hV R K = autI hV K)
    (hU : commV (autI hV K) ∈ IrrPlus (autI hV K) ⊤)
    (hpair : B42ModulePair (autI hV K) (commV (autI hV K))
      (fixV (autI hV K) ⊓ commV (autI hV K))) :
    ResidueTypeI K V := by
  have hq : CFSG.IsQuasisimple ↥(autI hV K) := hs.quasisimple
  have halt : ∀ m, (m = 5 ∨ m = 7) → ↥(alternatingGroup (Fin m)) ≃* ↥(autI hV K) → False :=
    fun m hm e => false_of_autOn_equiv_alt hC124 h hs hnchi hnexc hm e.symm
  rcases hpair with ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ |
    ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ | hG2d | ⟨π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨α, π, hπ⟩ | hHat | hSL4 | hSL5 | hE4 | hE5
  ·
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    have := Fintype.ofFinite F
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have h1 : n = 1 := by omega
      subst h1
      exact not_isQuasisimple_statedSL_two_two (hF.trans (pow_one 2)) e.symm hq
    exact Or.inl ⟨n, F, iF, inferInstance, hn2, by rw [Fintype.card_eq_nat_card, hF],
      ⟨e.symm⟩, hV, π, hπ⟩
  ·
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    have := Fintype.ofFinite F
    exact Or.inr (Or.inl (Or.inl ⟨n, F, iF, inferInstance,
      R3c2.one_le_of_natCard_eq_two_pow hF, by rw [Fintype.card_eq_nat_card, hF], ⟨e.symm⟩,
      hV, Or.inl ⟨π, hπ⟩⟩))
  ·
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    have := Fintype.ofFinite F
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have h1 : n = 1 := by omega
      subst h1
      exact R3c2.not_isQuasisimple_statedSp_two (hF.trans (pow_one 2)) e.symm hq
    exact Or.inr (Or.inl (Or.inr (Or.inl ⟨n, F, iF, inferInstance, hn2,
      by rw [Fintype.card_eq_nat_card, hF], ⟨e.symm⟩, hV, π, hπ⟩)))
  ·
    have : CharP F 2 := FFC.charP_two_of_card_pow hF
    let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ
    have := Fintype.ofFinite F
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have h1 : n = 1 := by omega
      subst h1
      exact R3c2.not_isQuasisimple_quasithinG2_two (hF.trans (pow_one 2)) e.symm hq
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨n, F, iF, inferInstance, hn2,
      by rw [Fintype.card_eq_nat_card, hF], ⟨e.symm⟩, hV, π, hπ⟩))))
  ·
    exact absurd hGL (ne_of_g2NaturalDerived hI IntMod.sq_eq_one hHyp hU hG2d)
  · exact (halt 5 (Or.inl rfl) (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
  ·
    let e := FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨e.symm⟩, hV, π, hπ⟩)))))
  · exact (halt 7 (Or.inr rfl) (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
  · exact (halt 7 (Or.inr rfl) (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ)).elim
  ·
    obtain ⟨Kf, iK, fK, Γ₀, -, -, hhat, -, π, hπ⟩ := id hHat
    have hHatL : IsHat ↥(autI hV K) ↥(alternatingGroup (Fin 6)) :=
      IsHat.of_mulEquiv (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ) hhat
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hHatL, hV, hHat⟩)))))
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL4
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    exact Or.inr (Or.inr ⟨4, Or.inl rfl, ⟨e.symm⟩, hV, Or.inl ⟨π, hπ⟩⟩)
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL5
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    exact Or.inr (Or.inr ⟨5, Or.inr rfl, ⟨e.symm⟩, hV, Or.inl ⟨π, hπ⟩⟩)
  ·
    obtain ⟨π, hπ⟩ := id hE4
    let e := FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ
    exact Or.inr (Or.inr ⟨4, Or.inl rfl, ⟨e.symm⟩, hV, Or.inr (Or.inl hE4)⟩)
  ·
    obtain ⟨π, hπ⟩ := id hE5
    let e := FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ
    exact Or.inr (Or.inr ⟨5, Or.inr rfl, ⟨e.symm⟩, hV, Or.inr (Or.inl hE5)⟩)

end Pair

end CFSG.Quasithin.SmithC27
