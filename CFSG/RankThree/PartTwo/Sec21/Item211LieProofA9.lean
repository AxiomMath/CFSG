module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofStar
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartTwo.Sec21.Item211LieProofA9Four
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Item462ProofCent
import CFSG.RankThree.PartTwo.Sec6.Item65Two
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open Item211Res2Proof
open scoped commutatorElement

namespace Item211LieProof

variable {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}

theorem isSimpleGroup_alternatingGroup_nine : IsSimpleGroup (alternatingGroup (Fin 9)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)

theorem isInnerAut_of_pow_three {X : Type*} [Group X] (e₀ : X ≃* alternatingGroup (Fin 9))
    (τ : MulAut X) (hτ : τ ^ 3 = 1) : τ ∈ (MulAut.conj : X →* MulAut X).range := by
  set σ : Equiv.Perm (Fin 9) ≃* MulAut (alternatingGroup (Fin 9)) := MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num)
      (by norm_num)) with hσ
  set τ' := MulAut.congr e₀ τ with hτ'def
  have hτ' : τ' ^ 3 = 1 := by rw [hτ'def, ← map_pow, hτ, map_one]
  set π := σ.symm τ' with hπdef
  have hπ : π ^ 3 = 1 := by rw [hπdef, ← map_pow, hτ', map_one]
  have hsign : Equiv.Perm.sign π = 1 := by
    have h1 : (Equiv.Perm.sign π) ^ 3 = 1 := by rw [← map_pow, hπ, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 (by decide)
  have hπA : π ∈ alternatingGroup (Fin 9) := Equiv.Perm.mem_alternatingGroup.mpr hsign
  have hτ'i : KFacts.IsInnerAut τ' := by
    refine ⟨⟨π, hπA⟩, ?_⟩
    have h1 : σ π = τ' := σ.apply_symm_apply τ'
    rw [← h1]
    exact (MulAut.conjNormal_val (h := (⟨π, hπA⟩ : alternatingGroup (Fin 9)))).symm
  exact (KFacts.isInnerAut_congr e₀ τ).mp hτ'i

theorem card_barImage_U_le_two_of_plus (h : PairFacts A E U c L)
    (hP : U ∈ fourGroupsPlus E) (e₀ : lBar L ≃* alternatingGroup (Fin 9)) :
    Nat.card (barImage L U) ≤ 2 := by
  set σ : Equiv.Perm (Fin 9) ≃* MulAut (alternatingGroup (Fin 9)) := MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num)
      (by norm_num)) with hσ
  set Φ : MulAut (lBar L) ≃* Equiv.Perm (Fin 9) := (MulAut.congr e₀).trans σ.symm with hΦ
  have hT := ks211S9CentE9 ((barImage L E).map Φ.toMonoidHom) ((barImage L U).map Φ.toMonoidHom)
    (Sec4.Item462Proof.isElemAbelian_map' _ (isElemAbelian_barImage_E h))
    (by rw [Subgroup.card_map_of_injective Φ.injective, card_barImage_E h])
    ((isPGroup_barImage_U h).map _) (by
      rintro _ ⟨a, ha, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      change Φ b * Φ a = Φ a * Φ b
      rw [← map_mul, ← map_mul, barImage_U_comm_E_of_plus hP a ha b hb])
  rwa [Subgroup.card_map_of_injective Φ.injective] at hT

theorem exists_elemAbelian_le_of_alternating (h : PairFacts A E U c L)
    (e₀ : lBar L ≃* alternatingGroup (Fin 9)) :
    ∃ P : Subgroup G, P ≤ L ∧ IsElemAbelian 3 P ∧ Nat.card P * 3 = Nat.card A := by
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := isSimpleGroup_alternatingGroup_nine
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.q e₀
  have hAi : barImage L A ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range := fun τ hτ =>
    isInnerAut_of_pow_three e₀ τ ((isElemAbelian_barImage_A h).2 τ hτ)
  set B := (barImage L A).comap (MulAut.conj : lBar L →* MulAut (lBar L)) with hB
  have hBe : IsElemAbelian 3 B :=
    isElemAbelian_comap_of_injective (conj_injective_of_center_eq_bot hZ)
      (isElemAbelian_barImage_A h)
  have hBc : Nat.card B = Nat.card (barImage L A) := card_comap_conj hZ hAi
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, -, hSe, hSc⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift (G := L)
    (aschbacherSolvableCore 3 L) (KFacts.not_three_dvd_card_aschbacherSolvableCore L) hBe
  refine ⟨S.map L.subtype, Subgroup.map_subtype_le _,
    Sec4.Item462Proof.isElemAbelian_map' _ hSe, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, hSc, hBc, card_barImage_A h]

theorem c_not_mem (h : PairFacts A E U c L) (hZ : Subgroup.center (lBar L) = ⊥) : c ∉ L := by
  intro hcL
  have hcZ : ((⟨c, hcL⟩ : L) : lBar L) ∈ Subgroup.center (lBar L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    induction z using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (h.L_le_centralizer l.2)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcZ
  have h3 : orderOf (⟨⟨c, hcL⟩, hcZ⟩ : aschbacherSolvableCore 3 L) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, h.orderOf_c]
  have h4 := orderOf_dvd_natCard (⟨⟨c, hcL⟩, hcZ⟩ : aschbacherSolvableCore 3 L)
  rw [h3] at h4
  exact KFacts.not_three_dvd_card_aschbacherSolvableCore L h4

theorem mem_normalizer_sup_of {M : Type*} [Group M] [Finite M] {H₁ H₂ : Subgroup M} {g : M}
    (h₁ : ∀ x ∈ H₁, g * x * g⁻¹ ∈ H₁ ⊔ H₂) (h₂ : ∀ x ∈ H₂, g * x * g⁻¹ ∈ H₁ ⊔ H₂) :
    g ∈ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup M) : Set M) := by
  have hle : H₁ ⊔ H₂ ≤ (H₁ ⊔ H₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun x hx => h₁ x hx) (fun x hx => h₂ x hx)
  exact Subgroup.mem_normalizer_fintype fun x hx => hle hx

theorem false_of_rank_four (hG : TheoremFourHyp G) (h : PairFacts A E U c L)
    (hR : U ⊓ Sec4.thetaQuotCentralizer L ≠ ⊥) {P : Subgroup G} (hPL : P ≤ L)
    (hPe : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) (hcP : c ∉ P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθ
  set R := U ⊓ Sec4.thetaQuotCentralizer L with hRdef
  set M := θ ⊔ R with hM
  have : (aschbacherSolvableCore 3 L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic L
  have hNθ : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (θ : Set G) :=
    SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L _
  have hRN : R ≤ Subgroup.normalizer (θ : Set G) := (inf_le_left.trans h.UN).trans hNθ
  obtain ⟨hQe, hQc⟩ := Sec6.isElemAbelian_sup_zpowers_three hPe hcP h.c3 fun β hβ =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.L_le_centralizer (hPL hβ))
  set Q := P ⊔ Subgroup.zpowers c with hQ
  have hLM : ∀ l ∈ L, l ∈ Subgroup.normalizer (M : Set G) := by
    intro l hl
    refine mem_normalizer_sup_of (fun x hx => Subgroup.mem_sup_left ?_) (fun r hr => ?_)
    · exact (Subgroup.mem_normalizer_iff.mp (hNθ (Subgroup.le_normalizer hl)) x).mp hx
    · obtain ⟨-, hrL⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hr.2
      have h1 := hrL l⁻¹ (L.inv_mem hl)
      rw [inv_inv] at h1
      have e : l * r * l⁻¹ = (l * (r * l⁻¹ * r⁻¹)) * r := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hr)
  have hcM : c ∈ Subgroup.normalizer (M : Set G) := by
    refine mem_normalizer_sup_of (fun x hx => Subgroup.mem_sup_left ?_) (fun r hr => ?_)
    · exact (Subgroup.mem_normalizer_iff.mp (hNθ (h.AL h.cA)) x).mp hx
    · have h1 : c * r = r * c := (Subgroup.mem_centralizer_iff.mp h.cU r hr.1).symm
      rw [h1, mul_inv_cancel_right]
      exact Subgroup.mem_sup_right hr
  have hQM : Q ≤ Subgroup.normalizer (M : Set G) :=
    sup_le (fun x hx => hLM x (hPL hx)) (Subgroup.zpowers_le.mpr hcM)
  have hθ3 : ¬ 3 ∣ Nat.card θ := by
    rw [hθ, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore L
  have hR2 : IsPGroup 2 R := h.U2.to_le inf_le_left
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hM3 : ¬ 3 ∣ Nat.card M := by
    intro h3
    have hdvd : Nat.card M ∣ Nat.card R * Nat.card θ := by
      rw [hM, sup_comm]
      exact Dvd.intro _ (Sec6.card_sup_mul_card_inf hRN)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hdvd) with h2 | h2
    · exact hR3 h2
    · exact hθ3 h2
  have hcop : Nat.Coprime 3 (Nat.card M) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3
  have hM2 : 2 ∣ Nat.card M := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    have hk0 : k ≠ 0 := by
      intro hk0
      rw [hk0, pow_zero] at hk
      exact hR (Subgroup.eq_bot_of_card_eq R hk)
    exact (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le le_sup_right)
  have hQ3 : IsPGroup 3 Q := fun g => ⟨1, Subtype.ext (by simpa using hQe.2 _ g.2)⟩
  obtain ⟨S, hQS, hSne⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    3 2 Nat.prime_three Nat.prime_two Q M hQ3 hQM hcop hM2
  set S' := (S : Subgroup M).map M.subtype with hS'
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map M.subtype
  have h4 : 4 ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (S' : Set G)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨Q, hQS, hQe, by rw [hQc, hP27]; norm_num⟩
  have h5 := CFSG.RankThree.Classical.pRank_le_localRank (G := G) (p := 3) (by norm_num)
    (⟨S', hSne, hS'2, rfl⟩ : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (S' : Set G)))
  have h6 := hG.localRank_three
  omega

end Item211LieProof

open Item211LieProof

section Certs


theorem item211LiePlusA9_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) :
    Item211LiePlusA9 := by
  intro G _ _ A E U c L hpair _ hP hcase
  obtain ⟨hA81, ⟨e₀⟩, -⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := isSimpleGroup_alternatingGroup_nine
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.q e₀
  have hR := inf_K_ne_bot_of_card_le_two h (card_barImage_U_le_two_of_plus h hP e₀)
  obtain ⟨P, hPL, hPe, hPc⟩ := exists_elemAbelian_le_of_alternating h e₀
  exact false_of_rank_four hpair.standing.toTheoremFourHyp h hR hPL hPe (by omega)
    fun hcP => c_not_mem h hZ (hPL hcP)

theorem item211LieMinusA9_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) :
    Item211LieMinusA9 := by
  intro G _ _ A E U c L hpair _ hM hcase
  obtain ⟨-, ⟨e₀⟩, -⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := isSimpleGroup_alternatingGroup_nine
  have : IsSimpleGroup (lBar L) := e₀.isSimpleGroup
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.q e₀
  set Inn := (MulAut.conj : lBar L →* MulAut (lBar L)).range with hInn
  set B := E ⊓ Subgroup.centralizer (U : Set G) with hB
  set V := lThreeV E U c with hV
  have hEi : barImage L E ≤ Inn := fun τ hτ =>
    isInnerAut_of_pow_three e₀ τ ((isElemAbelian_barImage_E h).2 τ hτ)
  have hBi : barImage L B ≤ Inn := barImage_B_le_E.trans hEi
  have hUeq := barImage_U_eq_comm_of_minus h hM
  have hUi : barImage L U ≤ Inn := by
    rw [hUeq]
    exact commutator_le_range_conj _ _ hEi
  have hVeq := barImage_V_comm_B h
  have hVi : barImage L V ≤ Inn := by
    rw [← hVeq]
    exact commutator_le_range_conj _ _ hBi
  obtain ⟨R, hR2, hVR, hRU, -, hRτ⟩ :=
    star hpair.mem_S h (by rw [hZ, Subgroup.card_bot]; exact odd_one)
  set W := R ⊓ Inn with hW
  set ψ : alternatingGroup (Fin 9) →* MulAut (lBar L) :=
    (MulAut.conj : lBar L →* MulAut (lBar L)).comp e₀.symm.toMonoidHom with hψ
  have hψi : Function.Injective ψ :=
    (conj_injective_of_center_eq_bot hZ).comp e₀.symm.injective
  have hψr : ψ.range = Inn := by
    ext τ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e₀ z, by simp [hψ]⟩
  have hInnL : Inn ≤ barImage L L := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    exact mem_barImage_iff.mpr ⟨l, Subgroup.le_normalizer l.2, l.2, barAct_of_mem l.2⟩
  have hWi : W ≤ ψ.range := hψr ▸ inf_le_right
  have hEr : barImage L E ≤ ψ.range := hψr ▸ hEi
  have hUr : barImage L U ≤ ψ.range := hψr ▸ hUi
  have hBr : barImage L B ≤ ψ.range := hψr ▸ hBi
  have hBW : (barImage L B).comap ψ ≤
      Subgroup.centralizer ((W.comap ψ : Subgroup (alternatingGroup (Fin 9))) :
        Set (alternatingGroup (Fin 9))) := by
    refine le_trans ?_ (le_centralizer_of_fourGroup_alternating _ _ _
      (isElemAbelian_comap_of_injective hψi (isElemAbelian_barImage_E h))
      (isElemAbelian_comap_of_injective hψi (isElemAbelian_barImage_U h))
      ((card_comap_of_le_range hψi hUr).trans (card_barImage_U_of_minus h hM)) ?_
      (comap_commutator_of_le_range hψi hUr hEr hUeq.symm)
      ((hR2.to_le inf_le_left).comap_of_injective ψ hψi) ?_ ?_)
    · intro b hb
      refine Subgroup.mem_inf.mpr ⟨barImage_B_le_E hb, ?_⟩
      rw [← comap_centralizer_of_le_range hψi hUr, Subgroup.mem_comap,
        Subgroup.mem_centralizer_iff]
      intro u hu
      exact barImage_U_comm_B u hu _ hb
    · rw [← Subgroup.comap_normalizer_eq_of_le_range hUr]
      exact Subgroup.comap_mono (barImage_E_le_normalizer_U h)
    · rw [← comap_centralizer_of_le_range hψi hUr]
      refine Subgroup.comap_mono fun r hr => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (hRU r hr.1 u hu).symm
    · intro g hg hg3
      rw [← comap_centralizer_of_le_range hψi hUr, Subgroup.mem_comap] at hg
      rw [← Subgroup.comap_normalizer_eq_of_le_range hWi, Subgroup.mem_comap]
      have hgL : ψ g ∈ barImage L L := hInnL ⟨_, rfl⟩
      have hgU : ∀ u ∈ barImage L U, ψ g * u = u * ψ g := fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hg u hu).symm
      have hgR := hRτ (ψ g) hgL hgU (by rw [← map_pow, hg3, map_one])
      refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hgR x).mp hx.1
      · obtain ⟨y, hy⟩ := hx.2
        rw [← hy, KFacts.mul_mulAutConj_mul_inv]
        exact ⟨_, rfl⟩
  apply barImage_V_ne_bot h
  rw [← hVeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨v', rfl⟩ := hWi ⟨hVR hv, hVi hv⟩
  obtain ⟨b', rfl⟩ := hBr hb
  have h1 := Subgroup.mem_centralizer_iff.mp (hBW (show b' ∈ (barImage L B).comap ψ from hb)) v'
    (show v' ∈ W.comap ψ from ⟨hVR hv, hVi hv⟩)
  rw [← map_mul, ← map_mul, h1]

end Certs

end CFSG.RankThree.PartTwo.Sec21
