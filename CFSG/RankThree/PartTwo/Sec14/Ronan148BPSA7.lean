module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSTrans
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7Conj
import CFSG.Quasithin.H13.NQCatT3A7

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.A7

open Equiv Subgroup CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts.KP2
open scoped commutatorElement Pointwise

theorem isSolvable_stabilizer {α : Type*} [Finite α] (s : Set α) (hs : Nat.card s ≤ 4)
    (hsc : Nat.card (sᶜ : Set α) ≤ 4) :
    Group.IsSolvable (MulAction.stabilizer (Perm α) s) := by
  set H := MulAction.stabilizer (Perm α) s with hH
  have hHc : H ≤ MulAction.stabilizer (Perm α) sᶜ := by
    rw [stabilizer_compl]
  let φ₁ : ↥H →* Perm s := MulAction.toPermHom ↥H s
  let φ₂ : ↥H →* Perm ↥(sᶜ : Set α) :=
    (MulAction.toPermHom ↥(MulAction.stabilizer (Perm α) sᶜ) ↥(sᶜ : Set α)).comp
      (Subgroup.inclusion hHc)
  have hφ : Function.Injective (φ₁.prod φ₂) := by
    intro g h hgh
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ s
    · have := congrArg (fun p : Perm s × Perm ↥(sᶜ : Set α) => ((p.1 ⟨x, hx⟩ : s) : α)) hgh
      exact this
    · have := congrArg (fun p : Perm s × Perm ↥(sᶜ : Set α) => ((p.2 ⟨x, hx⟩ : ↥(sᶜ : Set α)) : α))
        hgh
      simpa [φ₂, SMul.smul_stabilizer_def, Perm.smul_def] using this
  haveI := Equiv.Perm.isSolvable hs
  haveI := Equiv.Perm.isSolvable hsc
  exact Group.isSolvable_of_isSolvable_injective hφ

theorem pretransitive_or_le_stabilizer {α : Type*} {M : Subgroup (Perm α)} (s : Set α) (b : α)
    (hs : ∀ y ∈ s, ∃ h ∈ M, h b = y) (hsc : ∀ z ∉ s, ∀ y ∉ s, ∃ h ∈ M, h z = y) :
    MulAction.IsPretransitive M α ∨ M ≤ MulAction.stabilizer (Perm α) s := by
  by_cases hmove : ∃ g ∈ M, ∃ x ∈ s, g x ∉ s
  · left
    obtain ⟨g, hg, x, hx, hgx⟩ := hmove
    rw [MulAction.isPretransitive_iff_base b]
    intro y
    by_cases hy : y ∈ s
    · obtain ⟨h, hh, rfl⟩ := hs y hy
      exact ⟨⟨h, hh⟩, rfl⟩
    · obtain ⟨h₀, hh₀, hh₀b⟩ := hs x hx
      obtain ⟨h₁, hh₁, hh₁y⟩ := hsc (g x) hgx y hy
      refine ⟨⟨h₁ * g * h₀, M.mul_mem (M.mul_mem hh₁ hg) hh₀⟩, ?_⟩
      change (h₁ * g * h₀) b = y
      simp only [Perm.mul_apply, hh₀b, hh₁y]
  · right
    push Not at hmove
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmove g hg x hx
    · intro hy
      refine ⟨g⁻¹ y, hmove g⁻¹ (M.inv_mem hg) y hy, ?_⟩
      change g (g⁻¹ y) = y
      simp

theorem isThreeCycle_cOne : cOne.IsThreeCycle := by
  rw [← card_support_eq_three_iff]
  decide +kernel

theorem isThreeCycle_sq : ((vOneF 3 * vTwoF 3) ^ 2).IsThreeCycle := by
  rw [← card_support_eq_three_iff]
  decide +kernel

theorem cOne_reach : ∀ y : Fin 7, y.val < 3 → ∃ i : Fin 3, (cOne ^ (i : ℕ)) 0 = y := by
  decide +kernel

theorem cTwo_reach : ∀ y : Fin 7, 3 ≤ y.val → y.val < 6 → ∃ i : Fin 3, (cTwo ^ (i : ℕ)) 3 = y := by
  decide +kernel

theorem vOne_reach : ∀ m : Fin 4, m ≠ 0 → ∀ z y : Fin 7, 3 ≤ z.val → 3 ≤ y.val →
    ∃ i j : Fin 3, ∃ e : Bool,
      (cTwo ^ (i : ℕ) * (if e then vOneF m else 1) * cTwo ^ (j : ℕ)) z = y := by
  decide +kernel

theorem vTwo_reach : ∀ m : Fin 4, m ≠ 0 → ∀ z y : Fin 7, (z.val < 3 ∨ z.val = 6) →
    (y.val < 3 ∨ y.val = 6) → ∃ i j : Fin 3, ∃ e : Bool,
      (cOne ^ (i : ℕ) * (if e then vTwoF m else 1) * cOne ^ (j : ℕ)) z = y := by
  decide +kernel

theorem six_reach : ∀ y : Fin 7, ∃ m : Fin 4, vOneF m 6 = y ∨ vTwoF m 6 = y := by
  decide +kernel

theorem eNine_conj_vOne : ∀ (i j : Fin 3) (m : Fin 4), ∃ m' : Fin 4,
    eNineF i j * vOneF m * (eNineF i j)⁻¹ = vOneF m' := by
  decide +kernel

theorem eNine_conj_vTwo : ∀ (i j : Fin 3) (m : Fin 4), ∃ m' : Fin 4,
    eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF m' := by
  decide +kernel

theorem vOne_comm : ∀ m : Fin 4, ∃ (m' : Fin 4) (i j : Fin 3),
    vOneF m = vOneF m' * eNineF i j * (vOneF m')⁻¹ * (eNineF i j)⁻¹ := by
  decide +kernel

theorem vTwo_comm : ∀ m : Fin 4, ∃ (m' : Fin 4) (i j : Fin 3),
    vTwoF m = vTwoF m' * eNineF i j * (vTwoF m')⁻¹ * (eNineF i j)⁻¹ := by
  decide +kernel

theorem alt_le_vOne_sup_vTwo : alternatingGroup (Fin 7) ≤ vOne ⊔ vTwo := by
  have hpre : MulAction.IsPretransitive ↥(vOne ⊔ vTwo) (Fin 7) := by
    rw [MulAction.isPretransitive_iff_base (6 : Fin 7)]
    intro y
    obtain ⟨m, hm | hm⟩ := six_reach y
    · exact ⟨⟨vOneF m, mem_sup_left ⟨m, rfl⟩⟩, hm⟩
    · exact ⟨⟨vTwoF m, mem_sup_right ⟨m, rfl⟩⟩, hm⟩
  have hprim : MulAction.IsPreprimitive ↥(vOne ⊔ vTwo) (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim isThreeCycle_sq
    (pow_mem (mul_mem (mem_sup_left (show vOneF 3 ∈ vOne from ⟨3, rfl⟩))
      (mem_sup_right (show vTwoF 3 ∈ vTwo from ⟨3, rfl⟩))) 2)

theorem vOne_eq_commutator : vOne = ⁅vOne, eNine⁆ := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    obtain ⟨m', i, j, h⟩ := vOne_comm m
    rw [h]
    exact Subgroup.commutator_mem_commutator ⟨m', rfl⟩ ⟨i, j, rfl⟩
  · rw [Subgroup.commutator_le]
    rintro _ ⟨m, rfl⟩ _ ⟨i, j, rfl⟩
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (eNineF i j)]
    obtain ⟨k, hk⟩ := vOneF_inv m
    have : eNineF i j * (vOneF m)⁻¹ * (eNineF i j)⁻¹ ∈ vOne := by
      rw [hk]
      obtain ⟨m'', hm''⟩ := eNine_conj_vOne i j k
      exact ⟨m'', hm''⟩
    exact vOne.mul_mem ⟨m, rfl⟩ this

theorem vTwo_eq_commutator : vTwo = ⁅vTwo, eNine⁆ := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    obtain ⟨m', i, j, h⟩ := vTwo_comm m
    rw [h]
    exact Subgroup.commutator_mem_commutator ⟨m', rfl⟩ ⟨i, j, rfl⟩
  · rw [Subgroup.commutator_le]
    rintro _ ⟨m, rfl⟩ _ ⟨i, j, rfl⟩
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (eNineF i j)]
    obtain ⟨k, hk⟩ := vTwoF_inv m
    have : eNineF i j * (vTwoF m)⁻¹ * (eNineF i j)⁻¹ ∈ vTwo := by
      rw [hk]
      obtain ⟨m'', hm''⟩ := eNine_conj_vTwo i j k
      exact ⟨m'', hm''⟩
    exact vTwo.mul_mem ⟨m, rfl⟩ this

abbrev ι : alternatingGroup (Fin 7) →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype

theorem ι_injective : Function.Injective ι := Subgroup.subtype_injective _

theorem range_ι : ι.range = alternatingGroup (Fin 7) := Subgroup.range_subtype _

theorem vOne_le_alt : vOne ≤ alternatingGroup (Fin 7) := vOne_le_centOne.trans inf_le_right

theorem vTwo_le_alt : vTwo ≤ alternatingGroup (Fin 7) := vTwo_le_centTwo.trans inf_le_right

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem isSolvable_of_map_le {V : Subgroup (alternatingGroup (Fin 7))}
    (h : V.map ι ≤ vOne ∨ V.map ι ≤ vTwo) : Group.IsSolvable V := by
  have h4 : Nat.card V ∣ 4 := by
    rw [← card_map_of_injective ι_injective]
    rcases h with h | h
    · rw [← card_vOne]; exact Subgroup.card_dvd_of_le h
    · rw [← card_vTwo]; exact Subgroup.card_dvd_of_le h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card V ∣ 2 ^ 2 from h4)
  have hp : IsPGroup 2 V := IsPGroup.of_card hi
  have := hp.isNilpotent
  infer_instance

theorem exists_conj {P : Subgroup (alternatingGroup (Fin 7))} (hP9 : Nat.card P = 9) :
    ∃ x : alternatingGroup (Fin 7), (P.map (MulAut.conj x).toMonoidHom).map ι = eNine := by
  obtain ⟨g, hg, hgE⟩ := exists_conj_eq_eNine (P := P.map ι)
    (by rw [card_map_of_injective ι_injective, hP9])
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [← hgE, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem threeSolvIn_alt7 : ThreeSolvIn148 (alternatingGroup (Fin 7)) := by
  intro P V hP hP9 hV3 hPV
  obtain ⟨x, hx⟩ := exists_conj hP9
  set c := MulAut.conj x with hc
  set V' := V.map c.toMonoidHom with hV'
  have hN : eNine ≤ Subgroup.normalizer ((V'.map ι : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
    rw [← hx]
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map ι)
    rw [hV', ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hPV
  have h3 : ¬ 3 ∣ Nat.card (V'.map ι) := by
    rw [card_map_of_injective ι_injective, hV', card_map_of_injective c.injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hV3
  have hsol := isSolvable_of_map_le (V := V')
    (le_vOne_or_le_vTwo h3 (hN cOne_mem_eNine) (hN cTwo_mem_eNine))
  have e : ↥V ≃* ↥V' := V.equivMapOfInjective c.toMonoidHom c.injective
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem rankTwo_alt7 : RankTwo148 (alternatingGroup (Fin 7)) := by
  intro E _ hE
  have h := Subgroup.card_subgroup_dvd_card E
  rw [hE, card_alt7] at h
  norm_num at h

theorem mem_signalizers {P : Subgroup (alternatingGroup (Fin 7))} (hP : P.map ι = eNine)
    {V₀ : Subgroup (Perm (Fin 7))} (hV₀ : V₀ ≤ alternatingGroup (Fin 7)) (h4 : Nat.card V₀ = 4)
    (hconj : ∀ e ∈ eNine, ∀ v ∈ V₀, e * v * e⁻¹ ∈ V₀) (hcomm : V₀ = ⁅V₀, eNine⁆) :
    V₀.comap ι ∈ {V : Subgroup (alternatingGroup (Fin 7)) | V ≤ ⊤ ∧
      V ∈ invariantPiSubgroups ⊤ P (piCompl 3) ∧ V = ⁅V, P⁆} := by
  have hmap : (V₀.comap ι).map ι = V₀ := by
    rw [Subgroup.map_comap_eq_self (by rw [range_ι]; exact hV₀)]
  refine ⟨le_top, ⟨le_top, ?_, ?_⟩, ?_⟩
  · intro r hr
    rw [← card_map_of_injective ι_injective, hmap, h4] at hr
    change (r : ℕ) ≠ 3
    intro h3
    rw [h3] at hr
    norm_num at hr
  · intro p hp
    refine PS.mem_normalizer_of_conj_le fun v hv => ?_
    change ι (p * v * p⁻¹) ∈ V₀
    rw [map_mul, map_mul, map_inv]
    exact hconj _ (hP ▸ Subgroup.mem_map_of_mem ι hp) _ hv
  · apply Subgroup.map_injective ι_injective
    rw [Subgroup.map_commutator, hmap, hP]
    exact hcomm

theorem sigGenConcl_of_eNine {P K Q D : Subgroup (alternatingGroup (Fin 7))}
    (hP : P.map ι = eNine) (hh : SigGenHyp P K Q D) : SigGenConcl P K := by
  classical
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hQ3 : ¬ 3 ∣ Nat.card (Q.map ι) := by
    rw [card_map_of_injective ι_injective]
    exact fun h3 => (hh.inv.2.1 ⟨3, Nat.prime_three⟩ h3) rfl
  have hNQ : eNine ≤ Subgroup.normalizer ((Q.map ι : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
    rw [← hP]
    exact (Subgroup.map_mono hh.inv.2.2).trans (Subgroup.le_normalizer_map ι)
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    apply hh.nontriv
    rw [Subgroup.commutator_bot_right]
    exact bot_le
  obtain ⟨⟨q, hqQ⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
  have hq1' : ι q ≠ 1 := fun h => hq1 (Subtype.ext (ι_injective (h.trans (map_one ι).symm)))
  set M : Subgroup (Perm (Fin 7)) := (Subgroup.normalizer (K : Set (alternatingGroup (Fin 7)))).map ι
    with hM
  have hEM : eNine ≤ M := by rw [← hP]; exact Subgroup.map_mono hh.normK
  have hqM : ι q ∈ M := ⟨q, hh.normQ hqQ, rfl⟩
  have h1M : cOne ∈ M := hEM cOne_mem_eNine
  have h2M : cTwo ∈ M := hEM cTwo_mem_eNine
  have key : alternatingGroup (Fin 7) ≤ M ∨ ∃ s : Set (Fin 7), Nat.card s ≤ 4 ∧
      Nat.card (sᶜ : Set (Fin 7)) ≤ 4 ∧ M ≤ MulAction.stabilizer (Perm (Fin 7)) s := by
    have jordan : MulAction.IsPretransitive M (Fin 7) → alternatingGroup (Fin 7) ≤ M := fun h =>
      Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
        (MulAction.IsPreprimitive.of_prime_card
          (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)) isThreeCycle_cOne h1M
    rcases le_vOne_or_le_vTwo hQ3 (hNQ cOne_mem_eNine) (hNQ cTwo_mem_eNine) with hle | hle
    · obtain ⟨m, hm⟩ := hle ⟨q, hqQ, rfl⟩
      have hm0 : m ≠ 0 := by rintro rfl; exact hq1' (hm.trans (by decide +kernel))
      rcases pretransitive_or_le_stabilizer (M := M) {y | y.val < 3} 0
          (fun y hy => by
            obtain ⟨i, hi⟩ := cOne_reach y hy
            exact ⟨_, M.pow_mem h1M _, hi⟩)
          (fun z hz y hy => by
            obtain ⟨i, j, e, hij⟩ := vOne_reach m hm0 z y (by simp at hz; omega)
              (by simp at hy; omega)
            refine ⟨_, ?_, hij⟩
            refine M.mul_mem (M.mul_mem (M.pow_mem h2M _) ?_) (M.pow_mem h2M _)
            split_ifs
            · rw [← hm]; exact hqM
            · exact M.one_mem) with h | h
      · exact Or.inl (jordan h)
      · refine Or.inr ⟨_, ?_, ?_, h⟩
        · rw [Nat.card_eq_fintype_card]; decide
        · rw [Nat.card_eq_fintype_card]; decide
    · obtain ⟨m, hm⟩ := hle ⟨q, hqQ, rfl⟩
      have hm0 : m ≠ 0 := by rintro rfl; exact hq1' (hm.trans (by decide +kernel))
      rcases pretransitive_or_le_stabilizer (M := M) {y | 3 ≤ y.val ∧ y.val < 6} 3
          (fun y hy => by
            obtain ⟨i, hi⟩ := cTwo_reach y hy.1 hy.2
            exact ⟨_, M.pow_mem h2M _, hi⟩)
          (fun z hz y hy => by
            obtain ⟨i, j, e, hij⟩ := vTwo_reach m hm0 z y (by simp at hz; omega)
              (by simp at hy; omega)
            refine ⟨_, ?_, hij⟩
            refine M.mul_mem (M.mul_mem (M.pow_mem h1M _) ?_) (M.pow_mem h1M _)
            split_ifs
            · rw [← hm]; exact hqM
            · exact M.one_mem) with h | h
      · exact Or.inl (jordan h)
      · refine Or.inr ⟨_, ?_, ?_, h⟩
        · rw [Nat.card_eq_fintype_card]; decide
        · rw [Nat.card_eq_fintype_card]; decide
  have hK : K = ⊤ := by
    rcases key with hA | ⟨s, hs, hsc, hMs⟩
    · have hN : Subgroup.normalizer (K : Set (alternatingGroup (Fin 7))) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, hy, hyx⟩ := hA x.2
        rwa [← ι_injective hyx]
      haveI : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
      · exfalso
        have := hh.three
        rw [h, Subgroup.card_bot] at this
        norm_num at this
      · exact h
    · exfalso
      have hsol := isSolvable_stabilizer s hs hsc
      have hKM : K.map ι ≤ MulAction.stabilizer (Perm (Fin 7)) s :=
        (Subgroup.map_mono (Subgroup.le_normalizer)).trans hMs
      have : Group.IsSolvable (K.map ι) :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKM)
      have e : ↥K ≃* ↥(K.map ι) := K.equivMapOfInjective ι ι_injective
      have hKs : Group.IsSolvable K :=
        Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      have hK1 : K ≠ ⊥ := by
        rintro rfl
        have := hh.three
        rw [Subgroup.card_bot] at this
        norm_num at this
      haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
      haveI := hh.perf
      exact Group.IsPerfect.not_isSolvable K hKs
  subst hK
  have h1 := mem_signalizers hP vOne_le_alt card_vOne
    (by
      rintro _ ⟨i, j, rfl⟩ _ ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := eNine_conj_vOne i j m
      exact ⟨m', hm'⟩) vOne_eq_commutator
  have h2 := mem_signalizers hP vTwo_le_alt card_vTwo
    (by
      rintro _ ⟨i, j, rfl⟩ _ ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := eNine_conj_vTwo i j m
      exact ⟨m', hm'⟩) vTwo_eq_commutator
  intro x _
  have hx : ι x ∈ vOne ⊔ vTwo := alt_le_vOne_sup_vTwo x.2
  have hsup : (vOne.comap ι ⊔ vTwo.comap ι).map ι = vOne ⊔ vTwo := by
    rw [Subgroup.map_sup, Subgroup.map_comap_eq_self (by rw [range_ι]; exact vOne_le_alt),
      Subgroup.map_comap_eq_self (by rw [range_ι]; exact vTwo_le_alt)]
  rw [← hsup] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← ι_injective hyx]
  exact (sup_le (le_sSup h1) (le_sSup h2)) hy

theorem sigGenIn_alt7 : SigGenIn148 (alternatingGroup (Fin 7)) := by
  intro P K Q D _ hP9 hh
  obtain ⟨x, hx⟩ := exists_conj hP9
  set f : alternatingGroup (Fin 7) →* alternatingGroup (Fin 7) :=
    (MulAut.conj x).symm.toMonoidHom with hf
  have hfi : Function.Injective f := (MulAut.conj x).symm.injective
  have hfr : ∀ H : Subgroup (alternatingGroup (Fin 7)), H ≤ f.range := fun H y _ =>
    ⟨MulAut.conj x y, by simp [hf]; group⟩
  have hcomap : ∀ H : Subgroup (alternatingGroup (Fin 7)),
      H.comap f = H.map (MulAut.conj x).toMonoidHom := fun H => by
    rw [hf, Subgroup.comap_equiv_eq_map_symm', MulEquiv.symm_symm]
  refine SigGenConcl.of_comap f hfi (hfr P) (hfr K) ?_
  have hh' := hh.comap f hfi (hfr P) (hfr K) (hfr Q)
  exact sigGenConcl_of_eNine (by rw [hcomap]; exact hx) hh'

theorem inspIn148_alt7 : InspIn148 (alternatingGroup (Fin 7)) := by
  refine ⟨alternatingGroup.center_eq_bot (by simp), fun α hα => ?_, threeSolvIn_alt7,
    rankTwo_alt7, sigGenIn_alt7⟩
  have hodd : Odd (orderOf α) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨x, rfl⟩ := CFSG.Quasithin.H13.NQCat.T3.oddInner_alt7 α hodd
  exact ⟨x, rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.A7
