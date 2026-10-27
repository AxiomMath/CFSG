module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUBT
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofOut
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofRat
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUWt

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem oddFixedBorelTits_uP (hf : Even f) (hn : n = 4 ∨ n = 5)
    {E : Subgroup (MulAut (uP h n))} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEinn : E ≤ (MulAut.conj : uP h n →* MulAut (uP h n)).range)
    {T : Subgroup (MulAut (uP h n))} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTE : T ≤ Subgroup.centralizer (E : Set (MulAut (uP h n)))) :
    OddFixedBorelTits (uP h n) T := by
  classical
  intro U hU hUN
  have hn3 : 3 ≤ n := by omega
  have hnq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := Sec4.isPrimeFormGram_one_GL
  obtain ⟨hZ2, hZ3⟩ := coprime_card_uZ h hf
  have hcinj := conj_injective_uP h hn3 hnq
  set Ē₀ := E.comap (MulAut.conj : uP h n →* MulAut (uP h n)) with hĒ₀
  have hĒ₀map : Ē₀.map MulAut.conj = E := Subgroup.map_comap_eq_self hEinn
  have hĒ₀9 : Nat.card Ē₀ = 9 := by
    rw [← hE9, ← hĒ₀map, Subgroup.card_map_of_injective hcinj]
  have hĒ₀e : CFSG.Assembly.IsElemAbelian 3 Ē₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcinj ?_)⟩⟩, fun x hx => hcinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  obtain ⟨E₀, hE₀map, hE₀9, hE₀3, hE₀c, -⟩ := exists_lift_E9 (uZ h n) hZ3 hĒ₀e hĒ₀9
  have : Fintype E₀ := Fintype.ofFinite _
  obtain ⟨hC2, hW4, hM0⟩ := weights_uS h hf hn E₀ hE₀9 hE₀3 hE₀c
  have hE₀E : ∀ e ∈ E₀, MulAut.conj (QuotientGroup.mk' (uZ h n) e) ∈ E := fun e he => by
    have : QuotientGroup.mk' (uZ h n) e ∈ Ē₀ := hE₀map ▸ Subgroup.mem_map_of_mem _ he
    exact this
  have hTI := inf_inner_eq_bot_uP h hf hn3 hnq hE₀3 hC2 hE₀E hT hTE
  have hTcyc : IsCyclic T := outTwoCyclic_primeFormP h hn3 hnq T hT hTI
  obtain ⟨⟨t₀, ht₀⟩, hgen⟩ := hTcyc.exists_generator
  have hpowT : ∀ t ∈ T, ∃ i : ℤ, t = t₀ ^ i := by
    intro t ht
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨t, ht⟩)
    have := congrArg Subtype.val hi
    simp only [SubgroupClass.coe_zpow] at this
    exact ⟨i, this.symm⟩
  have hTfix : ∀ y : uP h n, t₀ y = y → ∀ t ∈ T, t y = y := by
    intro y hy t ht
    obtain ⟨i, rfl⟩ := hpowT t ht
    have hstab : t₀ ∈ MulAction.stabilizer (MulAut (uP h n)) y := hy
    exact zpow_mem hstab i
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn3 hnq t₀
  rw [primeFormPsi_apply] at hAφ
  have hAU : (A : GL (Fin n) K) ∈ uU h n := A.2
  have hff : primeFormFieldFactor h hC hn3 hnq t₀ = φ := by
    rw [← hAφ]
    exact primeFormFieldFactor_apply h hC hn3 hnq A φ
  obtain ⟨k₀, hk₀⟩ := hT ⟨t₀, ht₀⟩
  have ht₀k : t₀ ^ 2 ^ k₀ = 1 := congrArg Subtype.val hk₀
  have hφk : φ ^ 2 ^ k₀ = 1 := by rw [← hff, ← map_pow, ht₀k, map_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    have ht₀1 : t₀ = 1 := eq_one_of_fieldFactor_uP h hn3 hnq hT hTI ht₀ (by rw [hff, h1])
    apply hT1
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨i, rfl⟩ := hpowT t ht
    rw [ht₀1, _root_.one_zpow, Subgroup.mem_bot]
  obtain ⟨a, ha⟩ : ∃ a, orderOf φ = 2 ^ (a + 1) := by
    have hd : orderOf φ ∣ 2 ^ k₀ := orderOf_dvd_of_pow_eq_one hφk
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rcases j with _ | a
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hjeq, pow_zero])) hφ1
    · exact ⟨a, hjeq⟩
  have hσφ : ∀ c : K, φ c = c → (uF h n).σ c = c := fun c hc => by
    rw [uF_σ, UnitaryFieldData.bar_apply]
    exact pow_eq_self_of_fixed h ha hc
  set ψ := uPsi (A : GL (Fin n) K) φ with hψ
  have hψs : ∀ (c : K) (v : Fin n → K), ψ (c • v) = φ c • ψ v := uPsi_smul _ φ
  have hψβ : ∀ u v, (uF h n).β (ψ u) (ψ v) = φ ((uF h n).β u v) := uPsi_β h hAU φ
  have hψm : ∀ v, (⇑ψ)^[orderOf φ] v = v := by
    have hpow := conj_field_pow h hC hAU φ (orderOf φ)
    have hAeq : (⟨(A : GL (Fin n) K), hAU⟩ : uU h n) = A := rfl
    rw [hAeq, hAφ, pow_orderOf_eq_one, map_one, mul_one] at hpow
    have ht₀m : t₀ ^ orderOf φ = 1 := eq_one_of_fieldFactor_uP h hn3 hnq hT hTI
      (pow_mem ht₀ _) (by rw [map_pow, hff, pow_orderOf_eq_one])
    rw [ht₀m] at hpow
    have hΨ : primeFormPsi h hC ⟨⟨uIter (A : GL (Fin n) K) φ (orderOf φ),
        uIter_mem h hC hAU φ _⟩, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one, ← hpow]
    obtain ⟨-, c, hcN, hcM⟩ := (primeFormPsi_eq_one_iff h hC hn3 _).mp hΨ
    have hcM' : (uIter (A : GL (Fin n) K) φ (orderOf φ) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hcM
    have hψmv : ∀ v, (⇑ψ)^[orderOf φ] v = (c : K) • v := by
      intro v
      rw [hψ, uPsi_iterate, pow_orderOf_eq_one]
      change ((uIter (A : GL (Fin n) K) φ (orderOf φ) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v = _
      rw [hcM', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      funext i
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    have hcφ : φ c = c := by
      have hn0 : 0 < n := by omega
      set w : Fin n → K := Pi.single ⟨0, hn0⟩ 1 with hw
      have hw0 : w ≠ 0 := by
        intro h0
        have := congrFun h0 ⟨0, hn0⟩
        simp [hw] at this
      have h1 := Function.iterate_succ_apply' (⇑ψ) (orderOf φ) (ψ.symm w)
      rw [Function.iterate_succ_apply, hψmv, hψmv, hψs, AddEquiv.apply_symm_apply] at h1
      have h2 : (φ (c : K) - c) • w = 0 := by rw [sub_smul, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0)
    have hc1 : (c : K) = 1 := by
      refine eq_one_of_fixed_of_norm h ha hcφ ?_
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hcN
      rw [pow_succ, mul_comm]
      exact hcN
    intro v
    rw [hψmv, hc1, one_smul]
  have hψE : ∀ e ∈ E₀, ∀ v, ψ (natRep (uS h n) e v) = natRep (uS h n) e (ψ v) := by
    intro e he v
    have hfix : t₀ (QuotientGroup.mk' (uZ h n) e) = QuotientGroup.mk' (uZ h n) e := by
      have h1 := Subgroup.mem_centralizer_iff.mp (hTE ht₀) _ (hE₀E e he)
      apply hcinj
      rw [← mul_conj_mul_inv t₀ (QuotientGroup.mk' (uZ h n) e), ← h1, mul_inv_cancel_right]
    rw [← hAφ, conjField_apply_mk] at hfix
    have hcube : (⟨(A : GL (Fin n) K) * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
        (e : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹,
        conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h hC φ e.2)⟩ : uS h n) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, conj_pow, ← map_pow, Subgroup.coe_one]
      have he3 : (e : GL (Fin n) K) ^ 3 = 1 := by
        rw [← SubmonoidClass.coe_pow, hE₀3 e he, Subgroup.coe_one]
      rw [he3, map_one, mul_one, mul_inv_cancel]
    have heq := eq_of_mk_eq_of_pow_three h hZ3 hfix hcube (hE₀3 e he)
    have hmat : (A : GL (Fin n) K) * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
        (e : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = (e : GL (Fin n) K) := congrArg Subtype.val heq
    rw [natRep_apply, natRep_apply]
    have h1 := natRep_conj_uPsi (A : GL (Fin n) K) φ (e : GL (Fin n) K) (ψ v)
    rw [hmat, AddEquiv.symm_apply_apply] at h1
    exact h1.symm
  set avg := avgE h E₀ with havg
  have hψavg : ∀ v, ψ (avg v) = avg (ψ v) := by
    intro v
    rw [havg, avgE_apply, avgE_apply, map_sum]
    exact Finset.sum_congr rfl fun e _ => hψE e e.2 v
  have hψavg' : ∀ v, ψ.symm (avg v) = avg (ψ.symm v) := by
    intro v
    apply ψ.injective
    rw [AddEquiv.apply_symm_apply, hψavg, AddEquiv.apply_symm_apply]
  set W := LinearMap.ker avg with hWdef
  have hWψ : ∀ w ∈ W, ψ w ∈ W := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← hψavg, hw, map_zero]
  have hWψ' : ∀ w ∈ W, ψ.symm w ∈ W := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← hψavg', hw, map_zero]
  have hfixavg : ∀ v, ∀ e ∈ E₀, natRep (uS h n) e (avg v) = avg v := fun v e he =>
    avgE_fixed h E₀ v he
  have hdecomp : ∀ v, v - avg v ∈ W := by
    intro v
    rw [LinearMap.mem_ker, map_sub, avgE_of_fixed h E₀ hE₀9 (hfixavg v), sub_self]
  have hfixW : ∀ m, (∀ e ∈ E₀, natRep (uS h n) e m = m) → ∀ w ∈ W, (uF h n).β w m = 0 := by
    intro m hm w hw
    rw [uF_symm, form_fixed_ker_avgE h E₀ hE₀9 hm hw, map_zero]
  have hWnd : ∀ c ∈ W, (∀ w ∈ W, (uF h n).β w c = 0) → c = 0 := by
    intro c hc hcW
    apply (uF h n).nondeg c
    intro v
    apply (uF h n).refl
    have h1 : v = avg v + (v - avg v) := by abel
    rw [h1, (uF h n).add_left, hcW _ (hdecomp v), add_zero]
    exact form_fixed_ker_avgE h E₀ hE₀9 (hfixavg v) hc
  have hiso : ∀ v ∈ W, ψ v = v → (uF h n).β v v = 0 := by
    intro v hv hψv
    have hev : ∀ e ∈ E₀, natRep (uS h n) e v ∈ W ∧ ψ (natRep (uS h n) e v) =
        natRep (uS h n) e v := by
      intro e he
      refine ⟨?_, by rw [hψE e he, hψv]⟩
      rw [LinearMap.mem_ker, havg, avgE_apply]
      rw [LinearMap.mem_ker, havg, avgE_apply] at hv
      rw [show (∑ x : E₀, natRep (uS h n) (x : uS h n) (natRep (uS h n) e v)) =
          natRep (uS h n) e (∑ x : E₀, natRep (uS h n) (x : uS h n) v) from by
        rw [map_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
          hE₀c x x.2 e he], hv, map_zero]
    have hQadd : ∀ x y, ψ x = x → ψ y = y →
        (uF h n).β (x + y) (x + y) = (uF h n).β x x + (uF h n).β y y := by
      intro x y hx hy
      have hxy : (uF h n).β y x = (uF h n).β x y := by
        rw [uF_symm, hσφ _ (by rw [← hψβ, hx, hy])]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [(uF h n).add_left, (uF h n).add_right, (uF h n).add_right, hxy]
      linear_combination (uF h n).β x y * h2
    have hQsum : ∀ s : Finset E₀, (uF h n).β (∑ e ∈ s, natRep (uS h n) (e : uS h n) v)
        (∑ e ∈ s, natRep (uS h n) (e : uS h n) v) = ∑ _e ∈ s, (uF h n).β v v := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.sum_empty, (uF h n).β_zero_left]
      | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx, hQadd _ _ (hev x x.2).2, ih]
        · congr 1
          exact isIsometric_uS h (x : uS h n) v v
        · rw [map_sum]
          exact Finset.sum_congr rfl fun e _ => (hev e e.2).2
    have h1 := hQsum Finset.univ
    rw [← avgE_apply, ← havg, LinearMap.mem_ker.mp hv, (uF h n).β_zero_left, Finset.sum_const,
      Finset.card_univ, Fintype.card_eq_nat_card, hE₀9, ← Nat.cast_smul_eq_nsmul K,
      Nat.cast_ofNat, nine_eq_one, one_smul] at h1
    exact h1.symm
  have hperpW : ∀ w : Fin n → K, w ≠ 0 → (∀ w' ∈ W, (uF h n).β w' w = 0) →
      (uF h n).β w w ≠ 0 := by
    intro w hw0 hwW
    have hx : w - avg w = 0 := by
      refine hWnd _ (hdecomp w) fun w' hw' => ?_
      rw [(uF h n).β_sub_right, hwW w' hw', hfixW _ (hfixavg w) w' hw', sub_zero]
    have hwfix : ∀ e ∈ E₀, natRep (uS h n) e w = w := by
      intro e he
      rw [sub_eq_zero.mp hx]
      exact hfixavg w e he
    exact hM0 w hw0 hwfix
  have hdimW : 3 ≤ finrank K W := by rw [hWdef, hW4]; omega
  obtain ⟨hadd, hscale, hnd, hhyp, hpair, hspan⟩ := rational_form_props
    (e := 2 * f) (by have := h.one_le; omega) h.card (uF h n) (uF_symm h) hσφ ψ hψs hψβ hψm W
    hWψ hWψ' hdimW hWnd hiso
  obtain ⟨Q, hQ2, hQmap⟩ := exists_isPGroup_map_eq (uZ h n) hU
  have hNQ := normalizer_eq_comap_normalizer_map (uZ h n) (uZ_le_center h) hZ2 hQ2
  have hQbot : Q = ⊥ := by
    refine eq_bot_of_tv (uF h n) (uF_symm h) (natRep (uS h n)) (isIsometric_uS h)
      (natRep_injective _) Q hQ2 {v | v ∈ W ∧ ψ v = v} (fun a ha => hiso a ha.1 ha.2) hadd
      hscale hnd hhyp hpair ?_ (fun w hw0 hw => hperpW w hw0 (hspan w hw))
    intro a ha e he hae
    have haa : (uF h n).β a a = 0 := hiso a ha.1 ha.2
    have hee : (uF h n).β e e = 0 := hiso e he.1 he.2
    set g : uS h n := ⟨tvGL h haa, tvGL_mem h haa⟩ * ⟨tvGL h hee, tvGL_mem h hee⟩ with hg
    have hρg : natRep (uS h n) g = tv (uF h n) a * tv (uF h n) e := by
      refine LinearMap.ext fun v => ?_
      rw [natRep_apply, hg, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        tvGL_mulVec, tvGL_mulVec]
      rfl
    refine ⟨g, ?_, hρg⟩
    rw [hNQ, Subgroup.mem_comap, hQmap]
    apply hUN
    apply Subgroup.subset_closure
    refine ⟨hTfix _ ?_, ?_⟩
    ·
      rw [← hAφ, conjField_apply_mk]
      congr 1
      apply Subtype.ext
      change (A : GL (Fin n) K) * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
        (tvGL h haa * tvGL h hee) * (A : GL (Fin n) K)⁻¹ = tvGL h haa * tvGL h hee
      rw [map_mul]
      have h1 := conj_glAut_tvGL h hAU φ haa ha.2
      have h2 := conj_glAut_tvGL h hAU φ hee he.2
      calc (A : GL (Fin n) K) * (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
            (tvGL h haa) * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
            (tvGL h hee)) * (A : GL (Fin n) K)⁻¹ =
          ((A : GL (Fin n) K) * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
            (tvGL h haa) * (A : GL (Fin n) K)⁻¹) *
          ((A : GL (Fin n) K) * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
            (tvGL h hee) * (A : GL (Fin n) K)⁻¹) := by group
        _ = tvGL h haa * tvGL h hee := by rw [h1, h2]
    ·
      have hg3 : g ^ 3 = 1 := by
        apply natRep_injective (uS h n)
        rw [map_pow, hρg, map_one]
        exact tv_mul_tv_pow_three (uF h n) (uF_symm h) haa hee hae
      have hpi3 : (QuotientGroup.mk' (uZ h n) g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
      have hd : orderOf (QuotientGroup.mk' (uZ h n) g) ∣ 3 := orderOf_dvd_of_pow_eq_one hpi3
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1 <;> rw [h1] <;> decide
  rw [← hQmap, hQbot, Subgroup.map_bot]

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
