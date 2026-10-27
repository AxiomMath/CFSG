module

public import CFSG.Quasithin.AppendixH.H14.TwoCentralElements
public import CFSG.Quasithin.AppendixH.H14.InvolutionArrays
public import CFSG.CGT.M24R.WrapM24Inv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Monster.Code CFSG.ASVolI.ChH CFSG.Sporadic.Schreier CFSG.CGT.M24R CFSG.Blueprint
  CFSG.Quasithin.H.Mathieu

@[expose] def involution2A : Equiv.Perm (Fin 24) := bridgeQ⁻¹ * m24Rep2 * bridgeQ

@[expose] def involution2B : Equiv.Perm (Fin 24) := bridgeQ⁻¹ * m24Rep1 * bridgeQ

theorem hasArr_involution2A : HasArr involution2A octadArr := by
  unfold HasArr involution2A
  decide +kernel

theorem hasArr_involution2B : HasArr involution2B fptFreeArr := by
  unfold HasArr involution2B
  decide +kernel

theorem involution2A_fixed (i : Fin 24) : involution2A i = i ↔ i ∈ octadOf2AInvolution :=
  (hasArr_fix_iff hasArr_involution2A i).trans (fixed_iff_octad i)

theorem involution2B_fixed (i : Fin 24) : involution2B i ≠ i :=
  fun h => not_fixed_fptFree i ((hasArr_fix_iff hasArr_involution2B i).1 h)

theorem factorization_two_card_AutPerm :
    (Nat.card AutPerm).factorization 2 = 10 := by
  rw [card_AutPerm]
  have h : (244823040 : ℕ) = 2 ^ 10 * 239085 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two]
  have h2 : (239085 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h2]

theorem isOctad_map_of_mem_AutPerm {g : Equiv.Perm (Fin 24)} (hg : g ∈ AutPerm)
    {O : Finset (Fin 24)} (hO : IsOctad O) : IsOctad (O.map g.toEmbedding) := by
  refine ⟨by rw [Finset.card_map]; exact hO.1, ?_⟩
  rw [← permAct_eY g O, mem_golayC_iff']
  have h : Multiplicative.toAdd (G6.permAct 24 g (eY O)) =
      permWord g (Multiplicative.toAdd (eY O)) := by
    funext i
    rw [G6.permAct_apply]
    rfl
  rw [h]
  exact permWord_mem_of_mem_AutPerm hg ((mem_golayC_iff' (eY O)).1 hO.2)

theorem centralizerIn_map_conj {Y : Type*} [Group Y] (H : Subgroup Y) (c u : Y) :
    centralizerIn (H.map (MulAut.conj c).toMonoidHom) (c * u * c⁻¹) =
      (centralizerIn H u).map (MulAut.conj c).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, mem_centralizerIn, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hxu⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    calc y * u = c⁻¹ * (c * y * c⁻¹ * (c * u * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * u * c⁻¹) * (c * y * c⁻¹)) * c := by rw [hxu]
      _ = u * y := by group
  · rintro ⟨y, ⟨hy, hyu⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
      _ = c * (u * y) * c⁻¹ := by rw [hyu]
      _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group

theorem orderOf_involution2A : orderOf involution2A = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    ext i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hasArr_involution2A (involution2A i), hasArr_involution2A i]
    exact arr_involutive_octad (i : ℕ) i.isLt
  · intro h
    have hne : (involution2A ⟨0, by norm_num⟩ : ℕ) ≠ 0 := by
      rw [hasArr_involution2A]
      decide +kernel
    exact hne (by rw [h]; rfl)

theorem orderOf_involution2B : orderOf involution2B = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    ext i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hasArr_involution2B (involution2B i), hasArr_involution2B i]
    exact arr_involutive_fptFree (i : ℕ) i.isLt
  · intro h
    have hne : (involution2B ⟨0, by norm_num⟩ : ℕ) ≠ 0 := by
      rw [hasArr_involution2B]
      decide +kernel
    exact hne (by rw [h]; rfl)

theorem involution2A_mem :
    involution2A ∈ AutPerm := by
  refine (mem_AutPerm_iff_conj involution2A).2 ⟨m24Rep2, ?_, ?_⟩
  · simpa [m24Certificate_originalSubgroup] using (m24_rep_data2).1
  · intro i
    simp [involution2A, Equiv.Perm.mul_apply]

theorem involution2B_mem :
    involution2B ∈ AutPerm := by
  refine (mem_AutPerm_iff_conj involution2B).2 ⟨m24Rep1, ?_, ?_⟩
  · simpa [m24Certificate_originalSubgroup] using (m24_rep_data1).1
  · intro i
    simp [involution2B, Equiv.Perm.mul_apply]

theorem exists_conj_involution2
    {z : Equiv.Perm (Fin 24)} (hz : z ∈ AutPerm)
    (hz2 : orderOf z = 2) :
    (∃ c ∈ AutPerm, z = c * involution2A * c⁻¹) ∨ (∃ c ∈ AutPerm, z = c * involution2B * c⁻¹) := by
  obtain ⟨g, hgM, hzg⟩ := (mem_AutPerm_iff_conj z).1 hz
  have hg_eq : g = bridgeQ * z * bridgeQ⁻¹ := by
    apply Equiv.ext
    intro i
    have h : bridgeQ (z (bridgeQ⁻¹ i)) = g i := by
      have h0 : z (bridgeQ⁻¹ i) = bridgeQ⁻¹ (g i) := by simpa using hzg (bridgeQ⁻¹ i)
      rw [h0]
      simp [Equiv.Perm.inv_def]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact h.symm
  have hg_order : orderOf g = 2 := by
    rw [hg_eq, ← MulAut.conj_apply]
    exact (MulEquiv.orderOf_eq (MulAut.conj bridgeQ) z).trans hz2
  obtain ⟨r, hr, c, hc, hgconj⟩ := m24_involution_conj_reps hgM hg_order
  have hz_eq : z = bridgeQ⁻¹ * g * bridgeQ := by rw [hg_eq]; group
  have hc' : bridgeQ⁻¹ * c * bridgeQ ∈ AutPerm := by
    refine (mem_AutPerm_iff_conj _).2 ⟨c, hc, fun i => ?_⟩
    simp [Equiv.Perm.mul_apply]
  rw [m24InvReps_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right
    refine ⟨bridgeQ⁻¹ * c * bridgeQ, hc', ?_⟩
    rw [hz_eq, hgconj, involution2B]
    group
  · left
    refine ⟨bridgeQ⁻¹ * c * bridgeQ, hc', ?_⟩
    rw [hz_eq, hgconj, involution2A]
    group

theorem card_centralizerIn_involution2A :
    Nat.card (centralizerIn AutPerm involution2A) = 21504 := by
  have hAut : AutPerm =
      NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom :=
    AutPerm_eq_closure.trans bridge_closure_eq_map
  rw [hAut]
  change Nat.card (centralizerIn
      (NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom)
      (bridgeQ⁻¹ * m24Rep2 * (bridgeQ⁻¹)⁻¹)) = 21504
  rw [centralizerIn_map_conj NativeSporadic.M24 bridgeQ⁻¹ m24Rep2,
    Subgroup.card_map_of_injective (MulAut.conj bridgeQ⁻¹).injective,
    CFSG.EvenSporadicStandard.HypOne.M24.centralizerIn_rep2]
  exact (m24_rep_data2).2.2.2.1

theorem card_centralizerIn_involution2B :
    Nat.card (centralizerIn AutPerm involution2B) = 7680 := by
  have hAut : AutPerm =
      NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom :=
    AutPerm_eq_closure.trans bridge_closure_eq_map
  rw [hAut]
  change Nat.card (centralizerIn
      (NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom)
      (bridgeQ⁻¹ * m24Rep1 * (bridgeQ⁻¹)⁻¹)) = 7680
  rw [centralizerIn_map_conj NativeSporadic.M24 bridgeQ⁻¹ m24Rep1,
    Subgroup.card_map_of_injective (MulAut.conj bridgeQ⁻¹).injective,
    CFSG.EvenSporadicStandard.HypOne.M24.centralizerIn_rep1]
  exact (m24_rep_data1).2.2.2.1

theorem involution_dichotomy
    {z : Equiv.Perm (Fin 24)}
    (hz : z ∈ M24g) (hz2 : orderOf z = 2) :
    (IsTwoCentralElt M24g z ∧ (∃ c ∈ M24g, z = c * involution2A * c⁻¹) ∧
      (∃ O : Finset (Fin 24), IsOctad O ∧ ∀ i, i ∈ O ↔ z i = i) ∧ ∃ i, z i = i) ∨
    (¬ IsTwoCentralElt M24g z ∧ (∃ c ∈ M24g, z = c * involution2B * c⁻¹) ∧ ∀ i, z i ≠ i) := by
  rcases exists_conj_involution2 (show z ∈ AutPerm from hz) hz2 with ⟨c, hc, hzA⟩ | ⟨c, hc, hzB⟩
  · left
    have hcM : c ∈ M24g := hc
    have h2A : IsTwoCentralElt M24g involution2A := by
      rw [isTwoCentralElt_iff_dvd_card]
      change 2 ^ (Nat.card AutPerm).factorization 2 ∣
        Nat.card (centralizerIn AutPerm involution2A)
      rw [factorization_two_card_AutPerm, card_centralizerIn_involution2A]
      norm_num
    have hzc2 : IsTwoCentralElt M24g z := by
      rw [hzA]
      exact (isTwoCentralElt_conj hcM).2 h2A
    refine ⟨hzc2, ⟨c, hcM, hzA⟩, ?_, ?_⟩
    · refine ⟨octadOf2AInvolution.map c.toEmbedding,
        isOctad_map_of_mem_AutPerm hc isOctad_octadOf2AInvolution, fun i => ?_⟩
      have hzi : z i = c (involution2A (c⁻¹ i)) := by
        rw [hzA, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have hOiff : i ∈ octadOf2AInvolution.map c.toEmbedding ↔
          c⁻¹ i ∈ octadOf2AInvolution := by
        rw [Finset.mem_map_equiv]
        simp [Equiv.Perm.inv_def]
      have hziff : z i = i ↔ c⁻¹ i ∈ octadOf2AInvolution := by
        rw [hzi]
        constructor
        · intro hh
          have h2 : involution2A (c⁻¹ i) = c⁻¹ i :=
            c.injective (hh.trans (by simp [Equiv.Perm.inv_def]))
          exact (involution2A_fixed (c⁻¹ i)).1 h2
        · intro hh
          rw [(involution2A_fixed (c⁻¹ i)).2 hh]
          simp [Equiv.Perm.inv_def]
      exact hOiff.trans hziff.symm
    · refine ⟨c 1, ?_⟩
      have hzi : z (c 1) = c (involution2A (c⁻¹ (c 1))) := by
        rw [hzA, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have hfix : involution2A (c⁻¹ (c 1)) = c⁻¹ (c 1) := by
        have hc1 : c⁻¹ (c 1) = 1 := by simp [Equiv.Perm.inv_def]
        rw [hc1]
        exact (involution2A_fixed 1).2 (by decide +kernel)
      rw [hzi, hfix]
      simp
  · right
    have hcM : c ∈ M24g := hc
    have h2B : ¬ IsTwoCentralElt M24g involution2B := by
      rw [isTwoCentralElt_iff_dvd_card]
      change ¬ (2 ^ (Nat.card AutPerm).factorization 2 ∣
        Nat.card (centralizerIn AutPerm involution2B))
      rw [factorization_two_card_AutPerm, card_centralizerIn_involution2B]
      norm_num
    have hzBnc : ¬ IsTwoCentralElt M24g z := by
      rw [hzB]
      exact fun h => h2B ((isTwoCentralElt_conj hcM).1 h)
    refine ⟨hzBnc, ⟨c, hcM, hzB⟩, fun i hi => ?_⟩
    have hzi : z i = c (involution2B (c⁻¹ i)) := by
      rw [hzB, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [hzi] at hi
    have hci : involution2B (c⁻¹ i) = c⁻¹ i := by
      have := congrArg (fun x : Fin 24 => c⁻¹ x) hi
      simpa [Equiv.Perm.inv_def] using this
    exact involution2B_fixed (c⁻¹ i) hci

private lemma not_exists_isOctad_fixed_iff_of_fixedFree {z : Equiv.Perm (Fin 24)}
    (hfree : ∀ i, z i ≠ i) :
    ¬ ∃ O : Finset (Fin 24), IsOctad O ∧ ∀ i, i ∈ O ↔ z i = i := by
  rintro ⟨O, hO, hOfix⟩
  have hOempty : O = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    exact hfree i ((hOfix i).1 hi)
  have h8 : O.card = 8 := hO.1
  rw [hOempty, Finset.card_empty] at h8
  exact absurd h8 (by norm_num)

theorem m24_involution_classes :
    (∀ z ∈ M24g, orderOf z = 2 →
      ((IsTwoCentralElt M24g z ↔ ∃ O : Finset (Fin 24), IsOctad O ∧ ∀ i, i ∈ O ↔ z i = i) ∧
        (¬ IsTwoCentralElt M24g z ↔ ∀ i : Fin 24, z i ≠ i))) ∧
    (∃ z ∈ M24g, orderOf z = 2 ∧ IsTwoCentralElt M24g z) ∧
    (∃ t ∈ M24g, orderOf t = 2 ∧ ¬ IsTwoCentralElt M24g t) ∧
    (∀ z ∈ M24g, ∀ z' ∈ M24g, orderOf z = 2 → orderOf z' = 2 → IsTwoCentralElt M24g z →
      IsTwoCentralElt M24g z' → IsConjIn M24g z z') ∧
    (∀ t ∈ M24g, ∀ t' ∈ M24g, orderOf t = 2 → orderOf t' = 2 → ¬ IsTwoCentralElt M24g t →
      ¬ IsTwoCentralElt M24g t' → IsConjIn M24g t t') := by
  have h2A : IsTwoCentralElt M24g involution2A := by
    rw [isTwoCentralElt_iff_dvd_card]
    change 2 ^ (Nat.card AutPerm).factorization 2 ∣
      Nat.card (centralizerIn AutPerm involution2A)
    rw [factorization_two_card_AutPerm, card_centralizerIn_involution2A]
    norm_num
  have h2B : ¬ IsTwoCentralElt M24g involution2B := by
    rw [isTwoCentralElt_iff_dvd_card]
    change ¬ (2 ^ (Nat.card AutPerm).factorization 2 ∣
      Nat.card (centralizerIn AutPerm involution2B))
    rw [factorization_two_card_AutPerm, card_centralizerIn_involution2B]
    norm_num
  refine ⟨?_, ⟨involution2A, involution2A_mem, orderOf_involution2A, h2A⟩,
    ⟨involution2B, involution2B_mem, orderOf_involution2B, h2B⟩, ?_, ?_⟩
  · intro z hz hz2
    rcases involution_dichotomy hz hz2 with
      ⟨h2c, hconjA, ⟨O, hOoct, hOiff⟩, ⟨i0, hi0⟩⟩ | ⟨h2nc, hconjB, hfree⟩
    · refine ⟨⟨fun _ => ⟨O, hOoct, hOiff⟩, fun _ => h2c⟩,
        ⟨fun h => absurd h2c h, fun hfix _ => ?_⟩⟩
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [hOoct.1]; norm_num)
      exact absurd ((hOiff i).1 hi) (hfix i)
    · refine ⟨⟨fun h => absurd h h2nc,
        fun hO => absurd hO (not_exists_isOctad_fixed_iff_of_fixedFree hfree)⟩,
        ⟨fun _ => hfree, fun _ => h2nc⟩⟩
  · intro z hz z' hz' hz2 hz2' hzc hzc'
    rcases involution_dichotomy hz hz2 with ⟨-, ⟨c, hc, hzeq⟩, -, -⟩ | ⟨h2nc, -, -⟩
    · rcases involution_dichotomy hz' hz2' with ⟨-, ⟨c', hc', hz'eq⟩, -, -⟩ | ⟨h2nc', -, -⟩
      · refine ⟨c' * c⁻¹, M24g.mul_mem hc' (M24g.inv_mem hc), ?_⟩
        rw [hzeq, hz'eq]
        group
      · exact absurd hzc' h2nc'
    · exact absurd hzc h2nc
  · intro t ht t' ht' ht2 ht2' htc htc'
    rcases involution_dichotomy ht ht2 with ⟨h2c, -, -⟩ | ⟨-, ⟨c, hc, teq⟩, -⟩
    · exact absurd h2c htc
    · rcases involution_dichotomy ht' ht2' with ⟨h2c', -, -⟩ | ⟨-, ⟨c', hc', t'eq⟩, -⟩
      · exact absurd h2c' htc'
      · refine ⟨c' * c⁻¹, M24g.mul_mem hc' (M24g.inv_mem hc), ?_⟩
        rw [teq, t'eq]
        group

end CFSG.Quasithin.AppendixH.H14
