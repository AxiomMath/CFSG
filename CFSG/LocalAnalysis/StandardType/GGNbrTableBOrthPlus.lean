module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBWeyl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBCard
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrderRestOn

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

section Model

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

private theorem closure_ggTorusReflSet_le {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Subgroup.closure (ggTorusReflSet p A) ≤
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
  refine (Subgroup.closure_le _).mpr fun φ hφ => ?_
  obtain ⟨n, hn, -, rfl, -⟩ := hφ
  exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn

theorem ggTorusReflGenW_of_evenSignedPermEltSC {kP : ℕ → Prop} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSC p R kP) :
    GGTorusReflGenW p r R I := by
  intro L' _ _ ψ A hA v hv
  obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ := hA
  obtain ⟨k, Θ, hk, -, hW, -, hP, hST, hN⟩ :=
    OrthExcEven.exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
  have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
  set H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    (Subgroup.closure (ggTorusReflSet p A)).comap (MulAut.congr Θ).toMonoidHom with hH
  have hgen : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)), α ^ 2 = 1 →
      Nat.card {f // α f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) →
      (∃ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hm = MulAut.congr Θ α) → α ∈ H := by
    rintro α hα2 hαfix ⟨m, hm, hmα⟩
    exact Subgroup.subset_closure ⟨m, hm, hW m hm, hmα.symm,
      ⟨by rw [← map_pow, hα2, map_one],
        (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 hα2) hαfix).2⟩⟩
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := fun a b hab =>
    hgen _ (permAut_swap_sq a b) (card_fix_permAut_swap hp hp2 hab) (hP _)
  have hdH : ∀ a b : Fin k, a ≠ b → sgnAut a * sgnAut b ∈ H := fun a b hab => by
    have h1 := H.mul_mem (hgen _ (OrthExcEven.sgnTransp_sq hab)
      (OrthExcEven.card_fix_sgnTransp hp hp2 hab) (hST a b hab)) (htH a b hab)
    rwa [mul_assoc, OrthExcEven.permAut_swap_mul_self, mul_one] at h1
  have hHA : ∀ u ∈ H, MulAut.congr Θ u ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := fun u hu =>
    closure_ggTorusReflSet_le A hu
  set u := (MulAut.congr Θ).symm (ggConjAut A hcN) with hudef
  have hcu : MulAut.congr Θ u = ggConjAut A hcN := MulEquiv.apply_symm_apply _ _
  obtain ⟨i₀⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hu' : u ∈ H := by
    rcases OrthExcEven.mem_or_mul_mem_of_isSignedPerm hdH htH i₀ (hN n hcN) with h1 | h1
    · exact h1
    · have hs : MulAut.congr Θ (sgnAut i₀) ∈
          ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
        have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _
          (ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hcN)) (hHA _ h1)
        have e : (ggConjAut A hcN)⁻¹ * MulAut.congr Θ (u * sgnAut i₀) =
            MulAut.congr Θ (sgnAut i₀) := by
          rw [map_mul, hcu, inv_mul_cancel_left]
        rwa [e] at h2
      obtain ⟨c', ⟨m, rfl⟩, hmN, hmc⟩ := mem_ggAutomizer_iff.mp hs
      have hm : ggConjAut A hmN = MulAut.congr Θ (sgnAut i₀) :=
        MulEquiv.ext fun a => Subtype.ext (hmc a).symm
      have hsH := hgen _ (sgnAut_sq i₀) (card_fix_sgnAut hp hp2 i₀) ⟨m, hmN, hm⟩
      have h3 := H.mul_mem h1 (H.inv_mem hsH)
      rwa [mul_inv_cancel_right] at h3
  rw [hv', ← hcu]
  exact hu'

theorem ggTorusAutCardDvdSCr_of_evenSignedPermEltSC {kP : ℕ → Prop} (hp : p.Prime)
    (hp2 : p ≠ 2) (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R)
    (h : GGTorusEvenSignedPermEltSC p R kP) :
    GGTorusAutCardDvdSCr p r R I (2 ^ (r - 1) * r.factorial) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAab, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨k, Θ, hk, -, -, hD, hP, -, hN⟩ :=
    OrthExcEven.exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hAab hAI h3 hsc
  let W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  let H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    W.comap (MulAut.congr Θ).toMonoidHom
  have hmap : Subgroup.map (MulAut.congr Θ).toMonoidHom H = W :=
    Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.congr Θ).toMonoidHom)
      (MulAut.congr Θ).surjective W
  have hcardH : Nat.card H = Nat.card W := by
    rw [← hmap, Subgroup.card_map_of_injective (f := (MulAut.congr Θ).toMonoidHom)
      (MulAut.congr Θ).injective]
  have hHH : ∀ u ∈ H, IsSignedPerm ⇑u := by
    intro u hu
    have huW : MulAut.congr Θ u ∈ W := Subgroup.mem_comap.mp hu
    obtain ⟨_, ⟨n, rfl⟩, hmn, hmu⟩ := mem_ggAutomizer_iff.mp huW
    have hcu : MulAut.congr Θ u = ggConjAut A hmn := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      exact (hmu b).trans (ggConjAut_apply A hmn b).symm
    have hu' : u = (MulAut.congr Θ).symm (ggConjAut A hmn) := by
      rw [← hcu, MulEquiv.symm_apply_apply]
    rw [hu']
    exact hN n hmn
  have hdH : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H := by
    intro i j hij
    obtain ⟨n, hn, hnD⟩ := hD i j hij
    refine Subgroup.mem_comap.mpr ?_
    rw [show (MulAut.congr Θ).toMonoidHom (sgnAut i * sgnAut j) = ggConjAut A hn
      from hnD.symm]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := by
    intro a b hab
    obtain ⟨n, hn, hnP⟩ := hP (Equiv.swap a b)
    refine Subgroup.mem_comap.mpr ?_
    rw [show (MulAut.congr Θ).toMonoidHom (permAut (Equiv.swap a b)) = ggConjAut A hn
      from hnP.symm]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hdvd := SignedPermCount.dvd_card_of_isSignedPerm_even hp hp2 hHH hdH htH
  have hrk : r ≤ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card A :=
      Nat.card_congr Θ.toEquiv
    rw [hcV] at h1
    rw [← h1] at hr
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hr
  have hdiv : 2 ^ (r - 1) * r.factorial ∣ 2 ^ (k - 1) * k.factorial :=
    mul_dvd_mul (pow_dvd_pow 2 (Nat.sub_le_sub_right hrk 1))
      (Nat.factorial_dvd_factorial hrk)
  change 2 ^ (r - 1) * r.factorial ∣ Nat.card W
  rw [← hcardH]
  exact hdiv.trans hdvd

end Model

theorem recipeOmegaPlus_reflGenW
    {l n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    TableBSymp.ggTorusLift_omegaPlus hp hp2 hpK (by omega),
    ggTorusReflGenW_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
      (ggOrthEvenTorusInput_holds.1 K l p hl hp (Or.inl hpK))⟩

theorem recipeOmegaPlus_autCardDvd
    {l n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧
        GGTorusAutCardDvdSCr p r R I (2 ^ (l - 1) * l.factorial) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    TableBSymp.ggTorusLift_omegaPlus hp hp2 hpK (by omega),
    ggTorusAutCardDvdSCr_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
      (ggOrthEvenTorusInput_holds.1 K l p hl hp (Or.inl hpK))⟩

theorem ggNbrTableBWeylInputOn_typeD_holds :
    GGNbrTableBWeylInputOn fun _ lab => lab.tag = .D := by
  rintro p hp - ⟨tag, l, n⟩ hlab htag - hsp Q hQ
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl3 : 3 ≤ l := hlab.2
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · exact recipeLinear_reflGenW (d := 4) (N := 2 ^ n) hp hsp.2.2 ⟨n, rfl⟩ (by norm_num) hQ
  · exact recipeOmegaPlus_reflGenW hp hn hsp.2.2 (by omega) hQ

theorem ggNbrTableBOrderRestInputOn_typeD_holds :
    GGNbrTableBOrderRestInputOn fun _ lab => lab.tag = .D := by
  rintro p hp - ⟨tag, l, n⟩ N hlab htag hsp hN Q hQ
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl3 : 3 ≤ l := hlab.2
  obtain rfl : N = 2 ^ (l - 1) * l.factorial := by
    rcases hN with ⟨h, -⟩ | ⟨-, hN⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by simp)
    · exact hN
    all_goals exact absurd h (by simp)
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · subst h3
    obtain ⟨K, i₁, i₂, hK, hQ', r, hL, hC⟩ :=
      recipeLinear_autCard (d := 4) (N := 2 ^ n) hp hsp.2.2 ⟨n, rfl⟩ (by norm_num) hQ
    refine ⟨K, i₁, i₂, hK, hQ', r, hL, ?_⟩
    rw [show 2 ^ (3 - 1) * Nat.factorial 3 = Nat.factorial 4 by decide]
    exact hC.toDvd
  · exact recipeOmegaPlus_autCardDvd hp hn hsp.2.2 (by omega) hQ

end CFSG.StandardType
