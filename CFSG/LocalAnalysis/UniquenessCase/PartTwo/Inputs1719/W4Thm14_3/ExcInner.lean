module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcDim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcTensor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcF4
public import CFSG.Quasithin.Vol2.Ch3B513NSp4
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.SmithB45L2Class

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

private lemma card_roots_four {F : Type} [Field F] {x : F} (hx : x ≠ 0) :
    Nat.card {t : F | x * t ^ 4 = t * x ^ 4} ≤ 4 := by
  classical
  let p : Polynomial F := Polynomial.C x * Polynomial.X ^ 4 - Polynomial.C (x ^ 4) * Polynomial.X
  have hdeg : p.natDegree ≤ 4 := by
    have h1 : (Polynomial.C x * Polynomial.X ^ 4 : Polynomial F).natDegree ≤ 4 :=
      Polynomial.natDegree_C_mul_X_pow_le x 4
    have h2 : (Polynomial.C (x ^ 4) * Polynomial.X : Polynomial F).natDegree ≤ 1 := by
      simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le (x ^ 4) 1
    have h := Polynomial.natDegree_sub_le (Polynomial.C x * Polynomial.X ^ 4)
      (Polynomial.C (x ^ 4) * Polynomial.X)
    exact h.trans (max_le h1 (h2.trans (by norm_num)))
  have hp_ne : p ≠ 0 := by
    intro hp0
    have hc : p.coeff 4 = x := by
      simp only [p, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X]
      norm_num
    rw [hp0] at hc
    simp at hc
    exact hx hc.symm
  have hset : {t : F | p.IsRoot t} = (p.roots.toFinset : Set F) := by
    ext t
    rw [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
  have heq : Nat.card {t : F | p.IsRoot t} = p.roots.toFinset.card := by
    rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset]
  calc Nat.card {t : F | x * t ^ 4 = t * x ^ 4}
      = Nat.card {t : F | p.IsRoot t} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
        intro t
        show x * t ^ 4 = t * x ^ 4 ↔ p.eval t = 0
        simp only [p, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X]
        rw [sub_eq_zero]
        constructor
        · intro h; rw [h, mul_comm]
        · intro h; rw [h, mul_comm]
    _ = p.roots.toFinset.card := heq
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ 4 := hdeg

private lemma card_f4_roots {F : Type} [Field F] [Fintype F] :
    Nat.card {l : F | l ^ 4 = l} ≤ 4 := by
  classical
  have h := CFSG.Quasithin.B45L2.card_le_of_frob_fixed (d := 2) (by norm_num)
    (Finset.univ.filter (fun l : F => l ^ 4 = l))
    (fun u hu => by simpa using (Finset.mem_filter.mp hu).2)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa using h

private lemma card_image_le {F : Type} [Field F] [Fintype F] {x y : F} :
    Nat.card {t : F | ∃ l l' : F, l ^ 4 = l ∧ l' ^ 4 = l' ∧ t = l * x + l' * y} ≤ 16 := by
  classical
  let g : ({l : F // l ^ 4 = l} × {l' : F // l' ^ 4 = l'}) →
      {t : F // ∃ l l' : F, l ^ 4 = l ∧ l' ^ 4 = l' ∧ t = l * x + l' * y} :=
    fun p => ⟨p.1.1 * x + p.2.1 * y, ⟨p.1.1, p.2.1, p.1.2, p.2.2, rfl⟩⟩
  have hsurj : Function.Surjective g := by
    intro t
    obtain ⟨l, l', hl, hl', ht⟩ := t.2
    exact ⟨⟨⟨l, hl⟩, ⟨l', hl'⟩⟩, Subtype.ext ht.symm⟩
  have h1 : Nat.card {t : F | ∃ l l' : F, l ^ 4 = l ∧ l' ^ 4 = l' ∧ t = l * x + l' * y}
      ≤ Nat.card ({l : F // l ^ 4 = l} × {l' : F // l' ^ 4 = l'}) :=
    Nat.card_le_card_of_surjective g hsurj
  have h2 : Nat.card ({l : F // l ^ 4 = l} × {l' : F // l' ^ 4 = l'}) ≤ 16 := by
    rw [Nat.card_prod]
    have h3 : Nat.card {l : F // l ^ 4 = l} ≤ 4 := card_f4_roots
    have h4 : Nat.card {l : F // l ^ 4 = l} ≤ 4 := card_f4_roots
    nlinarith
  exact h1.trans h2

theorem exists_fixW_ne {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 6) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hD : SixtyFourDescent ρ)
    (A₀ : AddSubgroup F) (hA : 8 ≤ Nat.card A₀) :
    ∃ B₀ : AddSubgroup F, B₀ ≤ A₀ ∧ Nat.card A₀ ≤ 4 * Nat.card B₀ ∧
      Nat.card {w : W // ∀ t ∈ B₀, ρ (uElt t) w = w} ≠
        Nat.card {w : W // ∀ t ∈ A₀, ρ (uElt t) w = w} := by
  classical
  haveI hfin : Finite (EndRing ρ) := finite_endRing ρ
  haveI hfd : FiniteDimensional (EndRing ρ) W := Module.Finite.of_finite
  let b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W :=
    Module.finBasis (EndRing ρ) W
  obtain ⟨hDcard, hDdata⟩ := hD
  obtain ⟨E, hE, hFin, hChar, ιF, ιD, J, hJ, hΦ⟩ := hDdata b
  letI : Field E := hE
  letI : Finite E := hFin
  letI : CharP E 2 := hChar
  letI : Algebra F E := ιF.toAlgebra
  obtain ⟨Φ⟩ := hΦ
  have h64 : Nat.card F = 64 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  have hdv : Nat.card A₀ ∣ 2 ^ 6 := by
    have h : Nat.card ↥A₀ * A₀.index = Nat.card F := AddSubgroup.card_mul_index A₀
    have hdvd : Nat.card ↥A₀ ∣ Nat.card F := ⟨A₀.index, h.symm⟩
    rw [h64] at hdvd
    rwa [show (2:ℕ)^6 = 64 by norm_num]
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdv
  have hk_ge : 3 ≤ k := by
    rw [hk_eq] at hA
    have h : 2 ^ 3 ≤ 2 ^ k := by norm_num; exact hA
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hk_cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl
  ·
    obtain ⟨x, hxA, y, hyA, hxne, hxy⟩ := exists_pair_of_eight_le hF A₀ (by rw [hk_eq]; norm_num)
    let B₀ := AddSubgroup.zmultiples x
    have hB₀le : B₀ ≤ A₀ := AddSubgroup.zmultiples_le.mpr hxA
    have hB₀card : Nat.card B₀ = 2 := by
      rw [Nat.card_zmultiples]
      exact addOrderOf_eq_prime (p := 2) (by rw [two_nsmul]; exact CharTwo.add_self_eq_zero x) hxne
    refine ⟨B₀, hB₀le, by rw [hk_eq, hB₀card]; norm_num, ?_⟩
    obtain ⟨w, hwB, hwy⟩ := exists_fixW_line_moved ρ hF b ιF ιD J hJ Φ hxne hxy
    have hfixB : ∀ t ∈ B₀, ρ (uElt t) w = w := by
      intro t ht
      change t ∈ AddSubgroup.zmultiples x at ht
      rw [AddSubgroup.zmultiples_eq_closure] at ht
      refine AddSubgroup.closure_induction (p := fun t _ => ρ (uElt t) w = w) ?_ ?_ ?_ ?_ ht
      · intro y' hy'
        rw [Set.mem_singleton_iff] at hy'
        subst hy'
        simpa using hwB 1 (by norm_num)
      · rw [uElt_zero]; simp
      · intro a b ha hb hpa hpb
        rw [uElt_add, map_mul ρ, Module.End.mul_apply, hpb, hpa]
      · intro a ha hpa
        rw [CharTwo.neg_eq]
        exact hpa
    have hnotA : ¬ ∀ t ∈ A₀, ρ (uElt t) w = w := fun h => hwy (h y hyA)
    have hsubset : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ B₀, ρ (uElt t) w = w} := by
      intro v hv t ht
      exact hv t (hB₀le ht)
    have hnotsub : ¬ ({w : W | ∀ t ∈ B₀, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} := by
      intro hsub
      exact hnotA (hsub hfixB)
    have hlt : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W).ncard <
        ({w : W | ∀ t ∈ B₀, ρ (uElt t) w = w} : Set W).ncard :=
      Set.ncard_lt_ncard ⟨hsubset, hnotsub⟩
    exact ne_of_gt hlt
  ·
    obtain ⟨x, K, hxne, hKle, hKcard, hKprop⟩ :=
      exists_line_of_sixteen_le hF A₀ (by rw [hk_eq]; norm_num)
    have hy_exists : ∃ y ∈ A₀, y ∉ K := by
      by_contra h
      push Not at h
      have hle : A₀ ≤ K := fun t ht => h t ht
      have hcard : Nat.card A₀ ≤ Nat.card K :=
        Nat.card_le_card_of_injective (fun t : A₀ => (⟨t.1, hle t.2⟩ : K)) (by
          intro a b hab
          exact Subtype.ext (congrArg (fun x : K => x.1) hab))
      rw [hk_eq, hKcard] at hcard
      norm_num at hcard
    obtain ⟨y, hyA, hyK⟩ := hy_exists
    have hK_subset : (K : Set F) ⊆ {t : F | x * t ^ 4 = t * x ^ 4} := by
      intro t ht
      obtain ⟨l, hl, hlt⟩ := hKprop t ht
      rw [hlt]
      calc x * (l * x) ^ 4 = x * (l ^ 4 * x ^ 4) := by rw [mul_pow]
        _ = x * (l * x ^ 4) := by rw [hl]
        _ = l * x * x ^ 4 := by ring
    have hbound : ({t : F | x * t ^ 4 = t * x ^ 4} : Set F).ncard ≤ 4 := card_roots_four hxne
    have hKcard' : (K : Set F).ncard = 4 := by
      rw [← Nat.card_coe_set_eq (K : Set F)]
      change Nat.card ↥K = 4
      exact hKcard
    have hcard_le : (K : Set F).ncard ≤ ({t : F | x * t ^ 4 = t * x ^ 4} : Set F).ncard :=
      Set.ncard_le_ncard hK_subset
    have hcard_eq : ({t : F | x * t ^ 4 = t * x ^ 4} : Set F).ncard = 4 := by omega
    have hK_eq : (K : Set F) = {t : F | x * t ^ 4 = t * x ^ 4} :=
      Set.eq_of_subset_of_ncard_le hK_subset (by rw [hcard_eq, hKcard'])
    have hxy : x * y ^ 4 ≠ y * x ^ 4 := by
      intro h
      have hyK' : y ∈ (K : Set F) := by
        rw [hK_eq]
        exact h
      exact hyK hyK'
    refine ⟨K, hKle, by rw [hk_eq, hKcard]; norm_num, ?_⟩
    obtain ⟨w, hwB, hwy⟩ := exists_fixW_line_moved ρ hF b ιF ιD J hJ Φ hxne hxy
    have hfixB : ∀ t ∈ K, ρ (uElt t) w = w := by
      intro t ht
      obtain ⟨l, hl, hlt⟩ := hKprop t ht
      rw [hlt]; simpa using hwB l hl
    have hnotA : ¬ ∀ t ∈ A₀, ρ (uElt t) w = w := fun h => hwy (h y hyA)
    have hsubset : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ K, ρ (uElt t) w = w} := by
      intro v hv t ht
      exact hv t (hKle ht)
    have hnotsub : ¬ ({w : W | ∀ t ∈ K, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} := by
      intro hsub
      exact hnotA (hsub hfixB)
    have hlt : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W).ncard <
        ({w : W | ∀ t ∈ K, ρ (uElt t) w = w} : Set W).ncard :=
      Set.ncard_lt_ncard ⟨hsubset, hnotsub⟩
    exact ne_of_gt hlt
  ·
    have hA32 : 32 ≤ Nat.card A₀ := by rw [hk_eq]; norm_num
    obtain ⟨x, y, K, hxne, hxy, hKle, hKcard, hKprop⟩ :=
      exists_plane_of_thirtytwo_le hF A₀ hA32
    have hz_exists : ∃ z ∈ A₀, z ∉ K := by
      by_contra h
      push Not at h
      have hle : A₀ ≤ K := fun t ht => h t ht
      have hcard : Nat.card A₀ ≤ Nat.card K :=
        Nat.card_le_card_of_injective (fun t : A₀ => (⟨t.1, hle t.2⟩ : K)) (by
          intro a b hab
          exact Subtype.ext (congrArg (fun x : K => x.1) hab))
      rw [hk_eq, hKcard] at hcard
      norm_num at hcard
    obtain ⟨z, hzA, hzK⟩ := hz_exists
    let S : Set F := {t : F | ∃ l l' : F, l ^ 4 = l ∧ l' ^ 4 = l' ∧ t = l * x + l' * y}
    have hK_subset : (K : Set F) ⊆ S := by
      intro t ht
      obtain ⟨l, l', hl, hl', hlt⟩ := hKprop t ht
      exact ⟨l, l', hl, hl', hlt⟩
    have hbound : S.ncard ≤ 16 := card_image_le
    have hKcard' : (K : Set F).ncard = 16 := by
      rw [← Nat.card_coe_set_eq (K : Set F)]
      change Nat.card ↥K = 16
      exact hKcard
    have hcard_le : (K : Set F).ncard ≤ S.ncard :=
      Set.ncard_le_ncard hK_subset
    have hcard_eq : S.ncard = 16 := by omega
    have hK_eq : (K : Set F) = S :=
      Set.eq_of_subset_of_ncard_le hK_subset (by rw [hcard_eq, hKcard'])
    have hz : ∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' → z ≠ l * x + l' * y := by
      intro l l' hl hl' hz_eq
      apply hzK
      change z ∈ (K : Set F)
      rw [hK_eq]
      exact ⟨l, l', hl, hl', hz_eq⟩
    refine ⟨K, hKle, by rw [hk_eq, hKcard]; norm_num, ?_⟩
    obtain ⟨w, hwB, hwy⟩ := exists_fixW_plane_moved ρ hF b ιF ιD J hJ Φ hxne hxy hz
    have hfixB : ∀ t ∈ K, ρ (uElt t) w = w := by
      intro t ht
      obtain ⟨l, l', hl, hl', hlt⟩ := hKprop t ht
      rw [hlt]; simpa using hwB l l' hl hl'
    have hnotA : ¬ ∀ t ∈ A₀, ρ (uElt t) w = w := fun h => hwy (h z hzA)
    have hsubset : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ K, ρ (uElt t) w = w} := by
      intro v hv t ht
      exact hv t (hKle ht)
    have hnotsub : ¬ ({w : W | ∀ t ∈ K, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} := by
      intro hsub
      exact hnotA (hsub hfixB)
    have hlt : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W).ncard <
        ({w : W | ∀ t ∈ K, ρ (uElt t) w = w} : Set W).ncard :=
      Set.ncard_lt_ncard ⟨hsubset, hnotsub⟩
    exact ne_of_gt hlt
  ·
    have hA32 : 32 ≤ Nat.card A₀ := by rw [hk_eq]; norm_num
    obtain ⟨x, y, K, hxne, hxy, hKle, hKcard, hKprop⟩ :=
      exists_plane_of_thirtytwo_le hF A₀ hA32
    have hz_exists : ∃ z ∈ A₀, z ∉ K := by
      by_contra h
      push Not at h
      have hle : A₀ ≤ K := fun t ht => h t ht
      have hcard : Nat.card A₀ ≤ Nat.card K :=
        Nat.card_le_card_of_injective (fun t : A₀ => (⟨t.1, hle t.2⟩ : K)) (by
          intro a b hab
          exact Subtype.ext (congrArg (fun x : K => x.1) hab))
      rw [hk_eq, hKcard] at hcard
      norm_num at hcard
    obtain ⟨z, hzA, hzK⟩ := hz_exists
    let S : Set F := {t : F | ∃ l l' : F, l ^ 4 = l ∧ l' ^ 4 = l' ∧ t = l * x + l' * y}
    have hK_subset : (K : Set F) ⊆ S := by
      intro t ht
      obtain ⟨l, l', hl, hl', hlt⟩ := hKprop t ht
      exact ⟨l, l', hl, hl', hlt⟩
    have hbound : S.ncard ≤ 16 := card_image_le
    have hKcard' : (K : Set F).ncard = 16 := by
      rw [← Nat.card_coe_set_eq (K : Set F)]
      change Nat.card ↥K = 16
      exact hKcard
    have hcard_le : (K : Set F).ncard ≤ S.ncard :=
      Set.ncard_le_ncard hK_subset
    have hcard_eq : S.ncard = 16 := by omega
    have hK_eq : (K : Set F) = S :=
      Set.eq_of_subset_of_ncard_le hK_subset (by rw [hcard_eq, hKcard'])
    have hz : ∀ l l' : F, l ^ 4 = l → l' ^ 4 = l' → z ≠ l * x + l' * y := by
      intro l l' hl hl' hz_eq
      apply hzK
      change z ∈ (K : Set F)
      rw [hK_eq]
      exact ⟨l, l', hl, hl', hz_eq⟩
    refine ⟨K, hKle, by rw [hk_eq, hKcard]; norm_num, ?_⟩
    obtain ⟨w, hwB, hwy⟩ := exists_fixW_plane_moved ρ hF b ιF ιD J hJ Φ hxne hxy hz
    have hfixB : ∀ t ∈ K, ρ (uElt t) w = w := by
      intro t ht
      obtain ⟨l, l', hl, hl', hlt⟩ := hKprop t ht
      rw [hlt]; simpa using hwB l l' hl hl'
    have hnotA : ¬ ∀ t ∈ A₀, ρ (uElt t) w = w := fun h => hwy (h z hzA)
    have hsubset : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ K, ρ (uElt t) w = w} := by
      intro v hv t ht
      exact hv t (hKle ht)
    have hnotsub : ¬ ({w : W | ∀ t ∈ K, ρ (uElt t) w = w} : Set W) ⊆
        {w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} := by
      intro hsub
      exact hnotA (hsub hfixB)
    have hlt : ({w : W | ∀ t ∈ A₀, ρ (uElt t) w = w} : Set W).ncard <
        ({w : W | ∀ t ∈ K, ρ (uElt t) w = w} : Set W).ncard :=
      Set.ncard_lt_ncard ⟨hsubset, hnotsub⟩
    exact ne_of_gt hlt

private noncomputable def innerPsiL {F : Type} [Field F] {I : Type} [CommGroup I]
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F)) (x : SL(2, F)) :
    Multiplicative F →* ↥L :=
  φ.symm.toMonoidHom.comp
    ((MulAut.conj x).toMonoidHom.comp (CFSG.SL2MinimalFaithful.unipotentHom (F := F)))

private noncomputable def innerPsi {F : Type} [Field F] {I : Type} [CommGroup I]
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F)) (x : SL(2, F)) :
    Multiplicative F →* MulAut I :=
  L.subtype.comp (innerPsiL φ x)

private theorem innerPsiL_apply {F : Type} [Field F] {I : Type} [CommGroup I]
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F)) (x : SL(2, F))
    (t : Multiplicative F) :
    innerPsiL φ x t = φ.symm (x * uElt (Multiplicative.toAdd t) * x⁻¹) := by
  simp only [innerPsiL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rfl

private theorem innerPsi_injective {F : Type} [Field F] {I : Type} [CommGroup I]
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F)) (x : SL(2, F)) :
    Function.Injective (innerPsi φ x) := by
  intro s t h
  have h1 : (innerPsiL φ x s : MulAut I) = (innerPsiL φ x t : MulAut I) := h
  have h2 : innerPsiL φ x s = innerPsiL φ x t := Subtype.ext h1
  have h3 : φ (innerPsiL φ x s) = φ (innerPsiL φ x t) := congrArg _ h2
  rw [innerPsiL_apply, innerPsiL_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
  have h4 : uElt (Multiplicative.toAdd s) = uElt (Multiplicative.toAdd t) :=
    mul_left_cancel (mul_right_cancel h3)
  exact Multiplicative.toAdd.injective (uElt_injective h4)

private lemma natCard_fixV {F : Type} [Field F] [Fintype F] [CharP F 2]
    {I : Type} [CommGroup I] [Finite I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (θ : I ≃* Multiplicative W) {L : Subgroup (MulAut I)}
    (φ : ↥L ≃* SL(2, F)) (x : SL(2, F)) (C : AddSubgroup F) :
    Nat.card (fixV (C.toSubgroup.map (innerPsi φ x))) =
      Nat.card {w : W // ∀ t ∈ C, B45L2.repOf θ φ (uElt t) w = w} := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun v => ⟨(B45L2.repOf θ φ) x⁻¹ (Multiplicative.toAdd (θ v.1)),
        fun t ht => ?_⟩
      invFun := fun w =>
        ⟨θ.symm (Multiplicative.ofAdd ((B45L2.repOf θ φ) x w.1)), fun a ha => ?_⟩
      left_inv := fun v => ?_
      right_inv := fun w => ?_ }
  · have hv : ((innerPsiL φ x (Multiplicative.ofAdd t) : ↥L) : MulAut I) v.1 = v.1 :=
      v.2 (innerPsi φ x (Multiplicative.ofAdd t))
        ⟨Multiplicative.ofAdd t,
          (Multiplicative.mem_toSubgroup C (Multiplicative.ofAdd t)).mpr ht, rfl⟩
    have hv' : Multiplicative.toAdd
        (θ (((innerPsiL φ x (Multiplicative.ofAdd t) : ↥L) : MulAut I) v.1)) =
        Multiplicative.toAdd (θ v.1) := by rw [hv]
    have hx1 : φ (innerPsiL φ x (Multiplicative.ofAdd t)) = x * uElt t * x⁻¹ := by
      rw [innerPsiL_apply, MulEquiv.apply_symm_apply]
      rfl
    have h1 : (B45L2.repOf θ φ) (x * uElt t * x⁻¹) (Multiplicative.toAdd (θ v.1)) =
        Multiplicative.toAdd (θ v.1) := by
      have h2 : (B45L2.repOf θ φ) (φ (innerPsiL φ x (Multiplicative.ofAdd t)))
          (Multiplicative.toAdd (θ v.1)) = Multiplicative.toAdd (θ v.1) := by
        rw [B45L2.repOf_theta, B42L2.toAdd_binPsi]
        exact hv'
      rwa [hx1] at h2
    rw [← Module.End.mul_apply, ← map_mul (B45L2.repOf θ φ),
      show uElt t * x⁻¹ = x⁻¹ * (x * uElt t * x⁻¹) by group,
      map_mul (B45L2.repOf θ φ), Module.End.mul_apply, h1]
  · obtain ⟨s, hs, rfl⟩ := ha
    have hs' : Multiplicative.toAdd s ∈ C := (Multiplicative.mem_toSubgroup C s).mp hs
    have hx1 : φ (innerPsiL φ x s) = x * uElt (Multiplicative.toAdd s) * x⁻¹ := by
      rw [innerPsiL_apply, MulEquiv.apply_symm_apply]
    have hv : Multiplicative.toAdd
        (θ (θ.symm (Multiplicative.ofAdd ((B45L2.repOf θ φ) x w.1)))) =
        (B45L2.repOf θ φ) x w.1 := by
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h1 : ((innerPsiL φ x s : ↥L) : MulAut I)
        (θ.symm (Multiplicative.ofAdd ((B45L2.repOf θ φ) x w.1))) =
        θ.symm (Multiplicative.ofAdd ((B45L2.repOf θ φ) x w.1)) := by
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [← B42L2.toAdd_binPsi, ← B45L2.repOf_theta (θL := φ), hx1, hv]
      change ((B45L2.repOf θ φ) (x * uElt (Multiplicative.toAdd s) * x⁻¹))
        ((B45L2.repOf θ φ) x w.1) = (B45L2.repOf θ φ) x w.1
      rw [← Module.End.mul_apply, ← map_mul (B45L2.repOf θ φ),
        show (x * uElt (Multiplicative.toAdd s) * x⁻¹) * x =
          x * uElt (Multiplicative.toAdd s) by group,
        map_mul (B45L2.repOf θ φ), Module.End.mul_apply, w.2 (Multiplicative.toAdd s) hs']
    exact h1
  · apply Subtype.ext
    apply θ.injective
    rw [MulEquiv.apply_symm_apply, ← Module.End.mul_apply, ← map_mul (B45L2.repOf θ φ),
      mul_inv_cancel, map_one, Module.End.one_apply]
    rfl
  · apply Subtype.ext
    show (B45L2.repOf θ φ) x⁻¹
      (Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd ((B45L2.repOf θ φ) x w.1))))) =
      w.1
    rw [MulEquiv.apply_symm_apply]
    change (B45L2.repOf θ φ) x⁻¹ ((B45L2.repOf θ φ) x w.1) = w.1
    rw [← Module.End.mul_apply, ← map_mul (B45L2.repOf θ φ), inv_mul_cancel, map_one,
      Module.End.one_apply]

theorem not_mem_aSet_three_of_le {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 6) {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (θ : I ≃* Multiplicative W)
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F)) [Fact (B45L2.repOf θ φ).IsIrreducible]
    (hD : SixtyFourDescent (B45L2.repOf θ φ)) (X : Subgroup (MulAut I))
    (A : Subgroup (MulAut I)) (hAL : A ≤ L) : A ∉ E3.aSet 3 X := by
  classical
  rintro ⟨hAX, hAne, hAe, hAfix⟩
  have hfixbot : fixV (⊥ : Subgroup (MulAut I)) = ⊤ :=
    eq_top_iff.mpr fun v _ y hy => by simp [Subgroup.mem_bot.mp hy]
  have hfixA_ne : fixV A ≠ ⊤ := by
    intro htop
    apply hAne
    refine le_antisymm (fun a ha => ?_) bot_le
    rw [Subgroup.mem_bot]
    apply MulEquiv.ext
    intro v
    have hv : v ∈ fixV A := by rw [htop]; exact Subgroup.mem_top v
    exact (mem_fixV.mp hv) a ha
  set A₁ : Subgroup SL(2, F) := (A.subgroupOf L).map φ.toMonoidHom with hA₁
  have hA₁2 : ∀ g ∈ A₁, g * g = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    have hl2 : (l : MulAut I) * (l : MulAut I) = 1 := by
      have h := hAe.2 (l : MulAut I) hl
      rwa [pow_two] at h
    have hl2' : (l : ↥L) * l = 1 := Subtype.ext hl2
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, hl2', map_one]
  obtain ⟨x, hx⟩ := exists_conj_le_rootGroup A₁ hA₁2
  let A₀ : AddSubgroup F :=
    { carrier := {t : F | x * uElt t * x⁻¹ ∈ A₁}
      zero_mem' := by
        show x * uElt 0 * x⁻¹ ∈ A₁
        rw [uElt_zero]
        simpa using A₁.one_mem
      add_mem' := fun {s t} hs ht => by
        show x * uElt (s + t) * x⁻¹ ∈ A₁
        have h1 : x * uElt (s + t) * x⁻¹ =
            (x * uElt s * x⁻¹) * (x * uElt t * x⁻¹) := by
          rw [uElt_add]; group
        rw [h1]
        exact A₁.mul_mem hs ht
      neg_mem' := fun {t} ht => by
        rw [CharTwo.neg_eq]
        exact ht }
  have hA₀mem : ∀ t : F, t ∈ A₀ ↔ x * uElt t * x⁻¹ ∈ A₁ := fun _ => Iff.rfl
  have hAmap : A₀.toSubgroup.map (innerPsi φ x) = A := by
    ext a
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : x * uElt (Multiplicative.toAdd t) * x⁻¹ ∈ A₁ :=
        (hA₀mem _).mp ((Multiplicative.mem_toSubgroup A₀ t).mp ht)
      obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp h1
      have h2 : innerPsiL φ x t = l := φ.injective (by
        rw [innerPsiL_apply, MulEquiv.apply_symm_apply]
        exact hle.symm)
      have h3 : innerPsi φ x t = (l : MulAut I) := by
        show ((innerPsiL φ x t : ↥L) : MulAut I) = (l : MulAut I)
        rw [h2]
      rw [h3]
      exact hl
    · intro ha
      have haL : a ∈ L := hAL ha
      have hA₁a : φ ⟨a, haL⟩ ∈ A₁ := ⟨⟨a, haL⟩, ha, rfl⟩
      obtain ⟨t, ht⟩ := (mem_rootGroup_iff _).mp (hx _ hA₁a)
      refine ⟨Multiplicative.ofAdd t, (Multiplicative.mem_toSubgroup A₀ _).mpr ?_, ?_⟩
      · rw [hA₀mem]
        show x * uElt t * x⁻¹ ∈ A₁
        rwa [← ht, show x * (x⁻¹ * φ ⟨a, haL⟩ * x) * x⁻¹ = φ ⟨a, haL⟩ by group]
      · show ((innerPsiL φ x (Multiplicative.ofAdd t) : ↥L) : MulAut I) = a
        have h3 : innerPsiL φ x (Multiplicative.ofAdd t) = ⟨a, haL⟩ := φ.injective (by
          rw [innerPsiL_apply, MulEquiv.apply_symm_apply]
          show x * uElt t * x⁻¹ = φ ⟨a, haL⟩
          rwa [← ht, show x * (x⁻¹ * φ ⟨a, haL⟩ * x) * x⁻¹ = φ ⟨a, haL⟩ by group])
        rw [h3]
  have hA₀card : Nat.card A₀ = Nat.card A := by
    rw [← hAmap, Subgroup.card_map_of_injective (innerPsi_injective φ x),
      CFSG.Quasithin.B513N.card_toSubgroup]
  have hAp : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hAe
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hAp
  by_cases hsmall : Nat.card A ≤ 4
  · have hk2 : k ≤ 2 := by
      have h : 2 ^ k ≤ 4 := by rw [← hk]; exact hsmall
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at h
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    have hm : E3.mQuot A ⊥ < 3 := by
      show padicValNat 2 ((⊥ : Subgroup (MulAut I)).relIndex A) < 3
      rw [Subgroup.relIndex_bot_left, hk, padicValNat.prime_pow]
      omega
    exact hfixA_ne (by rw [← hAfix ⊥ bot_le hm]; exact hfixbot)
  · have hk3 : 3 ≤ k := by
      have h : 4 < 2 ^ k := by rw [← hk]; omega
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at h
      have h' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
      omega
    have h8 : 8 ≤ Nat.card A₀ := by
      rw [hA₀card, hk]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    obtain ⟨B₀, hB₀le, hB₀card, hB₀ne⟩ :=
      exists_fixW_ne hF (B45L2.repOf θ φ) hD A₀ h8
    set B : Subgroup (MulAut I) := B₀.toSubgroup.map (innerPsi φ x) with hB
    have hBA : B ≤ A := by
      rw [hB, ← hAmap]
      exact Subgroup.map_mono hB₀le
    have hcardB : Nat.card B = Nat.card B₀ := by
      rw [hB, Subgroup.card_map_of_injective (innerPsi_injective φ x),
        CFSG.Quasithin.B513N.card_toSubgroup]
    have hm : E3.mQuot A B < 3 := by
      have hrel : B.relIndex A * Nat.card B = Nat.card A := by
        have h := Subgroup.relIndex_mul_card (H := B) (K := A)
        rwa [inf_eq_left.mpr hBA] at h
      have hle : B.relIndex A ≤ 4 := by
        have h1 : B.relIndex A * Nat.card B ≤ 4 * Nat.card B := by
          calc B.relIndex A * Nat.card B = Nat.card A := hrel
            _ = Nat.card A₀ := hA₀card.symm
            _ ≤ 4 * Nat.card B₀ := hB₀card
            _ = 4 * Nat.card B := by rw [hcardB]
        exact Nat.le_of_mul_le_mul_right h1 (Nat.card_pos (α := B))
      have hdvd : B.relIndex A ∣ 2 ^ k := ⟨Nat.card B, (hrel.trans hk).symm⟩
      obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hj2 : j ≤ 2 := by
        have h : 2 ^ j ≤ 4 := by rw [← hje]; exact hle
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at h
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
      show padicValNat 2 (B.relIndex A) < 3
      rw [hje, padicValNat.prime_pow]
      omega
    have hBcount : Nat.card (fixV B) =
        Nat.card {w : W // ∀ t ∈ B₀, B45L2.repOf θ φ (uElt t) w = w} := by
      rw [hB]
      exact natCard_fixV θ φ x B₀
    have hAcount : Nat.card (fixV A) =
        Nat.card {w : W // ∀ t ∈ A₀, B45L2.repOf θ φ (uElt t) w = w} := by
      rw [← hAmap]
      exact natCard_fixV θ φ x A₀
    have hfixne : fixV B ≠ fixV A :=
      fun heq => hB₀ne (by rw [← hBcount, ← hAcount, heq])
    exact hfixne (hAfix B hBA hm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
