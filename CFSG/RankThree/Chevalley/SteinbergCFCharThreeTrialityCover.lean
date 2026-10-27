module

public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2OddField
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.RankThree.CentralCover CFSG.RankThree.Classical2 CFSG.Assembly
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

theorem two_field_prime_witness {G : Type*} [Group G] [Finite G] (Y : Subgroup G) {H : Type*}
    [Group H] {φ : Y →* H} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K₁ K₂ : Type*} [Field K₁] [Fintype K₁] [Field K₂]
    [Fintype K₂] {f₁ : ℕ} (hK₁ : Fintype.card K₁ = p ^ f₁) (hK₁3 : 3 < p ^ f₁)
    (hK₁9 : p ^ f₁ ≠ 9) (hK₂ : Fintype.card K₂ = p) (ι₁ : SL(2, K₁) →* H) (ι₂ : SL(2, K₂) →* H)
    (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂)
    (hcomm : ∀ A B, ι₁ A * ι₂ B = ι₂ B * ι₁ A) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ (f₁ + 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hc₁ : CharP K₁ p := charP_of_card_eq_prime_pow hK₁
  have hc₂ : CharP K₂ p := charP_of_card_eq_prime_pow (by rw [hK₂, pow_one])
  set x₁ : Multiplicative K₁ →* H := ι₁.comp (sl2UpperHom K₁) with hx₁
  set x₂ : Multiplicative K₂ →* H := ι₂.comp (sl2UpperHom K₂) with hx₂
  have hx₁app : ∀ c : K₁, x₁ (.ofAdd c) = ι₁ (sl2Upper c) := fun _ => rfl
  have hx₂app : ∀ c : K₂, x₂ (.ofAdd c) = ι₂ (sl2Upper c) := fun _ => rfl
  have hscale : ∀ (a : K₁ˣ) (c : K₁), ι₁ (sl2Diag a) * x₁ (.ofAdd c) * (ι₁ (sl2Diag a))⁻¹ =
      x₁ (.ofAdd ((a : K₁) ^ 2 * c)) := fun a c => by
    rw [hx₁app, hx₁app, ← map_inv, ← map_mul, ← map_mul, sl2Diag_conj_upper]
  have hx₁inj : Function.Injective x₁ := h₁.comp sl2UpperHom_injective
  have hx₂inj : Function.Injective x₂ := h₂.comp sl2UpperHom_injective
  have hab₁ : ∀ a b, Commute (x₁ a) (x₁ b) := fun a b => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hab₂ : ∀ a b, Commute (x₂ a) (x₂ b) := fun a b => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have h12 : ∀ a b, Commute (x₁ a) (x₂ b) := fun a b => hcomm _ _
  set S : Set H := Set.range x₁ ∪ Set.range x₂ with hS
  have hSc : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩) _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact hab₁ a b
    · exact h12 a b
    · exact (h12 b a).symm
    · exact hab₂ a b
  obtain ⟨lam, hlam⟩ := exists_unit_sq_ne_one (K := K₁)
    (by rw [Nat.card_eq_fintype_card, hK₁]; exact hK₁3)
  have hmixed : ∀ (a : Multiplicative K₁) (b : Multiplicative K₂),
      liftComm φ hφ (x₁ a) (x₂ b) = 1 := fun a b => by
    have := liftComm_eq_one_of_scale hφ hker x₁ (fun _ => h12 _ b) hlam (hscale lam)
      (by rw [show x₂ b = ι₂ (sl2UpperHom K₂ b) from rfl, hcomm, mul_inv_cancel_right])
      (Multiplicative.toAdd a)
    rwa [ofAdd_toAdd] at this
  have hK₂gen : ∀ b : Multiplicative K₂, x₂ b ∈ Subgroup.closure {x₂ (.ofAdd 1)} := by
    intro b
    set g : ZMod p →+* K₂ := ZMod.castHom (dvd_refl p) K₂
    have hbij : Function.Bijective g :=
      g.injective.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card, hK₂, Nat.card_zmod])
    obtain ⟨n, hn⟩ := hbij.2 (Multiplicative.toAdd b)
    have hb : b = (Multiplicative.ofAdd (1 : K₂)) ^ n.val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, ← hn, ZMod.castHom_apply,
        ZMod.cast_eq_val]
    rw [hb, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_singleton _)) _
  have hpair : ∀ s ∈ S, ∀ t ∈ S, liftComm φ hφ s t = 1 := by
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩) _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · have := liftComm_eq_one_of_square_invariant hφ hker hp2
        (by rw [Nat.card_eq_fintype_card, hK₁]) hK₁9 x₁ (fun a => ι₁ (sl2Diag a)) hscale
        (Multiplicative.toAdd a) (Multiplicative.toAdd b)
      rwa [ofAdd_toAdd, ofAdd_toAdd] at this
    · exact hmixed a b
    · rw [liftComm_swap, hmixed b a, inv_one]
    · exact liftComm_eq_one_of_mem_closure hφ hker
        (fun s hs t ht => by rw [Set.mem_singleton_iff.1 hs, Set.mem_singleton_iff.1 ht])
        (fun s hs t ht => by
          rw [Set.mem_singleton_iff.1 hs, Set.mem_singleton_iff.1 ht]
          exact liftComm_self hφ _) (hK₂gen a) (hK₂gen b)
  have hF := comap_closure_comm hφ hker hSc hpair
  have hSp : ∀ s ∈ S, s ^ p = 1 := by
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · rw [← map_pow, show a ^ p = 1 from Multiplicative.toAdd.injective (by
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]), map_one]
    · rw [← map_pow, show a ^ p = 1 from Multiplicative.toAdd.injective (by
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]), map_one]
  have hDp : ∀ d ∈ Subgroup.closure S, d ^ p = 1 := fun d hd =>
    pow_eq_one_of_mem_closure hSc hSp hd
  set R : Fin 2 → Subgroup H := ![x₁.range, x₂.range] with hR
  have hRS : ∀ i (a : H), a ∈ R i → a ∈ S := by
    intro i a ha
    fin_cases i
    · exact Or.inl ha
    · exact Or.inr ha
  have hcommR : Pairwise fun i j => ∀ a b : H, a ∈ R i → b ∈ R j → Commute a b :=
    fun i j _ a b ha hb => hSc a (hRS i a ha) b (hRS j b hb)
  have hcl : Subgroup.closure S = ⨆ i, R i := by
    refine le_antisymm ((Subgroup.closure_le _).2 fun s hs => ?_) (iSup_le fun i => ?_)
    · rcases hs with hs | hs
      · exact (le_iSup R 0) hs
      · exact (le_iSup R 1) hs
    · intro y hy
      exact Subgroup.subset_closure (hRS i y hy)
  have hdisj : Disjoint x₁.range x₂.range := by
    rw [Subgroup.disjoint_def]
    rintro y ⟨a, rfl⟩ ⟨b, hb⟩
    have hfix : ι₁ (sl2Diag lam) * x₂ b * (ι₁ (sl2Diag lam))⁻¹ = x₂ b := by
      rw [show x₂ b = ι₂ (sl2UpperHom K₂ b) from rfl, hcomm, mul_inv_cancel_right]
    have h1 := hscale lam (Multiplicative.toAdd a)
    rw [ofAdd_toAdd, ← hb, hfix, hb] at h1
    have h2 := hx₁inj h1
    have h3 : ((lam : K₁) ^ 2 - 1) * Multiplicative.toAdd a = 0 := by
      have := congrArg Multiplicative.toAdd h2
      simp only [toAdd_ofAdd] at this
      rw [sub_mul, one_mul, ← this, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) hlam
    · rw [show a = 1 from Multiplicative.toAdd.injective (h4.trans toAdd_one.symm), map_one]
  have hind : iSupIndep R := (iSupIndep_pair (by decide : (0 : Fin 2) ≠ 1)
    (fun k => by fin_cases k <;> simp)).2 (by simpa [hR] using hdisj)
  have hcard : Nat.card (Subgroup.closure S) = p ^ (f₁ + 1) := by
    rw [hcl, card_iSup_eq_prod hcommR hind, Fin.prod_univ_two]
    simp only [hR, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Nat.card_congr (MonoidHom.ofInjective hx₁inj).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hx₂inj).toEquiv]
    change Nat.card K₁ * Nat.card K₂ = _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hK₁, hK₂, pow_succ]
  have hK₁2 : ringChar K₁ ≠ 2 := by
    rw [ringChar.eq K₁ p]
    exact hp2
  have hz : orderOf (ι₁ (sl2Diag (-1))) = 2 := by
    rw [orderOf_injective _ h₁, orderOf_sl2Diag_neg_one hK₁2]
  have hzS : ∀ s ∈ S, Commute (ι₁ (sl2Diag (-1))) s := by
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact (sl2Diag_neg_one_commute _).map ι₁
    · exact hcomm _ _
  have hzD : ∀ d ∈ Subgroup.closure S, Commute (ι₁ (sl2Diag (-1))) d := by
    intro d hd
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {ι₁ (sl2Diag (-1))} :=
      (Subgroup.closure_le _).2 fun s hs =>
        Subgroup.mem_centralizer_singleton_iff.2 (hzS s hs).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hd)).symm
  obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -⟩ :=
    central_cover_involution_witness Y hφ hker hp hp2 hDp hF hcard.ge hz hzD
  exact ⟨u, huY, hu, A, hA, hAab, hAcard⟩

theorem exists_elemAbelian_le_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {V : Subgroup G} (hV : IsElemAbelian p V) {r s : ℕ} (hVcard : Nat.card V = p ^ r)
    (hsr : s ≤ r) : ∃ W ≤ V, IsElemAbelian p W ∧ Nat.card W = p ^ s := by
  obtain ⟨W, hW, -, hWV⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (H := ⊥) (L := V) (n := s) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hVcard]; exact pow_dvd_pow p hsr) bot_le
  refine ⟨W, hWV, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hV.2 x (hWV hx)⟩, hW⟩
  have h := congrArg Subtype.val (hV.1.is_comm.comm (⟨a, hWV a.2⟩ : V) ⟨b, hWV b.2⟩)
  exact h

theorem characteristic_three_triality_actual_central_cover_local_rank_four {X : Type} [Group X]
    [Finite X] (Y : Subgroup X) {f : ℕ}
    (hmod : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .trialityD4 3 f) :
    (∃ u ∈ Y, orderOf u = 2 ∧ ∃ V : Subgroup X, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian 3 V ∧ Nat.card V = 3 ^ 4) ∧
      4 ≤ localRank 3 X ∧ 4 ≤ CFSG.twoLocalOddRank X := by
  classical
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
  have hK' : Nat.card K = (3 ^ f) ^ 3 := hK
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨e'⟩ := nonempty_derivedCentralQuotient_equiv .D4 Nat.prime_three hf K hK' σ hσ
  obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_of_equiv' (e.trans e')
  obtain ⟨σ', hσ', -, -, -, k, hk, hkcard, -⟩ :=
    finite_graph_field_parameter_fields .D4 Nat.prime_three hf K hK'
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    change σ' c = σ c
    rw [hσ', hσ]
  have h3 : σ' ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ' (σ' (σ' c)) = c
    rw [hσ', hσ', hσ', ← pow_mul, ← pow_mul,
      show 3 ^ f * (3 ^ f * 3 ^ f) = (3 ^ f) ^ 3 by ring, ← hK', Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hfix : fixSubfield σ' = k := SetLike.ext' (by
    rw [hk]
    ext c
    change σ' c = c ↔ c ^ (3 ^ f) = c
    rw [hσ'])
  have hkcard' : Fintype.card (fixSubfield σ') = 3 ^ f := by
    rw [← Nat.card_eq_fintype_card, hfix, hkcard]
  have hKcard : Fintype.card K = 3 ^ (3 * f) := by
    rw [← Nat.card_eq_fintype_card, hK', ← pow_mul, mul_comm]
  subst hσσ'
  obtain ⟨ι, η, hι, hη, hcomm⟩ := triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ' h3
  have hV : ∃ u ∈ Y, orderOf u = 2 ∧ ∃ V : Subgroup X, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian 3 V ∧ Nat.card V = 3 ^ 4 := by
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · obtain ⟨u, huY, hu, A, hA, hAab, hAcard⟩ := two_field_prime_witness Y hφ hker
        Nat.prime_three (by norm_num) (f₁ := 3) (by rw [hKcard]) (by norm_num) (by norm_num)
        (by rw [hkcard', pow_one]) ι η hι hη hcomm
      exact ⟨u, huY, hu, A, hA, hAab, hAcard⟩
    · have h27 : 3 ^ 6 ≤ 3 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      obtain ⟨u, huY, hu, V, hVle, hVab, hVcard, -⟩ :=
        commuting_SL2_odd_field_actual_central_cover_local_rank Y Nat.prime_three (by norm_num)
          (by omega : 1 ≤ 3 * f) (by norm_num : 1 ≤ 1) hKcard (by omega)
          (fun h => by rw [h] at h27; norm_num at h27) φ hφ hker ![ι] (fun i => by
            fin_cases i
            exact hι) (fun i j hij => absurd (Subsingleton.elim i j) hij)
      obtain ⟨W, hWV, hWab, hWcard⟩ := exists_elemAbelian_le_of_le Nat.prime_three hVab hVcard
        (show 4 ≤ 1 * (3 * f) by omega)
      exact ⟨u, huY, hu, W, hWV.trans hVle, hWab, hWcard⟩
  obtain ⟨u, huY, hu, V, hVle, hVab, hVcard⟩ := hV
  have hrank : 4 ≤ localRank 3 X :=
    le_localRank_of_involution_elemAbelian Nat.prime_three hu (hVle.trans inf_le_right) hVab
      hVcard
  have h3X : 3 ∣ Nat.card X :=
    (Dvd.intro_left _ (hVcard.symm.trans (by norm_num))).trans (Subgroup.card_subgroup_dvd_card V)
  exact ⟨⟨u, huY, hu, V, hVle, hVab, hVcard⟩, hrank,
    hrank.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num)
      h3X)⟩

end CFSG.RankThree.Chevalley
