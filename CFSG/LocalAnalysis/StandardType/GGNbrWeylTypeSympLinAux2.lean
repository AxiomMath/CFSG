module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSympLinAux
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24Sp
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24SlNsNorm
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeSigned

public section

namespace CFSG.StandardType

open Matrix Polynomial CoordSL Multiplicative SpCoord CFSG.Assembly TableBSymp
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open SlNsRootGen in
theorem ggWTB2_weylTypeB_projectiveSL {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K + 1) (r : ℕ) :
    GGTorusWeylTypeB (fun k => d < (p - 1) * (k + 1)) p r (projectiveSL d K)
      (Set.range (conjAut d K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  have hpK' : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
      have : 0 < Nat.card K := Nat.card_pos
      omega
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hsub ▸ Nat.dvd_sub hpK hK1))
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hC : (rootMat g).det = 1 := det_rootMat hp hpK' hpK0 hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK0 hgd
  have hζ : AdjoinRoot.root g ^ p = 1 := (root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1) :=
    isUnit_rootMat_pow_sub hp hpK' hpK0 hgd
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  obtain ⟨s, r', ε, φ, hφs, hφc, hs3, hM⟩ :=
    exists_isBlockTorusModel hp hp2 hpK hgd hC hψ hker hperf hAe hAI h3 hsc
  have hpow : ∀ u : Fin s → ZMod p, torusSL ε hC hCp (ofAdd u) ^ p = 1 := by
    intro u
    have hu : p • u = 0 := by
      funext i
      simp
    rw [← map_pow, ← ofAdd_nsmul, hu, ofAdd_zero, map_one]
  have hcen : ∀ a b : SpecialLinearGroup (Fin d) K, a ^ p = 1 → b ^ p = 1 →
      MulAut.conj (φ a) = MulAut.conj (φ b) → a = b := by
    intro a b hap hbp h
    have hz : a * b⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
      refine hφc _ (Subgroup.mem_center_iff.mpr fun y => ?_)
      have h2 : MulAut.conj (φ (a * b⁻¹)) y = y := by
        rw [map_mul, map_inv, map_mul, map_inv, h, mul_inv_cancel]
        rfl
      rw [MulAut.conj_apply] at h2
      calc y * φ (a * b⁻¹) = φ (a * b⁻¹) * y * (φ (a * b⁻¹))⁻¹ * φ (a * b⁻¹) := by rw [h2]
        _ = φ (a * b⁻¹) * y := by group
    have hc : Commute a b⁻¹ := by
      have h1 := Subgroup.mem_center_iff.mp hz b
      calc a * b⁻¹ = b⁻¹ * (b * (a * b⁻¹)) := by group
        _ = b⁻¹ * (a * b⁻¹ * b) := by rw [h1]
        _ = b⁻¹ * a := by group
    have hzp : (a * b⁻¹) ^ p = 1 := by
      rw [hc.mul_pow, hap, inv_pow, hbp, inv_one, one_mul]
    obtain ⟨c, -, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    rw [← mul_inv_eq_one]
    ext i j
    have h1 := congrArg (fun y : SpecialLinearGroup (Fin d) K =>
      ((SpecialLinearGroup.toGL y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) hzp
    simp only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one, one_apply_eq] at h1
    have h3 : ((SpecialLinearGroup.toGL (a * b⁻¹) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = scalar (Fin d) c := hcz.symm
    rw [h3, ← map_pow, scalar_apply, diagonal_apply_eq] at h1
    rw [← hcz, OrdPNS.eq_one_of_pow_eq_one hp hpK' h1, map_one]
    rfl
  set Θ : (Fin s → Multiplicative (ZMod p)) ≃* ↥A :=
    (MulEquiv.piMultiplicative fun _ : Fin s => ZMod p).symm.trans
      (torusEquiv hCp hM hφc hunit)
  have hΘapp : ∀ f, ((Θ f : ↥A) : MulAut L') =
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd fun i => toAdd (f i)))) := fun f =>
    coe_torusEquiv hCp hM hφc hunit _
  have hgen : ∀ (w : SpecialLinearGroup (Fin d) K) (F : (Fin s → ZMod p) → Fin s → ZMod p)
      (α : MulAut (Fin s → Multiplicative (ZMod p))),
      (∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (F t))) →
      Function.Surjective F → (∀ t, F (F t) = t) → Nat.card {t // F t = t} * p = p ^ s →
      (∀ f, (fun i => toAdd (α f i)) = F fun i => toAdd (f i)) →
      MulAut.congr Θ α ∈ ggTorusReflSet p A := by
    intro w F α hw hFs hF2 hfix hαF
    have hn := conj_mem_normalizer_of_conj hM hw hFs
    have heq : ggConjAut A hn = MulAut.congr Θ α := by
      refine MulEquiv.ext fun b => ?_
      obtain ⟨f, rfl⟩ := Θ.surjective b
      have h2 : MulAut.congr Θ α (Θ f) = Θ (α f) := by
        rw [MulAut.congr_apply]
        exact congrArg Θ (congrArg α (Θ.symm_apply_apply f))
      rw [h2]
      have h1 := ggConjAut_torusEquiv hM hφc hunit hw hn fun i => toAdd (f i)
      rw [← hαF] at h1
      exact h1
    rw [← heq]
    exact ⟨φ w, hn, ggTorusWeylElt_of_conj hM hw, rfl,
      isReflection_of_conj hM hφc hunit hw hn hF2 hfix⟩
  have hsH : ∀ i, MulAut.congr Θ (sgnAut i) ∈ ggTorusReflSet p A := by
    intro i
    obtain ⟨w, -, hw⟩ := exists_neg_mem_zeroBlock ε hC hCp hζ hpK i
    refine hgen w _ _ hw (negMap_surjective i) (negMap_negMap i) (card_fixed_negMap hp2 i)
      fun f => ?_
    funext k
    by_cases hk : k = i
    · subst hk
      simp [sgnAut_apply, negMap]
    · simp [sgnAut_apply, negMap, Function.update_of_ne hk]
  have htH : ∀ a b : Fin s, a ≠ b →
      MulAut.congr Θ (permAut (Equiv.swap a b)) ∈ ggTorusReflSet p A := by
    intro a b hab
    obtain ⟨w, -, hw⟩ := exists_swap_mem_pairBlock ε hC hCp a b
    refine hgen w _ _ hw (swapMap_surjective a b) (swapMap_swapMap a b) (card_fixed_swapMap hab)
      fun f => ?_
    funext k
    simp [permAut_apply, swapMap, Equiv.swap_inv]
  have hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)) := by
    intro n hn
    obtain ⟨x, rfl⟩ := hφs n
    have hconj : ∀ t t' : Fin s → ZMod p,
        MulAut.conj (φ x) * MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) *
          (MulAut.conj (φ x))⁻¹ =
          MulAut.conj (φ (torusSL ε hC hCp (ofAdd t'))) →
        x * torusSL ε hC hCp (ofAdd t) * x⁻¹ = torusSL ε hC hCp (ofAdd t') := by
      intro t t' h
      refine hcen _ _ (by rw [conj_pow, hpow, mul_one, mul_inv_cancel]) (hpow t') ?_
      rw [← h]
      simp only [map_mul, map_inv]
    have hx : ∀ t, ∃ t', x * torusSL ε hC hCp (ofAdd t) * x⁻¹ =
        torusSL ε hC hCp (ofAdd t') := by
      intro t
      have hmem := (Subgroup.mem_normalizer_iff.mp hn
        (MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))))).mp ((hM.mem_iff hCp).mpr ⟨t, rfl⟩)
      obtain ⟨t', ht'⟩ := (hM.mem_iff hCp).mp hmem
      exact ⟨t', hconj t t' ht'⟩
    obtain ⟨π, σ, hσ, hrel⟩ := exists_signedPerm_of_conj hpK hgd ε hC hCp x hx
    refine ⟨π, σ, hσ, fun f i => ?_⟩
    refine hrel (fun i => toAdd (f i))
      (fun i => toAdd ((MulAut.congr Θ).symm (ggConjAut A hn) f i)) (hconj _ _ ?_) i
    have h1 : ((ggConjAut A hn (Θ f) : ↥A) : MulAut L') =
        ((Θ ((MulAut.congr Θ).symm (ggConjAut A hn) f) : ↥A) : MulAut L') :=
      congrArg Subtype.val (Θ.apply_symm_apply (ggConjAut A hn (Θ f))).symm
    rw [ggConjAut_apply, hΘapp, hΘapp] at h1
    exact h1
  have hbound : d < (p - 1) * (s + 1) := by
    have hns : ∀ c : K,
        rootMat g ≠ c • (1 : Matrix (Fin (rootPB g).dim) (Fin (rootPB g).dim) K) := by
      intro c hc
      have h1 := hunit 1 hp.not_dvd_one c
      rw [pow_one, hc, sub_self] at h1
      have : Nonempty (Fin (rootPB g).dim) := ⟨⟨0, rootPB_dim_pos g⟩⟩
      exact not_isUnit_zero h1
    have hr := hM.fixed_lt_dim hCp hns hφc hsc
    have hd : d = (rootPB g).dim * s + r' := by
      simpa [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, mul_comm] using
        Fintype.card_congr ε
    have hdim : (rootPB g).dim ≤ p - 1 := by
      calc (rootPB g).dim = g.natDegree := AdjoinRoot.powerBasis_dim _
        _ ≤ (cyclotomic p K).natDegree := natDegree_le_of_dvd hgd (cyclotomic_ne_zero p K)
        _ = p - 1 := by rw [natDegree_cyclotomic, Nat.totient_prime hp]
    calc d = (rootPB g).dim * s + r' := hd
      _ < (rootPB g).dim * (s + 1) := by rw [mul_add, mul_one]; omega
      _ ≤ (p - 1) * (s + 1) := Nat.mul_le_mul_right _ hdim
  exact ⟨s, hs3, hbound, ggWTB2_coxeterB_of_reflModel hp hp2 hs3 Θ hsH htH hN⟩

theorem ggWTB2_largeEvenLabelAll_weylTypeW_spNonsplit
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGSpNonsplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have : NeZero l := ⟨by omega⟩
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have : Finite (LargeEvenSpGroup K l) := Subtype.finite
    have : Finite (LargeEvenProj (LargeEvenSpGroup K l)) :=
      Finite.of_equiv _ (spProjEquivSp (K := K) (m := l)).symm.toEquiv
    have h2 : 2 ∣ Nat.card (LargeEvenProj (LargeEvenSpGroup K l)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let i₀ : Fin l := ⟨0, by omega⟩
      rcases (spRootGroup_isPGroup (K := K) i₀).card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) (spRootGroup_ne_bot i₀)
      · exact h1.trans (Subgroup.card_subgroup_dvd_card _)
    obtain ⟨hT, hcp⟩ := ggSpNonsplitTorusInput_holds K l p hl2 hp hpK
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 0, TypeA.ggTorusLift_zero h2,
      ggTorusWeylTypeW_of_signedEltSC hp hp2 center_spProj_eq_bot
        (fun φ hφ _ => sp_I_subset_inn hφ) hcp hT⟩

theorem ggWTB2_largeEvenLabelAll_weylTypeB_linearNs {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      GGTorusWeylTypeB (fun k => lab.rank + 1 < (p - 1) * (k + 1)) p r R I := by
  intro Q hQ
  obtain ⟨tag, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  subst htag
  have hl1 : 1 ≤ l := hlab.2.1
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  set e := TypeA.recipeEquiv (l + 1) K
  refine ⟨K, inferInstance, inferInstance, hK, hQ', 0, TypeA.ggTorusLift_of_mulEquiv e
    (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by omega))), ?_⟩
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  refine ggWTB2_weylTypeB_projectiveSL hp hpK 0 L' (e.toMonoidHom.comp ψ) A
    ⟨e.surjective.comp hψ, (TypeA.ker_comp_mulEquiv e ψ).symm ▸ hker, hperf, hAe,
      fun a ha => ?_, hr, h3, hsc⟩
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨MulAut.congr e φ, TypeA.congr_recipeEquiv_mem hφ, fun l' => ?_⟩
  change e (φ (e.symm (e (ψ l')))) = e (ψ (a l'))
  rw [MulEquiv.symm_apply_apply, hφa]

theorem ggWTB2_largeEvenLabelAll_weylTypeW_linearNs {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I :=
  ggNbrLabelAll_mono (fun _ _ _ _ ⟨r, hl, hB⟩ => ⟨r, hl, hB.toWeylTypeW⟩)
    (ggWTB2_largeEvenLabelAll_weylTypeB_linearNs hp hlab h)

end CFSG.StandardType

end
