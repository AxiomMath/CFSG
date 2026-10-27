module

public import CFSG.RankThree.Chevalley.SteinbergCAF4PairTorus
public import CFSG.RankThree.Chevalley.SteinbergCFF4CyclotomicSixWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFF4CyclotomicSixIndex
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups EvenF4QPlus CFSG.Timmesfeld.ExceptionalOrders RootSpace

@[expose] def f4PhiSixPairBasis : F4PairBasis f4PhiSix where
  B := f4PhiSixBasis
  N := f4PhiSixCoord
  ε := 1
  smul_zero := by rw [← weylMatrix_mulVec, weylMatrix_f4PhiSix]; decide
  smul_one := by rw [← weylMatrix_mulVec, weylMatrix_f4PhiSix]; decide
  smul_two := by rw [← weylMatrix_mulVec, weylMatrix_f4PhiSix]; decide
  smul_three := by rw [← weylMatrix_mulVec, weylMatrix_f4PhiSix]; decide
  N_mul := f4PhiSixCoord_mul
  mul_N := mul_f4PhiSixCoord

theorem pow_six_eq_phiSix_mul_add_one {q : ℕ} (hq : 1 ≤ q) :
    q ^ 6 = (q ^ 2 - q + 1) * (q ^ 4 + q ^ 3 - q - 1) + 1 := by
  have h1 : q ≤ q ^ 2 := le_sq_self q
  have h2 : q ≤ q ^ 4 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  have h4 : q + 1 ≤ q ^ 4 + q ^ 3 := by omega
  have h5 : q ≤ q ^ 4 + q ^ 3 := by omega
  have h6 : 1 ≤ q ^ 4 + q ^ 3 - q := by omega
  zify [h1, h5, h6]
  ring

theorem F4_cyclotomic_six_torus_and_surviving_A2_kernels
    (K : Type) [Field K] [Finite K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω)
    (hF : ∀ c, F c = c ^ Nat.card K) (n : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω f4PhiSix) :
    (∀ v : Fin Tag.F4.rank → ℤ, f4PhiSix • v = -((f4Coxeter ^ 4) • v)) ∧
    orderOf f4PhiSix = 6 ∧
    weylMatrix f4PhiSix * weylMatrix f4PhiSix - weylMatrix f4PhiSix + 1 = 0 ∧
    (∃ g ∈ adjointGroup .F4 Ω, g⁻¹ * Units.map (entrywiseHom F) g = n) ∧
    ∀ g ∈ adjointGroup .F4 Ω, g⁻¹ * Units.map (entrywiseHom F) g = n →
    ∀ Γ T₀ T : Subgroup (ModGL .F4 Ω), Γ = conjEntrywiseImage K g⁻¹ →
      T₀ = torusGroup .F4 Ω ⊓ Γ → T = T₀.map (MulAut.conj g).toMonoidHom →
      Γ = adjointGroup .F4 Ω ⊓ (twistedEntrywise n F).eqLocus (MonoidHom.id _) ∧
      Nonempty (T₀ ≃* Multiplicative (ZMod (Nat.card K ^ 2 - Nat.card K + 1)) ×
        Multiplicative (ZMod (Nat.card K ^ 2 - Nat.card K + 1))) ∧
      T ≤ (adjointGroup .F4 K).map (baseChangeGL (algebraMap K Ω)) ∧
      Odd (Nat.card T) ∧
      (∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card K ^ 2 - Nat.card K + 1 →
        (∃ S : Sylow p (adjointGroup .F4 K), (S : Subgroup (adjointGroup .F4 K)).map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) ≤ T) ∧
        (∀ P : Subgroup (adjointGroup .F4 K), IsPGroup p P → ∃ c : adjointGroup .F4 K,
          (P.map (MulAut.conj c).toMonoidHom).map
            ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) ≤ T) ∧
        (∃ V : Subgroup (ModGL .F4 Ω), (∀ h, h ∈ V ↔ h ∈ T₀ ∧ h ^ p = 1) ∧
          Nat.card V = p ^ 2 ∧
          ∃ x ∈ V, x ≠ 1 ∧ {α | IsRoot .F4 α ∧ torusRootChar x α = 1}.Nonempty) ∧
        ∀ x ∈ T₀, orderOf x = p → ∀ R : Set (Fin Tag.F4.rank → ℤ),
          R = {α | IsRoot .F4 α ∧ torusRootChar x α = 1} →
          (R = ∅ ∨ ∃ (u : WeylGroup .F4) (i j : Fin Tag.F4.rank) (ε : ℤ),
            ((i = f4Index 0 ∧ j = f4Index 1) ∨ (i = f4Index 2 ∧ j = f4Index 3)) ∧
            (ε = 1 ∨ ε = -1) ∧
            (fun α => u • α) '' R = parabolicRoots .F4 {i, j} ∧
            ∀ y ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {i, j}),
              weylAct .F4 (u * f4PhiSix * u⁻¹) y =
                -weylAct .F4 ((simple .F4 i * simple .F4 j) ^ ε) y) ∧
          (R = ∅ → Γ ⊓ Subgroup.centralizer {x} = T₀)) ∧
      (CharP K 2 → ∀ K₆ : IntermediateField K Ω, Module.finrank K K₆ = 6 →
        g ∈ (adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ∧
        T₀ ≤ (torusGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ∧
        Γ = (adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ⊓
          (twistedEntrywise n F).eqLocus (MonoidHom.id _)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Finite (Module.End K (RootModule .F4 K)) := Module.finite_of_finite K
  have hbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  set q := Nat.card K with hq
  have hnG : n ∈ adjointGroup .F4 Ω := hn ▸ canonicalRep_mem_adjointGroup _ Ω _
  refine ⟨f4PhiSix_smul, orderOf_f4PhiSix, f4PhiSixMatrix_relation,
    exists_inv_mul_entrywise_eq K F hF .F4 hnG, fun g hg hgn Γ T₀ T hΓ hT₀ hT => ?_⟩
  have hΓfix := conjEntrywiseImage_inv_eq_fixed (Or.inr rfl) F hF hbij hg hgn
  have hΓG : Γ ≤ adjointGroup .F4 Ω := by
    rw [hΓ, hΓfix]
    exact inf_le_left
  set D := f4PhiSixPairBasis with hD
  have hd : ((q ^ 2 - q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - D.ε * q + 1 := by
    change _ = _ - (1 : ℤ) * _ + 1
    push_cast [Nat.cast_sub (le_sq_self q)]
    ring
  have hfixT : ∀ u ∈ torusGroup .F4 Ω, u ∈ Γ ↔ u ∈ D.torus Ω q (q ^ 2 - q + 1) := fun u hu => by
    rw [hΓ, hΓfix, ← D.conj_frob_eq_iff_mem_torus F hF hd hu, ← hn]
    exact ⟨fun h => h.2, fun h => ⟨torusGroup_le_adjointGroup_F4 hu, h⟩⟩
  have hT₀eq : T₀ = D.torus Ω q (q ^ 2 - q + 1) := by
    ext u
    rw [hT₀, Subgroup.mem_inf]
    constructor
    · rintro ⟨hu, huΓ⟩
      exact (hfixT u hu).1 huΓ
    · intro hu
      have huH := D.torus_le_torusGroup _ _ hu
      exact ⟨huH, (hfixT u huH).2 hu⟩
  have hqK : ((q : ℕ) : K) = 0 := by
    rw [hq, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have hdK : ((q ^ 2 - q + 1 : ℕ) : K) = 1 := by
    push_cast [Nat.cast_sub (le_sq_self q)]
    rw [hqK]
    ring
  have hdΩ : ((q ^ 2 - q + 1 : ℕ) : Ω) = 1 := by
    rw [← map_natCast (algebraMap K Ω), hdK, map_one]
  have : NeZero ((q ^ 2 - q + 1 : ℕ) : Ω) := ⟨by
    rw [hdΩ]
    exact one_ne_zero⟩
  have hT₀Γ : T₀ ≤ Γ := hT₀ ▸ inf_le_right
  have hTle : T ≤ (adjointGroup .F4 K).map (baseChangeGL (algebraMap K Ω)) := by
    rw [hT]
    exact map_conj_le_of_le_conjEntrywiseImage_inv (hΓ ▸ hT₀Γ)
  have hcardT₀ : Nat.card T₀ = (q ^ 2 - q + 1) ^ 2 := by
    rw [hT₀eq]
    exact D.natCard_torus q _
  have hcardT : Nat.card T = (q ^ 2 - q + 1) ^ 2 := by
    rw [hT, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardT₀]
  refine ⟨hΓ.trans hΓfix, by rw [hT₀eq]; exact D.nonempty_torus_mulEquiv q _, hTle,
    hcardT ▸ (odd_sq_sub_self_add_one q).pow, fun p hp hp3 hpd => ?_, fun h2 K₆ hK₆ => ?_⟩
  ·
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero (p : Ω) := ⟨fun h0 => by
      have hpK : (p : K) = 0 := by
        apply (algebraMap K Ω).injective
        rw [map_natCast, h0, map_zero]
      have h1 : ((q ^ 2 - q + 1 : ℕ) : K) = 0 := by
        obtain ⟨t, ht⟩ := hpd
        rw [ht, Nat.cast_mul, hpK, zero_mul]
      rw [hdK] at h1
      exact one_ne_zero h1⟩
    set φ := (baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype with hφ
    have hφinj : Function.Injective φ :=
      (baseChangeGL_injective (τ := .F4) (algebraMap K Ω)).comp Subtype.val_injective
    have hφrange : φ.range = (adjointGroup .F4 K).map (baseChangeGL (algebraMap K Ω)) := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    have hidx : ¬ p ∣ (T.comap φ).index := F4_not_dvd_index_phiSix K hp hp3 hpd _
      (by rw [natCard_comap_of_le_range hφinj (hφrange ▸ hTle), hcardT])
    obtain ⟨hSyl, hconj⟩ := exists_sylow_map_le_and_conj_of_not_dvd_index φ hidx
    refine ⟨hSyl, hconj, ⟨D.torus Ω q p, fun h => by rw [hT₀eq]; exact D.mem_torus_iff_of_dvd hpd,
      D.natCard_torus q p, ?_⟩, fun x hx hxp R hR => ?_⟩
    · obtain ⟨x, hxV, hx1, hxα⟩ :=
        D.exists_ne_one_mem_torus_torusRootChar_eq_one (L := Ω) q hp (isRoot_single .F4 (f4Index 0))
      exact ⟨x, hxV, hx1, ⟨_, isRoot_single .F4 (f4Index 0), hxα⟩⟩
    ·
      rw [hT₀eq] at hx
      have hxH := D.torus_le_torusGroup _ _ hx
      have hfx := (D.conj_frob_eq_iff_mem_torus F hF hd hxH).2 hx
      have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
      have hx1 : x ≠ 1 := fun h => by
        rw [h, orderOf_one] at hxp
        exact hp.one_lt.ne hxp
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := Ω) (n := p)
      obtain ⟨ξ, hξζ⟩ := hζ.isUnit hp.ne_zero
      rw [← hξζ, IsPrimitiveRoot.coe_units_iff] at hζ
      have hξ : orderOf ξ = p := hζ.eq_orderOf.symm
      obtain ⟨v, hv0, hdual, hRv⟩ :=
        F4_exists_charRootKernel_eq F hF hξ f4PhiSix hxH hfx hxp' hx1
      rw [hR, hRv]
      refine ⟨F4_phiSix_charRootKernel hp hp3 (zmod_phiSix_eq_zero hpd) hv0 hdual,
        fun hempty => ?_⟩
      rw [F4_inf_centralizer_eq_of_root_kernel_empty hp hp3 hΓG hxH hxp (hRv.trans hempty),
        hT₀]
  ·
    have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
    have : Module.Finite K K₆ := Module.finite_of_finrank_pos (by omega)
    have : Finite K₆ := Module.finite_of_finite K
    have hcard₆ : Nat.card K₆ = q ^ 6 := by
      rw [Module.natCard_eq_pow_finrank (K := K), hK₆]
    have hF6 : ∀ c, (F ^ 6) c = c ^ Nat.card K₆ := fun c => by
      rw [hcard₆, RingHom.coe_pow]
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, hF]
      ring
    have hFn : Units.map (entrywiseHom F) n = n := by
      have h := entrywise_canonicalRep (RingEquiv.ofBijective F hbij) (τ := .F4) f4PhiSix
      rw [hn]
      exact h
    have hpow : ∀ k : ℕ, canonicalRep (coxeterSystem .F4) Ω (f4PhiSix ^ k) =
        canonicalRep (coxeterSystem .F4) Ω f4PhiSix ^ k := fun k => by
      induction k with
      | zero => rw [pow_zero, pow_zero, canonicalRep_one]
      | succ k ih => rw [pow_succ f4PhiSix k, canonicalRep_mul_of_charTwo, ih, ← pow_succ]
    have hn6 : n ^ 6 = 1 := by
      rw [hn, ← hpow, ← orderOf_f4PhiSix, pow_orderOf_eq_one, canonicalRep_one]
    have hgK₆ : g ∈ (adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) :=
      mem_map_adjointGroup_of_iterate_eq (Or.inr rfl) F hF6 hbij hg
        (by rw [iterate_entrywise_eq_of_inv_mul F hFn hgn, hn6, mul_one])
    have hΓK₆ : Γ = (adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ⊓
        (twistedEntrywise n F).eqLocus (MonoidHom.id _) := by
      rw [hΓ, hΓfix]
      ext y
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hy, hyF⟩
        refine ⟨mem_map_adjointGroup_of_iterate_eq (Or.inr rfl) F hF6 hbij hy ?_, hyF⟩
        rw [iterate_entrywise_eq_of_conj F hFn hyF, hn6, inv_one, one_mul, mul_one]
      · rintro ⟨⟨y', hy', rfl⟩, hyF⟩
        exact ⟨baseChangeGL_mem_adjointGroup _ hy', hyF⟩
    have hq6 := pow_six_eq_phiSix_mul_add_one (q := q) Nat.card_pos
    have hT₀K₆ : T₀ ≤ (torusGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) := by
      intro u hu
      rw [hT₀eq] at hu
      obtain ⟨⟨ζ, η⟩, ⟨hζ, hη⟩, rfl⟩ := hu
      show rootDiagUnit .F4 (D.pairTuple q ζ η) ∈ _
      refine rootDiagUnit_mem_map_torusGroup fun j => ?_
      have h1 : ((ζ, η) : Ωˣ × Ωˣ) ^ (q ^ 2 - q + 1) = 1 :=
        Prod.ext ((mem_rootsOfUnity _ ζ).1 hζ) ((mem_rootsOfUnity _ η).1 hη)
      have hcd : D.pairTuple q ζ η ^ (q ^ 2 - q + 1) = 1 := by
        rw [← D.pairTupleHom_apply q (ζ, η), ← map_pow, h1, map_one]
      have hj : D.pairTuple q ζ η j ^ (q ^ 2 - q + 1) = 1 := by simpa using congrFun hcd j
      rw [hcard₆, ← Units.val_pow_eq_pow_val, hq6, pow_succ, pow_mul, hj, one_pow, one_mul]
    exact ⟨hgK₆, hT₀K₆, hΓK₆⟩

end CFSG.RankThree.Chevalley
