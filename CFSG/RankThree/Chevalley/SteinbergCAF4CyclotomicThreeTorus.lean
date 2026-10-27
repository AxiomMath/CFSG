module

public import CFSG.RankThree.Chevalley.SteinbergCAF4PairTorus
public import CFSG.RankThree.Chevalley.SteinbergCEF4OrderThree
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicCentralizers
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups EvenF4QPlus CFSG.Timmesfeld.ExceptionalOrders RootSpace
  CFSG.LieType.Steinberg.Adjoint

@[expose] def f4OrderThreePairBasis : F4PairBasis (f4Coxeter ^ 4) where
  B := f4OrderThreeBasisMatrix
  N := !![1, 0, 0, -1; 0, 1, 0, -1; 0, -2, 1, 0; 0, 0, 0, -1]
  ε := -1
  smul_zero := by rw [f4Coxeter_pow, f4WordProd_smul]; decide
  smul_one := by rw [f4Coxeter_pow, f4WordProd_smul]; decide
  smul_two := by rw [f4Coxeter_pow, f4WordProd_smul]; decide
  smul_three := by rw [f4Coxeter_pow, f4WordProd_smul]; decide
  N_mul := by decide
  mul_N := by decide

theorem F4_not_dvd_index_three (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1) (T : Subgroup (adjointGroup .F4 K))
    (hT : Nat.card T = (Nat.card K ^ 2 + Nat.card K + 1) ^ 2) : ¬ p ∣ T.index := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := T.card_mul_index
  rw [hT, card_adjointGroup_F4, CFSG.Open.ordF4] at hcard
  set Q : ℤ := (Nat.card K : ℤ) with hQ
  have hcardZ : (Q ^ 2 + Q + 1) ^ 2 * T.index =
      Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq1)] at h
    exact h
  have hd0 : (Q ^ 2 + Q + 1) ^ 2 ≠ 0 := by positivity
  have hidx : (T.index : ℤ) = Q ^ 24 * (Q - 1) ^ 2 * (Q ^ 3 + 1) ^ 2 * (Q ^ 6 + 1) *
      (Q ^ 8 - 1) * (Q ^ 2 - 1) := by
    apply mul_left_cancel₀ hd0
    rw [hcardZ]
    ring
  have two : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_zmod_ne_zero_of_pos_of_lt (by norm_num) (by omega : 2 < p)
  have three : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_zmod_ne_zero_of_pos_of_lt (by norm_num) hp3
  set x : ZMod p := ((Nat.card K : ℕ) : ZMod p) with hx
  have hf : x ^ 2 + x + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ p).2 hpd
    push_cast at h
    exact h
  intro hdvd
  have hi : ((T.index : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
  have h0 := congrArg (Int.cast : ℤ → ZMod p) hidx
  push_cast at h0
  rw [show ((Q : ℤ) : ZMod p) = x by rw [hQ, Int.cast_natCast], hi] at h0
  refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_)
    ?_) h0.symm
  · exact pow_ne_zero _ fun h =>
      one_ne_zero (by linear_combination hf - (x + 1) * h : (1 : ZMod p) = 0)
  · exact pow_ne_zero _ fun h => three (by linear_combination hf - (x + 2) * h)
  · exact pow_ne_zero _ fun h => two (by linear_combination h - (x - 1) * hf)
  · exact fun h => two (by linear_combination h - (x - 1) * (x ^ 3 + 1) * hf)
  · exact fun h => three (by
      linear_combination (1 - (x - 1) * (x ^ 2 * (x - 1) * (x ^ 3 + 1) + 1)) * hf + (x - 1) * h)
  · exact fun h => three (by linear_combination (2 - x) * hf + (x - 1) * h)

theorem orderOf_unit_eq_three_of_dvd {p q : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hpd : p ∣ q ^ 2 + q + 1) (hq0 : (q : ZMod p) ≠ 0) :
    orderOf (Units.mk0 (q : ZMod p) hq0) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have three : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_zmod_ne_zero_of_pos_of_lt (by norm_num) hp3
  have hf : (q : ZMod p) ^ 2 + q + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ p).2 hpd
    push_cast at h
    exact h
  refine orderOf_eq_prime ?_ fun h => ?_
  · refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    linear_combination ((q : ZMod p) - 1) * hf
  · have h' := congrArg Units.val h
    simp only [Units.val_mk0, Units.val_one] at h'
    exact three (by linear_combination hf - ((q : ZMod p) + 2) * h')

theorem F4_cyclotomic_three_torus_and_regular_prime_centralizers
    (K : Type) [Field K] [Finite K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω)
    (hF : ∀ c, F c = c ^ Nat.card K) (n : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 4)) :
    (∃ g ∈ adjointGroup .F4 Ω, g⁻¹ * Units.map (entrywiseHom F) g = n) ∧
    ∀ g ∈ adjointGroup .F4 Ω, g⁻¹ * Units.map (entrywiseHom F) g = n →
    ∀ Γ T₀ T : Subgroup (ModGL .F4 Ω), Γ = conjEntrywiseImage K g⁻¹ →
      T₀ = torusGroup .F4 Ω ⊓ Γ → T = T₀.map (MulAut.conj g).toMonoidHom →
      Γ = adjointGroup .F4 Ω ⊓ (twistedEntrywise n F).eqLocus (MonoidHom.id _) ∧
      Nonempty (T₀ ≃* Multiplicative (ZMod (Nat.card K ^ 2 + Nat.card K + 1)) ×
        Multiplicative (ZMod (Nat.card K ^ 2 + Nat.card K + 1))) ∧
      T ≤ (adjointGroup .F4 K).map (baseChangeGL (algebraMap K Ω)) ∧ Odd (Nat.card T) ∧
      (∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card K ^ 2 + Nat.card K + 1 →
        (∃ S : Sylow p (adjointGroup .F4 K), (S : Subgroup (adjointGroup .F4 K)).map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) ≤ T) ∧
        (∀ P : Subgroup (adjointGroup .F4 K), IsPGroup p P → ∃ c : adjointGroup .F4 K,
          (P.map (MulAut.conj c).toMonoidHom).map
            ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) ≤ T) ∧
        (∃ V : Subgroup (ModGL .F4 Ω), (∀ h, h ∈ V ↔ h ∈ T₀ ∧ h ^ p = 1) ∧
          Nat.card V = p ^ 2 ∧
          ∀ E₀ : Subgroup (ModGL .F4 Ω), E₀ ≤ T₀ → Nat.card E₀ = p ^ 2 →
            (∀ x ∈ E₀, x ^ p = 1) →
            E₀ = V ∧ ∃ x ∈ E₀, x ≠ 1 ∧ {α | IsRoot .F4 α ∧ torusRootChar x α = 1}.Nonempty) ∧
        ∀ x ∈ T₀, orderOf x = p → ∀ R : Set (Fin Tag.F4.rank → ℤ),
          R = {α | IsRoot .F4 α ∧ torusRootChar x α = 1} →
          (R = ∅ ∨ ∃ (u : WeylGroup .F4) (i j : Fin Tag.F4.rank) (ε : ℤ),
            ((i = f4Index 0 ∧ j = f4Index 1) ∨ (i = f4Index 2 ∧ j = f4Index 3)) ∧
            (ε = 1 ∨ ε = -1) ∧
            (fun α => u • α) '' R = parabolicRoots .F4 {i, j} ∧
            ∀ y ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {i, j}),
              weylAct .F4 (u * f4Coxeter ^ 4 * u⁻¹) y =
                weylAct .F4 ((simple .F4 i * simple .F4 j) ^ ε) y) ∧
          (R ≠ ∅ → R.ncard = 6 ∧ ∀ α ∈ R, ∀ β ∈ R, iform α α = iform β β) ∧
          (R = ∅ → Γ ⊓ Subgroup.centralizer {x} = T₀)) ∧
      (CharP K 2 → ∀ K₃ : IntermediateField K Ω, Module.finrank K K₃ = 3 →
        g ∈ (adjointGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) ∧
        T₀ ≤ (torusGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) ∧
        Γ = (adjointGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) ⊓
          (twistedEntrywise n F).eqLocus (MonoidHom.id _)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Finite (Module.End K (RootModule .F4 K)) := Module.finite_of_finite K
  have hbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  set q := Nat.card K with hq
  have hnG : n ∈ adjointGroup .F4 Ω := hn ▸ canonicalRep_mem_adjointGroup _ Ω _
  refine ⟨exists_inv_mul_entrywise_eq K F hF .F4 hnG, fun g hg hgn Γ T₀ T hΓ hT₀ hT => ?_⟩
  have hΓfix := conjEntrywiseImage_inv_eq_fixed (Or.inr rfl) F hF hbij hg hgn
  have hΓG : Γ ≤ adjointGroup .F4 Ω := by
    rw [hΓ, hΓfix]
    exact inf_le_left
  set D := f4OrderThreePairBasis with hD
  have hd : ((q ^ 2 + q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - D.ε * q + 1 := by
    change _ = _ - (-1 : ℤ) * _ + 1
    push_cast
    ring
  have hfixT : ∀ u ∈ torusGroup .F4 Ω, u ∈ Γ ↔ u ∈ D.torus Ω q (q ^ 2 + q + 1) :=
    fun u hu => by
      rw [hΓ, hΓfix, ← D.conj_frob_eq_iff_mem_torus F hF hd hu, ← hn]
      exact ⟨fun h => h.2, fun h => ⟨torusGroup_le_adjointGroup_F4 hu, h⟩⟩
  have hT₀eq : T₀ = D.torus Ω q (q ^ 2 + q + 1) := by
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
  have hdK : ((q ^ 2 + q + 1 : ℕ) : K) = 1 := by
    push_cast
    rw [hqK]
    ring
  have hdΩ : ((q ^ 2 + q + 1 : ℕ) : Ω) = 1 := by
    rw [← map_natCast (algebraMap K Ω), hdK, map_one]
  have : NeZero ((q ^ 2 + q + 1 : ℕ) : Ω) := ⟨by
    rw [hdΩ]
    exact one_ne_zero⟩
  have hT₀Γ : T₀ ≤ Γ := hT₀ ▸ inf_le_right
  have hTle : T ≤ (adjointGroup .F4 K).map (baseChangeGL (algebraMap K Ω)) := by
    rw [hT]
    exact map_conj_le_of_le_conjEntrywiseImage_inv (hΓ ▸ hT₀Γ)
  have hcardT₀ : Nat.card T₀ = (q ^ 2 + q + 1) ^ 2 := by
    rw [hT₀eq]
    exact D.natCard_torus q _
  have hcardT : Nat.card T = (q ^ 2 + q + 1) ^ 2 := by
    rw [hT, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardT₀]
  have hdodd : Odd ((q ^ 2 + q + 1) ^ 2) := by
    have h : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
    rw [h]
    exact (Nat.even_mul_succ_self q).add_one.pow
  refine ⟨hΓ.trans hΓfix, by rw [hT₀eq]; exact D.nonempty_torus_mulEquiv q _, hTle,
    hcardT ▸ hdodd, fun p hp hp3 hpd => ?_, fun h2 K₃ hK₃ => ?_⟩
  ·
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero (p : Ω) := ⟨fun h0 => by
      have hpK : (p : K) = 0 := by
        apply (algebraMap K Ω).injective
        rw [map_natCast, h0, map_zero]
      have h1 : ((q ^ 2 + q + 1 : ℕ) : K) = 0 := by
        obtain ⟨t, ht⟩ := hpd
        rw [ht, Nat.cast_mul, hpK, zero_mul]
      rw [hdK] at h1
      exact one_ne_zero h1⟩
    set φ := (baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype with hφ
    have hφinj : Function.Injective φ :=
      (baseChangeGL_injective (τ := .F4) (algebraMap K Ω)).comp Subtype.val_injective
    have hφrange : φ.range = (adjointGroup .F4 K).map (baseChangeGL (algebraMap K Ω)) := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    have hidx : ¬ p ∣ (T.comap φ).index := F4_not_dvd_index_three K hp hp3 hpd _
      (by rw [natCard_comap_of_le_range hφinj (hφrange ▸ hTle), hcardT])
    obtain ⟨hSyl, hconj⟩ := exists_sylow_map_le_and_conj_of_not_dvd_index φ hidx
    have hVcard := D.natCard_torus (L := Ω) q p
    have : Finite (D.torus Ω q p) := Nat.finite_of_card_ne_zero (by
      rw [hVcard]
      exact pow_ne_zero _ hp.ne_zero)
    refine ⟨hSyl, hconj, ⟨D.torus Ω q p, fun h => by rw [hT₀eq]; exact D.mem_torus_iff_of_dvd hpd,
      hVcard, fun E₀ hE₀ hE₀card hE₀p => ?_⟩, fun x hx hxp R hR => ?_⟩
    ·
      have hle : E₀ ≤ D.torus Ω q p := fun x hx =>
        (D.mem_torus_iff_of_dvd hpd).2 ⟨hT₀eq ▸ hE₀ hx, hE₀p x hx⟩
      have heq : E₀ = D.torus Ω q p :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hE₀card, hVcard])
      refine ⟨heq, ?_⟩
      rw [heq]
      obtain ⟨x, hxV, hx1, hxα⟩ :=
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
        F4_exists_charRootKernel_eq F hF hξ (f4Coxeter ^ 4) hxH hfx hxp' hx1
      have hq0 : (q : ZMod p) ≠ 0 := fun h => by
        have h' := (ZMod.natCast_eq_zero_iff _ p).2 hpd
        push_cast at h'
        rw [h] at h'
        simp at h'
      obtain ⟨-, -, -, -, -, hA2⟩ := F4_order_three_Weyl_lattice_and_surviving_A2_kernels
      obtain ⟨hcase, hcount⟩ := hA2 p hp hp3 _ (orderOf_unit_eq_three_of_dvd hp3 hpd hq0) v hv0
        (by rw [Units.val_mk0]; exact hdual)
      rw [hR, hRv]
      refine ⟨hcase, hcount, fun hempty => ?_⟩
      rw [F4_inf_centralizer_eq_of_root_kernel_empty hp hp3 hΓG hxH hxp (hRv.trans hempty),
        hT₀]
  ·
    have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
    have : Module.Finite K K₃ := Module.finite_of_finrank_pos (by omega)
    have : Finite K₃ := Module.finite_of_finite K
    have hcard₃ : Nat.card K₃ = q ^ 3 := by
      rw [Module.natCard_eq_pow_finrank (K := K), hK₃]
    have hF3 : ∀ c, (F ^ 3) c = c ^ Nat.card K₃ := fun c => by
      rw [hcard₃, RingHom.coe_pow]
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, hF]
      ring
    have hFn : Units.map (entrywiseHom F) n = n := by
      have h := entrywise_canonicalRep (RingEquiv.ofBijective F hbij) (τ := .F4) (f4Coxeter ^ 4)
      rw [hn]
      exact h
    have hpow : ∀ k : ℕ, canonicalRep (coxeterSystem .F4) Ω ((f4Coxeter ^ 4) ^ k) =
        canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 4) ^ k := fun k => by
      induction k with
      | zero => rw [pow_zero, pow_zero, canonicalRep_one]
      | succ k ih => rw [pow_succ (f4Coxeter ^ 4) k, canonicalRep_mul_of_charTwo, ih, ← pow_succ]
    have hn3 : n ^ 3 = 1 := by
      rw [hn, ← hpow, ← orderOf_f4OrderThree, pow_orderOf_eq_one, canonicalRep_one]
    have hgK₃ : g ∈ (adjointGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) :=
      mem_map_adjointGroup_of_iterate_eq (Or.inr rfl) F hF3 hbij hg
        (by rw [iterate_entrywise_eq_of_inv_mul F hFn hgn, hn3, mul_one])
    have hΓK₃ : Γ = (adjointGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) ⊓
        (twistedEntrywise n F).eqLocus (MonoidHom.id _) := by
      rw [hΓ, hΓfix]
      ext y
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hy, hyF⟩
        refine ⟨mem_map_adjointGroup_of_iterate_eq (Or.inr rfl) F hF3 hbij hy ?_, hyF⟩
        rw [iterate_entrywise_eq_of_conj F hFn hyF, hn3, inv_one, one_mul, mul_one]
      · rintro ⟨⟨y', hy', rfl⟩, hyF⟩
        exact ⟨baseChangeGL_mem_adjointGroup _ hy', hyF⟩
    have hq3 : q ^ 3 = (q ^ 2 + q + 1) * (q - 1) + 1 := by
      have h1 : 1 ≤ q := Nat.card_pos
      zify [h1]
      ring
    have hT₀K₃ : T₀ ≤ (torusGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) := by
      intro u hu
      rw [hT₀eq] at hu
      obtain ⟨⟨ζ, η⟩, ⟨hζ, hη⟩, rfl⟩ := hu
      show rootDiagUnit .F4 (D.pairTuple q ζ η) ∈ _
      refine rootDiagUnit_mem_map_torusGroup fun j => ?_
      have h1 : ((ζ, η) : Ωˣ × Ωˣ) ^ (q ^ 2 + q + 1) = 1 :=
        Prod.ext ((mem_rootsOfUnity _ ζ).1 hζ) ((mem_rootsOfUnity _ η).1 hη)
      have hcd : D.pairTuple q ζ η ^ (q ^ 2 + q + 1) = 1 := by
        rw [← D.pairTupleHom_apply q (ζ, η), ← map_pow, h1, map_one]
      have hj : D.pairTuple q ζ η j ^ (q ^ 2 + q + 1) = 1 := by simpa using congrFun hcd j
      rw [hcard₃, ← Units.val_pow_eq_pow_val, hq3, pow_succ, pow_mul, hj, one_pow, one_mul]
    exact ⟨hgK₃, hT₀K₃, hΓK₃⟩

end CFSG.RankThree.Chevalley
