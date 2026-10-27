module

public import CFSG.Quasithin.Background.HSL3Bridge

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

theorem isFFModule_map_congrHom {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    {X : Subgroup (MulAut V)} (h : IsFFModule X) : IsFFModule (X.map (congrHom e)) := by
  obtain ⟨A, hAX, hA1, hAel, hcard⟩ := h
  refine ⟨A.map (congrHom e), Subgroup.map_mono hAX,
    (Subgroup.map_eq_bot_iff_of_injective _ (congrHom_injective e)).not.mpr hA1,
    (isElemAbelian2_map_congrHom e).mpr hAel, ?_⟩
  rw [card_map_congrHom, fixV_map_congrHom,
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, ← Nat.card_congr e.toEquiv]
  exact hcard

namespace SL3Pair

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem mem_linSub_of_two (hK : Nat.card K = 2) (a : MulAut (StdMod (Fin 3) K)) :
    a ∈ linSub := by
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_contra hc
    push Not at hc
    have hinj : Function.Injective (![0, 1, c] : Fin 3 → K) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [eq_comm, zero_ne_one]
    have := Nat.card_le_card_of_injective _ hinj
    rw [hK, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  intro c v
  rcases h01 c with rfl | rfl
  · rw [zero_smul, toAddMap_zero, RingEquiv.refl_apply, zero_smul]
  · rw [one_smul, RingEquiv.refl_apply, one_smul]

theorem card_mul_le_of_swap_two (hK : Nat.card K = 2)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    {y : MulAut (PairMod K)} (hyA : y ∈ A) (hy : y ∉ pairSub K) :
    Nat.card A * Nat.card ↥(fixV A) ≤ 2 ^ 5 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨s, -, hyeq⟩ := exists_swap_decomp (hAN hyA) hy
  have hF := card_fstSub_le_of_swap hAN hA2 le_rfl hK1 hyA hy
  have h5 := card_le_two_mul_card_inf_pairSub hAN
  have h1 := card_le_card_fstSub hAN hA2
  have hfix : Nat.card ↥(fixV A) ≤
      Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨(v : PairMod K).1, ?_⟩) fun v w h => ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply] at this
      exact congrArg Prod.fst this
    · have h' : (v : PairMod K).1 = (w : PairMod K).1 := congrArg Subtype.val h
      have hv := v.2 _ hyA
      have hw := w.2 _ hyA
      rw [hyeq] at hv hw
      have hv2 : (v : PairMod K).2 = fstHom K s (v : PairMod K).1 :=
        (congrArg Prod.snd hv).symm
      have hw2 : (w : PairMod K).2 = fstHom K s (w : PairMod K).1 :=
        (congrArg Prod.snd hw).symm
      exact Subtype.ext (Prod.ext h' (by rw [hv2, hw2, h']))
  have hq3 : Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} ≤ Nat.card K ^ 3 :=
    calc _ ≤ Nat.card (StdMod (Fin 3) K) := Finite.card_subtype_le _
      _ = Nat.card K ^ 3 := by rw [card_stdMod, Fintype.card_fin]
  by_cases hF1 : fstSub A = ⊥
  · have hF1' : Nat.card (fstSub A) = 1 := by rw [hF1, Subgroup.card_bot]
    have hA : Nat.card A ≤ 2 := by omega
    calc Nat.card A * Nat.card ↥(fixV A) ≤ 2 * Nat.card K ^ 3 :=
          Nat.mul_le_mul hA (hfix.trans hq3)
      _ ≤ 2 ^ 5 := by rw [hK]; norm_num
  · obtain ⟨⟨f, hf⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
    have hf2 : (f : MulAut (StdMod (Fin 3) K)) ^ 2 = 1 := (isElemAbelian2_fstSub hA2).2 _ hf
    have hfN := fstSub_le_natNorm hAN hf
    have hq2 : Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} ≤ Nat.card K ^ 2 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun v : {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} =>
          (⟨v.1, v.2 _ hf⟩ : {v : StdMod (Fin 3) K // (f : MulAut _) v = v}))
        fun v w h => Subtype.ext ?_) ?_
      · exact congrArg (fun z : {v : StdMod (Fin 3) K // (f : MulAut _) v = v} => z.1) h
      · exact card_fix_le_sq le_rfl hK1 hfN hf2 (fun h => hf1 (Subtype.ext h))
    have hA : Nat.card A ≤ 4 * Nat.card K := by omega
    calc Nat.card A * Nat.card ↥(fixV A) ≤ 4 * Nat.card K * Nat.card K ^ 2 :=
          Nat.mul_le_mul hA (hfix.trans hq2)
      _ = 2 ^ 5 := by rw [hK]; norm_num

theorem card_mul_le_of_linear_two (hK : Nat.card K = 2)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) (hsub : A ≤ pairSub K) :
    Nat.card A * Nat.card ↥(fixV A) ≤ 2 ^ 5 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hlin : fstSub A ≤ linSub := fun a _ => mem_linSub_of_two hK a
  have hF2 := isElemAbelian2_fstSub hA2
  set E := linMat (fstSub A) with hEdef
  have hEcard : Nat.card E = Nat.card (fstSub A) := by
    rw [hEdef, card_linMat, inf_eq_left.mpr hlin]
  have h1 := card_le_card_fstSub hAN hA2
  rw [inf_eq_left.mpr hsub] at h1
  obtain ⟨hRC, hcard⟩ := card_le_of_elemAbelian_GL3' E (linMat_sq hF2) (linMat_comm hF2)
  have hfix : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixSp E) *
      Nat.card {w : Fin 3 → K // ∀ B ∈ E, (B : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w = w} := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun v => (⟨Multiplicative.toAdd (v : PairMod K).1, ?_⟩,
        ⟨Multiplicative.toAdd (v : PairMod K).2, ?_⟩)) fun v w h => ?_
    · refine (Submodule.mem_iInf _).mpr fun B => ?_
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := B.2
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply, hxB] at h
      have h' : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (v : PairMod K).1 =
          Multiplicative.toAdd (v : PairMod K).1 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.1) h
      rw [LinearMap.mem_ker, nOf_apply, h', sub_self]
    · intro B hB
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := hB
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have hx2 : (x : MulAut (PairMod K)) * x = 1 := by
        rw [← sq]
        exact hA2.2 _ hxA
      obtain ⟨-, hT⟩ := snd_eq_transpose (hAN hxA) hx2 hxB
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply] at h
      have h' : toAddMap (sndHom K x) (Multiplicative.toAdd (v : PairMod K).2) =
          Multiplicative.toAdd (v : PairMod K).2 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.2) h
      rw [← hT]
      exact h'
    · have h1 := congrArg (fun p => (p.1 : Fin 3 → K)) h
      have h2 := congrArg (fun p => (p.2 : Fin 3 → K)) h
      exact Subtype.ext (Prod.ext h1 h2)
  have hD := card_transpose_fix_le E
  have hC : Nat.card ↥(fixSp E) = Nat.card K ^ Module.finrank K (fixSp E) :=
    Module.natCard_eq_pow_finrank (K := K) (V := fixSp E)
  have hc3 : Module.finrank K (fixSp E) ≤ 3 := by
    have := Submodule.finrank_le (fixSp E)
    rwa [Module.finrank_fin_fun] at this
  have hrc := Submodule.finrank_mono hRC
  have hA2' : 2 ≤ Nat.card A := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have := (Finite.one_lt_card_iff_nontrivial (α := ↥A)).mpr ⟨⟨⟨a, ha⟩, 1, ha1⟩⟩
    omega
  have hpos : 1 ≤ (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) := by
    by_contra h
    push Not at h
    have h0 : (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) = 0 := by omega
    rw [h0, pow_zero] at hcard
    omega
  have hexp : Module.finrank K (fixSp E) + (3 - Module.finrank K (commSp E)) +
      (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) ≤ 5 := by
    generalize Module.finrank K (fixSp E) = c at hc3 hrc hpos ⊢
    generalize Module.finrank K (commSp E) = r at hrc hpos ⊢
    interval_cases c <;> interval_cases r <;> omega
  have hA : Nat.card A ≤
      Nat.card K ^ ((3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) := by
    rw [← hEcard] at h1
    exact h1.trans hcard
  have hfix' : Nat.card ↥(fixV A) ≤ Nat.card K ^ Module.finrank K (fixSp E) *
      Nat.card K ^ (3 - Module.finrank K (commSp E)) := by
    rw [← hC]
    exact hfix.trans (Nat.mul_le_mul_left _ hD)
  calc Nat.card A * Nat.card ↥(fixV A)
      ≤ Nat.card K ^ ((3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) *
          (Nat.card K ^ Module.finrank K (fixSp E) *
            Nat.card K ^ (3 - Module.finrank K (commSp E))) :=
        Nat.mul_le_mul hA hfix'
    _ = Nat.card K ^ (Module.finrank K (fixSp E) + (3 - Module.finrank K (commSp E)) +
          (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) := by
        ring
    _ ≤ Nat.card K ^ 5 := Nat.pow_le_pow_right (by omega) hexp
    _ = 2 ^ 5 := by rw [hK]

theorem card_mul_le_two (hK : Nat.card K = 2)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) : Nat.card A * Nat.card ↥(fixV A) ≤ 2 ^ 5 := by
  by_cases hsub : A ≤ pairSub K
  · exact card_mul_le_of_linear_two hK hAN hA2 hA1 hsub
  · obtain ⟨y, hyA, hy⟩ : ∃ y ∈ A, y ∉ pairSub K := by
      by_contra h
      push Not at h
      exact hsub h
    exact card_mul_le_of_swap_two hK hAN hA2 hyA hy

theorem not_isFFModule_two (hK : Nat.card K = 2) {X : Subgroup (MulAut (PairMod K))}
    (hXN : X ≤ pairNorm K) : ¬ IsFFModule X := by
  rintro ⟨A, hAX, hA1, hAel, hcard⟩
  have h := card_mul_le_two hK (hAX.trans hXN) hAel hA1
  rw [card_pairMod, hK] at hcard
  have e6 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have e5 : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [e6] at hcard
  rw [e5] at h
  omega

theorem H4_SL3Two {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) : ¬ IsFFModule M := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e.toEquiv
  have h2 : M.map (congrHom e) ≤ pairNorm K := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
          Set (MulAut (PairMod K))) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    rw [pairNorm, ← he, ← h3]
    exact Subgroup.map_mono hMN
  exact fun hFF => not_isFFModule_two (by rw [hK, pow_one]) h2 (isFFModule_map_congrHom e hFF)

end SL3Pair

end H

end CFSG.Quasithin
