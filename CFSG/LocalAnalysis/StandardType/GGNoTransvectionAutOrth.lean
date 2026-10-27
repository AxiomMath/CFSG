module

public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutExc
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix Multiplicative TableBOrthL

namespace NoTvAut

section Gram

variable {p k : ℕ} [Fact p.Prime]

variable (p) in
@[expose] def dneg (a j : Fin k) (x : Fin k → ZMod p) : Fin k → ZMod p :=
  fun l => if l = a ∨ l = j then -x l else x l

theorem addMonoidHom_smul (T : (Fin k → ZMod p) →+ (Fin k → ZMod p)) (c : ZMod p)
    (v : Fin k → ZMod p) : T (c • v) = c • T v := by
  have h := map_nsmul T c.val v
  rwa [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val, ← Nat.cast_smul_eq_nsmul (ZMod p),
    ZMod.natCast_zmod_val] at h

theorem addMonoidHom_eq_sum (T : (Fin k → ZMod p) →+ (Fin k → ZMod p)) (x : Fin k → ZMod p) :
    T x = ∑ a, x a • T (Pi.single a 1) := by
  have hx : x = ∑ a, x a • Pi.single a (1 : ZMod p) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun a _ => ?_
    funext l
    by_cases h : l = a
    · subst h
      simp
    · simp [h]
  conv_lhs => rw [hx]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => addMonoidHom_smul T _ _

theorem gram_eq_smul (hp2 : p ≠ 2) (hk : 3 ≤ k) (T : (Fin k → ZMod p) →+ (Fin k → ZMod p))
    (hd : ∀ a j : Fin k, a ≠ j → ∀ x y, T (dneg p a j x) ⬝ᵥ T (dneg p a j y) = T x ⬝ᵥ T y)
    (hs : ∀ σ : Equiv.Perm (Fin k), ∀ x y, T (x ∘ ⇑σ⁻¹) ⬝ᵥ T (y ∘ ⇑σ⁻¹) = T x ⬝ᵥ T y) :
    ∃ c : ZMod p, ∀ x y, T x ⬝ᵥ T y = c * (x ⬝ᵥ y) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hoff : ∀ a b : Fin k, a ≠ b →
      T (Pi.single a 1) ⬝ᵥ T (Pi.single b 1) = 0 := by
    intro a b hab
    obtain ⟨j, hja, hjb⟩ : ∃ j : Fin k, j ≠ a ∧ j ≠ b := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin k)) ⊆ {a, b} := fun j _ => by
        by_cases hja : j = a
        · simp [hja]
        · simp [hcon j hja]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h3 := Finset.card_le_two (a := a) (b := b)
      omega
    have h1 := hd a j (Ne.symm hja) (Pi.single a 1) (Pi.single b 1)
    have e1 : dneg p a j (Pi.single a 1) = -(Pi.single a 1) := by
      funext l
      simp only [dneg, Pi.neg_apply]
      by_cases hla : l = a
      · subst hla
        simp
      · by_cases hlj : l = j
        · subst hlj
          simp [hla]
        · simp [hla, hlj]
    have e2 : dneg p a j (Pi.single b 1) = Pi.single b 1 := by
      funext l
      simp only [dneg]
      by_cases hl : l = a ∨ l = j
      · rw [ite_eq_left_iff.mpr (fun h => absurd hl h)]
        have hlb : l ≠ b := by
          rcases hl with rfl | rfl
          · exact hab
          · exact hjb
        simp [hlb]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hl)]
    rw [e1, e2, map_neg, neg_dotProduct] at h1
    have h3 : 2 * (T (Pi.single a 1) ⬝ᵥ T (Pi.single b 1)) = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hdiag : ∀ a b : Fin k,
      T (Pi.single a 1) ⬝ᵥ T (Pi.single a 1) = T (Pi.single b 1) ⬝ᵥ T (Pi.single b 1) := by
    intro a b
    have h1 := hs (Equiv.swap a b) (Pi.single a 1) (Pi.single a 1)
    have e1 : (Pi.single a (1 : ZMod p) : Fin k → ZMod p) ∘ ⇑(Equiv.swap a b)⁻¹ =
        Pi.single b 1 := by
      funext l
      simp only [Function.comp_apply, Equiv.swap_inv, Pi.single_apply]
      by_cases hlb : l = b
      · subst hlb
        simp
      · by_cases hla : l = a
        · subst hla
          rw [Equiv.swap_apply_left]
          simp [hlb, Ne.symm hlb]
        · rw [Equiv.swap_apply_of_ne_of_ne hla hlb]
          simp [hla, hlb]
    rw [e1] at h1
    exact h1.symm
  have hk0 : 0 < k := by omega
  refine ⟨T (Pi.single ⟨0, hk0⟩ 1) ⬝ᵥ T (Pi.single ⟨0, hk0⟩ 1), fun x y => ?_⟩
  rw [addMonoidHom_eq_sum T x, addMonoidHom_eq_sum T y, sum_dotProduct]
  simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have hxy : x ⬝ᵥ y = ∑ a, x a * y a := rfl
  rw [hxy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hba => by rw [hoff a b (Ne.symm hba), mul_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ a) h), hdiag a ⟨0, hk0⟩]
  ring

end Gram

section Model

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

variable (p) in
@[expose] def coordHom (k : ℕ) :
    Multiplicative (Fin k → ZMod p) →* (Fin k → Multiplicative (ZMod p)) where
  toFun s i := ofAdd (toAdd s i)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coordHom_injective (k : ℕ) : Function.Injective (coordHom p k) := fun _ _ h =>
  toAdd.injective (funext fun i => ofAdd.injective (congrFun h i))

theorem dinv_ofAdd {k : ℕ} {i j : Fin k} (hij : i ≠ j) (x : Fin k → ZMod p) :
    NbrOrth.dinv i j (fun l => ofAdd (x l)) = fun l => ofAdd (dneg p i j x l) := by
  funext l
  rw [OrthNs.dinv_apply_eq]
  simp only [dneg, hij]
  split_ifs <;> first | rfl | contradiction

theorem ggNoTransvectionSC_of_evenSignedPermEltSC {kP : ℕ → Prop} (hp : p.Prime)
    (hp2 : p ≠ 2) (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGTorusEvenSignedPermEltSC p R kP) :
    GGNoTransvectionSC p R I := by
  have := Fact.mk hp
  intro Eh hEhI hEhA h3 hscR a htv
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI hφ)
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA x.2 y.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    show MulAut.conj g ∈ Eh
    refine hscR g (fun φ hφ => ?_) hgp
    obtain ⟨y, rfl⟩ := hI (hEhI hφ)
    have hy : y ∈ E := hφ
    rw [MulAut.conj_apply, ← hg y hy, mul_inv_cancel_right]
  obtain ⟨k, τ, hτinj, hτE, -, hd, hP, hnorm⟩ := h E hEe (hcardE ▸ h3) hscE
  have hτmem : ∀ f, τ f ∈ E := fun f => hτE ▸ ⟨f, rfl⟩
  have hk : 3 ≤ k := by
    have h1 : Nat.card E = p ^ k := by
      rw [← hτE, ← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, Nat.card_fun,
        Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    rw [← hcardE, h1] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  have haE : ∀ b : Subgroup.normalizer (Eh : Set (MulAut R)), ∀ e ∈ E, (b : MulAut R) e ∈ E := by
    intro b e he
    show MulAut.conj ((b : MulAut R) e) ∈ Eh
    rw [← TableBOrth.mulAut_mul_conj_mul_inv]
    exact (Subgroup.mem_normalizer_iff.mp b.2 (MulAut.conj e)).mp he
  have hex : ∀ f, ∃ f', (a : MulAut R) (τ f) = τ f' := fun f => by
    have h1 : (a : MulAut R) (τ f) ∈ τ.range := hτE ▸ haE a _ (hτmem f)
    obtain ⟨f', hf'⟩ := h1
    exact ⟨f', hf'.symm⟩
  choose u hu using hex
  have humul : ∀ f g, u (f * g) = u f * u g := fun f g => hτinj (by
    calc τ (u (f * g)) = (a : MulAut R) (τ (f * g)) := (hu _).symm
      _ = (a : MulAut R) (τ f) * (a : MulAut R) (τ g) := by rw [map_mul, map_mul]
      _ = τ (u f) * τ (u g) := by rw [hu, hu]
      _ = τ (u f * u g) := (map_mul _ _ _).symm)
  set T : (Fin k → ZMod p) →+ (Fin k → ZMod p) :=
    AddMonoidHom.mk' (fun x i => toAdd (u (fun j => ofAdd (x j)) i)) (fun x y => by
      funext i
      show toAdd (u ((fun j => ofAdd (x j)) * fun j => ofAdd (y j)) i) = _
      rw [humul]
      rfl) with hTdef
  have hTu : ∀ x : Fin k → ZMod p, (fun i => ofAdd (T x i)) = u (fun j => ofAdd (x j)) :=
    fun x => rfl
  set ι : Multiplicative (Fin k → ZMod p) →* MulAut R :=
    (MulAut.conj : R →* MulAut R).comp (τ.comp (coordHom p k)) with hιdef
  have hιapp : ∀ s, ι s = MulAut.conj (τ (coordHom p k s)) := fun s => rfl
  have hι : Function.Injective ι := hinj.comp (hτinj.comp (coordHom_injective k))
  have hιB : ι.range = Eh := by
    ext φ
    constructor
    · rintro ⟨s, rfl⟩
      exact hτmem _
    · intro hφ
      obtain ⟨y, rfl⟩ := hI (hEhI hφ)
      have hy : y ∈ E := hφ
      rw [← hτE] at hy
      obtain ⟨f, rfl⟩ := hy
      exact ⟨ofAdd fun i => toAdd (f i), rfl⟩
  obtain ⟨hfix, hN⟩ := transvection_coords (t := T) hι hιB (fun b s hb => by
      show (a : MulAut R) * b * (a : MulAut R)⁻¹ = ι (ofAdd (T s))
      rw [hb, hιapp, hιapp, TableBOrth.mulAut_mul_conj_mul_inv, hu]
      rfl) htv
  have hsp : ∀ w : R, (∀ e ∈ E, w * e * w⁻¹ ∈ E) →
      ∀ g : (Fin k → ZMod p) → (Fin k → ZMod p),
      (∀ x, w * τ (fun j => ofAdd (x j)) * w⁻¹ = τ (fun j => ofAdd (g x j))) →
      ∀ x y, T (g x) ⬝ᵥ T (g y) = T x ⬝ᵥ T y := by
    intro w hwE g hg x y
    have haw : ∀ e ∈ E, (a : MulAut R) w * e * ((a : MulAut R) w)⁻¹ ∈ E := by
      intro e he
      have h1 : ((a⁻¹ : Subgroup.normalizer (Eh : Set (MulAut R))) : MulAut R) e ∈ E :=
        haE a⁻¹ e he
      have h2 := haE a _ (hwE _ h1)
      rwa [map_mul, map_mul, map_inv, Subgroup.coe_inv, MulAut.apply_inv_self] at h2
    obtain ⟨π, ε, hε, hact⟩ := hnorm _ haw
    have hxy : ∀ x i, T (g x) (π i) = ε i * T x i := by
      intro x i
      have h1 : (a : MulAut R) w * τ (u (fun j => ofAdd (x j))) * ((a : MulAut R) w)⁻¹ =
          τ (u (fun j => ofAdd (g x j))) := by
        calc (a : MulAut R) w * τ (u (fun j => ofAdd (x j))) * ((a : MulAut R) w)⁻¹
            = (a : MulAut R) w * (a : MulAut R) (τ (fun j => ofAdd (x j))) *
                (a : MulAut R) w⁻¹ := by rw [hu, map_inv]
          _ = (a : MulAut R) (w * τ (fun j => ofAdd (x j)) * w⁻¹) := by rw [map_mul, map_mul]
          _ = (a : MulAut R) (τ (fun j => ofAdd (g x j))) := by rw [hg]
          _ = τ (u (fun j => ofAdd (g x j))) := hu _
      exact hact _ _ h1 i
    calc T (g x) ⬝ᵥ T (g y) = ∑ i, T (g x) (π i) * T (g y) (π i) :=
          (Equiv.sum_comp π fun j => T (g x) j * T (g y) j).symm
      _ = ∑ i, T x i * T y i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hxy x i, hxy y i]
          have hε2 : ε i * ε i = 1 := by rcases hε i with h' | h' <;> rw [h'] <;> ring
          linear_combination (T x i * T y i) * hε2
      _ = T x ⬝ᵥ T y := rfl
  have hwE : ∀ w : R, ∀ g : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p)),
      (∀ f, w * τ f * w⁻¹ = τ (g f)) → ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro w g hg e he
    rw [← hτE] at he
    obtain ⟨f, rfl⟩ := he
    rw [hg]
    exact hτmem _
  obtain ⟨c, hc⟩ := gram_eq_smul hp2 hk T
    (fun i j hij x y => by
      obtain ⟨w, hw⟩ := hd i j hij
      exact hsp w (hwE w _ hw) (dneg p i j) (fun x => by rw [hw, dinv_ofAdd hij]) x y)
    (fun σ x y => by
      obtain ⟨w, hw⟩ := hP σ
      exact hsp w (hwE w _ hw) (fun x => x ∘ ⇑σ⁻¹) (fun x => by rw [hw]; rfl) x y)
  have hdet : (1 : Matrix (Fin k) (Fin k) (ZMod p)).det ≠ 0 := by
    rw [det_one]
    exact one_ne_zero
  exact false_of_isTransvection_similitude hp2 transpose_one hdet T c
    (fun x y => by rw [one_mulVec, one_mulVec]; exact hc x y) hfix hN

end Model

section Families

theorem ggOmegaPlusTvSCInput_of_torus (hS : GGOrthSignedTorusInput)
    (hE : GGOrthEvenTorusInput) : GGOmegaPlusTvSCInput := by
  intro K _ _ _ m p hm hp hp2 hpq
  obtain ⟨hZ, -⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m)
  have hmodel : ∃ kP : ℕ → Prop, GGTorusEvenSignedPermEltSC p (OrthRest.RPlus K m) kP := by
    rcases hpq with h1 | ⟨hK2, hp3⟩
    · exact ⟨_, hE.1 K m p hm hp (Or.inl h1)⟩
    · have hpK : p ∣ Nat.card K + 1 := by rw [hK2, hp3]
      rcases Nat.even_or_odd m with hme | hmo
      · exact ⟨_, hE.1 K m p hm hp (Or.inr ⟨hme, hpK⟩)⟩
      · have hm5 : 5 ≤ m := by
          obtain ⟨j, rfl⟩ := hmo
          omega
        exact ⟨_, ggTorusEvenSignedPermEltSC_of_signedEltSC (hS.1 K m p hm5 hmo hp hpK)⟩
  obtain ⟨kP, hmodel⟩ := hmodel
  exact ggNoTransvectionSC_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hmodel

theorem ggOmegaMinusTvSCInput_of_torus (hS : GGOrthSignedTorusInput)
    (hE : GGOrthEvenTorusInput) : GGOmegaMinusTvSCInput := by
  intro K _ _ _ m p b c hm hp hp2 hbc hpq
  obtain ⟨hZ, -⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
  have hmodel : ∃ kP : ℕ → Prop, GGTorusEvenSignedPermEltSC p (OrthRest.RMinus K m b c) kP := by
    rcases hpq with h1 | h1
    · exact ⟨_, ggTorusEvenSignedPermEltSC_of_signedEltSC
        (hS.2 K m p b c hm hbc hp (Or.inl h1))⟩
    · rcases Nat.even_or_odd m with hme | hmo
      · have hm4 : 4 ≤ m := by
          obtain ⟨j, rfl⟩ := hme
          omega
        exact ⟨_, hE.2 K m p b c hm4 hme hbc hp h1⟩
      · exact ⟨_, ggTorusEvenSignedPermEltSC_of_signedEltSC
          (hS.2 K m p b c hm hbc hp (Or.inr ⟨hmo, h1⟩))⟩
  obtain ⟨kP, hmodel⟩ := hmodel
  exact ggNoTransvectionSC_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hmodel

end Families

end NoTvAut

open NoTvAut

section Drop

theorem ggOrthLTvSCRest_of_torus (hS : GGOrthSignedTorusInput) (hE : GGOrthEvenTorusInput)
    (hU : GGUnitaryFourTvSCInput) : GGOrthLTvSCRest :=
  ⟨ggOmegaPlusTvSCInput_of_torus hS hE, ggOmegaMinusTvSCInput_of_torus hS hE, hU⟩

end Drop

end CFSG.StandardType

end
