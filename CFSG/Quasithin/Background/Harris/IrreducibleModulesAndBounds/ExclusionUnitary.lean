module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bOuter

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.X5 CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_elemAbelian_normalizer_le_unitary
    {f : ℕ} {K : Type} [Field K] (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K)
    {W : Type} [CommGroup W] [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w * w = 1) (L : Subgroup (MulAut W)) (hperf : Group.IsPerfect L)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (α : L ⧸ Subgroup.center L ≃* unitaryPSU h 3)
    (A : Subgroup (MulAut W)) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAe : CFSG.Quasithin.IsElemAbelian2 A) : Nat.card A ≤ 2 * 2 ^ f := by
  have := hperf
  have hfin : Finite (MulAut W) := Finite.of_injective (fun σ : MulAut W => (σ : W → W))
    DFunLike.coe_injective
  have hCodd := centralizer_odd hW L hirr
  have hZodd : Odd (Nat.card (Subgroup.center L)) := by
    let ι : Subgroup.center L →* Subgroup.centralizer (L : Set (MulAut W)) :=
      (L.subtype.comp (Subgroup.center L).subtype).codRestrict _ (fun z =>
        Subgroup.mem_centralizer_iff.mpr fun g hg => by
          have := (Subgroup.mem_center_iff.mp z.2) ⟨g, hg⟩
          exact congrArg Subtype.val this)
    have hinj : Function.Injective ι := fun x y hxy => by
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
    exact Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_injective ι hinj)
  obtain ⟨φ, hφs, hφk, hφZ, hφα⟩ := exists_cover_map hf h hZodd α
  obtain ⟨Ψ, hΨ⟩ := exists_fieldFactor_hom hf h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [sq] using hAe.2 a ha
  let τ : Subgroup.normalizer (L : Set (MulAut W)) →* MulAut (unitaryPSU h 3) :=
    (MulAut.congr α).toMonoidHom.comp (normalizerAct L)
  let ψ : A →* (K ≃+* K) := (Ψ.comp τ).comp (Subgroup.inclusion hAN)
  have hψ : ∀ a : A, ψ a = Ψ (τ ⟨(a : MulAut W), hAN a.2⟩) := fun a => rfl
  have hinner_iff : ∀ (a : MulAut W) (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W))),
      τ ⟨a, ha⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 3) →
        normalizerAct L ⟨a, ha⟩ ∈
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range := by
    rintro a ha ⟨x, hx⟩
    refine ⟨α.symm x, ?_⟩
    have h1 : MulAut.congr α.symm (MulAut.conj x) = MulAut.conj (α.symm x) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj α.symm x
    have h2 : MulAut.congr α.symm (τ ⟨a, ha⟩) = normalizerAct L ⟨a, ha⟩ := by
      ext y
      simp [τ, MulAut.congr_apply]
    show MulAut.conj (α.symm x) = normalizerAct L ⟨a, ha⟩
    rw [← h1, ← h2]
    exact congrArg (MulAut.congr α.symm) hx
  have hker : ∀ a : A, ψ a = 1 → (a : MulAut W) ∈ L := by
    intro a ha
    have haN : (a : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := hAN a.2
    have hββ : τ ⟨(a : MulAut W), haN⟩ * τ ⟨(a : MulAut W), haN⟩ = 1 := by
      rw [← map_mul]
      have : (⟨(a : MulAut W), haN⟩ * ⟨(a : MulAut W), haN⟩ :
          Subgroup.normalizer (L : Set (MulAut W))) = 1 := Subtype.ext (hAsq a a.2)
      rw [this, map_one]
    have hβ := hΨ _ (by rw [← hψ]; exact ha) hββ
    exact mem_of_involution_inner L hCodd haN (hAsq a a.2) (hinner_iff _ haN hβ)
  have hrange : Nat.card ψ.range ≤ 2 := by
    refine card_le_two_of_sq_eq_one (p := 2) ψ.range ?_
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hAe.2 a a.2)
    rw [this, map_one]
  have hc : Nat.card A ≤ 2 * Nat.card ψ.ker := card_le_two_mul_ker ψ hrange
  have hAL_fin : Finite ↥(A ⊓ L) := inferInstance
  have hd : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ L) := by
    refine Nat.card_le_card_of_injective (fun a : ψ.ker =>
      (⟨((a : A) : MulAut W), ⟨(a : A).2, hker a a.2⟩⟩ : ↥(A ⊓ L))) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this
  have he : Nat.card ↥(A ⊓ L) ≤ 2 ^ f := by
    set E : Subgroup L := (A ⊓ L).subgroupOf L with hE
    have hEe : IsElemAbelianTwo E := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · exact Subtype.ext (hAe.1 _ ((Subgroup.mem_subgroupOf.mp hx).1) _
          ((Subgroup.mem_subgroupOf.mp hy).1))
      · exact Subtype.ext (hAe.2 _ ((Subgroup.mem_subgroupOf.mp hx).1))
    have hcardE : Nat.card E = Nat.card ↥(A ⊓ L) := by
      rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
        hE, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    rw [← hcardE]
    exact matrix_quotient_card_elemAbelian_le h hφs hφk E hEe
  exact hc.trans (Nat.mul_le_mul_left _ (hd.trans he))

theorem false_of_unitaryEven
    {f : ℕ} (hf : 2 ≤ f) {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hU : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 f) :
    False := by
  obtain ⟨⟨hp, hf1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hU
  have hUD : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  let β : ↥L ⧸ Subgroup.center ↥L ≃* unitaryPSU hUD 3 :=
    e.trans (unitaryPSUEquiv hUD (by norm_num)).symm
  have hd : 6 * f ≤ Module.finrank (ZMod 2) V := by
    obtain ⟨ℓ, hℓ, hℓ2, hord, -, -, hnot3⟩ :=
      binary_multiple_six_exponents_have_primitive_prime_divisors hf
    have hℓ3 : ℓ ≠ 3 := fun h0 => hnot3 (by rw [h0]; exact dvd_mul_right 3 _)
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨-, x, -, -, hxord, -⟩ := exists_model_aut hUD hf hℓ hℓ3 hord
    obtain ⟨e2⟩ := nonempty_primeFormP_mulEquiv hUD
      (isPrimeFormGram_one' (K := K) (n := 3))
    have hdvd : ℓ ∣ Nat.card (unitaryPSU hUD 3) := by
      rw [← Nat.card_congr e2.toEquiv, ← hxord]
      exact orderOf_dvd_natCard x
    have h1 := orderOf_two_le_finrank_of_dvd_card_quotient β hℓ2 hdvd
    rw [hord] at h1
    exact h1
  have hm : m ≤ f + 1 := by
    obtain ⟨hAN, hAel, hAcard, hirr⟩ := exists_mulaut_data
      (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
    have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
    have hq := isQuasisimple_toMulSub h.L_comp.2.2
    have : Nontrivial (Multiplicative V) := hirr.1
    have : Group.IsPerfect ↥(toMulSub L) := hq.1
    have hc := card_elemAbelian_normalizer_le_unitary hf hUD hW (toMulSub L) hq.1 hirr.2
      ((cqEquiv_toMulSub_comp β)) (toMulSub A) hAN hAel
    rw [hAcard] at hc
    have hc' : 2 ^ m ≤ 2 ^ (f + 1) := by rw [pow_succ']; exact hc
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hc'
  have hb := h.bound
  omega

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
