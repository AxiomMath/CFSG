module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.CoverLift
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.PartOne.S15K.CommonEigen
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB

open Module Module.End

section Lin

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

theorem linearIndependent_of_eigen₂ {κ : Type*} (A B : End K W) (a b : κ → K)
    (hab : ∀ i j, a i = a j → b i = b j → i = j) (v : κ → W) (hv0 : ∀ k, v k ≠ 0)
    (hA : ∀ k, A (v k) = a k • v k) (hB : ∀ k, B (v k) = b k • v k) : LinearIndependent K v :=
  ((TauCeti.iSupIndep_iInf_eigenspace ![A, B]).comp (f := fun k => ![a k, b k])
    fun i j h => hab i j (by simpa using congrFun h 0)
      (by simpa using congrFun h 1)).linearIndependent
    _ (fun k => (Submodule.mem_iInf _).2 fun i => mem_eigenspace_iff.2 <| by
      fin_cases i
      exacts [hA k, hB k]) hv0

theorem exists_eigen_of_mapsTo [IsAlgClosed K] [FiniteDimensional K W] (R : End K W)
    {p : Submodule K W} (hp : p ≠ ⊥) (hR : ∀ w ∈ p, R w ∈ p) :
    ∃ v ∈ p, v ≠ 0 ∧ ∃ μ : K, R v = μ • v := by
  haveI := Submodule.nontrivial_iff_ne_bot.2 hp
  obtain ⟨μ, hμ⟩ := exists_eigenvalue (R.restrict hR)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  exact ⟨w, w.2, fun h => hw.2 (Subtype.ext h), μ, congrArg Subtype.val hw.apply_eq_smul⟩

theorem exists_eigen_ne_one [IsAlgClosed K] [FiniteDimensional K W] {T : End K W} {n : ℕ}
    (hn : (n : K) ≠ 0) (hT : T ^ n = 1) (hT1 : T ≠ 1) :
    ∃ c : K, c ≠ 1 ∧ eigenspace T c ≠ ⊥ := by
  obtain ⟨_, ⟨u, rfl⟩, hw0, c, hc⟩ := exists_eigen_of_mapsTo T
    (p := LinearMap.range (T - 1)) (by rwa [Ne, LinearMap.range_eq_bot, sub_eq_zero])
    (by rintro _ ⟨u, rfl⟩; exact ⟨T u, by simp only [LinearMap.sub_apply, one_apply, map_sub]⟩)
  refine ⟨c, ?_, fun h => hw0 ((Submodule.eq_bot_iff _).1 h _ (mem_eigenspace_iff.2 hc))⟩
  rintro rfl
  rw [one_smul] at hc
  have hfix : ∀ i : ℕ, (T ^ i) ((T - 1) u) = (T - 1) u := fun i => by
    induction i with
    | zero => rw [pow_zero, one_apply]
    | succ i ih => rw [pow_succ, mul_apply, hc, ih]
  have h := congrArg (· u) (geom_sum_mul T n)
  simp only [hT, sub_self, LinearMap.zero_apply, mul_apply, LinearMap.sum_apply, hfix,
    Finset.sum_const, Finset.card_range] at h
  exact hw0 ((smul_eq_zero.1 ((Nat.cast_smul_eq_nsmul K n _).trans h)).resolve_left hn)

theorem exists_eigen_of_commute [IsAlgClosed K] [FiniteDimensional K W] {T R : End K W}
    (hTR : Commute T R) {c : K} (hc : eigenspace T c ≠ ⊥) :
    ∃ v : W, v ≠ 0 ∧ T v = c • v ∧ ∃ d : K, R v = d • v := by
  obtain ⟨v, hv, hv0, d, hd⟩ := exists_eigen_of_mapsTo R hc fun w hw => mem_eigenspace_iff.2 <| by
    rw [← mul_apply, hTR.eq, mul_apply, mem_eigenspace_iff.1 hw, map_smul]
  exact ⟨v, hv0, mem_eigenspace_iff.1 hv, d, hd⟩

theorem exists_jointEigen [IsAlgClosed K] [FiniteDimensional K W] {T : End K W} {n : ℕ}
    (hn : (n : K) ≠ 0) (hT : T ^ n = 1) (hT1 : T ≠ 1) {R : End K W} (hTR : Commute T R) :
    ∃ v : W, v ≠ 0 ∧ ∃ c d : K, c ≠ 1 ∧ c ^ n = 1 ∧ T v = c • v ∧ R v = d • v := by
  obtain ⟨c, hc1, hc⟩ := exists_eigen_ne_one hn hT hT1
  obtain ⟨v, hv0, hTv, d, hd⟩ := exists_eigen_of_commute hTR hc
  exact ⟨v, hv0, c, d, hc1, CFSG.RankThree.PartOne.S15K.eigenvalue_pow_eq_one hT hv0 hTv, hTv, hd⟩

theorem eq_zero_of_eigen_ne_one [FiniteDimensional K W] {κ : Type*} [Fintype κ] {v : κ → W}
    (hv : LinearIndependent K v) (hdim : finrank K W ≤ Fintype.card κ) {B : End K W}
    {b : κ → K} (hb : ∀ k, B (v k) = b k • v k) (hb1 : ∀ k, b k ≠ 1) {w : W} (hw : B w = w) :
    w = 0 := by
  have hspan := hv.span_eq_top_of_card_eq_finrank' (le_antisymm hv.fintype_card_le_finrank hdim)
  have hw' : w ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw'
  simp only [map_sum, map_smul, hb, smul_smul] at hw
  have h0 := Fintype.linearIndependent_iff.1 hv (fun k => a k * (b k - 1)) (by
    simp only [mul_sub, mul_one, sub_smul, Finset.sum_sub_distrib, hw, sub_self])
  simp [fun k => (mul_eq_zero.1 (h0 k)).resolve_right (sub_ne_zero.2 (hb1 k))]

theorem apply_comm {M : Type*} [Monoid M] (ρ : M →* End K W) {a b c d : M} (h : a * b = c * d)
    (w : W) : ρ a (ρ b w) = ρ c (ρ d w) := by
  rw [← mul_apply, ← map_mul, h, map_mul, mul_apply]

variable {J : Type*} [Group J] (τ : J →* End K W)

theorem apply_of_conj {g x y : J} (h : g * x * g⁻¹ = y) (v : W) :
    τ y (τ g v) = τ g (τ x v) := by
  rw [← h, ← mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, mul_apply]

theorem apply_ne_zero (g : J) {v : W} (hv : v ≠ 0) : τ g v ≠ 0 := fun h => hv <| by
  have := congrArg (τ g⁻¹) h
  rwa [← mul_apply, ← map_mul, inv_mul_cancel, map_one, one_apply, map_zero] at this

end Lin

section Lift

variable {L J M : Type*} [Group L] [Group J] [Group M]

theorem exists_lift_hom [Finite L] [Finite J] [Finite M] (φ : J →* L)
    (hφ : Function.Surjective φ) {q : ℕ} [Fact q.Prime] (hq : Nat.Coprime q (Nat.card φ.ker))
    (hM : IsPGroup q M) (f : M →* L) {t : L} (ht : ∀ a, t * f a * t⁻¹ ∈ f.range) :
    ∃ (f' : M →* J) (t' : J), (∀ a, φ (f' a) = f a) ∧ φ t' = t ∧
      t' ∈ Subgroup.normalizer (f'.range : Set J) := by
  obtain ⟨S, t', -, hmap, hinj, ht', rfl⟩ := SEFive.exists_lift φ hφ hq
    (hM.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    (Subgroup.mem_normalizer_fintype fun _ ⟨a, ha⟩ => ha ▸ ht a)
  have hS : ∀ a, ∃ x ∈ S, φ x = f a := fun a => Subgroup.mem_map.1 (by rw [hmap]; exact ⟨a, rfl⟩)
  choose g hgS hg using hS
  let f' : M →* J :=
    { toFun := g
      map_one' := hinj (hgS 1) S.one_mem (by rw [hg, map_one, map_one])
      map_mul' := fun a b => hinj (hgS _) (S.mul_mem (hgS a) (hgS b)) (by
        rw [map_mul, hg, hg, hg, map_mul]) }
  have hr : f'.range = S := le_antisymm (by rintro _ ⟨a, rfl⟩; exact hgS a) fun x hx => by
    obtain ⟨a, ha⟩ : φ x ∈ f.range := hmap ▸ Subgroup.mem_map_of_mem φ hx
    exact ⟨a, hinj (hgS a) hx (by rw [hg, ha])⟩
  exact ⟨f', t', hg, rfl, hr ▸ ht'⟩

theorem conj_lift {φ : J →* L} {f : M →* L} (hf : Function.Injective f) {f' : M →* J}
    (hf' : ∀ a, φ (f' a) = f a) {g : J} (hg : g ∈ Subgroup.normalizer (f'.range : Set J))
    {a b : M} (h : φ g * f a * (φ g)⁻¹ = f b) : g * f' a * g⁻¹ = f' b := by
  obtain ⟨c, hc⟩ := (Subgroup.mem_normalizer_iff.1 hg (f' a)).1 ⟨a, rfl⟩
  have : c = b := hf (by rw [← hf' c, hc, map_mul, map_mul, map_inv, hf', h])
  rw [← hc, this]

end Lift

theorem coverActsTriviallyOnSmall_of_rep {p : ℕ} (hp : p.Prime) {L : Type*} [Group L]
    [IsSimpleGroup L]
    (h : ∀ (J : Type) [Group J] [Finite J] (φ : J →* L), Function.Surjective φ →
      Nat.Coprime (Nat.card φ.ker) (2 * p) → ∀ (K : Type) [Field K] [IsAlgClosed K],
      (2 : K) ≠ 0 → (p : K) ≠ 0 → ∀ (W : Type) [AddCommGroup W] [Module K W]
      [FiniteDimensional K W], finrank K W ≤ 4 → ∀ τ : J →* End K W,
      (∀ x, τ x = 1 → φ x = 1) → False) :
    CoverActsTriviallyOnSmall p L := by
  intro J _ _ hJ φ hφ hcop hsol ℓ hℓ hℓ2 hℓp V _ _ hcomm hpow hcard ρ
  refine (SEFive.ker_le_or_eq_one hJ φ hφ hsol ρ).resolve_left fun hker => ?_
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp (fun v => ⟨1, by simpa using hpow v⟩ : IsPGroup ℓ V)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hd
  letI : Module (ZMod ℓ) (Fin d → ZMod ℓ) := Pi.Function.module (Fin d) (ZMod ℓ) (ZMod ℓ)
  let toEnd : GL (Fin d) (ZMod ℓ) →* End (ZMod ℓ) (Fin d → ZMod ℓ) :=
    (Matrix.toLinAlgEquiv' (R := ZMod ℓ) (n := Fin d)).toAlgHom.toMonoidHom.comp
      (Units.coeHom (Matrix (Fin d) (Fin d) (ZMod ℓ)))
  have hne : ∀ {n : ℕ}, n.Prime → n ≠ ℓ → (n : AlgebraicClosure (ZMod ℓ)) ≠ 0 :=
    fun hn hnℓ h0 =>
      hnℓ ((Nat.prime_dvd_prime_iff_eq hℓ hn).1
        ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod ℓ)) ℓ _).1 h0)).symm
  refine h J φ hφ hcop (AlgebraicClosure (ZMod ℓ)) (hne Nat.prime_two (Ne.symm hℓ2))
    (hne hp (Ne.symm hℓp)) _ ?_ ((End.baseChangeHom (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))
      (Fin d → ZMod ℓ)).toMonoidHom.comp
        (toEnd.comp ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ρ)))
    fun x hx => hker ?_
  · rw [Module.finrank_baseChange]
    simp only [Module.finrank_fin_fun]
    exact (Nat.pow_le_pow_iff_right hℓ.one_lt).1 (hd ▸ hcard)
  · have hx' : End.baseChangeHom (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ)
        (toEnd (CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ x))) =
        End.baseChangeHom (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Fin d → ZMod ℓ) 1 :=
      hx.trans (map_one _).symm
    have h1 : toEnd (CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ x)) = toEnd 1 :=
      (LinearMap.baseChangeHom_injective (ZMod ℓ) (Fin d → ZMod ℓ) (AlgebraicClosure (ZMod ℓ))
        hx').trans (map_one toEnd).symm
    have h2 : CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ x) = 1 :=
      Units.ext ((Matrix.toLinAlgEquiv' (R := ZMod ℓ) (n := Fin d)).injective h1)
    exact MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff _).1 h2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB
