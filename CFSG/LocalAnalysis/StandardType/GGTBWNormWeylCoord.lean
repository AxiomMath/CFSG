module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormIsometry
public import CFSG.LocalAnalysis.StandardType.GGTBWNormFrame
public import CFSG.LocalAnalysis.StandardType.GGTBWNormFixedFree
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylAutInner
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace ExcWeylCoord

variable {p : ℕ} [Fact p.Prime] [NeZero p]

theorem exists_smul_of_commute_torusMulAut {τ : Tag} (hp2 : p ≠ 2)
    {M : CoxeterMatrix (Fin τ.rank)} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M τ.cartan)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (hdet : ((τ.cartan.det : ℤ) : ZMod p) ≠ 0)
    (f : MulAut (Multiplicative (Fin τ.rank → ZMod p)))
    (hf : ∀ w ∈ (ExcWeylOuter.torusMulAut τ p).range, f * w = w * f) :
    ∃ c : ZMod p, ∀ v, Multiplicative.toAdd (f (Multiplicative.ofAdd v)) = c • v := by
  classical
  let T0 : (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) :=
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (f (Multiplicative.ofAdd v))) fun v w => by
      rw [ofAdd_add, map_mul, toAdd_mul]
  let T : (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) := T0.toZModLinearMap p
  have hTv : ∀ v, T v = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) := fun _ => rfl
  let α : Fin τ.rank → Module.Dual (ZMod p) (Fin τ.rank → ZMod p) :=
    fun i => CFSG.RankThree.CentralCover.cartanFunctional τ p i
  let h : Fin τ.rank → (Fin τ.rank → ZMod p) := fun i => Pi.single i 1
  have hpair : ∀ i j, α i (h j) = (τ.cartan i j : ZMod p) := by
    intro i j
    change CFSG.RankThree.CentralCover.cartanFunctional τ p i (Pi.single j 1) = _
    rw [CFSG.RankThree.CentralCover.cartanFunctional_apply]
    simp [Pi.single_apply, hsymm j i]
  have hfix : ∀ v, (∀ i, α i v = 0) → v = 0 := by
    intro v hv
    refine Matrix.eq_zero_of_mulVec_eq_zero (M := τ.cartan.map (Int.castRingHom (ZMod p))) ?_ ?_
    · have e : (τ.cartan.map (Int.castRingHom (ZMod p))).det = ((τ.cartan.det : ℤ) : ZMod p) := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
      rw [e]
      exact hdet
    · funext i
      have hi := hv i
      change CFSG.RankThree.CentralCover.cartanFunctional τ p i v = 0 at hi
      rw [CFSG.RankThree.CentralCover.cartanFunctional_apply] at hi
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, eq_intCast, Pi.zero_apply]
      rw [← hi]
      exact Finset.sum_congr rfl fun j _ => by rw [hsymm]
  have hT : ∀ i v, T (v - α i v • h i) = T v - α i (T v) • h i := by
    intro i v
    have he := congrArg (fun a => Multiplicative.toAdd (a (Multiplicative.ofAdd v)))
      (hf (ExcWeylOuter.torusMulAut τ p (simple τ i)) ⟨_, rfl⟩)
    simp only [MulAut.mul_apply, ExcWeylOuter.torusMulAut_apply] at he
    rw [← TableBExc.torusRefl_eq_torusAct hsymm, TableBExc.torusRefl_eq] at he
    have he' : Multiplicative.toAdd (f (Multiplicative.ofAdd v)) -
        α i (Multiplicative.toAdd (f (Multiplicative.ofAdd v))) • h i =
        TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (f (Multiplicative.ofAdd v))) := by
      rw [← TableBExc.torusRefl_eq_torusAct hsymm, TableBExc.torusRefl_eq]
    rw [hTv, hTv]
    exact he.trans (he'.symm.trans rfl) |>.trans rfl
  exact ggWeylDatum_commutant_eq_smul hp2 hM hC h α hpair hfix T hT

theorem wNormConcl_of_weyl_coordinates {τ : Tag}
    (hrank : 3 ≤ τ.rank)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    (hNI : NormInducesInner (ExcWeylOuter.torusMulAut τ p).range)
    (hcomm : ∀ f : MulAut (Multiplicative (Fin τ.rank → ZMod p)),
      (∀ w ∈ (ExcWeylOuter.torusMulAut τ p).range, f * w = w * f) →
        ∃ c : ZMod p, ∀ v, Multiplicative.toAdd (f (Multiplicative.ofAdd v)) = c • v)
    {L : Type} [Group L] [Finite L] (A : Subgroup (MulAut L))
    (κ : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥A)
    (hW : (ExcWeylOuter.torusMulAut τ p).range.map (MulAut.congr κ).toMonoidHom =
      ggAutomizer (MulAut.conj : L →* MulAut L).range A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A = Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  classical
  let W := ggAutomizer (MulAut.conj : L →* MulAut L).range A
  have hmemW : ∀ x, x ∈ (ExcWeylOuter.torusMulAut τ p).range ↔ MulAut.congr κ x ∈ W := by
    intro x
    change _ ↔ MulAut.congr κ x ∈ ggAutomizer (MulAut.conj : L →* MulAut L).range A
    rw [← hW, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hNIW : NormInducesInner W :=
    NormInducesInner.of_mulEquiv (MulAut.congr κ).symm (W' := (ExcWeylOuter.torusMulAut τ p).range)
      (fun x => by rw [hmemW, MulEquiv.apply_symm_apply]) hNI
  letI : (MulAut.conj : L →* MulAut L).range.Normal := by
    constructor
    rintro a ⟨x, rfl⟩ b
    refine ⟨b x, ?_⟩
    apply MulEquiv.ext
    intro y
    change b x * y * (b x)⁻¹ = b (x * b⁻¹ y * x⁻¹)
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  have hsN : s ∈ Subgroup.normalizer (W : Set (MulAut ↥A)) :=
    mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal hs
  obtain ⟨w, hwW, hconj⟩ := hNIW s hsN
  let f : MulAut ↥A := w⁻¹ * s
  have hfc : ∀ u ∈ W, f * u = u * f := by
    intro u hu
    change (w⁻¹ * s) * u = u * (w⁻¹ * s)
    calc _ = w⁻¹ * (s * u * s⁻¹) * s := by group
      _ = u * (w⁻¹ * s) := by rw [hconj u hu]; group
  let f' := (MulAut.congr κ).symm f
  have hf'c : ∀ x ∈ (ExcWeylOuter.torusMulAut τ p).range, f' * x = x * f' := by
    intro x hx
    apply (MulAut.congr κ).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hfc _ ((hmemW x).mp hx)
  obtain ⟨c, hc⟩ := hcomm f' hf'c
  have hκf : ∀ v, f (κ (Multiplicative.ofAdd v)) = κ (Multiplicative.ofAdd (c • v)) := by
    intro v
    have h1 : f (κ (Multiplicative.ofAdd v)) = κ (f' (Multiplicative.ofAdd v)) := by
      change f (κ (Multiplicative.ofAdd v)) = κ (κ.symm (f (κ (Multiplicative.ofAdd v))))
      rw [MulEquiv.apply_symm_apply]
    rw [h1, ← hc v, ofAdd_toAdd]
  have hc0 : c ≠ 0 := by
    intro hz
    have hpos : 0 < τ.rank := by omega
    let e0 : Fin τ.rank → ZMod p := Pi.single ⟨0, hpos⟩ 1
    have h1 : f' (Multiplicative.ofAdd e0) = f' 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      rw [hc, hz, zero_smul, toAdd_one]
    have h2 : e0 = 0 := Multiplicative.ofAdd.injective (f'.injective h1)
    have h3 := congrArg (fun x : Fin τ.rank → ZMod p => x ⟨0, hpos⟩) h2
    simp [e0] at h3
  obtain ⟨u, hu⟩ : ∃ u : WeylGroup τ, w = MulAut.congr κ (ExcWeylOuter.torusMulAut τ p u) := by
    have hw' : (MulAut.congr κ).symm w ∈ (ExcWeylOuter.torusMulAut τ p).range := by
      rw [hmemW, MulEquiv.apply_symm_apply]
      exact hwW
    obtain ⟨u, hu⟩ := hw'
    exact ⟨u, by rw [hu, MulEquiv.apply_symm_apply]⟩
  have hsact : ∀ v : Fin τ.rank → ZMod p,
      s (κ (Multiplicative.ofAdd v)) =
        κ (Multiplicative.ofAdd (((Units.mk0 c hc0 : (ZMod p)ˣ) : ZMod p) •
          TableBExc.torusAct τ p u v)) := by
    intro v
    have hsw : s = w * f := by
      change s = w * (w⁻¹ * s)
      group
    rw [hsw, MulAut.mul_apply, hκf, hu, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, Units.val_mk0,
      ExcWeylOuter.torusMulAut_apply]
    congr 2
    have hadd : ∀ x y, TableBExc.torusAct τ p u (x + y) =
        TableBExc.torusAct τ p u x + TableBExc.torusAct τ p u y := by
      intro x y
      have hm := map_mul (ExcWeylOuter.torusMulAut τ p u) (Multiplicative.ofAdd x)
        (Multiplicative.ofAdd y)
      rw [← ofAdd_add, ExcWeylOuter.torusMulAut_apply, ExcWeylOuter.torusMulAut_apply,
        ExcWeylOuter.torusMulAut_apply, ← ofAdd_add] at hm
      exact Multiplicative.ofAdd.injective hm
    exact ((AddMonoidHom.mk' (TableBExc.torusAct τ p u) hadd).toZModLinearMap p).map_smul c v
  exact ggWNormConcl_of_scalar_weyl_coordinates ι φ h α κ hrank hdet hgen hW
    (Units.mk0 c hc0) u hsact

theorem wNormConcl_of_weyl_coordinates_E7E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    (hp2 : p ≠ 2)
    {L : Type} [Group L] [Finite L] (A : Subgroup (MulAut L))
    (κ : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥A)
    (hW : (ExcWeylOuter.torusMulAut τ p).range.map (MulAut.congr κ).toMonoidHom =
      ggAutomizer (MulAut.conj : L →* MulAut L).range A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A = Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  have hp : p.Prime := Fact.out
  rcases hτ with rfl | rfl
  · have hM : GGIsWeylMatrix CoxeterMatrix.E₇ :=
      Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), (ggCoxeterMatrix_reindex_refl _).symm⟩))
    have hC : GGIntCartan CoxeterMatrix.E₇ (Tag.cartan .E7) := by
      rw [show Tag.cartan .E7 = CartanMatrix.E 7 from cartanE_eq 7]
      exact ggIntCartan_E₇
    have hdet : ((Tag.E7.cartan.det : ℤ) : ZMod p) ≠ 0 := by
      rw [det_cartan_E7]
      intro h2
      have hd : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h2
      have hd' : p ∣ 2 := by exact_mod_cast hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd')
    exact wNormConcl_of_weyl_coordinates (by decide)
      (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inl rfl)) hp2)
      (normInducesInner_range_torusMulAut_E7 hp2)
      (fun f hf => exists_smul_of_commute_torusMulAut hp2 hM hC TableBExc.Three.cartan_symm_E7
        hdet f hf) A κ hW ι φ h α hgen hs
  · have hM : GGIsWeylMatrix CoxeterMatrix.E₈ :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), (ggCoxeterMatrix_reindex_refl _).symm⟩)))
    have hC : GGIntCartan CoxeterMatrix.E₈ (Tag.cartan .E8) := by
      rw [show Tag.cartan .E8 = CartanMatrix.E 8 from cartanE_eq 8]
      exact ggIntCartan_E₈
    have hdet : ((Tag.E8.cartan.det : ℤ) : ZMod p) ≠ 0 := by
      rw [det_cartan_E8, Int.cast_one]
      exact one_ne_zero
    exact wNormConcl_of_weyl_coordinates (by decide)
      (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2)
      (normInducesInner_range_torusMulAut_E8 hp2)
      (fun f hf => exists_smul_of_commute_torusMulAut hp2 hM hC TableBExc.Three.cartan_symm_E8
        hdet f hf) A κ hW ι φ h α hgen hs

theorem wNormConcl_of_centralCover_weylFrame_E7E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    (hp2 : p ≠ 2)
    {R L : Type} [Group R] [Group L] [Finite L]
    (ψ : L →* R) (hψ : Function.Surjective ψ)
    (Λ : R →* MulAut L) (hΛ : Function.Injective Λ)
    (hΛψ : ∀ l, Λ (ψ l) = MulAut.conj l)
    (E : Subgroup R) (A : Subgroup (MulAut L)) (hEA : E.map Λ = A)
    (t : Multiplicative (Fin τ.rank → ZMod p) →* R)
    (ht : Function.Injective t) (htr : t.range = E)
    (n : Fin τ.rank → R)
    (hns : ∀ i v, n i * t (Multiplicative.ofAdd v) * (n i)⁻¹ =
      t (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) v)))
    (hN : ∀ g ∈ Subgroup.normalizer (E : Set R), ∃ u : WeylGroup τ,
      ∀ v, g * t (Multiplicative.ofAdd v) * g⁻¹ =
        t (Multiplicative.ofAdd (TableBExc.torusAct τ p u v)))
    {Λ' V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ' → MulAut ↥A) (h : Λ' → V)
    (α : Λ' → Module.Dual (ZMod p) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A = Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  have hp : p.Prime := Fact.out
  obtain ⟨hn, -⟩ := exists_markedWeyl_ggAutomizer (hp.odd_of_ne_two hp2) E t ht htr n hns hN
  let κ0 : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥E :=
    (MonoidHom.ofInjective ht).trans (MulEquiv.subgroupCongr htr)
  let κE : ↥E ≃* ↥A :=
    (E.equivMapOfInjective Λ hΛ).trans (MulEquiv.subgroupCongr hEA)
  let κ : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥A := κ0.trans κE
  have hWE := ggAutomizer_eq_range_of_weyl_frame E t ht htr n hn hns hN
  have hΛr : Λ.range = (MulAut.conj : L →* MulAut L).range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := hψ x
      exact ⟨l, (hΛψ l).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨ψ l, hΛψ l⟩
  have hρ : (ExcWeylOuter.torusMulAut τ p).range.map (MulAut.congr κ).toMonoidHom =
      ggAutomizer (MulAut.conj : L →* MulAut L).range A := by
    have hmap := F4AutWeyl.ggAutomizer_map_eq hΛ (⊤ : Subgroup R) E hEA
    rw [Subgroup.map_top, hΛr] at hmap
    rw [hmap, ← hWE, Subgroup.map_map]
    congr 1
  exact wNormConcl_of_weyl_coordinates_E7E8 hτ hp2 A κ hρ ι φ h α hgen hs

end ExcWeylCoord

end CFSG.StandardType

end
