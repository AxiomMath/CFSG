module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.ClassicalInvolution.RouteD.TWYType
import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om8
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsField
import CFSG.RankThree.PartOne.K159.BorelSp
import CFSG.RankThree.PartOne.K159.RowFourType
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.GGQ2Prime

section Cases

open Module Polynomial CFSG.RankThree.PartOne.KCPrimary

private theorem card_linearEquiv_of_card_two {F M : Type*} [Field F] [Finite F]
    [AddCommGroup M] [Module F M] [FiniteDimensional F M] (hF : Nat.card F = 2) :
    Nat.card (M ≃ₗ[F] M) = ∏ i : Fin (finrank F M), (2 ^ finrank F M - 2 ^ (i : ℕ)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let b : Module.Basis (Fin (finrank F M)) F M := Module.finBasisOfFinrankEq F M rfl
  let e : GL (Fin (finrank F M)) F ≃* (M ≃ₗ[F] M) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F M)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF]

private theorem not_eleven_dvd_card_GL_two {n : ℕ} (hn : n ≤ 9) :
    ¬ 11 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

private theorem eq_of_mem_of_not_dvd_two {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 2) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] {d : ℕ} (hd : d ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V))
    {E : Submodule F V} (hE : ∀ y, ∀ v ∈ E, α y v ∈ E)
    (hGL : ¬ d ∣ ∏ i : Fin (finrank F E), (2 ^ finrank F E - 2 ^ (i : ℕ))) (y : Y) {v : V}
    (hv : v ∈ E) : α y v = v := by
  classical
  have hmap : ∀ y, E.map ((α y : V ≃ₗ[F] V) : V →ₗ[F] V) = E := fun y => by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq (α y) E)
    rintro _ ⟨w, hw, rfl⟩
    exact hE y w hw
  let ρ : Y →* (E ≃ₗ[F] E) :=
    { toFun := fun y => LinearEquiv.ofSubmodules (α y) E E (hmap y)
      map_one' := by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        rw [LinearEquiv.ofSubmodules_apply, map_one]
        rfl
      map_mul' := fun a b => by
        refine LinearEquiv.ext fun x => Subtype.ext ?_
        rw [LinearEquiv.ofSubmodules_apply, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          LinearEquiv.ofSubmodules_apply, LinearEquiv.ofSubmodules_apply] }
  have hρ : ∀ y (x : E), ((ρ y x : E) : V) = α y x := fun y x => rfl
  by_cases htriv : ∀ y, ρ y = 1
  · have := congrArg (fun e : E ≃ₗ[F] E => ((e ⟨v, hv⟩ : E) : V)) (htriv y)
    simpa [hρ] using this
  exfalso
  push Not at htriv
  obtain ⟨y₀, hy₀⟩ := htriv
  have hker : ρ.ker = ⊥ := (ρ.normal_ker.eq_bot_or_eq_top).resolve_right fun h =>
    hy₀ (h ▸ Subgroup.mem_top y₀ : y₀ ∈ ρ.ker)
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  have hdvd : Nat.card Y ∣ Nat.card (E ≃ₗ[F] E) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [card_linearEquiv_of_card_two hF] at hdvd
  exact hGL (hd.trans hdvd)

private theorem twelve_cases {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : finrank F V = 12) {z : V ≃ₗ[F] V}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {W : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup W]
    (h11 : 11 ∣ Nat.card W) (hWz : ∀ w ∈ W, w * z = z * w) :
    (∀ v, z v = v → v = 0) ∨
      (finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 2 ∧
        ∀ w ∈ W, ∀ v, z v = v → w v = v) ∨
      (finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 10 ∧
        ∀ w ∈ W, ∀ v ∈ LinearMap.range (z.toLinearMap - LinearMap.id), w v = v) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V)) fun a b h =>
      LinearEquiv.ext (congrFun h)
  have h2 : (2 : F) = 0 := by
    letI : Fintype F := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
    exact_mod_cast CharP.cast_eq_zero F 2
  have hvv : ∀ v : V, v + v = 0 := fun v => by rw [← two_smul F v, h2, zero_smul]
  have hneg : ∀ v : V, -v = v := fun v => neg_eq_of_add_eq_zero_right (hvv v)
  have hz3' : ∀ v, z (z (z v)) = v := fun v => by
    have h := LinearEquiv.congr_fun hz3 v
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  set C := LinearMap.ker (z.toLinearMap - LinearMap.id) with hCdef
  set U := LinearMap.range (z.toLinearMap - LinearMap.id) with hUdef
  have hmemC : ∀ v, v ∈ C ↔ z v = v := fun v => by
    rw [hCdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero]
  have hmemU : ∀ v, v ∈ U ↔ ∃ x, z x + x = v := fun v => by
    rw [hUdef, LinearMap.mem_range]
    refine exists_congr fun x => ?_
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_add_neg, hneg]
  have hU3 : ∀ u ∈ U, z (z u) + z u + u = 0 := by
    intro u hu
    obtain ⟨x, rfl⟩ := (hmemU u).1 hu
    simp only [map_add]
    rw [hz3']
    have : x + z (z x) + (z (z x) + z x) + (z x + x) = (x + x) + (z x + z x) +
        (z (z x) + z (z x)) := by abel
    rw [this]
    simp only [hvv]
  have hUker : U = primaryComponent z.toLinearMap (X ^ 2 + X + 1) := by
    ext u
    rw [mem_primaryComponent]
    have hev : aeval z.toLinearMap (X ^ 2 + X + 1 : F[X]) u = z (z u) + z u + u := by
      simp [pow_two, Module.End.mul_apply]
    rw [hev]
    refine ⟨hU3 u, fun h => (hmemU u).2 ⟨z u, ?_⟩⟩
    have : z (z u) + z u = z (z u) + z u + u + u := by
      rw [add_assoc (z (z u) + z u) u u, hvv, add_zero]
    rw [this, h, zero_add]
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : F[X])) :=
    ⟨CFSG.HardMathSupport.Timmesfeld.CrossChar.irreducible_cyc3 hF⟩
  have hUeven : Even (finrank F U) := by
    rw [hUker, finrank_primaryComponent]
    have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
    rw [hdeg]
    exact even_two_mul _
  have hdisj : Disjoint C U := by
    rw [Submodule.disjoint_def]
    intro v hvC hvU
    have hz : z v = v := (hmemC v).1 hvC
    have := hU3 v hvU
    rw [hz, hz, hvv, zero_add] at this
    exact this
  have hcodisj : C ⊔ U = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hc : z (z v) + z v + v ∈ C := (hmemC _).2 (by rw [map_add, map_add, hz3']; abel)
    have hu : z (z v) + z v ∈ U := (hmemU _).2 ⟨z v, rfl⟩
    have : v = (z (z v) + z v + v) + (z (z v) + z v) := by
      rw [show z (z v) + z v + v + (z (z v) + z v) = (z (z v) + z (z v)) + (z v + z v) + v by
        abel, hvv, hvv, zero_add, zero_add]
    rw [this]
    exact Submodule.add_mem_sup hc hu
  have hdim : finrank F C + finrank F U = 12 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq C U
    rw [hcodisj, disjoint_iff.1 hdisj, finrank_top, finrank_bot, add_zero, hV] at this
    exact this.symm
  have hWC : ∀ w : W, ∀ v ∈ C, (w : V ≃ₗ[F] V) v ∈ C := fun w v hv => by
    rw [hmemC] at hv ⊢
    have := LinearEquiv.congr_fun (hWz w w.2) v
    simp only [LinearEquiv.mul_apply] at this
    rw [← this, hv]
  have hWU : ∀ w : W, ∀ v ∈ U, (w : V ≃ₗ[F] V) v ∈ U := fun w v hv => by
    obtain ⟨x, rfl⟩ := (hmemU v).1 hv
    refine (hmemU _).2 ⟨(w : V ≃ₗ[F] V) x, ?_⟩
    have := LinearEquiv.congr_fun (hWz w w.2) x
    simp only [LinearEquiv.mul_apply] at this
    rw [map_add, this]
  have htriv : ∀ E : Submodule F V, (∀ w : W, ∀ v ∈ E, (w : V ≃ₗ[F] V) v ∈ E) →
      finrank F E ≤ 9 → ∀ w : W, ∀ v ∈ E, (w : V ≃ₗ[F] V) v = v := fun E hE hdimE w v hv =>
    eq_of_mem_of_not_dvd_two hF h11 W.subtype hE (not_eleven_dvd_card_GL_two hdimE) w hv
  have hU0 : finrank F U ≠ 0 := by
    intro h0
    apply hz1
    have hUbot : U = ⊥ := Submodule.finrank_eq_zero.1 h0
    refine LinearEquiv.ext fun v => ?_
    have hm : z v + v ∈ U := (hmemU _).2 ⟨v, rfl⟩
    rw [hUbot, Submodule.mem_bot] at hm
    have := eq_neg_of_add_eq_zero_left hm
    rw [hneg] at this
    exact this
  have hnot : ¬ (finrank F C ≤ 9 ∧ finrank F U ≤ 9) := by
    rintro ⟨hC9, hU9⟩
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    apply hw
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have hv : v ∈ C ⊔ U := hcodisj ▸ Submodule.mem_top
    obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.1 hv
    show (w : V ≃ₗ[F] V) (c + u) = c + u
    rw [map_add, htriv C hWC hC9 w c hc, htriv U hWU hU9 w u hu]
  obtain ⟨k, hk⟩ := hUeven
  by_cases hU10 : 10 ≤ finrank F U
  · rcases (by omega : finrank F U = 10 ∨ finrank F U = 12) with h10 | h12
    · right; left
      exact ⟨by omega, fun w hw v hv => htriv C hWC (by omega) ⟨w, hw⟩ v ((hmemC v).2 hv)⟩
    · left
      intro v hv
      have hCbot : C = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
      have hvC : v ∈ C := (hmemC v).2 hv
      rw [hCbot, Submodule.mem_bot] at hvC
      exact hvC
  · have hC10 : 10 ≤ finrank F C := by
      by_contra hlt
      exact hnot ⟨by omega, by omega⟩
    right; right
    exact ⟨by omega, fun w hw v hv => htriv U hWU (by omega) ⟨w, hw⟩ v hv⟩

end Cases

section Free

open Polynomial Module CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem aeval_cyc3_eq_zero_of_fixedFree {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0) :
    aeval z.toLinearMap (cyc3 F) = 0 := by
  rw [aeval_cyc3]
  refine LinearMap.ext fun v => ?_
  have hz3' : z (z (z v)) = v := by
    have h := LinearEquiv.congr_fun hz3 v
    simpa [pow_succ] using h
  have hw : z (z (z v) + z v + v) = z (z v) + z v + v := by
    rw [map_add, map_add, hz3']
    abel
  have h0 := hfix _ hw
  simpa [pow_two] using h0

private theorem primaryComponent_cyc3_eq_top {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0) :
    primaryComponent z.toLinearMap (cyc3 F) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_primaryComponent, aeval_cyc3_eq_zero_of_fixedFree hz3 hfix, LinearMap.zero_apply]

private theorem aeval_cyc3_eq {F : Type} [Field F] {A : Type*} [CommRing A] [Algebra F A]
    (a : A) : aeval a (cyc3 F) = a ^ 2 + a + 1 := by
  simp [cyc3]

private theorem eq_cyc3_of_mem_primaryFactors {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 2) {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1)
    (hfix : ∀ v, z v = v → v = 0) {k : F[X]} (hk : k ∈ primaryFactors z.toLinearMap) :
    k = cyc3 F := by
  obtain ⟨hki, hkm, hkd⟩ := mem_primaryFactors.mp hk
  have hdvd : k ∣ cyc3 F :=
    hkd.trans (minpoly.dvd F _ (aeval_cyc3_eq_zero_of_fixedFree hz3 hfix))
  exact eq_of_monic_of_associated hkm (monic_cyc3 F)
    (hki.associated_of_dvd (irreducible_cyc3 hF) hdvd)

private theorem mem_supportedBlock_cyc3 {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) {Q : QuadraticForm F V} {z : V ≃ₗ[F] V}
    (hz3 : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0) {g : V ≃ₗ[F] V}
    (hg : g ∈ isometryCentralizer Q z) : g ∈ supportedBlock Q z (cyc3 F) :=
  mem_supportedBlock.mpr ⟨hg, fixes_othersSpace_iff.mpr fun _ hk hkh _ _ _ =>
    absurd (eq_cyc3_of_mem_primaryFactors hF hz3 hfix hk) hkh⟩

private theorem blockDet_self_cyc3 {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) {Q : QuadraticForm F V} {z : V ≃ₗ[F] V}
    (hzB : z ∈ supportedBlock Q z (cyc3 F))
    (hm : primaryMultiplicity z.toLinearMap (cyc3 F) = 6) :
    blockDet Q z (cyc3 F) ⟨z, hzB⟩ = 1 := by
  have : Fact (Irreducible (cyc3 F)) := ⟨irreducible_cyc3 hF⟩
  have hroot : ((blockGL Q z (cyc3 F) ⟨z, hzB⟩ : BlockGL z (cyc3 F)) :
      Module.End (AdjoinRoot (cyc3 F)) (primaryComponent z.toLinearMap (cyc3 F))) =
      AdjoinRoot.root (cyc3 F) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [coe_blockGL, LinearMap.smul_apply, LinearMap.id_apply, coe_root_smul_primaryComponent]
    rfl
  have hm' : finrank (AdjoinRoot (cyc3 F)) (primaryComponent z.toLinearMap (cyc3 F)) = 6 := hm
  rw [blockDet_apply, hroot, LinearMap.det_smul, LinearMap.det_id, mul_one, hm']
  have hr : AdjoinRoot.root (cyc3 F) ^ 2 + AdjoinRoot.root (cyc3 F) + 1 = 0 := by
    have h := AdjoinRoot.aeval_eq (f := cyc3 F) (cyc3 F)
    rw [AdjoinRoot.mk_self] at h
    rw [← aeval_cyc3_eq (F := F), h]
  linear_combination (AdjoinRoot.root (cyc3 F) ^ 4 - AdjoinRoot.root (cyc3 F) ^ 3 +
    AdjoinRoot.root (cyc3 F) - 1) * hr

private theorem exists_quadraticForm_polar_eq_of_fixedFree {F V : Type} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] (hF : Nat.card F = 2) {f : LinearMap.BilinForm F V}
    (halt : f.IsAlt) {d : V ≃ₗ[F] V} (hd3 : d ^ 3 = 1) (hd : ∀ v, d v = v → v = 0)
    (hdf : ∀ u v, f (d u) (d v) = f u v) :
    ∃ Q : QuadraticForm F V, (∀ v, Q v = f v (d v)) ∧
      ∀ x y, QuadraticMap.polar Q x y = f x y := by
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rwa [← Nat.card_eq_fintype_card, hF, Nat.cast_ofNat] at h
  have hww : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul F x, h2, zero_smul]
  have hneg : ∀ x : V, -x = x := fun x => neg_eq_of_add_eq_zero_right (hww x)
  have hd3' : ∀ y, d (d (d y)) = y := fun y => by
    have h := LinearEquiv.congr_fun hd3 y
    simpa [pow_succ] using h
  have hd2 : ∀ v, d (d v) + d v + v = 0 := fun v => by
    have hw : d (d (d v) + d v + v) = d (d v) + d v + v := by
      rw [map_add, map_add, hd3' v]
      abel
    exact hd _ hw
  have hsym : ∀ x y, f y x = f x y := fun x y => by
    rw [← halt.neg_eq x y]
    exact neg_eq_of_add_eq_zero_right (by rw [← two_mul, h2, zero_mul])
  refine ⟨LinearMap.BilinMap.toQuadraticMap (f.compl₂ (d : V →ₗ[F] V)), fun v => rfl,
    fun x y => ?_⟩
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  show f x (d y) + f y (d x) = f x y
  rw [(hsym (d x) y).trans (hdf (d x) y).symm, ← LinearMap.map_add₂]
  have h3 : x + d (d x) = d x := by
    have : x + d (d x) + d x = 0 := by rw [← hd2 x]; abel
    rw [eq_neg_of_add_eq_zero_left this, hneg]
  rw [h3]
  exact hdf x y

private theorem twFreeOrth_holds {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : V ≃ₗ[F] V}
    (hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hz3 : z ^ 3 = 1)
    (hfix : ∀ v, z v = v → v = 0) {M W : Subgroup (V ≃ₗ[F] V)}
    (hMz : M ≤ Subgroup.centralizer {z}) (hM : orthDerived Q ⊓ Subgroup.centralizer {z} ≤ M)
    (hWO : W ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hcomp : CFSG.Open.IsComponentOf W M)
    (hZ : Subgroup.center W = ⊥) : False := by
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rwa [← Nat.card_eq_fintype_card, hF, Nat.cast_ofNat] at h
  have h3 : (3 : F) ≠ 0 := by
    have : (3 : F) = 2 + 1 := by norm_num
    rw [this, h2, zero_add]
    exact one_ne_zero
  have hx : OddOrderIsometry Q 3 z :=
    ⟨hzO, hz3, h3, fun v hv => hQ.1 v fun w => by simpa using hv w⟩
  have : Fact (Irreducible (cyc3 F)) := ⟨irreducible_cyc3 hF⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank F V)
  have htop := primaryComponent_cyc3_eq_top hz3 hfix
  have hne : primaryComponent z.toLinearMap (cyc3 F) ≠ ⊥ := by
    rw [htop]
    exact top_ne_bot
  have hh : cyc3 F ∈ primaryFactors z.toLinearMap :=
    mem_primaryFactors_of_primaryComponent_ne_bot (irreducible_cyc3 hF) (monic_cyc3 F) hne
  have hm : primaryMultiplicity z.toLinearMap (cyc3 F) = 6 := by
    have h1 := finrank_primaryComponent (x := z.toLinearMap) (a := cyc3 F)
    rw [natDegree_cyc3] at h1
    have h12 : finrank F (primaryComponent z.toLinearMap (cyc3 F)) = 12 := by
      rw [htop, finrank_top, hV]
    have : primaryMultiplicity z.toLinearMap (cyc3 F) =
      finrank (AdjoinRoot (cyc3 F)) (primaryComponent z.toLinearMap (cyc3 F)) := rfl
    omega
  have hq : CFSG.IsQuasisimple ↥(specialBlock Q z (cyc3 F)) :=
    orth2_isQuasisimple_specialBlock_selfDual hx (by decide) hh (cyc3_ne_X_sub_one F)
      (reciprocal_cyc3 F).symm (by omega)
  have hSO : specialBlock Q z (cyc3 F) ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (specialBlock_le_isometryCentralizer _).trans fun _ hg => (Subgroup.mem_inf.mp hg).1
  have hSz : specialBlock Q z (cyc3 F) ≤ Subgroup.centralizer {z} :=
    (specialBlock_le_isometryCentralizer _).trans fun _ hg => (Subgroup.mem_inf.mp hg).2
  have hSM : specialBlock Q z (cyc3 F) ≤ M := fun g hg =>
    hM (Subgroup.mem_inf.mpr ⟨specialBlock_le_orthDerived_of_perfect hq.1 hSO hg, hSz hg⟩)
  have hWB : W ≤ supportedBlock Q z (cyc3 F) := fun w hw =>
    mem_supportedBlock_cyc3 hF hz3 hfix (Subgroup.mem_inf.mpr ⟨hWO hw, hMz (hcomp.1 hw)⟩)
  have hWS : W ≤ specialBlock Q z (cyc3 F) := by
    intro w hw
    let ψ : ↥W →* (AdjoinRoot (cyc3 F))ˣ :=
      ((blockDet Q z (cyc3 F)).comp (Subgroup.inclusion hWB)).toHomUnits
    have h1 : ψ ⟨w, hw⟩ = 1 := Abelianization.commutator_subset_ker ψ
      (by rw [hcomp.2.2.1]; exact Subgroup.mem_top _)
    exact mem_specialBlock.mpr ⟨hWB hw, congrArg Units.val h1⟩
  have hWsub : IsSubnormal W (specialBlock Q z (cyc3 F)) := by
    have := CFSG.Open.IsSubnormal.inf_of_le hcomp.2.1 hSM
    rwa [inf_eq_left.mpr hWS] at this
  have hWeq : W = specialBlock Q z (cyc3 F) :=
    CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
      ⟨hWS, hWsub, hcomp.2.2⟩ ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hzB : z ∈ supportedBlock Q z (cyc3 F) := mem_supportedBlock_cyc3 hF hz3 hfix
    (Subgroup.mem_inf.mpr ⟨hzO, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have hzW : z ∈ W := by
    rw [hWeq]
    exact mem_specialBlock.mpr ⟨hzB, blockDet_self_cyc3 hF hzB hm⟩
  have hzc : (⟨z, hzW⟩ : ↥W) ∈ Subgroup.center ↥W := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hSz (hWS g.2)))
  rw [hZ, Subgroup.mem_bot] at hzc
  have hz1 : z = 1 := congrArg Subtype.val hzc
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (hfix v (by rw [hz1]; rfl))

private theorem twFreeSp_holds {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : finrank F V = 12)
    {B : LinearMap.BilinForm F V} (hBalt : B.IsAlt) (hBnd : B.Nondegenerate) {z : V ≃ₗ[F] V}
    (hzB : z ∈ TauCeti.BilinForm.isometryGroup B) (hz3 : z ^ 3 = 1)
    (hfix : ∀ v, z v = v → v = 0) {M W : Subgroup (V ≃ₗ[F] V)}
    (hMz : M ≤ Subgroup.centralizer {z})
    (hM : TauCeti.BilinForm.isometryGroup B ⊓ Subgroup.centralizer {z} ≤ M)
    (hMB : M ≤ TauCeti.BilinForm.isometryGroup B) (hcomp : CFSG.Open.IsComponentOf W M)
    (hZ : Subgroup.center W = ⊥) : False := by
  have hzf : ∀ u v, B (z u) (z v) = B u v := TauCeti.BilinForm.mem_isometryGroup_iff.mp hzB
  obtain ⟨Q, hQv, hQp⟩ := exists_quadraticForm_polar_eq_of_fixedFree hF hBalt hz3 hfix hzf
  have hpol : QuadraticMap.polarBilin Q = B := LinearMap.ext₂ fun x y => by
    rw [QuadraticMap.polarBilin_apply_apply, hQp]
  have hQinv : ∀ g : V ≃ₗ[F] V, g ∈ TauCeti.BilinForm.isometryGroup B → g * z = z * g →
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg hgz =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      have h : g (z v) = z (g v) := LinearEquiv.congr_fun hgz v
      rw [hQv, hQv, ← h, TauCeti.BilinForm.mem_isometryGroup_iff.mp hg]
  have hBO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      g ∈ TauCeti.BilinForm.isometryGroup B := fun g hg =>
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun u v => by
      rw [← hQp, ← hQp, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg]
  refine twFreeOrth_holds hF hV (Q := Q) (hpol ▸ hBnd) (z := z) (hQinv z hzB rfl) hz3 hfix
    (M := M) (W := W) hMz (fun g hg => ?_) (fun w hw => ?_) hcomp hZ
  · obtain ⟨hgΩ, hgz⟩ := Subgroup.mem_inf.mp hg
    exact hM (Subgroup.mem_inf.mpr ⟨hBO g (orthDerived_le_orthogonalGroup hgΩ), hgz⟩)
  · exact hQinv w (hMB (hcomp.1 hw))
      (Subgroup.mem_centralizer_singleton_iff.mp (hMz (hcomp.1 hw)))

end Free

section Ten

open Module Polynomial CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary

private theorem twTenOrth_holds {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (_hV : finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : V ≃ₗ[F] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hz3 : z ^ 3 = 1)
    (hd : finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 10)
    {M W : Subgroup (V ≃ₗ[F] V)} (hMz : M ≤ Subgroup.centralizer {z})
    (hM : orthDerived Q ⊓ Subgroup.centralizer {z} ≤ M)
    (hWO : W ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hWU : ∀ w ∈ W, ∀ v ∈ LinearMap.range (z.toLinearMap - LinearMap.id), w v = v)
    (hWM : CFSG.Open.IsComponentOf W M) (hW : Nat.card W = 13685760) : False := by
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 1) le_rfl (by rw [hF, pow_one])
  have hx : OddOrderIsometry Q 3 z := by
    refine ⟨hz, hz3, ?_, fun v hv => hQ.1 v fun w => by simpa using hv w⟩
    intro h0
    have : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h0
    omega
  have hC : finrank F (fixedSpace z) = 10 := hd
  set T := supportedFixedDerived Q z with hT
  have hTq : CFSG.Open.IsQuasisimple T := by
    have hsing := CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.exists_threeSingular_of_eight_le
      hx.polarBilin_fixed_nondegenerate (by rw [hC]; norm_num)
    obtain ⟨hp, hs, -⟩ := hx.isQuasisimple_supportedFixedDerived hsing
    exact ⟨hp.commutator_eq_top, hs⟩
  have hTM : T ≤ M := fun g hg => hM (Subgroup.mem_inf.mpr
    ⟨hx.supportedFixedDerived_le_orthDerived hg,
      (Subgroup.mem_inf.mp (supportedFixedDerived_le_isometryCentralizer hg)).2⟩)
  have hWF : W ≤ supportedBlock Q z (X - 1) := by
    intro w hw
    refine mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr ⟨hWO hw, hMz (hWM.1 hw)⟩, fun v hv => ?_⟩
    exact hWU w hw v (CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.othersSpace_le_range hx hv)
  have hWT : W ≤ T := by
    have hperf : ⁅W, W⁆ = W := by
      rw [← Subgroup.map_subtype_commutator, hWM.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hperf, hT, hx.supportedFixedDerived_eq]
    exact Subgroup.commutator_mono hWF hWF
  have hsub : IsSubnormal W T := by
    have := CFSG.Open.IsSubnormal.inf_of_le hWM.2.1 hTM
    rwa [inf_eq_left.mpr hWT] at this
  have hWeq : W = T := CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
    ⟨hWT, hsub, hWM.2.2⟩ hTq
  have hcard : Nat.card W = Nat.card (orthDerived (Q.comp (fixedSpace z).subtype)) := by
    rw [hWeq]
    exact Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv
  rw [hW] at hcard
  rcases CFSG.SeitzReduction.OmegaPilot.card_derivedOrthogonal_of_regular (g := 1) (n := 5)
    le_rfl (by rw [hF, pow_one]) (by norm_num) (Q.comp (fixedSpace z).subtype)
    hx.polarBilin_fixed_nondegenerate (by rw [hC]) with h | h
  · rw [← hcard] at h
    revert h
    simp only [CFSG.Open.ordD]
    decide
  · rw [← hcard] at h
    revert h
    simp only [CFSG.Open.ordTwistedD]
    decide

private theorem twTenSp_holds {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : finrank F V = 12)
    {B : LinearMap.BilinForm F V} (hB : B.IsAlt) (hBnd : B.Nondegenerate) {z : V ≃ₗ[F] V}
    (hz : z ∈ TauCeti.BilinForm.isometryGroup B) (hz3 : z ^ 3 = 1)
    (hd : finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 10)
    {M W : Subgroup (V ≃ₗ[F] V)} (hMz : M ≤ Subgroup.centralizer {z})
    (hM : TauCeti.BilinForm.isometryGroup B ⊓ Subgroup.centralizer {z} ≤ M)
    (hMB : M ≤ TauCeti.BilinForm.isometryGroup B)
    (hWU : ∀ w ∈ W, ∀ v ∈ LinearMap.range (z.toLinearMap - LinearMap.id), w v = v)
    (hWM : CFSG.Open.IsComponentOf W M) (hW : Nat.card W = 13685760) : False := by
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 1) le_rfl (by rw [hF, pow_one])
  set C : Submodule F V := fixedSpace z with hCdef
  set U : Submodule F V := LinearMap.range (z.toLinearMap - LinearMap.id) with hUdef
  have hC : finrank F C = 10 := hd
  have hzB : ∀ x y, B (z x) (z y) = B x y := TauCeti.BilinForm.mem_isometryGroup_iff.mp hz
  have hzC : ∀ c ∈ C, z c = c := fun c hc => mem_fixedSpace.mp hc
  have hvv : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  have hz3v : ∀ v, z (z (z v)) = v := fun v => by
    have := congrArg (fun g : V ≃ₗ[F] V => g v) hz3
    simpa [pow_succ] using this
  have hzU : ∀ u ∈ U, z u ∈ U := by
    rintro _ ⟨w, rfl⟩
    exact ⟨z w, by simp⟩
  have horth : ∀ c ∈ C, ∀ u ∈ U, B c u = 0 := by
    rintro c hc _ ⟨w, rfl⟩
    have h1 : B c (z w) = B c w := by rw [← hzB c w, hzC c hc]
    simp [h1]
  have horth' : ∀ u ∈ U, ∀ c ∈ C, B u c = 0 := by
    rintro _ ⟨w, rfl⟩ c hc
    have h1 : B (z w) c = B w c := by rw [← hzB w c, hzC c hc]
    simp [h1]
  have hdisj : Disjoint C U := by
    rw [Submodule.disjoint_def]
    rintro v hvC ⟨w, rfl⟩
    have h1 : z ((z.toLinearMap - LinearMap.id : V →ₗ[F] V) w) =
        (z.toLinearMap - LinearMap.id : V →ₗ[F] V) w := hzC _ hvC
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub] at h1 ⊢
    have h2 : z (z w) = w := by
      calc z (z w) = (z (z w) - z w) + z w := by abel
        _ = (z w - w) + z w := by rw [h1]
        _ = (z w + z w) - w := by abel
        _ = w := by rw [hvv, zero_sub, neg_eq_iff_add_eq_zero]; exact hvv w
    have h3 : z w = w := by
      have := hz3v w
      rwa [h2] at this
    rw [h3, sub_self]
  have hU : finrank F U = 2 := by
    have h : finrank F U + finrank F C = finrank F V :=
      LinearMap.finrank_range_add_finrank_ker (z.toLinearMap - LinearMap.id)
    omega
  have hcompl : IsCompl C U :=
    (Submodule.isCompl_iff_disjoint C U (by omega)).mpr hdisj
  set BC : LinearMap.BilinForm F C := B.restrict C with hBC
  have hBCalt : BC.IsAlt := fun x => hB x
  have hBCnd : BC.Nondegenerate := by
    refine ⟨fun x hx => Subtype.ext (hBnd.1 x fun v => ?_),
      fun y hy => Subtype.ext (hBnd.2 y fun v => ?_)⟩
    · obtain ⟨c, u, rfl⟩ := exists_coe_add_of_isCompl hcompl v
      rw [map_add, horth x x.2 u u.2, add_zero]
      exact hx c
    · obtain ⟨c, u, rfl⟩ := exists_coe_add_of_isCompl hcompl v
      rw [map_add, LinearMap.add_apply, horth' u u.2 y y.2, add_zero]
      exact hy c
  set T : Subgroup (V ≃ₗ[F] V) := (TauCeti.BilinForm.isometryGroup B ⊓
    Subgroup.centralizer {z}) ⊓ fixingSubgroup (V ≃ₗ[F] V) (U : Set V) with hT
  have hTB : ∀ g ∈ T, ∀ x y, B (g x) (g y) = B x y := fun g hg =>
    TauCeti.BilinForm.mem_isometryGroup_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
  have hTz : ∀ g ∈ T, g ∈ Subgroup.centralizer ({z} : Set (V ≃ₗ[F] V)) := fun g hg =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
  have hTU : ∀ g ∈ T, ∀ u ∈ U, g u = u := fun g hg u hu =>
    (mem_fixingSubgroup_iff _).mp (Subgroup.mem_inf.mp hg).2 u hu
  let ρ : T →* (C ≃ₗ[F] C) :=
    { toFun := fun g => restrictEquiv C g.1 (fun _ hw => mem_fixedSpace_of_apply (hTz _ g.2) hw)
        (fun _ hw => mem_fixedSpace_of_apply (symm_mem_centralizer z (hTz _ g.2)) hw)
      map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => LinearEquiv.ext fun _ => Subtype.ext rfl }
  have hρB : ∀ g, ρ g ∈ TauCeti.BilinForm.isometryGroup BC := fun g =>
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => hTB g.1 g.2 x y
  let ρ' : T →* TauCeti.BilinForm.isometryGroup BC := ρ.codRestrict _ hρB
  have hinj : Function.Injective ρ' := by
    intro g g' hgg
    have hgg' : ρ g = ρ g' := congrArg Subtype.val hgg
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨c, u, rfl⟩ := exists_coe_add_of_isCompl hcompl v
    have h1 : g.1 c = g'.1 c := congrArg (fun φ : C ≃ₗ[F] C => (φ c : V)) hgg'
    rw [map_add, map_add, h1, hTU g.1 g.2 u u.2, hTU g'.1 g'.2 u u.2]
  have hsurj : Function.Surjective ρ' := by
    rintro ⟨φ, hφ⟩
    have hφB : ∀ x y : C, B (φ x) (φ y) = B x y := TauCeti.BilinForm.mem_isometryGroup_iff.mp hφ
    set g : V ≃ₗ[F] V := glue hcompl φ 1 with hg
    have hgapp : ∀ (c : C) (u : U), g ((c : V) + u) = (φ c : V) + u := fun c u => by
      rw [hg, glue_apply]
      rfl
    have hgT : g ∈ T := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [TauCeti.BilinForm.mem_isometryGroup_iff]
        intro x y
        obtain ⟨c, u, rfl⟩ := exists_coe_add_of_isCompl hcompl x
        obtain ⟨c', u', rfl⟩ := exists_coe_add_of_isCompl hcompl y
        rw [hgapp, hgapp]
        simp only [map_add, LinearMap.add_apply]
        rw [horth _ (φ c).2 _ u'.2, horth' _ u.2 _ (φ c').2, horth _ c.2 _ u'.2,
          horth' _ u.2 _ c'.2, hφB]
      · rw [mem_centralizer_iff z]
        intro v
        obtain ⟨c, u, rfl⟩ := exists_coe_add_of_isCompl hcompl v
        have h1 : z ((c : V) + u) = (c : V) + ((⟨z u, hzU u u.2⟩ : U) : V) := by
          rw [map_add, hzC c c.2]
        rw [h1, hgapp, hgapp, map_add, hzC _ (φ c).2]
      · rw [mem_fixingSubgroup_iff]
        intro u hu
        show g u = u
        simpa using hgapp 0 ⟨u, hu⟩
    refine ⟨⟨g, hgT⟩, Subtype.ext (LinearEquiv.ext fun c => Subtype.ext ?_)⟩
    show g c = φ c
    simpa using hgapp c 0
  let e : T ≃* TauCeti.BilinForm.isometryGroup BC := MulEquiv.ofBijective ρ' ⟨hinj, hsurj⟩
  obtain ⟨e2⟩ := CFSG.RankThree.PartOne.K159.nonempty_isometryGroup_mulEquiv_statedSp BC hBCalt
    hBCnd (m := 5) (by rw [hC])
  have hTq : CFSG.Open.IsQuasisimple T := by
    obtain ⟨hp, hs, -⟩ := CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.trans e2).symm
      (CFSG.LieType.Universal.Symplectic.isQuasisimple 5 F (by norm_num)
        (Or.inr (Or.inr ⟨hF, by norm_num⟩)))
    exact ⟨hp.commutator_eq_top, hs⟩
  have hcardT : Nat.card T = Nat.card (StatedSp 5 F) := Nat.card_congr (e.trans e2).toEquiv
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF] at hcardT
  have hWT : W ≤ T := fun w hw => Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
    ⟨hMB (hWM.1 hw), hMz (hWM.1 hw)⟩, (mem_fixingSubgroup_iff _).mpr fun u hu => hWU w hw u hu⟩
  have hTM : T ≤ M := fun g hg => hM (Subgroup.mem_inf.mp hg).1
  have hsub : IsSubnormal W T := by
    have := CFSG.Open.IsSubnormal.inf_of_le hWM.2.1 hTM
    rwa [inf_eq_left.mpr hWT] at this
  have hWeq : W = T := CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
    ⟨hWT, hsub, hWM.2.2⟩ hTq
  have hcard : Nat.card W = Nat.card T := by rw [hWeq]
  rw [hW, hcardT] at hcard
  revert hcard
  decide

end Ten

section Two

open Module CFSG.Open CFSG.RankThree.Classical2
open scoped commutatorElement

namespace TwTwo

private theorem vadd_self (F : Type*) {V : Type*} [Field F] [CharP F 2] [AddCommGroup V]
    [Module F V] (v : V) : v + v = 0 := by
  rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]

private theorem one_apply' {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (v : V) :
    (1 : V ≃ₗ[F] V) v = v := rfl

private theorem apply_three {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1) (v : V) : z (z (z v)) = v := by
  have h := congrArg (fun g : V ≃ₗ[F] V => g v) hz3
  simpa only [pow_three, LinearEquiv.mul_apply, one_apply'] using h

private theorem fixed_pi {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1) (v : V) :
    z (z (z v) + z v + v) = z (z v) + z v + v := by
  rw [map_add, map_add, apply_three hz3]
  abel

private theorem bil_eq_zero {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} {z : V ≃ₗ[F] V} (hzB : ∀ x y, B (z x) (z y) = B x y)
    {p y : V} (hp : z p = p) (hy : z (z y) + z y + y = 0) : B y p = 0 := by
  have h1 : B (z y) p = B y p := by
    have := hzB y p
    rwa [hp] at this
  have h2 : B (z (z y)) p = B y p := by
    have := hzB (z y) p
    rw [hp] at this
    rw [this, h1]
  have h0 : B (z (z y) + z y + y) p = 0 := by
    rw [hy, map_zero, LinearMap.zero_apply]
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h2, h1,
    CharTwo.add_self_eq_zero, zero_add] at h0
  exact h0

private theorem tri_rest {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1) (v : V) :
    z (z (z (z v) + z v)) + z (z (z v) + z v) + (z (z v) + z v) = 0 := by
  have e : z (z (z (z v) + z v)) + z (z (z v) + z v) + (z (z v) + z v) =
      (z v + z v) + (v + v) + (z (z v) + z (z v)) := by
    simp only [map_add, apply_three hz3]
    abel
  rw [e]
  simp only [vadd_self F]

private theorem decomp {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    (z : V ≃ₗ[F] V) (v : V) : v = (z (z v) + z v + v) + (z (z v) + z v) := by
  have e : (z (z v) + z v + v) + (z (z v) + z v) = v + ((z (z v) + z (z v)) + (z v + z v)) := by
    abel
  rw [e]
  simp only [vadd_self F, add_zero]

private theorem bil_apply_eq {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} {z : V ≃ₗ[F] V} (hzB : ∀ x y, B (z x) (z y) = B x y)
    (hz3 : z ^ 3 = 1) {w : V ≃ₗ[F] V} (hwz : w * z = z * w) (hwP : ∀ v, z v = v → w v = v)
    {p : V} (hp : z p = p) (x : V) : B (w x) p = B x p := by
  have hw : ∀ v, w (z v) = z (w v) := fun v => by
    have := congrArg (fun g : V ≃ₗ[F] V => g v) hwz
    simpa only [LinearEquiv.mul_apply] using this
  have hpi : w (z (z x) + z x + x) = z (z x) + z x + x := hwP _ (fixed_pi hz3 x)
  have e1 : w (z (z x) + z x + x) = z (z (w x)) + z (w x) + w x := by
    rw [map_add, map_add, hw (z x), hw x]
  have hy : z (z (w x - x)) + z (w x - x) + (w x - x) = 0 := by
    have e2 : z (z (w x - x)) + z (w x - x) + (w x - x) =
        (z (z (w x)) + z (w x) + w x) - (z (z x) + z x + x) := by
      simp only [map_sub]
      abel
    rw [e2, ← e1, hpi, sub_self]
  have h := bil_eq_zero hzB hp hy
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h
  exact h

private theorem core {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} (hB : B.IsAlt) {z : V ≃ₗ[F] V}
    (hzB : ∀ x y, B (z x) (z y) = B x y) (hz3 : z ^ 3 = 1) {W : Subgroup (V ≃ₗ[F] V)}
    (hWz : ∀ w ∈ W, w * z = z * w) (hWP : ∀ w ∈ W, ∀ v, z v = v → w v = v)
    {a b : V} (ha : z a = a) (hb : z b = b) (hab : B a b = 1)
    {ta tb : V ≃ₗ[F] V} (hta : ∀ x, ta x = x + B x a • a) (htb : ∀ x, tb x = x + B x b • b) :
    orderOf ⁅tb, ta⁆ = 3 ∧ (∀ w ∈ W, ⁅tb, ta⁆ * w = w * ⁅tb, ta⁆) ∧
      ⁅tb, ta⁆ * z = z * ⁅tb, ta⁆ ∧ ⁅tb, ta⁆ ∉ Subgroup.zpowers z := by
  have hba : B b a = 1 := by rw [← hB.neg_eq, hab, CharTwo.neg_eq]
  have haa := hB.self_eq_zero a
  have hbb := hB.self_eq_zero b
  have hinv : ∀ {c : V} {t : V ≃ₗ[F] V}, B c c = 0 → (∀ x, t x = x + B x c • c) → t⁻¹ = t := by
    intro c t hc ht
    refine inv_eq_of_mul_eq_one_left (LinearEquiv.ext fun x => ?_)
    rw [LinearEquiv.mul_apply, ht, ht, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, hc, smul_eq_mul, mul_zero, add_zero, add_assoc, vadd_self F,
      add_zero, one_apply']
  set s := ⁅tb, ta⁆ with hs_def
  have hr : ∀ x, tb (ta x) = x + B x a • a + (B x a + B x b) • b := by
    intro x
    rw [htb, hta]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab]
    module
  have hs : ∀ x, s x = x + (B x a + B x b) • a + B x b • b := by
    intro x
    rw [hs_def, commutatorElement_def, hinv haa hta, hinv hbb htb]
    simp only [LinearEquiv.mul_apply]
    rw [hr, hr]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
      hbb, hab, hba]
    match_scalars <;> ring_nf <;> reduce_mod_char!
  have hs2 : ∀ x, s (s x) = x + B x a • a + (B x a + B x b) • b := by
    intro x
    rw [hs, hs]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
      hbb, hab, hba]
    match_scalars <;> ring_nf <;> reduce_mod_char!
  have hs3 : s ^ 3 = 1 := by
    refine LinearEquiv.ext fun x => ?_
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hs2, hs, one_apply']
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
      hbb, hab, hba]
    match_scalars <;> ring_nf <;> reduce_mod_char!
  have hsa : s a = b := by
    rw [hs, haa, hab, zero_add, one_smul, one_smul, vadd_self F, zero_add]
  have hba' : b ≠ a := by
    intro h
    rw [h, haa] at hab
    exact zero_ne_one hab
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, one_apply'] at hsa
    exact hba' hsa.symm
  refine ⟨orderOf_eq_prime hs3 hs1, fun w hw => ?_, ?_, fun hmem => ?_⟩
  · refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hs, hs,
      bil_apply_eq hzB hz3 (hWz w hw) (hWP w hw) ha, bil_apply_eq hzB hz3 (hWz w hw) (hWP w hw) hb,
      map_add, map_add, map_smul, map_smul, hWP w hw a ha, hWP w hw b hb]
  · refine LinearEquiv.ext fun x => ?_
    have hza : ∀ y, B (z y) a = B y a := fun y => by rw [← hzB y a, ha]
    have hzb : ∀ y, B (z y) b = B y b := fun y => by rw [← hzB y b, hb]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hs, hs, hza, hzb, map_add, map_add,
      map_smul, map_smul, ha, hb]
  · have hstab : Subgroup.zpowers z ≤ MulAction.stabilizer (V ≃ₗ[F] V) a :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]; exact ha)
    have h := hstab hmem
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def, hsa] at h
    exact hba' h

private theorem exists_transv {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} (hB : B.IsAlt) (c : V) :
    ∃ t : V ≃ₗ[F] V, t ∈ TauCeti.BilinForm.isometryGroup B ∧ ∀ x, t x = x + B x c • c := by
  let f : V →ₗ[F] V := LinearMap.id + (B.flip c).smulRight c
  have hf : ∀ x, f x = x + B x c • c := fun x => by simp [f]
  have hinv : Function.Involutive f := by
    intro x
    rw [hf, hf, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hB.self_eq_zero, smul_eq_mul, mul_zero, add_zero, add_assoc, vadd_self F, add_zero]
  refine ⟨LinearEquiv.ofInvolutive f hinv, ?_, fun x => hf x⟩
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  simp only [LinearEquiv.coe_ofInvolutive, hf, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero]
  rw [← hB.neg_eq y c]
  ring

private theorem exists_bil_ne_zero {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V]
    [Module F V] {B : LinearMap.BilinForm F V} (hB : B.IsAlt) (hBn : B.SeparatingLeft)
    {z : V ≃ₗ[F] V} (hzB : ∀ x y, B (z x) (z y) = B x y) (hz3 : z ^ 3 = 1)
    {a : V} (ha : z a = a) (ha0 : a ≠ 0) : ∃ b, z b = b ∧ B a b ≠ 0 := by
  by_contra! h
  refine ha0 (hBn a fun v => ?_)
  have hu := bil_eq_zero hzB ha (tri_rest hz3 v)
  rw [decomp z v, map_add, h _ (fixed_pi hz3 v), zero_add, ← hB.neg_eq, hu, neg_zero]

private theorem eq_one_of_ne_zero {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {c : F}
    (hc : c ≠ 0) : c = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hF, sq] at h
  exact mul_left_cancel₀ hc (h.trans (mul_one c).symm)

private theorem reflect_apply_eq {F V : Type} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {c : V} (hc : Q c = 1) (x : V) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q c x = x + QuadraticMap.polarBilin Q x c • c := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (by rw [hc]; exact one_ne_zero), hc, div_one,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, sub_eq_add_neg, ← neg_smul,
    CharTwo.neg_eq]

end TwTwo

open TwTwo

private theorem twTwoSp_holds {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (_hV : finrank F V = 12)
    {B : LinearMap.BilinForm F V} (hB : B.IsAlt) (hBn : B.Nondegenerate) {z : V ≃ₗ[F] V}
    (hz : z ∈ TauCeti.BilinForm.isometryGroup B) (hz3 : z ^ 3 = 1) (_hz1 : z ≠ 1)
    (hd : finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 2)
    {W : Subgroup (V ≃ₗ[F] V)} (hWz : ∀ w ∈ W, w * z = z * w)
    (hWP : ∀ w ∈ W, ∀ v, z v = v → w v = v)
    (hcent : ∀ g ∈ TauCeti.BilinForm.isometryGroup B, orderOf g = 3 →
      (∀ w ∈ W, g * w = w * g) → g * z = z * g → g ∈ Subgroup.zpowers z) : False := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hzB := TauCeti.BilinForm.mem_isometryGroup_iff.mp hz
  obtain ⟨a, ha, ha0⟩ : ∃ a, z a = a ∧ a ≠ 0 := by
    have hne : LinearMap.ker (z.toLinearMap - LinearMap.id) ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      exact absurd hd (by norm_num)
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨a, ?_, ha0⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at ha
    exact ha
  obtain ⟨b', hb', hab'⟩ := exists_bil_ne_zero hB hBn.1 hzB hz3 ha ha0
  have hb : z ((B a b')⁻¹ • b') = (B a b')⁻¹ • b' := by rw [map_smul, hb']
  have hab : B a ((B a b')⁻¹ • b') = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hab']
  obtain ⟨ta, hta, hta'⟩ := exists_transv hB a
  obtain ⟨tb, htb, htb'⟩ := exists_transv hB ((B a b')⁻¹ • b')
  obtain ⟨hord, hcW, hcz, hnot⟩ := core hB hzB hz3 hWz hWP ha hb hab hta' htb'
  refine hnot (hcent _ ?_ hord hcW hcz)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem htb hta) (inv_mem htb)) (inv_mem hta)

private theorem twTwoOrth_holds {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (hdim : finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {z : V ≃ₗ[F] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hz3 : z ^ 3 = 1) (_hz1 : z ≠ 1)
    (hd : finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 2)
    {W : Subgroup (V ≃ₗ[F] V)} (hWz : ∀ w ∈ W, w * z = z * w)
    (hWP : ∀ w ∈ W, ∀ v, z v = v → w v = v)
    (hcent : ∀ g ∈ orthDerived Q, orderOf g = 3 → (∀ w ∈ W, g * w = w * g) →
      g * z = z * g → g ∈ Subgroup.zpowers z) : False := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  set B := QuadraticMap.polarBilin Q
  have hBapp : ∀ x y, B x y = QuadraticMap.polar Q x y := fun x y =>
    QuadraticMap.polarBilin_apply_apply Q x y
  have hB : B.IsAlt := fun x => by
    rw [hBapp, QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hzB : ∀ x y, B (z x) (z y) = B x y := fun x y => by
    rw [hBapp, hBapp]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hz x y
  set P := LinearMap.ker (z.toLinearMap - LinearMap.id) with hP_def
  set U := LinearMap.ker ((z.toLinearMap ∘ₗ z.toLinearMap) + z.toLinearMap + LinearMap.id)
    with hU_def
  have hmemP : ∀ v, v ∈ P ↔ z v = v := fun v => by
    rw [hP_def, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hmemU : ∀ v, v ∈ U ↔ z (z v) + z v + v = 0 := fun v => by
    rw [hU_def, LinearMap.mem_ker]
    rfl
  have hc : IsCompl P U := by
    refine ⟨Submodule.disjoint_def.mpr fun v hvP hvU => ?_, ?_⟩
    · rw [hmemP] at hvP
      rw [hmemU, hvP, hvP, vadd_self F, zero_add] at hvU
      exact hvU
    · refine codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => Submodule.mem_sup.mpr ?_)
      exact ⟨_, (hmemP _).mpr (fixed_pi hz3 v), _, (hmemU _).mpr (tri_rest hz3 v),
        (decomp z v).symm⟩
  have horth : ∀ x ∈ P, ∀ y ∈ U, QuadraticMap.polar Q x y = 0 := fun x hx y hy => by
    rw [QuadraticMap.polar_comm, ← hBapp]
    exact bil_eq_zero hzB ((hmemP x).mp hx) ((hmemU y).mp hy)
  have hzero : ∀ x, (∀ y ∈ P, QuadraticMap.polar Q x y = 0) →
      (∀ y ∈ U, QuadraticMap.polar Q x y = 0) → x = 0 := fun x hxP hxU => by
    refine hQ.1 x fun v => ?_
    obtain ⟨p, hp, u, hu, rfl⟩ := Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top :
      v ∈ P ⊔ U)
    rw [map_add, hBapp, hBapp, hxP p hp, hxU u hu, add_zero]
  have hPreg : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P := fun x hx h =>
    hzero x h fun y hy => horth x hx y hy
  have hUreg : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q U := fun x hx h =>
    hzero x (fun y hy => by rw [QuadraticMap.polar_comm]; exact horth y hy x hx) h
  have hPd : finrank F P = 2 * 1 := hd
  have hUd : finrank F U = 2 * 5 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    rw [hdim] at this
    omega
  have hodd : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Q 3 z := by
    refine ⟨hz, hz3, ?_, fun v hv => hQ.1 v fun w => by rw [hBapp]; exact hv w⟩
    rw [Ne, CharP.cast_eq_zero_iff F 2]
    decide
  have hzU : ∀ u ∈ U, z u ∈ U := fun u hu => by
    rw [hmemU] at hu ⊢
    rw [← map_add, ← map_add, hu, map_zero]
  have hfix : ∀ u ∈ U, z u = u → u = 0 := fun u hu h => by
    rw [hmemU, h, h, vadd_self F, zero_add] at hu
    exact hu
  have hUnot : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp U.subtype) := by
    rw [CFSG.RankThree.PartOne.K159.isPlusType_iff_even_of_fixedFree hodd Nat.prime_three
      (by norm_num) (by rw [hF]) 5 U hzU hUreg hfix hUd]
    decide
  have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hc horth hPreg
    hUreg le_rfl (by norm_num) hPd hUd
  have hPnot : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict P) := fun h =>
    hUnot ((hiff.mp hplus).mp h)
  have haniso : ∀ p ∈ P, Q p = 0 → p = 0 := by
    intro p hp hQp
    by_contra hp0
    have hp0' : (⟨p, hp⟩ : P) ≠ 0 := fun h => hp0 (congrArg Subtype.val h)
    refine hPnot ⟨F ∙ (⟨p, hp⟩ : P), ?_, fun x hx => ?_⟩
    · rw [finrank_span_singleton hp0', hPd]
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [QuadraticMap.map_smul, hQp]
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h : P = ⊥ => by
    rw [h, finrank_bot] at hd
    exact absurd hd (by norm_num))
  obtain ⟨b, hbP, hab0⟩ := hPreg.exists_polar_ne_zero haP ha0
  have hb0 : b ≠ 0 := fun h => hab0 (by rw [h, QuadraticMap.polar_zero_right])
  have hQa : Q a = 1 := eq_one_of_ne_zero hF fun h => ha0 (haniso a haP h)
  have hQb : Q b = 1 := eq_one_of_ne_zero hF fun h => hb0 (haniso b hbP h)
  have hab : B a b = 1 := by rw [hBapp]; exact eq_one_of_ne_zero hF hab0
  obtain ⟨hord, hcW, hcz, hnot⟩ := core hB hzB hz3 hWz hWP ((hmemP a).mp haP) ((hmemP b).mp hbP)
    hab (reflect_apply_eq hQa) (reflect_apply_eq hQb)
  exact hnot (hcent _ (Subgroup.commutator_mem_commutator
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q b)
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q a)) hord hcW hcz)

end Two

theorem false_of_twelve_sp_config {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : Module.finrank F V = 12)
    {B : LinearMap.BilinForm F V} (hBalt : B.IsAlt) (hBnd : B.Nondegenerate) {z : V ≃ₗ[F] V}
    (hzB : z ∈ TauCeti.BilinForm.isometryGroup B) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {W : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup W] (hWc : Nat.card W = 13685760)
    (hcomp : CFSG.Open.IsComponentOf W
      (TauCeti.BilinForm.isometryGroup B ⊓ Subgroup.centralizer {z}))
    (hKF : ∀ g ∈ TauCeti.BilinForm.isometryGroup B, orderOf g = 3 → (∀ w ∈ W, g * w = w * g) →
      g * z = z * g → g ∈ Subgroup.zpowers z) : False := by
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hWc]; norm_num)
  have hWz : ∀ w ∈ W, w * z = z * w := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hcomp.1 hw)).2
  have hWZ : Subgroup.center W = ⊥ :=
    CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup (by rw [hWc]; norm_num)
  rcases twelve_cases hF hV hz3 hz1 (by rw [hWc]; norm_num) hWz with hfree | ⟨h2, htr⟩ |
      ⟨h10, htr⟩
  · exact twFreeSp_holds hF hV hBalt hBnd hzB hz3 hfree inf_le_right le_rfl inf_le_left hcomp hWZ
  · exact twTwoSp_holds hF hV hBalt hBnd hzB hz3 hz1 h2 hWz htr hKF
  · exact twTenSp_holds hF hV hBalt hBnd hzB hz3 h10 inf_le_right le_rfl inf_le_left htr hcomp hWc

theorem twelve_orth_fixed_two {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : Module.finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : V ≃ₗ[F] V}
    (hzΩ : z ∈ CFSG.RankThree.Classical2.orthDerived Q) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {W : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup W] (hWc : Nat.card W = 13685760)
    (hcomp : CFSG.Open.IsComponentOf W
      (CFSG.RankThree.Classical2.orthDerived Q ⊓ Subgroup.centralizer {z})) :
    Module.finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 2 ∧
      ∀ w ∈ W, ∀ v, z v = v → w v = v := by
  have hΩO : CFSG.RankThree.Classical2.orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
  have hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hΩO hzΩ
  have hWO : W ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hcomp.1.trans (inf_le_left.trans hΩO)
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hWc]; norm_num)
  have hWz : ∀ w ∈ W, w * z = z * w := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hcomp.1 hw)).2
  have hWZ : Subgroup.center W = ⊥ :=
    CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup (by rw [hWc]; norm_num)
  rcases twelve_cases hF hV hz3 hz1 (by rw [hWc]; norm_num) hWz with hfree | h2 | ⟨h10, htr⟩
  · exact (twFreeOrth_holds hF hV hQ hzO hz3 hfree inf_le_right le_rfl hWO hcomp hWZ).elim
  · exact h2
  · exact (twTenOrth_holds hF hV hQ hzO hz3 h10 inf_le_right le_rfl hWO htr hcomp hWc).elim

theorem false_of_twelve_orth_config {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : Module.finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {z : V ≃ₗ[F] V}
    (hzΩ : z ∈ CFSG.RankThree.Classical2.orthDerived Q) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {W : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup W] (hWc : Nat.card W = 13685760)
    (hcomp : CFSG.Open.IsComponentOf W
      (CFSG.RankThree.Classical2.orthDerived Q ⊓ Subgroup.centralizer {z}))
    (hKF : ∀ g ∈ CFSG.RankThree.Classical2.orthDerived Q, orderOf g = 3 →
      (∀ w ∈ W, g * w = w * g) → g * z = z * g → g ∈ Subgroup.zpowers z) : False := by
  obtain ⟨h2, htr⟩ := twelve_orth_fixed_two hF hV hQ hzΩ hz3 hz1 hWc hcomp
  have hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup hzΩ
  have hWz : ∀ w ∈ W, w * z = z * w := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hcomp.1 hw)).2
  exact twTwoOrth_holds hF hV hQ hplus hzO hz3 hz1 h2 hWz htr hKF

end CFSG.GGQ2Prime
