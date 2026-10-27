module

public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanCore
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Blueprint.LieModelAPI
public import CFSG.RankThree.GF2n.NaturalDecomp
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Mat
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Count
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.RepresentationTheory.SL2NatSum

open CFSG.LocalAnalysis.UniquenessCase.UCK.Higman CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
open CFSG.Blueprint
open scoped MatrixGroups

private theorem quad_of_fpf {K W : Type*} [Field K] [CharP K 2] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) SL(2, K) W) {d : SL(2, K)}
    (hd3 : d ^ 3 = 1) (hfix : ∀ w : W, ρ d w = w → w = 0) :
    ∀ v : W, ρ d (ρ d v) + ρ d v + v = 0 := by
  intro v
  set A : Module.End (ZMod 2) W := ρ d with hA
  have hA3 : A ^ 3 = 1 := by
    rw [hA, ← map_pow, hd3, map_one]
  have hpow : ∀ w : W, A (A (A w)) = w := by
    intro w
    have := congrArg (fun f : Module.End (ZMod 2) W => f w) hA3
    simpa [pow_three, Module.End.mul_apply] using this
  have hfixu : A (A (A v) + A v + v) = A (A v) + A v + v := by
    rw [map_add, map_add, hpow v]
    abel
  simpa [hA] using hfix _ hfixu

private theorem quad_of_conj {K W : Type*} [Field K] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) SL(2, K) W) {c d g : SL(2, K)}
    (h : g * c * g⁻¹ = d) (hd : ∀ v : W, ρ d (ρ d v) + ρ d v + v = 0) :
    ∀ v : W, ρ c (ρ c v) + ρ c v + v = 0 := by
  intro v
  have hdc : ∀ w : W, ρ d w = ρ g (ρ c (ρ g⁻¹ w)) := by
    intro w
    rw [← h, map_mul, map_mul]
    rfl
  have hgg : ∀ w : W, ρ g⁻¹ (ρ g w) = w := by
    intro w
    have h1 : ρ g⁻¹ * ρ g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    simpa using congrArg (fun f : Module.End (ZMod 2) W => f w) h1
  have hu : ρ d (ρ g v) = ρ g (ρ c v) := by
    rw [hdc (ρ g v), hgg]
  have hu2 : ρ d (ρ g (ρ c v)) = ρ g (ρ c (ρ c v)) := by
    rw [hdc (ρ g (ρ c v)), hgg]
  have h1 := hd (ρ g v)
  rw [hu, hu2] at h1
  have h2 := congrArg (ρ g⁻¹) h1
  simpa [map_add, hgg] using h2

private theorem quad_of_order_three {K : Type} {W : Type*} [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2, K) W) {d : SL(2, K)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hd : ∀ v : W, ρ d (ρ d v) + ρ d v + v = 0) :
    ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : W,
      ρ c (ρ c v) + ρ c v + v = 0 := by
  intro c hc3 hc1 v
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcOrd : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hdOrd : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hcP : CFSG.IsPRegular 2 c := by
    change Nat.Coprime (orderOf c) 2
    rw [hcOrd]
    decide
  have hdP : CFSG.IsPRegular 2 d := by
    change Nat.Coprime (orderOf d) 2
    rw [hdOrd]
    decide
  have hct : (c : Matrix (Fin 2) (Fin 2) K).trace = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.l2op_trace_eq_one hc3 hc1
  have hdt : (d : Matrix (Fin 2) (Fin 2) K).trace = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.l2op_trace_eq_one hd3 hd1
  have hconj : IsConj c d :=
    CFSG.CGT.PushingUpLit.CGT6.m3_isConj_of_trace_eq hcP hdP (by rw [hct, hdt])
  obtain ⟨g, hg⟩ := hconj
  have hgc : (g : SL(2, K)) * c * (g : SL(2, K))⁻¹ = d := by
    rw [hg.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact quad_of_conj ρ hgc hd v

private lemma eq_sub_add_of_add_eq_zero {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] [DistribMulAction G W] {d : G} {w : W}
    (h : d • (d • w) + d • w + w = 0) :
    w = (d • w - w) + ((d * d) • w - w) := by
  have hrel : (d * d) • w + d • w + w = 0 := by
    rw [mul_smul]
    exact h
  have h2w : w + w = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hneg : -w = w := neg_eq_of_add_eq_zero_right h2w
  have hba : (d * d) • w + d • w = w := by
    have := eq_neg_of_add_eq_zero_left hrel
    rwa [hneg] at this
  calc w = ((d * d) • w + d • w) + (w + w) := by rw [hba, h2w, add_zero]
    _ = (d • w - w) + ((d * d) • w - w) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, hneg]
          abel

private theorem hgen_of_quadratic {K : Type} {W : Type*} [Field K] [CharP K 2] [AddCommGroup W]
    [Module (ZMod 2) W] [DistribMulAction SL(2, K) W]
    (hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : W,
      a' • (a • v - v) = a • v - v)
    {d : SL(2, K)} (hdquad : ∀ v : W, d • (d • v) + d • v + v = 0)
    (U : AddSubgroup W) (hU : ∀ g : SL(2, K), ∀ v ∈ U, g • v ∈ U)
    (hLU : ∀ v : W, (∀ a ∈ upperUnipotent K, a • v = v) → v ∈ U) :
    U = ⊤ := by
  let M : Subgroup SL(2, K) :=
    { carrier := {x | ∀ w : W, x • w - w ∈ U}
      one_mem' := fun w => by simpa using U.zero_mem
      mul_mem' := fun {x y} hx hy w => by
        have h : (x * y) • w - w = x • (y • w - w) + (x • w - w) := by
          rw [mul_smul, smul_sub]
          abel
        rw [h]
        exact U.add_mem (hU x _ (hy w)) (hx w)
      inv_mem' := fun {x} hx w => by
        have h : x⁻¹ • w - w = x⁻¹ • (w - x • w) := by
          rw [smul_sub, inv_smul_smul]
        rw [h]
        exact hU x⁻¹ _ (by simpa [neg_sub] using U.neg_mem (hx w)) }
  have hupper_le : upperUnipotent K ≤ M := by
    intro a ha w
    exact hLU (a • w - w) (fun a' ha' => hquad a ha a' ha' w)
  have hlower_le : lowerUnipotent K ≤ M := by
    intro b hb w
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff K).mp hb
    have hconv : lowerElt K t =
        (wMat : SL(2, K)) * (uMat t : SL(2, K)) * (wMat : SL(2, K))⁻¹ := by
      rw [wconj_U]
      exact Subtype.ext rfl
    have hupper : (uMat t : SL(2, K)) ∈ upperUnipotent K :=
      (mem_upperUnipotent_iff K).mpr ⟨t, Subtype.ext rfl⟩
    have hmem : (uMat t : SL(2, K)) • ((wMat : SL(2, K))⁻¹ • w) -
        (wMat : SL(2, K))⁻¹ • w ∈ U :=
      hupper_le hupper (((wMat : SL(2, K))⁻¹) • w)
    have hsm : ((wMat : SL(2, K)) * (uMat t : SL(2, K)) * (wMat : SL(2, K))⁻¹) • w -
        w = (wMat : SL(2, K)) •
          ((uMat t : SL(2, K)) • ((wMat : SL(2, K))⁻¹ • w) -
            (wMat : SL(2, K))⁻¹ • w) := by
      rw [mul_smul, mul_smul, smul_sub, smul_inv_smul]
    rw [hconv, hsm]
    exact hU (wMat : SL(2, K)) _ hmem
  have hMtop : M = ⊤ := by
    rw [eq_top_iff, ← upperUnipotent_sup_lowerUnipotent (K := K)]
    exact sup_le hupper_le hlower_le
  have hdM : d ∈ M := by rw [hMtop]; exact Subgroup.mem_top d
  have hd2M : d * d ∈ M := by rw [hMtop]; exact Subgroup.mem_top (d * d)
  rw [eq_top_iff]
  intro w _
  rw [eq_sub_add_of_add_eq_zero (hdquad w)]
  exact U.add_mem (hdM w) (hd2M w)

private theorem exists_additive_decomp {K : Type} {W : Type*} [Field K] [CharP K 2]
    [PerfectRing K 2] [AddCommGroup W] [Finite W] [Module (ZMod 2) W]
    [DistribMulAction SL(2, K) W]
    (ρ' : Representation (ZMod 2) SL(2, K) W)
    (hsmul : ∀ (g : SL(2, K)) (v : W), g • v = ρ' g v)
    (hquad : ∀ (x y : K) (v : W),
      ρ' (uMat y) (ρ' (uMat x) v - v) = ρ' (uMat x) v - v)
    {d : SL(2, K)} (hdquad : ∀ v : W, ρ' d (ρ' d v) + ρ' d v + v = 0)
    (hdfix : ∀ v : W, ρ' d v = v → v = 0) :
    ∃ s : Finset (AddSubgroup W), s.SupIndep id ∧ s.sup id = ⊤ ∧
      ∀ W' ∈ s, (∀ g : SL(2, K), ∀ v ∈ W', g • v ∈ W') ∧
        ∃ θ : (Fin 2 → K) →+ W, Function.Injective θ ∧ θ.range = W' ∧
          ∀ (x : SL(2, K)) (v : Fin 2 → K),
            θ ((x : Matrix (Fin 2) (Fin 2) K).mulVec v) = x • θ v := by
  classical
  have huMat : ∀ x : K, uMat x = upperElt K x := fun _ => Subtype.ext rfl
  have hquadW : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : W,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    obtain ⟨x, rfl⟩ := (mem_upperUnipotent_iff K).mp ha
    obtain ⟨y, rfl⟩ := (mem_upperUnipotent_iff K).mp ha'
    rw [hsmul (upperElt K y), hsmul (upperElt K x)]
    change ρ' (upperElt K y) (ρ' (upperElt K x) v - v) =
      ρ' (upperElt K x) v - v
    simpa [huMat] using hquad x y v
  have hdquad' : ∀ v : W, d • (d • v) + d • v + v = 0 := by
    intro v
    rw [hsmul d, hsmul d]
    exact hdquad v
  let L : AddSubgroup W :=
    { carrier := {w | ∀ a ∈ upperUnipotent K, a • w = w}
      zero_mem' := fun a _ => by simp
      add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha]
      neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha] }
  have hL : ∀ w ∈ L, ∀ a ∈ upperUnipotent K, a • w = w := fun _ hw => hw
  have hgen : ∀ U : AddSubgroup W, (∀ g : SL(2, K), ∀ v ∈ U, g • v ∈ U) → L ≤ U →
      U = ⊤ := fun U hU hLU => hgen_of_quadratic hquadW hdquad' U hU (fun v hv => hLU hv)
  have hfix : ∀ v : W, (∀ g : SL(2, K), g • v = v) → v = 0 := by
    intro v hv
    have hv' : ρ' d v = v := by
      rw [← hsmul d v]
      exact hv d
    exact hdfix v hv'
  obtain ⟨s, hs, hsup, hWnat⟩ :=
    CFSG.RankThree.GF2n.exists_supIndep_natural (K := K) (V := W) hfix hquadW hL hgen
  exact ⟨s, hs, hsup, fun W' hW' => ⟨(hWnat W' hW').1, (hWnat W' hW').2.2.2⟩⟩

private theorem submodule_decomp_of_additive {K : Type} {H W : Type*} [Field K] [Finite K] [Group H]
    [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction SL(2, K) W]
    (e : H ≃* SL(2, K)) (ρ : H →* LGL 2 W)
    (hsmul : ∀ (h : H) (v : W), ρ h v = (e h) • v)
    {n : ℕ} (hcard : Nat.card K = 2 ^ n)
    {s : Finset (AddSubgroup W)} (hs : s.SupIndep id) (hsup : s.sup id = ⊤)
    (hWnat : ∀ W' ∈ s, (∀ g : SL(2, K), ∀ v ∈ W', g • v ∈ W') ∧
      ∃ θ : (Fin 2 → K) →+ W, Function.Injective θ ∧ θ.range = W' ∧
        ∀ (x : SL(2, K)) (v : Fin 2 → K),
          θ ((x : Matrix (Fin 2) (Fin 2) K).mulVec v) = x • θ v) :
    ∃ s' : Finset (Submodule (ZMod 2) W),
      (∀ U ∈ s', ∀ h : H, ∀ u ∈ U, ρ h u ∈ U) ∧ s'.sup id = ⊤ ∧
      (∀ U ∈ s', U ⊓ (s'.erase U).sup id = ⊥) ∧
      ∀ U ∈ s', ∃ (K' : Type) (_ : Field K') (_ : Finite K') (φ : H ≃* SL(2, K'))
        (ψ : ↥U ≃+ (Fin 2 → K')),
        Nat.card K' = 2 ^ n ∧ ∀ (h : H) (u : ↥U) (hu : ρ h (u : W) ∈ U),
          ψ ⟨ρ h (u : W), hu⟩ = (φ h : Matrix (Fin 2) (Fin 2) K').mulVec (ψ u) := by
  classical
  let f : AddSubgroup W ≃o Submodule (ZMod 2) W := AddSubgroup.toZModSubmodule 2
  have hf_sup : ∀ x y, f (x ⊔ y) = f x ⊔ f y := fun _ _ => by rw [OrderIso.map_sup]
  have hf_inf : ∀ x y, f (x ⊓ y) = f x ⊓ f y := fun _ _ => by rw [OrderIso.map_inf]
  have hf_bot : f ⊥ = ⊥ := by rw [OrderIso.map_bot]
  have hf_top : f ⊤ = ⊤ := by rw [OrderIso.map_top]
  let s' : Finset (Submodule (ZMod 2) W) := s.image f
  have hs' : s'.SupIndep id :=
    CFSG.RankThree.GF2n.supIndep_image_of_lattice_hom hs f hf_sup hf_inf hf_bot
  have hsup' : s'.sup id = ⊤ := by
    change (s.image f).sup id = ⊤
    rw [CFSG.RankThree.GF2n.sup_image_of_sup_hom s f hf_sup hf_bot, hsup, hf_top]
  refine ⟨s', ?_, hsup', ?_, ?_⟩
  · intro U hU h u hu
    obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hU
    have hu' : u ∈ W' := hu
    have hinv := (hWnat W' hW').1 (e h) u hu'
    rw [hsmul h u]
    exact hinv
  · intro U hU
    have hdis := (Finset.supIndep_iff_disjoint_erase.mp hs') U hU
    exact disjoint_iff.mp hdis
  · intro U hU
    obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨-, θ, hθinj, hθrange, hθeq⟩ := hWnat W' hW'
    have hmem : ∀ v : Fin 2 → K, θ v ∈ W' := fun v => by
      rw [← hθrange]
      exact ⟨v, rfl⟩
    let θU : (Fin 2 → K) →+ ↥(f W') :=
      { toFun := fun v => ⟨θ v, hmem v⟩
        map_zero' := Subtype.ext (map_zero θ)
        map_add' := fun a b => Subtype.ext (map_add θ a b) }
    have hθUinj : Function.Injective θU := by
      intro a b h
      exact hθinj (Subtype.ext_iff.mp h)
    have hθUsurj : Function.Surjective θU := by
      intro u
      have hu : (u : W) ∈ θ.range := by
        rw [hθrange]
        exact u.2
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, Subtype.ext hv⟩
    let eθ := AddEquiv.ofBijective θU ⟨hθUinj, hθUsurj⟩
    let ψ : ↥(f W') ≃+ (Fin 2 → K) := eθ.symm
    have hψθ : ∀ v : Fin 2 → K, ψ (θU v) = v := fun v => eθ.symm_apply_apply v
    have hθψ : ∀ u : ↥(f W'), θU (ψ u) = u := fun u => eθ.apply_symm_apply u
    refine ⟨K, inferInstance, inferInstance, e, ψ, hcard, ?_⟩
    intro h u hu
    have huθ : (u : W) = θ (ψ u) :=
      (congrArg Subtype.val (hθψ u)).symm
    have hstep : ρ h (u : W) = θ ((e h : Matrix (Fin 2) (Fin 2) K).mulVec (ψ u)) := by
      rw [huθ, hsmul h (θ (ψ u)), ← hθeq]
    have hsub : (⟨ρ h (u : W), hu⟩ : ↥(f W')) =
        θU ((e h : Matrix (Fin 2) (Fin 2) K).mulVec (ψ u)) :=
      Subtype.ext hstep
    calc ψ ⟨ρ h (u : W), hu⟩ = ψ (θU ((e h : Matrix (Fin 2) (Fin 2) K).mulVec (ψ u))) := by
          rw [hsub]
      _ = (e h : Matrix (Fin 2) (Fin 2) K).mulVec (ψ u) := hψθ _

theorem natSum_of_quadratic {n : ℕ}
    (hquad : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
        (ρ : Representation (ZMod 2) SL(2, K) V),
        (∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V, ρ c (ρ c v) + ρ c v + v = 0) →
        ∀ (x y : K) (v : V), ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x) v - v)
    {H : Type} [Group H] [Finite H] (hH : CFSG.Quasithin.IsPSL 2 2 n H)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : H →* LGL 2 W)
    (hD : ∃ D : Subgroup H, Nat.card D = 3 ∧ ∀ w : W, (∀ d ∈ D, ρ d w = w) → w = 0) :
    ∃ s : Finset (Submodule (ZMod 2) W),
      (∀ U ∈ s, ∀ h : H, ∀ u ∈ U, ρ h u ∈ U) ∧ s.sup id = ⊤ ∧
      (∀ U ∈ s, U ⊓ (s.erase U).sup id = ⊥) ∧
      ∀ U ∈ s, ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : H ≃* SL(2, K))
        (ψ : ↥U ≃+ (Fin 2 → K)),
        Nat.card K = 2 ^ n ∧ ∀ (h : H) (u : ↥U) (hu : ρ h (u : W) ∈ U),
          ψ ⟨ρ h (u : W), hu⟩ = (φ h : Matrix (Fin 2) (Fin 2) K).mulVec (ψ u) := by
  classical
  have hLmodel : LieModel H .PSL 2 2 n :=
    (LieModel.classical_iff (by decide)).mpr hH
  obtain ⟨K, hKf, hKfin, hKchar, hKcard, ⟨e⟩⟩ := sl2_of_lieModel hLmodel
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : PerfectRing K 2 := inferInstance
  let ρH : Representation (ZMod 2) H W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  let ρ' : Representation (ZMod 2) SL(2, K) W := ρH.comp e.symm.toMonoidHom
  letI : DistribMulAction SL(2, K) W := DistribMulAction.compHom W ρ'
  obtain ⟨D, hDcard, hDfix⟩ := hD
  obtain ⟨d₀, hDz, hd0pow, hd0ne⟩ := exists_gen_of_card_three D hDcard
  let d : SL(2, K) := e d₀
  have hd3 : d ^ 3 = 1 := by
    dsimp only [d]
    rw [← map_pow, hd0pow, map_one]
  have hd1 : d ≠ 1 := by
    intro h
    exact hd0ne (e.injective (by simpa [d] using h))
  have hdfix : ∀ w : W, ρ' d w = w → w = 0 := by
    intro w hw
    apply hDfix w
    intro a ha
    rw [hDz] at ha
    have hd0 : ρH d₀ w = w := by simpa [d, ρ'] using hw
    have ha' := fixed_of_zpowers ρH d₀ w hd0 a ha
    simpa [ρH] using ha'
  have hdquad : ∀ v : W, ρ' d (ρ' d v) + ρ' d v + v = 0 :=
    quad_of_fpf ρ' hd3 hdfix
  have hquad3 : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : W,
      ρ' c (ρ' c v) + ρ' c v + v = 0 :=
    quad_of_order_three ρ' hd3 hd1 hdquad
  have hquadRep : ∀ (x y : K) (v : W),
      ρ' (uMat y) (ρ' (uMat x) v - v) = ρ' (uMat x) v - v :=
    hquad K hKcard W ρ' hquad3
  obtain ⟨s, hs, hsup, hWnat⟩ :=
    exists_additive_decomp ρ' (fun _ _ => rfl) hquadRep hdquad hdfix
  have hsmul : ∀ (h : H) (v : W), ρ h v = (e h) • v := by
    intro h v
    show ρ h v = ρ' (e h) v
    rw [show ρ' (e h) = ρH h from by simp [ρ']]
    rfl
  exact submodule_decomp_of_additive e ρ hsmul hKcard hs hsup hWnat

end CFSG.RepresentationTheory.SL2NatSum
