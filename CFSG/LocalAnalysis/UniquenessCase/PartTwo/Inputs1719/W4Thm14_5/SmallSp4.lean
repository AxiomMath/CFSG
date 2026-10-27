module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUSp4Grp
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp4Par
public import CFSG.Quasithin.Background.SmithB42Sp4Ident
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUSp4
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
import CFSG.Quasithin.Background.E3MParamAttained

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.QuasithinUnique.Setup

theorem exists_pow_two_pow_ne_self {K : Type} [Field K] [Fintype K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Fintype.card K = 2 ^ (2 * m)) : ∃ x : K, x ^ 2 ^ m ≠ x := by
  classical
  by_contra h
  push Not at h
  set p : Polynomial K := Polynomial.X ^ 2 ^ m - Polynomial.X with hp
  have h1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have hdeg : p.natDegree = 2 ^ m := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [Polynomial.natDegree_X_pow, h1]
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset K) ⊆ p.roots.toFinset := fun x _ => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    simp [hp, h x]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, hK] at hcard
  have h2 := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  rw [hdeg] at h2
  have h3 : 2 ^ m < 2 ^ (2 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

variable {K : Type} [Field K] [CharP K 2]

theorem lowUSp_zero_ne_one {s : K} (hs : s ≠ 0) : X7b.lowUSp (0 : K) s 0 0 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K) 2 0) h
  simp [X7b.glMat_lowUSp, X7b.lowU] at h1
  exact hs h1

theorem lowUSp_zero_mul_self (s : K) : X7b.lowUSp (0 : K) s 0 0 * X7b.lowUSp 0 s 0 0 = 1 := by
  rw [X7b.lowUSp_mul, ← X7b.lowUSp_zero]
  simp [CharTwo.add_self_eq_zero]

theorem lowUSp_zero_inv_mul (b s : K) :
    (X7b.lowUSp (0 : K) b 0 0)⁻¹ * X7b.lowUSp 0 s 0 0 = X7b.lowUSp 0 (b + s) 0 0 := by
  rw [X7b.lowUSp_inv, X7b.lowUSp_mul]
  simp

theorem exists_involution_of_outer_even [Fintype K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Fintype.card K = 2 ^ (2 * m)) (c : antiSp K) {α : MulAut (antiSp K)}
    (hα : α = MulAut.conj c * minorAut K ^ (2 * m) * (MulAut.conj c)⁻¹) :
    ∃ l : antiSp K, (α l)⁻¹ * l ≠ 1 ∧ (α l)⁻¹ * l * ((α l)⁻¹ * l) = 1 := by
  subst hα
  obtain ⟨x, hx⟩ := exists_pow_two_pow_ne_self hm hK
  refine ⟨c * X7b.lowUSp 0 x 0 0 * c⁻¹, ?_⟩
  have h1 : (MulAut.conj c * minorAut K ^ (2 * m) * (MulAut.conj c)⁻¹)
      (c * X7b.lowUSp 0 x 0 0 * c⁻¹) = c * X7b.lowUSp 0 (x ^ 2 ^ m) 0 0 * c⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply,
      show c⁻¹ * (c * X7b.lowUSp 0 x 0 0 * c⁻¹) * c = X7b.lowUSp 0 x 0 0 by group,
      X7b.minorAut_pow_two_mul_lowUSp, MulAut.conj_apply]
    simp
  have h2 : (c * X7b.lowUSp (0 : K) (x ^ 2 ^ m) 0 0 * c⁻¹)⁻¹ * (c * X7b.lowUSp 0 x 0 0 * c⁻¹) =
      c * X7b.lowUSp 0 (x ^ 2 ^ m + x) 0 0 * c⁻¹ := by
    rw [← lowUSp_zero_inv_mul]
    group
  have hs : x ^ 2 ^ m + x ≠ 0 := by
    intro h
    apply hx
    have := congrArg (· + x) h
    simpa [CharTwo.add_self_eq_zero, add_assoc] using this
  rw [h1, h2]
  refine ⟨fun h => lowUSp_zero_ne_one hs ?_, ?_⟩
  · calc X7b.lowUSp (0 : K) (x ^ 2 ^ m + x) 0 0 =
          c⁻¹ * (c * X7b.lowUSp 0 (x ^ 2 ^ m + x) 0 0 * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · rw [show c * X7b.lowUSp (0 : K) (x ^ 2 ^ m + x) 0 0 * c⁻¹ *
          (c * X7b.lowUSp 0 (x ^ 2 ^ m + x) 0 0 * c⁻¹) =
        c * (X7b.lowUSp 0 (x ^ 2 ^ m + x) 0 0 * X7b.lowUSp 0 (x ^ 2 ^ m + x) 0 0) * c⁻¹ by group,
      lowUSp_zero_mul_self, mul_one, mul_inv_cancel]

theorem exists_involution_of_aut' [Fintype K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (antiSp K)) (hα : α * α = 1) (hα1 : α ≠ 1) :
    ∃ l : antiSp K, (α l)⁻¹ * l ≠ 1 ∧ (α l)⁻¹ * l * ((α l)⁻¹ * l) = 1 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · by_cases hinn : α ∈ inner (antiSp K)
    · obtain ⟨s, rfl⟩ := hinn
      have hs : s * s = 1 := X7b.conj_injective (by rw [map_mul, hα, map_one])
      have hs1 : s ≠ 1 := by
        rintro rfl
        exact hα1 (map_one _)
      have h2 : 2 < Nat.card K := by
        have := K148.four_le_card hn hK
        omega
      obtain ⟨l, hl1, hl2⟩ := K147SpU.exists_conj_commute_ne h2 hs hs1
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
      have key : (MulAut.conj s l⁻¹)⁻¹ * l⁻¹ = s * (l * s * l⁻¹) := by
        rw [MulAut.conj_apply]
        calc (s * l⁻¹ * s⁻¹)⁻¹ * l⁻¹ = s * l * s⁻¹ * l⁻¹ := by group
          _ = s * (l * s * l⁻¹) := by rw [hsinv]; group
      have hs' : l * s * l⁻¹ * (l * s * l⁻¹) = 1 := by
        rw [show l * s * l⁻¹ * (l * s * l⁻¹) = l * (s * s) * l⁻¹ by group, hs, mul_one,
          mul_inv_cancel]
      refine ⟨l⁻¹, ?_, ?_⟩
      · rw [key]
        intro h
        apply hl1
        rw [eq_inv_of_mul_eq_one_right h, hsinv]
      · rw [key]
        calc s * (l * s * l⁻¹) * (s * (l * s * l⁻¹)) =
            s * (l * s * l⁻¹ * s) * (l * s * l⁻¹) := by group
          _ = s * (s * (l * s * l⁻¹)) * (l * s * l⁻¹) := by rw [← hl2]
          _ = s * s * (l * s * l⁻¹ * (l * s * l⁻¹)) := by group
          _ = 1 := by rw [hs, hs', mul_one]
    · obtain ⟨c, hc⟩ := X7b.outer_involution_conj hn hK α hα hinn
      have hm1 : 1 ≤ m := by omega
      have hKf : Fintype.card K = 2 ^ (2 * m) := by
        rw [← Nat.card_eq_fintype_card, hK, hm, two_mul]
      exact exists_involution_of_outer_even hm1 hKf c (by rw [hc, hm, two_mul])
  · exact K147SpU.exists_involution_of_aut hn hodd hK α hα hα1

variable {G : Type} [Group G]

theorem exists_mul_conj_involution' {L : Subgroup G} {n : ℕ} (hSp : IsSp4 ↥L n) {t : G}
    (htN : t ∈ normalizer (L : Set G)) (ht : t * t = 1) (htc : ∃ x ∈ L, t * x ≠ x * t) :
    ∃ l ∈ L, t * (l⁻¹ * t * l) ∈ L ∧ t * (l⁻¹ * t * l) ≠ 1 ∧
      t * (l⁻¹ * t * l) * (t * (l⁻¹ * t * l)) = 1 := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := K148.exists_antiSp_of_isSp4 hSp
  let b : ↥(normalizer (L : Set G)) := ⟨t, htN⟩
  let α : MulAut (antiSp K) := MulAut.congr e (K148.AutAux.condHom L b)
  have hαe : ∀ x : ↥L, α (e x) = e (K148.AutAux.condHom L b x) := fun x => by
    show e (K148.AutAux.condHom L b (e.symm (e x))) = _
    rw [MulEquiv.symm_apply_apply]
  have hαα : α * α = 1 := by
    show MulAut.congr e (K148.AutAux.condHom L b) * MulAut.congr e (K148.AutAux.condHom L b) = 1
    rw [← map_mul, ← map_mul, show b * b = 1 from Subtype.ext ht, map_one, map_one]
  have hα1 : α ≠ 1 := by
    obtain ⟨x, hx, hxt⟩ := htc
    intro h1
    apply hxt
    have h2 := hαe ⟨x, hx⟩
    rw [h1, MulAut.one_apply] at h2
    have h3 : x = t * x * t⁻¹ := by
      have := congrArg Subtype.val (e.injective h2)
      rwa [K148.AutAux.condHom_apply] at this
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [← h3]
  obtain ⟨l, hl1, hl2⟩ := exists_involution_of_aut' hn hK α hαα hα1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : e.symm (α l) = K148.AutAux.condHom L b (e.symm l) := by
    rw [MulEquiv.symm_apply_eq, ← hαe, MulEquiv.apply_symm_apply]
  have key : t * (((e.symm l : ↥L) : G)⁻¹ * t * (e.symm l : ↥L)) =
      ((e.symm ((α l)⁻¹ * l) : ↥L) : G) := by
    rw [map_mul e.symm, map_inv e.symm, h1, Subgroup.coe_mul, Subgroup.coe_inv,
      K148.AutAux.condHom_apply]
    show t * (((e.symm l : ↥L) : G)⁻¹ * t * (e.symm l : ↥L)) =
      (t * (e.symm l : ↥L) * t⁻¹)⁻¹ * (e.symm l : ↥L)
    simp only [mul_inv_rev, inv_inv, htinv]
    group
  refine ⟨(e.symm l : G), (e.symm l).2, ?_, ?_, ?_⟩
  · rw [key]
    exact (e.symm _).2
  · rw [key]
    intro h
    apply hl1
    have : e.symm ((α l)⁻¹ * l) = 1 := Subtype.ext h
    rwa [MulEquiv.map_eq_one_iff] at this
  · rw [key, ← Subgroup.coe_mul, ← map_mul, hl2, map_one, Subgroup.coe_one]

section Natural

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.Layer
open scoped Matrix

variable {I : Type} [CommGroup I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem natSpn_of_mulVec {K : Type} [Field K] [Finite K] [CharP K 2] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (θ : I ≃* Multiplicative W) {L : Subgroup (MulAut I)}
    (Θ : ↥L ≃* antiSp K) (φ' : W ≃+ (Fin 4 → K))
    (hφ' : ∀ (l : ↥L) (w : W), φ' (binPsi θ (l : MulAut I) w) =
      (glMat ((Θ l : antiSp K) : GL (Fin 4) K)).mulVec (φ' w)) :
    NatSpn L ⊤ ⊥ 4 e := by
  refine ⟨⟨2, rfl⟩, K, inferInstance, inferInstance, hK, ?_⟩
  refine realizes_nat_of_equiv θ (Θ.trans (antiSpEquiv K))
    (φ'.trans (LinearEquiv.funCongrLeft K K antiIdx).toAddEquiv) fun l w => ?_
  have hmat : (((antiSpEquiv K (Θ l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (glMat ((Θ l : antiSp K) : GL (Fin 4) K)).submatrix antiIdx antiIdx :=
    spMat_antiSpEquiv (Θ l)
  show (LinearEquiv.funCongrLeft K K antiIdx) (φ' (binPsi θ (l : MulAut I) w)) =
    (((antiSpEquiv K (Θ l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (LinearEquiv.funCongrLeft K K antiIdx) (φ' w)
  rw [hmat, hφ', LinearEquiv.funCongrLeft_apply, LinearEquiv.funCongrLeft_apply,
    Matrix.submatrix_mulVec_equiv]
  congr 2

end Natural

section Row

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.Layer CFSG.RankThree.FFModules

theorem k14_5SmallFor_sp4 : K14_5SmallFor fun L _ e => IsSp4 L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  have hne : n = e := nParam_eq_of_isSp4_parabolic hS hPL hpar hinf hN
  subst e
  obtain ⟨hn2, K, _, _, _, hK, ⟨φ⟩⟩ := K148.exists_antiSp_of_isSp4 hS
  have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := I) fun v => by
    rw [← pow_two]
    exact hI v
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let π : antiSp K →* (W ≃ₗ[ZMod 2] W) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp φ.symm.toMonoidHom)
  have hπ : ∀ g w, π g w = binPsi θ ((φ.symm g : ↥L) : MulAut I) w := fun _ _ => rfl
  have hirrW : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    obtain ⟨-, -, -, hJ⟩ := hirr
    have hirrV : ∀ J : Subgroup I, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ :=
      fun J hJL => hJ J hJL bot_le le_top
    intro U hU
    refine B42L2.irr_map θ hirrV U ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h := hU (φ ⟨l, hl⟩) u hu
    rwa [hπ, MulEquiv.symm_apply_apply] at h
  have hntW : Nontrivial W := by
    obtain ⟨hlt, -, -, -⟩ := hirr
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have : Fact (B42Sp4.repOf π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (B42Sp4.repOf π)).mpr ⟨hntW, hirrW⟩⟩
  have hntπ : ∃ g, B42Sp4.repOf π g ≠ 1 := by
    refine ⟨lowUSp 0 1 0 1, fun h => K147SpU.lowUSp_zero_one_zero_one_ne_one (K := K) ?_⟩
    have h2 : π (lowUSp 0 1 0 1) = 1 := LinearEquiv.ext fun w => LinearMap.congr_fun h w
    have h3 : ((φ.symm (lowUSp 0 1 0 1) : ↥L) : MulAut I) = 1 := by
      apply (binPsi θ).injective
      rw [map_one]
      exact h2
    have h4 : φ.symm (lowUSp (0 : K) 1 0 1) = 1 := Subtype.ext h3
    rw [← φ.apply_symm_apply (lowUSp 0 1 0 1), h4, map_one]
  have hev : Even (Nat.card ↥X) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let u : ↥X := ⟨_, hLX (φ.symm (lowUSp 0 1 0 1)).2⟩
    have hu : orderOf u = 2 := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
      · show ((φ.symm (lowUSp 0 1 0 1) : ↥L) : MulAut I) ^ 2 = 1
        rw [← Subgroup.coe_pow, ← map_pow, pow_two, K147SpU.lowUSp_zero_one_zero_one_mul_self,
          map_one, Subgroup.coe_one]
      · have h1 : ((φ.symm (lowUSp 0 1 0 1) : ↥L) : MulAut I) = 1 := congrArg Subtype.val h
        have h2 : φ.symm (lowUSp (0 : K) 1 0 1) = 1 := Subtype.ext h1
        apply K147SpU.lowUSp_zero_one_zero_one_ne_one (K := K)
        rw [← φ.apply_symm_apply (lowUSp 0 1 0 1), h2, map_one]
    exact even_iff_two_dvd.2 (hu ▸ orderOf_dvd_natCard u)
  obtain ⟨t₀, ht₀X, ht₀, ht₀m⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have ht₀2 : t₀ * t₀ = 1 := by rw [← pow_two, ← ht₀, pow_orderOf_eq_one]
  have htc : ∃ x ∈ L, t₀ * x ≠ x * t₀ := by
    by_contra hall
    push Not at hall
    have h1 := eq_one_of_commute_of_isIrrOn hI hirr (by rw [pow_two]; exact ht₀2) hall
    rw [h1, orderOf_one] at ht₀
    exact absurd ht₀ (by norm_num)
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  obtain ⟨l, hlL, hyL, hy1, hy2⟩ := exists_mul_conj_involution' hS (hXN ht₀X) ht₀2 htc
  let a := subRep θ X
  let T : ↥X := ⟨t₀, ht₀X⟩
  let Λ : ↥X := ⟨l, hLX hlL⟩
  have hT : orderOf T = 2 := by rw [Subgroup.orderOf_mk]; exact ht₀
  have hdT : Module.finrank (ZMod 2) (LinearMap.range ((a T : W →ₗ[ZMod 2] W) - 1)) ≤ n + 1 := by
    have h1 := UC22.Excl147.finrank_quotient_fixSub_eq a hT
    rw [CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.commSpace_zpowers_eq_range a T
      (orderOf_pos_iff.mp (by omega))] at h1
    rw [← h1, finrank_quotient_fixSub_subRep, MonoidHom.map_zpowers]
    exact ht₀m.le.trans hm
  have hdY : Module.finrank (ZMod 2)
      (LinearMap.range ((a (T * (Λ⁻¹ * T * Λ)) : W →ₗ[ZMod 2] W) - 1)) ≤ 2 * (n + 1) := by
    have h4 := Submodule.finrank_mono (K147SpU.range_mul_le_sup a T (Λ⁻¹ * T * Λ))
    have h5 := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range ((a T : W →ₗ[ZMod 2] W) - 1))
      (LinearMap.range ((a (Λ⁻¹ * T * Λ) : W →ₗ[ZMod 2] W) - 1))
    have h6 := K147SpU.finrank_range_conj a T Λ
    omega
  let z : antiSp K := φ ⟨_, hyL⟩
  have hz2 : z * z = 1 := by
    rw [← map_mul, show (⟨_, hyL⟩ : ↥L) * ⟨_, hyL⟩ = 1 from Subtype.ext hy2, map_one]
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    have h1 : (⟨_, hyL⟩ : ↥L) = 1 := by
      rw [← φ.symm_apply_apply ⟨_, hyL⟩]
      show φ.symm z = 1
      rw [h, map_one]
    exact congrArg Subtype.val h1
  have hdisp : dispRank (π z) ≤ 2 * (n + 1) := by
    have hπz : π z = binPsi θ (t₀ * (l⁻¹ * t₀ * l)) := by
      show binPsi θ ((φ.symm (φ ⟨_, hyL⟩) : ↥L) : MulAut I) = _
      rw [MulEquiv.symm_apply_apply]
    unfold dispRank
    rw [hπz]
    exact hdY
  have hdim : Module.finrank (EndRing (B42Sp4.repOf π)) W = 4 := by
    by_contra hne4
    have h := (B42Sp4.displacement_ge hKf (by omega) π hntπ hne4 hz2 hz1).1
    omega
  obtain ⟨i, φ', hφ'⟩ := B42Sp4.exists_natural_of_four hKf (by omega) π hntπ hdim
  have hNat : NatSpn L ⊤ ⊥ 4 n := by
    refine natSpn_of_mulVec hK θ (φ.trans (minorAut K ^ i)) φ' fun l w => ?_
    have h := hφ' (φ l) w
    rwa [hπ, MulEquiv.symm_apply_apply] at h
  exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, hNat⟩))), Or.inl rfl⟩

end Row

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
