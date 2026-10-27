module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU1Core
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TriD4
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTorality
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KGD

theorem ggNbrLSideRSExcU1TriD4_conj_injective {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [← Subgroup.mem_bot, ← hZ, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun φ : MulAut G => φ g) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * x = (x * g * x⁻¹) * x := by rw [h]
    _ = x * g := by group

theorem ggNbrLSideRSExc_u1_triD4 :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 3 →
      GGNbrLSideRSExcTransport Tag.D4
        (LargeEvenChevIDImage LargeEvenCartanD4 K
          (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) (2 ^ n) := by
  unfold GGNbrLSideRSExcTransport
  intro K _ _ n hn hK φ hφI ψ hψI hφ1 hφ3 hψ3 hcomm
  classical
  have hK3 : Nat.card K = 2 ^ (n * 3) := by rw [hK, ← pow_mul]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set σ : K ≃+* K := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hcommL : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      (iterateFrobenius (AlgebraicClosure K) 2 n).comp
        (algebraMap K (AlgebraicClosure K)) := by
    refine RingHom.ext fun c => ?_
    change algebraMap K (AlgebraicClosure K) (σ c) =
      iterateFrobenius (AlgebraicClosure K) 2 n (algebraMap K (AlgebraicClosure K) c)
    rw [hσ c, iterateFrobenius_def, map_pow]
  obtain ⟨-, -, -, -, -, hCcomm, hCz, ⟨e₂⟩⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σ hσ
  obtain ⟨e₁⟩ := centerQuot_twistedH_equiv K .D4 n σ.toRingHom hσ
  let eC : LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e₁.trans e₂
  have hInn := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK
  obtain ⟨c, hc⟩ := hInn hφI
  obtain ⟨c', hc'⟩ := hInn hψI
  let c₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eC c
  let c'₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eC c'
  have hφ_conj : MulAut.congr eC φ = MulAut.conj c₀ := by
    rw [← hc, mulAut_congr_conj]
  have hψ_conj : MulAut.congr eC ψ = MulAut.conj c'₀ := by
    rw [← hc', mulAut_congr_conj]
  have hφ03 : (MulAut.congr eC φ) ^ 3 = 1 := by rw [← map_pow, hφ3, map_one]
  have hψ03 : (MulAut.congr eC ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hc03 : c₀ ^ 3 = 1 := by
    apply ggNbrLSideRSExcU1TriD4_conj_injective hCz
    rw [map_pow, ← hφ_conj, hφ03, map_one]
  have hc'03 : c'₀ ^ 3 = 1 := by
    apply ggNbrLSideRSExcU1TriD4_conj_injective hCz
    rw [map_pow, ← hψ_conj, hψ03, map_one]
  have hφ01 : MulAut.congr eC φ ≠ 1 := by
    intro h
    exact hφ1 ((MulAut.congr eC).injective (by rw [h, map_one]))
  have hc01 : c₀ ≠ 1 := by
    intro h
    exact hφ01 (by rw [hφ_conj, h, map_one])
  have hconjcomm : MulAut.conj c₀ * MulAut.conj c'₀ =
      MulAut.conj c'₀ * MulAut.conj c₀ := by
    rw [← hφ_conj, ← hψ_conj, ← map_mul, ← map_mul, hcomm]
  have hc0comm : c₀ * c'₀ = c'₀ * c₀ := by
    apply ggNbrLSideRSExcU1TriD4_conj_injective hCz
    rw [map_mul, map_mul]
    exact hconjcomm
  let u : ModGL TwistTag.D4.tag (AlgebraicClosure K) :=
    triEmb K σ (AlgebraicClosure K) c₀
  let u' : ModGL TwistTag.D4.tag (AlgebraicClosure K) :=
    triEmb K σ (AlgebraicClosure K) c'₀
  have hu3 : u ^ 3 = 1 := by
    change triEmb K σ (AlgebraicClosure K) c₀ ^ 3 = 1
    rw [← map_pow, hc03, map_one]
  have hu'3 : u' ^ 3 = 1 := by
    change triEmb K σ (AlgebraicClosure K) c'₀ ^ 3 = 1
    rw [← map_pow, hc'03, map_one]
  have hu1 : u ≠ 1 := by
    intro h
    apply hc01
    exact triEmb_injective (L := AlgebraicClosure K) (by rw [map_one]; exact h)
  have hu'G : u' ∈ adjointGroup Tag.D4 (AlgebraicClosure K) :=
    triEmb_mem_adjointGroup c'₀
  have hcommu : u * u' = u' * u := by
    change triEmb K σ (AlgebraicClosure K) c₀ * triEmb K σ (AlgebraicClosure K) c'₀ =
      triEmb K σ (AlgebraicClosure K) c'₀ * triEmb K σ (AlgebraicClosure K) c₀
    calc triEmb K σ (AlgebraicClosure K) c₀ * triEmb K σ (AlgebraicClosure K) c'₀
        = triEmb K σ (AlgebraicClosure K) (c₀ * c'₀) := (map_mul _ _ _).symm
      _ = triEmb K σ (AlgebraicClosure K) (c'₀ * c₀) := by rw [hc0comm]
      _ = triEmb K σ (AlgebraicClosure K) c'₀ * triEmb K σ (AlgebraicClosure K) c₀ :=
          map_mul _ _ _
  have hφ_core : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      triEmb K σ (AlgebraicClosure K) (MulAut.congr eC φ x) =
        u * triEmb K σ (AlgebraicClosure K) x * u⁻¹ := by
    intro x
    rw [hφ_conj, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hψ_core : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      triEmb K σ (AlgebraicClosure K) (MulAut.congr eC ψ x) =
        u' * triEmb K σ (AlgebraicClosure K) x * u'⁻¹ := by
    intro x
    rw [hψ_conj, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hufix : twistHom TwistTag.D4 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 n) u = u :=
    triEmb_fixed (iterateFrobenius (AlgebraicClosure K) 2 n) hcommL c₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmon : MonomialToralAt Tag.D4 3 := monomialToralAt_three_of_block a2BlockToral_D4
  have hconjT : ∃ g ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K),
      g⁻¹ * u * g ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) :=
    exists_conj_torusGroup_of_pow_eq_one (τ := Tag.D4) (p := 3) Nat.prime_three hmon
      (by norm_num) (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (triEmb_mem_adjointGroup c₀) hu3
  obtain ⟨D, hDΦ, hDq, hmem⟩ :=
    exists_langDatum_of_toral_twisted TwistTag.D4 (L := AlgebraicClosure K) n hn hufix hconjT
  have hu'F : D.Φ u' = u' := by
    rw [hDΦ]
    exact triEmb_fixed (iterateFrobenius (AlgebraicClosure K) 2 n) hcommL c'₀
  have hd : LangDescent D 3 (triEmb K σ (AlgebraicClosure K)) :=
    langDescent_triD4_inner (K := K) (L := AlgebraicClosure K) (ℓ := 2) (f := n)
      Nat.prime_two hn hK σ hσ (Fr := iterateFrobenius (AlgebraicClosure K) 2 n)
      (fun c => iterateFrobenius_def 2 n c) D hDΦ (p := 3)
  obtain ⟨S, a, e₀, y, hSq, hT, ha3, h1, hyM, hyC, hy3, hφeq, hψeq⟩ :=
    ggNbrLSideRSExc_transport_of_datum (τ := Tag.D4) (L := AlgebraicClosure K) (f := n) hn
      D hDq (p₀ := 5) Nat.prime_five (by norm_num) (Or.inl le_rfl) hd.finite_model
      (triEmb K σ (AlgebraicClosure K)) triEmb_injective hd.Γ_eq
      (MulAut.congr eC φ) (MulAut.congr eC ψ) (u := u) (u' := u')
      hφ_core hψ_core hmem hu3 hu1 hu'G hu'F hu'3 hcommu
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, 5, S, a, eC.trans e₀, y,
    CharP.cast_eq_zero (AlgebraicClosure K) 2, hSq, hT, ha3, h1, hyM, hyC, hy3, ?_, ?_⟩
  · intro r
    have hφr : eC (φ r) = MulAut.congr eC φ (eC r) := by
      symm
      rw [hφ_conj, MulAut.conj_apply]
      change eC c * eC r * (eC c)⁻¹ = eC (φ r)
      rw [← hc, MulAut.conj_apply, map_mul, map_mul, map_inv]
    change ((e₀ (eC (φ r)) : ↥S.Γ) : ModGL Tag.D4 (AlgebraicClosure K)) =
      rootDiagUnit Tag.D4 a * ((e₀ (eC r) : ↥S.Γ) : ModGL Tag.D4 (AlgebraicClosure K)) *
        (rootDiagUnit Tag.D4 a)⁻¹
    rw [hφr]
    exact hφeq (eC r)
  · intro r
    have hψr : eC (ψ r) = MulAut.congr eC ψ (eC r) := by
      symm
      rw [hψ_conj, MulAut.conj_apply]
      change eC c' * eC r * (eC c')⁻¹ = eC (ψ r)
      rw [← hc', MulAut.conj_apply, map_mul, map_mul, map_inv]
    change ((e₀ (eC (ψ r)) : ↥S.Γ) : ModGL Tag.D4 (AlgebraicClosure K)) =
      y * ((e₀ (eC r) : ↥S.Γ) : ModGL Tag.D4 (AlgebraicClosure K)) * y⁻¹
    rw [hψr]
    exact hψeq (eC r)

end CFSG.StandardType

end
