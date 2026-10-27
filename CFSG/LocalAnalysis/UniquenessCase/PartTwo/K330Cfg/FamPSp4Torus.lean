module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Basic
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.SylowIndex
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open Matrix CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.ClassicalInvolution.ModelFacts.OddCover

private theorem k330c_map_isMulCommutative {G N : Type} [Group G] [Group N] (f : G →* N)
    {S : Subgroup G} (h : IsMulCommutative S) : IsMulCommutative (S.map f) := by
  rw [isMulCommutative_iff] at h ⊢
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
  have hc := congrArg (fun z : S => f (z : G)) (h ⟨a', ha'⟩ ⟨b', hb'⟩)
  exact Subtype.ext (by simpa only [Subgroup.coe_mul, map_mul] using hc)

private theorem k330c_sp_torusBig_of_abelian {G : Type} [Group G] [Finite G] {L : ℕ}
    {H : Subgroup G} (hcomm : IsMulCommutative H) (hidx : ¬ 3 ∣ H.index)
    (hcard : L ≤ Nat.card H) : TorusBig G L := by
  intro Z hZ hZ9
  obtain ⟨x, hx⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_conj_le_of_not_dvd_index
      Nat.prime_three H hidx Z hZ.isPGroup
  let H' : Subgroup G := H.map (MulAut.conj x⁻¹).toMonoidHom
  have hZH' : Z ≤ H' := by
    intro z hz
    exact Subgroup.mem_map.2 ⟨x * z * x⁻¹, hx z hz, by
      change MulAut.conj x⁻¹ (x * z * x⁻¹) = z
      rw [MulAut.conj_apply, inv_inv]
      group⟩
  have hH'comm : IsMulCommutative H' := k330c_map_isMulCommutative _ hcomm
  have hH'cen : H' ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact hZH'.trans (Subgroup.le_centralizer_iff_isMulCommutative.2 hH'comm)
  have hH'norm : H' ≤ Subgroup.normalizer (Z : Set G) :=
    hH'cen.trans (Subgroup.centralizer_le_normalizer _)
  calc L ≤ Nat.card H := hcard
    _ = Nat.card H' := (Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective).symm
    _ ≤ Nat.card (Subgroup.normalizer (Z : Set G)) := Subgroup.card_le_of_le hH'norm

private theorem k330c_sp_torusBig_of_abelian_card {G : Type} [Group G] [Finite G] {L : ℕ}
    {H : Subgroup G} (hcomm : IsMulCommutative H) (h9 : 9 ∣ Nat.card H)
    (hcard : L ≤ Nat.card H) : TorusBig G L := by
  by_cases hsep : ∃ Z : Subgroup G, IsSylowOf 3 Z ⊤ ∧ Nat.card Z = 9
  · obtain ⟨Z₀, hZ₀, hZ₀9⟩ := hsep
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hG3 : (Nat.card G).factorization 3 = 2 := by
      have h1 : Nat.card Z₀ = 3 ^ (Nat.card (⊤ : Subgroup G)).factorization 3 := hZ₀.card_eq
      rw [hZ₀9, Subgroup.card_top] at h1
      have h2 : 3 ^ (Nat.card G).factorization 3 = 3 ^ 2 := by
        rw [← h1]
        norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
    have hHle : (Nat.card H).factorization 3 ≤ (Nat.card G).factorization 3 :=
      ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).2
        (Subgroup.card_subgroup_dvd_card H)) 3
    have hHge : 2 ≤ (Nat.card H).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2) (Nat.card_pos.ne')).1
        (by simpa using h9)
    have hH3 : (Nat.card H).factorization 3 = 2 := by
      rw [hG3] at hHle
      omega
    have hidx : ¬ 3 ∣ H.index := by
      intro h3
      have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hge : 1 ≤ H.index.factorization 3 :=
        (Nat.prime_three.dvd_iff_one_le_factorization hne).1 h3
      have hfac : (Nat.card G).factorization 3 =
          (Nat.card H).factorization 3 + H.index.factorization 3 := by
        have h1 := congrArg (fun f : ℕ →₀ ℕ => f 3)
          (Nat.factorization_mul (Nat.card_pos (α := H)).ne' hne)
        rw [Subgroup.card_mul_index H] at h1
        exact h1
      rw [hG3, hH3] at hfac
      omega
    exact k330c_sp_torusBig_of_abelian hcomm hidx hcard
  · intro Z hZ hZ9
    exact (hsep ⟨Z, hZ, hZ9⟩).elim

private theorem k330c_card_map_mul_card_subgroupOf_ker {G N : Type} [Group G] [Group N]
    (f : G →* N) (T : Subgroup G) :
    Nat.card (T.map f) * Nat.card ((f.ker).subgroupOf T) = Nat.card T := by
  have h := Subgroup.card_ker_mul_card_range (f.comp T.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hker : (f.comp T.subtype).ker = (f.ker).subgroupOf T := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [hker] at h
  rw [mul_comm] at h
  exact h

private def k330c_subgroupOfToSub {G : Type} [Group G] (N S : Subgroup G) :
    (N.subgroupOf S) →* N where
  toFun x := ⟨(x.1 : G), x.2⟩
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl

private theorem k330c_subgroupOfToSub_injective {G : Type} [Group G] (N S : Subgroup G) :
    Function.Injective (k330c_subgroupOfToSub N S) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : G)) h))

private theorem k330c_card_ker_proj_le_two {K : Type} [Field K] [Finite K] :
    Nat.card (SymplecticFlag.proj 2 K).ker ≤ 2 := by
  have hker : (SymplecticFlag.proj 2 K).ker = SymplecticHigher.spScalars 2 K :=
    QuotientGroup.ker_mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
  rw [hker, CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K (by norm_num : 1 ≤ 2)]
  exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 2 _)

private theorem k330c_sp_card_map_proj_ge {K : Type} [Field K] [Finite K]
    (H0 : Subgroup (StatedSp 2 K)) :
    Nat.card H0 / 2 ≤ Nat.card (H0.map (SymplecticFlag.proj 2 K)) := by
  have hsplit := k330c_card_map_mul_card_subgroupOf_ker (SymplecticFlag.proj 2 K) H0
  have hle : Nat.card (((SymplecticFlag.proj 2 K).ker).subgroupOf H0) ≤ 2 :=
    le_trans (Nat.card_le_card_of_injective _
      (k330c_subgroupOfToSub_injective _ H0)) (k330c_card_ker_proj_le_two (K := K))
  apply Nat.div_le_of_le_mul
  calc Nat.card H0 = Nat.card (H0.map (SymplecticFlag.proj 2 K)) *
        Nat.card (((SymplecticFlag.proj 2 K).ker).subgroupOf H0) := hsplit.symm
    _ ≤ Nat.card (H0.map (SymplecticFlag.proj 2 K)) * 2 := Nat.mul_le_mul_left _ hle
    _ = 2 * Nat.card (H0.map (SymplecticFlag.proj 2 K)) := Nat.mul_comm _ _

private theorem k330c_sp_nine_dvd_map {K : Type} [Field K] [Finite K]
    {H0 : Subgroup (StatedSp 2 K)} (h9 : 9 ∣ Nat.card H0) :
    9 ∣ Nat.card (H0.map (SymplecticFlag.proj 2 K)) := by
  have hsplit := k330c_card_map_mul_card_subgroupOf_ker (SymplecticFlag.proj 2 K) H0
  have hle : Nat.card (((SymplecticFlag.proj 2 K).ker).subgroupOf H0) ≤ 2 :=
    le_trans (Nat.card_le_card_of_injective _
      (k330c_subgroupOfToSub_injective _ H0)) (k330c_card_ker_proj_le_two (K := K))
  have hnot3 : ¬ 3 ∣ Nat.card (((SymplecticFlag.proj 2 K).ker).subgroupOf H0) := by
    intro h
    have := Nat.le_of_dvd (Nat.card_pos (α := ((SymplecticFlag.proj 2 K).ker).subgroupOf H0)) h
    omega
  have hcop : Nat.Coprime 9 (Nat.card (((SymplecticFlag.proj 2 K).ker).subgroupOf H0)) := by
    rw [show 9 = 3 ^ 2 by norm_num]
    exact (Nat.coprime_pow_left_iff (by norm_num) 3 _).2
      ((Nat.prime_three.coprime_iff_not_dvd).2 hnot3)
  have hprod : 9 ∣ Nat.card (H0.map (SymplecticFlag.proj 2 K)) *
      Nat.card (((SymplecticFlag.proj 2 K).ker).subgroupOf H0) := by
    rw [hsplit]
    exact h9
  exact hcop.dvd_of_dvd_mul_right hprod

private theorem k330c_card_torus_two (K : Type) [Field K] [Finite K] :
    Nat.card (torus 2 K) = (Nat.card K - 1) ^ 2 := by
  rw [torus, ← Nat.card_congr (MonoidHom.ofInjective
    (torusHom_injective (r := 2) (k := K))).toEquiv,
    Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]

private theorem k330c_isMulCommutative_torus_two (K : Type) [Field K] :
    IsMulCommutative (torus 2 K) :=
  Subgroup.range_isMulCommutative (torusHom (r := 2) (k := K))

private theorem k330c_card_Qsp {K : Type} [Field K] [Finite K] :
    Nat.card (Qsp K) = Nat.card K ^ 3 := by
  let f : K × K × K → Qsp K :=
    fun v => ⟨qSp v.1 v.2.1 v.2.2, ⟨v.1, v.2.1, v.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := qSp_injective (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨g, x, y, z, rfl⟩ := g
      exact ⟨(x, y, z), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod]
  ring

private theorem k330c_isMulCommutative_Qsp {K : Type} [Field K] :
    IsMulCommutative (Qsp K) := by
  rw [isMulCommutative_iff]
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨x, y, z, rfl⟩ := ha
  obtain ⟨x', y', z', rfl⟩ := hb
  exact Subtype.ext (qSp_comm x y z x' y' z')

private theorem k330c_pairMat_injective {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]
    {a b : ι} (hab : a ≠ b) :
    Function.Injective (fun g : Matrix (Fin 2) (Fin 2) R => pairMat a b g) := by
  intro g g' h
  have h' : pairMat a b g = pairMat a b g' := h
  ext i j
  fin_cases i <;> fin_cases j
  · have h1 := (pairMat_apply_pair hab g).1
    have h2 := (pairMat_apply_pair hab g').1
    have := congrFun (congrFun h' a) a
    rwa [h1, h2] at this
  · have h1 := (pairMat_apply_pair hab g).2.1
    have h2 := (pairMat_apply_pair hab g').2.1
    have := congrFun (congrFun h' a) b
    rwa [h1, h2] at this
  · have h1 := (pairMat_apply_pair hab g).2.2.1
    have h2 := (pairMat_apply_pair hab g').2.2.1
    have := congrFun (congrFun h' b) a
    rwa [h1, h2] at this
  · have h1 := (pairMat_apply_pair hab g).2.2.2
    have h2 := (pairMat_apply_pair hab g').2.2.2
    have := congrFun (congrFun h' b) b
    rwa [h1, h2] at this

private theorem k330c_lam_injective {k : Type} [Field k] {r : ℕ} (i : Fin r) :
    Function.Injective (lam (k := k) i) := by
  intro g g' h
  have hmat : pairMat (Sum.inl i) (Sum.inr i) ((g : Matrix (Fin 2) (Fin 2) k)) =
      pairMat (Sum.inl i) (Sum.inr i) ((g' : Matrix (Fin 2) (Fin 2) k)) := by
    have := congrArg (fun z : StatedSp r k => ((z : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) h
    simpa only [coe_lam] using this
  exact Subtype.ext (k330c_pairMat_injective Sum.inl_ne_inr hmat)

private noncomputable def k330c_sp_pairHom {K : Type} [Field K] {M : Type} [Group M]
    (ψ : M →* SpecialLinearGroup (Fin 2) K) : M × M →* StatedSp 2 K where
  toFun p := lam (k := K) (r := 2) 0 (ψ p.1) * lam (r := 2) 1 (ψ p.2)
  map_one' := by simp
  map_mul' p q := by
    have hc : Commute (lam (k := K) (r := 2) 0 (ψ q.1)) (lam (r := 2) 1 (ψ p.2)) :=
      commute_lam_lam (i := (0 : Fin 2)) (j := 1) (by decide) (ψ q.1) (ψ p.2)
    have key : lam (k := K) (r := 2) 0 (ψ p.1) * lam (r := 2) 0 (ψ q.1) *
          (lam (r := 2) 1 (ψ p.2) * lam (r := 2) 1 (ψ q.2)) =
        (lam (r := 2) 0 (ψ p.1) * lam (r := 2) 1 (ψ p.2)) *
          (lam (r := 2) 0 (ψ q.1) * lam (r := 2) 1 (ψ q.2)) := by
      calc lam (k := K) (r := 2) 0 (ψ p.1) * lam (r := 2) 0 (ψ q.1) *
            (lam (r := 2) 1 (ψ p.2) * lam (r := 2) 1 (ψ q.2))
          = lam (k := K) (r := 2) 0 (ψ p.1) *
              (lam (r := 2) 0 (ψ q.1) * lam (r := 2) 1 (ψ p.2)) *
              lam (r := 2) 1 (ψ q.2) := by group
        _ = lam (k := K) (r := 2) 0 (ψ p.1) *
              (lam (r := 2) 1 (ψ p.2) * lam (r := 2) 0 (ψ q.1)) *
              lam (r := 2) 1 (ψ q.2) := by rw [hc.eq]
        _ = (lam (r := 2) 0 (ψ p.1) * lam (r := 2) 1 (ψ p.2)) *
              (lam (r := 2) 0 (ψ q.1) * lam (r := 2) 1 (ψ q.2)) := by group
    rw [Prod.fst_mul, Prod.snd_mul,
      map_mul ψ p.1 q.1, map_mul ψ p.2 q.2,
      map_mul (lam (k := K) (r := 2) 0) (ψ p.1) (ψ q.1),
      map_mul (lam (r := 2) 1) (ψ p.2) (ψ q.2), key]

private theorem k330c_sp_pairHom_ker_eq_bot {K : Type} [Field K] {M : Type} [Group M]
    (ψ : M →* SpecialLinearGroup (Fin 2) K) (hψ : Function.Injective ψ) :
    (k330c_sp_pairHom ψ).ker = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hp
  rw [MonoidHom.mem_ker] at hp
  have hAB : Disjoint ({Sum.inl (0 : Fin 2), Sum.inr 0} : Set (Fin 2 ⊕ Fin 2))
      ({Sum.inl 1, Sum.inr 1} : Set (Fin 2 ⊕ Fin 2)) := by
    rw [Set.disjoint_left]
    rintro x (hx | hx) (hy | hy) <;> simp_all
  have hp' : lam (k := K) (r := 2) 0 (ψ a) * lam (r := 2) 1 (ψ b) = 1 := hp
  have hp'' : lam (k := K) (r := 2) 1 (ψ b) * lam (r := 2) 0 (ψ a) = 1 :=
    mul_eq_one_comm.mp hp'
  have hprod : (((lam (k := K) (r := 2) 0 (ψ a) : StatedSp 2 K) :
          GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((lam (k := K) (r := 2) 1 (ψ b) : StatedSp 2 K) :
          GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, hp']
    rfl
  have hprod' : (((lam (k := K) (r := 2) 1 (ψ b) : StatedSp 2 K) :
          GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((lam (k := K) (r := 2) 0 (ψ a) : StatedSp 2 K) :
          GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, hp'']
    rfl
  have hMmat : (((lam (k := K) (r := 2) 0 (ψ a) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    ext x y
    by_cases hx : x ∈ ({Sum.inl (0 : Fin 2), Sum.inr 0} : Set (Fin 2 ⊕ Fin 2))
    · rw [← IsSupp.mul_apply_of_mem (isSupp_lam (k := K) (r := 2) (0 : Fin 2) (ψ a))
          (isSupp_lam (k := K) (r := 2) (1 : Fin 2) (ψ b)) hAB hx, hprod]
    · exact (isSupp_lam (k := K) (r := 2) (0 : Fin 2) (ψ a)) x y (Or.inl hx)
  have hNmat : (((lam (k := K) (r := 2) 1 (ψ b) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    ext x y
    by_cases hx : x ∈ ({Sum.inl 1, Sum.inr 1} : Set (Fin 2 ⊕ Fin 2))
    · rw [← IsSupp.mul_apply_of_mem (isSupp_lam (k := K) (r := 2) (1 : Fin 2) (ψ b))
          (isSupp_lam (k := K) (r := 2) (0 : Fin 2) (ψ a)) hAB.symm hx, hprod']
    · exact (isSupp_lam (k := K) (r := 2) (1 : Fin 2) (ψ b)) x y (Or.inl hx)
  have hM1 : lam (k := K) (r := 2) 0 (ψ a) = 1 := Subtype.ext (Units.ext hMmat)
  have hN1 : lam (k := K) (r := 2) 1 (ψ b) = 1 := Subtype.ext (Units.ext hNmat)
  have ha : ψ a = 1 := k330c_lam_injective (0 : Fin 2) (by rw [hM1, map_one])
  have hb : ψ b = 1 := k330c_lam_injective (1 : Fin 2) (by rw [hN1, map_one])
  rw [Subgroup.mem_bot]
  exact Prod.ext (hψ (by simpa using ha)) (hψ (by simpa using hb))

private theorem k330c_sp_pairHom_injective {K : Type} [Field K] {M : Type} [Group M]
    (ψ : M →* SpecialLinearGroup (Fin 2) K) (hψ : Function.Injective ψ) :
    Function.Injective (k330c_sp_pairHom ψ) :=
  (MonoidHom.ker_eq_bot_iff _).mp (k330c_sp_pairHom_ker_eq_bot ψ hψ)

private theorem k330c_sp_nonsplit_abelian (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (h3 : 3 ∣ Nat.card K + 1) :
    ∃ H : Subgroup (StatedProj (StatedSp 2 K)),
      IsMulCommutative H ∧ 9 ∣ Nat.card H ∧
      ((Nat.card K - 1) ^ 2) / 2 ≤ Nat.card H := by
  let E := FiniteField.Extension K p 2
  haveI hquad : Algebra.IsQuadraticExtension K E :=
    { finrank_eq_two' := FiniteField.finrank_extension K p 2 }
  let N1 : Subgroup Eˣ := (TauCeti.Algebra.normUnits K : Eˣ →* Kˣ).ker
  have hfun : (TauCeti.Algebra.normUnits K : Eˣ →* Kˣ) =
      Units.map (Algebra.norm K (S := E)) := by
    ext u
    rw [TauCeti.Algebra.coe_normUnits (R := K) (S := E) u, Units.coe_map]
  have hnorm : Function.Surjective (TauCeti.Algebra.normUnits K : Eˣ →* Kˣ) := by
    rw [hfun]
    exact FiniteField.unitsMap_norm_surjective K E
  have hcardN1 : Nat.card N1 = Nat.card K + 1 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hnorm
    rw [Nat.card_units, Nat.card_units, FiniteField.natCard_extension] at h
    have hK1 : 1 < Nat.card K := Finite.one_lt_card
    have hsub : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      simpa using Nat.sq_sub_sq (Nat.card K) 1
    rw [hsub] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  let ψfun : N1 → SpecialLinearGroup (Fin 2) K := fun x =>
    ⟨(TauCeti.GL2NonSplitTorusHom K E (x : Eˣ) : Matrix (Fin 2) (Fin 2) K), by
      rw [← Matrix.GeneralLinearGroup.val_det_apply,
        TauCeti.GL2NonSplitTorus.det_gl2NonSplitTorusHom (F := K) (E := E),
        (MonoidHom.mem_ker).1 x.2, Units.val_one]⟩
  let ψ : N1 →* SpecialLinearGroup (Fin 2) K :=
    { toFun := ψfun
      map_one' := by
        apply Subtype.ext
        simp [ψfun]
      map_mul' := fun x y => by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul]
        show (TauCeti.GL2NonSplitTorusHom K E ((x : Eˣ) * (y : Eˣ)) :
            Matrix (Fin 2) (Fin 2) K) =
          ((TauCeti.GL2NonSplitTorusHom K E (x : Eˣ) : Matrix (Fin 2) (Fin 2) K) *
           (TauCeti.GL2NonSplitTorusHom K E (y : Eˣ) : Matrix (Fin 2) (Fin 2) K))
        rw [map_mul, Units.val_mul] }
  have hψinj : Function.Injective ψ := by
    intro x y h
    have hmat : (TauCeti.GL2NonSplitTorusHom K E (x : Eˣ) : Matrix (Fin 2) (Fin 2) K) =
        (TauCeti.GL2NonSplitTorusHom K E (y : Eˣ) : Matrix (Fin 2) (Fin 2) K) :=
      congrArg Subtype.val h
    have hunit : TauCeti.GL2NonSplitTorusHom K E (x : Eˣ) =
        TauCeti.GL2NonSplitTorusHom K E (y : Eˣ) := Units.ext hmat
    exact Subtype.ext (TauCeti.GL2NonSplitTorus.gl2NonSplitTorusHom_injective hunit)
  let Φ : N1 × N1 →* StatedSp 2 K := k330c_sp_pairHom ψ
  have hΦinj : Function.Injective Φ := k330c_sp_pairHom_injective ψ hψinj
  let H0 : Subgroup (StatedSp 2 K) := Φ.range
  have hH0card : Nat.card H0 = (Nat.card K + 1) ^ 2 := by
    change Nat.card Φ.range = (Nat.card K + 1) ^ 2
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv, Nat.card_prod, hcardN1]
    ring
  have hH0comm : IsMulCommutative H0 := Subgroup.range_isMulCommutative Φ
  refine ⟨H0.map (SymplecticFlag.proj 2 K), ?_, ?_, ?_⟩
  · exact k330c_map_isMulCommutative _ hH0comm
  · have h9 : 9 ∣ Nat.card H0 := by
      rw [hH0card]
      obtain ⟨m, hm⟩ := h3
      exact ⟨m ^ 2, by rw [hm]; ring⟩
    exact k330c_sp_nine_dvd_map h9
  · have hge := k330c_sp_card_map_proj_ge H0
    have hle : (Nat.card K - 1) ^ 2 ≤ (Nat.card K + 1) ^ 2 :=
      Nat.pow_le_pow_left ((Nat.sub_le _ _).trans (Nat.le_succ _)) 2
    calc ((Nat.card K - 1) ^ 2) / 2 ≤ ((Nat.card K + 1) ^ 2) / 2 := Nat.div_le_div_right hle
      _ = Nat.card H0 / 2 := by rw [hH0card]
      _ ≤ Nat.card (H0.map (SymplecticFlag.proj 2 K)) := hge

private theorem k330c_torusBig_of_mulEquiv {J T : Type} [Group J] [Finite J] [Group T] [Finite T]
    (e : J ≃* T) {L : ℕ} (h : TorusBig T L) : TorusBig J L := by
  intro Z hZ hZ9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ' : IsSylowOf 3 (Z.map e.toMonoidHom) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [Subgroup.card_map_of_injective e.injective, hZ.card_eq, Subgroup.card_top,
      Subgroup.card_top, Nat.card_congr e.toEquiv]
  have h9' : Nat.card (Z.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hZ9]
  have hres := h (Z.map e.toMonoidHom) hZ' h9'
  have hN : Nat.card (Subgroup.normalizer ((Z.map e.toMonoidHom : Subgroup T) : Set T)) =
      Nat.card (Subgroup.normalizer (Z : Set J)) := by
    rw [← Subgroup.map_equiv_normalizer_eq Z e, Subgroup.card_map_of_injective e.injective]
  rwa [hN] at hres

theorem torusBig_PSp4 {J : Type} [Group J] [Finite J] {p f : ℕ} (e : LieModel J .PSp 2 p f) :
    TorusBig J (spTorusLow (p ^ f)) := by
  have hC : StatedClassicalModel J .PSp 2 p f := e.statedClassicalModel (by decide)
  obtain ⟨hadm, K, hfield, hfinite, hKcard, ⟨eK⟩⟩ := hC
  letI : Field K := hfield
  letI : Finite K := hfinite
  obtain ⟨hp, hf, -⟩ := hadm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card, hKcard])
  have hmain : TorusBig (StatedProj (StatedSp 2 K)) (((p ^ f - 1) ^ 2) / 2) := by
    have hmod : Nat.card K % 3 = 0 ∨ Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by
      have := Nat.mod_lt (Nat.card K) (by norm_num : 0 < 3)
      omega
    rcases hmod with h0 | h1 | h2
    ·
      have h3 : 3 ∣ Nat.card K := Nat.dvd_of_mod_eq_zero h0
      let H0 : Subgroup (StatedSp 2 K) := Qsp K
      have hcard : Nat.card H0 = Nat.card K ^ 3 := k330c_card_Qsp
      have hcomm : IsMulCommutative H0 := k330c_isMulCommutative_Qsp
      have h9 : 9 ∣ Nat.card H0 := by
        rw [hcard]
        obtain ⟨m, hm⟩ := h3
        exact ⟨3 * m ^ 3, by rw [hm]; ring⟩
      have hge := k330c_sp_card_map_proj_ge H0
      have hle : (Nat.card K - 1) ^ 2 ≤ Nat.card H0 := by
        rw [hcard]
        calc (Nat.card K - 1) ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
          _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_right (by
              have hK1 : 1 < Nat.card K := Finite.one_lt_card
              omega) (by norm_num : 2 ≤ 3)
      have hbound : (((p ^ f - 1) ^ 2) / 2) ≤ Nat.card (H0.map (SymplecticFlag.proj 2 K)) := by
        rw [← hKcard]
        calc ((Nat.card K - 1) ^ 2) / 2 ≤ Nat.card H0 / 2 := Nat.div_le_div_right hle
          _ ≤ Nat.card (H0.map (SymplecticFlag.proj 2 K)) := hge
      exact k330c_sp_torusBig_of_abelian_card (k330c_map_isMulCommutative _ hcomm)
        (k330c_sp_nine_dvd_map h9) hbound
    ·
      let H0 : Subgroup (StatedSp 2 K) := torus 2 K
      have hcard : Nat.card H0 = (Nat.card K - 1) ^ 2 := k330c_card_torus_two K
      have hcomm : IsMulCommutative H0 := k330c_isMulCommutative_torus_two K
      have h9 : 9 ∣ Nat.card H0 := by
        rw [hcard]
        obtain ⟨m, hm⟩ : ∃ m, Nat.card K = 3 * m + 1 := ⟨Nat.card K / 3, by omega⟩
        have hm1 : Nat.card K - 1 = 3 * m := by omega
        exact ⟨m ^ 2, by rw [hm1]; ring⟩
      have hbound : (((p ^ f - 1) ^ 2) / 2) ≤ Nat.card (H0.map (SymplecticFlag.proj 2 K)) := by
        rw [← hKcard, ← hcard]
        exact k330c_sp_card_map_proj_ge H0
      exact k330c_sp_torusBig_of_abelian_card (k330c_map_isMulCommutative _ hcomm)
        (k330c_sp_nine_dvd_map h9) hbound
    ·
      have h3 : 3 ∣ Nat.card K + 1 := by
        obtain ⟨m, hm⟩ : ∃ m, Nat.card K = 3 * m + 2 := ⟨Nat.card K / 3, by omega⟩
        exact ⟨m + 1, by omega⟩
      obtain ⟨H, hHcomm, hH9, hHbound⟩ := k330c_sp_nonsplit_abelian K p h3
      have hbound : (((p ^ f - 1) ^ 2) / 2) ≤ Nat.card H := by
        rw [← hKcard]
        exact hHbound
      exact k330c_sp_torusBig_of_abelian_card hHcomm hH9 hbound
  have hJ := k330c_torusBig_of_mulEquiv eK hmain
  simpa [spTorusLow] using hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
