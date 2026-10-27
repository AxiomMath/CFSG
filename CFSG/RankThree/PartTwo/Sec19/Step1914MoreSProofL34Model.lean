module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec15.NoModNineTools

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProof

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K]

theorem card_pgl_three_of_card_four [Finite K] (h4 : Nat.card K = 4) :
    Nat.card (ProjGenLinGroup (Fin 3) K) = 60480 := by
  classical
  let _ := Fintype.ofFinite K
  have hq : Fintype.card K = 4 := by rw [Fintype.card_eq_nat_card, h4]
  have hGL : Nat.card (GL (Fin 3) K) = 181440 := by
    rw [Matrix.card_GL_field, hq, Fin.prod_univ_three]
    norm_num
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
    intro u v huv
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) huv
    simp at this
    exact Units.ext this
  have hZ : Nat.card (Subgroup.center (GL (Fin 3) K)) = 3 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hinj, Subgroup.card_top, Nat.card_units, h4]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (GL (Fin 3) K))
  rw [hGL, hZ] at h
  change Nat.card (GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K)) = 60480
  omega

theorem factorization_card_pgl_three_of_card_four [Finite K] (h4 : Nat.card K = 4) :
    (Nat.card (ProjGenLinGroup (Fin 3) K)).factorization 3 = 3 := by
  rw [card_pgl_three_of_card_four h4, show (60480 : ℕ) = 3 ^ 3 * 2240 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] noncomputable def stdTorus (K : Type) [Field K] :
    Subgroup (ProjGenLinGroup (Fin 3) K) :=
  (stdTypeC K).map ProjGenLinGroup.mk

@[expose] noncomputable def cycBar (K : Type) [Field K] : ProjGenLinGroup (Fin 3) K :=
  ProjGenLinGroup.mk cycThree

@[expose] noncomputable def stdSylow (K : Type) [Field K] :
    Subgroup (ProjGenLinGroup (Fin 3) K) :=
  stdTorus K ⊔ Subgroup.zpowers (cycBar K)

theorem card_stdTorus {π : Bool} {p f : ℕ} (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card (stdTorus K) = 9 := by
  rw [stdTorus, Sec15.card_map_mk_eq]
  exact (isTypeC_stdTypeC hK hq).2.2.1

theorem isElemAbelian_stdTorus : CFSG.Assembly.IsElemAbelian 3 (stdTorus K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨_, ⟨u, -, rfl⟩, rfl⟩⟩ := a
    obtain ⟨_, ⟨_, ⟨v, -, rfl⟩, rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm u v]
  · rintro _ ⟨_, ⟨abc, ⟨ha, hb, hc⟩, rfl⟩, rfl⟩
    rw [← map_pow, ← map_pow]
    have ha' : abc.1 ∈ rootsOfUnity 3 K := ha
    have hb' : abc.2.1 ∈ rootsOfUnity 3 K := hb
    have hc' : abc.2.2 ∈ rootsOfUnity 3 K := hc
    rw [mem_rootsOfUnity] at ha' hb' hc'
    have : abc ^ 3 = 1 := Prod.ext ha' (Prod.ext hb' hc')
    rw [this, map_one, map_one]

theorem cycBar_pow_three : cycBar K ^ 3 = 1 := by
  rw [cycBar, ← map_pow, cycThree_pow_three, map_one]

theorem cycBar_mem_normalizer [Finite K] :
    cycBar K ∈ Subgroup.normalizer (stdTorus K : Set _) := by
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  have hle : ∀ (g : GL (Fin 3) K), g ∈ stdTypeC K → cycThree * g * cycThree⁻¹ ∈ stdTypeC K := by
    rintro _ ⟨abc, ⟨ha, hb, hc⟩, rfl⟩
    refine ⟨(abc.2.2, abc.1, abc.2.1), ⟨hc, ha, hb⟩, ?_⟩
    change diagUnits abc.2.2 abc.1 abc.2.1 = cycThree * diagUnits abc.1 abc.2.1 abc.2.2 * _
    rw [cycThree_conj_diagUnits]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by
    rw [Subgroup.card_map_of_injective (MulAut.conj (cycBar K)).injective])
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨cycThree * g * cycThree⁻¹, hle g hg, ?_⟩
  simp [cycBar, map_mul, map_inv]

theorem cycBar_not_mem : cycBar K ∉ stdTorus K := by
  rintro ⟨_, ⟨abc, -, rfl⟩, h⟩
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  simp only [Units.val_mul, coe_diagHom, GeneralLinearGroup.coe_scalar, coe_cycThree] at h1
  simp at h1

theorem card_stdSylow {π : Bool} {p f : ℕ} (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card (stdSylow K) = 27 := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  have hN : Subgroup.zpowers (cycBar K) ≤ Subgroup.normalizer (stdTorus K : Set _) :=
    Subgroup.zpowers_le.mpr cycBar_mem_normalizer
  have hcard := Sec6.card_sup_mul_card_inf hN
  have hc1 : cycBar K ≠ 1 := fun h1 => cycBar_not_mem (h1 ▸ (stdTorus K).one_mem)
  have hord : orderOf (cycBar K) = 3 := orderOf_eq_prime cycBar_pow_three hc1
  have hinf : Subgroup.zpowers (cycBar K) ⊓ stdTorus K = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers (cycBar K) ⊓ stdTorus K : Subgroup _) ∣ 3 := by
      have h1 := Subgroup.card_dvd_of_le
        (inf_le_left : Subgroup.zpowers (cycBar K) ⊓ stdTorus K ≤ Subgroup.zpowers (cycBar K))
      rwa [Nat.card_zpowers, hord] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers (cycBar K) ⊓ stdTorus K = Subgroup.zpowers (cycBar K) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hord])
      have hc : cycBar K ∈ Subgroup.zpowers (cycBar K) ⊓ stdTorus K := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact cycBar_not_mem hc.2
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord, card_stdTorus hK hq,
    sup_comm] at hcard
  rw [stdSylow]
  omega

theorem isSylowOf_stdSylow {π : Bool} {p f : ℕ} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h4 : Nat.card K = 4) :
    CFSG.ABGLocalTools.IsSylowOf 3 (stdSylow K) (⊤ : Subgroup (ProjGenLinGroup (Fin 3) K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [card_stdSylow hK hq, Subgroup.card_top, factorization_card_pgl_three_of_card_four h4]
  norm_num

theorem stdTorus_not_le [Finite K] (h4 : Nat.card K = 4) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (q : ℕ) : ¬ stdTorus K ≤ projImage (slPi true 3 q K) := by
  intro hle
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set t : Kˣ := Units.mk0 τ hτ0 with ht
  have htmem : diagHom (t, 1, 1) ∈ stdTypeC K := by
    refine ⟨(t, 1, 1), ⟨?_, one_mem _, one_mem _⟩, rfl⟩
    change t ∈ rootsOfUnity 3 K
    rw [mem_rootsOfUnity]
    exact Units.ext (by simp [ht, hτ])
  obtain ⟨s, hs, hsd⟩ := hle ⟨_, htmem, rfl⟩
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hsd
  have hdet := congrArg GeneralLinearGroup.det hu
  rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hs1 : GeneralLinearGroup.det s = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact (mem_slPi_true q).mp hs)
  have hd : GeneralLinearGroup.det (diagHom (t, 1, 1)) = t := Units.ext (by
    rw [GeneralLinearGroup.val_det_apply, coe_diagHom, det_diagonal, Fin.prod_univ_three]
    simp)
  rw [hs1, one_mul, hd] at hdet
  have hu3 : u ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := u)
    rw [Nat.card_units, h4] at this
    simpa using this
  rw [hu3] at hdet
  apply hτ1
  have := congrArg Units.val hdet
  simpa [ht] using this.symm

theorem isTypeC_map_conj {π : Bool} {q : ℕ} {D : Subgroup (GL (Fin 3) K)}
    (hD : IsTypeC π q K D) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 q K) :
    IsTypeC π q K (D.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hDH, hD3, hD9, b, hb, hbD⟩ := hD
  have hconj : ∀ d : GL (Fin 3) K, (MulAut.conj g).toMonoidHom d = g * d * g⁻¹ := fun d => rfl
  refine ⟨?_, ?_, ?_, fun i => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [hconj]
    exact mul_mem (mul_mem hg (hDH hd)) (inv_mem hg)
  · rintro _ ⟨d, hd, rfl⟩
    rw [hconj, conj_pow]
    have h3 := hD3 d hd
    rw [commute_of_mem_statedScalars h3 g, mul_inv_cancel_right]
    exact h3
  · have hmap : (D.map (MulAut.conj g).toMonoidHom).map
        (QuotientGroup.mk' (StatedScalars (Fin 3) K)) =
        (D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K))).map
          (MulAut.conj (QuotientGroup.mk' (StatedScalars (Fin 3) K) g)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj _).injective, hD9]
  · have hinj : LinearMap.ker (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro v w hvw
      have h1 := congrArg (fun u => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) hvw
      simpa [Matrix.mulVec_mulVec] using h1
    have h : LinearIndependent K ((Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) ∘ b) :=
      hb.map' _ hinj
    exact h
  · rintro _ ⟨d, hd, rfl⟩ i
    obtain ⟨c, hc⟩ := hbD d hd i
    refine ⟨c, ?_⟩
    rw [hconj, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]

end CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProof
