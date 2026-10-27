module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOne
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessNorm
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessSim
public import CFSG.RankThree.SteinbergR3ECAOddD4Centralizer

public section

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification CFSG.RankThree.Classical2
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.OddD4Centralizer CFSG.RankThree.EvenD4Centralizer

namespace CFSG.RankThree.PartOne

theorem d4_mem_matrixProjectiveImage (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    ∀ (αP : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
      {u v : Fin (2 * 4) → K} (_ : coordinateQuadPlus 4 K u = 1)
      (_ : coordinateQuadPlus 4 K v = 1) (_ : polar (coordinateQuadPlus 4 K) u v = 0)
      (_ : ∀ s t : K, s • u + t • v = 0 → s = 0 ∧ t = 0)
      (ĝ : matrixDerived (coordinateQuadPlus 4 K))
      (_ : matrixLinearEquiv ĝ.val =
        reflect (coordinateQuadPlus 4 K) u * reflect (coordinateQuadPlus 4 K) v)
      (_ : αP (matrixProjectiveProjection (coordinateQuadPlus 4 K) ĝ) =
        matrixProjectiveProjection (coordinateQuadPlus 4 K) ĝ),
      αP ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  classical
  set Q := coordinateQuadPlus 4 K with hQdef
  intro αP u v hu hv huv hind ĝ hgl hαPfix
  have hconjeq : αP * MulAut.conj (matrixProjectiveProjection Q ĝ) * αP⁻¹ =
      MulAut.conj (matrixProjectiveProjection Q ĝ) := by
    rw [mulAut_conj_conj, hαPfix]
  have hchar : ringChar K = ℓ := (coordinate_model_witness_plus h K hK e).1
  by_cases h2 : (2 : K) = 0
  ·
    have hℓ2 : ℓ = 2 := by
      have h1 : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by exact_mod_cast h2)
      rw [← hchar]
      exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime K _) Nat.prime_two).mp h1
    subst hℓ2
    have hlin : LinearIndependent K ![u, v] := LinearIndependent.pair_iff.mpr hind
    obtain ⟨g', -, hvec, -, -, -, hcent, -⟩ :=
      even_D4_rank_two_involution_full_centralizer_preserves_point_family G h K hK e hlin hu hv
        huv
    have hneg : ∀ a : K, -a = a := fun a => by
      have : a + a = 0 := by rw [← two_mul, h2, zero_mul]
      exact neg_eq_of_add_eq_zero_right this
    have hgg : ĝ = g' := by
      refine Subtype.ext (matrixLinearIso.injective (LinearEquiv.ext fun x => ?_))
      have h1 : matrixLinearIso ĝ.val x = x - polar Q u x • u - polar Q v x • v := by
        have := KCOrthogonal.reflectPair_apply hu hv huv x
        rw [← this, ← hgl]
        rfl
      rw [h1, sub_eq_add_neg, sub_eq_add_neg, ← neg_smul, ← neg_smul, hneg, hneg,
        polar_comm Q u x, polar_comm Q v x]
      exact (hvec x).symm
    subst hgg
    exact (hcent αP hconjeq).2
  ·
    have hℓ : ℓ ≠ 2 := fun h2' => h2 (by
      have h3 : ringChar K ∣ 2 := by rw [hchar.trans h2']
      exact_mod_cast (ringChar.spec K 2).mpr h3)
    obtain ⟨g₀, hg₀l, -, hg₀ord, hg₀cent, hg₀E, -⟩ :=
      odd_D4_two_reflection_full_centralizer_preserves_point_family G hℓ h K hK e
    have hr : ∀ y, coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4) y) =
        quadPlus 4 K y := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
    have hQu₀ : coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4)
        (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)) = 1 := by
      rw [hr]
      exact quadPlus_single_add_single 0
    have hQv₀ : coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4)
        (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) = 1 := by
      rw [hr]
      exact quadPlus_single_add_single 1
    have huv₀ : polar (coordinateQuadPlus 4 K) (reindexVectorEquiv (plusIndexEquiv 4)
        (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1))
        (reindexVectorEquiv (plusIndexEquiv 4)
          (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) = 0 := by
      rw [CFSG.RankThree.EvenD4Centralizer.polar_map_isometry
        (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr, polar_single_add_single]
      simp
    obtain ⟨k, hkO, hku, hkv⟩ := exists_isometry_pair h2 Q hu hv huv hQu₀ hQv₀ huv₀
    have hconj : k * (reflect Q u * reflect Q v) * k⁻¹ = matrixLinearEquiv g₀.val := by
      rw [hg₀l]
      calc k * (reflect Q u * reflect Q v) * k⁻¹ =
          (k * reflect Q u * k⁻¹) * (k * reflect Q v * k⁻¹) := by group
        _ = _ := by rw [reflect_conj hkO, reflect_conj hkO, hku, hkv]
    have hkM : matrixLinearIso.symm k ∈ matrixIsometries Q := by
      change matrixLinearIso (matrixLinearIso.symm k) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
      rw [MulEquiv.apply_symm_apply]
      exact hkO
    have hconjM : matrixLinearIso.symm k * ĝ.val * (matrixLinearIso.symm k)⁻¹ = g₀.val := by
      apply matrixLinearIso.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact (congrArg (fun z => k * z * k⁻¹) hgl).trans hconj
    obtain ⟨β, hβE, hβ⟩ := exists_mem_projectiveImage_apply_eq Q hkM hconjM
    exact centralizer_conj_le_of_apply_eq _ hβE hβ (hg₀cent.trans hg₀E.le)
      (Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := hconjeq
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this))

theorem d4_induced_of_fixes_involution (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    ∀ (α : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)))
      {u v : Fin (2 * 4) → K} (_ : coordinateQuadPlus 4 K u = 1)
      (_ : coordinateQuadPlus 4 K v = 1) (_ : polar (coordinateQuadPlus 4 K) u v = 0)
      (_ : ∀ s t : K, s • u + t • v = 0 → s = 0 ∧ t = 0)
      (hg : reflect (coordinateQuadPlus 4 K) u * reflect (coordinateQuadPlus 4 K) v ∈
        orthDerived (coordinateQuadPlus 4 K))
      (_ : (2 : K) = 0 → reflect (coordinateQuadPlus 4 K) u * reflect (coordinateQuadPlus 4 K) v =
        eichler (coordinateQuadPlus 4 K) (u + v) u)
      (_ : α (QuotientGroup.mk (⟨reflect (coordinateQuadPlus 4 K) u *
          reflect (coordinateQuadPlus 4 K) v, hg⟩ : orthDerived (coordinateQuadPlus 4 K))) =
        QuotientGroup.mk (⟨reflect (coordinateQuadPlus 4 K) u *
          reflect (coordinateQuadPlus 4 K) v, hg⟩ : orthDerived (coordinateQuadPlus 4 K))),
      KCOrthogonalAut.InducedBySemilinear (coordinateQuadPlus 4 K) α := by
  classical
  have hd : 0 < 2 * 4 := by norm_num
  set Q := coordinateQuadPlus 4 K with hQdef
  intro α u v hu hv huv hind hg heich hfix
  obtain ⟨ĝ, hĝ⟩ := KCOrthogonalAut.exists_matrixDerived Q
    (⟨reflect Q u * reflect Q v, hg⟩ : orthDerived Q)
  have hbr : KCOrthogonalAut.coordBridge Q hd (matrixProjectiveProjection Q ĝ) =
      QuotientGroup.mk (⟨reflect Q u * reflect Q v, hg⟩ : orthDerived Q) :=
    KCOrthogonalAut.coordBridge_mk Q hd ĝ _ hĝ
  set αP : MulAut (matrixProjectiveDerived Q) :=
    MulAut.congr (KCOrthogonalAut.coordBridge Q hd).symm α with hαP
  have hαPfix : αP (matrixProjectiveProjection Q ĝ) = matrixProjectiveProjection Q ĝ := by
    rw [hαP, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
      hbr, hfix, ← hbr, MulEquiv.symm_apply_apply]
  exact KCOrthogonalAut.exists_semilin_of_mem_matrixProjectiveImage Q hd α
    (d4_mem_matrixProjectiveImage G h K hK e αP hu hv huv hind ĝ hĝ.symm hαPfix)

theorem orthogonal_inner_plane_common_centralizer_q_plus_one_d4 (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ℓ) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))))
    (hD : (MulAut.conj : ProjOrthDerived (coordinateQuadPlus 4 K) →*
      MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))).range ≤ D)
    (A : Subgroup (ProjOrthDerived (coordinateQuadPlus 4 K))) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) :
    (⨅ (a : ProjOrthDerived (coordinateQuadPlus 4 K)) (_ : a ∈ A ∧ a ≠ 1),
      Subgroup.centralizer (((CFSG.layer ↥(D ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)))))).map
          (D ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))))).subtype :
          Subgroup (MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)))) :
          Set (MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))))) = ⊥ := by
  obtain ⟨hchar, hnd, hT, -, -, -⟩ := coordinate_model_witness_plus h K hK e
  have hpl' : p ≠ ringChar K := by
    rw [hchar]
    exact hpl
  refine orthogonal_inner_plane_common_centralizer_q_plus_one_of_natural _ hnd hT hp hp3 hpl' hpq
    D hD A hA hAc fun α hcent => ?_
  obtain ⟨u, v, hg, hu, hv, huv, hind, -, heich, hfix⟩ :=
    qplus_pair_involution hnd hT hp hp3 hpl' hpq D hD A hA hAc α hcent
  exact d4_induced_of_fixes_involution G h K hK e α hu hv huv hind hg heich hfix

end CFSG.RankThree.PartOne
