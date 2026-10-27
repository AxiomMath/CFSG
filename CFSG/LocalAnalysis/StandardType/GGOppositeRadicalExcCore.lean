module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcAscent
public import CFSG.GroupTheory.OppositeRadicals
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalKempf
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.BruhatDecomposition
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLift

public section

namespace CFSG.StandardType

namespace GGOppRadExc

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical

section General

variable {G : Type*} [Group G]

theorem eq_of_inf_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hQ : IsPGroup p Q) (hRQ : R ≤ Q)
    (hN : Q ⊓ Subgroup.normalizer (R : Set G) ≤ R) : R = Q := by
  by_contra hne
  have hlt : R.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hRQ fun x hx => ?_)
    have : (⟨x, hx⟩ : Q) ∈ R.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨x, hxN, hxR⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf Q) hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hRQ, Subgroup.mem_subgroupOf] at hxN
  exact hxR (Subgroup.mem_subgroupOf.mpr (hN (Subgroup.mem_inf.mpr ⟨x.2, hxN⟩)))

theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

theorem map_conj_le_of_le {P A : Subgroup G} {g : G} (hg : g ∈ P) (hA : A ≤ P) :
    A.map (MulAut.conj g).toMonoidHom ≤ P := by
  rintro _ ⟨a, ha, rfl⟩
  exact mul_mem (mul_mem hg (hA ha)) (inv_mem hg)

end General

variable {τ : Tag} {K : Type} [Field K]

theorem rootSubgroup_le_parabolicSubgroup_of_neg {J : Set (Fin τ.rank)} {β : Fin τ.rank → ℤ}
    (hβ : -β ∈ parabolicPosRoots τ J) : rootSubgroup τ K β ≤ parabolicSubgroup τ K J := by
  obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-β) rfl hβ
  have hβw : β = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by rw [smul_neg, hwj, neg_neg]
  rw [hβw, ← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_neg_single τ j)]
  exact map_conj_le_of_le (canonicalRep_mem_parabolicSubgroup hw)
    ((rootSubgroup_neg_single_le_parabolicLevi hj).trans (parabolicLevi_le_parabolicSubgroup J))

theorem rootSubgroup_le_posUnipotent {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) : rootSubgroup τ K α ≤ posUnipotent τ K :=
  le_biSup (rootSubgroup τ K) (show α ∈ {α | IsRoot τ α ∧ 0 < height α} from ⟨hα, hpos⟩)

theorem exists_mul_of_mem_posUnipotent (J : Set (Fin τ.rank)) {x : ModGL τ K}
    (hx : x ∈ posUnipotent τ K) :
    ∃ q ∈ parabolicRadical τ K J, ∃ v ∈ parabolicLeviUnipotent τ K J, x = q * v := by
  have hxB : x ∈ (borelGroup τ K : Set (ModGL τ K)) := (le_sup_right : posUnipotent τ K ≤
    borelGroup τ K) hx
  rw [borelGroup_eq_mul_parabolic J] at hxB
  obtain ⟨q, hq, t, ht, hqt⟩ := Set.mem_mul.mp hxB
  obtain ⟨h, hh, v, hv, rfl⟩ := Set.mem_mul.mp ht
  subst hqt
  have hvU : v ∈ posUnipotent τ K := parabolicLeviUnipotent_le_posUnipotent J hv
  have hqU : q ∈ posUnipotent τ K := parabolicRadical_le_posUnipotent J hq
  have hhU : h ∈ posUnipotent τ K := by
    have : h = q⁻¹ * (q * (h * v)) * v⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hqU) hx) (inv_mem hvU)
  have h1 : h ∈ torusGroup τ K ⊓ posUnipotent τ K := Subgroup.mem_inf.mpr ⟨hh, hhU⟩
  rw [(triangular_borel_structure.{0, 0} τ K).2.2.2.1, Subgroup.mem_bot] at h1
  exact ⟨q, hq, v, hv, by rw [h1, one_mul]⟩

theorem pCoreOf_parabolicSubgroup_prime [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (J : Set (Fin τ.rank)) :
    pCoreOf r (parabolicSubgroup τ K J) = parabolicRadical τ K J := by
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨hQP, -, -, -, hQM, -, -, -, -, hVM, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors τ K J
  set P := parabolicSubgroup τ K J with hPdef
  set Q := parabolicRadical τ K J with hQdef
  set M := parabolicLevi τ K J with hMdef
  set O := pCoreOf r P with hOdef
  set U := posUnipotent τ K with hUdef
  set C := adjointGroup τ K with hCdef
  have hO2 : IsPGroup r O := pCoreOf_isPGroup r P
  have hPO : P ≤ Subgroup.normalizer (O : Set (ModGL τ K)) := le_normalizer_pCoreOf r P
  have hQO : Q ≤ O := le_pCoreOf_of_le_normalizer r hQP
    (parabolicSubgroup_le_normalizer_parabolicRadical J) (hfin r).2.1
  refine le_antisymm ?_ hQO
  have hUP : U ≤ P := posUnipotent_le_parabolicSubgroup J
  have hPC : P ≤ C := parabolicSubgroup_le_adjointGroup τ K J
  have hUC : U ≤ C := hUP.trans hPC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index r hUC (card_posUnipotent (τ := τ) (K := K))
  have hOU2 : IsPGroup r (O ⊔ U : Subgroup (ModGL τ K)) :=
    IsPGroup.to_sup_of_normal_left' hO2 (hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUC))
      (hUP.trans hPO)
  have hOUC : O ⊔ U ≤ C := sup_le ((pCoreOf_le r P).trans hPC) hUC
  have hmax := (hUp.toSylow hUi).is_maximal' (Q := (O ⊔ U).subgroupOf C)
    hOU2.comap_subtype (by
      rw [IsPGroup.toSylow_coe]
      exact fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)))
  rw [IsPGroup.toSylow_coe] at hmax
  have hOU : O ≤ U := by
    intro x hx
    have hxC : x ∈ C := hOUC (Subgroup.mem_sup_left hx)
    have : (⟨x, hxC⟩ : C) ∈ (O ⊔ U).subgroupOf C :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hx)
    rw [hmax] at this
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨wJ, ⟨hwJ, hwJroots⟩, -⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.2.2
  set n := canonicalRep (coxeterSystem τ) K wJ with hn
  have hnM : n ∈ M := canonicalRep_mem_parabolicLevi hwJ
  have hnP : n ∈ P := parabolicLevi_le_parabolicSubgroup J hnM
  have hOM : O ⊓ M = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hyO, hyM⟩ := Subgroup.mem_inf.mp hy
    have hV : ∀ z ∈ O, z ∈ M → z ∈ parabolicLeviUnipotent τ K J := by
      intro z hzO hzM
      obtain ⟨q, hq, v, hv, rfl⟩ := exists_mul_of_mem_posUnipotent J (hOU hzO)
      have hqM : q ∈ M := by
        have : q = q * v * v⁻¹ := by group
        rw [this]
        exact mul_mem hzM (inv_mem (hVM hv))
      have hq1 : q ∈ Q ⊓ M := Subgroup.mem_inf.mpr ⟨hq, hqM⟩
      rw [hQM, Subgroup.mem_bot] at hq1
      rw [hq1, one_mul]
      exact hv
    have hy' : n⁻¹ * y * n ∈ parabolicLeviUnipotent τ K J := by
      refine hV _ ?_ (mul_mem (mul_mem (inv_mem hnM) hyM) hnM)
      have := (Subgroup.mem_normalizer_iff.mp (hPO (inv_mem hnP)) y).mp hyO
      rwa [inv_inv] at this
    have hyN : y ∈ negUnipotent τ K := by
      have hmem : (MulAut.conj n).toMonoidHom (n⁻¹ * y * n) ∈
          (parabolicLeviUnipotent τ K J).map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy'
      rw [parabolicLeviUnipotent, (canonical_weyl_root_transport τ K).1 wJ _
        (fun α hα => hα.1.1), hwJroots] at hmem
      have e : (MulAut.conj n).toMonoidHom (n⁻¹ * y * n) = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e] at hmem
      refine rootSpan_le_negUnipotent (fun α hα => ?_) hmem
      obtain ⟨β, hβ, rfl⟩ := hα
      exact ⟨IsRoot.neg hβ.1.1, by rw [height_neg]; have := hβ.2.2; omega⟩
    have h1 : y ∈ U ⊓ negUnipotent τ K := Subgroup.mem_inf.mpr ⟨hOU hyO, hyN⟩
    rwa [CFSG.LieType.Chevalley.posUnipotent_inf_negUnipotent] at h1
  intro x hx
  obtain ⟨q, hq, v, hv, rfl⟩ := exists_mul_of_mem_posUnipotent J (hOU hx)
  have hvO : v ∈ O := by
    have : v = q⁻¹ * (q * v) := by group
    rw [this]
    exact mul_mem (inv_mem (hQO hq)) hx
  have hv1 : v ∈ O ⊓ M := Subgroup.mem_inf.mpr ⟨hvO, hVM hv⟩
  rw [hOM, Subgroup.mem_bot] at hv1
  rw [hv1, mul_one]
  exact hq

theorem pCoreOf_parabolicSubgroup [Finite K] [CharP K 2] (J : Set (Fin τ.rank)) :
    pCoreOf 2 (parabolicSubgroup τ K J) = parabolicRadical τ K J :=
  pCoreOf_parabolicSubgroup_prime 2 J

theorem isRadicalPGroup_parabolicRadical_prime [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (J : Set (Fin τ.rank)) :
    CFSG.GroupTheory.IsRadicalPGroup r (adjointGroup τ K) (parabolicRadical τ K J) := by
  unfold CFSG.GroupTheory.IsRadicalPGroup
  rw [adjointGroup_inf_normalizer_parabolicRadical, pCoreOf_parabolicSubgroup_prime r J]

theorem parabolicRadical_univ : parabolicRadical τ K Set.univ = ⊥ := by
  refine iSup₂_eq_bot.mpr fun α hα => ?_
  exact absurd ⟨⟨hα.1.1, fun i hi => absurd (Set.mem_univ i) hi⟩, hα.1⟩ hα.2

theorem exists_eq_map_conj_parabolicRadical_prime [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    {R : Subgroup (ModGL τ K)} (hR : R ≠ ⊥)
    (hRad : CFSG.GroupTheory.IsRadicalPGroup r (adjointGroup τ K) R) :
    ∃ g ∈ adjointGroup τ K, ∃ J : Set (Fin τ.rank),
      R = (parabolicRadical τ K J).map (MulAut.conj g).toMonoidHom := by
  have := finite_modGL (τ := τ) (K := K)
  set C := adjointGroup τ K with hCdef
  have hRC : R ≤ C := hRad.le
  have hR2 : IsPGroup r R := hRad.isPGroup
  obtain ⟨g, hg, J, hN, hQ⟩ := exists_optimal_radical_ordinary_prime r hRC hR2 hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ K J
  set R' := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'def
  have hgN : g⁻¹ ∈ Subgroup.normalizer (C : Set (ModGL τ K)) :=
    Subgroup.le_normalizer (inv_mem hg)
  have hR'rad : CFSG.GroupTheory.IsRadicalPGroup r C R' :=
    hRad.map_mulAut (MulAut.conj g⁻¹) (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN)
  have hR'Q : R' ≤ parabolicRadical τ K J := by
    rintro _ ⟨q, hq, rfl⟩
    have := hQ q hq
    simpa [MulAut.conj_apply] using this
  have hN' : C ⊓ Subgroup.normalizer (R' : Set (ModGL τ K)) ≤ parabolicSubgroup τ K J := by
    intro x hx
    obtain ⟨hxC, hxN⟩ := Subgroup.mem_inf.mp hx
    have hgx : g * x * g⁻¹ ∈ Subgroup.normalizer (R : Set (ModGL τ K)) := by
      have h1 : R = R'.map (MulAut.conj g).toMonoidHom := by
        rw [hR'def, ← GGTwoSig.map_conj_mul, mul_inv_cancel, GGTwoSig.map_conj_one]
      rw [h1, ← GGTwoSig.map_conj_normalizer]
      exact ⟨x, hxN, rfl⟩
    have := hN _ (mul_mem (mul_mem hg hxC) (inv_mem hg)) hgx
    simpa [mul_assoc] using this
  have hRQ : R' = parabolicRadical τ K J := by
    refine eq_of_inf_normalizer_le (hfin r).2.1 hR'Q ?_
    have hle : parabolicRadical τ K J ⊓ (C ⊓ Subgroup.normalizer (R' : Set (ModGL τ K))) ≤
        pCoreOf r (C ⊓ Subgroup.normalizer (R' : Set (ModGL τ K))) :=
      le_pCoreOf_of_le_normalizer r inf_le_right (fun x hx => mem_normalizer_inf
        (parabolicSubgroup_le_normalizer_parabolicRadical J (hN' hx))
        (Subgroup.le_normalizer hx)) ((hfin r).2.1.to_le inf_le_left)
    have hR'eq : pCoreOf r (C ⊓ Subgroup.normalizer (R' : Set (ModGL τ K))) = R' := hR'rad
    rw [hR'eq] at hle
    intro x hx
    obtain ⟨hxQ, hxN⟩ := Subgroup.mem_inf.mp hx
    exact hle (Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_inf.mpr
      ⟨(parabolicSubgroup_le_adjointGroup τ K J) (parabolicRadical_le_posUnipotent J hxQ |>
        posUnipotent_le_parabolicSubgroup J), hxN⟩⟩)
  refine ⟨g, hg, J, ?_⟩
  rw [← hRQ, hR'def, ← GGTwoSig.map_conj_mul, mul_inv_cancel, GGTwoSig.map_conj_one]

theorem exists_eq_map_conj_parabolicRadical [Finite K] [CharP K 2] {R : Subgroup (ModGL τ K)}
    (hR : R ≠ ⊥) (hRad : GGRadicalTwo (adjointGroup τ K) R) :
    ∃ g ∈ adjointGroup τ K, ∃ J : Set (Fin τ.rank),
      R = (parabolicRadical τ K J).map (MulAut.conj g).toMonoidHom := by
  refine exists_eq_map_conj_parabolicRadical_prime 2 hR ?_
  simpa [CFSG.GroupTheory.IsRadicalPGroup, GGRadicalTwo] using hRad

end GGOppRadExc

end CFSG.StandardType
