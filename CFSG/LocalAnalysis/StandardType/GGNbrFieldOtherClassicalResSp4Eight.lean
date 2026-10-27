module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResSp4EightAlt
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Sp4
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.Open (StatedProj StatedSp)
open CFSG.ComponentClassification.PresentationLocal (omegaPerm omegaPerm_injective
  omegaPerm_surjective centralizer_alternatingGroup_eq_bot)
open Equiv Equiv.Perm

namespace ResSp4Eight

theorem exists_fixDerEquiv_Sp4Eight {R : Type} [Group R] (x : MulAut R)
    (Ψ : ggFixSub x ≃* Perm (Fin 6)) :
    ∃ θ : ggFixDer x ≃* alternatingGroup (Fin 6), ∀ (g : R) (hg : g ∈ ggFixDer x),
      ((θ ⟨g, hg⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        Ψ ⟨g, ggFixDer_le_ggFixSub x hg⟩ := by
  have h1 : (commutator (ggFixSub x)).map (ggFixSub x).subtype = ggFixDer x :=
    Subgroup.map_subtype_commutator (ggFixSub x)
  have h2 : (commutator (ggFixSub x)).map Ψ.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [← alternatingGroup.commutator_perm_eq (by simp), commutator_def, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 Ψ.surjective]
  have hmem : ∀ (g : R) (hg : g ∈ ggFixDer x),
      Ψ ⟨g, ggFixDer_le_ggFixSub x hg⟩ ∈ alternatingGroup (Fin 6) := by
    intro g hg
    have hg' : g ∈ (commutator (ggFixSub x)).map (ggFixSub x).subtype := by rw [h1]; exact hg
    obtain ⟨h, hh, hhg⟩ := hg'
    have e : (⟨g, ggFixDer_le_ggFixSub x hg⟩ : ggFixSub x) = h := Subtype.ext hhg.symm
    rw [e, ← h2]
    exact ⟨h, hh, rfl⟩
  let θf : ggFixDer x →* alternatingGroup (Fin 6) :=
    { toFun := fun g => ⟨Ψ ⟨g, ggFixDer_le_ggFixSub x g.2⟩, hmem g g.2⟩
      map_one' := Subtype.ext (map_one Ψ)
      map_mul' := fun a b => Subtype.ext (map_mul Ψ ⟨a, ggFixDer_le_ggFixSub x a.2⟩
        ⟨b, ggFixDer_le_ggFixSub x b.2⟩) }
  have hbij : Function.Bijective θf := by
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · have h := Ψ.injective (congrArg Subtype.val hab)
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    · have hc : (c : Perm (Fin 6)) ∈ (commutator (ggFixSub x)).map Ψ.toMonoidHom := by
        rw [h2]
        exact c.2
      obtain ⟨h, hh, hhc⟩ := hc
      have hhR : (h : R) ∈ ggFixDer x := by
        rw [← h1]
        exact ⟨h, hh, rfl⟩
      exact ⟨⟨h, hhR⟩, Subtype.ext hhc⟩
  exact ⟨MulEquiv.ofBijective θf hbij, fun g hg => rfl⟩

theorem two_dvd_card_alt_Sp4Eight : 2 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  have hmem : swap (0 : Fin 6) 1 * swap 2 3 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hx2 : (⟨swap 0 1 * swap 2 3, hmem⟩ : alternatingGroup (Fin 6)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show (swap (0 : Fin 6) 1 * swap 2 3) ^ 2 = 1
    decide
  have hx1 : (⟨swap 0 1 * swap 2 3, hmem⟩ : alternatingGroup (Fin 6)) ≠ 1 := by
    intro h
    have h' : swap (0 : Fin 6) 1 * swap 2 3 = 1 := congrArg Subtype.val h
    exact absurd h' (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← orderOf_eq_prime hx2 hx1]
  exact orderOf_dvd_natCard _

theorem exists_ne_comm_alt_Sp4Eight :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative (alternatingGroup (Fin 6)) := isMulCommutative_iff.mpr hcon
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.mp this
  simp at h3

variable {K : Type} [Field K] [Finite K]

theorem fixDataKX_Sp4Eight (hK : Nat.card K = 2 ^ 3)
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K 2)))
    (hna : ∃ a b : LargeEvenProj (LargeEvenSpGroup K 2), a * b ≠ b * a)
    {f : MulAut (LargeEvenProj (LargeEvenSpGroup K 2))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K 2)))
    (hord : orderOf f = 3) :
    GGFixDataKX 3 (fun k => ¬ 3 ∣ k)
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 2)) (LargeEvenGSpSet K 2)) f := by
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hσ : orderOf σ = 3 := by
    rw [← orderOf_injective (fieldAut 2 K) FieldFixSp.fieldAut_injective σ]
    exact hord
  have hσp : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two (by norm_num) hK hσ
  have hk : Nat.card (descentField σ) = 2 := by
    rw [hcard]
    norm_num
  haveI := hS
  have hι : Function.Injective (subfieldInj (r := 2) σ) := subfieldInj_injective σ
  have hrange : (subfieldInj (r := 2) σ).range = ggFixSub (fieldAut 2 K σ) := by
    rw [range_subfieldInj, ← spFixedGroup_fieldAut_eq_range (by decide : Odd 3) hσp]
    exact Subgroup.ext fun x => Iff.rfl
  let Φ : StatedProj (StatedSp 2 (descentField σ)) ≃* Perm (Fin 6) :=
    (statedProjEquivSympFour hk).trans
      (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩)
  let Ψ : ggFixSub (fieldAut 2 K σ) ≃* Perm (Fin 6) :=
    (MulEquiv.subgroupCongr hrange.symm).trans ((MonoidHom.ofInjective hι).symm.trans Φ)
  obtain ⟨θ₀, hθ₀⟩ := exists_fixDerEquiv_Sp4Eight (fieldAut 2 K σ) Ψ
  have key : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 2))
      (LargeEvenGSpSet K 2), φ * fieldAut 2 K σ = fieldAut 2 K σ * φ →
        ∃ y ∈ ggFixSub (fieldAut 2 K σ), φ = MulAut.conj y := by
    intro φ hφI hφ
    obtain ⟨y, rfl⟩ := RecipeFieldSp.mem_conjImage_iff_inn.mp hφI
    refine ⟨y, ?_, rfl⟩
    have hc : ∀ u : StatedProj (StatedSp 2 K),
        u * (y⁻¹ * fieldAut 2 K σ y) = (y⁻¹ * fieldAut 2 K σ y) * u := by
      intro u
      obtain ⟨z, rfl⟩ := MulEquiv.surjective (fieldAut 2 K σ) u
      have e := congrArg (fun α : MulAut (StatedProj (StatedSp 2 K)) => α z) hφ
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at e
      calc fieldAut 2 K σ z * (y⁻¹ * fieldAut 2 K σ y)
          = y⁻¹ * (y * fieldAut 2 K σ z * y⁻¹) * fieldAut 2 K σ y := by group
        _ = y⁻¹ * (fieldAut 2 K σ y * fieldAut 2 K σ z * (fieldAut 2 K σ y)⁻¹) *
              fieldAut 2 K σ y := by rw [e]
        _ = (y⁻¹ * fieldAut 2 K σ y) * fieldAut 2 K σ z := by group
    have h1 : y⁻¹ * fieldAut 2 K σ y = 1 := FieldFixSp.eq_one_of_forall_comm hna hc
    have hy : fieldAut 2 K σ y = y := by
      have := congrArg (y * ·) h1
      simpa using this
    exact mem_ggFixSub.mpr hy
  refine ⟨alternatingGroup (Fin 6), inferInstance,
    Set.range (MulAut.conjNormal : Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))), ∅, θ₀,
    alternatingGroup.isSimpleGroup (by simp), exists_ne_comm_alt_Sp4Eight, ⟨?_, ?_⟩,
    TypeA.ggTorusLift_zero two_dvd_card_alt_Sp4Eight, ggTorusNoLineTwoKX_alt_Sp4Eight,
    fun _ _ _ φ₀ hφ₀ => absurd hφ₀ (Set.notMem_empty φ₀)⟩
  ·
    intro φ hφI hφ
    obtain ⟨y, hy, rfl⟩ := key φ hφI hφ
    refine ⟨MulAut.conjNormal (Ψ ⟨y, hy⟩), ⟨_, rfl⟩, fun g hg => Subtype.ext ?_⟩
    rw [MulAut.conjNormal_apply, hθ₀, hθ₀]
    have e : (⟨MulAut.conj y g, ggFixDer_le_ggFixSub _ (ggFixDer_map_mem hφ hg)⟩ :
        ggFixSub (fieldAut 2 K σ)) = ⟨y, hy⟩ * ⟨g, ggFixDer_le_ggFixSub _ hg⟩ * ⟨y, hy⟩⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]
  ·
    intro φ hφI hφ hfix
    obtain ⟨y, hy, rfl⟩ := key φ hφI hφ
    have hc : Ψ ⟨y, hy⟩ ∈
        Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Perm (Fin 6))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨⟨g, hg⟩, hga⟩ := θ₀.surjective ⟨a, ha⟩
      have ha' : a = Ψ ⟨g, ggFixDer_le_ggFixSub _ hg⟩ := by
        rw [← hθ₀ g hg, hga]
      have hyg : y * g * y⁻¹ = g := hfix g hg
      rw [ha', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show g * y = y * g
      calc g * y = (y * g * y⁻¹) * y := by rw [hyg]
        _ = y * g := by group
    rw [centralizer_alternatingGroup_eq_bot (by simp), Subgroup.mem_bot] at hc
    have hy1 : (⟨y, hy⟩ : ggFixSub (fieldAut 2 K σ)) = 1 := Ψ.injective (by rw [hc, map_one])
    rw [show y = 1 from congrArg Subtype.val hy1, map_one]

theorem ggCenterKp_of_centerPrime_Sp4Eight {p : ℕ} {R : Type} [Group R]
    (h : GGCenterPrime p R) : GGCenterKp (fun k => ¬ p ∣ k) R :=
  fun L' _ _ ψ hψ hker hperf hdvd =>
    h L' ψ hψ hker hperf (hdvd.trans (Subgroup.card_dvd_of_le hker))

end ResSp4Eight

open ResSp4Eight

theorem largeEvenLabelAll_rowKX_sp4Eight
    {lab : LargeEvenLabel}
    (h : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ lab.n = 3) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift 3 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp 3 0 R I ∧ GGCenterKp (fun k => ¬ 3 ∣ k) R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hBC, hl, hn⟩ := h
  dsimp only at hBC hl hn
  subst hl hn
  have hlab : LargeEvenInLambda2 ⟨t, 2, 3⟩ := by
    refine ⟨by norm_num, ?_⟩
    rcases hBC with rfl | rfl <;> exact ⟨le_rfl, fun _ => by norm_num⟩
  have hrow := largeEvenLabelAll_rowPlainTwo_sp4 Nat.prime_three (by norm_num) hlab
    ⟨hBC, rfl, Or.inl (by norm_num)⟩
  have hcen : LargeEvenLabelAll ⟨t, 2, 3⟩ fun R _ _ _ => GGCenterKp (fun k => ¬ 3 ∣ k) R := by
    intro Q hQ
    rcases hBC with rfl | rfl <;>
    · dsimp only [LargeEvenRawDatum] at hQ ⊢
      refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
      haveI : CharP K 2 := charP_two_of_card hK
      exact ggCenterKp_of_centerPrime_Sp4Eight (ggCenterPrime_sp Nat.prime_three (by norm_num))
  exact (largeEvenLabelAll_and hrow hcen).mono fun _ _ _ _ ⟨⟨hi, hl, hn⟩, hc⟩ =>
    ⟨hi, hl, fun hs hna => ⟨ggTorusNoLineComp_of_ggTorusNoLine
      (ggTorusNoLine_of_two Nat.prime_three (hn hs hna)), hc⟩⟩

theorem largeEvenLabelAll_fixKX_sp4Eight {lab : LargeEvenLabel}
    (h : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ lab.n = 3) :
    LargeEvenLabelAll lab (GGRawFieldFixKX 3 (fun k => ¬ 3 ∣ k)) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hBC, hl, hn⟩ := h
  dsimp only at hBC hl hn
  subst hl hn
  intro Q hQ
  rcases hBC with rfl | rfl <;>
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    intro hS hna f hf hord
    exact fixDataKX_Sp4Eight hK hS hna hf hord

end CFSG.StandardType

end
