module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Diag
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Conj
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Weyl
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated
import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoNum
import CFSG.LocalAnalysis.StandardType.StarFour.PsiInjective

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.StandardType.GGHalf
open scoped Pointwise

private theorem e6TwoT31_natCard : Nat.card (FiniteField.Extension F2 2 5) = 32 := by
  rw [FiniteField.natCard_extension]
  rw [show Nat.card F2 = 2 from by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num]
  norm_num

private theorem e6TwoT31_frob_eq_self_iff (x : FiniteField.Extension F2 2 5) :
    (FiniteField.Extension.frob F2 2 5) x = x ↔
      x ∈ Set.range (algebraMap F2 (FiniteField.Extension F2 2 5)) := by
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    intro g
    obtain ⟨i, -, rfl⟩ := FiniteField.Extension.exists_frob_pow_eq F2 2 5 g
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  · rintro ⟨a, rfl⟩
    exact (FiniteField.Extension.frob F2 2 5).commutes a

private theorem e6TwoT31_a5LeviRoots_eq_perpRoots :
    E6Pilot.a5LeviRoots = EPilot.perpRoots .E6 := by
  ext γ
  rw [E6Pilot.mem_a5LeviRoots, EPilot.mem_perpRoots_iff_iform (Or.inl rfl),
    EPilot.iform_highRoot (Or.inl rfl)]

private theorem e6TwoT31_rootSpan_pair
    {τ : Tag} {K : Type} [Field K]
    (a b : Fin τ.rank → ℤ) :
    rootSpan τ K ({a, b} : Set (Fin τ.rank → ℤ)) =
      rootSubgroup τ K a ⊔ rootSubgroup τ K b := by
  apply le_antisymm
  · refine iSup₂_le fun α hα => ?_
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl <;> simp
  · refine sup_le ?_ ?_
    · exact le_iSup₂ (f := fun α (_ : α ∈ ({a, b} : Set (Fin τ.rank → ℤ))) => rootSubgroup τ K α)
        a (by simp)
    · exact le_iSup₂ (f := fun α (_ : α ∈ ({a, b} : Set (Fin τ.rank → ℤ))) => rootSubgroup τ K α)
        b (by simp)

private theorem e6TwoT31_map_conj_eq_self {G : Type*} [Group G] {H : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (H : Set G)) :
    H.map (MulAut.conj c).toMonoidHom = H := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change c * y * c⁻¹ ∈ H
    have h := Subgroup.mem_centralizer_iff.1 hc y hy
    rw [← h, mul_inv_cancel_right]
    exact hy
  · intro x hx
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · change c⁻¹ * x * c ∈ H
      have h := Subgroup.mem_centralizer_iff.1 (inv_mem hc) x hx
      have e : c⁻¹ * x * c = x := by rw [← h]; group
      rw [e]
      exact hx
    · change c * (c⁻¹ * x * c) * c⁻¹ = x
      group

private theorem e6TwoT31_map_zpowers {G H : Type*} [Group G] [Group H] (f : G →* H) (x : G) :
    (Subgroup.zpowers x).map f = Subgroup.zpowers (f x) := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (f x)) k
  · rw [Subgroup.zpowers_le]
    exact ⟨x, Subgroup.mem_zpowers x, rfl⟩

private theorem e6TwoT31_card_sup {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hdisj : Disjoint H K) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
      have h : (h₁ : G) * (k₁ : G) = (h₂ : G) * (k₂ : G) := congrArg Subtype.val heq
      have hH : (h₂ : G)⁻¹ * (h₁ : G) ∈ H := mul_mem (inv_mem h₂.2) h₁.2
      have hK : (h₂ : G)⁻¹ * (h₁ : G) ∈ K := by
        have e : (h₂ : G)⁻¹ * (h₁ : G) = (k₂ : G) * (k₁ : G)⁻¹ := by
          calc (h₂ : G)⁻¹ * (h₁ : G) =
                (h₂ : G)⁻¹ * ((h₁ : G) * (k₁ : G)) * (k₁ : G)⁻¹ := by group
            _ = (h₂ : G)⁻¹ * ((h₂ : G) * (k₂ : G)) * (k₁ : G)⁻¹ := by rw [h]
            _ = (k₂ : G) * (k₁ : G)⁻¹ := by group
        rw [e]
        exact mul_mem k₂.2 (inv_mem k₁.2)
      have hmem : (h₂ : G)⁻¹ * (h₁ : G) = 1 := (Subgroup.disjoint_def.1 hdisj) hH hK
      have hh : h₁ = h₂ := by
        apply Subtype.ext
        calc (h₁ : G) = (h₂ : G) * ((h₂ : G)⁻¹ * (h₁ : G)) := by group
          _ = (h₂ : G) := by rw [hmem, mul_one]
      subst hh
      have hk : k₁ = k₂ := Subtype.ext (mul_left_cancel h)
      subst hk
      rfl
    · intro x
      have hx : (x : G) ∈ ((H : Set G) * (K : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hHK]
        exact x.2
      obtain ⟨h, hh, k, hk, hk_eq⟩ := Set.mem_mul.1 hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hk_eq⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

private theorem e6TwoT31_not_thirtyOne_sq_dvd_ordA : ¬ 31 ^ 2 ∣ CFSG.Open.ordA 5 2 := by
  decide +kernel

private theorem e6TwoT31_a5LeviBaseChange_fixed
    {d' : E6Pilot.a5Levi (FiniteField.Extension F2 2 5)}
    (hσd' : E6Pilot.a5LeviBaseChange
        (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom d' = d') :
    ∃ d₀ : E6Pilot.a5Levi F2,
      E6Pilot.a5LeviBaseChange (algebraMap F2 (FiniteField.Extension F2 2 5)) d₀ = d' := by
  haveI : CharP (FiniteField.Extension F2 2 5) 2 :=
    charP_of_injective_algebraMap
      (algebraMap F2 (FiniteField.Extension F2 2 5)).injective 2
  obtain ⟨A, hA⟩ := E6Pilot.slToA5Levi_surjective d'
  rw [← hA] at hσd'
  rw [E6Pilot.a5LeviBaseChange_slToA5Levi] at hσd'
  have hZker : A⁻¹ * Matrix.SpecialLinearGroup.map
        (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom A ∈
      (E6Pilot.slToA5Levi (K := FiniteField.Extension F2 2 5)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσd', inv_mul_cancel]
  have hZc : A⁻¹ * Matrix.SpecialLinearGroup.map
        (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom A ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) (FiniteField.Extension F2 2 5)) := by
    rwa [E6Pilot.ker_slToA5Levi] at hZker
  have hcenter : Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 6) (FiniteField.Extension F2 2 5)) = ⊥ :=
    StarFour.center_specialLinearGroup_eq_bot_of_coprime (by rw [e6TwoT31_natCard]; norm_num)
  rw [hcenter, Subgroup.mem_bot] at hZc
  have hAfix : Matrix.SpecialLinearGroup.map
      (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom A = A := by
    calc Matrix.SpecialLinearGroup.map
          (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom A =
        A * (A⁻¹ * Matrix.SpecialLinearGroup.map
          (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom A) := by group
      _ = A * 1 := by rw [hZc]
      _ = A := by rw [mul_one]
  obtain ⟨B₀, hB₀⟩ := E6Pilot.exists_specialLinearGroup_map_eq_of_map_eq
    (algebraMap F2 (FiniteField.Extension F2 2 5))
    (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom
    (fun z => e6TwoT31_frob_eq_self_iff z) A hAfix
  exact ⟨E6Pilot.slToA5Levi B₀, by rw [E6Pilot.a5LeviBaseChange_slToA5Levi, hB₀, hA]⟩

private theorem e6TwoT31_descent_a5Levi
    {d : ModGL .E6 (FiniteField.Extension F2 2 5)}
    (hd : d ∈ rootSpan .E6 (FiniteField.Extension F2 2 5) E6Pilot.a5LeviRoots)
    (hσd : baseChangeGL (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom d = d) :
    ∃ d₀ ∈ rootSpan .E6 F2 E6Pilot.a5LeviRoots,
      baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5)) d₀ = d := by
  have hdC : d ∈ adjointGroup .E6 (FiniteField.Extension F2 2 5) :=
    E6Pilot.rootSpan_le_adjointGroup_E6 _ hd
  set d' : E6Pilot.a5Levi (FiniteField.Extension F2 2 5) :=
    ⟨⟨d, hdC⟩, E6Pilot.mem_a5Levi_iff.2 hd⟩ with hd'def
  have hσd' : E6Pilot.a5LeviBaseChange
      (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom d' = d' := by
    apply Subtype.ext
    apply Subtype.ext
    rw [E6Pilot.coe_a5LeviBaseChange, hd'def]
    exact hσd
  obtain ⟨d₀, hd₀⟩ := e6TwoT31_a5LeviBaseChange_fixed hσd'
  refine ⟨(((d₀ : E6Pilot.a5Levi F2) : adjointGroup .E6 F2) : ModGL .E6 F2), ?_, ?_⟩
  · exact E6Pilot.mem_a5Levi_iff.1 d₀.2
  · rw [← E6Pilot.coe_a5LeviBaseChange, hd₀, hd'def]

theorem centralizer_e6TwoT31 :
    Subgroup.centralizer ({e6TwoT31} : Set EC) = Subgroup.zpowers e6TwoT31 ⊔ sTheta := by
  haveI : CharP (FiniteField.Extension F2 2 5) 2 :=
    charP_of_injective_algebraMap
      (algebraMap F2 (FiniteField.Extension F2 2 5)).injective 2
  have ht₀ : (e6TwoT31 : ModGL .E6 F2) ∈ rootSpan .E6 F2 (EPilot.perpRoots .E6) := by
    have h : (e6TwoT31 : ModGL .E6 F2) ∈ rootSpan .E6 F2 E6Pilot.a5LeviRoots :=
      E6Pilot.mem_a5Levi_iff.1 e6TwoT31_mem_lE
    rwa [e6TwoT31_a5LeviRoots_eq_perpRoots] at h
  refine le_antisymm ?_ ?_
  · intro g hg
    have hgx : g * e6TwoT31 = e6TwoT31 * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hgx_mod : (g : ModGL .E6 F2) * ((e6TwoT31 : EC) : ModGL .E6 F2) =
        ((e6TwoT31 : EC) : ModGL .E6 F2) * (g : ModGL .E6 F2) := by
      simpa only [Subgroup.coe_mul] using congrArg Subtype.val hgx
    obtain ⟨ζ, hζ, n, hn, hconj⟩ := exists_conj_baseChangeGL_e6TwoT31
    have hn' : n ∈ rootSpan .E6 (FiniteField.Extension F2 2 5) (EPilot.perpRoots .E6) := by
      rwa [e6TwoT31_a5LeviRoots_eq_perpRoots] at hn
    set m : ModGL .E6 (FiniteField.Extension F2 2 5) :=
      n⁻¹ * baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
        (g : ModGL .E6 F2) * n with hmdef
    have hm : m ∈ toralCentralizer .E6 (FiniteField.Extension F2 2 5) (e6TwoT31Char ζ) := by
      rw [hmdef, mem_toralCentralizer]
      refine ⟨?_, ?_⟩
      · exact mul_mem (mul_mem (inv_mem (E6Pilot.rootSpan_le_adjointGroup_E6 _ hn))
          (baseChangeGL_mem_adjointGroup (algebraMap F2 (FiniteField.Extension F2 2 5)) g.2))
          (E6Pilot.rootSpan_le_adjointGroup_E6 _ hn)
      · have hgx₂ : baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
              (g : ModGL .E6 F2) *
            baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
              ((e6TwoT31 : EC) : ModGL .E6 F2) =
            baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
              ((e6TwoT31 : EC) : ModGL .E6 F2) *
            baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5)) (g : ModGL .E6 F2) := by
          rw [← map_mul, hgx_mod, map_mul]
        rw [← hconj]
        calc (n⁻¹ * baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
                ((e6TwoT31 : EC) : ModGL .E6 F2) * n) *
              (n⁻¹ * baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
                (g : ModGL .E6 F2) * n) *
              (n⁻¹ * baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
                ((e6TwoT31 : EC) : ModGL .E6 F2) * n)⁻¹ =
            n⁻¹ * (baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
                ((e6TwoT31 : EC) : ModGL .E6 F2) *
              baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
                (g : ModGL .E6 F2)) *
              (baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
                ((e6TwoT31 : EC) : ModGL .E6 F2))⁻¹ * n := by group
          _ = n⁻¹ * baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
                (g : ModGL .E6 F2) * n := by rw [← hgx₂]; group
    have htc : toralCentralizer .E6 (FiniteField.Extension F2 2 5) (e6TwoT31Char ζ) =
        toralRootGroup .E6 (FiniteField.Extension F2 2 5) (e6TwoT31Char ζ) :=
      CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_of_stabilizer_le
        .E6 (FiniteField.Extension F2 2 5) (e6TwoT31Char ζ)
        (rootCharStabilizerSubgroup_e6TwoT31Char_le hζ)
    have hm' : m ∈ EPilot.highRootSL2 .E6 (FiniteField.Extension F2 2 5) ⊔
        rootSpan .E6 (FiniteField.Extension F2 2 5) (EPilot.perpRoots .E6) := by
      have h1 : m ∈ toralRootGroup .E6 (FiniteField.Extension F2 2 5) (e6TwoT31Char ζ) := by
        rwa [← htc]
      rw [toralRootGroup, rootCharKernel_e6TwoT31Char hζ, e6TwoT31_rootSpan_pair] at h1
      have hT : torusGroup .E6 (FiniteField.Extension F2 2 5) ≤
          EPilot.highRootSL2 .E6 (FiniteField.Extension F2 2 5) ⊔
            rootSpan .E6 (FiniteField.Extension F2 2 5) (EPilot.perpRoots .E6) := by
        have hsq := F4Pilot.exists_sq_eq_of_ringChar_eq_two
          (K := FiniteField.Extension F2 2 5) (ringChar.eq _ 2)
        refine (EPilot.torusGroup_le_highTorusLine_sup (τ := .E6) (Or.inl rfl) hsq).trans ?_
        exact sup_le ((EPilot.highTorusLine_le_highRootSL2 (τ := .E6) (Or.inl rfl)).trans
          le_sup_left) le_sup_right
      exact (sup_le hT le_sup_left) h1
    have hJ : EPilot.highRootSL2 .E6 (FiniteField.Extension F2 2 5) ≤
        Subgroup.normalizer (rootSpan .E6 (FiniteField.Extension F2 2 5)
          (EPilot.perpRoots .E6) : Set (ModGL .E6 (FiniteField.Extension F2 2 5))) :=
      (Subgroup.le_centralizer_iff.2
        (EPilot.rootSpan_perpRoots_le_centralizer_highRootSL2 (τ := .E6) (Or.inl rfl))).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hJ] at hm'
    obtain ⟨j', hj'J, d', hd'D, hj'd'm⟩ := Set.mem_mul.1 hm'
    have hn_comm_j : n * j' * n⁻¹ = j' := by
      have hc := E6Pilot.commute_of_mem_highRootSL2_of_mem_perpLevi (τ := .E6) (Or.inl rfl)
        hj'J hn'
      rw [← hc, mul_inv_cancel_right]
    set d : ModGL .E6 (FiniteField.Extension F2 2 5) := n * d' * n⁻¹ with hddef
    have hdD : d ∈ rootSpan .E6 (FiniteField.Extension F2 2 5) (EPilot.perpRoots .E6) :=
      mul_mem (mul_mem hn' hd'D) (inv_mem hn')
    have hg₂ : baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
        (g : ModGL .E6 F2) = j' * d := by
      rw [hmdef] at hj'd'm
      calc baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5)) (g : ModGL .E6 F2) =
            n * (n⁻¹ * baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
              (g : ModGL .E6 F2) * n) * n⁻¹ := by group
        _ = n * (j' * d') * n⁻¹ := by rw [hj'd'm]
        _ = (n * j' * n⁻¹) * (n * d' * n⁻¹) := by group
        _ = j' * d := by rw [hn_comm_j, hddef]
    have hσι : ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom).comp
        (algebraMap F2 (FiniteField.Extension F2 2 5)) =
        algebraMap F2 (FiniteField.Extension F2 2 5) :=
      RingHom.ext fun a => (FiniteField.Extension.frob F2 2 5).commutes a
    have hσg : baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom)
        (baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
          (g : ModGL .E6 F2)) =
        baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5)) (g : ModGL .E6 F2) := by
      rw [F4Pilot.baseChangeGL_baseChangeGL, hσι]
    have hσj : baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j' ∈
        EPilot.highRootSL2 .E6 (FiniteField.Extension F2 2 5) := by
      rw [← E6Pilot.range_rootSL2_highRoot] at hj'J
      obtain ⟨B, hB⟩ := hj'J
      rw [← hB, E6Pilot.baseChangeGL_rootSL2_highRoot]
      exact E6Pilot.rootSL2_highRoot_mem_highRootSL2 _
    have hσd : baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) d ∈
        rootSpan .E6 (FiniteField.Extension F2 2 5) (EPilot.perpRoots .E6) :=
      F4Pilot.map_rootSpan_baseChangeGL_le _ _ ⟨d, hdD, rfl⟩
    have hjd : baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j' = j' ∧
        baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) d = d := by
      have h1 : (baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j')⁻¹ *
            j' = baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) d * d⁻¹ := by
        have h2 : baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j' *
              baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) d =
              j' * d := by
          rw [← map_mul, ← hg₂, hσg]
        calc (baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j')⁻¹ *
              j' =
            (baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j')⁻¹ *
              (j' * d) * d⁻¹ := by group
          _ = (baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j')⁻¹ *
              (baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j' *
                baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) d) *
              d⁻¹ := by rw [h2]
          _ = baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) d *
              d⁻¹ := by group
      have hJmem : (baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j')⁻¹ *
          j' ∈ EPilot.highRootSL2 .E6 (FiniteField.Extension F2 2 5) :=
        mul_mem (inv_mem hσj) hj'J
      have hDmem : (baseChangeGL ((FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom) j')⁻¹ *
          j' ∈ rootSpan .E6 (FiniteField.Extension F2 2 5) (EPilot.perpRoots .E6) := by
        rw [h1]
        exact mul_mem hσd (inv_mem hdD)
      have h0 := (Subgroup.disjoint_def.1
        (E6Pilot.disjoint_highRootSL2_perpLevi (τ := .E6) (Or.inl rfl))) hJmem hDmem
      rw [h0] at h1
      exact ⟨inv_mul_eq_one.1 h0, mul_inv_eq_one.1 h1.symm⟩
    obtain ⟨d₀, hd₀D, hd₀⟩ := e6TwoT31_descent_a5Levi hdD hjd.2
    obtain ⟨y, hyJ, hy⟩ := E6Pilot.exists_baseChangeGL_eq_of_mem_highRootSL2
      (algebraMap F2 (FiniteField.Extension F2 2 5))
      (FiniteField.Extension.frob F2 2 5).toRingEquiv.toRingHom
      (fun z => e6TwoT31_frob_eq_self_iff z) hj'J hjd.1
    have hgyd : (g : ModGL .E6 F2) = y * d₀ :=
      baseChangeGL_injective (algebraMap F2 (FiniteField.Extension F2 2 5))
        (by rw [map_mul, hy, hd₀, hg₂])
    set yE : EC := ⟨y, EPilot.highRootSL2_le_adjointGroup hyJ⟩ with hyEdef
    set d₀E : EC := ⟨d₀, E6Pilot.rootSpan_le_adjointGroup_E6 _ hd₀D⟩ with hd₀Edef
    have hg_eq : g = yE * d₀E := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, hyEdef, hd₀Edef] using hgyd
    have hyE_sTheta : yE ∈ sTheta := Subgroup.mem_subgroupOf.2 hyJ
    have hd₀E_lE : d₀E ∈ lE := E6Pilot.mem_a5Levi_iff.2 hd₀D
    have hy_comm_mod : y * (e6TwoT31 : ModGL .E6 F2) =
        (e6TwoT31 : ModGL .E6 F2) * y :=
      E6Pilot.commute_of_mem_highRootSL2_of_mem_perpLevi (τ := .E6) (Or.inl rfl) hyJ ht₀
    have hy_comm : yE * e6TwoT31 = e6TwoT31 * yE := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, hyEdef] using hy_comm_mod
    have hd₀_comm : d₀E ∈ Subgroup.centralizer ({e6TwoT31} : Set EC) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hd₀_eq : d₀E = yE⁻¹ * g := by rw [hg_eq]; group
      rw [hd₀_eq]
      have hinv : yE⁻¹ * e6TwoT31 = e6TwoT31 * yE⁻¹ := by
        calc yE⁻¹ * e6TwoT31 = yE⁻¹ * (e6TwoT31 * yE) * yE⁻¹ := by group
          _ = yE⁻¹ * (yE * e6TwoT31) * yE⁻¹ := by rw [← hy_comm]
          _ = e6TwoT31 * yE⁻¹ := by group
      calc (yE⁻¹ * g) * e6TwoT31 = yE⁻¹ * (g * e6TwoT31) := by group
        _ = yE⁻¹ * (e6TwoT31 * g) := by rw [hgx]
        _ = (yE⁻¹ * e6TwoT31) * g := by group
        _ = (e6TwoT31 * yE⁻¹) * g := by rw [hinv]
        _ = e6TwoT31 * (yE⁻¹ * g) := by group
    have hd₀E_zpow : d₀E ∈ Subgroup.zpowers e6TwoT31 := by
      have hmem : d₀E ∈ lE ⊓ Subgroup.centralizer ({e6TwoT31} : Set EC) :=
        Subgroup.mem_inf.2 ⟨hd₀E_lE, hd₀_comm⟩
      rwa [lE_inf_centralizer_e6TwoT31] at hmem
    rw [hg_eq]
    exact mul_mem (Subgroup.mem_sup_right hyE_sTheta) (Subgroup.mem_sup_left hd₀E_zpow)
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hxJ : (x : ModGL .E6 F2) ∈ EPilot.highRootSL2 .E6 F2 := Subgroup.mem_subgroupOf.1 hx
      simpa only [Subgroup.coe_mul] using
        E6Pilot.commute_of_mem_highRootSL2_of_mem_perpLevi (τ := .E6) (Or.inl rfl) hxJ ht₀

theorem e6TwoCentT31_holds :
    E6TwoCentT31 := by
  intro t ht_lE ht_order
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  haveI hFin : Finite EC := finite_EC
  have hlE_cent : lE ≤ Subgroup.centralizer (sTheta : Set EC) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    apply Subtype.ext
    have hx' : (x : ModGL .E6 F2) ∈ rootSpan .E6 F2 (EPilot.perpRoots .E6) := by
      have h := E6Pilot.mem_a5Levi_iff.1 hx
      rwa [e6TwoT31_a5LeviRoots_eq_perpRoots] at h
    have hy' : (y : ModGL .E6 F2) ∈ EPilot.highRootSL2 .E6 F2 := Subgroup.mem_subgroupOf.1 hy
    simpa only [Subgroup.coe_mul] using
      E6Pilot.commute_of_mem_highRootSL2_of_mem_perpLevi (τ := .E6) (Or.inl rfl) hy' hx'
  have hPall : ∀ P : Sylow 31 ↥lE, Nat.card ↥P = 31 := by
    intro P
    have hG : Nat.card ↥lE = 31 * (Nat.card ↥lE / 31) :=
      (Nat.mul_div_cancel' (by rw [card_lE]; exact thirtyOne_dvd_ordA)).symm
    have hm : ¬ 31 ∣ Nat.card ↥lE / 31 := by
      intro hd
      obtain ⟨k, hk⟩ := hd
      apply e6TwoT31_not_thirtyOne_sq_dvd_ordA
      refine ⟨k, ?_⟩
      rw [← card_lE, hG, hk, pow_two]
      ring
    exact CFSG.GroupTheory.GL52.card_sylow_of_card_eq_prime_mul hG hm P
  have hP0card : Nat.card ↥(Subgroup.zpowers (⟨e6TwoT31, e6TwoT31_mem_lE⟩ : ↥lE)) = 31 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨e6TwoT31, e6TwoT31_mem_lE⟩ : ↥lE),
      orderOf_e6TwoT31]
  have hP1card : Nat.card ↥(Subgroup.zpowers (⟨t, ht_lE⟩ : ↥lE)) = 31 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨t, ht_lE⟩ : ↥lE), ht_order]
  obtain ⟨P0, hP0⟩ := CFSG.GroupTheory.GL52.exists_sylow_eq_of_card hP0card hPall
  obtain ⟨P1, hP1⟩ := CFSG.GroupTheory.GL52.exists_sylow_eq_of_card hP1card hPall
  obtain ⟨c, hc⟩ := CFSG.GroupTheory.GL52.exists_eq_map_conj_sylow P0 P1
  have hx0_mem : (⟨e6TwoT31, e6TwoT31_mem_lE⟩ : ↥lE) ∈ (P0 : Subgroup ↥lE) := by
    rw [hP0]
    exact Subgroup.mem_zpowers _
  have hc_x0 : c * (⟨e6TwoT31, e6TwoT31_mem_lE⟩ : ↥lE) * c⁻¹ ∈ (P1 : Subgroup ↥lE) := by
    rw [hc]
    refine Subgroup.mem_map.2 ⟨_, hx0_mem, ?_⟩
    rfl
  rw [hP1] at hc_x0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc_x0
  have hconjEC : (c : EC) * e6TwoT31 * (c : EC)⁻¹ = t ^ k := by
    have h := congrArg (fun z : ↥lE => (z : EC)) hk
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, Subtype.coe_mk] using h.symm
  have horder_u : orderOf ((c : EC) * e6TwoT31 * (c : EC)⁻¹) = orderOf e6TwoT31 := by
    simpa only [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj (c : EC)) e6TwoT31)
  have hzu : Subgroup.zpowers ((c : EC) * e6TwoT31 * (c : EC)⁻¹) = Subgroup.zpowers t := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      rw [hconjEC]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
    · rw [Nat.card_zpowers, Nat.card_zpowers, ht_order, horder_u, orderOf_e6TwoT31]
  have hcz : Subgroup.centralizer ({(c : EC) * e6TwoT31 * (c : EC)⁻¹} : Set EC) =
      Subgroup.centralizer ({t} : Set EC) := by
    have e1 : Subgroup.centralizer
        (Subgroup.zpowers ((c : EC) * e6TwoT31 * (c : EC)⁻¹) : Set EC) =
        Subgroup.centralizer ({(c : EC) * e6TwoT31 * (c : EC)⁻¹} : Set EC) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have e2 : Subgroup.centralizer (Subgroup.zpowers t : Set EC) =
        Subgroup.centralizer ({t} : Set EC) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← e1, ← e2, hzu]
  have hc_cent : (c : EC) ∈ Subgroup.centralizer (sTheta : Set EC) := hlE_cent c.2
  have hmap_sTheta : sTheta.map (MulAut.conj (c : EC)).toMonoidHom = sTheta :=
    e6TwoT31_map_conj_eq_self hc_cent
  have hmap_zp : (Subgroup.zpowers e6TwoT31).map (MulAut.conj (c : EC)).toMonoidHom =
      Subgroup.zpowers ((c : EC) * e6TwoT31 * (c : EC)⁻¹) := by
    rw [e6TwoT31_map_zpowers]
    rfl
  have hCeq : Subgroup.centralizer ({t} : Set EC) = Subgroup.zpowers t ⊔ sTheta := by
    rw [← hcz, CFSG.GroupTheory.GL52.centralizer_conj (c : EC) e6TwoT31,
      centralizer_e6TwoT31, Subgroup.map_sup, hmap_zp, hmap_sTheta, hzu]
  have hcard_t : Nat.card (Subgroup.zpowers t) = 31 := by
    rw [Nat.card_zpowers, ht_order]
  have hdisj : Disjoint (Subgroup.zpowers t) sTheta :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hcard_t, card_sTheta]; norm_num)
  have hNormalizer : Subgroup.zpowers t ≤ Subgroup.normalizer (sTheta : Set EC) :=
    (Subgroup.zpowers_le.2 (hlE_cent ht_lE)).trans (Subgroup.centralizer_le_normalizer _)
  have hcard_cent : Nat.card (Subgroup.centralizer ({t} : Set EC)) = 186 := by
    rw [hCeq, e6TwoT31_card_sup hNormalizer hdisj, hcard_t, card_sTheta]
  exact ⟨hCeq, hdisj, hcard_cent⟩

end CFSG.StandardType.GGSixE6Two
