module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofConfig

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

structure Config228Aut (Y : Type) [Group Y] (β : MulAut Y) (N Kb : Subgroup Y) (m : ℕ) : Prop where
  fix : ∀ k ∈ N, β k = k
  normalizes : ∀ g : Y, β g = g → ∀ k ∈ N, g * k * g⁻¹ ∈ N
  le : Kb ≤ N
  equiv : Nonempty (Kb ≃* projSL 2 (GaloisField 2 m))
  pos : 0 < m
  even : Even m
  eq_or : Kb = N ∨ StatedClassicalModel N .PSU 3 2 2

namespace Item228Census2Proof

open Item22Res4Proof Item223CensusProof

variable {G : Type} [Group G] [Finite G]

theorem config228Aut_of {X A K K₀ : Subgroup G} {m : ℕ}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    {ρ : MulAut A} (hρ : ρ ∈ starOf A X) (hρr : IsReflectionOn ρ) (hKK : K ≤ K₀)
    (hK0X : K₀ ≤ X) (hK0C : K₀ ≤ Subgroup.centralizer (fixedInG A ρ : Set G))
    (hnorm : ∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A ρ : Set G), ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀)
    (hU : K = K₀ ∨ StatedClassicalModel K₀ .PSU 3 2 2)
    (hKm : Nonempty (K ≃* projSL 2 (GaloisField 2 m))) (hm0 : 0 < m) (hme : Even m) :
    ∃ b ∈ A, ∃ hbN : b ∈ Subgroup.normalizer (X : Set G),
      Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩) ≠ 1 ∧
      ∃ N Kb : Subgroup (X ⧸ aschbacherSolvableCore 3 X), Config228Aut
        (X ⧸ aschbacherSolvableCore 3 X) (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩))
        N Kb m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hAmax.prop
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  set Y := X ⧸ aschbacherSolvableCore 3 X with hY
  set B : Subgroup G := fixedInG A ρ with hBdef
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBA.trans hAN
  have hCB : A ⊓ Sec4.thetaQuotCentralizer X ≤ B := by
    rintro a ⟨haA, haC⟩
    exact ⟨⟨a, haA⟩, fix_of_mem_starOf hAe hρ haA haC, rfl⟩
  have hB9 : Nat.card B = 9 := Item228ResProof.card_fixedInG_eq_nine hAc hA27 hρr
  set D := (Sec4.thetaAct hBN).range with hDdef
  have hDcard : Nat.card D = 3 := by
    have h1 : Nat.card D * Nat.card (B ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) =
        Nat.card B := card_range_thetaAct hBN
    have h2 : B ⊓ Sec4.thetaQuotCentralizer X = A ⊓ Sec4.thetaQuotCentralizer X :=
      le_antisymm (inf_le_inf_right _ hBA) (le_inf hCB inf_le_right)
    rw [h2, hAC, hB9] at h1
    omega
  have hD1 : D ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  obtain ⟨⟨β, hβD⟩, hβ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
  have hβ1 : β ≠ 1 := fun h => hβ1' (Subtype.ext h)
  have hβ3 : β ^ 3 = 1 := by
    obtain ⟨b, rfl⟩ := hβD
    rw [← map_pow]
    have : b ^ 3 = 1 := Subtype.ext (hAe.2 _ (hBA b.2))
    rw [this, map_one]
  have hDz : D = Subgroup.zpowers β := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hβD) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime hβ3 hβ1, hDcard]
  obtain ⟨b, hbβ⟩ := hβD
  have hfixD : ∀ g : Y, β g = g → ∀ d ∈ D, d g = g := by
    intro g hg d hd
    rw [hDz] at hd
    obtain ⟨k, rfl⟩ := hd
    have hk : ∀ k : ℤ, (β ^ k) g = g := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ j ih => rw [zpow_add_one, MulAut.mul_apply, hg, ih]
      | pred j ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have : β⁻¹ g = g := by
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hg]
        rw [this, ih]
    exact hk k
  obtain ⟨eK⟩ := hKm
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) :=
    isSimpleGroup_projSL_two (by obtain ⟨r, hr⟩ := hme; omega)
  have : IsSimpleGroup K := eK.isSimpleGroup
  have hK3 : 3 ∣ Nat.card K := by
    rw [Nat.card_congr eK.toEquiv]
    exact three_dvd_card_projSL_two hm0
  set ιK := (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K.subgroupOf X).subtype
    with hιK
  have hιKi : Function.Injective ιK := injective_of_three_dvd (hKK.trans hK0X) hK3
  set ι₀ := (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K₀.subgroupOf X).subtype
    with hι₀
  have hβeq : β = Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hBN b.2⟩) := by
    rw [← hbβ, Sec4.thetaAct_apply]
  refine ⟨b, hBA b.2, hBN b.2, hβeq ▸ hβ1, ι₀.range, ιK.range, ?_⟩
  rw [← hβeq]
  refine ⟨?_, ?_, ?_,
    ⟨(MonoidHom.ofInjective hιKi).symm.trans ((Subgroup.subgroupOfEquivOfLe (hKK.trans hK0X)).trans
      eK)⟩, hm0, hme, ?_⟩
  ·
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hk
    rw [← hbβ]
    change Sec4.thetaAct hBN b ((k : X) : Y) = ((k : X) : Y)
    rw [thetaAct_mk]
    congr 1
    apply Subtype.ext
    have hkb := Subgroup.mem_centralizer_iff.mp (hK0C hk) b b.2
    change (b : G) * (k : G) * (b : G)⁻¹ = k
    rw [hkb, mul_inv_cancel_right]
  ·
    intro g hg k hk
    have hfixz : ∀ b' : B, Item223KFactsProof.barAct hBN b' g = g := fun b' =>
      hfixD g hg _ ⟨b', rfl⟩
    have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
    obtain ⟨g', rfl, hgC⟩ := Item223KFactsProof.exists_lift_of_fixed hBN hB3 g hfixz
    obtain ⟨⟨x, hx⟩, rfl⟩ := hk
    have hgk : (g' : G) * ((x : X) : G) * (g' : G)⁻¹ ∈ K₀ :=
      hnorm g' ⟨g'.2, hgC⟩ _ (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨⟨g' * (x : X) * g'⁻¹, Subgroup.mem_subgroupOf.mpr hgk⟩, ?_⟩
    change QuotientGroup.mk' (aschbacherSolvableCore 3 X) (g' * (x : X) * g'⁻¹) =
      (g' : Y) * ι₀ ⟨x, hx⟩ * (g' : Y)⁻¹
    rw [map_mul, map_mul, map_inv]
    rfl
  ·
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.mpr (hKK (Subgroup.mem_subgroupOf.mp hk))⟩, rfl⟩
  ·
    rcases hU with rfl | hU
    · exact Or.inl rfl
    · right
      have := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _ hU).2
      have h3 : 3 ∣ Nat.card K₀ := hK3.trans (Subgroup.card_dvd_of_le hKK)
      have hι₀i : Function.Injective ι₀ := injective_of_three_dvd hK0X h3
      exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe hK0X).symm.trans (MonoidHom.ofInjective hι₀i)).symm hU

end Item228Census2Proof

end CFSG.RankThree.PartTwo.Sec21
