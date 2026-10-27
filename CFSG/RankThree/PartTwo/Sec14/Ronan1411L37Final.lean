module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1411L37Vac
public import CFSG.RankThree.PartTwo.Sec14.Ronan1411L37Hess
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessFinal
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofHeis
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1411L37

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank
open Matrix (ProjGenLinGroup)


theorem ks1411HJCoreL37 : KS1411HJCoreL37 := by
  intro M _ _ Ybar Abar Xbar Rbar abar hset hX S T hS hT hST hsupp
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hXn := Wales1411W.HJInner.normal_X hset
  obtain ⟨h7, -⟩ := id hX
  obtain ⟨e, hpgl⟩ := exists_pgl_model hset hX
  set K := GaloisField 7 1 with hKdef
  have hK : PiField true 7 1 K :=
    ⟨Fact.out, le_rfl, by rw [GaloisField.card 7 1 (by norm_num)]; rfl⟩
  have hq : ModThree true (7 ^ 1) := by
    change 7 ^ 1 % 3 = 1
    norm_num
  have h9 : ¬ ModNine true (7 ^ 1) := by
    change ¬ 7 ^ 1 % 9 = 1
    norm_num
  haveI : Group.IsPerfect ↥Xbar := hset.perfect
  haveI := isPerfect_projImage_of_equiv e
  have : Finite K := hK.finite
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hA := maximal_elemAbelian hset
  have hAc := inf_centralizer_X hset
  have hc3 : orderOf abar = 3 := orderOf_eq_prime (hset.isElemAbelian.2 abar hset.mem_A)
    hset.ne_one
  have hAcomm : ∀ a ∈ Abar, ∀ b ∈ Abar, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ Abar, a ^ 3 = 1 := hset.isElemAbelian.2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  set R := (pglHomP hK hq Abar hpgl).range with hR
  have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm
  have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpgl) hA3
  have hR9 : Nat.card R = 9 := by
    have h := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hpgl)
    rw [hAc, Nat.card_zpowers, hc3, hset.card_A, ← hR] at h
    omega
  have hvA : ∀ a ∈ Abar, ∀ v ∈ Xbar, a * v⁻¹ ∈ Subgroup.centralizer (Xbar : Set M) →
      v ∈ Abar := by
    intro a ha v hv hav
    have hCn : (Subgroup.centralizer (Xbar : Set M)).Normal := inferInstance
    set c := a * v⁻¹ with hcdef
    have hvc : v * c = c * v := Subgroup.mem_centralizer_iff.mp hav v hv
    have hav' : a = c * v := by rw [hcdef]; group
    have hvcomm : v ∈ Subgroup.centralizer (Abar : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro ε hε
      have hk : v * ε * v⁻¹ * ε⁻¹ ∈ Xbar ⊓ Subgroup.centralizer (Xbar : Set M) := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have : v * ε * v⁻¹ * ε⁻¹ = v * (ε * v⁻¹ * ε⁻¹) := by group
          rw [this]
          exact mul_mem hv (hXn.conj_mem _ (inv_mem hv) ε)
        · have h1 : v * ε * v⁻¹ * ε⁻¹ = c⁻¹ * (ε * c * ε⁻¹) := by
            have hae : a * ε = ε * a := hAcomm a ha ε hε
            have hv' : v = c⁻¹ * a := by rw [hav']; group
            rw [hv']
            calc c⁻¹ * a * ε * (c⁻¹ * a)⁻¹ * ε⁻¹ = c⁻¹ * (a * ε) * a⁻¹ * c * ε⁻¹ := by group
              _ = c⁻¹ * (ε * a) * a⁻¹ * c * ε⁻¹ := by rw [hae]
              _ = c⁻¹ * (ε * c * ε⁻¹) := by group
          rw [h1]
          exact mul_mem (inv_mem hav) (hCn.conj_mem _ hav ε)
      rw [hLC, Subgroup.mem_bot] at hk
      calc ε * v = v * ε * v⁻¹ * ε⁻¹ * (ε * v) := by rw [hk, one_mul]
        _ = v * ε := by group
    have hv3 : v ^ 3 = 1 := by
      have hc3' : c ^ 3 * v ^ 3 = 1 := by
        rw [← (Commute.mul_pow (show Commute c v from hvc.symm) 3), ← hav']
        exact hA3 a ha
      have hk : v ^ 3 ∈ Xbar ⊓ Subgroup.centralizer (Xbar : Set M) := by
        refine Subgroup.mem_inf.mpr ⟨pow_mem hv 3, ?_⟩
        have : v ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hc3'
        rw [this]
        exact inv_mem (pow_mem hav 3)
      rw [hLC, Subgroup.mem_bot] at hk
      exact hk
    by_cases hv1 : v = 1
    · rw [hv1]
      exact one_mem _
    · exact hset.mem_A_of_three v (hset.le_Y hv) hvcomm (orderOf_eq_prime hv3 hv1)
  rcases frame_or_heis h3K hτ hτ1 R hRcomm hRexp (by omega) with
    ⟨bas, hbas, hd, -, -, -, -, -⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  ·
    set D : Subgroup (GL (Fin 3) K) :=
      R.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi true 3 (7 ^ 1) K with hD
    have hmemD : ∀ y, y ∈ D ↔ (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ R ∧
        y ∈ glPi true 3 (7 ^ 1) K := fun y => Iff.rfl
    have hmap : D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = R := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact ((hmemD y).mp hy).1
      · rintro x ⟨a, rfl⟩
        obtain ⟨y, hy⟩ := hpgl a a.2
        refine ⟨y, (hmemD y).mpr ⟨?_, hy.1⟩, ?_⟩
        · exact mk_mem_range_pglHomP a.2 hy
        · exact (pglHomP_apply a hy).symm
    have hC : IsTypeC true (7 ^ 1) K D := by
      refine ⟨inf_le_right, fun a ha => ?_, by rw [hmap, hR9], bas, hbas, fun a ha => hd a
        ((hmemD a).mp ha).1⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hRexp _ ((hmemD a).mp ha).1
    obtain ⟨a₁, ha₁D, ha₁1, htypes⟩ := isTypeC_types hK hq hC
    have ha₁Z : a₁ ∉ StatedScalars (Fin 3) K := by
      intro h
      apply Res423Four.not_mem_zPi_of_type1 hK hq ha₁1
      have hπ : true = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 7 1 K :=
        fun h => absurd h (by decide)
      have hq' : true = false → ModThree false (7 ^ 1) := fun h => absurd h (by decide)
      rw [zPi_eq hπ hq' hτ hτ1]
      exact ⟨((hmemD a₁).mp ha₁D).2, h⟩
    by_cases hin : Abar ≤ Xbar ⊔ Subgroup.centralizer (Xbar : Set M)
    ·
      exfalso
      obtain ⟨r, hrR, hr⟩ : ∃ r ∈ R, r ∉ ({1, (a₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K),
          (a₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)⁻¹} : Set _) := by
        by_contra h
        push Not at h
        have hsub : (R : Set (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)) ⊆
            {1, (a₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K),
              (a₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)⁻¹} := fun x hx => h x hx
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hR9] at hle
        have h3 : ({1, (a₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K),
            (a₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)⁻¹} : Set _).ncard ≤ 3 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
          rw [Set.ncard_singleton]
        omega
      obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective r
      have hy₂H : y₂ ∈ glPi true 3 (7 ^ 1) K := Subgroup.mem_top y₂
      have hy₂D : y₂ ∈ D := (hmemD y₂).mpr ⟨hrR, hy₂H⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
      obtain ⟨hr1, hra, hrai⟩ := hr
      have hy₂Z : y₂ ∉ StatedScalars (Fin 3) K := fun h =>
        hr1 ((QuotientGroup.eq_one_iff y₂).mpr h)
      have hnot1 : ¬ Type123 true (7 ^ 1) K y₂ 1 := by
        intro h1
        rcases ((htypes y₂ hy₂D hy₂Z).1.mp h1) with h | h
        · apply hra
          rw [QuotientGroup.eq]
          have : y₂⁻¹ * a₁ = (a₁⁻¹ * (y₂ * a₁⁻¹) * a₁⁻¹⁻¹)⁻¹ := by group
          rw [this]
          exact inv_mem ((StatedScalars.normal (Fin 3) K).conj_mem _ h a₁⁻¹)
        · apply hrai
          rw [← QuotientGroup.mk_inv, QuotientGroup.eq]
          have : y₂⁻¹ * a₁⁻¹ = (a₁ * (y₂ * a₁) * a₁⁻¹)⁻¹ := by group
          rw [this]
          exact inv_mem ((StatedScalars.normal (Fin 3) K).conj_mem _ h a₁)
      obtain ⟨a₂, ha₂A, ha₂⟩ := exists_isPGLAtP_of_mk_mem hy₂H hrR
      have ha₂C : a₂ ∉ Subgroup.centralizer (Xbar : Set M) := fun h => by
        have h1 := isPGLAtP_inv_mul_mem hK hq (isPGLAtP_of_mem_centralizer e h) ha₂
        rw [inv_one, one_mul] at h1
        exact hy₂Z h1
      obtain ⟨l, hl, hyl⟩ := exists_inner_of_mem_supP hK hq (hin ha₂A) ha₂
      rcases (rank3II_4_10_two hK hq hτ hτ1 hy₂H (not_mem_zPi_of_isPGLAtP hK hq ha₂C ha₂)
          (pow_three_mem_zPiP hK hq (hA3 a₂ ha₂A) ha₂)).mp ⟨l, hl, hyl⟩ with
        ⟨y, ⟨z, hz, rfl⟩, g, hg, hD'⟩ | ⟨-, h9'⟩
      · exact hnot1 ⟨τ, hτ, hτ1, z, hz, g, hg, hD'⟩
      · exact h9 h9'
    ·
      obtain ⟨a, haA, ha⟩ := exists_isPGLAtP_of_mk_mem ((hmemD a₁).mp ha₁D).2
        ((hmemD a₁).mp ha₁D).1
      obtain ⟨l, hl, hyl⟩ := exists_inner_of_type1 hK hq ((hmemD a₁).mp ha₁D).2 ha₁1
      obtain ⟨v, hv, -, hav⟩ := exists_inner_mem_of_innerP hK hq ha hl hyl
      have hv1 : v ≠ 1 := by
        rintro rfl
        rw [inv_one, mul_one] at hav
        have h1 := isPGLAtP_inv_mul_mem hK hq (isPGLAtP_of_mem_centralizer e hav) ha
        rw [inv_one, one_mul] at h1
        exact ha₁Z h1
      obtain ⟨a₀, ha₀A, ha₀⟩ := SetLike.not_le_iff_exists.mp hin
      exact (false_of_not_inner hset hX (hvA a haA v hv hav) hv hv1 ⟨a₀, ha₀A, ha₀⟩ hS hT hST
        hsupp).elim
  ·
    by_cases hin : Abar ≤ Xbar ⊔ Subgroup.centralizer (Xbar : Set M)
    ·
      have hAeq : Abar ⊓ (Xbar ⊔ Subgroup.centralizer (Xbar : Set M)) = Abar := inf_eq_left.mpr hin
      have hcardALC := card_inf_sup_centralizer hA hLC hc3 hAc
      rw [hAeq, hset.card_A] at hcardALC
      have hAL9 : Nat.card (Abar ⊓ Xbar : Subgroup M) = 9 := by omega
      have hsup := inf_sup_centralizer_eq hA hLC hAc
      rw [hAeq] at hsup
      have hAX : Abar ⊔ Xbar = Subgroup.zpowers abar ⊔ Xbar := by
        apply le_antisymm
        · rw [hsup]
          exact sup_le (sup_le (inf_le_right.trans le_sup_right) le_sup_left) le_sup_right
        · refine sup_le ?_ le_sup_right
          rw [← hAc]
          exact inf_le_left.trans le_sup_left
      have hE : ∀ a ∈ Abar ⊓ Xbar, ∃ y, IsPGLAtP e a y := fun a ha =>
        hpgl a (Subgroup.mem_inf.mp ha).1
      have hrange : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ R →
          (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
            (pglHomP hK hq (Abar ⊓ Xbar) hE).range := by
        intro y hy
        obtain ⟨⟨a, ha⟩, hay⟩ := hy
        obtain ⟨z, hz⟩ := hpgl a ha
        rw [pglHomP_apply ⟨a, ha⟩ hz] at hay
        rw [← hay]
        exact mem_range_inf_of_mem_sup hK hq hA hLC hE ha (hin ha) hz
      have h1 : ∀ x ∈ Abar ⊓ Xbar, x ≠ 1 → ∀ y, IsPGLAtP e x y →
          Type123 true (7 ^ 1) K y 1 := by
        intro x hx hx1 y hy
        have hxC : x ∉ Subgroup.centralizer (Xbar : Set M) := fun h => hx1 (by
          have : x ∈ Xbar ⊓ Subgroup.centralizer (Xbar : Set M) := ⟨hx.2, h⟩
          rw [hLC] at this
          exact this)
        rcases type13_of_heisP hK hq hRcomm hy₁ hy₂ hζ1 hζ hy.1
            (not_mem_zPi_of_isPGLAtP hK hq hxC hy) (pow_three_mem_zPiP hK hq (hA3 x hx.1) hy)
            (mk_mem_range_pglHomP hx.1 hy) with h | h
        · exact h
        · exact absurd (exists_inner_of_mem_supP hK hq (Subgroup.mem_sup_left hx.2) hy)
            (not_inner_of_type3 hK hq hy.1 h)
      have htr := transitive_of_range_heis hK hq inf_le_right hAL9
        (fun a ha b hb => hAcomm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1)
        (fun a ha => hA3 a (Subgroup.mem_inf.mp ha).1) hE (hrange _ hy₁) (hrange _ hy₂) hζ1 hζ h1
      exact conj_of_hess Sec4.Ronan148L.kl3HessTori_holds hset hX hAX htr hS hT hST
    ·
      obtain ⟨a₀, ha₀A, ha₀⟩ := SetLike.not_le_iff_exists.mp hin
      obtain ⟨y₀, hy₀⟩ := hpgl a₀ ha₀A
      have ha₀C : a₀ ∉ Subgroup.centralizer (Xbar : Set M) := fun h =>
        ha₀ (Subgroup.mem_sup_right h)
      rcases type13_of_heisP hK hq hRcomm hy₁ hy₂ hζ1 hζ hy₀.1
          (not_mem_zPi_of_isPGLAtP hK hq ha₀C hy₀) (pow_three_mem_zPiP hK hq (hA3 a₀ ha₀A) hy₀)
          (mk_mem_range_pglHomP ha₀A hy₀) with h | h
      · exfalso
        obtain ⟨l, hl, hyl⟩ := exists_inner_of_type1 hK hq hy₀.1 h
        obtain ⟨v, hv, -, hav⟩ := exists_inner_mem_of_innerP hK hq hy₀ hl hyl
        apply ha₀
        have : a₀ = a₀ * v⁻¹ * v := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_right hav) (Subgroup.mem_sup_left hv)
      · obtain ⟨v, hv, hv1⟩ := exists_mem_inf_of_type3 hK hq hA hset.card_A hLC hc3 hAc hpgl
          ha₀A hy₀ h
        exact (false_of_not_inner hset hX (Subgroup.mem_inf.mp hv).1 (Subgroup.mem_inf.mp hv).2 hv1
          ⟨a₀, ha₀A, ha₀⟩ hS hT hST hsupp).elim

end CFSG.RankThree.PartTwo.Sec14.Ronan1411L37
