module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofCensus
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofInner
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofZRoot
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

structure Config228 (Y : Type) [Group Y] (E : Subgroup (MulAut Y)) (y : Y) (N Kb : Subgroup Y)
    (m : ℕ) : Prop where
  elemAbelian : IsElemAbelian 3 E
  card_E : Nat.card E = 3 ^ 2
  le_inner : E ≤ (MulAut.conj : Y →* MulAut Y).range
  mem_E : MulAut.conj y ∈ E
  not_mem_center : y ∉ Subgroup.center Y
  comm : ∀ k ∈ N, y * k = k * y
  normalizes : ∀ g : Y, g * y = y * g → ∀ k ∈ N, g * k * g⁻¹ ∈ N
  le : Kb ≤ N
  equiv : Nonempty (Kb ≃* projSL 2 (GaloisField 2 m))
  pos : 0 < m
  even : Even m
  eq_or : Kb = N ∨ StatedClassicalModel N .PSU 3 2 2

namespace Item22Res4Proof

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_theta {X A : Subgroup G} (hA : IsElemAbelian 3 A) {w : G} (hwA : w ∈ A)
    (hwθ : w ∈ inSubgroup (aschbacherSolvableCore 3) X) : w = 1 := by
  obtain ⟨t, ht, rfl⟩ := hwθ
  have h3 : ((t : X) : G) ^ 3 = 1 := hA.2 _ hwA
  set t' : aschbacherSolvableCore 3 X := ⟨t, ht⟩
  have h3' : t' ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [t'] using h3
  have hdvd3 : orderOf t' ∣ 3 := orderOf_dvd_of_pow_eq_one h3'
  have hdvdN : orderOf t' ∣ Nat.card (aschbacherSolvableCore 3 X) := orderOf_dvd_natCard t'
  have h1 : orderOf t' = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact h
    · exact absurd (h ▸ hdvdN) three_not_dvd_card_aschbacherSolvableCore
  have h2 : t' = 1 := orderOf_eq_one_iff.mp h1
  have h4 : t = 1 := congrArg Subtype.val h2
  simp [h4]

theorem fix_of_mem_starOf {X A : Subgroup G} (hA : IsElemAbelian 3 A) {ρ : MulAut A}
    (hρ : ρ ∈ starOf A X) {a : G} (haA : a ∈ A) (haC : a ∈ Sec4.thetaQuotCentralizer X) :
    ρ ⟨a, haA⟩ = ⟨a, haA⟩ := by
  obtain ⟨⟨x, hxN⟩, hxX', rfl⟩ := hρ
  have hxX : x ∈ X := hxX'
  obtain ⟨⟨a', haN⟩, ha1, rfl⟩ := haC
  apply Subtype.ext
  change x * a' * x⁻¹ = a'
  have h1 := congrArg (fun σ : MulAut (X ⧸ aschbacherSolvableCore 3 X) =>
    σ ((⟨x, hxX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X)) ha1
  simp only [MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk, MulAut.one_apply] at h1
  have h2 := QuotientGroup.eq.mp h1
  set w : G := a' * x⁻¹ * a'⁻¹ * x with hw
  have hwθ : w ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    refine ⟨_, h2, ?_⟩
    change ((X.normalizerMonoidHom ⟨a', haN⟩ ⟨x, hxX⟩ : X) : G)⁻¹ * x = w
    rw [Sec4.normalizerMonoidHom_apply_coe, hw]
    group
  have hwA : w ∈ A := by
    have hxA : x⁻¹ * a'⁻¹ * x ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) a'⁻¹).mp
        (A.inv_mem haA)
      simpa using this
    have : w = a' * (x⁻¹ * a'⁻¹ * x) := by rw [hw]; group
    rw [this]
    exact A.mul_mem haA hxA
  have hw1 := eq_one_of_mem_theta hA hwA hwθ
  rw [hw] at hw1
  calc x * a' * x⁻¹ = x * (a' * x⁻¹ * a'⁻¹ * x) * x⁻¹ * a' := by group
    _ = a' := by rw [hw1]; group

theorem injective_of_three_dvd {X K : Subgroup G} (hKX : K ≤ X) [IsSimpleGroup K]
    (h3 : 3 ∣ Nat.card K) :
    Function.Injective ((QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp
      (K.subgroupOf X).subtype) := by
  set ι := (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K.subgroupOf X).subtype
  let eK : K.subgroupOf X ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  have : IsSimpleGroup (K.subgroupOf X) := eK.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ι.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff ι).mp h
  · exfalso
    have hle : K.subgroupOf X ≤ aschbacherSolvableCore 3 X := fun x hx =>
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp
        (h ▸ Subgroup.mem_top (⟨x, hx⟩ : K.subgroupOf X)))
    have hdvd : Nat.card (K.subgroupOf X) ∣ Nat.card (aschbacherSolvableCore 3 X) :=
      Subgroup.card_dvd_of_le hle
    rw [Nat.card_congr eK.toEquiv] at hdvd
    exact three_not_dvd_card_aschbacherSolvableCore (h3.trans hdvd)

theorem three_dvd_card_projSL_two {m : ℕ} (hm : 0 < m) :
    3 ∣ Nat.card (projSL 2 (GaloisField 2 m)) := by
  rw [card_projSL_two m hm]
  refine Dvd.dvd.mul_left ?_ _
  have h : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 m

end Item22Res4Proof

open Item22Res4Proof Item223CensusProof

variable {G : Type} [Group G] [Finite G]

theorem config228_of {X A K K₀ : Subgroup G} {m : ℕ}
    (hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X) {ρ : MulAut A} (hρ : ρ ∈ starOf A X)
    (hρr : IsReflectionOn ρ) (hKK : K ≤ K₀) (hK0X : K₀ ≤ X)
    (hK0C : K₀ ≤ Subgroup.centralizer (fixedInG A ρ : Set G))
    (hnorm : ∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A ρ : Set G), ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀)
    (hU : K = K₀ ∨ StatedClassicalModel K₀ .PSU 3 2 2)
    (hKm : Nonempty (K ≃* projSL 2 (GaloisField 2 m))) (hm0 : 0 < m) (hme : Even m) :
    ∃ (E : Subgroup (MulAut (X ⧸ aschbacherSolvableCore 3 X))) (y : X ⧸ aschbacherSolvableCore 3 X)
      (N Kb : Subgroup (X ⧸ aschbacherSolvableCore 3 X)),
      Config228 (X ⧸ aschbacherSolvableCore 3 X) E y N Kb m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hAmax.prop
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  set Y := X ⧸ aschbacherSolvableCore 3 X with hY
  set B : Subgroup G := fixedInG A ρ with hBdef
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBA.trans hAN
  set E := (Sec4.thetaAct hAN).range with hEdef
  have hE := Sec4.isElemAbelian_range_thetaAct hAN hAe
  have hEcard : Nat.card E = 3 ^ 2 := by
    have h1 : Nat.card E * Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) =
        Nat.card A := card_range_thetaAct hAN
    rw [hAC, hA27] at h1
    norm_num at h1 ⊢
    omega
  have hEinn := Sec4.range_thetaAct_le_inner hAN hin
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
  have hDE : D ≤ E := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBA b.2⟩, rfl⟩
  have hD1 : D ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  obtain ⟨⟨β, hβD⟩, hβ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
  have hβ1 : β ≠ 1 := fun h => hβ1' (Subtype.ext h)
  obtain ⟨y, rfl⟩ := hEinn (hDE hβD)
  have hβ3 : (MulAut.conj y) ^ 3 = 1 := hE.2 _ (hDE hβD)
  have hDz : D = Subgroup.zpowers (MulAut.conj y) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hβD) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime hβ3 hβ1, hDcard]
  have hfixD : ∀ g : Y, g * y = y * g → ∀ d ∈ D, d g = g := by
    intro g hg d hd
    rw [hDz] at hd
    obtain ⟨k, rfl⟩ := hd
    have hβg : MulAut.conj y g = g := by
      rw [MulAut.conj_apply, ← hg, mul_inv_cancel_right]
    have hk : ∀ k : ℤ, (MulAut.conj y) ^ k = 1 ∨ ((MulAut.conj y) ^ k) g = g := by
      intro k
      right
      induction k using Int.induction_on with
      | zero => simp
      | succ j ih => rw [zpow_add_one, MulAut.mul_apply, hβg, ih]
      | pred j ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have : (MulAut.conj y)⁻¹ g = g := by
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hβg]
        rw [this, ih]
    rcases hk k with h | h
    · simp [h]
    · exact h
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
  refine ⟨E, y, ι₀.range, ιK.range, ⟨hE, hEcard, hEinn, hDE hβD, ?_, ?_, ?_, ?_, ?_, hm0, hme,
    ?_⟩⟩
  ·
    intro hyZ
    apply hβ1
    ext z
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hyZ z).symm,
      mul_inv_cancel_right]
  ·
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hk
    have hβk : ∀ b : B, Sec4.thetaAct hBN b (ι₀ ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩) =
        ι₀ ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩ := by
      intro b
      change Sec4.thetaAct hBN b ((k : X) : Y) = ((k : X) : Y)
      rw [thetaAct_mk]
      congr 1
      apply Subtype.ext
      have hkb := Subgroup.mem_centralizer_iff.mp (hK0C hk) b b.2
      change (b : G) * (k : G) * (b : G)⁻¹ = k
      rw [hkb, mul_inv_cancel_right]
    obtain ⟨b, hb⟩ := hβD
    have h1 := hβk b
    rw [hb, MulAut.conj_apply] at h1
    calc y * ι₀ ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩ =
        y * ι₀ ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩ * y⁻¹ * y := by group
      _ = _ := by rw [h1]
  ·
    intro g hg k hk
    have hfixz : ∀ b : B, Item223KFactsProof.barAct hBN b g = g := fun b =>
      hfixD g hg _ ⟨b, rfl⟩
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
    exact ⟨(MonoidHom.ofInjective hιKi).symm.trans
      ((Subgroup.subgroupOfEquivOfLe (hKK.trans hK0X)).trans eK)⟩
  ·
    rcases hU with rfl | hU
    · exact Or.inl rfl
    · right
      have := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _ hU).2
      have h3 : 3 ∣ Nat.card K₀ := hK3.trans (Subgroup.card_dvd_of_le hKK)
      have hι₀i : Function.Injective ι₀ := injective_of_three_dvd hK0X h3
      exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe hK0X).symm.trans (MonoidHom.ofInjective hι₀i)).symm hU

end CFSG.RankThree.PartTwo.Sec21
