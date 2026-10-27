module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_of_subnormal_sup_isPGroup {H J R : Subgroup Y} (hJ : ⁅J, J⁆ = J)
    (hsn : CFSG.Open.IsSubnormal H J) (hR : IsPGroup 2 R) (hJR : J = H ⊔ R) : H = J := by
  induction hsn with
  | refl => rfl
  | @step H M K hle hnormal hMK ih =>
    have hMR : K = M ⊔ R := by
      apply le_antisymm
      · rw [hJR]; exact sup_le_sup_right hle R
      · refine sup_le hMK.le ?_
        rw [hJR]; exact le_sup_right
    have hMK' : M = K := ih hJ hMR
    subst hMK'
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥R := hR.isNilpotent
    have h1 := CFSG.Quasithin.perfectCore_le_of_sup_solvable hle hnormal hJR inferInstance
    rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect hJ] at h1
    exact le_antisymm hle h1

theorem perfectCore_sup_eq {A Q : Subgroup Y} [Q.Normal] (hQ : IsPGroup 2 Q)
    (hsn : CFSG.Open.IsSubnormal A ⊤) (hAp : ⁅A, A⁆ = A) : CFSG.Quasithin.perfectCore (A ⊔ Q) = A := by
  set J := CFSG.Quasithin.perfectCore (A ⊔ Q) with hJdef
  have hAJ : A ≤ J := CFSG.Quasithin.le_perfectCore_of_perfect le_sup_left hAp
  have hJle : J ≤ A ⊔ Q := CFSG.Quasithin.perfectCore_le _
  have hJp : ⁅J, J⁆ = J := CFSG.Quasithin.perfectCore_perfect _
  have hJR : J = A ⊔ (J ⊓ Q) := by
    apply le_antisymm
    · intro j hj
      obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hJle hj)
      have hqJ : q ∈ J ⊓ Q := ⟨by
        have := J.mul_mem (J.inv_mem (hAJ ha)) hj
        simpa using this, hq⟩
      exact Subgroup.mul_mem_sup ha hqJ
    · exact sup_le hAJ inf_le_left
  have hsnJ : CFSG.Open.IsSubnormal A J := CFSG.Quasithin.A3.subnormal_of_le_of_le hsn hAJ le_top
  have hRpg : IsPGroup 2 ↥(J ⊓ Q) := hQ.to_le inf_le_right
  exact (eq_of_subnormal_sup_isPGroup hJp hsnJ hRpg hJR).symm

theorem image_injective {A A' : Subgroup Y} (hsn : CFSG.Open.IsSubnormal A ⊤) (hp : ⁅A, A⁆ = A)
    (hsn' : CFSG.Open.IsSubnormal A' ⊤) (hp' : ⁅A', A'⁆ = A')
    (h : A.map (QuotientGroup.mk' (CFSG.pCore 2 Y)) = A'.map (QuotientGroup.mk' (CFSG.pCore 2 Y))) :
    A = A' := by
  have hQp : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.pCore_isPGroup
  have key : ∀ {B B' : Subgroup Y},
      B.map (QuotientGroup.mk' (CFSG.pCore 2 Y)) = B'.map (QuotientGroup.mk' (CFSG.pCore 2 Y)) →
        B ≤ B' ⊔ CFSG.pCore 2 Y := by
    intro B B' hBB'
    have h1 : B ≤ (B.map (QuotientGroup.mk' (CFSG.pCore 2 Y))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 Y)) := Subgroup.le_comap_map _ B
    rw [hBB', Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
    exact h1
  have h1 : A ⊔ CFSG.pCore 2 Y = A' ⊔ CFSG.pCore 2 Y := by
    apply le_antisymm
    · exact sup_le (key h) le_sup_right
    · exact sup_le (key h.symm) le_sup_right
  have h2 := perfectCore_sup_eq hQp hsn hp
  rw [h1, perfectCore_sup_eq hQp hsn' hp'] at h2
  exact h2.symm

theorem conj_mem_map_of_characteristic' {X : Subgroup Y} {D : Subgroup X} [hD : D.Characteristic]
    {g : Y} (hg : g ∈ normalizer (X : Set Y)) {x : Y} (hx : x ∈ D.map X.subtype) :
    g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem map_pCore_le_of_isSubnormal {K : Subgroup Y} (hK : K.IsSubnormal) :
    (CFSG.pCore 2 K).map K.subtype ≤ CFSG.pCore 2 Y := by
  have key : ∀ {X Z : Subgroup Y}, X ≤ Z → Z ≤ normalizer (X : Set Y) →
      (CFSG.pCore 2 X).map X.subtype ≤ (CFSG.pCore 2 Z).map Z.subtype := by
    intro X Z hXZ hZN
    have hLZ : (CFSG.pCore 2 X).map X.subtype ≤ Z := (Subgroup.map_subtype_le _).trans hXZ
    have hle : ((CFSG.pCore 2 X).map X.subtype).subgroupOf Z ≤ CFSG.pCore 2 Z := by
      apply le_sSup
      refine ⟨⟨fun l hl z => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using conj_mem_map_of_characteristic' (hZN z.2) hl
      · exact ((CFSG.pCore_isPGroup (p := 2) (G := X)).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLZ).symm
    calc (CFSG.pCore 2 X).map X.subtype
        = (((CFSG.pCore 2 X).map X.subtype).subgroupOf Z).map Z.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLZ).symm
      _ ≤ (CFSG.pCore 2 Z).map Z.subtype := Subgroup.map_mono hle
  induction hK with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => conj_mem_map_of_characteristic' ?_ hl⟩,
      (CFSG.pCore_isPGroup (p := 2) (G := (⊤ : Subgroup Y))).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Z hXZ hZ hN ih =>
    exact (key hXZ ((Subgroup.normal_subgroupOf_iff_le_normalizer hXZ).mp hN)).trans ih

theorem pCore_eq_subgroupOf {A : Subgroup Y} (hsn : CFSG.Open.IsSubnormal A ⊤) :
    CFSG.pCore 2 ↥A = (CFSG.pCore 2 Y).subgroupOf A := by
  apply le_antisymm
  · intro x hx
    exact map_pCore_le_of_isSubnormal (CFSG.Quasithin.A3.subnormal_top_iff.mp hsn) ⟨x, hx, rfl⟩
  · apply le_sSup
    exact ⟨inferInstance, CFSG.pCore_isPGroup.comap_subtype⟩

noncomputable def barIso {A : Subgroup Y} (hsn : CFSG.Open.IsSubnormal A ⊤) :
    (↥A ⧸ CFSG.pCore 2 ↥A) ≃* ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 Y))) := by
  let π : Y →* Y ⧸ CFSG.pCore 2 Y := QuotientGroup.mk' (CFSG.pCore 2 Y)
  let ψ : ↥A →* ↥(A.map π) := ((π.comp A.subtype).codRestrict (A.map π)
    (fun a => ⟨a, a.2, rfl⟩))
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hker : ψ.ker = CFSG.pCore 2 ↥A := by
    rw [pCore_eq_subgroupOf hsn]
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have : π (x : Y) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (x : Y)).1 this
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (x : Y)).2 h)
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

theorem isComponent_image {A : Subgroup Y} (hsn : CFSG.Open.IsSubnormal A ⊤)
    (hq : CFSG.Open.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) :
    CFSG.IsComponent (A.map (QuotientGroup.mk' (CFSG.pCore 2 Y))) := by
  refine ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr (hq.of_mulEquiv (barIso hsn).symm), ?_⟩
  exact CFSG.Quasithin.A3.subnormal_top_iff.mp
    (CFSG.Quasithin.A3.subnormal_top_map (QuotientGroup.mk'_surjective _) hsn)

theorem exists_elemAbelian_of_commute {Z : Type*} [Group Z] [Finite Z] {q a b : ℕ} (hq : q.Prime)
    {F F' : Subgroup Z} (hFel : IsElemAbelian q F) (hF'el : IsElemAbelian q F')
    (hFc : Nat.card F = q ^ a) (hF'c : Nat.card F' = q ^ b)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F', x * y = y * x) (hint : F ⊓ F' = ⊥) :
    ∃ W : Subgroup Z, IsElemAbelian q W ∧ Nat.card W = q ^ (a + b) := by
  classical
  let φ : ↥F × ↥F' →* Z := MonoidHom.noncommCoprod F.subtype F'.subtype
    (fun m n => hcomm (m : Z) m.2 (n : Z) n.2)
  have hφ : ∀ x : ↥F, ∀ y : ↥F', φ (x, y) = (x : Z) * (y : Z) := fun x y => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h1 : (x : Z) * (y : Z) = 1 := by rw [← hφ]; exact hxy
    have h2 : (x : Z) = ((y : Z))⁻¹ := mul_eq_one_iff_eq_inv.1 h1
    have h3 : (x : Z) ∈ F ⊓ F' := ⟨x.2, by rw [h2]; exact F'.inv_mem y.2⟩
    rw [hint, Subgroup.mem_bot] at h3
    have hx : x = 1 := Subtype.ext h3
    have hy : y = 1 := by
      apply Subtype.ext
      have : (y : Z) = 1 := by rw [h3, one_mul] at h1; exact h1
      exact this
    simp [hx, hy]
  refine ⟨φ.range, ?_, ?_⟩
  · refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨⟨x₁, y₁⟩, hu⟩ := u.2
      obtain ⟨⟨x₂, y₂⟩, hv⟩ := v.2
      apply Subtype.ext
      show (u : Z) * (v : Z) = (v : Z) * (u : Z)
      rw [← hu, ← hv, hφ, hφ]
      have hx : (x₁ : Z) * x₂ = x₂ * x₁ := by
        have := hFel.1
        exact congrArg Subtype.val (mul_comm' x₁ x₂)
      have hy : (y₁ : Z) * y₂ = y₂ * y₁ := by
        have := hF'el.1
        exact congrArg Subtype.val (mul_comm' y₁ y₂)
      have h12 := hcomm _ x₁.2 _ y₂.2
      have h21 := hcomm _ x₂.2 _ y₁.2
      calc (x₁ : Z) * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
        _ = x₁ * (x₂ * y₁) * y₂ := by rw [← h21]
        _ = (x₁ * x₂) * (y₁ * y₂) := by group
        _ = (x₂ * x₁) * (y₂ * y₁) := by rw [hx, hy]
        _ = x₂ * (x₁ * y₂) * y₁ := by group
        _ = x₂ * (y₂ * x₁) * y₁ := by rw [h12]
        _ = (x₂ : Z) * y₂ * (x₁ * y₁) := by group
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      have hx : (x : Z) ^ q = 1 := hFel.2 _ x.2
      have hy : (y : Z) ^ q = 1 := hF'el.2 _ y.2
      have hc : Commute (x : Z) (y : Z) := hcomm _ x.2 _ y.2
      rw [hc.mul_pow, hx, hy, one_mul]
  · have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [Nat.card_prod, hFc, hF'c, ← pow_add] at h1
    exact h1.symm

theorem rank_add_of_ne {A A' E E' : Subgroup Y} {q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hsn : CFSG.Open.IsSubnormal A ⊤) (hp : ⁅A, A⁆ = A)
    (hqs : CFSG.Open.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A))
    (hsn' : CFSG.Open.IsSubnormal A' ⊤) (hp' : ⁅A', A'⁆ = A')
    (hqs' : CFSG.Open.IsQuasisimple (↥A' ⧸ CFSG.pCore 2 ↥A')) (hne : A ≠ A')
    (hZ : ¬ q ∣ Nat.card (center (↥A ⧸ CFSG.pCore 2 ↥A)))
    (hEA : E ≤ A) (hE'A' : E' ≤ A') (hEel : IsElemAbelian q E) (hE'el : IsElemAbelian q E')
    (hEc : Nat.card E = q ^ a) (hE'c : Nat.card E' = q ^ b) :
    ∃ W : Subgroup Y, IsElemAbelian q W ∧ Nat.card W = q ^ (a + b) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : Y →* Y ⧸ CFSG.pCore 2 Y := QuotientGroup.mk' (CFSG.pCore 2 Y)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hAc := isComponent_image hsn hqs
  have hA'c := isComponent_image hsn' hqs'
  have hne' : A.map π ≠ A'.map π := fun h => hne (image_injective hsn hp hsn' hp' h)
  have hcomm : ⁅A.map π, A'.map π⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hAc hA'c).resolve_left hne'
  have hdisj : ∀ {F : Subgroup Y}, IsElemAbelian q F → Disjoint F π.ker := by
    intro F hF
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    exact eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hF.isPGroup hker hx hxk
  have hEcard : Nat.card (E.map π) = q ^ a := by
    rw [card_map_of_disjoint_ker π E (hdisj hEel), hEc]
  have hE'card : Nat.card (E'.map π) = q ^ b := by
    rw [card_map_of_disjoint_ker π E' (hdisj hE'el), hE'c]
  have hcommEE : ∀ x ∈ E.map π, ∀ y ∈ E'.map π, x * y = y * x := by
    intro x hx y hy
    have hxA : x ∈ A.map π := Subgroup.map_mono hEA hx
    have hyA : y ∈ A'.map π := Subgroup.map_mono hE'A' hy
    have h1 : A.map π ≤ Subgroup.centralizer ((A'.map π : Subgroup _) : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (h1 hxA) y hyA).symm
  have hint : E.map π ⊓ E'.map π = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzA : z ∈ A.map π := Subgroup.map_mono hEA hz.1
    have hzA' : z ∈ A'.map π := Subgroup.map_mono hE'A' hz.2
    have h1 : A.map π ≤ Subgroup.centralizer ((A'.map π : Subgroup _) : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hzc : (⟨z, hzA⟩ : ↥(A.map π)) ∈ Subgroup.center ↥(A.map π) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 (h1 g.2) z hzA').symm
    have hzq : z ^ q = 1 := (hEel.map π).2 z hz.1
    have hcen : ¬ q ∣ Nat.card (Subgroup.center ↥(A.map π)) := by
      rw [← Nat.card_congr (Subgroup.centerCongr (barIso hsn)).toEquiv]
      exact hZ
    have hord1 : orderOf (⟨⟨z, hzA⟩, hzc⟩ : ↥(Subgroup.center ↥(A.map π))) ∣ q := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      apply Subtype.ext
      simpa using hzq
    have hord2 := orderOf_dvd_natCard (⟨⟨z, hzA⟩, hzc⟩ : ↥(Subgroup.center ↥(A.map π)))
    have hcop : Nat.Coprime q (Nat.card (Subgroup.center ↥(A.map π))) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 hcen
    have h1' : orderOf (⟨⟨z, hzA⟩, hzc⟩ : ↥(Subgroup.center ↥(A.map π))) ∣ Nat.gcd q
        (Nat.card (Subgroup.center ↥(A.map π))) := Nat.dvd_gcd hord1 hord2
    rw [hcop.gcd_eq_one] at h1'
    have h2 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1')
    have h3 : z = 1 := by
      have := congrArg (fun w : ↥(Subgroup.center ↥(A.map π)) => ((w : ↥(A.map π)) : Y ⧸ CFSG.pCore 2 Y)) h2
      simpa using this
    rw [h3]
    exact Subgroup.one_mem _
  obtain ⟨W, hWel, hWcard⟩ := exists_elemAbelian_of_commute hq (hEel.map π) (hE'el.map π) hEcard hE'card
    hcommEE hint
  obtain ⟨Q₁, hQ₁p, hQ₁map, hQ₁disj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 W hWel.isPGroup
  refine ⟨Q₁, isElemAbelian_of_disjoint_ker π Q₁ hQ₁disj (by rw [hQ₁map]; exact hWel), ?_⟩
  rw [← card_map_of_disjoint_ker π Q₁ hQ₁disj, hQ₁map, hWcard]

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
