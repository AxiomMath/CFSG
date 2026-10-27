module

public import CFSG.RankThree.PartOne.FIVES.Lift
public import CFSG.RankThree.PartOne.S12.InputsCT
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
import CFSG.RankThree.PartOne.CTP.PhanBridge

public section

namespace CFSG.RankThree.PartOne.FIVES

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem statedClassicalModel_quot_center {f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X]
    (hX : CentrallyUThree f X) :
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨θ₀, hθ, hker⟩ := CTP.exists_su3_surj_of_centrallyUThree hK hX
  exact CTP.statedClassicalModel_psu_of_surjective hK hq (le_refl 3) θ₀ hθ hker

variable {J : Type} [Group J] [Finite J]

omit [Finite J] in
theorem eq_of_forall_mk_eq {K' : Subgroup J} (hK'p : Group.IsPerfect ↥K') (γ : MulAut J)
    (h : ∀ x : J, QuotientGroup.mk' (Subgroup.center J) (γ x) = QuotientGroup.mk' (Subgroup.center J) x) :
    ∀ y ∈ K', γ y = y := by
  have hcent : ∀ x : J, x⁻¹ * γ x ∈ Subgroup.center J := by
    intro x
    have : QuotientGroup.mk' (Subgroup.center J) (x⁻¹ * γ x) = 1 := by
      rw [map_mul, map_inv, h x]
      exact inv_mul_cancel _
    exact (QuotientGroup.eq_one_iff _).mp this
  let φ : ↥K' →* J :=
    { toFun := fun y => (y : J)⁻¹ * γ (y : J)
      map_one' := by simp
      map_mul' := fun a b => by
        have hc := Subgroup.mem_center_iff.mp (hcent (a : J)) (b : J)⁻¹
        show ((a * b : ↥K') : J)⁻¹ * γ ((a * b : ↥K') : J) = ((a : J)⁻¹ * γ (a : J)) *
          ((b : J)⁻¹ * γ (b : J))
        rw [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc ((b : J)⁻¹ * (a : J)⁻¹) * (γ (a : J) * γ (b : J))
            = (b : J)⁻¹ * ((a : J)⁻¹ * γ (a : J)) * γ (b : J) := by group
          _ = ((a : J)⁻¹ * γ (a : J)) * (b : J)⁻¹ * γ (b : J) := by rw [hc]
          _ = ((a : J)⁻¹ * γ (a : J)) * ((b : J)⁻¹ * γ (b : J)) := by group }
  have : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  have hcomm : IsMulCommutative ↥φ.range := by
    refine ⟨⟨fun u v => ?_⟩⟩
    obtain ⟨_, ⟨a, rfl⟩⟩ := u
    obtain ⟨_, ⟨b, rfl⟩⟩ := v
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcent (a : J))) (φ b)).symm
  have hsub : Subsingleton ↥φ.range := inferInstance
  intro y hy
  have h1 : (⟨φ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : ↥φ.range) = 1 := Subsingleton.elim _ _
  have h2 : φ ⟨y, hy⟩ = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.mp h2).symm

theorem exists_invariant_two_subgroup {f : ℕ} (hf : 2 ≤ f)
    (hJ : CentrallyUThree f J) {K K' : Subgroup J} (hKs : IsSimpleGroup ↥K)
    (hKp : Group.IsPerfect ↥K) (hK'p : Group.IsPerfect ↥K') {z : J} (hzK : z ∈ K) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (Γ : Set (MulAut J)) (hΓK : ∀ γ ∈ Γ, ∀ k ∈ K, γ k = k)
    (hΓ : ∃ γ ∈ Γ, ∃ y ∈ K', γ y ≠ y) :
    ∃ U : Subgroup J, IsPGroup 2 U ∧ (∀ γ ∈ Γ, U.map γ.toMonoidHom = U) ∧
      ∃ γ ∈ Γ, ∃ u ∈ U, γ u ≠ u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup J := Subgroup.center J with hZ
  set π : J →* J ⧸ Z := QuotientGroup.mk' Z with hπ
  have hmodel := statedClassicalModel_quot_center hf hJ
  obtain ⟨e⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hf hmodel
  have hB := CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e
  have hBG := CFSG.ComponentClassification.Asc76X.isBenderGroup_of_mulEquiv_psu3 hf e
  have hTI : ∀ {P Q : Sylow 2 (J ⧸ Z)}, P ≠ Q → (P : Subgroup (J ⧸ Z)) ⊓ Q = ⊥ := fun h =>
    CFSG.ComponentClassification.Asc76X.inf_eq_bot_of_fusionBenderBorel hB h
  have := hKp
  have := hK'p
  have hKZ : ∀ x ∈ K, x ∈ Z → x = 1 := by
    intro x hxK hxZ
    have hN : ((Subgroup.center J).subgroupOf K).Normal := inferInstance
    rcases hKs.eq_bot_or_eq_top_of_normal ((Subgroup.center J).subgroupOf K) with h | h
    · have hx : (⟨x, hxK⟩ : ↥K) ∈ (Subgroup.center J).subgroupOf K := hxZ
      rw [h] at hx
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hx)
    · exfalso
      have hcomm : IsMulCommutative ↥K := by
        refine ⟨⟨fun a b => ?_⟩⟩
        have ha : (a : J) ∈ Subgroup.center J := by
          have : a ∈ (Subgroup.center J).subgroupOf K := by rw [h]; exact Subgroup.mem_top a
          exact this
        exact Subtype.ext ((Subgroup.mem_center_iff.mp ha) (b : J)).symm
      have hsub : Subsingleton ↥K := inferInstance
      exact hz1 (congrArg Subtype.val (Subsingleton.elim (⟨z, hzK⟩ : ↥K) 1))
  have hπz1 : π z ≠ 1 := fun h => hz1 (hKZ z hzK ((QuotientGroup.eq_one_iff z).mp h))
  have hπz2 : π z ^ 2 = 1 := by rw [sq, ← map_mul, hz2, map_one]
  have hord : orderOf (π z) = 2 := orderOf_eq_prime hπz2 hπz1
  have hzp : IsPGroup 2 (Subgroup.zpowers (π z)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨Q, hQz⟩ := hzp.exists_le_sylow
  have hzQ : π z ∈ (Q : Subgroup (J ⧸ Z)) := hQz (Subgroup.mem_zpowers _)
  have huniq : ∀ Q' : Sylow 2 (J ⧸ Z), π z ∈ (Q' : Subgroup (J ⧸ Z)) → Q' = Q := by
    intro Q' hQ'
    by_contra hne
    have hbot := hTI hne
    have hmem : π z ∈ (Q' : Subgroup (J ⧸ Z)) ⊓ (Q : Subgroup (J ⧸ Z)) := ⟨hQ', hzQ⟩
    rw [hbot] at hmem
    exact hπz1 (Subgroup.mem_bot.mp hmem)
  have hqfix : ∀ γ ∈ Γ, quotAut γ (π z) = π z := by
    intro γ hγ
    show quotAut γ (QuotientGroup.mk z) = QuotientGroup.mk z
    rw [quotAut_mk, hΓK γ hγ z hzK]
  have hQinv : ∀ γ ∈ Γ, ∀ x ∈ (Q : Subgroup (J ⧸ Z)), quotAut γ x ∈ (Q : Subgroup (J ⧸ Z)) := by
    intro γ hγ x hx
    have hsm : (quotAut γ) • Q = Q := by
      apply huniq
      show π z ∈ (((quotAut γ) • Q : Sylow 2 (J ⧸ Z)) : Subgroup (J ⧸ Z))
      rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : (quotAut γ)⁻¹ • π z = π z := by
        rw [MulAut.smul_def, MulAut.inv_def, MulEquiv.symm_apply_eq]
        exact (hqfix γ hγ).symm
      rw [this]
      exact hzQ
    have : quotAut γ x ∈ (((quotAut γ) • Q : Sylow 2 (J ⧸ Z)) : Subgroup (J ⧸ Z)) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul x (quotAut γ) _ hx
    rwa [hsm] at this
  obtain ⟨U, hU2, hUmap, hUinv⟩ := exists_lift_two_subgroup (Q : Subgroup (J ⧸ Z)) Q.isPGroup'
  have hRinv : ∀ γ ∈ Γ, ((Q : Subgroup (J ⧸ Z)).comap π).map γ.toMonoidHom =
      (Q : Subgroup (J ⧸ Z)).comap π := by
    intro γ hγ
    have hle : ((Q : Subgroup (J ⧸ Z)).comap π).map γ.toMonoidHom ≤
        (Q : Subgroup (J ⧸ Z)).comap π := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π x ∈ (Q : Subgroup (J ⧸ Z)) := hx
      show π (γ x) ∈ (Q : Subgroup (J ⧸ Z))
      have : π (γ x) = quotAut γ (π x) := (quotAut_mk γ x).symm
      rw [this]
      exact hQinv γ hγ _ hx'
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective γ.injective]
  have hKmove : ∃ k ∈ K, π k ∉ Subgroup.normalizer ((Q : Subgroup (J ⧸ Z)) : Set (J ⧸ Z)) := by
    by_contra hcon
    push Not at hcon
    set R : Subgroup J := (Q : Subgroup (J ⧸ Z)).comap π with hR
    have hRK : (R.subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : π (n : J) ∈ (Q : Subgroup (J ⧸ Z)) := hn
      show π ((g * n * g⁻¹ : ↥K) : J) ∈ (Q : Subgroup (J ⧸ Z))
      have hg := hcon (g : J) g.2
      rw [Subgroup.mem_normalizer_iff] at hg
      have := (hg (π (n : J))).mp hn'
      simpa [map_mul, map_inv] using this
    rcases hKs.eq_bot_or_eq_top_of_normal (R.subgroupOf K) with h | h
    · have hz : (⟨z, hzK⟩ : ↥K) ∈ R.subgroupOf K := by
        show π z ∈ (Q : Subgroup (J ⧸ Z))
        exact hzQ
      rw [h] at hz
      exact hz1 (congrArg Subtype.val (Subgroup.mem_bot.mp hz))
    ·
      have hKR : ∀ k ∈ K, π k ∈ (Q : Subgroup (J ⧸ Z)) := by
        intro k hk
        have : (⟨k, hk⟩ : ↥K) ∈ R.subgroupOf K := by rw [h]; exact Subgroup.mem_top _
        exact this
      let fK : ↥K →* ↥(Q : Subgroup (J ⧸ Z)) := (π.comp K.subtype).codRestrict _ (fun k => hKR k k.2)
      have hfK : Function.Injective fK := by
        rw [injective_iff_map_eq_one]
        intro k hk
        have h1 : π (k : J) = 1 := by
          have := congrArg (fun y : ↥(Q : Subgroup (J ⧸ Z)) => (y : J ⧸ Z)) hk
          exact this
        exact Subtype.ext (hKZ k k.2 ((QuotientGroup.eq_one_iff _).mp h1))
      have hK2 : IsPGroup 2 ↥K := (Q.isPGroup').of_injective fK hfK
      have : Group.IsNilpotent ↥K := hK2.isNilpotent
      have hnt : Nontrivial ↥K := ⟨⟨⟨z, hzK⟩, 1, fun h' => hz1 (congrArg Subtype.val h')⟩⟩
      exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  refine ⟨U, hU2, fun γ hγ => hUinv γ (hRinv γ hγ), ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨γ₀, hγ₀, y, hyK', hγ₀y⟩ := hΓ
  have hfixQ : ∀ x ∈ (Q : Subgroup (J ⧸ Z)), quotAut γ₀ x = x := by
    intro x hx
    rw [← hUmap] at hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    show quotAut γ₀ (QuotientGroup.mk u) = QuotientGroup.mk u
    rw [quotAut_mk, hno γ₀ hγ₀ u hu]
  obtain ⟨c, hcQ, -, hγc⟩ := CFSG.ComponentClassification.Asc76X.exists_eq_conj_of_forall_apply_eq
    hBG Q (quotAut γ₀) hfixQ
  obtain ⟨k, hkK, hkn⟩ := hKmove
  have hc1 : c = 1 := by
    have h1 : quotAut γ₀ (π k) = π k := by
      show quotAut γ₀ (QuotientGroup.mk k) = QuotientGroup.mk k
      rw [quotAut_mk, hΓK γ₀ hγ₀ k hkK]
    rw [hγc, MulAut.conj_apply] at h1
    have hcomm : c * π k = π k * c := by
      calc c * π k = c * π k * c⁻¹ * c := by group
        _ = π k * c := by rw [h1]
    have hcmem : c ∈ (((π k) • Q : Sylow 2 (J ⧸ Z)) : Subgroup (J ⧸ Z)) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : (MulAut.conj (π k))⁻¹ • c = c := by
        rw [MulAut.smul_def, MulAut.inv_def, MulEquiv.symm_apply_eq, MulAut.conj_apply]
        calc c = π k * c * (π k)⁻¹ := by rw [← hcomm]; group
          _ = _ := rfl
      rw [this]
      exact hcQ
    have hne : (π k) • Q ≠ Q := fun h' => hkn (Sylow.smul_eq_iff_mem_normalizer.mp h')
    have hbot := hTI hne
    have hmem : c ∈ (((π k) • Q : Sylow 2 (J ⧸ Z)) : Subgroup (J ⧸ Z)) ⊓
        (Q : Subgroup (J ⧸ Z)) := ⟨hcmem, hcQ⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hid : ∀ x : J, QuotientGroup.mk' (Subgroup.center J) (γ₀ x) =
      QuotientGroup.mk' (Subgroup.center J) x := by
    intro x
    have h3 : quotAut γ₀ (π x) = π x := by
      rw [hγc, hc1]
      simp
    show QuotientGroup.mk (γ₀ x) = QuotientGroup.mk x
    exact (quotAut_mk γ₀ x).symm.trans h3
  exact hγ₀y (eq_of_forall_mk_eq hK'p γ₀ hid y hyK')

end CFSG.RankThree.PartOne.FIVES
