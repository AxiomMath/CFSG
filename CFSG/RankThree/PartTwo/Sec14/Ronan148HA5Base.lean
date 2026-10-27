module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HTheta

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

section Gen

variable {X : Type} [Group X] [Finite X]

theorem le_centralizer_of_card_le_four {M N : Subgroup X} (hMp : Group.IsPerfect M)
    (hMN : M ≤ Subgroup.normalizer (N : Set X)) (hN4 : Nat.card N ≤ 4) :
    M ≤ Subgroup.centralizer (N : Set X) := by
  letI : MulDistribMulAction M N := Subgroup.conjMulDistribMulActionOfLeNormalizer M N hMN
  let φ : ↥M →* Equiv.Perm ↥N := MulAction.toPermHom ↥M ↥N
  have hdvd : Nat.card φ.range ∣ 24 := by
    have h1 : Nat.card φ.range ∣ Nat.card (Equiv.Perm ↥N) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm] at h1
    refine h1.trans ?_
    have : Nat.card N ≤ 4 := hN4
    interval_cases h : Nat.card N <;> decide
  have hsolv : Group.IsSolvable φ.range := by
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.mp (show Nat.card φ.range ∣ 2 ^ 3 * 3 ^ 1 from hdvd)
    obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk₁
    obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hk₂
    have : Fintype φ.range := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := a) (b := b)
      Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hk])
  have hperf : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable φ.range hsolv
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have h1 : φ ⟨m, hm⟩ = 1 := by
    rw [← Subgroup.mem_bot, ← hbot]
    exact ⟨⟨m, hm⟩, rfl⟩
  have h2 := congrArg (fun σ : Equiv.Perm ↥N => ((σ ⟨n, hn⟩ : ↥N) : X)) h1
  simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at h2
  have hsm : (((⟨m, hm⟩ : ↥M) • (⟨n, hn⟩ : ↥N) : ↥N) : X) = m * n * m⁻¹ :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit M N hMN ⟨m, hm⟩ ⟨n, hn⟩
  have h3 : m * n * m⁻¹ = n := hsm.symm.trans h2
  calc n * m = m * n * m⁻¹ * m := by rw [h3]
    _ = m * n := by group

theorem card_eq_one_or_four {N : Subgroup X} {q : X} (hq3 : q ^ 3 = 1)
    (hqN : q ∈ Subgroup.normalizer (N : Set X)) (hN4 : Nat.card N ≤ 4)
    (hfix : N ⊓ Subgroup.centralizer ({q} : Set X) = ⊥) : Nat.card N = 1 ∨ Nat.card N = 4 := by
  have hzN : Subgroup.zpowers q ≤ Subgroup.normalizer (N : Set X) := Subgroup.zpowers_le.mpr hqN
  letI : MulDistribMulAction (Subgroup.zpowers q) N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer _ N hzN
  have hp : IsPGroup 3 (Subgroup.zpowers q) := by
    rw [IsPGroup.iff_card]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hq3) with h | h
    · exact ⟨0, by rw [Nat.card_zpowers, h, pow_zero]⟩
    · exact ⟨1, by rw [Nat.card_zpowers, h, pow_one]⟩
  have hmod := hp.card_modEq_card_fixedPoints ↥N
  have hfp : Nat.card (MulAction.fixedPoints (Subgroup.zpowers q) ↥N) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun g => smul_one g⟩, fun ⟨x, hx⟩ => Subtype.ext ?_⟩
    have hxq : (x : X) ∈ Subgroup.centralizer ({q} : Set X) := by
      have h1 := hx ⟨q, Subgroup.mem_zpowers q⟩
      have h2 : q * (x : X) * q⁻¹ = x := congrArg Subtype.val h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : X) * q = q * x * q⁻¹ * q := by rw [h2]
        _ = q * x := by group
    have : (x : X) ∈ N ⊓ Subgroup.centralizer ({q} : Set X) := ⟨x.2, hxq⟩
    rw [hfix, Subgroup.mem_bot] at this
    exact Subtype.ext this
  rw [hfp] at hmod
  have hpos : 0 < Nat.card N := Nat.card_pos
  interval_cases h : Nat.card N
  · left; rfl
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · right; rfl

theorem mem_normalizer_of_forall_commute {a : X} {K : Subgroup X}
    (h : ∀ k ∈ K, a * k = k * a) : a ∈ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [show a * k * a⁻¹ = k by rw [h k hk]; group]
    exact hk
  · intro hk
    have h1 : a * (a * k * a⁻¹) = a * k * a⁻¹ * a := h _ hk
    have : a * k * a⁻¹ = k := by
      calc a * k * a⁻¹ = a⁻¹ * (a * (a * k * a⁻¹)) := by group
        _ = a⁻¹ * (a * k * a⁻¹ * a) := by rw [h1]
        _ = k := by group
    rw [← this]
    exact hk

theorem le_of_isPerfect_of_le_sup {F A K : Subgroup X} (hFp : Group.IsPerfect F)
    (hF : F ≤ A ⊔ K) (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : F ≤ K := by
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := fun a ha =>
    mem_normalizer_of_forall_commute (hAK a ha)
  have hcomm : ⁅A ⊔ K, A ⊔ K⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : x ∈ ((A : Set X) * (K : Set X)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A K hAN]; exact hx
    have hy' : y ∈ ((A : Set X) * (K : Set X)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A K hAN]; exact hy
    obtain ⟨a, ha, k, hk, rfl⟩ := hx'
    obtain ⟨b, hb, l, hl, rfl⟩ := hy'
    show a * k * (b * l) * (a * k)⁻¹ * (b * l)⁻¹ ∈ K
    have hbk : b * k = k * b := hAK b hb k hk
    have hab : a * b = b * a := hA a ha b hb
    have hcen : ∀ c ∈ A, ∀ y ∈ K, c * y * c⁻¹ = y := fun c hc y hy => by
      rw [hAK c hc y hy]; group
    have e1 : a * k * (b * l) * (a * k)⁻¹ * (b * l)⁻¹ =
        a * (b * (k * l * k⁻¹) * b⁻¹) * a⁻¹ * (b * l⁻¹ * b⁻¹) * (b * a * b⁻¹ * a⁻¹) := by
      have : b * a * b⁻¹ * a⁻¹ = 1 := by rw [← hab]; group
      rw [this, mul_one]
      calc a * k * (b * l) * (a * k)⁻¹ * (b * l)⁻¹
          = a * (k * b) * l * k⁻¹ * a⁻¹ * l⁻¹ * b⁻¹ := by group
        _ = a * (b * k) * l * k⁻¹ * a⁻¹ * l⁻¹ * b⁻¹ := by rw [hbk]
        _ = a * (b * (k * l * k⁻¹) * b⁻¹) * a⁻¹ * (b * l⁻¹ * b⁻¹) := by
            rw [show b * l⁻¹ * b⁻¹ = l⁻¹ from hcen b hb _ (K.inv_mem hl)]
            have h2 : a * b = b * a := hab
            rw [show a * (b * (k * l * k⁻¹) * b⁻¹) * a⁻¹ * l⁻¹ =
              a * (b * (k * l * k⁻¹) * b⁻¹) * a⁻¹ * l⁻¹ from rfl]
            rw [hcen b hb _ (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk))]
            rw [hcen a ha _ (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)) |>
              fun h => (show a * (k * l * k⁻¹) * a⁻¹ * l⁻¹ = (k * l * k⁻¹) * l⁻¹ by rw [h])]
            have h3 : a * (b * k) * l * k⁻¹ * a⁻¹ * l⁻¹ * b⁻¹ =
                a * b * (k * l * k⁻¹) * a⁻¹ * (l⁻¹ * b⁻¹) := by group
            rw [h3, h2]
            have h4 : b * a * (k * l * k⁻¹) * a⁻¹ * (l⁻¹ * b⁻¹) =
                b * (a * (k * l * k⁻¹) * a⁻¹) * l⁻¹ * b⁻¹ := by group
            rw [h4, hcen a ha _ (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk))]
            have h5 : b * (k * l * k⁻¹) * l⁻¹ * b⁻¹ = b * (k * l * k⁻¹ * l⁻¹) * b⁻¹ := by group
            rw [h5, hcen b hb _ (K.mul_mem (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk))
              (K.inv_mem hl))]
    rw [e1, hcen b hb _ (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)),
      hcen a ha _ (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)),
      hcen b hb _ (K.inv_mem hl), show b * a * b⁻¹ * a⁻¹ = 1 by rw [← hab]; group, mul_one]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)) (K.inv_mem hl)
  have hF' : ⁅F, F⁆ = F := Subgroup.isPerfect_iff.mp hFp
  rw [← hF']
  exact (Subgroup.commutator_mono hF hF).trans hcomm

theorem mem_of_mem_sup_of_pow {q x : X} {K : Subgroup X} (hq3 : q ^ 3 = 1)
    (hqK : ∀ k ∈ K, q * k = k * q) (hI : Subgroup.zpowers q ⊓ K = ⊥)
    (hx : x ∈ Subgroup.zpowers q ⊔ K) {n : ℕ} (hn : Nat.Coprime n 3) (hxn : x ^ n = 1) : x ∈ K := by
  have hAN : Subgroup.zpowers q ≤ Subgroup.normalizer (K : Set X) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_forall_commute hqK)
  have hx' : x ∈ ((Subgroup.zpowers q : Set X) * (K : Set X)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ K hAN]; exact hx
  obtain ⟨y, hy, k, hk, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  show q ^ i * k ∈ K
  have hcomm : Commute (q ^ i) k := Commute.zpow_left (hqK k hk) i
  have hxn' : (q ^ i * k) ^ n = 1 := hxn
  rw [hcomm.mul_pow] at hxn'
  have h1 : (q ^ i) ^ n = (k ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hxn'
  have h2 : (q ^ i) ^ n ∈ Subgroup.zpowers q ⊓ K :=
    ⟨Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers q i) _, h1 ▸ K.inv_mem (K.pow_mem hk _)⟩
  rw [hI, Subgroup.mem_bot] at h2
  have h3 : (q ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq3, one_zpow]
  have h4 : q ^ i = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    rwa [hn.gcd_eq_one, pow_one] at this
  rw [h4, one_mul]
  exact hk

theorem exists_rho {K : Subgroup X}
    (hK : IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)))
    (hZK : Subgroup.center X ≤ K) (hZ3 : Nat.card (Subgroup.center X) = 3) :
    ∃ ρ : ↥K →* ↥(alternatingGroup (Fin 6)), ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ Subgroup.center X := by
  obtain ⟨Z', hZ'n, ⟨eZ⟩, ⟨eQ⟩⟩ := hK
  have hZ'3 : Nat.card Z' = 3 := by
    rw [Nat.card_congr eZ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  let ρ : ↥K →* ↥(alternatingGroup (Fin 6)) := eQ.toMonoidHom.comp (QuotientGroup.mk' Z')
  have hρker : ∀ k : ↥K, ρ k = 1 ↔ k ∈ Z' := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hρs : Function.Surjective ρ := eQ.surjective.comp (QuotientGroup.mk'_surjective Z')
  set C := (Subgroup.center X).subgroupOf K with hCdef
  have hC3 : Nat.card C = 3 := by
    rw [hCdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZ3]
  have hCn : C.Normal := ⟨fun n hn g => by
    rw [hCdef, Subgroup.mem_subgroupOf] at hn ⊢
    have : (g : X) * n * (g : X)⁻¹ = n := by
      rw [(Subgroup.mem_center_iff.mp hn) g]; group
    simpa using this.symm ▸ hn⟩
  have hCZ : C ≤ Z' := by
    intro k hk
    by_contra hkZ
    have hS : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases (hCn.map ρ hρs).eq_bot_or_eq_top with hb | ht
    · have : ρ k ∈ C.map ρ := Subgroup.mem_map_of_mem ρ hk
      rw [hb, Subgroup.mem_bot] at this
      exact hkZ ((hρker k).mp this)
    · have h1 : Nat.card (C.map ρ) ∣ Nat.card C := Subgroup.card_map_dvd C ρ
      rw [ht, Subgroup.card_top, hC3, nat_card_alternatingGroup, Nat.card_fin] at h1
      norm_num [Nat.factorial] at h1
  have hCeq : C = Z' := Subgroup.eq_of_le_of_card_ge hCZ (by rw [hC3, hZ'3])
  refine ⟨ρ, fun k => ?_⟩
  rw [hρker, ← hCeq, hCdef, Subgroup.mem_subgroupOf]

end Gen

structure A5Cfg {X : Type} [Group X] [Finite X] (P : Subgroup X) (q : X) (M F : Subgroup X) :
    Prop where
  perf : Group.IsPerfect X
  triple : IsTripleCover X CFSG.Blueprint.NativeSporadic.ON
  e27 : Late.IsE27 P
  qP : q ∈ P
  qZ : q ∉ Subgroup.center X
  PM : P ≤ Subgroup.normalizer (M : Set X)
  Mp : Group.IsPerfect M
  Mq : IsQuasisimple (M ⧸ aschbacherSolvableCore 3 M)
  FM : F ≤ M
  Fq : F ≤ Subgroup.centralizer ({q} : Set X)
  Fp : Group.IsPerfect F
  FA5 : Nonempty (F ⧸ aschbacherSolvableCore 3 F ≃* alternatingGroup (Fin 5))
  qs : q ∉ Late.sectionCentralizer P M (inSubgroup (aschbacherSolvableCore 3) M)

namespace A5Cfg

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P : Subgroup X} {q : X} {M F : Subgroup X}

noncomputable abbrev thetaM (M : Subgroup X) : Subgroup X := inSubgroup (aschbacherSolvableCore 3) M

theorem thetaM_le (M : Subgroup X) : thetaM M ≤ M := Subgroup.map_subtype_le _

theorem not_three_dvd_thetaM (M : Subgroup X) : ¬ 3 ∣ Nat.card (thetaM M) := by
  rw [thetaM, inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
  exact (solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three).2.2.1

theorem le_normalizer_thetaM (h : A5Cfg P q M F) : P ≤ Subgroup.normalizer (thetaM M : Set X) :=
  h.PM.trans (Sec6.normalizer_le_normalizer_theta M)

theorem card_thetaM_le (h : A5Cfg P q M F) : Nat.card (thetaM M) ≤ 4 :=
  card_le_four_of_le_normalizer h.perf h.triple h.e27 h.le_normalizer_thetaM
    (not_three_dvd_thetaM M)

theorem isPGroup_thetaM (h : A5Cfg P q M F) : IsPGroup 2 (thetaM M) :=
  isPGroup_two_of_le_normalizer h.perf h.triple h.e27 h.le_normalizer_thetaM
    (not_three_dvd_thetaM M)

theorem le_centralizer_thetaM (h : A5Cfg P q M F) :
    M ≤ Subgroup.centralizer (thetaM M : Set X) :=
  le_centralizer_of_card_le_four h.Mp (Sec6.le_normalizer_theta M) h.card_thetaM_le

theorem q_cube (h : A5Cfg P q M F) : q ^ 3 = 1 := h.e27.1.2 q h.qP

theorem not_mem_center_of_cube (h : A5Cfg P q M F) {f : ↥F} (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1)
    (hfc : f ∈ Subgroup.center ↥F) : False := by
  obtain ⟨e⟩ := h.FA5
  obtain ⟨-, hθc, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥F) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 ↥F).Normal := by haveI := hθc; infer_instance
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥F)
  have hc5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  have h1 : e (π f) ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥F) y
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hfc x]
  rw [hc5, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
  have hmem : f ∈ aschbacherSolvableCore 3 ↥F := (QuotientGroup.eq_one_iff f).mp h1
  have hord : orderOf (⟨f, hmem⟩ : aschbacherSolvableCore 3 ↥F) = 3 := by
    rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime hf3 hf1
  have := orderOf_dvd_natCard (⟨f, hmem⟩ : aschbacherSolvableCore 3 ↥F)
  rw [hord] at this
  exact hθ3 this

theorem three_dvd_card_F (h : A5Cfg P q M F) : 3 ∣ Nat.card F := by
  obtain ⟨e⟩ := h.FA5
  have h60 : Nat.card (↥F ⧸ aschbacherSolvableCore 3 ↥F) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; rfl
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥F)
  rw [h60] at this
  rw [this]
  exact Dvd.dvd.mul_right (by norm_num) _

theorem le_K (h : A5Cfg P q M F) {K : Subgroup X}
    (hC : Subgroup.centralizer ({q} : Set X) = Subgroup.zpowers q ⊔ K) : F ≤ K := by
  have hKq : K ≤ Subgroup.centralizer ({q} : Set X) := hC ▸ le_sup_right
  refine le_of_isPerfect_of_le_sup h.Fp (hC ▸ h.Fq) (fun a ha k hk => ?_) (fun a ha b hb => ?_)
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hKq hk)).symm i)
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self q i j)

theorem inf_centralizer_theta (h : A5Cfg P q M F) :
    thetaM M ⊓ Subgroup.centralizer ({q} : Set X) = ⊥ := by
  obtain ⟨K, hK, hC, hI, hZK⟩ := exists_centralizer_eq h.perf h.triple h.e27 h.qP h.qZ
  obtain ⟨ρ, hρ⟩ := exists_rho hK hZK h.triple.1
  have hFK := h.le_K hC
  have hKq : ∀ k ∈ K, q * k = k * q := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp ((hC ▸ le_sup_right : K ≤ _) hk)).symm
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 3 h.three_dvd_card_F
  have hf3 : f ^ 3 = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  have hf1 : f ≠ 1 := by rintro rfl; rw [orderOf_one] at hf; norm_num at hf
  have hfZ : (f : X) ∉ Subgroup.center X := by
    intro hfZ
    refine h.not_mem_center_of_cube hf3 hf1 (Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_)
    exact Subgroup.mem_center_iff.mp hfZ g
  set f' : ↥K := ⟨f, hFK f.2⟩ with hf'
  have hρf1 : (ρ f' : Equiv.Perm (Fin 6)) ≠ 1 := fun h1 => hfZ ((hρ f').mp (Subtype.ext h1))
  have hρf3 : (ρ f' : Equiv.Perm (Fin 6)) ^ 3 = 1 := by
    have : f' ^ 3 = 1 := Subtype.ext (by simpa using congrArg Subtype.val hf3)
    have h' : ρ f' ^ 3 = 1 := by rw [← map_pow, this, map_one]
    exact congrArg Subtype.val h'
  rw [eq_bot_iff]
  rintro x ⟨hxθ, hxq⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := h.isPGroup_thetaM ⟨x, hxθ⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have hxK : x ∈ K := mem_of_mem_sup_of_pow h.q_cube hKq hI (hC ▸ hxq) hcop hxk
  set x' : ↥K := ⟨x, hxK⟩ with hx'
  have hxf : x' * f' = f' * x' := Subtype.ext ((Subgroup.mem_centralizer_iff.mp
    (h.le_centralizer_thetaM (h.FM f.2))) x hxθ)
  have hρx3 : (ρ x' : Equiv.Perm (Fin 6)) ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup.alt_six_centralizer_cube
      _ hρf3 hρf1 (Equiv.Perm.mem_alternatingGroup.mp (ρ f').2) _
      (Equiv.Perm.mem_alternatingGroup.mp (ρ x').2)
      (by
        have := congrArg (fun u : ↥(alternatingGroup (Fin 6)) => (u : Equiv.Perm (Fin 6)))
          (show ρ x' * ρ f' = ρ f' * ρ x' by rw [← map_mul, ← map_mul, hxf])
        simpa using this)
  have hρxk : ρ x' ^ 2 ^ k = 1 := by
    rw [← map_pow, show x' ^ 2 ^ k = 1 from Subtype.ext (by simpa using hxk), map_one]
  have hρx : ρ x' = 1 := by
    have h3 : ρ x' ^ 3 = 1 := Subtype.ext (by simpa using hρx3)
    have := pow_gcd_eq_one.mpr ⟨hρxk, h3⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hxZ : x ∈ Subgroup.center X := (hρ x').mp hρx
  have hx3 : x ^ 3 = 1 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hxZ
    rw [h.triple.1] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have := pow_gcd_eq_one.mpr ⟨hxk, hx3⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem card_theta (h : A5Cfg P q M F) : Nat.card (thetaM M) = 1 ∨ Nat.card (thetaM M) = 4 :=
  card_eq_one_or_four h.q_cube (h.le_normalizer_thetaM h.qP) h.card_thetaM_le
    h.inf_centralizer_theta

end A5Cfg

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
