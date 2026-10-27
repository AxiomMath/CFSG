module

public import CFSG.Walter.ReeOrder.JT.AuxGroup

public section

namespace CFSG.Walter.JT

open CFSG

theorem commute_of_card_le_four {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) {x : X} (hx : IsPGroup p (Subgroup.zpowers x)) {R : Subgroup X}
    (hR : Nat.card R ≤ 4) (hxR : x ∈ Subgroup.normalizer (R : Set X)) :
    ∀ y ∈ R, x * y = y * x := by
  classical
  let c : Subgroup.zpowers x →* Equiv.Perm R :=
    { toFun := fun g =>
        { toFun := fun y => ⟨(g : X) * y * (g : X)⁻¹, by
            obtain ⟨k, hk⟩ := g.2
            rw [← hk]
            exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hxR k) y).mp y.2⟩
          invFun := fun y => ⟨(g : X)⁻¹ * y * g, by
            obtain ⟨k, hk⟩ := g.2
            have := (Subgroup.mem_normalizer_iff.mp
              (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hxR k)) y).mp y.2
            rw [← hk]
            simpa using this⟩
          left_inv := fun y => Subtype.ext (by simp [mul_assoc])
          right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by ext y; simp
      map_mul' := fun a b => by ext y; simp [mul_assoc] }
  have hx' : (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) ∈
      (⊤ : Subgroup (Subgroup.zpowers x)) := Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have h1 : orderOf (c ⟨x, Subgroup.mem_zpowers x⟩) ∣ p ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, hk, map_one]
  have h2 : orderOf (c ⟨x, Subgroup.mem_zpowers x⟩) ∣ 24 := by
    refine (orderOf_dvd_natCard _).trans ?_
    rw [Nat.card_perm]
    have : (Nat.card R).factorial ∣ (4 : ℕ).factorial := Nat.factorial_dvd_factorial hR
    exact this
  have hcop : Nat.Coprime (p ^ k) 24 := by
    refine Nat.Coprime.pow_left _ ?_
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) ?_
    · exact (Nat.coprime_primes hp.out Nat.prime_two).mpr (by omega)
    · exact (Nat.coprime_primes hp.out Nat.prime_three).mpr (by omega)
  have hσ : c ⟨x, Subgroup.mem_zpowers x⟩ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  intro y hy
  have := congrArg (fun σ : Equiv.Perm R => ((σ ⟨y, hy⟩ : R) : X)) hσ
  simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Equiv.Perm.coe_one,
    id_eq] at this
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [this]

theorem sylow_le_pCore_of_centralize_normal {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hX : Group.IsSolvable X)
    (hcomm : ∀ x : X, IsPGroup p (Subgroup.zpowers x) → ∀ q : ℕ, q.Prime → q ≠ p →
      ∀ R : Subgroup X, IsPGroup q R → (R ⊔ pCore p X).Normal →
        x ∈ Subgroup.normalizer (R : Set X) → ∀ y ∈ R, x * y = y * x)
    (P : Sylow p X) : (P : Subgroup X) ≤ pCore p X := by
  classical
  set U := pCore p X with hU
  set π := QuotientGroup.mk' U
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective U
  have hUp : IsPGroup p U := pCore_isPGroup
  have hcore : pCore p (X ⧸ U) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup p U hUp, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  have hsolvQ : Group.IsSolvable (X ⧸ U) := inferInstance
  have key : ∀ x : X, IsPGroup p (Subgroup.zpowers x) → π x = 1 := by
    intro x hx
    have hcen : Subgroup.zpowers (π x) ≤
        Subgroup.centralizer (fittingSubgroup (X ⧸ U) : Set (X ⧸ U)) := by
      refine subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun q => ?_
      have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have : Fact q.1.1.Prime := ⟨hq⟩
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      by_cases hqp : q.1.1 = p
      · intro y hy
        rw [hqp, hcore] at hy
        rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
      set Rt : Subgroup X := (pCore q.1.1 (X ⧸ U)).comap π
      have hRtn : Rt.Normal := pCore_normal.comap π
      obtain ⟨R₀⟩ : Nonempty (Sylow q.1.1 Rt) := inferInstance
      set R : Subgroup X := (R₀ : Subgroup Rt).map Rt.subtype
      have hRRt : R ≤ Rt := Subgroup.map_subtype_le _
      have hRq : IsPGroup q.1.1 R := R₀.isPGroup'.map _
      have hxRt : x ∈ Subgroup.normalizer (Rt : Set X) := Subgroup.le_normalizer_of_normal
        (Subgroup.mem_top x)
      obtain ⟨y, hyRt, hyx⟩ := exists_mul_mem_normalizer_of_sylow R₀ hxRt
      let πR : Rt →* pCore q.1.1 (X ⧸ U) := (π.comp Rt.subtype).codRestrict _ fun z => z.2
      have hπR : Function.Surjective πR := by
        rintro ⟨z, hz⟩
        obtain ⟨w, rfl⟩ := hπ z
        exact ⟨⟨w, hz⟩, rfl⟩
      have hRmap : ∀ z ∈ pCore q.1.1 (X ⧸ U), ∃ ρ ∈ R, π ρ = z := by
        intro z hz
        let S := Sylow.mapSurjective hπR R₀
        have hS : (S : Subgroup (pCore q.1.1 (X ⧸ U))) = ⊤ :=
          (S.is_maximal' (pCore_isPGroup.to_subgroup ⊤) le_top).symm
        have hzS : (⟨z, hz⟩ : pCore q.1.1 (X ⧸ U)) ∈ (S : Subgroup _) := hS ▸ Subgroup.mem_top _
        rw [Sylow.coe_mapSurjective] at hzS
        obtain ⟨w, hw, hwz⟩ := hzS
        exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwz⟩
      obtain ⟨ρ, hρR, hρy⟩ := hRmap (π y) hyRt
      have hu : ρ⁻¹ * y ∈ U := by
        rw [← QuotientGroup.ker_mk' U, MonoidHom.mem_ker, map_mul, map_inv, hρy, inv_mul_cancel]
      have hnN : ρ⁻¹ * y * x ∈ Subgroup.normalizer (R : Set X) := by
        rw [mul_assoc]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hρR)) hyx
      have hnp : IsPGroup p (Subgroup.zpowers (ρ⁻¹ * y * x)) := by
        have hsup : IsPGroup p (U ⊔ Subgroup.zpowers x : Subgroup X) :=
          IsPGroup.to_sup_of_normal_left' hUp hx (by
            intro g _
            exact Subgroup.le_normalizer_of_normal (Subgroup.mem_top g))
        refine hsup.to_le ?_
        rw [Subgroup.zpowers_le]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
      have hRU : R ⊔ U = Rt := by
        refine le_antisymm (sup_le hRRt fun u hu => ?_) fun z hz => ?_
        · change π u ∈ pCore q.1.1 (X ⧸ U)
          rw [show π u = 1 from (QuotientGroup.eq_one_iff u).mpr hu]
          exact Subgroup.one_mem _
        · obtain ⟨ρ', hρ'R, hρ'z⟩ := hRmap (π z) hz
          have hρz : ρ'⁻¹ * z ∈ U := by
            rw [← QuotientGroup.ker_mk' U, MonoidHom.mem_ker, map_mul, map_inv, ← hρ'z,
              inv_mul_cancel]
          rw [show z = ρ' * (ρ'⁻¹ * z) by group]
          exact Subgroup.mul_mem_sup hρ'R hρz
      have hRUn : (R ⊔ U).Normal := hRU ▸ hRtn
      have hncomm := hcomm _ hnp q.1.1 hq hqp R hRq hRUn hnN
      have hπu : π (ρ⁻¹ * y) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hu
      have hπn : π (ρ⁻¹ * y * x) = π x := by
        rw [map_mul, hπu, one_mul]
      intro z hz
      obtain ⟨ρ', hρ'R, rfl⟩ := hRmap z hz
      rw [← hπn, ← map_mul, ← map_mul, hncomm ρ' hρ'R]
    have hF := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolvQ
      (hcen (Subgroup.mem_zpowers (π x)))
    have hzp : IsPGroup p (Subgroup.zpowers (π x)) := by
      rw [← MonoidHom.map_zpowers]
      exact hx.map π
    have hzF : Subgroup.zpowers (π x) ≤ fittingSubgroup (X ⧸ U) := by
      rw [Subgroup.zpowers_le]
      exact hF
    obtain ⟨S, hS⟩ := (hzp.comap_subtype (K := fittingSubgroup (X ⧸ U))).exists_le_sylow
    have hle := Sylow.map_le_pCore (inferInstance : (fittingSubgroup (X ⧸ U)).Normal)
      inferInstance p S
    rw [hcore] at hle
    have hmem : π x ∈ (S : Subgroup _).map (fittingSubgroup (X ⧸ U)).subtype :=
      ⟨⟨π x, hF⟩, hS (by
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_zpowers _), rfl⟩
    exact Subgroup.mem_bot.mp (hle hmem)
  intro x hxP
  have hx : IsPGroup p (Subgroup.zpowers x) := by
    have := P.isPGroup'.to_le ((Subgroup.zpowers_le).mpr hxP)
    exact this
  have := key x hx
  rw [← QuotientGroup.ker_mk' U, MonoidHom.mem_ker]
  exact this

theorem sylow_le_pCore_of_centralize {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hX : Group.IsSolvable X)
    (hcomm : ∀ x : X, IsPGroup p (Subgroup.zpowers x) → ∀ q : ℕ, q.Prime → q ≠ p →
      ∀ R : Subgroup X, IsPGroup q R → x ∈ Subgroup.normalizer (R : Set X) →
        ∀ y ∈ R, x * y = y * x)
    (P : Sylow p X) : (P : Subgroup X) ≤ pCore p X :=
  sylow_le_pCore_of_centralize_normal hX
    (fun x hx q hq hqp R hR _ hxR => hcomm x hx q hq hqp R hR hxR) P

end CFSG.Walter.JT
