module

public import CFSG.Quasithin.Background.RonanH412Chief
public import CFSG.Quasithin.Background.RonanH412Core
public import CFSG.Quasithin.Background.RonanH412Three

public section

namespace CFSG.Quasithin.RonanH412

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Quasithin.RonanH49

theorem wmod_sq (a : WMod) : a * a = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem exists_gen_of_card_three {G : Type*} [Group G] {Y : Subgroup G} (hY : Nat.card Y = 3) :
    ∃ y ∈ Y, y ≠ 1 ∧ y ^ 3 = 1 ∧ Subgroup.zpowers y = Y := by
  haveI : Finite ↥Y := Nat.finite_of_card_ne_zero (by omega)
  have hne : Y ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hY
    omega
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hdvd : orderOf y ∣ 3 := hY ▸ Subgroup.orderOf_dvd_natCard Y hy
  have hord : orderOf y = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left fun h => hy1' (orderOf_eq_one_iff.1 h)
  have hpow : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hord] at this
  refine ⟨y, hy, hy1', hpow, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hy) ?_⟩
  rw [Nat.card_zpowers, hord, hY]

theorem zpow_cases_of_pow_three {G : Type*} [Group G] {y : G} (hy : y ^ 3 = 1) (k : ℤ) :
    y ^ k = 1 ∨ y ^ k = y ∨ y ^ k = y * y := by
  have hk : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
  have h3 : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy
  have hmod : y ^ k = y ^ (k % 3) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h <;> rw [hmod, h]
  · exact Or.inl (zpow_zero y)
  · exact Or.inr (Or.inl (zpow_one y))
  · exact Or.inr (Or.inr (zpow_two y))

theorem card_wmod : Nat.card WMod = 2 ^ 9 := by
  show Nat.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 2 ^ 9
  rw [Matrix.card_matrix, Nat.card_zmod, Nat.card_fin] <;> norm_num

theorem h412_one {Y : Subgroup (MulAut WMod)} (hY : Y ≤ GW) (hcard : Nat.card Y = 3) :
    HasChiefCount {f | ∃ y ∈ Y, f = fun v => y v} ⊤ 3 := by
  obtain ⟨y, hyY, hy1, hy3, hgen⟩ := exists_gen_of_card_three hcard
  have hynorm : y ∈ norm := by
    rw [← GW_eq_norm]
    exact hY hyY
  let ψ : WMod →* WMod := (y : MulAut WMod).toMonoidHom
  have hset : {f | ∃ y' ∈ Y, f = fun v => y' v} = powMaps ψ := by
    ext f
    constructor
    · rintro ⟨y', hy', rfl⟩
      rw [← hgen] at hy'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
      rcases zpow_cases_of_pow_three hy3 k with h | h | h
      · left
        funext v
        show (y ^ k) v = v
        rw [h]
        rfl
      · right
        left
        funext v
        show (y ^ k) v = y v
        rw [h]
      · right
        right
        funext v
        show (y ^ k) v = y (y v)
        rw [h]
        rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, Y.one_mem, rfl⟩
      · exact ⟨y, hyY, rfl⟩
      · exact ⟨y * y, Y.mul_mem hyY hyY, rfl⟩
  have hψ3 : ∀ a : WMod, ψ (ψ (ψ a)) = a := by
    intro a
    have h : y * (y * y) = 1 := by
      rw [← pow_three]
      exact hy3
    exact congrArg (fun z : MulAut WMod => z a) h
  have hfix : fixSub ψ ⊤ = fixV (Subgroup.zpowers y) := by
    ext v
    constructor
    · rintro ⟨-, h⟩
      exact mem_fixV_zpowers.2 h
    · intro h
      exact ⟨Subgroup.mem_top _, mem_fixV_zpowers.1 h⟩
  have h8 : Nat.card ↥(fixSub ψ ⊤) = 8 := by
    rw [hfix]
    exact card_fixV_eq_eight_of_three hynorm hy3 hy1
  have hc : Nat.card WMod = 4 ^ 3 * Nat.card ↥(fixSub ψ ⊤) := by
    rw [h8, card_wmod]
    norm_num
  rw [hset]
  exact exists_hasChiefCount wmod_sq hψ3 3 hc

theorem h412_two {P : Subgroup (MulAut WMod)} (hP1 : P ≤ stabE) (hP0 : P ≤ img)
    (hPa : ¬ P ≤ ((⊤ : Subgroup ↥SL32).prod ⊥).map rho)
    (hPb : ¬ P ≤ ((⊥ : Subgroup ↥SL32).prod ⊤).map rho) (hcard : Nat.card P = 3) :
    HasChiefCount {f | ∃ p ∈ P, f = fun u => p * u * p⁻¹} (CFSG.Open.pCoreOf 2 stabE) 2 := by
  obtain ⟨p, hpP, hp1, hp3, hgen⟩ := exists_gen_of_card_three hcard
  obtain ⟨⟨a, b⟩, hab⟩ := hP0 hpP
  subst hab
  have hpS : rho (a, b) ∈ stabE := hP1 hpP
  obtain ⟨ha1P, hb1P⟩ := mem_P1_of_rho_E00 (a := a) (b := b) (mem_stabE_iff.1 hpS).2
  have hab3 : (a, b) ^ 3 = 1 := rho_injective (by rw [map_pow, hp3, map_one])
  have ha3 : a ^ 3 = 1 := by simpa using congrArg Prod.fst hab3
  have hb3 : b ^ 3 = 1 := by simpa using congrArg Prod.snd hab3
  have ha1 : a ≠ 1 := fun h => hPb (by
    subst h
    rw [← hgen]
    exact Subgroup.zpowers_le.2 ⟨(1, b), Subgroup.mem_prod.2 ⟨Subgroup.one_mem _,
      Subgroup.mem_top _⟩, rfl⟩)
  have hb1 : b ≠ 1 := fun h => hPa (by
    subst h
    rw [← hgen]
    exact Subgroup.zpowers_le.2 ⟨(a, 1), Subgroup.mem_prod.2 ⟨Subgroup.mem_top _,
      Subgroup.one_mem _⟩, rfl⟩)
  letI : CommGroup ↥Shat :=
    { (inferInstance : Group ↥Shat) with
      mul_comm := fun x y => Subtype.ext (Shat_comm x.2 y.2) }
  let φ : MulAut WMod →* MulAut WMod := (MulAut.conj (rho (a, b))).toMonoidHom
  let ψ : ↥Shat →* ↥Shat :=
    MonoidHom.codRestrict (φ.comp Shat.subtype) Shat (fun s => conj_mem_Shat hpS s.2)
  have hcomm : ∀ s : ↥Shat, Shat.subtype (ψ s) = φ (Shat.subtype s) := fun s => rfl
  have hsq : ∀ s : ↥Shat, s * s = 1 := fun s => Subtype.ext (mul_self_eq_one_of_mem_Shat s.2)
  have hψ3 : ∀ s : ↥Shat, ψ (ψ (ψ s)) = s := by
    intro s
    apply Subtype.ext
    have h3 : rho (a, b) * (rho (a, b) * rho (a, b)) = 1 := by
      rw [← pow_three]
      exact hp3
    change rho (a, b) * (rho (a, b) * (rho (a, b) * (s : MulAut WMod) * (rho (a, b))⁻¹) *
      (rho (a, b))⁻¹) * (rho (a, b))⁻¹ = s
    calc rho (a, b) * (rho (a, b) * (rho (a, b) * (s : MulAut WMod) * (rho (a, b))⁻¹) *
          (rho (a, b))⁻¹) * (rho (a, b))⁻¹
        = (rho (a, b) * (rho (a, b) * rho (a, b))) * (s : MulAut WMod) *
            (rho (a, b) * (rho (a, b) * rho (a, b)))⁻¹ := by group
      _ = s := by rw [h3]; group
  have hfix : fixSub ψ ⊤ = ⊥ := by
    ext s
    constructor
    · rintro ⟨-, h⟩
      refine Subgroup.mem_bot.2 (Subtype.ext ?_)
      exact Shat_fixed_trivial ha1P hb1P ha3 hb3 ha1 hb1 s.2 (congrArg Subtype.val h)
    · intro h
      rw [Subgroup.mem_bot] at h
      subst h
      exact ⟨Subgroup.mem_top _, map_one ψ⟩
  have hc : Nat.card ↥Shat = 4 ^ 2 * Nat.card ↥(fixSub ψ ⊤) := by
    rw [hfix, Subgroup.card_bot, card_Shat]
    norm_num
  have h := exists_hasChiefCount (A := ↥Shat) hsq hψ3 2 hc
  have h' := hasChiefCount_map (ι := Shat.subtype) Subtype.val_injective hcomm h
  have hset : {f | ∃ p' ∈ P, f = fun u => p' * u * p'⁻¹} = powMaps φ := by
    ext f
    constructor
    · rintro ⟨p', hp', rfl⟩
      rw [← hgen] at hp'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp'
      rcases zpow_cases_of_pow_three hp3 k with h | h | h
      · left
        funext u
        show (rho (a, b)) ^ k * u * ((rho (a, b)) ^ k)⁻¹ = u
        rw [h]
        group
      · right
        left
        funext u
        show (rho (a, b)) ^ k * u * ((rho (a, b)) ^ k)⁻¹ = rho (a, b) * u * (rho (a, b))⁻¹
        rw [h]
      · right
        right
        funext u
        show (rho (a, b)) ^ k * u * ((rho (a, b)) ^ k)⁻¹ =
          rho (a, b) * (rho (a, b) * u * (rho (a, b))⁻¹) * (rho (a, b))⁻¹
        rw [h]
        group
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, P.one_mem, by funext u; simp⟩
      · exact ⟨rho (a, b), hpP, rfl⟩
      · refine ⟨rho (a, b) * rho (a, b), P.mul_mem hpP hpP, ?_⟩
        funext u
        show rho (a, b) * (rho (a, b) * u * (rho (a, b))⁻¹) * (rho (a, b))⁻¹ =
          rho (a, b) * rho (a, b) * u * (rho (a, b) * rho (a, b))⁻¹
        group
  rw [hset, pCoreOf_stabE]
  rw [Subgroup.range_subtype] at h'
  exact h'

end CFSG.Quasithin.RonanH412
