module

public import CFSG.Walter.W67.Section5.P56AbBasic
public import CFSG.Walter.W67.Section5.Sylow52

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

noncomputable abbrev φ : d.NV →* MulAut d.V := conjAut d.NV d.V le_rfl

theorem φ_apply_coe (x : d.NV) (m : d.V) : ((d.φ x m : d.V) : G) = (x : G) * m * (x : G)⁻¹ :=
  rfl

theorem φ_eq_one_iff (x : d.NV) : d.φ x = 1 ↔ (x : G) ∈ d.CV := by
  rw [conjAut_eq_one_iff, Subgroup.mem_centralizer_iff]
  exact ⟨fun h m hm => (h m hm).symm, fun h m hm => (h m hm).symm⟩

theorem ker_φ : d.φ.ker = d.CV.subgroupOf d.NV := by
  ext x
  rw [MonoidHom.mem_ker, φ_eq_one_iff, Subgroup.mem_subgroupOf]

theorem φ_eq_iff (x y : d.NV) : d.φ x = d.φ y ↔ (y : G)⁻¹ * x ∈ d.CV := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, φ_eq_one_iff]
  constructor
  · intro h
    have := (Subgroup.mem_normalizer_iff.mp (d.mem_normalizer_CV (y⁻¹ : d.NV).2) _).mp h
    simpa [mul_assoc] using this
  · intro h
    have := (Subgroup.mem_normalizer_iff.mp (d.mem_normalizer_CV y.2) _).mp h
    simpa [mul_assoc] using this

noncomputable abbrev Nbar : Subgroup (MulAut d.V) := d.φ.range

noncomputable abbrev bar (X : Subgroup G) : Subgroup (MulAut d.V) :=
  (X.subgroupOf d.NV).map d.φ

theorem mem_bar {X : Subgroup G} {α : MulAut d.V} :
    α ∈ d.bar X ↔ ∃ x : d.NV, (x : G) ∈ X ∧ d.φ x = α := by
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem φ_mem_bar {X : Subgroup G} {x : d.NV} (hx : (x : G) ∈ X) : d.φ x ∈ d.bar X :=
  ⟨x, hx, rfl⟩

theorem bar_le_Nbar (X : Subgroup G) : d.bar X ≤ d.Nbar := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

theorem bar_mono {X Y : Subgroup G} (h : X ≤ Y) : d.bar X ≤ d.bar Y :=
  Subgroup.map_mono (fun _ hx => h hx)

theorem card_bar_dvd (X : Subgroup G) : Nat.card (d.bar X) ∣ Nat.card X := by
  have h1 := Subgroup.card_map_dvd (X.subgroupOf d.NV) d.φ
  let f : X.subgroupOf d.NV →* X :=
    { toFun := fun y => ⟨((y : d.NV) : G), y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b h => by
    have h' : ((f a : X) : G) = ((f b : X) : G) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  exact h1.trans (Subgroup.card_dvd_of_injective f hf)

theorem bar_le_normalizer {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    d.bar X ≤ Subgroup.normalizer (d.bar Y : Set (MulAut d.V)) := by
  rintro _ ⟨x, hxX, rfl⟩
  apply Sec53.mem_normalizer_of_conj_le
  rintro _ ⟨y, hyY, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  refine ⟨x * y * x⁻¹, ?_, rfl⟩
  have hxX' : (x : G) ∈ X := hxX
  have hyY' : (y : G) ∈ Y := hyY
  show ((x * y * x⁻¹ : d.NV) : G) ∈ Y
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hXY hxX') y).mp hyY'

noncomputable abbrev Jbar : MulAut d.V := d.φ ⟨d.J, d.J_mem_NV⟩

theorem Jbar_mem_Nbar : d.Jbar ∈ d.Nbar := ⟨_, rfl⟩

theorem Jbar_ne_one : d.Jbar ≠ 1 := fun h => d.J_not_mem_CV ((d.φ_eq_one_iff _).mp h)

theorem Jbar_mul_Jbar : d.Jbar * d.Jbar = 1 := by
  rw [← map_mul]
  have : (⟨d.J, d.J_mem_NV⟩ : d.NV) * ⟨d.J, d.J_mem_NV⟩ = 1 := Subtype.ext d.J_mul_J
  rw [this, map_one]

theorem orderOf_Jbar : orderOf d.Jbar = 2 :=
  orderOf_eq_prime (by rw [sq, d.Jbar_mul_Jbar]) d.Jbar_ne_one

theorem Jbar_inv : d.Jbar⁻¹ = d.Jbar := by
  rw [inv_eq_iff_mul_eq_one, d.Jbar_mul_Jbar]

theorem comm_Jbar_iff (x : d.NV) :
    d.φ x * d.Jbar = d.Jbar * d.φ x ↔ (x : G) * d.J * (x : G)⁻¹ * d.J⁻¹ ∈ d.CV := by
  have : d.φ x * d.Jbar = d.Jbar * d.φ x ↔
      d.φ (x * ⟨d.J, d.J_mem_NV⟩ * x⁻¹ * (⟨d.J, d.J_mem_NV⟩ : d.NV)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc d.φ x * d.Jbar = (d.φ x * d.Jbar * (d.φ x)⁻¹ * d.Jbar⁻¹) * (d.Jbar * d.φ x) := by
            group
        _ = d.Jbar * d.φ x := by rw [h, one_mul]
  rw [this, φ_eq_one_iff]
  rfl

theorem mem_Hbar_of_comm (x : d.NV) (h : d.φ x * d.Jbar = d.Jbar * d.φ x) :
    d.φ x ∈ d.bar d.H := by
  have hx := d.mem_H_sup_CV x.2 ((d.comm_Jbar_iff x).mp h)
  have hHC : d.H ≤ Subgroup.normalizer (d.CV : Set G) := fun h hh => d.mem_normalizer_CV
    (d.H_le_NV hh)
  rw [sup_comm] at hx
  obtain ⟨c, hc, k, hk, hck⟩ := (mem_sup_iff_of_le_normalizer hHC).mp hx
  set c' : d.NV := ⟨c, d.CV_le_NV hc⟩
  set k' : d.NV := ⟨k, d.H_le_NV hk⟩
  have hxe : x = c' * k' := Subtype.ext hck.symm
  rw [hxe, map_mul, (d.φ_eq_one_iff c').mpr hc, one_mul]
  exact d.φ_mem_bar hk

theorem mem_Hbar_of_comm' {α : MulAut d.V} (hα : α ∈ d.Nbar) (h : α * d.Jbar = d.Jbar * α) :
    α ∈ d.bar d.H := by
  obtain ⟨x, rfl⟩ := hα
  exact d.mem_Hbar_of_comm x h

theorem card_ker_mul_card_Nbar :
    Nat.card (d.CV.subgroupOf d.NV) * Nat.card d.Nbar = Nat.card d.NV := by
  rw [← d.ker_φ]
  exact Subgroup.card_ker_mul_card_range d.φ

theorem factorization_two_NV : (Nat.card d.NV).factorization 2 ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 d.NV))
  have h := d.card_le_two (Subgroup.map_subtype_le (S : Subgroup d.NV)) (S.isPGroup'.map _)
  rw [Subgroup.card_map_of_injective d.NV.subtype_injective, Sylow.card_eq_multiplicity] at h
  by_contra hcon
  push Not at hcon
  have : 2 ^ 2 ≤ 2 ^ (Nat.card d.NV).factorization 2 := Nat.pow_le_pow_right (by norm_num) hcon
  omega

theorem factorization_two_Nbar : (Nat.card d.Nbar).factorization 2 ≤ 1 := by
  have h := d.card_ker_mul_card_Nbar
  have h1 := d.factorization_two_NV
  rw [← h, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h1
  simp only [Finsupp.coe_add, Pi.add_apply] at h1
  omega

theorem card_le_two_of_le_Nbar {X : Subgroup (MulAut d.V)} (hX : X ≤ d.Nbar)
    (h2 : IsPGroup 2 X) : Nat.card X ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hdvd : Nat.card X ∣ Nat.card d.Nbar := Subgroup.card_dvd_of_le hX
  rw [hk] at hdvd ⊢
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have h1 := d.factorization_two_Nbar
  have hk1 : k ≤ 1 := by omega
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num

theorem eq_one_of_mem_B_of_mem_CV {b : G} (hb : b ∈ d.B) (hbC : b ∈ d.CV) : b = 1 := by
  by_contra hb1
  have hP₁ : d.P₁ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    exact d.fixedPointFree₁ b hb hb1 y hy
      ((Subgroup.mem_centralizer_iff.mp hbC y (Subgroup.mem_sup_left hy)).symm)
  have := d.card_P₁
  rw [hP₁, Subgroup.card_bot] at this
  have h1 : 1 < 3 ^ d.n := Nat.one_lt_pow (by have := d.three_le_n; omega) (by norm_num)
  omega

theorem eq_one_of_mem_P₀_of_mem_CV {y : G} (hy : y ∈ d.P₀) (hyC : y ∈ d.CV) : y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hy1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp d.P₀_isPGroup
  have hoy : orderOf y ∣ 3 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard d.P₀ hy
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hoy
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by rw [hj, pow_zero]))
  set x := y ^ (3 ^ (j - 1)) with hxdef
  have hox : orderOf x = 3 := by
    rw [hxdef, orderOf_pow_of_dvd (by positivity) (hj ▸ Nat.pow_dvd_pow 3 (Nat.sub_le j 1)), hj,
      Nat.pow_div (Nat.sub_le j 1) (by norm_num),
      Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hj0), pow_one]
  have hxC : x ∈ d.CV := d.CV.pow_mem hyC _
  have h := d.free x (d.P₀.pow_mem hy _) hox
  have hinf : (d.V ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = d.V := by
    apply inf_eq_left.mpr
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxC m hm
  rw [hinf, d.card_V] at h
  have h1 : 1 < 3 ^ (2 * d.n) := Nat.one_lt_pow (by have := d.three_le_n; omega) (by norm_num)
  have : 3 ^ (2 * d.n) < (3 ^ (2 * d.n)) ^ 3 := by
    calc 3 ^ (2 * d.n) = (3 ^ (2 * d.n)) ^ 1 := (pow_one _).symm
      _ < (3 ^ (2 * d.n)) ^ 3 := Nat.pow_lt_pow_right h1 (by norm_num)
  omega

theorem not_three_dvd_card_B : ¬ 3 ∣ Nat.card d.B := by
  intro h3
  have h := d.card_B
  have h3' : 3 ∣ 3 ^ d.n := dvd_pow_self 3 (by have := d.three_le_n; omega)
  have h3'' : 3 ∣ 3 ^ d.n - 1 := h ▸ Dvd.dvd.mul_left h3 2
  have := Nat.dvd_sub h3' h3''
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at this
  norm_num at this

theorem mem_normalizer_zpowers_J {g : G} (hg : g * d.J = d.J * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers d.J : Subgroup G) : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [show g * d.J ^ k * g⁻¹ = d.J ^ k by
    rw [(Commute.zpow_right (show Commute g d.J from hg) k).eq, mul_inv_cancel_right]]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem mem_normalizer_sup' {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  have hle : A ⊔ C ≤ (A ⊔ C).comap (MulAut.conj g).toMonoidHom := sup_le
    (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
    (fun c hc => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hC c).mp hc))
  exact fun y hy => hle hy

theorem factorization_three_H :
    (Nat.card d.H).factorization 3 ≤ (Nat.card d.P₀).factorization 3 := by
  have hJB : d.B ≤ Subgroup.normalizer ((Subgroup.zpowers d.J : Subgroup G) : Set G) :=
    fun b hb => d.mem_normalizer_zpowers_J (Subgroup.mem_centralizer_singleton_iff.mp (d.B_le hb))
  have h1 := Sec52.card_sup_mul_card_inf hJB
  rw [Nat.card_zpowers, d.orderOf_J, sup_comm] at h1
  have hE : d.E ≤ Subgroup.normalizer ((Subgroup.zpowers d.J ⊔ d.B : Subgroup G) : Set G) :=
    fun e he => mem_normalizer_sup' (d.mem_normalizer_zpowers_J
      (Subgroup.mem_centralizer_singleton_iff.mp (d.E_le he))) (d.E_le_normalizer_B he)
  have h2 := Sec52.card_sup_mul_card_inf hE
  have h2' : Nat.card d.H * Nat.card ((Subgroup.zpowers d.J ⊔ d.B) ⊓ d.E : Subgroup G) =
      Nat.card (Subgroup.zpowers d.J ⊔ d.B : Subgroup G) * Nat.card d.E := by
    rw [show d.H = d.E ⊔ (Subgroup.zpowers d.J ⊔ d.B) from sup_comm _ _]
    exact h2
  have hne : ∀ X : Subgroup G, Nat.card X ≠ 0 := fun X => Nat.card_pos.ne'
  have h3 : (Nat.card (Subgroup.zpowers d.J ⊔ d.B : Subgroup G)).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h3
    have : 3 ∣ 2 * Nat.card d.B := h3.trans (Dvd.intro _ h1)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h | h
    · norm_num at h
    · exact d.not_three_dvd_card_B h
  have h4 := congrArg (fun m => m.factorization 3) h2'
  simp only [Nat.factorization_mul (hne _) (hne _), Finsupp.coe_add, Pi.add_apply] at h4
  rw [d.P₀_sylow]
  omega

theorem P₀_le_H : d.P₀ ≤ d.H := d.P₀_le.trans le_sup_right

theorem card_P₀bar : Nat.card (d.bar d.P₀) = Nat.card d.P₀ := by
  have hinj : Function.Injective (d.φ.comp (Subgroup.inclusion d.P₀_le_NV)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, φ_eq_one_iff] at hy
    rw [Subgroup.mem_bot]
    exact Subtype.ext (d.eq_one_of_mem_P₀_of_mem_CV y.2 hy)
  have : d.bar d.P₀ = (d.φ.comp (Subgroup.inclusion d.P₀_le_NV)).range := by
    ext α
    rw [mem_bar, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨_, y.2, rfl⟩
  rw [this, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]

theorem exists_conj_le_P₀bar {X : Subgroup (MulAut d.V)} (hXH : X ≤ d.bar d.H)
    (hX : IsPGroup 3 X) : ∃ h ∈ d.bar d.H, ∀ x ∈ X, h⁻¹ * x * h ∈ d.bar d.P₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP₀H : d.bar d.P₀ ≤ d.bar d.H := d.bar_mono d.P₀_le_H
  have hcard : Nat.card ((d.bar d.P₀).subgroupOf (d.bar d.H)) =
      3 ^ (Nat.card (d.bar d.H)).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀H).toEquiv, d.card_P₀bar]
    have hP₀ : IsPGroup 3 d.P₀ := d.P₀_isPGroup
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₀
    have h1 : (Nat.card (d.bar d.H)).factorization 3 ≤ k := by
      have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (d.card_bar_dvd d.H) 3
      have h2 := d.factorization_three_H
      rw [hk, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at h2
      omega
    have h2 : k ≤ (Nat.card (d.bar d.H)).factorization 3 := by
      have hdvd : Nat.card (d.bar d.P₀) ∣ Nat.card (d.bar d.H) := Subgroup.card_dvd_of_le hP₀H
      rw [d.card_P₀bar, hk] at hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
    rw [hk, le_antisymm h1 h2]
  set S : Sylow 3 (d.bar d.H) := Sylow.ofCard _ hcard
  obtain ⟨T, hT⟩ := (show IsPGroup 3 (X.subgroupOf (d.bar d.H)) from
    hX.comap_subtype).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (d.bar d.H) T S
  refine ⟨((h⁻¹ : d.bar d.H) : MulAut d.V), (h⁻¹ : d.bar d.H).2, fun x hx => ?_⟩
  have hxT : (⟨x, hXH hx⟩ : d.bar d.H) ∈ (T : Subgroup (d.bar d.H)) := hT hx
  have hS : h * ⟨x, hXH hx⟩ * h⁻¹ ∈ (S : Subgroup (d.bar d.H)) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hxT, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hS' := Subgroup.mem_subgroupOf.mp hS
  simpa using hS'

theorem eq_one_of_mem_bar_of_pow {D : Subgroup G} (hDB : D ≤ d.B) {z : MulAut d.V}
    (hz : z ∈ d.bar D) {k : ℕ} (hzk : z ^ (3 ^ k) = 1) : z = 1 := by
  have h1 : orderOf z ∣ Nat.card d.B :=
    ((Subgroup.orderOf_coe (⟨z, hz⟩ : d.bar D)) ▸ orderOf_dvd_natCard (⟨z, hz⟩ : d.bar D)).trans
      ((d.card_bar_dvd D).trans (Subgroup.card_dvd_of_le hDB))
  have h2 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have hcop : Nat.Coprime (3 ^ k) (Nat.card d.B) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      d.not_three_dvd_card_B)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem eq_bot_of_comm_Jbar {D : Subgroup G} (hDB : D ≤ d.B)
    (hDH : d.H ≤ Subgroup.normalizer (D : Set G))
    (hD : ∀ y ∈ d.P₀, (∀ b ∈ D, y * b = b * y) → y = 1)
    {X : Subgroup (MulAut d.V)} (hXN : X ≤ d.Nbar) (hXJ : ∀ x ∈ X, x * d.Jbar = d.Jbar * x)
    (hX : IsPGroup 3 X) (hDX : d.bar D ≤ Subgroup.normalizer (X : Set (MulAut d.V))) :
    X = ⊥ := by
  have hXH : X ≤ d.bar d.H := fun x hx => d.mem_Hbar_of_comm' (hXN hx) (hXJ x hx)
  obtain ⟨h, hhH, hh⟩ := d.exists_conj_le_P₀bar hXH hX
  have hHD : d.bar d.H ≤ Subgroup.normalizer (d.bar D : Set (MulAut d.V)) :=
    d.bar_le_normalizer hDH
  have hhD := hHD hhH
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hyP : h⁻¹ * x * h ∈ d.bar d.P₀ := hh x hx
  obtain ⟨p, hpP, hpy⟩ := d.mem_bar.mp hyP
  have hcomm : ∀ c ∈ d.bar D, d.φ p * c = c * d.φ p := by
    intro c hc
    rw [hpy]
    set y := h⁻¹ * x * h with hy
    have hyN := hHD (d.bar_mono d.P₀_le_H hyP)
    have h1 : y * c * y⁻¹ * c⁻¹ ∈ d.bar D :=
      (d.bar D).mul_mem ((Subgroup.mem_normalizer_iff.mp hyN c).mp hc) ((d.bar D).inv_mem hc)
    have h2 : h * (y * c * y⁻¹ * c⁻¹) * h⁻¹ ∈ X := by
      have hc' : h * c * h⁻¹ ∈ d.bar D := (Subgroup.mem_normalizer_iff.mp hhD c).mp hc
      have hcX := hDX hc'
      have : h * (y * c * y⁻¹ * c⁻¹) * h⁻¹ =
          x * ((h * c * h⁻¹) * x⁻¹ * (h * c * h⁻¹)⁻¹) := by rw [hy]; group
      rw [this]
      exact X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hcX x⁻¹).mp (X.inv_mem hx))
    obtain ⟨k, hk⟩ := hX ⟨_, h2⟩
    have hk' : (h * (y * c * y⁻¹ * c⁻¹) * h⁻¹) ^ (3 ^ k) = 1 := congrArg Subtype.val hk
    rw [conj_pow] at hk'
    have hk'' : (y * c * y⁻¹ * c⁻¹) ^ (3 ^ k) = 1 := by
      have := congrArg (fun w => h⁻¹ * w * h) hk'
      simpa [mul_assoc] using this
    have := d.eq_one_of_mem_bar_of_pow hDB h1 hk''
    calc y * c = (y * c * y⁻¹ * c⁻¹) * (c * y) := by group
      _ = c * y := by rw [this, one_mul]
  have hp1 : (p : G) = 1 := by
    apply hD _ hpP
    intro b hb
    have hbN : b ∈ d.NV := d.B_le_NV (hDB hb)
    have hc := hcomm (d.φ ⟨b, hbN⟩) (d.φ_mem_bar hb)
    rw [← map_mul, ← map_mul, d.φ_eq_iff] at hc
    obtain ⟨q, hqN⟩ := p
    simp only at hpP ⊢
    have hw : (b * q)⁻¹ * (q * b) ∈ d.CV := hc
    have hmem : q * b * q⁻¹ * b⁻¹ ∈ D := by
      have hpD : q ∈ Subgroup.normalizer (D : Set G) := hDH (d.P₀_le_H hpP)
      exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp hpD b).mp hb) (D.inv_mem hb)
    have hC : q * b * q⁻¹ * b⁻¹ ∈ d.CV := by
      have h' := (Subgroup.mem_normalizer_iff.mp (d.mem_normalizer_CV
        (d.NV.mul_mem hbN hqN)) _).mp hw
      have : b * q * ((b * q)⁻¹ * (q * b)) * (b * q)⁻¹ = q * b * q⁻¹ * b⁻¹ := by group
      rwa [this] at h'
    have h1 := d.eq_one_of_mem_B_of_mem_CV (hDB hmem) hC
    calc q * b = (q * b * q⁻¹ * b⁻¹) * (b * q) := by group
      _ = b * q := by rw [h1, one_mul]
  have hy1 : h⁻¹ * x * h = 1 := by
    rw [← hpy, (d.φ_eq_one_iff p).mpr (by rw [hp1]; exact d.CV.one_mem)]
  calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    _ = 1 := by rw [hy1, mul_one, mul_inv_cancel]

end P56AbData

end CFSG.Walter.W67
