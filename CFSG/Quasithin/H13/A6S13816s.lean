module

public import CFSG.Quasithin.H13.A6S13816q
public import CFSG.Quasithin.EmptyFaithful.S146xB2Excl

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace L2Aut

open CFSG.Quasithin.SBc5SL2

variable {F : Type} [Field F]

theorem xm_injective : Function.Injective (xm : F → SL2 F) := by
  intro s t h
  have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [L2Borel.coe_xm'] using this

theorem xm_neg (t : F) : xm (-t) = (xm t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, xm_mul, neg_add_cancel]
  exact Subtype.ext (by ext i j; rw [L2Borel.coe_xm']; fin_cases i <;> fin_cases j <;> simp)

theorem exists_sq [Finite F] [CharP F 2] (a : F) : ∃ c : F, c ^ 2 = a := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hinj : Function.Injective (fun x : F => x ^ 2) := fun x y h => by
    have h' : (x - y) ^ 2 = 0 := by
      have h1 : x ^ 2 = y ^ 2 := h
      linear_combination h1 + (y ^ 2 - x * y) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h')
  obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp hinj) a
  exact ⟨c, hc⟩

theorem xm_zero : xm (0 : F) = 1 :=
  Subtype.ext (by ext i j; rw [L2Borel.coe_xm']; fin_cases i <;> fin_cases j <;> simp)

theorem exists_inner [Finite F] [CharP F 2] (α : SL2 F →* SL2 F) (hinj : Function.Injective α)
    (hU : ∀ t : F, α (xm t) ∈ Uplus F) {c₀ : Fˣ} (hc₀ : ∀ c : Fˣ, c ∈ Subgroup.zpowers c₀)
    (hc₀1 : c₀ ≠ 1) (hD : α (dm c₀) * (dm c₀)⁻¹ ∈ Uplus F) :
    ∃ g : SL2 F, ∀ x, α x = g * x * g⁻¹ := by
  classical
  have := Fintype.ofFinite F
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc2 : (1 : F) - (c₀ : F) ^ 2 ≠ 0 := by
    intro hc
    apply hc₀1
    have h3 : ((c₀ : F) - 1) ^ 2 = 0 := by linear_combination (-1 : F) * hc - ((c₀ : F) - 1) * h2
    exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3))
  obtain ⟨s, hs⟩ := mem_Uplus_iff.mp hD
  have hαd : α (dm c₀) = xm s * dm c₀ := by
    rw [← hs, inv_mul_cancel_right]
  set r : F := -s / (1 - (c₀ : F) ^ 2) with hr
  have hrs : r + s - (c₀ : F) ^ 2 * r = 0 := by
    rw [hr]
    field_simp
    ring
  set u : SL2 F := xm r with hu
  have hud : u * α (dm c₀) * u⁻¹ = dm c₀ := by
    have e1 : dm c₀ * (xm r)⁻¹ = xm (-((c₀ : F) ^ 2 * r)) * dm c₀ := by
      rw [xm_neg, ← L2Borel.dm_conj_xm, mul_inv_rev, inv_inv]
      group
    rw [hαd, hu, mul_assoc, mul_assoc, e1, ← mul_assoc, ← mul_assoc, xm_mul, xm_mul]
    have e2 : r + s + -((c₀ : F) ^ 2 * r) = 0 := by rw [← hrs]; ring
    rw [e2, xm_zero, one_mul]
  let σ₁ : SL2 F →* SL2 F := (MulAut.conj u).toMonoidHom.comp α
  have hσ₁ : ∀ x, σ₁ x = u * α x * u⁻¹ := fun x => rfl
  have hσ₁inj : Function.Injective σ₁ := (MulAut.conj u).injective.comp hinj
  have hσ₁d : ∀ c : Fˣ, σ₁ (dm c) = dm c := by
    intro c
    obtain ⟨k, rfl⟩ := hc₀ c
    have e : dm (c₀ ^ k) = (L2Borel.dmHom c₀) ^ k := (map_zpow L2Borel.dmHom c₀ k).trans rfl
    rw [e, map_zpow]
    exact congrArg (· ^ k) hud
  have hσ₁U : ∀ t : F, σ₁ (xm t) ∈ Uplus F := fun t => by
    rw [hσ₁]
    exact (Uplus F).mul_mem ((Uplus F).mul_mem (xm_mem_Uplus r) (hU t))
      ((Uplus F).inv_mem (xm_mem_Uplus r))
  choose f hf using fun t => mem_Uplus_iff.mp (hσ₁U t)
  have f_add : ∀ a b, f (a + b) = f a + f b := fun a b => by
    apply xm_injective
    rw [← hf, ← xm_mul, ← xm_mul, ← hf, ← hf, map_mul]
  have f_sq : ∀ (c : Fˣ) (t : F), f ((c : F) ^ 2 * t) = (c : F) ^ 2 * f t := fun c t => by
    apply xm_injective
    rw [← hf, ← L2Borel.dm_conj_xm, map_mul, map_mul, map_inv, hσ₁d, hf, L2Borel.dm_conj_xm]
  have f_zero : f 0 = 0 := by
    have := f_add 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have f_lin : ∀ t, f t = t * f 1 := by
    intro t
    by_cases ht : t = 0
    · rw [ht, f_zero, zero_mul]
    · obtain ⟨c, hc⟩ := exists_sq t
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact ht (by rw [← hc]; ring)
      have := f_sq (Units.mk0 c hc0) 1
      simp only [Units.val_mk0, mul_one] at this
      rwa [hc] at this
  set μ := f 1 with hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : σ₁ (xm 1) = σ₁ 1 := by rw [hf, ← hμ, h0, xm_zero, map_one]
    have h3 := xm_injective ((hσ₁inj h1).trans xm_zero.symm)
    exact one_ne_zero h3
  obtain ⟨d, hd⟩ := exists_sq μ
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [← hd]; ring)
  set du : Fˣ := Units.mk0 d hd0 with hdu
  let σ₂ : SL2 F →* SL2 F := (MulAut.conj (dm du)⁻¹).toMonoidHom.comp σ₁
  have hσ₂ : ∀ x, σ₂ x = (dm du)⁻¹ * σ₁ x * (dm du)⁻¹⁻¹ := fun x => rfl
  have hdinv : (dm du)⁻¹ = dm du⁻¹ := (map_inv L2Borel.dmHom du).symm
  have hσ₂x : ∀ t : F, σ₂ (xm t) = xm t := by
    intro t
    rw [hσ₂, hf, f_lin, hdinv, L2Borel.dm_conj_xm]
    congr 1
    rw [Units.val_inv_eq_inv_val, hdu, Units.val_mk0, ← hd]
    field_simp
  have hσ₂d : σ₂ (dm c₀) = dm c₀ := by
    rw [hσ₂, hσ₁d, hdinv]
    have hc : dm du⁻¹ * dm c₀ = dm c₀ * dm du⁻¹ := by
      have e1 : dm du⁻¹ * dm c₀ = L2Borel.dmHom (du⁻¹ * c₀) :=
        (map_mul L2Borel.dmHom du⁻¹ c₀).symm
      have e2 : dm c₀ * dm du⁻¹ = L2Borel.dmHom (c₀ * du⁻¹) :=
        (map_mul L2Borel.dmHom c₀ du⁻¹).symm
      rw [e1, e2, mul_comm]
    rw [hc, mul_inv_cancel_right]
  have hid := hom_eq_id σ₂ hσ₂x hc₀1 hσ₂d
  refine ⟨u⁻¹ * dm du, fun x => ?_⟩
  have h1 := hid x
  rw [hσ₂, hσ₁] at h1
  calc α x = u⁻¹ * (dm du * ((dm du)⁻¹ * (u * α x * u⁻¹) * (dm du)⁻¹⁻¹) * (dm du)⁻¹) * u := by
        group
    _ = u⁻¹ * dm du * x * (u⁻¹ * dm du)⁻¹ := by rw [h1]; group

theorem dm_one : dm (1 : Fˣ) = 1 := map_one L2Borel.dmHom

theorem exists_inner_of_isPSL {X : Type} [Group X] (hX : IsPSL 2 2 2 X) {Q : Subgroup X}
    (hQ : IsSylowTwoOf Q ⊤) (α : X →* X) (hinj : Function.Injective α)
    (hαQ : ∀ x ∈ Q, α x ∈ Q) {a : X} (haN : a ∈ Subgroup.normalizer (Q : Set X)) (haQ : a ∉ Q)
    (hαa : α a * a⁻¹ ∈ Q) : ∃ g : X, ∀ x, α x = g * x * g⁻¹ := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, hn, ⟨φ⟩⟩ := SBc6.exists_sl2_equiv_of_psl hX
  classical
  have := Fintype.ofFinite F
  have hQ' := L2Borel.isSylowTwoOf_top_comap φ hQ
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_Uplus hn hFcard) hQ'
  let ψ : SL2 F ≃* X := (MulAut.conj g).trans φ
  have hψ : ∀ y, ψ y ∈ Q ↔ y ∈ Uplus F := fun y => by
    have h1 : ψ y ∈ Q ↔ g * y * g⁻¹ ∈ Q.comap (φ : SL2 F →* X) := Iff.rfl
    rw [h1, hg, B6.mem_conjSub]
    simp [mul_assoc]
  have hψN : ∀ y, ψ y ∈ Subgroup.normalizer (Q : Set X) ↔ y ∈ Tplus F := fun y => by
    rw [← normalizer_Uplus, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h u
      rw [← hψ, ← hψ, map_mul, map_mul, map_inv]
      exact h (ψ u)
    · intro h x
      obtain ⟨u, rfl⟩ := ψ.surjective x
      rw [← map_inv, ← map_mul, ← map_mul, hψ, hψ]
      exact h u
  let α' : SL2 F →* SL2 F := ψ.symm.toMonoidHom.comp (α.comp ψ.toMonoidHom)
  have hα' : ∀ y, α' y = ψ.symm (α (ψ y)) := fun y => rfl
  have hinj' : Function.Injective α' := ψ.symm.injective.comp (hinj.comp ψ.injective)
  have hU : ∀ t : F, α' (xm t) ∈ Uplus F := fun t => by
    rw [hα', ← hψ, MulEquiv.apply_symm_apply]
    exact hαQ _ ((hψ _).mpr (xm_mem_Uplus t))
  obtain ⟨t₀, c₀, hta⟩ := mem_Tplus_iff.mp ((hψN (ψ.symm a)).mp (by simpa using haN))
  have hc₀1 : c₀ ≠ 1 := by
    rintro rfl
    apply haQ
    have : ψ.symm a ∈ Uplus F := by rw [hta, dm_one, mul_one]; exact xm_mem_Uplus t₀
    simpa using (hψ _).mpr this
  have hcard : Nat.card Fˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hFcard]
    norm_num
  have hc₀ : ∀ c : Fˣ, c ∈ Subgroup.zpowers c₀ := by
    have hord : orderOf c₀ = 3 := by
      have h1 := orderOf_dvd_natCard c₀
      rw [hcard] at h1
      rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hc₀1
      · exact h
    have htop : Subgroup.zpowers c₀ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, hcard]
    intro c
    rw [htop]
    exact Subgroup.mem_top c
  have hD : α' (dm c₀) * (dm c₀)⁻¹ ∈ Uplus F := by
    have h1 : α' (ψ.symm a) * (ψ.symm a)⁻¹ ∈ Uplus F := by
      rw [← hψ, map_mul, map_inv, hα', MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hαa
    have e : dm c₀ = (xm t₀)⁻¹ * ψ.symm a := by rw [hta, inv_mul_cancel_left]
    have e2 : α' (dm c₀) * (dm c₀)⁻¹ =
        (α' (xm t₀))⁻¹ * (α' (ψ.symm a) * (ψ.symm a)⁻¹) * xm t₀ := by
      rw [e, map_mul, map_inv]
      group
    rw [e2]
    exact (Uplus F).mul_mem ((Uplus F).mul_mem ((Uplus F).inv_mem (hU t₀)) h1) (xm_mem_Uplus t₀)
  obtain ⟨h, hh⟩ := exists_inner α' hinj' hU hc₀ hc₀1 hD
  refine ⟨ψ h, fun x => ?_⟩
  have h2 := hh (ψ.symm x)
  rw [hα', MulEquiv.apply_symm_apply] at h2
  have h3 := congrArg ψ h2
  rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h3
  exact h3

theorem exists_centralizing {P : Type} [Group P] {K₁ K₂ Q₁ Q₂ : Subgroup P}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hK₁ : IsPSL 2 2 2 ↥K₁)
    (hK₂ : IsPSL 2 2 2 ↥K₂) (hQ₁ : IsSylowTwoOf Q₁ K₁) (hQ₂ : IsSylowTwoOf Q₂ K₂) {y : P}
    (hy₁ : y ∈ Subgroup.normalizer (K₁ : Set P)) (hy₂ : y ∈ Subgroup.normalizer (K₂ : Set P))
    (hyQ₁ : y ∈ Subgroup.normalizer (Q₁ : Set P)) (hyQ₂ : y ∈ Subgroup.normalizer (Q₂ : Set P))
    {a₁ a₂ : P} (ha₁K : a₁ ∈ K₁) (ha₂K : a₂ ∈ K₂) (ha₁N : a₁ ∈ Subgroup.normalizer (Q₁ : Set P))
    (ha₂N : a₂ ∈ Subgroup.normalizer (Q₂ : Set P)) (ha₁Q : a₁ ∉ Q₁) (ha₂Q : a₂ ∉ Q₂)
    (hya₁ : y * a₁ * y⁻¹ * a₁⁻¹ ∈ Q₁) (hya₂ : y * a₂ * y⁻¹ * a₂⁻¹ ∈ Q₂) :
    ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, (∀ x ∈ K₁, (k₁ * k₂)⁻¹ * y * x = x * ((k₁ * k₂)⁻¹ * y)) ∧
      ∀ x ∈ K₂, (k₁ * k₂)⁻¹ * y * x = x * ((k₁ * k₂)⁻¹ * y) := by
  have key : ∀ {K Q : Subgroup P}, IsPSL 2 2 2 ↥K → IsSylowTwoOf Q K →
      y ∈ Subgroup.normalizer (K : Set P) → y ∈ Subgroup.normalizer (Q : Set P) →
      ∀ {a : P}, a ∈ K → a ∈ Subgroup.normalizer (Q : Set P) → a ∉ Q →
      y * a * y⁻¹ * a⁻¹ ∈ Q → ∃ k ∈ K, ∀ x ∈ K, y * x * y⁻¹ = k * x * k⁻¹ := by
    intro K Q hK hQ hyK hyQ a haK haN haQ hya
    let α : ↥K →* ↥K :=
      { toFun := fun x => ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyK x).mp x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x x' => Subtype.ext (by simp [mul_assoc]) }
    have hα : ∀ x : ↥K, ((α x : ↥K) : P) = y * x * y⁻¹ := fun x => rfl
    have hinj : Function.Injective α := fun x x' h => by
      have h1 := congrArg Subtype.val h
      rw [hα, hα] at h1
      exact Subtype.ext (by simpa using h1)
    have hαQ : ∀ x ∈ Q.subgroupOf K, α x ∈ Q.subgroupOf K := fun x hx => by
      rw [Subgroup.mem_subgroupOf, hα]
      exact (Subgroup.mem_normalizer_iff.mp hyQ x).mp (Subgroup.mem_subgroupOf.mp hx)
    have haN' : (⟨a, haK⟩ : ↥K) ∈ Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) :
        Set ↥K) := L2Hat.mem_normalizer_subgroupOf haK haN
    have haQ' : (⟨a, haK⟩ : ↥K) ∉ Q.subgroupOf K := fun h => haQ (Subgroup.mem_subgroupOf.mp h)
    have hαa : α ⟨a, haK⟩ * (⟨a, haK⟩ : ↥K)⁻¹ ∈ Q.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      simpa [hα] using hya
    obtain ⟨k, hk⟩ := exists_inner_of_isPSL hK (isSylowTwoOf_top_subgroupOf hQ) α hinj hαQ haN'
      haQ' hαa
    refine ⟨k, k.2, fun x hx => ?_⟩
    have := congrArg Subtype.val (hk ⟨x, hx⟩)
    simpa [hα] using this
  obtain ⟨k₁, hk₁K, hk₁⟩ := key hK₁ hQ₁ hy₁ hyQ₁ ha₁K ha₁N ha₁Q hya₁
  obtain ⟨k₂, hk₂K, hk₂⟩ := key hK₂ hQ₂ hy₂ hyQ₂ ha₂K ha₂N ha₂Q hya₂
  refine ⟨k₁, hk₁K, k₂, hk₂K, fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := hk₁ x hx
    have hc : k₂ * x = x * k₂ := (hcomm x hx k₂ hk₂K).symm
    calc (k₁ * k₂)⁻¹ * y * x = k₂⁻¹ * (k₁⁻¹ * (y * x * y⁻¹) * k₁) * k₁⁻¹ * y := by group
      _ = k₂⁻¹ * x * k₁⁻¹ * y := by rw [h1]; group
      _ = x * ((k₁ * k₂)⁻¹ * y) := by
        have hc' : k₂⁻¹ * x = x * k₂⁻¹ := by
          calc k₂⁻¹ * x = k₂⁻¹ * (x * k₂) * k₂⁻¹ := by group
            _ = k₂⁻¹ * (k₂ * x) * k₂⁻¹ := by rw [hc]
            _ = x * k₂⁻¹ := by group
        calc k₂⁻¹ * x * k₁⁻¹ * y = (k₂⁻¹ * x) * k₁⁻¹ * y := rfl
          _ = (x * k₂⁻¹) * k₁⁻¹ * y := by rw [hc']
          _ = x * ((k₁ * k₂)⁻¹ * y) := by group
  · have h1 := hk₂ x hx
    have hc : k₁ * x = x * k₁ := hcomm k₁ hk₁K x hx
    calc (k₁ * k₂)⁻¹ * y * x = k₂⁻¹ * k₁⁻¹ * (y * x * y⁻¹) * y := by group
      _ = k₂⁻¹ * k₁⁻¹ * (k₂ * x * k₂⁻¹) * y := by rw [h1]
      _ = x * ((k₁ * k₂)⁻¹ * y) := by
        have hc' : k₁⁻¹ * (k₂ * x * k₂⁻¹) = (k₂ * x * k₂⁻¹) * k₁⁻¹ := by
          have hm : k₂ * x * k₂⁻¹ ∈ K₂ := K₂.mul_mem (K₂.mul_mem hk₂K hx) (K₂.inv_mem hk₂K)
          have := hcomm k₁⁻¹ (K₁.inv_mem hk₁K) _ hm
          exact this
        calc k₂⁻¹ * k₁⁻¹ * (k₂ * x * k₂⁻¹) * y = k₂⁻¹ * (k₁⁻¹ * (k₂ * x * k₂⁻¹)) * y := by
              group
          _ = k₂⁻¹ * ((k₂ * x * k₂⁻¹) * k₁⁻¹) * y := by rw [hc']
          _ = x * ((k₁ * k₂)⁻¹ * y) := by group

theorem eq_one_of_centralizes {P : Type} [Group P] {K₀ : Subgroup P} (hK₀ : K₀.Normal)
    (h2 : ∀ x : P, ∃ e : ℕ, x ^ 2 ^ e ∈ K₀) (hZ : ∀ x ∈ K₀, (∀ y ∈ K₀, x * y = y * x) → x = 1)
    (hO2 : CFSG.pCore 2 P = ⊥) {z : P} (hz : ∀ y ∈ K₀, z * y = y * z) : z = 1 := by
  set C := Subgroup.centralizer (K₀ : Set P) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hC2 : IsPGroup 2 C := fun c => by
    obtain ⟨e, he⟩ := h2 c
    refine ⟨e, Subtype.ext ?_⟩
    have hmem : (c : P) ^ 2 ^ e ∈ C := C.pow_mem c.2 _
    simpa using hZ _ he (fun y hy => (Subgroup.mem_centralizer_iff.mp hmem y hy).symm)
  have hle : C ≤ CFSG.pCore 2 P := le_sSup ⟨hCn, hC2⟩
  rw [hO2] at hle
  have hzC : z ∈ C := Subgroup.mem_centralizer_iff.mpr fun y hy => (hz y hy).symm
  exact Subgroup.mem_bot.mp (hle hzC)

end L2Aut

namespace L2Hat

variable {Q : Type} [Group Q]

theorem comp_of_normalizes {K₁ K₂ U₁ U₂ Tq : Subgroup Q}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥) (hU₁ : U₁ ≤ K₁)
    (hU₂ : U₂ ≤ K₂) (hT : Tq ⊓ (K₁ ⊔ K₂) ≤ U₁ ⊔ U₂) {w x x' z z' : Q}
    (hw₁ : w ∈ Subgroup.normalizer (K₁ : Set Q)) (hw₂ : w ∈ Subgroup.normalizer (K₂ : Set Q))
    (hx : x ∈ K₁) (hx' : x' ∈ K₁) (hz : z ∈ K₂) (hz' : z' ∈ K₂)
    (h : w * (x * z) * w⁻¹ * (x' * z') ∈ Tq) :
    w * x * w⁻¹ * x' ∈ U₁ ∧ w * z * w⁻¹ * z' ∈ U₂ := by
  have hwx : w * x * w⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hw₁ x).mp hx
  have hwz : w * z * w⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp hw₂ z).mp hz
  have hX : w * x * w⁻¹ * x' ∈ K₁ := K₁.mul_mem hwx hx'
  have hZ : w * z * w⁻¹ * z' ∈ K₂ := K₂.mul_mem hwz hz'
  have e : w * (x * z) * w⁻¹ * (x' * z') = (w * x * w⁻¹ * x') * (w * z * w⁻¹ * z') := by
    have hc := hcomm x' hx' (w * z * w⁻¹) hwz
    calc w * (x * z) * w⁻¹ * (x' * z') = (w * x * w⁻¹) * ((w * z * w⁻¹) * x') * z' := by group
      _ = (w * x * w⁻¹) * (x' * (w * z * w⁻¹)) * z' := by rw [hc]
      _ = (w * x * w⁻¹ * x') * (w * z * w⁻¹ * z') := by group
  have hmem : (w * x * w⁻¹ * x') * (w * z * w⁻¹ * z') ∈ U₁ ⊔ U₂ :=
    hT ⟨e ▸ h, Subgroup.mul_mem _ (Subgroup.mem_sup_left hX) (Subgroup.mem_sup_right hZ)⟩
  refine ⟨mem_of_mul_mem_sup hcomm hinf hU₁ hU₂ hX hZ hmem, ?_⟩
  have hcomm' : ∀ x ∈ K₂, ∀ y ∈ K₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hinf' : K₂ ⊓ K₁ = ⊥ := by rw [inf_comm]; exact hinf
  refine mem_of_mul_mem_sup hcomm' hinf' hU₂ hU₁ hZ hX ?_
  rw [← hcomm _ hX _ hZ, sup_comm]
  exact hmem

theorem comp_of_swaps {K₁ K₂ U₁ U₂ Tq : Subgroup Q}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥) (hU₁ : U₁ ≤ K₁)
    (hU₂ : U₂ ≤ K₂) (hT : Tq ⊓ (K₁ ⊔ K₂) ≤ U₁ ⊔ U₂) {w x x' z z' : Q}
    (hwx : w * x * w⁻¹ ∈ K₂) (hwz : w * z * w⁻¹ ∈ K₁) (hx' : x' ∈ K₁) (hz' : z' ∈ K₂)
    (h : w * (x * z) * w⁻¹ * (x' * z') ∈ Tq) : w * z * w⁻¹ * x' ∈ U₁ := by
  have hX : w * z * w⁻¹ * x' ∈ K₁ := K₁.mul_mem hwz hx'
  have hZ : w * x * w⁻¹ * z' ∈ K₂ := K₂.mul_mem hwx hz'
  have e : w * (x * z) * w⁻¹ * (x' * z') = (w * z * w⁻¹ * x') * (w * x * w⁻¹ * z') := by
    have h1 := hcomm (w * z * w⁻¹) hwz (w * x * w⁻¹) hwx
    have h2 := hcomm x' hx' (w * x * w⁻¹) hwx
    calc w * (x * z) * w⁻¹ * (x' * z') = (w * x * w⁻¹) * (w * z * w⁻¹) * x' * z' := by group
      _ = (w * z * w⁻¹) * (w * x * w⁻¹) * x' * z' := by rw [h1]
      _ = (w * z * w⁻¹) * ((w * x * w⁻¹) * x') * z' := by group
      _ = (w * z * w⁻¹) * (x' * (w * x * w⁻¹)) * z' := by rw [h2]
      _ = (w * z * w⁻¹ * x') * (w * x * w⁻¹ * z') := by group
  exact mem_of_mul_mem_sup hcomm hinf hU₁ hU₂ hX hZ
    (hT ⟨e ▸ h, Subgroup.mul_mem _ (Subgroup.mem_sup_left hX) (Subgroup.mem_sup_right hZ)⟩)

theorem pow_mul_mem {U : Subgroup Q} {p a : Q} (hp : p ∈ U)
    (ha : a ∈ Subgroup.normalizer (U : Set Q)) (f : ℕ) : (p * a) ^ f * (a ^ f)⁻¹ ∈ U := by
  induction f with
  | zero => simp
  | succ f ih =>
    have haf : a ^ f ∈ Subgroup.normalizer (U : Set Q) := Subgroup.pow_mem _ ha f
    have h1 : a ^ f * p * (a ^ f)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp haf p).mp hp
    have e : (p * a) ^ (f + 1) * (a ^ (f + 1))⁻¹ =
        ((p * a) ^ f * (a ^ f)⁻¹) * (a ^ f * p * (a ^ f)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact U.mul_mem ih h1

theorem false_of_mem_coset {U : Subgroup Q} (hU : IsPGroup 2 U) {a a' : Q} {f : ℕ}
    (ha'3 : a' ^ 3 = 1) (ha'1 : a' ≠ 1) (h1 : a' * (a ^ f)⁻¹ ∈ U)
    (h2 : a'⁻¹ * (a ^ f)⁻¹ ∈ U) : False := by
  have hsq : a' ^ 2 ∈ U := by
    have e : a' ^ 2 = (a' * (a ^ f)⁻¹) * (a'⁻¹ * (a ^ f)⁻¹)⁻¹ := by rw [pow_two]; group
    rw [e]
    exact U.mul_mem h1 (U.inv_mem h2)
  have ha' : a' ∈ U := by
    have e : a' = (a' ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ']
      exact ha'3
    rw [e]
    exact U.inv_mem hsq
  obtain ⟨k, hk⟩ := hU ⟨a', ha'⟩
  have hk' : a' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ha'1 (L32Comm.eq_one_of_pow_of_cube hk' ha'3)

end L2Hat

namespace L2Hat

variable {Q : Type} [Group Q]

theorem eq_one_of_central {K U : Subgroup Q} (hK : IsPSL 2 2 2 ↥K) (hU : IsSylowTwoOf U K)
    {a : Q} (haK : a ∈ K) (haN : a ∈ Subgroup.normalizer (U : Set Q)) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) {x : Q} (hxK : x ∈ K) (hx : ∀ y ∈ K, x * y = y * x) : x = 1 := by
  have hsimple : IsSimpleGroup ↥K := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 hK).2
  have hxC : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (hx y y.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · rw [h] at hxC
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxC)
  · exfalso
    have hUbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have huC : (⟨u, hU.1 hu⟩ : ↥K) ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top _
      have hcomm := congrArg Subtype.val ((Subgroup.mem_center_iff.mp huC) ⟨a, haK⟩)
      have hau : a * u * a⁻¹ = u := by
        simp only [Subgroup.coe_mul] at hcomm
        rw [hcomm, mul_inv_cancel_right]
      exact Subgroup.mem_bot.mpr (eq_one_of_conj_eq_in hK hU haK haN ha3 ha1 hu hau)
    have hcard : Nat.card ↥K = 2 ^ 2 * (4 ^ 2 - 1) :=
      CFSG.Quasithin.card_of_isPSL_two_even (by norm_num) hK
    apply hU.2.2
    rw [hUbot]
    show 2 ∣ ((⊥ : Subgroup Q).subgroupOf K).index
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, hcard]
    norm_num

end L2Hat

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem O2_le_K0 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (hhat : IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K) (hHK : H = K ⊔ T)
    (hn : IsPSL 2 2 2 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    pCoreOf 2 (S.L1 ⊔ T) ≤ conjClosure K T ⊔ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hℓK : S.L1 ≤ conjClosure K T :=
    S.L1_le_conjClosure' h37 h38 h122 hH hK hne (L2Case.three_dvd_card (Or.inl ⟨2, hn⟩))
  have hℓH : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hN₀ : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ2 : ∀ x : ↥H, π x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    have hmem := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hmem⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  set Kb := (K.subgroupOf H).map π with hKb
  set Tb := (T.subgroupOf H).map π with hTb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := modO2Image_mem_cComp hK
  have hTbs : IsSylowTwoOf Tb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) π hπs
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  obtain ⟨-, hL2'⟩ := h38 _ hQ Kb hKbc
  rcases hL2' Tb hTbs with ⟨hnorm, -, -⟩ | ⟨t, htT, -, hconj, -, hcomm', hinf, hTN, -⟩
  · exact (hne (L32Case.conjClosure_eq_of_normal hKH hTH (normal_of_normal_map_of_mem_cComp
      (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H) (subgroupOf_mem_cComp hK) hnorm))).elim
  set K₂ := Kb.map (MulAut.conj t).toMonoidHom with hK₂
  set X := (S.L1.subgroupOf H).map π with hX
  have hXle : X ≤ Kb ⊔ K₂ := by
    have hcc : (conjClosure (K.subgroupOf H) (T.subgroupOf H)).map H.subtype =
        conjClosure K T := by
      rw [A3.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hTH]
    have hcl : conjClosure (K.subgroupOf H) (T.subgroupOf H) ≤ (Kb ⊔ K₂).comap π := by
      refine conjClosure_le fun s hs k hk => ?_
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hs' : π s ∈ Tb := Subgroup.mem_map_of_mem π hs
      have hk' : π k ∈ Kb := Subgroup.mem_map_of_mem π hk
      have hmem : Kb.map (MulAut.conj (π s)).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
        ⟨π s, hs', rfl⟩
      rw [hconj] at hmem
      have hsk : π s * π k * (π s)⁻¹ ∈ Kb.map (MulAut.conj (π s)).toMonoidHom :=
        ⟨π k, hk', by simp [MulAut.conj_apply]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h] at hsk
        exact Subgroup.mem_sup_left hsk
      · rw [h] at hsk
        exact Subgroup.mem_sup_right hsk
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ conjClosure K T := hℓK (Subgroup.mem_subgroupOf.mp hy)
    rw [← hcc] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hcl hz
  have hcomm : ∀ x ∈ Kb, ∀ y ∈ K₂, x * y = y * x :=
    L32Comm.mul_comm_of_commutator_eq_bot hcomm'
  have hcomm2 : ∀ x ∈ K₂, ∀ y ∈ Kb, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hK₂c : K₂ ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := A38.cComp_conj hKbc
  have hU₁ : IsSylowTwoOf (Tb ⊓ Kb) Kb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKbc) hTbs
  have hU₂ : IsSylowTwoOf (Tb ⊓ K₂) K₂ :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₂c) hTbs
  have hK0N1 : Kb ⊔ K₂ ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le Subgroup.le_normalizer fun x hx => L2Comm.mem_normalizer_of_comm hcomm le_rfl hx
  have hK0N2 : Kb ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le (fun x hx => L2Comm.mem_normalizer_of_comm hcomm2 le_rfl hx) Subgroup.le_normalizer
  have hP := S14.plusData_l1plus S (S.hatL1Plus hhat)
  obtain ⟨c₀, hc₀, hc₀3, hc₀O, hdec₀⟩ := l0_decomp hhat
  obtain ⟨c₁, hc₁, hρc₁, hc₁3⟩ := hP.exists_c012_cube
  have hL0H : l0 L ≤ H := S.l0_le_L1.trans hℓH
  have hLpH : l1plus T L V ≤ H := hP.le_L1.trans hℓH
  have hTl0 : T ≤ Subgroup.normalizer (l0 L : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (S.T_le_NL.trans normalizer_L_le_o2Z)
  set X₀ := ((l0 L).subgroupOf H).map π with hX₀
  set X₁ := ((l1plus T L V).subgroupOf H).map π with hX₁
  have hX₀le : X₀ ≤ Kb ⊔ K₂ := (Subgroup.map_mono (f := π)
    (show (l0 L).subgroupOf H ≤ S.L1.subgroupOf H from fun x hx => S.l0_le_L1 hx)).trans hXle
  have hX₁le : X₁ ≤ Kb ⊔ K₂ := (Subgroup.map_mono (f := π)
    (show (l1plus T L V).subgroupOf H ≤ S.L1.subgroupOf H from fun x hx => hP.le_L1 hx)).trans
      hXle
  have hTX₀ : Tb ≤ Subgroup.normalizer (X₀ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hTl0 π
  have hTX₁ : Tb ≤ Subgroup.normalizer (X₁ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hP.T_le π
  obtain ⟨hcb₀3, hcb₀1, hNp₀, hdecb₀⟩ := L2Hat.bar_data π hπ2 hL0H hc₀ hc₀3 hc₀O hdec₀
  obtain ⟨hcb₁3, hcb₁1, hNp₁, hdecb₁⟩ := L2Hat.bar_data π hπ2 hLpH hc₁ hc₁3
    (S14.PlusData.not_mem hρc₁ hc₁3) (fun x hx => hP.decomp hc₁ hρc₁ hx)
  obtain ⟨a, haK, b, hbK, hcab, ha3, ha1, hb3, hb1, haN, hbN⟩ := L2Hat.split_of hcomm' hinf
    hX₀le (hTX₀ htT) (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 (l0 L)) π) hNp₀
    ⟨⟨c₀, hL0H hc₀⟩, Subgroup.mem_subgroupOf.mpr hc₀, rfl⟩ hcb₀3 hcb₀1 hdecb₀ hU₁ hU₂
    (inf_le_left.trans hTX₀) (inf_le_left.trans hTX₀)
  obtain ⟨a', ha'K, b', hb'K, hcab', ha'3, ha'1, hb'3, hb'1, ha'N, hb'N⟩ := L2Hat.split_of hcomm'
    hinf hX₁le (hTX₁ htT) (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 _) π) hNp₁
    ⟨⟨c₁, hLpH hc₁⟩, Subgroup.mem_subgroupOf.mpr hc₁, rfl⟩ hcb₁3 hcb₁1 hdecb₁ hU₁ hU₂
    (inf_le_left.trans hTX₁) (inf_le_left.trans hTX₁)
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  have hKbP : IsPSL 2 2 2 ↥Kb := isPSL_congr e₁ hn
  have hK₂P : IsPSL 2 2 2 ↥K₂ := isPSL_congr (A38.conjEquiv t Kb) hKbP
  have hW : (Tb ⊓ Kb) ⊔ (Tb ⊓ K₂) = Tb ⊓ (Kb ⊔ K₂) := by
    apply le_antisymm
    · exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    · intro u hu
      obtain ⟨k, hk⟩ := L32Comm.exists_pow_of_isPGroup hTbs.2.1 hu.1
      refine L2Comm.mem_sup_of_two_elt hcomm hinf hU₁ hU₂ hu.2 ?_ ?_ hk
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N1 hu.2)
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N2 hu.2)
  have hKbne : Kb ≠ K₂ := fun h => ha1 (by
    have : a ∈ Kb ⊓ K₂ := ⟨haK, h ▸ haK⟩
    rw [hinf] at this
    exact this)
  have hTstab : ∀ s ∈ Tb, s ∈ L2Hat.pairStab Kb K₂ := by
    intro s hs
    have hA : Kb.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Tb Kb := ⟨s, hs, rfl⟩
    have hB : K₂.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
      ⟨s * t, Tb.mul_mem hs htT, L2Hat.map_conj_map_conj Kb t s⟩
    rw [hconj] at hA hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    have hinj : Kb.map (MulAut.conj s).toMonoidHom ≠ K₂.map (MulAut.conj s).toMonoidHom := by
      intro h
      apply hKbne
      calc Kb = (Kb.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
            (L2Hat.map_conj_inv_map_conj Kb s).symm
        _ = (K₂.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by rw [h]
        _ = K₂ := L2Hat.map_conj_inv_map_conj K₂ s
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact absurd (hA.trans hB.symm) hinj
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hB⟩
    · exact absurd (hA.trans hB.symm) hinj
  have hTq : Tb ⊓ (Kb ⊔ K₂) ≤ (Tb ⊓ Kb) ⊔ (Tb ⊓ K₂) := hW.ge
  have hinv : ∀ {x z : ↥H ⧸ CFSG.pCore 2 ↥H}, x ∈ Kb → z ∈ K₂ → (x * z)⁻¹ = x⁻¹ * z⁻¹ :=
    fun hx hz => by rw [mul_inv_rev]; exact (hcomm _ (Kb.inv_mem hx) _ (K₂.inv_mem hz)).symm
  have hmapK : ∀ {w x : ↥H ⧸ CFSG.pCore 2 ↥H} {A B : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)},
      A.map (MulAut.conj w).toMonoidHom = B → x ∈ A → w * x * w⁻¹ ∈ B := by
    intro w x A B h hx
    rw [← h]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hU2 : ∀ {x : ↥H ⧸ CFSG.pCore 2 ↥H} {U : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)},
      IsPGroup 2 U → x ^ 3 = 1 → x ≠ 1 → x ∉ U := by
    intro x U hU hx3 hx1 hxU
    obtain ⟨k, hk⟩ := hU ⟨x, hxU⟩
    exact hx1 (L32Comm.eq_one_of_pow_of_cube (by simpa using congrArg Subtype.val hk) hx3)
  obtain ⟨s, hsTL, hρs⟩ := S14.exists_TL_rho S S14.t0_facts.1 S14.t0_facts.2.1
  have hsH : (s : G) ∈ H := hTH hsTL.1
  have hO₂L : pCoreOf 2 L ≤ T :=
    (pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  have he₀ : (s : G) * c₀ * (s : G)⁻¹ * c₀⁻¹ ∈ T := by
    obtain ⟨-, hc⟩ := mem_o2Z_iff.mp (oTwoRes_le _ hc₀)
    have e : (s : G) * c₀ * (s : G)⁻¹ * c₀⁻¹ = (c₀ * s * c₀⁻¹ * (s : G)⁻¹)⁻¹ := by group
    rw [e]
    exact T.inv_mem (hO₂L (hc s hsTL.2))
  have he₁ : (s : G) * c₁ * (s : G)⁻¹ * c₁ ∈ T := by
    have hm : ((s * c₁ * s⁻¹ * c₁ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ l1plus T L V := by
      have h1 : (s : G) * c₁ * (s : G)⁻¹ ∈ l1plus T L V :=
        (Subgroup.mem_normalizer_iff.mp (hP.T_le hsTL.1) c₁).mp hc₁
      simpa using (l1plus T L V).mul_mem h1 hc₁
    have hK4 : S.frame.ρ (s * c₁ * s⁻¹ * c₁) ∈ K4L := by
      rw [map_mul, map_mul, map_mul, map_inv, hρs, hρc₁]
      decide +kernel
    simpa using hP.pCoreOf_le_T (hP.mem_pCoreOf_of_K4 hm hK4)
  set sb := π ⟨s, hsH⟩ with hsb
  have hsbT : sb ∈ Tb := ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsTL.1, rfl⟩
  have hē₀ : sb * π ⟨c₀, hL0H hc₀⟩ * sb⁻¹ * (π ⟨c₀, hL0H hc₀⟩)⁻¹ ∈ Tb := by
    refine ⟨⟨s, hsH⟩ * ⟨c₀, hL0H hc₀⟩ * ⟨s, hsH⟩⁻¹ * ⟨c₀, hL0H hc₀⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr (by simpa using he₀), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hē₁ : sb * π ⟨c₁, hLpH hc₁⟩ * sb⁻¹ * π ⟨c₁, hLpH hc₁⟩ ∈ Tb := by
    refine ⟨⟨s, hsH⟩ * ⟨c₁, hLpH hc₁⟩ * ⟨s, hsH⟩⁻¹ * ⟨c₁, hLpH hc₁⟩,
      Subgroup.mem_subgroupOf.mpr (by simpa using he₁), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv]
  obtain ⟨hsw₁, hsw₂⟩ : Kb.map (MulAut.conj sb).toMonoidHom = K₂ ∧
      K₂.map (MulAut.conj sb).toMonoidHom = Kb := by
    rcases hTstab sb hsbT with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have hsK : sb ∈ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
        A38.map_conj_eq_iff.mp h1
      refine L2Hat.false_of_inv hKbP hcomm hinf hU₁ inf_le_right hTq haK ha'K hbK hb'K haN
        ha'N ha3 ha1 ha'3 ha'1 hsK (A38.map_conj_eq_iff.mp h2)
        (F7.mem_normalizer_inf (Subgroup.le_normalizer hsbT) hsK) ?_ ?_
      · rw [← hcab]
        exact hē₀
      · rw [← hcab']
        exact hē₁
    · exact ⟨h1, h2⟩
  obtain ⟨f, q', hq', hb'eq⟩ := L2Hat.exists_pow_mul hbN hb3
    (L2Hat.mul_mem_or_in hK₂P hU₂ hbK hb'K hbN hb'N hb3 hb1 hb'3 hb'1)
  have hp₃ : sb * b * sb⁻¹ * a⁻¹ ∈ Tb ⊓ Kb := by
    refine L2Hat.comp_of_swaps hcomm hinf inf_le_right inf_le_right hTq (hmapK hsw₁ haK)
      (hmapK hsw₂ hbK) (Kb.inv_mem haK) (K₂.inv_mem hbK) (Tq := Tb) ?_
    rw [← hinv haK hbK, ← hcab]
    exact hē₀
  have hp₄ : sb * b' * sb⁻¹ * a' ∈ Tb ⊓ Kb := by
    refine L2Hat.comp_of_swaps hcomm hinf inf_le_right inf_le_right hTq (hmapK hsw₁ ha'K)
      (hmapK hsw₂ hb'K) ha'K hb'K (Tq := Tb) ?_
    rw [← hcab']
    exact hē₁
  have haQ : a ∉ Tb ⊓ Kb := hU2 hU₁.2.1 ha3 ha1
  have hbQ : b ∉ Tb ⊓ K₂ := hU2 hU₂.2.1 hb3 hb1
  have hKTb : Kb ⊔ Tb = ⊤ := by
    have h1 : (K.subgroupOf H ⊔ T.subgroupOf H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, Subgroup.subgroupOf_eq_top, ← hHK]
    rw [hKb, hTb, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  have hK₀N : ⊤ ≤ Subgroup.normalizer ((Kb ⊔ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [← hKTb]
    exact sup_le (le_sup_left.trans Subgroup.le_normalizer) hTN
  have hK₀n : (Kb ⊔ K₂).Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hK₀N)
  have h2 : ∀ x : ↥H ⧸ CFSG.pCore 2 ↥H, ∃ e : ℕ, x ^ 2 ^ e ∈ Kb ⊔ K₂ := by
    intro x
    have hle : Kb ⊔ Tb ≤ (Kb ⊔ K₂) ⊔ Tb := sup_le_sup_right le_sup_left Tb
    exact InternalSec.two_of_sup hTbs.2.1 hTN x (hle (hKTb ▸ Subgroup.mem_top x))
  have hZ : ∀ x ∈ Kb ⊔ K₂, (∀ y ∈ Kb ⊔ K₂, x * y = y * x) → x = 1 := by
    intro x hx hxc
    have hN : Kb ≤ Subgroup.normalizer (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := fun u hu =>
      L2Comm.mem_normalizer_of_comm hcomm2 le_rfl hu
    have hmul : ((Kb ⊔ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) =
        (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) * (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      Subgroup.coe_mul_of_left_le_normalizer_right Kb K₂ hN
    have hx' : x ∈ (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) * (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← hmul]
      exact hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Set.mem_mul.mp hx'
    have h1 : x₁ = 1 := L2Hat.eq_one_of_central hKbP hU₁ haK haN ha3 ha1 hx₁ fun y hy => by
      have h3 := hxc y (Subgroup.mem_sup_left hy)
      have hc := hcomm2 x₂ hx₂ y hy
      calc x₁ * y = x₁ * (y * x₂) * x₂⁻¹ := by group
        _ = x₁ * (x₂ * y) * x₂⁻¹ := by rw [hc]
        _ = (x₁ * x₂ * y) * x₂⁻¹ := by group
        _ = (y * (x₁ * x₂)) * x₂⁻¹ := by rw [h3]
        _ = y * x₁ := by group
    have h2 : x₂ = 1 := L2Hat.eq_one_of_central hK₂P hU₂ hbK hbN hb3 hb1 hx₂ fun y hy => by
      have h3 := hxc y (Subgroup.mem_sup_right hy)
      have hc := hcomm x₁ hx₁ y hy
      calc x₂ * y = x₁⁻¹ * (x₁ * x₂ * y) := by group
        _ = x₁⁻¹ * (y * (x₁ * x₂)) := by rw [h3]
        _ = x₁⁻¹ * (y * x₁) * x₂ := by group
        _ = x₁⁻¹ * (x₁ * y) * x₂ := by rw [hc]
        _ = y * x₂ := by group
    rw [h1, h2, one_mul]
  have hO2 : CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ :=
    CFSG.QuasithinUnique.Setup.Campbell.pCore_quotient_pCore_eq_bot' 2
  have hK₀im : Kb ⊔ K₂ ≤ ((conjClosure K T).subgroupOf H).map π := by
    have hKK₀ : Kb ≤ ((conjClosure K T).subgroupOf H).map π :=
      Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (le_conjClosure K T (Subgroup.mem_subgroupOf.mp hx))
    refine sup_le hKK₀ ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨t', ht', rfl⟩ := htT
    obtain ⟨k', hk', rfl⟩ := hk
    refine ⟨t' * k' * t'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using mem_conjClosure (Subgroup.mem_subgroupOf.mp ht') (Subgroup.mem_subgroupOf.mp hk')
    · simp [MulAut.conj_apply]
  intro y hy
  have hyH : y ∈ H := ((pCoreOf_le 2 _).trans (sup_le hℓH hTH)) hy
  have hyT : y ∈ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right hy
  have hyc : ∀ c ∈ S.L1, y * c * y⁻¹ * c⁻¹ ∈ T := fun c hc => by
    have h1 : c * y⁻¹ * c⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hc))
        _).mp (Subgroup.inv_mem _ hy)
    have e : y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) := by group
    rw [e]
    exact pCoreOf_le_of_sylow S.h13.sylow le_sup_right (Subgroup.mul_mem _ hy h1)
  set yb := π ⟨y, hyH⟩ with hyb
  have hybT : yb ∈ Tb := ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hyT, rfl⟩
  have hyc₀ : yb * π ⟨c₀, hL0H hc₀⟩ * yb⁻¹ * (π ⟨c₀, hL0H hc₀⟩)⁻¹ ∈ Tb := by
    refine ⟨⟨y, hyH⟩ * ⟨c₀, hL0H hc₀⟩ * ⟨y, hyH⟩⁻¹ * ⟨c₀, hL0H hc₀⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr (by simpa using hyc c₀ (S.l0_le_L1 hc₀)), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hyc₁ : yb * π ⟨c₁, hLpH hc₁⟩ * yb⁻¹ * (π ⟨c₁, hLpH hc₁⟩)⁻¹ ∈ Tb := by
    refine ⟨⟨y, hyH⟩ * ⟨c₁, hLpH hc₁⟩ * ⟨y, hyH⟩⁻¹ * ⟨c₁, hLpH hc₁⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr (by simpa using hyc c₁ (hP.le_L1 hc₁)), ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hyK₀ : yb ∈ Kb ⊔ K₂ := by
    rcases hTstab yb hybT with ⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩
    ·
      have hyN₁ := A38.map_conj_eq_iff.mp hy₁
      have hyN₂ := A38.map_conj_eq_iff.mp hy₂
      have h0 : yb * (a * b) * yb⁻¹ * (a⁻¹ * b⁻¹) ∈ Tb := by
        rw [← hinv haK hbK, ← hcab]
        exact hyc₀
      obtain ⟨hya, hyb'⟩ := L2Hat.comp_of_normalizes hcomm hinf inf_le_right inf_le_right hTq hyN₁
        hyN₂ haK (Kb.inv_mem haK) hbK (K₂.inv_mem hbK) h0
      obtain ⟨k₁, hk₁, k₂, hk₂, hz₁, hz₂⟩ := L2Aut.exists_centralizing hcomm hKbP hK₂P hU₁ hU₂ hyN₁
        hyN₂ (F7.mem_normalizer_inf (Subgroup.le_normalizer hybT) hyN₁)
        (F7.mem_normalizer_inf (Subgroup.le_normalizer hybT) hyN₂) haK hbK haN hbN haQ hbQ hya hyb'
      have hz : ∀ x ∈ Kb ⊔ K₂, (k₁ * k₂)⁻¹ * yb * x = x * ((k₁ * k₂)⁻¹ * yb) := by
        have hle : Kb ⊔ K₂ ≤ Subgroup.centralizer {(k₁ * k₂)⁻¹ * yb} := by
          refine sup_le (fun x hx => ?_) (fun x hx => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact (hz₁ x hx).symm
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact (hz₂ x hx).symm
        intro x hx
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
      have hz1 := L2Aut.eq_one_of_centralizes hK₀n h2 hZ hO2 hz
      rw [← inv_mul_eq_one.mp hz1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk₁) (Subgroup.mem_sup_right hk₂)
    ·
      exfalso
      have hp₁ : yb * b * yb⁻¹ * a⁻¹ ∈ Tb ⊓ Kb := by
        refine L2Hat.comp_of_swaps hcomm hinf inf_le_right inf_le_right hTq (hmapK hy₁ haK)
          (hmapK hy₂ hbK) (Kb.inv_mem haK) (K₂.inv_mem hbK) (Tq := Tb) ?_
        rw [← hinv haK hbK, ← hcab]
        exact hyc₀
      have hp₂ : yb * b' * yb⁻¹ * a'⁻¹ ∈ Tb ⊓ Kb := by
        refine L2Hat.comp_of_swaps hcomm hinf inf_le_right inf_le_right hTq (hmapK hy₁ ha'K)
          (hmapK hy₂ hb'K) (Kb.inv_mem ha'K) (K₂.inv_mem hb'K) (Tq := Tb) ?_
        rw [← hinv ha'K hb'K, ← hcab']
        exact hyc₁
      have hq₁ : yb * q' * yb⁻¹ ∈ Tb ⊓ Kb :=
        ⟨Tb.mul_mem (Tb.mul_mem hybT hq'.1) (Tb.inv_mem hybT), hmapK hy₂ hq'.2⟩
      have hq₂ : sb * q' * sb⁻¹ ∈ Tb ⊓ Kb :=
        ⟨Tb.mul_mem (Tb.mul_mem hsbT hq'.1) (Tb.inv_mem hsbT), hmapK hsw₂ hq'.2⟩
      have haf : a ^ f ∈ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
          Set (↥H ⧸ CFSG.pCore 2 ↥H)) := Subgroup.pow_mem _ haN f
      have eb : ∀ w : ↥H ⧸ CFSG.pCore 2 ↥H,
          w * b' * w⁻¹ = (w * b * w⁻¹ * a⁻¹ * a) ^ f * (w * q' * w⁻¹) := fun w => by
        rw [show w * b * w⁻¹ * a⁻¹ * a = w * b * w⁻¹ by group, conj_pow, hb'eq]
        group
      have hA : a' * (a ^ f)⁻¹ ∈ Tb ⊓ Kb := by
        set X := yb * b' * yb⁻¹ with hX
        have e : a' * (a ^ f)⁻¹ = (X * a'⁻¹)⁻¹ *
            ((yb * b * yb⁻¹ * a⁻¹ * a) ^ f * (a ^ f)⁻¹) *
            (a ^ f * (yb * q' * yb⁻¹) * (a ^ f)⁻¹) := by
          rw [show (yb * b * yb⁻¹ * a⁻¹ * a) ^ f = X * (yb * q' * yb⁻¹)⁻¹ by rw [hX, eb yb]; group]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hp₂)
          (L2Hat.pow_mul_mem hp₁ haN f)) ((Subgroup.mem_normalizer_iff.mp haf _).mp hq₁)
      have hB : a'⁻¹ * (a ^ f)⁻¹ ∈ Tb ⊓ Kb := by
        set Y := sb * b' * sb⁻¹ with hY
        have e : a'⁻¹ * (a ^ f)⁻¹ = (Y * a')⁻¹ *
            ((sb * b * sb⁻¹ * a⁻¹ * a) ^ f * (a ^ f)⁻¹) *
            (a ^ f * (sb * q' * sb⁻¹) * (a ^ f)⁻¹) := by
          rw [show (sb * b * sb⁻¹ * a⁻¹ * a) ^ f = Y * (sb * q' * sb⁻¹)⁻¹ by rw [hY, eb sb]; group]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hp₄)
          (L2Hat.pow_mul_mem hp₃ haN f)) ((Subgroup.mem_normalizer_iff.mp haf _).mp hq₂)
      exact L2Hat.false_of_mem_coset hU₁.2.1 ha'3 ha'1 hA hB
  obtain ⟨k, hk, hkπ⟩ := hK₀im hyK₀
  have hq : k⁻¹ * ⟨y, hyH⟩ ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥H), MonoidHom.mem_ker, map_mul, map_inv]
    exact inv_mul_eq_one.mpr hkπ
  have e : y = (k : G) * ((k⁻¹ * ⟨y, hyH⟩ : ↥H) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk))
    (Subgroup.mem_sup_right ((mem_pCore_iff _).1 hq))

end Setting4

end CFSG.Quasithin.H13.A6
