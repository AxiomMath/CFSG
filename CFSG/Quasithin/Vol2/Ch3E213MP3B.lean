module

public import CFSG.Quasithin.Vol2.Ch3E213MP3A
public import CFSG.Quasithin.H13.QRCPairedFactors
public import CFSG.Quasithin.H13.QRCPairLift

public section

namespace CFSG.Quasithin.Ch3E213M.P3

open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F] {p : ℕ}

section Factor

variable {K₁ : Subgroup Y}

omit [Finite Y] in
theorem seven_le (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) : 7 ≤ p := by
  have := hp.two_le
  omega

omit [Finite Y] [Finite F] in
theorem isSimpleGroup_of (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hF : Nat.card F = p)
    (θ : K₁ ≃* PSL2 F) : IsSimpleGroup K₁ := by
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    (by rw [hF]; have := seven_le hp hp8; omega)
  exact θ.isSimpleGroup

omit [Finite Y] in
theorem eq_one_of_central (θ : K₁ ≃* PSL2 F) {z : Y} (hz : z ∈ K₁)
    (h : ∀ y ∈ K₁, z * y = y * z) : z = 1 := by
  have h1 : θ ⟨z, hz⟩ ∈ center (PSL2 F) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := θ.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (h y y.2).symm)
  rw [psl2_center_eq_bot, mem_bot, MulEquiv.map_eq_one_iff] at h1
  exact congrArg Subtype.val h1

omit [Finite Y] in
theorem eight_dvd_card_inf (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hF : Nat.card F = p)
    (θ : K₁ ≃* PSL2 F) {S : Subgroup Y} (hS : IsSylowTwoOf (S ⊓ K₁) K₁) :
    2 ^ 3 ∣ Nat.card (S ⊓ K₁ : Subgroup Y) := by
  have h8 : 2 ^ 3 ∣ Nat.card K₁ := Nat.card_congr θ.toEquiv ▸ eight_dvd_card hp hp8 hF
  have hc := card_mul_index ((S ⊓ K₁).subgroupOf K₁)
  rw [Nat.card_congr (subgroupOfEquivOfLe hS.1).toEquiv] at hc
  have hcop : Nat.Coprime (2 ^ 3) ((S ⊓ K₁).subgroupOf K₁).index :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS.2.2)
  exact hcop.dvd_of_dvd_mul_right (hc ▸ h8)

omit [Finite Y] in
theorem card_le_four_of_sq
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p) (θ : K₁ ≃* PSL2 F) {Q : Subgroup Y}
    (hQ : Q ≤ K₁) (h2 : ∀ y ∈ Q, y * y = 1) : Nat.card Q ≤ 4 := by
  set f : K₁ →* PGammaL2 F := (incl F).comp θ.toMonoidHom with hf
  have hfi : Function.Injective f := (incl_injective F).comp θ.injective
  have h := pGammaL2_card_le_four_of_sq_of_prime hp hp2 hF ((Q.subgroupOf K₁).map f) (by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (h2 _ hy)
    rw [this, map_one])
  rwa [card_map_of_injective hfi, Nat.card_congr (subgroupOfEquivOfLe hQ).toEquiv] at h

end Factor

variable {K₁ K₂ S E : Subgroup Y}

theorem le_normalizer_of_sylow
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hF : Nat.card F = p) (θ : K₁ ≃* PSL2 F)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hcard : Nat.card K₁ = Nat.card K₂) (hS : IsSylowTwoOf S ⊤)
    (hSE : S ≤ normalizer (E : Set Y)) (hE2 : ∀ e ∈ E, e * e = 1) :
    E ≤ normalizer (K₁ : Set Y) := by
  have := isSimpleGroup_of hp hp8 hF θ
  have hp2 : p ≠ 2 := by omega
  intro v hv
  rcases H13.QRC.conj_factor_eq_or hc hKn (fun z hz h => eq_one_of_central θ hz h) hcard v
    with h | h
  · exact mem_normalizer_iff_map_conj_eq.mpr h
  exfalso
  have hSK : IsSylowTwoOf (S ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂) :=
    A4.isSylowTwoOf_inf_normal hS le_top (normalizer_eq_top_iff.mpr hKn).ge
  have hSK₁ : IsSylowTwoOf (S ⊓ K₁) K₁ := by
    have h1 := A4.isSylowTwoOf_inf_normal hSK le_sup_left
      (sup_le le_normalizer (H13.QRC.le_normalizer_of_commute hc))
    rwa [inf_assoc, inf_eq_right.mpr (le_sup_left : K₁ ≤ K₁ ⊔ K₂)] at h1
  have h8 := eight_dvd_card_inf hp hp8 hF θ hSK₁
  have hsq : ∀ y ∈ S ⊓ K₁, y * y = 1 := by
    rintro y ⟨hyS, hyK⟩
    have hu : v * y * v⁻¹ ∈ K₂ := by
      rw [← h]
      exact ⟨y, hyK, rfl⟩
    have hcE : v * y * v⁻¹ * y⁻¹ ∈ E := by
      have h1 : y * v⁻¹ * y⁻¹ ∈ E := (mem_normalizer_iff.mp (hSE hyS) v⁻¹).mp (E.inv_mem hv)
      have e : v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
      rw [e]
      exact E.mul_mem hv h1
    have hcc := hE2 _ hcE
    set u := v * y * v⁻¹ with hudef
    have hyu : y⁻¹ * u = u * y⁻¹ := hc _ (K₁.inv_mem hyK) u hu
    have e : u * y⁻¹ * (u * y⁻¹) = u * u * (y⁻¹ * y⁻¹) := by
      calc u * y⁻¹ * (u * y⁻¹) = u * (y⁻¹ * u) * y⁻¹ := by group
        _ = u * (u * y⁻¹) * y⁻¹ := by rw [hyu]
        _ = u * u * (y⁻¹ * y⁻¹) := by group
    rw [e] at hcc
    have huu : u * u = y * y := by
      calc u * u = (y⁻¹ * y⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hcc
        _ = y * y := by rw [mul_inv_rev, inv_inv]
    have hmem : y * y ∈ K₁ ⊓ K₂ := ⟨K₁.mul_mem hyK hyK, huu ▸ K₂.mul_mem hu hu⟩
    rwa [hd, mem_bot] at hmem
  have h4 := card_le_four_of_sq hp hp2 hF θ inf_le_right hsq
  have := Nat.le_of_dvd Nat.card_pos h8
  omega

theorem card_le_sq {t : Y} (hCK : ∀ a : Y, (∀ k ∈ K₁ ⊔ K₂, a * k = k * a) → a = 1)
    (hK₂ : K₁.map (MulAut.conj t).toMonoidHom = K₂) (htE : t ∈ normalizer (E : Set Y)) :
    Nat.card E ≤ (E ⊓ centralizer (K₁ : Set Y)).relIndex E ^ 2 := by
  set A₁ := E ⊓ centralizer (K₁ : Set Y) with hA₁
  set A₂ := E ⊓ centralizer (K₂ : Set Y) with hA₂
  have hA : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨-, hz₁⟩, -, hz₂⟩
    rw [mem_bot]
    have hle : K₁ ⊔ K₂ ≤ centralizer ({z} : Set Y) := by
      refine sup_le (fun k hk => mem_centralizer_iff.mpr fun h hh => ?_)
        (fun k hk => mem_centralizer_iff.mpr fun h hh => ?_)
      · rw [Set.mem_singleton_iff.mp hh]
        exact (mem_centralizer_iff.mp hz₁ k hk).symm
      · rw [Set.mem_singleton_iff.mp hh]
        exact (mem_centralizer_iff.mp hz₂ k hk).symm
    exact hCK z fun k hk => mem_centralizer_iff.mp (hle hk) z rfl
  have hmap : A₁.map (MulAut.conj t).toMonoidHom ≤ A₂ := by
    rintro _ ⟨a, ⟨haE, haC⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.mp htE a).mp haE, mem_centralizer_iff.mpr fun k hk => ?_⟩
    rw [← hK₂] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    have h1 : k' * a = a * k' := mem_centralizer_iff.mp haC k' hk'
    change t * k' * t⁻¹ * (t * a * t⁻¹) = t * a * t⁻¹ * (t * k' * t⁻¹)
    calc t * k' * t⁻¹ * (t * a * t⁻¹) = t * (k' * a) * t⁻¹ := by group
      _ = t * (a * k') * t⁻¹ := by rw [h1]
      _ = t * a * t⁻¹ * (t * k' * t⁻¹) := by group
  have hEt : E.map (MulAut.conj t).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.mp htE
  have hne : (A₁.map (MulAut.conj t).toMonoidHom).relIndex E ≠ 0 := by
    have h1 := relIndex_mul_card (A₁.map (MulAut.conj t).toMonoidHom) E
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have h2 : A₂.relIndex E ≤ A₁.relIndex E := by
    have h3 := relIndex_map_map_of_injective (f := (MulAut.conj t).toMonoidHom) A₁ E
      (MulAut.conj t).injective
    rw [hEt] at h3
    exact h3 ▸ relIndex_le_of_le_left hmap hne
  calc Nat.card E = (A₁ ⊓ A₂).relIndex E := by rw [hA, relIndex_bot_left]
    _ ≤ A₁.relIndex E * A₂.relIndex E := relIndex_inf_le
    _ ≤ A₁.relIndex E * A₁.relIndex E := Nat.mul_le_mul_left _ h2
    _ = A₁.relIndex E ^ 2 := (sq _).symm

theorem autCard_le_eight
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p) (θ : K₁ ≃* PSL2 F) (hS2 : IsPGroup 2 S)
    (hSE : S ≤ normalizer (E : Set Y)) (hEN : E ≤ normalizer (K₁ : Set Y))
    (hE2 : ∀ e ∈ E, e * e = 1) (h4 : 4 ≤ (E ⊓ centralizer (K₁ : Set Y)).relIndex E) :
    E2.autCard S K₁ ≤ 8 := by
  set W := autSub θ E with hW
  have hWcard : Nat.card W = (E ⊓ centralizer (K₁ : Set Y)).relIndex E := by
    rw [hW, card_autSub, E2.autCard, inf_eq_left.mpr hEN]
  have hW2 : ∀ w ∈ W, w * w = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul]
    have : e * e = 1 := Subtype.ext (hE2 _ he)
    rw [this, map_one]
  have hW4 : Nat.card W = 4 :=
    le_antisymm (pGammaL2_card_le_four_of_sq_of_prime hp hp2 hF W hW2) (hWcard ▸ h4)
  have hC := centralizer_eq_self hp hp2 hF hW4 hW2
  rw [← card_autSub θ S]
  refine card_le_eight_of_le_normalizer hW4 hW2 hC.le (hS2.comap_subtype.map (act θ)) ?_
  rintro _ ⟨s, hs, rfl⟩
  refine mem_normalizer_fintype fun w hw => ?_
  obtain ⟨e, he, rfl⟩ := hw
  rw [← map_mul, ← map_inv, ← map_mul]
  refine ⟨s * e * s⁻¹, ?_, rfl⟩
  exact (mem_normalizer_iff.mp (hSE hs) e).mp he

omit [Finite Y] in
theorem eq_one_or_eq_of_mem_zpowers {a z : Y} (ha : a * a = 1) (hz : z ∈ zpowers a) :
    z = 1 ∨ z = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem exists_eq_sup (hp : p.Prime)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hF : Nat.card F = p) (θ : K₁ ≃* PSL2 F) {t : Y}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ a : Y, (∀ k ∈ K₁ ⊔ K₂, a * k = k * a) → a = 1) (hS : IsSylowTwoOf S ⊤)
    (htS : t ∈ S) (hK₂ : K₁.map (MulAut.conj t).toMonoidHom = K₂)
    (hSE : S ≤ normalizer (E : Set Y)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE4 : 4 ≤ Nat.card E) (haut : 8 < E2.autCard S K₁) :
    E ≤ normalizer (K₁ : Set Y) ∧ ∃ a ∈ E, a ∉ centralizer (K₁ : Set Y) ∧
      E = zpowers a ⊔ (E ⊓ centralizer (K₁ : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card K₁ = Nat.card K₂ := by
    rw [← hK₂, card_map_of_injective (MulAut.conj t).injective]
  have hEN := le_normalizer_of_sylow hp hp8 hF θ hc hd hKn hcard hS hSE hE2
  set A₁ := E ⊓ centralizer (K₁ : Set Y) with hA₁
  have hr4 : A₁.relIndex E < 4 := by
    by_contra h4
    exact absurd (autCard_le_eight hp hp2 hF θ hS.2.1 hSE hEN hE2 (not_lt.mp h4)) (by omega)
  have hsq : Nat.card E ≤ A₁.relIndex E ^ 2 := card_le_sq hCK hK₂ (hSE htS)
  have hE2g : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hE2 _ x.2)⟩
  obtain ⟨n, hn⟩ := hE2g.exists_card_eq
  obtain ⟨j, -, hrj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hn ▸ relIndex_dvd_card A₁ E)
  have hr2 : A₁.relIndex E = 2 := by
    rw [hrj] at hsq hr4 ⊢
    have hj : j < 2 := by
      by_contra h
      have := Nat.pow_le_pow_right two_pos (not_lt.mp h)
      omega
    interval_cases j
    · rw [pow_zero] at hsq
      omega
    · rfl
  obtain ⟨a, haE, haA⟩ : ∃ a ∈ E, a ∉ A₁ := by
    by_contra h
    push Not at h
    have : A₁.relIndex E = 1 := relIndex_eq_one.mpr h
    omega
  refine ⟨hEN, a, haE, fun h => haA ⟨haE, h⟩, ?_⟩
  have hle : zpowers a ⊔ A₁ ≤ E := sup_le (zpowers_le.mpr haE) inf_le_left
  have hza : zpowers a ⊓ A₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz, hzA⟩
    rcases eq_one_or_eq_of_mem_zpowers (hE2 a haE) hz with rfl | rfl
    · exact one_mem _
    · exact absurd hzA haA
  have ha1 : a ≠ 1 := fun h => haA (h ▸ one_mem _)
  have hza2 : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hE2 a haE) ha1
  have hcardE : Nat.card E = 2 * Nat.card A₁ := by
    have h1 := relIndex_mul_card A₁ E
    rw [hr2, inf_eq_left.mpr inf_le_left] at h1
    exact h1.symm
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [H13.QRC.card_sup_of_commute
    (fun x hx y hy => hEc x (zpowers_le.mpr haE hx) y ((inf_le_left : A₁ ≤ E) hy)) hza,
    hza2, hcardE]

end CFSG.Quasithin.Ch3E213M.P3
