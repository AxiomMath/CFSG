module

public import CFSG.Quasithin.H13.GoldschmidtU43EIdx6
public import CFSG.Quasithin.H13.GoldschmidtU43EIdx7
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm10
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm11
public import CFSG.Quasithin.H13.GoldschmidtU43EV3

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem normalizer_preimage_le_Ng_of_unique (P : Subgroup S.Nbar)
    (huniq : ∀ M' : Subgroup G, M' ≤ S.preimageNbar P →
      (∀ a ∈ M', ∀ b ∈ M', a * b = b * a) → Nat.card M' = 81 → M' = S.Mg) {x : G}
    (hx : x ∈ Subgroup.normalizer (S.preimageNbar P : Set G)) : x ∈ S.Ng := by
  set Sg := S.preimageNbar P with hSg
  have hMS : S.Mg ≤ Sg := S.Mg_le_preimageNbar _
  have hle : S.Mg.map (MulAut.conj x).toMonoidHom ≤ Sg := by
    rintro _ ⟨m, hm, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx m).mp (hMS hm)
  have hab : ∀ a ∈ S.Mg.map (MulAut.conj x).toMonoidHom, ∀ b ∈ S.Mg.map
      (MulAut.conj x).toMonoidHom, a * b = b * a := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
    show x * m * x⁻¹ * (x * m' * x⁻¹) = x * m' * x⁻¹ * (x * m * x⁻¹)
    have := S.abelian_Mg m hm m' hm'
    calc x * m * x⁻¹ * (x * m' * x⁻¹) = x * (m * m') * x⁻¹ := by group
      _ = x * (m' * m) * x⁻¹ := by rw [this]
      _ = x * m' * x⁻¹ * (x * m * x⁻¹) := by group
  have hcard : Nat.card (S.Mg.map (MulAut.conj x).toMonoidHom) = 81 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, S.card_Mg_eq_81]
  have heq := huniq _ hle hab hcard
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨m, hm, hmh⟩ := hh
    have : m = h := by
      have h' : x * m * x⁻¹ = x * h * x⁻¹ := hmh
      simpa using h'
    rw [← this]
    exact hm

theorem exists_sylow_preimage_of_unique (P : Sylow 3 S.Nbar)
    (huniq : ∀ M' : Subgroup G, M' ≤ S.preimageNbar (P : Subgroup S.Nbar) →
      (∀ a ∈ M', ∀ b ∈ M', a * b = b * a) → Nat.card M' = 81 → M' = S.Mg) :
    ∃ Q : Sylow 3 G, (Q : Subgroup G) = S.preimageNbar (P : Subgroup S.Nbar) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have hpre : ∀ w : ↥S.Ng, (w : G) ∈ S.preimageNbar (P : Subgroup S.Nbar) ↔
      S.piN w ∈ (P : Subgroup S.Nbar) := by
    intro w
    constructor
    · intro h
      exact (S.mem_preimageNbar.mp h).2
    · intro h
      exact S.mem_preimageNbar.mpr ⟨w.2, h⟩
  refine u43_exists_sylow_eq (p := 3) (Y := S.preimageNbar (P : Subgroup S.Nbar)) ?_ ?_
  · exact IsPGroup.of_card (n := 4 + j) (by rw [S.card_preimageNbar, hj]; ring)
  · intro x hx hxp
    have hxN : x ∈ S.Ng := S.normalizer_preimage_le_Ng_of_unique _ huniq hx
    set n : ↥S.Ng := ⟨x, hxN⟩ with hn
    have hnorm : S.piN n ∈ Subgroup.normalizer ((P : Subgroup S.Nbar) : Set S.Nbar) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
      have e1 : S.piN n * (w : S.Nbar) * (S.piN n)⁻¹ = S.piN (n * w * n⁻¹) := by
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [e1]
      have e2 : ((n * w * n⁻¹ : ↥S.Ng) : G) = x * w * x⁻¹ := rfl
      have e3 : (w : S.Nbar) = S.piN w := rfl
      rw [e3, ← hpre, ← hpre, e2]
      exact Subgroup.mem_normalizer_iff.mp hx w
    have hpow : ∃ k : ℕ, x ^ 3 ^ k = 1 := by
      have := (isPGroup_iff_pow_pow_eq_one.mp hxp) ⟨x, Subgroup.mem_zpowers x⟩
      obtain ⟨k, hk⟩ := this
      exact ⟨k, congrArg Subtype.val hk⟩
    obtain ⟨k, hk⟩ := hpow
    have hgk : S.piN n ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : n ^ 3 ^ k = 1 := Subtype.ext hk
      rw [this, map_one]
    have hgp : IsPGroup 3 (Subgroup.zpowers (S.piN n)) := by
      apply IsPGroup.of_card_dvd_pow (n := k)
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hgk
    have h1 := hgp.inf_normalizer_sylow P
    have h2' : Subgroup.zpowers (S.piN n) ≤ Subgroup.normalizer (P : Set S.Nbar) :=
      (Subgroup.zpowers_le).mpr hnorm
    rw [inf_eq_left.mpr h2'] at h1
    have h3 : S.piN n ∈ (P : Subgroup S.Nbar) :=
      (inf_le_right : Subgroup.zpowers (S.piN n) ⊓ (P : Subgroup S.Nbar) ≤ _)
        (h1 ▸ Subgroup.mem_zpowers (S.piN n))
    exact S.mem_preimageNbar.mpr ⟨hxN, h3⟩

theorem false_of_index_two
    (hAU : (S.A : G) ∈ Uz z) {J : Subgroup S.Nbar} (hJ : J.index = 2) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ν, hν3, hν1, hrel⟩ := S.exists_nu_of_index_two hJ
  have hcard := S.card_Nbar_of_index_two hJ
  have hord : orderOf ν = 3 := orderOf_eq_prime hν3 hν1
  have hzp : IsPGroup 3 (Subgroup.zpowers ν) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hP3 : Nat.card P = 3 := card_sylow_three_of_card_24_or_120 hcard P
  have hPeq : (P : Subgroup S.Nbar) = Subgroup.zpowers ν :=
    (Subgroup.eq_of_le_of_card_ge hP (by rw [hP3, Nat.card_zpowers, hord])).symm
  obtain ⟨Q, hQ⟩ := S.exists_sylow_preimage_of_unique P (fun M' h1 h2 h3 =>
    S.unique_abelian_Mnu hν3 hrel hPeq hP3 h1 h2 h3)
  have hQcard : Nat.card Q = 243 := by
    rw [hQ, S.card_preimageNbar, hP3]
  obtain ⟨Q', hQ'p, hQ'card, -⟩ := S.exists_big_three_group hAU
  obtain ⟨Q'', hle⟩ := hQ'p.exists_le_sylow
  have h1 : Nat.card Q'' = Nat.card Q := by
    rw [Sylow.card_eq_multiplicity Q'', Sylow.card_eq_multiplicity Q]
  have h2 : Nat.card Q' ≤ Nat.card Q'' := Subgroup.card_le_of_le hle
  omega

theorem Nbar_iso_A6
    (hAU : (S.A : G) ∈ Uz z) : Nonempty (S.Nbar ≃* alternatingGroup (Fin 6)) := by
  rcases S.Nbar_classify with ⟨J, hJ⟩ | h168 | h
  · exact (S.false_of_index_two hAU hJ).elim
  · exact (S.card_Nbar_ne_168 h168).elim
  · exact h

end JWSetup

end CFSG.Quasithin.H13.U43
