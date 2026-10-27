module

public import CFSG.Quasithin.H13.GoldschmidtU43EA6Syl2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (P : Sylow 3 S.Nbar)

theorem mem_preimageNbar_iff {Q : Subgroup S.Nbar} (w : ↥S.Ng) :
    (w : G) ∈ S.preimageNbar Q ↔ S.piN w ∈ Q := by
  constructor
  · intro h
    obtain ⟨hN, h'⟩ := S.mem_preimageNbar.mp h
    exact h'
  · intro h
    exact S.mem_preimageNbar.mpr ⟨w.2, h⟩

theorem normalizer_preimage_le_Ng (e : S.Nbar ≃* alternatingGroup (Fin 6)) {x : G}
    (hx : x ∈ Subgroup.normalizer (S.preimageNbar (P : Subgroup S.Nbar) : Set G)) :
    x ∈ S.Ng := by
  set Sg := S.preimageNbar (P : Subgroup S.Nbar) with hSg
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
  have heq := S.unique_abelian_Msyl P e hle hab hcard
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

theorem exists_sylow_preimage (e : S.Nbar ≃* alternatingGroup (Fin 6)) :
    ∃ Q : Sylow 3 G, (Q : Subgroup G) = S.preimageNbar (P : Subgroup S.Nbar) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.card P = 9 := card_sylow_three_of_card_360 (S.card_Nbar_of_iso e) P
  refine u43_exists_sylow_eq (p := 3) (Y := S.preimageNbar (P : Subgroup S.Nbar)) ?_ ?_
  · exact IsPGroup.of_card (n := 6) (by rw [S.card_preimageNbar, h9]; norm_num)
  · intro x hx hxp
    have hxN : x ∈ S.Ng := S.normalizer_preimage_le_Ng P e hx
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
      rw [e3, ← S.mem_preimageNbar_iff, ← S.mem_preimageNbar_iff, e2]
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
    have h2 : Subgroup.zpowers (S.piN n) ≤
        Subgroup.normalizer ((P : Subgroup S.Nbar) : Set S.Nbar) :=
      (Subgroup.zpowers_le).mpr hnorm
    have h2' : Subgroup.zpowers (S.piN n) ≤ Subgroup.normalizer (P : Set S.Nbar) := h2
    rw [inf_eq_left.mpr h2'] at h1
    have h3 : S.piN n ∈ (P : Subgroup S.Nbar) :=
      (inf_le_right : Subgroup.zpowers (S.piN n) ⊓ (P : Subgroup S.Nbar) ≤ _)
        (h1 ▸ Subgroup.mem_zpowers (S.piN n))
    exact S.mem_preimageNbar.mpr ⟨hxN, h3⟩

end JWSetup

end CFSG.Quasithin.H13.U43
