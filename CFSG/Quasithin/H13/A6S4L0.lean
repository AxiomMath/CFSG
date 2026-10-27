module

public import CFSG.Quasithin.H13.A5S1520b
public import CFSG.Quasithin.H13.A6S4Reduced

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section General

variable {G : Type} [Group G]

theorem oTwoRes_mono {X Y : Subgroup G} (h : X ≤ Y) : oTwoRes X ≤ oTwoRes Y := by
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨hy, m, hm, hym⟩
  exact Subgroup.subset_closure ⟨h hy, m, hm, hym⟩

theorem mem_o2Z_iff {L : Subgroup G} {y : G} :
    y ∈ o2Z L ↔ ∃ _ : y ∈ L, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  constructor
  · intro h
    obtain ⟨y', hy', rfl⟩ := h
    exact ⟨y'.2, fun l hl => comm_mem_of_mem_o2Z ⟨y', hy', rfl⟩ hl⟩
  · rintro ⟨hy, hc⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : ((⟨y, hy⟩ * l * (⟨y, hy⟩ : ↥L)⁻¹ * l⁻¹ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_pCore_iff]
      exact hc l l.2
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    rw [QuotientGroup.mk'_apply]
    set a : ↥L ⧸ CFSG.pCore 2 ↥L := ((⟨y, hy⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L)
    set b : ↥L ⧸ CFSG.pCore 2 ↥L := ((l : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L)
    calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
      _ = a * b := by rw [h1, inv_one, one_mul]

end General

section L0

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem o2Z_le_L : o2Z L ≤ L := Subgroup.map_subtype_le _

omit [Finite G] in
theorem l0_le_L : l0 L ≤ L := (oTwoRes_le _).trans o2Z_le_L

omit [Finite G] in
theorem normalizer_L_le_o2Z :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (o2Z L : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun g hg y hy => ?_
  obtain ⟨hyL, hc⟩ := mem_o2Z_iff.1 hy
  have hgyL : g * y * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg y).mp hyL
  refine mem_o2Z_iff.2 ⟨hgyL, fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
  have h1 := hc _ hl'
  have h2 := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hg) _).mp h1
  have e : g * (y * (g⁻¹ * l * g⁻¹⁻¹) * y⁻¹ * (g⁻¹ * l * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * y * g⁻¹ * l * (g * y * g⁻¹)⁻¹ * l⁻¹ := by group
  rwa [e] at h2

omit [Finite G] in
theorem L_le_normalizer_l0 : L ≤ Subgroup.normalizer (l0 L : Set G) :=
  A5.le_normalizer_oTwoRes_of_le_normalizer (Subgroup.le_normalizer.trans normalizer_L_le_o2Z)

theorem mem_pCoreOf_l0 {x : G} (hx : x ∈ l0 L) (hx2 : x ∈ pCoreOf 2 L) :
    x ∈ pCoreOf 2 (l0 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left :
    l0 L ⊓ pCoreOf 2 L ≤ l0 L) (F7.le_normalizer_inf Subgroup.le_normalizer
      ((l0_le_L (L := L)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right) ⟨hx, hx2⟩

theorem pCoreOf_l0_le : pCoreOf 2 (l0 L) ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans l0_le_L)
    ((L_le_normalizer_l0 (L := L)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem exists_l0_c (h3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3) :
    ∃ c : G, c ∈ l0 L ∧ c ^ 3 = 1 ∧ c ∉ pCoreOf 2 L ∧
      ∀ x ∈ o2Z L, x ∈ pCoreOf 2 L ∨ c * c * x ∈ pCoreOf 2 L ∨ c * x ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 3 (by rw [h3])
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ζ : Q)
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set y₁ : ↥L := y ^ (2 ^ a) with hy₁
  have hy₁m : y₁ ^ m = 1 := by rw [hy₁, ← pow_mul, ← hnm, pow_orderOf_eq_one]
  set η : Q := (y₁ : Q) with hη
  have hηζ : η = (ζ : Q) ^ (2 ^ a) := by rw [hη, hy₁, QuotientGroup.mk_pow, hy]
  have hηc : η ∈ Subgroup.center Q := by
    rw [hηζ]
    exact Subgroup.pow_mem _ ζ.2 _
  have hζ3 : (ζ : Q) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    exact congrArg Subtype.val this
  have hη3 : η ^ 3 = 1 := by rw [hηζ, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
  have hη1 : η ≠ 1 := by
    intro h
    rw [hηζ] at h
    have h' : ζ ^ (2 ^ a) = 1 := Subtype.ext (by simpa using h)
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hζ] at this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  have hord : orderOf η = 3 := orderOf_eq_prime hη3 hη1
  have hZ : Subgroup.center Q = Subgroup.zpowers η := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hηc) ?_).symm
    rw [Nat.card_zpowers, hord, h3]
  have hy₁Z : (y₁ : G) ∈ o2Z L := ⟨y₁, hηc, rfl⟩
  have hy₁l0 : (y₁ : G) ∈ l0 L :=
    Subgroup.subset_closure ⟨hy₁Z, m, hm, by simpa using congrArg Subtype.val hy₁m⟩
  have hy₁3 : (y₁ : G) ^ 3 = 1 := by
    have h1 : ((y₁ ^ 3 : ↥L) : Q) = 1 := by rw [QuotientGroup.mk_pow, ← hη, hη3]
    rw [QuotientGroup.eq_one_iff, mem_pCore_iff] at h1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, h1⟩
    have hk' : ((y₁ : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : ((y₁ : G) ^ 3) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      simp [show (y₁ : G) ^ m = 1 by simpa using congrArg Subtype.val hy₁m]
    have h2 : orderOf ((y₁ : G) ^ 3) ∣ Nat.gcd (2 ^ k) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
    rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left.mpr hm).pow_left k), Nat.dvd_one,
      orderOf_eq_one_iff] at h2
    exact h2
  refine ⟨y₁, hy₁l0, hy₁3, fun h => hη1 ?_, fun x hx => ?_⟩
  · rw [hη, QuotientGroup.eq_one_iff, mem_pCore_iff]
    exact h
  · obtain ⟨x', hx', rfl⟩ := hx
    have hx'Z : (x' : Q) ∈ Subgroup.zpowers η := hZ ▸ hx'
    have hmem : ∀ w : ↥L, (w : Q) = 1 → (w : G) ∈ pCoreOf 2 L := fun w hw =>
      (mem_pCore_iff w).1 ((QuotientGroup.eq_one_iff _).1 hw)
    rcases A5.eq_of_mem_zpowers_of_cube hη3 hx'Z with h | h | h
    · exact Or.inl (hmem x' h)
    · refine Or.inr (Or.inl (hmem (y₁ * y₁ * x') ?_))
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, h, ← hη, ← pow_three', hη3]
    · refine Or.inr (Or.inr (hmem (y₁ * x') ?_))
      rw [QuotientGroup.mk_mul, h, ← hη, ← mul_assoc, ← pow_three', hη3]

theorem l0_decomp (hhat : IsHatA6 L) : ∃ c : G, c ∈ l0 L ∧ c ^ 3 = 1 ∧
    c ∉ pCoreOf 2 (l0 L) ∧ ∀ x ∈ l0 L, x ∈ pCoreOf 2 (l0 L) ∨ c * c * x ∈ pCoreOf 2 (l0 L) ∨
      c * x ∈ pCoreOf 2 (l0 L) := by
  obtain ⟨c, hc, hc3, hcO, hdec⟩ := exists_l0_c hhat.2.1
  refine ⟨c, hc, hc3, fun h => hcO (pCoreOf_l0_le h), fun x hx => ?_⟩
  have hxZ : x ∈ o2Z L := oTwoRes_le _ hx
  rcases hdec x hxZ with h | h | h
  · exact Or.inl (mem_pCoreOf_l0 hx h)
  · exact Or.inr (Or.inl (mem_pCoreOf_l0 ((l0 L).mul_mem ((l0 L).mul_mem hc hc) hx) h))
  · exact Or.inr (Or.inr (mem_pCoreOf_l0 ((l0 L).mul_mem hc hx) h))

end L0

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem o2Z_le_centralizer
    : o2Z L ≤ Subgroup.centralizer (V : Set G) := by
  intro y hy
  obtain ⟨hyL, hc⟩ := mem_o2Z_iff.1 hy
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hyL
  have hcomm : ∀ l (hl : l ∈ L), S.frame.ρ ⟨y, hyN⟩ * S.frame.ρ ⟨l, S.frame.L_le hl⟩ =
      S.frame.ρ ⟨l, S.frame.L_le hl⟩ * S.frame.ρ ⟨y, hyN⟩ := by
    intro l hl
    set a : ↥(Subgroup.normalizer (V : Set G)) := ⟨y, hyN⟩
    set b : ↥(Subgroup.normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩
    have hk : S.frame.ρ (a * b * a⁻¹ * b⁻¹) = 1 :=
      (S.rho_eq_one_iff _).2 (S.pCoreOf_L_le_centralizer (hc l hl))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    calc S.frame.ρ a * S.frame.ρ b = (S.frame.ρ a * S.frame.ρ b * (S.frame.ρ a)⁻¹ *
          (S.frame.ρ b)⁻¹) * (S.frame.ρ b * S.frame.ρ a) := by group
      _ = S.frame.ρ b * S.frame.ρ a := by rw [hk, one_mul]
  have hlift : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
      S.frame.ρ ⟨y, hyN⟩ * σ = σ * S.frame.ρ ⟨y, hyN⟩ := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσ)
    have := hcomm _ hgL
    rw [show (⟨(g : G), S.frame.L_le hgL⟩ : ↥(Subgroup.normalizer (V : Set G))) = g from rfl,
      hg] at this
    exact this
  have h1 := eq_one_of_comm_three _ (hlift _ (by decide)) (hlift _ (by decide))
    (hlift _ (by decide))
  exact (S.rho_eq_one_iff _).1 h1

theorem o2Z_le_inf
    : o2Z L ≤ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := fun _ hy =>
  ⟨o2Z_le_L hy, Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V)
      (S.o2Z_le_centralizer hy))⟩

theorem l0_le_L1 : l0 L ≤ S.L1 := by
  show oTwoRes (o2Z L) ≤ oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G))
  exact oTwoRes_mono S.o2Z_le_inf

theorem normalizer_le_l0 :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (l0 L : Set G) :=
  A5.le_normalizer_oTwoRes_of_le_normalizer (S.NV_le_M.trans normalizer_L_le_o2Z)

end Setting4

end CFSG.Quasithin.H13.A6
