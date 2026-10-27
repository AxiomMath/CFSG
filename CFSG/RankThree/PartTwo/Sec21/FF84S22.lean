module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.FF84A8
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Small
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.GLTheoremA.CatB (A8)

section Lambda

variable {Λ : Type} [Group Λ] [Finite Λ] (ρ : Λ →* A8)

theorem ker_one (hker : ρ.ker = Subgroup.center Λ) (hZ : ∀ z ∈ Subgroup.center Λ, z ^ 2 = 1)
    {z : Λ} (hz : ρ z = 1) (h3 : z ^ 3 = 1) : z = 1 := by
  have hz2 : z ^ 2 = 1 := hZ z (hker ▸ hz)
  have : z = z ^ 3 * (z ^ 2)⁻¹ := by group
  rw [this, h3, hz2]; simp

theorem zpow_cube {w : Λ} (hw : w ^ 3 = 1) (k : ℤ) : (w ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast (w ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

theorem lift_comm (hker : ρ.ker = Subgroup.center Λ) (hZ : ∀ z ∈ Subgroup.center Λ, z ^ 2 = 1)
    {u : Λ} (hu : u ^ 3 = 1) {y : Λ} (hy : ρ y * ρ u = ρ u * ρ y) : y * u = u * y := by
  set z : Λ := y * u * y⁻¹ * u⁻¹ with hzdef
  have hρz : ρ z = 1 := by
    rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc ρ y * ρ u * (ρ y)⁻¹ * (ρ u)⁻¹ = (ρ y * ρ u) * (ρ y)⁻¹ * (ρ u)⁻¹ := rfl
      _ = (ρ u * ρ y) * (ρ y)⁻¹ * (ρ u)⁻¹ := by rw [hy]
      _ = 1 := by group
  have hzc : z ∈ Subgroup.center Λ := hker ▸ hρz
  have hzu : Commute z u := (Subgroup.mem_center_iff.1 hzc u).symm
  have hzu3 : (z * u) ^ 3 = 1 := by
    have : z * u = y * u * y⁻¹ := by rw [hzdef]; group
    rw [this]
    calc (y * u * y⁻¹) ^ 3 = y * u ^ 3 * y⁻¹ := conj_pow
      _ = 1 := by rw [hu]; group
  have hz3 : z ^ 3 = 1 := by
    rw [hzu.mul_pow, hu, mul_one] at hzu3
    exact hzu3
  have hz1 : z = 1 := ker_one ρ hker hZ hρz hz3
  have : y * u * y⁻¹ * u⁻¹ = 1 := hz1
  calc y * u = (y * u * y⁻¹ * u⁻¹) * (u * y) := by group
    _ = u * y := by rw [this, one_mul]

theorem card_comap_of_surjective (hρ : Function.Surjective ρ) (T : Subgroup A8) :
    Nat.card (T.comap ρ) = Nat.card ρ.ker * Nat.card T := by
  have h1 := Subgroup.card_mul_index (T.comap ρ)
  have h2 := Subgroup.card_mul_index T
  have h3 := Subgroup.card_ker_mul_card_of_surjective hρ
  rw [Subgroup.index_comap_of_surjective _ hρ] at h1
  have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h3, ← h2]
  ring

theorem card_cent (hρ : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center Λ)
    (hZ : ∀ z ∈ Subgroup.center Λ, z ^ 2 = 1) {u : Λ} (hu : u ^ 3 = 1) :
    Nat.card (Subgroup.centralizer ({u} : Set Λ)) =
      Nat.card (Subgroup.center Λ) * Nat.card (Subgroup.centralizer ({ρ u} : Set A8)) := by
  have : Subgroup.centralizer ({u} : Set Λ) = (Subgroup.centralizer ({ρ u} : Set A8)).comap ρ := by
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [← map_mul, ← map_mul, h]
    · exact lift_comm ρ hker hZ hu
  rw [this, card_comap_of_surjective ρ hρ, hker]

end Lambda

theorem exists_mul_of_mem_sup_zpowers {G : Type*} [Group G] {x : G} {H : Subgroup G}
    (hH : H ≤ Subgroup.centralizer ({x} : Set G)) {a : G} (ha : a ∈ Subgroup.zpowers x ⊔ H) :
    ∃ i : ℤ, ∃ h ∈ H, a = x ^ i * h := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ k ∈ H, x * k = k * x := fun k hk =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hH hk)).symm
    constructor
    · intro hh
      have : x * h * x⁻¹ = h := by rw [hc h hh]; group
      rw [this]; exact hh
    · intro hh
      have h2 : x⁻¹ * (x * h * x⁻¹) * x = h := by group
      have h3 : x⁻¹ * (x * h * x⁻¹) = (x * h * x⁻¹) * x⁻¹ := by
        have := hc (x * h * x⁻¹) hh
        calc x⁻¹ * (x * h * x⁻¹) = x⁻¹ * (x * h * x⁻¹) * x * x⁻¹ := by group
          _ = x⁻¹ * (x * (x * h * x⁻¹)) * x⁻¹ := by rw [this]; group
          _ = (x * h * x⁻¹) * x⁻¹ := by group
      rw [h3] at h2
      have h4 : (x * h * x⁻¹) * x⁻¹ * x = x * h * x⁻¹ := by group
      rw [h4] at h2
      rw [← h2]; exact hh
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x) H hle
  have ha' : a ∈ ((Subgroup.zpowers x ⊔ H : Subgroup G) : Set G) := ha
  rw [hset] at ha'
  obtain ⟨y, hy, h, hh, rfl⟩ := ha'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ⟨i, h, hh, rfl⟩

theorem mono_facts {G : Type} [Group G] {b b₁ b₂ : G} {B : Subgroup G} (hb : orderOf b = 3)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hmono : IsFullMonomial B b b₁ b₂) :
    b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b₁ * b₂ = b₂ * b₁ ∧ b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ (∀ k : ℤ, b₂ ≠ b₁ ^ k) ∧
      ∃ m : G, m * b * m⁻¹ = b ∧ m * b₁ * m⁻¹ = b₂ := by
  obtain ⟨⟨hel, -⟩, -, -, ⟨n₁, -, e1b, e1b1, e1b2⟩, ⟨n₂, -, e2b, e2b1, e2b2⟩,
    ⟨n₃, -, e3b, e3b1, e3b2⟩⟩ := hmono
  have hb1 : b ≠ 1 := by
    intro h; rw [h] at hb; simp at hb
  have hconj1 : ∀ (n a : G), n * a * n⁻¹ = 1 → a = 1 := fun n a h => by
    have : a = n⁻¹ * (n * a * n⁻¹) * n := by group
    rw [this, h]; group
  have h13 : b₁ ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := B) b₁ hb₁
  have h23 : b₂ ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := B) b₂ hb₂
  have hne1 : b₁ ≠ 1 := fun h => hb1 (hconj1 n₂ b (by rw [e2b, h]))
  have hne2 : b₂ ≠ 1 := fun h => hb1 (by
    have := e3b2; rw [h] at this
    rw [← this]; group)
  refine ⟨h13, h23, ?_, hne1, hne2, ?_, n₂ * n₃, ?_, ?_⟩
  · have := (hel.toIsMulCommutative.is_comm.comm ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩)
    exact congrArg Subtype.val this
  · intro k hk
    have h1 : b₂ = b ^ k := by
      have : n₂ * b₂ * n₂⁻¹ = n₂ * b₁ ^ k * n₂⁻¹ := by rw [hk]
      rw [e2b2, ← conj_zpow, e2b1] at this
      exact this
    have h2 : b₂ = b ^ (-k) := by
      have this : n₁ * b₂ * n₁⁻¹ = n₁ * b ^ k * n₁⁻¹ := by rw [← h1]
      rw [e1b2, ← conj_zpow, e1b, inv_zpow'] at this
      exact this
    have h3 : b ^ (2 * k) = 1 := by
      have e : b ^ k = b ^ (-k) := h1.symm.trans h2
      calc b ^ (2 * k) = b ^ k * b ^ k := by rw [two_mul, zpow_add]
        _ = b ^ (-k) * b ^ k := by rw [← e]
        _ = 1 := by rw [← zpow_add]; simp
    have h4 : ((orderOf b : ℕ) : ℤ) ∣ 2 * k := orderOf_dvd_iff_zpow_eq_one.2 h3
    rw [hb] at h4
    obtain ⟨t, ht⟩ : (3 : ℤ) ∣ k := by omega
    apply hne2
    rw [hk, ht, zpow_mul]
    simpa [zpow_natCast] using congrArg (· ^ t) h13
  · calc n₂ * n₃ * b * (n₂ * n₃)⁻¹ = n₂ * (n₃ * b * n₃⁻¹) * n₂⁻¹ := by group
      _ = b := by rw [e3b, e2b1]
  · calc n₂ * n₃ * b₁ * (n₂ * n₃)⁻¹ = n₂ * (n₃ * b₁ * n₃⁻¹) * n₂⁻¹ := by group
      _ = b₂ := by rw [e3b1, e2b2]

theorem card_inf_cen_le {G : Type} [Group G] [Finite G] {L : Subgroup G} {m a a' : G}
    (hm : m ∈ Nor L) (h : m * a * m⁻¹ = a') :
    Nat.card ↥(L ⊓ Cen a) ≤ Nat.card ↥(L ⊓ Cen a') := by
  have hle : (L ⊓ Cen a).map (MulAut.conj m).toMonoidHom ≤ L ⊓ Cen a' := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 hy
    have hyC' : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hm y).1 hyL
    · rw [Subgroup.mem_centralizer_singleton_iff, ← h]
      show m * y * m⁻¹ * (m * a * m⁻¹) = m * a * m⁻¹ * (m * y * m⁻¹)
      calc m * y * m⁻¹ * (m * a * m⁻¹) = m * (y * a) * m⁻¹ := by group
        _ = m * (a * y) * m⁻¹ := by rw [hyC']
        _ = m * a * m⁻¹ * (m * y * m⁻¹) := by group
  calc Nat.card ↥(L ⊓ Cen a) = Nat.card ↥((L ⊓ Cen a).map (MulAut.conj m).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj m).injective).symm
    _ ≤ Nat.card ↥(L ⊓ Cen a') := Subgroup.card_le_of_le hle

theorem card_inf_cen_eq_of_conj {G : Type} [Group G] [Finite G] {L : Subgroup G} {m a a' : G}
    (hm : m ∈ Nor L) (h : m * a * m⁻¹ = a') :
    Nat.card ↥(L ⊓ Cen a) = Nat.card ↥(L ⊓ Cen a') := by
  refine le_antisymm (card_inf_cen_le hm h) (card_inf_cen_le (m := m⁻¹) (inv_mem hm) ?_)
  rw [← h]; group

theorem card_inf_cen {G : Type} [Group G] {L : Subgroup G} {a : G} (ha : a ∈ L) :
    Nat.card ↥(L ⊓ Cen a) = Nat.card (Subgroup.centralizer ({(⟨a, ha⟩ : ↥L)} : Set ↥L)) := by
  have : (Subgroup.centralizer ({(⟨a, ha⟩ : ↥L)} : Set ↥L)).map L.subtype = L ⊓ Cen a := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hw
      exact ⟨w.2, congrArg Subtype.val hw⟩
    · rintro ⟨hyL, hy⟩
      refine ⟨⟨y, hyL⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hy
  rw [← this, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

theorem statedModel_of_alt5 (X : Type) [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 5))) : StatedClassicalModel X .PSL 2 2 2 := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hcard]; norm_num))
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hcard, ⟨e.trans e5.symm⟩⟩

theorem center_alt5_trivial {H : Subgroup A8} (e5 : H ≃* alternatingGroup (Fin 5)) {z : H}
    (hz : z ∈ Subgroup.center H) : z = 1 := by
  have h1 : e5 z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨h, rfl⟩ := e5.surjective a
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz h]
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
  exact e5.map_eq_one_iff.1 h1

theorem quot_center_equiv {G : Type} [Group G] {L K : Subgroup G} (hKL : K ≤ L) (ρ : ↥L →* A8)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center ↥L) {H : Subgroup A8}
    (e5 : H ≃* alternatingGroup (Fin 5))
    (hK1 : ∀ k : ↥K, ρ (Subgroup.inclusion hKL k) ∈ H)
    (hK2 : ∀ w : ↥L, ρ w ∈ H → w.1 ∈ K) :
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 5)) := by
  let ψ : ↥K →* ↥H := (ρ.comp (Subgroup.inclusion hKL)).codRestrict H hK1
  have hψ : ∀ k, (ψ k : A8) = ρ (Subgroup.inclusion hKL k) := fun k => rfl
  have hsurj : Function.Surjective ψ := by
    intro h
    obtain ⟨w, hw⟩ := hρ h.1
    have hwK : w.1 ∈ K := hK2 w (by rw [hw]; exact h.2)
    refine ⟨⟨w.1, hwK⟩, Subtype.ext ?_⟩
    rw [hψ]
    exact hw.trans rfl
  have hkerψ : Subgroup.center ↥K = ψ.ker := by
    ext k
    constructor
    · intro hk
      have hc : ψ k ∈ Subgroup.center ↥H := by
        rw [Subgroup.mem_center_iff]
        intro h
        obtain ⟨k₂, rfl⟩ := hsurj h
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hk k₂]
      exact center_alt5_trivial e5 hc
    · intro hk
      rw [MonoidHom.mem_ker] at hk
      have hk1 : ρ (Subgroup.inclusion hKL k) = 1 := by
        have := congrArg Subtype.val hk
        rw [hψ] at this
        exact this
      have hcen : Subgroup.inclusion hKL k ∈ Subgroup.center ↥L := hker ▸ hk1
      rw [Subgroup.mem_center_iff]
      intro k₂
      apply Subgroup.inclusion_injective hKL
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 hcen _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).trans e5)⟩

theorem ff84_2_2 :
    FF84_2_2 := by
  intro G _ _ b L B b₁ b₂ hyp hB hb₁ hb₂ hgen hmono
  obtain ⟨e⟩ : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
      (Or.inl ⟨by decide, hyp.model⟩)
  have hZc : Nat.card (Subgroup.center ↥L) ∣ 2 :=
    CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_two_of_eight hyp.quasi e
  have hZ : ∀ z ∈ Subgroup.center ↥L, z ^ 2 = 1 := by
    intro z hz
    have h1 : orderOf (⟨z, hz⟩ : Subgroup.center ↥L) ∣ 2 :=
      (orderOf_dvd_natCard _).trans hZc
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
    exact congrArg Subtype.val h2
  let ρ : ↥L →* A8 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hρ : Function.Surjective ρ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center ↥L := by
    ext y
    simp [ρ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  obtain ⟨hb₁B, -⟩ := Subgroup.mem_inf.1 hb₁
  obtain ⟨hb₂B, -⟩ := Subgroup.mem_inf.1 hb₂
  obtain ⟨hb₁L⟩ : Nonempty (b₁ ∈ L) := ⟨(Subgroup.mem_inf.1 hb₁).2⟩
  obtain ⟨hb₂L⟩ : Nonempty (b₂ ∈ L) := ⟨(Subgroup.mem_inf.1 hb₂).2⟩
  obtain ⟨h13, h23, hcomm, hne1, hne2, hind, m, hmb, hmb₁⟩ :=
    mono_facts hyp.ord hb₁B hb₂B hmono
  set u : ↥L := ⟨b₁, hb₁L⟩ with hu
  set v : ↥L := ⟨b₂, hb₂L⟩ with hv
  have hu3 : u ^ 3 = 1 := Subtype.ext h13
  have hv3 : v ^ 3 = 1 := Subtype.ext h23
  have huv : u * v = v * u := Subtype.ext hcomm
  have hu1 : u ≠ 1 := fun h => hne1 (congrArg Subtype.val h)
  have hmN : m ∈ Nor L := hyp.hLN (Subgroup.mem_centralizer_singleton_iff.2 (by
    calc m * b = (m * b * m⁻¹) * m := by group
      _ = b * m := by rw [hmb]))
  have hcardCu : Nat.card ↥(L ⊓ Cen b₁) = Nat.card ↥(L ⊓ Cen b₂) :=
    card_inf_cen_eq_of_conj hmN hmb₁
  have hZpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
  have hcu' : Nat.card ↥(L ⊓ Cen b₁) = Nat.card (Subgroup.centralizer ({u} : Set ↥L)) :=
    card_inf_cen hb₁L
  have hcv' : Nat.card ↥(L ⊓ Cen b₂) = Nat.card (Subgroup.centralizer ({v} : Set ↥L)) :=
    card_inf_cen hb₂L
  have hcu := card_cent ρ hρ hker hZ hu3
  have hcv := card_cent ρ hρ hker hZ hv3
  rw [← hcu'] at hcu
  rw [← hcv'] at hcv
  have hcard : Nat.card (Subgroup.centralizer ({ρ u} : Set A8)) =
      Nat.card (Subgroup.centralizer ({ρ v} : Set A8)) := by
    apply Nat.eq_of_mul_eq_mul_left hZpos
    rw [← hcu, ← hcv]; exact hcardCu
  have hx3 : ρ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hy3 : ρ v ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
  have hc : ρ u * ρ v = ρ v * ρ u := by rw [← map_mul, ← map_mul, huv]
  have hx1 : ρ u ≠ 1 := fun h => hu1 (ker_one ρ hker hZ h hu3)
  have hyx : ρ v ∉ Subgroup.zpowers (ρ u) := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    have hρk : ρ (v * (u ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk]; simp
    have hcomm' : Commute v (u ^ k)⁻¹ :=
      ((show Commute u v from huv).symm.zpow_right k).inv_right
    have hz3 : (v * (u ^ k)⁻¹) ^ 3 = 1 := by
      rw [hcomm'.mul_pow, hv3, one_mul, inv_pow, zpow_cube hu3 k, inv_one]
    have hz1 := ker_one ρ hker hZ hρk hz3
    have hvu : v = u ^ k := mul_inv_eq_one.1 hz1
    exact hind k (by simpa using congrArg Subtype.val hvu)
  rcases a8_pair hx3 hy3 hc hx1 hyx hcard with h18 | ⟨H, ⟨e5⟩, hyH, hHc, hsup, hinf⟩
  · left
    rw [hcu, h18, mul_comm]
  · right
    set K' : Subgroup ↥L := H.comap ρ with hK'
    set K : Subgroup G := K'.map L.subtype with hK
    have hKL : K ≤ L := Subgroup.map_subtype_le K'
    have memK : ∀ w : ↥L, w.1 ∈ K ↔ ρ w ∈ H := by
      intro w
      constructor
      · rintro ⟨w', hw', hw'e⟩
        have : w' = w := Subtype.ext hw'e
        rw [← this]; exact hw'
      · intro hw; exact ⟨w, hw, rfl⟩
    have hK1 : ∀ k : ↥K, ρ (Subgroup.inclusion hKL k) ∈ H := fun k =>
      (memK (Subgroup.inclusion hKL k)).1 k.2
    have hK2 : ∀ w : ↥L, ρ w ∈ H → w.1 ∈ K := fun w hw => (memK w).2 hw
    have hKc : K ≤ Cen b₁ := by
      intro k hk
      have hkL := hKL hk
      have hk' := (memK ⟨k, hkL⟩).1 hk
      have := lift_comm ρ hker hZ hu3 (y := ⟨k, hkL⟩)
        (Subgroup.mem_centralizer_singleton_iff.1 (hHc hk'))
      exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
    refine ⟨K, (memK v).2 hyH, statedModel_of_alt5 _ (quot_center_equiv hKL ρ hρ hker e5 hK1 hK2),
      ?_, ?_, hKc⟩
    · apply le_antisymm
      · refine sup_le ?_ (le_inf hKL hKc)
        exact Subgroup.zpowers_le.2
          (Subgroup.mem_inf.2 ⟨hb₁L, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
      · intro g hg
        obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.1 hg
        have hw : (⟨g, hgL⟩ : ↥L) * u = u * ⟨g, hgL⟩ :=
          Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgC)
        have hρw : ρ ⟨g, hgL⟩ ∈ Subgroup.centralizer ({ρ u} : Set A8) :=
          Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hw])
        rw [← hsup] at hρw
        obtain ⟨i, h, hh, hρeq⟩ := exists_mul_of_mem_sup_zpowers hHc hρw
        have hw' : ρ (u ^ (-i) * ⟨g, hgL⟩) = h := by
          rw [map_mul, map_zpow, hρeq]; group
        have hmem : (u ^ (-i) * (⟨g, hgL⟩ : ↥L) : ↥L).1 ∈ K :=
          (memK _).2 (by rw [hw']; exact hh)
        have hcoe : (u ^ (-i) * (⟨g, hgL⟩ : ↥L) : ↥L).1 = b₁ ^ (-i) * g := rfl
        have : g = b₁ ^ i * (u ^ (-i) * (⟨g, hgL⟩ : ↥L) : ↥L).1 := by
          rw [hcoe]; group
        rw [this]
        exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b₁) i) hmem
    · rw [eq_bot_iff]
      rintro g ⟨hg1, hg2⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg1
      have hwL : b₁ ^ i ∈ L := Subgroup.zpow_mem _ hb₁L i
      have hw := (memK ⟨b₁ ^ i, hwL⟩).1 hg2
      have hu_eq : (⟨b₁ ^ i, hwL⟩ : ↥L) = u ^ i := Subtype.ext rfl
      rw [hu_eq, map_zpow] at hw
      have hmem : ρ u ^ i ∈ Subgroup.zpowers (ρ u) ⊓ H :=
        ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _, hw⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have hu_i : u ^ i = 1 :=
        ker_one ρ hker hZ (by rw [map_zpow]; exact hmem) (zpow_cube hu3 i)
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hu_i)

end CFSG.RankThree.PartTwo.Sec21.FF84
