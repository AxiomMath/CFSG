module

public import CFSG.Quasithin.H13.GoldschmidtC137H6InvFin
public import CFSG.Quasithin.H13.GoldschmidtC137H6Str

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem exists_central_order_three :
    ∃ z ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L), orderOf z = 3 := by
  have hne : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≠ ⊥ := by
    intro hb
    have := h.hhat.2.1
    rw [hb, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hdvd : orderOf z ∣ 3 := h.hhat.2.1 ▸ Subgroup.orderOf_dvd_natCard _ hz
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · exact absurd (Subtype.ext (orderOf_eq_one_iff.1 h1)) hz1
  · exact ⟨z, hz, h1⟩

end H6Ctx

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem not_comm_lifts {l₁ l₂ : G} (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L)
    (h₁ : convI h.hVe ⟨l₁, h.hXN (h.hLX hl₁)⟩ = F.ρ cT1)
    (h₂ : convI h.hVe ⟨l₂, h.hXN (h.hLX hl₂)⟩ = F.ρ cT2) :
    l₁ * l₂ * l₁⁻¹ * l₂⁻¹ ∉ pCoreOf 2 L := by
  intro hcomm
  have hLN : L ≤ normalizer (V : Set G) := h.hLX.trans h.hXN
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L with hQ
  let φ₀ : ↥L →* MulAut (IntMod V h.hVe) := convHom h.hVe L hLN
  have hOker : CFSG.pCore 2 ↥L ≤ φ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff]
    exact h.pCoreOf_le_centralizer (coe_mem_pCoreOf_iff.2 hx)
  let π : Q →* MulAut (IntMod V h.hVe) := QuotientGroup.lift _ φ₀ hOker
  have hπ : ∀ y : ↥L, π (QuotientGroup.mk y) = φ₀ y := fun y => rfl
  have hker : π.ker = Subgroup.center Q := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, hπ, convHom_apply, convI_eq_one_iff]
    constructor
    · intro hy
      have : (y : G) ∈ A6.o2Z L := h.D_eq_o2Z ▸ ⟨y.2, hy⟩
      obtain ⟨hyL, hc⟩ := mem_o2Z_gc.1 this
      exact hc
    · intro hc
      have : (y : G) ∈ A6.o2Z L := mem_o2Z_gc.2 ⟨y.2, hc⟩
      exact (h.D_eq_o2Z ▸ this : (y : G) ∈ L ⊓ centralizer (V : Set G)).2
  have hrange : π.range = autI h.hVe L := by
    rw [← range_convHom h.hVe L hLN]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨QuotientGroup.mk y, rfl⟩
  set S : Subgroup Q := (E9.map F.ρ).comap π with hS
  have hidx : S.index = 40 := by
    rw [hS, Subgroup.index_comap, hrange, ← F.hA,
      Subgroup.relIndex_map_map_of_injective _ _ F.inj, relIndex_E9]
  set q₁ : Q := QuotientGroup.mk ⟨l₁, hl₁⟩ with hq₁
  set q₂ : Q := QuotientGroup.mk ⟨l₂, hl₂⟩ with hq₂
  have hπq₁ : π q₁ = F.ρ cT1 := h₁
  have hπq₂ : π q₂ = F.ρ cT2 := h₂
  have hq : Commute q₁ q₂ := by
    have hk : ((⟨l₁, hl₁⟩ : ↥L) * ⟨l₂, hl₂⟩ * ⟨l₁, hl₁⟩⁻¹ * ⟨l₂, hl₂⟩⁻¹ : ↥L) ∈
        CFSG.pCore 2 ↥L := coe_mem_pCoreOf_iff.1 hcomm
    have h1 := (QuotientGroup.eq_one_iff _).2 hk
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hcen : ∀ w ∈ Subgroup.center Q, ∀ g : Q, Commute g w := fun w hw g =>
    Subgroup.mem_center_iff.1 hw g
  have hdec : ∀ a ∈ S, ∃ i j : ℕ, ∃ w ∈ Subgroup.center Q, a = q₁ ^ i * q₂ ^ j * w := by
    intro a ha
    obtain ⟨e, he, hea⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 ha)
    obtain ⟨i, j, rfl⟩ := E9_decomp he
    refine ⟨i, j, (q₁ ^ i * q₂ ^ j)⁻¹ * a, ?_, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_pow, map_pow, hπq₁, hπq₂,
      ← map_pow, ← map_pow, ← map_mul, hea, inv_mul_cancel]
  have hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, j, w₁, hw₁, rfl⟩ := hdec a ha
    obtain ⟨i', j', w₂, hw₂, rfl⟩ := hdec b hb
    have hxy : Commute (q₁ ^ i * q₂ ^ j) (q₁ ^ i' * q₂ ^ j') :=
      Commute.mul_left (Commute.mul_right ((Commute.refl q₁).pow_pow i i') (hq.pow_pow i j'))
        (Commute.mul_right (hq.symm.pow_pow j i') ((Commute.refl q₂).pow_pow j j'))
    exact (Commute.mul_left (Commute.mul_right hxy (hcen w₂ hw₂ _))
      (Commute.mul_right (hcen w₁ hw₁ _).symm (hcen w₁ hw₁ _).symm)).eq
  obtain ⟨z, hzc, hz3⟩ := h.exists_central_order_three
  exact no_abelian_of_perfect_central_gc h.hhat.1 hSab hzc hz3 (by rw [hidx]; norm_num)

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
