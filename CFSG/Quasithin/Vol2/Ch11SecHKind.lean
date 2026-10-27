module

public import CFSG.Quasithin.Vol2.Ch11SecHV
public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem card_natMod' {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Nat.card (FFModel.nat Γ).Mod = Nat.card K ^ Fintype.card ι := by
  rw [← Nat.card_congr (MulEquiv.ofBijective (G64.natQuot Γ)
    ⟨G64.natQuot_injective, G64.natQuot_surjective⟩).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

theorem card_of_realizesVia {W : Type*} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (MulAut W)} {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    Nat.card W = Nat.card K ^ Fintype.card ι := by
  have := G64.RealizesVia.card_eq h
  rw [Subgroup.card_top, Subgroup.card_bot, mul_one, card_natMod'] at this
  exact this

omit [Finite G] in
theorem card_B_subgroupOf (T I H : Subgroup G) :
    Nat.card ((bOf T I H).subgroupOf (fsuV T I)) = Nat.card (bOf T I H) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem sq_fsuV : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
  Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV d.c.s.hyp).2 w w.2)

theorem not_sp4 (i : Inp32) [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (π : ↥(StatedSp 2 F) →* ↥(autOn L (fsuV T I)))
    (hπ : (FFModel.nat (StatedSp 2 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π) :
    False := by
  have hle := i.hKF2 F n d.c.two_le hF ↥(fsuV T I) d.sq_fsuV _ π hπ
    (autOn (conjSubgroup (bOf T I H) h) (fsuV T I)) ((bOf T I H).subgroupOf (fsuV T I))
    (d.autOn_Bh_le_normalizer i) d.autOn_Bh_sq (d.autOn_Bh_fix i)
    (by rw [card_B_subgroupOf, d.card_fsuV])
  rw [d.card_autOn_Bh i] at hle
  have h4 := card_of_realizesVia hπ
  rw [d.card_fsuV, hF] at h4
  simp only [Fintype.card_sum, Fintype.card_fin] at h4
  have hB : Nat.card (bOf T I H) = (2 ^ n) ^ 3 := by
    have h5 : 2 ^ n * Nat.card (bOf T I H) = 2 ^ n * (2 ^ n) ^ 3 := by rw [h4]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h5
  rw [hB] at hle
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) d.c.two_le
  have h16 : 16 ≤ 2 ^ n * 2 ^ n := by nlinarith
  have : 2 ^ n * 16 ≤ (2 ^ n) ^ 3 := by
    calc 2 ^ n * 16 ≤ 2 ^ n * (2 ^ n * 2 ^ n) := Nat.mul_le_mul_left _ h16
      _ = (2 ^ n) ^ 3 := by ring
  omega

theorem exists_sl3 (i : Inp32) : ∃ (_ : IsMulCommutative ↥(fsuV T I)) (F : Type) (_ : Field F)
    (_ : Finite F), Nat.card F = 2 ^ n ∧ ∃ π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I)),
      (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π := by
  obtain ⟨hc, -, -, -, hk⟩ := i.h1102 G T L I n d.c.s.hyp
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [d.VL, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  rcases hk with ⟨F, _, _, hF, -, π, hπ, -⟩ | ⟨F, _, _, hF, -, π, hπ, -⟩ |
      ⟨F, _, _, hF, ⟨e⟩, -⟩
  · rw [hZ] at hπ
    exact ⟨hc, F, inferInstance, inferInstance, hF, π, hπ⟩
  · rw [hZ] at hπ
    exact (d.not_sp4 i hF π hπ).elim
  · exfalso
    have hk2 : KindG2 L (fsuV T I) n := ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
    rcases d.c.s.kind i.h1134 with h1 | h1
    · exact SecA.kind_not_SL3_G2 i.hG2 d.c.two_le h1 hk2
    · exact SecA.kind_not_Sp4_G2 i.hG2 d.c.two_le h1 hk2

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
