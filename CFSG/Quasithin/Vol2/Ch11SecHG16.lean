module

public import CFSG.Quasithin.Vol2.Ch11SecHSL3b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem isSylowTwoOf_of_card {Y : Type*} [Group Y] {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) {X A : Subgroup Y}
    (e : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hAX : A ≤ X) (hA : IsPGroup 2 A)
    (hc : Nat.card A = 2 ^ n) : QuasithinUnique.IsSylowTwoOf A X := by
  refine ⟨hAX, hA, ?_⟩
  have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have hcA : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  have hmul := Subgroup.index_mul_card (A.subgroupOf X)
  rw [hcA, hc, hX] at hmul
  have hidx : (A.subgroupOf X).index = (2 ^ n) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) (by rw [hmul, mul_comm])
  rw [hidx]
  exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_ne_one {A : Subgroup G} (hA : A ≠ ⊥) (x : G) :
    ∃ a ∈ conjSubgroup A x, a ≠ 1 := by
  rcases Subgroup.bot_or_exists_ne_one (conjSubgroup A x) with hb | hb
  · exfalso
    apply hA
    rw [eq_bot_iff]
    intro z hz
    have : x⁻¹ * z * x ∈ conjSubgroup A x :=
      mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hz)
    rw [hb, Subgroup.mem_bot] at this
    have h1 : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [Subgroup.mem_bot, h1, this]
    group
  · exact hb

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem fsuV_inf_centralizer_P (i : Inp32) [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π) :
    fsuV T I ⊓ Subgroup.centralizer (pOf T I H h : Set G) = bOf T I H := by
  have hPab := d.isElemAbelian_P i
  refine le_antisymm ?_ ?_
  · rintro v ⟨hv, hvC⟩
    by_contra hvB
    obtain ⟨b', hb', hb'1⟩ := exists_conj_ne_one (d.B_ne_bot_sl3 hF hπ) h
    have hcomm : v * b' = b' * v :=
      (Subgroup.mem_centralizer_iff.mp hvC b' (Subgroup.mem_sup_right hb')).symm
    have hb'B := d.mem_B_of_comm i hF hπ hv hvB (Subgroup.mem_sup_right hb') hcomm
    have : b' ∈ fsuV T I ⊓ conjSubgroup (fsuV T I) h :=
      ⟨(inf_le_left : bOf T I H ≤ fsuV T I) hb'B, E3.conjSubgroup_mono_left _ inf_le_left hb'⟩
    rw [d.fsuV_inf_Vh i, Subgroup.mem_bot] at this
    exact hb'1 this
  · intro b hb
    refine Subgroup.mem_inf.mpr ⟨(inf_le_left : bOf T I H ≤ fsuV T I) hb, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact comm_of_isElemAbelian hPab hp (Subgroup.mem_sup_left hb)

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
