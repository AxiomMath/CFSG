module

public import CFSG.Quasithin.Vol2.Ch3nE2

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem relIndex_A_eq (h : E2.Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V) :
    (conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (conjSub g (kerIn M X ⊓ V)) = (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  obtain ⟨-, -, -, -, -, hAC⟩ := Ch3n.exists_cubic_of_pair h hchar hXV
  rw [hAC]
  have hZg : conjSub g (V ⊓ conjSub g V) = V ⊓ conjSub g V := h.conjSub_inf_conj h.mem
  conv_lhs => rw [← hZg]
  exact Ch3n.relIndex_conjSub g _ _

theorem two_le_relIndex (h : E2.Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V) :
    2 ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  obtain ⟨-, -, -, -, hnot, -⟩ := Ch3n.exists_cubic_of_pair h hchar hXV
  rw [← relIndex_A_eq h hchar hXV]
  have h0 : (conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (conjSub g (kerIn M X ⊓ V)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (conjSub g (kerIn M X ⊓ V)) ≠ 1 := fun h1 =>
    hnot ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
  omega

theorem count_lt_of_lt (h : E2.Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V)
    (hlt : (kerIn M X ⊓ V).relIndex V < (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V)) :
    (V ⊓ Subgroup.centralizer ((conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G)).relIndex V <
      ((conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (conjSub g (kerIn M X ⊓ V))) ^ 2 := by
  rw [relIndex_A_eq h hchar hXV]
  set B := kerIn M X ⊓ V with hB
  set A := conjSub g B with hA
  set Z := V ⊓ conjSub g V with hZ
  have hZB : Z ≤ B := h.inf_conj_le_kerIn_inf
  have hAX : A ≤ X := h.A_le_pCoreOf.trans (pCoreOf_le 2 X)
  have hZC : Z ≤ V ⊓ Subgroup.centralizer (A : Set G) := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun a ha => (h.mem_center hz (hAX ha)).symm⟩
  have hpos : 0 < Z.relIndex V := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmul : Z.relIndex B * B.relIndex V = Z.relIndex V :=
    Subgroup.relIndex_mul_relIndex Z B V hZB inf_le_right
  have hZBpos : 0 < Z.relIndex B := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  calc (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ Z.relIndex V :=
        Nat.le_of_dvd hpos (Subgroup.relIndex_dvd_of_le_left V hZC)
    _ = Z.relIndex B * B.relIndex V := hmul.symm
    _ < Z.relIndex B * Z.relIndex B := Nat.mul_lt_mul_of_pos_left hlt hZBpos
    _ = (Z.relIndex B) ^ 2 := (sq _).symm

theorem count_lt_of_commute (h : E2.Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V)
    (hrank : (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V))
    (hBA : ⁅kerIn M X ⊓ V, conjSub g (kerIn M X ⊓ V)⁆ = ⊥) :
    (V ⊓ Subgroup.centralizer ((conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G)).relIndex V <
      ((conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (conjSub g (kerIn M X ⊓ V))) ^ 2 := by
  have h2 := two_le_relIndex h hchar hXV
  rw [relIndex_A_eq h hchar hXV]
  set B := kerIn M X ⊓ V with hB
  set A := conjSub g B with hA
  set Z := V ⊓ conjSub g V with hZ
  have hBC : B ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro b hb
    refine ⟨hb.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have h1 : b * a * b⁻¹ * a⁻¹ ∈ ⁅B, A⁆ := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hb ha
    rw [hBA, Subgroup.mem_bot] at h1
    have h3 : b * a = a * b := by
      calc b * a = b * a * b⁻¹ * a⁻¹ * (a * b) := by group
        _ = a * b := by rw [h1, one_mul]
    exact h3.symm
  have hpos : 0 < B.relIndex V := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  calc (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ B.relIndex V :=
        Nat.le_of_dvd hpos (Subgroup.relIndex_dvd_of_le_left V hBC)
    _ ≤ Z.relIndex B := hrank
    _ < Z.relIndex B * Z.relIndex B := by nlinarith
    _ = (Z.relIndex B) ^ 2 := (sq _).symm

theorem commutator_eq_bot_of_inf_eq_bot (h : E2.Pair X T M V g) (hZ : V ⊓ conjSub g V = ⊥) :
    ⁅kerIn M X ⊓ V, conjSub g (kerIn M X ⊓ V)⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro b hb a ha
  have h1 := h.commutator_B_A hb ha
  rw [hZ] at h1
  rwa [commutatorElement_def]

omit [Finite G] in
theorem le_normalizer_of_isTISetIn {M₀ : Subgroup G} (h : E2.Pair X T M V g) (hM : M ≤ M₀)
    (hTI : IsTISetIn V M₀) (hZ : V ⊓ conjSub g V ≠ ⊥) :
    M ≤ Subgroup.normalizer (V : Set G) := by
  intro m hm
  by_contra hmN
  apply hZ
  have h1 := hTI.2 m (hM hm) hmN
  rw [eq_bot_iff]
  intro z hz
  have hzX : m * z * m⁻¹ = z := by
    rw [← h.mem_center hz (h.le_X hm), mul_inv_cancel_right]
  have h3 : z ∈ conjSubgroup V m := by
    rw [mem_conjSubgroup_iff, hzX]
    exact hz.1
  have h2 : z ∈ V ⊓ conjSubgroup V m := Subgroup.mem_inf.mpr ⟨hz.1, h3⟩
  rwa [h1] at h2

end CFSG.Quasithin.Ch3E215M
