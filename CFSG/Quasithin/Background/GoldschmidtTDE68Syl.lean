module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Ind
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.E6.Alt

open Subgroup CFSG.Quasithin.E6.Bar CFSG.QuasithinUnique

theorem exists_conj_of_card_two_pow {G : Type*} [Group G] [Finite G] {k m : ℕ}
    (hG : Nat.card G = 2 ^ k * m) (hm : Odd m) (D D' : Subgroup G) (hD : Nat.card D = 2 ^ k)
    (hD' : Nat.card D' = 2 ^ k) : ∃ c : G, D.map (MulAut.conj c).toMonoidHom = D' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ E : Subgroup G, Nat.card E = 2 ^ k → ¬ 2 ∣ E.index := by
    intro E hE h2
    have hmul := E.card_mul_index
    rw [hE, hG] at hmul
    have : E.index = m := by
      have hpos : 0 < 2 ^ k := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpos hmul
    rw [this] at h2
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)
  let P : Sylow 2 G := (IsPGroup.of_card hD).toSylow (hidx D hD)
  let Q : Sylow 2 G := (IsPGroup.of_card hD').toSylow (hidx D' hD')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, ?_⟩
  have h1 : ((g • P : Sylow 2 G) : Subgroup G) = (Q : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  exact h1

theorem card_eq_eight_of_sylow {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : Odd m)
    (hX : Nat.card X = 8 * m) (P : Subgroup X) (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) :
    Nat.card P = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hmul := P.card_mul_index
  rw [hk, hX] at hmul
  have hidxodd : Nat.Coprime 8 P.index := by
    have : Nat.Coprime 2 P.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx
    simpa using Nat.Coprime.pow_left 3 this
  have hmcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have h1 : 2 ^ k ∣ 8 := by
    have : 2 ^ k ∣ 8 * m := ⟨P.index, hmul.symm⟩
    exact hmcop.dvd_of_dvd_mul_right this
  have h2 : 8 ∣ 2 ^ k := by
    have : 8 ∣ 2 ^ k * P.index := ⟨m, hmul⟩
    exact hidxodd.dvd_of_dvd_mul_right this
  rw [hk]
  exact Nat.dvd_antisymm h1 h2

variable {Y : Type} [Group Y] [Finite Y] {L R : Subgroup Y} {G : Type} [Group G] [Finite G]

omit [Finite Y] [Finite G] in
theorem card_eq_eight_mul_odd {m : ℕ} (hm : Odd m) (hG : Nat.card G = 8 * m)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (φ : Qbar L ≃* G) :
    ∃ m' : ℕ, Odd m' ∧ Nat.card ↥L = 8 * m' := by
  refine ⟨m * Nat.card ↥(Subgroup.center ↥L), hm.mul hodd, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L),
    ← Nat.card_congr φ.toEquiv.symm, hG]
  ring

omit [Finite G] in
theorem card_imgBar {m : ℕ} (hm : Odd m) (hG : Nat.card G = 8 * m)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (φ : Qbar L ≃* G)
    (hsyl : IsSylowTwoOf (R ⊓ L) L) : Nat.card ↥(imgBar L R) = 8 := by
  obtain ⟨m', hm', hL⟩ := card_eq_eight_mul_odd hm hG hodd φ
  have hPeq : (R ⊓ L).subgroupOf L = R.subgroupOf L := Subgroup.inf_subgroupOf_right R L
  have hP : IsPGroup 2 ↥((R ⊓ L).subgroupOf L) :=
    hsyl.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hsyl.1).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hsyl.1).injective
  have h8 : Nat.card ↥((R ⊓ L).subgroupOf L) = 8 :=
    card_eq_eight_of_sylow hm' hL _ hP hsyl.2.2
  have h1 := map_mk_card (L := L) hodd _ hP
  unfold imgBar
  rw [← hPeq, h1, h8]

theorem exists_iso_imgBar_eq {m : ℕ} (hm : Odd m) (hG : Nat.card G = 8 * m)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (φ : Qbar L ≃* G)
    (hsyl : IsSylowTwoOf (R ⊓ L) L) (D : Subgroup G) (hD : Nat.card D = 8) :
    ∃ e : Qbar L ≃* G, (imgBar L R).map e.toMonoidHom = D := by
  have h8 := card_imgBar hm hG hodd φ hsyl
  have h8' : Nat.card ↥((imgBar L R).map φ.toMonoidHom) = 2 ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective, h8]
    norm_num
  obtain ⟨c, hc⟩ := exists_conj_of_card_two_pow (k := 3) (m := m) (by rw [hG]; norm_num) hm
    ((imgBar L R).map φ.toMonoidHom) D h8' (by rw [hD]; norm_num)
  refine ⟨φ.trans (MulAut.conj c), ?_⟩
  rw [← hc, Subgroup.map_map]
  rfl

end CFSG.Quasithin.E6.Alt
