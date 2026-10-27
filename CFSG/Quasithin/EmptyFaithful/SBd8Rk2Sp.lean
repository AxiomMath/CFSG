module

public import CFSG.Quasithin.EmptyFaithful.SBd8Rk2Std
import CFSG.Quasithin.Background.GoldschmidtS146RLatSp
public import CFSG.Quasithin.EmptyFaithful.SBd8Map

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

namespace SBd8

section Sp4

variable {F : Type} [Field F] [Finite F]

theorem latShape_sp4 [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    GoldS146R.LatShape (StatedSp 2 F) (unipotent 2 F) := by
  have hinj : Function.Injective (proj 2 F) := proj_injective_charTwo
  let e : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
    MulEquiv.ofBijective (proj 2 F) ⟨hinj, proj_surjective⟩
  have h := (GoldS146R.latShape_statedProj_sp_two hn hF).map e.symm
  have hU : ((unipotent 2 F).map (proj 2 F)).map e.symm.toMonoidHom = unipotent 2 F := by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp (proj 2 F) = MonoidHom.id _ :=
      MonoidHom.ext fun x => e.symm_apply_apply x
    rw [this, Subgroup.map_id]
  rwa [hU] at h

theorem normalizer_unipotent_two_ne_top (hK : ∃ k : ℕ, Nat.card F = 2 ^ k) :
    Subgroup.normalizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) ≠ ⊤ := by
  have h := CFSG.Quasithin.SzN2.sp4_residualOvergroupsAt hK
  have hmax : Q2 F 0 ⋖ ⊤ := (h.2.2.1 (Q2 F 0) (h.2.1 0)).2 ⟨0, rfl⟩
  have hle : borelSubgroup 2 F ≤ Q2 F 0 := CFSG.Quasithin.SzN2.borelSubgroup_le_Q2' 0
  rw [normalizer_unipotent]
  intro htop
  rw [htop] at hle
  exact hmax.lt.ne (top_le_iff.mp hle)

theorem nine_dvd_card_normalizer_unipotent_two {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    3 ∣ Nat.card ↥(Subgroup.normalizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F))) →
    9 ∣ Nat.card ↥(Subgroup.normalizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F))) := by
  intro h
  rw [normalizer_unipotent, card_borelSubgroup, hF] at h ⊢
  have h3q : ¬ 3 ∣ (2 ^ n) ^ 2 ^ 2 := by
    intro h3
    have h1 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have h3b : 3 ∣ 2 ^ n - 1 := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
    · exact absurd h1 h3q
    · exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  have h9 : 9 ∣ (2 ^ n - 1) ^ 2 := by
    have := pow_dvd_pow_of_dvd h3b 2
    norm_num at this
    exact this
  exact Dvd.dvd.mul_left h9 _

theorem famSp4_std {A : Subgroup (MulAut (StatedSp 2 F))} {U K : Subgroup (StatedSp 2 F)}
    (d : OvgData (StatedSp 2 F) A U K) {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : False := by
  have : CharP F 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four h4
  exact rank2_false_std d CFSG.Quasithin.SzN2.isSylowTwoOf_unipotent (latShape_sp4 hn hF)
    (CFSG.Quasithin.SzN2.sp4_solvable_overgroup_le_normalizer hK4)
    (normalizer_unipotent_two_ne_top ⟨n, hF⟩) (nine_dvd_card_normalizer_unipotent_two hF)

end Sp4

section Family

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem famSp4 (d : OvgData X A U K) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) : False :=
  famSp4_std (d.map e) hF hn

end Family

end SBd8

end CFSG.Quasithin
