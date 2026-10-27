module

public import CFSG.Quasithin.EmptyFaithful.SBd8Rk2Std
import CFSG.Quasithin.Background.GoldschmidtS146RLatLin
public import CFSG.Quasithin.EmptyFaithful.SBd8Map

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Setup.X7a

namespace SBd8

section SL3

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem scalars_three_eq_bot (h3 : ¬ 3 ∣ Nat.card F - 1) : scalars 3 F = ⊥ := by
  ext A
  rw [mem_scalars, Subgroup.mem_bot]
  constructor
  · rintro ⟨c, hc, hA⟩
    have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc
    have h2 : orderOf c ∣ Nat.card F - 1 := by
      rw [← Nat.card_units]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 3 (Nat.card F - 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have hc1 : c = 1 :=
      orderOf_eq_one_iff.1 ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
    subst hc1
    apply Subtype.ext
    rw [hA]
    simp
  · rintro rfl
    exact ⟨1, one_pow 3, by simp⟩

theorem latShape_sl3 [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (h3 : ¬ 3 ∣ Nat.card F - 1) :
    GoldS146R.LatShape (Matrix.SpecialLinearGroup (Fin 3) F) (unitriangular 3 F) := by
  have hinj : Function.Injective (proj 3 F) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, scalars_three_eq_bot h3])
  let e : Matrix.SpecialLinearGroup (Fin 3) F ≃* projectiveSL 3 F :=
    MulEquiv.ofBijective (proj 3 F) ⟨hinj, proj_surjective 3 F⟩
  have h := (GoldS146R.latShape_projectiveSL_three hn hF).map e.symm
  have hU : ((unitriangular 3 F).map (proj 3 F)).map e.symm.toMonoidHom = unitriangular 3 F := by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp (proj 3 F) = MonoidHom.id _ :=
      MonoidHom.ext fun x => e.symm_apply_apply x
    rw [this, Subgroup.map_id]
  rwa [hU] at h

omit [Finite F] in
theorem normalizer_unitriangular_three_ne_top :
    Subgroup.normalizer ((unitriangular 3 F : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) F)) ≠ ⊤ := by
  rw [normalizer_unitriangular]
  intro h
  have hmem : reflElt 3 F 1 ∈ upperTriangular 3 F := h ▸ Subgroup.mem_top _
  exact reflElt_not_mem_upperTriangular (n := 3) (i := 1) (by norm_num) (by norm_num) hmem

theorem not_three_dvd_card_normalizer_unitriangular_three {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : Odd n) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.normalizer ((unitriangular 3 F :
      Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) F))) := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hxo : orderOf (x : Matrix.SpecialLinearGroup (Fin 3) F) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hxm : (x : Matrix.SpecialLinearGroup (Fin 3) F) ∈ upperTriangular 3 F :=
    (normalizer_unitriangular (n := 3) (K := F)).le x.2
  exact CFSG.Quasithin.SzN2.orderOf_ne_three_of_mem_upperTriangular ⟨n, hF⟩
    (by rw [hF]; exact CFSG.Quasithin.SzN2.not_three_dvd_two_pow_sub_one hn) hxm hxo

theorem famSL3_std {A : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {U K : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (d : OvgData (Matrix.SpecialLinearGroup (Fin 3) F) A U K) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n) : False := by
  have : CharP F 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hF
  have h3 : ¬ 3 ∣ Nat.card F - 1 := by
    rw [hF]
    exact CFSG.Quasithin.SzN2.not_three_dvd_two_pow_sub_one hn
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four h4
  exact rank2_false_std d (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (by norm_num))
    (latShape_sl3 (by omega) hF h3)
    (CFSG.Quasithin.SzN2.sl_solvable_overgroup_le_normalizer (by norm_num)
      fun A hA hs => CFSG.Quasithin.SzN2.sl3_le_upperTriangular_of_solvable hK4 hA hs)
    normalizer_unitriangular_three_ne_top
    fun h => absurd h (not_three_dvd_card_normalizer_unitriangular_three hF hn)

end SL3

section Family

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem famSL3 (d : OvgData X A U K) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : False :=
  famSL3_std (d.map (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm))
    hF hn hn3

end Family

end SBd8

end CFSG.Quasithin
