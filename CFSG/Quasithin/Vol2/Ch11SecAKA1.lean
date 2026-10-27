module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4J
public import CFSG.Quasithin.Vol2.Ch11SecQ9aSp4P

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq act_N0_mod usp_le_perfectCore)

namespace KA

theorem exists_point_coords {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π) {P : Subgroup (MulAut W)}
    (hP : QuasithinUnique.IsSylowTwoOf P H) {U : Subgroup W}
    (hU : Ch11.SecA.IsFlagW H P Z (2 ^ n) 1 U) :
    ∃ (f : W → (Fin 2 ⊕ Fin 2 → K)) (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
      (g : StatedSp 2 K),
      (∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W)) ∧
        U = hf.pre (gmapSp g (spLine K)).toAddSubgroup := by
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [← hK] at hU
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU
  exact ⟨f, hf, g, hg, by rw [(eq_std_of_stable_sp hS).1 (by rw [hc, pow_one])]⟩

end KA

theorem factPointSp4_holds : Ch11.SecA.FactPointSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  obtain ⟨f, hf, g, -, rfl⟩ := KA.exists_point_coords hn hK hW hπ hP hU
  intro h hh u hu
  rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) =
    Ch11.SecS.gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup) from rfl,
    gammaW_pre_eq hf g 0 _ flag_one_eq] at hh
  obtain ⟨M, hM, rfl⟩ := hh
  exact (hf.eq_iff _ _).mp (act_N0_mod hf g hM hu)

theorem factSylowLeviSp4_holds : Ch11.SecA.FactSylowLeviSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  obtain ⟨f, hf, g, hg, rfl⟩ := KA.exists_point_coords hn hK hW hπ hP hU
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
  rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) =
    Ch11.SecS.gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup) from rfl,
    gammaW_pre_eq hf g 0 _ flag_one_eq]
  exact ⟨u, usp_le_perfectCore hK4 hu, rfl⟩

end CFSG.Quasithin.Vol2.KGNat
