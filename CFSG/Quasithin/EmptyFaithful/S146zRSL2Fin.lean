module

public import CFSG.Quasithin.EmptyFaithful.S146zRSL2Set
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.Quasithin.EmptyFaithful.S146zQArith

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped MatrixGroups

section Fin

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_wreath_A5 (h12 : Stage14612PartP) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ 3)
    (hmax : PMaximal T M 3) {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁) {m : ℕ} (hm : 2 ≤ m)
    (hpm : 3 ∣ 2 ^ m - 1)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) :
    m = 2 ∧ Nonempty (OTwoQuot (mcOf T) ≃*
      (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))) := by
  classical
  have hcardF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hq : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpF : 3 ∣ Nat.card (GaloisField 2 m) - 1 := by rw [hcardF]; exact hpm
  obtain ⟨hsG, ⟨e1⟩, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hq hpF e
  have hKle := q_hatK_le hK₁ hsG hKz
  have hm2 : m = 2 := by
    refine m_eq_two_of_prime_dvd hm fun r hr hd => ?_
    rcases q_prime_dvd_pred S hred hmax hF hq e1.symm hKle hr (by rw [hcardF]; exact hd) with h | h
    · exact h
    · omega
  subst hm2
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 (GaloisField 2 2)
    CFSG.Quasithin.A5Model.card_gf4 CFSG.Quasithin.A5Model.card_sl2_gf4
  have hautcard :
      Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) = 120 := by
    rw [Nat.card_congr (CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm e5).toEquiv,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcardL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 :=
    CFSG.Quasithin.A5Model.card_sl2_gf4
  have hrel : 2 * Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) ^ 2 ≤
      (pCoreOf 2 H).relIndex T *
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) ^ 2 := by
    rw [q_relIndex_eq_eight h12 S hred hmax, hautcard, hcardL]
    norm_num
  obtain ⟨eW⟩ := q_wreath_SL2 h36 hlist iS S hred hmax hK₁ hsT hsN hKz hq hpF e hrel
  exact ⟨rfl, ⟨eW.trans (RegularWreathProduct.congr
    (CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm e5) (MulEquiv.refl _))⟩⟩

end Fin

end CFSG.Quasithin
