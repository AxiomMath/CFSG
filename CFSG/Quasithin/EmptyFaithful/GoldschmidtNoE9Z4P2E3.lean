module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Defs
public import CFSG.Quasithin.EmptyFaithful.S146zSWr
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.Quasithin.Background.G2A5Iso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Case

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9_index_and_sup_sl2_four (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ 3)
    (hmax : PMaximal T M 3) {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T))
    (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) :
    (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 8 ∧
      mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T := by
  classical
  have hcardF : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by omega)
  have hq : 4 ≤ Nat.card (GaloisField 2 2) := by rw [hcardF]; norm_num
  have hpF : 3 ∣ Nat.card (GaloisField 2 2) - 1 := by rw [hcardF]; norm_num
  obtain ⟨hsG, ⟨e1⟩, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hq hpF e
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp (conjSub_mem_cComp_of_mem hK₁ hsG)
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 (GaloisField 2 2)
    CFSG.Quasithin.A5Model.card_gf4 CFSG.Quasithin.A5Model.card_sl2_gf4
  have hcard : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) = 60 := by
    rw [← Nat.card_congr e1.toEquiv]
    exact CFSG.Quasithin.A5Model.card_sl2_gf4
  have hbot : imageOTwoQuot (mcOf T) K₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hautcard :
      Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) = 120 := by
    rw [Nat.card_congr (CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm e5).toEquiv,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hA : Nat.card (MulAut ↥(imageOTwoQuot (mcOf T) K₁)) =
      2 ^ 1 * Nat.card ↥(imageOTwoQuot (mcOf T) K₁) := by
    rw [← Nat.card_congr (MulAut.congr e1).toEquiv, hautcard, hcard]
    norm_num
  have hidx := q_index_dvd_of_card_aut_pow hF hbot hA
  have hsup : imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁) =
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) := by
    rw [hKz, q_image_sup hK₁G hK₂G]
  rw [hsup] at hidx
  have hidx8 : (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 2 ^ 3 :=
    hidx
  have : (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).Normal := by
    rw [← hsup]
    exact hF.normal
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp hidx8
  have hpq : IsPGroup 2 (OTwoQuot (mcOf T) ⧸
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))) :=
    IsPGroup.of_card (n := j) (by rw [← Subgroup.index_eq_card, hj])
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := by
    rw [hKz]
    exact sup_le hK₁G hK₂G
  refine ⟨by simpa using hidx8, le_antisymm ?_ (sup_le hKzG ?_)⟩
  · exact q_le_sup_of_isPGroup_quotient S hpq
  · exact hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)

theorem e9_caseE3 (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (hshape : IsE9Z4Shape T H p) {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T))
    (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁) {m : ℕ} (hm : 2 ≤ m)
    (hpm : 3 ∣ 2 ^ m - 1)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) :
    Stage14614E9C3 T H := by
  classical
  obtain rfl := hshape.1
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
    rcases q_prime_dvd_pred S hred hmax hF hq e1.symm hKle hr (by rw [hcardF]; exact hd) with
      h | h
    · exact h
    · omega
  subst hm2
  obtain ⟨-, hG⟩ := e9_index_and_sup_sl2_four h36 hlist iS S hred hmax hK₁ hsT hsN hKz e
  exact ⟨K₁, s, hK₁, hsT, hsN, hKz, e, hG⟩

end Case

end CFSG.Quasithin
