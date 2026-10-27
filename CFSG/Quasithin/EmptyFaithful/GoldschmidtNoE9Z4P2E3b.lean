module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Cfg2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Loc
public import CFSG.Quasithin.Background.G2A5Iso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Normalizer

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem card_le_nine_of_isPGroup_three {X : Type*} [Group X] {L P : Subgroup X}
    (hPL : P ≤ L) (hL : Nat.card L = 3600) (hP3 : IsPGroup 3 ↥P) [Finite X] :
    Nat.card P ≤ 9 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP3
  have hdvd : Nat.card P ∣ 3600 := hL ▸ Subgroup.card_dvd_of_le hPL
  by_contra hbig
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have h2 : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : 27 ∣ Nat.card P := by
    rw [hn]
    exact pow_dvd_pow 3 hn3
  have := h27.trans hdvd
  omega

theorem e9_normalizer_le_of_E3 (h35 : Lemma1435) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p) (hC : Stage14614E9C3 T H)
    {T0 : Subgroup G} (h1 : pCoreOf 2 H ≤ T0) (h2 : T0 ≤ T) :
    Subgroup.normalizer (T0 : Set G) ⊓ mcOf T ≤ H := by
  classical
  have hshape' := hshape
  obtain rfl := hshape.1
  obtain ⟨K₁, s, hK₁, hsT, hsN, hKz, e, hG⟩ := hC
  have hcardF : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by omega)
  have hq : 4 ≤ Nat.card (GaloisField 2 2) := by rw [hcardF]; norm_num
  have hpF : 3 ∣ Nat.card (GaloisField 2 2) - 1 := by rw [hcardF]; norm_num
  obtain ⟨hsG, ⟨e1⟩, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hq hpF e
  have hKle := q_hatK_le hK₁ hsG hKz
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp (conjSub_mem_cComp_of_mem hK₁ hsG)
  have hsup : imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) =
      imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁) := by
    rw [hKz, q_image_sup hK₁G hK₂G]
  obtain ⟨Eh, -, hloc⟩ := e9Local_of_config h35 S hred hshape'
  have hSyl := q_hatT_sylow S
  have hSyl₁ := q_isSylowTwoOf_inf_fst hF hSyl
  have hSyl₂ := q_isSylowTwoOf_inf_snd hF hSyl
  let e₂ : ↥(imageOTwoQuot (mcOf T) (conjSub s K₁)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) := (q_equiv_snd hF).trans e1.symm
  have hB₁ := sl2_normalizer_inf_solvable_dvd e1.symm inf_le_right hSyl₁.2.1 hSyl₁.2.2
  have hB₂ := sl2_normalizer_inf_solvable_dvd e₂ inf_le_right hSyl₂.2.1 hSyl₂.2.2
  have hBs := q_two_closed_prod_normalizer_solvable _ _ hF.comm hF.disj
    (imageOTwoQuot (mcOf T) T ⊓ imageOTwoQuot (mcOf T) K₁)
    (imageOTwoQuot (mcOf T) T ⊓ imageOTwoQuot (mcOf T) (conjSub s K₁)) inf_le_right inf_le_right
    hB₁.1 hB₂.1
  have hEq := q_inf_sup_eq hF hSyl
  have hHU : ∀ x ∈ imageOTwoQuot (mcOf T) H, x ∈ Subgroup.normalizer
      ((imageOTwoQuot (mcOf T) T ⊓ imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) :
        Subgroup (OTwoQuot (mcOf T))) : Set (OTwoQuot (mcOf T))) := by
    intro x hx
    rw [hsup]
    exact q_hat_normalizes_U_sl2 S hred hF hq e1.symm hKle x hx
  have hNs : Group.IsSolvable ↥(Subgroup.normalizer
      ((imageOTwoQuot (mcOf T) T ⊓ imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) :
        Subgroup (OTwoQuot (mcOf T))) : Set (OTwoQuot (mcOf T))) ⊓
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))) := by
    rw [hsup, hEq]
    exact hBs
  have hr : ∀ A : Subgroup (OTwoQuot (mcOf T)), imageOTwoQuot (mcOf T) H ≤ A →
      Group.IsSolvable ↥A → ∀ r : ℕ, r.Prime → r ∣ Nat.card A → r = 2 ∨ r = 3 :=
    fun A hHA hA r hr hd => e9_primes_of_solvable S hred hmax hshape' hHA hA r hr hd
  have hcard : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) = 60 := by
    rw [← Nat.card_congr e1.toEquiv]
    exact CFSG.Quasithin.A5Model.card_sl2_gf4
  have hL3 : ∀ P : Subgroup (OTwoQuot (mcOf T)),
      P ≤ imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) →
        IsPGroup 3 ↥P → Nat.card P ≤ 9 := by
    intro P hPL hP3
    refine card_le_nine_of_isPGroup_three hPL ?_ hP3
    rw [hsup, q_card_sup_pair hF, hcard]
    norm_num
  exact e9_normalizer_le_of_hat S hred h1 h2
    (hloc.normalizer_le (e9_hX_of_eq_sup S hG) hHU hNs hr hL3 (q_image_mono h1) (q_image_mono h2))

end Normalizer

end CFSG.Quasithin
