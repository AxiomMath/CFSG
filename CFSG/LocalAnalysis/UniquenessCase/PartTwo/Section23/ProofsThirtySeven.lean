module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNExc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.BZeroCentralizerZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsUniqueN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem IsInnerCartanOnL.exists_mem_orderOf_eq {K A L T : Subgroup G} {m r : ℕ}
    (hA : IsInnerCartanOnL A K L T m) (hm1 : m ≠ 0)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ m - 1) : ∃ a ∈ A, orderOf a = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hAcard : Nat.card A = 2 ^ m - 1 := hA.2.2.1
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) r (by rw [hAcard]; exact hrdvd)
  exact ⟨a, a.2, by rw [Subgroup.orderOf_coe]; exact ha⟩

theorem Ctx23L.exists_mem_B0_orderOf_eq {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h52 : S23_5_2 D Ch) {m r : ℕ} (hmdvd : m ∣ CFSG.Open.pRank 2 D.Z)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ m - 1) : ∃ b ∈ c.B0, orderOf b = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hmn : CFSG.Open.pRank 2 D.Z ∣ c.n := by
    rcases h52 h1930 c with h | ⟨-, -, h⟩
    · rw [← h]
    · rw [h]
      exact dvd_mul_left _ 2
  have hrdvdB : r ∣ Nat.card c.B0 := by
    have hreta : r ∈ etaSet c.n :=
      ⟨hr, hrdvd.trans ((Nat.pow_sub_one_dvd_pow_sub_one 2 hmdvd).trans
        (Nat.pow_sub_one_dvd_pow_sub_one 2 hmn))⟩
    rw [← c.hpi] at hreta
    exact hreta.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hrdvdB
  exact ⟨b, b.2, by rw [Subgroup.orderOf_coe]; exact hb⟩

theorem Ctx23L.inf_zpowers_eq_bot_of_le_centralizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    {K A : Subgroup G} (hAK : A ≤ K) (hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G))
    {a b : G} (haA : a ∈ A) (hbB0 : b ∈ c.B0) {r : ℕ} (hr : r.Prime)
    (har : orderOf a = r) (hbr : orderOf b = r) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
  by_contra hxne
  have hx1 : orderOf x ≠ 1 := fun h => hxne (orderOf_eq_one_iff.mp h)
  have hxdvd : orderOf x ∣ r := by
    have h1 : orderOf x ∣ Nat.card (Subgroup.zpowers b) := Subgroup.orderOf_dvd_natCard _ hxb
    rwa [Nat.card_zpowers, hbr] at h1
  have hxr : orderOf x = r := by
    rcases (Nat.dvd_prime hr).mp hxdvd with h | h
    · exact absurd h hx1
    · exact h
  have heq : Subgroup.zpowers x = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxb) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hxr, hbr]
  have hbzx : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
  have hbzp : b ∈ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hxa hbzx
  have hbA : b ∈ A := Subgroup.zpowers_le.mpr haA hbzp
  have hbK : b ∈ K := hAK hbA
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  exact Ctx23L.not_mem_centralizer_Z_of_mem_B0 D Ch h4 h23 h1930 c hbB0 hb1 (hKCZ hbK)

theorem Ctx23L.exists_order_r_pair {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h52 : S23_5_2 D Ch)
    {K : Subgroup G}
    (hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G))
    {m : ℕ} (hm2 : 2 ≤ m) (hmdvd : m ∣ CFSG.Open.pRank 2 D.Z)
    {A : Subgroup G} (hA : IsInnerCartanOnL A K c.L D.T m)
    (hAB : ⁅A, c.B0⁆ = ⊥)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ m - 1) (hr2m : ¬ r ∣ 2 * m) :
    ∃ a ∈ A, ∃ b ∈ c.B0, orderOf a = r ∧ orderOf b = r ∧ Commute a b ∧
      Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  classical
  have hm1 : m ≠ 0 := by omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hr2m (dvd_mul_right 2 m)
  obtain ⟨a, haA, har⟩ := IsInnerCartanOnL.exists_mem_orderOf_eq hA hm1 hr hrdvd
  obtain ⟨b, hbB0, hbr⟩ := c.exists_mem_B0_orderOf_eq h1930 h52 hmdvd hr hrdvd
  have hABcent : A ≤ Subgroup.centralizer (c.B0 : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hAB
  have hcomm : Commute a b :=
    (Subgroup.mem_centralizer_iff.mp (hABcent haA) b hbB0).symm
  exact ⟨a, haA, b, hbB0, har, hbr, hcomm,
    c.inf_zpowers_eq_bot_of_le_centralizer h1930 h4 h23 (hA.1.trans inf_le_left) hKCZ
      haA hbB0 hr har hbr⟩

theorem Ctx23L.cartan_conclusion_of_isL2_four {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h2112 : S21_12 D Ch) (h1930 : H1930 D)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hK4 : IsL2 (Bar2 K) 2) :
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (Bar2 K) q) ∧
      ⁅CFSG.Quasithin.opResidual 3 c.B, K⁆ ≤ CFSG.Open.pCoreOf 2 K := by
  have h5 : CFSG.Blueprint.LieModel (Bar2 K) .PSL 2 5 1 :=
    CFSG.ComponentClassification.CatLeafProof.X10CNE.lieModel_psl_two_five_of_four hK4
  haveI : IsSimpleGroup (Bar2 K) :=
    uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hK4
  have hcenter : Subgroup.center (Bar2 K) = ⊥ := uc22p21k_center_eq_bot hK.2.2
  obtain ⟨e⟩ : Nonempty (BarInf K ≃* Bar2 K) :=
    uc22p21k_barInf_equiv_of_center_bot hK.2.2 hcenter
  have h5' : CFSG.Blueprint.LieModel (BarInf K) .PSL 2 5 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm h5
  have hChev : IsChev (BarInf K) 5 :=
    ⟨.PSL, 2, 1, h5'.admissible, h5'⟩
  have hconcl := h2112 h1930 c.toCtx23.toCtx21 K hK 5 Nat.prime_five (by norm_num) hChev
  exact ⟨⟨5, Nat.prime_five, by norm_num, h5⟩, hconcl.2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
