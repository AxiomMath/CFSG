module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.Quasithin.Vol2.Ch5AssemblyClause
public import CFSG.GH74.Orders.LieType
public import CFSG.Timmesfeld.Final.Simple
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_14_notf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ quasithinIsFaithfulLocal T (oTwoUpper H)

section Orders

theorem ordA_one_ne_20160' (m : ℕ) : ordA 1 m ≠ 20160 := by
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge m 35 with hm | hm
  · interval_cases m <;> decide
  · have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (20160 + 1) ≤ m * (m ^ 2 - 1) := by
      have h1 : 35 * 1224 ≤ m * (m ^ 2 - 1) := by
        have h2 : 1224 ≤ m ^ 2 - 1 := by
          have : 35 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
          omega
        exact Nat.mul_le_mul hm h2
      omega
    have h1 : m * (m ^ 2 - 1) / 2 ≤ m * (m ^ 2 - 1) / Nat.gcd 2 (m - 1) :=
      Nat.div_le_div_left hle hg
    have h2 : 20160 + 1 ≤ m * (m ^ 2 - 1) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
    exact (Nat.lt_of_lt_of_le (Nat.lt_of_succ_le h2) h1).ne'

theorem not_three_dvd_ordSuzuki {f : ℕ} (hf : Odd f) : ¬ 3 ∣ ordSuzuki (2 ^ f) := by
  obtain ⟨a, rfl⟩ := hf
  have h1 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  unfold ordSuzuki
  generalize 2 ^ (2 * a + 1) = q at h1 ⊢
  have e1 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h1]
  have e2 : (q ^ 2 + 1) % 3 = 2 := by omega
  have e3 : (q - 1) % 3 = 1 := by omega
  have : q ^ 2 * (q ^ 2 + 1) * (q - 1) % 3 = 2 := by
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 2), e1, e2, e3]
  omega

variable {X : Type} [Group X]

theorem card_of_lieModel_PSL34 (hK : LieModel X .PSL 3 2 2) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (hK.statedClassicalModel (by decide))

theorem not_lieModel_PSL2_of_PSL34 (hK : LieModel X .PSL 3 2 2) {k : ℕ}
    (h : LieModel X .PSL 2 2 k) : False := by
  have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) h
  rw [card_of_lieModel_PSL34 hK] at h1
  exact ordA_one_ne_20160' _ h1.symm

theorem not_suzukiModel_of_PSL34 (hK : LieModel X .PSL 3 2 2) {k : ℕ}
    (h : SuzukiModel X 2 k) : False := by
  obtain ⟨-, a, -, hf, hc⟩ := CFSG.GH74.card_of_suzukiModel h
  rw [card_of_lieModel_PSL34 hK] at hc
  apply not_three_dvd_ordSuzuki (f := k) ⟨a, hf⟩
  rw [← hc]
  norm_num

end Orders

section General

variable {G : Type} [Group G]

theorem perfect_conjClosure {K₁ T : Subgroup G} (h : ⁅K₁, K₁⁆ = K₁) :
    ⁅conjClosure K₁ T, conjClosure K₁ T⁆ = conjClosure K₁ T := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  refine conjClosure_le fun t ht z hz => ?_
  have hmap : K₁.map (MulAut.conj t).toMonoidHom ≤ conjClosure K₁ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_conjClosure ht hy
  have hz' : t * z * t⁻¹ ∈ K₁.map (MulAut.conj t).toMonoidHom := ⟨z, hz, rfl⟩
  rw [← h, Subgroup.map_commutator] at hz'
  exact Subgroup.commutator_mono hmap hmap hz'

end General

variable {G : Type} [Group G] [Finite G]

theorem isMaximalLocal_of_L34
    (h510 : Stmt5_1_10) (h5112 : Stmt5_1_12)
    {T M L H B D : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hN : IsNotation5_1_9 T M L H B D) (hK : LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2) :
    quasithinIsMaximalLocal T (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨k, hk⟩ := h510.exists_fieldParam hyp hN
  obtain ⟨-, K₁, hK₁, hKeq, -⟩ := id hk
  set K := oTwoUpper H with hKdef
  have hperf : ⁅K, K⁆ = K := by
    rw [hKeq]
    exact perfect_conjClosure hK₁.2.1
  have hs : IsSimpleGroup (O2Q K) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hK
  have hKH : K ≤ H := oTwoUpper_le H
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_oTwoUpper H)
  have hKC : quasithinIsCComponent K H := mem_cComp_of_normal_of_simple hKH hKn hperf hs
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hH.1.1.trans (le_normalizer_oTwoUpper H)
  have hKK : K = conjClosure K T := by
    apply le_antisymm (le_conjClosure K T)
    exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hTK ht) z).mp hz
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  have hHeq : H = K ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTH
  have hloc : quasithinIsLocal T K := by
    refine ⟨h.sylow.1, ?_, ?_, ?_⟩
    · rw [← hHeq]
      exact hKC
    · rw [← hHeq]
      exact hTH.2.2
    · rw [← hHeq]
      exact hH.1.2
  refine ⟨hloc, fun K' hK' hKK' => ?_⟩
  have hHX : InH H (K' ⊔ T) := ⟨hHeq.le.trans (sup_le_sup_right hKK' T), hK'.2.2.2⟩
  obtain ⟨Kh₁, hhat, -, hcases⟩ :=
    h5112 G T M L H B D K n k hyp hN hk hKC hKK (K' ⊔ T) hHX
  have hK'eq : K' = Kh₁ := hhat.2.2 K' hK'.2.1 hKK'
  rcases hcases with h1 | ⟨hlt, -⟩ | ⟨hsz, -⟩ | ⟨hl2, -⟩ | ⟨hl4, -⟩
  · apply le_antisymm _ hKK'
    rw [hK'eq, hKdef, h1]
    exact le_conjClosure Kh₁ T
  · exact absurd hlt (lt_irrefl K)
  · exact (not_suzukiModel_of_PSL34 hK hsz).elim
  · exact (not_lieModel_PSL2_of_PSL34 hK hl2).elim
  · exact (not_lieModel_PSL2_of_PSL34 hK hl4).elim

theorem stmt5_1_14_one_of
    (h510 : Stmt5_1_10) (h5112 : Stmt5_1_12) (hnf : Stmt5_1_14_notf) :
    Stmt5_1_14_one := fun G _ _ T M L V H B D n hyp hN hV hK =>
  ⟨isMaximalLocal_of_L34 h510 h5112 hyp hN hK, hnf G T M L V H B D n hyp hN hV hK⟩

end CFSG.Quasithin.H13
