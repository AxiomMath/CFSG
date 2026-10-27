module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GSL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Facts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GCover

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4.G

theorem exists_two_pow_mul_three_pow_of_dvd {N a b : ℕ} (h : N ∣ 2 ^ a * 3 ^ b) :
    ∃ x y : ℕ, N = 2 ^ x * 3 ^ y := by
  obtain ⟨k₁, k₂, h1, h2, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨x, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨y, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  exact ⟨x, y, rfl⟩

variable {G : Type} [Group G] [Finite G]

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

omit [Finite G] in
theorem three_dvd_card_X {n : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    3 ∣ Nat.card X := by
  obtain ⟨φ⟩ := e
  have hXN := le_normalizer_V X M I
  have h1 : Nat.card ↥(autOn X (P4V M I X)) ∣ Nat.card ↥X :=
    Subgroup.card_dvd_of_surjective (S153D.autOnHom_surjective hXN)
  have h2 : Nat.card ↥(autOn X (P4V M I X)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) :=
    (Nat.card_congr φ.toEquiv).trans
      (Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv.symm)
  have h3 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3),
      Nat.card_eq_fintype_card, hF,
      show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by norm_num)]
    have h4 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow 4 1 n
      have h5 : (2 ^ n) ^ 2 = 4 ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [h5]
      simpa using this
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h4 _) _
  exact h3.trans (h2 ▸ h1)

theorem isSolvable_sup (c : P4Ctx T Mc M H B₀ I X) :
    Group.IsSolvable ↥((oTwoUpper H ⊓ X) ⊔ (sOf152 T Mc M B₀ ⊓ X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := oTwoUpper H ⊓ X with hJ
  set A := sOf152 T Mc M B₀ ⊓ X with hA
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨c.A_le_normalizer_K hx, Subgroup.le_normalizer (inf_le_right (a := sOf152 T Mc M B₀) hx)⟩
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAJ
  have hK : Nat.card ↥(oTwoUpper H) = Nat.card ↥(pCoreOf 2 (oTwoUpper H)) * 9 := by
    rw [card_eq_card_pCoreOf_mul_relIndex (oTwoUpper H), c.relIndex_K]
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 (oTwoUpper H))
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp c.A_isPGroup
  have hJK : Nat.card ↥J ∣ 2 ^ i * 3 ^ 2 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : J ≤ oTwoUpper H)
    rw [hK, hi] at h
    have h9 : (2 : ℕ) ^ i * 3 ^ 2 = 2 ^ i * 9 := by norm_num
    rwa [h9]
  obtain ⟨x, y, hxy⟩ := exists_two_pow_mul_three_pow_of_dvd hJK
  have hdvd : Nat.card ↥(J ⊔ A) ∣ 2 ^ (x + a) * 3 ^ y := by
    have h1 : Nat.card ↥(J ⊔ A) ∣ Nat.card ↥J * Nat.card ↥A :=
      hcard ▸ Dvd.intro _ rfl
    rw [hxy, ha] at h1
    have h2 : 2 ^ x * 3 ^ y * 2 ^ a = 2 ^ (x + a) * 3 ^ y := by ring
    rwa [h2] at h1
  obtain ⟨x', y', hxy'⟩ := exists_two_pow_mul_three_pow_of_dvd hdvd
  exact E6.Spor.isSolvable_of_card_two_pow_mul_three_pow hxy'

theorem false_of_odd (hcover : AsA36NoOddCover) (c : P4Ctx T Mc M H B₀ I X)
    {n : ℕ} (hn : 1 < n) (hodd : Odd n) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    False := by
  have hC := inf_centralizer_eq_pCoreOf hcover c hF e
  obtain ⟨φ⟩ := e
  obtain ⟨E, hEK, hE, hE9⟩ := c.exists_E9
  have hne := exists_mem_inf_of_rank (pRank_three_le_two_of_hyp c) c.X_le_I (hEK.trans c.K_le_I)
    (hEK.trans c.K_norm) hE hE9 (three_dvd_card_X hF ⟨φ⟩)
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu3 : u ^ 3 = 1 := hE.2 u hu.1
  set J := oTwoUpper H ⊓ X with hJ
  set A := sOf152 T Mc M B₀ ⊓ X with hA
  have hXN := le_normalizer_V X M I
  have hAX : IsSylowTwoOf A X :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp c.comp) c.sylow
  have hJY : J ≤ J ⊔ A := le_sup_left
  have hAY : A ≤ J ⊔ A := le_sup_right
  have hYX : J ⊔ A ≤ X := sup_le inf_le_right inf_le_right
  set f := S153D.autOnHom hXN with hf
  have hfs : Function.Surjective f := S153D.autOnHom_surjective hXN
  have hPY : (A.subgroupOf X).map f ≤ ((J ⊔ A).subgroupOf X).map f :=
    Subgroup.map_mono (fun x hx => hAY hx)
  have hP2 : IsPGroup 2 ↥((A.subgroupOf X).map f) :=
    (hAX.isPGroup.comap_subtype (K := X)).map f
  have hPodd : ¬ 2 ∣ ((A.subgroupOf X).map f).index := fun hd =>
    hAX.2.2 (hd.trans (Subgroup.index_map_dvd _ hfs))
  have hsolv : Group.IsSolvable ↥(((J ⊔ A).subgroupOf X).map f) := by
    have : Group.IsSolvable ↥(J ⊔ A) := isSolvable_sup c
    have h1 : Group.IsSolvable ↥((J ⊔ A).subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hYX).injective
    exact Group.isSolvable_of_surjective (f := f.subgroupMap _)
      (MonoidHom.subgroupMap_surjective f _)
  have huJ : u ∈ J := ⟨hEK hu.1, hu.2⟩
  have huY : (⟨u, hu.2⟩ : ↥X) ∈ (J ⊔ A).subgroupOf X := hJY huJ
  have hfu : f ⟨u, hu.2⟩ ∈ ((J ⊔ A).subgroupOf X).map f := Subgroup.mem_map_of_mem f huY
  have h3 : (f ⟨u, hu.2⟩) ^ 3 = 1 := by
    have : (⟨u, hu.2⟩ : ↥X) ^ 3 = 1 := Subtype.ext hu3
    rw [← map_pow, this, map_one]
  have h1 := eq_one_of_mem_solvable_of_equiv hn hodd hF φ hPY hP2 hPodd hsolv hfu h3
  have hcentr : u ∈ Subgroup.centralizer (P4V M I X : Set G) :=
    (S153D.autOnHom_eq_one_iff hXN ⟨u, hu.2⟩).mp h1
  have hupc : u ∈ pCoreOf 2 X := by
    rw [← hC]
    exact ⟨hu.2, hcentr⟩
  exact hu1 (Subtype.ext (eq_one_of_isPGroup_two_of_pow_three (pCoreOf_isPGroup 2 X) hupc hu3))

end S15223P4.G

end CFSG.Quasithin
