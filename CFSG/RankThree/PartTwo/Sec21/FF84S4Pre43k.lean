module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42b

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem le_sylow_of_two_group {X V Q : Subgroup G} (hV : IsSylowOf 2 V X) (hVQ : V ≤ Q)
    (hQX : Q ≤ X) (hQ2 : IsPGroup 2 Q) : Q ≤ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hkQ⟩ := FF79.L41.exists_conj_le_sylowOf_p hV hQX hQ2
  have hle : conjBy k Q ≤ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hkQ y hy
  have hcard := Subgroup.card_le_of_le hle
  rw [FF79.L41.card_conjBy] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hVQ hcard).ge

theorem le_Op_nor {V : Subgroup G} (hV : IsPGroup 2 V) : V ≤ Op 2 (Nor V) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine FF79.L41.le_Op_of_normalized (fun y hy => FF79.L41.mem_nor_of_forall (fun z hz =>
    V.mul_mem (V.mul_mem hy hz) (V.inv_mem hy))) (fun g hg x hx => ?_) hV
  exact ((Subgroup.mem_set_normalizer_iff.mp hg) x).mp hx

theorem tstar_cen_b (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    {V : Subgroup G} (hV : IsSylowOf 2 V (Opp 3 (Cen b))) : Op 2 (Nor V) ⊓ Cen b ≤ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXL : Opp 3 (Cen b) ≤ CenS L := X_le_cenS_L h.hyp hA
  have hVL : ∀ l ∈ L, ∀ y ∈ V, l * y * l⁻¹ = y := by
    intro l hl y hy
    rw [Subgroup.mem_centralizer_iff.1 (hXL (hV.1 hy)) l hl]
    group
  have hLN : ∀ l ∈ L, l ∈ Nor V := fun l hl =>
    FF79.L41.mem_nor_of_forall (fun y hy => by rw [hVL l hl y hy]; exact hy)
  have hT2 : IsPGroup 2 (Op 2 (Nor V)) := FF79.L41.Op_isPGroup _
  have hLT : ∀ l ∈ L, ∀ z ∈ Op 2 (Nor V), l * z * l⁻¹ ∈ Op 2 (Nor V) := fun l hl z hz =>
    FF79.L41.Op_conj_mem (hLN l hl) hz
  rintro u ⟨huT, huc⟩
  have huN : u ∈ Nor L := h.hyp.hLN huc
  have h3N : ¬ 3 ∣ Nat.card ↥(Op 2 (Nor V) ⊓ L) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hT2.to_inf_left : IsPGroup 2 ↥(Op 2 (Nor V) ⊓ L))
    rw [hn]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hcomm : ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ L ⊓ CenS L := by
    intro l hl
    have hmL : u * l * u⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 huN l).1 hl) (inv_mem hl)
    have hmT : u * l * u⁻¹ * l⁻¹ ∈ Op 2 (Nor V) := by
      have := mul_mem huT (hLT l hl u⁻¹ (inv_mem huT))
      rwa [show u * (l * u⁻¹ * l⁻¹) = u * l * u⁻¹ * l⁻¹ by group] at this
    refine ⟨hmL, ?_⟩
    have hN := normal_three'_central h.hyp hA (N := Op 2 (Nor V) ⊓ L) inf_le_right
      (fun l' hl' x hx => ⟨hLT l' hl' x hx.1, L.mul_mem (L.mul_mem hl' hx.2) (L.inv_mem hl')⟩)
      h3N (u * l * u⁻¹ * l⁻¹) ⟨hmT, hmL⟩
    exact Subgroup.mem_centralizer_iff.2 (fun l' hl' => (hN l' hl').symm)
  have huCL := FF79.L41.centralizes_of_comm_central h.hyp.quasi.1 hcomm
  have huCenS : u ∈ CenS L := Subgroup.mem_centralizer_iff.2 huCL
  obtain ⟨i, x, hx, hux⟩ := Q_decomp' h (Z_sq hA) u ⟨huc, huCenS⟩
  obtain ⟨k, hk⟩ := hT2 ⟨u, huT⟩
  have hk' : u ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hxc : x ∈ Cen b := FF79.L14.Opp_le 3 _ hx
  have hbx : Commute b x := (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  have hcm : Commute (b ^ i) x := hbx.zpow_left i
  have hN : ¬ 3 ∣ 2 ^ k := fun hd => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hcN : (b ^ i) ^ (2 ^ k) * x ^ (2 ^ k) = 1 := by
    rw [← hcm.mul_pow, ← hux]; exact hk'
  have hy : (b ^ i) ^ (2 ^ k) ∈ Opp 3 (Cen b) := by
    have : (b ^ i) ^ (2 ^ k) = (x ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hcN
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hx _)
  have hb3 : b ^ 3 = 1 := h.hyp.ord ▸ pow_orderOf_eq_one b
  have hbi3 : (b ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hy3 : ((b ^ i) ^ (2 ^ k)) ^ 3 = 1 := by rw [pow_right_comm, hbi3, one_pow]
  have hy1 : (b ^ i) ^ (2 ^ k) = 1 := by
    have d1 : orderOf ((b ^ i) ^ (2 ^ k)) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have d2 : orderOf ((b ^ i) ^ (2 ^ k)) ∣ Nat.card (Opp 3 (Cen b)) :=
      (Subgroup.orderOf_mk _ hy).symm ▸ Subgroup.orderOf_dvd_natCard _ hy
    have := Nat.eq_one_of_dvd_coprimes (FF79.L14.Opp_coprime 3 (Cen b)) d1 d2
    exact orderOf_eq_one_iff.mp this
  have hbi : b ^ i = 1 := by
    rw [← zpow_natCast, ← zpow_mul] at hy1
    have h1 : ((orderOf b : ℕ) : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr hy1
    rw [h.hyp.ord] at h1
    have h3 : (3 : ℤ) ∣ i := by
      rcases Int.prime_three.dvd_or_dvd h1 with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) hN
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [h.hyp.ord]; exact h3)
  have huX : u ∈ Opp 3 (Cen b) := by
    rw [hux, hbi, one_mul]; exact hx
  exact le_sylow_of_two_group hV (le_inf (le_Op_nor hV.2.1) hV.1) inf_le_right
    (hT2.to_inf_left : IsPGroup 2 ↥(Op 2 (Nor V) ⊓ Opp 3 (Cen b))) ⟨huT, huX⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
