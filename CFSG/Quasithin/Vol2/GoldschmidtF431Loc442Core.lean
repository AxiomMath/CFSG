module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Free
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.Quasithin.Background.GoldschmidtShultThm

public section

namespace CFSG.Quasithin.Loc442

open CFSG.Open CFSG.Quasithin.Shult MulAction

theorem divisors12288 : Nat.divisors 12288 =
    {1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048,
      3072, 4096, 6144, 12288} := by
  decide +kernel

theorem numerics (N b a m : ℕ) (h8 : 8 ∣ N) (hb : b ∣ 12288) (hodd : Odd a) (hab : a ∣ b)
    (hm : m = 60 ∨ m = 62400) (hn : (N + 1) * b = a * m) : False := by
  have hbd : b ∈ Nat.divisors 12288 := Nat.mem_divisors.2 ⟨hb, by norm_num⟩
  have had : a ∈ Nat.divisors 12288 := Nat.mem_divisors.2 ⟨hab.trans hb, by norm_num⟩
  rw [divisors12288] at hbd had
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbd had
  obtain ⟨c, rfl⟩ := h8
  rcases hodd with ⟨a', rfl⟩
  rcases hm with rfl | rfl <;>
  rcases hbd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases had with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h <;>
  omega

theorem odd_card_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

section Count

variable {K : Type*} [Group K] [Finite K] {X L : Subgroup K}

omit [Finite K] in
theorem smul_one_coset (l : ↥L) : l • ((1 : K) : K ⧸ X) = ((l : K) : K ⧸ X) := by
  rw [Subgroup.smul_def, Quotient.smul_coe]
  simp

theorem card_deltaSet_succ :
    (Nat.card ↥(deltaSet X L) + 1) * Nat.card ↥(X ⊓ L) = Nat.card ↥L := by
  classical
  have := Fintype.ofFinite ↥L
  have := Fintype.ofFinite ↥(orbit ↥L ((1 : K) : K ⧸ X))
  have := Fintype.ofFinite ↥(stabilizer ↥L ((1 : K) : K ⧸ X))
  have hstab : stabilizer ↥L ((1 : K) : K ⧸ X) = X.subgroupOf L := by
    ext l
    rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, smul_one_coset]
    exact mk_eq_one_iff _
  have horb : orbit ↥L ((1 : K) : K ⧸ X) = insert ((1 : K) : K ⧸ X) (deltaSet X L) := by
    ext c
    constructor
    · rintro ⟨l, rfl⟩
      beta_reduce
      rw [smul_one_coset]
      by_cases hl : (l : K) ∈ X
      · left
        exact (mk_eq_one_iff _).2 hl
      · right
        exact ⟨l, l.2, hl, rfl⟩
    · rintro (rfl | ⟨l, hl, hlX, rfl⟩)
      · exact ⟨1, by simp⟩
      · exact ⟨⟨l, hl⟩, smul_one_coset _⟩
  have hnot : ((1 : K) : K ⧸ X) ∉ deltaSet X L := by
    rintro ⟨l, hl, hlX, h⟩
    exact hlX ((mk_eq_one_iff _).1 h.symm)
  have hcard : Nat.card ↥(orbit ↥L ((1 : K) : K ⧸ X)) = Nat.card ↥(deltaSet X L) + 1 := by
    rw [horb, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hnot
      (Set.toFinite _), add_comm]
  have hb := card_orbit_mul_card_stabilizer_eq_card_group ↥L ((1 : K) : K ⧸ X)
  have hsub : Nat.card (X.subgroupOf L) = Nat.card ↥(X ⊓ L) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← hsub, ← hcard, ← hstab, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact hb

end Count

section Core


theorem acore {K : Type} [Group K] [Finite K] {X V : Subgroup K} (hX : X ≠ ⊤) (hVX : V ≤ X)
    (hVn : (V.subgroupOf X).Normal) (hV4 : Nat.card V = 4)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    (hfix : ShultFixedPoint X V) {q : K} (hqX : q ∈ X) (hqV : ∀ v ∈ V, q * v = v * q)
    (hq2 : q ^ 2 ∈ V) (hq2' : q ^ 2 ≠ 1) (hXc : Nat.card X ∣ 12288) : False := by
  have hVbot : V ≠ ⊥ := by
    intro h
    rw [h] at hV4
    simp at hV4
  have hElem : IsElemAbelian 2 V := ⟨⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩, hV2⟩
  have hyp : ShultI85Hyp X V := ⟨hX, hVbot, hVX, hVn, hElem, hfix⟩
  rcases shultI85Part1 K X V hyp with ⟨h2, -⟩ | ⟨f, hf, hBQ, -, hXL, hSE⟩
  · omega
  · have hf2 : f = 2 := by
      have : (2 : ℕ) ^ f = 2 ^ 2 := by rw [← hf, hV4]; norm_num
      exact Nat.pow_right_injective le_rfl this
    subst hf2
    set L := Subgroup.normalClosure (V : Set K) with hL
    have : L.Normal := Subgroup.normalClosure_normal
    have hVL : V ≤ L := Subgroup.le_normalClosure
    have h8 := eight_dvd hSE hVL hVX hV4 hV2 hqX hqV hq2 hq2'
    have hcount := card_deltaSet_succ (X := X) (L := L)
    have hZodd : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
      rw [hBQ.2.1]
      exact odd_card_fusionOddCore ↥L
    have hLZ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    have hm : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60 ∨
        Nat.card (↥L ⧸ Subgroup.center ↥L) = 62400 := by
      rcases hBQ.2.2 with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨a, ha, hfa, -⟩
      · left
        rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by norm_num)]
        norm_num
      · right
        rw [Nat.card_congr e.toEquiv,
          CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3 (by norm_num)]
        norm_num
      · omega
    have hZle : (Subgroup.center ↥L).map L.subtype ≤ X ⊓ L := by
      rintro _ ⟨z, hz, rfl⟩
      have hc : ∀ w ∈ L, (z : K) * w * (z : K)⁻¹ = w := by
        intro w hw
        have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨w, hw⟩)
        simp only [Subgroup.coe_mul] at this
        rw [← this]
        group
      have hzN : (z : K) ∈ Subgroup.normalizer (V : Set K) := by
        rw [Subgroup.mem_normalizer_iff]
        intro v
        constructor
        · intro hv
          rw [hc v (hVL hv)]
          exact hv
        · intro hv
          have hvL : v ∈ L := by
            have h1 : (z : K)⁻¹ * ((z : K) * v * (z : K)⁻¹) * (z : K) ∈ L :=
              L.mul_mem (L.mul_mem (L.inv_mem z.2) (hVL hv)) z.2
            simpa [mul_assoc] using h1
          rwa [hc v hvL] at hv
      have : (z : K) ∈ X ⊓ L := by
        rw [hXL]
        exact ⟨hzN, z.2⟩
      exact this
    have hab : Nat.card ↥(Subgroup.center ↥L) ∣ Nat.card ↥(X ⊓ L) := by
      have := Subgroup.card_dvd_of_le hZle
      rwa [Subgroup.card_map_of_injective L.subtype_injective] at this
    have hb : Nat.card ↥(X ⊓ L) ∣ 12288 := (Subgroup.card_dvd_of_le inf_le_left).trans hXc
    refine numerics (Nat.card ↥(deltaSet X L)) (Nat.card ↥(X ⊓ L)) _ _ h8 hb hZodd hab hm ?_
    rw [hcount, hLZ, mul_comm]

end Core

end CFSG.Quasithin.Loc442
