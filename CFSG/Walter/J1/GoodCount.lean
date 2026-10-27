module

public import CFSG.Walter.J1.Exclude27

public section

namespace CFSG.Walter.J1

section General

variable {G : Type*} [Group G]

theorem card_dvd_of_free {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X]
    (hfree : ∀ (k : K) (x : X), k • x = x → k = 1) : Nat.card K ∣ Nat.card X := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype X := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    MulAction.card_eq_sum_card_group_div_card_stabilizer K X]
  refine Finset.dvd_sum fun ω _ => ?_
  have hstab : Fintype.card (MulAction.stabilizer K ω.out) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨1, fun k => Subtype.ext ?_⟩
    exact hfree k ω.out (MulAction.mem_stabilizer_iff.mp k.2)
  rw [hstab, Nat.div_one]

@[reducible, expose] def conjActionOn (K : Subgroup G) (S : Set (Subgroup G))
    (hS : ∀ k ∈ K, ∀ Y ∈ S, Y.map (MulAut.conj k).toMonoidHom ∈ S) : MulAction K S where
  smul k Y := ⟨Y.1.map (MulAut.conj (k : G)).toMonoidHom, hS k k.2 Y.1 Y.2⟩
  one_smul Y := Subtype.ext (map_conj_one Y.1)
  mul_smul k l Y := Subtype.ext (map_conj_mul Y.1 k l)

theorem mem_normalizer_of_map_conj_eq [Finite G] {Y : Subgroup G} {k : G}
    (hk : Y.map (MulAut.conj k).toMonoidHom = Y) : k ∈ Subgroup.normalizer (Y : Set G) :=
  mem_normalizer_of_conj_mem fun _ hy => hk ▸ conj_mem_map_conj hy

end General

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

@[expose] def goodSet (A : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≤ A ∧ Nat.card Y = 3 ∧ ∃ y : G, orderOf y = 2 ∧ Y ≤ Subgroup.centralizer ({y} : Set G)}

omit [Finite G] in
theorem map_conj_mem_goodSet {A : Subgroup G} {k : G} (hk : k ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ goodSet A) : Y.map (MulAut.conj k).toMonoidHom ∈ goodSet A := by
  obtain ⟨hYA, hY3, y, hy, hYy⟩ := hY
  refine ⟨?_, ?_, k * y * k⁻¹, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hk z).mp (hYA hz)
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hY3]
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp (hYy hz)
    change k * z * k⁻¹ * (k * y * k⁻¹) = k * y * k⁻¹ * (k * z * k⁻¹)
    calc k * z * k⁻¹ * (k * y * k⁻¹) = k * (z * y) * k⁻¹ := by group
      _ = k * (y * z) * k⁻¹ := by rw [hzy]
      _ = k * y * k⁻¹ * (k * z * k⁻¹) := by group

omit [Finite G] in
theorem eq_of_mem_of_mem {Y Y' : Subgroup G} (hY : Nat.card Y = 3) (hY' : Nat.card Y' = 3)
    {z : G} (hz : z ∈ Y) (hz' : z ∈ Y') (hz1 : z ≠ 1) : Y = Y' := by
  rw [eq_zpowers_of_card_prime Nat.prime_three hY hz hz1,
    eq_zpowers_of_card_prime Nat.prime_three hY' hz' hz1]

theorem ncard_goodSet_le {A : Subgroup G} (hA : Nat.card A = 27) :
    (goodSet A).ncard ≤ 13 := by
  classical
  have : Finite (goodSet A) := Set.toFinite _ |>.to_subtype
  have hgen : ∀ Y : goodSet A, ∃ y ∈ (Y : Subgroup G), y ≠ 1 := fun Y =>
    exists_ne_one_of_card Y.2.2.1 (by norm_num)
  choose gen hgenY hgen1 using hgen
  have hgen3 : ∀ Y : goodSet A, gen Y ^ 3 = 1 := fun Y => by
    rw [← Y.2.2.1]; exact pow_card_eq_one_of_mem (hgenY Y)
  let φ : goodSet A × Bool → {z : G // z ∈ A ∧ z ≠ 1} := fun p =>
    if p.2 then ⟨gen p.1, p.1.2.1 (hgenY p.1), hgen1 p.1⟩
    else ⟨(gen p.1)⁻¹, A.inv_mem (p.1.2.1 (hgenY p.1)), inv_ne_one.mpr (hgen1 p.1)⟩
  have hinv : ∀ Y : goodSet A, (gen Y)⁻¹ ≠ gen Y := by
    intro Y h1
    apply hgen1 Y
    have h2 : gen Y * gen Y = 1 := by
      calc gen Y * gen Y = gen Y * (gen Y)⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel _
    have h3 := hgen3 Y
    rw [pow_three, h2, mul_one] at h3
    exact h3
  have hφ : Function.Injective φ := by
    rintro ⟨Y, b⟩ ⟨Y', b'⟩ hYY
    have hYY' : ∀ (z : G), z ∈ (Y : Subgroup G) → z ∈ (Y' : Subgroup G) → z ≠ 1 → Y = Y' :=
      fun z hz hz' hz1 => Subtype.ext (eq_of_mem_of_mem Y.2.2.1 Y'.2.2.1 hz hz' hz1)
    cases b <;> cases b' <;> simp only [φ, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq]
      at hYY
    ·
      have h1 := inv_injective hYY
      obtain rfl := hYY' (gen Y) (hgenY Y) (h1 ▸ hgenY Y') (hgen1 Y)
      rfl
    ·
      have hmem : gen Y' ∈ (Y : Subgroup G) := hYY ▸ (Y : Subgroup G).inv_mem (hgenY Y)
      obtain rfl := hYY' (gen Y') hmem (hgenY Y') (hgen1 Y')
      exact absurd hYY (hinv Y)
    · have hmem : gen Y ∈ (Y' : Subgroup G) := hYY ▸ (Y' : Subgroup G).inv_mem (hgenY Y')
      obtain rfl := hYY' (gen Y) (hgenY Y) hmem (hgen1 Y)
      exact absurd hYY.symm (hinv Y)
    · obtain rfl := hYY' (gen Y) (hgenY Y) (hYY ▸ hgenY Y') (hgen1 Y)
      rfl
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle
  have hcard : Nat.card {z : G // z ∈ A ∧ z ≠ 1} = 26 := by
    have : Nat.card {z : G // z ∈ A ∧ z ≠ 1} = ({z : G | z ∈ A ∧ z ≠ 1} : Set G).ncard :=
      (Nat.card_coe_set_eq _)
    rw [this]
    have hset : ({z : G | z ∈ A ∧ z ≠ 1} : Set G) = (A : Set G) \ {1} := by
      ext z; simp
    rw [hset, Set.ncard_sdiff_singleton_of_mem (by simp), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, hA]
  rw [hcard] at hle
  rw [← Nat.card_coe_set_eq]
  omega

include h in
theorem eq_coord_of_good {a b : G} (hT : IsFour a b) {A : Subgroup G} (hM : IsMaxInv a b A)
    (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : Nat.card A = 27)
    (ha : Nat.card (A ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 3)
    (hb : Nat.card (A ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = 3)
    (hab : Nat.card (A ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = 3)
    {ν : G} (hνA : ν ∈ Subgroup.normalizer (A : Set G)) (hν3 : orderOf ν = 3) (hνA' : ν ∉ A)
    {X : Subgroup G} (hX : X ∈ goodSet A) :
    X = A ⊓ Subgroup.centralizer ({a} : Set G) ∨ X = A ⊓ Subgroup.centralizer ({b} : Set G) ∨
      X = A ⊓ Subgroup.centralizer ({a * b} : Set G) := by
  classical
  set Aa := A ⊓ Subgroup.centralizer ({a} : Set G)
  set Ab := A ⊓ Subgroup.centralizer ({b} : Set G)
  set Aab := A ⊓ Subgroup.centralizer ({a * b} : Set G)
  set 𝒢 := goodSet A
  set 𝒞 : Set (Subgroup G) := {Aa, Ab, Aab}
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions a b hT.mul_self_a hT.mul_self_b
    hT.2.2.2
  have hT4 : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b hT.mul_self_a hT.mul_self_b hT.a_ne_one hT.b_ne_one hT.2.2.1 _
  have hmemT := fun x => mem_kleinFour_iff (x := x) hT.mul_self_a hT.mul_self_b hT.2.2.2
  have hTN : T ≤ Subgroup.normalizer (A : Set G) := kleinFour_le_normalizer hT hM.1
  have hfour := h.inf_centralizer_four_eq_bot hT hM.1.1
  have e4 : b * a = a * b := hT.2.2.2.symm
  have hT1 : IsFour b a := hT.swap
  have hM1 : IsMaxInv b a A := hM.swap
  have hT3 : IsFour (a * b) a := hT.mul_right.swap
  have hM3 : IsMaxInv (a * b) a A := (hM.mul_right hT).swap
  have hAa𝒢 : Aa ∈ 𝒢 := ⟨inf_le_left, ha, a, hT.1, inf_le_right⟩
  have hAb𝒢 : Ab ∈ 𝒢 := ⟨inf_le_left, hb, b, hT.2.1, inf_le_right⟩
  have hAab𝒢 : Aab ∈ 𝒢 := ⟨inf_le_left, hab, a * b, hT.orderOf_mul, inf_le_right⟩
  have h𝒞𝒢 : 𝒞 ⊆ 𝒢 := by
    rintro Y (rfl | rfl | rfl)
    exacts [hAa𝒢, hAb𝒢, hAab𝒢]
  have hne : ∀ {x y : G}, x * y = y * x → orderOf x = 2 → orderOf y = 2 → x ≠ y →
      (x = a ∨ x = b ∨ x = a * b) → (y = a ∨ y = b ∨ y = a * b) →
      A ⊓ Subgroup.centralizer ({x} : Set G) ≠ A ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro x y hxy hx hy hxy' hxT hyT h0
    have hx3 : Nat.card (A ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 3 := by
      rcases hxT with rfl | rfl | rfl <;> assumption
    have hT' : IsFour x y := ⟨hx, hy, hxy', hxy⟩
    have := h.inf_centralizer_four_eq_bot hT' hM.1.1
    rw [h0, inf_assoc, inf_idem] at this
    rw [h0, this, Subgroup.card_bot] at hx3
    omega
  have hcab : a * (a * b) = (a * b) * a := by rw [hT.a_mul_mul, hT.mul_mul_a]
  have hcbab : b * (a * b) = (a * b) * b := by rw [hT.b_mul_mul, mul_assoc, hT.mul_self_b,
    mul_one]
  have h12 : Aa ≠ Ab := hne hT.2.2.2 hT.1 hT.2.1 hT.2.2.1 (Or.inl rfl) (Or.inr (Or.inl rfl))
  have h13 : Aa ≠ Aab := hne hcab hT.1 hT.orderOf_mul hT.mul_ne_a.symm (Or.inl rfl)
    (Or.inr (Or.inr rfl))
  have h23 : Ab ≠ Aab := hne hcbab hT.2.1 hT.orderOf_mul hT.mul_ne_b.symm (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr rfl))
  have h𝒞card : 𝒞.ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨h12, h13⟩),
      Set.ncard_pair h23]
  have h𝒢3 : 3 ∣ 𝒢.ncard := by
    set K := Subgroup.zpowers ν
    have hKN : ∀ k ∈ K, k ∈ Subgroup.normalizer (A : Set G) := fun k hk =>
      (Subgroup.zpowers_le).mpr hνA hk
    let := conjActionOn K 𝒢 fun k hk Y hY => map_conj_mem_goodSet (hKN k hk) hY
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hK3 : IsPGroup 3 K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hν3, pow_one])
    have : Finite 𝒢 := (Set.toFinite _).to_subtype
    have hmod := hK3.card_modEq_card_fixedPoints 𝒢
    have hfix : Nat.card (MulAction.fixedPoints K 𝒢) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨Y, hY⟩
      have hYν := hY ⟨ν, Subgroup.mem_zpowers ν⟩
      have hYν' : (Y : Subgroup G).map (MulAut.conj ν).toMonoidHom = Y := congrArg Subtype.val hYν
      obtain ⟨hYA, hY3, y, hy, hYy⟩ := Y.2
      exact hνA' (h.mem_of_normalizer_of_orderOf_three habel hA hYA hY3 hy hYy hν3
        (mem_normalizer_of_map_conj_eq hYν'))
    rw [hfix] at hmod
    rw [← Nat.card_coe_set_eq]
    exact (Nat.modEq_zero_iff_dvd.mp hmod)
  have h𝒢4 : 4 ∣ (𝒢 \ 𝒞).ncard := by
    have hS : ∀ k ∈ T, ∀ Y ∈ 𝒢 \ 𝒞, Y.map (MulAut.conj k).toMonoidHom ∈ 𝒢 \ 𝒞 := by
      intro k hk Y hY
      refine ⟨map_conj_mem_goodSet (hTN hk) hY.1, fun hk𝒞 => hY.2 ?_⟩
      have hfix : ∀ Z ∈ 𝒞, Z.map (MulAut.conj k⁻¹).toMonoidHom = Z := by
        have hk' : k⁻¹ ∈ T := T.inv_mem hk
        have hcomm : ∀ x, (x = a ∨ x = b ∨ x = a * b) → k⁻¹ * x = x * k⁻¹ := fun x hx =>
          congrArg Subtype.val (hT4.isMulCommutative.is_comm.comm ⟨k⁻¹, hk'⟩
            ⟨x, (hmemT x).mpr (by rcases hx with rfl | rfl | rfl <;> simp)⟩)
        rintro Z (rfl | rfl | rfl)
        · exact map_conj_eq_of_mem_normalizer (mem_normalizer_inf_centralizer (hTN hk')
            (hcomm a (Or.inl rfl)).symm)
        · exact map_conj_eq_of_mem_normalizer (mem_normalizer_inf_centralizer (hTN hk')
            (hcomm b (Or.inr (Or.inl rfl))).symm)
        · exact map_conj_eq_of_mem_normalizer (mem_normalizer_inf_centralizer (hTN hk')
            (hcomm (a * b) (Or.inr (Or.inr rfl))).symm)
      have := hfix _ hk𝒞
      rw [← map_conj_mul, inv_mul_cancel, map_conj_one] at this
      rw [this]
      exact hk𝒞
    let := conjActionOn T (𝒢 \ 𝒞) hS
    have : Finite (𝒢 \ 𝒞 : Set (Subgroup G)) := (Set.toFinite _).to_subtype
    have := card_dvd_of_free (K := T) (X := (𝒢 \ 𝒞 : Set (Subgroup G))) (by
      rintro ⟨k, hk⟩ ⟨Y, hY⟩ hkY
      have hkY' : (Y : Subgroup G).map (MulAut.conj k).toMonoidHom = Y := congrArg Subtype.val hkY
      have hkN := mem_normalizer_of_map_conj_eq hkY'
      obtain ⟨⟨hYA, hY3, y, hy, hYy⟩, hY𝒞⟩ := hY
      apply Subtype.ext
      change k = 1
      rcases (hmemT k).mp hk with rfl | rfl | rfl | rfl
      · exfalso; apply hY𝒞
        rcases h.eq_coord_of_mem_normalizer hT3 hM3 habel hA hab hYA hY3 hy hYy hkN with
          h1 | h1 | h1
        · exact Or.inr (Or.inr h1)
        · exact Or.inl h1
        · rw [hT.mul_mul_a] at h1; exact Or.inr (Or.inl h1)
      · exfalso; apply hY𝒞
        rcases h.eq_coord_of_mem_normalizer hT hM habel hA ha hYA hY3 hy hYy hkN with
          h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
      · exfalso; apply hY𝒞
        rcases h.eq_coord_of_mem_normalizer hT1 hM1 habel hA hb hYA hY3 hy hYy hkN with
          h1 | h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inl h1
        · rw [e4] at h1; exact Or.inr (Or.inr h1)
      · rfl)
    rw [hT4.card_four, Nat.card_coe_set_eq] at this
    exact this
  have hsplit : 𝒢.ncard = 𝒞.ncard + (𝒢 \ 𝒞).ncard := by
    rw [← Set.ncard_union_eq Set.disjoint_sdiff_right, Set.union_sdiff_cancel h𝒞𝒢]
  have hle : 𝒢.ncard ≤ 13 := ncard_goodSet_le hA
  rw [h𝒞card] at hsplit
  have hzero : (𝒢 \ 𝒞).ncard = 0 := by omega
  rw [Set.ncard_eq_zero (Set.toFinite _), Set.sdiff_eq_empty] at hzero
  rcases hzero hX with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

end JankoHyp

end CFSG.Walter.J1
