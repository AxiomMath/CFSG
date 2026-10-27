module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Phi3

variable {K : Type} [Field K]

@[expose] noncomputable def phi3 (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

theorem natDegree_phi3 : (phi3 K).natDegree = 2 := by
  unfold phi3
  compute_degree!

theorem monic_phi3 : (phi3 K).Monic := by
  unfold phi3
  monicity!

theorem X_sub_one_mul_phi3 : (X - 1) * phi3 K = X ^ 3 - 1 := by
  unfold phi3
  ring

theorem phi3_ne_X_sub_one : phi3 K ≠ X - 1 := by
  intro h
  have h1 := congrArg natDegree h
  rw [natDegree_phi3, show (X - 1 : K[X]) = X - C 1 by rw [C_1], natDegree_X_sub_C] at h1
  omega

variable [Finite K]

theorem eq_zero_or_eq_one (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  have : Fintype K := Fintype.ofFinite K
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 by rfl, pow_one] at h

variable [CharP K 2]

theorem phi3_irreducible (hK : Nat.card K = 2) : Irreducible (phi3 K) := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_phi3]; decide)
    fun a ha => ?_
  rw [IsRoot, phi3, eval_add, eval_add, eval_pow, eval_X, eval_one] at ha
  rcases eq_zero_or_eq_one hK a with rfl | rfl
  · norm_num at ha
  · rw [one_pow, CharTwo.add_self_eq_zero, zero_add] at ha
    exact one_ne_zero ha

theorem primaryFactor_cases (hK : Nat.card K = 2) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} (hx : x ^ 3 = 1) {k : K[X]}
    (hk : k ∈ primaryFactors x) : k = X - 1 ∨ k = phi3 K := by
  obtain ⟨hki, hkm, hkd⟩ := mem_primaryFactors.mp hk
  have hdvd : minpoly K x ∣ (X - 1) * phi3 K := by
    rw [X_sub_one_mul_phi3]
    refine minpoly.dvd K x ?_
    rw [map_sub, map_pow, aeval_X, map_one, hx, sub_self]
  rcases hki.prime.dvd_or_dvd (hkd.trans hdvd) with h | h
  · left
    exact eq_of_monic_of_associated hkm monic_X_sub_one
      (hki.associated_of_dvd irreducible_X_sub_one h)
  · right
    exact eq_of_monic_of_associated hkm monic_phi3
      (hki.associated_of_dvd (phi3_irreducible hK) h)

end Phi3

section Factors

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem fix_of_mem_spSupported {x g : StatedSp n K} {O : Set K[X]} (hg : g ∈ spSupported x O)
    {k : K[X]} (hk : Irreducible k) (hkm : k.Monic) (hkO : k ∉ O) {v : Fin n ⊕ Fin n → K}
    (hv : aeval (spEnd x) k v = 0) : spEnd g v = v := by
  by_cases hkp : k ∈ primaryFactors (spEnd x)
  · exact (mem_spSupported.mp hg).2 k hkp hkO v (mem_primaryComponent.mpr hv)
  · have h0 : v ∈ primaryComponent (spEnd x) k := mem_primaryComponent.mpr hv
    rw [primaryComponent_eq_bot_of_not_mem hk hkm hkp, Submodule.mem_bot] at h0
    rw [h0, map_zero]

omit [Finite K] [CharP K 2] in
theorem aeval_X_sub_one_apply (T : Module.End K (Fin n ⊕ Fin n → K)) (v : Fin n ⊕ Fin n → K) :
    aeval T (X - 1 : K[X]) v = T v - v := by
  simp

omit [Finite K] [CharP K 2] in
theorem aeval_phi3_apply (T : Module.End K (Fin n ⊕ Fin n → K)) (v : Fin n ⊕ Fin n → K) :
    aeval T (phi3 K) v = T (T v) + T v + v := by
  simp [phi3, sq]

theorem mem_spSupported_of (hK : Nat.card K = 2) {x g : StatedSp n K} (hx3 : x ^ 3 = 1)
    {O : Set K[X]} (hgx : g * x = x * g)
    (h1 : (X - 1 : K[X]) ∉ O → ∀ v, spEnd x v = v → spEnd g v = v)
    (h2 : phi3 K ∉ O → ∀ v, spEnd x (spEnd x v) + spEnd x v + v = 0 → spEnd g v = v) :
    g ∈ spSupported x O := by
  refine mem_spSupported.mpr ⟨hgx, fun k hk hkO v hv => ?_⟩
  have hT3 : spEnd x ^ 3 = 1 := by rw [← spEnd_pow, hx3, spEnd_one]
  have hv' := mem_primaryComponent.mp hv
  rcases primaryFactor_cases hK hT3 hk with rfl | rfl
  · rw [aeval_X_sub_one_apply, sub_eq_zero] at hv'
    exact h1 hkO v hv'
  · rw [aeval_phi3_apply] at hv'
    exact h2 hkO v hv'

theorem commute_of_mem_spFixedFactor (hK : Nat.card K = 2) {x g g' : StatedSp n K}
    (hx3 : x ^ 3 = 1) {O : Set K[X]} (hO : (X - 1 : K[X]) ∉ O) (hg : g ∈ spFixedFactor x)
    (hg' : g' ∈ spSupported x O) : g * g' = g' * g := by
  set T := spEnd x with hTdef
  have hT3 : ∀ v, T (T (T v)) = v := fun v => by
    rw [hTdef, ← spEnd_mul_apply, ← spEnd_mul_apply, ← pow_three', hx3, spEnd_one_apply]
  have hgT : ∀ w, spEnd g (T w) = T (spEnd g w) := fun w => by
    rw [hTdef, ← spEnd_mul_apply, ← spEnd_mul_apply, (mem_spSupported.mp hg).1]
  have hg'T : ∀ w, spEnd g' (T w) = T (spEnd g' w) := fun w => by
    rw [hTdef, ← spEnd_mul_apply, ← spEnd_mul_apply, (mem_spSupported.mp hg').1]
  have hnot : phi3 K ∉ ({X - 1} : Set K[X]) := fun h => phi3_ne_X_sub_one h
  have h1 : ∀ w, T w = w → spEnd g' w = w := fun w hw =>
    fix_of_mem_spSupported hg' irreducible_X_sub_one monic_X_sub_one hO
      (by rw [aeval_X_sub_one_apply, ← hTdef, hw, sub_self])
  have h2 : ∀ w, T (T w) + T w + w = 0 → spEnd g w = w := fun w hw =>
    fix_of_mem_spSupported hg (phi3_irreducible hK) monic_phi3 hnot
      (by rw [aeval_phi3_apply, ← hTdef, hw])
  refine eq_of_spEnd_eq' fun v => ?_
  have hc2 : ∀ w : Fin n ⊕ Fin n → K, w + w = 0 := add_self_eq_zero_of_charTwo (K := K)
  obtain ⟨a, ha⟩ : ∃ a, a = T v := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = T a := ⟨_, rfl⟩
  have hTb : T b = v := by rw [hb, ha, hT3]
  obtain ⟨w₁, hw₁⟩ : ∃ w, w = b + a + v := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w, w = b + a := ⟨_, rfl⟩
  have hTw₁ : T w₁ = w₁ := by
    rw [hw₁, map_add, map_add, hTb, ← hb, ← ha]
    abel
  have hTw₂ : T w₂ = v + b := by rw [hw₂, map_add, hTb, ← hb]
  have hPw₂ : T (T w₂) + T w₂ + w₂ = 0 := by
    rw [hTw₂, map_add, hTb, ← ha, hw₂]
    calc a + v + (v + b) + (b + a) = (a + a) + ((v + v) + (b + b)) := by abel
      _ = 0 := by rw [hc2, hc2, hc2, add_zero, add_zero]
  have hv : v = w₁ + w₂ := by
    rw [hw₁, hw₂]
    calc v = v + ((b + a) + (b + a)) := by rw [hc2, add_zero]
      _ = b + a + v + (b + a) := by abel
  have hgw₂ : spEnd g w₂ = w₂ := h2 w₂ hPw₂
  have hg'w₁ : spEnd g' w₁ = w₁ := h1 w₁ hTw₁
  have hgg'w₂ : spEnd g (spEnd g' w₂) = spEnd g' w₂ := h2 _ (by
    rw [← hg'T, ← hg'T, ← map_add, ← map_add, hPw₂, map_zero])
  have hg'gw₁ : spEnd g' (spEnd g w₁) = spEnd g w₁ := h1 _ (by rw [← hgT, hTw₁])
  rw [spEnd_mul_apply, spEnd_mul_apply, hv]
  simp only [map_add, hg'w₁, hgw₂, hgg'w₂, hg'gw₁]

end Factors

theorem two_eq_zero_L (K : Type) [Field K] [CharP K 2] {L : Type} [Field L] [Algebra K L] :
    (2 : L) = 0 := by
  rw [← map_ofNat (algebraMap K L) 2, CharTwo.two_eq_zero, map_zero]

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L] [Algebra K L]
  {ζ : L} {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)

namespace SpFrame

omit [Finite K] [CharP K 2] in
theorem tor_fix_iff (hζo : IsPrimitiveRoot ζ 3) (c : Fin F.s → ZMod 3) (d : Fin F.s → L) :
    spEnd (F.tor c) (F.Φ d) = F.Φ d ↔ ∀ i, c i ≠ 0 → d i = 0 := by
  rw [F.tor_acts c, F.Φ.injective.eq_iff]
  constructor
  · intro h i hi
    have h1 := congrFun h i
    rw [torE_apply] at h1
    have hne : ζ ^ (c i).val ≠ 1 := hζo.pow_ne_one_of_pos_of_lt
      (fun h0 => hi ((ZMod.val_eq_zero (c i)).mp h0)) (ZMod.val_lt (c i))
    have h2 : (ζ ^ (c i).val - 1) * d i = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  · intro h
    funext i
    rw [torE_apply]
    by_cases hi : c i = 0
    · rw [hi, ZMod.val_zero, pow_zero, one_mul]
    · rw [h i hi, mul_zero]


omit [Finite K] in
theorem tor_phi3_iff (hζo : IsPrimitiveRoot ζ 3) (c : Fin F.s → ZMod 3) (d : Fin F.s → L) :
    spEnd (F.tor c) (spEnd (F.tor c) (F.Φ d)) + spEnd (F.tor c) (F.Φ d) + F.Φ d = 0 ↔
      ∀ i, c i = 0 → d i = 0 := by
  have h2L : (2 : L) = 0 := two_eq_zero_L K
  rw [F.tor_acts c, F.tor_acts c, ← map_add, ← map_add, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h i hi
    have h1 := congrFun h i
    simp only [Pi.add_apply, torE_apply, hi, ZMod.val_zero, pow_zero, one_mul,
      Pi.zero_apply] at h1
    linear_combination h1 - d i * h2L
  · intro h
    funext i
    simp only [Pi.add_apply, torE_apply, Pi.zero_apply]
    by_cases hi : c i = 0
    · rw [h i hi]
      ring
    · set y := ζ ^ (c i).val with hy
      have hy1 : y ≠ 1 := hζo.pow_ne_one_of_pos_of_lt
        (fun h0 => hi ((ZMod.val_eq_zero (c i)).mp h0)) (ZMod.val_lt (c i))
      have hy3 : (y - 1) * (y * y + y + 1) = 0 := by
        have : y ^ 3 = 1 := by rw [hy, ← pow_mul, mul_comm, pow_mul, hζo.pow_eq_one, one_pow]
        linear_combination this
      have hy0 : y * y + y + 1 = 0 := (mul_eq_zero.mp hy3).resolve_left (sub_ne_zero.mpr hy1)
      linear_combination d i * hy0

theorem tor_mem_spSupported (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (c κ : Fin F.s → ZMod 3) (hκ : ∀ i, c i = 0 → κ i = 0) {O : Set K[X]} (hO : phi3 K ∈ O) :
    F.tor κ ∈ spSupported (F.tor c) O := by
  refine mem_spSupported_of hK (F.tor_pow_three hζo.pow_eq_one c)
    (F.tor_comm hζo.pow_eq_one κ c) (fun _ v hv => ?_) (fun h => absurd hO h)
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  rw [F.tor_fix_iff hζo] at hv ⊢
  intro i hi
  by_cases hc : c i = 0
  · exact absurd (hκ i hc) hi
  · exact hv i hc

theorem tor_mem_spFixedFactor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (c κ : Fin F.s → ZMod 3) (hκ : ∀ i, c i ≠ 0 → κ i = 0) :
    F.tor κ ∈ spFixedFactor (F.tor c) := by
  refine mem_spSupported_of hK (F.tor_pow_three hζo.pow_eq_one c)
    (F.tor_comm hζo.pow_eq_one κ c) (fun h => absurd (Set.mem_singleton _) h) fun _ v hv => ?_
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  rw [F.tor_phi3_iff hζo] at hv
  rw [F.tor_fix_iff hζo]
  intro i hi
  by_cases hc : c i = 0
  · exact hv i hc
  · exact absurd (hκ i hc) hi

omit [Finite K] [CharP K 2] in
theorem swap_fix {i j : Fin F.s} (b : Bool) {d : Fin F.s → L} (hi : d i = 0) (hj : d j = 0) :
    spEnd (F.swap i j b) (F.Φ d) = F.Φ d := by
  rw [F.swap_acts i j b]
  congr 1
  funext l
  by_cases hli : l = i
  · subst hli
    rw [swapL_apply_left, hj, map_zero, hi]
  · by_cases hlj : l = j
    · subst hlj
      rw [swapL_apply_right, hi, map_zero, hj]
    · rw [swapL_apply_of_ne b hli hlj]

theorem swap_mem_spSupported (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (c : Fin F.s → ZMod 3) {i j : Fin F.s} (b : Bool) (hci : c i ≠ 0) (hcj : c j ≠ 0)
    (hrel : c i = sgnZ b (c j)) {O : Set K[X]} (hO : phi3 K ∈ O) :
    F.swap i j b ∈ spSupported (F.tor c) O := by
  refine mem_spSupported_of hK (F.tor_pow_three hζo.pow_eq_one c)
    (F.swap_comm_tor hζo.pow_eq_one b hrel) (fun _ v hv => ?_) (fun h => absurd hO h)
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  rw [F.tor_fix_iff hζo] at hv
  exact F.swap_fix b (hv i hci) (hv j hcj)

theorem swap_mem_spFixedFactor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (c : Fin F.s → ZMod 3) {i j : Fin F.s} (b : Bool) (hci : c i = 0) (hcj : c j = 0) :
    F.swap i j b ∈ spFixedFactor (F.tor c) := by
  have hrel : c i = sgnZ b (c j) := by rw [hci, hcj, sgnZ_zero]
  refine mem_spSupported_of hK (F.tor_pow_three hζo.pow_eq_one c)
    (F.swap_comm_tor hζo.pow_eq_one b hrel) (fun h => absurd (Set.mem_singleton _) h)
    fun _ v hv => ?_
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  rw [F.tor_phi3_iff hζo] at hv
  exact F.swap_fix b (hv i hci) (hv j hcj)

end SpFrame

end Frame

end ChoiceTwo

end CFSG.StandardType
