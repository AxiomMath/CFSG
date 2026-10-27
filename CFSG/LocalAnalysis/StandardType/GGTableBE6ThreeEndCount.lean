module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace E6ThreeEnd

theorem exists_forall_mem_iff_dot {n : ℕ} (X : AddSubgroup (Fin n → ZMod 3))
    (hX : 3 ^ (n - 1) ≤ Nat.card X) :
    ∃ c : Fin n → ZMod 3, ∀ x, x ∈ X ↔ ∑ i, c i * x i = 0 := by
  classical
  by_cases htop : X = ⊤
  · exact ⟨0, fun x => by simp [htop]⟩
  obtain ⟨v, hv⟩ : ∃ v, v ∉ X := by
    by_contra h
    push Not at h
    exact htop (eq_top_iff.2 fun x _ => h x)
  have hsmul : ∀ (t : ZMod 3) {y : Fin n → ZMod 3}, y ∈ X → t • y ∈ X := by
    intro t y hy
    have e : t • y = t.val • y := by
      funext i
      simp [nsmul_eq_mul]
    rw [e]
    exact X.nsmul_mem hy _
  have hsq : ∀ t : ZMod 3, t ≠ 0 → t * t = 1 := by decide
  have hv0 : ∀ t : ZMod 3, t • v ∈ X → t = 0 := by
    intro t ht
    by_contra h0
    apply hv
    have e : v = t • (t • v) := by
      rw [smul_smul, hsq t h0, one_smul]
    rw [e]
    exact hsmul _ ht
  have hn : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact hv (by
      have : v = 0 := funext fun i => i.elim0
      rw [this]
      exact X.zero_mem)
  let F : ZMod 3 × X → (Fin n → ZMod 3) := fun q => q.1 • v + (q.2 : Fin n → ZMod 3)
  have hFinj : Function.Injective F := by
    rintro ⟨k, y⟩ ⟨k', y'⟩ h
    have h' : k • v + (y : Fin n → ZMod 3) = k' • v + (y' : Fin n → ZMod 3) := h
    have h1 : (k - k') • v = (y' : Fin n → ZMod 3) - y := by
      funext i
      have hi := congrFun h' i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi ⊢
      linear_combination hi
    have hk : k = k' := sub_eq_zero.mp (hv0 _ (h1 ▸ X.sub_mem y'.2 y.2))
    subst hk
    have hy : (y : Fin n → ZMod 3) = y' := add_left_cancel h'
    exact Prod.ext rfl (Subtype.ext hy)
  have hcardV : Nat.card (Fin n → ZMod 3) = 3 ^ n := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hle : Nat.card (Fin n → ZMod 3) ≤ Nat.card (ZMod 3 × X) := by
    rw [hcardV, Nat.card_prod, Nat.card_zmod]
    calc 3 ^ n = 3 * 3 ^ (n - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 3 * Nat.card X := Nat.mul_le_mul_left _ hX
  have hFsurj : Function.Surjective F :=
    ((Nat.bijective_iff_injective_and_card F).mpr
      ⟨hFinj, le_antisymm (Nat.card_le_card_of_injective F hFinj) hle⟩).2
  have hcov : ∀ x, ∃ k : ZMod 3, x - k • v ∈ X := by
    intro x
    obtain ⟨⟨k, y⟩, hky⟩ := hFsurj x
    refine ⟨k, ?_⟩
    have e : x - k • v = y := by
      rw [← hky]
      exact add_sub_cancel_left _ _
    rw [e]
    exact y.2
  choose kf hkf using hcov
  refine ⟨fun i => kf (Pi.single i 1), fun x => ?_⟩
  have hsum : x - (∑ i, kf (Pi.single i 1) * x i) • v ∈ X := by
    have e : x - (∑ i, kf (Pi.single i 1) * x i) • v =
        ∑ i, x i • (Pi.single i 1 - kf (Pi.single i 1) • v) := by
      funext j
      have e1 : ∀ i, (x i • (Pi.single i 1 - kf (Pi.single i 1) • v) : Fin n → ZMod 3) j =
          x i * (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) j - x i * kf (Pi.single i 1) * v j := by
        intro i
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      have e2 : ∑ i, x i * (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) j = x j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · intro h
          exact absurd (Finset.mem_univ j) h
      have e3 : ∑ i, (x i * (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) j -
            x i * kf (Pi.single i 1) * v j) =
          ∑ i, x i * (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) j -
            ∑ i, x i * kf (Pi.single i 1) * v j :=
        Finset.sum_sub_distrib (fun i => x i * (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) j)
          (fun i => x i * kf (Pi.single i 1) * v j)
      have e4 : (x - (∑ i, kf (Pi.single i 1) * x i) • v) j =
          x j - (∑ i, kf (Pi.single i 1) * x i) * v j := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e5 : (∑ i, kf (Pi.single i 1) * x i) * v j = ∑ i, x i * kf (Pi.single i 1) * v j :=
        (Finset.sum_mul Finset.univ (fun i => kf (Pi.single i 1) * x i) (v j)).trans
          (Finset.sum_congr rfl fun i _ => by ring)
      rw [Finset.sum_apply, Finset.sum_congr rfl fun i _ => e1 i, e3, e2, e4, e5]
    rw [e]
    exact X.sum_mem fun i _ => hsmul _ (hkf _)
  constructor
  · intro hx
    have h1 : (∑ i, kf (Pi.single i 1) * x i) • v ∈ X :=
      sub_sub_cancel x ((∑ i, kf (Pi.single i 1) * x i) • v) ▸ X.sub_mem hx hsum
    exact hv0 _ h1
  · intro h0
    have h0' : ∑ i, kf (Pi.single i 1) * x i = 0 := h0
    have e : x - (∑ i, kf (Pi.single i 1) * x i) • v = x := by
      rw [h0']
      exact sub_eq_self.mpr (zero_smul _ v)
    exact e ▸ hsum

open TableBExc.Three TableBExc.E6Three

local instance e6ThreeEndFactThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

local instance e6ThreeEndNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def nfVec (v : Fin 3 → ZMod 3) : List (Fin Tag.E6.rank) :=
  nfWordE6 (v 0).val (v 1).val (v 2).val

theorem card_fixAll_cd1 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![wordE6C, nfWordE6 1 1 1] t) x = x} ≤ 3 ^ (6 - 4) :=
  card_fixAll_adWord_le (τ := .E6) _ ![(0, 0), (0, 1), (0, 2), (1, 0)] ![0, 1, 2, 4]
    (by decide) ![![1, 2, 1, 0], ![1, 2, 2, 2], ![1, 2, 1, 2], ![1, 0, 2, 2]] (by decide +kernel)

theorem card_fixAll_cd2 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![wordE6C, nfWordE6 2 2 2] t) x = x} ≤ 3 ^ (6 - 4) :=
  card_fixAll_adWord_le (τ := .E6) _ ![(0, 0), (0, 1), (0, 2), (1, 0)] ![0, 1, 2, 4]
    (by decide) ![![1, 2, 1, 0], ![1, 2, 2, 1], ![1, 2, 1, 1], ![1, 0, 2, 1]] (by decide +kernel)

theorem card_fixAll_N :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ t, adWord .E6 3 (wordE6G t) x = x} ≤
      3 ^ (6 - 5) :=
  card_fixAll_adWord_le (τ := .E6) _ ![(0, 0), (0, 3), (1, 3), (1, 4), (2, 3)] ![0, 1, 2, 4, 5]
    (by decide) ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0],
      ![0, 0, 1, 1, 0]] (by decide +kernel)

@[expose] def pairY : Fin 13 → Fin 3 → ZMod 3 :=
  ![![0, 1, 0], ![0, 0, 1], ![0, 2, 1], ![0, 1, 1], ![0, 0, 1], ![0, 1, 0], ![0, 1, 0],
    ![0, 0, 1], ![0, 2, 1], ![0, 1, 1], ![0, 0, 1], ![0, 1, 1], ![1, 0, 1]]

@[expose] def pairZ : Fin 13 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![0, 1, 0], ![2, 0, 1], ![1, 0, 1],
    ![1, 2, 0], ![1, 2, 0], ![1, 2, 0], ![1, 1, 0], ![1, 1, 0], ![1, 1, 0]]

theorem exists_pair_aux : ∀ c₀ c₁ c₂ : ZMod 3, ∃ k : Fin 13,
    c₀ * pairY k 0 + c₁ * pairY k 1 + c₂ * pairY k 2 = 0 ∧
      c₀ * pairZ k 0 + c₁ * pairZ k 1 + c₂ * pairZ k 2 = 0 := by
  decide +kernel

theorem exists_pair (c : Fin 3 → ZMod 3) :
    ∃ k : Fin 13, ∑ i, c i * pairY k i = 0 ∧ ∑ i, c i * pairZ k i = 0 := by
  obtain ⟨k, hk⟩ := exists_pair_aux (c 0) (c 1) (c 2)
  exact ⟨k, by simpa [Fin.sum_univ_three] using hk⟩

theorem card_fixAll_pair (k : Fin 13) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![nfVec (pairY k), nfVec (pairZ k)] t) x = x} ≤ 3 ^ (6 - 4) := by
  fin_cases k
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 3), (0, 4), (1, 0), (1, 3)] ![0, 2, 4, 5]
      (by decide) ![![0, 0, 1, 1], ![0, 0, 0, 1], ![1, 0, 0, 0], ![1, 1, 0, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 0), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![0, 0, 1, 1], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![2, 0, 1, 1], ![0, 1, 2, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![2, 0, 2, 1], ![0, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 3), (1, 4)] ![0, 1, 4, 5]
      (by decide) ![![2, 0, 0, 2], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 3), (0, 4), (1, 0), (1, 3)] ![0, 1, 4, 5]
      (by decide) ![![0, 0, 2, 0], ![0, 0, 1, 1], ![1, 0, 0, 0], ![1, 1, 0, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 3), (0, 4), (1, 0), (1, 3)] ![0, 1, 4, 5]
      (by decide) ![![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![1, 1, 0, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 0), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![2, 0, 0, 1], ![0, 1, 0, 0], ![2, 0, 2, 1], ![1, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![2, 0, 0, 1], ![0, 1, 2, 0], ![0, 0, 2, 1], ![0, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![2, 0, 0, 1], ![0, 1, 1, 0], ![0, 0, 1, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 0), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![2, 0, 0, 1], ![0, 1, 0, 0], ![2, 0, 2, 1], ![1, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![2, 0, 0, 1], ![0, 1, 1, 0], ![0, 0, 1, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 0), (0, 1), (0, 3), (1, 3)] ![0, 1, 2, 4]
      (by decide) ![![0, 2, 0, 1], ![1, 1, 1, 2], ![2, 2, 0, 1], ![1, 1, 0, 0]] (by decide +kernel)

theorem fixAllCard_le_two {A : Subgroup (Model piE7 piE7_pow_three)}
    {y z : Model piE7 piE7_pow_three} (hy : y ∈ A) (hz : z ∈ A) {ωy ωz : List (Fin Tag.E6.rank)}
    (hωy : modelHomE6 y = (coxeterSystem .E6).wordProd ωy)
    (hωz : modelHomE6 z = (coxeterSystem .E6).wordProd ωz) :
    fixAllCard (adPerm .E6 3) modelHomE6 A ≤
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ t, adWord .E6 3 (![ωy, ωz] t) x = x} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1, fun t => ?_⟩)
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  have h0 := x.2 y hy
  have h1 := x.2 z hz
  rw [adPerm_apply, hωy, ← adWord_eq_adAct] at h0
  rw [adPerm_apply, hωz, ← adWord_eq_adAct] at h1
  fin_cases t
  · exact h0
  · exact h1

theorem modelHomE6_inl_single (i : Fin 3) :
    modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) = gE6 i := by
  rw [modelHomE6, modelHom_inl, modelN_single, ZMod.val_one, pow_one]

theorem modelHomE6_inl_single_word (i : Fin 3) :
    modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) =
      (coxeterSystem .E6).wordProd (wordE6G i) :=
  (modelHomE6_inl_single i).trans rfl

theorem zpowers_inl_single_two (i : Fin 3) :
    Subgroup.zpowers (SemidirectProduct.inl (.ofAdd (Pi.single i 2)) :
      Model piE7 piE7_pow_three) =
      Subgroup.zpowers (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) := by
  set g : Model piE7 piE7_pow_three := SemidirectProduct.inl (.ofAdd (Pi.single i 1)) with hg
  have e2 : (SemidirectProduct.inl (.ofAdd (Pi.single i 2)) : Model piE7 piE7_pow_three) =
      g ^ 2 := by
    rw [hg, ← map_pow]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_single]
    rfl
  have hg3 : g ^ 3 = 1 := by
    rw [hg, ← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]
  rw [e2]
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact pow_mem (Subgroup.mem_zpowers g) 2
  · rw [Subgroup.zpowers_le]
    have h4 : (g ^ 2) ^ 2 = g := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hg3, one_mul]
    have h5 := pow_mem (Subgroup.mem_zpowers (g ^ 2)) 2
    rwa [h4] at h5

theorem exists_conj_c (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : v * shiftAut piE7 v * (shiftAut piE7 ^ 2) v = 1) :
    ∃ w, w * v * (shiftAut piE7 w)⁻¹ = 1 := by
  refine ⟨.ofAdd ![0, -(v.toAdd 1), v.toAdd 0], ?_⟩
  rw [eq_ofAdd_vec3 v] at hv
  have hw := conj_vec3_E7 _ _ _ hv
  rw [← eq_ofAdd_vec3 v] at hw
  exact hw

theorem eq_const_of_shiftAut : ∀ a b c : ZMod 3,
    shiftAut piE7 (.ofAdd ![a, b, c]) = (.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3)) →
      b = a ∧ c = a := by
  decide +kernel

theorem refined_model_outside {A : Subgroup (Model piE7 piE7_pow_three)}
    (hA3 : ∀ y ∈ A, y ^ 3 = 1) (hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    {y : Model piE7 piE7_pow_three} (hyA : y ∈ A) (hy1 : y.right ≠ 1) :
    Nat.card A * fixAllCard (adPerm .E6 3) modelHomE6 A < 3 ^ 5 := by
  have := finite_model (π := piE7) (hπ := piE7_pow_three)
  obtain ⟨y₁, hy₁A, hy₁⟩ := exists_right_eq_ofAdd_one hyA hy1
  have he : y₁ = ⟨y₁.left, .ofAdd 1⟩ := SemidirectProduct.ext rfl hy₁
  have hv3 : y₁.left * shiftAut piE7 y₁.left * (shiftAut piE7 ^ 2) y₁.left = 1 := by
    rw [← left_cube (hπ := piE7_pow_three), ← he, hA3 y₁ hy₁A, SemidirectProduct.one_left]
  obtain ⟨w, hwv⟩ := exists_conj_c y₁.left hv3
  set A' := A.map (MulAut.conj (SemidirectProduct.inl w : Model piE7 piE7_pow_three)).toMonoidHom
    with hA'
  have hfixA : fixAllCard (adPerm .E6 3) modelHomE6 A' =
      fixAllCard (adPerm .E6 3) modelHomE6 A :=
    fixAllCard_map_conj (adPerm .E6 3) modelHomE6 A _
  have hc₀ : (⟨1, .ofAdd 1⟩ : Model piE7 piE7_pow_three) ∈ A' := by
    refine ⟨y₁, hy₁A, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, he, inl_conj_eq, hwv]
  have hcardA : Nat.card A ≤ 3 * 3 := card_le_of_right_eq hAc hy₁A hy₁ card_fixShift_E7
  have hfixc : fixCard (adPerm .E6 3) modelHomE6 ⟨1, .ofAdd 1⟩ ≤ 3 ^ 3 := by
    rw [fixCard_adPerm_eq _ _ _ modelHomE6_c]
    exact card_fix_adWordE6C
  have hfixA' : fixAllCard (adPerm .E6 3) modelHomE6 A' ≤ 3 ^ 3 :=
    (fixAllCard_le (adPerm .E6 3) modelHomE6 hc₀).trans hfixc
  rw [← hfixA]
  by_cases h3 : Nat.card A ≤ 3
  · calc Nat.card A * fixAllCard (adPerm .E6 3) modelHomE6 A' ≤ 3 * 3 ^ 3 :=
          Nat.mul_le_mul h3 hfixA'
      _ < 3 ^ 5 := by norm_num
  set r : A →* Multiplicative (ZMod 3) := SemidirectProduct.rightHom.comp A.subtype with hr
  have h1 := TableB.card_range_mul_card_ker r
  have h2 : Nat.card r.range ≤ 3 := by
    calc Nat.card r.range ≤ Nat.card (Multiplicative (ZMod 3)) := Subgroup.card_le_card_group _
      _ = 3 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hker : r.ker ≠ ⊥ := by
    intro hbot
    apply h3
    rw [← h1, hbot, Subgroup.card_bot, mul_one]
    exact h2
  obtain ⟨⟨⟨z, hzA⟩, hzk⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hker
  have hzr : z.right = 1 := hzk
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzs : shiftAut piE7 z.left = z.left := by
    apply shiftAut_eq_of_comm (v := y₁.left)
    have e1 : z = ⟨z.left, 1⟩ := SemidirectProduct.ext rfl hzr
    rw [← e1, ← he]
    exact hAc _ hzA _ hy₁A
  rw [eq_ofAdd_vec3 z.left] at hzs
  obtain ⟨hb, hc⟩ := eq_const_of_shiftAut _ _ _ hzs
  have hzl : z.left = .ofAdd ![z.left.toAdd 0, z.left.toAdd 0, z.left.toAdd 0] := by
    conv_lhs => rw [eq_ofAdd_vec3 z.left]
    rw [hb, hc]
  have ha0 : z.left.toAdd 0 ≠ 0 := by
    intro h0
    apply hz1'
    refine SemidirectProduct.ext ?_ hzr
    rw [hzl, h0, SemidirectProduct.one_left]
    decide
  have hzA' : z ∈ A' := by
    refine ⟨z, hzA, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e1 : z = SemidirectProduct.inl z.left := eq_inl_of_right_eq_one hzr
    rw [e1, ← map_inv, ← map_mul, ← map_mul, mul_comm w, mul_inv_cancel_right]
  have hfixA'' : fixAllCard (adPerm .E6 3) modelHomE6 A' ≤ 3 ^ (6 - 4) := by
    have h12 : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
    rcases h12 _ ha0 with h | h
    · refine (fixAllCard_le_two (ωz := nfWordE6 1 1 1) hc₀ hzA' modelHomE6_c ?_).trans
        card_fixAll_cd1
      rw [eq_inl_of_right_eq_one hzr, hzl, h, modelHomE6_inl]
      rfl
    · refine (fixAllCard_le_two (ωz := nfWordE6 2 2 2) hc₀ hzA' modelHomE6_c ?_).trans
        card_fixAll_cd2
      rw [eq_inl_of_right_eq_one hzr, hzl, h, modelHomE6_inl]
      rfl
  calc Nat.card A * fixAllCard (adPerm .E6 3) modelHomE6 A' ≤ (3 * 3) * 3 ^ (6 - 4) :=
        Nat.mul_le_mul hcardA hfixA''
    _ < 3 ^ 5 := by norm_num

@[expose] def expSub (A : Subgroup (Model piE7 piE7_pow_three)) : AddSubgroup (Fin 3 → ZMod 3) where
  carrier := {v | SemidirectProduct.inl (.ofAdd v) ∈ A}
  add_mem' := fun {u v} hu hv => by
    change SemidirectProduct.inl (.ofAdd (u + v)) ∈ A
    rw [ofAdd_add, map_mul]
    exact mul_mem hu hv
  zero_mem' := by
    change SemidirectProduct.inl (.ofAdd 0) ∈ A
    rw [ofAdd_zero, map_one]
    exact one_mem A
  neg_mem' := fun {v} hv => by
    have e : (SemidirectProduct.inl (.ofAdd (-v)) : Model piE7 piE7_pow_three) =
        (SemidirectProduct.inl (.ofAdd v))⁻¹ := by
      rw [← map_inv]
      rfl
    change SemidirectProduct.inl (.ofAdd (-v)) ∈ A
    rw [e]
    exact inv_mem hv

theorem mem_expSub {A : Subgroup (Model piE7 piE7_pow_three)} {v : Fin 3 → ZMod 3} :
    v ∈ expSub A ↔ SemidirectProduct.inl (.ofAdd v) ∈ A :=
  Iff.rfl

theorem card_expSub {A : Subgroup (Model piE7 piE7_pow_three)}
    (hI : ∀ y ∈ A, y.right = 1) : Nat.card (expSub A) = Nat.card A := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun v => (⟨SemidirectProduct.inl (.ofAdd v.1), v.2⟩ : A)) ⟨?_, ?_⟩)
  · intro u v huv
    apply Subtype.ext
    exact Multiplicative.ofAdd.injective
      (SemidirectProduct.inl_injective (congrArg Subtype.val huv))
  · rintro ⟨y, hy⟩
    have hyl : y = SemidirectProduct.inl y.left := eq_inl_of_right_eq_one (hI y hy)
    refine ⟨⟨Multiplicative.toAdd y.left, ?_⟩, ?_⟩
    · rw [mem_expSub, ofAdd_toAdd, ← hyl]
      exact hy
    · apply Subtype.ext
      change SemidirectProduct.inl (.ofAdd (Multiplicative.toAdd y.left)) = y
      rw [ofAdd_toAdd, ← hyl]

theorem refined_model {A : Subgroup (Model piE7 piE7_pow_three)} (hA3 : ∀ y ∈ A, y ^ 3 = 1)
    (hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : A ≠ ⊥) :
    Nat.card A * fixAllCard (adPerm .E6 3) modelHomE6 A < 3 ^ 5 ∨
      ∃ i, A = Subgroup.zpowers (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) := by
  classical
  have := finite_model (π := piE7) (hπ := piE7_pow_three)
  by_cases hI : ∃ y ∈ A, y.right ≠ 1
  · obtain ⟨y, hyA, hy1⟩ := hI
    exact Or.inl (refined_model_outside hA3 hAc hyA hy1)
  push Not at hI
  have hAN : A ≤ (SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 3) →*
      Model piE7 piE7_pow_three).range :=
    fun y hy => ⟨y.left, (eq_inl_of_right_eq_one (hI y hy)).symm⟩
  have hdvd : Nat.card A ∣ 3 ^ 3 :=
    card_range_inl (π := piE7) (hπ := piE7_pow_three) ▸ Subgroup.card_dvd_of_le hAN
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk3 : k = 3 ∨ k = 2 ∨ k ≤ 1 := by omega
  rcases hk3 with rfl | rfl | hk1
  ·
    left
    have hAeq : A = (SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 3) →*
        Model piE7 piE7_pow_three).range :=
      Subgroup.eq_of_le_of_card_ge hAN (by rw [card_range_inl, hk'])
    have hfix : fixAllCard (adPerm .E6 3) modelHomE6 A ≤ 3 ^ (6 - 5) := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x => (⟨x.1, fun t => ?_⟩ : {x : Fin Tag.E6.rank → ZMod 3 //
          ∀ t, adWord .E6 3 (wordE6G t) x = x}))
        fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) card_fixAll_N
      have hmem : SemidirectProduct.inl (.ofAdd (Pi.single t 1)) ∈ A := by
        rw [hAeq]
        exact ⟨_, rfl⟩
      have h0 := x.2 _ hmem
      rw [adPerm_apply, modelHomE6_inl_single_word, ← adWord_eq_adAct] at h0
      exact h0
    calc Nat.card A * fixAllCard (adPerm .E6 3) modelHomE6 A ≤ 3 ^ 3 * 3 ^ (6 - 5) :=
          Nat.mul_le_mul hk'.le hfix
      _ < 3 ^ 5 := by norm_num
  ·
    left
    obtain ⟨c, hc⟩ := exists_forall_mem_iff_dot (expSub A)
      (le_of_eq (by rw [card_expSub hI, hk']))
    obtain ⟨j, hj1, hj2⟩ := exists_pair c
    have hyA : SemidirectProduct.inl (.ofAdd (pairY j)) ∈ A := (hc (pairY j)).mpr hj1
    have hzA : SemidirectProduct.inl (.ofAdd (pairZ j)) ∈ A := (hc (pairZ j)).mpr hj2
    have hfix : fixAllCard (adPerm .E6 3) modelHomE6 A ≤ 3 ^ (6 - 4) :=
      (fixAllCard_le_two (ωy := nfVec (pairY j)) (ωz := nfVec (pairZ j)) hyA hzA
        (modelHomE6_inl _) (modelHomE6_inl _)).trans (card_fixAll_pair j)
    calc Nat.card A * fixAllCard (adPerm .E6 3) modelHomE6 A ≤ 3 ^ 2 * 3 ^ (6 - 4) :=
          Nat.mul_le_mul hk'.le hfix
      _ < 3 ^ 5 := by norm_num
  ·
    have hA3' : Nat.card A ≤ 3 := by
      rw [hk']
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := pow_one 3
    obtain ⟨⟨y, hyA⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyo : orderOf y = 3 := orderOf_eq_prime (hA3 y hyA) hy1'
    have hAy : A = Subgroup.zpowers y := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyA) ?_).symm
      rw [Nat.card_zpowers, hyo]
      exact hA3'
    have hyl : y = SemidirectProduct.inl y.left := eq_inl_of_right_eq_one (hI y hyA)
    by_cases hsupp : 2 ≤ (supp y.left).card
    · left
      have hfix : fixAllCard (adPerm .E6 3) modelHomE6 A ≤ 3 ^ 3 := by
        refine (fixAllCard_le (adPerm .E6 3) modelHomE6 hyA).trans ?_
        rw [hyl]
        exact fix_supp_E6 _ hsupp
      calc Nat.card A * fixAllCard (adPerm .E6 3) modelHomE6 A ≤ 3 * 3 ^ 3 :=
            Nat.mul_le_mul hA3' hfix
        _ < 3 ^ 5 := by norm_num
    · right
      have hyl1 : y.left ≠ 1 := fun h => hy1' (by rw [hyl, h, map_one])
      obtain ⟨i, hi⟩ : ∃ i, y.left.toAdd i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hyl1 (Multiplicative.toAdd.injective (funext hcon))
      have hsupp1 : supp y.left = {i} :=
        (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (mem_supp.mpr hi))
          (by rw [Finset.card_singleton]; omega)).symm
      refine ⟨i, ?_⟩
      rw [hAy, hyl, eq_single_of_supp hsupp1]
      have h12 : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
      rcases h12 _ hi with h | h
      · rw [h]
      · rw [h, zpowers_inl_single_two]

theorem refined_E6 (A : Subgroup (WeylGroup .E6)) (hAS : A ≤ modelHomE6.range)
    (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x} <
        3 ^ 5 ∨
      ∃ i, A = Subgroup.zpowers (gE6 i) := by
  have hmap : (A.comap modelHomE6).map modelHomE6 = A := Subgroup.map_comap_eq_self hAS
  have hcard : Nat.card (A.comap modelHomE6) = Nat.card A := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective modelHomE6_injective).symm
  have hfix : fixAllCard (adPerm .E6 3) modelHomE6 (A.comap modelHomE6) =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro h a ha
      obtain ⟨y, rfl⟩ := hAS ha
      exact h y ha
    · intro h y hy
      exact h (modelHomE6 y) hy
  have hA'1 : A.comap modelHomE6 ≠ ⊥ := fun hbot => hA1 (by rw [← hmap, hbot, Subgroup.map_bot])
  rcases refined_model (A := A.comap modelHomE6)
      (fun y hy => modelHomE6_injective (by rw [map_pow, map_one]; exact hA.2 _ hy))
      (fun y hy z hz => modelHomE6_injective (by
        rw [map_mul, map_mul]; exact TableB.IsElemAbelian.comm hA hy hz)) hA'1 with h | ⟨i, hi⟩
  · left
    rw [← hcard, ← hfix]
    exact h
  · right
    refine ⟨i, ?_⟩
    rw [← hmap, hi, MonoidHom.map_zpowers, modelHomE6_inl_single]

end E6ThreeEnd

end CFSG.StandardType
