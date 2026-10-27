module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenZ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem ten_four_relIndex (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {U : Subgroup G}
    (hU : uA V V₁ = U) (D : HatModelU U) {x : G} (hx : x ∈ rconj (centerOf U) g) :
    (centerOf U).relIndex (⁅U, Subgroup.zpowers x⁆ ⊔ centerOf U) ≤ 4 := by
  subst hU
  classical
  have hxT : x ∈ T := S.rconj_wA_le_T hg (rconj_centerOf_le_rconj_wA V V₁ g hx)
  have hxN : x ∈ Subgroup.normalizer (uA V V₁ : Set G) := S.T_le_normalizer_uA hxT
  have hrank := S.ten_four_rank hg D hx hxN
  set R : Submodule (ZMod 2) D.V :=
    LinearMap.range ((D.ρ ⟨x, hxN⟩ : D.V ≃ₗ[ZMod 2] D.V).toLinearMap - LinearMap.id) with hR
  let K : Subgroup ↥(Subgroup.normalizer (uA V V₁ : Set G)) :=
    { carrier := {y | ∀ v : D.V, D.ρ y v - v ∈ R}
      one_mem' := fun v => by simp
      mul_mem' := fun {y z} hy hz v => by
        have e : D.ρ (y * z) v - v = (D.ρ y (D.ρ z v) - D.ρ z v) + (D.ρ z v - v) := by
          rw [map_mul]
          simp
        rw [e]
        exact R.add_mem (hy (D.ρ z v)) (hz v)
      inv_mem' := fun {y} hy v => by
        have e : D.ρ y⁻¹ v - v = -(D.ρ y (D.ρ y⁻¹ v) - D.ρ y⁻¹ v) := by
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          simp
        rw [e]
        exact R.neg_mem (hy (D.ρ y⁻¹ v)) }
  have hxK : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (uA V V₁ : Set G))) ∈ K := fun v =>
    ⟨v, by simp⟩
  have hyK : ∀ y ∈ Subgroup.zpowers x,
      ∃ hy : y ∈ Subgroup.normalizer (uA V V₁ : Set G), (⟨y, hy⟩ :
        ↥(Subgroup.normalizer (uA V V₁ : Set G))) ∈ K := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨zpow_mem hxN j, ?_⟩
    have e : (⟨x ^ j, zpow_mem hxN j⟩ : ↥(Subgroup.normalizer (uA V V₁ : Set G))) =
        ⟨x, hxN⟩ ^ j := Subtype.ext (by simp)
    rw [e]
    exact zpow_mem hxK j
  let N : Subgroup G :=
    { carrier := {a | a ∈ uA V V₁ ∧ D.π a ∈ R}
      one_mem' := ⟨(uA V V₁).one_mem, by rw [HatU.π_one D]; exact R.zero_mem⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨(uA V V₁).mul_mem ha.1 hb.1, by
          rw [D.π_mul a ha.1 b hb.1]
          exact R.add_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha =>
        ⟨(uA V V₁).inv_mem ha.1, by
          rw [HatU.π_inv D ha.1]
          exact R.neg_mem ha.2⟩ }
  have hcomm : ⁅uA V V₁, Subgroup.zpowers x⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    obtain ⟨hyN, hyK⟩ := hyK y hy
    have hyu : y * u⁻¹ * y⁻¹ ∈ uA V V₁ := HatU.conj_mem hyN ((uA V V₁).inv_mem hu)
    have e : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    refine ⟨by rw [e]; exact (uA V V₁).mul_mem hu hyu, ?_⟩
    rw [e, D.π_mul u hu _ hyu]
    have h1 : D.π (y * u⁻¹ * y⁻¹) = D.ρ ⟨y, hyN⟩ (D.π u⁻¹) :=
      (D.ρ_π ⟨y, hyN⟩ u⁻¹ ((uA V V₁).inv_mem hu)).symm
    rw [h1, HatU.π_inv D hu, map_neg]
    have h2 := R.neg_mem (hyK (D.π u))
    convert h2 using 1
    abel
  have hZN : centerOf (uA V V₁) ≤ N := fun z hz =>
    ⟨hz.1, by rw [(HatU.π_eq_zero_iff D hz.1).mpr hz]; exact R.zero_mem⟩
  have hAN : ⁅uA V V₁, Subgroup.zpowers x⁆ ⊔ centerOf (uA V V₁) ≤ N := sup_le hcomm hZN
  have hAU : ⁅uA V V₁, Subgroup.zpowers x⁆ ⊔ centerOf (uA V V₁) ≤ uA V V₁ := fun a ha =>
    (hAN ha).1
  have hhat : D.hat (⁅uA V V₁, Subgroup.zpowers x⁆ ⊔ centerOf (uA V V₁)) ≤ R := by
    intro v hv
    obtain ⟨a, haA, haU, rfl⟩ := (HatU.mem_hat D).mp hv
    exact (hAN haA).2
  have hcard := HatU.card_hat D hAU
  rw [inf_eq_right.mpr le_sup_right] at hcard
  rw [← hcard]
  calc Nat.card (D.hat (⁅uA V V₁, Subgroup.zpowers x⁆ ⊔ centerOf (uA V V₁))) ≤ Nat.card R :=
        Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hhat)
    _ = 2 ^ Module.finrank (ZMod 2) R := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := R), Nat.card_zmod]
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrank
    _ = 4 := by norm_num

end Setting

end L128A

namespace L128P

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizerMod_eq {V₁ X Y U : Subgroup G} (hXY : X ≤ Y) :
    X ⊓ centralizerMod V₁ Y U = centralizerMod V₁ X U := by
  ext x
  simp only [Subgroup.mem_inf, mem_centralizerMod]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hXY h.1, h.2⟩⟩

theorem commutator_eq_bot_centerOf_i128 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    {k : G} (hk : k ∈ oTwoUpper (p128 T L V)) (hkN : k ∉ Subgroup.normalizer (V₁ : Set G))
    (hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁) :
    ⁅L, centerOf (i128 T L V V₁)⁆ = ⊥ := by
  obtain ⟨hZ, -, hKC, hLTN⟩ := sup_le_normalizer_centerOf_i128 h1222 h12213 hs hk hkN hkZ
  set J := centerOf (i128 T L V V₁) with hJdef
  have hJZ : J ≤ zU128 V V₁ := le_sup_left.trans hZ.ge
  have hL₁J : lOne L V₁ ≤ Subgroup.centralizer (J : Set G) :=
    (lOne_le_centralizer_centerOf h1222 h12213 hs hk hkN hkZ).trans (Subgroup.centralizer_le hJZ)
  have hKL : oTwoUpper (p128 T L V) ≤ L := oTwoUpper_p128_le hs.hyp
  have hL₁L : lOne L V₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hKLT : oTwoUpper (p128 T L V) ≤ L ⊔ T := hKL.trans le_sup_left
  have hL₁LT : lOne L V₁ ≤ L ⊔ T := hL₁L.trans le_sup_left
  have hX := L1297.sup_le_of_not_le_normalizer h1222 hs.hyp hs.v1
    (X := oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T) (sup_le_sup_right le_sup_right T)
    (sup_le (sup_le hKLT hL₁LT) le_sup_right)
    (fun hle' => hkN (hle' (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk))))
  set C : Subgroup G := L ⊓ Subgroup.centralizer (J : Set G) with hCdef
  have hKC' : oTwoUpper (p128 T L V) ≤ C := le_inf hKL hKC
  have hL₁C : lOne L V₁ ≤ C := le_inf hL₁L hL₁J
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) := le_sup_right.trans hLTN
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hs.hyp.hyp.normalizes ht,
      normalizer_le_normalizer_centralizer'' J (hTJ ht)⟩
  have hLC : L ≤ C ⊔ T :=
    (le_sup_left.trans hX).trans (sup_le_sup_right (sup_le hKC' hL₁C) T)
  have hCL : (C.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
      normalizer_le_normalizer_centralizer'' J (hLTN (Subgroup.mem_sup_left hl))⟩
  have hCeq : C = L := hs.hyp.hyp.faithful.2.1 C inf_le_left hCL fun x hx =>
    exists_two_pow_mem_of_le_sup hs.hyp.hyp.sylow.1 hTC hLC hx
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hCeq.ge.trans inf_le_right)

end L128P

open L128P

theorem lemma12_8_10_of_four (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h84 : Lemma12_8_4_four) : Lemma12_8_10 := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  have S := setting128A h1222 h12213 hs
  have hUeq := uA_eq h1222 hs
  have hA := hs.almostSpecial h1222 h12213
  have hI := i128_eq_sup h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨-, hTZ⟩ := T_le_normalizer_w128 h1222 h12213 hs
  have hTU : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) := hA.G22_three.2
  rw [hkY _ hTU, hkY _ hTZ, hkY _ hs.v1.2.2]
  have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · have h := S.ten_one hgood
    rw [hUeq] at h
    exact h
  · have h := S.ten_two hgood
    rw [hUeq, ← hI] at h
    exact h
  · intro hlt
    have h := S.ten_three hgood (by rw [hUeq]; exact hlt)
    rw [hUeq, ← hI] at h
    exact h
  · have h := S.ten_four hgood
    simp only [L128A.wA, hUeq] at h
    exact h
  · intro x hx
    obtain ⟨D⟩ := hs.exists_hatModelU h1222 h12213
    exact L128A.Setting.ten_four_relIndex S hgood hUeq D hx
  · intro hle
    have hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁ := fun z hz =>
      hle (mem_rconj.mpr (by rw [show k * (k⁻¹ * z * k) * k⁻¹ = z by group]; exact hz))
    obtain ⟨hZ, hdisj, -, -⟩ := sup_le_normalizer_centerOf_i128 h1222 h12213 hs hk hkN hkZ
    exact ⟨hZ, disjoint_iff.mp hdisj,
      commutator_eq_bot_centerOf_i128 h1222 h12213 hs hk hkN hkZ⟩
  · have h84' : centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (L128A.uA V₂ V₁) =
        pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
      rw [hUeq]
      exact h84 G T L V n hs.hyp V₁ _ hs.v1 (isHzOne_normalizer h12213 hs.hyp hs.v1)
    have h6 := S.ten_six hgood h84'
    rw [hUeq, ← hI] at h6
    obtain ⟨h61, h62, h63, h64, h65, h66⟩ := h6
    have hZT : CFSG.conjugate (zU128 V V₁) k ≤ T := by
      have h := (L128A.Setting.rconj_centerOf_le_rconj_wA V₂ V₁ k).trans
        (S.rconj_wA_le_T hgood)
      rw [hUeq] at h
      exact h
    have hZk : CFSG.conjugate (zU128 V V₁) k ≤ Subgroup.normalizer (V₁ : Set G) :=
      hZT.trans hs.v1.2.2
    refine ⟨?_, ?_, h63, ?_, ?_, h66⟩
    · rw [inf_centralizerMod_eq hZk, inf_centralizerMod_eq hZk]
      exact h61
    · rw [inf_centralizerMod_eq hZk]
      exact h62
    · rw [inf_comm (CFSG.conjugate (zU128 V V₁) k) (zU128 V V₁)]
      exact h64
    · rw [inf_comm (CFSG.conjugate (zU128 V V₁) k) (zU128 V V₁)]
      exact h65

theorem lemma12_8_10_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Lemma12_8_10 :=
  lemma12_8_10_of_four h1222 h12213 (lemma12_8_4_four h1222 h37 h38 h39)

end CFSG.Quasithin.H13
