module

public import CFSG.Quasithin.Background.E1Sec6
public import CFSG.Quasithin.Background.E1Sec7Two

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

universe u

section Step

variable {G : Type*} [Group G] [Finite G]

theorem ten_eight_step {r : ℕ} {T A Y₁ J₁ : Subgroup G} [Y₁.Normal] (hT : IsSylowIn 2 T ⊤)
    (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    (hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆) (hr : r.Prime)
    (hY₁ : IsPGroup r Y₁) (hY₁ab : ∀ a ∈ Y₁, ∀ b ∈ Y₁, a * b = b * a)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ Y₁ → K ≠ ⊥ → K = Y₁) (hTJ : T ≤ J₁)
    (hJY : J₁ ⊔ Y₁ = ⊤) (hE : ⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K ≤ J₁) :
    Y₁ ≤ J₁ := by
  have hnormY : ∀ g : G, g ∈ Subgroup.normalizer (Y₁ : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  by_cases hr2 : r = 2
  · subst hr2
    have : Fact (Nat.Prime 2) := ⟨hr⟩
    exact (hT.le_of_normal le_top inferInstance hY₁).trans hTJ
  have : Fact r.Prime := ⟨hr⟩
  have hcommY : ⁅Y₁, A⁆ ≤ Y₁ := Subgroup.commutator_le.mpr fun n hn a ha => by
    have e : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Y₁.mul_mem hn (Subgroup.Normal.conj_mem inferInstance n⁻¹ (Y₁.inv_mem hn) a)
  have hYA : ⁅Y₁, A⁆ ≤ J₁ := by
    refine (comm_le_iSup_twoResidual hr hr2 hT hA hAab hY₁).trans ?_
    refine iSup₂_le fun K hK => (twoResidual_le K).trans ?_
    exact (le_iSup₂_of_le K hK.1 le_rfl).trans hE
  by_cases hYA0 : ⁅Y₁, A⁆ = ⊥
  ·
    set P := perfectCore (⊤ : Subgroup G) with hP
    have hAc : A ≤ Subgroup.centralizer (Y₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact hYA0)
    have hCnorm : ∀ g c : G, c ∈ Subgroup.centralizer (Y₁ : Set G) →
        g * c * g⁻¹ ∈ Subgroup.centralizer (Y₁ : Set G) := by
      intro g c hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro y hy
      have hy' : g⁻¹ * y * g ∈ Y₁ := by
        have := Subgroup.Normal.conj_mem inferInstance y hy g⁻¹
        simpa using this
      have h1 := hc _ hy'
      calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = (g * c * g⁻¹) * y := by group
    have hPC : P ≤ Subgroup.centralizer (Y₁ : Set G) := by
      calc P = ⁅P, A⁆ := hcomm
        _ ≤ Subgroup.centralizer (Y₁ : Set G) := by
          refine Subgroup.commutator_le.mpr fun p hp a ha => ?_
          have e : ⁅p, a⁆ = (p * a * p⁻¹) * a⁻¹ := rfl
          rw [e]
          exact Subgroup.mul_mem _ (hCnorm p a (hAc ha)) (Subgroup.inv_mem _ (hAc ha))
    have hY₁P : Y₁ ≤ P := by
      intro y hy
      obtain ⟨k, hk⟩ := hY₁ ⟨y, hy⟩
      have hyk : y ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup G) y (Subgroup.mem_top y)
      rw [← hres]
      exact mem_of_pow_mem_two_p hr hr2 (by rw [hyk]; exact Subgroup.one_mem _) hj
    set P₁ := perfectCore J₁ with hP₁
    have hP₁P : P₁ ≤ P := perfectCore_mono le_top
    have hπ : (⊤ : Subgroup G).map (QuotientGroup.mk' Y₁) = J₁.map (QuotientGroup.mk' Y₁) := by
      have h1 : (J₁ ⊔ Y₁).map (QuotientGroup.mk' Y₁) = J₁.map (QuotientGroup.mk' Y₁) := by
        rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff Y₁).mpr (QuotientGroup.ker_mk' Y₁).ge,
          sup_bot_eq]
      rw [← h1, hJY]
    have hPle : P ≤ P₁ ⊔ Y₁ := by
      have h1 : P.map (QuotientGroup.mk' Y₁) = P₁.map (QuotientGroup.mk' Y₁) := by
        rw [hP, hP₁, map_perfectCore, map_perfectCore, hπ]
      calc P ≤ (P.map (QuotientGroup.mk' Y₁)).comap (QuotientGroup.mk' Y₁) :=
            Subgroup.le_comap_map _ _
        _ = (P₁.map (QuotientGroup.mk' Y₁)).comap (QuotientGroup.mk' Y₁) := by rw [h1]
        _ = P₁ ⊔ Y₁ := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    have hYP₁ : Y₁ ≤ Subgroup.normalizer (P₁ : Set G) := by
      intro y hy
      apply mem_normalizer_of_conj_mem
      intro p hp
      have h1 : y * p = p * y := Subgroup.mem_centralizer_iff.mp (hPC (hP₁P hp)) y hy
      have e : y * p * y⁻¹ = p := by
        calc y * p * y⁻¹ = (p * y) * y⁻¹ := by rw [h1]
          _ = p := by group
      rw [e]
      exact hp
    have hUnorm : P₁ ⊔ Y₁ ≤ Subgroup.normalizer (P₁ : Set G) :=
      sup_le Subgroup.le_normalizer hYP₁
    have hP₁U : (P₁.subgroupOf (P₁ ⊔ Y₁)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hUnorm
    have hY₁solv : Group.IsSolvable Y₁ := by
      have : IsMulCommutative ↥Y₁ := ⟨⟨fun a b => Subtype.ext (hY₁ab a a.2 b b.2)⟩⟩
      infer_instance
    have hperfU : P ≤ perfectCore (P₁ ⊔ Y₁) :=
      le_perfectCore_of_perfect hPle (perfectCore_perfect ⊤)
    have hPP₁ : P ≤ P₁ :=
      hperfU.trans (perfectCore_le_of_sup_solvable le_sup_left hP₁U rfl hY₁solv)
    exact (hY₁P.trans hPP₁).trans (perfectCore_le J₁)
  ·
    set N := Subgroup.normalClosure ((⁅Y₁, A⁆ : Subgroup G) : Set G) with hN
    have hNY : N ≤ Y₁ := Subgroup.normalClosure_le_normal hcommY
    have hNne : N ≠ ⊥ := fun h => hYA0 (le_bot_iff.mp (Subgroup.le_normalClosure.trans h.le))
    have hNeq : N = Y₁ := hmin N inferInstance hNY hNne
    have hNJ : N ≤ J₁ := by
      rw [hN, Subgroup.normalClosure, Subgroup.closure_le]
      intro g hg
      obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have hcmem : c ∈ (↑(J₁ ⊔ Y₁) : Set G) := by
        rw [hJY]
        exact Subgroup.mem_top c
      rw [Subgroup.coe_mul_of_left_le_normalizer_right J₁ Y₁ (fun x _ => hnormY x)] at hcmem
      obtain ⟨j, hj, y, hy, hjy⟩ := hcmem
      have hzY : z ∈ Y₁ := hcommY hz
      have e : g = j * z * j⁻¹ := by
        rw [← hc, ← hjy]
        have hyz : y * z = z * y := hY₁ab y hy z hzY
        calc j * y * z * (j * y)⁻¹ = j * (y * z) * y⁻¹ * j⁻¹ := by group
          _ = j * (z * y) * y⁻¹ * j⁻¹ := by rw [hyz]
          _ = j * z * j⁻¹ := by group
      rw [e]
      exact J₁.mul_mem (J₁.mul_mem hj (hYA hz)) (J₁.inv_mem hj)
    rw [← hNeq]
    exact hNJ

end Step

theorem ten_eight_aux : ∀ (n : ℕ) (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ {T A Y J : Subgroup G} [Y.Normal], IsSylowIn 2 T ⊤ → A ≤ T → IsElemAbelian 2 A →
      twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) →
      perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆ →
      Group.IsSolvable Y → T ≤ J → J ⊔ Y = ⊤ →
      J ⊔ (⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K) = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ h
    exact absurd h (by have := Nat.card_pos (α := G); omega)
  | succ n ih =>
    intro G _ _ hn T A Y J _ hT hA hAab hres hcomm hY hTJ hJY
    set J₁ := J ⊔ (⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K) with hJ₁
    by_cases hYbot : Y = ⊥
    · rw [hYbot, sup_bot_eq] at hJY
      exact top_le_iff.mp (hJY ▸ le_sup_left)
    · obtain ⟨Y₁, hY₁n, hY₁Y, hY₁ne, hY₁min⟩ :=
        CFSG.exists_minimal_normal_le Y inferInstance hYbot
      have : Y₁.Normal := hY₁n
      have hY₁solv : Group.IsSolvable Y₁ :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hY₁Y)
          (Subgroup.inclusion_injective hY₁Y)
      have hIM : CFSG.IsMinimalNormal Y₁ := ⟨fun K _ hKY => by
        by_cases hK : K = ⊥
        · exact Or.inl hK
        · exact Or.inr (hY₁min K ‹_› hKY hK)⟩
      obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian Y₁
      have hY₁p : IsPGroup r Y₁ := CFSG.IsElementaryAbelian.isPGroup r Y₁
      have hY₁ab : ∀ a ∈ Y₁, ∀ b ∈ Y₁, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      set π := QuotientGroup.mk' Y₁ with hπ
      have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y₁
      have hker : π.ker = Y₁ := QuotientGroup.ker_mk' Y₁
      have hcardlt : Nat.card (G ⧸ Y₁) ≤ n := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Y₁
        have h2 : 1 < Nat.card Y₁ := (Subgroup.one_lt_card_iff_ne_bot Y₁).mpr hY₁ne
        have h3 := Nat.card_pos (α := G ⧸ Y₁)
        nlinarith
      have hYn : (Y.map π).Normal := Subgroup.Normal.map inferInstance π hπs
      have hYs : Group.IsSolvable (Y.map π) :=
        Group.isSolvable_of_surjective (π.subgroupMap_surjective Y)
      have hres' : twoResidual (⊤ : Subgroup (G ⧸ Y₁)) =
          perfectCore (⊤ : Subgroup (G ⧸ Y₁)) := by
        have h1 := congrArg (Subgroup.map π) hres
        rw [map_twoResidual π ⊤, map_perfectCore π ⊤, Subgroup.map_top_of_surjective π hπs] at h1
        exact h1
      have hcomm' : perfectCore (⊤ : Subgroup (G ⧸ Y₁)) =
          ⁅perfectCore (⊤ : Subgroup (G ⧸ Y₁)), A.map π⁆ := by
        have h1 := congrArg (Subgroup.map π) hcomm
        rw [Subgroup.map_commutator, map_perfectCore π ⊤,
          Subgroup.map_top_of_surjective π hπs] at h1
        exact h1
      have hJY' : J.map π ⊔ Y.map π = ⊤ := by
        rw [← Subgroup.map_sup, hJY, Subgroup.map_top_of_surjective π hπs]
      have hIH := ih (G ⧸ Y₁) hcardlt (T := T.map π) (A := A.map π) (Y := Y.map π)
        (J := J.map π) (isSylowIn_two_map_top hπs hT) (Subgroup.map_mono hA)
        (isElemAbelian_map' π hAab) hres' hcomm' hYs (Subgroup.map_mono hTJ) hJY'
      have hπJ₁ : J₁.map π = ⊤ := by
        refine top_le_iff.mp ?_
        rw [← hIH]
        refine sup_le (Subgroup.map_mono le_sup_left) (iSup₂_le fun K hK => ?_)
        obtain ⟨J', hJ', hJ'K⟩ := ten_seven hT hA hAab hK
        have hJ'J₁ : J' ≤ J₁ := by
          have h1 : J' ≤ ⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K :=
            le_iSup₂_of_le (f := fun K (_ : K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}) => K) J' hJ'
              le_rfl
          exact h1.trans le_sup_right
        calc K ≤ twoResidual K ⊔ (T.map π ⊓ K) := le_twoResidual_sup_of_isSylowIn hK.2.2.1
          _ ≤ (twoResidual J').map π ⊔ T.map π := by
            rw [hJ'K]
            exact sup_le_sup le_rfl inf_le_left
          _ ≤ J₁.map π := sup_le (Subgroup.map_mono ((twoResidual_le J').trans hJ'J₁))
            (Subgroup.map_mono (hTJ.trans le_sup_left))
      have hJ₁Y₁ : J₁ ⊔ Y₁ = ⊤ := by
        have h := Subgroup.comap_map_eq π J₁
        rw [hπJ₁, Subgroup.comap_top, hker] at h
        exact h.symm
      have hY₁J₁ : Y₁ ≤ J₁ :=
        ten_eight_step hT hA hAab hres hcomm hr hY₁p hY₁ab hY₁min (hTJ.trans le_sup_left)
          hJ₁Y₁ le_sup_right
      rw [← hJ₁Y₁]
      exact (sup_eq_left.mpr hY₁J₁).symm

theorem ten_eight {G : Type u} [Group G] [Finite G] {T A Y J : Subgroup G} [Y.Normal]
    (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (h1 : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    (h2 : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆)
    (hY : IsTwoClosed Y) (hTJ : T ≤ J) (hJY : J ⊔ Y = ⊤) :
    J ⊔ (⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K) = ⊤ :=
  ten_eight_aux (Nat.card G) G le_rfl hT hA hAab h1 h2 (isSolvable_of_isTwoClosed hY) hTJ hJY

end E1

end CFSG.Quasithin
