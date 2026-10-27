module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenModOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section CyclicRank

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16n9b_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16n9b_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

theorem s16n9b_zpowers_eq_of_ne_one {A : Subgroup (MulAut T)} {p : ℕ} (hp : p.Prime)
    (hA : Nat.card A = p) {z : MulAut T} (hz : z ∈ A) (hz1 : z ≠ 1) :
    Subgroup.zpowers z = A := by
  have hdvd : orderOf z ∣ p := hA ▸ Subgroup.orderOf_dvd_natCard A hz
  have hord : orderOf z = p := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz) ?_
  rw [Nat.card_zpowers, hord, hA]

theorem s16n9b_exists_gen {A : Subgroup (MulAut T)} {p : ℕ} (hp : p.Prime)
    (hA : Nat.card A = p) : ∃ a ∈ A, orderOf a = p ∧ Subgroup.zpowers a = A := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p (by rw [hA])
  refine ⟨(x : MulAut T), x.2, ?_, ?_⟩
  · rw [← hx]
    exact Subgroup.orderOf_coe x
  · refine s16n9b_zpowers_eq_of_ne_one hp hA x.2 ?_
    intro h1
    have h2 : x = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hx
    exact hp.one_lt.ne hx

theorem s16n9b_map_conj_of_mem {A : Subgroup (MulAut T)} {a : MulAut T} (ha : a ∈ A) :
    A.map (MulAut.conj a).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      A.mul_mem (A.mul_mem ha hy) (A.inv_mem ha)
  · intro hx
    refine ⟨a⁻¹ * x * a, A.mul_mem (A.mul_mem (A.inv_mem ha) hx) ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem s16n9b_cyc_rank (hT : ∀ t : T, t ^ 2 = 1) {A : Subgroup (MulAut T)} {p : ℕ}
    (hp : p = 3 ∨ p = 7) (hA : Nat.card A = p) (hrk : rk ↥(commSub ⊤ A) = 2 * dParam p)
    {φ : MulAut T} (hφ : A.map (MulAut.conj φ).toMonoidHom = A) :
    (∀ w ∈ commSub ⊤ A, φ w = w) ∨
      dParam p ≤ rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers φ)) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hodd : Odd (Nat.card A) := by
    rw [hA]
    rcases hp with rfl | rfl <;> decide
  obtain ⟨a, haA, hap, hgen⟩ := s16n9b_exists_gen hpp hA
  have hfixW : commSub ⊤ A ⊓ fixV A = ⊥ := by
    have := (coprime_decomp hodd hT (W := (⊤ : Subgroup T))
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    simpa only [top_inf_eq] using this
  have hWA : ∀ b ∈ A, (commSub ⊤ A).map b.toMonoidHom = commSub ⊤ A := by
    intro b hb
    rw [← s15_Infra_commSub_top_map_conj A b, s16n9b_map_conj_of_mem hb]
  have hWφ : (commSub ⊤ A).map φ.toMonoidHom = commSub ⊤ A := by
    rw [← s15_Infra_commSub_top_map_conj A φ, hφ]
  have hstW : φ ∈ stabSub (commSub ⊤ A) := s16n9b_mem_stabSub_of_map_eq hWφ
  have hinv : ∀ x ∈ Subgroup.zpowers φ, ∀ w ∈ commSub ⊤ A, x w ∈ commSub ⊤ A :=
    fun x hx w hw => (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW hx) w).2 hw
  by_cases hcomm : ∀ b ∈ A, φ * b = b * φ
  ·
    by_cases hfix : ∀ w ∈ commSub ⊤ A, φ w = w
    · exact Or.inl hfix
    · right
      push Not at hfix
      obtain ⟨w, hwW, hwφ⟩ := hfix
      have hU_map : (commSub (commSub ⊤ A) (Subgroup.zpowers φ)).map a.toMonoidHom =
          commSub (commSub ⊤ A) (Subgroup.zpowers φ) := by
        have h1 := s15_Core_commSub_map_conj (commSub ⊤ A) (Subgroup.zpowers φ) a
        have h2 : (Subgroup.zpowers φ).map (MulAut.conj a).toMonoidHom =
            Subgroup.zpowers φ := by
          rw [MonoidHom.map_zpowers]
          congr 1
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [← hcomm a haA, mul_inv_cancel_right]
        rw [hWA a haA, h2] at h1
        exact h1.symm
      have hU_le : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ≤ commSub ⊤ A :=
        commSub_le_of_invariant hinv
      have hU_ne : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ≠ ⊥ := by
        intro hU0
        apply hwφ
        have h1 : φ w * w⁻¹ ∈ commSub (commSub ⊤ A) (Subgroup.zpowers φ) :=
          Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, w, hwW, rfl⟩
        rw [hU0, Subgroup.mem_bot, mul_inv_eq_one] at h1
        exact h1
      have hU_fix : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ⊓
          fixV (Subgroup.zpowers a) = ⊥ := by
        rw [hgen]
        exact le_bot_iff.1 ((inf_le_inf hU_le le_rfl).trans hfixW.le)
      rcases hp with rfl | rfl
      · rw [s16n9b_dParam_three]
        exact s16c167_two_le_rk_of_order_three hT hap hU_map hU_fix hU_ne
      · rw [s16n9b_dParam_seven]
        exact s16c167_three_le_rk_of_order_seven hT hap hU_map hU_fix hU_ne
  ·
    right
    push Not at hcomm
    obtain ⟨b, hbA, hbφ⟩ := hcomm
    have hkey : ∀ c ∈ commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ), c ≠ 1 →
        b c ∉ commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ) := by
      intro c hc hc1 hbc
      have hcW : c ∈ commSub ⊤ A := hc.1
      have hφc : φ c = c := mem_fixV_zpowers_iff_apply.1 hc.2
      have hφbc : φ (b c) = b c := mem_fixV_zpowers_iff_apply.1 hbc.2
      have hφinv : φ⁻¹ c = c := by
        calc φ⁻¹ c = φ⁻¹ (φ c) := by rw [hφc]
          _ = c := MulAut.inv_apply_self _ _ _
      have hy : φ * b * φ⁻¹ ∈ A := by
        have h1 : (MulAut.conj φ).toMonoidHom b ∈ A.map (MulAut.conj φ).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hbA
        rw [hφ] at h1
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
      have hyc : (φ * b * φ⁻¹) c = b c := by
        show φ (b (φ⁻¹ c)) = b c
        rw [hφinv, hφbc]
      have hzA : b⁻¹ * (φ * b * φ⁻¹) ∈ A := A.mul_mem (A.inv_mem hbA) hy
      have hzc : (b⁻¹ * (φ * b * φ⁻¹)) c = c := by
        show b⁻¹ ((φ * b * φ⁻¹) c) = c
        rw [hyc]
        exact MulAut.inv_apply_self _ _ _
      by_cases hz1 : b⁻¹ * (φ * b * φ⁻¹) = 1
      · apply hbφ
        have h1 : φ * b * φ⁻¹ = b := by
          have h2 := congrArg (fun z => b * z) hz1
          simpa using h2
        calc φ * b = φ * b * φ⁻¹ * φ := by group
          _ = b * φ := by rw [h1]
      · apply hc1
        have hz : Subgroup.zpowers (b⁻¹ * (φ * b * φ⁻¹)) = A :=
          s16n9b_zpowers_eq_of_ne_one hpp hA hzA hz1
        have hcfix : c ∈ fixV A := by
          rw [← hz]
          exact mem_fixV_zpowers_iff_apply.2 hzc
        have hmem : c ∈ commSub ⊤ A ⊓ fixV A := ⟨hcW, hcfix⟩
        rw [hfixW, Subgroup.mem_bot] at hmem
        exact hmem
    have hbot : (commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ)) ⊓
        (commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ)).map b.toMonoidHom = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxmap⟩ := hx
      obtain ⟨c, hcC, rfl⟩ := Subgroup.mem_map.1 hxmap
      by_cases hc1 : c = 1
      · rw [hc1, map_one]
        exact Subgroup.one_mem _
      · exact absurd hxC (hkey c hcC hc1)
    have hC_le : (commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ)) ≤ commSub ⊤ A := inf_le_left
    have hCb_le : (commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ)).map b.toMonoidHom ≤
        commSub ⊤ A := by
      calc (commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ)).map b.toMonoidHom
          ≤ (commSub ⊤ A).map b.toMonoidHom := Subgroup.map_mono inf_le_left
        _ = commSub ⊤ A := hWA b hbA
    have hsum := rk_sup_add_rk_inf (commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ))
      ((commSub ⊤ A ⊓ fixV (Subgroup.zpowers φ)).map b.toMonoidHom)
    rw [hbot, rk_bot, s16n9b_rk_map b] at hsum
    have hle := rk_mono (sup_le hC_le hCb_le)
    have hsplit := rk_commSub_add_rk_inf_fixV hinv
    omega

end CyclicRank

section Leaf

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case10_invFix (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥) {p : ℕ}
    (hp : p = 3 ∨ p = 7) (h10 : Case168_10At D V₀ V hV L p) :
    s16n9bInvFix (Mbar D.M V₀ V hV) p (2 * dParam p - 1) := by
  obtain ⟨hcyc, hrkW, hs, -, -⟩ := h10
  obtain ⟨g, hg⟩ := s16n9b_twoConj D h1217 hV hc hV0 hs
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hd : 0 < dParam p := dParam_pos hpp (by rcases hp with rfl | rfl <;> norm_num)
  have hA : Nat.card ↥(lBar V₀ V hV L) = p := hcyc.2
  have hrk : rk ↥(commSub ⊤ (lBar V₀ V hV L)) = 2 * dParam p := hrkW
  obtain ⟨a, haA, hap, -⟩ := s16n9b_exists_gen hpp hA
  refine s16n9b_two_invFix hg (p := p) (r := dParam p) ?_ ?_ ⟨a, haA, hap⟩ ?_
  · rw [hrk]
    omega
  · omega
  · intro φ _ _ hφA
    exact s16n9b_cyc_rank (s15_Infra_vtil_sq_eq_one V₀ V hV) hp hA hrk hφA

end Leaf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
