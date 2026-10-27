module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnHolds

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn Hering214

variable {G : Type} [Group G] [Finite G]

private theorem lift_conj' {J P : Subgroup G} {S : Type} [Group S] {R : Subgroup S}
    (L : LiftData J P S R) {j : ↥J} (hj : L.ϕ j ∈ Subgroup.normalizer (R : Set S)) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P)
    (h : L.ϕ j * L.ϕ ⟨x, L.le hx⟩ * (L.ϕ j)⁻¹ = L.ϕ ⟨y, L.le hy⟩) :
    (j : G) * x * (j : G)⁻¹ = y := by
  have hc : (j : G) * x * (j : G)⁻¹ ∈ P := L.conj_mem_of_image hj hx
  refine L.inj_on_P hc hy ?_
  rw [← h, ← map_inv, ← map_mul, ← map_mul]
  rfl

private theorem conj_to_mul' {r x y : G} (h : r * x * r⁻¹ = y) : r * x = y * r := by
  rw [← h]; group

theorem exists_normData4
    {J P : Subgroup G} (hq : CFSG.IsQuasisimple ↥J)
    (hm : IsTypeLnq 4 2 1 J) (hP : IsSylowOf 3 P J) :
    ∃ u v r₁ r₂ w : G, u ∈ P ∧ v ∈ P ∧ r₁ ∈ J ∧ r₂ ∈ J ∧ w ∈ J ∧ NormData u v r₁ r₂ w ∧
      P = R u v ∧
      ∀ g ∈ Nor J, g ∈ Nor P → InBlocks u v (g * u * g⁻¹) ∧ InBlocks u v (g * v * g⁻¹) := by
  have hZ := FF79.card_center_dvd_two_of_typeLn hq (Or.inl rfl) hm
  have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J)) :=
    Nat.Coprime.coprime_dvd_right hZ (by norm_num)
  obtain ⟨e'⟩ : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one hm
    haveI := Hering214.charP_two_of_natCard_eq_two hK
    exact ⟨e.trans (MulEquiv.ofBijective (Hering214.embedTwo K 4)
      (embedTwo_bijective hK (Or.inl rfl))).symm⟩
  obtain ⟨⟨L⟩, hc⟩ := liftData_of_equiv hq hP hcop e' card_R_sylow4
  have M := tModel4
  have N4 := normData4
  have E4 := N4.toE9Data
  obtain ⟨pu, hpuP, hpu⟩ := (L.img sA4).mp E4.a_mem
  obtain ⟨pv, hpvP, hpv⟩ := (L.img sB4).mp E4.b_mem
  obtain ⟨j₁, hj₁⟩ := L.surj sR1_4
  obtain ⟨j₂, hj₂⟩ := L.surj sR2_4
  obtain ⟨jw, hjw⟩ := L.surj sW4
  set u : G := (pu : G) with hu
  set v : G := (pv : G) with hv
  have hpu' : pu = ⟨u, L.le hpuP⟩ := rfl
  have hpv' : pv = ⟨v, L.le hpvP⟩ := rfl
  have hN1 : L.ϕ j₁ ∈ Subgroup.normalizer (R sA4 sB4 : Set _) := by
    rw [hj₁]; simpa [jk] using N4.jk_mem 1
  have hN2 : L.ϕ j₂ ∈ Subgroup.normalizer (R sA4 sB4 : Set _) := by
    rw [hj₂]; simpa [jk] using N4.jk_mem 2
  have hNw : L.ϕ jw ∈ Subgroup.normalizer (R sA4 sB4 : Set _) := by
    rw [hjw]; simpa [jk] using N4.jk_mem 4
  have hu2 : u ^ 2 ∈ P := P.pow_mem hpuP 2
  have hv2 : v ^ 2 ∈ P := P.pow_mem hpvP 2
  have hϕu2 : L.ϕ ⟨u ^ 2, L.le hu2⟩ = sA4 ^ 2 := by
    rw [show (⟨u ^ 2, L.le hu2⟩ : ↥J) = pu ^ 2 from rfl, map_pow, hpu]
  have hϕv2 : L.ϕ ⟨v ^ 2, L.le hv2⟩ = sB4 ^ 2 := by
    rw [show (⟨v ^ 2, L.le hv2⟩ : ↥J) = pv ^ 2 from rfl, map_pow, hpv]
  have hmodel : ∀ {r x y : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)}, r * x = y * r →
      r * x * r⁻¹ = y := fun h => by rw [h]; group
  have hdist : ∀ i j k l : Fin 3, u ^ (i : ℕ) * v ^ (j : ℕ) = u ^ (k : ℕ) * v ^ (l : ℕ) →
      i = k ∧ j = l := by
    intro i j k l h
    apply E4.dist
    have h' : pu ^ (i : ℕ) * pv ^ (j : ℕ) = pu ^ (k : ℕ) * pv ^ (l : ℕ) := Subtype.ext (by
      simpa using h)
    have := congrArg L.ϕ h'
    simpa [map_mul, map_pow, hpu, hpv] using this
  have hE : E9Data u v :=
    ⟨L.cube_P M hpuP, L.cube_P M hpvP, L.comm_P M hpuP hpvP, hdist⟩
  have hND : NormData u v (j₁ : G) (j₂ : G) (jw : G) := by
    have e1 := lift_conj' L hN1 hpuP hu2 (by rw [hj₁, ← hpu', hpu, hϕu2]; exact hmodel N4.r₁a)
    have e2 := lift_conj' L hN1 hpvP hpvP (by rw [hj₁, ← hpv', hpv]; exact hmodel N4.r₁b)
    have e3 := lift_conj' L hN2 hpuP hpuP (by rw [hj₂, ← hpu', hpu]; exact hmodel N4.r₂a)
    have e4 := lift_conj' L hN2 hpvP hv2 (by rw [hj₂, ← hpv', hpv, hϕv2]; exact hmodel N4.r₂b)
    have e5 := lift_conj' L hNw hpuP hpvP (by
      rw [hjw, ← hpu', ← hpv', hpu, hpv]; exact hmodel N4.wa)
    have e6 := lift_conj' L hNw hpvP hpuP (by
      rw [hjw, ← hpu', ← hpv', hpu, hpv]; exact hmodel N4.wb)
    exact ⟨hE, conj_to_mul' e1, conj_to_mul' e2, conj_to_mul' e3, conj_to_mul' e4, conj_to_mul' e5,
      conj_to_mul' e6⟩
  have hRP : R u v ≤ P := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hpuP
    · exact hpvP
  have hPcard : Nat.card P = 9 := by rw [hc, ← card_R_sylow4, M.card]
  have hPR : P = R u v :=
    (Subgroup.eq_of_le_of_card_ge hRP (by rw [hPcard, hE.card_R])).symm
  refine ⟨u, v, j₁, j₂, jw, hpuP, hpvP, j₁.2, j₂.2, jw.2, hND, hPR, ?_⟩
  have hblk := hconj_of_trace E4 (fun g => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace)
    trace_conj_sl trace4' trace4
  intro g hgJ hgP
  obtain ⟨j, hjP, hjx⟩ := L.nor_act_lift M hgJ hgP
  have hjN := L.image_mem_nor hjP
  obtain ⟨hbu, hbv⟩ := hblk _ hjN
  have key : ∀ {x : G} (hx : x ∈ P) {s : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)},
      L.ϕ ⟨x, L.le hx⟩ = s → InBlocks sA4 sB4 (MulAut.conj (L.ϕ j) s) →
      InBlocks u v (g * x * g⁻¹) := by
    intro x hx s hs hb
    rw [hjx x hx]
    rw [← hs] at hb
    simp only [MulAut.conj_apply] at hb
    rcases hb with h | h | h | h
    · exact Or.inl (lift_conj' L hjN hx hpuP (by rw [h, ← hpu', hpu]))
    · exact Or.inr (Or.inl (lift_conj' L hjN hx hu2 (by rw [h, hϕu2])))
    · exact Or.inr (Or.inr (Or.inl (lift_conj' L hjN hx hpvP (by rw [h, ← hpv', hpv]))))
    · exact Or.inr (Or.inr (Or.inr (lift_conj' L hjN hx hv2 (by rw [h, hϕv2]))))
  exact ⟨key hpuP (by rw [← hpu']; exact hpu) hbu, key hpvP (by rw [← hpv']; exact hpv) hbv⟩

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
