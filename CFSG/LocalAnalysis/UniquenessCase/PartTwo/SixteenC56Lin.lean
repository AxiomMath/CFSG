module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Refl
public import CFSG.RankThree.GF2n.Stroth80.FieldAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private def linSub (S : OmegaModel W) : Subgroup (MulAut W) where
  carrier := {g : MulAut W | ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w)}
  one_mem' := by intro c w; simp
  mul_mem' := by
    intro g h hg hh c w
    have hg' : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w) := hg
    have hh' : ∀ (c : S.K) (w : W), h (S.smul c w) = S.smul c (h w) := hh
    simp only [MulAut.mul_apply]
    rw [hh' c w, hg' c (h w)]
  inv_mem' := by
    intro g hg c w
    have hg' : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w) := hg
    apply g.injective
    simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rw [hg' c (g.symm w)]
    simp

private theorem eq_of_smul_eq_smul {a b : S.K} (h : ∀ w : W, S.smul a w = S.smul b w) :
    a = b := by
  have h1 := congrFun (congrArg S.vec (h (S.ofVec (Pi.single (Sum.inl 0) 1)))) (Sum.inl 0)
  simpa [S.vec_smul, S.vec_ofVec] using h1

private theorem twist_mul_self_eq_one {g : MulAut W} {σ : S.K ≃+* S.K}
    (hg : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul (σ c) (g w)) (hg2 : g * g = 1) :
    σ * σ = 1 := by
  ext c
  change σ (σ c) = c
  apply eq_of_smul_eq_smul S
  intro w
  have h1 : g (g (S.smul c w)) = S.smul (σ (σ c)) w := by
    rw [hg c w, hg (σ c) (g w)]
    congr 1
    rw [← MulAut.mul_apply, hg2, MulAut.one_apply]
  have h2 : g (g (S.smul c w)) = S.smul c w := by
    rw [← MulAut.mul_apply, hg2, MulAut.one_apply]
  rw [← h1, h2]

theorem linear_of_mem_aSet {X : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W)))
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X) {b : MulAut W} (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hfix : Nat.card S.K ^ 2 < Nat.card {v : W // b v = v}) :
    ∀ g ∈ A, ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g₀, hg₀A, c₀, w₁, hg₀ne⟩ := hcon
  have hg₀nl : ¬ (∀ (c : S.K) (w : W), g₀ (S.smul c w) = S.smul c (g₀ w)) :=
    fun h => hg₀ne (h c₀ w₁)
  obtain ⟨σ₀, hσ₀⟩ := S.exists_ringEquiv_of_mem_normalizer (hX (hA.1 hg₀A))
  have hg₀2 : g₀ * g₀ = 1 := by
    have h := hA.2.2.1.2 g₀ hg₀A
    rwa [pow_two] at h
  have hσ₀ne : σ₀ ≠ RingEquiv.refl S.K := by
    intro h
    exact hg₀nl fun c w => by rw [hσ₀ c w]; simp [h]
  have hσ₀sq : σ₀ * σ₀ = 1 := twist_mul_self_eq_one S hσ₀ hg₀2
  have hσ₀key : ∀ c : S.K, σ₀ (σ₀ c) = c := by
    intro c
    have h := congrArg (fun e : S.K ≃+* S.K => e c) hσ₀sq
    simpa using h
  let B' : Subgroup (MulAut W) := A ⊓ linSub S
  have hB'le : B' ≤ A := inf_le_left
  have hg₀notB : g₀ ∉ B' := fun h => hg₀nl h.2
  have hmemB' : ∀ {h : MulAut W}, h ∈ B' →
      ∀ (c : S.K) (w : W), h (S.smul c w) = S.smul c (h w) := fun hh => hh.2
  have hmulB' : ∀ b ∈ A, b * g₀ ∈ B' ↔ b ∉ B' := by
    intro b hbA
    constructor
    · intro hbg hbB'
      have hg₀B' : g₀ ∈ B' := by
        have h1 : b⁻¹ * (b * g₀) = g₀ := by group
        rw [← h1]
        exact B'.mul_mem (B'.inv_mem hbB') hbg
      exact hg₀notB hg₀B'
    · intro hbB'
      have hbnotlin : ¬ (∀ (c : S.K) (w : W), b (S.smul c w) = S.smul c (b w)) :=
        fun h => hbB' ⟨hbA, h⟩
      obtain ⟨σ, hσ⟩ := S.exists_ringEquiv_of_mem_normalizer (hX (hA.1 hbA))
      have hb2 : b * b = 1 := by
        have h := hA.2.2.1.2 b hbA
        rwa [pow_two] at h
      have hσne : σ ≠ RingEquiv.refl S.K := fun h => hbnotlin fun c w => by
        rw [hσ c w]; simp [h]
      have hσeq : σ = σ₀ :=
        CFSG.RankThree.GF2n.Stroth80.ringEquiv_eq_of_sq_eq_one σ σ₀
          (twist_mul_self_eq_one S hσ hb2) hσ₀sq hσne hσ₀ne
      refine ⟨A.mul_mem hbA hg₀A, ?_⟩
      intro c w
      simp only [MulAut.mul_apply]
      rw [hσ₀ c w, hσ (σ₀ c) (g₀ w), hσeq, hσ₀key c]
  have hrel : B'.relIndex A = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    exact ⟨g₀, hg₀A, hg₀notB, fun b hbA => by
      by_cases hb : b ∈ B'
      · exact Or.inr hb
      · exact Or.inl ((hmulB' b hbA).mpr hb)⟩
  have hmq : E3.mQuot A B' < 2 := by
    unfold E3.mQuot
    rw [hrel, padicValNat_self (p := 2)]
    norm_num
  have hfixBA : fixV B' = fixV A := hA.2.2.2 B' hB'le hmq
  have hb2 : b * b = 1 := by
    have h := hA.2.2.1.2 b hbA
    rwa [pow_two] at h
  obtain ⟨hb_lin, hb_iso⟩ := S.linear_isometry_of_card_fixed_gt (hX (hA.1 hbA)) hb2 hfix
  obtain ⟨e, hQe, ⟨u, hu⟩, hline⟩ := S.exists_line_of_card_fixed_gt hb_lin hb_iso hb1 hfix
  have he1 : e ≠ 1 := fun h => hQe (by rw [h, S.Q_one])
  have hfixB'e : ∀ h ∈ B', h e = e := by
    intro h hhB'
    have hh2 : h * h = 1 := by
      have h := hA.2.2.1.2 h (hB'le hhB')
      rwa [pow_two] at h
    have hcomm : b * h = h * b := hA.2.2.1.1 b hbA h (hB'le hhB')
    exact S.apply_eq_of_commute (hmemB' hhB') hh2 hcomm he1 hline hu
  have he_mem_A : e ∈ fixV A := by
    rw [← hfixBA]
    exact mem_fixV.mpr fun h hh => hfixB'e h hh
  have hg₀e : g₀ e = e := (mem_fixV.mp he_mem_A) g₀ hg₀A
  have hce_mem_A : ∀ c : S.K, S.smul c e ∈ fixV A := by
    intro c
    rw [← hfixBA]
    refine mem_fixV.mpr fun h hhB' => ?_
    rw [hmemB' hhB' c e, hfixB'e h hhB']
  have hg₀ce : ∀ c : S.K, g₀ (S.smul c e) = S.smul c e :=
    fun c => (mem_fixV.mp (hce_mem_A c)) g₀ hg₀A
  have hσ₀fix : ∀ c : S.K, σ₀ c = c := by
    intro c
    have h1 : S.smul (σ₀ c) e = S.smul c e := by
      have hthis := hσ₀ c e
      rw [hg₀e] at hthis
      rw [← hthis, hg₀ce c]
    have h2 := congrArg S.vec h1
    rw [S.vec_smul, S.vec_smul] at h2
    have h3 : (σ₀ c - c) • S.vec e = 0 := by
      rw [sub_smul, h2, sub_self]
    have hne : S.vec e ≠ 0 := fun h0 => he1 (S.vec_injective (h0.trans S.vec_one.symm))
    obtain ⟨i, hi⟩ : ∃ i, S.vec e i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have h4 : (σ₀ c - c) * S.vec e i = 0 := by
      have h := congrFun h3 i
      simpa [Pi.smul_apply, smul_eq_mul] using h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hi)
  exact hσ₀ne (RingEquiv.ext fun c => by simpa using hσ₀fix c)

theorem exists_fixed_line_of_mem_aSet {X : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W)))
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X) {b : MulAut W} (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hfix : Nat.card S.K ^ 2 < Nat.card {v : W // b v = v}) :
    ∃ e : W, S.Q e ≠ 0 ∧ ∀ g ∈ A, ∀ c : S.K, g (S.smul c e) = S.smul c e := by
  have hlinA := S.linear_of_mem_aSet hX hA hbA hb1 hfix
  have hb2 : b * b = 1 := by
    have := hA.2.2.1.2 b hbA
    rwa [pow_two] at this
  obtain ⟨hl_b, hi_b⟩ := S.linear_isometry_of_card_fixed_gt (hX (hA.1 hbA)) hb2 hfix
  obtain ⟨e, hQ, ⟨w₀, hw₀⟩, hline⟩ := S.exists_line_of_card_fixed_gt hl_b hi_b hb1 hfix
  have he1 : e ≠ 1 := fun h => hQ (by rw [h, S.Q_one])
  refine ⟨e, hQ, fun g hg c => ?_⟩
  have hg2 : g * g = 1 := by
    have := hA.2.2.1.2 g hg
    rwa [pow_two] at this
  have hge : g e = e :=
    S.apply_eq_of_commute (hlinA g hg) hg2 (hA.2.2.1.1 b hbA g hg) he1 hline hw₀
  rw [hlinA g hg, hge]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
