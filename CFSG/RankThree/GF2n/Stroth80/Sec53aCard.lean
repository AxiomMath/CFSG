module

public import CFSG.RankThree.GF2n.Stroth80.Sec53aConverse
public import CFSG.RankThree.GF2n.Stroth80.Sec53aVone

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.le_sup_imgQInfQB_sp_of_hplane (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E,
      e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ (conjSubgroup r B) := by
  obtain ⟨K₁, iF, iFin, hK, hrep⟩ := hV
  letI := iF
  letI := iFin
  haveI : CharP K₁ 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hnat : SpNat hc t := ⟨K₁, iF, iFin, hK, m, hm, hrep⟩
  obtain ⟨φ, hφ, hker, hact⟩ := hrep
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ₂, M₀₂, hD₂, θ, hθ, u₀, hu₀, hBiff₀, hW₀⟩ :=
    Ctx.sp_perp_data h34 hc hs hnotQB hK hm φ hφ hker ψ hψ
  obtain ⟨u₁, hu₁, hBiff₁, hL₁, hplane₁⟩ :=
    Ctx.sp_points_core h34 hRoot hc hs hK hm φ hφ hker ψ hψ
  obtain ⟨c, hc₁⟩ := (hBiff₀ u₁).mp ((hBiff₁ u₁).mpr ⟨1, (one_smul K₁ u₁).symm⟩)
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu₁
    rw [hc₁, h0, zero_smul]
  have hne₁ : spForm m K₁ u₁
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₁) ≠ 0 :=
    ((hplane₁ ⟨r, hr⟩).1).mp hplane
  have hne₀ : spForm m K₁ u₀
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀) ≠ 0 := by
    intro h0
    apply hne₁
    have hform : ∀ x y : Fin m ⊕ Fin m → K₁,
        spForm m K₁ x y = CFSG.Timmesfeld.ARS.CaseM.spForm x y := fun x y =>
      (spForm_apply x y).trans rfl
    rw [hc₁, Matrix.mulVec_smul]
    have hsc : spForm m K₁ (c • u₀)
        (c • ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀)) =
        c * (c * spForm m K₁ u₀
          ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀)) := by
      rw [hform (c • u₀) (c • _),
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left',
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right',
        ← hform u₀ _]
    rw [hsc, h0]
    simp
  exact Ctx.le_sup_imgQInfQB_sp (K := K₁) (K₂ := K) (M₀ := M₀)
    hc hs φ hφ ψ hψ hr hW₀ hne₀ T hTmem

theorem Ctx.finrank_inf_imgQInfQB_of_card_vone (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hV : SpMNat hc t m)
    {C : Subgroup G} (hcC : Ctx M Q Z C) (hnoC : NoA2 Q Z (LB M Q C))
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E)
    (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hBT : Module.finrank K ↥(imgQInfQB M₀ B ⊓ T) + 1 = 2 * m)
    (hCT : Module.finrank K ↥(imgQInfQB M₀ C ⊓ T) + 1 = 2 * m)
    (hspan : T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ C)
    (hcard : Nat.card ↥(Vone Q B C (Vt M (LB M Q B) B Z t))
      = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z) :
    Module.finrank K ↥(imgQInfQB M₀ B ⊓ imgQInfQB M₀ C) + 1 = 2 * m := by
  haveI : FiniteDimensional K M₀.E := M₀.fin
  haveI hTfin : FiniteDimensional K ↥T := FiniteDimensional.finiteDimensional_submodule T
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hK2 : 2 ≤ Nat.card K := by rw [hD.card]; exact hq2
  have hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) :=
    SpMNat.card_V hV
  have hTcard : Nat.card ↥T = Nat.card Z ^ (2 * m) := by
    have hVT : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card ↥T := by
      rw [M₀.card_eq hVQ hZV]
      exact congrArg (fun n => Nat.card Z * n)
        (Nat.card_congr (Equiv.subtypeEquivRight fun e => (hTmem e).symm))
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
    calc Nat.card Z * Nat.card ↥T = Nat.card ↥(Vt M (LB M Q B) B Z t) := hVT.symm
      _ = Nat.card Z ^ (2 * m + 1) := hVcard
      _ = Nat.card Z * Nat.card Z ^ (2 * m) := by rw [pow_succ']
  have hT : Module.finrank K ↥T = 2 * m := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := ↥T)
    have h2 : Nat.card K ^ Module.finrank K ↥T = Nat.card K ^ (2 * m) := by
      rw [← h, hTcard, hD.card]
    exact Nat.pow_right_injective hK2 h2
  have hV1eq : Nat.card ↥(Vone Q B C (Vt M (LB M Q B) B Z t)) =
      Nat.card Z * Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t))) :=
    M₀.card_eq (vone_le_Q hVQ) Z_le_vone
  have hcardimg : Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t))) =
      Nat.card K ^ (2 * m + 1) := by
    have hVT : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card K ^ (2 * m) := by
      rw [M₀.card_eq hVQ hZV]
      congr 1
      calc Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card ↥T :=
            Nat.card_congr (Equiv.subtypeEquivRight fun e => (hTmem e).symm)
        _ = Nat.card K ^ (2 * m) := by rw [hTcard, hD.card]
    have heq : Nat.card Z * Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t))) =
        Nat.card Z * (Nat.card K ^ (2 * m) * Nat.card Z) := by
      rw [← hV1eq, hcard, hVT]
      ring
    have hcancel : Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t))) =
        Nat.card K ^ (2 * m) * Nat.card Z :=
      Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) heq
    calc Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t)))
        = Nat.card K ^ (2 * m) * Nat.card Z := hcancel
      _ = Nat.card K ^ (2 * m + 1) := by rw [hD.card, ← pow_succ]
  have hcardsub : Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t))) =
      Nat.card ↥((imgQInfQB M₀ B ⊔ T) ⊓ (imgQInfQB M₀ C ⊔ T)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e =>
      Ctx.mem_img_vone_iff hc hs hcC hnoC hD hVQ hZV T hTmem e)
  have hdim : Module.finrank K ↥((imgQInfQB M₀ B ⊔ T) ⊓
      (imgQInfQB M₀ C ⊔ T)) = 2 * m + 1 := by
    have hnat := Module.natCard_eq_pow_finrank (K := K)
      (V := ↥((imgQInfQB M₀ B ⊔ T) ⊓ (imgQInfQB M₀ C ⊔ T)))
    have h2 : Nat.card K ^ Module.finrank K
        ↥((imgQInfQB M₀ B ⊔ T) ⊓ (imgQInfQB M₀ C ⊔ T)) =
        Nat.card K ^ (2 * m + 1) := by
      rw [← hnat, ← hcardsub, hcardimg]
    exact Nat.pow_right_injective hK2 h2
  have hSB : Module.finrank K ↥(imgQInfQB M₀ B) = n :=
    (hc.imgQInfQB_lagr hs.width hs.n_gt hs.noA2 hD).1
  have hSC : Module.finrank K ↥(imgQInfQB M₀ C) = n :=
    (hcC.imgQInfQB_lagr hs.width hs.n_gt hnoC hD).1
  exact sec53a_finrank_inf_of_finrank_sup_sup hSB hSC hT hBT hCT hspan hdim

theorem stroth53a_of_card_vone (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hcard : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (m : ℕ), SpMNat hc t m →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ T : Submodule K M₀.E,
        (∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
        Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))
          = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z)
    (hOdd : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t → Odd n) :
    Stroth53aStatement := by
  refine stroth53a_of_sp_model_count h34 hRoot ?_ hOdd
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane m hV K _ _ _ γ M₀ hD
  obtain ⟨T, hTmem, hcard'⟩ :=
    hcard G M Q Z B hc n t hs hsp r hr hplane m hV K γ M₀ hD
  obtain ⟨K₀, iF₀, iFin₀, hK₀, m₀, hm₀, hrep₀⟩ := hsp
  have hm : 2 ≤ m := by
    have hEq : m = m₀ := SpMNat.m_unique hV ⟨K₀, iF₀, iFin₀, hK₀, hrep₀⟩
    omega
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  refine ⟨T, hTmem, ?_⟩
  exact Ctx.finrank_inf_imgQInfQB_of_card_vone h34 hc hs hV hcC hnoC hD T hTmem
    (Ctx.finrank_imgQInfQB_inf_Vt_sp h34 hRoot hc hs hm hV hD T hTmem)
    (Ctx.finrank_imgQInfQB_conj_inf_Vt_sp h34 hRoot hc hs hm hV hD T hTmem hr)
    (Ctx.le_sup_imgQInfQB_sp_of_hplane h34 hRoot hc hs hm hV hr hplane hD T hTmem)
    hcard'

end CFSG.RankThree.GF2n.Stroth80
