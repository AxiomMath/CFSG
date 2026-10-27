module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

private theorem ggQ2s08bf3_zmod3_eq_one_or_neg_one :
    ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by
  decide

private theorem ggQ2s08bf3_isRefl_ggLinRefl {n : ℕ} {g : Vn n ≃ₗ[ZMod 3] Vn n}
    (hg : IsRefl g) : GGLinRefl g := by
  obtain ⟨c, a, hac, hv⟩ := hg
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hac
    exact (by decide : (0 : ZMod 3) ≠ 2) hac
  have hdotv : ∀ v, a ⬝ᵥ (v - (a ⬝ᵥ v) • c) = -((a ⬝ᵥ v)) := by
    intro v
    rw [dotProduct_sub, dotProduct_smul, hac]
    exact (by decide : ∀ q : ZMod 3, q - q • (2 : ZMod 3) = -q) (a ⬝ᵥ v)
  have hc_mem : c ∈ ggLinMove g := by
    refine ⟨c, ?_⟩
    show g c - c = c
    rw [hv c, hac]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact (by decide : ∀ p : ZMod 3, p - 2 * p - p = p) (c i)
  constructor
  · apply LinearEquiv.ext
    intro v
    change g (g v) = v
    rw [hv v, hv (v - (a ⬝ᵥ v) • c), hdotv]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact (by decide : ∀ p q r : ZMod 3, p - q * r - -(q) * r = p)
      (v i) (a ⬝ᵥ v) (c i)
  · have hspan : ggLinMove g = Submodule.span (ZMod 3) {c} := by
      apply le_antisymm
      · intro x hx
        obtain ⟨v, rfl⟩ := hx
        change g v - v ∈ Submodule.span (ZMod 3) {c}
        have hneg : g v - v = -((a ⬝ᵥ v) • c) := by
          rw [hv v]
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
          exact (by decide : ∀ p q r : ZMod 3, p - q * r - p = -(q * r))
            (v i) (a ⬝ᵥ v) (c i)
        rw [hneg]
        exact Submodule.neg_mem (Submodule.span (ZMod 3) {c})
          (Submodule.smul_mem (Submodule.span (ZMod 3) {c}) (a ⬝ᵥ v)
            (Submodule.mem_span_singleton_self c))
      · intro x hx
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
        exact Submodule.smul_mem (ggLinMove g) t hc_mem
    rw [hspan]
    exact finrank_span_singleton hc0

private def ggQ2s08bf3_moveMap {n : ℕ} (a : Vn n ≃ₗ[ZMod 3] Vn n) :
    Vn n →ₗ[ZMod 3] Vn n where
  toFun v := a v - v
  map_add' x y := by
    change a (x + y) - (x + y) = (a x - x) + (a y - y)
    rw [map_add]
    abel
  map_smul' r x := by
    change a (r • x) - r • x = r • (a x - x)
    rw [map_smul, smul_sub]

private theorem ggQ2s08bf3_moveMap_range {n : ℕ} {a : Vn n ≃ₗ[ZMod 3] Vn n} :
    (ggQ2s08bf3_moveMap a).range = ggLinMove a := by
  ext v
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    change a w - w = v
    simpa [ggQ2s08bf3_moveMap] using hw
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    change a w - w = v
    exact hw

private theorem ggQ2s08bf3_isTransv_of_rank_one {n : ℕ} {a : Vn n ≃ₗ[ZMod 3] Vn n}
    (hrank : Module.finrank (ZMod 3) (ggLinMove a) = 1)
    (hsq : ∀ w, a (a w - w) = a w - w) : IsTransv a := by
  classical
  let N : Vn n →ₗ[ZMod 3] Vn n := ggQ2s08bf3_moveMap a
  have hNapply : ∀ v, N v = a v - v := fun v => rfl
  have hNrange : N.range = ggLinMove a := ggQ2s08bf3_moveMap_range
  have hsq' : ∀ w, N (N w) = 0 := by
    intro w
    have h := hsq w
    rw [← hNapply w] at h
    rw [hNapply (N w), h, sub_self]
  have hrankN : Module.finrank (ZMod 3) N.range = 1 := by
    rw [hNrange]
    exact hrank
  have hne : N.range ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank (ZMod 3) N.range = 0 := by rw [hbot, finrank_bot]
    exact (by decide : (0 : ℕ) ≠ 1) (h0.symm.trans hrankN)
  obtain ⟨c, hcrange, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, hu⟩ := hcrange
  have hcN : N c = 0 := by
    rw [← hu]
    exact hsq' u
  have hspan : N.range = Submodule.span (ZMod 3) {c} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrankN ⟨u, hu⟩ hc0
  obtain ⟨j, hcj⟩ : ∃ j : Fin n, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext fun k => h k)
  let ψ : Vn n →ₗ[ZMod 3] ZMod 3 :=
    { toFun := fun v => (N v) j * (c j)⁻¹
      map_add' := by
        intro x y
        show (N (x + y)) j * (c j)⁻¹ =
          (N x) j * (c j)⁻¹ + (N y) j * (c j)⁻¹
        rw [map_add, Pi.add_apply, add_mul]
      map_smul' := by
        intro r x
        show (N (r • x)) j * (c j)⁻¹ = r • ((N x) j * (c j)⁻¹)
        rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  let a' : Vn n := fun k => ψ (Pi.single k 1)
  have hdot : ∀ v : Vn n, a' ⬝ᵥ v = ψ v := fun v => ggQ2Cell_dotProduct_eval ψ v
  have hNv : ∀ v, N v = ψ v • c := by
    intro v
    have hmem : N v ∈ Submodule.span (ZMod 3) {c} := by
      rw [← hspan]
      exact ⟨v, rfl⟩
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    have hcoord : (N v) j = k * c j := by
      rw [← hk, Pi.smul_apply, smul_eq_mul]
    have hψ : ψ v = k := by
      show (N v) j * (c j)⁻¹ = k
      rw [hcoord, mul_assoc, mul_inv_cancel₀ hcj, mul_one]
    rw [hψ]
    exact hk.symm
  have hψc : ψ c = 0 := by
    show (N c) j * (c j)⁻¹ = 0
    rw [hcN, Pi.zero_apply, zero_mul]
  have hNne : N ≠ 0 := by
    intro hN0
    have hbot : N.range = ⊥ := by rw [hN0]; simp
    have h0 : Module.finrank (ZMod 3) N.range = 0 := by rw [hbot, finrank_bot]
    exact (by decide : (0 : ℕ) ≠ 1) (h0.symm.trans hrankN)
  have ha'0 : a' ≠ 0 := by
    intro ha'
    apply hNne
    apply LinearMap.ext
    intro v
    have hψ0 : ψ v = 0 := by
      rw [← hdot v, ha', zero_dotProduct]
    rw [hNv v, hψ0]
    simp
  unfold IsTransv
  refine ⟨c, a', hc0, ha'0, ?_, ?_⟩
  · rw [hdot c, hψc]
  · intro v
    have hav : a v = v + N v := by
      show a v = v + (a v - v)
      abel
    rw [hav, hNv v, hdot v]

private theorem ggQ2s08bf3_not_exists_smul_of_not_fixesLine {n : ℕ} {x : Vn n}
    (hx : x ≠ 0) {g : Vn n ≃ₗ[ZMod 3] Vn n} (hg : ¬ FixesLine x g) :
    ¬ ∃ c : ZMod 3, g x = c • x := by
  rintro ⟨c, hc⟩
  apply hg
  change g x = x ∨ g x = -x
  rcases eq_or_ne c 0 with h0 | h0
  · exfalso
    exact hx (g.injective (by simp [hc, h0]))
  · rcases ggQ2s08bf3_zmod3_eq_one_or_neg_one c h0 with h1 | h1
    · left
      rw [hc, h1, one_smul]
    · right
      rw [hc, h1]
      funext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      exact (by decide : ∀ p : ZMod 3, (-1) * p = -p) (x i)

theorem ggQ2s08_big_test (hKG : GGReflClassLargeThree) {ℓ : ℕ} (hℓ : 9 ≤ ℓ)
    {s : Fin ℓ → (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))} {Mx : CoxeterMatrix (Fin ℓ)}
    {x₀ : Vn (ℓ + 1)} {H : Submodule (ZMod 3) (Vn (ℓ + 1))} (hD : GGQ2S08BigLin s Mx x₀ H)
    {A Mg : Subgroup (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))}
    (hT : TestHyp (Subgroup.closure (Set.range s)) x₀ A Mg)
    (hb₁ : ∀ R : Subgroup (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)), R ≤ A →
      8 * Nat.card R < 3 ^ ((ℓ + 1) * ℓ / 2))
    (hb₂ : ∀ R : Subgroup (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)), R ≤ A →
      (∀ a ∈ R, ∀ h ∈ H, a h ∈ H) → 8 * Nat.card R < 3 ^ (ℓ * (ℓ - 1) / 2))
    {r : Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)} (hr : r ∈ Mg) (hrr : IsRefl r)
    (hrx : ¬ FixesLine x₀ r) {t : Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)} (ht : t ∈ A) (htr : IsRefl t)
    (htx : ¬ FixesLine x₀ t) :
    t ∈ Mg ∨ GGQ2S08CoreRO (N := ℓ + 1)
      (Subgroup.closure
        (((Subgroup.closure (Set.range s) : Subgroup (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))) :
          Set (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))) ∪ {r, t}))
      (Subgroup.closure (Set.range s)) r x₀ := by
  classical
  let W : Subgroup (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)) :=
    Subgroup.closure (Set.range s)
  let R : Subgroup (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)) :=
    Subgroup.closure ((W : Set (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))) ∪ {r, t})
  have hWdef : W = Subgroup.closure (Set.range s) := rfl
  have hRdef : R = Subgroup.closure
      ((W : Set (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))) ∪ {r, t}) := rfl
  have hWA : W ≤ A := le_trans hT.W_le hT.le
  have hrA : r ∈ A := hT.le hr
  have hRA : R ≤ A := by
    show Subgroup.closure
      ((W : Set (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))) ∪ {r, t}) ≤ A
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact hWA hx
    · rcases hx with rfl | rfl
      · exact hrA
      · exact ht
  have hnt : ∀ a ∈ R, ¬ (Module.finrank (ZMod 3) (ggLinMove a) = 1 ∧
      ∀ w, a (a w - w) = a w - w) := by
    intro a ha hcond
    exact hT.noTransv a (hRA ha)
      (ggQ2s08bf3_isTransv_of_rank_one hcond.1 hcond.2)
  have hdim : Module.finrank (ZMod 3) (Vn (ℓ + 1)) = ℓ + 1 := by
    rw [Module.finrank_fin_fun]
  rcases ggQ2s08_core hKG hℓ hdim H x₀ hD.hx hD.hH R W r t hRdef s Mx hD.hM
      hD.srefl hD.sH hD.rel hD.dist hD.ncomm hWdef hD.Wfix hD.WH hD.WirrH
      (ggQ2s08bf3_isRefl_ggLinRefl hrr) (ggQ2s08bf3_isRefl_ggLinRefl htr)
      (ggQ2s08bf3_not_exists_smul_of_not_fixesLine hD.hx hrx)
      (ggQ2s08bf3_not_exists_smul_of_not_fixesLine hD.hx htx)
      hnt (hb₁ R hRA) (fun hpres => hb₂ R hRA hpres) with hM0 | hRO
  · left
    have hle : GGQ2S08M0 R W r x₀ ≤ Mg := by
      show Subgroup.closure
        ((W : Set (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1))) ∪ {r} ∪
          GGQ2S08LineStab R x₀) ≤ Mg
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with ha | ha
      · rcases ha with haW | har
        · exact hT.W_le haW
        · rw [Set.mem_singleton_iff] at har
          rw [har]
          exact hr
      · obtain ⟨haR, cc, hcc0, hccx⟩ := ha
        refine hT.stab_mem a (hRA haR) ?_
        rcases ggQ2s08bf3_zmod3_eq_one_or_neg_one cc hcc0 with h1 | h1
        · left
          exact hccx.trans (by rw [h1]; simp)
        · right
          exact hccx.trans (by rw [h1]; exact neg_one_smul (ZMod 3) x₀)
    exact hle hM0
  · right
    exact hRO

end CFSG.StandardType

end
