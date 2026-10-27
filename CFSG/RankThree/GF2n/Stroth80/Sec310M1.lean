module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

theorem nilp_two {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
    (W : Submodule K E) (hW : Module.finrank K W = 2) (N : E →ₗ[K] E)
    (hNW : ∀ x ∈ W, N x ∈ W) (hN2 : ∀ x ∈ W, N (N x) = 0)
    {b : E} (hbW : b ∈ W) (hb0 : b ≠ 0) (hNb : N b = 0) :
    ∀ x ∈ W, N x ∈ Submodule.span K {b} := by
  intro x hx
  by_contra hnot
  have hy : N x ∈ W := hNW x hx
  have hli : LinearIndependent K ![b, N x] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at h
      exact ⟨h.resolve_right hb0, rfl⟩
    · exfalso
      apply hnot
      have h2 : t⁻¹ • (s • b + t • N x) = 0 := by rw [h, smul_zero]
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h2
      rw [Submodule.mem_span_singleton]
      refine ⟨-(t⁻¹ * s), ?_⟩
      rw [neg_smul]
      exact neg_eq_iff_add_eq_zero.mpr h2
  haveI : Module.Finite K W := Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  have hle : Submodule.span K (Set.range ![b, N x]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [hbW, hy]
  have hd : Module.finrank K (Submodule.span K (Set.range ![b, N x])) = Module.finrank K W := by
    rw [finrank_span_eq_card hli, hW, Fintype.card_fin]
  have heq : Submodule.span K (Set.range ![b, N x]) = W :=
    Submodule.eq_of_le_of_finrank_eq hle hd
  have hxs : x ∈ Submodule.span K (Set.range ![b, N x]) := by
    rw [heq]
    exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxs
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hc
  have hN : N x = 0 := by
    have h3 := congrArg N hc
    rw [map_add, map_smul, map_smul, hNb, hN2 x hx, smul_zero, smul_zero, add_zero] at h3
    exact h3.symm
  exact hnot (by rw [hN]; exact Submodule.zero_mem _)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.Vt_le_inf_QB_of_card_eq (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ 3) :
    Vt M (LB M Q B) B Z t ≤ Q ⊓ QB B := by
  classical
  have hconc : Conc34 M Q Z B := h34 G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen
  have h352 : ∀ m ∈ M, CQt Q Z (LB M Q (conjSubgroup m B)) =
      ((conjSubgroup m B ⊔ Z : Subgroup G) : Set G) := fun m hm =>
    (stroth_3_5 h34 (hc.conj_of_mem hm) hs.width hs.n_gt (hc.noA2_conj hs.noA2 hm)
      (hs.gen.conj_of_mem hm)).2.1
  have hcomm := hc.Vt_comm h352 hs.mem hs.notQ
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  refine hconc _ (le_inf hVQ fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b (hBV hb) x hx) ?_
  intro x hx l hl
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have hlH : l ∈ H0 M Z := hc.LB_le_H0 hl
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem hl
  have hlM : l ∈ M := hc.LB_le_M hl
  let W : Submodule (GaloisField 2 n') M₀.E :=
    imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c e he => hc.smul_mem_img_Vt h t c he)
  have hWmem : ∀ e, e ∈ W ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun e => mem_imgSub
  have hWdim : Module.finrank (GaloisField 2 n') W = 2 := by
    have h1 := M₀.card_eq hVQ hZV
    have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ 2 := by
      have : Nat.card Z * Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
          Nat.card Z * Nat.card Z ^ 2 := by
        rw [← h1, hcard]
        ring
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
    have h3 : Nat.card W = Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) :=
      Nat.card_congr (Equiv.subtypeEquivRight hWmem)
    have h4 : Nat.card W = Nat.card (GaloisField 2 n') ^ Module.finrank (GaloisField 2 n') W :=
      Module.natCard_eq_pow_finrank
    rw [h3, h2, h.card] at h4
    have hq : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    exact (Nat.pow_right_injective hq h4).symm
  have hQnorm : ∀ y ∈ Q, l * y * l⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) y).mp hy
  have hTπ : ∀ y ∈ Q, M₀.π (l * y * l⁻¹) = φ ⟨l, hlH⟩ (M₀.π y) := fun y hy =>
    hφπ ⟨l, hlH⟩ y hy
  have hT2 : ∀ e, φ ⟨l, hlH⟩ (φ ⟨l, hlH⟩ e) = e := by
    intro e
    have h1 := hc.actionHom_sq_eq_one φ hφQ hl
    have h2 : (φ ⟨l, hc.LB_le_H0 hl⟩ ^ 2) e = e := by rw [h1]; rfl
    simpa [pow_two] using h2
  have h2K : (2 : GaloisField 2 n') = 0 := CharTwo.two_eq_zero
  have hxx : ∀ e : M₀.E, e + e = 0 := fun e => by
    rw [← two_smul (GaloisField 2 n') e, h2K, zero_smul]
  let N : M₀.E →ₗ[GaloisField 2 n'] M₀.E :=
    ((φ ⟨l, hlH⟩ : M₀.E ≃ₗ[GaloisField 2 n'] M₀.E) : M₀.E →ₗ[GaloisField 2 n'] M₀.E) - 1
  have hN : ∀ e, N e = φ ⟨l, hlH⟩ e - e := fun e => by
    simp only [N, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
  have hNW : ∀ y ∈ W, N y ∈ W := by
    intro y hy
    obtain ⟨u, huV, huQ, rfl⟩ := (hWmem y).mp hy
    have hlu : l * u * l⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt hs.mem hlR) u).mp huV
    have hTy : φ ⟨l, hlH⟩ (M₀.π u) ∈ W := by
      rw [← hTπ u huQ]
      exact (hWmem _).mpr (M₀.pi_mem_img hlu (hVQ hlu))
    rw [hN]
    exact W.sub_mem hTy hy
  have hN2 : ∀ y ∈ W, N (N y) = 0 := by
    intro y _
    rw [hN, hN, map_sub, hT2]
    calc y - φ ⟨l, hlH⟩ y - (φ ⟨l, hlH⟩ y - y) =
        (y + y) - (φ ⟨l, hlH⟩ y + φ ⟨l, hlH⟩ y) := by abel
      _ = 0 := by rw [hxx, hxx, sub_zero]
  obtain ⟨u₀, hu₀B, hu₀Q, hu₀⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
  have hbW : b ∈ W := (hWmem b).mpr (M₀.img_mono hBV ((hB b).mpr ⟨1, (one_smul _ b).symm⟩))
  have hNb : N b = 0 := by
    rw [hN, sub_eq_zero, ← hu₀, ← hTπ u₀ hu₀Q]
    have hz := hc.comm_B_mem_Z hl hu₀B
    exact ((Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hu₀Q (hQnorm u₀ hu₀Q)).mp hz)
  have hsub := nilp_two W hWdim N hNW hN2 hbW hb0 hNb (M₀.π x)
    ((hWmem _).mpr (M₀.pi_mem_img hx (hVQ hx)))
  obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp hsub
  have hxQ : x ∈ Q := hVQ hx
  have hcQ : ⁅l, x⁆ ∈ Q := by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hc.comm_mem_Q hlM hxQ)
  have hπc : M₀.π ⁅l, x⁆ = s • b := by
    rw [hs', hN, ← hTπ x hxQ]
    rw [show ⁅l, x⁆ = (l * x * l⁻¹) * x⁻¹ by rw [commutatorElement_def],
      M₀.π_mul _ (hQnorm x hxQ) _ (Q.inv_mem hxQ), M₀.pi_inv hxQ, sub_eq_add_neg]
  have hZS : Z ≤ B ⊔ Z := le_sup_right
  exact (M₀.mem_img_iff hZS hcQ).mp (by
    rw [hπc]
    exact M₀.img_mono le_sup_left ((hB _).mpr ⟨s, rfl⟩))

end CFSG.RankThree.GF2n.Stroth80
