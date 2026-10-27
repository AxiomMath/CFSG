module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SL
import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Model

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

private theorem quadModel_nondegenerate (M₀ : Tim79.QuadModel Q Z K γ) : M₀.B.Nondegenerate :=
  ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩

private theorem apply_apply_of_sq_eq_one {R E : Type*} [Semiring R] [AddCommMonoid E]
    [Module R E] {τ : E ≃ₗ[R] E} (h : τ ^ 2 = 1) (e : E) : τ (τ e) = e := by
  have h2 := congrArg (fun f : E ≃ₗ[R] E => f e) h
  simpa [pow_two] using h2

end Model

section Involution

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.eq_zero_of_fixed (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) (t : G)
    (hline : ∀ w : M₀.E, ∃ v ∈ M₀.img (Vt M (LB M Q B) B Z t), v ∉ Submodule.span K {w})
    {w : M₀.E}
    (hw : ∀ l ∈ Rt M (LB M Q B) t, ∀ S : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) → (∀ e, M₀.Qf (S e) = M₀.Qf e) → S w = w) :
    w = 0 := by
  by_contra hw0
  have hmain := hc.img_Vt_le_of_invariant h35 hM t (Submodule.span K {w})
    (by simpa using hw0) fun l hl S hS hSQ v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, hw l hl S hS hSQ]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)
  obtain ⟨v, hv, hvw⟩ := hline w
  exact hvw (hmain v hv)

theorem Ctx.Qf_sub_eq_zero (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) (t : G) (τ : M₀.E ≃ₗ[K] M₀.E)
    (hτQ : ∀ e, M₀.Qf (τ e) = M₀.Qf e) (hτ2 : ∀ e, τ (τ e) = e)
    (hcomm : ∀ l ∈ Rt M (LB M Q B) t, ∀ S : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) → ∀ e, S (τ e) = τ (S e))
    (hline : ∀ w : M₀.E, ∃ v ∈ M₀.img (Vt M (LB M Q B) B Z t), v ∉ Submodule.span K {w}) :
    ∀ e, M₀.Qf (τ e - e) = 0 := by
  classical
  have hnd := quadModel_nondegenerate M₀
  have hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f := B_map_eq_of_Qf τ hτQ
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg : ∀ e : M₀.E, -e = e := fun e => by
    have : e + e = 0 := by rw [← two_smul K e, h2, zero_smul]
    exact neg_eq_of_add_eq_zero_right this
  have hfix : ∀ e, τ (τ e - e) = τ e - e := fun e => by
    rw [map_sub, hτ2, ← neg_sub, hneg]
  have hperp : ∀ e f, τ f = f → M₀.B (τ e - e) f = 0 := fun e f hf => by
    have := hτB e f
    rw [hf] at this
    rw [map_sub, LinearMap.sub_apply, this, sub_self]
  have hBN : ∀ e f, M₀.B (τ e - e) (τ f - f) = 0 := fun e f => hperp e _ (hfix f)
  have hadd : ∀ e f, M₀.Qf (τ (e + f) - (e + f)) = M₀.Qf (τ e - e) + M₀.Qf (τ f - f) := by
    intro e f
    rw [show τ (e + f) - (e + f) = (τ e - e) + (τ f - f) by rw [map_add]; abel,
      M₀.Qf_add, hBN, add_zero]
  have hsmul : ∀ (c : K) e, M₀.Qf (τ (c • e) - c • e) = c ^ 2 * M₀.Qf (τ e - e) := by
    intro c e
    rw [show τ (c • e) - c • e = c • (τ e - e) by rw [map_smul, smul_sub], M₀.Qf_smul]
  have hfrob : ∀ c : K, (frobeniusEquiv K 2).symm (c ^ 2) = c := fun c => by
    have : (frobeniusEquiv K 2) c = c ^ 2 := by simp [frobeniusEquiv_apply, frobenius_def]
    rw [← this, RingEquiv.symm_apply_apply]
  let g : M₀.E →ₗ[K] K :=
    { toFun := fun e => (frobeniusEquiv K 2).symm (M₀.Qf (τ e - e))
      map_add' := fun e f => by rw [hadd, map_add]
      map_smul' := fun c e => by
        rw [hsmul, map_mul, hfrob]
        rfl }
  have hg : ∀ e, g e = (frobeniusEquiv K 2).symm (M₀.Qf (τ e - e)) := fun e => rfl
  intro e₀
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, ∀ e, M₀.B w e = g e :=
    ⟨(M₀.B.toDual hnd).symm g, fun e => M₀.B.apply_toDual_symm_apply g e⟩
  have hge₀ : g e₀ ≠ 0 := by
    rw [hg]
    intro h0
    exact hne (by simpa using h0)
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hge₀ (by rw [← hw e₀]; simp)
  refine hw0 (hc.eq_zero_of_fixed h35 hM t hline fun l hl S hS hSQ => ?_)
  have hSτ := hcomm l hl S hS
  have hSB := B_map_eq_of_Qf S hSQ
  have hgS : ∀ e, g (S e) = g e := fun e => by
    rw [hg, hg, show τ (S e) - S e = S (τ e - e) by rw [map_sub, hSτ], hSQ]
  refine sub_eq_zero.mp (M₀.nondeg _ fun f => ?_)
  obtain ⟨e', rfl⟩ := S.surjective f
  rw [map_sub, LinearMap.sub_apply, hSB, hw, hw, hgS, sub_self]

theorem Ctx.exists_not_mem_span_of_SLNat (hc : Ctx M Q Z B) {t : G} (hSL : SLNat hc t)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hK : Nat.card K = Nat.card Z) (w : M₀.E) :
    ∃ v ∈ M₀.img (Vt M (LB M Q B) B Z t), v ∉ Submodule.span K {w} := by
  by_contra hcon
  push Not at hcon
  obtain ⟨K', _, _, hK', d, hd, φ', hrange, -, hRN, hZn, ψ, hψ⟩ := hSL
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨ι, hιπ, hιi⟩ := exists_Vt_transport (M₀ := M₀) hVQ ψ
  have hψs : ∀ u, ∃ v : Vt M (LB M Q B) B Z t,
      Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = u := fun u => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd u))
    exact ⟨v, by rw [hv, ψ.apply_symm_apply, toAdd_ofAdd]⟩
  let F : (Fin d → K') → Submodule.span K {w} := fun u => ⟨ι u, by
    obtain ⟨v, rfl⟩ := hψs u
    rw [hιπ]
    exact hcon _ (M₀.pi_mem_img v.2 (hVQ v.2))⟩
  have hF : Function.Injective F := fun u u' h => by
    have h1 : ι u = ι u' := congrArg Subtype.val h
    have h0 : ι (u - u') = 0 := by rw [map_sub, h1, sub_self]
    exact sub_eq_zero.mp (hιi _ h0)
  have hsurj : Function.Surjective
      (fun c : K => (⟨c • w, Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)⟩ :
        Submodule.span K {w})) := by
    rintro ⟨_, hv⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨c, rfl⟩
  haveI : Finite (Submodule.span K {w}) := Finite.of_surjective _ hsurj
  have hcard1 := Nat.card_le_card_of_injective F hF
  have hcard2 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_fun, Nat.card_fin, hK'] at hcard1
  have hq := hc.hyp.q4
  have hpow : Nat.card Z ^ 2 ≤ Nat.card Z ^ d := Nat.pow_le_pow_right (by omega) hd
  nlinarith

theorem Ctx.isElemAbelian_Ut (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) (hSL : SLNat hc t) : CFSG.Open.IsElemAbelian 2 (Ut Q Z t) := by
  obtain ⟨n', γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp hM
  have ht := h.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htH := hc.LB_le_H0 ht
  obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
  set τ := φ ⟨t, htH⟩ with hτ
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨t, htH⟩ x hx
  have hτ2 : ∀ e, τ (τ e) = e := apply_apply_of_sq_eq_one (hc.actionHom_sq_eq_one φ hφQ ht)
  have h35 := (stroth_3_5 h34 hc h.width h.n_gt h.noA2 h.gen).2.1
  have hQf := hc.Qf_sub_eq_zero h35 hM t τ (hφiso _) hτ2
    (fun l hl S hS e => hc.hyp.comm_action (hc.Rt_le_M t hl) htM (hc.Rt_comm_mem_Q hl) hS hτπ e)
    (fun w => hc.exists_not_mem_span_of_SLNat hSL hM.card w)
  refine (M₀.isElemAbelian_iff hM.reg (hc.Ut_le_Q htM)).mpr fun e he => ?_
  obtain ⟨x, rfl⟩ := (mem_img_comm_zpowers_sup_iff M₀ hM.reg τ htQ1 htQ2 hτπ e).mp he
  simpa using hQf x

end Involution

section Centralizer

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem Ut_le_centralizer_of_sq {Q Z : Subgroup G} {t : G} (ht2 : t ^ 2 = 1)
    (hZ : ∀ z ∈ Z, t * z * t⁻¹ = z) (hU : ∀ u ∈ Ut Q Z t, u * u = 1) :
    Ut Q Z t ≤ Subgroup.centralizer ({t} : Set G) := by
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact ht2
  have hinv : t⁻¹ = t := mul_eq_one_iff_inv_eq.mp htt
  have hpow : ∀ k : ℤ, t ^ k = 1 ∨ t ^ k = t := by
    intro k
    induction k using Int.induction_on with
    | zero => exact Or.inl (zpow_zero t)
    | succ k ih =>
      rcases ih with h | h
      · exact Or.inr (by rw [zpow_add_one, h, one_mul])
      · exact Or.inl (by rw [zpow_add_one, h, htt])
    | pred k ih =>
      rcases ih with h | h
      · exact Or.inr (by rw [zpow_sub_one, h, one_mul, hinv])
      · exact Or.inl (by rw [zpow_sub_one, h]; simp)
  refine sup_le (Subgroup.commutator_le.mpr fun x hx s hs => ?_) fun z hz => ?_
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    rcases hpow k with h1 | h1
    · rw [h1]
      simp [commutatorElement_def]
    · rw [h1, Subgroup.mem_centralizer_singleton_iff]
      have hwmem : ⁅x, t⁆ ∈ Ut Q Z t :=
        Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t))
      have hsq : ⁅x, t⁆ * ⁅x, t⁆ = 1 := hU _ hwmem
      have hw : ⁅x, t⁆ = x * t * x⁻¹ * t := by
        rw [commutatorElement_def, hinv]
      have hwinv : ⁅x, t⁆⁻¹ = t * x * t * x⁻¹ := by
        rw [hw, show (x * t * x⁻¹ * t)⁻¹ = t⁻¹ * x * t⁻¹ * x⁻¹ by group, hinv]
      have hwself : ⁅x, t⁆⁻¹ = ⁅x, t⁆ := mul_eq_one_iff_inv_eq.mp hsq
      have h1' : t * ⁅x, t⁆ * t = ⁅x, t⁆ := by
        calc t * ⁅x, t⁆ * t = t * (t * x * t * x⁻¹) * t := by rw [← hwinv, hwself]
          _ = (t * t) * (x * t * x⁻¹ * t) := by group
          _ = ⁅x, t⁆ := by rw [htt, one_mul, hw]
      calc ⁅x, t⁆ * t = (t * t) * ⁅x, t⁆ * t := by rw [htt, one_mul]
        _ = t * (t * ⁅x, t⁆ * t) := by group
        _ = t * ⁅x, t⁆ := by rw [h1']
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * t = t * z * t⁻¹ * t := by rw [hZ z hz]
      _ = t * z := by group


theorem Ctx.Ut_le_centralizer (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) (hSL : SLNat hc t) (ht2 : t ^ 2 = 1) :
    Ut Q Z t ≤ Subgroup.centralizer ({t} : Set G) :=
  Ut_le_centralizer_of_sq ht2 (fun z hz => hc.LB_centralizes_Z h.mem z hz) fun u hu => by
    rw [← pow_two]
    exact (hc.isElemAbelian_Ut h34 h hSL).2 u hu

end Centralizer

section Model

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem fix_of_comm_range_le (τ S : M₀.E ≃ₗ[K] M₀.E) (Vs : AddSubgroup M₀.E)
    (hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f) (hSB : ∀ e f, M₀.B (S e) (S f) = M₀.B e f)
    (hτ2 : ∀ e, τ (τ e) = e) (hSτ : ∀ e, S (τ e) = τ (S e))
    (hVT : ∀ v ∈ Vs, ∃ w, (∀ v' ∈ Vs, M₀.B w v' = 0) ∧ τ w - w = v)
    (hcomm : ∀ e, S (τ e - e) - (τ e - e) ∈ Vs) : ∀ v ∈ Vs, S v = v := by
  have hadj : ∀ x w, M₀.B x (τ w - w) = M₀.B (τ x - x) w := fun x w => by
    have h1 : M₀.B x (τ w) = M₀.B (τ x) w := by
      have := hτB (τ x) w
      rwa [hτ2] at this
    rw [map_sub, map_sub M₀.B, LinearMap.sub_apply, h1]
  have hstep1 : ∀ e, ∀ v' ∈ Vs, M₀.B (S e - e) v' = 0 := by
    intro e v' hv'
    obtain ⟨w', hw', rfl⟩ := hVT v' hv'
    rw [hadj]
    have hx : τ (S e - e) - (S e - e) = S (τ e - e) - (τ e - e) := by
      rw [map_sub, ← hSτ e, map_sub]
      abel
    rw [hx, Tim79.QuadModel.B_comm, hw' _ (hcomm e), neg_zero]
  intro v hv
  refine sub_eq_zero.mp (M₀.nondeg _ fun f => ?_)
  obtain ⟨e', rfl⟩ := S.surjective f
  have h1 := hstep1 e' v hv
  rw [Tim79.QuadModel.B_comm, map_sub] at h1
  rw [map_sub, LinearMap.sub_apply, hSB]
  have h2 : M₀.B v (S e') = M₀.B v e' := by
    have : M₀.B v (S e') - M₀.B v e' = 0 := by
      have h3 := h1
      rw [neg_eq_zero] at h3
      exact h3
    exact sub_eq_zero.mp this
  rw [h2, sub_self]

end Model

section CN

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.mem_CN_of_comm_Ut_le_Vt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (h : Sec5Hyp hc n t) (hSL : SLNat hc t) {l : G} (hl : l ∈ Rt M (LB M Q B) t)
    (hcomm : ∀ u ∈ Ut Q Z t, ⁅u, l⁆ ∈ Vt M (LB M Q B) B Z t) : l ∈ hc.CN t := by
  refine ⟨hl, fun v hv => ?_⟩
  obtain ⟨n', γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp hM
  have ht := h.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htH := hc.LB_le_H0 ht
  have hlM : l ∈ M := hc.Rt_le_M t hl
  have hlH : l ∈ H0 M Z := hc.Rt_le_H0 t hl
  obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨hlQ1, hlQ2⟩ := hc.conj_mem_Q_of_mem_M hlM
  have hT2 := hc.actionHom_sq_eq_one φ hφQ ht
  set τ := φ ⟨t, htH⟩ with hτ
  set S := φ ⟨l, hlH⟩ with hS
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨t, htH⟩ x hx
  have hSπ : ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x) := fun x hx => hφπ ⟨l, hlH⟩ x hx
  have hτ2 : ∀ e, τ (τ e) = e := apply_apply_of_sq_eq_one hT2
  have hSτ : ∀ e, S (τ e) = τ (S e) := fun e =>
    hc.hyp.comm_action hlM htM (hc.Rt_comm_mem_Q hl) hSπ hτπ e
  have hτB := B_map_eq_of_Qf τ (hφiso _)
  have hSB := B_map_eq_of_Qf S (hφiso _)
  have h35 := (stroth_3_5 h34 hc h.width h.n_gt h.noA2 h.gen).2.1
  have hVT := hc.Vt_le_Tt_of_SLNat h h35 hSL
  have hVQ := hc.Vt_le_Q t
  have hVT' : ∀ x ∈ M₀.img (Vt M (LB M Q B) B Z t), ∃ w,
      (∀ v' ∈ M₀.img (Vt M (LB M Q B) B Z t), M₀.B w v' = 0) ∧ τ w - w = x := by
    intro x hx
    obtain ⟨y, hyV, hyQ, rfl⟩ := hx
    obtain ⟨w, hw, hwx⟩ := (hc.hyp.mem_img_Tt_iff φ hφπ (Vt M (LB M Q B) B Z t) ⟨t, htH⟩ hT2
      (e := M₀.π y)).mp (M₀.pi_mem_img (hVT hyV) hyQ)
    exact ⟨w, (mem_img_Wt_iff M₀ hM.reg hVQ).mp hw, by simpa using hwx⟩
  have hcomm' : ∀ e, S (τ e - e) - (τ e - e) ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have huQ : ⁅x, t⁆ ∈ Q := hc.comm_mem_Q htM hxQ
    have hcl := hcomm _ (comm_mem_Ut hxQ)
    have hπu : M₀.π ⁅x, t⁆ = M₀.π x - τ (M₀.π x) := pi_comm_eq_sub htQ1 hτπ hxQ
    have hlu : l * ⁅x, t⁆⁻¹ * l⁻¹ ∈ Q := hlQ1 _ (Q.inv_mem huQ)
    have hlQ : ⁅⁅x, t⁆, l⁆ ∈ Q := by
      rw [show ⁅⁅x, t⁆, l⁆ = ⁅x, t⁆ * (l * ⁅x, t⁆⁻¹ * l⁻¹) by
        simp only [commutatorElement_def]; group]
      exact Q.mul_mem huQ hlu
    have hπ : M₀.π ⁅⁅x, t⁆, l⁆ = S (τ (M₀.π x) - M₀.π x) - (τ (M₀.π x) - M₀.π x) := by
      rw [show ⁅⁅x, t⁆, l⁆ = ⁅x, t⁆ * (l * ⁅x, t⁆⁻¹ * l⁻¹) by
        simp only [commutatorElement_def]; group, M₀.π_mul _ huQ _ hlu,
        hSπ _ (Q.inv_mem huQ), M₀.pi_inv huQ, hπu]
      simp only [map_neg, map_sub]
      abel
    rw [← hπ]
    exact M₀.pi_mem_img hcl hlQ
  have hfix := fix_of_comm_range_le τ S (M₀.img (Vt M (LB M Q B) B Z t)) hτB hSB hτ2 hSτ hVT'
    hcomm' (M₀.π v) (M₀.pi_mem_img hv (hVQ hv))
  have hvQ := hVQ hv
  have hlvQ : l * v * l⁻¹ ∈ Q := hlQ1 v hvQ
  have hcQ : ⁅l, v⁆ ∈ Q := by
    rw [show ⁅l, v⁆ = (l * v * l⁻¹) * v⁻¹ by rw [commutatorElement_def]]
    exact Q.mul_mem hlvQ (Q.inv_mem hvQ)
  refine (M₀.π_ker _ hcQ).mp ?_
  rw [show ⁅l, v⁆ = (l * v * l⁻¹) * v⁻¹ by rw [commutatorElement_def],
    M₀.π_mul _ hlvQ _ (Q.inv_mem hvQ), hSπ v hvQ, hfix, M₀.pi_inv hvQ, add_neg_cancel]

end CN

end CFSG.RankThree.GF2n.Stroth80
