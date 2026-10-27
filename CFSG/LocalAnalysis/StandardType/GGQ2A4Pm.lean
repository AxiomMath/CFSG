module

public import CFSG.LocalAnalysis.StandardType.GGQ2A4Refl
public import CFSG.LocalAnalysis.StandardType.GGQ2HypLin
public import CFSG.LocalAnalysis.StandardType.GGQ2HypStab
import Mathlib.Data.Finset.Sum

public section

namespace CFSG.StandardType

open Module QTwoLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem ggQ2A4Pm_refl_fixed_iff {c : V} {φ : Dual (ZMod 3) V} (h : φ c = 2) {v : V} :
    Module.reflection h v = v ↔ φ v = 0 := by
  have htwo : (2 : ZMod 3) ≠ 0 := by decide
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, map_zero] at h
    exact htwo h.symm
  constructor
  · intro hv
    rw [Module.reflection_apply] at hv
    have hz : φ v • c = 0 := sub_eq_self.mp hv
    exact (smul_eq_zero.mp hz).resolve_right hc
  · intro hv
    rw [Module.reflection_apply, hv, zero_smul, sub_zero]

private theorem ggQ2A4Pm_reflGp_span (K : GGQ2A4Conf V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (h : ∀ t ∈ A, IsReflLin t → t K.x ∈ Submodule.span (ZMod 3) {K.x}) :
    ∀ r ∈ reflGp A, r K.x ∈ Submodule.span (ZMod 3) {K.x} := by
  have hx0 : K.x ≠ 0 := by
    intro h0
    exact K.x_notMem (by rw [h0]; exact Submodule.zero_mem K.H)
  intro r hr
  rw [reflGp] at hr
  refine Subgroup.closure_induction (p := fun r _ => r K.x ∈ Submodule.span (ZMod 3) {K.x})
    (fun t ht => h t ht.1 ht.2) ?_ ?_ ?_ hr
  · exact Submodule.mem_span_singleton_self K.x
  · intro x y hx hy ihx ihy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ihy
    rw [LinearEquiv.mul_apply, ← hc, map_smul]
    exact Submodule.smul_mem _ c ihx
  · intro x hx ihx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ihx
    have hc0 : c ≠ 0 := by
      intro hc0
      have hzero : x K.x = 0 := by rw [← hc, hc0, zero_smul]
      exact hx0 (x.injective (by rw [hzero, map_zero]))
    have hxinv : x⁻¹ K.x = c⁻¹ • K.x := by
      apply x.injective
      rw [show x (x⁻¹ K.x) = K.x from by simp]
      rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hxinv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self K.x)

theorem ggQ2A4_pm_branch3 (K : GGQ2A4Conf V) (hF : K.Full) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (hsA : ∀ i, K.s i ∈ A)
    (hRH : ∀ r ∈ reflGp A, ∀ h ∈ K.H, r h ∈ K.H)
    (hRx : ¬ ∀ r ∈ reflGp A, r K.x ∈ Submodule.span (ZMod 3) {K.x}) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a K.x = ε • r K.x := by
  classical
  have : Module.Finite (ZMod 3) V := K.finite hF
  have hsR : ∀ i, K.s i ∈ reflGp A := fun i => Subgroup.subset_closure ⟨hsA i, K.s_isRefl i⟩
  have h2 : 2 ≤ Module.finrank (ZMod 3) K.H := by
    rw [K.finrank_H]
    norm_num
  have hcen : ∀ (c₀ : V) (φ : Dual (ZMod 3) V) (hφ : φ c₀ = 2),
      Module.reflection hφ ∈ A → c₀ ∈ K.H := by
    intro c₀ φ hφ ht
    have h := ggQ2Hyp_refl_move (V := V) (ι := Fin 4) A hTF K.c K.α K.coroot_two K.s K.s_apply
      hsR K.x (K.hfix hF) K.hconn h2 (K.hhyp hF) hRH hRx (Module.reflection hφ) ht
      ⟨c₀, φ, hφ, rfl⟩ c₀
    rw [Module.reflection_apply, hφ] at h
    have htwo : (2 : ZMod 3) • c₀ = -c₀ := by
      rw [show (2 : ZMod 3) = -1 by decide]
      exact neg_one_smul (ZMod 3) c₀
    rw [htwo] at h
    have heq : c₀ - -c₀ - c₀ = c₀ := by abel
    rwa [heq] at h
  have hneg : ∀ r ∈ reflGp A, ¬ ∀ h ∈ K.H, r h = -h := fun r hr =>
    ggQ2Hyp_R_not_neg (V := V) (ι := Fin 4) A hTF K.c K.α K.coroot_two K.s K.s_apply hsR K.x
      (K.hfix hF) K.hconn h2 (K.hhyp hF) hRH hRx r hr
  have ht0 : ∃ t ∈ A, IsReflLin t ∧ t K.x ∉ Submodule.span (ZMod 3) {K.x} := by
    by_contra hcon
    apply hRx
    intro r hr
    exact ggQ2A4Pm_reflGp_span K A (by
      intro t ht hrefl
      by_contra htx
      exact hcon ⟨t, ht, hrefl, htx⟩) r hr
  obtain ⟨t0, ht0A, ht0Refl, ht0x⟩ := ht0
  rcases ggQ2A4_refl_classify K A hTF hsA hcen hneg ht0A ht0Refl with
    ⟨γ0, hγ0⟩ | ⟨k0, ψ0, hψ0, hψ0H, hψ0eq⟩
  · exfalso
    apply ht0x
    rw [hγ0, K.rootRefl_x γ0]
    exact Submodule.mem_span_singleton_self K.x
  · have hψ0A : Module.reflection hψ0 ∈ A := by rwa [← hψ0eq]
    set μ : ZMod 3 := ψ0 K.x with hμdef
    have hμ : μ ≠ 0 := by
      intro hμ0
      apply ht0x
      rw [hψ0eq, Module.reflection_apply, ← hμdef, hμ0, zero_smul, sub_zero]
      exact Submodule.mem_span_singleton_self K.x
    have hExt : ∀ k : Fin 5, ∃ (ψ : Dual (ZMod 3) V) (hψ : ψ (K.κ (ggA4F k)) = 2),
        (∀ n, ψ (K.κ n) = ggA4B (ggA4F k) n) ∧ ψ K.x = μ ∧ Module.reflection hψ ∈ A :=
      fun k => ggQ2A4_ext_all K A hsA hψ0 hψ0H hψ0A k
    choose ψ hψ hψH hψx htψ using hExt
    intro a ha
    obtain ⟨l0, n0, hl0⟩ := K.decomp hF (a K.x)
    have hl0ne : l0 ≠ 0 := by
      intro hl0z
      apply K.x_notMem
      have hm : a K.x = K.κ n0 := by rw [hl0, hl0z, zero_smul, zero_add]
      have hmem := ggQ2Hyp_A_stab A K.c K.α K.s K.s_apply hsR K.x (K.hfix hF) K.hconn h2 hRH
        a⁻¹ (A.inv_mem ha) (K.κ n0) (K.κ_mem_H n0)
      have hx : K.x = a⁻¹ (K.κ n0) := by
        rw [← hm]
        simp
      rw [hx]
      exact hmem
    let n : Fin 4 → ZMod 3 := l0⁻¹ • n0
    let v : V := K.x + K.κ n
    have hav : a K.x = l0 • v := by
      rw [hl0]
      change l0 • K.x + K.κ n0 = l0 • (K.x + K.κ n)
      have hκ : K.κ n = l0⁻¹ • K.κ n0 := K.κ.map_smul l0⁻¹ n0
      rw [hκ, smul_add, smul_smul, mul_inv_cancel₀ hl0ne, one_smul]
    have htfun_mem : ∀ γ : Fin 10, a * K.rootRefl γ * a⁻¹ ∈ A := by
      intro γ
      exact A.mul_mem (A.mul_mem ha (K.rootRefl_mem hsA γ)) (A.inv_mem ha)
    have htfun_refl : ∀ γ : Fin 10, IsReflLin (a * K.rootRefl γ * a⁻¹) := by
      intro γ
      exact ggQ2_isReflLin_conj a (K.rootRefl γ) (K.rootRefl_isRefl γ)
    have htfun_fix : ∀ γ : Fin 10, (a * K.rootRefl γ * a⁻¹) v = v := by
      intro γ
      have h1 : (a * K.rootRefl γ * a⁻¹) (a K.x) = a K.x := by
        simp [K.rootRefl_x γ]
      have h2 : v = l0⁻¹ • (a K.x) := by
        rw [hav, smul_smul, inv_mul_cancel₀ hl0ne, one_smul]
      rw [h2, map_smul, h1, ← h2]
    let Groot : Finset (Fin 10) :=
      Finset.univ.filter (fun δ => ggA4B (ggA4Root δ) n = 0)
    let Gext : Finset (Fin 5) :=
      Finset.univ.filter (fun k => μ + ggA4B (ggA4F k) n = 0)
    have hex : ∀ γ : Fin 10, ∃ s : Fin 10 ⊕ Fin 5,
        s ∈ Groot.disjSum Gext ∧
        (∀ δ : Fin 10, s = Sum.inl δ → a * K.rootRefl γ * a⁻¹ = K.rootRefl δ) ∧
        (∀ k : Fin 5, s = Sum.inr k →
          a * K.rootRefl γ * a⁻¹ = Module.reflection (hψ k)) := by
      intro γ
      have htA := htfun_mem γ
      have htR := htfun_refl γ
      have hfv := htfun_fix γ
      rcases ggQ2A4_refl_classify K A hTF hsA hcen hneg htA htR with
        ⟨δ, hδ⟩ | ⟨k, ψk, hψk, hψkH, hδ⟩
      · have hB : ggA4B (ggA4Root δ) n = 0 := by
          have hfixroot : K.rootRefl δ v = v := by rw [← hδ]; exact hfv
          have h0 : K.rootFun δ v = 0 :=
            (ggQ2A4Pm_refl_fixed_iff (K.rootFun_rootVec δ)).mp hfixroot
          change K.rootFun δ (K.x + K.κ n) = 0 at h0
          rw [map_add, K.rootFun_x δ, zero_add, K.rootFun_κ δ] at h0
          exact h0
        refine ⟨Sum.inl δ, ?_, ?_, ?_⟩
        · rw [Finset.inl_mem_disjSum]
          change δ ∈ Finset.univ.filter (fun δ => ggA4B (ggA4Root δ) n = 0)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩
        · intro δ' h
          rw [Sum.inl.injEq] at h
          rw [← h]
          exact hδ
        · intro k' h
          exact absurd h (by simp)
      · have hψeq : ψk = ψ k :=
          ggQ2A4_ext_eq K A hTF hψk (hψ k) (by rw [← hδ]; exact htA) (htψ k)
        subst hψeq
        have hB : μ + ggA4B (ggA4F k) n = 0 := by
          have hfixk : Module.reflection hψk v = v := by rw [← hδ]; exact hfv
          have h0 : ψ k v = 0 := (ggQ2A4Pm_refl_fixed_iff hψk).mp hfixk
          have h2' : ψ k v = μ + ggA4B (ggA4F k) n := by
            change ψ k (K.x + K.κ n) = μ + ggA4B (ggA4F k) n
            rw [map_add, hψkH n, hψx k]
          rw [h2'] at h0
          exact h0
        refine ⟨Sum.inr k, ?_, ?_, ?_⟩
        · rw [Finset.inr_mem_disjSum]
          change k ∈ Finset.univ.filter (fun k => μ + ggA4B (ggA4F k) n = 0)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩
        · intro δ' h
          exact absurd h (by simp)
        · intro k' h
          rw [Sum.inr.injEq] at h
          rw [← h, hδ]
    choose q hqmem hqroot hqext using hex
    have hinj : Function.Injective q := by
      have hcancel : ∀ γ γ' : Fin 10,
          a * K.rootRefl γ * a⁻¹ = a * K.rootRefl γ' * a⁻¹ → γ = γ' := by
        intro γ γ' h
        have hroot : K.rootRefl γ = K.rootRefl γ' := by
          have h4 : a⁻¹ * (a * K.rootRefl γ * a⁻¹) * a =
              a⁻¹ * (a * K.rootRefl γ' * a⁻¹) * a := by rw [h]
          have e1 : a⁻¹ * (a * K.rootRefl γ * a⁻¹) * a = K.rootRefl γ := by group
          have e2 : a⁻¹ * (a * K.rootRefl γ' * a⁻¹) * a = K.rootRefl γ' := by group
          rw [e1, e2] at h4
          exact h4
        apply ggA4_root_inj
        intro k
        have hk := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (K.κ (Pi.single k 1))) hroot
        have h1 : K.rootRefl γ (K.κ (Pi.single k 1)) =
            K.κ (ggA4RAct 1 (ggA4Root γ) (Pi.single k 1)) := by
          change Module.reflection (K.rootFun_rootVec γ) (K.κ (Pi.single k 1)) = _
          exact K.refl_κ (m := ggA4Root γ) (φ := K.rootFun γ) (ε := 1)
            (K.rootFun_rootVec γ) (fun n => by rw [K.rootFun_κ]; ring) (Pi.single k 1)
        have h2 : K.rootRefl γ' (K.κ (Pi.single k 1)) =
            K.κ (ggA4RAct 1 (ggA4Root γ') (Pi.single k 1)) := by
          change Module.reflection (K.rootFun_rootVec γ') (K.κ (Pi.single k 1)) = _
          exact K.refl_κ (m := ggA4Root γ') (φ := K.rootFun γ') (ε := 1)
            (K.rootFun_rootVec γ') (fun n => by rw [K.rootFun_κ]; ring) (Pi.single k 1)
        rw [h1, h2] at hk
        exact K.κ_injective hk
      intro γ γ' heq
      apply hcancel γ γ'
      rcases hq : q γ with δ | k
      · have h1 := hqroot γ δ hq
        have h2' := hqroot γ' δ (by rw [← heq]; exact hq)
        rw [h1, h2']
      · have h1 := hqext γ k hq
        have h2' := hqext γ' k (by rw [← heq]; exact hq)
        rw [h1, h2']
    have hcard : 10 ≤ Groot.card + Gext.card := by
      have hle := Finset.card_le_card_of_injOn q
        (s := (Finset.univ : Finset (Fin 10))) (t := Groot.disjSum Gext)
        (by intro γ _; exact hqmem γ) (by intro γ _ γ' _ h; exact hinj h)
      simpa [Finset.card_disjSum] using hle
    have hline : n = 0 ∨ ∃ k : Fin 5, n = -(μ • ggA4F k) :=
      ggA4_line_check μ hμ n (by simpa [Groot, Gext] using hcard)
    rcases hline with hn | ⟨k, hn⟩
    · refine ⟨1, Subgroup.one_mem _, l0, hl0ne, ?_⟩
      rw [hav]
      have hv : v = K.x := by
        change K.x + K.κ n = K.x
        rw [hn, map_zero, add_zero]
      rw [hv]
      rfl
    · refine ⟨Module.reflection (hψ k), ?_, l0, hl0ne, ?_⟩
      · exact Subgroup.subset_closure ⟨htψ k, ⟨K.κ (ggA4F k), ψ k, hψ k, rfl⟩⟩
      · rw [hav]
        have hv : v = Module.reflection (hψ k) K.x := by
          change K.x + K.κ n = Module.reflection (hψ k) K.x
          rw [Module.reflection_apply, hψx k]
          have hκn : K.κ n = -(μ • K.κ (ggA4F k)) := by
            rw [hn]
            exact (LinearMap.map_neg K.κ (μ • ggA4F k)).trans
              (congrArg Neg.neg (LinearMap.map_smul K.κ μ (ggA4F k)))
          rw [hκn, sub_eq_add_neg]
        rw [hv]

theorem ggQ2A4_pm (K : GGQ2A4Conf V) (hF : K.Full) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (hsA : ∀ i, K.s i ∈ A)
    (hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A)) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a K.x = ε • r K.x := by
  have : Module.Finite (ZMod 3) V := K.finite hF
  have hsR : ∀ i, K.s i ∈ reflGp A := fun i => Subgroup.subset_closure ⟨hsA i, K.s_isRefl i⟩
  have h2 : 2 ≤ Module.finrank (ZMod 3) K.H := by
    rw [K.finrank_H]
    norm_num
  by_cases hRxAll : ∀ r ∈ reflGp A, r K.x ∈ Submodule.span (ZMod 3) {K.x}
  · intro a ha
    have hline : a K.x ∈ Submodule.span (ZMod 3) {K.x} :=
      ggQ2Hyp_line_of_R A K.c K.α K.s K.s_apply hsR K.x (K.hfix hF) K.hconn h2 hRxAll a ha
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    by_cases hx0 : K.x = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      simp [hx0]
    · rw [Submodule.mem_span_singleton] at hline
      obtain ⟨ε, hε⟩ := hline
      refine ⟨ε, ?_, hε.symm⟩
      intro hε0
      apply hx0
      have hz : a K.x = 0 := by rw [← hε, hε0, zero_smul]
      exact a.injective (by rw [hz, map_zero])
  · by_cases hRH : ∀ r ∈ reflGp A, ∀ h ∈ K.H, r h ∈ K.H
    · intro a ha
      exact ggQ2A4_pm_branch3 K hF A hTF hsA hRH hRxAll a ha
    · intro a ha
      exact absurd
        (ggQ2Hyp_absIrred A K.c K.α K.coroot_two K.s K.s_apply hsR K.x (K.hfix hF) K.hconn
          (K.hhyp hF) hRH hRxAll) hNotAbs

end CFSG.StandardType

end
