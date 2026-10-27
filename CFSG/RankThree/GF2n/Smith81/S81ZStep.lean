module

public import CFSG.RankThree.GF2n.Smith81.S81ZLayE

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X
open scoped commutatorElement


variable {K : Type} [Field K] {R : Finset Rt} {f : (Fin (Tag.rank .E7) → ℤ) →+ ℤ}

section Quot

variable (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) (hR : Closed R) [CharP K 2]
  {E : Subgroup (Gp K)}

@[expose] def Epr (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) (hR : Closed R)
    (E : Subgroup (Gp K)) : Subgroup (Gp K) :=
  (E.subgroupOf (URge K R 1)).map (projHom hf hR)

theorem mem_Epr {y : Gp K} :
    y ∈ Epr hf hR E ↔ ∃ (e : Gp K) (he : e ∈ URge K R 1), e ∈ E ∧ prC hf hR ⟨e, he⟩ = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, x.2, hx, rfl⟩
  · rintro ⟨e, he, heE, rfl⟩
    exact ⟨⟨e, he⟩, heE, rfl⟩

theorem Epr_le : Epr hf hR E ≤ URge K (Rp f R) 1 := by
  intro y hy
  obtain ⟨e, he, -, rfl⟩ := (mem_Epr hf hR).1 hy
  exact prC_mem hf hR _

theorem prC_conj_tau (t : Tt K) (g : ↥(URge K R 1)) :
    prC hf hR ⟨tau t * g.1 * (tau t)⁻¹, conj_tau_mem_URge hR t g.2⟩ =
      tau t * prC hf hR g * (tau t)⁻¹ := by
  obtain ⟨v, hv, h⟩ := prC_spec hf hR g
  refine prC_eq hf hR _ (u := tau t * prC hf hR g * (tau t)⁻¹) (v := tau t * v * (tau t)⁻¹)
    (conj_tau_mem_URge (closed_Rp hR) t (prC_mem hf hR g))
    (conj_tau_mem_URge (closed_Rn hf hR) t hv) ?_
  show tau t * g.1 * (tau t)⁻¹ = _
  rw [h]
  group

theorem prC_conj_Rp {u₀ : Gp K} (hu₀ : u₀ ∈ URge K (Rp f R) 1) (g : ↥(URge K R 1)) :
    prC hf hR ⟨u₀ * g.1 * u₀⁻¹, conj_mem_URge hR (URge_mono_R (Rp_subset R) hu₀) g.2⟩ =
      u₀ * prC hf hR g * u₀⁻¹ := by
  obtain ⟨v, hv, h⟩ := prC_spec hf hR g
  refine prC_eq hf hR _ (u := u₀ * prC hf hR g * u₀⁻¹) (v := u₀ * v * u₀⁻¹)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu₀ (prC_mem hf hR g)) (Subgroup.inv_mem _ hu₀))
    (UN_normal hf hR (URge_mono_R (Rp_subset R) hu₀) hv) ?_
  show u₀ * g.1 * u₀⁻¹ = _
  rw [h]
  group

theorem isStab_Epr (hE : IsStab R E) : IsStab (Rp f R) (Epr hf hR E) where
  le := Epr_le hf hR
  tau t y hy := by
    obtain ⟨e, he, heE, rfl⟩ := (mem_Epr hf hR).1 hy
    refine (mem_Epr hf hR).2 ⟨tau t * e * (tau t)⁻¹, conj_tau_mem_URge hR t he,
      hE.tau t e heE, ?_⟩
    exact prC_conj_tau hf hR t ⟨e, he⟩
  norm u hu y hy := by
    obtain ⟨e, he, heE, rfl⟩ := (mem_Epr hf hR).1 hy
    refine (mem_Epr hf hR).2 ⟨u * e * u⁻¹, conj_mem_URge hR (URge_mono_R (Rp_subset R) hu) he,
      hE.norm u (URge_mono_R (Rp_subset R) hu) e heE, ?_⟩
    exact prC_conj_Rp hf hR hu ⟨e, he⟩
  comm y hy y' hy' := by
    obtain ⟨e, he, heE, rfl⟩ := (mem_Epr hf hR).1 hy
    obtain ⟨e', he', heE', rfl⟩ := (mem_Epr hf hR).1 hy'
    have : (⟨e, he⟩ : ↥(URge K R 1)) * ⟨e', he'⟩ = ⟨e', he'⟩ * ⟨e, he⟩ :=
      Subtype.ext (hE.comm e heE e' heE')
    have h2 := congrArg (prC hf hR) this
    rw [prC_mul hf hR, prC_mul hf hR] at h2
    exact h2

end Quot

section Phi

variable [CharP K 2]

@[expose] def PhiL (L : List (Tt K)) (e : Gp K) : Gp K := (L.map fun t => tau t * e * (tau t)⁻¹).prod

@[expose] def PhiS (S : Finset (Tt K)) (e : Gp K) : Gp K := PhiL S.toList e

theorem PhiL_nil (e : Gp K) : PhiL ([] : List (Tt K)) e = 1 := rfl

theorem PhiL_cons (t : Tt K) (L : List (Tt K)) (e : Gp K) :
    PhiL (t :: L) e = (tau t * e * (tau t)⁻¹) * PhiL L e := by
  simp [PhiL]

theorem PhiL_mem_URge (hR : Closed R) {h : ℕ} {e : Gp K} (he : e ∈ URge K R h) (L : List (Tt K)) :
    PhiL L e ∈ URge K R h := by
  induction L with
  | nil => exact Subgroup.one_mem _
  | cons t L ih => rw [PhiL_cons]; exact Subgroup.mul_mem _ (conj_tau_mem_URge hR t he) ih

theorem PhiL_mem {E : Subgroup (Gp K)} (hE : IsStab R E) {e : Gp K} (he : e ∈ E) (L : List (Tt K)) :
    PhiL L e ∈ E := by
  induction L with
  | nil => exact E.one_mem
  | cons t L ih => rw [PhiL_cons]; exact E.mul_mem (hE.tau t e he) ih

theorem layCoord_PhiL (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (e : ↥(URge K R h)) (L : List (Tt K))
    (hmem : PhiL L e.1 ∈ URge K R h) :
    layCoord hR hh ⟨PhiL L e.1, hmem⟩ =
      fun α => (L.map fun t => ((chi α.1 t : Kˣ) : K)).sum * layCoord hR hh e α := by
  induction L with
  | nil =>
    have : (⟨PhiL ([] : List (Tt K)) e.1, hmem⟩ : ↥(URge K R h)) = 1 := Subtype.ext rfl
    rw [this, layCoord_one]
    funext α
    simp
  | cons t L ih =>
    have hP : PhiL L e.1 ∈ URge K R h := PhiL_mem_URge hR e.2 L
    have hconj : tau t * e.1 * (tau t)⁻¹ ∈ URge K R h := conj_tau_mem_URge hR t e.2
    have hsplit : (⟨PhiL (t :: L) e.1, hmem⟩ : ↥(URge K R h)) = ⟨_, hconj⟩ * ⟨PhiL L e.1, hP⟩ :=
      Subtype.ext (PhiL_cons t L e.1)
    rw [hsplit, layCoord_mul, ih hP]
    have h1 := congrArg Multiplicative.toAdd (layHom_conj_tau hR hh t e)
    have h2 : layCoord hR hh ⟨tau t * e.1 * (tau t)⁻¹, hconj⟩ =
        fun α : ↥(Lay R h) => ((chi α.1 t : Kˣ) : K) * layCoord hR hh e α := h1
    rw [h2]
    funext α
    simp only [Pi.add_apply, List.map_cons, List.sum_cons]
    ring

theorem layCoord_PhiS (hR : Closed R) {h : ℕ} (hh : 1 ≤ h) (e : ↥(URge K R h)) (S : Finset (Tt K))
    (hmem : PhiS S e.1 ∈ URge K R h) :
    layCoord hR hh ⟨PhiS S e.1, hmem⟩ =
      fun α => (∑ t ∈ S, ((chi α.1 t : Kˣ) : K)) * layCoord hR hh e α := by
  have := layCoord_PhiL hR hh e S.toList hmem
  refine this.trans ?_
  funext α
  rw [Finset.sum_map_toList S (fun t => ((chi α.1 t : Kˣ) : K))]

theorem PhiS_mem_Eh_succ (hR : Closed R) {E : Subgroup (Gp K)} {h : ℕ} (hh : 1 ≤ h)
    (S : Finset (Tt K))
    (hS : ∀ α ∈ R, InA hR E α → ∑ t ∈ S, ((chi α t : Kˣ) : K) = 0) {e : Gp K}
    (he : e ∈ Eh E R h) (hE : IsStab R E) : PhiS S e ∈ Eh E R (h + 1) := by
  have hmemU : PhiS S e ∈ URge K R h := PhiL_mem_URge hR he.2 _
  have hmemE : PhiS S e ∈ E := PhiL_mem hE he.1 _
  refine ⟨hmemE, ?_⟩
  have hco := layCoord_PhiS hR hh ⟨e, he.2⟩ S hmemU
  have h0 : layCoord hR hh ⟨PhiS S e, hmemU⟩ = 0 := by
    rw [hco]
    funext α
    by_cases hc : layCoord hR hh ⟨e, he.2⟩ α = 0
    · simp [hc]
    · have hα : α ∈ Ah hR hh E := by
        rw [mem_Ah]
        exact ⟨layCoord hR hh ⟨e, he.2⟩, mem_Sh.2 ⟨⟨e, he⟩, rfl⟩, hc⟩
      have hInA : InA hR E α.1 := ⟨h, hh, α.2, hα⟩
      rw [hS α.1 (mem_Lay.1 α.2).1 hInA]
      simp
  have : layHom hR hh ⟨PhiS S e, hmemU⟩ = 1 := by
    rw [layHom_apply, h0]
    rfl
  exact (layHom_eq_one_iff hR hh _).1 this

theorem PhiS_iter_mem (hR : Closed R) {E : Subgroup (Gp K)} (hE : IsStab R E) (S : Finset (Tt K))
    (hS : ∀ α ∈ R, InA hR E α → ∑ t ∈ S, ((chi α t : Kˣ) : K) = 0) {e : Gp K} (he : e ∈ E) :
    ∀ n : ℕ, (PhiS S)^[n] e ∈ Eh E R (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id]
    rw [zero_add, Eh_one hE]
    exact he
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact PhiS_mem_Eh_succ hR (Nat.succ_pos n) S hS ih hE

theorem PhiS_fix (hR : Closed R) {E : Subgroup (Gp K)} (hE : IsStab R E) {h : ℕ} (hh : 1 ≤ h)
    (S : Finset (Tt K)) (hS : ∀ α ∈ R, ∑ t ∈ S, ((chi α t : Kˣ) : K) = 1) {e : Gp K}
    (he : e ∈ Eh E R h) (htop : Eh E R (h + 1) = ⊥) : PhiS S e = e := by
  have hmemU : PhiS S e ∈ URge K R h := PhiL_mem_URge hR he.2 _
  have hmemE : PhiS S e ∈ E := PhiL_mem hE he.1 _
  have hco := layCoord_PhiS hR hh ⟨e, he.2⟩ S hmemU
  have h1 : layCoord hR hh ⟨PhiS S e, hmemU⟩ = layCoord hR hh ⟨e, he.2⟩ := by
    rw [hco]
    funext α
    rw [hS α.1 (mem_Lay.1 α.2).1, one_mul]
  have h2 : layHom hR hh (⟨PhiS S e, hmemU⟩⁻¹ * ⟨e, he.2⟩) = 1 := by
    rw [map_mul, map_inv, layHom_apply, layHom_apply, h1]
    simp
  have h3 := (layHom_eq_one_iff hR hh _).1 h2
  have h4 : (PhiS S e)⁻¹ * e ∈ Eh E R (h + 1) := ⟨E.mul_mem (E.inv_mem hmemE) he.1, h3⟩
  rw [htop, Subgroup.mem_bot] at h4
  exact (inv_mul_eq_one.1 h4)

theorem prC_PhiL (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) (hR : Closed R)
    (g : ↥(URge K R 1)) (L : List (Tt K)) (hmem : PhiL L g.1 ∈ URge K R 1) :
    prC hf hR ⟨PhiL L g.1, hmem⟩ = PhiL L (prC hf hR g) := by
  induction L with
  | nil =>
    have : (⟨PhiL ([] : List (Tt K)) g.1, hmem⟩ : ↥(URge K R 1)) = 1 := Subtype.ext rfl
    rw [this, PhiL_nil]
    exact (projHom hf hR).map_one
  | cons t L ih =>
    have hP : PhiL L g.1 ∈ URge K R 1 := PhiL_mem_URge hR g.2 L
    have hconj : tau t * g.1 * (tau t)⁻¹ ∈ URge K R 1 := conj_tau_mem_URge hR t g.2
    have hsplit : (⟨PhiL (t :: L) g.1, hmem⟩ : ↥(URge K R 1)) = ⟨_, hconj⟩ * ⟨PhiL L g.1, hP⟩ :=
      Subtype.ext (PhiL_cons t L g.1)
    rw [hsplit, prC_mul hf hR, prC_conj_tau hf hR t g, ih hP, PhiL_cons]

theorem E_le_Rn (hf : ∀ γ ∈ R, f γ = 0 ∨ f γ = 1) (hR : Closed R)
    {E : Subgroup (Gp K)} (hE : IsStab R E) (hC : Chars K R) {H : ℕ} (hH : ∀ α ∈ R, ht α ≤ H)
    (hA : ∀ α, InA hR E α → f α = 1) : E ≤ URge K (Rn f R) 1 := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_char_sum (ι := ↥R) (fun α => chi (K := K) α.1)
    (fun α => hC.surj α.1 α.2)
    (fun α β hαβ σ => hC.ne α.1 α.2 β.1 β.2 (fun e => hαβ (Subtype.ext e)) σ)
    (fun α => if InA hR E α.1 then 0 else 1)
  have hS0 : ∀ α ∈ R, InA hR E α → ∑ t ∈ S, ((chi α t : Kˣ) : K) = 0 := by
    intro α hα hInA
    have := hS ⟨α, hα⟩
    rwa [if_pos hInA] at this
  have hS1 : ∀ β ∈ Rp f R, ∑ t ∈ S, ((chi β t : Kˣ) : K) = 1 := by
    intro β hβ
    obtain ⟨hβR, hβ0⟩ := Finset.mem_filter.1 hβ
    have hnot : ¬ InA hR E β := fun h => by have := hA β h; omega
    have := hS ⟨β, hβR⟩
    rwa [if_neg hnot] at this
  have hnil : ∀ e ∈ E, (PhiS S)^[H] e = 1 := by
    intro e he
    have h1 := PhiS_iter_mem hR hE S hS0 he H
    have hbot : Eh E R (H + 1) = ⊥ := by
      unfold Eh
      rw [URge_eq_bot hH]
      simp
    rw [hbot, Subgroup.mem_bot] at h1
    exact h1
  have hE'' := isStab_Epr hf hR (E := E) hE
  have hC'' : Chars K (Rp f R) :=
    ⟨fun α hα => hC.surj α (Rp_subset R hα),
     fun α hα β hβ hαβ σ => hC.ne α (Rp_subset R hα) β (Rp_subset R hβ) hαβ σ⟩
  have hH'' : ∀ α ∈ Rp f R, ht α ≤ H := fun α hα => hH α (Rp_subset R hα)
  have hbot'' : Epr hf hR E = ⊥ := by
    by_contra hne
    have hRp : Closed (Rp f R) := closed_Rp hR
    have hex : ∃ n : ℕ, Eh (Epr hf hR E) (Rp f R) (n + 2) = ⊥ := by
      refine ⟨H, ?_⟩
      unfold Eh
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ URge K (Rp f R) (H + 1) := URge_anti (by omega) hx.2
      rw [URge_eq_bot hH''] at h1
      have h2 : x = 1 := h1
      rw [h2]
      exact Subgroup.one_mem _
    classical
    set n₀ := Nat.find hex with hn₀def
    have hn₀ : Eh (Epr hf hR E) (Rp f R) (n₀ + 2) = ⊥ := Nat.find_spec hex
    have hlayer : Eh (Epr hf hR E) (Rp f R) (n₀ + 1) ≠ ⊥ := by
      rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
      · rw [h0, zero_add, Eh_one hE'']
        exact hne
      · obtain ⟨k, hk⟩ : ∃ k, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
        have := Nat.find_min hex (m := k) (by omega)
        rw [show n₀ + 1 = k + 2 by omega]
        exact this
    obtain ⟨e'', hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hlayer
    have he''1 : (e'' : Gp K) ∈ Eh (Epr hf hR E) (Rp f R) (n₀ + 1) := e''.2
    have hfix : PhiS S (e'' : Gp K) = e'' :=
      PhiS_fix hRp hE'' (Nat.succ_pos n₀) S (fun β hβ => hS1 β hβ) he''1 hn₀
    obtain ⟨e, he, heE, hpre⟩ := (mem_Epr hf hR).1 he''1.1
    have hiter : ∀ n : ℕ, ∃ hm : (PhiS S)^[n] e ∈ URge K R 1,
        prC hf hR ⟨(PhiS S)^[n] e, hm⟩ = (PhiS S)^[n] (prC hf hR ⟨e, he⟩) := by
      intro n
      induction n with
      | zero => exact ⟨he, rfl⟩
      | succ n ih =>
        obtain ⟨hm, hEq⟩ := ih
        have hm' : (PhiS S)^[n + 1] e ∈ URge K R 1 := by
          rw [Function.iterate_succ_apply']
          exact PhiL_mem_URge hR hm _
        refine ⟨hm', ?_⟩
        have hsplit : (⟨(PhiS S)^[n + 1] e, hm'⟩ : ↥(URge K R 1)) =
            ⟨PhiL S.toList ((PhiS S)^[n] e), PhiL_mem_URge hR hm _⟩ := by
          apply Subtype.ext
          show (PhiS S)^[n + 1] e = _
          rw [Function.iterate_succ_apply']
          rfl
        rw [hsplit, prC_PhiL hf hR ⟨(PhiS S)^[n] e, hm⟩ S.toList, hEq,
          Function.iterate_succ_apply']
        rfl
    obtain ⟨hmH, hEqH⟩ := hiter H
    have h1 : prC hf hR ⟨(PhiS S)^[H] e, hmH⟩ = 1 := by
      have : (⟨(PhiS S)^[H] e, hmH⟩ : ↥(URge K R 1)) = 1 := Subtype.ext (hnil e heE)
      rw [this]
      exact (projHom hf hR).map_one
    rw [h1, hpre, Function.iterate_fixed hfix] at hEqH
    exact hne1 (Subtype.ext hEqH.symm)
  intro e he
  have hmem : e ∈ URge K R 1 := hE.le he
  obtain ⟨v, hv, hev⟩ := prC_spec hf hR ⟨e, hmem⟩
  have h1 : prC hf hR ⟨e, hmem⟩ = 1 := by
    have : prC hf hR ⟨e, hmem⟩ ∈ Epr hf hR E := (mem_Epr hf hR).2 ⟨e, hmem, he, rfl⟩
    rw [hbot'', Subgroup.mem_bot] at this
    exact this
  rw [h1, one_mul] at hev
  have : e = v := hev
  rw [this]
  exact hv

end Phi

end CFSG.RankThree.GF2n.Smith81.S81Z
