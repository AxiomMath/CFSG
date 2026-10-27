module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.GGQ2Frame.UnitRaw

open CFSG CFSG.Assembly Module
open CFSG.StandardType (GGLabelIso)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def equivLabels {N : ℕ} (S : Finset (Fin N)) : Set LargeEvenLabel :=
  {lab | GGLabelIso (label S) lab}

private lemma l02qfru_mem_oneLine_of_constOn_univ {N : ℕ} {w : W N}
    (hw : ∀ i j : Fin N, w i = w j) : w ∈ oneLine N := by
  rw [mem_oneLine]
  by_cases h : Nonempty (Fin N)
  · exact ⟨w (Classical.choice h), by
      funext i
      exact hw i (Classical.choice h)⟩
  · exact ⟨0, by funext i; exact (h ⟨i⟩).elim⟩

private lemma l02qfru_constOn_univ_le_oneLine (N : ℕ) :
    constOn (Finset.univ : Finset (Fin N)) ≤ oneLine N := by
  intro w hw
  exact l02qfru_mem_oneLine_of_constOn_univ
    (fun i j => hw i (Finset.mem_univ i) j (Finset.mem_univ j))

private lemma l02qfru_mem_cent_iff_diffFun {N : ℕ} {S : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ S) (v : Vfull N) :
    v ∈ cent S ↔ ∀ i ∈ S, diffFun N i i₀ v = 0 := by
  constructor
  · intro hv i hi
    obtain ⟨w, hw, hwconst⟩ := (mem_cent_iff S v).mp hv
    rw [← hw, diffFun_mk]
    exact sub_eq_zero.mpr (hwconst i hi i₀ hi₀)
  · intro hv
    rw [mem_cent_iff]
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (oneLine N) v
    refine ⟨w, hw, ?_⟩
    intro i hi j hj
    have hi' : w i = w i₀ := by
      have := hv i hi
      rw [← hw, diffFun_mk, sub_eq_zero] at this
      exact this
    have hj' : w j = w i₀ := by
      have := hv j hj
      rw [← hw, diffFun_mk, sub_eq_zero] at this
      exact this
    rw [hi', hj']

private lemma l02qfru_finrank_cent_aux {N : ℕ} (S : Finset (Fin N)) (i₀ : Fin N) (hi₀ : i₀ ∈ S) :
    finrank F (cent S) = N - S.card := by
  have hcard_le : S.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hcard_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  let Φ : Vfull N →ₗ[F] (S → F) := LinearMap.pi (fun i : S => diffFun N i.1 i₀)
  have hker : LinearMap.ker Φ = cent S := by
    ext v
    rw [LinearMap.mem_ker, l02qfru_mem_cent_iff_diffFun hi₀ v]
    constructor
    · intro hv i hi
      have := congrFun hv ⟨i, hi⟩
      simpa [Φ, LinearMap.pi_apply] using this
    · intro hv
      funext i
      simpa [Φ, LinearMap.pi_apply] using hv i.1 i.2
  let ev : (S → F) →ₗ[F] F := LinearMap.proj (R := F) (φ := fun _ : S => F) ⟨i₀, hi₀⟩
  have hrange : LinearMap.range Φ = LinearMap.ker ev := by
    ext f
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (oneLine N) v
      rw [LinearMap.mem_ker]
      show diffFun N i₀ i₀ ((oneLine N).mkQ w) = 0
      rw [diffFun_mk]
      exact sub_self _
    · intro hf
      rw [LinearMap.mem_ker] at hf
      refine ⟨(oneLine N).mkQ (fun i => if h : i ∈ S then f ⟨i, h⟩ else 0), ?_⟩
      funext i
      have hwi : (if h : i.1 ∈ S then f ⟨i.1, h⟩ else 0) = f i := by
        rw [dif_pos i.2]
      have hwi0 : (if h : i₀ ∈ S then f ⟨i₀, h⟩ else 0) = 0 := by
        rw [dif_pos hi₀]
        simpa [ev, LinearMap.proj_apply] using hf
      show diffFun N i.1 i₀
        ((oneLine N).mkQ (fun j => if h : j ∈ S then f ⟨j, h⟩ else 0)) = f i
      rw [diffFun_mk, hwi, hwi0, sub_zero]
  have hdimrange : finrank F (LinearMap.range Φ) = S.card - 1 := by
    rw [hrange]
    have hrank := LinearMap.finrank_range_add_finrank_ker ev
    have hsurj : LinearMap.range ev = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨fun _ => c, by simp [ev, LinearMap.proj_apply]⟩
    have htop : finrank F (⊤ : Submodule F F) = 1 := by simp
    rw [hsurj, htop, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrank
    omega
  have hdimV : finrank F (Vfull N) = N - 1 := by
    rw [Submodule.finrank_quotient]
    have hW : finrank F (W N) = N := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have hline : finrank F (oneLine N) = 1 := by
      rw [oneLine]
      exact finrank_span_singleton (K := F) (v := fun _ : Fin N => (1 : F)) (by
        intro h
        have := congrFun h i₀
        simpa using this)
    rw [hW, hline]
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hdimrange, hker, hdimV] at hrank
  omega

private lemma l02qfru_labelIso_eq_of_twA_rank_ne_three {lab lab' : LargeEvenLabel}
    (htag : lab.tag = .twA) (hr : lab.rank ≠ 3) (h : GGLabelIso lab lab') :
    lab' = lab := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  · obtain ⟨h1, _⟩ := h
    exact absurd (htag ▸ h1) (by decide)
  · obtain ⟨h1, _⟩ := h
    have : lab.tag = .D := congrArg LargeEvenLabel.tag h1
    exact absurd (htag ▸ this) (by decide)
  · obtain ⟨h1, _⟩ := h
    have : lab.tag = .A := congrArg LargeEvenLabel.tag h1
    exact absurd (htag ▸ this) (by decide)
  · obtain ⟨h1, _⟩ := h
    have : lab.tag = .twD := congrArg LargeEvenLabel.tag h1
    exact absurd (htag ▸ this) (by decide)
  · obtain ⟨h1, _⟩ := h
    have : lab.rank = 3 := congrArg LargeEvenLabel.rank h1
    exact absurd this hr
  · obtain ⟨h1, _⟩ := h
    have : lab.tag = .twD := congrArg LargeEvenLabel.tag h1
    exact absurd (htag ▸ this) (by decide)
  · obtain ⟨_, h2⟩ := h
    have : lab.tag = .A := congrArg LargeEvenLabel.tag h2
    exact absurd (htag ▸ this) (by decide)

private lemma l02qfru_not_twoNodeLabels_twA_rank_succ {labX labJ : LargeEvenLabel}
    (htX : labX.tag = .twA) (htJ : labJ.tag = .twA)
    (hr : labX.rank = labJ.rank + 1) :
    ¬ TwoNodeLabels 3 labX labJ := by
  intro h
  unfold TwoNodeLabels at h
  rcases h with ⟨h1, _, h3, _, _, _⟩ | ⟨h1, _, h3, _, _, _⟩ | ⟨h1, _, _, _, _, _⟩ |
    ⟨h1, _, _, _, _, _⟩
  · exact absurd (htJ ▸ h1) (by decide)
  · omega
  · exact absurd (htJ ▸ h1) (by decide)
  · exact absurd (htJ ▸ h1) (by decide)

theorem occurs_le_cent {N : ℕ} (U : Submodule F (Vfull N)) (S : Finset (Fin N)) (h : occurs U S) :
    U ≤ cent S := by
  intro u hu
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (oneLine N) u
  rw [mem_cent_iff]
  refine ⟨w, rfl, ?_⟩
  intro i hi j hj
  have hd := (h.2 i hi j).mp hj ((oneLine N).mkQ w) hu
  rw [diffFun_mk, sub_eq_zero] at hd
  exact hd

theorem cent_univ {N : ℕ} : cent (Finset.univ : Finset (Fin N)) = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    rw [mem_cent_iff] at hv
    obtain ⟨w, hw, hwconst⟩ := hv
    rw [← hw]
    have hw1 : w ∈ oneLine N := l02qfru_constOn_univ_le_oneLine N hwconst
    have hmem : w ∈ (oneLine N).mkQ.ker := by
      rw [Submodule.ker_mkQ]
      exact hw1
    exact LinearMap.mem_ker.mp hmem
  · exact bot_le

theorem finrank_cent {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) (hne : S ≠ Finset.univ) :
    finrank F (cent S) = N - S.card := by
  obtain ⟨i₀, hi₀⟩ := hS
  exact l02qfru_finrank_cent_aux S i₀ hi₀

theorem unitFull_noInternalTwoNode {N : ℕ} (hN : 4 ≤ N) (v : Vfull N) (hv : v ≠ 0)
    (U : Submodule F (Vfull N)) (hU : finrank F U = 2) (hvU : v ∈ U) (S T : Finset (Fin N))
    (hS : admissible S) (hT : admissible T)
    (hocc_S : occurs (Submodule.span F {v}) S) (hocc_T : occurs U T)
    (hcent_S : cent S = Submodule.span F {v}) (hcent_T : cent T ≤ U)
    (hin : v ∈ inside S) :
    ∀ labK ∈ equivLabels S, ∀ labJ ∈ equivLabels T,
      ¬ CFSG.StandardType.GGQ2Frame.TwoNodeLabels 3 labK labJ := by
  have hcentT_eq : cent T = U := le_antisymm hcent_T (occurs_le_cent U T hocc_T)
  have hSne : S.Nonempty := hocc_S.1
  have hS_ne_univ : S ≠ Finset.univ := by
    intro h
    have hbot : cent S = ⊥ := by rw [h]; exact cent_univ
    rw [hcent_S, Submodule.span_singleton_eq_bot] at hbot
    exact hv hbot
  have hdimS : finrank F (cent S) = N - S.card := finrank_cent S hSne hS_ne_univ
  have hspan1 : finrank F (Submodule.span F {v}) = 1 := by
    rw [finrank_span_singleton]
    exact hv
  have hNS : N - S.card = 1 := by rw [← hdimS, hcent_S, hspan1]
  have hS_le : S.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hScard : S.card = N - 1 := by omega
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨w, hwmk, hwsupp, hwsum⟩ := (mem_inside_iff S v).mp hin
  have hwconst : ∀ i ∈ S, w i = w s₀ := by
    intro i hi
    have hd := (hocc_S.2 s₀ hs₀ i).mp hi v (Submodule.mem_span_singleton_self v)
    rw [← hwmk, diffFun_mk] at hd
    exact (sub_eq_zero.mp hd).symm
  have hb : w s₀ ≠ 0 := by
    intro hb0
    have hwz : w = 0 := by
      funext i
      by_cases hi : i ∈ S
      · rw [hwconst i hi, hb0]; rfl
      · exact hwsupp i hi
    have : v = 0 := by rw [← hwmk, hwz]; rfl
    exact hv this
  have hsumS : ∑ i, w i = Finset.sum S w :=
    (Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) (f := w)
      (Finset.subset_univ S) (fun x _ hx => hwsupp x hx)).symm
  have hsumcard : Finset.sum S w = S.card • w s₀ := by
    rw [Finset.sum_congr rfl (fun i hi => hwconst i hi), Finset.sum_const]
  have hcast : (S.card : F) = 0 := by
    have h1 : (S.card : F) * w s₀ = 0 := by
      have h2 : ∑ i, w i = S.card • w s₀ := by rw [hsumS, hsumcard]
      rw [hwsum] at h2
      simpa [nsmul_eq_mul] using h2.symm
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hb
  have hdvd : 3 ∣ S.card := (ZMod.natCast_eq_zero_iff S.card 3).mp hcast
  have hS4 : 4 ≤ S.card := hS
  have hSge6 : 6 ≤ S.card := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  have hN7 : 7 ≤ N := by omega
  have hTne : T.Nonempty := hocc_T.1
  have hT_ne_univ : T ≠ Finset.univ := by
    intro h
    have h0 : finrank F (cent T) = 0 := by rw [h, cent_univ, finrank_bot]
    have h2 : finrank F (cent T) = 2 := by rw [hcentT_eq]; exact hU
    omega
  have hdimT : finrank F (cent T) = N - T.card := finrank_cent T hTne hT_ne_univ
  have hNT : N - T.card = 2 := by rw [← hdimT, hcentT_eq, hU]
  have hT_le : T.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ T
  have hTcard : T.card = N - 2 := by omega
  have hrankS : (label S).rank ≠ 3 := by
    have : S.card - 1 ≠ 3 := by omega
    simpa [label] using this
  have hrankT : (label T).rank ≠ 3 := by
    have : T.card - 1 ≠ 3 := by omega
    simpa [label] using this
  intro labK hKmem labJ hJmem htwo
  have hK : labK = label S :=
    l02qfru_labelIso_eq_of_twA_rank_ne_three (lab := label S) (lab' := labK) rfl hrankS hKmem
  have hJ : labJ = label T :=
    l02qfru_labelIso_eq_of_twA_rank_ne_three (lab := label T) (lab' := labJ) rfl hrankT hJmem
  rw [hK, hJ] at htwo
  refine l02qfru_not_twoNodeLabels_twA_rank_succ (labX := label S) (labJ := label T)
    rfl rfl ?_ htwo
  have : S.card - 1 = (T.card - 1) + 1 := by omega
  simpa [label] using this

end

end CFSG.StandardType.GGQ2Frame.UnitRaw
