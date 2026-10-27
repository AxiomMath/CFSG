module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Thirteen_k_lt_m {γ s k : ℕ} (hγ2 : 2 ≤ γ) (hs : 2 ≤ s) (hk : k = 1 ∨ k = 2)
    (hcon : ¬ (γ ≤ 3 ∧ s = 2)) (h2 : γ = 2 → k = 1 ∨ s = 5 ∨ s = 6) :
    k < max γ ((s - 2) * γ) := by
  rcases Nat.lt_or_ge γ 3 with h | h
  · have hγ : γ = 2 := by omega
    subst hγ
    have hs3 : 3 ≤ s := by omega
    rcases h2 rfl with h1 | h5
    · exact lt_max_of_lt_left (by omega)
    · exact lt_max_of_lt_right (by omega)
  · exact lt_max_of_lt_left (by omega)

theorem s15_Thirteen_lt_rParam (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {k : ℕ}
    (hk : k < max (gamma15 D.M V₀ V hV L) ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L)) :
    (k : ℕ∞) < E3.rParam V := by
  have h1 := s15_Tools_le_rMV D h hV hL
  rw [rMV_eq_rParam (Hyp125.normalizer_eq h.hyp151.hyp125)] at h1
  refine lt_of_lt_of_le ?_ h1
  exact_mod_cast Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)

private theorem s15_ThirteenC_conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_sup _ _ _

private theorem s15_ThirteenC_commElt_mono {A B : Subgroup G} {t : G} (hAB : A ≤ B) :
    commElt A t ≤ commElt B t := by
  rw [commElt, Subgroup.closure_le]
  rintro c ⟨a, ha, rfl⟩
  exact Subgroup.subset_closure ⟨a, hAB ha, rfl⟩

private theorem s15_ThirteenC_commElt_le_of_conj_eq_self {X : Subgroup G} {t : G}
    (h : conjSubgroup X t = X) : commElt X t ≤ X := by
  rw [commElt, Subgroup.closure_le]
  rintro c ⟨x, hx, rfl⟩
  have hmem : t⁻¹ * x * t ∈ X := by
    have hmem' : t⁻¹ * x * t ∈ conjSubgroup X t :=
      mem_conjSubgroup_iff.2 (by
        rw [show t * (t⁻¹ * x * t) * t⁻¹ = x by group]
        exact hx)
    rwa [h] at hmem'
  have hgen : x⁻¹ * t⁻¹ * x * t = x⁻¹ * (t⁻¹ * x * t) := by group
  rw [hgen]
  exact X.mul_mem (X.inv_mem hx) hmem

private theorem s15_ThirteenC_commElt_le_sup_conj (X : Subgroup G) (t : G) :
    commElt X t ≤ X ⊔ conjSubgroup X t := by
  rw [commElt, Subgroup.closure_le]
  rintro c ⟨x, hx, rfl⟩
  have hmem : t⁻¹ * x * t ∈ conjSubgroup X t :=
    mem_conjSubgroup_iff.2 (by
      rw [show t * (t⁻¹ * x * t) * t⁻¹ = x by group]
      exact hx)
  have hgen : x⁻¹ * t⁻¹ * x * t = x⁻¹ * (t⁻¹ * x * t) := by group
  rw [hgen]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (X.inv_mem hx))
    (Subgroup.mem_sup_right hmem)

private theorem s15_ThirteenC_le_centralizer_of_commElt_bot {X : Subgroup G} {t : G}
    (h : commElt X t = ⊥) : X ≤ centralizer ({t} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : x⁻¹ * t⁻¹ * x * t ∈ commElt X t := Subgroup.subset_closure ⟨x, hx, rfl⟩
  rw [h] at hmem
  have h1 : x⁻¹ * t⁻¹ * x * t = 1 := Subgroup.mem_bot.1 hmem
  have h2 : t⁻¹ * x * t = x := by
    have := congrArg (fun y => x * y) h1
    simpa [mul_assoc] using this
  have h3 : x * t = t * x := by
    have := congrArg (fun y => t * y) h2
    simpa [mul_assoc] using this
  exact h3

theorem s15_Thirteen_beta (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    ((max (gamma15 D.M V₀ V hV L) ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) : ℕ) : ℕ∞) ≤
      betaN 0 D.M V := by
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hγ2 : 2 ≤ gamma15 D.M V₀ V hV L := two_le_gamma15 D h.hyp151 hV hL
  have hγpos : 0 < gamma15 D.M V₀ V hV L := by omega
  refine le_iInf₂ fun U hU => ?_
  unfold calBn propN at hU
  obtain ⟨hUV, t, ht, htord, W', hW'V, hW'0, hUW', htW', hPropB⟩ := hU
  have hW'eq : W' = V := (E3.mQuot_eq_zero_iff hV2 hW'V).1 (Nat.le_zero.1 hW'0)
  subst W'
  have htM : t ∈ D.M := ht.1
  have htCent : t ∈ centralizer (U : Set G) := ht.2
  have hUC : U ≤ centralizer ({t} : Set G) := by
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 htCent u hu)
  have hUt : U ≤ V ⊓ centralizer ({t} : Set G) := le_inf hUV hUC
  have hZV : commElt V t ≤ V := by
    rw [commElt, Subgroup.closure_le]
    rintro c ⟨v, hv, rfl⟩
    have htN : t ∈ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer htM
    have hmem : t⁻¹ * v * t ∈ V := (Subgroup.mem_normalizer_iff''.1 htN v).1 hv
    have hgen : v⁻¹ * t⁻¹ * v * t = v⁻¹ * (t⁻¹ * v * t) := by group
    rw [hgen]
    exact V.mul_mem (V.inv_mem hv) hmem
  have hZ_inf_F : ∀ m ∈ D.M, commElt V t ⊓
      (conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L) = ⊥ := by
    intro m hm
    have h1 := s15_Tools_inf_conj_eq_bot D h hV hZV hPropB hm
    have h2 := s15_ThirteenC_conjSubgroup_sup (wSub V₀ V hV L)
      (v1Sub D.M V₀ V hV L) m
    rw [h2, s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV hm] at h1
    exact h1
  have hexF : ∃ X ∈ wConj D.M V₀ V hV L,
      conjSubgroup (fSub15 D.M V₀ V hV L X) t ≠ fSub15 D.M V₀ V hV L X := by
    by_contra hcon
    push Not at hcon
    apply htW'
    rw [← iSup_wConj_eq D h1217 h.hyp151 hV hL]
    refine iSup₂_le fun X hX => ?_
    have hFfix : conjSubgroup (fSub15 D.M V₀ V hV L X) t =
        fSub15 D.M V₀ V hV L X := hcon X hX
    have hXt_mem : conjSubgroup X t ∈ wConj D.M V₀ V hV L := by
      obtain ⟨m, hm, rfl⟩ := hX
      exact ⟨m * t, D.M.mul_mem hm htM, by rw [conjSubgroup_conjSubgroup]⟩
    have hFeq : fSub15 D.M V₀ V hV L (conjSubgroup X t) =
        fSub15 D.M V₀ V hV L X := by
      have hh := hFfix
      unfold fSub15 at hh ⊢
      rw [s15_ThirteenC_conjSubgroup_sup,
        s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV htM] at hh
      exact hh
    have hXeq : conjSubgroup X t = X :=
      s15_Twelve_fSub_inj D h1217 h.hyp151 hV hL hγpos hXt_mem hX hFeq
    obtain ⟨m, hm, rfl⟩ := hX
    have hXV : conjSubgroup (wSub V₀ V hV L) m ≤ V :=
      s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
    have hcomm_le_X : commElt (conjSubgroup (wSub V₀ V hV L) m) t ≤
        conjSubgroup (wSub V₀ V hV L) m :=
      s15_ThirteenC_commElt_le_of_conj_eq_self hXeq
    have hcomm_le_Z : commElt (conjSubgroup (wSub V₀ V hV L) m) t ≤ commElt V t :=
      s15_ThirteenC_commElt_mono hXV
    have hle : commElt (conjSubgroup (wSub V₀ V hV L) m) t ≤ commElt V t ⊓
        (conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L) :=
      le_inf hcomm_le_Z (hcomm_le_X.trans le_sup_left)
    rw [hZ_inf_F m hm] at hle
    exact s15_ThirteenC_le_centralizer_of_commElt_bot (le_bot_iff.1 hle)
  obtain ⟨X, hX, hmoveF⟩ := hexF
  have hγle : gamma15 D.M V₀ V hV L ≤ E3.mQuot V (centralizer ({t} : Set G)) :=
    s15_Twelve_moved_rank D h1217 h.hyp151 hV hL htM hX hmoveF
  have hmoveX : conjSubgroup X t ≠ X := by
    intro hXtX
    apply hmoveF
    have h1 : conjSubgroup (fSub15 D.M V₀ V hV L X) t = X ⊔ v1Sub D.M V₀ V hV L := by
      have h2 := s15_ThirteenC_conjSubgroup_sup X (v1Sub D.M V₀ V hV L) t
      have h3 : fSub15 D.M V₀ V hV L X = X ⊔ v1Sub D.M V₀ V hV L := rfl
      rw [h3, h2, s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV htM, hXtX]
    rw [h1]
    rfl
  by_cases hs4 : 4 ≤ s15 D.M V₀ V hV L
  · exfalso
    have hXt_mem : conjSubgroup X t ∈ wConj D.M V₀ V hV L := by
      obtain ⟨m, hm, rfl⟩ := hX
      exact ⟨m * t, D.M.mul_mem hm htM, by rw [conjSubgroup_conjSubgroup]⟩
    have hexM : ∃ x ∈ D.M, conjSubgroup (wSub V₀ V hV L) x ≠ X ∧
        conjSubgroup (wSub V₀ V hV L) x ≠ conjSubgroup X t := by
      by_contra hcon
      push Not at hcon
      have hsub : wConj D.M V₀ V hV L ⊆ ({X, conjSubgroup X t} : Set (Subgroup G)) := by
        rintro Y ⟨m, hm, rfl⟩
        by_cases h : conjSubgroup (wSub V₀ V hV L) m = X
        · rw [h]; simp
        · rw [hcon m hm h]; simp
      have h2 : (wConj D.M V₀ V hV L).ncard ≤
          ({X, conjSubgroup X t} : Set (Subgroup G)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 : ({X, conjSubgroup X t} : Set (Subgroup G)).ncard ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
      have hw : 4 ≤ (wConj D.M V₀ V hV L).ncard := by
        rw [ncard_wConj D h.hyp151 hV]
        exact hs4
      omega
    obtain ⟨x, hxM, hxX, hxXt⟩ := hexM
    have hlt : ({X, conjSubgroup X t, conjSubgroup (wSub V₀ V hV L) x} :
        Set (Subgroup G)).ncard < (wConj D.M V₀ V hV L).ncard := by
      have h3 : ({X, conjSubgroup X t, conjSubgroup (wSub V₀ V hV L) x} :
          Set (Subgroup G)).ncard ≤ 3 := by
        have h1 := Set.ncard_insert_le X ({conjSubgroup X t,
          conjSubgroup (wSub V₀ V hV L) x} : Set (Subgroup G))
        have h2 := Set.ncard_insert_le (conjSubgroup X t)
          ({conjSubgroup (wSub V₀ V hV L) x} : Set (Subgroup G))
        rw [Set.ncard_singleton] at h2
        omega
      rw [ncard_wConj D h.hyp151 hV]
      omega
    obtain ⟨Y, hYmem, hYnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    obtain ⟨y, hyM, rfl⟩ := hYmem
    have hyX : conjSubgroup (wSub V₀ V hV L) y ≠ X := by
      intro e
      exact hYnot (by rw [e]; simp)
    have hyXt : conjSubgroup (wSub V₀ V hV L) y ≠ conjSubgroup X t := by
      intro e
      exact hYnot (by rw [e]; simp)
    have hyx : conjSubgroup (wSub V₀ V hV L) y ≠ conjSubgroup (wSub V₀ V hV L) x := by
      intro e
      exact hYnot (by rw [e]; simp)
    have hxy : conjSubgroup (wSub V₀ V hV L) x ≠ conjSubgroup (wSub V₀ V hV L) y :=
      hyx.symm
    set S : Subgroup G := v1Sub D.M V₀ V hV L ⊔
      ⨆ Y ∈ {Y | Y ∈ wConj D.M V₀ V hV L ∧
        Y ≠ conjSubgroup (wSub V₀ V hV L) x ∧
        Y ≠ conjSubgroup (wSub V₀ V hV L) y}, Y with hSdef
    have hZS : commElt V t ⊓ S = ⊥ := by
      rw [hSdef]
      exact s15_Tools_inf_S_eq_bot D h hV hZV hPropB hxM hyM hxy
    have hXS : X ≤ S := by
      rw [hSdef]
      refine le_sup_of_le_right ?_
      refine le_iSup₂_of_le X ?_ le_rfl
      exact ⟨hX, hxX.symm, hyX.symm⟩
    have hXtS : conjSubgroup X t ≤ S := by
      rw [hSdef]
      refine le_sup_of_le_right ?_
      refine le_iSup₂_of_le (conjSubgroup X t) ?_ le_rfl
      exact ⟨hXt_mem, hxXt.symm, hyXt.symm⟩
    have hcomm_le_S : commElt X t ≤ S :=
      (s15_ThirteenC_commElt_le_sup_conj X t).trans (sup_le hXS hXtS)
    have hXV : X ≤ V := by
      obtain ⟨m, hm, rfl⟩ := hX
      exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
    have hcomm_le_Z : commElt X t ≤ commElt V t := s15_ThirteenC_commElt_mono hXV
    have hcomm_bot : commElt X t = ⊥ := by
      have hle : commElt X t ≤ commElt V t ⊓ S := le_inf hcomm_le_Z hcomm_le_S
      rw [hZS] at hle
      exact le_bot_iff.1 hle
    have hXleC : X ≤ centralizer ({t} : Set G) :=
      s15_ThirteenC_le_centralizer_of_commElt_bot hcomm_bot
    have hXnorm : t ∈ normalizer (X : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hcomm : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.1 (hXleC hh)
        rw [show t * h * t⁻¹ = h by rw [hcomm.symm]; group]
        exact hh
      · intro hh
        have hcomm : (t * h * t⁻¹) * t = t * (t * h * t⁻¹) :=
          Subgroup.mem_centralizer_singleton_iff.1 (hXleC hh)
        have hhh : h = t * h * t⁻¹ := by
          calc h = t⁻¹ * (t * h * t⁻¹) * t := by group
            _ = t⁻¹ * ((t * h * t⁻¹) * t) := by group
            _ = t⁻¹ * (t * (t * h * t⁻¹)) := by rw [hcomm]
            _ = t * h * t⁻¹ := by group
        rw [hhh]
        exact hh
    exact hmoveX (conjSubgroup_eq_iff_mem_normalizer.2 hXnorm)
  · have hsle3 : s15 D.M V₀ V hV L ≤ 3 := by omega
    have hmax : max (gamma15 D.M V₀ V hV L)
        ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) =
        gamma15 D.M V₀ V hV L := by
      refine max_eq_left ?_
      have hs : s15 D.M V₀ V hV L - 2 ≤ 1 := by omega
      calc (s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L
          ≤ 1 * gamma15 D.M V₀ V hV L := Nat.mul_le_mul_right _ hs
        _ = gamma15 D.M V₀ V hV L := one_mul _
    have hCeq : E3.mQuot V (centralizer ({t} : Set G)) =
        E3.mQuot V (V ⊓ centralizer ({t} : Set G)) := by
      unfold E3.mQuot
      rw [Subgroup.inf_relIndex_left]
    calc ((max (gamma15 D.M V₀ V hV L)
          ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) : ℕ) : ℕ∞)
        = (gamma15 D.M V₀ V hV L : ℕ∞) := by rw [hmax]
      _ ≤ (E3.mQuot V (centralizer ({t} : Set G)) : ℕ∞) := by exact_mod_cast hγle
      _ = (E3.mQuot V (V ⊓ centralizer ({t} : Set G)) : ℕ∞) := by rw [hCeq]
      _ ≤ (E3.mQuot V U : ℕ∞) := by exact_mod_cast E3.mQuot_mono (V := V) hUt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
