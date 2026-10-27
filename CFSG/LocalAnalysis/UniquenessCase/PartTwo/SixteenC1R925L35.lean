module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Fit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Gl2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Mult
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Five

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925_l35_pcore_centralized {Γ : Type} [Group Γ] [Finite Γ]
    {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M) (hq : IsL3Five ↥(K.map (toModO3p Γ))) :
    ∀ k ∈ K, ∀ x ∈ r925PCoreGe5 Γ, k * x = x * k := by
  obtain ⟨ψ, hψ⟩ := r925_pcore_reps h.rank_gt_three
  let W' : Subgroup ↥K := ((toModO3p Γ).subgroupMap K).ker
  have hker : (toModO3p Γ).ker = CFSG.pPrimeCore 3 Γ :=
    QuotientGroup.ker_mk' (N := CFSG.pPrimeCore 3 Γ)
  have hWorder : ∀ w ∈ W', ¬ 3 ∣ orderOf w := by
    intro w hw
    have h2 : w ∈ (toModO3p Γ).ker.subgroupOf K := by
      rw [← Subgroup.ker_subgroupMap]
      exact hw
    have h3 : (w : Γ) ∈ (toModO3p Γ).ker := Subgroup.mem_subgroupOf.mp h2
    rw [hker] at h3
    rw [← Subgroup.orderOf_coe w]
    exact r925_pPrimeCore_orderOf (w : Γ) h3
  have hq' : IsL3Five (↥K ⧸ W') :=
    hq.of_mulEquiv (r925QuotEquiv (toModO3p Γ) K).symm
  have htriv : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, ∀ k : ↥K, ψ p (k : Γ) = 1 := by
    intro p k
    haveI : Fact p.1.Prime := ⟨p.2.1⟩
    have hcomp : (ψ p).comp K.subtype = 1 :=
      r925_gl2_trivial_of_l35 h.perfect_k W' hWorder hq' p.1 p.2.2 ((ψ p).comp K.subtype)
    have h1 := DFunLike.congr_fun hcomp k
    simpa using h1
  have hA : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ a ∈ K, ∀ x ∈ CFSG.pCore p Γ, a * x = x * a := by
    intro p hp h5 a ha x hx
    haveI : Fact p.Prime := ⟨hp⟩
    exact r925_pcore_centralized_of_rep p h5 h.threeGen_k (hψ ⟨p, ⟨hp, h5⟩⟩).1
      (fun b hb => htriv ⟨p, ⟨hp, h5⟩⟩ ⟨b, hb⟩) a ha x hx
  intro k hk x hx
  exact r925_centralizes_pCoreGe5 K hA k hk x hx

theorem r925_l35_inf_eq_bot (hGA : CFSG.Open.GriessAllModelsStatement)
    (hKSch : UCK.KSch) {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hq : IsL3Five ↥(K.map (toModO3p Γ))) :
    K ⊓ CFSG.pPrimeCore 3 Γ = ⊥ := by
  let J : Subgroup Γ := CFSG.pPrimeCore 3 Γ
  let W' : Subgroup ↥K := ((toModO3p Γ).subgroupMap K).ker
  have hker : (toModO3p Γ).ker = J :=
    QuotientGroup.ker_mk' (N := CFSG.pPrimeCore 3 Γ)
  have hq' : IsL3Five (↥K ⧸ W') :=
    hq.of_mulEquiv (r925QuotEquiv (toModO3p Γ) K).symm
  have hle : r925FittingIn J ≤ r925PCoreGe5 Γ := by
    simpa [J] using r925_fitting_le_pCoreGe5 (Γ := Γ) h.o2_eq_bot
  have hlayer : K ≤ Subgroup.centralizer (r925LayerIn J : Set Γ) := by
    simpa [J] using r925_layer_centralized hKSch h.kgroup
      (fun q hq h5 => h.rank_gt_three q hq (by omega)) h.perfect_k h.threeGen_k
  have hcentP : K ≤ Subgroup.centralizer (r925PCoreGe5 Γ : Set Γ) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (r925_l35_pcore_centralized h hq k hk x hx).symm
  have hfit : K ≤ Subgroup.centralizer (r925FittingIn J : Set Γ) :=
    hcentP.trans (Subgroup.centralizer_le
      (show (r925FittingIn J : Set Γ) ⊆ r925PCoreGe5 Γ from hle))
  have hstar : K ≤ Subgroup.centralizer (Fstar J : Set Γ) := by
    rw [r925_fstar_eq_sup J]
    exact Subgroup.le_centralizer_iff.mp
      (sup_le (Subgroup.le_centralizer_iff.mpr hfit) (Subgroup.le_centralizer_iff.mpr hlayer))
  have hWcenter : W' ≤ Subgroup.center ↥K := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hwJ : (w : Γ) ∈ J := by
      have h2 : w ∈ (toModO3p Γ).ker.subgroupOf K := by
        rw [← Subgroup.ker_subgroupMap]
        exact hw
      have h3 : (w : Γ) ∈ (toModO3p Γ).ker := Subgroup.mem_subgroupOf.mp h2
      rwa [hker] at h3
    have hwF : (w : Γ) ∈ Subgroup.centralizer (Fstar J : Set Γ) ⊓ J :=
      Subgroup.mem_inf.mpr ⟨hstar w.2, hwJ⟩
    have hwfit : (w : Γ) ∈ r925FittingIn J := r925_centralizer_fstar_le_fitting J hwF
    have hwP : (w : Γ) ∈ r925PCoreGe5 Γ := hle hwfit
    exact r925_l35_pcore_centralized h hq (z : Γ) z.2 (w : Γ) hwP
  have hW'bot : W' = ⊥ := l35_central_trivial hGA W' hWcenter h.perfect_k hq'
  have hW'map : W'.map K.subtype = K ⊓ J := by
    change (((toModO3p Γ).subgroupMap K).ker.map K.subtype) = K ⊓ J
    rw [Subgroup.ker_subgroupMap, hker, Subgroup.subgroupOf_map_subtype]
    exact inf_comm J K
  change K ⊓ J = ⊥
  rw [← hW'map, hW'bot, Subgroup.map_bot]

theorem r925_l35 (hGA : CFSG.Open.GriessAllModelsStatement)
    (hKSch : UCK.KSch) {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M)
    (hd : IsL3Five ↥(K.map (toModO3p Γ)) ∧ IsSL2Prime ↥(Y.map (toModO3p Γ)) 5) :
    R925Concl Y K := by
  have hbot := r925_l35_inf_eq_bot hGA hKSch h hd.1
  have hinj : ∀ x ∈ K, toModO3p Γ x = 1 → x = 1 := fun x hx hx1 => by
    have hxJ : x ∈ CFSG.pPrimeCore 3 Γ := (QuotientGroup.eq_one_iff x).1 hx1
    have hmem : x ∈ K ⊓ CFSG.pPrimeCore 3 Γ := ⟨hx, hxJ⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  obtain ⟨eK⟩ := r925_nonempty_equiv_map (toModO3p Γ) hinj
  obtain ⟨eY⟩ := r925_nonempty_equiv_map (toModO3p Γ)
    (fun x hx hx1 => hinj x (h.y_le_k hx) hx1)
  exact ⟨s16c1_isSL2Prime_of_equiv hd.2 eY.symm, Or.inl (hd.1.of_mulEquiv eK.symm)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
