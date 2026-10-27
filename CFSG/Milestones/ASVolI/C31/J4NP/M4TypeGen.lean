module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Om

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc (omegaZ)

theorem burnsideJ4NP_W_eq_map_conj {A₀ W₀ R : Subgroup J}
    (hA : Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x} = W₀) {c : J}
    (hAZ : A₀.map (MulAut.conj c).toMonoidHom ≤ omegaZ R)
    (hWA : burnsideJ4NP_W R ≤ A₀.map (MulAut.conj c).toMonoidHom) :
    burnsideJ4NP_W R = W₀.map (MulAut.conj c).toMonoidHom := by
  rw [burnsideJ4NP_W_eq_closure hAZ hWA, burnsideJ4NP_closure2A_map_conj, hA]

theorem burnsideJ4NP_verdictW_of_char
    {W₀ K F : Subgroup J} (hK : Subgroup.centralizer (W₀ : Set J) = K) (hK2 : IsPGroup 2 ↥K)
    (hNF : Subgroup.normalizer (K : Set J) ≤ Subgroup.normalizer (F : Set J))
    (hF2 : IsPGroup 2 ↥F) (hF1 : F ≠ ⊥) {g : J}
    (hgF : g ∈ Subgroup.normalizer (F : Set J)) (hgW : g ∉ Subgroup.normalizer (W₀ : Set J)) :
    burnsideJ4NP_VerdictW W₀ := by
  refine burnsideJ4NP_verdictW_of_false fun A₀ hA R hR c hAZ hWA => ?_
  have hW := burnsideJ4NP_W_eq_map_conj hA hAZ hWA
  have hC : Subgroup.centralizer (burnsideJ4NP_W R : Set J) =
      K.map (MulAut.conj c).toMonoidHom := by
    rw [hW, burnsideJ4NP_centralizer_map_conj, hK]
  have hRK : R ≤ K.map (MulAut.conj c).toMonoidHom := hC ▸ burnsideJ4NP_R_le_centralizer_W R
  have hNR : Subgroup.normalizer (R : Set J) ≤
      Subgroup.normalizer ((K.map (MulAut.conj c).toMonoidHom : Subgroup J) : Set J) := by
    rw [← burnsideJ4NP_normalizer_W hR, ← hC]
    exact burnsideJ4NP_normalizer_le_normalizer_centralizer _
  have hReq : R = K.map (MulAut.conj c).toMonoidHom :=
    le_antisymm hRK (hR.core _ (hK2.map _) hNR)
  have hNF' : Subgroup.normalizer (R : Set J) ≤
      Subgroup.normalizer ((F.map (MulAut.conj c).toMonoidHom : Subgroup J) : Set J) := by
    rw [hReq, burnsideJ4NP_normalizer_map_conj, burnsideJ4NP_normalizer_map_conj]
    exact Subgroup.map_mono hNF
  have hmax := hR.max _ (hF2.map _) (burnsideJ4KW_map_conj_ne_bot hF1 c) hNF'
  have hg' : c * g * c⁻¹ ∈ Subgroup.normalizer
      ((F.map (MulAut.conj c).toMonoidHom : Subgroup J) : Set J) := by
    rw [burnsideJ4NP_normalizer_map_conj, burnsideJ4NP_mem_map_conj]
    simpa [mul_assoc] using hgF
  rw [hmax, ← burnsideJ4NP_normalizer_W hR, hW, burnsideJ4NP_normalizer_map_conj,
    burnsideJ4NP_mem_map_conj] at hg'
  exact hgW (by simpa [mul_assoc] using hg')

theorem burnsideJ4NP_verdictW_of_core
    {W₀ Y₀ : Subgroup J}
    (hNY : Subgroup.normalizer (W₀ : Set J) ≤ Subgroup.normalizer (Y₀ : Set J))
    (hC2 : IsPGroup 2 ↥(Subgroup.centralizer (Y₀ : Set J))) {h : J}
    (hhY : h ∈ Subgroup.centralizer (Y₀ : Set J))
    (hhW : h ∉ Subgroup.centralizer (W₀ : Set J)) : burnsideJ4NP_VerdictW W₀ := by
  refine burnsideJ4NP_verdictW_of_false fun A₀ hA R hR c hAZ hWA => ?_
  have hW := burnsideJ4NP_W_eq_map_conj hA hAZ hWA
  set C := Subgroup.centralizer (Y₀ : Set J) with hCdef
  have hNR : Subgroup.normalizer (R : Set J) ≤
      Subgroup.normalizer ((C.map (MulAut.conj c).toMonoidHom : Subgroup J) : Set J) := by
    rw [← burnsideJ4NP_normalizer_W hR, hW, burnsideJ4NP_normalizer_map_conj,
      burnsideJ4NP_normalizer_map_conj]
    exact Subgroup.map_mono (hNY.trans (burnsideJ4NP_normalizer_le_normalizer_centralizer Y₀))
  have hCR := hR.core _ (hC2.map _) hNR
  have hRC : R ≤ (Subgroup.centralizer (W₀ : Set J)).map (MulAut.conj c).toMonoidHom := by
    rw [← burnsideJ4NP_centralizer_map_conj, ← hW]
    exact burnsideJ4NP_R_le_centralizer_W R
  have hmem : c * h * c⁻¹ ∈ C.map (MulAut.conj c).toMonoidHom := by
    rw [burnsideJ4NP_mem_map_conj]
    simpa [mul_assoc] using hhY
  have h2 := hRC (hCR hmem)
  rw [burnsideJ4NP_mem_map_conj] at h2
  exact hhW (by simpa [mul_assoc] using h2)

@[expose] def burnsideJ4NP_classSet (K : Subgroup J) (m : ℕ) : Set J :=
  {t | t ∈ K ∧ t * t = 1 ∧ Nat.card ↥(K ⊓ Subgroup.centralizer {t}) = m}

theorem burnsideJ4NP_inf_centralizer_map_conj {K : Subgroup J} {n : J}
    (hn : n ∈ Subgroup.normalizer (K : Set J)) (t : J) :
    (K ⊓ Subgroup.centralizer {t}).map (MulAut.conj n).toMonoidHom =
      K ⊓ Subgroup.centralizer {n * t * n⁻¹} := by
  ext x
  rw [burnsideJ4NP_mem_map_conj, Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hK : n⁻¹ * x * n ∈ K ↔ x ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n))
    rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this
    exact this
  rw [hK]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    calc x * (n * t * n⁻¹) = n * ((n⁻¹ * x * n) * t) * n⁻¹ := by group
      _ = n * (t * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
      _ = n * t * n⁻¹ * x := by group
  · intro h
    calc n⁻¹ * x * n * t = n⁻¹ * (x * (n * t * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * t * n⁻¹) * x) * n := by rw [h]
      _ = t * (n⁻¹ * x * n) := by group

theorem burnsideJ4NP_normalizer_le_normalizer_classSet (K : Subgroup J) (m : ℕ) :
    Subgroup.normalizer (K : Set J) ≤
      Subgroup.normalizer
        ((Subgroup.closure (burnsideJ4NP_classSet K m) : Subgroup J) : Set J) := by
  intro n hn
  apply burnsideJ4NP_mem_normalizer_closure
  rintro t ⟨htK, ht2, htc⟩
  refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hn t).mp htK, ?_, ?_⟩
  · calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  · rw [← burnsideJ4NP_inf_centralizer_map_conj hn, burnsideJ4KW_card_map_conj, htc]

theorem burnsideJ4NP_centralizer_le_Hj_of_pts
    {W₀ : Subgroup J} (cs : List ℕ)
    (hz : CFSG.Quasithin.J4Loc.z0 ∈ W₀) (hcs : ∀ c ∈ cs, eta uJ 11 c ∈ W₀)
    (htest : ∀ i, 0 < i → i < 77 → ∃ c ∈ cs,
      (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * eta uJ 11 c * CFSG.Quasithin.J4M2.ptElt i ∉ Eg uJ 11) :
    Subgroup.centralizer (W₀ : Set J) ≤ Hj := by
  have hF := j4Facts
  intro x hx
  have hxz : x ∈ CFSG.Quasithin.J4M2.M2 := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx _ hz).symm
  have hmem : x • CFSG.Quasithin.F134.J4E9.basePt ∈
      {w : J ⧸ Hj | ∃ q ∈ CFSG.Quasithin.J4M2.M2, q • CFSG.Quasithin.F134.J4E9.basePt = w} :=
    ⟨x, hxz, rfl⟩
  rw [CFSG.Quasithin.J4M2.pt_range hF] at hmem
  obtain ⟨i, hi, hxi⟩ := hmem
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [CFSG.Quasithin.J4M2.pt_zero] at hxi
    exact CFSG.Quasithin.F134.J4E9.smul_basePt_eq_self_iff.mp hxi
  · exfalso
    obtain ⟨c, hc, hcE⟩ := htest i hi0 hi
    have hh : (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * x ∈ Hj := by
      rw [← CFSG.Quasithin.J4M2.ptElt_smul_basePt] at hxi
      exact CFSG.Quasithin.F134.J4E9.smul_basePt_eq_iff.mp hxi
    have hcomm : eta uJ 11 c * x = x * eta uJ 11 c :=
      Subgroup.mem_centralizer_iff.mp hx _ (hcs c hc)
    have e : (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * eta uJ 11 c * CFSG.Quasithin.J4M2.ptElt i =
        ((CFSG.Quasithin.J4M2.ptElt i)⁻¹ * x) * eta uJ 11 c *
          ((CFSG.Quasithin.J4M2.ptElt i)⁻¹ * x)⁻¹ := by
      calc (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * eta uJ 11 c * CFSG.Quasithin.J4M2.ptElt i
          = (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * (x * eta uJ 11 c) * x⁻¹ *
              CFSG.Quasithin.J4M2.ptElt i := by rw [← hcomm]; group
        _ = ((CFSG.Quasithin.J4M2.ptElt i)⁻¹ * x) * eta uJ 11 c *
              ((CFSG.Quasithin.J4M2.ptElt i)⁻¹ * x)⁻¹ := by group
    apply hcE
    rw [e]
    exact Hj_normalizes_Eg hF.mat _ hh _ (eta_mem_Eg 11 le_rfl c)

end CFSG.ASVolI
