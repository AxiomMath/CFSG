module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FX
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FZ
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5A7N
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FY

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C


theorem exists_of_case1_alt_seven_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    (h7 : IsAlt 7 ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥) :
    ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
      z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
      ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := by
  classical
  obtain ⟨e⟩ := h7
  set F := quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) with hFdef
  have hq := h1.1
  have h2520 : Nat.card ↥F = 2520 := by rw [Nat.card_congr e.toEquiv, Even7.card_alt]
  rcases Vol2.Ch10.SecB.C11AmS.K8.part1_shape h1.2.1.1 (Or.inl h2520) with hnat | h4
  swap
  · rw [hfix, bot_inf_eq] at h4
    exact (c.false_of_case1_alt_seven_four_ch615 hU hN hq e hfix h4).elim
  rw [hfix, bot_inf_eq] at hnat
  have hs : IsSimpleGroup ↥F := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hdl := dLemmaFacts_of_smallAlt_ch615 hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple hq) (Or.inl ⟨7, by norm_num, ⟨e⟩⟩)
  have hZ := center_of_isSimpleGroup_ch615 hs hdl.1
  have hFX : F ≤ autI hU (borelL T L ⊔ H) := (quasithinGenFitting_le _).trans (B6.ffJ_le _)
  have hXF := le_normalizer_genFitting_ch615 hU
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨d, hdD, hd1, hdPD, hSPD, hPDS, hPDs, hPKF, hPKS, hPKs, -⟩ :=
    c.exists_overgroups_ch615 hU hN hD hFX hXF hdl hZ hKF
  have hgen := c.le_sup_overgroups_ch615 hU hFX hXF hdl hZ hKF
  have htop : commV F = ⊤ := by
    have h := (Vol2.Ch10.SecB.C11AmS.K8.part2_direct h1.2.1.2.1 h2520).1
    rwa [hfix, sup_bot_eq] at h
  obtain ⟨ι₀, β₀, hβ₀⟩ := A7N.coords_alt7_ch615 hnat htop
  set S := autI hU T ⊓ F with hSdef
  have hSF : S ≤ F := inf_le_right
  obtain ⟨h₀, -, hh₀⟩ := Even7.isSylow_D.exists_conj (isSylowTwoOf_map_ch615 ι₀ hS)
  set h : Perm (Fin 7) := (h₀ : Perm (Fin 7)) with hh
  set ι : ↥F ≃* ↥(alternatingGroup (Fin 7)) :=
    ι₀.trans (MulAut.conjNormal (H := alternatingGroup (Fin 7)) h⁻¹) with hι
  set β : IntMod (UX615 T L H) hU ≃* ↥(G6.coreMod 7) := β₀.trans (A7S.coreAut_ch615 h⁻¹)
    with hβdef
  have hβ := A7S.hβ_conj_ch615 ι₀ β₀ hβ₀ h
  have hιv : ∀ f : ↥F, (ι f : Perm (Fin 7)) = h⁻¹ * (ι₀ f : Perm (Fin 7)) * h := fun f => by
    simp [hι]
  have hSD : ∀ s (hs : s ∈ S), (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) ∈ Even7.D := by
    intro s hs
    have h1 : ι₀ ⟨s, hSF hs⟩ ∈ (S.subgroupOf F).map ι₀.toMonoidHom :=
      ⟨⟨s, hSF hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hh₀] at h1
    obtain ⟨t, ht, hte⟩ := h1
    have e1 : (ι₀ ⟨s, hSF hs⟩ : Perm (Fin 7)) = h * (t : Perm (Fin 7)) * h⁻¹ := by
      rw [← hte]
      simp [MulAut.conj_apply, hh]
    rw [hιv, e1]
    have e2 : h⁻¹ * (h * (t : Perm (Fin 7)) * h⁻¹) * h = t := by group
    rw [e2]
    exact Subgroup.mem_subgroupOf.mp ht
  have hDS : ∀ d ∈ Even7.D, ∃ s, ∃ hs : s ∈ S, (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) = d := by
    intro d hd
    have hdA := Even7.D_le hd
    have h1 : MulAut.conj h₀ (⟨d, hdA⟩ : ↥(alternatingGroup (Fin 7))) ∈
        (S.subgroupOf F).map ι₀.toMonoidHom := by
      rw [hh₀]
      exact ⟨⟨d, hdA⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    obtain ⟨⟨s, hsF⟩, hs, hse⟩ := h1
    refine ⟨s, Subgroup.mem_subgroupOf.mp hs, ?_⟩
    rw [hιv]
    have e1 : (ι₀ ⟨s, hsF⟩ : Perm (Fin 7)) = h * d * h⁻¹ := by
      have := congrArg Subtype.val hse
      simpa [MulAut.conj_apply, hh] using this
    show h⁻¹ * (ι₀ ⟨s, hsF⟩ : Perm (Fin 7)) * h = d
    rw [e1]
    group
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hTN : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut (IntMod (UX615 T L H) hU))) :=
    fun t ht => hXF (autI_mono hU hTX ht)
  have hTS : ∀ t ∈ autI hU T, ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun t ht s hs =>
    ⟨(autI hU T).mul_mem ((autI hU T).mul_mem ht hs.1) ((autI hU T).inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp (hTN ht) s).mp hs.2⟩
  rcases A7N.five_or_six_ch615 ι hSF hDS le_sup_right hPKF hPKS hPKs hSPD inf_le_right hPDS hPDs
    hgen with hPD5 | ⟨hPK5, hPD6⟩
  ·
    obtain ⟨w, hw1, hwT, -, G₁, hG₁F, hs₁, hns₁, hdG₁, hG₁w⟩ :=
      A7N.good_ch615 ι β hβ hSF hSD hDS hTN hTS hdPD.2 (hPD5 d hdPD)
    have hwX : w ∈ commV (autI hU (borelL T L ⊔ H)) :=
      B19.commV_mono hFX (htop ▸ Subgroup.mem_top w)
    exact c.exists_of_fix_ch615 hU hD hw1 hwT hwX hdD hd1 (hG₁F.trans hFX) hs₁ hns₁ hdG₁ hG₁w
  ·
    exfalso
    have hJT : autI hU (thompsonJ T) ≤ autI hU T := autI_mono hU (thompsonJ_le_self T)
    have hJgen : autI hU (thompsonJ T) ≤ Subgroup.closure {y | ∃ A : Subgroup (MulAut _),
        A ≤ autI hU (thompsonJ T) ∧ IsFFStarOffender (autI hU T) A ∧ y ∈ A} := by
      refine (c.autI_thompsonJ_le_ch615 hU).trans (Subgroup.closure_mono ?_)
      rintro y ⟨A, hA, hoff, hyA⟩
      exact ⟨autI hU A, autI_mono hU (le_iSup₂_of_le A hA le_rfl), hoff, hyA⟩
    have hdJ : ∀ j ∈ autI hU (thompsonJ T), d * j * d⁻¹ ∈ autI hU (thompsonJ T) :=
      c.conj_mem_autI_thompsonJ_ch615 hU d (autI_mono hU hD.1 hdD)
    rcases A7N.bad_ch615 ι β hβ hSF hSD hDS hTN hTS hJT hJgen hKF
      (fun k hk => hPK5 k (Subgroup.mem_sup_left hk)) (c.le_commutator_ch615 hU) hdPD.2
      (hPD6 d hdPD) hdJ with hfixd | h2
    · exact c.not_fix_hall_ch615 hU hD hdD hd1 fun w hw => hfixd w fun s hs => hw s hs.1
    · exact c.autI_oTwoUpper_ne_bot_ch615 hU (autI_oTwoUpper_eq_bot_ch615 hU h2 le_rfl)

end Cx615C


theorem res615EFF_of_hat_ch615 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (hB56 : AsB56)
    (hHat : ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
      Cx615C G T M L V H n → ∀ hU : IsElemAbelian 2 (UX615 T L H),
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) →
      B56Case1 (ffJ (autI hU (borelL T L ⊔ H))) →
      IsHat ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
        ↥(alternatingGroup (Fin 6)) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)) :
    Res615EFF :=
  res615EFF_of_alt7_hat_ch615 h331 h432 hB56
    (fun _ _ _ _ _ _ _ _ _ c hU hN h1 h7 hfix => c.exists_of_case1_alt_seven_ch615 hU hN h1 h7 hfix)
    hHat

end CFSG.Quasithin.H13
