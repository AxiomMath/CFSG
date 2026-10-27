module

public import CFSG.Quasithin.Vol2.Ch4Sec1Lem412
public import CFSG.Quasithin.Background.A4Local
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M Mp Mm : Subgroup G}

theorem oTwoUpper_le_sup_of_le_sup {X A P : Subgroup G} (hXAP : X ≤ A ⊔ P)
    (hA : A ≤ Subgroup.normalizer (P : Set G)) (hPX : P ≤ X) :
    oTwoUpper X ≤ oTwoUpper (X ⊓ A) ⊔ P := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  obtain ⟨a, ha, p, hp, rfl⟩ := (mem_sup_of_le_normalizer hA).mp (hXAP hx)
  have haX : a ∈ X := by
    have := X.mul_mem hx (X.inv_mem (hPX hp))
    simpa using this
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (X ⊓ A) ⟨haX, ha⟩
  have hp' : a * p * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hA ha) p).mp hp
  obtain ⟨x', hx', he⟩ := exists_pow_mul_eq hp' (hA ha) (2 ^ k)
  refine ⟨k, ?_⟩
  have e : a * p = a * p * a⁻¹ * a := by group
  rw [e, he]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx') (Subgroup.mem_sup_left hk)

omit [Finite G] in
theorem centralizerSection_eq_inf {K M X Z : Subgroup G} (hKM : K ≤ M) :
    centralizerSection K X Z = K ⊓ centralizerSection M X Z := by
  ext m
  simp only [Subgroup.mem_inf, mem_centralizerSection]
  constructor
  · rintro ⟨hK, h1, h2, h3⟩
    exact ⟨hK, hKM hK, h1, h2, h3⟩
  · rintro ⟨hK, -, h1, h2, h3⟩
    exact ⟨hK, h1, h2, h3⟩

omit [Finite G] in
theorem normalizer_le_normalizer_of_char {C R : Subgroup G} (hCR : C ≤ R)
    (hC : (C.subgroupOf R).Characteristic) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have h := normalizer_le_normalizer_map_of_characteristic (H := R) (C.subgroupOf R)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h

theorem CGS_le_of_isUniqueM {R X M : Subgroup G} (hU : IsUniqueM X M) (hR : IsPGroup 2 R)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) : CGS R ≤ M := by
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC => iSup_le fun hch => ?_
  exact isUniqueM_normalizer_le hU hC (hR.to_le hCR)
    (hXR.trans (normalizer_le_normalizer_of_char hCR hch))

omit [Finite G] in
theorem coe_eq_inf_mul_of_eq_sup {X Y : Subgroup G} (hYX : Y ≤ X) (hX : X = Y ⊔ pCoreOf 2 X)
    (hYn : Y ≤ Subgroup.normalizer (pCoreOf 2 X : Set G)) :
    (X : Set G) = ((Y ⊓ X : Subgroup G) : Set G) * (pCoreOf 2 X : Set G) := by
  rw [inf_eq_left.mpr hYX, ← Subgroup.coe_mul_of_left_le_normalizer_right Y _ hYn, ← hX]

omit [Finite G] in
theorem coe_eq_inf_mul_self {X Y : Subgroup G} (hYX : Y ≤ X) :
    (Y : Set G) = ((X ⊓ Y : Subgroup G) : Set G) * (pCoreOf 2 Y : Set G) := by
  rw [inf_eq_right.mpr hYX,
    ← Subgroup.coe_mul_of_left_le_normalizer_right Y _ (le_normalizer_pCoreOf 2 Y),
    sup_eq_left.mpr (pCoreOf_le 2 Y)]

omit [Finite G] in
theorem isSylowTwoOf_top {T : Subgroup G} (hT : quasithinIsSylowTwo T) : IsSylowTwoOf T ⊤ :=
  isSylowTwoOf_of_le hT le_top

omit [Finite G] in
theorem normalizer_pCoreOf_eq_of_isMaxTwoLocal [Finite G] {H : Subgroup G}
    (hH : quasithinIsMaxTwoLocal H) : Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
  hH.2 _ ⟨pCoreOf 2 H, pCoreOf_ne_bot_of_isTwoLocal hH.1, pCoreOf_isPGroup 2 H, rfl⟩
    (le_normalizer_pCoreOf 2 H)

namespace Hyp4_1_1

variable (h : Hyp4_1_1 G T M Mp)
include h

theorem le_C_of_isSignalizer {Y B : Subgroup G} (hYMp : Y ≤ Mp) (hMpY : Mp = Y ⊔ pCoreOf 2 Mp)
    (hB : IsSignalizer M Y B) : B ≤ centralizerSection M Mp (pCoreOf 2 Mp) :=
  (a4_3_1 h.Mp_eq_oTwoUpper h.subnormal_Mp (hYMp.trans h.Mp_le) (coe_eq_inf_mul_self hYMp)
    (coe_eq_inf_mul_of_eq_sup hYMp hMpY
      (hYMp.trans (h.Mp_le.trans h.le_normalizer_pCoreOf_Mp)))).1 B hB

theorem Mp_eq_sup (hS : IsSigma M Mp Mm) {I H : Subgroup G} (hI : IsIota M Mp Mm I)
    (hIH : I ≤ H) : Mp = oTwoUpper (Mp ⊓ H) ⊔ pCoreOf 2 Mp := by
  have hIM : I ≤ M := hI.1.trans hS.1
  have h1 : Mp ≤ oTwoUpper (Mp ⊓ I) ⊔ pCoreOf 2 Mp := by
    have := oTwoUpper_le_sup_of_le_sup hI.2.2.1 (hIM.trans h.le_normalizer_pCoreOf_Mp)
      (pCoreOf_le 2 Mp)
    rwa [h.oTwoUpper_eq] at this
  refine le_antisymm (h1.trans (sup_le_sup_right (oTwoUpper_mono (inf_le_inf_left Mp hIH)) _))
    (sup_le ((oTwoUpper_le _).trans inf_le_left) (pCoreOf_le 2 Mp))

end Hyp4_1_1

theorem lemma_4_1_4_one (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I : Subgroup G}
    (hI : IsIota M Mp Mm I) : pCoreOf 2 I ≤ centralizerSection M Mp (pCoreOf 2 Mp) := by
  have hIM : I ≤ M := hI.1.trans hS.1
  refine h.le_C_of_isSignalizer ((oTwoUpper_le _).trans inf_le_left) (h.Mp_eq_sup hS hI le_rfl)
    ⟨(pCoreOf_le 2 I).trans hIM, pCoreOf_isPGroup 2 I, ?_⟩
  exact ((oTwoUpper_le _).trans inf_le_right).trans (le_normalizer_pCoreOf 2 I)

theorem lemma_4_1_4_three (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I H : Subgroup G}
    (hI : IsIota M Mp Mm I) (hIH : I ≤ H) :
    Mp = oTwoUpper (Mp ⊓ H) ⊔ pCoreOf 2 Mp ∧
      H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (Mp ⊓ H) : Set G) := by
  refine ⟨h.Mp_eq_sup hS hI hIH, fun g hg => ?_⟩
  exact normalizer_le_normalizer_oTwoUpper _
    (mem_normalizer_inf (h.normal hg.2) (Subgroup.le_normalizer hg.1))

theorem lemma_4_1_4_two_core (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I : Subgroup G}
    (hI : IsGammaStar M Mp Mm I) :
    ∃ X : Subgroup G, IsUniqueM X M ∧ X ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := by
  set R := pCoreOf 2 I with hRdef
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hCdef
  have hRC : R ≤ C := lemma_4_1_4_one h hS hI.1.1
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 I
  have hR1 : R ≠ ⊥ := hI.1.1.2.2.2
  have hCMm : C ≤ Mm := le_sup_right.trans hS.2
  set M₁ := Mm ⊓ Subgroup.normalizer (R : Set G) with hM₁
  have hIM₁ : I ≤ M₁ := le_inf hI.1.1.1 (le_normalizer_pCoreOf 2 I)
  have hRM₁ : R ≤ M₁ ⊓ C := le_inf ((pCoreOf_le 2 I).trans hIM₁) hRC
  obtain ⟨R₁, hR₁, hRR₁⟩ := exists_isSylowTwoOf_ge hRM₁ hR2
  obtain ⟨Rp, hRp, hR₁Rp⟩ := exists_isSylowTwoOf_ge (hR₁.1.trans inf_le_right) hR₁.2.1
  have hR₁N : R₁ ≤ Subgroup.normalizer (R : Set G) := hR₁.1.trans (inf_le_left.trans inf_le_right)
  have hR₁eq : Rp ⊓ Subgroup.normalizer (R : Set G) = R₁ := by
    refine le_antisymm ?_ (le_inf hR₁Rp hR₁N)
    refine (isSylowTwoOf_iff_maximal.mp hR₁).2.2 _ ?_ (hRp.2.1.to_le inf_le_left)
      (le_inf hR₁Rp hR₁N)
    exact le_inf (le_inf (inf_le_left.trans (hRp.1.trans hCMm)) inf_le_right)
      (inf_le_left.trans hRp.1)
  by_cases hRRp : R = Rp
  ·
    refine ⟨M ⊓ Subgroup.normalizer (Rp : Set G), lemma_4_1_2 h hRp, ?_⟩
    rw [hRRp]
    exact inf_le_right
  · have hlt : R < Rp := lt_of_le_of_ne (hRR₁.trans hR₁Rp) hRRp
    obtain ⟨x, hxRp, hxN, hxR⟩ := exists_mem_normalizer_not_mem hRp.2.1 hlt
    have hxR₁ : x ∈ R₁ := by
      rw [← hR₁eq]
      exact ⟨hxRp, hxN⟩
    have hlt₁ : R < R₁ := lt_of_le_of_ne hRR₁ fun e => hxR (e ▸ hxR₁)
    set I₁ := M₁ ⊓ Subgroup.normalizer (R₁ : Set G) with hI₁
    have hRI₁ : R ≤ pCoreOf 2 I₁ :=
      le_pCoreOf_of_le_normalizer 2
        (le_inf ((pCoreOf_le 2 I).trans hIM₁) (hRR₁.trans Subgroup.le_normalizer))
        (inf_le_left.trans inf_le_right) hR2
    have hR₁I₁ : R₁ ≤ pCoreOf 2 I₁ :=
      le_pCoreOf_of_le_normalizer 2 (le_inf (hR₁.1.trans inf_le_left) Subgroup.le_normalizer)
        inf_le_right hR₁.2.1
    have hM₁M : M₁ ≤ M := inf_le_left.trans hS.1
    have hfr : I₁ ⊔ centralizerSection M₁ Mp (pCoreOf 2 Mp) = M₁ := by
      have hsyl : IsSylowTwoOf R₁ (centralizerSection M₁ Mp (pCoreOf 2 Mp)) := by
        rw [centralizerSection_eq_inf hM₁M]
        exact hR₁
      rw [sup_comm]
      exact sup_inf_normalizer_eq (centralizerSection_le_left _ _ _)
        (le_normalizer_centralizerSection' (hM₁M.trans h.normal)) hsyl
    have hMpI₁ : Mp ⊓ M₁ ≤ I₁ := by
      intro y hy
      refine ⟨hy.2, ?_⟩
      have hyRp : y ∈ Subgroup.normalizer (Rp : Set G) := h.Mp_le_normalizer hRp hy.1
      have hyN : y ∈ Subgroup.normalizer (Subgroup.normalizer (R : Set G) : Set G) :=
        Subgroup.le_normalizer hy.2.2
      have := mem_normalizer_inf hyRp hyN
      rwa [hR₁eq] at this
    have hI₁ne : pCoreOf 2 I₁ ≠ ⊥ := fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRI₁))
    have hle : OrdLE Mp I I₁ := ⟨hRI₁, fun y hy => ⟨hMpI₁ ⟨hy.2, hIM₁ hy.1⟩, hy.2⟩⟩
    have hU := lemma_4_1_3_two h hS hI hIM₁ inf_le_left inf_le_left hI₁ne hfr
      (hMpI₁.trans le_sup_left) hle (hlt₁.trans_le hR₁I₁)
    exact ⟨I₁, hU, inf_le_left.trans inf_le_right⟩

theorem lemma_4_1_4_two (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I : Subgroup G}
    (hI : IsGammaStar M Mp Mm I) : CGS (pCoreOf 2 I) ≤ M := by
  obtain ⟨X, hU, hX⟩ := lemma_4_1_4_two_core h hS hI
  exact CGS_le_of_isUniqueM hU (pCoreOf_isPGroup 2 I) hX

theorem lemma_4_1_4_two_normalizer (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm)
    {I : Subgroup G} (hI : IsGammaStar M Mp Mm I) :
    Subgroup.normalizer (pCoreOf 2 I : Set G) ≤ M := by
  obtain ⟨X, hU, hX⟩ := lemma_4_1_4_two_core h hS hI
  exact isUniqueM_normalizer_le hU hI.1.1.2.2.2 (pCoreOf_isPGroup 2 I) hX

theorem lemma_4_1_4_four_inf (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I H : Subgroup G}
    (hI : IsGammaStar M Mp Mm I) (hH : InH I H) (hHM : ¬ H ≤ M) :
    IsSylowTwoOf (pCoreOf 2 I)
      (centralizerSection (H ⊓ M) (oTwoUpper (Mp ⊓ H)) (pCoreOf 2 (oTwoUpper (Mp ⊓ H)))) := by
  set R := pCoreOf 2 I with hRdef
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hCdef
  set Hp := oTwoUpper (Mp ⊓ H) with hHpdef
  set CHM := centralizerSection (H ⊓ M) Hp (pCoreOf 2 Hp) with hCHM
  have hIH : I ≤ H := hH.1
  have hRC : R ≤ C := lemma_4_1_4_one h hS hI.1.1
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 I
  have hR1 : R ≠ ⊥ := hI.1.1.2.2.2
  have hCMm : C ≤ Mm := le_sup_right.trans hS.2
  obtain ⟨hMpHp, hHMn⟩ := lemma_4_1_4_three h hS hI.1.1 hIH
  have hHpMp : Hp ≤ Mp := (oTwoUpper_le _).trans inf_le_left
  have hHpH : Hp ≤ H := (oTwoUpper_le _).trans inf_le_right
  have hHpHM : Hp ≤ H ⊓ M := le_inf hHpH (hHpMp.trans h.Mp_le)
  have hHp : Hp = oTwoUpper Hp := (A4.oTwoUpper_oTwoUpper _).symm
  have hsub : IsSubnormal Hp (H ⊓ M) :=
    subnormal_of_normal hHpHM (Subgroup.normal_subgroupOf_of_le_normalizer hHMn)
  have hCHMle : CHM ≤ H ⊓ M := centralizerSection_le_left _ _ _
  have hSylC : ∀ S, IsSylowTwoOf S CHM → S ≤ C := fun S hSs =>
    h.le_C_of_isSignalizer hHpMp hMpHp
      ⟨hSs.1.trans (hCHMle.trans inf_le_right), hSs.2.1, ((a4_2_4 hHp hsub S).mpr hSs).1.2.2⟩
  have hHpO2 : Hp ⊓ pCoreOf 2 Mp ≤ pCoreOf 2 Hp :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
        (h.le_normalizer_pCoreOf_Mp (h.Mp_le (hHpMp hg))))
      ((pCoreOf_isPGroup 2 Mp).to_le inf_le_right)
  have hHC : H ⊓ C ≤ CHM := by
    intro c hc
    rw [hCHM, mem_centralizerSection_iff_of_le (pCoreOf_le 2 Hp)]
    have hcM : c ∈ M := centralizerSection_le_left _ _ _ hc.2
    refine ⟨⟨hc.1, hcM⟩, fun x hx => ?_⟩
    have h1 : x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 Mp :=
      (mem_centralizerSection.mp hc.2).2.2.2 x (hHpMp hx)
    have hcn : c ∈ Subgroup.normalizer (Hp : Set G) := hHMn ⟨hc.1, hcM⟩
    have h2 : x * c * x⁻¹ * c⁻¹ ∈ Hp := by
      have h3 : c * x⁻¹ * c⁻¹ ∈ Hp := (Subgroup.mem_normalizer_iff.mp hcn _).mp (Hp.inv_mem hx)
      have := Hp.mul_mem hx h3
      simpa [mul_assoc] using this
    exact hHpO2 ⟨h2, h1⟩
  have hRHC : R ≤ H ⊓ C := le_inf ((pCoreOf_le 2 I).trans hIH) hRC
  by_contra hns
  obtain ⟨S, hSs, hRS⟩ := exists_isSylowTwoOf_ge (hRHC.trans hHC) hR2
  have hRlt : R < S := lt_of_le_of_ne hRS fun e => hns (e ▸ hSs)
  have hSHC : S ≤ H ⊓ C := le_inf (hSs.1.trans (hCHMle.trans inf_le_left)) (hSylC S hSs)
  set H₁ := H ⊓ Mm ⊓ Subgroup.normalizer (R : Set G) with hH₁
  have hIH₁ : I ≤ H₁ := le_inf (le_inf hIH hI.1.1.1) (le_normalizer_pCoreOf 2 I)
  have hRH₁C : R ≤ H₁ ⊓ C := le_inf ((pCoreOf_le 2 I).trans hIH₁) hRC
  obtain ⟨R₁, hR₁, hRR₁⟩ := exists_isSylowTwoOf_ge hRH₁C hR2
  have hR₁HC : R₁ ≤ H ⊓ C :=
    le_inf (hR₁.1.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
      (hR₁.1.trans inf_le_right)
  obtain ⟨RH, hRH, hR₁RH⟩ := exists_isSylowTwoOf_ge hR₁HC hR₁.2.1
  have hR₁N : R₁ ≤ Subgroup.normalizer (R : Set G) := hR₁.1.trans (inf_le_left.trans inf_le_right)
  have hRHeq : RH ⊓ Subgroup.normalizer (R : Set G) = R₁ := by
    refine le_antisymm ?_ (le_inf hR₁RH hR₁N)
    refine (isSylowTwoOf_iff_maximal.mp hR₁).2.2 _ ?_ (hRH.2.1.to_le inf_le_left)
      (le_inf hR₁RH hR₁N)
    refine le_inf (le_inf (le_inf (inf_le_left.trans (hRH.1.trans inf_le_left))
      (inf_le_left.trans (hRH.1.trans (inf_le_right.trans hCMm)))) inf_le_right)
      (inf_le_left.trans (hRH.1.trans inf_le_right))
  have hRHs : IsSylowTwoOf RH CHM := by
    obtain ⟨S', hS', hRHS'⟩ := exists_isSylowTwoOf_ge (hRH.1.trans hHC) hRH.2.1
    have hS'HC : S' ≤ H ⊓ C := le_inf (hS'.1.trans (hCHMle.trans inf_le_left)) (hSylC S' hS')
    have heq := (isSylowTwoOf_iff_maximal.mp hRH).2.2 S' hS'HC hS'.2.1 hRHS'
    rwa [le_antisymm heq hRHS'] at hS'
  have hRRH : R < RH := by
    refine lt_of_le_of_ne (hRR₁.trans hR₁RH) fun e => ?_
    rw [← e] at hRH
    exact hRlt.not_ge ((isSylowTwoOf_iff_maximal.mp hRH).2.2 S hSHC hSs.2.1 hRS)
  obtain ⟨x, hxRH, hxN, hxR⟩ := exists_mem_normalizer_not_mem hRH.2.1 hRRH
  have hxR₁ : x ∈ R₁ := by
    rw [← hRHeq]
    exact ⟨hxRH, hxN⟩
  have hlt₁ : R < R₁ := lt_of_le_of_ne hRR₁ fun e => hxR (e ▸ hxR₁)
  set I₁ := H₁ ⊓ Subgroup.normalizer (R₁ : Set G) with hI₁
  have hRI₁ : R ≤ pCoreOf 2 I₁ :=
    le_pCoreOf_of_le_normalizer 2
      (le_inf ((pCoreOf_le 2 I).trans hIH₁) (hRR₁.trans Subgroup.le_normalizer))
      (inf_le_left.trans inf_le_right) hR2
  have hR₁I₁ : R₁ ≤ pCoreOf 2 I₁ :=
    le_pCoreOf_of_le_normalizer 2 (le_inf (hR₁.1.trans inf_le_left) Subgroup.le_normalizer)
      inf_le_right hR₁.2.1
  have hH₁Mm : H₁ ≤ Mm := inf_le_left.trans inf_le_right
  have hH₁M : H₁ ≤ M := hH₁Mm.trans hS.1
  have hfr : I₁ ⊔ centralizerSection H₁ Mp (pCoreOf 2 Mp) = H₁ := by
    have hsyl : IsSylowTwoOf R₁ (centralizerSection H₁ Mp (pCoreOf 2 Mp)) := by
      rw [centralizerSection_eq_inf hH₁M]
      exact hR₁
    rw [sup_comm]
    exact sup_inf_normalizer_eq (centralizerSection_le_left _ _ _)
      (le_normalizer_centralizerSection' (hH₁M.trans h.normal)) hsyl
  have hO2RH : pCoreOf 2 Mp ⊓ H ≤ RH := by
    refine le_of_normal_of_isSylowTwoOf hRH
      (le_inf inf_le_right (inf_le_left.trans (pCoreOf_le_centralizerSection h.Mp_le))) ?_
      ((pCoreOf_isPGroup 2 Mp).to_le inf_le_left)
    refine Subgroup.normal_subgroupOf_of_le_normalizer fun g hg => ?_
    exact mem_normalizer_inf (centralizerSection_le_normalizer_right _ _ _ hg.2)
      (Subgroup.le_normalizer hg.1)
  have hHpRH : Hp ≤ Subgroup.normalizer (RH : Set G) := ((a4_2_4 hHp hsub RH).mpr hRHs).1.2.2
  have hMpH₁ : Mp ⊓ H₁ ≤ I₁ := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    have hyRH : y ∈ Subgroup.normalizer (RH : Set G) := by
      have hyMp : y ∈ Hp ⊔ pCoreOf 2 Mp := hMpHp ▸ hy.1
      obtain ⟨a, ha, o, ho, rfl⟩ :=
        (mem_sup_of_le_normalizer (hHpMp.trans (h.Mp_le.trans h.le_normalizer_pCoreOf_Mp))).mp
          hyMp
      have hoH : o ∈ H := by
        have := H.mul_mem (H.inv_mem (hHpH ha)) hy.2.1.1
        simpa using this
      exact Subgroup.mul_mem _ (hHpRH ha) (Subgroup.le_normalizer (hO2RH ⟨ho, hoH⟩))
    have hyN : y ∈ Subgroup.normalizer (Subgroup.normalizer (R : Set G) : Set G) :=
      Subgroup.le_normalizer hy.2.2
    have := mem_normalizer_inf hyRH hyN
    rwa [hRHeq] at this
  have hI₁ne : pCoreOf 2 I₁ ≠ ⊥ := fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRI₁))
  have hι := lemma_4_1_3_one h hS hI.1.1 hIH₁ hH₁Mm inf_le_left hI₁ne hfr (hMpH₁.trans le_sup_left)
  have hΓ : IsGamma M Mp Mm I₁ :=
    ⟨hι, H, ⟨inf_le_left.trans (inf_le_left.trans inf_le_left), hH.2⟩, hHM⟩
  exact hI.2 I₁ hΓ ⟨hRI₁, fun y hy => ⟨hMpH₁ ⟨hy.2, hIH₁ hy.1⟩, hy.2⟩⟩ (hlt₁.trans_le hR₁I₁)

theorem lemma_4_1_4_four (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I H : Subgroup G}
    (hI : IsGammaStar M Mp Mm I) (hH : InH I H) (hHM : ¬ H ≤ M) :
    IsSylowTwoOf (pCoreOf 2 I)
        (centralizerSection H (oTwoUpper (Mp ⊓ H)) (pCoreOf 2 (oTwoUpper (Mp ⊓ H)))) ∧
      IsSylowTwoOf (pCoreOf 2 I)
        (centralizerSection (H ⊓ M) (oTwoUpper (Mp ⊓ H)) (pCoreOf 2 (oTwoUpper (Mp ⊓ H)))) := by
  have h4 := lemma_4_1_4_four_inf h hS hI hH hHM
  refine ⟨?_, h4⟩
  have hNR := lemma_4_1_4_two_normalizer h hS hI
  obtain ⟨S, hSs, hRS⟩ := exists_isSylowTwoOf_ge
    (h4.1.trans (centralizerSection_mono inf_le_left _ _)) (pCoreOf_isPGroup 2 I)
  have hle : S ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G) ≤ pCoreOf 2 I := by
    refine (isSylowTwoOf_iff_maximal.mp h4).2.2 _ ?_ (hSs.2.1.to_le inf_le_left)
      (le_inf hRS Subgroup.le_normalizer)
    rw [centralizerSection_eq_inf (inf_le_left : H ⊓ M ≤ H)]
    exact le_inf (le_inf (inf_le_left.trans (hSs.1.trans (centralizerSection_le_left _ _ _)))
      (inf_le_right.trans hNR)) (inf_le_left.trans hSs.1)
  have hRS' : pCoreOf 2 I = S := by
    by_contra hne
    obtain ⟨x, hxS, hxN, hxR⟩ :=
      exists_mem_normalizer_not_mem hSs.2.1 (lt_of_le_of_ne hRS hne)
    exact hxR (hle ⟨hxS, hxN⟩)
  rw [hRS']
  exact hSs

theorem lemma_4_1_4_five (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I H : Subgroup G}
    (hI : IsGammaStar M Mp Mm I) (hH : InH I H) (hHM : ¬ H ≤ M) :
    pCoreOf 2 I = pCoreOf 2 (H ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G)) ∧
      IsTwoRadicalIn H (pCoreOf 2 I) ∧ pCoreOf 2 H ≤ pCoreOf 2 (H ⊓ M) ∧
      pCoreOf 2 (H ⊓ M) ≤ pCoreOf 2 I := by
  set R := pCoreOf 2 I with hRdef
  set Hp := oTwoUpper (Mp ⊓ H) with hHpdef
  have h4 := (lemma_4_1_4_four h hS hI hH hHM).2
  have hNR := lemma_4_1_4_two_normalizer h hS hI
  obtain ⟨-, hHMn⟩ := lemma_4_1_4_three h hS hI.1.1 hH.1
  have hHpMp : Hp ≤ Mp := (oTwoUpper_le _).trans inf_le_left
  have hHpHM : Hp ≤ H ⊓ M := le_inf ((oTwoUpper_le _).trans inf_le_right) (hHpMp.trans h.Mp_le)
  have hrad := (c1_2_four (A4.oTwoUpper_oTwoUpper _).symm hHpHM
    (Subgroup.normal_subgroupOf_of_le_normalizer hHMn) h4 hI.1.1.2.2.2).2
  have he : H ⊓ M ⊓ Subgroup.normalizer (R : Set G) = H ⊓ Subgroup.normalizer (R : Set G) := by
    rw [inf_assoc, inf_eq_right.mpr hNR]
  have hRH : R ≤ H := hrad.1.trans inf_le_left
  have hrad' : IsTwoRadicalIn H R := ⟨hRH, hrad.2.1, by rw [← he]; exact hrad.2.2⟩
  have hHR := c2_1_pCore_le hrad'
  refine ⟨hrad'.2.2, hrad', ?_, c2_1_pCore_le hrad⟩
  exact le_pCoreOf_of_le_normalizer 2 (hHR.trans hrad.1)
    (inf_le_left.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)

theorem lemma_4_1_4_six (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {I H : Subgroup G}
    (hI : IsGammaStar M Mp Mm I) (hH : InH I H) (hHM : ¬ H ≤ M) : CharTwo (H ⊓ M) := by
  obtain ⟨H₁, hH₁, hHH₁⟩ := exists_inM_of_pCoreOf_ne_bot hH.2
  have hH₁M : ¬ H₁ ≤ M := fun hle => hHM (hHH₁.trans hle)
  have hIH₁ : InH I H₁ := ⟨hH.1.trans hHH₁, pCoreOf_ne_bot_of_isTwoLocal hH₁.1⟩
  obtain ⟨-, -, h5a, h5b⟩ := lemma_4_1_4_five h hS hI hIH₁ hH₁M
  have hc : CharTwo (H₁ ⊓ M) := by
    refine charTwo_of_isTwoLocal_of_pCore_centralizer_le h.qtke.2.1 (isSylowTwoOf_top h.sylow)
      h.maxTwoLocal.1 h.T_le inf_le_right ?_
    intro x hx
    refine ⟨?_, (pCoreOf_le 2 M) hx.1⟩
    have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 H₁ : Set G) :=
      Subgroup.centralizer_le h5a hx.2
    rw [← normalizer_pCoreOf_eq_of_isMaxTwoLocal hH₁]
    exact Subgroup.centralizer_le_normalizer _ hxc
  have hRHM : pCoreOf 2 I ≤ H ⊓ M :=
    (pCoreOf_le 2 I).trans (le_inf hH.1 (hI.1.1.1.trans hS.1))
  have hO : pCoreOf 2 (H₁ ⊓ M) ≤ pCoreOf 2 (H ⊓ M) :=
    le_pCoreOf_of_le_normalizer 2 (h5b.trans hRHM)
      ((inf_le_inf_right M hHH₁).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  intro x hx
  exact hO (hc ⟨inf_le_inf_right M hHH₁ hx.1, Subgroup.centralizer_le hO hx.2⟩)

end CFSG.Quasithin.H13.Ch4
