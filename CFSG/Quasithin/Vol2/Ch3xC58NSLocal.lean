module

public import CFSG.Quasithin.Vol2.Ch3xC58NSSingle
public import CFSG.Quasithin.Vol2.Ch3xC58NSA5Two
public import CFSG.Quasithin.Vol2.Ch3xC58NSGamma
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Commutation

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.C58 Subgroup

variable {G : Type} [Group G] [Finite G]

namespace BlockConfigNS

variable {H T R K₁ : Subgroup G} (hcfg : BlockConfigNS H T R K₁)
include hcfg

theorem le_oTwoUpper : K₁ ≤ oTwoUpper H :=
  calc K₁ = oTwoUpper K₁ := C1Pack.isShort2_eq_oTwoUpper hcfg.short
    _ ≤ oTwoUpper H := oTwoUpper_mono hcfg.le_H

theorem syl_R (hT2 : IsPGroup 2 T) (hRT : R ≤ T) (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R)) :
    IsSylowTwoOf (R ⊓ K₁) K₁ := by
  have hTKR : T ⊓ (oTwoUpper H ⊔ R) ≤ R :=
    (A4.isSylowTwoOf_iff_maximal.mp hRsyl).2.2 _ inf_le_right (hT2.to_le inf_le_left)
      (le_inf hRT le_sup_right)
  have e : R ⊓ K₁ = T ⊓ K₁ := le_antisymm (inf_le_inf_right _ hRT) fun g hg =>
    ⟨hTKR ⟨hg.1, le_sup_left (b := R) (hcfg.le_oTwoUpper hg.2)⟩, hg.2⟩
  rw [e]; exact hcfg.syl

omit [Finite G] in
theorem perm_R (hRT : R ≤ T) : ∀ g ∈ R, g ∉ normalizer (K₁ : Set G) →
    ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ g, a * b = b * a := by
  intro g hg hgN
  rcases hcfg.perm g (hRT hg) with h | h
  · exact absurd (conjSubgroup_eq_iff_mem_normalizer.mp h) hgN
  · exact h

theorem baum_facts (hT2 : IsPGroup 2 T) (hRT : R ≤ T) (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R)) :
    baum R ≤ normalizer (K₁ : Set G) ∧
      baum R = baum (R ⊓ normalizer (K₁ : Set G)) ∧
      thompsonJ (R ⊓ normalizer (K₁ : Set G)) = thompsonJ R ∧
      IsSylowTwoOf ((R ⊓ normalizer (K₁ : Set G)) ⊓ K₁) K₁ ∧
      IsSylowTwoOf (R ⊓ normalizer (K₁ : Set G)) (K₁ ⊔ (R ⊓ normalizer (K₁ : Set G))) ∧
      blockU K₁ ≤ R ⊓ normalizer (K₁ : Set G) := by
  set R₁ := R ⊓ normalizer (K₁ : Set G) with hR₁
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  have hR₁2 : IsPGroup 2 R₁ := hR2.to_le inf_le_left
  have hR₁N : R₁ ≤ normalizer (K₁ : Set G) := inf_le_right
  have hJN : thompsonJ R ≤ normalizer (K₁ : Set G) := C56.le_normalizer_of_commutator_eq hcfg.comm_J
  have hJR₁ : thompsonJ R ≤ R₁ := le_inf (GammaExtra.thompsonJ_le_self R) hJN
  have hJeq : thompsonJ R₁ = thompsonJ R := GammaExtra.thompsonJ_eq_of_le hJR₁ inf_le_left
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hcfg.short).trans (C1.blockQ_le K₁)
  have hUR₁ : blockU K₁ ≤ R₁ := le_inf hcfg.U_le_R (hUK.trans Subgroup.le_normalizer)
  have hsyl₁ : IsSylowTwoOf (R₁ ⊓ K₁) K₁ := by
    have e : R₁ ⊓ K₁ = R ⊓ K₁ :=
      le_antisymm (inf_le_inf_right _ inf_le_left)
        (le_inf (le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)) inf_le_right)
    rw [e]; exact hcfg.syl_R hT2 hRT hRsyl
  obtain ⟨e, heU, heZ, hec⟩ :=
    exists_central_of_block hcfg.short hcfg.typ hR₁2 hR₁N hsyl₁ hUR₁
  have hSN : baum R ≤ normalizer (K₁ : Set G) :=
    baum_le_normalizer_of_central hcfg.short (hcfg.perm_R hRT) heU heZ (hcfg.U_le_R heU)
      (fun y hy => hec y (hJR₁ hy))
  have hBeq : baum R = baum R₁ := baum_eq_of_le (le_inf inf_le_left hSN) inf_le_left
  exact ⟨hSN, hBeq, hJeq, hsyl₁,
    CFSG.Quasithin.H13.VolI.isSylowTwoOf_sup_of_inf hR₁2 hR₁N hsyl₁, hUR₁⟩

omit [Finite G] in
theorem exists_conj_not_le_centralizer {M₀ : Subgroup G} (hNC : NoCommonNormal R H M₀)
    (hTM₀ : T ≤ M₀) (hM₀R : M₀ ≤ normalizer (R : Set G)) (hRT : R ≤ T) (hTH : T ≤ H)
    (hH : H ≤ oTwoUpper H ⊔ T) (hUS : blockU K₁ ≤ baum R) :
    ∃ x ∈ M₀, ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G) := by
  set U₁ := blockU K₁ with hU₁
  set U₀ := conjClosure U₁ M₀ with hU₀
  have hM₀S : M₀ ≤ normalizer ((baum R : Subgroup G) : Set G) :=
    hM₀R.trans (normalizer_le_normalizer_baum R)
  have hSR : baum R ≤ R := inf_le_left
  have hU₀R : U₀ ≤ R := conjClosure_le fun m hm u hu =>
    (mem_normalizer_iff.mp (hM₀R hm) u).mp (hcfg.U_le_R hu)
  have hU₁ne : U₁ ≠ ⊥ := by
    intro h
    have h1 := hcfg.short.2.2.2.2.1
    rw [← hU₁, h] at h1
    exact (not_lt_bot h1).elim
  have hU₀ne : U₀ ≠ ⊥ := fun h => hU₁ne (le_bot_iff.mp (h ▸ le_conjClosure U₁ M₀))
  have hM₀U₀ : M₀ ≤ normalizer (U₀ : Set G) := le_normalizer_conjClosure U₁ M₀
  by_contra hall
  push Not at hall
  have hconj : ∀ x ∈ M₀, conjSubgroup U₁ x ≤ pCoreOf 2 H := by
    intro x hx
    have hxH : conjSubgroup U₁ x ≤ T := by
      have h1 := conjSubgroup_mono hUS x
      rw [conjSubgroup_eq_iff_mem_normalizer.mpr (hM₀S hx)] at h1
      exact h1.trans (hSR.trans hRT)
    have hxC : conjSubgroup U₁ x ≤
        centralizer ((⨆ (g : G) (_ : g ∈ T), conjSubgroup U₁ g : Subgroup G) : Set G) := by
      rw [le_centralizer_iff]
      refine iSup₂_le fun g hg => ?_
      rw [← le_centralizer_iff]
      have h1 := hall (x * g⁻¹) (mul_mem hx (inv_mem (hTM₀ hg)))
      rw [← conjSubgroup_conjSubgroup] at h1
      have h2 := (DoubleA3.le_centralizer_iff_conj g).mp h1
      rwa [conjSubgroup_inv_conjSubgroup] at h2
    exact (le_inf hxH hxC).trans hcfg.CH
  have hU₀Q : U₀ ≤ pCoreOf 2 H := by
    refine conjClosure_le fun m hm u hu => ?_
    have := hconj m⁻¹ (inv_mem hm)
    exact this (mem_conjSubgroup_iff.mpr (by
      have e : m⁻¹ * (m * u * m⁻¹) * m⁻¹⁻¹ = u := by group
      rw [e]; exact hu))
  have hQn : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hKU₀ : ∀ g ∈ T, conjSubgroup K₁ g ≤ normalizer (U₀ : Set G) := by
    intro g hg
    have key : ∀ k ∈ conjSubgroup K₁ g, ∀ u ∈ U₀, k * u * k⁻¹ ∈ U₀ := by
      intro k hk u hu
      rw [mem_conjSubgroup_iff] at hk
      have hgu : g * u * g⁻¹ ∈ pCoreOf 2 H :=
        (mem_normalizer_iff.mp (hQn (hTH hg)) u).mp (hU₀Q hu)
      have hw := hcfg.QH _ hgu _ hk
      set w := g * k * g⁻¹ * (g * u * g⁻¹) * (g * k * g⁻¹)⁻¹ * (g * u * g⁻¹)⁻¹ with hw'
      have e : k * u * k⁻¹ = (g⁻¹ * w * g) * u := by rw [hw']; group
      rw [e]
      refine mul_mem ?_ hu
      have := mem_conjClosure (inv_mem (hTM₀ hg)) hw
      simpa using this
    intro k hk
    exact B6.mem_normalizer_of_forall_mem (fun u hu => key k hk u hu)
      (fun u hu => by simpa using key k⁻¹ (inv_mem hk) u hu)
  have hHU₀ : H ≤ normalizer (U₀ : Set G) := by
    refine hH.trans (sup_le ?_ (hTM₀.trans hM₀U₀))
    exact hcfg.gen.trans (iSup₂_le fun g hg => hKU₀ g hg)
  exact hNC U₀ hU₀R hU₀ne hHU₀ hM₀U₀

theorem exists_good_elt {M₀ : Subgroup G} (hNC : NoCommonNormal R H M₀)
    (hT : IsSylowTwoOf T M₀) (hM₀R : M₀ ≤ normalizer (R : Set G)) (hRT : R ≤ T) (hTH : T ≤ H)
    (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R)) (hH : H ≤ oTwoUpper H ⊔ T) :
    ¬ T ≤ normalizer (K₁ : Set G) ∧ ∃ x ∈ M₀,
      x ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) ∧
      ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G) := by
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTM₀ : T ≤ M₀ := hT.1
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  set R₁ := R ⊓ normalizer (K₁ : Set G) with hR₁
  have hR₁2 : IsPGroup 2 R₁ := hR2.to_le inf_le_left
  have hR₁N : R₁ ≤ normalizer (K₁ : Set G) := inf_le_right
  obtain ⟨hSN, hBeq, hJeq, hsyl₁, hsylR₁, hUR₁⟩ := hcfg.baum_facts hT2 hRT hRsyl
  have hJ₁ : ⁅K₁, thompsonJ R₁⁆ = K₁ := by rw [hJeq]; exact hcfg.comm_J
  have hS2 : IsPGroup 2 (baum R) := hR2.to_le inf_le_left
  have hM₀S : M₀ ≤ normalizer ((baum R : Subgroup G) : Set G) :=
    hM₀R.trans (normalizer_le_normalizer_baum R)
  rcases hcfg.typ with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨hsyl, hc542⟩ := lin2_single hcfg.short hn hlin hR₁2 hR₁N hsyl₁ hJ₁
    rw [← hBeq] at hsyl hc542
    have hUS : blockU K₁ ≤ baum R :=
      (rank1_of_lin2 hcfg.short hn hlin hS2 hSN hsyl hc542).2.2.1
    obtain ⟨y, hyM₀, hyU⟩ := hcfg.exists_conj_not_le_centralizer hNC hTM₀ hM₀R hRT hTH hH hUS
    exact lin2_exists_good_elt hcfg.short hn hlin hS2 hSN hsyl hc542 hT hM₀S hcfg.index
      hyM₀ hyU
  · have hUS : blockU K₁ ≤ baum R := by
      rw [hBeq]; exact a5_blockU_le_baum hcfg.short h5 hR₁2 hR₁N hsylR₁
    have hQD : baum R ⊓ centralizer (blockU K₁ : Set G) =
        blockU K₁ ⊔ (baum R ⊓ centralizer (K₁ : Set G)) := by
      rw [hBeq]; exact a5_baum_inf_centralizer hcfg.short h5 hR₁2 hR₁N hsylR₁
    obtain ⟨P₀⟩ := nonempty_a5pi hcfg.short h5
    obtain ⟨P, -, hPB, -⟩ := exists_a5Pi_std hcfg.short hR₁N hUR₁ hsylR₁ hJ₁ P₀
    rw [← hBeq] at hPB
    have hc : A5Cfg K₁ R (baum R) P :=
      { short := hcfg.short
        alt := h5
        SR := inf_le_left
        RS := Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum R)
        SN := hSN
        US := hUS
        QD := hQD
        SE := hPB
        syl := hcfg.syl_R hT2 hRT hRsyl
        perm := hcfg.perm_R hRT }
    obtain ⟨y, hyM₀, hyU⟩ := hcfg.exists_conj_not_le_centralizer hNC hTM₀ hM₀R hRT hTH hH hUS
    exact hc.exists_good_elt hT hM₀S hM₀R hcfg.index hyM₀ hyU

end BlockConfigNS

end CFSG.Quasithin.C58NS
