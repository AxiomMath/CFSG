module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def s208Comps (D : Data G) (N : Subgroup G) : Set (Subgroup G) :=
  {C | C ∈ CFSG.Quasithin.cComp N ∧ ¬ C ≤ D.M ∧ CFSG.Open.IsQuasisimple (Bar2 C)}

theorem s208b_le_normalizer_sSup {N : Subgroup G} {𝒦 : Set (Subgroup G)}
    (h : ∀ g ∈ N, ∀ C ∈ 𝒦, uc22p20bCj g C ∈ 𝒦) :
    N ≤ normalizer ((sSup 𝒦 : Subgroup G) : Set G) := by
  have hle : ∀ g ∈ N, uc22p20bCj g (sSup 𝒦) ≤ sSup 𝒦 := by
    intro g hg
    show (sSup 𝒦).map (MulAut.conj g).toMonoidHom ≤ sSup 𝒦
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (h g hg C hC)
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hle g hg) ?_
  have h1 := s208a_cj_le_cj (g := g) (hle g⁻¹ (N.inv_mem hg))
  rw [s208a_cj_cj_inv] at h1
  exact h1

theorem s208b_orb_mem_calLOf (D : Data G) {N C : Subgroup G} (hN : N ∈ hSet D.T D.M)
    (hC : C ∈ s208Comps D N) :
    uc22p20bOrb D.T C ∈ calLOf D.T D.M N ∧ C ∈ calC (uc22p20bOrb D.T C) := by
  obtain ⟨hCc, hCM, hCq⟩ := hC
  have hCN : C ≤ N := CFSG.Quasithin.le_of_mem_cComp hCc
  have hON : uc22p20bOrb D.T C ≤ N := uc22p20b_orb_le hN.1 hCN
  have hCO : C ≤ uc22p20bOrb D.T C := uc22p20b_le_orb D.T C
  have hcalC : C ∈ calC (uc22p20bOrb D.T C) :=
    ⟨CFSG.Quasithin.A3.subnormal_of_le_of_le (CFSG.Quasithin.subnormal_of_mem_cComp hCc) hCO hON,
      CFSG.Quasithin.perfect_of_mem_cComp hCc, hCq⟩
  refine ⟨⟨⟨uc22p20b_le_normalizer_orb D.T C,
    uc22p20b_orb_perfect (CFSG.Quasithin.perfect_of_mem_cComp hCc),
    uc22p20b_mem_hSet D hN le_sup_right (sup_le hON hN.1)
      (fun h => hCM (hCO.trans (le_sup_left.trans h))), C, hcalC, rfl⟩,
    uc22p20b_orb_subnormal hCc hN.1⟩, hcalC⟩

theorem s208b_cj_mem_comps_of_calLOf (D : Data G) {N L' K : Subgroup G} (hN : N ∈ hSet D.T D.M)
    (hL' : L' ∈ calLOf D.T D.M N) (hK : K ∈ calC L')
    (hL'K : L' = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) {t : G} (ht : t ∈ D.T) :
    uc22p20bCj t K ∈ s208Comps D N := by
  have hKN : K ∈ CFSG.Quasithin.cComp N :=
    CFSG.Quasithin.cComp_mem_of_subnormal hL'.2 (uc22p20e_cComp_of_calC hK)
  refine ⟨uc22p20b_cj_mem_cComp hKN (hN.1 ht), fun hle => ?_, ?_⟩
  · have hKM : K ≤ D.M := by
      have := s208a_cj_le_cj (g := t⁻¹) hle
      rwa [s208a_cj_inv_cj,
        s208a_cj_eq_of_mem_normalizer (Subgroup.le_normalizer (D.sylowM.le (D.T.inv_mem ht)))]
        at this
    have hL'M : L' ≤ D.M := by
      rw [hL'K]
      refine iSup_le fun s => ?_
      have := s208a_cj_le_cj (g := (s : G)) hKM
      rwa [s208a_cj_eq_of_mem_normalizer (Subgroup.le_normalizer (D.sylowM.le s.2))] at this
    exact hL'.1.2.2.1.2.1 (sup_le hL'M D.sylowM.le)
  · obtain ⟨e⟩ := s208a_bar2_cj_equiv t K
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e hK.2.2

theorem s208b_gen_eq_sSup (D : Data G) {N : Subgroup G} (hN : N ∈ hSet D.T D.M) :
    s208Gen D N = sSup (s208Comps D N) := by
  apply le_antisymm
  · refine iSup₂_le fun L' hL' => ?_
    obtain ⟨-, -, -, K, hK, hL'K⟩ := hL'.1
    rw [hL'K]
    exact iSup_le fun t =>
      le_sSup (s208b_cj_mem_comps_of_calLOf D hN hL' hK hL'K t.2)
  · exact sSup_le fun C hC =>
      (uc22p20b_le_orb D.T C).trans (s208a_le_gen D (s208b_orb_mem_calLOf D hN hC).1)

theorem s208b_exists_mul (D : Data G) (h1930 : H1930 D) (h204 : S20_4 D) {N : Subgroup G}
    (hN : N ∈ hSet D.T D.M) {g : G} (hg : g ∈ N) :
    ∃ y ∈ CFSG.Quasithin.cCompSpan N, ∃ m ∈ N ⊓ D.M, g = y * m := by
  have h := h204 h1930 N hN
  have hg' : g ∈ ((⨆ L ∈ calLOf D.T D.M N, L : Subgroup G) : Set G) *
      ((N ⊓ D.M : Subgroup G) : Set G) := by
    rw [h]
    exact hg
  obtain ⟨y, hy, m, hm, rfl⟩ := Set.mem_mul.1 hg'
  exact ⟨y, s208a_gen_le_cCompSpan D hN.1 hy, m, hm, rfl⟩

theorem s208b_cj_mem_comps (D : Data G) (h1930 : H1930 D) (h204 : S20_4 D) {N C : Subgroup G}
    (hN : N ∈ hSet D.T D.M) (hC : C ∈ s208Comps D N) {g : G} (hg : g ∈ N) :
    uc22p20bCj g C ∈ s208Comps D N := by
  obtain ⟨y, hy, m, hm, rfl⟩ := s208b_exists_mul D h1930 h204 hN hg
  obtain ⟨hCc, hCM, hCq⟩ := hC
  have hmc : uc22p20bCj m C ∈ CFSG.Quasithin.cComp N := uc22p20b_cj_mem_cComp hCc hm.1
  have hyfix : uc22p20bCj y (uc22p20bCj m C) = uc22p20bCj m C :=
    s208a_cj_eq_of_mem_normalizer (uc22p20e_cCompSpan_le_normalizer hmc hy)
  rw [← uc22p20b_cj_cj, hyfix]
  refine ⟨hmc, fun hle => hCM ?_, ?_⟩
  · have := s208a_cj_le_cj (g := m⁻¹) hle
    rwa [s208a_cj_inv_cj,
      s208a_cj_eq_of_mem_normalizer (Subgroup.le_normalizer (D.M.inv_mem hm.2))] at this
  · obtain ⟨e⟩ := s208a_bar2_cj_equiv m C
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e hCq

theorem s208b_le_normalizer_gen (D : Data G) (h1930 : H1930 D) (h204 : S20_4 D) {N : Subgroup G}
    (hN : N ∈ hSet D.T D.M) : N ≤ normalizer (s208Gen D N : Set G) := by
  rw [s208b_gen_eq_sSup D hN]
  exact s208b_le_normalizer_sSup fun g hg C hC => s208b_cj_mem_comps D h1930 h204 hN hC hg

theorem s208b_mem_calLOf_normalizer (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    L ∈ calLOf D.T D.M (normalizer (L : Set G)) :=
  ⟨hL, CFSG.Quasithin.A3.subnormal_of_normal Subgroup.le_normalizer
    ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)⟩

theorem s208b_le_X (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    L ≤ s208Gen D (normalizer (L : Set G)) :=
  s208a_le_gen D (s208b_mem_calLOf_normalizer D hL)

theorem s208b_gen_le_gen_normalizer (D : Data G) (h1930 : H1930 D) (h205 : S20_5 D)
    {L N : Subgroup G} (hL : L ∈ calLStar D.T D.M) (hN : N ∈ hSet D.T D.M)
    (hLN : L ∈ calLOf D.T D.M N) : s208Gen D N ≤ s208Gen D (normalizer (L : Set G)) := by
  refine iSup₂_le fun L' hL' => ?_
  have hL'n : L' ≤ normalizer (L : Set G) :=
    ((s208a_le_gen D hL').trans (s208a_gen_le_cCompSpan D hN.1)).trans
      (s208a_cCompSpan_le_normalizer_of_mem D hN.1 hLN)
  obtain ⟨K, hK, hL'K⟩ := h205 h1930 L' hL'.1 _ (s208a_normalizer_mem_hSet D hL.1) hL'n
  exact hL'K.trans (s208a_le_gen D hK)

theorem s208b_eq_normalizer_of_le (D : Data G) (h1930 : H1930 D) (h204 : S20_4 D) (h205 : S20_5 D)
    {L N : Subgroup G} (hL : L ∈ calLStar D.T D.M) (hN : N ∈ calMOf (L ⊔ D.T))
    (hXN : s208Gen D (normalizer (L : Set G)) ≤ N) :
    N = normalizer (s208Gen D (normalizer (L : Set G)) : Set G) := by
  have hNH : N ∈ hSet D.T D.M := s208a_mem_hSet_of_mem_calMOf D hL.1 hN
  have hLN : L ∈ calLOf D.T D.M N :=
    s208a_mem_calLOf_of_calLStar D h1930 h205 hL hNH (le_sup_left.trans hN.2)
  have hYX := s208b_gen_le_gen_normalizer D h1930 h205 hL hNH hLN
  have hXY : s208Gen D (normalizer (L : Set G)) ≤ s208Gen D N := by
    refine iSup₂_le fun L'' hL'' => ?_
    obtain ⟨K, hK, hL''K⟩ :=
      h205 h1930 L'' hL''.1 N hNH ((s208a_le_gen D hL'').trans hXN)
    exact hL''K.trans (s208a_le_gen D hK)
  have hXeq : s208Gen D (normalizer (L : Set G)) = s208Gen D N := le_antisymm hXY hYX
  have hNX : N ≤ normalizer (s208Gen D (normalizer (L : Set G)) : Set G) := by
    rw [hXeq]
    exact s208b_le_normalizer_gen D h1930 h204 hNH
  have hX : s208Gen D (normalizer (L : Set G)) ≠ ⊥ := by
    intro h
    apply uc22p20i_not_le_M D hL.1
    have := s208b_le_X D hL.1
    rw [h] at this
    exact this.trans bot_le
  exact (s208a_normalizer_eq_of_normal hN.1 hNH.2.2 hXN hNX hX).symm

theorem s208b_s20_8_of_le (D : Data G) (h204 : S20_4 D) (h205 : S20_5 D)
    (hle : H1930 D → ∀ L ∈ calLStar D.T D.M, ∀ N ∈ calMOf (L ⊔ D.T),
      s208Gen D (normalizer (L : Set G)) ≤ N) : S20_8 D := by
  intro h1930 L hL
  change calMOf (L ⊔ D.T) = {normalizer (s208Gen D (normalizer (L : Set G)) : Set G)}
  ext N
  rw [Set.mem_singleton_iff]
  constructor
  · intro hN
    exact s208b_eq_normalizer_of_le D h1930 h204 h205 hL hN (hle h1930 L hL N hN)
  · rintro rfl
    obtain ⟨N₀, hN₀⟩ := s208a_nonempty_calMOf D hL.1
    have h := s208b_eq_normalizer_of_le D h1930 h204 h205 hL hN₀ (hle h1930 L hL N₀ hN₀)
    rw [← h]
    exact hN₀

end CFSG.LocalAnalysis.UniquenessCase.UC22
