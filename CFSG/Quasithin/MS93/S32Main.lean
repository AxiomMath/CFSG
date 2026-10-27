module

public import CFSG.Quasithin.MS93.S32Tr
public import CFSG.Quasithin.MS93.S32XCases
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S32PartXU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    B51Case1ii (ffJ (autI h.isElemAbelian_Xq M)) (autI h.isElemAbelian_Xq L) →
      ⁅Xq M, L⁆ = Uq M T L

@[expose] def S32PartG2Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L) (n : ℕ), 2 ≤ n →
    G2Natural (autI h.isElemAbelian_Uq L) ⊤ (fixV (autI h.isElemAbelian_Uq L)) n →
    (fixV (autI h.isElemAbelian_Uq L) = ⊥ ∨ (fixV (autI h.isElemAbelian_Uq L) ≠ ⊥ ∧
      XMod.IsIrrSec ↥(autI h.isElemAbelian_Uq L) (fixV (autI h.isElemAbelian_Uq L)) ⊤ ∧
      MS15CaseG2 (autI h.isElemAbelian_Uq M) (autI h.isElemAbelian_Uq L))) → False

@[expose] def S32PartG2Vertex : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    G2NaturalDerived (autI h.isElemAbelian_Uq L) ⊤ (fixV (autI h.isElemAbelian_Uq L)) 1 →
    (fixV (autI h.isElemAbelian_Uq L) = ⊥ ∨ (fixV (autI h.isElemAbelian_Uq L) ≠ ⊥ ∧
      XMod.IsIrrSec ↥(autI h.isElemAbelian_Uq L) (fixV (autI h.isElemAbelian_Uq L)) ⊤ ∧
      MS15CaseG2 (autI h.isElemAbelian_Uq M) (autI h.isElemAbelian_Uq L))) →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) = puTrans h.le (Uq M T L) α' ⊓
          Subgroup.centralizer (puTrans h.le L α' : Set (puAmalgam h.le).Universal) ∧
        imM h.le (Uq M T L ⊓ Zq M L) ≤ ⁅ZM (puAmalgam h.le) (baseA _), ZM (puAmalgam h.le) α'⁆

@[expose] def S32PartG2Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    G2NaturalDerived (autI h.isElemAbelian_Uq L) ⊤ (fixV (autI h.isElemAbelian_Uq L)) 1 →
    ⁅Xq M, L⁆ = Uq M T L → Xq M = Z0q M T ∧ Z0q M T = Zq M L ⊔ Uq M T L

@[expose] def S32PartHat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    TripleA6Six (autI h.isElemAbelian_Uq L) ⊤ ⊥ → fixV (autI h.isElemAbelian_Uq L) = ⊥ →
    ⁅Xq M, L⁆ = Uq M T L → Xq M = Zq M L ⊔ Uq M T L

@[expose] def S32PartL3Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    MS15CaseL3 (autI h.isElemAbelian_Uq M) (autI h.isElemAbelian_Uq L) →
    ⁅Xq M, L⁆ = Uq M T L → IsSL3TwoU M T L

@[expose] def S32PartL3NonSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), Nat.card F = 2 ^ n →
    (FFModel.nat (StatedSL 3 F)).Realizes (autI h.isElemAbelian_Uq L) ⊤ ⊥ →
    fixV (autI h.isElemAbelian_Uq L) = ⊥ → ⁅Xq M, L⁆ = Uq M T L →
    ¬ (Uq M T L ⊔ Zq M L = Xq M) → IsSL3TwoZ M T L

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem toG_bot {V : Subgroup G} (hV : IsElemAbelian 2 V) : C124.toG hV ⊥ = ⊥ :=
  Subgroup.map_bot _

theorem intSub_toG {V : Subgroup G} (hV : IsElemAbelian 2 V) (W : Subgroup (IntMod V hV)) :
    intSub hV (C124.toG hV W) = W :=
  Subgroup.comap_map_eq_self_of_injective (C124.valHom_injective hV) W

theorem isIrrSec_of_irrSecG {V : Subgroup G} (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G)) {A B : Subgroup (IntMod V hV)}
    (h : IrrSecG K (C124.toG hV A) (C124.toG hV B)) : XMod.IsIrrSec ↥(autI hV K) A B := by
  refine ⟨lt_of_le_of_ne ((C124.toG_le_iff hV).mp h.1.le) fun he => h.1.ne (by rw [he]),
    fun J hJ hAJ hJB => ?_⟩
  have hinv := (C124.isInv_iff hV hK).mp hJ
  have hJn : K ≤ Subgroup.normalizer (C124.toG hV J : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hinv g hg w hw, fun hw => ?_⟩
    have := hinv g⁻¹ (K.inv_mem hg) _ hw
    rwa [inv_inv, show g⁻¹ * (g * w * g⁻¹) * g = w by group] at this
  rcases h.2 _ hJn ((C124.toG_le_iff hV).mpr hAJ) ((C124.toG_le_iff hV).mpr hJB) with he | he
  · exact Or.inl ((C124.toG_inj hV).mp he)
  · exact Or.inr ((C124.toG_inj hV).mp he)

end Helpers

section DirectSum

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}

theorem inf_eq_bot_of_iSupIndep {I : Fin 2 → Subgroup V} (hind : iSupIndep I) : I 0 ⊓ I 1 = ⊥ :=
  (hind.pairwiseDisjoint (show (0 : Fin 2) ≠ 1 by decide)).eq_bot

theorem iSup_fin_two_eq (I : Fin 2 → Subgroup V) : (⨆ i, I i) = I 0 ⊔ I 1 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup I 0) (le_iSup I 1)

theorem not_isIrrSec_of_directSum {F : Type} [Field F]
    (hd : DirectSumOfCopies K ⊤ ⊥ (FFModel.nat (StatedSL 3 F)) 2)
    (hirr : XMod.IsIrrSec ↥K (⊥ : Subgroup V) ⊤) : False := by
  obtain ⟨I, π, -, hind, -, hreal⟩ := hd
  have hinv : ∀ i, XMod.IsInv ↥K (I i) := fun i a w hw => (hreal i).2.2.2.1 a w hw
  rcases hirr.2 (I 0) (hinv 0) bot_le le_top with h0 | h0
  · exact natReal_ne (hreal 0) h0
  · apply natReal_ne (hreal 1)
    have h1 := hind 1
    rw [eq_bot_iff] at h1 ⊢
    refine le_trans (le_inf le_rfl ?_) h1
    refine le_trans (h0 ▸ le_top) (le_sup_of_le_right ?_)
    exact le_iSup₂_of_le (f := fun j (_ : j ≠ (1 : Fin 2)) => I j) 0 (by decide) le_rfl

end DirectSum

section Cases

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem Uq_inf_Zq_eq_bot (h : PUHyp M T L) (hC : fixV (autI h.isElemAbelian_Uq L) = ⊥) :
    Uq M T L ⊓ Zq M L = ⊥ := by
  rw [← (toG_fixV_Uq h), hC, toG_bot]

theorem intSub_Uq_inf_Zq (h : PUHyp M T L) :
    intSub h.isElemAbelian_Uq (Uq M T L ⊓ Zq M L) = fixV (autI h.isElemAbelian_Uq L) := by
  rw [← (toG_fixV_Uq h), intSub_toG]

theorem isSp4DerSec_of_sp4 (h : PUHyp M T L)
    {Z' : Subgroup (IntMod (Uq M T L) h.isElemAbelian_Uq)}
    (hZ' : C124.toG h.isElemAbelian_Uq Z' = Uq M T L ⊓ Zq M L) {n : ℕ} (hn : 2 ≤ n)
    (hsp : BinaryNaturalSp4 (autI h.isElemAbelian_Uq L) ⊤ Z' n) :
    IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) n := by
  obtain ⟨F, iF, fF, hcard, π, hπ⟩ := hsp
  obtain ⟨α, hα, hsum⟩ :=
    isSumNat_one_of_realizesVia h.isElemAbelian_Uq ((isSecW_Uq h).L_le_normalizer h) hπ
  rw [hZ'] at hsum
  exact Or.inr ⟨hn, F, iF, Fintype.ofFinite F, α, by rw [Fintype.card_eq_nat_card]; exact hcard,
    hα, hsum⟩

theorem isSp4DerSec_of_alt (h : PUHyp M T L)
    {Z' : Subgroup (IntMod (Uq M T L) h.isElemAbelian_Uq)}
    (hZ' : C124.toG h.isElemAbelian_Uq Z' = Uq M T L ⊓ Zq M L)
    (halt : AlternatingNatural (autI h.isElemAbelian_Uq L) ⊤ Z' 6) :
    IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1 := by
  obtain ⟨π, hπ⟩ := halt
  obtain ⟨N, hN⟩ := isAltNaturalSection_of_realizesVia h.isElemAbelian_Uq
    ((isSecW_Uq h).L_le_normalizer h) (by norm_num) hπ
  rw [hZ'] at hN
  exact Or.inl ⟨rfl, N, hN⟩

theorem isG2U_of (h : PUHyp M T L) (hG2V : S32PartG2Vertex) (hG2S : S32PartG2Struct)
    (hXL : ⁅Xq M, L⁆ = Uq M T L)
    (hgd : G2NaturalDerived (autI h.isElemAbelian_Uq L) ⊤ (fixV (autI h.isElemAbelian_Uq L)) 1)
    (hcase : fixV (autI h.isElemAbelian_Uq L) = ⊥ ∨ (fixV (autI h.isElemAbelian_Uq L) ≠ ⊥ ∧
      XMod.IsIrrSec ↥(autI h.isElemAbelian_Uq L) (fixV (autI h.isElemAbelian_Uq L)) ⊤ ∧
      MS15CaseG2 (autI h.isElemAbelian_Uq M) (autI h.isElemAbelian_Uq L))) :
    IsG2U h.le L := by
  obtain ⟨h1, h2⟩ := hG2S _ _ _ _ h hgd hXL
  exact ⟨h1, h2, ⟨h.isElemAbelian_Uq, by rw [(intSub_Uq_inf_Zq h)]; exact hgd⟩,
    hG2V _ _ _ _ h hgd hcase⟩

end Cases

theorem s32_of (h51 : AsB51) (h14 : MS14AS) (h15 : MS15AS) (hSQ : SQTKQuot) (h45 : NoSL45)
    (hXU : S32PartXU) (hG2L : S32PartG2Large) (hG2V : S32PartG2Vertex)
    (hG2S : S32PartG2Struct) (hHat : S32PartHat) (hL3 : S32PartL3Two)
    (hNS : S32PartL3NonSplit) : S32 := by
  intro G _ _ M T L h
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := (isSecW_Uq h).L_le_normalizer h
  have hXL : ⁅Xq M, L⁆ = Uq M T L := by
    rcases (x_cases h) h51 hSQ h45 with ⟨-, he⟩ | ⟨hii, -, -⟩
    · exact he
    · exact hXU G M T L h hii
  refine ⟨h.centralizer_Z0q, hXL.le, ?_⟩
  rcases (u_cases h) h51 h14 h15 hSQ h45 with ⟨hirr, ⟨hC, hFF⟩ | ⟨hC, hMS⟩⟩ | hii
  ·
    have hUZ := (Uq_inf_Zq_eq_bot h) hC
    have hZ' : C124.toG h.isElemAbelian_Uq ⊥ = Uq M T L ⊓ Zq M L := by rw [toG_bot, hUZ]
    obtain ⟨-, -, hcases, -⟩ := hFF
    rcases hcases with ⟨n, F, iF, fF, -, hcard, -, -, ⟨π, hπ⟩ | hdir⟩ | ⟨hhat, -⟩ | hsp | hg2
    · by_cases hsplit : Uq M T L ⊔ Zq M L = Xq M
      · obtain ⟨α, hα, hsum⟩ := isSumNat_one_of_realizesVia h.isElemAbelian_Uq hLU hπ
        rw [toG_bot] at hsum
        exact Or.inl ⟨by rw [← hsplit, sup_comm], by rw [inf_comm, hUZ], n, F, iF,
          Fintype.ofFinite F, α, by rw [Fintype.card_eq_nat_card]; exact hcard, hα, hsum⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (hNS G M T L h F n hcard ⟨π, hπ⟩ hC hXL hsplit)))))
    · rw [hC] at hirr
      exact (not_isIrrSec_of_directSum hdir hirr).elim
    · exact Or.inr (Or.inl ⟨hHat G M T L h hhat hC hXL, by rw [inf_comm, hUZ],
        h.isElemAbelian_Uq, hhat⟩)
    · rcases hsp with ⟨n, hn, hsp⟩ | halt
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨n, (isSp4DerSec_of_sp4 h) hZ' hn hsp⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨1, (isSp4DerSec_of_alt h) hZ' halt⟩)))))
    · rcases hg2 with ⟨n, hn, hg⟩ | ⟨hgd, -, -⟩
      · rw [← hC] at hg
        exact (hG2L G M T L h n hn hg (Or.inl hC)).elim
      · rw [← hC] at hgd
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ((isG2U_of h) hG2V hG2S hXL hgd (Or.inl hC)))))))
  ·
    rcases hMS with hl3 | ⟨⟨n, hn, hsp, -⟩ | ⟨halt, -⟩⟩ | hg2
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hL3 G M T L h hl3 hXL))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, (isSp4DerSec_of_sp4 h) (toG_fixV_Uq h) hn hsp⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨1, (isSp4DerSec_of_alt h) (toG_fixV_Uq h) halt⟩)))))
    · rcases id hg2 with ⟨n, hn, hg, -⟩ | ⟨hgd, -⟩
      · exact (hG2L G M T L h n hn hg (Or.inr ⟨hC, hirr, hg2⟩)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ((isG2U_of h) hG2V hG2S hXL hgd (Or.inr ⟨hC, hirr, hg2⟩)))))))
  ·
    obtain ⟨-, n, F, iF, fF, hcard, I, π, hind, hsup, hreal, -, -⟩ := id hii
    have hfix : fixV (autI h.isElemAbelian_Uq L) = ⊥ := by
      have := fixV_inf_commV_of_case1ii hii
      rwa [(commV_autI_Uq h), inf_top_eq] at this
    have hUZ := (Uq_inf_Zq_eq_bot h) hfix
    rcases (x_cases h) h51 hSQ h45 with ⟨hirrX, -⟩ | ⟨-, hsupX, hinfX⟩
    · exfalso
      rw [hXL, hUZ] at hirrX
      have hirr' : XMod.IsIrrSec ↥(autI h.isElemAbelian_Uq L)
          (⊥ : Subgroup (IntMod (Uq M T L) h.isElemAbelian_Uq)) ⊤ := by
        apply isIrrSec_of_irrSecG h.isElemAbelian_Uq hLU
        rw [toG_bot, toG_top]
        exact hirrX
      apply not_isIrrSec_of_case1ii hii
      rw [(commV_autI_Uq h), ← fixV_eq_fixed, hfix]
      exact hirr'
    · rw [hXL] at hsupX hinfX
      have hsup' : I 0 ⊔ I 1 = ⊤ := by rw [← iSup_fin_two_eq, hsup, (commV_autI_Uq h)]
      obtain ⟨α, hα, hsum⟩ := isSumNat_two_of_compl h.isElemAbelian_Uq hLU
        (inf_eq_bot_of_iSupIndep hind) hsup' (hreal 0) (hreal 1)
      exact Or.inr (Or.inr (Or.inl ⟨by rw [← hsupX, sup_comm], by rw [inf_comm]; exact hinfX, n,
        F, iF, Fintype.ofFinite F, α, by rw [Fintype.card_eq_nat_card]; exact hcard, hα, hsum⟩))

end CFSG.Quasithin.MS93.S32
