module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23SettingProof
import CFSG.Quasithin.Vol2.Ch5Sec3Lemma531
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.Quasithin.Vol2.Ch1Unique
import CFSG.Quasithin.Vol2.Ch1A3Cat
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
import CFSG.Quasithin.Background.KnownMultTypes
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem card_GL_four_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem isSimpleGroup_GL_four_two : IsSimpleGroup (GL (Fin 4) (ZMod 2)) := by
  have h := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 4) (by norm_num)
    (Or.inl (by norm_num))).2.1
  let e : GL (Fin 4) (ZMod 2) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) :=
    ((Setup.Family.slEquivGL 4).symm.trans (Setup.Family.projEquiv 4)).trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 (ZMod 2)))
  exact e.isSimpleGroup

theorem eq_of_normal_card_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Nat.card S = 20160) {X A : Subgroup S} (hAX : A ≤ X) (hAn : (A.subgroupOf X).Normal)
    (hA : Nat.card A = 2520) : A = X := by
  have h1 : Nat.card A ∣ Nat.card X := Subgroup.card_dvd_of_le hAX
  have h2 : Nat.card X ∣ 20160 := hS ▸ Subgroup.card_subgroup_dvd_card X
  rw [hA] at h1
  obtain ⟨k, hk⟩ := h1
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk; exact absurd hk (Nat.card_pos.ne')
    · exact h0
  have hk8 : k ∣ 8 := by
    obtain ⟨m, hm⟩ := h2
    have hm' : 2520 * (k * m) = 2520 * 8 := by rw [← mul_assoc, ← hk, ← hm]
    exact ⟨m, (Nat.eq_of_mul_eq_mul_left (by norm_num) hm').symm⟩
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 := by
    have : k ≤ 8 := Nat.le_of_dvd (by norm_num) hk8
    interval_cases k <;> simp_all
  have hXne : X ≠ ⊤ := by
    intro hXt
    subst hXt
    have hAN : A.Normal := ⟨fun a ha g => by
      have := hAn.conj_mem ⟨a, Subgroup.mem_top a⟩ (Subgroup.mem_subgroupOf.mpr ha)
        ⟨g, Subgroup.mem_top g⟩
      exact Subgroup.mem_subgroupOf.mp this⟩
    rcases hAN.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.card_bot] at hA; norm_num at hA
    · rw [ht, Subgroup.card_top, hS] at hA; norm_num at hA
  have hidx : ∀ Y : Subgroup S, Y.index ≤ 4 → Y = ⊤ := by
    intro Y hY
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with hb | ht
    · exfalso
      have hdvd := Y.index_normalCore_dvd_factorial_index
      rw [hb, Subgroup.index_bot, hS] at hdvd
      have hpos : 0 < Y.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
      have hfac : Y.index.factorial ≤ 24 := by
        calc Y.index.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hY
          _ = 24 := rfl
      have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
      omega
    · exact eq_top_iff.mpr (ht ▸ Y.normalCore_le)
  have hXidx : X.index * Nat.card X = 20160 := by
    rw [← hS, mul_comm]; exact Subgroup.card_mul_index X
  rcases hk_cases with rfl | rfl | rfl | rfl
  · exact Subgroup.eq_of_le_of_card_ge hAX (by rw [hA, hk])
  · exact absurd (hidx X (by rw [hk] at hXidx; omega)) hXne
  · exact absurd (hidx X (by rw [hk] at hXidx; omega)) hXne
  · exact absurd (hidx X (by rw [hk] at hXidx; omega)) hXne

@[expose] def Stmt5_2_8_Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (K' : Subgroup G),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T → oTwoUpper H < K' →
    quasithinIsMaximalLocal T K' → CFSG.Quasithin.IsExcA7Block K' →
      IsElemAbelian 2 (pCoreOf 2 K') ∧ Nat.card (pCoreOf 2 K') = 16 ∧ T ≤ K'

variable {G : Type} [Group G]

theorem ker_conjNormal_le {M0 U : Subgroup G} (hUM0 : U ≤ M0) [(U.subgroupOf M0).Normal]
    (hC : M0 ⊓ Subgroup.centralizer (U : Set G) ≤ U) :
    (MulAut.conjNormal : M0 →* MulAut (U.subgroupOf M0)).ker ≤ U.subgroupOf M0 := by
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  refine hC (Subgroup.mem_inf.mpr ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩)
  have h1 := congrArg (fun φ : MulAut (U.subgroupOf M0) =>
    ((φ ⟨⟨x, hUM0 hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩ : U.subgroupOf M0) : M0)) hg
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  calc x * g = g * x * (g : G)⁻¹ * g := by rw [h2]
    _ = g * x := by group

theorem le_ker_conjNormal {M0 U : Subgroup G} [(U.subgroupOf M0).Normal]
    (hab : IsMulCommutative U) :
    U.subgroupOf M0 ≤ (MulAut.conjNormal : M0 →* MulAut (U.subgroupOf M0)).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  ext u
  simp only [MulAut.conjNormal_apply, MulAut.one_apply]
  have hgU : (g : G) ∈ U := Subgroup.mem_subgroupOf.mp hg
  have hu : ((u : M0) : G) ∈ U := Subgroup.mem_subgroupOf.mp u.2
  have hc : (g : G) * u = u * g := by
    have := hab.is_comm.comm ⟨g, hgU⟩ ⟨u, hu⟩
    exact congrArg Subtype.val this
  change (g : G) * u * (g : G)⁻¹ = u
  rw [hc]; group

theorem stmt5_2_11_four_of
    (h39 : Vol2Native.A39ForSQTKCat) (hQ : Stmt5_2_8_Q) :
    Stmt5_2_11_four := by
  intro G _ _ T M L V H B D L₂ n K' hyp hM23 hKK' hmax hexc
  obtain ⟨hUab, hU16, hTK⟩ := hQ G T M L V H B D L₂ n K' hyp hM23 hKK' hmax hexc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact
    Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved
    Vol2Native.a37ForSQTKCat_proved)
  have h39' : A39ForSQTK := a39ForSQTK_of_cat h39
  have hTN : T ≤ Subgroup.normalizer (K' : Set G) := hTK.trans Subgroup.le_normalizer
  have hUM := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39' hyp.sylow hmax
  rw [conjClosure_eq_self_of_le_normalizer hTN] at hUM
  set M0 := Subgroup.normalizer (K' : Set G) with hM0
  have hKM0 : K' ≤ M0 := Subgroup.le_normalizer
  have hTM0 : T ≤ M0 := hTK.trans hKM0
  suffices hMK : M0 = K' by
    refine ⟨?_, hTK⟩
    have := hUM.1.1
    rwa [hMK] at this
  set U := pCoreOf 2 K' with hUdef
  have hUK : U ≤ K' := CFSG.LieType.BorelTits.pCoreOf_le 2 K'
  have hUM0' : U ≤ M0 := hUK.trans hKM0
  have hUN : M0 ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K'
  have hU2 : IsPGroup 2 U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K'
  have hTs : IsSylowTwoOf T M0 := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM0
  have hO : pCoreOf 2 M0 = U := le_antisymm (pCoreOf_le_pCoreOf_of_sylow hTs hTK hKM0)
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUM0' hUN hU2)
  have hUne : U ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hU16
    norm_num at hU16
  have hCT : CharTwo M0 := charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTM0, by rw [hO]; exact hUne⟩
  have hC : M0 ⊓ Subgroup.centralizer (U : Set G) ≤ U := by
    have h := hCT
    unfold CharTwo at h
    rwa [hO] at h
  have hU'n : (U.subgroupOf M0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM0').mpr hUN
  set φ : M0 →* MulAut (U.subgroupOf M0) := MulAut.conjNormal
  have hker : φ.ker = U.subgroupOf M0 :=
    le_antisymm (ker_conjNormal_le hUM0' hC) (le_ker_conjNormal hUab.1)
  have hcardU' : Nat.card (U.subgroupOf M0) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM0').toEquiv, hU16]; norm_num
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := U.subgroupOf M0)
    (fun a b => by
      have := hUab.1.is_comm.comm ⟨(a : M0), Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨(b : M0), Subgroup.mem_subgroupOf.mp b.2⟩
      have h' : ((a : M0) : G) * ((b : M0) : G) = ((b : M0) : G) * ((a : M0) : G) :=
        congrArg Subtype.val this
      exact Subtype.ext (Subtype.ext h'))
    (fun a => by
      apply Subtype.ext; apply Subtype.ext
      exact hUab.2 _ (Subgroup.mem_subgroupOf.mp a.2))
    hcardU'
  set eGL := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  have hfin : Finite (MulAut (U.subgroupOf M0)) := Finite.of_equiv _ eGL.symm.toEquiv
  have hsimp : IsSimpleGroup (MulAut (U.subgroupOf M0)) := by
    have := isSimpleGroup_GL_four_two
    exact eGL.isSimpleGroup
  have hcardS : Nat.card (MulAut (U.subgroupOf M0)) = 20160 := by
    rw [Nat.card_congr eGL.toEquiv, card_GL_four_two]
  set ψ : K' →* MulAut (U.subgroupOf M0) := φ.comp (Subgroup.inclusion hKM0)
  obtain ⟨-, ⟨α, hαs, hαk⟩, -⟩ := hexc
  have hψk : ψ.ker = α.ker := by
    ext k
    rw [MonoidHom.mem_ker, hαk]
    change Subgroup.inclusion hKM0 k ∈ φ.ker ↔ _
    rw [hker, Subgroup.mem_subgroupOf]
    change ((k : G) ∈ (CFSG.Open.pCore 2 K').map K'.subtype) ↔ _
    constructor
    · intro h
      obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp h
      have : k' = k := Subtype.ext hkk'
      rw [← this]
      exact hk'
    · intro h
      exact Subgroup.mem_map.mpr ⟨k, h, rfl⟩
  have hcardA : Nat.card ψ.range = 2520 := by
    rw [← Subgroup.index_ker, hψk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hαs,
      Subgroup.card_top, card_alternatingGroup_seven]
  have hAeq : ψ.range = (K'.subgroupOf M0).map φ := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKM0 k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  have hKn : (K'.subgroupOf M0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM0).mpr le_rfl
  have hAn : (((K'.subgroupOf M0).map φ).subgroupOf φ.range).Normal := by
    refine ⟨fun a ha x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨k, hk, hka⟩ := ha
    obtain ⟨m, hm⟩ := x.2
    refine ⟨m * k * m⁻¹, hKn.conj_mem k hk m, ?_⟩
    simp only [map_mul, map_inv, hm, hka, Subgroup.coe_mul, Subgroup.coe_inv]
  have hEq := eq_of_normal_card_of_simple hcardS (Subgroup.map_le_range φ _) hAn
    (by rw [← hAeq]; exact hcardA)
  refine le_antisymm (fun m hm => ?_) hKM0
  have hmr : φ ⟨m, hm⟩ ∈ (K'.subgroupOf M0).map φ := by
    rw [hEq]; exact ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨k, hk, hkm⟩ := hmr
  have hker' : k⁻¹ * ⟨m, hm⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkm, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hker'
  have hkK : (k : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk
  have hmk : m = (k : G) * ((k⁻¹ * ⟨m, hm⟩ : M0) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [hmk]
  exact mul_mem hkK (hUK hker')

end CFSG.Quasithin.H13
