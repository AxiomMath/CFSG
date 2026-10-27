module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffQTwoDefs
import CFSG.LocalAnalysis.StandardType.GGLtBstarOfInner
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative

variable {G : Type} [Group G]

private theorem mem_zpowers_of_axis {n : ℕ} {i0 : Fin n} {f g : Fin n → Multiplicative (ZMod 3)}
    (hf : ∀ k, k ≠ i0 → f k = 1) (hg : ∀ k, k ≠ i0 → g k = 1) (hg0 : g i0 ≠ 1) :
    f ∈ Subgroup.zpowers g := by
  have key : ∀ s t : ZMod 3, s ≠ 0 → ∃ m : Fin 3, ((m : ℕ) : ZMod 3) * s = t := by decide
  have hs : toAdd (g i0) ≠ 0 := fun h => hg0 (by rw [← ofAdd_toAdd (g i0), h, ofAdd_zero])
  obtain ⟨m, hm⟩ := key _ (toAdd (f i0)) hs
  refine Subgroup.mem_zpowers_iff.mpr ⟨((m : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast]
  funext k
  rw [Pi.pow_apply]
  by_cases hk : k = i0
  · subst hk
    apply toAdd.injective
    rw [toAdd_pow, ← hm, nsmul_eq_mul]
  · rw [hf k hk, hg k hk, one_pow]

private theorem card_ggBsCoordZero_three {Bs : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i0 : Fin n) :
    Nat.card (ggBsCoordZero Bs eta i0) = 3 ^ (n - 1) := by
  have h := FrameBs.card_frame_trivial_on (p := 3) ({i0} : Finset (Fin n))
  rw [Finset.card_singleton] at h
  rw [ggBsCoordZero, Subgroup.card_map_of_injective Bs.subtype_injective, ← h]
  refine Nat.card_congr (Equiv.subtypeEquiv eta.toEquiv fun b => ?_)
  rw [MonoidHom.mem_ker]
  simp only [Finset.mem_singleton, forall_eq]
  rfl

private theorem ggBsCoordZero_le_of_bCoordinateBlock {Bs L : Subgroup G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0) :
    ggBsCoordZero Bs eta i0 ≤ L := by
  intro g hg
  obtain ⟨hgBs, hg0⟩ := mem_ggBsCoordZero.mp hg
  have hmem : negOff (p := 3) i0 ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hb]
    exact negOff_mem_bCoordinateBlock i0
  obtain ⟨ψ, hψ, hψeq⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨h, hhL, -, hh⟩ := mem_ggAutomizer_iff.mp hψ
  have h1 : eta (ψ ⟨g, hgBs⟩) = (eta ⟨g, hgBs⟩)⁻¹ := by
    have h2 : MulAut.congr eta ψ (eta ⟨g, hgBs⟩) = negOff (p := 3) i0 (eta ⟨g, hgBs⟩) := by
      rw [show MulAut.congr eta ψ = negOff i0 from hψeq]
    rw [MulAut.congr_apply] at h2
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    rw [h2]
    funext i
    rw [negOff_apply, Pi.inv_apply]
    split_ifs with hi
    · subst hi
      rw [hg0]
      exact inv_one.symm
    · rfl
  have hψb : ψ ⟨g, hgBs⟩ = (⟨g, hgBs⟩ : ↥Bs)⁻¹ := eta.injective (by rw [h1, map_inv])
  have hconj : h * g * h⁻¹ = g⁻¹ := by
    have h3 := hh ⟨g, hgBs⟩
    rw [hψb] at h3
    exact h3.symm
  have hg3 : g ^ 3 = 1 := hBs.2 g hgBs
  have hmemL : g * h⁻¹ * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hBsN hgBs) h⁻¹).mp (L.inv_mem hhL)
  have heq : g = h * (g * h⁻¹ * g⁻¹) := by
    calc g = g⁻¹ * g⁻¹ * g ^ 3 := by group
      _ = g⁻¹ * g⁻¹ := by rw [hg3, mul_one]
      _ = h * g * h⁻¹ * g⁻¹ := by rw [hconj]
      _ = h * (g * h⁻¹ * g⁻¹) := by group
  rw [heq]
  exact L.mul_mem hhL hmemL

variable [Finite G]

theorem GGConfig.lt_bstar_of_spTwo_coordB {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {n : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) :
    B < Bs := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hBsE, hxBs, hLx, h81⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.mp (hLx hl)) x (Set.mem_singleton x)).symm
  have hcardBs : Nat.card Bs = 3 ^ n := by
    rw [Nat.card_congr eta.toEquiv]
    simp [Nat.card_fun]
  have hn : 4 ≤ n := by
    rw [hcardBs] at h81
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h81
  obtain ⟨-, lab, -, hraw⟩ := hM
  obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := largeEvenRawDatum_exists (lab := lab) hraw
  obtain ⟨ht, hr, hn1⟩ := hS
  obtain ⟨t, r, m⟩ := lab
  dsimp only at ht hr hn1
  subst hr hn1
  suffices key : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ 1 →
      (L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSpGroup K (n - 1))) →
      Bs ≤ Subgroup.normalizer (L : Set G) → B < Bs by
    rcases ht with rfl | rfl
    · obtain ⟨K, _, _, hK, -, -, θ, -, hBsN, -⟩ := hraw
      exact key K hK θ hBsN
    · obtain ⟨K, _, _, hK, -, -, θ, -, hBsN, -⟩ := hraw
      exact key K hK θ hBsN
  intro K _ _ hK θ hBsN
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : NeZero (n - 1) := ⟨by omega⟩
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have hEL : ggBsCoordZero Bs eta i0 ≤ L := ggBsCoordZero_le_of_bCoordinateBlock hBsE hBsN eta hb
  have hax : ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (L : Set G) →
      ∀ k, k ≠ i0 → eta b k = 1 :=
    fun b hbc k hk => ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer (by norm_num) hb hbc hk
  refine GGConfig.lt_bstar_of_bstar_eq_sup hcfg ?_ ?_
  ·
    refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hxBs) inf_le_left)
    intro g hg
    set a : ↥Bs := eta.symm (Pi.mulSingle i0 (eta ⟨g, hg⟩ i0)) with ha
    have hc : ((a⁻¹ * ⟨g, hg⟩ : ↥Bs) : G) ∈ ggBsCoordZero Bs eta i0 := by
      rw [coe_mem_ggBsCoordZero, map_mul, map_inv, ha, MulEquiv.apply_symm_apply, Pi.mul_apply,
        Pi.inv_apply, Pi.mulSingle_eq_same]
      exact inv_mul_cancel _
    have hxax := hax ⟨x, hxBs⟩ hxL
    have hx0 : eta ⟨x, hxBs⟩ i0 ≠ 1 := by
      intro h0
      apply hx1
      have he : eta ⟨x, hxBs⟩ = 1 := funext fun k => by
        by_cases hk : k = i0
        · rw [hk, h0]
          rfl
        · exact hxax k hk
      exact congrArg Subtype.val (eta.injective (he.trans (map_one eta).symm))
    have haz : eta a ∈ Subgroup.zpowers (eta ⟨x, hxBs⟩) := by
      refine mem_zpowers_of_axis (fun k hk => ?_) hxax hx0
      rw [ha, MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne hk]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haz
    have hak : a = (⟨x, hxBs⟩ : ↥Bs) ^ k := eta.injective (by rw [map_zpow]; exact hk.symm)
    have hxk : (a : G) ∈ Subgroup.zpowers x :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [hak, Subgroup.coe_zpow]⟩
    have hg' : g = (a : G) * ((a⁻¹ * ⟨g, hg⟩ : ↥Bs) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [hg']
    exact Subgroup.mul_mem_sup hxk (Subgroup.mem_inf.mpr ⟨(a⁻¹ * ⟨g, hg⟩ : ↥Bs).2, hEL hc⟩)
  ·
    intro U hUL hU2 hBsU
    by_contra hU
    let φL : ↥L →* LargeEvenProj (LargeEvenSpGroup K (n - 1)) :=
      θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hker : ∀ l : ↥L, φL l = 1 → (l : G) ∈ Subgroup.centralizer (L : Set G) := by
      intro l hl
      have hq : (QuotientGroup.mk' (Subgroup.center ↥L) l) = 1 :=
        θ.injective (by rw [map_one]; exact hl)
      have hc : l ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff l).mp hq
      rw [Subgroup.mem_centralizer_iff]
      intro l' hl'
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l', hl'⟩)
    set Ut := (U.subgroupOf L).map φL with hUt
    have hUt1 : Ut ≠ ⊥ := by
      intro hbot
      apply hU
      intro u hu
      have hmem : φL ⟨u, hUL hu⟩ ∈ Ut :=
        Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact hu)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hker _ hmem
    have hUt2 : IsPGroup 2 Ut :=
      (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm).map φL
    set Et := ((ggBsCoordZero Bs eta i0).subgroupOf L).map φL with hEt
    have hEtE : IsElemAbelian 3 Et :=
      ((hBsE.mono (ggBsCoordZero_le i0)).subgroupOf L).map φL
    have hinj : Function.Injective (φL.domRestrict ((ggBsCoordZero Bs eta i0).subgroupOf L)) := by
      refine (injective_iff_map_eq_one _).mpr fun e he => ?_
      obtain ⟨⟨l, hlL⟩, hlE⟩ := e
      have hlE' : l ∈ ggBsCoordZero Bs eta i0 := by
        rw [Subgroup.mem_subgroupOf] at hlE
        exact hlE
      obtain ⟨hlBs, hl0⟩ := mem_ggBsCoordZero.mp hlE'
      have hlc := hker ⟨l, hlL⟩ he
      have he1 : eta ⟨l, hlBs⟩ = 1 := funext fun k => by
        by_cases hk : k = i0
        · rw [hk, hl0]
          rfl
        · exact hax ⟨l, hlBs⟩ hlc k hk
      have hl1 : l = 1 := congrArg Subtype.val (eta.injective (he1.trans (map_one eta).symm))
      subst hl1
      rfl
    have hcardEt : Nat.card Et = 3 ^ (n - 1) := by
      rw [hEt, ← MonoidHom.restrict_range,
        ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, card_ggBsCoordZero_three]
    have hEtU : ∀ a ∈ Et, ∀ u ∈ Ut, a * u * a⁻¹ ∈ Ut := by
      rintro _ ⟨e, he, rfl⟩ _ ⟨u, hu, rfl⟩
      refine ⟨e * u * e⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at he hu ⊢
      have heBs : ((e : ↥L) : G) ∈ Bs := ggBsCoordZero_le i0 he
      have h := (Subgroup.mem_normalizer_iff.mp (hBsU heBs) _).mp hu
      simpa using h
    have hle := SmallRule.card_le_sp_normalizes_two hK2 hEtE hUt1 hUt2 hEtU
    rw [hcardEt] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    omega

section Inputs


theorem ggSecFiveBCoordBOffQTwoSpInput_holds : GGSecFiveBCoordBOffQTwoSpInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ _ eta i0 _ hLB hLab hB _ _ _
  exfalso
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hp : p.Prime := hcfg.tableB_facts.1
  have hlab : ∀ lab : LargeEvenLabel, GGSecFiveBCoordBLabel n p lab →
      (lab.n = 1 ∧ (lab.tag = .B ∨ lab.tag = .C)) →
        p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧ lab.n = 1 := by
    intro lab h ⟨hn1, htag⟩
    rcases h with ⟨-, hr, hdvd | ⟨-, h3⟩⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · rw [hn1] at hdvd
      norm_num at hdvd
      exact absurd hdvd hp.one_lt.ne'
    · exact ⟨h3, htag, hr, hn1⟩
    all_goals rcases htag with h | h <;> rw [h] at ht <;> cases ht
  have hp3 : p = 3 := by
    obtain ⟨-, lab, -, hraw⟩ := hLab
    obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := largeEvenRawDatum_exists (lab := lab) hraw
    exact (hlab lab hS.1 hS.2).1
  subst hp3
  have hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨(hlab lab h.1.1 h.1.2).2, h.2⟩) hLab
  have hlt := GGConfig.lt_bstar_of_spTwo_coordB hcfg eta hLB hM
  exact hlt.ne hB

end Inputs

end CFSG.StandardType

end
