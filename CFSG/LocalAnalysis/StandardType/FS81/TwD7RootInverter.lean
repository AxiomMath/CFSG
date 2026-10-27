module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaFrame
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeCentralizer

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open E7Frame


theorem root_normalizer_data_of_attached_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) {J' : Subgroup G}
    (ψ : ↥L7 ≃* ↥J') {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1)
    (hJC : J' ≤ centralizer ({b₀ * B.b 1} : Set G))
    (hM : tr ψ M0 = ⁅centralizer ({B.b 1} : Set G) ⊓ K,
      centralizer ({B.b 1} : Set G) ⊓ K⁆) :
    tr ψ (Jn 0) ≤ normalizer (zpowers (b₀⁻¹ * B.b 1) : Set G) ∧
      tr ψ (Jn 0) ≤ normalizer (E : Set G) ∧
      tr ψ (Jn 0) ≤ centralizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
        centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := by
  let B' := B.twD7Beta
  have hspan : B'.span = E := B.twD7Beta_span.trans hB.1
  have hψz' : ((ψ z : ↥J') : G) = B'.b 1 := by
    simpa only [B', Basis3.twD7Beta_b_one, hB.2.1] using hψz
  have hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3 := orderOf_z ψ hψz'
  have hJ0M : tr ψ (Jn 0) ≤ centralizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
      centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := by
    rw [← hM]
    exact tr_jn0_le_centralizer ψ
  have hline : tr ψ (Jn 0) ≤ normalizer (zpowers (b₀⁻¹ * B.b 1) : Set G) := by
    intro j hj
    obtain ⟨y, hy, rfl⟩ := mem_tr.mp hj
    rw [← hψz]
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp
      (jn0_conj_mem e7NatFrame_holds hz hz3 hy)
    refine ⟨l * k, ?_⟩
    have hl' : ((ψ (y * z * y⁻¹) : ↥J') : G) = ((ψ z : ↥J') : G) ^ l := by
      have : y * z * y⁻¹ = z ^ l := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, hl])
      rw [this, map_zpow, Subgroup.coe_zpow]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hl'
    show ((ψ z : ↥J') : G) ^ (l * k) = _
    rw [zpow_mul, ← hl']
    exact (MulAut.conj ((ψ y : ↥J') : G)).toMonoidHom.map_zpow _ _ |>.symm
  have hJ0E : tr ψ (Jn 0) ≤ normalizer (E : Set G) := by
    intro j hj
    have hβ : j * (b₀ * B.b 1) * j⁻¹ = b₀ * B.b 1 := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hJC (tr_le_K ψ (Jn 0) hj))]
      group
    have hβ₁E : b₀⁻¹ * B.b 1 ∈ E := by
      have hb : B'.b 1 ∈ E := hspan ▸ B'.b_mem_span 1
      simpa only [B', Basis3.twD7Beta_b_one, hB.2.1] using hb
    have hβ₁ : j * (b₀⁻¹ * B.b 1) * j⁻¹ ∈ E :=
      (zpowers_le.mpr hβ₁E)
        ((Subgroup.mem_normalizer_iff.mp (hline hj) _).mp (Subgroup.mem_zpowers _))
    have htail : ∀ k : Fin 6, j * B.b k.succ.succ * j⁻¹ = B.b k.succ.succ := by
      intro k
      have hc := Subgroup.mem_centralizer_iff.mp (hJ0M hj) _
        (tail_mem_commutator_centralizer_of_std_twD7 hstd B hB hrec k)
      rw [← hc, mul_inv_cancel_right]
    have hbasis : ∀ k : Fin 8, j * B'.b k * j⁻¹ ∈ E := by
      intro k
      refine Fin.cases ?_ ?_ k
      · have hb : B'.b 0 ∈ E := hspan ▸ B'.b_mem_span 0
        simpa only [B', Basis3.twD7Beta_b_zero, hB.2.1, hβ] using hb
      · intro l
        refine Fin.cases ?_ ?_ l
        · change j * B'.b 1 * j⁻¹ ∈ E
          simpa only [B', Basis3.twD7Beta_b_one, hB.2.1] using hβ₁
        · intro m
          have hb : B.b m.succ.succ ∈ E := hB.1 ▸ B.b_mem_span m.succ.succ
          simpa only [B', Basis3.twD7Beta_b_succ_succ, htail] using hb
    have hmap : E.map (MulAut.conj j).toMonoidHom ≤ E := by
      rw [Subgroup.map_le_iff_le_comap, ← hspan]
      change Subgroup.closure (Set.range B'.b) ≤ _
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨k, rfl⟩
      change j * B'.b k * j⁻¹ ∈ B'.span
      exact hspan.symm ▸ hbasis k
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hmap (by
        rw [Subgroup.card_map_of_injective (MulAut.conj j).injective]))
  exact ⟨hline, hJ0E, hJ0M⟩

theorem exists_root_inverter_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) {J' : Subgroup G}
    (ψ : ↥L7 ≃* ↥J') {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1)
    (hJC : J' ≤ centralizer ({b₀ * B.b 1} : Set G))
    (hMJ : ⁅centralizer ({B.b 1} : Set G) ⊓ K,
      centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J') :
    tr ψ M0 = ⁅centralizer ({B.b 1} : Set G) ⊓ K,
      centralizer ({B.b 1} : Set G) ⊓ K⁆ ∧
    ∃ i ∈ tr ψ (Jn 0), i ∈ normalizer (E : Set G) ∧
      i * (b₀⁻¹ * B.b 1) * i⁻¹ = (b₀⁻¹ * B.b 1)⁻¹ ∧
      i ∈ centralizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
        centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := by
  obtain ⟨R₀, -, -, -, hCeq, -, -, -, hXR₀⟩ :=
    exists_threePrime_core_twD7 hstd hB hrec
  obtain ⟨-, hHyp, hCanon⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, hKz, -, -, -, -⟩ := hA
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hCanon.1 hKz
  have hb₁E : B.b 1 ∈ E := hB.1 ▸ B.b_mem_span 1
  have hb₁1 : B.b 1 ≠ 1 := by
    intro h
    have ho := B.ord 1
    rw [h, orderOf_one] at ho
    norm_num at ho
  have hR₀K : R₀ ≤ centralizer (K : Set G) :=
    hXR₀ K hKs (hKC.trans le_sup_left) ⟨B.b 1, hB.2.2 1 (by decide), hb₁E, hb₁1⟩
  have hM : tr ψ M0 = ⁅centralizer ({B.b 1} : Set G) ⊓ K,
      centralizer ({B.b 1} : Set G) ⊓ K⁆ :=
    tr_m0_eq_commutator_twD7 hstd hB hrec hR₀K hCeq ψ e7NatCent_holds hJC hMJ hz hψz
  obtain ⟨-, hJ0E, hJ0M⟩ :=
    root_normalizer_data_of_attached_twD7 hstd B hB hrec ψ hz hψz hJC hM
  have hψz' : ((ψ z : ↥J') : G) = B.twD7Beta.b 1 := by
    simpa only [Basis3.twD7Beta_b_one, hB.2.1] using hψz
  have hz3 := orderOf_z ψ hψz'
  obtain ⟨t, ht, htz⟩ := jn0_exists_inv e7NatFrame_holds hz hz3
  let i : G := ((ψ ⟨t, e7NatFrame_holds.1 0 ht⟩ : ↥J') : G)
  have hiJ0 : i ∈ tr ψ (Jn 0) := (coe_mem_tr_iff ψ _).mpr ht
  have hiβ₁ : i * (b₀⁻¹ * B.b 1) * i⁻¹ = (b₀⁻¹ * B.b 1)⁻¹ := by
    have ht' : (⟨t, e7NatFrame_holds.1 0 ht⟩ : ↥L7) * z *
        (⟨t, e7NatFrame_holds.1 0 ht⟩ : ↥L7)⁻¹ = z⁻¹ := Subtype.ext htz
    have h := congrArg (fun y => ((ψ y : ↥J') : G)) ht'
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψz] using h
  exact ⟨hM, i, hiJ0, hJ0E hiJ0, hiβ₁, hJ0M hiJ0⟩

end CFSG.StandardType.FrameRoute.FS81
