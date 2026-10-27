module

public import CFSG.Quasithin.H13.U3HullFrame
public import CFSG.Quasithin.H13.A6Inputs13_3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

@[expose] def U3Stmt13_3_12_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G),
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    ∀ V₂ V₃ : Subgroup G, V ⊓ centralizer (T : Set G) ≤ V₂ → V₂ ≤ V₃ → V₃ ≤ V →
      T ≤ normalizer (V₂ : Set G) → T ≤ normalizer (V₃ : Set G) → Nat.card V₂ = 4 →
      Nat.card V₃ = 8 →
    ∀ g : G, ⁅V, CFSG.conjugate V g⁆ ≠ ⊥ → ⁅V, CFSG.conjugate V g⁆ ≤ V ⊓ CFSG.conjugate V g →
      V ⊓ CFSG.conjugate V g = ⁅V, CFSG.conjugate V g⁆ ∧
        ⁅V, CFSG.conjugate V g⁆ = V ⊓ centralizer (CFSG.conjugate V g : Set G) ∧
        (∃ x : G, ⁅V, CFSG.conjugate V g⁆ = CFSG.conjugate V₃ x) ∧
        ¬ centralizer (V₃ : Set G) ≤ normalizer (L : Set G)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_L_eq_bot {T L V : Subgroup G} {z : G} (hF : QTU3InternalFrame T L V z) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, hirr, hnt, -, -, -⟩ := hF
  rcases hirr (V ⊓ centralizer (L : Set G)) inf_le_left
      (fun l hl w hw => by
        rw [show l * w * l⁻¹ = w by
          rw [(mem_centralizer_iff.1 hw.2) l hl, mul_inv_cancel_right]]
        exact hw) with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl, v, hv, hlv⟩ := hnt
    have hvC : v ∈ centralizer (L : Set G) := (h.symm ▸ hv : v ∈ V ⊓ _).2
    exact hlv (by rw [(mem_centralizer_iff.1 hvC) l hl, mul_inv_cancel_right])

omit [Finite G] in
theorem not_isHatA6_of_U3
    {L : Subgroup G} (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    ¬ A6.IsHatA6 L := by
  rintro ⟨-, hc, -⟩
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (MulEquiv.isSimpleGroup_congr (e1.trans e2.symm)).2 this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with h | h
  · rw [h, card_bot] at hc
    norm_num at hc
  · obtain ⟨x, y, hxy⟩ := u33Pres_nonabelian
    apply hxy
    have hc' : ∀ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b = b * a := fun a b =>
      (mem_center_iff.1 (h ▸ mem_top a) b).symm
    have := hc' ((e1.trans e2.symm).symm x) ((e1.trans e2.symm).symm y)
    simpa using congrArg (e1.trans e2.symm) this

theorem not_iso_a5_of_U3
    {T L V : Subgroup G} {z : G}
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z) :
    IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun e => ?_⟩
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  let φ₀ : ↥L →* ↥(autOn L V) :=
    ((conjAct V).comp (Subgroup.inclusion hLV)).codRestrict (autOn L V) fun l =>
      ⟨⟨l, hLV l.2⟩, l.2, rfl⟩
  have hφ₀ : Function.Surjective φ₀ := by
    rintro ⟨_, ⟨⟨n, hn⟩, hnL, rfl⟩⟩
    exact ⟨⟨n, hnL⟩, rfl⟩
  let φ : ↥L →* ↥(alternatingGroup (Fin 5)) := e.toMonoidHom.comp φ₀
  have hφ : Function.Surjective φ := e.surjective.comp hφ₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTC, -, -⟩ := id hF
  have hO : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro o ho
    have hoC : (o : G) ∈ centralizer (V : Set G) := by
      have h1 : (o : G) ∈ pCoreOf 2 L := ⟨o, mem_open_pCore_of_mem_pCore ho, rfl⟩
      have h2 := A6.pCoreOf_le_pCoreOf_sup hF.1 h1
      rw [← hTC] at h2
      exact h2.2
    rw [MonoidHom.mem_ker]
    have h3 : φ₀ o = 1 := by
      apply Subtype.ext
      refine MulEquiv.ext fun v => ?_
      apply Subtype.ext
      change (o : G) * v * (o : G)⁻¹ = v
      rw [← (mem_centralizer_iff.1 hoC) v v.2, mul_inv_cancel_right]
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, h3, map_one]
  let ψ := QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO
  have hψ : Function.Surjective ψ := by
    intro a
    obtain ⟨l, rfl⟩ := hφ a
    exact ⟨l, rfl⟩
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (MulEquiv.isSimpleGroup_congr (e1.trans e2.symm)).2 this
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := by
    rw [Nat.card_congr (e1.trans e2.symm).toEquiv, card_u33G]
  have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 h
    have := Nat.card_le_card_of_injective ψ hinj
    rw [hcard, hA5] at this
    norm_num at this
  · have h1 : ∀ a, ψ a = 1 := fun a => MonoidHom.mem_ker.1 (h ▸ mem_top a)
    have h2 : ∀ b : ↥(alternatingGroup (Fin 5)), b = 1 := fun b => by
      obtain ⟨a, rfl⟩ := hψ b
      exact h1 a
    have : Nat.card ↥(alternatingGroup (Fin 5)) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h2 a).trans (h2 b).symm⟩, inferInstance⟩
    rw [hA5] at this
    norm_num at this

omit [Finite G] in
theorem fsuV1_eq {T L V : Subgroup G} {z : G} (hF : QTU3InternalFrame T L V z) :
    fsuV1 T V = V ⊓ centralizer (T : Set G) := by
  have hVT : V ≤ T := hF.2.1
  have hVz : V ⊓ centralizer (T : Set G) = zpowers z := hF.2.2.2.2.2.2.2.2.2.2.2.1
  have hz2 : orderOf z = 2 := hF.2.2.2.2.2.2.2.2.2.2.2.2
  apply le_antisymm
  · refine inf_le_inf_left _ ((closure_le _).2 fun x hx => hx.1.2)
  · have hzm : z ∈ V ⊓ centralizer (T : Set G) := by rw [hVz]; exact mem_zpowers z
    rw [hVz, zpowers_le]
    refine ⟨hzm.1, subset_closure ⟨⟨hVT hzm.1, hzm.2⟩, ?_⟩⟩
    rw [← hz2]
    exact pow_orderOf_eq_one z

theorem u3V3Centralizer_of_stmt13_3_15
    (h1332 : Stmt13_3_2) (h13315 : A6.Stmt13_3_15) :
    U3V3Centralizer := by
  intro G _ _ T L V z hH hU3 hF V₂ V₃ h12 h23 h3V hT2 hT3 hc2 hc3
  have hirr := u3_isIrrPlusIn h1332 hH hU3 hF
  have hV2 : A6.IsV2 T V V₂ :=
    ⟨by rw [fsuV1_eq hF]; exact h12, h23.trans h3V, hT2, hc2⟩
  have h := h13315 G T L V V₂ (L₁Of L V₂)
    (conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) hH hirr
    (inf_centralizer_L_eq_bot hF) hV2 (not_iso_a5_of_U3 hU3 hF)
    (fun h => absurd h (not_isHatA6_of_U3 hU3)) (fun _ => rfl) rfl
  exact (h.2.2.2.2.2.2.2.2 V₃ h23 h3V hT3 hc3).1

namespace HullSetting

variable
  {T L V : Subgroup G}
  [IsElementaryAbelian 2 V] {z : G} (S : HullSetting G T L V z)
include S

theorem fsuV1_eq_V₁ :
    fsuV1 T V = S.V₁ := by
  rw [fsuV1_eq S.hF, S.hVz, S.V₁_eq]

theorem g1_eq_H :
    A6.g1 T V = S.H := by
  show normalizer (fsuV1 T V : Set G) = S.H
  rw [S.fsuV1_eq_V₁, S.normalizer_V₁]

theorem isV2 : A6.IsV2 T V S.V₂ :=
  ⟨by rw [S.fsuV1_eq_V₁]; exact S.le12, S.le23.trans S.le3, S.T_normalizes_V₂, S.card_V₂⟩

theorem centralizer_V₃_le
    (hB : U3V3Centralizer) :
    centralizer (S.V₃ : Set G) ≤ normalizer (V : Set G) :=
  hB G T L V z S.hH S.hU3 S.hF S.V₂ S.V₃ (by rw [S.hVz, ← S.V₁_eq]; exact S.le12) S.le23 S.le3
    S.T_normalizes_V₂ S.T_normalizes_V₃ S.card_V₂ S.card_V₃

theorem comm_eq_bot
    (h12_4 : U3Stmt13_3_12_4) (hB : U3V3Centralizer) :
    ∀ g ∈ S.H, ⁅V, conjSub g V⁆ ≤ V ⊓ conjSub g V → ⁅V, conjSub g V⁆ = ⊥ := by
  intro g _ hle
  have hcs : conjSub g V = CFSG.conjugate V g⁻¹ := by
    ext x
    rw [mem_conjSub, mem_conjugate_iff', inv_inv]
  by_contra hne
  rw [hcs] at hle hne
  obtain ⟨-, -, -, hC⟩ := h12_4 G T L V z S.hH S.hU3 S.hF S.V₂ S.V₃
    (by rw [S.hVz, ← S.V₁_eq]; exact S.le12) S.le23 S.le3 S.T_normalizes_V₂
    S.T_normalizes_V₃ S.card_V₂ S.card_V₃ g⁻¹ hne hle
  exact hC ((S.centralizer_V₃_le hB).trans S.normalizer_V_le)

end HullSetting

theorem u3_abelian_centralizer_hull
    (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14)
    (h13315 : A6.Stmt13_3_15) (h12_4 : U3Stmt13_3_12_4)
    (hcod : U3CodimThreeCentralizerControl) : U3AbelianCentralizerHull := by
  intro G _ _ T L V z hH hU3 hF
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  let S : HullSetting G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  have hB := u3V3Centralizer_of_stmt13_3_15 h1332 h13315
  have hsup : (⨆ h ∈ centralizer ({z} : Set G), CFSG.conjugate V h) = conjClosure V S.H := by
    rw [S.H_eq]
    apply le_antisymm
    · refine iSup₂_le fun h hh x hx => ?_
      rw [mem_conjugate_iff'] at hx
      have := mem_conjClosure (Z := V) (inv_mem hh) hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
    · refine conjClosure_le fun k hk v hv => ?_
      have hmem : k * v * k⁻¹ ∈ CFSG.conjugate V k⁻¹ := by
        rw [mem_conjugate_iff', inv_inv]
        simpa [mul_assoc] using hv
      exact (le_iSup₂ (f := fun h (_ : h ∈ centralizer ({z} : Set G)) =>
        CFSG.conjugate V h) k⁻¹ (inv_mem hk)) hmem
  rw [hsup]
  have hVea := isElemAbelian_of_isElementaryAbelian' V
  by_cases hHM : S.H ≤ normalizer (L : Set G)
  ·
    obtain ⟨-, -, hTI, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
    have hle : conjClosure V S.H ≤ V := by
      refine conjClosure_le fun k hk v hv => ?_
      have hkM := hHM (inv_mem hk)
      rcases hTI _ hkM with h | h
      · have : k * v * k⁻¹ ∈ CFSG.conjugate V k⁻¹ := by
          rw [mem_conjugate_iff', inv_inv]
          simpa [mul_assoc] using hv
        rwa [h] at this
      · exfalso
        have hz : z ∈ V ⊓ CFSG.conjugate V k⁻¹ := mem_inf.2 ⟨S.hzV, by
          rw [mem_conjugate_iff', S.conj_V₁_of_H (inv_mem hk) S.z_mem_V₁]
          exact S.hzV⟩
        rw [h] at hz
        exact S.hz1 hz
    exact (F7.isElemAbelian_mono hVea hle).1
  · have hcod' : ∀ F : Subgroup G, F ≤ V → F.relIndex V ≤ 8 →
        centralizer (F : Set G) ≤ normalizer (V : Set G) :=
      fun F hFV hidx => hcod G T L V z hH hU3 hF F hFV hidx
    have h14 : ¬ pCoreOf 2 S.H ≤ centralizer (S.V₂ : Set G) := by
      have := h13314 G T L V S.V₂ hH (u3_isIrrPlusIn h1332 hH hU3 hF)
        (inf_centralizer_L_eq_bot hF) S.isV2 (not_iso_a5_of_U3 hU3 hF)
      rwa [S.g1_eq_H] at this
    have h15 : pCoreOf 2 S.H ⊓ centralizer (S.V₂ : Set G) ≤
        pCoreOf 2 (normalizer (S.V₂ : Set G)) := by
      have h := h13315 G T L V S.V₂ (L₁Of L S.V₂)
        (conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (S.V₂ : Set G))) hH
        (u3_isIrrPlusIn h1332 hH hU3 hF) (inf_centralizer_L_eq_bot hF) S.isV2
        (not_iso_a5_of_U3 hU3 hF) (fun h => absurd h (not_isHatA6_of_U3 hU3))
        (fun _ => rfl) rfl
      rw [S.g1_eq_H] at h
      exact h.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1
    exact (S.hullHyp (S.centralizer_V₃_le hB) (S.comm_eq_bot h12_4 hB) hHM h14 h15
      hcod').isElemAbelian.1

end CFSG.Quasithin.H13.U3
