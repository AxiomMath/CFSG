module

public import CFSG.Quasithin.EmptyFaithful.S152FinGeom
public import CFSG.Quasithin.EmptyFaithful.S152FinConj
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.EmptyFaithful.S152FinBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G]

namespace S152Fin

theorem relIndex_eq_two_of_not_le {Q X : Subgroup G} (hle : Q.relIndex X ≤ 2) (hnot : ¬ X ≤ Q) :
    Q.relIndex X = 2 := by
  have h1 : Q.relIndex X ≠ 1 := fun h => hnot (Subgroup.relIndex_eq_one.mp h)
  have h0 : Q.relIndex X ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

omit [Finite G] in
theorem mQuot_eq_one_of_relIndex_two {Q X : Subgroup G} (h : Q.relIndex X = 2) :
    E3.mQuot X (X ⊓ Q) = 1 := by
  unfold E3.mQuot
  rw [Subgroup.inf_relIndex_left, h]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat_self

theorem final_core {M H T V Z : Subgroup G} (hAm : AmalgamHypV (M ⊔ H) M H T V)
    (hFF : ¬ @IsFFModule V (commGroupOfElemAbelian hAm.elemAbelian) (autOn M V))
    (hVQ : V ≤ pCoreOf 2 H) (hUab : IsElemAbelian 2 (conjClosure V H))
    (hs : 1 < E3.sParam hAm.elemAbelian) (hZV : Z ≤ V)
    (hw0 : E3.wClos V 0 (pCoreOf 2 H) ≤
      H ⊓ Subgroup.centralizer (conjClosure V H : Set G))
    (h27 : ∀ g : G, Z ⊓ conjSub g V ≠ ⊥ → ⁅V, conjSub g V⁆ = ⊥)
    (h28 : ⁅conjClosure V H, lambdaOf (pCoreOf 2 H)⁆ ≤ Z)
    (hKer : H ⊓ Subgroup.centralizer (conjClosure V H : Set G) ≤ pCoreOf 2 H)
    (hRankH : ∀ E : Subgroup G, E ≤ H → IsElemAbelian 2 E → (pCoreOf 2 H).relIndex E ≤ 4)
    (hRankM : ∀ D : Subgroup G, D ≤ M → IsElemAbelian 2 D →
      (Subgroup.centralizer (V : Set G)).relIndex D ≤ 2)
    (hKL : ∀ X : Subgroup G, X ≤ H → IsElemAbelian 2 X →
      (Subgroup.centralizer (X : Set G)).relIndex (conjClosure V H) ≤ 8 →
      (pCoreOf 2 H).relIndex X ≤ 2) : False := by
  have hV₂ : IsElemAbelian 2 V := hAm.elemAbelian
  have hVbot : V ≠ ⊥ := by
    intro hbot
    have h1 := E3.sParam_le_rk hV₂
    subst hbot
    rw [rk_bot] at h1
    omega
  have hodd := odd_critDist_of_not_isFFModule hAm hVbot hFF
  have hb2 := two_le_critDist_of_le_pCoreOf hAm hVbot hVQ
  obtain ⟨g, hVg, hVQg, hUg, hUg'⟩ := exists_geom_config hAm hVbot hodd hb2
  have hQM : pCoreOf 2 H ≤ M :=
    (F7.isSylowTwoOf_pCoreOf_le hAm.sylow₂).trans hAm.sylow₁.1
  have hex : ∃ h ∈ H, ¬ V ≤ Subgroup.centralizer (conjSub (g * h) V : Set G) := by
    by_contra hcon
    push Not at hcon
    have h1 : V ≤ Subgroup.centralizer (conjSub g (conjClosure V H) : Set G) :=
      le_centralizer_conjSub_conjClosure g hcon
    rw [conjSub_centralizer] at h1
    have h2 : conjSub g⁻¹ V ≤ H ⊓ Subgroup.centralizer (conjClosure V H : Set G) :=
      le_inf ((le_conjSub_iff g).mp hVg) ((le_conjSub_iff g).mp h1)
    exact hVQg ((le_conjSub_iff g).mpr (h2.trans hKer))
  obtain ⟨h, hhH, hnc⟩ := hex
  have hUa : conjSub (g * h) (conjClosure V H) = conjSub g (conjClosure V H) := by
    rw [conjSub_mul, conjSub_conjClosure_of_mem hhH]
  have hQa : conjSub (g * h) (pCoreOf 2 H) = conjSub g (pCoreOf 2 H) := by
    rw [conjSub_mul, conjSub_pCoreOf_of_mem hhH]
  have hWU : conjSub (g * h) V ≤ conjSub g (conjClosure V H) := by
    rw [← hUa]
    exact conjSub_mono _ (le_conjClosure V H)
  have hWH : conjSub (g * h) V ≤ H := hWU.trans hUg
  have hUab' : IsElemAbelian 2 (conjSub g (conjClosure V H)) := F7.isElemAbelian_conjSub hUab
  have hWab : IsElemAbelian 2 (conjSub (g * h) V) := F7.isElemAbelian_mono hUab' hWU
  have hcomm_VW : ⁅V, conjSub (g * h) V⁆ ≠ ⊥ := fun hc =>
    hnc (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
  have hWQ : ¬ conjSub (g * h) V ≤ pCoreOf 2 H := by
    intro hle
    have h1 := conjSub_le_wClos_zero (g * h) hle
    have h2 : conjSub (g * h) V ≤ Subgroup.centralizer (conjClosure V H : Set G) :=
      (h1.trans hw0).trans inf_le_right
    have h3 : conjSub (g * h) V ≤ Subgroup.centralizer (V : Set G) :=
      h2.trans (Subgroup.centralizer_le (le_conjClosure V H))
    exact hnc (Subgroup.le_centralizer_iff.mp h3)
  have hDHidx : (conjSub g (pCoreOf 2 H)).relIndex (conjClosure V H) ≤ 4 := by
    have hE : conjSub g⁻¹ (conjClosure V H) ≤ H := (le_conjSub_iff g).mp hUg'
    have h1 := hRankH _ hE (F7.isElemAbelian_conjSub hUab)
    have h2 := relIndex_conjSub g (pCoreOf 2 H) (conjSub g⁻¹ (conjClosure V H))
    rw [conjSub_inv_conjSub] at h2
    rw [h2]
    exact h1
  have hDHC : (Subgroup.centralizer (conjSub (g * h) V : Set G)).relIndex
      (conjSub g (pCoreOf 2 H) ⊓ conjClosure V H) ≤ 2 := by
    have hD'eq : conjSub (g * h)⁻¹ (conjSub g (pCoreOf 2 H) ⊓ conjClosure V H) =
        pCoreOf 2 H ⊓ conjSub (g * h)⁻¹ (conjClosure V H) := by
      rw [conjSub_inf, ← hQa, conjSub_conjSub_inv, inf_comm]
    have hD'M : conjSub (g * h)⁻¹ (conjSub g (pCoreOf 2 H) ⊓ conjClosure V H) ≤ M := by
      rw [hD'eq]
      exact inf_le_left.trans hQM
    have hD'ab : IsElemAbelian 2
        (conjSub (g * h)⁻¹ (conjSub g (pCoreOf 2 H) ⊓ conjClosure V H)) := by
      rw [hD'eq]
      exact F7.isElemAbelian_mono (F7.isElemAbelian_conjSub hUab) inf_le_right
    have h1 := hRankM _ hD'M hD'ab
    have h2 := relIndex_centralizer_conjSub (g * h) V
      (conjSub (g * h)⁻¹ (conjSub g (pCoreOf 2 H) ⊓ conjClosure V H))
    rw [conjSub_inv_conjSub] at h2
    rw [h2]
    exact h1
  have hR1 : (Subgroup.centralizer (conjSub (g * h) V : Set G)).relIndex (conjClosure V H) ≤ 8 := by
    have h1 := relIndex_le_mul_inf (P := conjSub g (pCoreOf 2 H)) (U := conjClosure V H)
      (C := Subgroup.centralizer (conjSub (g * h) V : Set G))
    calc _ ≤ _ := h1
      _ ≤ 4 * 2 := Nat.mul_le_mul hDHidx hDHC
  have hW2 : (pCoreOf 2 H).relIndex (conjSub (g * h) V) = 2 :=
    relIndex_eq_two_of_not_le (hKL _ hWH hWab hR1) hWQ
  have hV'H : conjSub g⁻¹ V ≤ H := (le_conjSub_iff g).mp hVg
  have hV'ab : IsElemAbelian 2 (conjSub g⁻¹ V) := F7.isElemAbelian_conjSub hV₂
  have hR2 : (Subgroup.centralizer (conjSub g⁻¹ V : Set G)).relIndex (conjClosure V H) ≤ 8 := by
    have e := relIndex_centralizer_conjSub g (conjSub g⁻¹ V) (conjClosure V H)
    rw [conjSub_inv_conjSub] at e
    rw [← e]
    have h1 := relIndex_le_mul_inf (P := pCoreOf 2 H) (U := conjSub g (conjClosure V H))
      (C := Subgroup.centralizer (V : Set G))
    have h2 : (pCoreOf 2 H).relIndex (conjSub g (conjClosure V H)) ≤ 4 := hRankH _ hUg hUab'
    have h3 : (Subgroup.centralizer (V : Set G)).relIndex
        (pCoreOf 2 H ⊓ conjSub g (conjClosure V H)) ≤ 2 :=
      hRankM _ (inf_le_left.trans hQM) (F7.isElemAbelian_mono hUab' inf_le_right)
    calc _ ≤ _ := h1
      _ ≤ 4 * 2 := Nat.mul_le_mul h2 h3
  have hV'Q : ¬ conjSub g⁻¹ V ≤ pCoreOf 2 H := fun hle => hVQg ((le_conjSub_iff g).mpr hle)
  have hV'2 : (pCoreOf 2 H).relIndex (conjSub g⁻¹ V) = 2 :=
    relIndex_eq_two_of_not_le (hKL _ hV'H hV'ab hR2) hV'Q
  have hVγ2 : (conjSub g (pCoreOf 2 H)).relIndex V = 2 := by
    have h1 := relIndex_conjSub g (pCoreOf 2 H) (conjSub g⁻¹ V)
    rw [conjSub_inv_conjSub] at h1
    rw [h1]
    exact hV'2
  have hDHab : IsElemAbelian 2 (conjSub g (pCoreOf 2 H) ⊓ conjClosure V H) :=
    F7.isElemAbelian_mono hUab inf_le_right
  have hDγab : IsElemAbelian 2 (pCoreOf 2 H ⊓ conjSub g (conjClosure V H)) :=
    F7.isElemAbelian_mono hUab' inf_le_right
  have c1 : ⁅conjSub g (pCoreOf 2 H) ⊓ conjClosure V H, pCoreOf 2 H ⊓ conjSub g (conjClosure V H)⁆ ≤ Z :=
    (Subgroup.commutator_mono inf_le_right
      (le_lambdaOf_of_isElemAbelian hDγab inf_le_left)).trans h28
  have c2 : ⁅conjSub g (pCoreOf 2 H) ⊓ conjClosure V H, pCoreOf 2 H ⊓ conjSub g (conjClosure V H)⁆ ≤
      conjSub (g * h) Z := by
    have hle : conjSub g (pCoreOf 2 H) ⊓ conjClosure V H ≤ conjSub (g * h) (lambdaOf (pCoreOf 2 H)) :=
      le_conjSub_lambdaOf (g * h) hDHab (by rw [hQa]; exact inf_le_left)
    calc _ ≤ ⁅conjSub g (pCoreOf 2 H) ⊓ conjClosure V H, conjSub g (conjClosure V H)⁆ :=
          Subgroup.commutator_mono le_rfl inf_le_right
      _ = ⁅conjSub g (conjClosure V H), conjSub g (pCoreOf 2 H) ⊓ conjClosure V H⁆ :=
          Subgroup.commutator_comm _ _
      _ ≤ ⁅conjSub (g * h) (conjClosure V H), conjSub (g * h) (lambdaOf (pCoreOf 2 H))⁆ := by
          rw [hUa]
          exact Subgroup.commutator_mono le_rfl hle
      _ = conjSub (g * h) ⁅conjClosure V H, lambdaOf (pCoreOf 2 H)⁆ :=
          conjSub_commutator (g * h) _ _
      _ ≤ conjSub (g * h) Z := conjSub_mono _ h28
  have hZZ : Z ⊓ conjSub (g * h) Z = ⊥ := by
    by_contra hne
    have hne' : Z ⊓ conjSub (g * h) V ≠ ⊥ := fun hbot =>
      hne (le_bot_iff.mp ((inf_le_inf_left Z (conjSub_mono (g * h) hZV)).trans hbot.le))
    exact hcomm_VW (h27 (g * h) hne')
  have hDD : ⁅conjSub g (pCoreOf 2 H) ⊓ conjClosure V H, pCoreOf 2 H ⊓ conjSub g (conjClosure V H)⁆ = ⊥ :=
    le_bot_iff.mp ((le_inf c1 c2).trans hZZ.le)
  have hcomm_QQ : ⁅V ⊓ conjSub g (pCoreOf 2 H), conjSub (g * h) V ⊓ pCoreOf 2 H⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono ?_ ?_).trans hDD.le)
    · exact le_inf inf_le_right (inf_le_left.trans (le_conjClosure V H))
    · exact le_inf inf_le_right (inf_le_left.trans hWU)
  have hs' : 1 < E3.sParam hV₂ := hs
  have hVWab : IsElemAbelian 2 (conjSubgroup V (g * h)⁻¹) := E3.isElemAbelian_conjSubgroup hV₂ _
  have hVeq : conjSubgroup V (g * h)⁻¹ = conjSub (g * h) V := conjSubgroup_inv_eq_conjSub V (g * h)
  have hsW : 1 < E3.sParam hVWab := by
    rw [E3.sParam_conj hV₂ _ hVWab]
    exact hs'
  have hE2 : IsPGroup 2 ↥(V ⊓ conjSub g (pCoreOf 2 H)) := hAm.isPGroup.to_le inf_le_left
  have hmQ1 : E3.mQuot (conjSubgroup V (g * h)⁻¹)
      (conjSubgroup V (g * h)⁻¹ ⊓ pCoreOf 2 H) = 1 := by
    rw [hVeq]
    exact mQuot_eq_one_of_relIndex_two hW2
  have h6 := E3.e3_6 hVWab (A := conjSubgroup V (g * h)⁻¹)
    (B := conjSubgroup V (g * h)⁻¹ ⊓ pCoreOf 2 H) (E := V ⊓ conjSub g (pCoreOf 2 H))
    inf_le_left le_rfl (by omega) hE2
  have hE₁ : V ⊓ conjSub g (pCoreOf 2 H) ≤ Subgroup.centralizer (conjSub (g * h) V : Set G) := by
    have hle : V ⊓ conjSub g (pCoreOf 2 H) ≤
        Subgroup.centralizer ((conjSub (g * h) V ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_QQ
    have h1 := h6.1
    rw [hVeq] at h1
    have h2 : (V ⊓ conjSub g (pCoreOf 2 H)) ⊓
        Subgroup.centralizer ((conjSub (g * h) V ⊓ pCoreOf 2 H : Subgroup G) : Set G) =
        V ⊓ conjSub g (pCoreOf 2 H) := inf_eq_left.mpr hle
    exact inf_eq_left.mp (h1.trans h2)
  have hE3 : IsPGroup 2 (conjSub (g * h) V) := F7.isPGroup_conjSub hAm.isPGroup
  have hmQ2 : E3.mQuot V (V ⊓ conjSub g (pCoreOf 2 H)) = 1 :=
    mQuot_eq_one_of_relIndex_two hVγ2
  have h7 := E3.e3_6 hV₂ (A := V) (B := V ⊓ conjSub g (pCoreOf 2 H)) (E := conjSub (g * h) V)
    inf_le_left le_rfl (by omega) hE3
  have hW_le : conjSub (g * h) V ≤
      Subgroup.centralizer ((V ⊓ conjSub g (pCoreOf 2 H) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp hE₁
  have h8 : conjSub (g * h) V ⊓ Subgroup.centralizer (V : Set G) = conjSub (g * h) V := by
    rw [h7.1]
    exact inf_eq_left.mpr hW_le
  exact hnc (Subgroup.le_centralizer_iff.mp (inf_eq_left.mp h8))

end S152Fin

end CFSG.Quasithin
