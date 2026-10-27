module

public import CFSG.Quasithin.H13.L32A721b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem false_of_conj_le_centralizer {D : Subgroup G} (hD1 : D ≠ ⊥) (hD2 : IsPGroup 2 ↥D)
    (hDH : D ≤ hz T V) (hDn : hz T V ≤ Subgroup.normalizer (D : Set G))
    (hcent : ∀ g : G, Quasithin.conjSub g D ≤ pCoreOf 2 (l1 T L V ⊔ T) →
      Quasithin.conjSub g D ≤ Subgroup.centralizer (fsuU T V : Set G)) : False := by
  have h := E.S.hyp
  have h13322 := stmt13_3_2_two_of E.h1332
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  have hnot : ¬ hz T V ≤ Subgroup.normalizer (L : Set G) := hH ▸ E.S.hz.2.2
  obtain ⟨hQR, hR1T⟩ := E.qh_le_r1
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hQR₁ : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      ((sup_le_sup_right hl1L T).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  set S : Set G := {x | ∃ g : G, Quasithin.conjSub g D ≤ pCoreOf 2 (l1 T L V ⊔ T) ∧
    x ∈ Quasithin.conjSub g D} with hS
  have hgen : ∀ g : G, Quasithin.conjSub g D ≤ pCoreOf 2 (l1 T L V ⊔ T) →
      Quasithin.conjSub g D ≤ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 (hz T V) := by
    intro g hg
    have hT := hg.trans hR1T
    have hC := hcent g hg
    refine le_inf ?_ fun d hd => E.centralizer_le_qh hF
      (Subgroup.mem_inf.mpr ⟨E.t_le_hz (hT hd), hC hd⟩)
    rw [← hF.cT]
    exact le_inf hT (hC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVU)))
  have hXQ : Subgroup.closure S ≤ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 (hz T V) := by
    rw [Subgroup.closure_le]
    rintro x ⟨g, hg, hx⟩
    exact hgen g hg hx
  have hnorm : ∀ Y : Subgroup G, (∀ y ∈ Y, ∀ g : G,
      Quasithin.conjSub g D ≤ pCoreOf 2 (l1 T L V ⊔ T) →
        Quasithin.conjSub (y * g) D ≤ pCoreOf 2 (l1 T L V ⊔ T)) →
      Y ≤ Subgroup.normalizer (Subgroup.closure S : Set G) := by
    intro Y hY y hy
    refine mem_normalizer_of_forall_conj (Q := Y) (R := Subgroup.closure S)
      (fun q hq x hx => ?_) hy
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj q).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x ⟨g, hg, hxg⟩
      show (MulAut.conj q) x ∈ Subgroup.closure S
      refine Subgroup.subset_closure ⟨q * g, hY q hq g hg, ?_⟩
      rw [Quasithin.conjSub_mul]
      exact ⟨x, hxg, rfl⟩
    exact hle hx
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.closure S : Set G) :=
    hnorm (L ⊔ T) fun y hy g hg => by
      rw [Quasithin.conjSub_mul]
      have h2 : Quasithin.conjSub y (pCoreOf 2 (L ⊔ T)) = pCoreOf 2 (L ⊔ T) :=
        conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hy)
      exact ((Quasithin.conjSub_mono y ((hgen g hg).trans inf_le_left)).trans h2.le).trans hQR₁
  have hHX : hz T V ≤ Subgroup.normalizer (Subgroup.closure S : Set G) :=
    hnorm (hz T V) fun y hy g hg => by
      rw [Quasithin.conjSub_mul]
      have h2 : Quasithin.conjSub y (pCoreOf 2 (hz T V)) = pCoreOf 2 (hz T V) :=
        conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hy)
      exact ((Quasithin.conjSub_mono y ((hgen g hg).trans inf_le_right)).trans h2.le).trans hQR
  have hDX : D ≤ Subgroup.closure S := by
    have hD1' : Quasithin.conjSub 1 D ≤ pCoreOf 2 (l1 T L V ⊔ T) := by
      rw [Quasithin.conjSub_one]
      exact (le_pCoreOf_of_le_normalizer 2 hDH hDn hD2).trans hQR
    intro d hd
    exact Subgroup.subset_closure ⟨1, hD1', by rw [Quasithin.conjSub_one]; exact hd⟩
  have hX1 : Subgroup.closure S ≠ ⊥ := fun h0 => hD1 (le_bot_iff.mp (h0 ▸ hDX))
  have hX2 : IsPGroup 2 ↥(Subgroup.closure S) :=
    (pCoreOf_isPGroup 2 _).to_le (hXQ.trans inf_le_right)
  exact hnot (hHX.trans (normalizer_le_normalizer_L h h13322 hX1 hX2 hLT))

end Ctx7153

end CFSG.Quasithin.H13.L32A
