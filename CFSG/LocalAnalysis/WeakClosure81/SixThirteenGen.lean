module

public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenConj
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl613 (k : ℕ) (V : Subgroup G) : Prop :=
  ∀ H S : Subgroup G, CFSG.QuasithinUnique.CharTwo H → IsSylowIn 2 S H →
    (CompFactorAutInF k H S →
      (H : Set G) = ((H ⊓ normalizer (E3.wClos V 0 S : Set G) : Subgroup G) : Set G) *
        ((H ⊓ centralizer (E3.cClos V k S : Set G) : Subgroup G) : Set G)) ∧
    (E1.InE k H →
      (H ⊓ normalizer (E3.wClos V 0 S : Set G)) ⊔ (H ⊓ centralizer (E3.cClos V k S : Set G)) = H)

theorem exists_inCalO1_of_commutator_ne_bot {M V₀ V H S A K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hMnorm : normalizer (V : Set G) = M) (hN₀ : normalizer (V₀ : Set G) = M)
    (hTI : ∀ y : G, V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ → conjSubgroup V₀ y = V₀)
    (hS : IsSylowIn 2 S H) {k : ℕ}
    (hA : A ∈ E3.gammaSet V 0 S) (hK : E1.IsE k H S A K)
    (hkV : k < rk ↥V) (hr : (k : ℕ∞) < E3.rParam V)
    (hmbar : k < mBar M V₀ V hV)
    (hne : ⁅twoResidual K, E3.cClos V k S⁆ ≠ ⊥) :
    V₀ ≠ ⊥ ∧ ∃ g : G, InCalO1 k M V₀ V g := by
  obtain ⟨-, x, hAx, -⟩ := id hA
  have hVx : IsElemAbelian 2 (conjSubgroup V x) := E3.isElemAbelian_conjSubgroup hV x
  have hV₀x : conjSubgroup V₀ x ≤ conjSubgroup V x := E3.conjSubgroup_mono_left x hV₀
  have hNx : normalizer (conjSubgroup V x : Set G) = conjSubgroup M x := by
    rw [← E3.conjSubgroup_normalizer, hMnorm]
  have hN₀x : normalizer (conjSubgroup V₀ x : Set G) = conjSubgroup M x := by
    rw [← E3.conjSubgroup_normalizer, hN₀]
  have key := six_nine_one_core_of_isE (M := conjSubgroup M x) (V₀ := conjSubgroup V₀ x)
    (V := conjSubgroup V x) hVx hV₀x hNx.ge hN₀x.ge hNx hN₀x (isTI_form_conj hTI x) hS
    (by rwa [E3.gammaSet_conjV]) hAx hK (by rwa [E3.rk_conjSubgroup]) (by rwa [E3.rParam_conj])
    (by rw [mBar_conj M V₀ V hV hV₀ hM hM₀ x]; exact hmbar) (by rwa [E3.cClos_conjV])
  obtain ⟨hV₀ne, g', -, hg'⟩ := key
  refine ⟨fun h => hV₀ne (by rw [h, E3.conjSubgroup_bot]), x * g' * x⁻¹, ?_⟩
  have hO : InCalO k M V₀ V (x * g' * x⁻¹) := by
    refine (inCalO_conj x (x * g' * x⁻¹)).1 ?_
    rw [show x⁻¹ * (x * g' * x⁻¹) * x = g' by group]
    exact hg'.1
  exact (six_six hV hV₀ hM hM₀ hmbar _).1 hO

variable {M V₀ V : Subgroup G}

theorem mBar_bot_eq_mParam_autI {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : normalizer (V : Set G) = M) :
    mBar M ⊥ V hV = E3.mParam (autI hV ⊤) := by
  unfold mBar
  rw [Mbar, TwelveShort.barSub_bot_eq_map_congr M V hV hM.symm, E3.mParam_map_congr]

theorem mBar_le_rk {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) :
    mBar M V₀ V hV ≤ rk ↥V := by
  have h1 : mBar M V₀ V hV ≤ rk (Vtil V₀ V hV) := E3.mParam_le_rk _
  have hc := card_Vtil_eq V₀ V hV hV₀
  refine h1.trans ?_
  unfold rk
  exact padicValNat_two_le_of_dvd Nat.card_pos.ne' ⟨Nat.card V₀, by rw [hc, mul_comm]⟩

theorem commutator_twoResidual_cClos_eq_bot_of_no_calO1 (hH : Hyp6H M V₀ V) (hV₀ : V₀ ≠ ⊥)
    {k : ℕ} (hkr : (k : ℕ∞) < rMV M V) (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : ∀ g : G, ¬ InCalO1 k M V₀ V g)
    {H S A K : Subgroup G} (hS : IsSylowIn 2 S H) (hA : A ∈ E3.gammaSet V 0 S)
    (hK : E1.IsE k H S A K) :
    ⁅twoResidual K, E3.cClos V k S⁆ = ⊥ := by
  by_contra hne
  obtain ⟨-, g, hg⟩ := exists_inCalO1_of_commutator_ne_bot hH.elemAbelian hH.le
    hH.normalizer_eq.symm.le hH.le_normalizer₀ hH.normalizer_eq (hH.normalizer₀ hV₀)
    (forall_conjSubgroup_eq_of_isTI (hH.isTI hV₀)) hS hA hK
    (hkm.trans_le (mBar_le_rk hH.elemAbelian hH.le))
    (by rwa [← rMV_eq_rParam hH.normalizer_eq]) hkm hne
  exact hno g hg

theorem eGen_le_sup_of_no_calO1 (hH : Hyp6H M V₀ V) {k : ℕ} (hkr : (k : ℕ∞) < rMV M V)
    (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : V₀ ≠ ⊥ → ∀ g : G, ¬ InCalO1 k M V₀ V g) {H S : Subgroup G} (hS : IsSylowIn 2 S H) :
    E1.eGen k H S (E3.gammaSet V 0 H) ≤
      (H ⊓ centralizer (E3.cClos V k S : Set G)) ⊔ S := by
  by_cases hV₀ : V₀ = ⊥
  · have hV := hH.elemAbelian
    have hr : (k : ℕ∞) < E3.rParam V := by rwa [← rMV_eq_rParam hH.normalizer_eq]
    have hm : k < E3.mParam (autI hV ⊤) := by
      rwa [← mBar_bot_eq_mParam_autI hV hH.normalizer_eq, ← hV₀]
    have hlt : 0 + k < E3.sParam hV := by
      rw [zero_add]
      exact E3.lt_sParam_of_lt hV hr hm
    simpa using TwelveShort.eGen_le_sup_of_lt_sParam hV hS hlt
  · refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
    have hAΓ : A ∈ E3.gammaSet V 0 S := ⟨hAS, hA.2⟩
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    have hKeq : K = (S ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hSK).symm
    have hcomm := commutator_twoResidual_cClos_eq_bot_of_no_calO1 hH hV₀ hkr hkm
      (hno hV₀) hS hAΓ hK
    have h1 : S ⊓ K ≤ S := inf_le_left
    have h2 : twoResidual K ≤ H ⊓ centralizer (E3.cClos V k S : Set G) :=
      le_inf ((twoResidual_le K).trans hK.1)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
    rw [hKeq]
    exact sup_le (h1.trans le_sup_right) (h2.trans le_sup_left)

theorem six_thirteen_two_of_no_calO1 (hH : Hyp6H M V₀ V) {k : ℕ} (hkr : (k : ℕ∞) < rMV M V)
    (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : V₀ ≠ ⊥ → ∀ g : G, ¬ InCalO1 k M V₀ V g) {H S : Subgroup G} (hS : IsSylowIn 2 S H)
    (hE : E1.InE k H) :
    (H ⊓ normalizer (E3.wClos V 0 S : Set G)) ⊔ (H ⊓ centralizer (E3.cClos V k S : Set G)) =
      H := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have hV := hH.elemAbelian
  have hEF := (E1.inE_iff_inEFor hS).1 hE (E3.gammaSet V 0 H) (E3.isInvColl_gammaSet hV 0 H)
  rw [E3.weakClosure_gammaSet hS.le] at hEF
  have hSN : S ≤ H ⊓ normalizer (E3.wClos V 0 S : Set G) :=
    le_inf hS.le (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S))
  calc H = E1.eGen k H S (E3.gammaSet V 0 H) ⊔
        (H ⊓ normalizer (E3.wClos V 0 S : Set G)) := hEF.symm
    _ ≤ ((H ⊓ centralizer (E3.cClos V k S : Set G)) ⊔ S) ⊔
        (H ⊓ normalizer (E3.wClos V 0 S : Set G)) :=
      sup_le_sup_right (eGen_le_sup_of_no_calO1 hH hkr hkm hno hS) _
    _ ≤ _ := sup_le (sup_le le_sup_right (hSN.trans le_sup_left)) le_sup_left

theorem six_thirteen_one_of_no_calO1 (h45 : W3Lem45_2 G) (hH : Hyp6H M V₀ V) {k : ℕ}
    (hk1 : 1 ≤ k) (hkr : (k : ℕ∞) < rMV M V) (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : V₀ ≠ ⊥ → ∀ g : G, ¬ InCalO1 k M V₀ V g) {H S : Subgroup G} (hS : IsSylowIn 2 S H)
    (hFk : CompFactorAutInF k H S) :
    (H : Set G) = ((H ⊓ normalizer (E3.wClos V 0 S : Set G) : Subgroup G) : Set G) *
      ((H ⊓ centralizer (E3.cClos V k S : Set G) : Subgroup G) : Set G) := by
  have hV := hH.elemAbelian
  have h45' := h45 H S k (E3.gammaSet V 0 H) hk1 hS (E3.isInvColl_gammaSet hV 0 H) hFk
  rw [E3.weakClosure_gammaSet hS.le] at h45'
  have h45'' : (H : Set G) =
      (E1.eGen k H S (E3.gammaSet V 0 H) : Set G) *
        ((H ⊓ normalizer (E3.wClos V 0 S : Set G) : Subgroup G) : Set G) := h45'
  have hSN : S ≤ H ⊓ normalizer (E3.wClos V 0 S : Set G) :=
    le_inf hS.le (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S))
  have hSC : S ≤ normalizer
      ((H ⊓ centralizer (E3.cClos V k S : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_inf (hS.le.trans Subgroup.le_normalizer)
      (A1a.le_normalizer_centralizer
        (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := k) S)))
  have hmain := TwelveShort.eq_mul_of_le_sup (H := H) (S := S)
    (C := H ⊓ centralizer (E3.cClos V k S : Set G))
    (N := H ⊓ normalizer (E3.wClos V 0 S : Set G))
    (E := E1.eGen k H S (E3.gammaSet V 0 H))
    inf_le_left inf_le_left hSN hSC (eGen_le_sup_of_no_calO1 hH hkr hkm hno hS) h45''
  ext x
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ (H : Set G) := H.inv_mem hx
    rw [hmain] at hx'
    obtain ⟨c, hc, n, hn, hcn⟩ := hx'
    refine ⟨n⁻¹, Subgroup.inv_mem _ hn, c⁻¹, Subgroup.inv_mem _ hc, ?_⟩
    have hcn' : c * n = x⁻¹ := hcn
    show n⁻¹ * c⁻¹ = x
    rw [← mul_inv_rev, hcn', inv_inv]
  · rintro ⟨n, hn, c, hc, rfl⟩
    exact H.mul_mem hn.1 hc.1

theorem concl613_of_no_calO1 (h45 : W3Lem45_2 G) (hH : Hyp6H M V₀ V) {k : ℕ}
    (hk1 : 1 ≤ k) (hkr : (k : ℕ∞) < rMV M V) (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : V₀ ≠ ⊥ → ∀ g : G, ¬ InCalO1 k M V₀ V g) : Concl613 k V := by
  intro H S _ hS
  exact ⟨fun hFk => six_thirteen_one_of_no_calO1 h45 hH hk1 hkr hkm hno hS hFk,
    fun hE => six_thirteen_two_of_no_calO1 hH hkr hkm hno hS hE⟩

end CFSG.LocalAnalysis.WeakClosure81
