module

public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F E2

namespace LRed10

variable {G : Type*} [Group G] [Finite G] {V H T M : Subgroup G}

@[expose] def CardEq (V R : Subgroup G) : Prop :=
  ∀ A : Subgroup G, IsMaxElemAbelian R A → ¬ A ≤ Subgroup.centralizer (V : Set G) →
    Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))

theorem alpha_facts' {R : Subgroup G} (hV : IsElemAbelian 2 V) (hVR : V ≤ R) (hc : CardEq V R) :
    (∀ D, IsMaxElemAbelian (R ⊓ Subgroup.centralizer (V : Set G)) D → IsMaxElemAbelian R D) ∧
    V ≤ omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ∧
    omegaOneCenterOf (thompsonJ R) ≤
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ∧
    (∀ A, IsMaxElemAbelian R A →
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ≤
        (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
  set Q := R ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := le_centralizer_self hV
  have hVQ : V ≤ Q := le_inf hVR hVC
  have hsub : ∀ D, IsMaxElemAbelian Q D → IsMaxElemAbelian R D := by
    by_cases hex : ∃ A, IsMaxElemAbelian R A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G)
    · obtain ⟨A, hA, hAC⟩ := hex
      exact (B24_three hV hVR hA (hc A hA hAC)).2.2.1
    · push Not at hex
      obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian R
      have hA₀Q : A₀ ≤ Q := le_inf hA₀.1 (hex A₀ hA₀)
      intro D hD
      refine ⟨hD.1.trans inf_le_left, hD.2.1, fun B hBR hB => ?_⟩
      exact (hA₀.2.2 B hBR hB).trans (hD.2.2 A₀ hA₀Q hA₀.2.1)
  have hVD : ∀ D, IsMaxElemAbelian Q D → V ≤ D := by
    intro D hD
    have hDC : D ≤ Subgroup.centralizer (V : Set G) := hD.1.trans inf_le_right
    have hE : IsElemAbelian 2 (D ⊔ V) :=
      isElemAbelian_sup_of_commute hD.2.1 hV fun d hd v hv =>
        (Subgroup.mem_centralizer_iff.1 (hDC hd) v hv).symm
    have hEQ : D ⊔ V ≤ Q := sup_le hD.1 hVQ
    have h := Subgroup.eq_of_le_of_card_ge (le_sup_left : D ≤ D ⊔ V) (hD.2.2 _ hEQ hE)
    exact le_sup_right.trans (le_of_eq h.symm)
  have hE : ∀ A, IsMaxElemAbelian R A →
      IsMaxElemAbelian Q ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
    intro A hA
    have hEe : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
      isElemAbelian_sup_of_commute (isElemAbelian_mono inf_le_left hA.2.1) hV
        fun a ha v hv => (Subgroup.mem_centralizer_iff.1 ha.2 v hv).symm
    have hEQ : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ Q :=
      sup_le (le_inf (inf_le_left.trans hA.1) inf_le_right) hVQ
    refine ⟨hEQ, hEe, fun B hBQ hB => ?_⟩
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
    · have hAE : A ≤ (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V :=
        le_sup_of_le_left (le_inf le_rfl hAC)
      exact (hA.2.2 B (hBQ.trans inf_le_left) hB).trans (Subgroup.card_le_of_le hAE)
    · have hmax := (B24_three hV hVR hA (hc A hA hAC)).1
      exact hmax.2.2 B (hBQ.trans inf_le_left) hB
  refine ⟨hsub, ?_, ?_, fun A hA => ?_⟩
  · rw [(omegaOne_centralizer_thompsonJ Q).2]
    exact le_iInf₂ fun D hD => hVD D hD
  · rw [(omegaOne_centralizer_thompsonJ R).2, (omegaOne_centralizer_thompsonJ Q).2]
    exact le_iInf₂ fun D hD => iInf₂_le D (hsub D hD)
  · rw [(omegaOne_centralizer_thompsonJ Q).2]
    exact iInf₂_le _ (hE A hA)

theorem commutator_alpha_mem' (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H)
    (hc : CardEq V T) {A : Subgroup G} (hA : IsMaxElemAbelian T A) {x a : G}
    (hx : x ∈ omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))))
    (ha : a ∈ A) : x * a * x⁻¹ * a⁻¹ ∈ V := by
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hred.2.1
  obtain ⟨-, -, -, h4⟩ := alpha_facts' hred.2.2.1 hVT hc
  have hxA := h4 A hA hx
  have hAN : A ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (hA.1.trans hTN)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hxA
  obtain ⟨c, hc', v, hv, rfl⟩ := hxA
  have hca : c * a = a * c := isElemAbelian_comm hA.2.1 hc'.1 ha
  have hcv : ∀ w ∈ V, c * w = w * c := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp hc'.2 w hw).symm
  have hav : a * v⁻¹ * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hTN (hA.1 ha)) _).mp (V.inv_mem hv)
  have hw : v * (a * v⁻¹ * a⁻¹) ∈ V := V.mul_mem hv hav
  have e : c * v * a * (c * v)⁻¹ * a⁻¹ = c * (v * (a * v⁻¹ * a⁻¹)) * c⁻¹ := by
    calc c * v * a * (c * v)⁻¹ * a⁻¹ = c * v * a * v⁻¹ * (c⁻¹ * a⁻¹) := by group
      _ = c * v * a * v⁻¹ * (a⁻¹ * c⁻¹) := by
          rw [← mul_inv_rev, ← mul_inv_rev, hca]
      _ = c * (v * (a * v⁻¹ * a⁻¹)) * c⁻¹ := by group
  rw [e, hcv _ hw, mul_inv_cancel_right]
  exact hw

theorem cjSub_thompsonJ_le_commCentralizer' (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hc : CardEq V T)
    {y : G} (hy : y ∈ H) :
    cjSub y (thompsonJ T) ≤
      commCentralizer (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)))) V := by
  have hT := h.isSylow
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hred.2.1
  have hJle : thompsonJ T ≤
      commCentralizer (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)))) V := by
    refine iSup₂_le fun A hA a ha => ⟨hTN (hA.1 ha), fun x hx => ?_⟩
    exact commutator_alpha_mem' hred hT hc hA hx ha
  intro z hz
  rw [mem_cjSub] at hz
  have := conj_mem_commCentralizer (le_normalizer_alpha h hred hJ hy) (hred.2.1 hy) (hJle hz)
  simpa [mul_assoc] using this

theorem baumann_core (hV : IsElemAbelian 2 V) (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hc : CardEq V T)
    (hg : ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set G) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T))
    (hrank : 2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤
      rkIdx (fixV (autI hV (twoResidual H)))) :
    omegaOneCenterOf (thompsonJ T) = (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G)) := by
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  obtain ⟨g, hgK, hgN, hKI⟩ := hg
  set E := omegaOneCenterOf (thompsonJ T) with hE
  set α := omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))) with hα
  set I₀ := thompsonJ T ⊔ cjSub g (thompsonJ T) with hI₀
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hT.1
  have hI₀H : I₀ ≤ H := by
    refine sup_le hJTH fun z hz => ?_
    rw [mem_cjSub] at hz
    have := H.mul_mem (H.mul_mem (hKH hgK) (hJTH hz)) (H.inv_mem (hKH hgK))
    simpa [mul_assoc] using this
  have hI₀N : I₀ ≤ Subgroup.normalizer (V : Set G) := hI₀H.trans hHN
  obtain ⟨-, hVα, hEα, -⟩ := alpha_facts' hV hVT hc
  have hαel : IsElemAbelian 2 α := isElemAbelian_omegaOneCenterOf _
  set W := E ⊔ V with hW
  have hWα : W ≤ α := sup_le hEα hVα
  have hWel : IsElemAbelian 2 W := isElemAbelian_mono hWα hαel
  have hI₀C : I₀ ≤ commCentralizer α V := by
    refine sup_le (fun x hx => ?_) (cjSub_thompsonJ_le_commCentralizer' h hred hJ hc (hKH hgK))
    refine cjSub_thompsonJ_le_commCentralizer' h hred hJ hc H.one_mem ?_
    rw [cjSub_one]
    exact hx
  have hI₀W : I₀ ≤ Subgroup.normalizer (W : Set G) := by
    have key : ∀ j ∈ commCentralizer α V, ∀ w ∈ W, j * w * j⁻¹ ∈ W := by
      intro j hj w hw
      have h1 := hj.2 w (hWα hw)
      have h2 : j * w * j⁻¹ = (w * j * w⁻¹ * j⁻¹)⁻¹ * w := by group
      rw [h2]
      exact W.mul_mem (Subgroup.mem_sup_right (V.inv_mem h1)) hw
    intro i hi
    have hiC := hI₀C hi
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key i hiC w, fun hw => ?_⟩
    have := key i⁻¹ ((commCentralizer α V).inv_mem hiC) _ hw
    simpa [mul_assoc] using this
  have hJTN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) := hJTH.trans hHN
  have hJgN : cjSub g (thompsonJ T) ≤ Subgroup.normalizer (V : Set G) :=
    (le_sup_right : cjSub g (thompsonJ T) ≤ I₀).trans hI₀N
  have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have r1 := rkIdx_fixV_autI hV hJTN
  have r2 := rkIdx_fixV_autI hV hJgN
  have r3 := rk_inf_centralizer_cjSub (U := V) hgN (thompsonJ T)
  have r5 := rkIdx_fixV_autI hV hKN
  have hd : rkIdx (fixV (autI hV (thompsonJ T))) +
      rkIdx (fixV (autI hV (cjSub g (thompsonJ T)))) ≤
        rkIdx (fixV (autI hV (twoResidual H))) := by omega
  have hX₁ : ∃ x ∈ I₀, cjSub x (thompsonJ T) ≤ thompsonJ T :=
    ⟨1, I₀.one_mem, (cjSub_one _).le⟩
  have hX₂ : ∃ x ∈ I₀, cjSub x (cjSub g (thompsonJ T)) ≤ thompsonJ T :=
    ⟨g⁻¹, I₀.inv_mem (hKI hgK), (cjSub_inv_cjSub g _).le⟩
  have hEZ : E ≤ Subgroup.centralizer (thompsonJ T : Set G) :=
    fun x hx => (omegaOneCenterOf_le_centerOf _ hx).2
  have hEJ : E ≤ thompsonJ T := fun x hx => (omegaOneCenterOf_le_centerOf _ hx).1
  have hWJ : W ≤ (W ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔ V :=
    sup_le ((le_inf le_sup_left hEZ).trans le_sup_left) le_sup_right
  obtain ⟨hU, hWUV⟩ := W_decomp_two hWel le_sup_right hI₀W hI₀N hKI hd hX₁ hX₂ hWJ
  have hWT : W ≤ T := sup_le (hEJ.trans (thompsonJ_le_self T)) hVT
  have hUE : W ⊓ Subgroup.centralizer (twoResidual H : Set G) ≤ E := by
    intro u hu
    have hu' : u ∈ W ⊓ Subgroup.centralizer (I₀ : Set G) := hU ▸ hu
    rw [hE, ← (omegaOne_centralizer_thompsonJ T).1]
    exact Subgroup.subset_closure ⟨⟨hWT hu'.1,
      Subgroup.centralizer_le (le_sup_left : thompsonJ T ≤ I₀) hu'.2⟩, hWel.2 u hu'.1⟩
  have hVU : V ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer (twoResidual H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun a ha b hb =>
      isElemAbelian_comm hWel ((le_sup_right : V ≤ W) ha) hb.1
  refine le_antisymm ?_ (sup_le (inf_centralizer_thompsonJ_le hV hVT) inf_le_left)
  intro x hx
  have hxW : x ∈ ((V ⊔ (W ⊓ Subgroup.centralizer (twoResidual H : Set G)) : Subgroup G) :
      Set G) := by
    rw [← hWUV]
    exact Subgroup.mem_sup_left hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVU] at hxW
  obtain ⟨v, hv, u, hu, rfl⟩ := hxW
  have huE : u ∈ E := hUE hu
  have hvE : v ∈ E := by
    have := E.mul_mem hx (E.inv_mem huE)
    simpa using this
  exact Subgroup.mul_mem_sup ⟨hv, hEZ hvE⟩ ⟨huE, hu.2⟩

theorem pCoreOf_twoResidual_le_baum (hV : IsElemAbelian 2 V) (h : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hc : CardEq V T)
    (hg : ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set G) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T))
    (hrank : 2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤
      rkIdx (fixV (autI hV (twoResidual H)))) :
    pCoreOf 2 (twoResidual H) ≤ baum T := by
  have h2 := baumann_core hV h hred hJ hc hg hrank
  have hPH : pCoreOf 2 (twoResidual H) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (twoResidual_le H))
      ((le_normalizer_twoResidual H).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  have hC1 : pCoreOf 2 (twoResidual H) ≤ Subgroup.centralizer
      ((omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G) :
        Subgroup G) : Set G) := fun o ho =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 hy.2 o (pCoreOf_le 2 _ ho)).symm
  have hC2 : pCoreOf 2 (twoResidual H) ≤ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (thompsonJ T : Set G) : Subgroup G) : Set G) := fun o ho =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      Subgroup.mem_centralizer_iff.1 (MinParabolic.pCoreOf_le_centralizer hred (hPH ho)) y hy.1
  have hC := le_centralizer_sup hC2 hC1
  rw [← h2] at hC
  intro o ho
  exact ⟨B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylow (hPH ho), hC ho⟩

end LRed10

end CFSG.Quasithin
