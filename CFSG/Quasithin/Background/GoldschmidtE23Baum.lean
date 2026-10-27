module

public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F E2

namespace GE23

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {H T M : Subgroup G}

theorem commutator_alpha_mem (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hnost : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) {x a : G}
    (hx : x ∈ omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))))
    (ha : a ∈ A) : x * a * x⁻¹ * a⁻¹ ∈ V := by
  obtain ⟨-, -, -, h4⟩ := alpha_facts hV hVT hTN hnost
  have hxA := h4 A hA hx
  have hAN : A ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (hA.1.trans hTN)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hxA
  obtain ⟨c, hc, v, hv, rfl⟩ := hxA
  have hca : c * a = a * c := isElemAbelian_comm hA.2.1 hc.1 ha
  have hcv : ∀ w ∈ V, c * w = w * c := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
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

theorem cjSub_thompsonJ_le_commCentralizer (hV : IsElemAbelian 2 V) (h : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hnost : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B) {y : G} (hy : y ∈ H) :
    cjSub y (thompsonJ T) ≤
      commCentralizer (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)))) V := by
  have hT := h.isSylow
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hred.2.1
  have hJle : thompsonJ T ≤
      commCentralizer (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)))) V := by
    refine iSup₂_le fun A hA a ha => ⟨hTN (hA.1 ha), fun x hx => ?_⟩
    exact commutator_alpha_mem hV hVT hTN hnost hA hx ha
  intro z hz
  rw [mem_cjSub] at hz
  have := conj_mem_commCentralizer (le_normalizer_alpha h hred hJ hy) (hred.2.1 hy) (hJle hz)
  simpa [mul_assoc] using this

theorem baumann_of_data (hV : IsElemAbelian 2 V) (h : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hnost : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B)
    (hgen : ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set G) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T))
    (hrank : 2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤
      rkIdx (fixV (autI hV (twoResidual H)))) :
    omegaOneCenterOf (thompsonJ T) = (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G)) ∧
      V ≤ conjClosure (omegaOneCenterOf (thompsonJ T)) (twoResidual H) := by
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  obtain ⟨g, hgK, hgN, hKI⟩ := hgen
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
  obtain ⟨-, hVα, hEα, -⟩ := alpha_facts hV hVT hTN hnost
  have hαel : IsElemAbelian 2 α := isElemAbelian_omegaOneCenterOf _
  set W := E ⊔ V with hW
  have hWα : W ≤ α := sup_le hEα hVα
  have hWel : IsElemAbelian 2 W := isElemAbelian_mono hWα hαel
  have hI₀C : I₀ ≤ commCentralizer α V := by
    refine sup_le (fun x hx => ?_)
      (cjSub_thompsonJ_le_commCentralizer hV h hred hJ hnost (hKH hgK))
    refine cjSub_thompsonJ_le_commCentralizer hV h hred hJ hnost H.one_mem ?_
    rw [E2.cjSub_one]
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
    ⟨1, I₀.one_mem, (E2.cjSub_one _).le⟩
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
    E2.le_normalizer_of_commute fun a ha b hb =>
      isElemAbelian_comm hWel ((le_sup_right : V ≤ W) ha) hb.1
  have hEeq : E = (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
      (E ⊓ Subgroup.centralizer (twoResidual H : Set G)) := by
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
  refine ⟨hEeq, ?_⟩
  obtain ⟨hUV, -⟩ := W_decomp_two hV le_rfl hI₀N hI₀N hKI hd hX₁ hX₂ le_sup_right
  set A₁ := V ⊓ Subgroup.centralizer (thompsonJ T : Set G) with hA₁
  set A₂ := V ⊓ Subgroup.centralizer (cjSub g (thompsonJ T) : Set G) with hA₂
  have hA12 : A₁ ⊓ A₂ = V ⊓ Subgroup.centralizer (twoResidual H : Set G) := by
    rw [hUV]
    ext x
    simp only [Subgroup.mem_inf, hA₁, hA₂]
    constructor
    · rintro ⟨⟨hxV, hx1⟩, ⟨-, hx2⟩⟩
      exact ⟨hxV, mem_centralizer_sup hx1 hx2⟩
    · rintro ⟨hxV, hx⟩
      exact ⟨⟨hxV, Subgroup.centralizer_le (le_sup_left : thompsonJ T ≤ I₀) hx⟩,
        ⟨hxV, Subgroup.centralizer_le (le_sup_right : cjSub g (thompsonJ T) ≤ I₀) hx⟩⟩
  have e1 := rk_sup_add_rk_inf_of_commute (A := A₁) (B := A₂)
    (fun a ha b hb => isElemAbelian_comm hV ha.1 hb.1)
  rw [hA12] at e1
  have hsup : A₁ ⊔ A₂ = V :=
    eq_of_le_of_rk_le_of_isPGroup (isPGroup_of_isElemAbelian hV)
      (sup_le inf_le_left inf_le_left) (by omega)
  have hA₁E : A₁ ≤ E := inf_centralizer_thompsonJ_le hV hVT
  have hA₂eq : A₂ = cjSub g A₁ := by
    rw [hA₁, cjSub_inf, cjSub_centralizer, cjSub_eq_of_mem_normalizer hgN]
  have hA₂ : A₂ ≤ conjClosure E (twoResidual H) := by
    intro x hx
    rw [hA₂eq, mem_cjSub] at hx
    have := mem_conjClosure (Z := E) hgK (hA₁E hx)
    simpa [mul_assoc] using this
  rw [← hsup]
  exact sup_le (hA₁E.trans (le_conjClosure _ _)) hA₂

theorem e23_two_of_data (hV : IsElemAbelian 2 V) (h : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hnost : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B)
    (hgen : ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set G) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T))
    (hrank : 2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤
      rkIdx (fixV (autI hV (twoResidual H))))
    (hS : autI hV (baum T) = autI hV (thompsonJ T))
    (hsyl : IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)))
    (hfixK : fixV (autI hV (twoResidual H)) ≤ fixV (autI hV (thompsonJ H)))
    (hVK : V = ⁅V, twoResidual H⁆ ⊔ (V ⊓ Subgroup.centralizer (twoResidual H : Set G))) :
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) ∧
      conjClosure (omegaOneCenterOf (thompsonJ T)) (twoResidual H) =
        ⁅V, twoResidual H⁆ ⊔
          (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G)) := by
  obtain ⟨hE, hVcl⟩ := baumann_of_data hV h hred hJ hnost hgen hrank
  have hT := h.isSylow
  set E := omegaOneCenterOf (thompsonJ T) with hEdef
  set K := twoResidual H with hK
  set S := baum T with hSdef
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : K ≤ H := twoResidual_le H
  have hST : S ≤ T := inf_le_left
  have hSH : S ≤ H := hST.trans hT.1
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have hSN : S ≤ Subgroup.normalizer (V : Set G) := hSH.trans hHN
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hCVK : V ⊓ Subgroup.centralizer (K : Set G) ≤ E ⊓ Subgroup.centralizer (K : Set G) := by
    intro x hx
    refine ⟨inf_centralizer_thompsonJ_le hV hVT ⟨hx.1, ?_⟩, hx.2⟩
    have hfix := (mem_fixV_autI hV hKN (IntMod.mk hV ⟨x, hx.1⟩)).2 hx.2
    have hfix' := B1.fixV_le_fixV
      (autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)) (hfixK hfix)
    exact (mem_fixV_autI hV ((thompsonJ_le_self T).trans (hT.1.trans hHN)) _).1 hfix'
  refine ⟨?_, ?_⟩
  ·
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.1.trans (le_normalizer_twoResidual H)
    have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
    have hSK : S ≤ Subgroup.normalizer (K : Set G) := hST.trans hTK
    have h2 : IsSylowTwoOf (autI hV S) (autI hV (K ⊔ S)) := by
      rw [autI_sup hV hKN hSN, hS]
      have hle : autI hV K ⊔ autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
        sup_le (autI_mono hV (E2.twoResidual_le_thompsonJ h hred hJ)) hsyl.1
      refine ⟨le_sup_right, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
      have h2' : 2 ∣ (autI hV (thompsonJ T)).relIndex (autI hV K ⊔ autI hV (thompsonJ T)) := h2
      show 2 ∣ (autI hV (thompsonJ T)).relIndex (autI hV (thompsonJ H))
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hle]
      exact h2'.mul_right _
    have hN_le : (K ⊔ S) ⊓ Subgroup.centralizer (V : Set G) ≤ H :=
      inf_le_left.trans (sup_le hKH hSH)
    have hTN' : T ≤ Subgroup.normalizer
        (((K ⊔ S) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf (B2F.le_normalizer_sup hTK hTS)
        (B2F.le_normalizer_centralizer (hT.1.trans hHN))
    have hodd := not_two_dvd_relIndex_inf_of_normalizer hT.1 hN_le hT.2.2 hTN'
    have hclaim : T ⊓ ((K ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) =
        S ⊓ Subgroup.centralizer (V : Set G) := by
      apply le_antisymm
      · rintro x ⟨hxT, hxKS, hxC⟩
        refine ⟨⟨hxT, ?_⟩, hxC⟩
        have hxKS' : x ∈ ((K ⊔ S : Subgroup G) : Set G) := hxKS
        rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSK] at hxKS'
        obtain ⟨k, hk, s, hs, rfl⟩ := hxKS'
        show k * s ∈ Subgroup.centralizer (E : Set G)
        rw [hE]
        refine mem_centralizer_sup ?_ ?_
        · exact Subgroup.mem_centralizer_iff.2 fun y hy =>
            Subgroup.mem_centralizer_iff.1 hxC y hy.1
        · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
          have e1 := Subgroup.mem_centralizer_iff.1 hy.2 k hk
          have e2 := Subgroup.mem_centralizer_iff.1 hs.2 y hy.1
          calc y * (k * s) = (y * k) * s := by rw [mul_assoc]
            _ = (k * y) * s := by rw [← e1]
            _ = k * (y * s) := by rw [mul_assoc]
            _ = k * (s * y) := by rw [e2]
            _ = (k * s) * y := by rw [mul_assoc]
      · exact fun x hx => ⟨hST hx.1, ⟨Subgroup.mem_sup_right hx.1, hx.2⟩⟩
    have hsylC : IsSylowTwoOf (S ⊓ Subgroup.centralizer (V : Set G))
        ((K ⊔ S) ⊓ Subgroup.centralizer (V : Set G)) := by
      refine ⟨inf_le_inf_right _ le_sup_right, hT.2.1.to_le (inf_le_left.trans hST), ?_⟩
      rw [← hclaim]
      exact hodd
    exact isSylowTwoOf_of_isSylowTwoOf_autI hV (sup_le hKN hSN) le_sup_right
      (hT.2.1.to_le hST) hsylC h2
  ·
    apply le_antisymm
    · have hAN : V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ≤ Subgroup.normalizer
          ((E ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
        E2.le_normalizer_of_commute fun a ha b hb =>
          isElemAbelian_comm (isElemAbelian_omegaOneCenterOf _)
            (inf_centralizer_thompsonJ_le hV hVT ha) hb.1
      have hle : conjClosure E K ≤ V ⊔ (E ⊓ Subgroup.centralizer (K : Set G)) := by
        refine conjClosure_le fun k hk x hx => ?_
        have hx' : x ∈ (((V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
            (E ⊓ Subgroup.centralizer (K : Set G)) : Subgroup G) : Set G) := by
          rw [← hE]
          exact hx
        rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hx'
        obtain ⟨a, ha, b, hb, rfl⟩ := hx'
        have hkb : k * b * k⁻¹ = b := by
          rw [(Subgroup.mem_centralizer_iff.1 hb.2 k hk), mul_inv_cancel_right]
        have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
        rw [e, hkb]
        exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hKN hk) a).mp ha.1) hb
      exact hle.trans (sup_le ((hVK.le.trans (sup_le_sup_left hCVK _))) le_sup_right)
    · exact sup_le ((E2.commutator_le_self hKN).trans hVcl) (inf_le_left.trans (le_conjClosure _ _))

end GE23

end CFSG.Quasithin
