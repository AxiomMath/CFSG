module

public import CFSG.Quasithin.EmptyFaithful.S152YE
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.S152Y

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section CGS

omit [Finite G] in
theorem normalizer_le_CGS' {R C : Subgroup G} (hC : C ≤ R) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf R).Characteristic) : Subgroup.normalizer (C : Set G) ≤ CGS R := by
  unfold CGS
  exact le_iSup_of_le C (le_iSup_of_le hC (le_iSup_of_le hC1 (le_iSup_of_le hchar le_rfl)))

omit [Finite G] in
theorem cgsIn_le_of_CGS_le' {I R M : Subgroup G} (h : CGS R ≤ M) : cgsIn I R ≤ M ⊓ I := by
  refine iSup_le fun C => iSup_le fun hC => iSup_le fun hC1 => iSup_le fun hchar => ?_
  exact le_inf (inf_le_right.trans ((normalizer_le_CGS' hC hC1 hchar).trans h)) inf_le_left

end CGS

section Core

variable {J L P E : Subgroup G}

theorem le_pCoreOf_of_acts_trivially (hJ : J ≤ L ⊔ P) (hLJ : L ≤ J) (hPJ : P ≤ J) (hP2 : IsPGroup 2 P)
    (hEP : E ≤ P) (hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G))
    (hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 L : Set G))
    (hPE : ∀ t ∈ P, ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hLE : ∀ l ∈ L, ∀ e ∈ E, l * e * l⁻¹ * e⁻¹ ∈ pCoreOf 2 L) : E ≤ pCoreOf 2 J := by
  have hEQ : E ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := hEP.trans hPQ
  have hset : ((pCoreOf 2 L ⊔ E : Subgroup G) : Set G) = (pCoreOf 2 L : Set G) * (E : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hEQ
  have hN2 : IsPGroup 2 ↥(pCoreOf 2 L ⊔ E) :=
    IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 L) (hP2.to_le hEP) hEQ
  have hNle : pCoreOf 2 L ⊔ E ≤ J := sup_le ((pCoreOf_le 2 L).trans hLJ) (hEP.trans hPJ)
  have hnorm : J ≤ Subgroup.normalizer ((pCoreOf 2 L ⊔ E : Subgroup G) : Set G) := by
    refine hJ.trans (sup_le ?_ ?_)
    · intro l hl
      refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
      obtain ⟨q, hq, e, he, rfl⟩ : k ∈ (pCoreOf 2 L : Set G) * (E : Set G) := hset ▸ hk
      have h1 : l * q * l⁻¹ ∈ pCoreOf 2 L := (Subgroup.mem_normalizer_iff.mp (hLQ hl) q).mp hq
      have h2 : l * e * l⁻¹ * e⁻¹ ∈ pCoreOf 2 L := hLE l hl e he
      have h3 : l * (q * e) * l⁻¹ = (l * q * l⁻¹) * ((l * e * l⁻¹ * e⁻¹) * e) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right he))
    · intro t ht
      refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
      obtain ⟨q, hq, e, he, rfl⟩ : k ∈ (pCoreOf 2 L : Set G) * (E : Set G) := hset ▸ hk
      have h1 : t * q * t⁻¹ ∈ pCoreOf 2 L := (Subgroup.mem_normalizer_iff.mp (hPQ ht) q).mp hq
      have h2 : t * e * t⁻¹ ∈ E := hPE t ht e he
      have h3 : t * (q * e) * t⁻¹ = (t * q * t⁻¹) * (t * e * t⁻¹) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  exact (le_sup_right : E ≤ pCoreOf 2 L ⊔ E).trans (le_pCoreOf_of_le_normalizer 2 hNle hnorm hN2)

end Core

section Sylow

variable {T M I : Subgroup G}

omit [Finite G] in
theorem lI_le_inf : lI T M I ≤ M ⊓ I := by
  have hLIle : lI T M I ≤ yOfL22 T M ⊓ I := oTwoUpper_le _
  exact le_inf ((hLIle.trans inf_le_left).trans (yOfL22_le T M)) (hLIle.trans inf_le_right)

theorem i1Of1469_le_inf (S : Setting146 G T M) : i1Of1469 T M I ≤ M ⊓ I :=
  sup_le lI_le_inf (le_inf (inf_le_left.trans S.hyp1281.inM.2) inf_le_right)

omit [Finite G] in
theorem inf_le_normalizer_lI (T M I : Subgroup G) :
    M ⊓ I ≤ Subgroup.normalizer (lI T M I : Set G) := by
  intro x hx
  have h1 : x ∈ Subgroup.normalizer (yOfL22 T M ⊓ I : Set G) := by
    have := Subgroup.inf_normalizer_le_normalizer_inf (H := yOfL22 T M) (K := I)
      ⟨le_normalizer_yOfL22 T M hx.1, Subgroup.le_normalizer hx.2⟩
    simpa using this
  exact normalizer_le_normalizer_oTwoUpper _ h1

theorem isSylowTwoOf_centralizerSection_i1 (S : Setting146 G T M) (hsyl : IsSylowTwoOf (T ⊓ I) I) :
    IsSylowTwoOf (pCoreOf 2 (i1Of1469 T M I))
      (centralizerSection (M ⊓ I) (lI T M I) (pCoreOf 2 (lI T M I))) := by
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hI₁def : i1Of1469 T M I = lI T M I ⊔ (T ⊓ I) := rfl
  have hLIM : lI T M I ≤ M ⊓ I := lI_le_inf
  have hTIM : T ⊓ I ≤ M ⊓ I := le_inf (inf_le_left.trans hTM) inf_le_right
  have hI₁M : i1Of1469 T M I ≤ M ⊓ I := i1Of1469_le_inf S
  have hI₁I : i1Of1469 T M I ≤ I := hI₁M.trans inf_le_right
  have hMIN : M ⊓ I ≤ Subgroup.normalizer (lI T M I : Set G) := inf_le_normalizer_lI T M I
  have hTIsylM : IsSylowTwoOf (T ⊓ I) (M ⊓ I) := A4.isSylowTwoOf_mono hsyl hTIM inf_le_right
  have hTIsylI₁ : IsSylowTwoOf (T ⊓ I) (i1Of1469 T M I) :=
    A4.isSylowTwoOf_mono hsyl (hI₁def ▸ le_sup_right) hI₁I
  have hR₁TI : pCoreOf 2 (i1Of1469 T M I) ≤ T ⊓ I := B6.pCoreOf_two_le_of_isSylowTwoOf hTIsylI₁
  have hR₁MI : pCoreOf 2 (i1Of1469 T M I) ≤ M ⊓ I := (pCoreOf_le 2 _).trans hI₁M
  have hLI₁ : lI T M I ≤ i1Of1469 T M I := hI₁def ▸ le_sup_left
  have hLIR : lI T M I ≤ Subgroup.normalizer (pCoreOf 2 (i1Of1469 T M I) : Set G) :=
    hLI₁.trans (le_normalizer_pCoreOf 2 _)
  have hR₁LI : pCoreOf 2 (i1Of1469 T M I) ≤ Subgroup.normalizer (lI T M I : Set G) :=
    hR₁MI.trans hMIN
  have hc1 : ⁅lI T M I, pCoreOf 2 (i1Of1469 T M I)⁆ ≤ lI T M I :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hR₁LI
  have hc2 : ⁅lI T M I, pCoreOf 2 (i1Of1469 T M I)⁆ ≤ pCoreOf 2 (i1Of1469 T M I) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hLIR
  have hcQ : ⁅lI T M I, pCoreOf 2 (i1Of1469 T M I)⁆ ≤ pCoreOf 2 (lI T M I) :=
    (le_inf hc1 hc2).trans (le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hLIR hl⟩)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right))
  have hR₁C : pCoreOf 2 (i1Of1469 T M I) ≤
      centralizerSection (M ⊓ I) (lI T M I) (pCoreOf 2 (lI T M I)) :=
    (le_centralizerSection_iff (pCoreOf_le 2 (lI T M I))).mpr ⟨hR₁MI, hcQ⟩
  have hCN : M ⊓ I ≤ Subgroup.normalizer
      (centralizerSection (M ⊓ I) (lI T M I) (pCoreOf 2 (lI T M I)) : Set G) :=
    centralizerSection_normal hMIN
  have hCMI : centralizerSection (M ⊓ I) (lI T M I) (pCoreOf 2 (lI T M I)) ≤ M ⊓ I :=
    centralizerSection_le_left _ _ _
  have hTI₁ : T ⊓ I ≤ i1Of1469 T M I := hI₁def ▸ le_sup_right
  have hE : (T ⊓ I) ⊓ centralizerSection (M ⊓ I) (lI T M I) (pCoreOf 2 (lI T M I)) ≤
      pCoreOf 2 (i1Of1469 T M I) :=
    le_pCoreOf_of_acts_trivially (le_of_eq hI₁def) hLI₁ hTI₁ hsyl.2.1 inf_le_left
      (le_normalizer_pCoreOf 2 _)
      (fun t ht => normalizer_le_normalizer_pCoreOf 2 _ (hMIN (hTIM ht)))
      (fun t ht e he => ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ht he.1) (Subgroup.inv_mem _ ht),
        (Subgroup.mem_normalizer_iff.mp (hCN (hTIM ht)) e).mp he.2⟩)
      (fun l hl e he => (mem_centralizerSection.mp he.2).2.2.2 l hl)
  have hEq : (T ⊓ I) ⊓ centralizerSection (M ⊓ I) (lI T M I) (pCoreOf 2 (lI T M I)) =
      pCoreOf 2 (i1Of1469 T M I) := le_antisymm hE (le_inf hR₁TI hR₁C)
  have := A4.isSylowTwoOf_inf_normal hTIsylM hCMI hCN
  rwa [hEq] at this

end Sylow

section C23

variable {T M H : Subgroup G} {u : G} {I I₂ : Subgroup G}

theorem pCoreOf_i1_ne_bot (c : Hyp14610 T M H u I I₂) (hVI₁ : VZ T M ≤ i1Of1469 T M I) :
    pCoreOf 2 (i1Of1469 T M I) ≠ ⊥ := by
  have S : Setting146 G T M := c.setting
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hUT : conjClosure (VZ T M) H ≤ T :=
    (S.conjClosure_le_pCoreOf c.hH).trans (S.pCoreOf_le_T c.hH)
  have hV2 : IsPGroup 2 (VZ T M) := S.hyp.sylow.1.to_le ((le_conjClosure _ _).trans hUT)
  have hI₁M : i1Of1469 T M I ≤ M := (i1Of1469_le_inf S).trans inf_le_left
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hVle : VZ T M ≤ pCoreOf 2 (i1Of1469 T M I) :=
    le_pCoreOf_of_le_normalizer 2 hVI₁ (hI₁M.trans hMV) hV2
  intro h
  rw [h, le_bot_iff] at hVle
  rw [hVle] at hV4
  simp at hV4

theorem c23_of_facts (c : Facts14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    IsTwoRadicalIn I (pCoreOf 2 (i1Of1469 T M I)) ∧
      IsSylowTwoOf (pCoreOf 2 (i1Of1469 T M I))
        (conjClosure (pCoreOf 2 (i1Of1469 T M I)) (M ⊓ I)) := by
  have S : Setting146 G T M := c.setting
  obtain ⟨-, -, -, -, hVI₁⟩ := Setting146.exists_y_fpf c.toHyp14610 hLT
  have hR1 : pCoreOf 2 (i1Of1469 T M I) ≠ ⊥ := pCoreOf_i1_ne_bot c.toHyp14610 hVI₁
  have hsylC := isSylowTwoOf_centralizerSection_i1 S hsyl
  have hLn : ((lI T M I).subgroupOf (M ⊓ I)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer lI_le_inf).mpr (inf_le_normalizer_lI T M I)
  obtain ⟨hsylD, hrad⟩ :=
    c1_2_four (oTwoUpper_oTwoUpper _).symm lI_le_inf hLn hsylC hR1
  refine ⟨⟨(pCoreOf_le 2 _).trans ((i1Of1469_le_inf S).trans inf_le_right), hR1, ?_⟩, hsylD⟩
  have hINM : I ⊓ Subgroup.normalizer (pCoreOf 2 (i1Of1469 T M I) : Set G) ≤ M ⊓ I :=
    (inf_normalizer_le_cgsIn hR1).trans (cgsIn_le_of_CGS_le' c.c1)
  have hEq : (M ⊓ I) ⊓ Subgroup.normalizer (pCoreOf 2 (i1Of1469 T M I) : Set G) =
      I ⊓ Subgroup.normalizer (pCoreOf 2 (i1Of1469 T M I) : Set G) :=
    le_antisymm (inf_le_inf_right _ inf_le_right) (le_inf hINM inf_le_right)
  rw [← hEq]
  exact hrad.2.2

end C23

end CFSG.Quasithin.S152Y
