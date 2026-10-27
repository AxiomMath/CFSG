module

public import CFSG.Quasithin.H13.GoldschmidtC137WeakComm
public import CFSG.Quasithin.Background.B2FactorizationBaumann

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

open B2F in
theorem B2_18' [Finite G] {V L R : Subgroup G} (hV : IsElemAbelian 2 V) (hVN : V.Normal)
    (hL : L = pResidualOf 2 (⊤ : Subgroup G)) (hR : IsPGroup 2 R) (hVR : V ≤ R)
    (ha₁ : pCoreOf 2 L ≤ R ⊓ Subgroup.centralizer (V : Set G))
    (ha₂ : L ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hb : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoPhi L)
    (hc : ∀ A, ¬ IsStrongFFOffender hV R A)
    (hde : ∃ (n : ℕ) (X : Fin n → Subgroup G),
      (∀ i, ∃ l ∈ L, cjSub l (X i) ≤ R) ∧ (∀ i, X i = thompsonJ (X i)) ∧
      (∀ i, Open.pRank 2 (X i) = Open.pRank 2 R) ∧ autI hV L ≤ ⨆ i, autI hV (X i) ∧
      ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV L)) ∧
      thompsonJ R ≤ ⨆ i, X i) :
    pCoreOf 2 L ≤ baum R ∧
      omegaOneCenterOf (thompsonJ R) =
        (omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G)) ⊔
          (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) ∧
      (IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
          ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) →
        IsSylowTwoOf (baum R ⊓ Subgroup.centralizer (V : Set G))
          ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) ∧
        (IsSylowTwoOf (autI hV (baum R)) (autI hV L ⊔ autI hV (baum R)) →
          IsSylowTwoOf (baum R) (L ⊔ baum R))) := by
  obtain ⟨n, X, hXconj, hXJ, hXrank, hLX, hsum, hJX⟩ := hde
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hVN]
    exact Subgroup.mem_top g
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := fun g _ => hN g
  have hLnormal : L.Normal := by
    rw [hL]
    exact normal_pResidualOf_top
  have hOR : pCoreOf 2 L ≤ R := ha₁.trans inf_le_left
  obtain ⟨I, hI⟩ : ∃ I : Subgroup G, I = ⨆ i, X i := ⟨_, rfl⟩
  have hJI : thompsonJ R ≤ I := by
    rw [hI]
    exact hJX
  have hXN : ∀ i, X i ≤ Subgroup.normalizer (V : Set G) := fun i g _ => hN g
  have hLI₀ : autI hV L ≤ autI hV I := by
    rw [hI, autI_iSup hV X hXN]
    exact hLX
  have hdec := L_decomp hV hN hL hb hLI₀
  have hGJ := exists_cjSub_eq (L := L) (R := R) (I := I) hOR hdec
  have hXJ' : ∀ i, ∃ l ∈ L, cjSub l (X i) ≤ thompsonJ R := fun i => by
    obtain ⟨l, hl, hlR⟩ := hXconj i
    exact ⟨l, hl, cjSub_le_thompsonJ (hXJ i) (hXrank i) hlR⟩
  obtain ⟨hIeq, hIN⟩ := I_eq_normalClosure X hI hJI hXJ' hGJ
  have hLI : L ≤ I := L_le_I hL hOR hdec hIN
  have hXg : ∀ i, ∃ g ∈ I, cjSub g (X i) ≤ thompsonJ R := by
    intro i
    obtain ⟨l, hl, hlX⟩ := hXJ' i
    obtain ⟨i', hi', he⟩ := hGJ l⁻¹ (Subgroup.mem_sup_left (L.inv_mem hl))
    refine ⟨i'⁻¹, I.inv_mem hi', ?_⟩
    have h1 : X i ≤ cjSub l⁻¹ (thompsonJ R) := by
      have := cjSub_mono (g := l⁻¹) hlX
      rwa [cjSub_inv_cjSub] at this
    rw [he] at h1
    have := cjSub_mono (g := i'⁻¹) h1
    rwa [cjSub_inv_cjSub] at this
  have hQM : L ⊔ R ≤ Subgroup.normalizer
      ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    sup_le ha₂ (le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hRN))
  have hcomm := commutator_alpha_le' hV hVN hVR hRN hc hQM hIeq
  have hfacts := alpha_facts' hV hVR hRN hc
  have hIW : I ≤ Subgroup.normalizer ((omegaOneCenterOf (thompsonJ R) ⊔ V : Subgroup G) : Set G) :=
    mem_normalizer_sup hVN hfacts.2.2.1 hcomm
  have hWQ : omegaOneCenterOf (thompsonJ R) ⊔ V ≤
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) :=
    sup_le hfacts.2.2.1 hfacts.2.1
  have hWel : IsElemAbelian 2 (omegaOneCenterOf (thompsonJ R) ⊔ V) :=
    isElemAbelian_mono hWQ (isElemAbelian_omegaOneCenterOf _)
  have hαZ : omegaOneCenterOf (thompsonJ R) ≤ Subgroup.centralizer (thompsonJ R : Set G) :=
    fun x hx => (omegaOneCenterOf_le_centerOf _ hx).2
  have hαJ : omegaOneCenterOf (thompsonJ R) ≤ thompsonJ R :=
    fun x hx => (omegaOneCenterOf_le_centerOf _ hx).1
  have hWJ : omegaOneCenterOf (thompsonJ R) ⊔ V ≤
      ((omegaOneCenterOf (thompsonJ R) ⊔ V) ⊓ Subgroup.centralizer (thompsonJ R : Set G)) ⊔ V :=
    sup_le_sup_right (le_inf le_sup_left hαZ) V
  obtain ⟨hU, hWUV⟩ := W_decomp hV hWel hVN le_sup_right X hI hIW hLI hsum hXg hWJ
  have hWR : omegaOneCenterOf (thompsonJ R) ⊔ V ≤ R :=
    sup_le (hαJ.trans (thompsonJ_le_self R)) hVR
  have hUα : (omegaOneCenterOf (thompsonJ R) ⊔ V) ⊓ Subgroup.centralizer (L : Set G) ≤
      omegaOneCenterOf (thompsonJ R) := by
    intro u hu
    have hu' : u ∈ (omegaOneCenterOf (thompsonJ R) ⊔ V) ⊓ Subgroup.centralizer (I : Set G) :=
      hU ▸ hu
    rw [← (omegaOne_centralizer_thompsonJ R).1]
    exact Subgroup.subset_closure ⟨⟨hWR hu'.1, Subgroup.centralizer_le hJI hu'.2⟩,
      hWel.2 u hu'.1⟩
  have h2 : omegaOneCenterOf (thompsonJ R) =
      (omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G)) ⊔
        (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) := by
    refine le_antisymm ?_ (sup_le inf_le_left (inf_centralizer_thompsonJ_le hV hVR))
    intro x hx
    have hxW : x ∈ omegaOneCenterOf (thompsonJ R) ⊔ V := Subgroup.mem_sup_left hx
    rw [hWUV, sup_comm] at hxW
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hxW
    have huα : u ∈ omegaOneCenterOf (thompsonJ R) := hUα hu
    have hvα : v ∈ omegaOneCenterOf (thompsonJ R) := by
      have := (omegaOneCenterOf (thompsonJ R)).mul_mem
        ((omegaOneCenterOf (thompsonJ R)).inv_mem huα) hx
      simpa using this
    exact Subgroup.mul_mem_sup (G := G) ⟨huα, hu.2⟩ ⟨hv, hαZ hvα⟩
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := fun g _ => hN g
  have h1 : pCoreOf 2 L ≤ baum R := by
    intro o ho
    refine ⟨hOR ho, ?_⟩
    have hC1 : pCoreOf 2 L ≤ Subgroup.centralizer
        ((omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
          Set G) := fun o ho =>
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 hy.2 o (pCoreOf_le 2 L ho)).symm
    have hC2 : pCoreOf 2 L ≤ Subgroup.centralizer
        ((V ⊓ Subgroup.centralizer (thompsonJ R : Set G) : Subgroup G) : Set G) := fun o ho =>
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        Subgroup.mem_centralizer_iff.1 (ha₁ ho).2 y hy.1
    have := le_centralizer_sup hC1 hC2
    rw [← h2] at this
    exact this ho
  refine ⟨h1, h2, fun hSyl => ?_⟩
  have hS_le : baum R ≤ R := inf_le_left
  have hRS : R ≤ Subgroup.normalizer (baum R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum R)
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 hLnormal]
    exact Subgroup.mem_top g
  have hclaimA : (R ⊓ Subgroup.centralizer (V : Set G)) ⊓
      ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) =
      baum R ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · rintro x ⟨⟨hxR, hxC⟩, ⟨hxLS, -⟩⟩
      refine ⟨⟨hxR, ?_⟩, hxC⟩
      obtain ⟨l, hl, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hxLS
      have hT1 : l * s ∈ Subgroup.centralizer
          ((omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
            Set G) := by
        refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        have e1 := Subgroup.mem_centralizer_iff.1 hy.2 l hl
        have e2 := Subgroup.mem_centralizer_iff.1 hs.2 y hy.1
        calc y * (l * s) = (y * l) * s := by rw [mul_assoc]
          _ = (l * y) * s := by rw [← e1]
          _ = l * (y * s) := by rw [mul_assoc]
          _ = l * (s * y) := by rw [e2]
          _ = (l * s) * y := by rw [mul_assoc]
      have hT2 : l * s ∈ Subgroup.centralizer
          ((V ⊓ Subgroup.centralizer (thompsonJ R : Set G) : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun y hy => Subgroup.mem_centralizer_iff.1 hxC y hy.1
      have := mem_centralizer_sup hT1 hT2
      rwa [← h2] at this
    · exact fun x hx => ⟨⟨hS_le hx.1, hx.2⟩, ⟨Subgroup.mem_sup_right hx.1, hx.2⟩⟩
  have hSN : R ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer
      (((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (le_normalizer_inf (le_normalizer_sup hRL hRS)
      (le_normalizer_centralizer hRN))
  have hN_le : (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) ≤
      (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) :=
    inf_le_inf_right _ (sup_le_sup_left hS_le L)
  have hsyl : IsSylowTwoOf ((R ⊓ Subgroup.centralizer (V : Set G)) ⊓
      ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)))
      ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) :=
    ⟨inf_le_right, hR.to_le (inf_le_left.trans inf_le_left),
      not_two_dvd_relIndex_inf_of_normalizer hSyl.1 hN_le hSyl.2.2 hSN⟩
  rw [hclaimA] at hsyl
  refine ⟨hsyl, fun hSyl2 => ?_⟩
  refine isSylowTwoOf_of_isSylowTwoOf_autI hV (A := L ⊔ baum R) (fun g _ => hN g)
    le_sup_right (hR.to_le hS_le) hsyl ?_
  rwa [autI_sup hV hLN (fun g _ => hN g)]

end CFSG.Quasithin
