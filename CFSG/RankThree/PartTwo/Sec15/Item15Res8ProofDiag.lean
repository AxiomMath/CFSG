module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagF
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag

open CFSG CFSG.ComponentClassification Equiv

structure DiagHyp {Γ : Type} [Group Γ] (U V E Y : Subgroup Γ) : Prop where
  comm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u
  elem : CFSG.Assembly.IsElemAbelian 3 E
  card : Nat.card E = 27
  norm_d : E ≤ Subgroup.normalizer ((U ⊔ V : Subgroup Γ) : Set Γ)
  norm_y : E ≤ Subgroup.normalizer (Y : Set Γ)
  le : Y ≤ U ⊔ V
  perfect : Group.IsPerfect Y
  q : ∀ N : Subgroup Γ, N ≤ Y → Y ≤ Subgroup.normalizer (N : Set Γ) →
    Group.IsSolvable N ∨ N = Y
  rank : ∀ F : Subgroup Γ, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 27

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem center_eq_bot_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    Subgroup.center X = ⊥ := by
  have h := OuterAutomorphisms.center_map_equiv e
  rw [alternatingGroup.center_eq_bot (by simp)] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

noncomputable def quotCenterEquiv {X T : Type*} [Group X] [Group T]
    (hZ : Subgroup.center X = ⊥) (e : X ≃* T) : X ⧸ Subgroup.center X ≃* T :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)

theorem isPerfect_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    Group.IsPerfect X := by
  have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Sec15.Y4Core.good3_alternatingGroup_five.1.1
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isSimpleGroup_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    IsSimpleGroup X := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

theorem card_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) : Nat.card X = 60 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  rfl

theorem isTripleCover_congr {X X' S : Type*} [Group X] [Group X'] [Group S] (e : X ≃* X')
    (h : Sec4.IsTripleCover X S) : Sec4.IsTripleCover X' S := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map (e : X →* X') = Subgroup.center X' := Subgroup.map_center_eq e
  refine ⟨by rw [← hc, Subgroup.card_map_of_injective e.injective, hcard], ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e hc).symm.trans φ

theorem isQuasisimple_tripleCover {X : Type*} [Group X] (hX : Group.IsPerfect X)
    (htc : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) : IsQuasisimple X := by
  obtain ⟨-, ⟨φ⟩⟩ := htc
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨a, b, hab⟩ := Sec15.Y4Core.alternatingGroup_six_nonabelian
  refine ⟨hX, φ.isSimpleGroup, φ.symm a, φ.symm b, fun h => hab ?_⟩
  have h1 := congrArg φ h
  simpa using h1

omit [Finite Γ] in
theorem eq_one_of_center_eq_bot {W : Subgroup Γ} (hZ : Subgroup.center ↥W = ⊥) {z : Γ}
    (hz : z ∈ W) (hzc : ∀ u ∈ W, u * z = z * u) : z = 1 := by
  have h1 : (⟨z, hz⟩ : ↥W) ∈ Subgroup.center ↥W :=
    Subgroup.mem_center_iff.mpr fun u => Subtype.ext (hzc u u.2)
  rw [hZ, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

omit [Finite Γ] in
theorem mem_centerIn_of_comm {W : Subgroup Γ} {z : Γ} (hz : z ∈ W)
    (hzc : ∀ u ∈ W, u * z = z * u) : z ∈ Sec14.Item148PtRes.centerIn W :=
  Sec14.Item148PtRes.mem_centerIn_iff.mpr
    ⟨hz, Subgroup.mem_center_iff.mpr fun u => Subtype.ext (hzc u u.2)⟩

omit [Finite Γ] in
theorem isPerfect_of_commutator_eq {K : Subgroup Γ} (h : ⁅K, K⁆ = K) : Group.IsPerfect K := by
  refine ⟨Subgroup.map_injective K.subtype_injective ?_⟩
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    h]

omit [Finite Γ] in
theorem exists_zpowers_three {W : Subgroup Γ} {x : ↥W} (hx : orderOf x = 3) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (x : Γ)) ∧
      Nat.card (Subgroup.zpowers (x : Γ)) = 3 ∧ Subgroup.zpowers (x : Γ) ≤ W := by
  have hx' : orderOf (x : Γ) = 3 := by rw [Subgroup.orderOf_coe, hx]
  refine ⟨isElemAbelian_zpowers ?_, by rw [Nat.card_zpowers, hx'], ?_⟩
  · rw [← hx']
    exact pow_orderOf_eq_one _
  · rw [Subgroup.zpowers_le]
    exact x.2

omit [Finite Γ] in
theorem exists_elemAbelian_map {W : Subgroup Γ} {F : Subgroup ↥W}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    CFSG.Assembly.IsElemAbelian 3 (F.map W.subtype) ∧ Nat.card (F.map W.subtype) = Nat.card F ∧
      F.map W.subtype ≤ W :=
  ⟨CFSG.SectionRank.isElemAbelian_map hF _, Subgroup.card_map_of_injective W.subtype_injective,
    Subgroup.map_subtype_le F⟩

theorem elemAbelian_sup {U V F₁ F₂ : Subgroup Γ} (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hF₁ : CFSG.Assembly.IsElemAbelian 3 F₁) (hF₂ : CFSG.Assembly.IsElemAbelian 3 F₂)
    (h₁ : F₁ ≤ U) (h₂ : F₂ ≤ V) :
    CFSG.Assembly.IsElemAbelian 3 (F₁ ⊔ F₂) ∧
      Nat.card (F₁ ⊔ F₂ : Subgroup Γ) * Nat.card (F₁ ⊓ F₂ : Subgroup Γ) =
        Nat.card F₁ * Nat.card F₂ := by
  have hc' : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a := fun a ha b hb => hc a (h₁ ha) b (h₂ hb)
  exact ⟨Sec13.isElemAbelian_sup hF₁ hF₂ hc',
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F₁ F₂ hc').1⟩

omit [Finite Γ] in
theorem comm_of_centralizes {U V E₀ : Subgroup Γ} (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hU : E₀ ≤ Subgroup.centralizer (U : Set Γ)) (hV : E₀ ≤ Subgroup.centralizer (V : Set Γ))
    {F : Subgroup Γ} (hF : F ≤ U ⊔ V) : ∀ x ∈ E₀, ∀ y ∈ F, x * y = y * x := fun _ hx _ hy =>
  (comm_sup_of_comm hc (fun u hu => Subgroup.mem_centralizer_iff.mp (hU hx) u hu)
    (fun v hv => Subgroup.mem_centralizer_iff.mp (hV hx) v hv) (hF hy)).symm

section FiveFive

variable {U V E Y : Subgroup Γ}

theorem mem_normalizer_of_five_five (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hinf : U ⊓ V = ⊥)
    (eU : ↥U ≃* alternatingGroup (Fin 5)) (eV : ↥V ≃* alternatingGroup (Fin 5)) {e : Γ}
    (heD : e ∈ Subgroup.normalizer ((U ⊔ V : Subgroup Γ) : Set Γ)) (he3 : e ^ 3 = 1) :
    e ∈ Subgroup.normalizer (U : Set Γ) ∧ e ∈ Subgroup.normalizer (V : Set Γ) := by
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (hc u hu v hv).symm
  have hZU := center_eq_bot_five eU
  have hZV := center_eq_bot_five eV
  have hcard : Nat.card U = Nat.card V := by rw [card_five eU, card_five eV]
  have hUne : U ≠ V := by
    intro hUV
    rw [hUV, inf_idem] at hinf
    have h1 := card_five eV
    rw [hinf, Subgroup.card_bot] at h1
    norm_num at h1
  have hDV : U ⊔ V = V ⊔ U := sup_comm U V
  have key : ∀ (W W' : Subgroup Γ) (hcW : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w),
      W ⊔ W' = U ⊔ V → Subgroup.center ↥W = ⊥ → IsSimpleGroup ↥W →
      Nat.card W' ≤ Nat.card W →
      W.map (MulAut.conj e).toMonoidHom = W ∨ W.map (MulAut.conj e).toMonoidHom = W' := by
    intro W W' hcW hWW' hZW hsW hle
    have heD' : e ∈ Subgroup.normalizer ((W ⊔ W' : Subgroup Γ) : Set Γ) := hWW' ▸ heD
    rcases map_conj_eq_or_comm le_sup_left (sup_le_normalizer_of_comm hcW) hsW heD' with h | h
    · exact Or.inl h
    · right
      have hle' : W.map (MulAut.conj e).toMonoidHom ≤ W' := by
        intro a ha
        have haD : a ∈ W ⊔ W' := by
          obtain ⟨w, hw, rfl⟩ := ha
          exact (Subgroup.mem_normalizer_iff.mp heD' w).mp (Subgroup.mem_sup_left hw)
        exact mem_of_comm_of_center_eq_bot hcW hZW haD fun u hu => (h a ha u hu).symm
      refine Subgroup.eq_of_le_of_card_ge hle' ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj e).injective]
      exact hle
  have hU' := key U V hc rfl hZU (isSimpleGroup_five eU) hcard.ge
  have hV' := key V U hcV hDV.symm hZV (isSimpleGroup_five eV) hcard.le
  have hV'' : V.map (MulAut.conj e).toMonoidHom = U ∨ V.map (MulAut.conj e).toMonoidHom = V :=
    hV'.symm
  obtain ⟨h1, h2⟩ := map_eq_of_swap hUne (conj_conj_conj he3) hU' hV''
  exact ⟨mem_normalizer_of_map_eq h1, mem_normalizer_of_map_eq h2⟩

theorem le_or_le_of_five_five (h : DiagHyp U V E Y) (hinf : U ⊓ V = ⊥)
    (eU : ↥U ≃* alternatingGroup (Fin 5)) (eV : ↥V ≃* alternatingGroup (Fin 5)) :
    Y ≤ U ∨ Y ≤ V := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hYU, hYV⟩ := hcon
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (h.comm u hu v hv).symm
  have hZU := center_eq_bot_five eU
  have hZV := center_eq_bot_five eV
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (U : Set Γ) ∧
      e ∈ Subgroup.normalizer (V : Set Γ) := fun e he =>
    mem_normalizer_of_five_five h.comm hinf eU eV (h.norm_d he) (h.elem.2 e he)
  have hYD' : Y ≤ V ⊔ U := by rw [sup_comm]; exact h.le
  have hT1 : (Y.subgroupOf (V ⊔ U)).map (projQ hcV) ≠ ⊥ := fun hb =>
    hYU (le_of_map_projQ_eq_bot hcV hYD' h.perfect hb)
  have eXV := quotCenterEquiv hZV eV
  have hEU : E ⊓ Subgroup.centralizer (U : Set Γ) ≤ Subgroup.centralizer (V : Set Γ) :=
    fun e he => mem_centralizer_of_mem_centralizer hcV hYD' h.perfect h.q hYV (isPerfect_five eV)
      (fun _ _ hT hT1 hS hTS => eq_bot_of_isSolvable_five eXV hT hT1 hS hTS)
      (fun _ _ _ _ hT hT1 hσT => eq_one_of_fix_five eXV hT hT1 hσT) hT1 (h.norm_y he.1)
      (hEN e he.1).2 (hEN e he.1).1 he.2 (k := 1) (by rw [pow_one]; exact h.elem.2 e he.1)
  have hcard := card_le_mul_card_inf_centralizer (fun e he => (hEN e he).1) h.elem
    (card_le_three_of_mulAut_five' eU)
  rw [h.card] at hcard
  obtain ⟨xU, hxU⟩ := exists_orderOf_three_five eU
  obtain ⟨xV, hxV⟩ := exists_orderOf_three_five eV
  obtain ⟨hFU, hFU3, hFUU⟩ := exists_zpowers_three hxU
  obtain ⟨hFV, hFV3, hFVV⟩ := exists_zpowers_three hxV
  obtain ⟨hFab, hFcard⟩ := elemAbelian_sup h.comm hFU hFV hFUU hFVV
  have hinfF : Subgroup.zpowers (xU : Γ) ⊓ Subgroup.zpowers (xV : Γ) = ⊥ :=
    le_bot_iff.mp (hinf ▸ inf_le_inf hFUU hFVV)
  rw [hinfF, Subgroup.card_bot, mul_one, hFU3, hFV3] at hFcard
  have hFD : Subgroup.zpowers (xU : Γ) ⊔ Subgroup.zpowers (xV : Γ) ≤ U ⊔ V :=
    sup_le_sup hFUU hFVV
  have hEF : E ⊓ Subgroup.centralizer (U : Set Γ) ⊓
      (Subgroup.zpowers (xU : Γ) ⊔ Subgroup.zpowers (xV : Γ)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨z, hz, hzc, z', hz', hz'c, rfl⟩ := exists_center_mul_of_comm h.comm (hFD hx.2)
      (fun u hu => Subgroup.mem_centralizer_iff.mp hx.1.2 u hu)
      (fun v hv => Subgroup.mem_centralizer_iff.mp (hEU hx.1) v hv)
    rw [eq_one_of_center_eq_bot hZU hz hzc, eq_one_of_center_eq_bot hZV hz' hz'c, mul_one]
    exact Subgroup.one_mem _
  have hG3 := card_mul_le_of_comm h.rank (isElemAbelian_of_le h.elem inf_le_left) hFab
    (comm_of_centralizes h.comm inf_le_right hEU hFD)
  rw [hFcard, hEF, Subgroup.card_bot] at hG3
  omega

end FiveFive

section FiveJ2


variable {U V E Y : Subgroup Γ}

theorem center_eq_bot_j2 {X : Type} [Group X] (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) :
    Subgroup.center X = ⊥ := by
  have h := OuterAutomorphisms.center_map_equiv e
  rw [KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem mem_normalizer_of_five_j2 (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (eU : ↥U ≃* alternatingGroup (Fin 5)) (eV : ↥V ≃* CFSG.Blueprint.NativeSporadic.J2) {e : Γ}
    (heD : e ∈ Subgroup.normalizer ((U ⊔ V : Subgroup Γ) : Set Γ)) :
    e ∈ Subgroup.normalizer (U : Set Γ) ∧ e ∈ Subgroup.normalizer (V : Set Γ) := by
  have hZU := center_eq_bot_five eU
  have hVs : IsSimpleGroup ↥V := by
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact eV.isSimpleGroup
  have hV604800 : Nat.card V = 604800 :=
    (Nat.card_congr eV.toEquiv).trans KFacts.KS14.card_nativeJ2
  have heU : e ∈ Subgroup.normalizer (U : Set Γ) := by
    rcases map_conj_eq_or_comm le_sup_left (sup_le_normalizer_of_comm hc)
        (isSimpleGroup_five eU) heD with h | h
    · exact mem_normalizer_of_map_eq h
    · exfalso
      set Ue := U.map (MulAut.conj e).toMonoidHom with hUe
      have hUeV : Ue ≤ V := by
        intro a ha
        have haD : a ∈ U ⊔ V := by
          obtain ⟨w, hw, rfl⟩ := ha
          exact (Subgroup.mem_normalizer_iff.mp heD w).mp (Subgroup.mem_sup_left hw)
        exact mem_of_comm_of_center_eq_bot hc hZU haD fun u hu => (h a ha u hu).symm
      have hUe60 : Nat.card Ue = 60 := by
        rw [hUe, Subgroup.card_map_of_injective (MulAut.conj e).injective, card_five eU]
      have hn : (Ue.subgroupOf V).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUeV]
        exact le_sup_right.trans (le_normalizer_map_conj (sup_le_normalizer_of_comm hc) heD)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Ue.subgroupOf V) with h1 | h1
      · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hUeV] at h1
        rw [h1, Subgroup.card_bot] at hUe60
        norm_num at hUe60
      · rw [Subgroup.subgroupOf_eq_top] at h1
        have h2 := Subgroup.card_le_of_le h1
        rw [hUe60, hV604800] at h2
        norm_num at h2
  exact ⟨heU, mem_normalizer_of_partner hc hZU heD heU⟩

theorem le_or_le_of_five_j2 (h : DiagHyp U V E Y) (hinf : U ⊓ V = ⊥)
    (eU : ↥U ≃* alternatingGroup (Fin 5)) (eV : ↥V ≃* CFSG.Blueprint.NativeSporadic.J2) :
    Y ≤ U ∨ Y ≤ V := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hYU, hYV⟩ := hcon
  have hZU := center_eq_bot_five eU
  have hZV := center_eq_bot_j2 eV
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (U : Set Γ) ∧
      e ∈ Subgroup.normalizer (V : Set Γ) := fun e he =>
    mem_normalizer_of_five_j2 h.comm eU eV (h.norm_d he)
  have hT1 : (Y.subgroupOf (U ⊔ V)).map (projQ h.comm) ≠ ⊥ := fun hb =>
    hYV (le_of_map_projQ_eq_bot h.comm h.le h.perfect hb)
  have eXU := quotCenterEquiv hZU eU
  have hEV : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ Subgroup.centralizer (U : Set Γ) :=
    fun e he => mem_centralizer_of_mem_centralizer h.comm h.le h.perfect h.q hYU
      (isPerfect_five eU)
      (fun _ _ hT hT1 hS hTS => eq_bot_of_isSolvable_five eXU hT hT1 hS hTS)
      (fun _ _ _ _ hT hT1 hσT => eq_one_of_fix_five eXU hT hT1 hσT) hT1 (h.norm_y he.1)
      (hEN e he.1).1 (hEN e he.1).2 he.2 (k := 1) (by rw [pow_one]; exact h.elem.2 e he.1)
  have hcard := card_le_mul_card_inf_centralizer (fun e he => (hEN e he).2) h.elem
    (card_le_nine_of_mulAut_j2 eV)
  rw [h.card] at hcard
  obtain ⟨xU, hxU⟩ := exists_orderOf_three_five eU
  obtain ⟨hFU, hFU3, hFUU⟩ := exists_zpowers_three hxU
  obtain ⟨F₀, hF₀, hF₀9⟩ := exists_elemAbelian_nine_j2 eV
  obtain ⟨hFV, hFV9, hFVV⟩ := exists_elemAbelian_map hF₀
  obtain ⟨hFab, hFcard⟩ := elemAbelian_sup h.comm hFU hFV hFUU hFVV
  have hinfF : Subgroup.zpowers (xU : Γ) ⊓ F₀.map V.subtype = ⊥ :=
    le_bot_iff.mp (hinf ▸ inf_le_inf hFUU hFVV)
  rw [hinfF, Subgroup.card_bot, mul_one, hFU3, hFV9, hF₀9] at hFcard
  have hFD : Subgroup.zpowers (xU : Γ) ⊔ F₀.map V.subtype ≤ U ⊔ V := sup_le_sup hFUU hFVV
  have hEF : E ⊓ Subgroup.centralizer (V : Set Γ) ⊓
      (Subgroup.zpowers (xU : Γ) ⊔ F₀.map V.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨z, hz, hzc, z', hz', hz'c, rfl⟩ := exists_center_mul_of_comm h.comm (hFD hx.2)
      (fun u hu => Subgroup.mem_centralizer_iff.mp (hEV hx.1) u hu)
      (fun v hv => Subgroup.mem_centralizer_iff.mp hx.1.2 v hv)
    rw [eq_one_of_center_eq_bot hZU hz hzc, eq_one_of_center_eq_bot hZV hz' hz'c, mul_one]
    exact Subgroup.one_mem _
  have hG3 := card_mul_le_of_comm h.rank (isElemAbelian_of_le h.elem inf_le_left) hFab
    (comm_of_centralizes h.comm hEV inf_le_right hFD)
  rw [hFcard, hEF, Subgroup.card_bot] at hG3
  omega

end FiveJ2

section SixFive

variable {U V E Y : Subgroup Γ}

omit [Finite Γ] in
theorem isPerfect_of_six_five (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hinf : U ⊓ V = ⊥)
    (hD : Group.IsPerfect (U ⊔ V : Subgroup Γ)) : Group.IsPerfect U := by
  set D := U ⊔ V with hDdef
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (hc u hu v hv).symm
  have hUn : (U.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le_normalizer_of_comm hc)
  have hVn : (V.subgroupOf D).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
    rw [sup_comm]
    exact sup_le_normalizer_of_comm hcV
  have hsup' : U.subgroupOf D ⊔ V.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hinf' : U.subgroupOf D ⊓ V.subgroupOf D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : Γ) ∈ U ⊓ V := ⟨hx.1, hx.2⟩
    rw [hinf] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
  have hUp : ⁅U.subgroupOf D, U.subgroupOf D⁆ = U.subgroupOf D :=
    Y4Core.commutator_eq_self_of_inf_eq_bot hD hsup' hinf'
  have h1 := congrArg (Subgroup.map D.subtype) hUp
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le le_sup_left] at h1
  exact isPerfect_of_commutator_eq h1

theorem mem_normalizer_of_six_five (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6))) (hUp : Group.IsPerfect U)
    (eV : ↥V ≃* alternatingGroup (Fin 5)) {e : Γ}
    (heD : e ∈ Subgroup.normalizer ((U ⊔ V : Subgroup Γ) : Set Γ)) :
    e ∈ Subgroup.normalizer (U : Set Γ) ∧ e ∈ Subgroup.normalizer (V : Set Γ) := by
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (hc u hu v hv).symm
  have hZV := center_eq_bot_five eV
  have heD' : e ∈ Subgroup.normalizer ((V ⊔ U : Subgroup Γ) : Set Γ) := by
    rw [sup_comm]
    exact heD
  have hU1080 : Nat.card U = 1080 := card_tripleCover hU
  have hUq := isQuasisimple_tripleCover hUp hU
  have heV : e ∈ Subgroup.normalizer (V : Set Γ) := by
    rcases map_conj_eq_or_comm le_sup_left (sup_le_normalizer_of_comm hcV)
        (isSimpleGroup_five eV) heD' with h | h
    · exact mem_normalizer_of_map_eq h
    · exfalso
      set Ve := V.map (MulAut.conj e).toMonoidHom with hVe
      have hVeU : Ve ≤ U := by
        intro a ha
        have haD : a ∈ V ⊔ U := by
          obtain ⟨w, hw, rfl⟩ := ha
          exact (Subgroup.mem_normalizer_iff.mp heD' w).mp (Subgroup.mem_sup_left hw)
        exact mem_of_comm_of_center_eq_bot hcV hZV haD fun u hu => (h a ha u hu).symm
      have hVe60 : Nat.card Ve = 60 := by
        rw [hVe, Subgroup.card_map_of_injective (MulAut.conj e).injective, card_five eV]
      have hn : (Ve.subgroupOf U).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVeU]
        exact le_sup_right.trans (le_normalizer_map_conj (sup_le_normalizer_of_comm hcV) heD')
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hUq hn with h1 | h1
      · rw [Subgroup.subgroupOf_eq_top] at h1
        have h2 := Subgroup.card_le_of_le h1
        rw [hVe60, hU1080] at h2
        norm_num at h2
      · have h2 : Nat.card (Ve.subgroupOf U) ∣ 3 :=
          hU.1 ▸ Subgroup.card_dvd_of_le h1
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVeU).toEquiv, hVe60] at h2
        norm_num at h2
  exact ⟨mem_normalizer_of_partner hcV hZV heD' heV, heV⟩

theorem le_or_le_of_six_five (h : DiagHyp U V E Y) (hinf : U ⊓ V = ⊥)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6))) (eV : ↥V ≃* alternatingGroup (Fin 5))
    (hD : Group.IsPerfect (U ⊔ V : Subgroup Γ)) : Y ≤ U ∨ Y ≤ V := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hYU, hYV⟩ := hcon
  have hZV := center_eq_bot_five eV
  have hUp := isPerfect_of_six_five h.comm hinf hD
  obtain ⟨hZU3, ⟨eXU⟩⟩ := hU
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (U : Set Γ) ∧
      e ∈ Subgroup.normalizer (V : Set Γ) := fun e he =>
    mem_normalizer_of_six_five h.comm ⟨hZU3, ⟨eXU⟩⟩ hUp eV (h.norm_d he)
  have hT1 : (Y.subgroupOf (U ⊔ V)).map (projQ h.comm) ≠ ⊥ := fun hb =>
    hYV (le_of_map_projQ_eq_bot h.comm h.le h.perfect hb)
  have hEV : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ Subgroup.centralizer (U : Set Γ) :=
    fun e he => mem_centralizer_of_mem_centralizer h.comm h.le h.perfect h.q hYU hUp
      (fun _ _ hT hT1 hS hTS => eq_bot_of_isSolvable_six eXU hT hT1 hS hTS)
      (fun _ _ hσ _ hT hT1 hσT => eq_one_of_fix_six eXU hσ hT hT1 hσT) hT1 (h.norm_y he.1)
      (hEN e he.1).1 (hEN e he.1).2 he.2 (k := 1) (by rw [pow_one]; exact h.elem.2 e he.1)
  have hcard := card_le_mul_card_inf_centralizer (fun e he => (hEN e he).2) h.elem
    (card_le_three_of_mulAut_five' eV)
  rw [h.card] at hcard
  obtain ⟨F₀, hF₀, hF₀9⟩ := exists_elemAbelian_nine_tripleCover hUp ⟨hZU3, ⟨eXU⟩⟩
  obtain ⟨hFU, hFU9, hFUU⟩ := exists_elemAbelian_map hF₀
  obtain ⟨xV, hxV⟩ := exists_orderOf_three_five eV
  obtain ⟨hFV, hFV3, hFVV⟩ := exists_zpowers_three hxV
  obtain ⟨hFab, hFcard⟩ := elemAbelian_sup h.comm hFU hFV hFUU hFVV
  have hinfF : F₀.map U.subtype ⊓ Subgroup.zpowers (xV : Γ) = ⊥ :=
    le_bot_iff.mp (hinf ▸ inf_le_inf hFUU hFVV)
  rw [hinfF, Subgroup.card_bot, mul_one, hFU9, hF₀9, hFV3] at hFcard
  have hFD : F₀.map U.subtype ⊔ Subgroup.zpowers (xV : Γ) ≤ U ⊔ V := sup_le_sup hFUU hFVV
  have hEF : E ⊓ Subgroup.centralizer (V : Set Γ) ⊓ (F₀.map U.subtype ⊔ Subgroup.zpowers (xV : Γ))
      ≤ Sec14.Item148PtRes.centerIn U := by
    intro x hx
    obtain ⟨z, hz, hzc, z', hz', hz'c, rfl⟩ := exists_center_mul_of_comm h.comm (hFD hx.2)
      (fun u hu => Subgroup.mem_centralizer_iff.mp (hEV hx.1) u hu)
      (fun v hv => Subgroup.mem_centralizer_iff.mp hx.1.2 v hv)
    rw [eq_one_of_center_eq_bot hZV hz' hz'c, mul_one]
    exact mem_centerIn_of_comm hz hzc
  have hEF3 : Nat.card (E ⊓ Subgroup.centralizer (V : Set Γ) ⊓
      (F₀.map U.subtype ⊔ Subgroup.zpowers (xV : Γ)) : Subgroup Γ) ≤ 3 := by
    have h1 := Subgroup.card_le_of_le hEF
    rwa [Sec14.Item148PtRes.centerIn, Subgroup.card_map_of_injective U.subtype_injective,
      hZU3] at h1
  have hG3 := card_mul_le_of_comm h.rank (isElemAbelian_of_le h.elem inf_le_left) hFab
    (comm_of_centralizes h.comm hEV inf_le_right hFD)
  rw [hFcard] at hG3
  omega

end SixFive

section SixSix

variable {U V E Y : Subgroup Γ}

theorem isPerfect_of_six_six (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (h3 : Nat.card (U ⊓ V : Subgroup Γ) = 3)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6)))
    (hrank : ∀ F : Subgroup Γ, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 27) :
    Group.IsPerfect U := by
  by_contra hUp
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (hc u hu v hv).symm
  have hUV : ⁅U, V⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_of_comm hcV)
  have hZU := Sec14.Item148PtRes.inf_eq_centerIn_left hUV h3 hU.1
  obtain ⟨F₁, hF₁, hF₁9, hF₁Z⟩ := exists_elemAbelian_nine_inf_center_eq_bot hU hUp
  obtain ⟨F₂, hF₂, hF₂9⟩ := exists_elemAbelian_nine_tripleCover' hV
  obtain ⟨hFU, hFU9, hFUU⟩ := exists_elemAbelian_map hF₁
  obtain ⟨hFV, hFV9, hFVV⟩ := exists_elemAbelian_map hF₂
  have hinf : F₁.map U.subtype ⊓ F₂.map V.subtype = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : x ∈ Sec14.Item148PtRes.centerIn U := hZU ▸ inf_le_inf hFUU hFVV hx
    obtain ⟨a, ha, rfl⟩ := hx.1
    obtain ⟨_, haZ⟩ := Sec14.Item148PtRes.mem_centerIn_iff.mp hxZ
    have h1 : a ∈ F₁ ⊓ Subgroup.center ↥U := ⟨ha, haZ⟩
    rw [hF₁Z, Subgroup.mem_bot] at h1
    rw [h1]
    exact (Subgroup.mem_bot).mpr rfl
  have hG3 := card_mul_le_of_comm hrank hFU hFV fun a ha b hb => hc a (hFUU ha) b (hFVV hb)
  rw [hFU9, hF₁9, hFV9, hF₂9, hinf, Subgroup.card_bot] at hG3
  omega

theorem mem_normalizer_of_six_six (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (h3 : Nat.card (U ⊓ V : Subgroup Γ) = 3)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6)))
    (hD : Group.IsPerfect (U ⊔ V : Subgroup Γ)) {e : Γ}
    (heD : e ∈ Subgroup.normalizer ((U ⊔ V : Subgroup Γ) : Set Γ)) (he3 : e ^ 3 = 1) :
    e ∈ Subgroup.normalizer (U : Set Γ) ∧ e ∈ Subgroup.normalizer (V : Set Γ) := by
  set D := U ⊔ V with hDdef
  have := hD
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (hc u hu v hv).symm
  have hUn : (U.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le_normalizer_of_comm hc)
  have hVn : (V.subgroupOf D).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
    rw [sup_comm]
    exact sup_le_normalizer_of_comm hcV
  have hsup' : U.subgroupOf D ⊔ V.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hcomm' : ⁅U.subgroupOf D, V.subgroupOf D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (hcV y (Subgroup.mem_subgroupOf.mp hy) x (Subgroup.mem_subgroupOf.mp hx))
  have h3' : Nat.card (U.subgroupOf D ⊓ V.subgroupOf D : Subgroup ↥D) = 3 := by
    rw [← h3, ← Subgroup.card_map_of_injective D.subtype_injective,
      Subgroup.map_inf _ _ _ D.subtype_injective, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  have hTU := isTripleCover_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : U ≤ D)).symm hU
  have hTV := isTripleCover_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : V ≤ D)).symm hV
  set σ := D.normalizerMonoidHom ⟨e, heD⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have h1 : (⟨e, heD⟩ : ↥(Subgroup.normalizer (D : Set Γ))) ^ 3 = 1 := Subtype.ext he3
    rw [h1, map_one]
  obtain ⟨hσU, hσV⟩ := Sec14.Item148PtRes.map_eq_of_pow_three hsup' hcomm' h3' hTU hTV hσ3
  have key : ∀ W : Subgroup Γ, W ≤ D → (W.subgroupOf D).map σ.toMonoidHom = W.subgroupOf D →
      e ∈ Subgroup.normalizer (W : Set Γ) := by
    intro W hWD hW
    apply mem_normalizer_of_conj_mem
    intro x hx
    have h1 : σ ⟨x, hWD hx⟩ ∈ (W.subgroupOf D).map σ.toMonoidHom :=
      ⟨⟨x, hWD hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hW] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  exact ⟨key U le_sup_left hσU, key V le_sup_right hσV⟩

theorem le_or_le_of_six_six (h : DiagHyp U V E Y) (h3 : Nat.card (U ⊓ V : Subgroup Γ) = 3)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6)))
    (hD : Group.IsPerfect (U ⊔ V : Subgroup Γ))
    (hgen : Y ≤ sSup {Q : Subgroup Γ | Q ≤ Y ∧ E ≤ Subgroup.normalizer (Q : Set Γ) ∧
      ¬ 3 ∣ Nat.card Q}) : Y ≤ U ∨ Y ≤ V := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hYU, hYV⟩ := hcon
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (h.comm u hu v hv).symm
  have hUV : ⁅U, V⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_of_comm hcV)
  have hZU := Sec14.Item148PtRes.inf_eq_centerIn_left hUV h3 hU.1
  have hZV := Sec14.Item148PtRes.inf_eq_centerIn_right hUV h3 hV.1
  have hUp := isPerfect_of_six_six h.comm h3 hU hV h.rank
  have hVp := isPerfect_of_six_six hcV (by rwa [inf_comm]) hV hU h.rank
  obtain ⟨eXU⟩ := hU.2
  obtain ⟨eXV⟩ := hV.2
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (U : Set Γ) ∧
      e ∈ Subgroup.normalizer (V : Set Γ) := fun e he =>
    mem_normalizer_of_six_six h.comm h3 hU hV hD (h.norm_d he) (h.elem.2 e he)
  have hYD' : Y ≤ V ⊔ U := by rw [sup_comm]; exact h.le
  have hT1V : (Y.subgroupOf (V ⊔ U)).map (projQ hcV) ≠ ⊥ := fun hb =>
    hYU (le_of_map_projQ_eq_bot hcV hYD' h.perfect hb)
  have hK1V : ∀ T S : Subgroup (↥V ⧸ Subgroup.center ↥V), Group.IsPerfect T → T ≠ ⊥ →
      Group.IsSolvable S → T ≤ Subgroup.normalizer (S : Set (↥V ⧸ Subgroup.center ↥V)) →
        S = ⊥ := fun _ _ hT hT1 hS hTS => eq_bot_of_isSolvable_six eXV hT hT1 hS hTS
  have hEU : E ⊓ Subgroup.centralizer (U : Set Γ) ≤ Subgroup.centralizer (V : Set Γ) :=
    fun e he => mem_centralizer_of_mem_centralizer hcV hYD' h.perfect h.q hYV hVp hK1V
      (fun _ _ hσ _ hT hT1 hσT => eq_one_of_fix_six eXV hσ hT hT1 hσT) hT1V (h.norm_y he.1)
      (hEN e he.1).2 (hEN e he.1).1 he.2 (k := 1) (by rw [pow_one]; exact h.elem.2 e he.1)
  have hcard := card_le_mul_card_inf_centralizer (fun e he => (hEN e he).1) h.elem
    (card_le_nine_of_mulAut_tripleCover' hUp hU)
  rw [h.card] at hcard
  obtain ⟨F₁, hF₁, hF₁9⟩ := exists_elemAbelian_nine_tripleCover hUp hU
  obtain ⟨F₂, hF₂, hF₂9⟩ := exists_elemAbelian_nine_tripleCover hVp hV
  obtain ⟨hFU, hFU9, hFUU⟩ := exists_elemAbelian_map hF₁
  obtain ⟨hFV, hFV9, hFVV⟩ := exists_elemAbelian_map hF₂
  obtain ⟨hFab, hFcard⟩ := elemAbelian_sup h.comm hFU hFV hFUU hFVV
  rw [hFU9, hF₁9, hFV9, hF₂9] at hFcard
  have hinf3 : Nat.card (F₁.map U.subtype ⊓ F₂.map V.subtype : Subgroup Γ) ≤ 3 :=
    h3 ▸ Subgroup.card_le_of_le (inf_le_inf hFUU hFVV)
  have hF27 : 27 ≤ Nat.card (F₁.map U.subtype ⊔ F₂.map V.subtype : Subgroup Γ) := by
    have h1 := Nat.mul_le_mul_left
      (Nat.card (F₁.map U.subtype ⊔ F₂.map V.subtype : Subgroup Γ)) hinf3
    rw [hFcard] at h1
    omega
  have hFD : F₁.map U.subtype ⊔ F₂.map V.subtype ≤ U ⊔ V := sup_le_sup hFUU hFVV
  have hEF : E ⊓ Subgroup.centralizer (U : Set Γ) ⊓ (F₁.map U.subtype ⊔ F₂.map V.subtype) ≤
      U ⊓ V := by
    intro x hx
    obtain ⟨z, hz, hzc, z', hz', hz'c, rfl⟩ := exists_center_mul_of_comm h.comm (hFD hx.2)
      (fun u hu => Subgroup.mem_centralizer_iff.mp hx.1.2 u hu)
      (fun v hv => Subgroup.mem_centralizer_iff.mp (hEU hx.1) v hv)
    have h1 : z ∈ U ⊓ V := by rw [hZU]; exact mem_centerIn_of_comm hz hzc
    have h2 : z' ∈ U ⊓ V := by rw [hZV]; exact mem_centerIn_of_comm hz' hz'c
    exact (U ⊓ V).mul_mem h1 h2
  have hG3 := card_mul_le_of_comm h.rank (isElemAbelian_of_le h.elem inf_le_left) hFab
    (comm_of_centralizes h.comm inf_le_right hEU hFD)
  have hle1 : Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) ⊓
        (F₁.map U.subtype ⊔ F₂.map V.subtype) : Subgroup Γ) ≤
      Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) ⊓ (U ⊓ V) : Subgroup Γ) :=
    Subgroup.card_le_of_le (le_inf inf_le_left hEF)
  have hEUZ : E ⊓ Subgroup.centralizer (U : Set Γ) ≤ U ⊓ V := by
    have h4 := (Nat.mul_le_mul_left (Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) :
      Subgroup Γ)) hF27).trans (hG3.trans (Nat.mul_le_mul_left 27 hle1))
    have h5 : Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) ≤
        Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) ⊓ (U ⊓ V) : Subgroup Γ) := by
      omega
    rw [← Subgroup.eq_of_le_of_card_ge inf_le_left h5]
    exact inf_le_right
  have hEU3 : Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) = 3 := by
    have h1 := Subgroup.card_le_of_le hEUZ
    rw [h3] at h1
    omega
  have hEUle : E ≤ Subgroup.normalizer (U : Set Γ) := fun e he => (hEN e he).1
  set ρ := (actQ U).comp (Subgroup.inclusion hEUle) with hρ
  have hker : Nat.card ρ.ker = 3 := by
    have hk : ρ.ker.map E.subtype = E ⊓ Subgroup.centralizer (U : Set Γ) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, mem_centralizer_of_actQ_eq_one hUp hx⟩
      · rintro ⟨hgE, hgC⟩
        exact ⟨⟨g, hgE⟩, actQ_eq_one_of_mem_centralizer hgC, rfl⟩
    rw [← Subgroup.card_map_of_injective E.subtype_injective, hk, hEU3]
  have hrange : Nat.card ρ.range = 9 := by
    have h1 : Nat.card E = Nat.card ρ.range * Nat.card ρ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [h.card, hker] at h1
    omega
  have hrange3 : IsPGroup 3 ρ.range :=
    (isPGroup_of_isElemAbelian h.elem).of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hQbot : ∀ Q ∈ {Q : Subgroup Γ | Q ≤ Y ∧ E ≤ Subgroup.normalizer (Q : Set Γ) ∧
      ¬ 3 ∣ Nat.card Q}, Q = ⊥ := by
    rintro Q ⟨hQY, hEQ, hQ3⟩
    have hQD : Q ≤ U ⊔ V := hQY.trans h.le
    set Qb := (Q.subgroupOf (U ⊔ V)).map (projQ h.comm) with hQb
    have hQb3 : ¬ 3 ∣ Nat.card Qb := fun h3' => hQ3 (h3'.trans (by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv]
      exact Subgroup.card_map_dvd _ _))
    have hinv : ∀ σ ∈ ρ.range, ∀ q ∈ Qb, σ q ∈ Qb := by
      rintro _ ⟨e, rfl⟩ _ ⟨q, hq, rfl⟩
      have hq' : (q : Γ) ∈ Q := Subgroup.mem_subgroupOf.mp hq
      have heq : (e : Γ) * q * (e : Γ)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hEQ e.2) q).mp hq'
      have heqD : (e : Γ) * q * (e : Γ)⁻¹ ∈ U ⊔ V := hQD heq
      have h1 := projQ_conj h.comm (hEN e e.2).1 (hEN e e.2).2 q heqD
      have hρe : ρ e = actQ U ⟨e, (hEN e e.2).1⟩ := rfl
      rw [hρe, ← h1]
      exact ⟨⟨_, heqD⟩, Subgroup.mem_subgroupOf.mpr heq, rfl⟩
    have hQbb := eq_bot_of_le_mulAut_six eXU hrange3 hrange hQb3 hinv
    have hQV : Q ≤ V := by
      intro q hq
      have h1 : projQ h.comm ⟨q, hQD hq⟩ = 1 := by
        have h2 : projQ h.comm ⟨q, hQD hq⟩ ∈ Qb :=
          ⟨⟨q, hQD hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
        rwa [hQbb, Subgroup.mem_bot] at h2
      obtain ⟨z, hz, hzc, v, hv, hqz⟩ := exists_of_projQ_eq_one h.comm h1
      have hzV : z ∈ U ⊓ V := by rw [hZU]; exact mem_centerIn_of_comm hz hzc
      have hqz' : q = z * v := hqz
      rw [hqz']
      exact V.mul_mem hzV.2 hv
    have hQZ : Q ≤ U ⊓ V := by
      intro q hq
      have hqYV : q ∈ Y ⊓ V := ⟨hQY hq, hQV hq⟩
      rw [hZV]
      exact mem_centerIn_of_comm (hQV hq) fun u hu =>
        inf_le_center hcV hYD' h.perfect h.q hYV hK1V hT1V hqYV hu
    have h1 : Nat.card Q ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le hQZ
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
    · exact Subgroup.card_eq_one.mp h2
    · exact absurd (by rw [h2] : 3 ∣ Nat.card Q) hQ3
  have hYb : Y = ⊥ := by
    rw [eq_bot_iff]
    refine hgen.trans (sSup_le fun Q hQ => ?_)
    rw [hQbot Q hQ]
  exact hYU (hYb ▸ bot_le)

end SixSix

end CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag
