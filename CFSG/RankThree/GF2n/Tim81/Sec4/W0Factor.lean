module

public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjH
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.RankThree.GF2n.Tim81.Sec4.KElem

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement
open CFSG.QuasithinUnique.C5

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

private theorem xOf_commute (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {x y : G}
    (hx : x ∈ Tim79a.xOf V H) (hy : y ∈ Tim79a.xOf V H) : x * y = y * x :=
  congrArg Subtype.val ((isElemAbelian_xOf h hPH hVH).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem commutator_W0_Pc_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) :
    ⁅W₀, Pc M V⁆ ≤ Pc M V ⊓ W₀ := by
  have hW₀_le_K : W₀ ≤ kOf V H := hW₀.trans (xOf_le_kOf h hPH hVH)
  have hW₀_le_NP : W₀ ≤ Subgroup.normalizer (Pc M V : Set G) :=
    (hW₀_le_K.trans (kOf_le_M h)).trans h.toHyp.le_normalizer_Pc
  have hP_le_NW₀ : Pc M V ≤ Subgroup.normalizer (W₀ : Set G) := hPH.trans hN
  refine le_inf ?_ ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_right
      (H := W₀) (K := Pc M V)).mp hW₀_le_NP
  · exact (Subgroup.le_normalizer_iff_commutator_le_left
      (H := Pc M V) (K := W₀)).mp hP_le_NW₀

private theorem commutator_W0_conj_Pc_le_of_mem (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {y : G} (hy : y ∈ H) :
    ⁅W₀, conjSubgroup y (Pc M V)⁆ ≤ conjSubgroup y (Pc M V) ⊓ W₀ := by
  have hW₀_le_K : W₀ ≤ kOf V H := hW₀.trans (xOf_le_kOf h hPH hVH)
  have hW₀_le_NPy : W₀ ≤ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) :=
    hW₀_le_K.trans (kOf_le_normalizer_conjSubgroup_Pc_of_mem h hy)
  have hPy_le_NW₀ : conjSubgroup y (Pc M V) ≤ Subgroup.normalizer (W₀ : Set G) :=
    (conjSubgroup_le_of_le_of_mem hPH hy).trans hN
  refine le_inf ?_ ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_right
      (H := W₀) (K := conjSubgroup y (Pc M V))).mp hW₀_le_NPy
  · exact (Subgroup.le_normalizer_iff_commutator_le_left
      (H := conjSubgroup y (Pc M V)) (K := W₀)).mp hPy_le_NW₀

private theorem sup_inf_Pc_conj_ne_bot_of_mem (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥) :
    (Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) ≠ ⊥ := by
  intro hEbot
  set A : Subgroup G := Pc M V ⊓ W₀ with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ W₀ with hB
  have hEbot' : A ⊔ B = ⊥ := hEbot
  have hA_bot : A = ⊥ := le_bot_iff.mp (le_sup_left.trans_eq hEbot')
  have hB_bot : B = ⊥ := le_bot_iff.mp (le_sup_right.trans_eq hEbot')
  have hP_bot : ⁅W₀, Pc M V⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (commutator_W0_Pc_le h hPH hVH hW₀ hN).trans_eq hA_bot
  have hPy_bot : ⁅W₀, conjSubgroup y (Pc M V)⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (commutator_W0_conj_Pc_le_of_mem h hPH hVH hW₀ hN hyH).trans_eq hB_bot
  have hW₀_le_V : W₀ ≤ V := by
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hP_bot
    rwa [h.toHyp.centralizer_Pc] at hle
  have hW₀_le_Vy : W₀ ≤ conjSubgroup y V := by
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPy_bot
    rwa [h.toHyp.centralizer_conj_Pc y] at hle
  have hVinfPy : V ⊓ conjSubgroup y (Pc M V) = ⊥ :=
    inf_conj_Pc_eq_bot h hHy hnM
  have hle : W₀ ≤ V ⊓ conjSubgroup y (Pc M V) :=
    le_inf hW₀_le_V
      (hW₀_le_Vy.trans (Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom)
        h.toHyp.le_Pc))
  rw [hVinfPy] at hle
  exact hW₀ne (le_bot_iff.mp hle)

private theorem Pc_conj_mem_sup_inf_Pc_conj_of_mem (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) :
    ∀ p ∈ Pc M V, ∀ e ∈
      ((Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) : Subgroup G),
      p * e * p⁻¹ ∈ (Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) := by
  set A : Subgroup G := Pc M V ⊓ W₀ with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ W₀ with hB
  set E : Subgroup G := A ⊔ B with hE
  have hE_le : E ≤ W₀ := sup_le inf_le_right inf_le_right
  have hPW : ⁅Pc M V, W₀⁆ ≤ A := by
    rw [Subgroup.commutator_comm]
    exact commutator_W0_Pc_le h hPH hVH hW₀ hN
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    refine le_normalizer_of_comm ?_
    intro b hb a ha
    exact xOf_commute h hPH hVH (hW₀ (hE_le ((le_sup_right : B ≤ A ⊔ B) hb)))
      (hW₀ (hE_le ((le_sup_left : A ≤ A ⊔ B) ha)))
  intro p hp e he
  have he' : e ∈ A ⊔ B := by rwa [hE] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hBA he'
  have haW : a ∈ W₀ := (inf_le_right : Pc M V ⊓ W₀ ≤ W₀) (by simpa [hA] using ha)
  have hbW : b ∈ W₀ :=
    (inf_le_right : conjSubgroup y (Pc M V) ⊓ W₀ ≤ W₀) (by simpa [hB] using hb)
  have hpa : p * a * p⁻¹ ∈ A := by
    have hmem : ⁅p, a⁆ ∈ A :=
      hPW (Subgroup.commutator_mem_commutator hp haW)
    have heq : p * a * p⁻¹ = ⁅p, a⁆ * a := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact A.mul_mem hmem ha
  have hpb : p * b * p⁻¹ ∈ E := by
    have hmem : ⁅p, b⁆ ∈ A :=
      hPW (Subgroup.commutator_mem_commutator hp hbW)
    have heq : p * b * p⁻¹ = ⁅p, b⁆ * b := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact E.mul_mem ((le_sup_left : A ≤ A ⊔ B) hmem)
      ((le_sup_right : B ≤ A ⊔ B) hb)
  have hconj : p * (a * b) * p⁻¹ = (p * a * p⁻¹) * (p * b * p⁻¹) := by group
  rw [hconj]
  exact E.mul_mem ((le_sup_left : A ≤ A ⊔ B) hpa) hpb

private theorem conj_Pc_conj_mem_sup_inf_Pc_conj_of_mem (h : RootHyp M V)
    (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) :
    ∀ p ∈ conjSubgroup y (Pc M V), ∀ e ∈
      ((Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) : Subgroup G),
      p * e * p⁻¹ ∈ (Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) := by
  set A : Subgroup G := Pc M V ⊓ W₀ with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ W₀ with hB
  set E : Subgroup G := A ⊔ B with hE
  have hE_le : E ≤ W₀ := sup_le inf_le_right inf_le_right
  have hPyW : ⁅conjSubgroup y (Pc M V), W₀⁆ ≤ B := by
    rw [Subgroup.commutator_comm]
    exact commutator_W0_conj_Pc_le_of_mem h hPH hVH hW₀ hN hyH
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    refine le_normalizer_of_comm ?_
    intro b hb a ha
    exact xOf_commute h hPH hVH (hW₀ (hE_le ((le_sup_right : B ≤ A ⊔ B) hb)))
      (hW₀ (hE_le ((le_sup_left : A ≤ A ⊔ B) ha)))
  intro p hp e he
  have he' : e ∈ A ⊔ B := by rwa [hE] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hBA he'
  have haW : a ∈ W₀ := (inf_le_right : Pc M V ⊓ W₀ ≤ W₀) (by simpa [hA] using ha)
  have hbW : b ∈ W₀ :=
    (inf_le_right : conjSubgroup y (Pc M V) ⊓ W₀ ≤ W₀) (by simpa [hB] using hb)
  have hpa : p * a * p⁻¹ ∈ E := by
    have hmem : ⁅p, a⁆ ∈ B :=
      hPyW (Subgroup.commutator_mem_commutator hp haW)
    have heq : p * a * p⁻¹ = ⁅p, a⁆ * a := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact E.mul_mem ((le_sup_right : B ≤ A ⊔ B) hmem)
      ((le_sup_left : A ≤ A ⊔ B) ha)
  have hpb : p * b * p⁻¹ ∈ B := by
    have hmem : ⁅p, b⁆ ∈ B :=
      hPyW (Subgroup.commutator_mem_commutator hp hbW)
    have heq : p * b * p⁻¹ = ⁅p, b⁆ * b := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact B.mul_mem hmem hb
  have hconj : p * (a * b) * p⁻¹ = (p * a * p⁻¹) * (p * b * p⁻¹) := by group
  rw [hconj]
  exact E.mul_mem hpa ((le_sup_right : B ≤ A ⊔ B) hpb)

theorem le_normalizer_sup_inf_Pc_conj_of_mem (h : RootHyp M V)
    (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) :
    H ≤ Subgroup.normalizer
      (((Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) : Subgroup G) : Set G) := by
  set E : Subgroup G := (Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) with hE
  have hP_conj_mem := Pc_conj_mem_sup_inf_Pc_conj_of_mem (y := y) h hPH hVH hW₀ hN
  have hPy_conj_mem := conj_Pc_conj_mem_sup_inf_Pc_conj_of_mem h hPH hVH hyH hW₀ hN
  have hP_norm_E : Pc M V ≤ Subgroup.normalizer (E : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact hP_conj_mem p hp e he
    · intro he
      have h := hP_conj_mem p⁻¹ ((Pc M V).inv_mem hp) (p * e * p⁻¹) he
      have h1 : p⁻¹ * (p * e * p⁻¹) * p⁻¹⁻¹ = e := by group
      rwa [h1] at h
  have hPy_norm_E : conjSubgroup y (Pc M V) ≤ Subgroup.normalizer (E : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact hPy_conj_mem p hp e he
    · intro he
      have h := hPy_conj_mem p⁻¹ ((conjSubgroup y (Pc M V)).inv_mem hp)
        (p * e * p⁻¹) he
      have h1 : p⁻¹ * (p * e * p⁻¹) * p⁻¹⁻¹ = e := by group
      rwa [h1] at h
  rw [hHy]
  exact sup_le hP_norm_E hPy_norm_E

theorem eq_sup_inf_of_minimal (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    W₀ = (Pc M V ⊓ W₀) ⊔ (conjSubgroup h₀ (Pc M V) ⊓ W₀) := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hE_ne : (Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) ≠ ⊥ :=
    sup_inf_Pc_conj_ne_bot_of_mem h hPH hVH hyH hHy hnM hW₀ hN hW₀ne
  have hE_norm : H ≤ Subgroup.normalizer
      (((Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) : Subgroup G) : Set G) :=
    le_normalizer_sup_inf_Pc_conj_of_mem h hPH hVH hyH hHy hW₀ hN
  have hE_le : (Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) ≤ W₀ :=
    sup_le inf_le_right inf_le_right
  have hE_eq : (Pc M V ⊓ W₀) ⊔ (conjSubgroup y (Pc M V) ⊓ W₀) = W₀ :=
    hmin _ hE_le hE_ne hE_norm
  rw [hPy]
  exact hE_eq.symm

theorem sup_inf_V_W0_ne_of_ne_bot (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    (V ⊓ W₀) ⊔ (conjSubgroup h₀ V ⊓ W₀) ≠ W₀ := by
  intro hEq
  obtain ⟨y, hyH, -, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  rw [hVy] at hEq
  set X : Subgroup G := conjSubgroup y V ⊓ W₀ with hX
  have hX_le_W₀ : X ≤ W₀ := inf_le_right
  have hX_le_Vy : X ≤ conjSubgroup y V := inf_le_left
  have hX_le_K : X ≤ kOf V H :=
    hX_le_Vy.trans (conjSubgroup_le_kOf_of_mem h hPH hVH hyH)
  have hX_le_M : X ≤ M := hX_le_K.trans (kOf_le_M h)
  have hK_le_CV : kOf V H ≤ Subgroup.centralizer (V : Set G) := by
    have h := kOf_le_centralizer_conjSubgroup_of_mem (V := V) (H := H) (y := 1) H.one_mem
    rwa [conjSubgroup_one] at h
  have hX_le_CV : X ≤ Subgroup.centralizer (V : Set G) := hX_le_K.trans hK_le_CV
  have hA₀_le_P : V ⊓ W₀ ≤ Pc M V := inf_le_left.trans h.toHyp.le_Pc
  have hPVy_bot : conjSubgroup y V ⊓ Pc M V = ⊥ :=
    conjSubgroup_inf_Pc_eq_bot h hHy hnM
  have hPX_bot : Pc M V ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ conjSubgroup y V ⊓ Pc M V :=
      Subgroup.mem_inf.mpr ⟨hX_le_Vy hx.2, hx.1⟩
    rwa [hPVy_bot] at hmem
  have hPinfW₀_eq : Pc M V ⊓ W₀ = V ⊓ W₀ := by
    refine le_antisymm ?_ ?_
    · intro p hp
      have hX_le_N : X ≤ Subgroup.normalizer ((V ⊓ W₀ : Subgroup G) : Set G) := by
        refine le_normalizer_of_comm ?_
        intro x hx a ha
        exact xOf_commute h hPH hVH (hW₀ (hX_le_W₀ hx)) (hW₀ ((inf_le_right : V ⊓ W₀ ≤ W₀) ha))
      have hpW : p ∈ W₀ := hp.2
      have hmem : p ∈ (V ⊓ W₀) ⊔ X := by
        rw [← hEq] at hpW
        exact hpW
      obtain ⟨a, ha, x, hx, rfl⟩ := exists_mul_of_mem_sup hX_le_N hmem
      have hxP : x ∈ Pc M V := by
        have haP : a ∈ Pc M V := h.toHyp.le_Pc ha.1
        have h := (Pc M V).mul_mem ((Pc M V).inv_mem haP) hp.1
        simpa using h
      have hxbot : x = 1 := by
        have hmem : x ∈ Pc M V ⊓ conjSubgroup y V := Subgroup.mem_inf.mpr ⟨hxP, hx.1⟩
        rwa [inf_comm, hPVy_bot] at hmem
      simpa [hxbot] using ha
    · exact le_inf (inf_le_left.trans h.toHyp.le_Pc) inf_le_right
  have hPX_le_V : ⁅Pc M V, X⁆ ≤ V := by
    have hPW : ⁅Pc M V, W₀⁆ ≤ Pc M V ⊓ W₀ := by
      rw [Subgroup.commutator_comm]
      exact commutator_W0_Pc_le h hPH hVH hW₀ hN
    have hle := (Subgroup.commutator_mono (le_refl (Pc M V)) hX_le_W₀).trans hPW
    rw [hPinfW₀_eq] at hle
    exact hle.trans inf_le_left
  have hX_Q : X ≤ inSubgroup (pCore 2) M :=
    h.toHyp.le_pCore_of_commutator_le hX_le_M hX_le_CV hPX_le_V
  have hX_le_P : X ≤ Pc M V := le_inf hX_Q hX_le_CV
  have hX_bot : X = ⊥ := by
    rw [eq_bot_iff]
    have hle : X ≤ Pc M V ⊓ conjSubgroup y V := le_inf hX_le_P hX_le_Vy
    rwa [inf_comm, hPVy_bot] at hle
  have hW₀_le_V : W₀ ≤ V := by
    rw [← hEq, hX_bot, sup_bot_eq]
    exact inf_le_left
  have hW₀_conj : conjSubgroup y W₀ = W₀ := conjSubgroup_eq_self_iff.mpr (hN hyH)
  have hW₀_le_Vy : W₀ ≤ conjSubgroup y V := by
    calc W₀ = conjSubgroup y W₀ := hW₀_conj.symm
      _ ≤ conjSubgroup y V := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hW₀_le_V
  have hW₀_bot : W₀ = ⊥ := by
    rw [eq_bot_iff]
    have hle : W₀ ≤ V ⊓ conjSubgroup y (Pc M V) :=
      le_inf hW₀_le_V (hW₀_le_Vy.trans (Subgroup.map_mono
        (f := (MulAut.conj y).toMonoidHom) h.toHyp.le_Pc))
    rwa [inf_conj_Pc_eq_bot h hHy hnM] at hle
  exact hW₀ne hW₀_bot

theorem card_conjSubgroup_inf_W0 (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) {W₀ : Subgroup G}
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) :
    Nat.card ↥(conjSubgroup h₀ (Pc M V) ⊓ W₀) = Nat.card ↥(Pc M V ⊓ W₀) := by
  obtain ⟨y, hyH, hPy, -, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hW₀_conj : conjSubgroup y W₀ = W₀ := conjSubgroup_eq_self_iff.mpr (hN hyH)
  calc Nat.card ↥(conjSubgroup h₀ (Pc M V) ⊓ W₀)
      = Nat.card ↥(conjSubgroup y (Pc M V) ⊓ W₀) := by rw [hPy]
    _ = Nat.card ↥(conjSubgroup y (Pc M V) ⊓ conjSubgroup y W₀) := by rw [hW₀_conj]
    _ = Nat.card ↥(conjSubgroup y (Pc M V ⊓ W₀)) := by
        rw [show conjSubgroup y (Pc M V ⊓ W₀) =
          conjSubgroup y (Pc M V) ⊓ conjSubgroup y W₀ from
          conjSubgroup_inf y (Pc M V) W₀]
    _ = Nat.card ↥(Pc M V ⊓ W₀) := card_conjSubgroup y (Pc M V ⊓ W₀)

theorem card_W0_mul_card_Pc_inf_conj_inf_W0 (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    Nat.card W₀ * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) =
      Nat.card ↥(Pc M V ⊓ W₀) ^ 2 := by
  set A : Subgroup G := Pc M V ⊓ W₀ with hA
  set B : Subgroup G := conjSubgroup h₀ (Pc M V) ⊓ W₀ with hB
  have hW₀_sup : W₀ = A ⊔ B := by
    rw [hA, hB]
    exact eq_sup_inf_of_minimal h hPH hVH hH hnM hW₀ hN hW₀ne hmin
  have hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    rw [hA] at hx
    rw [hB] at hy
    exact xOf_commute h hPH hVH (hW₀ ((inf_le_right : Pc M V ⊓ W₀ ≤ W₀) hx))
        (hW₀ ((inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ W₀ ≤ W₀) hy))
  have hprod := card_sup_mul_card_inf_of_le_normalizer
    (A := A) (B := B) (le_normalizer_of_comm hcomm)
  have hcard : Nat.card B = Nat.card A := by
    rw [hA, hB]
    exact card_conjSubgroup_inf_W0 h hPH hH hN
  have hAB : A ⊓ B = Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀ := by
    rw [hA, hB]
    ac_rfl
  have hmain : Nat.card W₀ * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀) =
      Nat.card A * Nat.card B := by
    rw [← hW₀_sup, hAB] at hprod
    exact hprod
  calc Nat.card W₀ * Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀)
      = Nat.card A * Nat.card B := hmain
    _ = Nat.card A * Nat.card A := by rw [hcard]
    _ = Nat.card ↥(Pc M V ⊓ W₀) ^ 2 := by rw [hA, pow_two]

theorem card_W0_le_sq (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    Nat.card W₀ ≤ Nat.card ↥(Pc M V ⊓ W₀) ^ 2 := by
  have h := card_W0_mul_card_Pc_inf_conj_inf_W0 h hPH hVH hH hnM hW₀ hN hW₀ne hmin
  exact Nat.le_of_dvd (pow_pos Nat.card_pos 2)
    ⟨Nat.card ↥(Pc M V ⊓ conjSubgroup h₀ (Pc M V) ⊓ W₀), h.symm⟩

theorem card_Pc_inf_W0_mul_card_V_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) :
    Nat.card ↥(Pc M V ⊓ W₀) * Nat.card V ≤
      Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀) := by
  set A : Subgroup G := Pc M V ⊓ W₀ with hA
  have hW₀_le_K : W₀ ≤ kOf V H := hW₀.trans (xOf_le_kOf h hPH hVH)
  have hA_le_P : A ≤ Pc M V := by rw [hA]; exact inf_le_left
  have hA_le_K : A ≤ kOf V H := by
    rw [hA]
    exact inf_le_right.trans hW₀_le_K
  have hcomm : ∀ x ∈ A, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    rw [hA] at hx
    exact xOf_commute h hPH hVH (hW₀ ((inf_le_right : Pc M V ⊓ W₀ ≤ W₀) hx))
        (le_xOf_self V H hy)
  have hprod := card_sup_mul_card_inf_of_le_normalizer
    (A := A) (B := V) (le_normalizer_of_comm hcomm)
  have hPV : Pc M V ⊓ V = V := by
    rw [inf_comm, inf_eq_left.mpr h.toHyp.le_Pc]
  have hAV : A ⊓ V = V ⊓ W₀ := by
    rw [hA]
    calc (Pc M V ⊓ W₀) ⊓ V = W₀ ⊓ (Pc M V ⊓ V) := by ac_rfl
      _ = W₀ ⊓ V := by rw [hPV]
      _ = V ⊓ W₀ := inf_comm _ _
  have hAV_le_PK : A ⊔ V ≤ Pc M V ⊓ kOf V H := by
    refine sup_le (le_inf hA_le_P hA_le_K) (le_inf h.toHyp.le_Pc (le_kOf h hPH hVH))
  have hcard_le : Nat.card ↥(A ⊔ V) ≤ Nat.card ↥(Pc M V ⊓ kOf V H) :=
    Nat.card_le_card_of_injective
      (fun x : ↥(A ⊔ V) => (⟨x.1, hAV_le_PK x.2⟩ : ↥(Pc M V ⊓ kOf V H)))
      (fun x y hxy => Subtype.ext
        (congrArg (fun z : ↥(Pc M V ⊓ kOf V H) => (z : G)) hxy))
  calc Nat.card A * Nat.card V
      = Nat.card ↥(A ⊔ V) * Nat.card ↥(A ⊓ V) := hprod.symm
    _ = Nat.card ↥(A ⊔ V) * Nat.card ↥(V ⊓ W₀) := by rw [hAV]
    _ ≤ Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀) :=
        Nat.mul_le_mul_right _ hcard_le

theorem card_Pc_inf_W0_mul_card_V_eq_iff (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) :
    Nat.card ↥(Pc M V ⊓ W₀) * Nat.card V =
        Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀) ↔
      Pc M V ⊓ kOf V H = (Pc M V ⊓ W₀) ⊔ V := by
  set A : Subgroup G := Pc M V ⊓ W₀ with hA
  have hW₀_le_K : W₀ ≤ kOf V H := hW₀.trans (xOf_le_kOf h hPH hVH)
  have hA_le_P : A ≤ Pc M V := by rw [hA]; exact inf_le_left
  have hA_le_K : A ≤ kOf V H := by
    rw [hA]
    exact inf_le_right.trans hW₀_le_K
  have hcomm : ∀ x ∈ A, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    rw [hA] at hx
    exact xOf_commute h hPH hVH (hW₀ ((inf_le_right : Pc M V ⊓ W₀ ≤ W₀) hx))
        (le_xOf_self V H hy)
  have hprod := card_sup_mul_card_inf_of_le_normalizer
    (A := A) (B := V) (le_normalizer_of_comm hcomm)
  have hPV : Pc M V ⊓ V = V := by
    rw [inf_comm, inf_eq_left.mpr h.toHyp.le_Pc]
  have hAV : A ⊓ V = V ⊓ W₀ := by
    rw [hA]
    calc (Pc M V ⊓ W₀) ⊓ V = W₀ ⊓ (Pc M V ⊓ V) := by ac_rfl
      _ = W₀ ⊓ V := by rw [hPV]
      _ = V ⊓ W₀ := inf_comm _ _
  have hAV_le_PK : A ⊔ V ≤ Pc M V ⊓ kOf V H := by
    refine sup_le (le_inf hA_le_P hA_le_K) (le_inf h.toHyp.le_Pc (le_kOf h hPH hVH))
  constructor
  · intro hcard
    have hcancel : Nat.card ↥(A ⊔ V) = Nat.card ↥(Pc M V ⊓ kOf V H) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(V ⊓ W₀)))
      calc Nat.card ↥(A ⊔ V) * Nat.card ↥(V ⊓ W₀)
          = Nat.card ↥(A ⊔ V) * Nat.card ↥(A ⊓ V) := by rw [hAV]
        _ = Nat.card A * Nat.card V := hprod
        _ = Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀) := hcard
    exact (Subgroup.eq_of_le_of_card_ge (H := A ⊔ V) (K := Pc M V ⊓ kOf V H)
      hAV_le_PK (le_of_eq hcancel.symm)).symm
  · intro hsub
    calc Nat.card A * Nat.card V
        = Nat.card ↥(A ⊔ V) * Nat.card ↥(A ⊓ V) := hprod.symm
      _ = Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card ↥(V ⊓ W₀) := by
          rw [← hsub, hAV]

end RootHyp

end CFSG.RankThree.GF2n.Tim81
