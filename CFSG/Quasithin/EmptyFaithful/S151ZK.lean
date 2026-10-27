module

public import CFSG.Quasithin.Background.FLcAbs
public import CFSG.Quasithin.Background.FLcAut
public import CFSG.Quasithin.Background.FLcSL

public section

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A]

structure SurjBorel (n : ℕ) (L B : Subgroup A) where
  e : ↥L →* SLt n
  surj : Function.Surjective e
  le_L : B ≤ L
  ker_le : e.ker ≤ B.subgroupOf L
  hB : (B.subgroupOf L).map e = Ut n

namespace SurjBorel

variable {n : ℕ} {L B : Subgroup A} (D : SurjBorel n L B)

@[expose] def model (P : Subgroup A) : Subgroup (SLt n) := (P.subgroupOf L).map D.e

@[expose] def cutsOf (P : Subgroup A) : Set ℕ := cuts (D.model P)

theorem mem_model {P : Subgroup A} (hBP : B ≤ P) (x : ↥L) : D.e x ∈ D.model P ↔ (x : A) ∈ P := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hker : y⁻¹ * x ∈ D.e.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hBx : ((y⁻¹ * x : ↥L) : A) ∈ B := D.ker_le hker
    have hPy : (y : A) ∈ P := hy
    have hxe : (x : A) = (y : A) * ((y⁻¹ * x : ↥L) : A) := by simp
    rw [hxe]
    exact P.mul_mem hPy (hBP hBx)
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem model_B : D.model B = Ut n := D.hB

theorem Ut_le_model {P : Subgroup A} (hBP : B ≤ P) : Ut n ≤ D.model P := by
  rw [← D.model_B]
  exact Subgroup.map_mono fun x hx => hBP hx

theorem model_le_iff {P P' : Subgroup A} (hBP : B ≤ P) (hBP' : B ≤ P') (hPL : P ≤ L) :
    D.model P ≤ D.model P' ↔ P ≤ P' := by
  constructor
  · intro h x hx
    have h1 : D.e ⟨x, hPL hx⟩ ∈ D.model P := (D.mem_model hBP _).2 hx
    exact (D.mem_model hBP' _).1 (h h1)
  · intro h
    exact Subgroup.map_mono fun x hx => h hx

theorem model_L : D.model L = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := D.surj g
  exact ⟨x, x.2, rfl⟩

theorem cutsOf_B : D.cutsOf B = {i | IsNode n i} := by
  rw [cutsOf, D.model_B, cuts_Ut]

theorem cutsOf_L : D.cutsOf L = ∅ := by
  rw [cutsOf, D.model_L]
  ext i
  constructor
  · rintro ⟨hi, hin, hnot⟩
    exact absurd (Subgroup.mem_top _) hnot
  · intro h
    exact absurd h (Set.notMem_empty i)

theorem isNode_of_mem_cutsOf {P : Subgroup A} {i : ℕ} (h : i ∈ D.cutsOf P) : IsNode n i :=
  isNode_of_mem_cuts h

theorem cutsOf_le_iff {P P' : Subgroup A} (hBP : B ≤ P) (hPL : P ≤ L) (hBP' : B ≤ P') :
    P ≤ P' ↔ D.cutsOf P' ⊆ D.cutsOf P := by
  rw [← D.model_le_iff hBP hBP' hPL]
  exact le_iff_cuts (D.Ut_le_model hBP) (D.Ut_le_model hBP')

theorem eq_of_cutsOf_eq {P P' : Subgroup A} (hBP : B ≤ P) (hPL : P ≤ L) (hBP' : B ≤ P')
    (hP'L : P' ≤ L) (h : D.cutsOf P = D.cutsOf P') : P = P' :=
  le_antisymm ((D.cutsOf_le_iff hBP hPL hBP').2 h.ge) ((D.cutsOf_le_iff hBP' hP'L hBP).2 h.le)

theorem exists_cutsOf_eq {I : Set ℕ} (hI : ∀ i ∈ I, IsNode n i) :
    ∃ P : Subgroup A, B ≤ P ∧ P ≤ L ∧ D.cutsOf P = I := by
  let K : Subgroup ↥L := (QI n I).comap D.e
  let P : Subgroup A := K.map L.subtype
  have hmemP : ∀ x : ↥L, (x : A) ∈ P ↔ D.e x ∈ QI n I := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hBP : B ≤ P := by
    intro b hb
    have hbL : b ∈ L := D.le_L hb
    have h1 : D.e ⟨b, hbL⟩ ∈ D.model B := ⟨⟨b, hbL⟩, hb, rfl⟩
    rw [D.model_B] at h1
    exact (hmemP ⟨b, hbL⟩).2 (Ut_le_QI n I h1)
  have hmodel : D.model P = QI n I := by
    ext g
    obtain ⟨x, rfl⟩ := D.surj g
    rw [D.mem_model hBP, hmemP]
  refine ⟨P, hBP, Subgroup.map_subtype_le _, ?_⟩
  rw [cutsOf, hmodel]
  exact cuts_QI hI

theorem isMax_of_cuts_insert {P K : Subgroup A} (hBP : B ≤ P) (hPL : P ≤ L) (hBK : B ≤ K)
    (hKL : K ≤ L) {x : ℕ} (hx : x ∉ D.cutsOf P) (hK : D.cutsOf K = insert x (D.cutsOf P)) :
    IsMaxSubgroupIn P K := by
  have hKP : K ≤ P :=
    (D.cutsOf_le_iff hBK hKL hBP).2 (by rw [hK]; exact Set.subset_insert _ _)
  have hxK : x ∈ D.cutsOf K := by rw [hK]; exact Set.mem_insert _ _
  have hne : K ≠ P := by
    intro he
    rw [he] at hxK
    exact hx hxK
  refine ⟨lt_of_le_of_ne hKP hne, fun K' hKK' hK'P => ?_⟩
  have hBK' : B ≤ K' := hBK.trans hKK'.le
  have hK'L : K' ≤ L := hK'P.trans hPL
  have h1 : D.cutsOf P ⊆ D.cutsOf K' := (D.cutsOf_le_iff hBK' hK'L hBP).1 hK'P
  have h2 : D.cutsOf K' ⊆ D.cutsOf K := (D.cutsOf_le_iff hBK hKL hBK').1 hKK'.le
  have hxK' : x ∉ D.cutsOf K' := by
    intro hxK'
    have h3 : D.cutsOf K ⊆ D.cutsOf K' := by
      rw [hK]
      exact Set.insert_subset hxK' h1
    exact hKK'.ne (D.eq_of_cutsOf_eq hBK hKL hBK' hK'L (Set.Subset.antisymm h3 h2))
  refine D.eq_of_cutsOf_eq hBK' hK'L hBP hPL (Set.Subset.antisymm (fun i hi => ?_) h1)
  have := h2 hi
  rw [hK] at this
  rcases this with rfl | h
  · exact absurd hi hxK'
  · exact h

theorem cutsOf_sup {P P' : Subgroup A} (hBP : B ≤ P) (hPL : P ≤ L) (hBP' : B ≤ P') (hP'L : P' ≤ L) :
    D.cutsOf (P ⊔ P') = D.cutsOf P ∩ D.cutsOf P' := by
  have hBS : B ≤ P ⊔ P' := hBP.trans le_sup_left
  have hSL : P ⊔ P' ≤ L := sup_le hPL hP'L
  apply Set.Subset.antisymm
  · exact Set.subset_inter ((D.cutsOf_le_iff hBP hPL hBS).1 le_sup_left)
      ((D.cutsOf_le_iff hBP' hP'L hBS).1 le_sup_right)
  · obtain ⟨R, hBR, hRL, hR⟩ := D.exists_cutsOf_eq (I := D.cutsOf P ∩ D.cutsOf P') (by
      intro i hi
      exact D.isNode_of_mem_cutsOf hi.1)
    have hPR : P ≤ R := (D.cutsOf_le_iff hBP hPL hBR).2 (by rw [hR]; exact Set.inter_subset_left)
    have hP'R : P' ≤ R := (D.cutsOf_le_iff hBP' hP'L hBR).2 (by rw [hR]; exact Set.inter_subset_right)
    have := (D.cutsOf_le_iff hBS hSL hBR).1 (sup_le hPR hP'R)
    rw [hR] at this
    exact this

noncomputable def psiHom (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A))
    (hk : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1) : SLt n →* SLt n :=
  D.e.liftOfRightInverse (Function.surjInv D.surj) (Function.rightInverse_surjInv D.surj)
    ⟨D.e.comp (L.normalizerMonoidHom ⟨s, hs⟩).toMonoidHom, fun x hx =>
      MonoidHom.mem_ker.mpr (hk x (MonoidHom.mem_ker.mp hx))⟩

theorem psiHom_e (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A))
    (hk : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1) (x : ↥L) :
    D.psiHom s hs hk (D.e x) = D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

noncomputable def psi (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A))
    (hk : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (hk' : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s⁻¹, inv_mem hs⟩ x) = 1) :
    SLt n ≃* SLt n :=
  MonoidHom.toMulEquiv (D.psiHom s hs hk) (D.psiHom s⁻¹ (inv_mem hs) hk')
    (MonoidHom.ext fun y => by
      obtain ⟨x, rfl⟩ := D.surj y
      simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
      rw [D.psiHom_e s hs hk, D.psiHom_e s⁻¹ (inv_mem hs) hk']
      congr 1
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
      group)
    (MonoidHom.ext fun y => by
      obtain ⟨x, rfl⟩ := D.surj y
      simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
      rw [D.psiHom_e s⁻¹ (inv_mem hs) hk', D.psiHom_e s hs hk]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
      group)

theorem psi_e (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A))
    (hk : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (hk' : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s⁻¹, inv_mem hs⟩ x) = 1) (x : ↥L) :
    D.psi s hs hk hk' (D.e x) = D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) :=
  D.psiHom_e s hs hk x

theorem map_model_conj (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A))
    (hk : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (hk' : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s⁻¹, inv_mem hs⟩ x) = 1)
    {K : Subgroup A} (hBK : B ≤ K) (hBK' : B ≤ conjSub s K) :
    (D.model K).map (D.psi s hs hk hk').toMonoidHom = D.model (conjSub s K) := by
  ext g
  obtain ⟨x, rfl⟩ := D.surj g
  rw [Subgroup.mem_map_equiv, D.mem_model hBK']
  have hsymm : (D.psi s hs hk hk').symm (D.e x) =
      D.e (L.normalizerMonoidHom ⟨s⁻¹, inv_mem hs⟩ x) := by
    rw [MulEquiv.symm_apply_eq, D.psi_e s hs hk hk']
    congr 1
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
    group
  rw [hsymm, D.mem_model hBK, mem_conjSub]
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]

theorem cutsOf_conj_dichotomy (hn : 3 ≤ n) (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A))
    (hk : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (hk' : ∀ x : ↥L, D.e x = 1 → D.e (L.normalizerMonoidHom ⟨s⁻¹, inv_mem hs⟩ x) = 1)
    (hBs : conjSub s B = B) :
    (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = D.cutsOf K) ∨
      (∀ K : Subgroup A, B ≤ K → K ≤ L →
        D.cutsOf (conjSub s K) = flipNodes n (D.cutsOf K)) := by
  have hBK' : ∀ K : Subgroup A, B ≤ K → B ≤ conjSub s K := by
    intro K hBK x hx
    rw [mem_conjSub]
    have : x ∈ conjSub s B := by rw [hBs]; exact hx
    rw [mem_conjSub] at this
    exact hBK this
  have hφ : (Ut n).map (D.psi s hs hk hk').toMonoidHom = Ut n := by
    have := D.map_model_conj s hs hk hk' (le_refl B) (hBK' B le_rfl)
    rw [hBs, D.model_B] at this
    exact this
  rcases aut_dichotomy hn (D.psi s hs hk hk') hφ with ⟨b, hbU, hb⟩ | h
  · left
    intro K hBK hKL
    have h1 := D.map_model_conj s hs hk hk' hBK (hBK' K hBK)
    have hbK : b ∈ D.model K := D.Ut_le_model hBK hbU
    have h2 : (D.model K).map (D.psi s hs hk hk').toMonoidHom = D.model K := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        have : (D.psi s hs hk hk').toMonoidHom g = b * g * b⁻¹ := hb g
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbK hg) (Subgroup.inv_mem _ hbK)
      · intro g hg
        refine ⟨b⁻¹ * g * b, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hbK) hg) hbK, ?_⟩
        have : (D.psi s hs hk hk').toMonoidHom (b⁻¹ * g * b) = b * (b⁻¹ * g * b) * b⁻¹ := hb _
        rw [this]
        group
    rw [cutsOf, cutsOf, ← h1, h2]
  · right
    intro K hBK hKL
    have h1 := D.map_model_conj s hs hk hk' hBK (hBK' K hBK)
    have hUt : Ut n ≤ D.model K := D.Ut_le_model hBK
    have e1 : D.model K = QI n (cuts (D.model K)) := eq_QI_cuts hUt
    have hI : ∀ i ∈ cuts (D.model K), IsNode n i := fun i hi => isNode_of_mem_cuts hi
    have e2 : (D.model K).map (D.psi s hs hk hk').toMonoidHom = QI n (flipNodes n (D.cutsOf K)) := by
      conv_lhs => rw [e1]
      exact map_QI_of_swap _ h hI
    rw [cutsOf, ← h1, e2]
    exact cuts_QI (by
      rintro j ⟨i, hi, rfl⟩
      exact isNode_flip (isNode_of_mem_cuts hi))

end SurjBorel

theorem exists_surjBorel [Finite A] {L B : Subgroup A} {n : ℕ} (hn : 1 ≤ n)
    (h : IsPSL n 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) (hB : IsSylowTwoOf B L) :
    ∃ D : SurjBorel n L B, D.e.ker = CFSG.pCore 2 ↥L := by
  obtain ⟨e₀⟩ := nonempty_equiv_SLt_of_isPSL h
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hB
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let e₁ : ↥L →* SLt n := e₀.toMonoidHom.comp π
  have he₁ : Function.Surjective e₁ := e₀.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective (f := e₁) he₁ P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup ↥L).map e₁ :=
    Sylow.coe_mapSurjective (f := e₁) he₁ P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular hn Q
  have hker₁ : e₁.ker = CFSG.pCore 2 ↥L := by
    ext x
    simp only [e₁, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, π,
      QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let e : ↥L →* SLt n := (MulAut.conj g⁻¹).toMonoidHom.comp e₁
  have hker : e.ker = CFSG.pCore 2 ↥L := by
    rw [← hker₁]
    ext x
    simp only [e, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hKP : CFSG.pCore 2 ↥L ≤ (P : Subgroup ↥L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).le_sylow_of_normal P
  refine ⟨⟨e, (MulAut.conj g⁻¹).surjective.comp he₁, hB.1, ?_, ?_⟩, hker⟩
  · show e.ker ≤ B.subgroupOf L
    rw [hker, ← hP]
    exact hKP
  · have h1 : (B.subgroupOf L).map e₁ = conjSub g (Ut n) := by
      rw [← hP, ← hQ, hg]
      rfl
    have h2 : (B.subgroupOf L).map e = conjSub g⁻¹ ((B.subgroupOf L).map e₁) := by
      rw [conjSub, Subgroup.map_map]
    show (B.subgroupOf L).map e = Ut n
    rw [h2, h1, conjSub_inv_conjSub]

end CFSG.Quasithin.FLc
