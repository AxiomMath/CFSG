module

public import CFSG.Quasithin.Background.FLcGrp
public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type*} [Group A]

structure BorelIso (n : ℕ) (L B : Subgroup A) where
  e : ↥L ≃* SLt n
  hB : (B.subgroupOf L).map e.toMonoidHom = Ut n

namespace BorelIso

variable {n : ℕ} {L B : Subgroup A} (D : BorelIso n L B)

@[expose] def model (P : Subgroup A) : Subgroup (SLt n) := (P.subgroupOf L).map D.e.toMonoidHom

@[expose] def cutsOf (P : Subgroup A) : Set ℕ := cuts (D.model P)

theorem mem_model {P : Subgroup A} (x : ↥L) : D.e x ∈ D.model P ↔ (x : A) ∈ P := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := D.e.injective hyx
    subst this
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem model_B : D.model B = Ut n := D.hB

theorem model_le_iff {P P' : Subgroup A} (hP : P ≤ L) : D.model P ≤ D.model P' ↔ P ≤ P' := by
  constructor
  · intro h x hx
    have h1 : D.e ⟨x, hP hx⟩ ∈ D.model P := (D.mem_model _).2 hx
    exact (D.mem_model _).1 (h h1)
  · intro h g hg
    obtain ⟨x, rfl⟩ := D.e.surjective g
    exact (D.mem_model x).2 (h ((D.mem_model x).1 hg))

theorem Ut_le_model_iff (hBL : B ≤ L) {P : Subgroup A} : Ut n ≤ D.model P ↔ B ≤ P := by
  rw [← D.model_B, D.model_le_iff hBL]

theorem card_model {P : Subgroup A} (hP : P ≤ L) : Nat.card (D.model P) = Nat.card P := by
  rw [model, Subgroup.card_map_of_injective D.e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv

theorem model_L : D.model L = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := D.e.surjective g
  exact (D.mem_model x).2 x.2

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

theorem cutsOf_le_iff (hBL : B ≤ L) {P P' : Subgroup A} (hBP : B ≤ P) (hPL : P ≤ L)
    (hBP' : B ≤ P') : P ≤ P' ↔ D.cutsOf P' ⊆ D.cutsOf P := by
  rw [← D.model_le_iff hPL]
  exact le_iff_cuts ((D.Ut_le_model_iff hBL).2 hBP) ((D.Ut_le_model_iff hBL).2 hBP')

theorem eq_of_cutsOf_eq (hBL : B ≤ L) {P P' : Subgroup A} (hBP : B ≤ P) (hPL : P ≤ L)
    (hBP' : B ≤ P') (hP'L : P' ≤ L) (h : D.cutsOf P = D.cutsOf P') : P = P' :=
  le_antisymm ((D.cutsOf_le_iff hBL hBP hPL hBP').2 h.ge)
    ((D.cutsOf_le_iff hBL hBP' hP'L hBP).2 h.le)

theorem exists_cutsOf_eq (hBL : B ≤ L) {I : Set ℕ} (hI : ∀ i ∈ I, IsNode n i) :
    ∃ P : Subgroup A, B ≤ P ∧ P ≤ L ∧ D.cutsOf P = I := by
  let K : Subgroup ↥L := (QI n I).comap D.e.toMonoidHom
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
  have hmodel : D.model P = QI n I := by
    ext g
    obtain ⟨x, rfl⟩ := D.e.surjective g
    rw [D.mem_model, hmemP]
  refine ⟨P, ?_, Subgroup.map_subtype_le _, ?_⟩
  · intro b hb
    have hbL : b ∈ L := hBL hb
    have h1 : D.e ⟨b, hbL⟩ ∈ D.model B := (D.mem_model _).2 hb
    rw [D.model_B] at h1
    exact (hmemP ⟨b, hbL⟩).2 (Ut_le_QI n I h1)
  · rw [cutsOf, hmodel]
    exact cuts_QI hI

theorem isMax_of_cuts_insert (hBL : B ≤ L) {P K : Subgroup A} (hBP : B ≤ P) (hPL : P ≤ L)
    (hBK : B ≤ K) (hKL : K ≤ L) {x : ℕ} (hx : x ∉ D.cutsOf P)
    (hK : D.cutsOf K = insert x (D.cutsOf P)) : IsMaxSubgroupIn P K := by
  have hKP : K ≤ P :=
    (D.cutsOf_le_iff hBL hBK hKL hBP).2 (by rw [hK]; exact Set.subset_insert _ _)
  have hxK : x ∈ D.cutsOf K := by rw [hK]; exact Set.mem_insert _ _
  have hne : K ≠ P := by
    intro he
    rw [he] at hxK
    exact hx hxK
  refine ⟨lt_of_le_of_ne hKP hne, fun K' hKK' hK'P => ?_⟩
  have hBK' : B ≤ K' := hBK.trans hKK'.le
  have hK'L : K' ≤ L := hK'P.trans hPL
  have h1 : D.cutsOf P ⊆ D.cutsOf K' := (D.cutsOf_le_iff hBL hBK' hK'L hBP).1 hK'P
  have h2 : D.cutsOf K' ⊆ D.cutsOf K := (D.cutsOf_le_iff hBL hBK hKL hBK').1 hKK'.le
  have hxK' : x ∉ D.cutsOf K' := by
    intro hxK'
    have h3 : D.cutsOf K ⊆ D.cutsOf K' := by
      rw [hK]
      exact Set.insert_subset hxK' h1
    exact hKK'.ne (D.eq_of_cutsOf_eq hBL hBK hKL hBK' hK'L (Set.Subset.antisymm h3 h2))
  refine D.eq_of_cutsOf_eq hBL hBK' hK'L hBP hPL (Set.Subset.antisymm (fun i hi => ?_) h1)
  have := h2 hi
  rw [hK] at this
  rcases this with rfl | h
  · exact absurd hi hxK'
  · exact h

theorem exists_unique_node_of_isMax (hBL : B ≤ L) {P : Subgroup A} (hPL : P ≤ L)
    (hmax : IsMaxSubgroupIn P B) :
    ∃ x, IsNode n x ∧ x ∉ D.cutsOf P ∧ ∀ y, IsNode n y → y ∉ D.cutsOf P → y = x := by
  have hBP : B ≤ P := hmax.1.le
  have hne : D.cutsOf P ≠ {i | IsNode n i} := by
    intro h
    exact hmax.1.ne (D.eq_of_cutsOf_eq hBL le_rfl hBL hBP hPL (by rw [h, D.cutsOf_B]))
  obtain ⟨x, hxF, hxP⟩ : ∃ x, IsNode n x ∧ x ∉ D.cutsOf P := by
    by_contra hall
    push Not at hall
    apply hne
    ext i
    exact ⟨fun hi => D.isNode_of_mem_cutsOf hi, fun hi => hall i hi⟩
  refine ⟨x, hxF, hxP, fun y hy hyP => ?_⟩
  by_contra hyx
  obtain ⟨K, hBK, hKL, hKJ⟩ := D.exists_cutsOf_eq hBL (I := insert x (D.cutsOf P)) (by
    intro i hi
    rcases hi with rfl | hi
    · exact hxF
    · exact D.isNode_of_mem_cutsOf hi)
  have hKmax := D.isMax_of_cuts_insert hBL hBP hPL hBK hKL hxP hKJ
  have hBK' : B < K := by
    refine lt_of_le_of_ne hBK fun he => ?_
    have h1 := congrArg D.cutsOf he
    have hy' : y ∈ D.cutsOf B := by rw [D.cutsOf_B]; exact hy
    rw [h1, hKJ] at hy'
    rcases hy' with h | h
    · exact hyx h
    · exact hyP h
  exact hKmax.1.ne (hmax.2 K hBK' hKmax.1.le)

theorem exists_unique_node_of_unique_max (hBL : B ≤ L) {P : Subgroup A} (hBP : B < P)
    (hPL : P ≤ L)
    (hunique : ∀ N₁ N₂ : Subgroup A, IsMaxSubgroupIn P N₁ → B ≤ N₁ → IsMaxSubgroupIn P N₂ →
      B ≤ N₂ → N₁ = N₂) :
    ∃ x, IsNode n x ∧ x ∉ D.cutsOf P ∧ ∀ y, IsNode n y → y ∉ D.cutsOf P → y = x := by
  have hne : D.cutsOf P ≠ {i | IsNode n i} := by
    intro h
    exact hBP.ne (D.eq_of_cutsOf_eq hBL le_rfl hBL hBP.le hPL (by rw [h, D.cutsOf_B]))
  obtain ⟨x, hxF, hxP⟩ : ∃ x, IsNode n x ∧ x ∉ D.cutsOf P := by
    by_contra hall
    push Not at hall
    apply hne
    ext i
    exact ⟨fun hi => D.isNode_of_mem_cutsOf hi, fun hi => hall i hi⟩
  refine ⟨x, hxF, hxP, fun y hy hyP => ?_⟩
  by_contra hyx
  have hmk : ∀ z, IsNode n z → z ∉ D.cutsOf P → ∃ K : Subgroup A, B ≤ K ∧ K ≤ L ∧
      D.cutsOf K = insert z (D.cutsOf P) := by
    intro z hz _
    exact D.exists_cutsOf_eq hBL (I := insert z (D.cutsOf P)) (by
      intro i hi
      rcases hi with rfl | hi
      · exact hz
      · exact D.isNode_of_mem_cutsOf hi) |>.imp fun K hK => hK
  obtain ⟨Kx, hBKx, hKxL, hKx⟩ := hmk x hxF hxP
  obtain ⟨Ky, hBKy, hKyL, hKy⟩ := hmk y hy hyP
  have hmx := D.isMax_of_cuts_insert hBL hBP.le hPL hBKx hKxL hxP hKx
  have hmy := D.isMax_of_cuts_insert hBL hBP.le hPL hBKy hKyL hyP hKy
  have heq := hunique Kx Ky hmx hBKx hmy hBKy
  have hxKx : x ∈ D.cutsOf Kx := by rw [hKx]; exact Set.mem_insert _ _
  rw [heq, hKy] at hxKx
  rcases hxKx with h | h
  · exact hyx h.symm
  · exact hxP h

@[expose] noncomputable def autOf (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A)) :
    SLt n ≃* SLt n :=
  D.e.symm.trans ((L.normalizerMonoidHom ⟨s, hs⟩).trans D.e)

theorem autOf_e (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A)) (x : ↥L) :
    D.autOf s hs (D.e x) = D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) := by
  simp [autOf]

theorem model_conjSub (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A)) (P : Subgroup A) :
    (D.model P).map (D.autOf s hs).toMonoidHom = D.model (conjSub s P) := by
  ext g
  obtain ⟨x, rfl⟩ := D.e.surjective g
  rw [Subgroup.mem_map_equiv, D.mem_model, mem_conjSub]
  have hxs : s⁻¹ * (x : A) * s ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hs) (x : A)).1 x.2
    simpa using this
  have hsymm : (D.autOf s hs).symm (D.e x) = D.e ⟨s⁻¹ * (x : A) * s, hxs⟩ := by
    rw [MulEquiv.symm_apply_eq, D.autOf_e]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show (x : A) = s * (s⁻¹ * (x : A) * s) * s⁻¹
    group
  rw [hsymm, D.mem_model]

end BorelIso

@[expose] def flipNodes (n : ℕ) (I : Set ℕ) : Set ℕ := {j | ∃ i ∈ I, j = n - i}

theorem isNode_flip {n i : ℕ} (h : IsNode n i) : IsNode n (n - i) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem map_QI_of_swap {n : ℕ} (φ : SLt n ≃* SLt n)
    (h : ∀ d, 1 ≤ d → d < n → (stabilizer (flagSpace n (ZMod 2) d)).map φ.toMonoidHom =
      stabilizer (flagSpace n (ZMod 2) (n - d))) {I : Set ℕ} (hI : ∀ i ∈ I, IsNode n i) :
    (QI n I).map φ.toMonoidHom = QI n (flipNodes n I) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_flagStabilizer, mem_flagStabilizer]
  constructor
  · rintro hg j ⟨i, hi, rfl⟩
    have hin := hI i hi
    have h1 := hg i hi
    have h2 : g ∈ (stabilizer (flagSpace n (ZMod 2) i)).map φ.toMonoidHom :=
      Subgroup.mem_map_equiv.2 h1
    rwa [h i hin.1 hin.2] at h2
  · intro hg i hi
    have hin := hI i hi
    have h1 := hg (n - i) ⟨i, hi, rfl⟩
    rw [← h i hin.1 hin.2] at h1
    exact Subgroup.mem_map_equiv.1 h1

namespace BorelIso

variable {n : ℕ} {L B : Subgroup A} (D : BorelIso n L B)

theorem cutsOf_conjSub (hBL : B ≤ L) (s : A) (hs : s ∈ Subgroup.normalizer (L : Set A))
    (h : ∀ d, 1 ≤ d → d < n → (stabilizer (flagSpace n (ZMod 2) d)).map
      (D.autOf s hs).toMonoidHom = stabilizer (flagSpace n (ZMod 2) (n - d)))
    {P : Subgroup A} (hBP : B ≤ P) :
    D.cutsOf (conjSub s P) = flipNodes n (D.cutsOf P) := by
  have hUt : Ut n ≤ D.model P := (D.Ut_le_model_iff hBL).2 hBP
  have e1 : D.model P = QI n (cuts (D.model P)) := eq_QI_cuts hUt
  have e2 : D.model (conjSub s P) = QI n (flipNodes n (D.cutsOf P)) := by
    rw [← D.model_conjSub s hs P]
    conv_lhs => rw [e1]
    exact map_QI_of_swap _ h (fun i hi => D.isNode_of_mem_cutsOf hi)
  rw [cutsOf, e2]
  exact cuts_QI (by
    rintro j ⟨i, hi, rfl⟩
    exact isNode_flip (D.isNode_of_mem_cutsOf hi))

end BorelIso

end CFSG.Quasithin.FLc
