module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.HyperplaneOrbitBounds
public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations
open CFSG.Quasithin

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]

@[expose] noncomputable def w16g_toSub : Subgroup W ≃o Submodule (ZMod 2) (Additive W) :=
  (Subgroup.toAddSubgroup (G := W)).trans (AddSubgroup.toZModSubmodule (n := 2) (M := Additive W))

@[simp]
theorem w16g_mem_toSub (S : Subgroup W) (x : Additive W) :
    x ∈ w16g_toSub S ↔ x.toMul ∈ S := by
  simp [w16g_toSub]

@[simp]
theorem w16g_toSub_top : w16g_toSub (⊤ : Subgroup W) = ⊤ :=
  w16g_toSub.map_top

@[simp]
theorem w16g_toSub_inf (S T : Subgroup W) :
    w16g_toSub (S ⊓ T) = w16g_toSub S ⊓ w16g_toSub T :=
  w16g_toSub.map_inf S T

@[simp]
theorem w16g_toSub_bot : w16g_toSub (⊥ : Subgroup W) = ⊥ :=
  w16g_toSub.map_bot

@[simp]
theorem w16g_toSub_iSup {ι : Sort*} (S : ι → Subgroup W) :
    w16g_toSub (⨆ i, S i) = ⨆ i, w16g_toSub (S i) :=
  w16g_toSub.map_iSup S

theorem w16g_toSub_fixV (D : Subgroup (MulAut W)) :
    w16g_toSub (CFSG.Quasithin.fixV D) =
      fixedSpace (CFSG.RankThree.FFModules.autRep W) D := by
  ext x
  rw [w16g_mem_toSub, mem_fixedSpace_iff, CFSG.Quasithin.mem_fixV]
  constructor
  · intro h d hd
    rw [CFSG.RankThree.FFModules.autRep_apply]
    simpa using congrArg Additive.ofMul (h d hd)
  · intro h d hd
    have := h d hd
    rw [CFSG.RankThree.FFModules.autRep_apply] at this
    exact Additive.ofMul.injective this

theorem w16g_toSub_closure (S : Set W) :
    w16g_toSub (Subgroup.closure S) = Submodule.span (ZMod 2) (Additive.ofMul '' S) := by
  apply le_antisymm
  · have h : Subgroup.closure S ≤
        w16g_toSub.symm (Submodule.span (ZMod 2) (Additive.ofMul '' S)) := by
      rw [Subgroup.closure_le]
      intro s hs
      change Additive.ofMul s ∈
        w16g_toSub (w16g_toSub.symm (Submodule.span (ZMod 2) (Additive.ofMul '' S)))
      rw [OrderIso.apply_symm_apply]
      exact Submodule.subset_span ⟨s, hs, rfl⟩
    simpa using w16g_toSub.monotone h
  · apply Submodule.span_le.2
    rintro _ ⟨s, hs, rfl⟩
    simpa using Subgroup.subset_closure hs

theorem w16g_toSub_commSub (U : Subgroup W) (X : Subgroup (MulAut W)) :
    w16g_toSub (CFSG.Quasithin.commSub U X) =
      commOn (CFSG.RankThree.FFModules.autRep W) X (w16g_toSub U) := by
  unfold CFSG.Quasithin.commSub CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commOn
  rw [w16g_toSub_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨c, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    exact ⟨x, hx, Additive.ofMul w, by rw [w16g_mem_toSub]; exact hw, by
      simp [CFSG.RankThree.FFModules.autRep_apply, sub_eq_add_neg]⟩
  · rintro ⟨x, hx, u, hu, rfl⟩
    rw [w16g_mem_toSub] at hu
    exact ⟨x u.toMul * (u.toMul)⁻¹, ⟨x, hx, u.toMul, hu, rfl⟩, by
      simp [CFSG.RankThree.FFModules.autRep_apply, sub_eq_add_neg]⟩

@[simp]
theorem w16g_commOn_top {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) :
    commOn ρ X ⊤ = commSpace ρ X := by
  unfold commOn commSpace
  congr 1
  ext w
  simp

theorem w16g_rk_eq_finrank [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (S : Subgroup W) :
    rk S = Module.finrank (ZMod 2) (w16g_toSub S) := by
  have hcard : Nat.card (w16g_toSub S) = Nat.card S :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.toMul, (w16g_mem_toSub S x.1).1 x.2⟩
        invFun := fun s => ⟨Additive.ofMul s.1, by rw [w16g_mem_toSub]; simp⟩
        left_inv := fun x => by ext; simp
        right_inv := fun s => by ext; simp }
  have h1 : Nat.card S = 2 ^ rk S := card_eq_two_pow hW S
  haveI : Fintype (w16g_toSub S) := Fintype.ofFinite _
  have h2 : Fintype.card (w16g_toSub S) =
      2 ^ Module.finrank (ZMod 2) (w16g_toSub S) := by
    simpa using Module.card_eq_pow_finrank (K := ZMod 2) (V := w16g_toSub S)
  have h3 : Nat.card (w16g_toSub S) = 2 ^ Module.finrank (ZMod 2) (w16g_toSub S) := by
    rw [Nat.card_eq_fintype_card]; exact h2
  have h4 : (2 : ℕ) ^ rk S = 2 ^ Module.finrank (ZMod 2) (w16g_toSub S) := by
    rw [← h1, ← hcard, h3]
  exact Nat.pow_right_injective (a := 2) (by norm_num) h4

theorem w16g_iSupIndep_map_subtype {ι : Type*} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {M : Submodule (ZMod 2) V} {f : ι → Submodule (ZMod 2) M} (h : iSupIndep f) :
    iSupIndep (fun i => (f i).map M.subtype) := by
  rw [iSupIndep_def] at h ⊢
  intro i
  have hmap := Submodule.disjoint_map (Submodule.subtype_injective (p := M)) (h i)
  simpa only [Submodule.map_iSup] using hmap

theorem w16g_map_commSpace_restrictRep {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (S : Subgroup G)
    (M : Submodule (ZMod 2) V) (hM : ∀ s ∈ S, ∀ m ∈ M, ρ s m ∈ M) (B : Subgroup S) :
    (commSpace (ExtraspecialDimensionDivisibility.restrictRep ρ S M hM) B).map M.subtype =
      commOn ρ (B.map S.subtype) M := by
  apply le_antisymm
  · rw [commSpace, Submodule.map_span_le]
    rintro m ⟨b, hb, m', rfl⟩
    have hgen : ((ExtraspecialDimensionDivisibility.restrictRep ρ S M hM b m' - m' : M) : V)
        = ρ (b : S) (m' : V) - (m' : V) := by
      simp [ExtraspecialDimensionDivisibility.restrictRep]
    simp only [Submodule.subtype_apply]
    rw [hgen]
    exact Submodule.subset_span
      ⟨(b : S), Subgroup.mem_map_of_mem S.subtype hb, (m' : V), m'.2, rfl⟩
  · rw [commOn, Submodule.span_le]
    rintro _ ⟨g, hg, u, hu, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hg
    refine Submodule.mem_map.2
      ⟨ExtraspecialDimensionDivisibility.restrictRep ρ S M hM b ⟨u, hu⟩ - ⟨u, hu⟩,
        Submodule.subset_span ⟨b, hb, ⟨u, hu⟩, rfl⟩, ?_⟩
    simp [ExtraspecialDimensionDivisibility.restrictRep]

theorem w16g_map_commOn_restrictRep {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (S : Subgroup G)
    (M : Submodule (ZMod 2) V) (hM : ∀ s ∈ S, ∀ m ∈ M, ρ s m ∈ M) (B : Subgroup S)
    (N : Submodule (ZMod 2) M) :
    (commOn (ExtraspecialDimensionDivisibility.restrictRep ρ S M hM) B N).map M.subtype =
      commOn ρ (B.map S.subtype) (N.map M.subtype) := by
  apply le_antisymm
  · rw [commOn, Submodule.map_span_le]
    rintro n ⟨b, hb, n', hn', rfl⟩
    have hgen : ((ExtraspecialDimensionDivisibility.restrictRep ρ S M hM b n' - n' : M) : V)
        = ρ (b : S) (n' : V) - (n' : V) := by
      simp [ExtraspecialDimensionDivisibility.restrictRep]
    simp only [Submodule.subtype_apply]
    rw [hgen]
    exact Submodule.subset_span
      ⟨(b : S), Subgroup.mem_map_of_mem S.subtype hb, (n' : V), ⟨n', hn', rfl⟩, rfl⟩
  · rw [commOn, Submodule.span_le]
    rintro _ ⟨g, hg, u, hu, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.1 hu
    refine Submodule.mem_map.2
      ⟨ExtraspecialDimensionDivisibility.restrictRep ρ S M hM b n - n,
        Submodule.subset_span ⟨b, hb, n, hn, rfl⟩, ?_⟩
    simp [ExtraspecialDimensionDivisibility.restrictRep]

theorem w16g_isElemAbelianOfRank_comm_pow {p n : ℕ} {P : Type*} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

theorem w16g_card_of_isElemAbelianOfRank {p n : ℕ} {P : Type*} [Group P]
    (h : IsElemAbelianOfRank p n P) : Nat.card P = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd]
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

theorem w16g_isElemAbelian_of_isElemAbelianOfRank {p n : ℕ} {G : Type*} [Group G]
    {X : Subgroup G} (h : IsElemAbelianOfRank p n X) : CFSG.Open.IsElemAbelian p X := by
  obtain ⟨hcomm, hpow⟩ := w16g_isElemAbelianOfRank_comm_pow h
  refine ⟨IsMulCommutative.of_comm hcomm, fun x hx => ?_⟩
  have := congrArg Subtype.val (hpow ⟨x, hx⟩)
  simpa using this

@[expose] noncomputable def w16g_hyperplanesEquiv {p : ℕ} (A : Subgroup (MulAut W)) :
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p (⊤ : Subgroup ↥A) ≃
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A where
  toFun D' := ⟨D'.1.map A.subtype, by
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    rw [HyperplaneOrbitBounds.relIndex_map_sub, ← Subgroup.relIndex_top_right, D'.2.2]⟩
  invFun D := ⟨D.1.subgroupOf A, by
    refine ⟨le_top, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact D.2.2⟩
  left_inv D' := by
    apply Subtype.ext
    show (D'.1.map A.subtype).subgroupOf A = D'.1
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective D'.1
  right_inv D := by
    apply Subtype.ext
    show (D.1.subgroupOf A).map A.subtype = D.1
    rw [Subgroup.map_subgroupOf_eq_of_le D.2.1]

end CFSG.LocalAnalysis.WeakClosure81
