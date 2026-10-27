module

public import CFSG.Quasithin.H13.GoldschmidtC137Baum
public import CFSG.Quasithin.H13.GoldschmidtC137WeakB19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBlockTransferHyp

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.Lift

variable {G : Type} [Group G]

theorem isMaxElemAbelian_map_subtype_gc {X R : Subgroup G} {A' : Subgroup ↥X} (hRX : R ≤ X)
    (h : IsMaxElemAbelian (R.subgroupOf X) A') : IsMaxElemAbelian R (A'.map X.subtype) := by
  refine ⟨?_, isElemAbelian_map_subtype h.2.1, fun B hBR hBe => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h.1 hy
  · have hBX : B ≤ X := hBR.trans hRX
    have h1 := h.2.2 (B.subgroupOf X) (fun x hx => hBR hx) (isElemAbelian_subgroupOf hBe)
    have h2 : Nat.card ↥(B.subgroupOf X) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
    rw [Subgroup.card_map_of_injective X.subtype_injective, ← h2]
    exact h1

theorem b2_19_rel' [Finite G] {X V L R : Subgroup G} (hV : IsElemAbelian 2 V) (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G))
    (hL : L = CFSG.QuasithinUnique.Setup.oddOrderSubgroup X)
    (hR : IsPGroup 2 R) (hRX : R ≤ X) (hVR : V ≤ R)
    (hA₁ : pCoreOf 2 L ≤ R ⊓ centralizer (V : Set G))
    (hA₂ : IsSylowTwoOf (R ⊓ centralizer (V : Set G)) ((L ⊔ R) ⊓ centralizer (V : Set G)))
    (hA₃ : L ≤ normalizer ((R ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
    (hB : (L ⊓ centralizer (V : Set G)).subgroupOf X ≤ oTwoPhi (L.subgroupOf X))
    (hC : ∀ A, ¬ IsStrongFFOffender hV R A)
    (hDE : ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V hV))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI hV L, B1.conjAut g (Y i) ≤ autI hV R) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn hV (L ⊔ R) (Y i))) ∧
      (∀ i, Y i = autI hV (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 R) ∧
      autI hV L ≤ ⨆ i, Y i ∧ ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV L)) ∧
      ∀ A, IsFFStarOffender (autI hV R) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V hV))), A = ⨆ k, Ai k ∧
          ∀ k, IsFFStarOffender (autI hV R) (Ai k) ∧ ∃ j : Fin n, ∃ g ∈ autI hV L,
            Ai k ≤ B1.conjAut g (Y j) ∧ B1.conjAut g (Y j) ≤ autI hV R) :
    IsSylowTwoOf (baum R ⊓ centralizer (V : Set G)) ((L ⊔ baum R) ⊓ centralizer (V : Set G)) ∧
      (IsSylowTwoOf (autI hV (baum R)) (autI hV L ⊔ autI hV (baum R)) →
        IsSylowTwoOf (baum R) (L ⊔ baum R)) := by
  have hLX : L ≤ X := hL ▸ CFSG.QuasithinUnique.Setup.oddOrderSubgroup_le X
  have hVN' := (Subgroup.normal_subgroupOf_iff_le_normalizer hVX).2 hXN
  have hV' := isElemAbelian_subgroupOf (X := X) hV
  set θ := theta (ivEquiv hV hVX) with hθ
  have hL' : L.subgroupOf X = pResidualOf 2 (⊤ : Subgroup ↥X) := by
    rw [B2F.pResidualOf_top_eq_closure_odd, hL,
      ← CFSG.QuasithinUnique.Setup.Lift.oddOrderSubgroup_top_eq_subgroupOf]
    unfold CFSG.QuasithinUnique.Setup.oddOrderSubgroup
    congr 1
    ext x
    simp
  have hR' := isPGroup_subgroupOf hRX hR
  have hVR' : V.subgroupOf X ≤ R.subgroupOf X := fun x hx => hVR hx
  have hCX : centralizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (centralizer (V : Set G)).subgroupOf X := centralizer_subgroupOf_eq hVX
  have hRCX : R ⊓ centralizer (V : Set G) ≤ X := inf_le_left.trans hRX
  have hLRX : L ⊔ R ≤ X := sup_le hLX hRX
  have hLRC : (L ⊔ R) ⊓ centralizer (V : Set G) ≤ X := inf_le_left.trans hLRX
  have hA₁' : pCoreOf 2 (L.subgroupOf X) ≤
      R.subgroupOf X ⊓ centralizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [pCoreOf_subgroupOf_eq hLX, hCX, ← inf_subgroupOf_eq]
    exact fun x hx => hA₁ hx
  have hA₂' : IsSylowTwoOf (R.subgroupOf X ⊓ centralizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X))
      ((L.subgroupOf X ⊔ R.subgroupOf X) ⊓
        centralizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X)) := by
    rw [hCX, ← inf_subgroupOf_eq, ← Subgroup.subgroupOf_sup hLX hRX, ← inf_subgroupOf_eq,
      isSylowTwoOf_subgroupOf_iff hA₂.1 hLRC]
    exact hA₂
  have hA₃' : L.subgroupOf X ≤ normalizer
      ((R.subgroupOf X ⊓ centralizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) :
        Subgroup ↥X) : Set ↥X) := by
    rw [hCX, ← inf_subgroupOf_eq]
    intro x hx
    exact (mem_normalizer_subgroupOf_iff hRCX x).2 (hA₃ hx)
  have hB' : L.subgroupOf X ⊓ centralizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤
      oTwoPhi (L.subgroupOf X) := by
    rw [hCX, ← inf_subgroupOf_eq]
    exact hB
  have hC' : ∀ A', ¬ IsStrongFFOffender hV' (R.subgroupOf X) A' := by
    intro A' hA'
    obtain ⟨A, hAX, rfl⟩ : ∃ A : Subgroup G, A ≤ X ∧ A' = A.subgroupOf X :=
      ⟨A'.map X.subtype, fun x ⟨y, _, hy⟩ => hy ▸ y.2,
        (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm⟩
    obtain ⟨⟨hmax, hnc⟩, hstr⟩ := hA'
    refine hC A ⟨⟨?_, ?_⟩, ?_⟩
    · have := isMaxElemAbelian_map_subtype_gc hRX hmax
      rwa [Subgroup.map_subgroupOf_eq_of_le hAX] at this
    · intro hAC
      apply hnc
      rw [hCX]
      intro x hx
      exact hAC hx
    · rw [autI_subgroupOf_eq hV hVX hXN hRX, autI_subgroupOf_eq hV hVX hXN hAX] at hstr
      exact (isStrongFFStarOffender_map_iff _).1 hstr
  obtain ⟨n, Y, Rs, h1, h2, h3, h4, h5, h6, h7⟩ := hDE
  have hDE' : ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod (V.subgroupOf X) hV')))
      (Rs : Fin n → Subgroup ↥X),
      (∀ i, ∃ g ∈ autI hV' (L.subgroupOf X), B1.conjAut g (Y i) ≤ autI hV' (R.subgroupOf X)) ∧
      (∀ i, IsSylowTwoOf (Rs i) (B2F.starPre hV' hVN' (L.subgroupOf X ⊔ R.subgroupOf X) (Y i))) ∧
      (∀ i, Y i = autI hV' (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 (R.subgroupOf X)) ∧
      autI hV' (L.subgroupOf X) ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV' (L.subgroupOf X))) ∧
      ∀ A, IsFFStarOffender (autI hV' (R.subgroupOf X)) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod (V.subgroupOf X) hV'))),
          A = ⨆ k, Ai k ∧ ∀ k, IsFFStarOffender (autI hV' (R.subgroupOf X)) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI hV' (L.subgroupOf X), Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI hV' (R.subgroupOf X) := by
    refine ⟨n, fun i => (Y i).map θ.toMonoidHom, fun i => (Rs i).subgroupOf X, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro i
      obtain ⟨g, hg, hle⟩ := h1 i
      refine ⟨θ g, ?_, ?_⟩
      · rw [autI_subgroupOf_eq hV hVX hXN hLX]
        exact ⟨g, hg, rfl⟩
      · rw [conjAut_map, autI_subgroupOf_eq hV hVX hXN hRX]
        exact Subgroup.map_mono hle
    · intro i
      rw [← Subgroup.subgroupOf_sup hLX hRX, starPre_eq hV hVX hXN _ (Y i)]
      refine (isSylowTwoOf_subgroupOf_iff (h2 i).2.1 ?_).2 (h2 i).2
      exact inf_le_left.trans hLRX
    · intro i
      rw [thompsonJ_subgroupOf_eq (h2 i).1,
        autI_subgroupOf_eq hV hVX hXN ((B6.thompsonJ_le _).trans (h2 i).1), ← h3 i]
    · intro i
      rw [pRank_subgroupOf_eq (h2 i).1, pRank_subgroupOf_eq hRX]
      exact h4 i
    · rw [autI_subgroupOf_eq hV hVX hXN hLX, ← Subgroup.map_iSup]
      exact Subgroup.map_mono h5
    · simp only [hθ, rkIdx_fixV_map]
      rw [autI_subgroupOf_eq hV hVX hXN hLX, rkIdx_fixV_map]
      exact h6
    · intro A' hA'
      obtain ⟨A, rfl⟩ : ∃ A, A' = A.map θ.toMonoidHom :=
        ⟨A'.map θ.symm.toMonoidHom, by rw [Subgroup.map_map]; simp⟩
      rw [autI_subgroupOf_eq hV hVX hXN hRX, isFFStarOffender_map_iff] at hA'
      obtain ⟨r, Ai, hA, hAi⟩ := h7 A hA'
      refine ⟨r, fun k => (Ai k).map θ.toMonoidHom, ?_, ?_⟩
      · rw [hA, Subgroup.map_iSup]
      · intro k
        obtain ⟨hk1, j, g, hg, hle1, hle2⟩ := hAi k
        refine ⟨?_, j, θ g, ?_, ?_, ?_⟩
        · rw [autI_subgroupOf_eq hV hVX hXN hRX, isFFStarOffender_map_iff]
          exact hk1
        · rw [autI_subgroupOf_eq hV hVX hXN hLX]
          exact ⟨g, hg, rfl⟩
        · rw [conjAut_map]
          exact Subgroup.map_mono hle1
        · rw [conjAut_map, autI_subgroupOf_eq hV hVX hXN hRX]
          exact Subgroup.map_mono hle2
  obtain ⟨-, -, c3, c4⟩ := B2_19' (G := ↥X) hV' hVN' hL' hR' hVR' hA₁' hA₂' hA₃' hB' hC' hDE'
  have hbX : baum R ≤ X := (inf_le_left : baum R ≤ R).trans hRX
  have hLbX : L ⊔ baum R ≤ X := sup_le hLX hbX
  have hbCX : baum R ⊓ centralizer (V : Set G) ≤ X := inf_le_left.trans hbX
  have hLbC : (L ⊔ baum R) ⊓ centralizer (V : Set G) ≤ X := inf_le_left.trans hLbX
  refine ⟨?_, fun hS => ?_⟩
  · rw [baum_subgroupOf_eq hRX, hCX, ← inf_subgroupOf_eq, ← Subgroup.subgroupOf_sup hLX hbX,
      ← inf_subgroupOf_eq, isSylowTwoOf_subgroupOf_iff
        (inf_le_inf_right _ le_sup_right) hLbC] at c3
    exact c3
  · have hS' : IsSylowTwoOf (autI hV' ((baum R).subgroupOf X))
        (autI hV' (L.subgroupOf X) ⊔ autI hV' ((baum R).subgroupOf X)) := by
      rw [autI_subgroupOf_eq hV hVX hXN hLX, autI_subgroupOf_eq hV hVX hXN hbX,
        ← Subgroup.map_sup, isSylowTwoOf_map_theta_iff]
      exact hS
    have := c4 (by rw [baum_subgroupOf_eq hRX]; exact hS')
    rw [baum_subgroupOf_eq hRX, ← Subgroup.subgroupOf_sup hLX hbX,
      isSylowTwoOf_subgroupOf_iff le_sup_right hLbX] at this
    exact this

end CFSG.Quasithin.H13.U3.GC137
