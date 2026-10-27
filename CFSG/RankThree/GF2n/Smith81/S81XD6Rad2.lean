module

public import CFSG.RankThree.GF2n.Smith81.S81XD6Rad

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6Spin


variable {K : Type} [Field K] [CharP K 2]

private theorem d6rad2_prodX_cons (γ : Fin (Tag.rank .E7) → ℤ) (L : List (Fin (Tag.rank .E7) → ℤ))
    (c : (Fin (Tag.rank .E7) → ℤ) → K) : prodX (γ :: L) c = xE γ (c γ) * prodX L c := by
  simp only [prodX, List.map_cons, List.prod_cons]

private theorem d6rad2_factor {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Phi b0) {e : K}
    (he : γ ∉ Perp → e = 0) : ∃ x ∈ rootRad0 K, IndW (xE γ e) x := by
  by_cases hp : γ ∈ Perp
  · have hpr : pr (a0 : Fin e7Data.d) γ = 1 := (mem_Phi.1 hγ).2
    refine ⟨vAut0 K (xuWUnit hp e), ?_, fun w => xuWUnit_induces hp e w⟩
    have hmem : vAut0 K (xuWUnit hp e) ∈ rootSet0 K :=
      ⟨γ, hp, hpr, e, fun w => xuWUnit_induces hp e w⟩
    exact Subgroup.subset_closure hmem
  · refine ⟨1, one_mem _, ?_⟩
    have h1 : xE γ e = 1 := by
      rw [he hp]
      exact e7Data_valid.xm_zero K γ
    rw [h1]
    exact IndW.one

theorem indW_prodX_mem {c : (Fin (Tag.rank .E7) → ℤ) → K} :
    ∀ L : List (Fin (Tag.rank .E7) → ℤ), (∀ γ ∈ L, γ ∈ Phi b0) → (∀ γ ∈ L, γ ∉ Perp → c γ = 0) →
      ∃ x ∈ rootRad0 K, IndW (prodX L c) x := by
  intro L
  induction L with
  | nil =>
    intro _ _
    refine ⟨1, one_mem _, ?_⟩
    have h : prodX [] c = 1 := by simp [prodX]
    rw [h]
    exact IndW.one
  | cons γ L ih =>
    intro hL hc
    obtain ⟨x, hx, hxI⟩ := ih (fun δ hδ => hL δ (by simp [hδ]))
      (fun δ hδ hnp => hc δ (by simp [hδ]) hnp)
    obtain ⟨y, hy, hyI⟩ := d6rad2_factor (hL γ (by simp)) (e := c γ) (fun hnp => hc γ (by simp) hnp)
    refine ⟨y * x, mul_mem hy hx, ?_⟩
    rw [d6rad2_prodX_cons]
    exact hyI.mul hxI

theorem mem_rootRad0_iff {x : W K ≃ₗ[K] W K} :
    x ∈ rootRad0 K ↔ ∃ y : Gp K, y ∈ UA K b0 ∧ y ∈ LamG K ∧ IndW y x := by
  constructor
  · intro hx
    unfold rootRad0 at hx
    induction hx using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨γ, hγ, hpr, c, hs'⟩ := hs
      have hγ' : IsRoot .E7 γ ∧ MinData.toWeight γ ⬝ᵥ theta = 0 := hγ
      have hγΦ : γ ∈ Phi b0 := mem_Phi.2 ⟨hγ'.1, hpr⟩
      exact ⟨xE γ c, Subgroup.subset_closure ⟨γ, hγΦ, c, rfl⟩,
        mem_LamG.2 (xu_mem_Lam hγ c), fun w => hs' w⟩
    | one => exact ⟨1, one_mem _, one_mem _, IndW.one⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨y, hy, hyL, hI⟩ := iha
      obtain ⟨y', hy', hyL', hI'⟩ := ihb
      exact ⟨y * y', mul_mem hy hy', mul_mem hyL hyL', hI.mul hI'⟩
    | inv a _ iha =>
      obtain ⟨y, hy, hyL, hI⟩ := iha
      exact ⟨y⁻¹, inv_mem hy, inv_mem hyL, hI.inv⟩
  · rintro ⟨y, hyU, hyL, hyI⟩
    obtain ⟨c, hc⟩ := mem_UA_iff.1 hyU
    subst hc
    obtain ⟨x', hx', hI'⟩ := indW_prodX_mem (c := c) (Phi b0).toList
      (fun γ hγ => Finset.mem_toList.1 hγ)
      (fun γ hγ hnp => coef_zero_off_perp hyL (Finset.mem_toList.1 hγ) hnp)
    rw [IndW.unique hyI hI']
    exact hx'

private theorem d6rad2_coord (P : Finset (Fin (Tag.rank .E7) → ℤ))
    (hP : ∀ γ ∈ P, γ ∈ Phi b0 ∧ γ ∈ Perp) (c : (Fin (Tag.rank .E7) → ℤ) → K)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ P) {b : Fin e7Data.d} (hb : pr b δ = -1)
    {b' : Idx0} (hb' : (b' : Fin e7Data.d) = b) {x : W K ≃ₗ[K] W K}
    (hx : IndW (prodX P.toList c) x) :
    emb K (x (Finsupp.single b' 1)) (shift δ b) = c δ := by
  have hL : ∀ γ ∈ P.toList, IsRoot .E7 γ ∧ pr b0 γ = 1 := fun γ hγ =>
    mem_Phi.1 (hP γ (Finset.mem_toList.1 hγ)).1
  have hδP : IsRoot .E7 δ ∧ MinData.toWeight δ ⬝ᵥ theta = 0 := (hP δ hδ).2
  have hc := coef_prod b0 P.toList hL (Finset.nodup_toList P) c b δ hδP.1 hb
  rw [if_pos (Finset.mem_toList.2 hδ)] at hc
  rw [hx (Finsupp.single b' 1), emb_single, hb', endoE_prodX, hc]

private theorem d6rad2_card_aux [Finite K] (P : Finset (Fin (Tag.rank .E7) → ℤ))
    (hP : ∀ γ ∈ P, γ ∈ Phi b0 ∧ γ ∈ Perp) :
    Nat.card K ^ P.card ≤ Nat.card ↥(rootRad0 K) := by
  haveI : Finite (W K) := Finite.of_equiv (Idx0 → K) Finsupp.equivFunOnFinite.symm
  haveI : Finite (W K ≃ₗ[K] W K) :=
    Finite.of_injective (fun e : W K ≃ₗ[K] W K => (e : W K → W K)) LinearEquiv.coe_injective
  have hX : ∀ f : ↥P → K, ∃ x ∈ rootRad0 K,
      IndW (prodX P.toList (fun γ => if h : γ ∈ P then f ⟨γ, h⟩ else 0)) x := by
    intro f
    refine indW_prodX_mem (c := fun γ => if h : γ ∈ P then f ⟨γ, h⟩ else 0) P.toList
      (fun γ hγ => (hP γ (Finset.mem_toList.1 hγ)).1) ?_
    intro γ hγ hnp
    exact absurd (hP γ (Finset.mem_toList.1 hγ)).2 hnp
  choose X hX1 hX2 using hX
  have hcf : ∀ (f : ↥P → K) (δ : ↥P),
      (fun γ : Fin (Tag.rank .E7) → ℤ => if h : γ ∈ P then f ⟨γ, h⟩ else 0) δ.1 = f δ :=
    fun f δ => dif_pos δ.2
  let F : (↥P → K) → ↥(rootRad0 K) := fun f => ⟨X f, hX1 f⟩
  have hF : Function.Injective F := by
    intro f g hfg
    have hXfg : X f = X g := congrArg Subtype.val hfg
    funext δ
    have hδP : IsRoot .E7 δ.1 ∧ MinData.toWeight δ.1 ⬝ᵥ theta = 0 := (hP δ.1 δ.2).2
    obtain ⟨b, hb0, hb⟩ := exists_idx0_move δ.1 hδP.1 hδP.2
    obtain ⟨b', hb'⟩ : ∃ b' : Idx0, (b' : Fin e7Data.d) = b := ⟨⟨b, mem_idx0.2 hb0⟩, rfl⟩
    have h1 := d6rad2_coord P hP (fun γ => if h : γ ∈ P then f ⟨γ, h⟩ else 0) δ.2 hb hb' (hX2 f)
    have h2 := d6rad2_coord P hP (fun γ => if h : γ ∈ P then g ⟨γ, h⟩ else 0) δ.2 hb hb' (hX2 g)
    rw [hXfg] at h1
    exact (hcf f δ).symm.trans (h1.symm.trans (h2.trans (hcf g δ)))
  calc Nat.card K ^ P.card = Nat.card (↥P → K) := by rw [Nat.card_fun, Nat.card_eq_finsetCard]
    _ ≤ Nat.card ↥(rootRad0 K) := Nat.card_le_card_of_injective F hF

theorem card_rootRad0_ge [Finite K] : Nat.card K ^ 15 ≤ Nat.card ↥(rootRad0 K) := by
  have hP : ∀ γ ∈ (rootFinset .E7).filter (fun γ => MinData.toWeight γ ⬝ᵥ theta = 0 ∧ pr b0 γ = 1),
      γ ∈ Phi b0 ∧ γ ∈ Perp := by
    intro γ hγ
    rw [Finset.mem_filter, mem_rootFinset] at hγ
    exact ⟨mem_Phi.2 ⟨hγ.1, hγ.2.2⟩,
      show IsRoot .E7 γ ∧ MinData.toWeight γ ⬝ᵥ theta = 0 from ⟨hγ.1, hγ.2.1⟩⟩
  have h := d6rad2_card_aux (K := K) _ hP
  rw [phiP_card] at h
  exact h

end CFSG.RankThree.GF2n.Smith81.D6X
