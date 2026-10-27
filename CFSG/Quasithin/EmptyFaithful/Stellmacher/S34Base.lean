module

public import CFSG.Quasithin.EmptyFaithful.SzF53MConj
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OneLtBMin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1Tri

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Cb (δ : Geo H M) : Subgroup G :=
  Vn δ ⊓ Subgroup.centralizer (oTwoRes (stab δ) : Set G)

omit [Finite G] in
theorem Cb_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Cb (g • δ) = conjSub (g : G) (Cb δ) := by
  unfold Cb
  rw [Vn_smul, stab_smul, ← conjSub_oTwoRes, conjSub_centralizer, ← conjSub_inf]

@[expose] def Good (δ : Geo H M) : Prop :=
  IsNatSec (stab δ) (Cb δ) (Vn δ) ∨ IsOrthSec (stab δ) (Cb δ) (Vn δ)

structure Glob (H M S : Subgroup G) : Prop where
  amalg : F53Amalgam H M S
  three_le : 3 ≤ bMin H M
  odd : Odd (bMin H M)
  crit : ∀ α : Geo H M, vtype α = true → bAt α = bMin H M
  central : ∀ δ : Geo H M, vtype δ = false → Zv δ ≤ centerOf (stab δ)
  prod : ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → vtype α = true →
    Qv α ⊔ Qv β = stab α ⊓ stab β

structure PD (δ δ' : Geo H M) : Prop where
  vδ : vtype δ = false
  vδ' : vtype δ' = false
  dist_eq : dist δ δ' + 1 = bMin H M
  not_le : ¬ Vn δ ≤ Qv δ'

@[expose] noncomputable def rk (δ : Geo H M) (y : G) : ℕ :=
  secIdx (Subgroup.zpowers y) (Cb δ) (Vn δ)

@[expose] def OverIn (X : Subgroup G) (g : G) : Prop :=
  g ∈ oTwoRes X ⊔ pCoreOf 2 X ∧ g ∉ pCoreOf 2 X ∧
    (g ^ 2 ∈ pCoreOf 2 X ∨ g ^ 3 ∈ pCoreOf 2 X)

@[expose] def OverInv (δ : Geo H M) (g : G) : Prop := OverIn (stab δ) g

@[expose] def NG (H M : Subgroup G) : Prop := ∀ δ : Geo H M, vtype δ = false → ¬ Good δ

omit [Finite G] in
theorem Good.of_vtype {δ δ' : Geo H M} (hδ : vtype δ = false) (hδ' : vtype δ' = false)
    (h : Good δ) : Good δ' := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hδ.trans hδ'.symm)
  unfold Good at h ⊢
  rw [stab_smul, Cb_smul, Vn_smul]
  rcases h with h | h
  · exact Or.inl (h.conj (g : G))
  · exact Or.inr (h.conj (g : G))

@[expose] def SameBlock (δ μ ν : Geo H M) : Prop :=
  ∃ P : Subgroup G, Qv δ ≤ P ∧ P ≤ stab δ ∧ P ≠ stab δ ∧ stab δ ⊓ stab μ ≤ P ∧
    stab δ ⊓ stab ν ≤ P

omit [Finite G] in
theorem Cb_le_Vn (δ : Geo H M) : Cb δ ≤ Vn δ := inf_le_left

theorem Zv_le_Vn (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) : Zv δ ≤ Vn δ := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hμ' : μ ∈ nbrs δ := hμ
  have h1 : Zv δ ≤ Zv μ := (Zv_eq_omegaOneCenter_inf hG.amalg hμ' (hG.central δ hδ)).2
  exact h1.trans (le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ hμ' le_rfl)

theorem Zv_le_Cb (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) : Zv δ ≤ Cb δ := by
  refine le_inf (Zv_le_Vn hG hδ) fun z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact ((hG.central δ hδ) hz).2 l (oTwoRes_le _ hl)

theorem Glob.of_crit (hA : F53Amalgam H M S) (h28 : Hss28At H M)
    {α β α' : Geo H M} (hc : IsCritData α β α') (hα : vtype α = true)
    (hz : ⁅Zv α, Zv α'⁆ = ⊥) : Glob H M S := by
  have hZβ : Zv β ≤ centerOf (stab β) := Zv_central_of_comm_eq_bot hA hc hz
  have hb : 1 < bMin H M := EmptyFaithful.Stellmacher.OrdinaryProofs.one_lt_bMin_of_s3_central
    hA hc hα hZβ
  obtain ⟨-, hodd, -⟩ := hss114_ab hA hc hz hb
  have hvβ : vtype β = false := by
    cases h : vtype β
    · rfl
    · exact absurd (hα.trans h.symm) (vtype_ne_of_adj hc.adj)
  have hcrit : ∀ α₁ : Geo H M, vtype α₁ = true → bAt α₁ = bMin H M := fun α₁ h1 =>
    (bAt_eq_of_vtype_eq (h1.trans hα.symm)).trans hc.bAt_eq
  refine ⟨hA, ?_, hodd, hcrit, fun δ hδ => ?_, fun α₁ β₁ hadj h1 => h28 hb α₁ β₁ hadj (hcrit α₁ h1)⟩
  · obtain ⟨k, hk⟩ := hodd
    omega
  · exact Zv_central_of_vtype_eq hA (hvβ.trans hδ.symm) hZβ

end S34

end F53.Stellmacher

end CFSG.Quasithin
