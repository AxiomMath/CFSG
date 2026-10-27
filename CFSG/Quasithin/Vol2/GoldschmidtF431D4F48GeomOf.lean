module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Kappa
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexGraph
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F48Gen CFSG.D4Hex
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion

structure HexGeomOf (S : LieSetting.{0, 0}) (K : Type) [Group K] [MulAction K (Fin 819)]
    [MulAction K (Fin 2457)] (Φ : K →* S.ι.G0) (Ψ : S.ι.G0 →* K) where
  Φ_Ψ : ∀ g, Φ (Ψ g) = g
  hm : S.m = 6
  e : S.ι.Γ ≃ HexVtx
  e_xv : e S.ι.xv = Sum.inl pt0
  e_lv : e S.ι.lv = Sum.inr 0
  e_smul : ∀ (g : K) (a : S.ι.Γ), e (Φ g • a) = g • e a
  e_adj : ∀ a b : S.ι.Γ, S.ι.graph.Adj a b ↔ hexGraph.Adj (e a) (e b)
  dist_lay : ∀ p : Fin 819, hexGraph.dist (Sum.inl pt0) (Sum.inl p) = lay0[(p : ℕ)]!

namespace HexGeomOf

variable {S : LieSetting.{0, 0}} {K : Type} [Group K] [MulAction K (Fin 819)]
  [MulAction K (Fin 2457)] {Φ : K →* S.ι.G0} {Ψ : S.ι.G0 →* K} (Gm : HexGeomOf S K Φ Ψ)

theorem e_inl (z : Pt S.ι) : ∃ m : Fin 819, Gm.e (Sum.inl z) = Sum.inl m := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₀ (G₂ := S.ι.φ2.range) z
  have h1 := Gm.e_smul (Ψ g) (CosetGeom.γ₀ _ _ _)
  rw [Gm.Φ_Ψ] at h1
  refine ⟨Ψ g • pt0, ?_⟩
  rw [show (Sum.inl z : S.ι.Γ) = g • CosetGeom.γ₀ _ _ _ from hg.symm, h1]
  show _ • Gm.e S.ι.xv = _
  rw [Gm.e_xv]
  rfl

theorem e_inr (w : S.ι.G0 ⧸ S.ι.φ2.range.subgroupOf (S.ι.φ1.range ⊔ S.ι.φ2.range)) :
    ∃ k : Fin 2457, Gm.e (Sum.inr w) = Sum.inr k := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₁ (G₁ := S.ι.φ1.range) w
  have h1 := Gm.e_smul (Ψ g) (CosetGeom.γ₁ _ _ _)
  rw [Gm.Φ_Ψ] at h1
  refine ⟨Ψ g • (0 : Fin 2457), ?_⟩
  rw [show (Sum.inr w : S.ι.Γ) = g • CosetGeom.γ₁ _ _ _ from hg.symm, h1]
  show _ • Gm.e S.ι.lv = _
  rw [Gm.e_lv]
  rfl

@[expose] noncomputable def κF (z : Pt S.ι) : Fin 819 := (Gm.e_inl z).choose

theorem e_κF (z : Pt S.ι) : Gm.e (Sum.inl z) = Sum.inl (Gm.κF z) :=
  (Gm.e_inl z).choose_spec

theorem κF_injective : Function.Injective Gm.κF := by
  intro z z' hzz
  have := Gm.e.injective ((Gm.e_κF z).trans ((congrArg Sum.inl hzz).trans (Gm.e_κF z').symm))
  exact Sum.inl_injective this

theorem κF_surjective : Function.Surjective Gm.κF := by
  intro m
  rcases hv : Gm.e.symm (Sum.inl m) with z | w
  · refine ⟨z, ?_⟩
    have := Gm.e_κF z
    rw [← hv, Equiv.apply_symm_apply] at this
    exact (Sum.inl_injective this).symm
  · obtain ⟨k, hk⟩ := Gm.e_inr w
    have := congrArg Gm.e hv
    rw [Equiv.apply_symm_apply, hk] at this
    exact absurd this Sum.inl_ne_inr

@[expose] noncomputable def κ : Pt S.ι ≃ Fin 819 :=
  Equiv.ofBijective Gm.κF ⟨Gm.κF_injective, Gm.κF_surjective⟩

theorem e_κ (z : Pt S.ι) : Gm.e (Sum.inl z) = Sum.inl (Gm.κ z) := Gm.e_κF z

theorem κ_phi (x : K) (z : Pt S.ι) : Gm.κ (Φ x • z) = x • Gm.κ z := by
  have h1 := Gm.e_smul x (Sum.inl z)
  rw [CosetGeom.smul_inl, Gm.e_κ, Gm.e_κ] at h1
  exact Sum.inl_injective h1

theorem κ_smul (g : S.ι.G0) (z : Pt S.ι) : Gm.κ (g • z) = Ψ g • Gm.κ z := by
  have := Gm.κ_phi (Ψ g) z
  rwa [Gm.Φ_Ψ] at this

theorem κ_one : Gm.κ ((1 : S.ι.G0) : Pt S.ι) = pt0 := by
  have h := Gm.e_xv
  have h2 : Gm.e (Sum.inl ((1 : S.ι.G0) : Pt S.ι)) = Sum.inl pt0 := h
  rw [Gm.e_κ] at h2
  exact Sum.inl_injective h2

theorem κ_near (z : Pt S.ι) : Near S.m S.ι z ↔ lay0[((Gm.κ z : Fin 819) : ℕ)]! ≤ 4 := by
  let iso : S.ι.graph ≃g hexGraph := ⟨Gm.e, fun {a b} => (Gm.e_adj a b).symm⟩
  have hd := iso_dist iso S.ι.xv (Sum.inl z)
  have hd' : S.ι.graph.dist S.ι.xv (Sum.inl z) = lay0[((Gm.κ z : Fin 819) : ℕ)]! := by
    rw [← hd]
    show hexGraph.dist (Gm.e S.ι.xv) (Gm.e (Sum.inl z)) = _
    rw [Gm.e_xv, Gm.e_κ]
    exact Gm.dist_lay _
  show S.ι.graph.dist S.ι.xv (Sum.inl z) ≤ S.m - 2 ↔ _
  rw [hd', Gm.hm]

include Gm in
theorem toPerm_injective (hK : Function.Injective (MulAction.toPermHom K (Fin 819))) :
    Function.Injective (MulAction.toPermHom S.ι.G0 (Pt S.ι)) := by
  have hΨ : Function.Injective Ψ := fun a b h => by
    rw [← Gm.Φ_Ψ a, ← Gm.Φ_Ψ b, h]
  exact toPerm_injective_of_kappa S Gm.κ ((MulAction.toPermHom K (Fin 819)).comp Ψ)
    (fun g z => Gm.κ_smul g z) (hK.comp hΨ)

include Gm in
theorem hNtr_of (hnt : ∀ m : Fin 819, ∃ g ∈ S.N, Ψ g • pt0 = m) :
    ∀ v : S.ι.Γ, CosetGeom.vtype v = false → ∃ g ∈ S.N, g • S.ι.xv = v := by
  intro v hv
  rcases v with z | w
  swap
  · simp [CosetGeom.vtype] at hv
  obtain ⟨g, hgN, hg⟩ := hnt (Gm.κ z)
  refine ⟨g, hgN, ?_⟩
  show g • (Sum.inl ((1 : S.ι.G0) : Pt S.ι) : S.ι.Γ) = Sum.inl z
  rw [CosetGeom.smul_inl]
  congr 1
  apply Gm.κ.injective
  rw [Gm.κ_smul, Gm.κ_one, hg]

include Gm in
theorem hfix_of
    (h819 : ∀ w : Fin 819, (∀ b ∈ S.N ⊓ (stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv), Ψ b • w = w) →
      w = pt0) :
    ∀ v : S.ι.Γ, CosetGeom.vtype v = false →
      (∀ b ∈ S.N ⊓ (stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv), b • v = v) → v = S.ι.xv := by
  intro v hv hfix
  rcases v with w | w
  swap
  · simp [CosetGeom.vtype] at hv
  have hw : Gm.κ w = pt0 := by
    refine h819 _ fun b hb => ?_
    have h1 := hfix b hb
    rw [CosetGeom.smul_inl] at h1
    have h2 : b • w = w := Sum.inl_injective h1
    rw [← Gm.κ_smul, h2]
  have := Gm.κ.injective (hw.trans Gm.κ_one.symm)
  rw [this]
  rfl

end HexGeomOf

end CFSG.Quasithin.D4Hex
