module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec5SLDual
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualField

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.comm_eq_one_V₁ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    {u v : G} (hu : u ∈ V₁) (hv : v ∈ V₁) : u * v = v * u := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, -, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨F, hFfield, hFfin, hFcard, φ', hrange, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φ, hΦ, hΦ₁, -⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ' hn
    hrange (by rw [h.card, hFcard]) Φ hΦ
  have hW₁ : ∀ e : M₀.E, e ∈ M₀.img V₁ ↔ (C.Ψ e).2 = 0 := fun e => by
    rw [hCΦ]
    exact hΦ₁ e
  have hBφ : ∀ t : ↥(H0 M Z), ∀ e f : M₀.E, M₀.B (φ t e) (φ t f) = M₀.B e f := by
    intro t e f
    have e1 : φ t (e + f) = φ t e + φ t f := map_add (φ t) e f
    have h1 := M₀.Qf_add (φ t e) (φ t f)
    rw [← e1, hφiso, hφiso, hφiso] at h1
    linear_combination (M₀.Qf_add e f) - h1
  have hβ : ∀ x y : Fin n → F, M₀.B (C.inl x) (C.inl y) = 0 := by
    let β : (Fin n → F) →+ (Fin n → F) →+ GaloisField 2 m := AddMonoidHom.mk'
      (fun x => (M₀.B (C.inl x)).toAddMonoidHom.comp C.inl)
      (fun x x' => by
        ext y
        simp [map_add])
    have hinv : ∀ g : GL (Fin n) F, g ∈ StatedSL n F → ∀ x y : Fin n → F,
        β ((g : Matrix (Fin n) (Fin n) F) *ᵥ x) ((g : Matrix (Fin n) (Fin n) F) *ᵥ y) =
          β x y := by
      intro g hg x y
      obtain ⟨s, hs⟩ := NatDualCoord.exists_eq_of_mem_statedSL hrange hg
      have hx : ∀ z : Fin n → F, C.inl ((g : Matrix (Fin n) (Fin n) F) *ᵥ z) =
          φ (Subgroup.inclusion hSH s) (C.inl z) := by
        intro z
        rw [← hs]
        exact (C.ρ_inl s z).symm
      show M₀.B (C.inl ((g : Matrix (Fin n) (Fin n) F) *ᵥ x))
          (C.inl ((g : Matrix (Fin n) (Fin n) F) *ᵥ y)) = M₀.B (C.inl x) (C.inl y)
      rw [hx x, hx y]
      exact hBφ _ _ _
    intro x y
    exact biadd_eq_zero_of_SL hn β hinv x y
  have hπ : ∀ w ∈ V₁, M₀.π w = C.inl (C.Ψ (M₀.π w)).1 := by
    intro w hw
    have h2 : (C.Ψ (M₀.π w)).2 = 0 := (hW₁ _).mp (M₀.pi_mem_img hw (hV₁Q hw))
    have h3 := C.eq_inl_add_inr (M₀.π w)
    rw [h2, map_zero, add_zero] at h3
    exact h3
  have hcomm : ⁅u, v⁆ = 1 := by
    rw [GM.comm_eq_one_iff h (hV₁Q hu) (hV₁Q hv), hπ u hu, hπ v hv]
    exact hβ _ _
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

theorem LinSetup.comm_eq_one_V₂ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    {u v : G} (hu : u ∈ V₂) (hv : v ∈ V₂) : u * v = v * u :=
  LinSetup.comm_eq_one_V₁ hc hS.symm hn hu hv

end CFSG.RankThree.GF2n.Smith81
