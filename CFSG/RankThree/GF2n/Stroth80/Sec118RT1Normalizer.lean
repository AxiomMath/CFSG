module

public import CFSG.RankThree.GF2n.Stroth80.Sec118CommBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.mk_mem_normalizer_bar_LB_of_stab (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m : ℕ} {W₁ W₂ : Submodule K M₀.E}
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (hs₁ : ∀ w ∈ W₁, M₀.Qf w = 0) (hs₂ : ∀ w ∈ W₂, M₀.Qf w = 0)
    (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁) (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K)
    (hρr : ρ.range = StatedSp m K)
    (hρe : ∀ (s : ↥(XbarH M Q Z B)) (w : ↥W₁),
      b.equivFun ⟨φ s (w : M₀.E), hW₁ s (w : M₀.E) w.2⟩ =
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ b.equivFun w)
    {a : G} (haL : a ∈ LB M Q B) (hA : IsA2 Q Z a) (haX : a ∈ XbarPre M Q Z B)
    {s : G} (hsM : s ∈ M) (hsX : s ∈ XbarPre M Q Z B) (c : K)
    (hstab : ∀ v ∈ LinearMap.range (Matrix.mulVecLin
      (((ρ ⟨⟨a, XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)),
      (ρ ⟨⟨s, XbarPre_le_H0 hc hsX⟩, (mem_XbarH_iff hc _).mpr hsX⟩ :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = c • v) :
    (QuotientGroup.mk (⟨s, hsM⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  classical
  have haH : a ∈ H0 M Z := XbarPre_le_H0 hc haX
  have hsH : s ∈ H0 M Z := XbarPre_le_H0 hc hsX
  obtain ⟨e₁, e₂, he₁, he₂⟩ := hc.exists_coords_of_global h φ hφπ hsup hW₁ hW₂ hs₁ hs₂ b ρ hρr hρe
  have hfix := hc.smul_range_of_stab h φ hφπ ha2 hsup hW₁ hW₂ ρ e₁ e₂ he₁ he₂ haL haX c
    (s := ⟨⟨s, hsH⟩, (mem_XbarH_iff hc _).mpr hsX⟩) hstab
  obtain ⟨b₀, -, -, hB, -, -⟩ := hc.dictB h
  refine hc.mk_mem_normalizer_bar_LB_of_fix_line hB hsM
    (T := (φ ⟨s, hsH⟩ : M₀.E →ₗ[K] M₀.E)) (fun y hy => hφπ ⟨s, hsH⟩ y hy) (μ := c) ?_
  obtain ⟨y, hyB, hyQ, hyb⟩ := (hB b₀).mpr ⟨1, (one_smul K b₀).symm⟩
  have hyD : y ∈ (⁅Q, Subgroup.zpowers a⁆ ⊔ Z : Subgroup G) := hc.B_le_commutator_of_a2 haL hA hyB
  have hrange : b₀ ∈ LinearMap.range
      (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) := by
    refine (hc.mem_img_zpowers_sup_iff φ hφπ haH hA.2.2.1 b₀).mp ?_
    exact ⟨y, hyD, hyQ, hyb⟩
  exact hfix b₀ hrange

end CFSG.RankThree.GF2n.Stroth80
