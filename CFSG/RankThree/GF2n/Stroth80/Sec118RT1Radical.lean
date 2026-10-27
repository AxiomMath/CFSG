module

public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Normalizer
public import CFSG.ClassicalGroups.Symplectic.PointRadicalNormalTwo
import CFSG.RankThree.GF2n.Stroth80.Sec37CommTrans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.rho_LB_le_LspGL_or_eq (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m : ℕ} {W₁ W₂ : Submodule K M₀.E}
    (hdisj : W₁ ⊓ W₂ = ⊥)
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (hs₁ : ∀ w ∈ W₁, M₀.Qf w = 0) (hs₂ : ∀ w ∈ W₂, M₀.Qf w = 0)
    (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁) (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K)
    (hρr : ρ.range = StatedSp m K)
    (hρk : ∀ s : ↥(XbarH M Q Z B), ρ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q)
    (hρe : ∀ (s : ↥(XbarH M Q Z B)) (w : ↥W₁),
      b.equivFun ⟨φ s (w : M₀.E), hW₁ s (w : M₀.E) w.2⟩ =
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ b.equivFun w)
    {a : G} (haL : a ∈ LB M Q B) (hA : IsA2 Q Z a) (haX : a ∈ XbarPre M Q Z B)
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (hrange : LinearMap.range (Matrix.mulVecLin
      (((ρ ⟨⟨a, XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)) = Submodule.span K {u}) :
    (∀ x : ↥(XbarH M Q Z B), ((x : ↥(H0 M Z)) : G) ∈ LB M Q B →
      (ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u) ∧
    (∀ x : ↥(XbarH M Q Z B), ((x : ↥(H0 M Z)) : G) ∈ LB M Q B → ρ x ∈ LspGL m K u) ∧
    ((∀ x : ↥(XbarH M Q Z B), ((x : ↥(H0 M Z)) : G) ∈ LB M Q B →
        ∃ c : K, ∀ v : Fin m ⊕ Fin m → K,
          (ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v + (c * spForm m K v u) • u) ∨
      (∀ g ∈ LspGL m K u, ∃ x : ↥(XbarH M Q Z B),
        ((x : ↥(H0 M Z)) : G) ∈ LB M Q B ∧ ρ x = g)) := by
  classical
  have haH : a ∈ H0 M Z := XbarPre_le_H0 hc haX
  set sa : ↥(XbarH M Q Z B) := ⟨⟨a, haH⟩, (mem_XbarH_iff hc _).mpr haX⟩ with hsa
  obtain ⟨e₁, e₂, he₁, he₂⟩ := hc.exists_coords_of_global h φ hφπ hsup hW₁ hW₂ hs₁ hs₂ b ρ hρr hρe
  obtain ⟨b₀, hb00, -, hB, -, -⟩ := hc.dictB h
  obtain ⟨y, hyB, hyQ, hyb⟩ := (hB b₀).mpr ⟨1, (one_smul K b₀).symm⟩
  have hyD : y ∈ (⁅Q, Subgroup.zpowers a⁆ ⊔ Z : Subgroup G) :=
    hc.B_le_commutator_of_a2 haL hA hyB
  have hrange0 : b₀ ∈ LinearMap.range
      (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) :=
    (hc.mem_img_zpowers_sup_iff φ hφπ haH hA.2.2.1 b₀).mp ⟨y, hyD, hyQ, hyb⟩
  have hdecomp : ∃ c₁ c₂ : K, b₀ = c₁ • ((e₁.symm u : W₁) : M₀.E) +
      c₂ • ((e₂.symm u : W₂) : M₀.E) := by
    rw [hc.range_sub_one_eq_map_cmComm h φ hφπ ha2 haL haH, ← hsup, Submodule.map_sup,
      map_sub_one_eq_span_of_range e₁ ((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
        (hW₁ sa) _ (he₁ sa) hrange,
      map_sub_one_eq_span_of_range e₂ ((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
        (hW₂ sa) _ (he₂ sa) hrange] at hrange0
    obtain ⟨x₁, hx₁, x₂, hx₂, hsum⟩ := Submodule.mem_sup.mp hrange0
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hx₁
    obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.mp hx₂
    exact ⟨c₁, c₂, hsum.symm⟩
  have hu₁ : ∀ x : ↥(XbarH M Q Z B), φ x ((e₁.symm u : W₁) : M₀.E) =
      ((e₁.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) : W₁) : M₀.E) := by
    intro x
    have h1 := he₁ x (e₁.symm u)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : (⟨φ x ((e₁.symm u : W₁) : M₀.E), hW₁ x _ (e₁.symm u).2⟩ : W₁) =
        e₁.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
      apply e₁.injective
      rw [h1, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hu₂ : ∀ x : ↥(XbarH M Q Z B), φ x ((e₂.symm u : W₂) : M₀.E) =
      ((e₂.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) : W₂) : M₀.E) := by
    intro x
    have h1 := he₂ x (e₂.symm u)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : (⟨φ x ((e₂.symm u : W₂) : M₀.E), hW₂ x _ (e₂.symm u).2⟩ : W₂) =
        e₂.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
      apply e₂.injective
      rw [h1, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hA2 : ∀ x : ↥(XbarH M Q Z B), ((x : ↥(H0 M Z)) : G) ∈ LB M Q B →
      (ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u := by
    intro x hx
    obtain ⟨hTb, -⟩ := hc.LB_act_fix_line h hB hx
      (T := ((φ (x : ↥(H0 M Z)) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E))
      (fun z hz => hφπ (x : ↥(H0 M Z)) z hz)
    obtain ⟨c₁, c₂, hb⟩ := hdecomp
    have h1 : φ x b₀ = b₀ := hTb
    rw [hb, map_add, map_smul, map_smul, hu₁, hu₂] at h1
    let z₁ : W₁ := c₁ • (e₁.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) -
      e₁.symm u)
    let z₂ : W₂ := c₂ • (e₂.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) -
      e₂.symm u)
    have hsum : (z₁ : M₀.E) + (z₂ : M₀.E) = 0 := by
      have e1 : (z₁ : M₀.E) = c₁ • ((e₁.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
          *ᵥ u) : W₁) : M₀.E) - c₁ • ((e₁.symm u : W₁) : M₀.E) := by
        simp only [z₁, Submodule.coe_smul, Submodule.coe_sub, smul_sub]
      have e2 : (z₂ : M₀.E) = c₂ • ((e₂.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
          *ᵥ u) : W₂) : M₀.E) - c₂ • ((e₂.symm u : W₂) : M₀.E) := by
        simp only [z₂, Submodule.coe_smul, Submodule.coe_sub, smul_sub]
      rw [e1, e2]
      calc _ = (c₁ • ((e₁.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) : W₁) :
            M₀.E) + c₂ • ((e₂.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) :
              W₂) : M₀.E)) - (c₁ • ((e₁.symm u : W₁) : M₀.E) + c₂ • ((e₂.symm u : W₂) : M₀.E)) := by
            abel
        _ = 0 := sub_eq_zero.mpr h1
    have hz₁ : (z₁ : M₀.E) ∈ W₁ ⊓ W₂ := ⟨z₁.2, by
      have : (z₁ : M₀.E) = -(z₂ : M₀.E) := eq_neg_of_add_eq_zero_left hsum
      rw [this]; exact W₂.neg_mem z₂.2⟩
    rw [hdisj, Submodule.mem_bot] at hz₁
    have hz₁0 : z₁ = 0 := Subtype.ext hz₁
    have hz₂0 : z₂ = 0 := by
      apply Subtype.ext
      have : (z₂ : M₀.E) = 0 := by rw [hz₁, zero_add] at hsum; exact hsum
      exact this
    by_cases hc₁ : c₁ = 0
    · by_cases hc₂ : c₂ = 0
      · exact absurd (by rw [hb, hc₁, hc₂]; simp) hb00
      · have : e₂.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) - e₂.symm u = 0 :=
          (smul_eq_zero.mp hz₂0).resolve_left hc₂
        exact e₂.symm.injective (sub_eq_zero.mp this)
    · have : e₁.symm ((ρ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) - e₁.symm u = 0 :=
        (smul_eq_zero.mp hz₁0).resolve_left hc₁
      exact e₁.symm.injective (sub_eq_zero.mp this)
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hK : 2 < Nat.card K := by
    have h4 := hc.hyp.q4
    rw [h.card]
    omega
  let LBX : Subgroup ↥(XbarH M Q Z B) :=
    (LB M Q B).comap (((H0 M Z).subtype).comp (XbarH M Q Z B).subtype)
  let S : Subgroup (GL (Fin m ⊕ Fin m) K) := LBX.map ρ
  have hLBX : ∀ x : ↥(XbarH M Q Z B), x ∈ LBX ↔ ((x : ↥(H0 M Z)) : G) ∈ LB M Q B :=
    fun x => Iff.rfl
  have hSmem : ∀ g, g ∈ S ↔ ∃ x : ↥(XbarH M Q Z B),
      ((x : ↥(H0 M Z)) : G) ∈ LB M Q B ∧ ρ x = g := fun g => by
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hSsp : S ≤ StatedSp m K := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := (hSmem g).mp hg
    rw [← hρr]
    exact ⟨x, rfl⟩
  have hSfix : ∀ g ∈ S, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := (hSmem g).mp hg
    exact hA2 x hx
  have hS2 : IsPGroup 2 S := by
    intro g
    obtain ⟨x, hx, hxg⟩ := (hSmem g).mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    have hx2 : ρ (x ^ 2) = 1 := by
      rw [hρk]
      exact hc.sq_mem_Q_of_mem_LB hx
    show (g : GL (Fin m ⊕ Fin m) K) ^ (2 ^ 1) = 1
    rw [← hxg, pow_one, ← map_pow]
    exact hx2
  have hSn : ∀ g ∈ StatedSp m K,
      (∃ c : K, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ t ∈ S, g * t * g⁻¹ ∈ S := by
    intro g hg ⟨c, hcu⟩ t ht
    obtain ⟨x, hx, rfl⟩ := (hSmem t).mp ht
    obtain ⟨s, hs⟩ : g ∈ ρ.range := by rw [hρr]; exact hg
    have hsX : ((s : ↥(H0 M Z)) : G) ∈ XbarPre M Q Z B := (mem_XbarH_iff hc _).mp s.2
    have hsM : ((s : ↥(H0 M Z)) : G) ∈ M := s.1.2.1
    have hstab : ∀ v ∈ LinearMap.range (Matrix.mulVecLin
        (((ρ ⟨⟨a, XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩ : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)),
        (ρ ⟨⟨(s : ↥(H0 M Z)), XbarPre_le_H0 hc hsX⟩, (mem_XbarH_iff hc _).mpr hsX⟩ :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = c • v := by
      intro v hv
      rw [hrange] at hv
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hv
      have hρs : (ρ ⟨⟨(s : ↥(H0 M Z)), XbarPre_le_H0 hc hsX⟩, (mem_XbarH_iff hc _).mpr hsX⟩ :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u := by
        have : (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u := by
          rw [hs]; exact hcu
        exact this
      rw [Matrix.mulVec_smul, hρs, smul_comm]
    have hnorm := hc.mk_mem_normalizer_bar_LB_of_stab h φ hφπ ha2 hsup hW₁ hW₂ hs₁ hs₂ b ρ hρr
      hρe haL hA haX hsM hsX c hstab
    have hxM : ((x : ↥(H0 M Z)) : G) ∈ M := x.1.2.1
    have hxbar : (QuotientGroup.mk' (Q.subgroupOf M) ⟨((x : ↥(H0 M Z)) : G), hxM⟩ : Mbar M Q) ∈
        bar M Q (LB M Q B) := (Tim37.mk_mem_bar_iff' hQLB ⟨((x : ↥(H0 M Z)) : G), hxM⟩).mpr hx
    have hconj := (Subgroup.mem_normalizer_iff.mp hnorm _).mp hxbar
    have hsxs : ((s : ↥(H0 M Z)) : G) * ((x : ↥(H0 M Z)) : G) * ((s : ↥(H0 M Z)) : G)⁻¹ ∈
        LB M Q B := by
      have hM' : ((s : ↥(H0 M Z)) : G) * ((x : ↥(H0 M Z)) : G) * ((s : ↥(H0 M Z)) : G)⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem hsM hxM) (M.inv_mem hsM)
      refine (Tim37.mk_mem_bar_iff' hQLB ⟨_, hM'⟩).mp ?_
      have e : (⟨((s : ↥(H0 M Z)) : G) * ((x : ↥(H0 M Z)) : G) * ((s : ↥(H0 M Z)) : G)⁻¹, hM'⟩ :
          ↥M) = ⟨((s : ↥(H0 M Z)) : G), hsM⟩ * ⟨((x : ↥(H0 M Z)) : G), hxM⟩ *
            ⟨((s : ↥(H0 M Z)) : G), hsM⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact hconj
    refine (hSmem _).mpr ⟨s * x * s⁻¹, hsxs, ?_⟩
    rw [map_mul, map_mul, map_inv, hs]
  obtain ⟨hSL, hdich⟩ := le_LspGL_and_transvections_or_eq hK hu S hSsp hSfix hS2 hSn
  refine ⟨hA2, fun x hx => hSL ((hSmem _).mpr ⟨x, hx, rfl⟩), ?_⟩
  rcases hdich with h1 | h1
  · left
    intro x hx
    exact h1 (ρ x) ((hSmem _).mpr ⟨x, hx, rfl⟩)
  · right
    intro g hg
    have : g ∈ S := h1 ▸ hg
    obtain ⟨x, hx, hxg⟩ := (hSmem g).mp this
    exact ⟨x, hx, hxg⟩

end CFSG.RankThree.GF2n.Stroth80
