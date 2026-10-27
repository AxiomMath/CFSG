module

public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G10Stmts
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_of_mem_span_singleton' {c x y : V} (hx : x ∈ Submodule.span (ZMod 2) {c})
    (hy : y ∈ Submodule.span (ZMod 2) {c}) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : y = x := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rcases hc a with rfl | rfl
  · exact absurd (zero_smul _ _) hx0
  · rcases hc b with rfl | rfl
    · exact absurd (zero_smul _ _) hy0
    · rfl

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem le_normalClosure_hat {a : GLV V} (ha : a ∈ X) {J : Submodule (ZMod 2) V}
    (hJ : IsIrr (normalClosure Γ L) J) (hfaith : FaithfulOn (normalClosure Γ L) J)
    (haJ : conjSub a J = J) (htr : ∃ c : V, InducesTransvection a J c) :
    normalClosure Γ L ≤
      normalClosure (normalClosure Γ L ⊔ Subgroup.zpowers a) (Subgroup.zpowers a) := by
  set H := normalClosure Γ L with hH
  set K := H ⊔ Subgroup.zpowers a with hK
  set T := normalClosure K (Subgroup.zpowers a) with hT
  have hLΓ : L ≤ Γ := hyp.component.1
  have hHΓ : H ≤ Γ := normalClosure_le hLΓ
  have haΓ : a ∈ Γ := hyp.X_le ha
  have hKΓ : K ≤ Γ := sup_le hHΓ ((Subgroup.zpowers_le).2 haΓ)
  have hHK : H ≤ K := le_sup_left
  have haK : a ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hTK : T ≤ K := normalClosure_le ((Subgroup.zpowers_le).2 haK)
  have hTnorm : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T := normalClosure_normal K _
  have haT : a ∈ T :=
    Subgroup.subset_closure ⟨1, K.one_mem, a, Subgroup.mem_zpowers a, by simp⟩
  have hsubT : IsSubnormal T K := by
    refine IsSubnormal.step hTK ?_ (IsSubnormal.refl K)
    rw [Subgroup.normal_subgroupOf_iff hTK]
    intro t k ht hk
    exact hTnorm k hk t ht
  set C : Subgroup (GLV V) := H ⊓ Subgroup.centralizer (T : Set (GLV V)) with hC
  have hCnorm : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C := by
    intro h hh c hc
    refine ⟨normalClosure_conj (hHΓ hh) hc.1, ?_⟩
    show h * c * h⁻¹ ∈ Subgroup.centralizer (T : Set (GLV V))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : h⁻¹ * t * h⁻¹⁻¹ ∈ T := hTnorm h⁻¹ (K.inv_mem (hHK hh)) t ht
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ ht'
    simp only [inv_inv] at h1
    calc t * (h * c * h⁻¹) = h * ((h⁻¹ * t * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * t * h)) * h⁻¹ := by rw [h1]
      _ = h * c * h⁻¹ * t := by group
  have hCbot : C = ⊥ := by
    obtain ⟨c, hcomm', u₀, hu₀, hau₀⟩ := htr
    set w : V := a u₀ - u₀ with hw
    have hwJ : w ∈ J := by
      have h1 : a u₀ ∈ conjSub a J := apply_mem_conjSub hu₀
      rw [haJ] at h1
      exact J.sub_mem h1 hu₀
    have hw0 : w ≠ 0 := fun h => hau₀ (sub_eq_zero.1 h)
    have hwspan : w ∈ Submodule.span (ZMod 2) {c} := hcomm' u₀ hu₀
    have hwC : ∀ c' ∈ C, c' w = w := by
      intro c' hc'
      have hac : a * c' = c' * a := Subgroup.mem_centralizer_iff.1 hc'.2 a haT
      have hc'u : c' u₀ ∈ J := hJ.1 c' hc'.1 u₀ hu₀
      have h1 : c' w = a (c' u₀) - c' u₀ := by
        have := congrArg (fun g : GLV V => g u₀) hac
        simp only [LinearEquiv.mul_apply] at this
        rw [hw, map_sub, ← this]
      have h2 : c' w ∈ Submodule.span (ZMod 2) {c} := by
        rw [h1]
        exact hcomm' (c' u₀) hc'u
      have h3 : c' w ≠ 0 := fun h => hw0 ((c'.map_eq_zero_iff).1 h)
      exact eq_of_mem_span_singleton' hwspan h2 hw0 h3
    set S : Submodule (ZMod 2) V := fixedSpace C ⊓ J with hS
    have hSinv : Invariant H S := (invariant_fixedSpace hCnorm).inf hJ.1
    have hwS : w ∈ S := ⟨fun c' hc' => hwC c' hc', hwJ⟩
    rcases hJ.eq_bot_or_eq hSinv inf_le_right with h0 | h1
    · exact absurd ((Submodule.mem_bot _).1 (h0 ▸ hwS)) hw0
    · rw [eq_bot_iff]
      intro c' hc'
      have hc'1 : c' = 1 := by
        have hcen : c' ∈ centralizerOn H J := ⟨hc'.1, fun u hu => by
          have hu' : u ∈ S := h1 ▸ hu
          exact hu'.1 c' hc'⟩
        rw [hfaith] at hcen
        exact Subgroup.mem_bot.1 hcen
      rw [hc'1]
      exact Subgroup.one_mem _
  have hcomp : ∀ γ ∈ Γ, L.map (MulAut.conj γ).toMonoidHom ≤ T := by
    intro γ hγ
    have hcompΓ := B113.isComponentOf_conj hyp.component hγ
    have hL'H : L.map (MulAut.conj γ).toMonoidHom ≤ H := by
      rintro _ ⟨l, hl, rfl⟩
      exact Subgroup.subset_closure ⟨γ, hγ, l, hl, rfl⟩
    have hcompK : IsComponentOf (L.map (MulAut.conj γ).toMonoidHom) K := by
      refine ⟨hL'H.trans hHK, ?_, hcompΓ.2.2⟩
      have := B113.isSubnormal_inf_of_le hcompΓ.2.1 hKΓ
      rwa [inf_eq_right.2 (hL'H.trans hHK)] at this
    rcases B113.component_le_or_commutator_eq_bot hcompK hsubT with h | h
    · exact h
    · exfalso
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      have hle : L.map (MulAut.conj γ).toMonoidHom ≤ C := fun x hx => ⟨hL'H hx, h hx⟩
      rw [hCbot] at hle
      obtain ⟨-, hs⟩ := hcompΓ.2.2
      have hsub : Subsingleton ↥(L.map (MulAut.conj γ).toMonoidHom) :=
        ⟨fun x y => Subtype.ext ((Subgroup.mem_bot.1 (hle x.2)).trans
          (Subgroup.mem_bot.1 (hle y.2)).symm)⟩
      have hsub' : Subsingleton (↥(L.map (MulAut.conj γ).toMonoidHom) ⧸
          Subgroup.center ↥(L.map (MulAut.conj γ).toMonoidHom)) :=
        Function.Surjective.subsingleton (QuotientGroup.mk_surjective)
      exact (not_subsingleton _) hsub'
  show Subgroup.closure _ ≤ T
  rw [Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact hcomp γ hγ ⟨l, hl, rfl⟩

end G108Hyp

end G11

end CFSG.Quasithin
