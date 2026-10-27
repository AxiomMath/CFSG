module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem connected_of_elationFull (hnd : F.Nondegenerate) (halt : F.IsAlt)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ sympSubgroup F) (S : Set V) (h0 : ∀ y ∈ S, y ≠ 0)
    (hinv : ∀ g ∈ H, ∀ y ∈ S, g y ∈ S) (hspan : Submodule.span K S = ⊤) {e : V} (he : e ∈ S)
    (hfull : ElationFull F ((H : Set _) ∩ pointRad F e) e) :
    ∀ x ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) e x := by
  intro x hx
  by_contra hxC
  have hCS : ∀ c, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) e c → c ∈ S := by
    intro c hc
    induction hc with
    | refl => exact he
    | tail _ hbc _ =>
      obtain ⟨_, hcS, _⟩ := hbc
      exact hcS
  have h1 : ∀ c, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) e c →
      F c x = 0 := by
    intro c hc
    by_contra hcx
    exact hxC (Relation.ReflTransGen.tail hc ⟨hCS c hc, hx, hcx⟩)
  have hex : F e x = 0 := h1 e Relation.ReflTransGen.refl
  have hxe : F x e = 0 := by rw [form_comm halt]; exact hex
  obtain ⟨r, hrS, herr⟩ : ∃ r ∈ S, F e r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 e he (eq_zero_of_perp_span hnd hspan hcon)
  have hrC : Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) e r :=
    Relation.ReflTransGen.single ⟨he, hrS, herr⟩
  have hre : F r e ≠ 0 := by rw [form_comm halt]; exact herr
  have hrx : F r x = 0 := h1 r hrC
  have hxspan : x ∉ Submodule.span K {e} := by
    intro hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    rw [map_smul, smul_eq_mul] at hrx
    rcases mul_eq_zero.mp hrx with hc | hc
    · exact h0 _ hx (by rw [hc, zero_smul])
    · exact hre hc
  obtain ⟨φ, hφe, hφx⟩ : ∃ φ : Module.Dual K V, φ e = 0 ∧ φ x = 1 := by
    obtain ⟨f, hfx, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxspan inferInstance
    have hfe : f e = 0 := by
      have hmem : f e ∈ (Submodule.span K {e}).map f :=
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self e)
      rw [hfp] at hmem
      simpa using hmem
    refine ⟨(f x)⁻¹ • f, ?_, ?_⟩
    · rw [LinearMap.smul_apply, hfe, smul_zero]
    · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfx]
  obtain ⟨g, hgD, hg⟩ := hfull φ hφe
  have hgH : g ∈ H := SetLike.mem_coe.mp hgD.1
  have hgP : g ∈ pointRadSubgroup F e := mem_pointRad_iff'.mp hgD.2
  have hgx : g x = x + e := by rw [hg x hxe, hφx, one_smul]
  have hge : g e = e := (mem_pointRad_iff.mp hgP).2.1
  have hgI : IsIsom F g := hH hgH
  have hu : ∀ v, g (g⁻¹ v) = v := fun v => by simp
  have hu' : ∀ v, g⁻¹ (g v) = v := fun v => by simp
  have hgi : g⁻¹ e = e := by
    apply g.injective
    rw [hu, hge]
  have hFinv : ∀ a b, F (g⁻¹ a) (g⁻¹ b) = F a b := by
    intro a b
    have := hgI (g⁻¹ a) (g⁻¹ b)
    rw [hu, hu] at this
    exact this.symm
  have htrans : ∀ y, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) e y →
      Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) e (g⁻¹ y) := by
    intro y hy
    induction hy with
    | refl => rw [hgi]
    | tail _ hbc ih =>
      obtain ⟨hbS, hcS, hbc0⟩ := hbc
      refine Relation.ReflTransGen.tail ih ⟨hinv (g⁻¹) (H.inv_mem hgH) _ hbS,
        hinv (g⁻¹) (H.inv_mem hgH) _ hcS, ?_⟩
      rw [hFinv]
      exact hbc0
  have hgS : g x ∈ S := hinv g hgH x hx
  have hgxC : ¬ Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) e (g x) := by
    intro hC
    apply hxC
    have := htrans (g x) hC
    rwa [hu'] at this
  have hrgx : F r (g x) = 0 := by
    by_contra hne
    exact hgxC (Relation.ReflTransGen.tail hrC ⟨hrS, hgS, hne⟩)
  rw [hgx, map_add, hrx, zero_add] at hrgx
  exact hre hrgx

end CFSG.RankThree.GF2n.Stroth80.Classify
