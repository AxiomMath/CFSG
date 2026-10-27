module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts12
public import CFSG.Quasithin.Vol2.Ch11SecSCartanL2
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X : Subgroup G} {n : ℕ}

theorem cartan_data (hC : CartanFacts) (hF : Facts12) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hX : IsCartanX T L X) :
    Nat.card ↥(centW (autOn X (fsuV T I))
        (gammaW (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I)))) = 2 ^ n - 1 ∧
      CartanPoint (autOn L (fsuV T I)) ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I))
        (V₁.subgroupOf (fsuV T I)) (autOn X (fsuV T I)) := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hP := isSylowTwoOf_P h
  have hU₁ := isFlagW_of_isVi h hV₁
  have hU₂ := isFlagW_of_isVi h hV₂
  have hD := isHall_autOn_cartan h1102 h hX
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  rcases hk with ⟨K, _, _, hK, e, π, hπ, -⟩ | ⟨K, _, _, hK, e, π, hπ, -⟩ |
      ⟨K, _, _, hK, e, hnat⟩
  · exact ⟨(hC.sl3 K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).2.2.2.2.1,
      hF.pointSL3 K n hn hK _ hsq _ _ π hπ _ hP _ hU₁ _ hD⟩
  · exact ⟨(hC.sp4 K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1.2.2.2.2.1,
      hF.pointSp4 K n hn hK _ hsq _ _ π hπ _ hP _ hU₁ _ hD⟩
  · obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
    exact ⟨(hC.g2 K' n hn hK' _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1.2.2.2.2.1,
      hF.pointG2 K' n hn hK' _ hsq _ _ π hπ _ hP _ hU₁ _ hD⟩

theorem card_xOne (hC : CartanFacts) (hF : Facts12) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hX : IsCartanX T L X) : Nat.card ↥(xOne X (LOf L V₁)) = 2 ^ n - 1 := by
  have d := transportData hN h1102 h hV₁ hV₂ hX
  rw [← d.card (inf_le_left : xOne X (LOf L V₁) ≤ X), d.f₁]
  exact (cartan_data hC hF h1102 h hV₁ hV₂ hX).1

theorem xOne_inf_centralizer (hC : CartanFacts) (hF : Facts12) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X) :
    xOne X (LOf L V₁) ⊓ Subgroup.centralizer (V₁ : Set G) = ⊥ := by
  have d := transportData hN h1102 h hV₁ hV₂ hX
  have hpt := (cartan_data hC hF h1102 h hV₁ hV₂ hX).2
  rw [eq_bot_iff]
  rintro x ⟨hx1, hxC⟩
  have hxX : x ∈ X := hx1.1
  have hxV := d.hXV hxX
  have hmem : conjV (fsuV T I) x hxV ∈ centW (autOn X (fsuV T I))
      (gammaW (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))) := by
    rw [← d.f₁]
    exact conjV_mem_autOn hx1 hxV
  have h1 := hpt _ hmem fun u hu => by
    have hfix : conjV (fsuV T I) x hxV u = u := Subtype.ext (by
      rw [conjV_apply_coe, ← Subgroup.mem_centralizer_iff.mp hxC u (Subgroup.mem_subgroupOf.mp hu),
        mul_inv_cancel_right])
    rw [hfix, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hxCV : x ∈ X ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨hxX, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h2 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) h1
    simp only [conjV_apply_coe, MulAut.one_apply] at h2
    calc v * x = x * v * x⁻¹ * x := by rw [h2]
      _ = x * v := by group
  rw [d.hXC] at hxCV
  exact hxCV

theorem xOne_le_normalizer_V1 (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    xOne X (LOf L V₁) ≤ Subgroup.normalizer (V₁ : Set G) :=
  inf_le_left.trans (cartan_le_normalizer_Vi hN h1102 h (Or.inl rfl) hV₁ hX)

theorem xOne_le_normalizer_lOf (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    xOne X (LOf L V₁) ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
  inf_le_left.trans (cartan_le_normalizer_lOf hN h1102 h (Or.inl rfl) hV₁ hX)

end CFSG.Quasithin.Vol2.Ch11.SecA
