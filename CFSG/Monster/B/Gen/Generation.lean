
module

public import CFSG.Monster.B.Gen.GenerationBase

public import CFSG.Monster.B.Co2.IrredAll

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot

theorem irreducible_Wv_rStar
    (U : Submodule (ZMod 2) (Wv (phi0 (coordOf rStar))))
    (hU : ∀ (k : Kstab (phi0 (coordOf rStar))) (w : Wv (phi0 (coordOf rStar))), w ∈ U →
      wAct _ k w ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  have h := (Co2.native_short_stabilizer_irreducible vMinus_zero_one_mem).2.2
  rw [← phi0_coordOf_rStar] at h
  exact h U hU

section Generation

variable (G : Subgroup Cbar)
  (hsurj : ∀ k : Kstab (phi0 (coordOf rStar)), ∃ g : Jbar, (g : Cbar) ∈ G ∧ jbarToKv g = k)

include hsurj in
theorem psiImage_eq_top
    (he : ∃ e : Ebar, (e : Cbar) ∈ G ∧ psiBar e ≠ 1) :
    psiImage G = ⊤ := by
  rcases irreducible_Wv_rStar (psiImage G) (psiImage_invariant G hsurj) with h | h
  · exfalso
    obtain ⟨e, heG, hne⟩ := he
    have hmem : Multiplicative.toAdd (psiBar e) ∈ psiImage G := ⟨e, heG, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hne (by rw [← ofAdd_toAdd (psiBar e), hmem, ofAdd_zero])
  · exact h

include hsurj in
theorem Ebar_le_of_irreducible
    (he : ∃ e : Ebar, (e : Cbar) ∈ G ∧ psiBar e ≠ 1)
    (hnonab : ∃ a b : Ebar, a * b ≠ b * a)
    (hcent : ∀ e : Ebar, e * ⟨xbar, xbar_mem_Ebar⟩ = ⟨xbar, xbar_mem_Ebar⟩ * e) :
    Ebar ≤ G := by
  have htop := psiImage_eq_top G hsurj he
  have hrep : ∀ e : Ebar, ∃ e' ∈ G.subgroupOf Ebar, e = e' ∨ e = e' * ⟨xbar, xbar_mem_Ebar⟩ := by
    intro e
    have hmem : Multiplicative.toAdd (psiBar e) ∈ psiImage G := by rw [htop]; trivial
    obtain ⟨e', he'G, he'⟩ := hmem
    have h1 : psiBar (e'⁻¹ * e) = 1 := by
      rw [map_mul, map_inv, ← ofAdd_toAdd (psiBar e'), he', ofAdd_toAdd, inv_mul_cancel]
    refine ⟨e', Subgroup.mem_subgroupOf.2 he'G, ?_⟩
    rcases (psiBar_eq_one_iff _).1 h1 with h | h
    · exact .inl (by rw [← mul_inv_cancel_left e' e, h, mul_one])
    · exact .inr (by rw [← mul_inv_cancel_left e' e, h])
  have hcomm : ∀ a ∈ G.subgroupOf Ebar, ∀ b ∈ G.subgroupOf Ebar,
      (b * a)⁻¹ * (a * b) = 1 ∨ (b * a)⁻¹ * (a * b) = ⟨xbar, xbar_mem_Ebar⟩ := by
    intro a _ b _
    apply (psiBar_eq_one_iff _).1
    rw [map_mul, map_inv, map_mul, map_mul, mul_comm (psiBar b) (psiBar a), inv_mul_cancel]
  have h := eq_top_of_cover (G.subgroupOf Ebar) _ hcent hrep hcomm hnonab
  intro e he
  have hmem : (⟨e, he⟩ : Ebar) ∈ G.subgroupOf Ebar := h ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hmem

include hsurj in
theorem Jbar_le_of_irreducible
    (he : ∃ e : Ebar, (e : Cbar) ∈ G ∧ psiBar e ≠ 1)
    (hnonab : ∃ a b : Ebar, a * b ≠ b * a)
    (hcent : ∀ e : Ebar, e * ⟨xbar, xbar_mem_Ebar⟩ = ⟨xbar, xbar_mem_Ebar⟩ * e) :
    Jbar ≤ G := by
  have hE := Ebar_le_of_irreducible G hsurj he hnonab hcent
  intro j hj
  obtain ⟨g, hgG, hgk⟩ := hsurj (jbarToKv ⟨j, hj⟩)
  have hker : (g⁻¹ * ⟨j, hj⟩ : Jbar) ∈ jbarToKv.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgk, inv_mul_cancel]
  rw [ker_jbarToKv, Subgroup.mem_subgroupOf] at hker
  have h1 : ((g⁻¹ * ⟨j, hj⟩ : Jbar) : Cbar) ∈ G := hE hker
  have h2 : j = (g : Cbar) * ((g⁻¹ * ⟨j, hj⟩ : Jbar) : Cbar) := by
    push_cast
    rw [mul_inv_cancel_left]
  rw [h2]
  exact G.mul_mem hgG h1

end Generation

theorem Jbar_le_of_generates
    (G : Subgroup Cbar)
    (hsurj : ∀ k : Kstab (phi0 (coordOf rStar)), ∃ g : Jbar, (g : Cbar) ∈ G ∧ jbarToKv g = k)
    (he : ∃ e : Ebar, (e : Cbar) ∈ G ∧ psiBar e ≠ 1) : Jbar ≤ G :=
  Jbar_le_of_irreducible G hsurj he Ebar_nonabelian xbarE_comm


theorem Kstab_v0_eq_closure_alpha :
    Kstab Co2.v0 = Subgroup.closure (Set.range Co2.alpha) := by
  apply le_antisymm
  · rw [← Co2.Agrp_eq_Kv, Co2.Agrp, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact alphaWord_mem_closure _
    · exact alphaWord_mem_closure _
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Co2.alpha_mem_Kv i

theorem closure_eq_top_of_generators
    {T : Set Cbar} (hτ : taubar ∈ T)
    (hgen : ∀ i, ∃ g : Jbar, (g : Cbar) ∈ Subgroup.closure T ∧
      ((jbarToKv g : Kstab (phi0 (coordOf rStar))) : OLq) = (Co2.alpha i)⁻¹)
    (he : ∃ e : Ebar, (e : Cbar) ∈ Subgroup.closure T ∧ psiBar e ≠ 1) :
    Subgroup.closure T = ⊤ := by
  set G := Subgroup.closure T with hG
  set I : Subgroup OLq :=
    ((G.subgroupOf Jbar).map jbarToKv).map (Kstab (phi0 (coordOf rStar))).subtype with hI
  have hK : Kstab (phi0 (coordOf rStar)) = Subgroup.closure (Set.range Co2.alpha) :=
    (congrArg Kstab phi0_coordOf_rStar).trans Kstab_v0_eq_closure_alpha
  have hKI : Subgroup.closure (Set.range Co2.alpha) ≤ I := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨g, hgG, hg⟩ := hgen i
    have hmem : (Co2.alpha i)⁻¹ ∈ I :=
      ⟨jbarToKv g, ⟨g, (Subgroup.mem_subgroupOf).2 hgG, rfl⟩, hg⟩
    simpa using I.inv_mem hmem
  have hsurj : ∀ k : Kstab (phi0 (coordOf rStar)), ∃ g : Jbar, (g : Cbar) ∈ G ∧ jbarToKv g = k := by
    intro k
    have hk : (k : OLq) ∈ I := hKI (hK ▸ k.2)
    obtain ⟨k', ⟨g, hgG, rfl⟩, hk'⟩ := hk
    exact ⟨g, (Subgroup.mem_subgroupOf).1 hgG, Subtype.ext hk'⟩
  have hJ := Jbar_le_of_generates G hsurj he
  have htop := closure_insert_taubar_eq_top hJ
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact Subgroup.subset_closure hτ
  · exact hx

end CFSG.Monster.B
