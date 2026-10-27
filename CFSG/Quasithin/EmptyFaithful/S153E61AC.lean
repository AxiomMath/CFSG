module

public import CFSG.Quasithin.EmptyFaithful.S153E58F
public import CFSG.Quasithin.EmptyFaithful.S153E58P
public import CFSG.Quasithin.EmptyFaithful.S153E59N

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E61A

section Group

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem z2_polar : ∀ a b c d : ZMod 2, a + b + c = d → a = b + c + d := by decide

noncomputable def qU (cx : Ctx15350 T Mc M V₁ V₂ t)
    (a : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) : ZMod 2 :=
  pwr153 ((Function.surjInv (S153E57.piU_surjective cx) a : ↥(UH153 T M V₁ Mc)) : G)

theorem qU_piU (cx : Ctx15350 T Mc M V₁ V₂ t) (h56 : Concl15356 cx N₁ s y t₁)
    (u : ↥(UH153 T M V₁ Mc)) : qU cx (S153E57.piU cx u) = pwr153 (u : G) := by
  unfold qU
  set u' := Function.surjInv (S153E57.piU_surjective cx) (S153E57.piU cx u) with hu'
  have h1 : (u : G)⁻¹ * (u' : G) ∈ quasithinOmegaOneCenter T := by
    have : S153E57.piU cx (u⁻¹ * u') = 1 := by
      rw [map_mul, map_inv, hu', Function.surjInv_eq (S153E57.piU_surjective cx), inv_mul_cancel]
    simpa using (S153E57.piU_eq_one_iff cx _).1 this
  have e1 : (u' : G) = (u : G) * ((u : G)⁻¹ * u') := by group
  rw [e1]
  exact h56.orth_inv u u.2 _ h1

theorem qU_mul (cx : Ctx15350 T Mc M V₁ V₂ t) (h56 : Concl15356 cx N₁ s y t₁)
    (a b : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    qU cx (a * b) = qU cx a + qU cx b + S153E58.bilU cx a b := by
  obtain ⟨u, rfl⟩ := S153E57.piU_surjective cx a
  obtain ⟨v, rfl⟩ := S153E57.piU_surjective cx b
  rw [← map_mul, qU_piU cx h56, qU_piU cx h56, qU_piU cx h56, S153E58.bilU_piU]
  exact z2_polar _ _ _ _ (h56.orth_polar u u.2 v v.2)

theorem qU_apply_HStar (cx : Ctx15350 T Mc M V₁ V₂ t) (h56 : Concl15356 cx N₁ s y t₁)
    {h : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))}
    (hh : h ∈ HStar153 T M V₁ Mc) (a : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    qU cx (h a) = qU cx a := by
  obtain ⟨n, hn, rfl⟩ := (S153E57.mem_XStar_iff cx Mc h).1 hh
  obtain ⟨u, rfl⟩ := S153E57.piU_surjective cx a
  rw [← S153E57.piU_conj cx n hn u, qU_piU cx h56, qU_piU cx h56]
  exact h56.orth_inv_H n hn u u.2

theorem qU_Pt (cx : Ctx15350 T Mc M V₁ V₂ t) (h56 : Concl15356 cx N₁ s y t₁)
    (x : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (hx : x ∈ S153E58.Pt T M V₁ Mc) : qU cx x = 0 := by
  obtain ⟨u, rfl⟩ := S153E57.piU_surjective cx x
  rw [qU_piU cx h56]
  have hu := (S153E58.mem_Pt_iff cx u).1 hx
  have h2 : (u : G) ^ 2 = 1 := cx.c.hyp.elemAbelian.2 _ hu.1
  simp [pwr153, h2]

theorem rho57_eq_rho59 (cx : Ctx15350 T Mc M V₁ V₂ t) (n : S153E57.NZ T) (hn : (n : G) ∈ Mc) :
    S153E57.rho cx n = S153E59.rho cx ⟨(n : G), hn⟩ := by
  ext w
  rw [S153E57.rho_apply_coe, S153E59.rho_apply_coe]
  rfl

theorem exists_a_mem_K (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁) :
    ∃ a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
      a ∈ XStar153 T M V₁ Mc (VZ T M) ∧ a ≠ 1 ∧ a ∈ oTwoUpper (HStar153 T M V₁ Mc) := by
  obtain ⟨a, haV, ha1, -, -⟩ := S153E58.exists_a c.toChain15356
  refine ⟨a, haV, ha1, ?_⟩
  have hH := S153E59.hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2
  have haX : a ∈ S153E57.XS T M V₁ Mc y := S153E57.Vs_le_XS c.toChain15356 haV
  obtain ⟨n, hnX, rfl⟩ := (S153E57.mem_XStar_iff cx _ a).1 haX
  have hnM : (n : G) ∈ Mc := S153E59.X_le_Mc cx c.toChain15358 hnX
  rw [rho57_eq_rho59 cx n hnM]
  exact S153E59.rho_X_mem cx c.toChain15358 hH hnX

theorem exists_lift_K (cx : Ctx15350 T Mc M V₁ V₂ t)
    {k' : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))}
    (hk' : k' ∈ oTwoUpper (HStar153 T M V₁ Mc)) :
    ∃ (k : G) (hkN : k ∈ S153E57.NZ T), k ∈ oTwoUpper Mc ∧ S153E57.rho cx ⟨k, hkN⟩ = k' := by
  rw [← S153E59.map_rho_oTwoUpper cx] at hk'
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hk'
  have hkK : (k : G) ∈ oTwoUpper Mc := Subgroup.mem_subgroupOf.mp hk
  have hkN : (k : G) ∈ S153E57.NZ T := S153E57.Mc_le_NZ cx k.2
  refine ⟨k, hkN, hkK, ?_⟩
  rw [rho57_eq_rho59 cx ⟨k, hkN⟩ k.2]
  exact hkx

end Group

end S153E61A

end CFSG.Quasithin
