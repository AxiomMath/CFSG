module

public import CFSG.Quasithin.EmptyFaithful.S153E61BD
public import CFSG.Quasithin.EmptyFaithful.S153E59J

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E61B

section Count

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem centralizer_of_fix (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁)
    {a : G} (ha : a ∈ VZ T M) (haU : a ∉ UH153 T M V₁ Mc) (hN : a ∈ S153E57.NZ T)
    {u : G} (hu : u ∈ UH153 T M V₁ Mc)
    (hfix : S153E57.rho cx ⟨a, hN⟩ (S153E57.piU cx ⟨u, hu⟩) = S153E57.piU cx ⟨u, hu⟩) :
    ∀ w ∈ VZ T M, u * w = w * u := by
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  have hMc : a ∈ Mc := S153E59.VZ_le_Mc cx ha
  let Φ : ↥(UH153 T M V₁ Mc) →* ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    (S153E57.phi (S153E57.rho cx ⟨a, hN⟩)).comp (S153E57.piU cx)
  have hrange : Φ.range = S153E58.Pt T M V₁ Mc := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (S153E57.piU_surjective cx)]
    exact map_phi_top_eq_Pt cx c ha haU hN
  have hcardU : Nat.card ↥(UH153 T M V₁ Mc) = 2 ^ 7 := S153E59.card_U cx c.toChain15358
  have h1 := Subgroup.card_ker_mul_card_range Φ
  rw [hrange, S153E58.card_Pt cx c.toChain15356, hcardU] at h1
  have hV := cx.c.hyp.elemAbelian
  have h2 := card_autI_mul_card_inf hV (S153E.U_le_N cx)
  have hk : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := (S153E59.klein_autOn_U cx c.toChain15358).1
  rw [hk, hcardU] at h2
  let Cs : Subgroup ↥(UH153 T M V₁ Mc) :=
    (UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G)).subgroupOf (UH153 T M V₁ Mc)
  have hCs : Nat.card ↥Cs = Nat.card ↥(UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hle : Cs ≤ Φ.ker := by
    intro x hx
    have hxC : (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) := (Subgroup.mem_subgroupOf.1 hx).2
    have hcomm : a * (x : G) = (x : G) * a := Subgroup.mem_centralizer_iff.1 hxC a ha
    have hconj := S153E57.piU_conj cx ⟨a, hN⟩ hMc x
    have hxe : (⟨a * (x : G) * a⁻¹, S153E.U_conj_mem hMc x.2⟩ : ↥(UH153 T M V₁ Mc)) = x :=
      Subtype.ext (by
        show a * (x : G) * a⁻¹ = x
        rw [hcomm]
        group)
    rw [hxe] at hconj
    rw [MonoidHom.mem_ker]
    show S153E57.phi (S153E57.rho cx ⟨a, hN⟩) (S153E57.piU cx x) = 1
    rw [S153E57.phi_eq_one_iff]
    exact hconj.symm
  have heq : Cs = Φ.ker := Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hmem : (⟨u, hu⟩ : ↥(UH153 T M V₁ Mc)) ∈ Φ.ker := by
    rw [MonoidHom.mem_ker]
    show S153E57.phi (S153E57.rho cx ⟨a, hN⟩) (S153E57.piU cx ⟨u, hu⟩) = 1
    rw [S153E57.phi_eq_one_iff]
    exact hfix
  rw [← heq] at hmem
  have hC : u ∈ Subgroup.centralizer (VZ T M : Set G) := (Subgroup.mem_subgroupOf.1 hmem).2
  intro w hw
  exact (Subgroup.mem_centralizer_iff.1 hC w hw).symm

end Count

end S153E61B

end CFSG.Quasithin
