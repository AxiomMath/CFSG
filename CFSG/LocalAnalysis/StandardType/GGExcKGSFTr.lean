module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

structure GGSFTr (t : StatedLieTag) (n f p : ℕ) (M : GGKGModel t n f p) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) (Bs : Subgroup G) where
  N : Subgroup G
  psi_le : ψ.range ≤ N
  bs_le : Bs ≤ N
  hom : N →* GGAutU t n f
  hom_inj : Function.Injective hom
  kappa : GGAutU t n f
  kappa_diag : GGInnDiagU t n f kappa
  hom_psi : ∀ k : (ggU t n f).K, hom ⟨ψ k, psi_le ⟨k, rfl⟩⟩ = kappa * ggPsiU t n f k * kappa⁻¹
  img : (Bs.subgroupOf N).map hom = M.Bfull ∨
    (Bs.subgroupOf N).map hom = M.Bfull ⊓ (ggPsiU t n f).range

namespace GGSFTr

variable {t : StatedLieTag} {n f p : ℕ} {M : GGKGModel t n f p} {G : Type} [Group G]
  {ψ : (ggU t n f).K →* G} {Bs : Subgroup G} (T : GGSFTr t n f p M ψ Bs)

@[expose] noncomputable def toHom : Bs →* GGAutU t n f := T.hom.comp (Subgroup.inclusion T.bs_le)

theorem toHom_apply (b : Bs) : T.toHom b = T.hom ⟨(b : G), T.bs_le b.2⟩ := rfl

theorem toHom_injective : Function.Injective T.toHom := fun _ _ h =>
  Subgroup.inclusion_injective T.bs_le (T.hom_inj h)

theorem toHom_mem_img (b : Bs) : T.toHom b ∈ (Bs.subgroupOf T.N).map T.hom :=
  ⟨⟨(b : G), T.bs_le b.2⟩, b.2, rfl⟩

theorem toHom_mem (b : Bs) : T.toHom b ∈ M.Bfull := by
  rcases T.img with h | h
  · exact h ▸ T.toHom_mem_img b
  · exact (h ▸ T.toHom_mem_img b : T.toHom b ∈ M.Bfull ⊓ (ggPsiU t n f).range).1

@[expose] noncomputable def toB : Bs →* M.Bfull := T.toHom.codRestrict M.Bfull T.toHom_mem

theorem toB_val (b : Bs) : ((T.toB b : M.Bfull) : GGAutU t n f) = T.toHom b := rfl

@[expose] noncomputable def coord :
    Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p) :=
  M.coord.comp T.toB

theorem coord_apply (b : Bs) : T.coord b = M.coord (T.toB b) := rfl

theorem coord_inj : Function.Injective T.coord := by
  intro b b' h
  have h1 : T.toB b = T.toB b' := M.coord_inj h
  exact T.toHom_injective (congrArg Subtype.val h1)

theorem coord_fixed (b : Bs) (i : Fin (ggU (absTag t) 6 f).D.rank) :
    Multiplicative.toAdd (T.coord b) (M.π i) = Multiplicative.toAdd (T.coord b) i :=
  M.coord_fixed (T.toB b) i

theorem coord_surj : ∀ g ∈ LatCorootSpan (ggU (absTag t) 6 f).D p, (∀ i, g (M.π i) = g i) →
    ∃ b : Bs, Multiplicative.toAdd (T.coord b) = g := by
  intro g hg hfix
  obtain ⟨bm, hbinn, hcb⟩ := M.coord_surj_inner g hg hfix
  have hmem : (bm : GGAutU t n f) ∈ (Bs.subgroupOf T.N).map T.hom := by
    rcases T.img with h | h
    · rw [h]; exact bm.2
    · rw [h]; exact ⟨bm.2, hbinn⟩
  obtain ⟨x, hx, hxb⟩ := hmem
  refine ⟨⟨(x : G), hx⟩, ?_⟩
  have h1 : T.toB ⟨(x : G), hx⟩ = bm := Subtype.ext hxb
  rw [coord_apply, h1]
  exact hcb

end GGSFTr

end Universal

end CFSG.StandardType
