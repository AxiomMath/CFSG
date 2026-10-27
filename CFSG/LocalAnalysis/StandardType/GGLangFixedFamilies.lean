module
public import CFSG.LocalAnalysis.StandardType.GGLangDictChar
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameTransport
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
public import CFSG.RankThree.PartOne.KE.StabGeneral

public section
namespace CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open Multiplicative

variable {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
  {Bs : Subgroup (GGAutU t n f)}
  {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
  {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
  {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}

@[expose] noncomputable def GGLangData.diagonalActorHom
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) :
    Bs →* ModGL B.τ L := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ : B.ζ ^ p = 1 := by simpa only [B.ζ_order] using pow_orderOf_eq_one B.ζ
  refine MonoidHom.mk' (fun b => rootDiagUnit B.τ (B.a b)) ?_
  intro b c
  rw [← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, B.a_coord, map_mul, toAdd_mul, Pi.add_apply]
  rw [ZMod.val_add, ← pow_eq_pow_mod
    ((toAdd (coord b) (Fin.cast B.rank_eq.symm j)).val +
      (toAdd (coord c) (Fin.cast B.rank_eq.symm j)).val) hζ, pow_add]

@[simp] theorem GGLangData.diagonalActorHom_apply
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (b : Bs) :
    B.diagonalActorHom hp b = rootDiagUnit B.τ (B.a b) := rfl
@[expose] noncomputable def GGLangData.langGroupEquiv
    (B : GGLangData L t n f p Bs S π coord) :
    ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) ≃* ↥B.setup.Γ :=
  MulEquiv.ofBijective (B.ι.codRestrict B.setup.Γ (fun k => by
    rw [← B.ι_range]
    exact ⟨k, rfl⟩)) ⟨fun _ _ h => B.ι_inj (congrArg Subtype.val h), by
      rintro ⟨y, hy⟩
      have hy' : y ∈ B.ι.range := by rwa [B.ι_range]
      obtain ⟨k, hk⟩ := hy'
      exact ⟨k, Subtype.ext hk⟩⟩

@[simp] theorem GGLangData.langGroupEquiv_apply_coe
    (B : GGLangData L t n f p Bs S π coord)
    (k : (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) :
    (B.langGroupEquiv k : ModGL B.τ L) = B.ι k := rfl

@[expose] noncomputable def GGLangData.modelToInnerHom
    (B : GGLangData L t n f p Bs S π coord) : ↥B.setup.Γ →* GGAutU t n f :=
  (ggPsiBar t n f).comp B.langGroupEquiv.symm.toMonoidHom

@[simp] theorem GGLangData.modelToInnerHom_apply_equiv
    (B : GGLangData L t n f p Bs S π coord)
    (k : (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) :
    B.modelToInnerHom (B.langGroupEquiv k) = ggPsiBar t n f k := by
  exact congrArg (ggPsiBar t n f) (B.langGroupEquiv.symm_apply_apply k)

end CFSG.StandardType
