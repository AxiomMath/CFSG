module

public import CFSG.Quasithin.EmptyFaithful.S151V3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped commutatorElement

namespace V2InQ

variable {G : Type} [Group G] {L : Subgroup G} {e : ↥L →* SLt 3}
  {β : ↥(blockU L) →* Multiplicative (Vt 3)}

@[expose] noncomputable def sigmaU (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ↥(blockU L) →* ↥(blockU L) :=
  ((blockU L).normalizerMonoidHom ⟨g, s151v_normalizer_le_normalizer_blockU L hg⟩).toMonoidHom

theorem sigmaU_coe (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) (u : ↥(blockU L)) :
    ((sigmaU g hg u : ↥(blockU L)) : G) = g * u * g⁻¹ :=
  (blockU L).normalizerMonoidHom_apply_apply_coe _ u

theorem sigmaU_mul (g h : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) (hgh : g * h ∈ Subgroup.normalizer (L : Set G))
    (u : ↥(blockU L)) : sigmaU (g * h) hgh u = sigmaU g hg (sigmaU h hh u) := by
  apply Subtype.ext
  simp only [sigmaU_coe]
  group

theorem sigmaU_ker (hs : LnStr L e β) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (u : ↥(blockU L)) (hu : β u = 1) : β (sigmaU g hg u) = 1 := by
  have hu' : u ∈ β.ker := hu
  rw [hs.βker] at hu'
  have hZ : (u : G) ∈ blockZ L := hu'
  have h1 : g * (u : G) * g⁻¹ ∈ blockZ L :=
    (Subgroup.mem_normalizer_iff.1 (s151v_normalizer_le_normalizer_blockZ L hg) _).1 hZ
  have h2 : sigmaU g hg u ∈ β.ker := by
    rw [hs.βker]
    show ((sigmaU g hg u : ↥(blockU L)) : G) ∈ blockZ L
    rw [sigmaU_coe]
    exact h1
  exact h2

@[expose] noncomputable def gammaHom (hs : LnStr L e β) (g : G)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    Multiplicative (Vt 3) →* Multiplicative (Vt 3) :=
  β.liftOfRightInverse (Function.surjInv hs.βsurj) (Function.rightInverse_surjInv hs.βsurj)
    ⟨β.comp (sigmaU g hg), fun u hu =>
      MonoidHom.mem_ker.mpr (sigmaU_ker hs g hg u (MonoidHom.mem_ker.mp hu))⟩

theorem gammaHom_apply (hs : LnStr L e β) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (u : ↥(blockU L)) : gammaHom hs g hg (β u) = β (sigmaU g hg u) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u

@[expose] noncomputable def gammaAut (hs : LnStr L e β) (g : G)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : MulAut (Multiplicative (Vt 3)) :=
  MonoidHom.toMulEquiv (gammaHom hs g hg)
    (gammaHom hs g⁻¹ ((Subgroup.normalizer (L : Set G)).inv_mem hg))
    (MonoidHom.ext fun b => by
      obtain ⟨u, rfl⟩ := hs.βsurj b
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, gammaHom_apply]
      congr 1
      apply Subtype.ext
      simp only [sigmaU_coe]
      group)
    (MonoidHom.ext fun b => by
      obtain ⟨u, rfl⟩ := hs.βsurj b
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, gammaHom_apply]
      congr 1
      apply Subtype.ext
      simp only [sigmaU_coe]
      group)

theorem gammaAut_apply (hs : LnStr L e β) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (u : ↥(blockU L)) : gammaAut hs g hg (β u) = β (sigmaU g hg u) :=
  gammaHom_apply hs g hg u

@[expose] noncomputable def gammaMap (hs : LnStr L e β) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (Multiplicative (Vt 3)) where
  toFun g := gammaAut hs g.1 g.2
  map_one' := by
    refine MulEquiv.ext fun b => ?_
    obtain ⟨u, rfl⟩ := hs.βsurj b
    show gammaAut hs 1 _ (β u) = β u
    rw [gammaAut_apply]
    congr 1
    apply Subtype.ext
    simp [sigmaU_coe]
  map_mul' g h := by
    refine MulEquiv.ext fun b => ?_
    obtain ⟨u, rfl⟩ := hs.βsurj b
    show gammaAut hs (g.1 * h.1) _ (β u) = gammaAut hs g.1 g.2 (gammaAut hs h.1 h.2 (β u))
    rw [gammaAut_apply, gammaAut_apply, gammaAut_apply, sigmaU_mul g.1 h.1 g.2 h.2]

theorem gammaMap_apply (hs : LnStr L e β) (g : ↥(Subgroup.normalizer (L : Set G)))
    (u : ↥(blockU L)) : gammaMap hs g (β u) = β (sigmaU g.1 g.2 u) :=
  gammaAut_apply hs g.1 g.2 u

end V2InQ

end CFSG.Quasithin
