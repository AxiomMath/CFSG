module

public import CFSG.Quasithin.H13.AS91Sec8Map
public import CFSG.Quasithin.Recognition.UniquenessSystemCriterion

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction

universe u v u' v'

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]
  {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]
  {x : X} {xb : Xb} {I : Subgroup G} {Ib : Subgroup Gb}

theorem exists_theta (a : ↥(stabilizer G x) ≃* ↥(stabilizer Gb xb)) (z : ↥I ≃* ↥Ib)
    (hz : ((stabilizer G x).subgroupOf I).map z.toMonoidHom = (stabilizer Gb xb).subgroupOf Ib)
    (ha : (I.subgroupOf (stabilizer G x)).map a.toMonoidHom = Ib.subgroupOf (stabilizer Gb xb)) :
    ∃ θ : ↥(I ⊓ stabilizer G x) ≃* ↥(I ⊓ stabilizer G x),
      ∀ b : ↥(I ⊓ stabilizer G x),
        totFun z (((θ b : ↥(I ⊓ stabilizer G x)) : G)) = totFun a (b : G) := by
  have hz' := (map_subgroupOf_eq_iff z (stabilizer G x) (stabilizer Gb xb)).mp hz
  have ha' := (map_subgroupOf_eq_iff a I Ib).mp ha
  have hA : ∀ b : G, b ∈ I → b ∈ stabilizer G x → totFun a b ∈ Ib ⊓ stabilizer Gb xb := by
    intro b hbI hbx
    rw [totFun_of_mem a hbx]
    exact Subgroup.mem_inf.mpr ⟨(ha' ⟨b, hbx⟩).mp hbI, (a ⟨b, hbx⟩).2⟩
  have hC : ∀ b : G, b ∈ I → b ∈ stabilizer G x → totFun z b ∈ Ib ⊓ stabilizer Gb xb := by
    intro b hbI hbx
    rw [totFun_of_mem z hbI]
    exact Subgroup.mem_inf.mpr ⟨(z ⟨b, hbI⟩).2, (hz' ⟨b, hbI⟩).mp hbx⟩
  have hB : ∀ c : Gb, c ∈ Ib → c ∈ stabilizer Gb xb → totFun z.symm c ∈ I ⊓ stabilizer G x := by
    intro c hcI hcx
    rw [totFun_of_mem z.symm hcI]
    refine Subgroup.mem_inf.mpr ⟨(z.symm ⟨c, hcI⟩).2, ?_⟩
    apply (hz' (z.symm ⟨c, hcI⟩)).mpr
    rw [MulEquiv.apply_symm_apply]
    exact hcx
  have hD : ∀ c : Gb, c ∈ Ib → c ∈ stabilizer Gb xb → totFun a.symm c ∈ I ⊓ stabilizer G x := by
    intro c hcI hcx
    rw [totFun_of_mem a.symm hcx]
    refine Subgroup.mem_inf.mpr ⟨?_, (a.symm ⟨c, hcx⟩).2⟩
    apply (ha' (a.symm ⟨c, hcx⟩)).mpr
    rw [MulEquiv.apply_symm_apply]
    exact hcI
  have hmemI : ∀ b : ↥(I ⊓ stabilizer G x), (b : G) ∈ I :=
    fun b => (Subgroup.mem_inf.mp b.2).1
  have hmemX : ∀ b : ↥(I ⊓ stabilizer G x), (b : G) ∈ stabilizer G x :=
    fun b => (Subgroup.mem_inf.mp b.2).2
  have hAI : ∀ b : ↥(I ⊓ stabilizer G x), totFun a (b : G) ∈ Ib :=
    fun b => (Subgroup.mem_inf.mp (hA _ (hmemI b) (hmemX b))).1
  have hCI : ∀ b : ↥(I ⊓ stabilizer G x), totFun z (b : G) ∈ Ib :=
    fun b => (Subgroup.mem_inf.mp (hC _ (hmemI b) (hmemX b))).1
  have hCX : ∀ b : ↥(I ⊓ stabilizer G x), totFun z (b : G) ∈ stabilizer Gb xb :=
    fun b => (Subgroup.mem_inf.mp (hC _ (hmemI b) (hmemX b))).2
  have hfmem : ∀ b : ↥(I ⊓ stabilizer G x),
      totFun z.symm (totFun a (b : G)) ∈ I ⊓ stabilizer G x :=
    fun b => hB _ (hAI b) (totFun_mem a (hmemX b))
  have hgmem : ∀ b : ↥(I ⊓ stabilizer G x),
      totFun a.symm (totFun z (b : G)) ∈ I ⊓ stabilizer G x :=
    fun b => hD _ (hCI b) (hCX b)
  let f : ↥(I ⊓ stabilizer G x) → ↥(I ⊓ stabilizer G x) := fun b =>
    ⟨totFun z.symm (totFun a (b : G)), hfmem b⟩
  let g : ↥(I ⊓ stabilizer G x) → ↥(I ⊓ stabilizer G x) := fun b =>
    ⟨totFun a.symm (totFun z (b : G)), hgmem b⟩
  have hfg : ∀ b : ↥(I ⊓ stabilizer G x), g (f b) = b := by
    intro b
    apply Subtype.ext
    show totFun a.symm (totFun z (totFun z.symm (totFun a (b : G)))) = (b : G)
    rw [totFun_totFun_symm z (hAI b), totFun_symm_totFun a (hmemX b)]
  have hgf : ∀ b : ↥(I ⊓ stabilizer G x), f (g b) = b := by
    intro b
    apply Subtype.ext
    show totFun z.symm (totFun a (totFun a.symm (totFun z (b : G)))) = (b : G)
    rw [totFun_totFun_symm a (hCX b), totFun_symm_totFun z (hmemI b)]
  have hfmul : ∀ b c : ↥(I ⊓ stabilizer G x), f (b * c) = f b * f c := by
    intro b c
    apply Subtype.ext
    show totFun z.symm (totFun a ((b : G) * (c : G))) =
      totFun z.symm (totFun a (b : G)) * totFun z.symm (totFun a (c : G))
    rw [totFun_mul a (hmemX b) (hmemX c), totFun_mul z.symm (hAI b) (hAI c)]
  let θ : ↥(I ⊓ stabilizer G x) ≃* ↥(I ⊓ stabilizer G x) :=
    { toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf
      map_mul' := hfmul }
  refine ⟨θ, fun b => ?_⟩
  show totFun z (totFun z.symm (totFun a (b : G))) = totFun a (b : G)
  exact totFun_totFun_symm z (hAI b)

end CFSG.Quasithin.H13.AS91
