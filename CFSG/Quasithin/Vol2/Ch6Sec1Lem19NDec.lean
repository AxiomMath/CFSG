module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19D
public import CFSG.Quasithin.Background.G6Transvection

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

namespace L619

variable {G : Type} [Group G] {W : Subgroup G} (hW : IsElemAbelian 2 W) (Z X : Subgroup G)

@[expose] def NormDec {s : ℕ} (Ks : Fin s → Subgroup (MulAut ↥(V0 hW Z X))) : Prop :=
  ∀ g : ↥(normWZX W Z X), (∀ i, ∃ j, conjSubgroup (Ks i) (act0 hW Z X g) = Ks j) ∧
    ((∀ i, conjSubgroup (Ks i) (act0 hW Z X g) = Ks i) → act0 hW Z X g ∈ img0 hW Z X)

theorem act0_mem_img0_of_normDec {Ks : Fin 1 → Subgroup (MulAut ↥(V0 hW Z X))}
    (hdec : G6.IsTransvectionDecomposition (img0 hW Z X) Ks) (hN : NormDec hW Z X Ks)
    (g : ↥(normWZX W Z X)) : act0 hW Z X g ∈ img0 hW Z X := by
  have hKi : ∀ i, Ks i = img0 hW Z X := fun i => by
    rw [← hdec.iSup_eq]
    refine le_antisymm (le_iSup Ks i) (iSup_le fun j => ?_)
    rw [Subsingleton.elim j i]
  refine (hN g).2 fun i => ?_
  rw [hKi i]
  ext x
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hx
    have := act0_conj_mem_img0 hW Z X g⁻¹ hx
    simpa [mul_assoc] using this
  · exact act0_conj_mem_img0 hW Z X g

end L619

end CFSG.Quasithin.H13
