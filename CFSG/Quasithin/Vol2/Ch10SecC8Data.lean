module

public import CFSG.Quasithin.Vol2.Ch10SecC8Coord
public import CFSG.Quasithin.Vol2.Ch10SecC8T1
public import CFSG.Quasithin.Vol2.Ch10SecC8V2
public import CFSG.Quasithin.Vol2.Ch10SecCL3F

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32 L3F
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def CompFacts (T L I K : Subgroup G) [IsMulCommutative ↥(Vi T L I K)]
    (D : L3Data (autOn K (Vi T L I K)) ⊤
      ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K))) : Prop :=
  K ≤ fsuL0 T L ∧ K ≤ Subgroup.normalizer (fsuVM T L I : Set G) ∧ T ⊓ K ≤ T1 T L ∧
    (∀ γ, ((D.π γ : ↥(autOn K (Vi T L I K))) : MulAut ↥(Vi T L I K)) ∈
      autOn (T ⊓ K) (Vi T L I K) ↔ γ ∈ U3) ∧
    (∀ s ∈ T1 T L, ∃ d ∈ T ⊓ K, ∀ w ∈ Vi T L I K, s * w * s⁻¹ = d * w * d⁻¹) ∧
    (∀ w : ↥(Vi T L I K), w ^ 2 = 1) ∧
    fixV (autOn K (Vi T L I K)) =
      (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K) ∧
    Nat.card ↥((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K)) = 2 ∧
    (∀ a ∈ autOn K (Vi T L I K), a ≠ 1 → a ^ 2 = 1 →
      commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
        Nat.card (fixV (Subgroup.zpowers a)) = 4) ∧
    (∀ A : Subgroup (MulAut ↥(Vi T L I K)), A ≤ autOn K (Vi T L I K) → IsElemAbelian2 A →
      Nat.card A ≤ 4)

variable {T L I : Subgroup G}

theorem conjugate_le_normalizer (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) :
    CFSG.conjugate L t ≤ Subgroup.normalizer (L : Set G) := fun _ hx =>
  ((Subgroup.normal_subgroupOf_iff_le_normalizer (SecA.le_fsuL0 T L)).mp
    (SecA.normal_fsuL0 hyp.fsu.maximal.1)) (SecA.conjugate_le_fsuL0 ht hx)

theorem exists_comp_data (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ (_ : IsMulCommutative ↥(Vi T L I L)) (_ : IsMulCommutative ↥(Vi T L I (CFSG.conjugate L t)))
      (D : L3Data (autOn L (Vi T L I L)) ⊤
        ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I L)))
      (D₂ : L3Data (autOn (CFSG.conjugate L t) (Vi T L I (CFSG.conjugate L t))) ⊤
        ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I (CFSG.conjugate L t)))),
      CompFacts T L I L D ∧ CompFacts T L I (CFSG.conjugate L t) D₂ := by
  obtain ⟨hc, hnat⟩ := h3.2
  have hc2 : IsMulCommutative ↥(Vi T L I (CFSG.conjugate L t)) :=
    ⟨⟨fun a b => Subtype.ext (fsuVM_comm hyp
      (commutator_le_left_of_le_normalizer
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) a.2)
      (commutator_le_left_of_le_normalizer
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) b.2))⟩⟩
  obtain ⟨D0⟩ := hnat.toL3Coord
  obtain ⟨D, hD⟩ := exists_L3Data_U3 hyp D0
  obtain ⟨hsq, hfix, hZc, hFF, hE4⟩ := fsuUL_module_facts h37 h38 hyp h1011 h484 D hnat hne
  obtain ⟨D₂, hD₂, hfix₂, hZc₂, hFF₂, hE4₂⟩ :=
    exists_V2_data h37 h38 hyp h1011 h484 D hD hnat hne ht
  have hLtN := conjugate_le_normalizer hyp ht
  refine ⟨hc, hc2, D, D₂, ⟨SecA.le_fsuL0 T L,
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I),
    fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩, hD,
    fun s hs => exists_mem_inf_acts_fsuUL hyp h1011 h3 D hD hs, hsq, hfix, hZc, hFF, hE4⟩,
    ⟨SecA.conjugate_le_fsuL0 ht,
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I),
    fun x hx => ⟨hx.1, hLtN hx.2⟩, hD₂,
    fun s hs => exists_mem_inf_acts_V2 h37 h38 hyp h1011 h3 D hD ht htn hs,
    fun w => Subtype.ext ((SecA.isElemAbelian_fsuVM hyp).2 _
      (commutator_le_left_of_le_normalizer
        ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) w.2)),
    hfix₂, hZc₂, hFF₂, hE4₂⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
