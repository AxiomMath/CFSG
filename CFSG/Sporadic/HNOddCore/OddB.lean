module

public import CFSG.Sporadic.HNOddCore.OddA
public import Certificates.Certificate2096
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Equiv Equiv.Perm
open CFSG.ComponentClassification.SymmetricLocal

abbrev Hi4 : Fin 12 → Prop := fun i => ¬ i.val < 4

abbrev A8P : Subgroup (Perm (Fin 12)) :=
  (alternatingGroup {i : Fin 12 // Hi4 i}).map Perm.ofSubtype

theorem mem_A8J_iff
    (h : JH) : h ∈ A8J ↔
    ∃ hh : h ∈ HJ, ∀ i : Fin 12, i.val < 4 → (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) i = i := by
  constructor
  · rintro ⟨⟨h', hh'⟩, hf, rfl⟩
    refine ⟨hh', fun i hi => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_fixingSubgroup_iff] at hf
    have := hf i hi
    rw [Perm.smul_def, thetaHom_apply] at this
    exact this
  · rintro ⟨hh, hf⟩
    refine ⟨⟨h, hh⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_fixingSubgroup_iff]
    intro i hi
    rw [Perm.smul_def, thetaHom_apply]
    exact hf i hi

@[expose] def a8Hom :
    A8J →* A8P :=
  (thetaHom.comp (Subgroup.inclusion A8J_le_HJ)).codRestrict A8P fun h => by
    obtain ⟨hh, hf⟩ := (mem_A8J_iff h.1).1 h.2
    rw [MonoidHom.comp_apply, thetaHom_apply]
    refine (mem_map_ofSubtype_alternatingGroup_iff (p := Hi4)).2 ⟨fun x hx => ?_, ?_⟩
    · exact hf x (not_not.1 hx)
    · exact Equiv.Perm.mem_alternatingGroup.1 (thetaJ _).2

theorem a8Hom_val
    (h : A8J) :
    ((a8Hom h : A8P) : Perm (Fin 12)) = (thetaJ ⟨h.1, A8J_le_HJ h.2⟩ : Perm (Fin 12)) := rfl

theorem a8Hom_bijective :
    Function.Bijective a8Hom := by
  constructor
  · intro a b hab
    have e1 : (thetaJ ⟨a.1, A8J_le_HJ a.2⟩ : Perm (Fin 12)) = thetaJ ⟨b.1, A8J_le_HJ b.2⟩ := by
      rw [← a8Hom_val, ← a8Hom_val, hab]
    have e2 := thetaJ.injective (Subtype.ext e1)
    have e3 := Subtype.ext_iff.1 e2
    dsimp only at e3
    exact Subtype.ext e3
  · rintro ⟨σ, hσ⟩
    obtain ⟨hfix, hsign⟩ := (mem_map_ofSubtype_alternatingGroup_iff (p := Hi4)).1 hσ
    set h : HJ := thetaJ.symm ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩ with hh
    have hθ : (thetaJ h : Perm (Fin 12)) = σ := by rw [hh, MulEquiv.apply_symm_apply]
    have hmem : (h : JH) ∈ A8J :=
      (mem_A8J_iff h).2 ⟨h.2, fun i hi => by rw [hθ]; exact hfix i (not_not.2 hi)⟩
    refine ⟨⟨h, hmem⟩, Subtype.ext ?_⟩
    rw [a8Hom_val]
    exact hθ

theorem card_Hi4 : Nat.card {i : Fin 12 // Hi4 i} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem A8P_simple : IsSimpleGroup A8P :=
  (Subgroup.equivMapOfInjective (alternatingGroup {i : Fin 12 // Hi4 i}) Perm.ofSubtype
    Perm.ofSubtype_injective).isSimpleGroup_congr.1
    (alternatingGroup.isSimpleGroup (by rw [card_Hi4]; norm_num))

theorem card_A8P : Nat.card A8P = 20160 := by
  have : Nontrivial {i : Fin 12 // Hi4 i} :=
    ⟨⟨⟨4, by decide⟩, ⟨5, by decide⟩, by decide⟩⟩
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (alternatingGroup {i : Fin 12 // Hi4 i})
    Perm.ofSubtype Perm.ofSubtype_injective).toEquiv, nat_card_alternatingGroup, card_Hi4]
  rfl

theorem sub_isSimpleGroup_of_bijective {G G' : Type*} [Group G] [Group G'] {H : Subgroup G}
    {K : Subgroup G'} (f : H →* K) (hf : Function.Bijective f) (hK : IsSimpleGroup K) :
    IsSimpleGroup H :=
  (MulEquiv.ofBijective f hf).isSimpleGroup_congr.2 hK

theorem A8J_simple :
    IsSimpleGroup A8J :=
  sub_isSimpleGroup_of_bijective a8Hom a8Hom_bijective A8P_simple

theorem card_A8J :
    Nat.card A8J = 20160 := by
  rw [Nat.card_congr (Equiv.ofBijective a8Hom a8Hom_bijective), card_A8P]

theorem sub_coe_comm {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup H} {a b : K}
    (h : a * b = b * a) : (a : H) * (b : H) = (b : H) * (a : H) := by
  have := congrArg Subtype.val h
  simpa using this

theorem sub_mem_centralizer_of_coe {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup H}
    {a b : K} (h : a * b = b * a) : (a : H) ∈ Subgroup.centralizer {(b : H)} :=
  sub_mem_centralizer_iff.2 (sub_coe_comm h)

theorem A8J_le_CJ_t2 :
    A8J ≤ Subgroup.centralizer {t2J} := by
  intro h hA
  obtain ⟨hh, hf⟩ := (mem_A8J_iff h).1 hA
  have hdis : (thetaJ ⟨h, hh⟩ : Perm (Fin 12)).Disjoint sig2 := by
    intro x
    by_cases hx : x.val < 4
    · exact Or.inl (hf x hx)
    · right
      revert x
      unfold sig2
      decide
  have hcomm : ⟨h, hh⟩ * t2H = t2H * ⟨h, hh⟩ := by
    apply thetaJ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, thetaJ_t2H]
    exact hdis.commute
  have := sub_mem_centralizer_of_coe hcomm
  exact this

end CFSG.Sporadic.HNOddCore
