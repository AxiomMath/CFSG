module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecANat2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] {L V : Subgroup G}

@[expose] noncomputable def conjL {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    ↥L ≃* ↥L :=
  ((MulAut.conj m).subgroupMap L).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer hm))

theorem conjL_coe {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    ((conjL hm l : ↥L) : G) = m * l * m⁻¹ :=
  rfl

theorem conjL_mul {a b : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    conjL (Subgroup.mul_mem _ ha hb) l = conjL ha (conjL hb l) := by
  apply Subtype.ext
  simp only [conjL_coe]
  group

theorem conjL_inv {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    conjL ha (conjL (Subgroup.inv_mem _ ha) l) = l := by
  apply Subtype.ext
  simp only [conjL_coe]
  group

theorem conjL_one (l : ↥L) : conjL (Subgroup.one_mem (Subgroup.normalizer (L : Set G))) l = l := by
  apply Subtype.ext
  simp only [conjL_coe]
  group

variable {ρ : ↥L →* MulAut ↥V}

theorem isInducedOn_one : IsInducedOn ρ (conjL (Subgroup.one_mem _)) :=
  ⟨1, fun l => by rw [conjL_one]; group⟩

theorem isInducedOn_mul {a b : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hia : IsInducedOn ρ (conjL ha))
    (hib : IsInducedOn ρ (conjL hb)) : IsInducedOn ρ (conjL (Subgroup.mul_mem _ ha hb)) := by
  obtain ⟨φa, hφa⟩ := hia
  obtain ⟨φb, hφb⟩ := hib
  refine ⟨φa * φb, fun l => ?_⟩
  rw [conjL_mul ha hb, hφa, hφb]
  group

theorem isInducedOn_inv {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hia : IsInducedOn ρ (conjL ha)) : IsInducedOn ρ (conjL (Subgroup.inv_mem _ ha)) := by
  obtain ⟨φ, hφ⟩ := hia
  refine ⟨φ⁻¹, fun l => ?_⟩
  have h1 := hφ (conjL (Subgroup.inv_mem _ ha) l)
  rw [conjL_inv ha] at h1
  rw [h1]
  group

theorem isInducedOn_of_mem_normalizer (hLV : L ≤ Subgroup.normalizer (V : Set G)) {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (htV : t ∈ Subgroup.normalizer (V : Set G)) :
    IsInducedOn (conjHomL V L hLV) (conjL ht) := by
  refine ⟨conjV V t htV, fun l => ?_⟩
  rw [conjHomL_apply, conjHomL_apply, ← conjV_inv, ← conjV_mul, ← conjV_mul]
  rfl

theorem isXSectionIso₂_of_isInducedOn (hLV : L ≤ Subgroup.normalizer (V : Set G)) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hi : IsInducedOn (conjHomL V L hLV) (conjL hm)) :
    IsXSectionIso₂ L (CFSG.conjugate V m) ⊥ V ⊥ := by
  obtain ⟨φ, hφ⟩ := hi
  have hmap : (CFSG.conjugate V m).map (MulAut.conj m).toMonoidHom = V := by
    ext x
    rw [mem_map_conj, mem_conjugate']
    simp [mul_assoc]
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ↥(CFSG.conjugate V m) ≃* ↥V,
      ∀ a : ↥(CFSG.conjugate V m), ((e₁ a : ↥V) : G) = m * a * m⁻¹ :=
    ⟨((MulAut.conj m).subgroupMap (CFSG.conjugate V m)).trans (MulEquiv.subgroupCongr hmap),
      fun _ => rfl⟩
  refine isXSectionIso₂_of_equiv (e₁.trans φ⁻¹) ?_
  intro l hl a ha
  have key : e₁ ⟨l * a * l⁻¹, ha⟩ = conjHomL V L hLV (conjL hm ⟨l, hl⟩) (e₁ a) := by
    apply Subtype.ext
    rw [he₁, conjHomL_apply, conjV_apply_coe, conjL_coe, he₁]
    group
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, key, hφ, MulAut.mul_apply, MulAut.mul_apply,
    MulAut.inv_apply_self, conjHomL_apply, conjV_apply_coe]

theorem mem_pCoreOf_iff_of_mem_normalizer {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (x : G) : x ∈ pCoreOf 2 L ↔ m * x * m⁻¹ ∈ pCoreOf 2 L := by
  have h1 : (pCoreOf 2 L).map (MulAut.conj m⁻¹).toMonoidHom = pCoreOf 2 L := by
    rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv,
      map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ hm)]
  conv_lhs => rw [← h1]
  rw [mem_map_conj, inv_inv]

end CFSG.Quasithin.Vol2.Ch11.SecA
