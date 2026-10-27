module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2014d_mem_barImage_iff (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (l : ↥L) : (QuotientGroup.mk l : Bar2 L) ∈ barImage L (D.M ⊓ L) ↔ (l : G) ∈ D.M := by
  constructor
  · rintro ⟨a, ha, he⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    have h2 : ((a⁻¹ * l : ↥L) : G) ∈ D.M :=
      D.sylowM.le (uc22p20i_pCoreOf_le D hL ⟨_, he, rfl⟩).1
    have h3 : (a : G) ∈ D.M := (Subgroup.mem_subgroupOf.1 ha).1
    simpa using D.M.mul_mem h3 h2
  · intro h
    exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨h, l.2⟩, rfl⟩

theorem uc22p2014d_barImage_ne_top (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    barImage L (D.M ⊓ L) ≠ ⊤ := by
  intro h
  refine uc22p20i_not_le_M D hL fun l hl => ?_
  refine (uc22p2014d_mem_barImage_iff D hL ⟨l, hl⟩).1 ?_
  rw [h]
  exact Subgroup.mem_top _

theorem uc22p2014d_isParabolicTwo (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) : IsParabolicTwo (Bar2 L) (barImage L (D.M ⊓ L)) :=
  (uc22p20i_inf_parabolic D hB h1930 hL).1.2.2

theorem uc22p2014d_not_dvd_card_inf_conj (D : Data G) {p : ℕ} (hsp : IsStronglyPEmbedded p D.M)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) (w : Bar2 L) (hw : w ∉ barImage L (D.M ⊓ L)) :
    ¬ p ∣ Nat.card ↥(barImage L (D.M ⊓ L) ⊓
      (barImage L (D.M ⊓ L)).map (MulAut.conj w).toMonoidHom) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
  have hlM : (l : G) ∉ D.M := fun h => hw ((uc22p2014d_mem_barImage_iff D hL l).2 h)
  set S : Subgroup G := D.M ⊓ D.M.map (MulAut.conj (l : G)).toMonoidHom with hS
  have hpS : ¬ p ∣ Nat.card S := hsp.2.2 l hlM
  have hle : barImage L (D.M ⊓ L) ⊓
      (barImage L (D.M ⊓ L)).map (MulAut.conj (QuotientGroup.mk l : Bar2 L)).toMonoidHom ≤
      (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rintro y ⟨hy1, hy2⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy2
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    have hz' : (z' : G) ∈ D.M := (uc22p2014d_mem_barImage_iff D hL z').1 hz
    have e : (MulAut.conj (QuotientGroup.mk l : Bar2 L)).toMonoidHom (QuotientGroup.mk z') =
        (QuotientGroup.mk (l * z' * l⁻¹) : Bar2 L) := by
      simp [MulAut.conj_apply]
    rw [e] at hy1 ⊢
    refine ⟨l * z' * l⁻¹, Subgroup.mem_subgroupOf.2
      ⟨(uc22p2014d_mem_barImage_iff D hL _).1 hy1, z', hz', ?_⟩, rfl⟩
    simp [MulAut.conj_apply]
  intro hp
  apply hpS
  have h3 : Nat.card (S.subgroupOf L) ∣ Nat.card S := by
    rw [← Subgroup.card_map_of_injective L.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact hp.trans ((Subgroup.card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans h3))

theorem uc22p2014d_map_barImage {L A : Subgroup G} {x : G} (hxL : x ∈ normalizer (L : Set G))
    (hxA : x ∈ normalizer (A : Set G)) :
    (barImage L A).map (UC6S846.rhoL L ⟨x, hxL⟩).toMonoidHom = barImage L A := by
  have hle : (barImage L A).map (UC6S846.rhoL L ⟨x, hxL⟩).toMonoidHom ≤ barImage L A := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨Subgroup.normalizerMonoidHom L ⟨x, hxL⟩ a, ?_, (UC6S846.rhoL_mk L _ a).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, UC6S846.rhoL_mk_coe]
    exact (Subgroup.mem_normalizer_iff.1 hxA _).1 (Subgroup.mem_subgroupOf.1 ha)
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge

theorem uc22p2014d_mem_of_inv_mul_mem (D : Data G) {p : ℕ} (hp : p.Prime)
    (hsp : IsStronglyPEmbedded p D.M) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {x : G}
    (hxL : x ∈ normalizer (L : Set G)) (hxM : x ∈ D.M) (hxp : IsPGroup p (zpowers x))
    (hx1 : x ≠ 1) (w : Bar2 L)
    (h : w⁻¹ * UC6S846.rhoL L ⟨x, hxL⟩ w ∈ barImage L (D.M ⊓ L)) : w ∈ barImage L (D.M ⊓ L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
  rw [uc22p2014d_mem_barImage_iff D hL]
  rw [UC6S846.rhoL_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    uc22p2014d_mem_barImage_iff D hL] at h
  have h1 : (l : G)⁻¹ * (x * l * x⁻¹) ∈ D.M := by
    simpa [UC6S846.rhoL_mk_coe] using h
  have h' : (l : G)⁻¹ * x * (l : G)⁻¹⁻¹ ∈ D.M := by
    have e : (l : G)⁻¹ * x * (l : G)⁻¹⁻¹ = (l : G)⁻¹ * (x * l * x⁻¹) * x := by group
    rw [e]
    exact D.M.mul_mem h1 hxM
  have hl := uc22p2014a_mem_of_conj_mem hsp hxp (zpowers_le.2 hxM) (mem_zpowers x) hx1 h'
  simpa using D.M.inv_mem hl

end CFSG.LocalAnalysis.UniquenessCase.UC22
