module

public import CFSG.Quasithin.EmptyFaithful.SzF53B1C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B1

section Hyp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace B1Hyp

theorem commutator_Qa_oTwoUpper_le (h : B1Hyp H M S) :
    ⁅pCoreOf 2 H, oTwoUpper H⁆ ≤ VZ S H := by
  obtain ⟨x, hx, hxH⟩ := h.exists_x
  have hZaN := h.H_le_normalizer_Za
  have hQaN := h.H_le_normalizer_Qa
  let C : Subgroup G :=
    { carrier := {g | g ∈ H ∧ ∀ q ∈ pCoreOf 2 H, ⁅q, g⁆ ∈ VZ S H}
      one_mem' := ⟨H.one_mem, fun q _ => by simp [(VZ S H).one_mem]⟩
      mul_mem' := by
        rintro g g' ⟨hg, hgC⟩ ⟨hg', hgC'⟩
        refine ⟨H.mul_mem hg hg', fun q hq => ?_⟩
        have e : ⁅q, g * g'⁆ = ⁅q, g⁆ * (g * ⁅q, g'⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (VZ S H).mul_mem (hgC q hq) ((Subgroup.mem_normalizer_iff.mp (hZaN hg) _).mp
          (hgC' q hq))
      inv_mem' := by
        rintro g ⟨hg, hgC⟩
        refine ⟨H.inv_mem hg, fun q hq => ?_⟩
        have e : ⁅q, g⁻¹⁆ = g⁻¹ * (⁅q, g⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hZaN (H.inv_mem hg)) _).mp
          ((VZ S H).inv_mem (hgC q hq)) }
  have hCH : C ≤ H := fun _ hg => hg.1
  have key : ∀ k ∈ H, ∀ g ∈ C, k * g * k⁻¹ ∈ C := by
    rintro k hk g ⟨hg, hgC⟩
    refine ⟨H.mul_mem (H.mul_mem hk hg) (H.inv_mem hk), fun q hq => ?_⟩
    have hq' : k⁻¹ * q * k ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (hQaN (H.inv_mem hk)) q).mp hq
      simpa using this
    have e : ⁅q, k * g * k⁻¹⁆ = k * ⁅k⁻¹ * q * k, g⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hZaN hk) _).mp (hgC _ hq')
  have hCn : H ≤ Subgroup.normalizer (C : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key k hk y hy, fun hy => ?_⟩
    have := key k⁻¹ (H.inv_mem hk) _ hy
    simpa [mul_assoc] using this
  have hQC : pCoreOf 2 H ≤ C := by
    intro g hg
    refine ⟨pCoreOf_le 2 H hg, fun q hq => ?_⟩
    have : ⁅q, g⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (F7.isElemAbelian_comm h.isElemAbelian_Qa hq hg)
    rw [this]
    exact (VZ S H).one_mem
  have hTN : pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H) ≤ Subgroup.normalizer (VZ S H : Set G) :=
    fun g hg => h.S_le_normalizer_Za (h.Qa_le_S hg.1)
  have hHaC : conjSub x (VZ S H) ⊓ pCoreOf 2 M ≤ C := by
    intro g hg
    have hgH : g ∈ H := h.S_le_H (h.Qb_le_S hg.2)
    refine ⟨hgH, fun q hq => ?_⟩
    have hq' : q ∈ (pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) ⊔ VZ S H := by
      rw [← h.Qa_eq_sup hx hxH]; exact hq
    obtain ⟨u, hu, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hTN).mp hq'
    have e : ⁅u * z, g⁆ = u * ⁅z, g⁆ * u⁻¹ * ⁅u, g⁆ := by
      simp only [commutatorElement_def]; group
    have hug : ⁅u, g⁆ = 1 := by
      have hc : u * g = g * u :=
        Subgroup.mem_centralizer_iff.mp (h.Za2_le_centralizer_Qa2 x hg.1) u hu.2
      exact commutatorElement_eq_one_iff_mul_comm.mpr hc
    have hzg : ⁅z, g⁆ ∈ VZ S H := by
      have e2 : ⁅z, g⁆ = z * (g * z⁻¹ * g⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e2]
      exact (VZ S H).mul_mem hz ((Subgroup.mem_normalizer_iff.mp (hZaN hgH) _).mp
        ((VZ S H).inv_mem hz))
    rw [e, hug]
    refine (VZ S H).mul_mem ?_ (VZ S H).one_mem
    exact (Subgroup.mem_normalizer_iff.mp (hZaN (pCoreOf_le 2 H hu.1)) _).mp hzg
  obtain ⟨ι⟩ := h.amalgam.quot_left
  let π : ↥H →* Equiv.Perm (Fin 5) :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  have hπ : Function.Surjective π := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = (pCoreOf 2 H).subgroupOf H := by
    rw [pCoreOf_subgroupOf]
    ext y
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hCn' : (C.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCn
  have hCbar : ((C.subgroupOf H).map π).Normal := Subgroup.Normal.map hCn' π hπ
  have hnt : Nontrivial ↥((C.subgroupOf H).map π) := by
    obtain ⟨g, hgHa, hgQ⟩ := IsConcreteLE.not_le_iff_exists.mp (h.not_Ha2_le_Qa hx hxH)
    have hgH : g ∈ H := h.S_le_H (h.Qb_le_S hgHa.2)
    have hgC : (⟨g, hgH⟩ : ↥H) ∈ C.subgroupOf H := hHaC hgHa
    have hπg : π ⟨g, hgH⟩ ≠ 1 := by
      intro h1
      apply hgQ
      have : (⟨g, hgH⟩ : ↥H) ∈ π.ker := h1
      rw [hker] at this
      exact this
    exact ⟨⟨π ⟨g, hgH⟩, ⟨_, hgC, rfl⟩⟩, 1, fun h2 => hπg (congrArg Subtype.val h2)⟩
  have hA5 : alternatingGroup (Fin 5) ≤ (C.subgroupOf H).map π :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
  have hsq : ∀ g ∈ H, g ^ 2 ∈ C := by
    intro g hg
    have hsign : Equiv.Perm.sign (π ⟨g, hg⟩ ^ 2) = 1 := by
      rw [map_pow, Int.units_pow_two]
    have hmem : π ⟨g, hg⟩ ^ 2 ∈ (C.subgroupOf H).map π :=
      hA5 (Equiv.Perm.mem_alternatingGroup.mpr hsign)
    obtain ⟨c, hc, hcπ⟩ := hmem
    have hdiff : c⁻¹ * (⟨g, hg⟩ : ↥H) ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hcπ]
      group
    rw [hker] at hdiff
    have hdiffC : c⁻¹ * (⟨g, hg⟩ : ↥H) ^ 2 ∈ C.subgroupOf H := hQC hdiff
    have h2 := (C.subgroupOf H).mul_mem hc hdiffC
    have h3 : (⟨g, hg⟩ : ↥H) ^ 2 ∈ C.subgroupOf H := by simpa using h2
    exact h3
  have hOC : oTwoUpper H ≤ C := oTwoUpper_le_of_pow_mem fun g hg =>
    ⟨1, by rw [pow_one]; exact hsq g hg⟩
  rw [Subgroup.commutator_le]
  intro q hq g hg
  exact (hOC hg).2 q hq

theorem eta_Qa (h : B1Hyp H M S) : F112W.eta H (pCoreOf 2 H) (pCoreOf 2 H) = 1 := by
  have hUH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hNz : IsNormalIn H (pCoreOf 2 H) (VZ S H) :=
    F112W.isNormalIn_of_le_normalizer h.Za_le_Qa h.H_le_normalizer_Za
  have hNq : IsNormalIn H (pCoreOf 2 H) (pCoreOf 2 H) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (le_normalizer_pCoreOf 2 H)
  rw [F112W.eta_eq_of_commutator_le hUH le_rfl hNz hNq h.Za_le_Qa h.commutator_Qa_oTwoUpper_le]
  exact (F112W.isChiefSeriesFrom_iff_eta hUH hNz).mp h.isChiefSeriesFrom_Za

theorem not_F53EData (h : B1Hyp H M S) {E : Subgroup G} (hE : F53EData H S E) : False := by
  have hEQ : E ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hE.le.trans h.S_le_H) hE.normal
      (h.sylow_H.2.1.to_le hE.le)
  have hch : IsChiefSeriesFrom H (pCoreOf 2 H) E 2 := isChiefSeriesFrom_mono_left hEQ hE.chief
  have hUH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hNE : IsNormalIn H (pCoreOf 2 H) E := F112W.isNormalIn_of_le_normalizer hEQ hE.normal
  have hNQ : IsNormalIn H (pCoreOf 2 H) (pCoreOf 2 H) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (le_normalizer_pCoreOf 2 H)
  have e1 : F112W.eta H (pCoreOf 2 H) E = 2 := (F112W.isChiefSeriesFrom_iff_eta hUH hNE).mp hch
  have e2 := F112W.eta_le_of_le hUH hNE hNQ hEQ
  rw [e1, h.eta_Qa] at e2
  omega

end B1Hyp

end Hyp

end F53B1

end CFSG.Quasithin
