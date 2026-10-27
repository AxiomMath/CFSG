module

public import CFSG.Quasithin.MS93.S46Base
public import CFSG.Quasithin.MS93.S4ABasic

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Hol

variable {G : Type} [Group G] [Finite G] {M T : Subgroup G} (hTM : T ≤ M)

omit [Finite G] in
theorem qv_baseB_eq_range :
    Qv (puAmalgam hTM) (baseB _) = (puAmalgam.ofT hTM).range := by
  rw [puAmalgam.qv_baseB, imM_of_le hTM le_rfl, Subgroup.subgroupOf_self,
    ← MonoidHom.range_eq_map]

omit [Finite G] in
theorem ofT_injective : Function.Injective (puAmalgam.ofT hTM) :=
  (puAmalgam hTM).ofB_injective.comp SemidirectProduct.inl_injective

theorem exists_stab_baseB_conj_eq {n : (puAmalgam hTM).Universal}
    (hn : n ∈ Subgroup.normalizer
      (Qv (puAmalgam hTM) (baseB _) : Set (puAmalgam hTM).Universal)) :
    ∃ h ∈ stab (puAmalgam hTM) (baseB _), ∀ t ∈ Qv (puAmalgam hTM) (baseB _),
      n * t * n⁻¹ = h * t * h⁻¹ := by
  have hR := qv_baseB_eq_range hTM
  have hinj := ofT_injective hTM
  have hmem : ∀ t : ↥T, n * puAmalgam.ofT hTM t * n⁻¹ ∈ (puAmalgam.ofT hTM).range := by
    intro t
    rw [← hR]
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hR ▸ ⟨t, rfl⟩)
  set e := MonoidHom.ofInjective hinj with he
  set c : ↥T →* ↥(puAmalgam.ofT hTM).range :=
    ((MulAut.conj n).toMonoidHom.comp (puAmalgam.ofT hTM)).codRestrict _ hmem with hc
  set σ₀ : ↥T →* ↥T := e.symm.toMonoidHom.comp c with hσ₀
  have hσ₀e : ∀ t, puAmalgam.ofT hTM (σ₀ t) = n * puAmalgam.ofT hTM t * n⁻¹ := by
    intro t
    have h1 : (e (σ₀ t) : (puAmalgam hTM).Universal) = puAmalgam.ofT hTM (σ₀ t) :=
      MonoidHom.ofInjective_apply hinj
    rw [← h1]
    have h2 : e (σ₀ t) = c t := by
      rw [hσ₀]
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.apply_symm_apply]
    rw [h2]
    rfl
  have hσinj : Function.Injective σ₀ := by
    intro t t' htt
    apply hinj
    have h1 := hσ₀e t
    have h2 := hσ₀e t'
    rw [htt] at h1
    have := h1.symm.trans h2
    have e2 : puAmalgam.ofT hTM t = n⁻¹ * (n * puAmalgam.ofT hTM t * n⁻¹) * n := by group
    have e3 : puAmalgam.ofT hTM t' = n⁻¹ * (n * puAmalgam.ofT hTM t' * n⁻¹) * n := by group
    rw [e2, e3, this]
  have hσbij : Function.Bijective σ₀ := ⟨hσinj, Finite.surjective_of_injective hσinj⟩
  set σ : MulAut ↥T := MulEquiv.ofBijective σ₀ hσbij with hσ
  refine ⟨(puAmalgam hTM).ofB (SemidirectProduct.inr σ), ?_, ?_⟩
  · rw [puAmalgam.stab_baseB]
    exact ⟨_, rfl⟩
  · intro t ht
    rw [hR] at ht
    obtain ⟨t₀, rfl⟩ := ht
    rw [← hσ₀e t₀]
    have := congrArg (puAmalgam hTM).ofB (Hol.inr_mul_inl_mul_inr_inv σ t₀)
    simp only [map_mul, map_inv] at this
    rw [show puAmalgam.ofT hTM (σ₀ t₀) = (puAmalgam hTM).ofB (SemidirectProduct.inl (σ t₀)) from
      rfl, ← this]
    rfl

theorem le_normalizer_of_normalizer_qv_baseB {K : Subgroup (puAmalgam hTM).Universal}
    (hKT : K ≤ Qv (puAmalgam hTM) (baseB _))
    (hKn : stab (puAmalgam hTM) (baseB _) ≤
      Subgroup.normalizer (K : Set (puAmalgam hTM).Universal)) :
    Subgroup.normalizer (Qv (puAmalgam hTM) (baseB _) : Set (puAmalgam hTM).Universal) ≤
      Subgroup.normalizer (K : Set (puAmalgam hTM).Universal) := by
  have key : ∀ n ∈ Subgroup.normalizer
      (Qv (puAmalgam hTM) (baseB _) : Set (puAmalgam hTM).Universal),
      ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
    intro n hn k hk
    obtain ⟨h, hh, hconj⟩ := exists_stab_baseB_conj_eq hTM hn
    rw [hconj k (hKT hk)]
    exact (Subgroup.mem_normalizer_iff.mp (hKn hh) k).mp hk
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key n hn k, fun hk => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hk
  simpa [mul_assoc] using this

end Hol

section General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem le_normalizer_of_normalizer_qv {β : Vtx (puAmalgam h.le)}
    (hβ : ¬ IsMVtx (puAmalgam h.le) β) {K : Subgroup (puAmalgam h.le).Universal}
    (hKT : K ≤ Qv (puAmalgam h.le) β)
    (hKn : stab (puAmalgam h.le) β ≤
      Subgroup.normalizer (K : Set (puAmalgam h.le).Universal)) :
    Subgroup.normalizer (Qv (puAmalgam h.le) β : Set (puAmalgam h.le).Universal) ≤
      Subgroup.normalizer (K : Set (puAmalgam h.le).Universal) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseB _ hβ
  set K₀ := K.map (MulAut.conj g⁻¹).toMonoidHom with hK₀
  have hK : K = K₀.map (MulAut.conj g).toMonoidHom := by
    rw [hK₀, Subgroup.map_map]
    have : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hK₀T : K₀ ≤ Qv (puAmalgam h.le) (baseB _) := by
    rw [hK, qv_smul, map_conj_le_map_conj_iff] at hKT
    exact hKT
  have hK₀n : stab (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (K₀ : Set (puAmalgam h.le).Universal) := by
    rw [hK, stab_smul, normalizer_map_conj, map_conj_le_map_conj_iff] at hKn
    exact hKn
  have hbase := le_normalizer_of_normalizer_qv_baseB h.le hK₀T hK₀n
  rw [hK, qv_smul, normalizer_map_conj, normalizer_map_conj]
  exact Subgroup.map_mono hbase

theorem normalizer_qv_le_normalizer_vv {β : Vtx (puAmalgam h.le)}
    (hβ : ¬ IsMVtx (puAmalgam h.le) β) :
    Subgroup.normalizer (Qv (puAmalgam h.le) β : Set (puAmalgam h.le).Universal) ≤
      Subgroup.normalizer (Vv (puAmalgam h.le) β : Set (puAmalgam h.le).Universal) := by
  refine le_normalizer_of_normalizer_qv h hβ ?_ (stab_le_normalizer_vv h β)
  rw [vv_eq_iSup_of_not_isMVtx hβ]
  refine iSup₂_le fun δ hδ => ?_
  have hδM : IsMVtx (puAmalgam h.le) δ := by have := isMVtx_iff_of_adj _ hδ; tauto
  exact (zm_le_qv_self _ hδM h.critDist_pos).trans (qv_le_qv _ h.hyp20 hδM hδ.symm)

theorem vv_smul_eq_of_mem_normalizer {β : Vtx (puAmalgam h.le)}
    (hβ : ¬ IsMVtx (puAmalgam h.le) β) {n : (puAmalgam h.le).Universal}
    (hn : n ∈ Subgroup.normalizer (Qv (puAmalgam h.le) β : Set (puAmalgam h.le).Universal)) :
    Vv (puAmalgam h.le) (n • β) = Vv (puAmalgam h.le) β := by
  rw [show Vv (puAmalgam h.le) (n • β) = Vi _ (n • β) 2 from rfl, vi_smul]
  exact map_conj_eq_of_mem_normalizer (normalizer_qv_le_normalizer_vv h hβ hn)

end General

end CFSG.Quasithin.MS93.S46
