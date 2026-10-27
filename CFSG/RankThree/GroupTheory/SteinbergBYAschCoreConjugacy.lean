module

public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.Assembly.RankThreeEven

variable {G : Type*} [Group G]

theorem map_centralizer_mulEquiv {G' : Type*} [Group G'] (φ : G ≃* G') (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((X.map φ.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    have := congrArg φ (h x hx)
    simpa using this
  · intro h x hx
    apply φ.injective
    have := h (φ x) ⟨x, hx, rfl⟩
    simpa using this

theorem assembly_pRank_map_mulEquiv [Finite G] {p : ℕ} (hp : 1 < p) (φ : G ≃* G)
    (X : Subgroup G) :
    CFSG.Assembly.pRank p (X.map φ.toMonoidHom) = CFSG.Assembly.pRank p X := by
  change Open.pRank p (X.map φ.toMonoidHom) = Open.pRank p X
  apply le_antisymm
  · have h := SectionRank.pRank_le_map hp φ.symm.toMonoidHom φ.symm.injective
      (X.map φ.toMonoidHom)
    have hcomp : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext fun x => φ.symm_apply_apply x
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h
  · exact SectionRank.pRank_le_map hp φ.toMonoidHom φ.injective X

theorem map_aschCore_le [Finite G] {p : ℕ} (hp : 1 < p) (k : ℕ) (φ : G ≃* G)
    (P : Subgroup G) :
    (aschCore k p P).map φ.toMonoidHom ≤ aschCore k p (P.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N ⟨X, hXP, hk, h3, hN⟩ => ?_
  rw [hN, ← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
  refine le_sSup ⟨X.map φ.toMonoidHom, Subgroup.map_mono hXP, ?_, ?_, rfl⟩
  · rwa [assembly_pRank_map_mulEquiv hp]
  · rwa [← map_centralizer_mulEquiv, ← Subgroup.map_inf_eq _ _ _ φ.injective,
      ← Subgroup.map_sup, assembly_pRank_map_mulEquiv hp]

theorem map_aschCore_mulEquiv [Finite G] {p : ℕ} (hp : 1 < p) (k : ℕ) (φ : G ≃* G)
    (P : Subgroup G) :
    (aschCore k p P).map φ.toMonoidHom = aschCore k p (P.map φ.toMonoidHom) := by
  refine le_antisymm (map_aschCore_le hp k φ P) ?_
  have hcomp : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => φ.apply_symm_apply x
  have hcomp' : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => φ.symm_apply_apply x
  have h := Subgroup.map_mono (f := φ.toMonoidHom)
    (map_aschCore_le hp k φ.symm (P.map φ.toMonoidHom))
  rwa [Subgroup.map_map, Subgroup.map_map, hcomp', Subgroup.map_id, hcomp, Subgroup.map_id] at h

theorem isPLocal_map_mulEquiv {r : ℕ} (φ : G ≃* G) {H : Subgroup G} (hH : IsPLocal r H) :
    IsPLocal r (H.map φ.toMonoidHom) := by
  obtain ⟨U, hU1, hU, rfl⟩ := hH
  refine ⟨U.map φ.toMonoidHom, ?_, hU.map φ.toMonoidHom, Subgroup.map_equiv_normalizer_eq U φ⟩
  rwa [Ne, Subgroup.map_eq_bot_iff_of_injective U φ.injective]

theorem aschbacher_core_conjugacy [Finite G] {p : ℕ} (hp : p.Prime) (k : ℕ) (P : Subgroup G) :
    (∀ g : G, conjugate (aschCore k p P) g = aschCore k p (conjugate P g)) ∧
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (aschCore k p P : Set G) ∧
      ∀ S : Sylow p G, (S : Subgroup G) = P →
        ((∃ H : Subgroup G, IsPLocal 2 H ∧ aschCore k p P ≤ H) ↔
          ∀ S' : Sylow p G, ∃ H' : Subgroup G, IsPLocal 2 H' ∧
            aschCore k p (S' : Subgroup G) ≤ H') := by
  have : Fact p.Prime := ⟨hp⟩
  have hconj : ∀ g : G, conjugate (aschCore k p P) g = aschCore k p (conjugate P g) :=
    fun g => map_aschCore_mulEquiv hp.one_lt k (MulAut.conj g⁻¹) P
  refine ⟨hconj, fun g hg => ?_, fun S hS => ⟨fun ⟨H, hH, hΓ⟩ S' => ?_, fun h => ?_⟩⟩
  ·
    have hP : P.map (MulAut.conj g⁻¹).toMonoidHom = P :=
      map_conj_eq_of_mem_normalizer (inv_mem hg)
    have hΓ : (aschCore k p P).map (MulAut.conj g⁻¹).toMonoidHom = aschCore k p P := by
      rw [map_aschCore_mulEquiv hp.one_lt, hP]
    simpa using inv_mem (mem_normalizer_of_map_conj_eq hΓ)
  ·
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
    have hS' : (S' : Subgroup G) = P.map (MulAut.conj g).toMonoidHom := by
      rw [← hg, ← hS]
      rfl
    refine ⟨H.map (MulAut.conj g).toMonoidHom, isPLocal_map_mulEquiv _ hH, ?_⟩
    rw [hS', ← map_aschCore_mulEquiv hp.one_lt]
    exact Subgroup.map_mono hΓ
  · obtain ⟨H, hH, hΓ⟩ := h S
    exact ⟨H, hH, hS ▸ hΓ⟩

end CFSG.RankThree.GroupTheory.SteinbergBY
