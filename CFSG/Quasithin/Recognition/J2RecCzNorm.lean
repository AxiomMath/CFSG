module

public import CFSG.Quasithin.Recognition.J2RecCzAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

theorem czAct_trans (χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM)
    (g : MulAut QM) (c : ↥(Subgroup.centralizer ({z} : Set G))) :
    czAct (χ.trans g) c = g * czAct χ c * g⁻¹ := by
  refine MulEquiv.ext fun p => (χ.trans g).symm.injective (Subtype.ext ?_)
  rw [czAct_apply, MulAut.mul_apply, MulAut.mul_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_trans_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, czAct_apply]

variable [Finite G]

theorem exists_equiv_QM_complement (h : IsTypeH2 G z) {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLQ : L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥) (hL : Nat.card L = 60) :
    ∃ χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM,
      ((χ.symm J2Cz.QM.z : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = z ∧
      ∀ l (hl : l ∈ L), czAct χ ⟨l, hLC hl⟩ ∈ L0 := by
  obtain ⟨χ₀, hχ₀z⟩ := h.exists_equiv_QM
  set ψ : ↥L →* MulAut QM := (czAct χ₀).comp (Subgroup.inclusion hLC) with hψ
  set lam : ↥L →* Perm (Fin 5) := linePermHom.comp ψ with hlam
  have hlam_inj : Function.Injective lam := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 := h.mem_pCoreOf_of_linePerm_eq_one χ₀ (g := Subgroup.inclusion hLC l) hl
    have h2 : (l : G) ∈ L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := ⟨l.2, h1⟩
    rw [hLQ, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hlam_range : lam.range = alternatingGroup (Fin 5) := by
    apply Perm.eq_alternatingGroup_of_index_eq_two
    have h1 := lam.range.card_mul_index
    rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 from rfl] at h1
    have h2 : Nat.card lam.range = 60 := by
      rw [← hL]
      exact (Nat.card_congr (MonoidHom.ofInjective hlam_inj).toEquiv).symm
    rw [h2] at h1
    omega
  obtain ⟨ka, hka⟩ : pa ∈ lam.range := hlam_range ▸ pa_mem
  obtain ⟨kb, hkb⟩ : pb ∈ lam.range := hlam_range ▸ pb_mem
  have hka2 : ka * ka = 1 := hlam_inj (by rw [map_mul, hka, pa_sq, map_one])
  have hkb3 : kb * kb * kb = 1 := hlam_inj (by rw [map_mul, map_mul, hkb, pb_cube, map_one])
  have hA : ∀ j, ψ ka (x j) = x (pa j) ∨ ψ ka (x j) = J2Cz.QM.z * x (pa j) := fun j => by
    have := linePerm_spec (ψ ka) j
    rwa [show linePerm (ψ ka) = pa from hka] at this
  have hB : ∀ j, ψ kb (x j) = x (pb j) ∨ ψ kb (x j) = J2Cz.QM.z * x (pb j) := fun j => by
    have := linePerm_spec (ψ kb) j
    rwa [show linePerm (ψ kb) = pb from hkb] at this
  obtain ⟨g, hgA, hgB⟩ := exists_conj_eq_phi hA hB
    (by rw [← map_mul, hka2, map_one]) (by rw [← map_mul, ← map_mul, hkb3, map_one])
  have hcl : Subgroup.closure ({ka, kb} : Set ↥L) = ⊤ := by
    have hmap : (Subgroup.closure ({ka, kb} : Set ↥L)).map lam = alternatingGroup (Fin 5) := by
      rw [MonoidHom.map_closure, Set.image_pair, hka, hkb, closure_pa_pb]
    have hcard : Nat.card (Subgroup.closure ({ka, kb} : Set ↥L)) = 60 := by
      rw [← Subgroup.card_map_of_injective hlam_inj, hmap, nat_card_alternatingGroup,
        Nat.card_fin]
      rfl
    exact Subgroup.eq_top_of_card_eq _ (by rw [hcard, hL])
  refine ⟨χ₀.trans g, ?_, fun l hl => ?_⟩
  · rw [MulEquiv.symm_trans_apply, aut_z g.symm, hχ₀z]
  · have hle : Subgroup.closure ({ka, kb} : Set ↥L) ≤
        L0.comap ((czAct (χ₀.trans g)).comp (Subgroup.inclusion hLC)) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | hy)
      · show czAct (χ₀.trans g) (Subgroup.inclusion hLC y) ∈ L0
        rw [czAct_trans]
        rw [show czAct χ₀ (Subgroup.inclusion hLC y) = ψ y from rfl, hgA]
        exact phiA_mem
      · rw [Set.mem_singleton_iff.mp hy]
        show czAct (χ₀.trans g) (Subgroup.inclusion hLC kb) ∈ L0
        rw [czAct_trans]
        rw [show czAct χ₀ (Subgroup.inclusion hLC kb) = ψ kb from rfl, hgB]
        exact phiB_mem
    exact hle (hcl ▸ Subgroup.mem_top (⟨l, hl⟩ : ↥L))

omit [Finite G] in
theorem czAct_injOn (h : IsTypeH2 G z)
    (χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM)
    {L : Subgroup G} (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLQ : L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥) {l l' : G} (hl : l ∈ L)
    (hl' : l' ∈ L) (he : czAct χ ⟨l, hLC hl⟩ = czAct χ ⟨l', hLC hl'⟩) : l = l' := by
  have h1 : czAct χ (⟨l, hLC hl⟩⁻¹ * ⟨l', hLC hl'⟩) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have h2 : l⁻¹ * l' ∈ L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    refine ⟨L.mul_mem (L.inv_mem hl) hl', ?_⟩
    rcases h.eq_one_or_eq_of_czAct_eq_one χ h1 with h3 | h3
    · have : l⁻¹ * l' = 1 := h3
      rw [this]
      exact one_mem _
    · have : l⁻¹ * l' = z := h3
      rw [this]
      exact h.z_mem_pCoreOf
  rw [hLQ, Subgroup.mem_bot] at h2
  calc l = l * (l⁻¹ * l') := by rw [h2, mul_one]
    _ = l' := by group

omit [Finite G] in
theorem exists_mem_czAct_eq (h : IsTypeH2 G z)
    (χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM) {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLQ : L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥) (hL : Nat.card L = 60)
    (hχL : ∀ l (hl : l ∈ L), czAct χ ⟨l, hLC hl⟩ ∈ L0) {α : MulAut QM} (hα : α ∈ L0) :
    ∃ l, ∃ hl : l ∈ L, czAct χ ⟨l, hLC hl⟩ = α := by
  classical
  set f : ↥L → ↥L0 := fun l => ⟨czAct χ ⟨l, hLC l.2⟩, hχL l l.2⟩ with hf
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (h.czAct_injOn χ hLC hLQ a.2 b.2 (congrArg Subtype.val hab))
  have hcard : Nat.card ↥L0 ≤ Nat.card ↥L := by rw [hL]; exact card_L0_le
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hinj, le_antisymm (Nat.card_le_card_of_injective f hinj) hcard⟩
  obtain ⟨l, hl⟩ := hbij.2 ⟨α, hα⟩
  exact ⟨l, l.2, congrArg Subtype.val hl⟩

end IsTypeH2

end CFSG.Quasithin
