module

public import CFSG.Quasithin.Background.HZ82Base

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

@[expose] def comm_sd4 {V : Type} [CommGroup V] (Y : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {x | ∃ y ∈ Y, ∃ v : V, x = y v * v⁻¹}

@[expose] def D4P_sd4 {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) (U : Subgroup V) :
    Subgroup (MulAut V) :=
  perfectCore (H ⊓ stabSub U)

@[expose] def D4N_sd4 {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) (U : Subgroup V) :
    Subgroup V :=
  comm_sd4 (D4P_sd4 H U)

@[expose] def D4NF_sd4 {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) (U : Subgroup V) :
    Prop :=
  U ≤ D4N_sd4 H U ∧
  Nat.card ↥(D4N_sd4 H U) = 16 * Nat.card ↥U ∧
  (∀ C : Subgroup V, U ≤ C → C ≤ D4N_sd4 H U →
    (∀ p ∈ D4P_sd4 H U, ∀ c ∈ C, p c ∈ C) → C = U ∨ C = D4N_sd4 H U) ∧
  ∃ p ∈ D4P_sd4 H U, ∃ q ∈ D4P_sd4 H U, ∃ n ∈ D4N_sd4 H U,
    ((⁅p, q⁆ : MulAut V)⁻¹ n) * n⁻¹ ∉ U

section Transport

variable {V W : Type} [CommGroup V] [CommGroup W]

theorem comm_sd4_map_sd4 (e : V ≃* W) (Y : Subgroup (MulAut V)) :
    (comm_sd4 Y).map e.toMonoidHom = comm_sd4 (Y.map (CFSG.Quasithin.H.congrHom e)) := by
  unfold comm_sd4
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨s, ⟨y, hy, v, rfl⟩, rfl⟩
    refine ⟨CFSG.Quasithin.H.congrHom e y, Subgroup.mem_map_of_mem _ hy,
      e v, ?_⟩
    simp [CFSG.Quasithin.H.congrHom_apply]
  · rintro ⟨y', hy', w, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy'
    refine ⟨y (e.symm w) * (e.symm w)⁻¹, ⟨y, hy, e.symm w, rfl⟩, ?_⟩
    simp [CFSG.Quasithin.H.congrHom_apply]

theorem D4P_sd4_map_sd4 [Finite V] [Finite W] (e : V ≃* W) (H : Subgroup (MulAut V))
    (U : Subgroup V) :
    D4P_sd4 (H.map (CFSG.Quasithin.H.congrHom e)) (U.map e.toMonoidHom) =
      (D4P_sd4 H U).map (CFSG.Quasithin.H.congrHom e) := by
  unfold D4P_sd4
  rw [CFSG.Quasithin.H.ZTrans.stabSub_map_congrHom, ← CFSG.Quasithin.H.ZTrans.perfectCore_map_congrHom,
    ← Subgroup.map_inf _ _ _ (CFSG.Quasithin.H.congrHom_injective e)]

theorem map_equiv_symm_map_sd4 (e : V ≃* W) (U : Subgroup V) :
    (U.map e.toMonoidHom).map e.symm.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id V := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem D4NF_sd4_of_equiv_sd4 [Finite V] [Finite W] (e : V ≃* W) (H : Subgroup (MulAut V))
    (U : Subgroup V) (h : D4NF_sd4 H U) :
    D4NF_sd4 (H.map (CFSG.Quasithin.H.congrHom e)) (U.map e.toMonoidHom) := by
  obtain ⟨hUN, hcard, hirr, p, hp, q, hq, n, hn, hnab⟩ := h
  have hNmap : D4N_sd4 (H.map (CFSG.Quasithin.H.congrHom e)) (U.map e.toMonoidHom) =
      (D4N_sd4 H U).map e.toMonoidHom := by
    unfold D4N_sd4
    rw [D4P_sd4_map_sd4, comm_sd4_map_sd4]
  have hPmem : ∀ x ∈ D4P_sd4 H U,
      CFSG.Quasithin.H.congrHom e x ∈ D4P_sd4 (H.map (CFSG.Quasithin.H.congrHom e))
        (U.map e.toMonoidHom) := by
    intro x hx
    rw [D4P_sd4_map_sd4]
    exact Subgroup.mem_map_of_mem _ hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hNmap]
    exact Subgroup.map_mono hUN
  · rw [hNmap, Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective e.injective]
    exact hcard
  · intro C' hU'C' hC'N' hinv'
    set C := C'.comap e.toMonoidHom with hC
    have hUC : U ≤ C := by
      intro u hu
      exact hU'C' (Subgroup.mem_map_of_mem _ hu)
    have hCN : C ≤ D4N_sd4 H U := by
      intro c hc
      have h1 : e c ∈ D4N_sd4 (H.map (CFSG.Quasithin.H.congrHom e)) (U.map e.toMonoidHom) :=
        hC'N' hc
      rw [hNmap] at h1
      obtain ⟨c', hc', hec⟩ := Subgroup.mem_map.mp h1
      have : c' = c := e.injective hec
      exact this ▸ hc'
    have hinv : ∀ p ∈ D4P_sd4 H U, ∀ c ∈ C, p c ∈ C := by
      intro p hp c hc
      show e (p c) ∈ C'
      have := hinv' _ (hPmem p hp) (e c) hc
      simpa [CFSG.Quasithin.H.congrHom_apply] using this
    have hsurj : Function.Surjective e.toMonoidHom := e.surjective
    have hmapC : C.map e.toMonoidHom = C' := Subgroup.map_comap_eq_self_of_surjective hsurj C'
    rcases hirr C hUC hCN hinv with hC1 | hC1
    · left
      rw [← hmapC, hC1]
    · right
      rw [← hmapC, hC1, hNmap]
  · have happ : ∀ (φ : MulAut V) (m : V), (CFSG.Quasithin.H.congrHom e φ) (e m) = e (φ m) := by
      intro φ m
      simp [CFSG.Quasithin.H.congrHom_apply]
    refine ⟨CFSG.Quasithin.H.congrHom e p, hPmem p hp, CFSG.Quasithin.H.congrHom e q,
      hPmem q hq, e n, ?_, ?_⟩
    · rw [hNmap]
      exact Subgroup.mem_map_of_mem _ hn
    · intro hmem
      apply hnab
      rw [Subgroup.mem_map_equiv] at hmem
      have hcomm : CFSG.Quasithin.H.congrHom e ⁅p, q⁆⁻¹ =
          ⁅CFSG.Quasithin.H.congrHom e p, CFSG.Quasithin.H.congrHom e q⁆⁻¹ := by
        rw [map_inv, map_commutatorElement]
      rw [← hcomm, happ, ← map_inv e n, ← map_mul e, MulEquiv.symm_apply_apply] at hmem
      exact hmem

end Transport

end CFSG.Quasithin.H13.L829N
