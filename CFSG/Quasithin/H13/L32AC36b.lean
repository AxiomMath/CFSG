module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22

public section

namespace CFSG.Quasithin.H13.L32A.C.M22Hex

open Equiv CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat PermLat

theorem closure_le_of_words {G : Type*} [Group G] {A B : List G} (ws : List (List ℕ))
    (h : ∀ k (hk : k < A.length), A[k] = evalW B (ws.getD k [])) :
    Subgroup.closure {g | g ∈ A} ≤ Subgroup.closure {g | g ∈ B} := by
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [h k hk]
  exact evalW_mem_closure B _

theorem len_eq : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]

abbrev hexGens : List (Perm (Fin 22)) := (cert.tGens :: cert.lat)[3]'(by rw [len_eq]; norm_num)

abbrev hex : Subgroup (Perm (Fin 22)) := Subgroup.closure {g | g ∈ hexGens}

theorem hex_le_M : hex ≤ Mgrp :=
  closure_le_of_words (B := cert.mGens)
    [[1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
      [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0],
      [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0,
        1, 0, 1, 0, 1, 1],
      [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0,
        1, 1]]
    (by decide +kernel)

theorem t_le_hex : Subgroup.closure {g | g ∈ cert.tGens} ≤ hex :=
  closure_le_of_words [[0], [1], [2]] (by decide +kernel)

theorem p1_le_hex :
    Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[1]'(by rw [len_eq]; norm_num)} ≤ hex :=
  closure_le_of_words [[0], [1], [2], [1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 3, 1]] (by decide +kernel)

theorem p5_le_hex :
    Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[5]'(by rw [len_eq]; norm_num)} ≤ hex :=
  closure_le_of_words [[0], [1], [2], [1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2]] (by decide +kernel)

abbrev hexM : Subgroup ↥Mgrp := hex.subgroupOf Mgrp

theorem card_hexM : Nat.card hexM = 5760 := by
  have hck := cert_check
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hex_le_M).toEquiv]
  exact cert.card_member_idx (rawIsEnc 22) (LatCert.closedOK_of_check hck)
    (LatCert.sizesOK_of_check hck) 3 _

theorem card_U : Nat.card Ugrp = 128 := by
  have hck := cert_check
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (t_le_hex.trans hex_le_M)).toEquiv]
  exact cert.card_t (rawIsEnc 22) (LatCert.closedOK_of_check hck) (LatCert.sizesOK_of_check hck)

theorem le_hex {P : Subgroup ↥Mgrp} (hUP : Ugrp ≤ P)
    (h3 : Ugrp.relIndex P = 3) : P ≤ hexM := by
  obtain ⟨j, hj, hLM, hPL, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) cert_check P hUP
  have hP : Nat.card P = 384 := by
    have h1 := Subgroup.card_mul_index (Ugrp.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv, card_U] at h1
    have h2 : (Ugrp.subgroupOf P).index = 3 := h3
    omega
  have hPj : Nat.card P = cert.sizes.getD j 0 := by
    rw [hPL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj]
  rw [hP] at hPj
  rw [len_eq] at hj
  interval_cases j
  · exact absurd hPj (by decide)
  · rw [hPL]
    exact fun _ hx => p1_le_hex hx
  · exact absurd hPj (by decide)
  · exact absurd hPj (by decide)
  · exact absurd hPj (by decide)
  · rw [hPL]
    exact fun _ hx => p5_le_hex hx

theorem eq_hex {N : Subgroup ↥Mgrp} (hUN : Ugrp ≤ N)
    (hc : Nat.card N = 5760) : N = hexM := by
  obtain ⟨j, hj, hLM, hPL, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) cert_check N hUN
  have hNj : Nat.card N = cert.sizes.getD j 0 := by
    rw [hPL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj]
  rw [hc] at hNj
  rw [len_eq] at hj
  interval_cases j
  · exact absurd hNj (by decide)
  · exact absurd hNj (by decide)
  · exact absurd hNj (by decide)
  · exact hPL
  · exact absurd hNj (by decide)
  · exact absurd hNj (by decide)

theorem exists_hexad {Y : Type} [Group Y] [Finite Y]
    (hY : IsSporadic .M22 Y) {S P : Subgroup Y} (hS : IsSylowTwoOf S ⊤) (hSP : S ≤ P)
    (hP : S.relIndex P = 3) :
    ∃ N : Subgroup Y, P ≤ N ∧ Nat.card N = 5760 ∧
      ∀ N' : Subgroup Y, S ≤ N' → Nat.card N' = 5760 → N' = N := by
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* ↥Mgrp :=
    (e₀ : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M22).trans (MulEquiv.subgroupCongr mGens_closure).symm
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) cert_check (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map _, ?_⟩
    have h : ¬ 2 ∣ S.relIndex ⊤ := hS.2.2
    change ¬ 2 ∣ (S.map e.toMonoidHom).relIndex ⊤
    rw [Subgroup.relIndex_top_right] at h ⊢
    rwa [show (S.map e.toMonoidHom).index = S.index from Subgroup.index_map_equiv (H := S) e]
  obtain ⟨c, hc⟩ := exists_conj_of_isSylowTwoOf hS' hU
  let φ : Y ≃* ↥Mgrp := e.trans (MulAut.conj c)
  have hSφ : S.map φ.toMonoidHom = Ugrp := by
    rw [← hc, Subgroup.map_map]
    rfl
  refine ⟨hexM.comap φ.toMonoidHom, ?_, ?_, fun N' hSN' hcN' => ?_⟩
  · have hle : P.map φ.toMonoidHom ≤ hexM := by
      refine le_hex (hSφ ▸ Subgroup.map_mono hSP) ?_
      rw [← hSφ, Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
      exact hP
    exact Subgroup.map_le_iff_le_comap.mp hle
  · rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective φ.symm.injective]
    exact card_hexM
  · have h1 : N'.map φ.toMonoidHom = hexM := by
      refine eq_hex (hSφ ▸ Subgroup.map_mono hSN') ?_
      rw [Subgroup.card_map_of_injective φ.injective]
      exact hcN'
    rw [← h1, Subgroup.comap_map_eq_self_of_injective φ.injective]

end CFSG.Quasithin.H13.L32A.C.M22Hex
