module

public import CFSG.Quasithin.AppendixH.H16.Sextet24
public import CFSG.Quasithin.AppendixH.Common.OctadAltHom
public import CFSG.Quasithin.Background.HFixSylBase

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

@[expose] def flagArr : Array ℕ :=
  #[0, 6, 7, 8, 12, 16, 5, 20, 13, 4, 18, 23, 3, 17, 19, 10, 2, 21, 11, 22, 9, 1, 14, 15]

@[expose] def flagInv : Array ℕ :=
  #[0, 21, 16, 12, 9, 6, 1, 2, 3, 20, 15, 18, 4, 8, 22, 23, 5, 13, 10, 14, 7, 17, 19, 11]

theorem flag_ok : InvPairOK 24 flagArr flagInv = true := by decide +kernel

theorem flag_aut : autArrOK flagArr flagInv = true := by decide +kernel

@[expose] noncomputable def flagPerm : Equiv.Perm (Fin 24) := permOfArr 24 flagArr flagInv flag_ok

theorem hasArr_flagPerm : HasArr flagPerm flagArr := hasArr_permOfArr flag_ok

theorem flagPerm_mem : flagPerm ∈ M24g := mem_AutPerm_of_arr flag_ok flag_aut

@[expose] noncomputable def flagSextet : Finset (Finset (Fin 24)) := flagPerm • stdSextet

theorem isSextet_flagSextet : IsSextet flagSextet :=
  isSextet_smul flagPerm_mem isSextet_stdSextet

theorem octad0_union_flagSextet :
    ∃ B₁ ∈ flagSextet, ∃ B₂ ∈ flagSextet, B₁ ≠ B₂ ∧ octad0 = B₁ ∪ B₂ := by
  refine ⟨flagPerm • (Finset.univ.filter fun x : Fin 24 => lab6 x = 0), ?_,
    flagPerm • (Finset.univ.filter fun x : Fin 24 => lab6 x = 1), ?_, ?_, ?_⟩
  · exact Finset.mem_smul_finset.2 ⟨_, Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩, rfl⟩
  · exact Finset.mem_smul_finset.2 ⟨_, Finset.mem_image.2 ⟨1, Finset.mem_univ _, rfl⟩, rfl⟩
  · decide +kernel
  · decide +kernel

private theorem smul_finset_eq_map_perm {α : Type*} [DecidableEq α]
    (g : Equiv.Perm α) (s : Finset α) : g • s = s.map g.toEmbedding := by
  rw [Finset.smul_finset_def, Finset.map_eq_image]
  rfl

private theorem exists_perm_smul_finset_eq {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Finset α} (h : s.card = t.card) : ∃ π : Equiv.Perm α, π • s = t := by
  classical
  have hc : Fintype.card {x : α // ¬ x ∈ s} = Fintype.card {x : α // ¬ x ∈ t} := by
    rw [Fintype.card_subtype_compl (fun x : α => x ∈ s),
      Fintype.card_subtype_compl (fun x : α => x ∈ t)]
    congr 1
    rw [show Fintype.card {x : α // x ∈ s} = s.card from Fintype.card_coe s,
      show Fintype.card {x : α // x ∈ t} = t.card from Fintype.card_coe t, h]
  let g : {x : α // ¬ x ∈ s} ≃ {x : α // ¬ x ∈ t} := Fintype.equivOfCardEq hc
  let π : Equiv.Perm α := (Equiv.sumCompl (fun x : α => x ∈ s)).symm.trans
    ((Equiv.sumCongr (Finset.equivOfCardEq h) g).trans (Equiv.sumCompl (fun x : α => x ∈ t)))
  refine ⟨π, ?_⟩
  have hπs : ∀ x ∈ s, π x ∈ t := by
    intro x hx
    have hsymm : (Equiv.sumCompl (fun x : α => x ∈ s)).symm x = Sum.inl ⟨x, hx⟩ := by
      apply (Equiv.sumCompl (fun x : α => x ∈ s)).injective
      rw [Equiv.apply_symm_apply, Equiv.sumCompl_apply_inl]
    simp only [π, Equiv.trans_apply, Equiv.sumCongr_apply, hsymm, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    exact (Finset.equivOfCardEq h ⟨x, hx⟩).2
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    rw [Finset.mem_smul_finset] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hπs x hx
  · rw [Finset.card_smul_finset, h]

private theorem exists_even_perm_smul_finset_eq {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Finset α} (hs : s.card = 4) {π : Equiv.Perm α} (hπ : π • s = t) :
    ∃ ρ ∈ alternatingGroup α, ρ • s = t := by
  classical
  by_cases hsign : Equiv.Perm.sign π = 1
  · exact ⟨π, Equiv.Perm.mem_alternatingGroup.2 hsign, hπ⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < s.card)
    have hswap : Equiv.swap a b • s = s := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_smul_finset] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Equiv.Perm.smul_def]
        by_cases hya : y = a
        · subst hya; rw [Equiv.swap_apply_left]; exact hb
        · by_cases hyb : y = b
          · subst hyb; rw [Equiv.swap_apply_right]; exact ha
          · rw [Equiv.swap_apply_of_ne_of_ne hya hyb]; exact hy
      · rw [Finset.card_smul_finset]
    refine ⟨π * Equiv.swap a b, ?_, ?_⟩
    · have hsignπ : Equiv.Perm.sign π = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hsign
        · exact h
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hsignπ,
        Equiv.Perm.sign_swap hab]
      rfl
    · rw [mul_smul, hswap, hπ]

theorem exists_octStab_smul_eq {O : Finset (Fin 24)}
    (hO : IsOctad O) {A B : Finset (Fin 24)} (hA : A ⊆ O) (hB : B ⊆ O) (hAc : A.card = 4)
    (hBc : B.card = 4) : ∃ m ∈ octStab O, m • A = B := by
  classical
  let A' : Finset ↥O := Finset.univ.filter fun x : ↥O => (x : Fin 24) ∈ A
  let B' : Finset ↥O := Finset.univ.filter fun x : ↥O => (x : Fin 24) ∈ B
  have hA'map : A'.map (Function.Embedding.subtype fun x : Fin 24 => x ∈ O) = A := by
    ext x
    rw [Finset.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [A'] using hy
    · intro hx
      exact ⟨⟨x, hA hx⟩, by simp [A', hx], rfl⟩
  have hB'map : B'.map (Function.Embedding.subtype fun x : Fin 24 => x ∈ O) = B := by
    ext x
    rw [Finset.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [B'] using hy
    · intro hx
      exact ⟨⟨x, hB hx⟩, by simp [B', hx], rfl⟩
  have hA'card : A'.card = 4 := by
    rw [← Finset.card_map (f := Function.Embedding.subtype fun x : Fin 24 => x ∈ O), hA'map, hAc]
  have hB'card : B'.card = 4 := by
    rw [← Finset.card_map (f := Function.Embedding.subtype fun x : Fin 24 => x ∈ O), hB'map, hBc]
  obtain ⟨π, hπ⟩ := exists_perm_smul_finset_eq (hA'card.trans hB'card.symm)
  obtain ⟨ρ, hρalt, hρ⟩ := exists_even_perm_smul_finset_eq hA'card hπ
  obtain ⟨m, hm⟩ := octActAlt_surjective hO ⟨ρ, hρalt⟩
  refine ⟨m, m.2, ?_⟩
  have hmeq : octAct O m = ρ := by
    rw [← octActAlt_apply hO m, hm]
  have hmem : (octAct O m) • A' = B' := by rw [hmeq, hρ]
  apply Finset.ext
  intro x
  by_cases hx : x ∈ O
  · have hinv : (m : S24)⁻¹ ∈ octStab O := (octStab O).inv_mem m.2
    have hmxO : (m : S24)⁻¹ x ∈ O := (mem_iff_of_mem_octStab hinv x).2 hx
    rw [smul_finset_eq_map, Finset.mem_map_equiv]
    change (m : S24)⁻¹ x ∈ A ↔ x ∈ B
    have hA'mem : (⟨(m : S24)⁻¹ x, hmxO⟩ : ↥O) ∈ A' ↔ (m : S24)⁻¹ x ∈ A := by
      simp [A']
    have hB'mem : (⟨x, hx⟩ : ↥O) ∈ B' ↔ x ∈ B := by
      simp [B']
    rw [← hA'mem, ← hB'mem]
    have hkey : ((octAct O m)⁻¹ ⟨x, hx⟩ : ↥O) = ⟨(m : S24)⁻¹ x, hmxO⟩ := by
      apply Subtype.ext
      rw [← map_inv, octAct_apply]
      rfl
    have hmap : (⟨x, hx⟩ : ↥O) ∈ (octAct O m) • A' ↔
        ((octAct O m)⁻¹ ⟨x, hx⟩) ∈ A' := by
      rw [smul_finset_eq_map_perm, Finset.mem_map_equiv]
      rfl
    have h2 : (⟨x, hx⟩ : ↥O) ∈ B' ↔ ((octAct O m)⁻¹ ⟨x, hx⟩) ∈ A' := by
      rw [← hmem]
      exact hmap
    rw [← hkey]
    exact h2.symm
  · have hxB : x ∉ B := fun h => hx (hB h)
    have hinv : (m : S24)⁻¹ ∈ octStab O := (octStab O).inv_mem m.2
    have hmxO : (m : S24)⁻¹ x ∉ O := by
      intro h
      exact hx ((mem_iff_of_mem_octStab hinv x).1 h)
    have hxA : (m : S24)⁻¹ x ∉ A := fun h => hmxO (hA h)
    rw [smul_finset_eq_map, Finset.mem_map_equiv]
    change (m : S24)⁻¹ x ∈ A ↔ x ∈ B
    exact iff_of_false hxA hxB

theorem exists_flag_conj {O : Finset (Fin 24)}
    {S : Finset (Finset (Fin 24))} (hO : IsOctad O) (hS : IsSextet S)
    (hOS : ∃ B₁ ∈ S, ∃ B₂ ∈ S, B₁ ≠ B₂ ∧ O = B₁ ∪ B₂) :
    ∃ τ ∈ M24g, τ • octad0 = O ∧ τ • flagSextet = S := by
  classical
  obtain ⟨B₁, hB₁S, B₂, hB₂S, hB₁B₂, hOeq⟩ := hOS
  obtain ⟨T₁, hT₁mem, T₂, hT₂mem, hT₁T₂, hO0eq⟩ := octad0_union_flagSextet
  obtain ⟨τ₁, hτ₁, hτ₁O⟩ := exists_smul_octad_eq isOctad_octad0 hO
  set S' : Finset (Finset (Fin 24)) := τ₁⁻¹ • S with hS'def
  set B₁' : Finset (Fin 24) := τ₁⁻¹ • B₁ with hB₁'def
  have hS' : IsSextet S' := by
    rw [hS'def]; exact isSextet_smul (M24g.inv_mem hτ₁) hS
  have hB₁'S' : B₁' ∈ S' := by
    rw [hS'def, hB₁'def]
    exact Finset.mem_smul_finset.2 ⟨B₁, hB₁S, rfl⟩
  have hB₁O : B₁ ⊆ O := by rw [hOeq]; exact Finset.subset_union_left
  have hτ₁invO : τ₁⁻¹ • O = octad0 := by
    calc τ₁⁻¹ • O = τ₁⁻¹ • (τ₁ • octad0) := by rw [hτ₁O]
      _ = octad0 := by rw [inv_smul_smul]
  have hB₁'O : B₁' ⊆ octad0 := by
    rw [hB₁'def]
    have hsub : τ₁⁻¹ • B₁ ⊆ τ₁⁻¹ • O := Finset.smul_finset_subset_smul_finset hB₁O
    rwa [hτ₁invO] at hsub
  have hT₁O : T₁ ⊆ octad0 := by rw [hO0eq]; exact Finset.subset_union_left
  have hB₁'card : B₁'.card = 4 := by
    rw [hB₁'def, Finset.card_smul_finset]; exact hS.2.1 B₁ hB₁S
  have hT₁card : T₁.card = 4 := isSextet_flagSextet.2.1 T₁ hT₁mem
  obtain ⟨m, hm, hmB₁'⟩ :=
    exists_octStab_smul_eq isOctad_octad0 hB₁'O hT₁O hB₁'card hT₁card
  have hmM : m ∈ M24g := (mem_octStab_iff.mp hm).1
  have hT₁_mem_mS' : T₁ ∈ m • S' := Finset.mem_smul_finset.2 ⟨B₁', hB₁'S', hmB₁'⟩
  have hmeqS : m • S' = flagSextet :=
    sextet_eq_of_mem (isSextet_smul hmM hS') isSextet_flagSextet hT₁_mem_mS' hT₁mem
  refine ⟨τ₁ * m⁻¹, M24g.mul_mem hτ₁ (M24g.inv_mem hmM), ?_, ?_⟩
  · have hmO : m • octad0 = octad0 := (mem_octStab_iff.mp hm).2
    have hmOinv : m⁻¹ • octad0 = octad0 := by
      calc m⁻¹ • octad0 = m⁻¹ • (m • octad0) := by rw [hmO]
        _ = octad0 := by rw [inv_smul_smul]
    calc (τ₁ * m⁻¹) • octad0 = τ₁ • (m⁻¹ • octad0) := mul_smul τ₁ m⁻¹ octad0
      _ = τ₁ • octad0 := by rw [hmOinv]
      _ = O := hτ₁O
  · calc (τ₁ * m⁻¹) • flagSextet = (τ₁ * m⁻¹) • (m • S') := by rw [← hmeqS]
      _ = τ₁ • (m⁻¹ • (m • S')) := by rw [mul_smul]
      _ = τ₁ • S' := by rw [inv_smul_smul]
      _ = S := by rw [hS'def, smul_inv_smul]

end CFSG.ASVolI.H16
