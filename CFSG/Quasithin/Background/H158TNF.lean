module

public import CFSG.Quasithin.Background.H158TSyl
public import CFSG.Quasithin.Background.H158TOct
public import CFSG.Quasithin.Background.H158TrioFix

public section

namespace CFSG.Quasithin.H158T

open CFSG.Quasithin.H.Trio CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open scoped Pointwise

@[expose] def labTrio : Finset (Finset (Fin 24)) := {o0F, o1F, o2F}

theorem arr_getElem!_eq (a : Array ℕ) (i : ℕ) : a[i]! = a.toList.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases a[i]? <;> rfl

theorem gen_perm_exists (j : ℕ) (hj : j ∈ [0, 1, 2, 3]) :
    ∃ σ ∈ qPerms, ∀ i : Fin 24, ((σ i : Fin 24) : ℕ) = gimg j i := by
  have hg : ∃ g ∈ genList, g.toList = genLs.getD j [] := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨genList.getD 0 #[], by simp [genList], rfl⟩
    · exact ⟨genList.getD 1 #[], by simp [genList], rfl⟩
    · exact ⟨genList.getD 2 #[], by simp [genList], rfl⟩
    · exact ⟨genList.getD 3 #[], by simp [genList], rfl⟩
  obtain ⟨g, hgm, hgl⟩ := hg
  obtain ⟨σ, hσ, hval⟩ := gen_mem_qPerms hgm
  refine ⟨σ, hσ, fun i => ?_⟩
  rw [hval i, arr_getElem!_eq, hgl]
  rfl

theorem gens_choice :
    ∃ σ : ℕ → Equiv.Perm (Fin 24), ∀ j ∈ [0, 1, 2, 3], σ j ∈ qPerms ∧
      ∀ i : Fin 24, ((σ j i : Fin 24) : ℕ) = gimg j i := by
  have key : ∀ j : ℕ, ∃ σ : Equiv.Perm (Fin 24), j ∈ [0, 1, 2, 3] → σ ∈ qPerms ∧
      ∀ i : Fin 24, ((σ i : Fin 24) : ℕ) = gimg j i := by
    intro j
    by_cases hj : j ∈ [0, 1, 2, 3]
    · obtain ⟨σ, hσ, hval⟩ := gen_perm_exists j hj
      exact ⟨σ, fun _ => ⟨hσ, hval⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose σ hσ using key
  exact ⟨σ, fun j hj => hσ j hj⟩

theorem mem_smul_perm_iff (y : Equiv.Perm (Fin 24)) (X : Finset (Fin 24)) (x : Fin 24) :
    y x ∈ y • X ↔ x ∈ X := by
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : z = x := y.injective (by simpa [Equiv.Perm.smul_def] using hzx)
    rw [← this]
    exact hz
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem trio_normal_form
    (T : Subgroup (Equiv.Perm (Fin 24))) (hT : CFSG.Quasithin.IsSylowIn 2 T AutPerm)
    (Tr : Finset (Finset (Fin 24))) (hcard : Tr.card = 3) (hblk : ∀ O ∈ Tr, O.card = 8)
    (hdisj : ∀ O ∈ Tr, ∀ O' ∈ Tr, O ≠ O' → Disjoint O O')
    (hcov : Tr.biUnion id = Finset.univ) (hst : ∀ g ∈ T, g • Tr = Tr) :
    ∃ h ∈ AutPerm, Tr = h • labTrio := by
  obtain ⟨h, hhA, hconj⟩ := exists_conj_sylow hT
  obtain ⟨σ, hσ⟩ := gens_choice
  obtain ⟨Tr', hTr'⟩ : ∃ X : Finset (Finset (Fin 24)), X = h • Tr := ⟨_, rfl⟩
  have hmemTr' : ∀ O, O ∈ Tr' ↔ ∃ O' ∈ Tr, h • O' = O := fun O => by
    rw [hTr']
    exact Finset.mem_smul_finset
  have hTr'card : Tr'.card = 3 := by rw [hTr', Finset.card_smul_finset, hcard]
  have hTr'blk : ∀ O ∈ Tr', O.card = 8 := by
    intro O hO
    obtain ⟨O', hO', rfl⟩ := (hmemTr' O).1 hO
    rw [Finset.card_smul_finset]
    exact hblk O' hO'
  have hTr'disj : ∀ O ∈ Tr', ∀ O' ∈ Tr', O ≠ O' → Disjoint O O' := by
    intro O hO O' hO' hne
    obtain ⟨X, hX, rfl⟩ := (hmemTr' O).1 hO
    obtain ⟨X', hX', rfl⟩ := (hmemTr' O').1 hO'
    have hXX : X ≠ X' := fun e => hne (by rw [e])
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, hyx⟩ := Finset.mem_smul_finset.1 hx
    obtain ⟨y', hy', hyx'⟩ := Finset.mem_smul_finset.1 hx'
    have hyy : y = y' := h.injective (hyx.trans hyx'.symm)
    exact Finset.disjoint_left.1 (hdisj X hX X' hX' hXX) hy (hyy ▸ hy')
  have hTr'cov : ∀ x : Fin 24, ∃ O ∈ Tr', x ∈ O := by
    intro x
    have hx : h⁻¹ x ∈ Tr.biUnion id := by
      rw [hcov]
      exact Finset.mem_univ _
    obtain ⟨O, hO, hxO⟩ := Finset.mem_biUnion.1 hx
    refine ⟨h • O, (hmemTr' _).2 ⟨O, hO, rfl⟩, ?_⟩
    exact Finset.mem_smul_finset.2 ⟨h⁻¹ x, hxO, by simp⟩
  obtain ⟨O, hOTr, hOfix⟩ := exists_common_fixed hT.2.1 Tr hcard (fun g hg O' hO' => by
    have hmem : g • O' ∈ g • Tr := Finset.mem_smul_finset.2 ⟨O', hO', rfl⟩
    rwa [hst g hg] at hmem)
  have hfixTr : ∀ y ∈ qPerms, y • Tr' = Tr' := by
    intro y hy
    have hyT : h⁻¹ * y * h ∈ T := hconj y hy
    calc y • Tr' = h • ((h⁻¹ * y * h) • Tr) := by
          rw [hTr', smul_smul, smul_smul, show h * (h⁻¹ * y * h) = y * h by group]
      _ = Tr' := by rw [hst _ hyT, hTr']
  have hfixO : ∀ y ∈ qPerms, y • (h • O) = h • O := by
    intro y hy
    have hyT : h⁻¹ * y * h ∈ T := hconj y hy
    calc y • (h • O) = h • ((h⁻¹ * y * h) • O) := by
          rw [smul_smul, smul_smul, show h * (h⁻¹ * y * h) = y * h by group]
      _ = h • O := by rw [hOfix _ hyT]
  have hO'mem : h • O ∈ Tr' := (hmemTr' _).2 ⟨O, hOTr, rfl⟩
  have hO2 : h • O = o2F := by
    refine orbit_fin σ (fun j hj x => (hσ j hj).2 x) (h • O) ?_ ?_
    · rw [Finset.card_smul_finset]
      exact hblk O hOTr
    · intro j hj x
      have e := mem_smul_perm_iff (σ j) (h • O) x
      rw [hfixO (σ j) (hσ j hj).1] at e
      exact e
  have hfixo2 : ∀ j ∈ [0, 1, 2, 3], σ j • o2F = o2F := by
    intro j hj
    have := hfixO (σ j) (hσ j hj).1
    rwa [hO2] at this
  have hO2mem : o2F ∈ Tr' := hO2 ▸ hO'mem
  have hcardE : (Tr'.erase o2F).card = 2 := by
    rw [Finset.card_erase_of_mem hO2mem, hTr'card]
  obtain ⟨A, B, hAB, hE⟩ := Finset.card_eq_two.1 hcardE
  have hAmem : A ∈ Tr'.erase o2F := by rw [hE]; simp
  have hBmem : B ∈ Tr'.erase o2F := by rw [hE]; simp
  obtain ⟨hAne, hAT⟩ := Finset.mem_erase.1 hAmem
  obtain ⟨hBne, hBT⟩ := Finset.mem_erase.1 hBmem
  have hTr'eq : Tr' = {o2F, A, B} := by
    have := Finset.insert_erase hO2mem
    rw [hE] at this
    exact this.symm
  have hABcov : ∀ x : Fin 24, x ∈ o2F ∨ x ∈ A ∨ x ∈ B := by
    intro x
    obtain ⟨O', hO'T, hxO'⟩ := hTr'cov x
    rw [hTr'eq] at hO'T
    simp only [Finset.mem_insert, Finset.mem_singleton] at hO'T
    rcases hO'T with rfl | rfl | rfl
    · exact Or.inl hxO'
    · exact Or.inr (Or.inl hxO')
    · exact Or.inr (Or.inr hxO')
  have hABdisj : Disjoint A B := hTr'disj A hAT B hBT hAB
  have hAo2 : Disjoint A o2F := hTr'disj A hAT o2F hO2mem hAne
  have hBo2 : Disjoint B o2F := hTr'disj B hBT o2F hO2mem hBne
  have hAcard : A.card = 8 := hTr'blk A hAT
  have hBcard : B.card = 8 := hTr'blk B hBT
  have hmapX : ∀ j ∈ [0, 1, 2, 3], ∀ X ∈ Tr', X ≠ o2F → (σ j • X = A ∨ σ j • X = B) := by
    intro j hj X hX hXne
    have h1 : σ j • X ∈ Tr' := by
      have hmem : σ j • X ∈ σ j • Tr' := Finset.mem_smul_finset.2 ⟨X, hX, rfl⟩
      rwa [hfixTr (σ j) (hσ j hj).1] at hmem
    have h2 : σ j • X ≠ o2F := by
      intro he
      apply hXne
      have e2 : σ j • X = σ j • o2F := by rw [he, hfixo2 j hj]
      have e3 := congrArg (fun Y : Finset (Fin 24) => (σ j)⁻¹ • Y) e2
      simp only [inv_smul_smul] at e3
      exact e3
    have := Finset.mem_erase.2 ⟨h2, h1⟩
    rw [hE] at this
    simpa using this
  have hσA : ∀ j ∈ [0, 1, 2, 3], (∀ x : Fin 24, x ∈ A ↔ σ j x ∈ A) ∨
      (∀ x : Fin 24, x ∈ A ↔ σ j x ∈ B) := by
    intro j hj
    rcases hmapX j hj A hAT hAne with e | e
    · left
      intro x
      have := mem_smul_perm_iff (σ j) A x
      rw [e] at this
      exact this.symm
    · right
      intro x
      have := mem_smul_perm_iff (σ j) A x
      rw [e] at this
      exact this.symm
  have hσB : ∀ j ∈ [0, 1, 2, 3], (∀ x : Fin 24, x ∈ B ↔ σ j x ∈ B) ∨
      (∀ x : Fin 24, x ∈ B ↔ σ j x ∈ A) := by
    intro j hj
    rcases hmapX j hj B hBT hBne with e | e
    · right
      intro x
      have := mem_smul_perm_iff (σ j) B x
      rw [e] at this
      exact this.symm
    · left
      intro x
      have := mem_smul_perm_iff (σ j) B x
      rw [e] at this
      exact this.symm
  have hc16 : ∀ x : Fin 24, x ∈ c16F ↔ x ∉ o2F := fun x => by simp [c16F]
  have hcon : ∀ x : Fin 24, (x ∈ A ∨ x ∈ B) ↔ x ∈ c16F := by
    intro x
    rw [hc16]
    constructor
    · rintro (hx | hx) hx2
      · exact Finset.disjoint_left.1 hAo2 hx hx2
      · exact Finset.disjoint_left.1 hBo2 hx hx2
    · intro hx
      rcases hABcov x with h2 | h2 | h2
      · exact absurd h2 hx
      · exact Or.inl h2
      · exact Or.inr h2
  have hzero : (0 : Fin 24) ∉ o2F := by
    rw [mem_o2F]
    decide
  have hANe : ∃ x : Fin 24, x ∈ A := Finset.card_pos.1 (by rw [hAcard]; norm_num)
  have hBNe : ∃ x : Fin 24, x ∈ B := Finset.card_pos.1 (by rw [hBcard]; norm_num)
  have hlab : Tr' = labTrio := by
    have hpart : (A = o0F ∧ B = o1F) ∨ (A = o1F ∧ B = o0F) := by
      by_cases h0A : (0 : Fin 24) ∈ A
      · left
        exact part_gen σ (fun j hj x => (hσ j hj).2 x) A B h0A hcon
          (fun x hx hxB => Finset.disjoint_left.1 hABdisj hx hxB) hBNe hσA
      · right
        have h0B : (0 : Fin 24) ∈ B := by
          rcases hABcov 0 with h2 | h2 | h2
          · exact absurd h2 hzero
          · exact absurd h2 h0A
          · exact h2
        have hres := part_gen σ (fun j hj x => (hσ j hj).2 x) B A h0B
          (fun x => by rw [or_comm]; exact hcon x)
          (fun x hx hxA => Finset.disjoint_left.1 hABdisj hxA hx) hANe hσB
        exact ⟨hres.2, hres.1⟩
    rw [hTr'eq]
    rcases hpart with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · unfold labTrio
      ext X
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · unfold labTrio
      ext X
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  refine ⟨h⁻¹, inv_mem hhA, ?_⟩
  rw [← hlab, hTr', inv_smul_smul]

end CFSG.Quasithin.H158T
