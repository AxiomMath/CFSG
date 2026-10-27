module

public import CFSG.Quasithin.EmptyFaithful.ModGStruct
public import CFSG.Quasithin.EmptyFaithful.ModGChkP
public import CFSG.Quasithin.EmptyFaithful.ModGSolv

public section

namespace CFSG.Quasithin.ModG

open scoped Pointwise
open MulAction CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

theorem mem_blk (l : List ℕ) (x : Fin 22) : x ∈ M22Insp.blk l ↔ x.val ∈ l := by
  simp only [M22Insp.blk, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    split at h
    · have := Option.some.inj h
      subst this
      exact hi
    · exact absurd h (by simp)
  · intro hx
    exact ⟨x.val, hx, by simp [x.isLt]⟩

theorem card_blk_six : ∀ l ∈ M22Insp.blocks, (M22Insp.blk l).card = 6 := by decide +kernel

theorem smul_eq_of_forall (g : Equiv.Perm (Fin 22)) (B : Finset (Fin 22)) (h : ∀ x ∈ B, g x ∈ B) :
    g • B = B := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
    exact h x hx
  · rw [Finset.card_smul_finset]

theorem smul_blk_eq (g : Equiv.Perm (Fin 22)) (l : List ℕ) (h : ∀ x : Fin 22, x.val ∈ l → (g x).val ∈ l) :
    g • M22Insp.blk l = M22Insp.blk l :=
  smul_eq_of_forall g _ fun x hx => (mem_blk l _).2 (h x ((mem_blk l x).1 hx))

theorem B0_eq : M22Insp.data.B₀ = M22Insp.blk B0l := rfl

theorem ks_fix_check : ∀ i ∈ List.range 8, ∀ x ∈ B0l,
    memB (Nat.sub (dg (Lks8K.getD i kId) x) 1) B0l = true := by decide +kernel

theorem Lks8_getD_cd (i : ℕ) : cd (Lks8.getD i 1) = Lks8K.getD i kId := by
  have := List.getD_map Lks8 1 (n := i) cd
  rw [cd_one, Lks8_cd] at this
  exact this.symm

theorem Lks8_length : Lks8.length = 8 := by
  rw [Lks8, invAlph_length, List.length_map, ksWd_len]

theorem Lks8_mem_Dg : ∀ y ∈ Lks8, y ∈ Dg := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi8 : i < 8 := by rw [← Lks8_length]; exact hi
  rw [Dg, mem_stabilizer_iff, B0_eq]
  have hy' : Lks8[i] = Lks8.getD i 1 := (List.getD_eq_getElem _ _ hi).symm
  show ((Lks8[i] : Mg) : Equiv.Perm (Fin 22)) • M22Insp.blk B0l = M22Insp.blk B0l
  apply smul_blk_eq
  intro x hx
  rw [val_apply_eq]
  have h1 := memB_iff.1 (ks_fix_check i (List.mem_range.2 hi8) x.val hx)
  have h2 : dg (pk ((Lks8[i] : Mg) : Equiv.Perm (Fin 22))) x.val = dg (Lks8K.getD i kId) x.val := by
    rw [← Lks8_getD_cd, ← hy']
    rfl
  rw [h2]
  exact h1

theorem ev_Lks8_mem_Dg (w : List ℕ) : ev Lks8 w ∈ Dg := ev_mem Lks8_mem_Dg w

theorem mem_invAlph {ls : List Mg} {x : Mg} : x ∈ invAlph ls ↔ x ∈ ls ∨ x⁻¹ ∈ ls := by
  simp only [invAlph, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hy)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨x⁻¹, h, by simp⟩

theorem Ls_mem_Dg : ∀ x ∈ Ls, x ∈ Dg := by
  intro x hx
  rw [Ls, mem_invAlph] at hx
  rcases hx with hx | hx
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact ev_Lks8_mem_Dg w
  · obtain ⟨w, -, hw⟩ := List.mem_map.1 hx
    have : x = (ev Lks8 w)⁻¹ := by rw [hw]; simp
    rw [this]
    exact Dg.inv_mem (ev_Lks8_mem_Dg w)

theorem Sg_le_Dg : Sg ≤ Dg := by
  rw [Sg, Subgroup.closure_le]
  exact fun x hx => Ls_mem_Dg x hx

theorem dEl_mem_Dg : ∀ d ∈ dEl, d ∈ Dg := by
  intro d hd
  rw [dEl, List.mem_map] at hd
  obtain ⟨w, -, rfl⟩ := hd
  exact ev_Lks8_mem_Dg w

theorem u1_mem_Dg : u1 ∈ Dg := ev_Lks8_mem_Dg _
theorem u2_mem_Dg : u2 ∈ Dg := ev_Lks8_mem_Dg _
theorem o1_mem_Dg : o1 ∈ Dg := ev_Lks8_mem_Dg _
theorem o2_mem_Dg : o2 ∈ Dg := ev_Lks8_mem_Dg _

theorem P1_le_Dg : P1 ≤ Dg := by
  rw [P1, Subgroup.closure_le]
  rintro x (hx | rfl)
  · exact Ls_mem_Dg x hx
  · exact u1_mem_Dg

theorem P2_le_Dg : P2 ≤ Dg := by
  rw [P2, Subgroup.closure_le]
  rintro x (hx | rfl)
  · exact Ls_mem_Dg x hx
  · exact u2_mem_Dg

theorem dEl_length : dEl.length = 45 := by
  rw [dEl, List.length_map]
  decide +kernel

theorem Dg_cosets :
    ∀ x ∈ Dg, ∃ d ∈ dEl, d⁻¹ * x ∈ Sg := by
  obtain ⟨E, -, -, hcardD, -⟩ := m22_struct
  apply exists_coset_rep Dg Sg dEl dEl_mem_Dg dEl_pairwise
  have h1 := Subgroup.card_mul_index (Sg.subgroupOf Dg)
  have h2 : Nat.card (Sg.subgroupOf Dg) = 128 := by
    rw [← card_Sg]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Sg_le_Dg).toEquiv
  rw [← h1] at hcardD
  rw [h2] at hcardD
  rw [dEl_length]
  omega

theorem zEl_getD (k : ℕ) : zEl.getD k 1 = zi k := by
  have h := List.getD_map zWd [] (n := k) (ev Lab)
  rw [ev_nil] at h
  rw [zi]
  exact h

theorem zi_zero : zi 0 = 1 := by
  have : zWd.getD 0 [] = [] := by decide +kernel
  rw [zi, this, ev_nil]

theorem exists_di (d : Mg) (hd : d ∈ dEl) : ∃ j < 45, d = di j := by
  rw [dEl, List.mem_map] at hd
  obtain ⟨w, hw, rfl⟩ := hd
  obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hw
  have hj45 : j < 45 := by
    have : dWd.length = 45 := by decide +kernel
    omega
  refine ⟨j, hj45, ?_⟩
  rw [di, List.getD_eq_getElem _ _ hj, hjw]

theorem blk_card_B0 : (M22Insp.blk B0l).card = 6 := by decide +kernel

theorem not_solvable_of_le {Z : Subgroup Mg} {a b : Mg} (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 5 = 1) (hb1 : b ≠ 1) (haZ : a ∈ Z) (hbZ : b ∈ Z) :
    ¬ Group.IsSolvable ↥Z := by
  intro hZ
  have hle : Subgroup.closure ({a, b} : Set Mg) ≤ Z := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact haZ
    · exact hbZ
  exact not_solvable_of_235 ha hb hab hb1
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

theorem lat (Z : Subgroup Mg)
    (hSZ : Sg ≤ Z) (hZ : Group.IsSolvable ↥Z) : Z ≤ Dg := by
  obtain ⟨E, -, -, -, horb⟩ := m22_struct
  intro y hy
  have hyH : y • M22Insp.data.B₀ ∈ M22Insp.data.H := horb _ ⟨y, rfl⟩
  have hHdef : M22Insp.data.H = M22Insp.blocks.map M22Insp.blk := rfl
  rw [hHdef, List.mem_map] at hyH
  obtain ⟨l, hl, hly⟩ := hyH
  obtain ⟨i, hi, hil⟩ := List.getElem_of_mem hl
  have hi77 : i < 77 := by rw [← blocks_length]; exact hi
  have hli : l = M22Insp.blocks.getD i [] := by rw [List.getD_eq_getElem _ _ hi, hil]
  obtain ⟨k, hk6, s, hsE, hcov⟩ := hex_cover i hi77
  have hsS : s ∈ Sg := (mem_Sg_iff s).2 hsE
  set g : Mg := s * zEl.getD k 1 with hg
  have hgB : g • M22Insp.data.B₀ = y • M22Insp.data.B₀ := by
    rw [← hly, B0_eq, hli]
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hz
      rw [mem_blk]
      exact hcov x ((mem_blk B0l x).1 hx)
    · rw [Finset.card_smul_finset, blk_card_B0, ← hli]
      exact (card_blk_six l hl).le
  have hmem : g⁻¹ * y ∈ Dg := by
    rw [Dg, mem_stabilizer_iff, mul_smul, ← hgB, inv_smul_smul]
  obtain ⟨d, hd, hds⟩ := Dg_cosets _ hmem
  obtain ⟨j, hj, rfl⟩ := exists_di d hd
  set s' : Mg := (di j)⁻¹ * (g⁻¹ * y) with hs'
  have hyeq : y = s * zEl.getD k 1 * di j * s' := by
    rw [hs', hg]; group
  have hs'Z : s' ∈ Z := hSZ hds
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [zEl_getD, zi_zero] at hyeq
    rw [hyeq]
    simp only [mul_one]
    exact Dg.mul_mem (Dg.mul_mem (Sg_le_Dg hsS) (dEl_mem_Dg _ hd)) (Sg_le_Dg hds)
  · exfalso
    rw [zEl_getD] at hyeq
    have hy' : zi k * di j ∈ Z := by
      have : zi k * di j = s⁻¹ * y * s'⁻¹ := by rw [hyeq]; group
      rw [this]
      exact Z.mul_mem (Z.mul_mem (Z.inv_mem (hSZ hsS)) hy) (Z.inv_mem hs'Z)
    obtain ⟨a, b, ha, hb, ha2, hb3, hab, hb1⟩ := claimC k j hkpos (by omega) hj
    have hcl : Subgroup.closure ({x | x ∈ Ls} ∪ {zi k * di j}) ≤ Z := by
      rw [Subgroup.closure_le]
      rintro x (hx | rfl)
      · exact hSZ (Subgroup.subset_closure hx)
      · exact hy'
    exact not_solvable_of_le ha2 hb3 hab hb1 (hcl ha) (hcl hb) hZ

end CFSG.Quasithin.ModG
