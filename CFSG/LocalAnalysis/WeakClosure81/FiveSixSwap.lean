module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderSwaps
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Perm
public import CFSG.Holt.H78.Sec4AltSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

@[expose] def cyc3 {α : Type*} [DecidableEq α] (a b c : α) : Perm α := swap a b * swap b c

theorem cyc3_apply_left {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : cyc3 a b c a = b := by
  simp [cyc3, swap_apply_of_ne_of_ne hab hac]

theorem cyc3_apply_middle {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : cyc3 a b c b = c := by
  simp [cyc3, swap_apply_of_ne_of_ne hac.symm hbc.symm]

theorem cyc3_apply_right {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : cyc3 a b c c = a := by
  simp [cyc3]

theorem cyc3_apply_of_ne {α : Type*} [DecidableEq α] {a b c x : α} (ha : x ≠ a) (hb : x ≠ b)
    (hc : x ≠ c) : cyc3 a b c x = x := by
  simp [cyc3, swap_apply_of_ne_of_ne hb hc, swap_apply_of_ne_of_ne ha hb]

theorem cyc3_mem_alternatingGroup {α : Type*} [DecidableEq α] [Fintype α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) : cyc3 a b c ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, cyc3, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hbc]
  decide

theorem cyc3_mul_swap_mul_inv {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : cyc3 a b c * swap a b * (cyc3 a b c)⁻¹ = swap b c := by
  rw [← swap_apply_apply, cyc3_apply_left hab hac hbc, cyc3_apply_middle hab hac hbc]

theorem false_of_swap_mem_of_swap_mem {α : Type*} [DecidableEq α] {S : Subgroup (Perm α)}
    (hS : IsPGroup 2 S) {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : swap a b ∈ S) (h2 : swap b c ∈ S) : False := by
  have h := CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender.disjoint_swap_of_pGroup
    hS h1 h2 ⟨a, b, hab, rfl⟩ ⟨b, c, hbc, rfl⟩ (by
      intro h
      have := congrArg (fun f : Perm α => f a) h
      simp [swap_apply_def, hab, hac, hbc, hab.symm, hac.symm, hbc.symm] at this)
  rcases h b with h | h
  · simp [swap_apply_def, hab.symm] at h
    exact hab h
  · simp [swap_apply_def, hbc] at h
    exact hbc h.symm

private theorem viaEmbeddingHom_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (ι : α ↪ β)
    (i j : α) : Equiv.Perm.viaEmbeddingHom ι (swap i j) = swap (ι i) (ι j) := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨y, rfl⟩ := hx
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply,
      ι.injective.swap_apply]
  · rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,
      swap_apply_of_ne_of_ne]
    · rintro rfl
      exact hx ⟨i, rfl⟩
    · rintro rfl
      exact hx ⟨j, rfl⟩

theorem exists_isPGroup_swap_move {n : ℕ} (hn : 4 ≤ n) :
    ∃ P : Subgroup (Perm (Fin n)), IsPGroup 2 P ∧
      ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ swap a b ∈ P ∧ ∃ s ∈ P, s a = c := by
  classical
  let ι : Fin 4 ↪ Fin n := Fin.castLEEmb hn
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 (Perm (Fin 4))))
  obtain ⟨g, hgP, x, y, hxy, hg⟩ :=
    CFSG.Quasithin.H13.L1294J.exists_isSwap_mem (n := 4) (by norm_num) P₀.isPGroup'
      (Sylow.not_dvd_index P₀)
  have hsw : swap x y ∈ (P₀ : Subgroup (Perm (Fin 4))) := hg ▸ hgP
  have hfus : CFSG.Open.fusionIsSylowIn 2 (P₀ : Subgroup (Perm (Fin 4))) ⊤ :=
    ⟨le_top, P₀.isPGroup', fun Q _ hQ hle => P₀.is_maximal' hQ hle⟩
  obtain ⟨a, haBit, haCard⟩ :=
    CFSG.Holt.H78.exists_testBit_card_orbit_of_fusionIsSylowIn_top (X := Fin 4) hfus x
  have haBit' : (4 : ℕ).testBit a := by simpa using haBit
  have hxmem : x ∈ MulAction.orbit P₀ x := MulAction.mem_orbit_self x
  have hymem : y ∈ MulAction.orbit P₀ x := by
    rw [MulAction.mem_orbit_iff]
    exact ⟨⟨swap x y, hsw⟩, by simpa using Equiv.swap_apply_left x y⟩
  have h2le : 2 ≤ Nat.card (MulAction.orbit P₀ x) := by
    have hinj : Function.Injective
        (fun i : Fin 2 =>
          if i = 0 then (⟨x, hxmem⟩ : MulAction.orbit P₀ x) else ⟨y, hymem⟩) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff]
    have h := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_fin] at h
    exact h
  have h4le : Nat.card (MulAction.orbit P₀ x) ≤ 4 := by
    have h := Nat.card_le_card_of_injective (fun z : MulAction.orbit P₀ x => (z : Fin 4))
      Subtype.val_injective
    rw [Nat.card_fin] at h
    exact h
  have ha2 : a = 2 := by
    have hle : 2 ^ a ≤ 4 := haCard ▸ h4le
    have hale : a ≤ 2 := by
      refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 ?_
      calc 2 ^ a ≤ 4 := hle
        _ = 2 ^ 2 := by norm_num
    have hane0 : a ≠ 0 := by
      rintro rfl
      exact absurd haBit' (by decide)
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 hane0
    interval_cases a
    · exact absurd haBit' (by decide)
    · rfl
  have horbit : Nat.card (MulAction.orbit P₀ x) = 4 := by
    rw [haCard, ha2]
    norm_num
  have hz : ∃ z : Fin 4, z ≠ x ∧ z ≠ y := by
    refine ENat.exists_ne_ne_of_three_le ?_ x y
    rw [ENat.card_eq_coe_fintype_card]
    norm_num
  obtain ⟨z, hzx, hzy⟩ := hz
  have hzmem : z ∈ MulAction.orbit P₀ x := by
    haveI hfin : Fintype {w : Fin 4 // w ∈ MulAction.orbit P₀ x} := Fintype.ofFinite _
    by_contra hz'
    have hlt := Fintype.card_subtype_lt (p := fun w : Fin 4 => w ∈ MulAction.orbit P₀ x) hz'
    have hcard : Fintype.card {w : Fin 4 // w ∈ MulAction.orbit P₀ x} = 4 := by
      rw [Fintype.card_eq_nat_card]
      simpa using horbit
    rw [hcard] at hlt
    simp at hlt
  rw [MulAction.mem_orbit_iff] at hzmem
  obtain ⟨s, hs⟩ := hzmem
  have hsz : (s : Perm (Fin 4)) x = z := by
    simpa [MulAction.subgroup_smul_def] using hs
  have hφswap : Equiv.Perm.viaEmbeddingHom ι (swap x y) = swap (ι x) (ι y) :=
    viaEmbeddingHom_swap ι x y
  refine ⟨(P₀ : Subgroup (Perm (Fin 4))).map (Equiv.Perm.viaEmbeddingHom ι),
    P₀.isPGroup'.map (Equiv.Perm.viaEmbeddingHom ι), ι x, ι y, ι z,
    ι.injective.ne hxy, ι.injective.ne hzx.symm, ι.injective.ne hzy.symm, ?_,
    Equiv.Perm.viaEmbeddingHom ι s, Subgroup.mem_map_of_mem _ s.2, ?_⟩
  · rw [← hφswap]
    exact Subgroup.mem_map_of_mem _ hsw
  · rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply, hsz]

theorem exists_swap_mem_isSylowIn {n : ℕ} (hn : 4 ≤ n) {S : Subgroup (Perm (Fin n))}
    (hS : IsSylowIn 2 S ⊤) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ swap a b ∈ S ∧ ∃ s ∈ S, s a = c := by
  obtain ⟨P, hP, a, b, c, hab, hac, hbc, hsw, s, hs, hsa⟩ := exists_isPGroup_swap_move hn
  obtain ⟨S₁, hS₁, hPS₁⟩ := B6.exists_isSylowTwoOf_ge hP (le_top : P ≤ ⊤)
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hS₁ hS
  have hmem : ∀ x ∈ S₁, g * x * g⁻¹ ∈ S := fun x hx => hg ▸ A1b.mem_conjSub_of_mem hx
  refine ⟨g a, g b, g c, g.injective.ne hab, g.injective.ne hac, g.injective.ne hbc, ?_,
    g * s * g⁻¹, hmem s (hPS₁ hs), ?_⟩
  · rw [swap_apply_apply]
    exact hmem _ (hPS₁ hsw)
  · simp [hsa]

end CFSG.LocalAnalysis.WeakClosure81
