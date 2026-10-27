module

public import CFSG.Sporadic.Co2Smith.GlDataChain
public import CFSG.Sporadic.Co2Smith.GlCosetCheck
public import CFSG.Sporadic.Co2Smith.CBound

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glCosetElem_parts :
    Native.glMaps Native.glZ 80 80 = true ∧ Native.glMaps Native.glRows[14]! 80 80 = true ∧
    Native.glMaps Native.glRows[14]! 1172 1339 = true ∧ Native.glMaps Native.glW0 80 80 = true ∧
    Native.glMaps Native.glB3 80 80 = true ∧ Native.glMaps Native.glB3 942 1172 = true ∧
    Native.glMaps Native.glB3 582 1348 = true ∧ Native.glMaps Native.glU 1348 728 = true ∧
    Native.glMaps Native.glW0 728 1172 = true ∧
    Native.glMaps (mulRows 22 Native.glV1 Native.glZ) 582 1977 = true ∧
    1977 ∈ Native.glWit0Pts 1 ∧
    (∀ w ∈ Native.glM2Words, Native.glMaps (Native.glR w) 80 80 = true ∧
      Native.glMaps (Native.glR w) 582 582 = true) ∧
    Native.glMaps (Native.glR Native.glM2Words[0]!) 942 942 = true := by
  have h := glCosetElem_check
  simp only [Native.glCosetElemOK, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem glM2Words_lt : ∀ w ∈ Native.glM2Words, ∀ k ∈ w, k < 22 := by decide

section Elements


theorem z0_mem_G1c : z0 ∈ G1c :=
  co2PermHom_apply_of_maps z0_val' (by norm_num) (by norm_num) glCosetElem_parts.1

theorem w0K_mem_G1c : w0K ∈ G1c :=
  co2PermHom_apply_of_maps w0K_val (by norm_num) (by norm_num) glCosetElem_parts.2.2.2.1

theorem β3K_mem_G1c : β3K ∈ G1c :=
  co2PermHom_apply_of_maps β3K_val (by norm_num) (by norm_num) glCosetElem_parts.2.2.2.2.1

theorem glElt14_mem_G1c : glElt 14 ∈ G1c :=
  co2PermHom_apply_of_maps (glElt_val (by norm_num)) (by norm_num) (by norm_num)
    glCosetElem_parts.2.1

theorem glElt14_1172 : co2PermHom (glElt 14) 1172 = 1339 :=
  co2PermHom_apply_of_maps (glElt_val (by norm_num)) (by norm_num) (by norm_num)
    glCosetElem_parts.2.2.1

theorem β3K_942 : co2PermHom β3K 942 = 1172 :=
  co2PermHom_apply_of_maps β3K_val (by norm_num) (by norm_num) glCosetElem_parts.2.2.2.2.2.1

theorem β3K_582 : co2PermHom β3K 582 = 1348 :=
  co2PermHom_apply_of_maps β3K_val (by norm_num) (by norm_num)
    glCosetElem_parts.2.2.2.2.2.2.1

theorem uK_1348 : co2PermHom uK 1348 = 728 :=
  co2PermHom_apply_of_maps uK_val (by norm_num) (by norm_num)
    glCosetElem_parts.2.2.2.2.2.2.2.1

theorem w0K_728 : co2PermHom w0K 728 = 1172 :=
  co2PermHom_apply_of_maps w0K_val (by norm_num) (by norm_num)
    glCosetElem_parts.2.2.2.2.2.2.2.2.1

theorem v1K_x16K_582 : co2PermHom (v1K * x16K) 582 = 1977 := by
  have hv : (v1K * x16K).val.val = rowsMatrix 22 (mulRows 22 Native.glV1 Native.glZ) := by
    rw [val_val_mul, v1K_val, x16K_val, rowsMatrix_mulRows]
  exact co2PermHom_apply_of_maps hv (by norm_num) (by norm_num)
    glCosetElem_parts.2.2.2.2.2.2.2.2.2.1

theorem glM2Words_fix :
    ∀ w ∈ Native.glM2Words, co2PermHom (glE w) glP0 = glP0 ∧ co2PermHom (glE w) 582 = 582 :=
  fun w hw => ⟨co2PermHom_apply_of_maps (glE_val (glM2Words_lt w hw)) _ _
      (glCosetElem_parts.2.2.2.2.2.2.2.2.2.2.2.1 w hw).1,
    co2PermHom_apply_of_maps (glE_val (glM2Words_lt w hw)) _ _
      (glCosetElem_parts.2.2.2.2.2.2.2.2.2.2.2.1 w hw).2⟩

theorem glM2Words_zero_942 : co2PermHom (glE Native.glM2Words[0]!) 942 = 942 :=
  co2PermHom_apply_of_maps (glE_val (glM2Words_lt _ (by decide))) (by norm_num) (by norm_num)
    glCosetElem_parts.2.2.2.2.2.2.2.2.2.2.2.2

end Elements

theorem mem_glWit0Pts_1977 : 1977 ∈ Native.glWit0Pts 1 :=
  glCosetElem_parts.2.2.2.2.2.2.2.2.2.2.1

theorem β3K_mem_C0c :
    β3K ∈ C0c := by
  have hx25 : x25K ∈ C0c :=
    C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c x16K_mem_C0c) δ1hK_mem_C0c
  have hx52 : x52K ∈ C0c :=
    C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c x61K_mem_C0c) δ1hK_mem_C0c
  have hx34 : x34K ∈ C0c := C0c.mul_mem (C0c.mul_mem δ0hK_mem_C0c hx25) δ0hK_mem_C0c
  have hx43 : x43K ∈ C0c := C0c.mul_mem (C0c.mul_mem δ0hK_mem_C0c hx52) δ0hK_mem_C0c
  exact C0c.mul_mem hx34 hx43

theorem v1K_mem_C0c :
    v1K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem (C0c.mul_mem β3K_mem_C0c β3K_mem_C0c) vK_mem_C0c) β3K_mem_C0c

theorem exists_C1c_of_mem
    {x : ℕ}
    (hx : x ∈ Native.glWit0Pts 1) :
    ∃ hx' : x < 2300, ∃ a ∈ C1c, co2PermHom (a * uK) glP0 = ⟨x, hx'⟩ := by
  obtain ⟨e, he, het, hex⟩ := mem_glWit0Pts.1 hx
  obtain ⟨hx', hC0, hfix, -, hmap⟩ := glWit0_spec he
  rw [het, glFormK_one] at hmap
  subst hex
  exact ⟨hx', glE e.2.2, ⟨hC0, hfix⟩, hmap⟩

theorem closure_psiK_M2 :
    Subgroup.closure {σ | ∃ w ∈ Native.glM2Words, psiK (glE w) = σ} = co2P01 := by
  have hbase : Native.glChainM2Base = ([3, 2, 8, 5] : List (Fin 2300)).map Fin.val := by
    decide
  have h : Native.glChainOK Native.glM2Words Native.glChainM2Base Native.glChainM2W 13063680 =
      true := glChainM2_check
  rw [hbase] at h
  have hcard := closure_psiK_card (by decide) glM2Words_lt h
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, card_co2P01])
  rw [Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨h0, h1⟩ := glM2Words_fix w hw
  refine ⟨⟨psiK_mem_co2P _, MulAction.mem_stabilizer_iff.2 ?_⟩,
    MulAction.mem_stabilizer_iff.2 ?_⟩
  · rw [Equiv.Perm.smul_def, ← cPerm_p0, psiK_fix_iff]
    exact h0
  · rw [Equiv.Perm.smul_def, ← cPerm_582, psiK_fix_iff]
    exact h1

theorem glChainCz_parts :
    (∀ k ∈ Native.glCzLetters, Native.glMaps (Native.glR [k]) 80 80 = true) ∧
    Native.glChainOK Native.glCzWords Native.glChainCzBase Native.glChainCzW 743178240 = true := by
  have h := glChainCz_check
  simp only [Native.glChainCzOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h

theorem glCzWords_lt : ∀ w ∈ Native.glCzWords, ∀ k ∈ w, k < 22 := by decide

theorem glCzLetters_mem
    {k : ℕ}
    (hk : k ∈ Native.glCzLetters) : glE [k] ∈ Cz ∧ glE [k] ∈ G1c := by
  have hlet : ∀ k ∈ Native.glCzLetters, k ∈ Native.glCzLet := by decide
  have hlt : ∀ k ∈ Native.glCzLetters, k < 22 := by decide
  refine ⟨glE_mem_Cz fun j hj => ?_, ?_⟩
  · rw [List.mem_singleton.1 hj]
    exact hlet k hk
  · exact co2PermHom_apply_of_maps (glE_val fun j hj => by
      rw [List.mem_singleton.1 hj]
      exact hlt k hk) (by norm_num) (by norm_num) (glChainCz_parts.1 k hk)

theorem glCzWords_mem_Cz :
    ∀ w ∈ Native.glCzWords, glE w ∈ Cz := by
  intro w hw
  simp only [Native.glCzWords, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨k, hk, rfl⟩ | rfl
  · exact (glCzLetters_mem hk).1
  · exact uK_mem_Cz

theorem closure_glCzWords :
    Subgroup.closure {g | ∃ w ∈ Native.glCzWords, glE w = g} = Cz := by
  have hbase : Native.glChainCzBase = ([1, 4, 5, 3, 0, 2] : List (Fin 2300)).map Fin.val := by
    decide
  have h := glChainCz_parts.2
  rw [hbase] at h
  have hcard := closure_psiK_card (by decide) glCzWords_lt h
  have hset : psiK '' {g | ∃ w ∈ Native.glCzWords, glE w = g} =
      {σ | ∃ w ∈ Native.glCzWords, psiK (glE w) = σ} := by
    ext σ
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hmap : (Subgroup.closure {g | ∃ w ∈ Native.glCzWords, glE w = g}).map psiK =
      Subgroup.closure {σ | ∃ w ∈ Native.glCzWords, psiK (glE w) = σ} := by
    rw [MonoidHom.map_closure, hset]
  have hc : Nat.card (Subgroup.closure {g | ∃ w ∈ Native.glCzWords, glE w = g}) = 743178240 := by
    rw [← Subgroup.card_map_of_injective psiK_injective, hmap, hcard]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hc, natCard_Cz])
  rw [Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact glCzWords_mem_Cz w hw

theorem glCosetLab_parts :
    stabRec.1[Native.glCArr[578]!]! = 36 ∧ stabRec.1[Native.glCArr[3]!]! = 4 ∧
    stabRec.1[Native.glCArr[487]!]! = 5 ∧ p01Rec.1[Native.glCArr[3]!]! = 4 ∧
    p0Rec.1[2]! = 1 ∧ p0Rec.1[8]! = 1 ∧ ∀ x ∈ [578, 3, 487, 1172], x ∈ Native.glWit0Pts 1 := by
  have h := glCosetLab_check
  simp only [Native.glCosetLabOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end CFSG.Sporadic.Co2Smith
