module

public import CFSG.Quasithin.Background.F918W5
public import CFSG.Quasithin.Background.F918W6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.D35ValChk

open Matrix

private theorem kid_lt_pow18 : kid < 2 ^ 18 := by decide

private theorem toM_expand_kid_one : toM (expand kid) = 1 := by
  rw [show expand kid = idm by decide, toM_idm]

private theorem toM_expand_kmul_lt {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) :
    toM (expand (kmul a b)) = toM (expand a) * toM (expand b) := by
  rw [expand_kmul ha hb, toM_bmul]

private theorem code_eq_of_toM {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18)
    (h : toM (expand a) = toM (expand b)) : a = b :=
  expand_inj ha hb (toM_inj (expand_lt a) (expand_lt b) h)

private theorem G0_eq_of_code {x y : G0} {c : Nat}
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c))
    (hy : ((y : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c)) :
    x = y :=
  Subtype.ext (Units.ext (hx.trans hy.symm))

private theorem G0_eq_one_of_code {x : G0}
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand kid)) :
    x = 1 :=
  G0_eq_of_code hx toM_expand_kid_one.symm

private theorem G0_code_mul {x y : G0} {c d : Nat} (hc : c < 2 ^ 18) (hd : d < 2 ^ 18)
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c))
    (hy : ((y : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand d)) :
    (((x * y : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      toM (expand (kmul c d)) := by
  rw [Subgroup.coe_mul, Units.val_mul, hx, hy, toM_expand_kmul_lt hc hd]

private theorem G0_code_inv {x : G0} {c d : Nat} (hc : c < 2 ^ 18) (hd : d < 2 ^ 18) (hcd : kmul c d = kid)
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c)) :
    (((x⁻¹ : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      toM (expand d) := by
  rw [Subgroup.coe_inv]
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hx, ← toM_expand_kmul_lt hc hd, hcd, toM_expand_kid_one])

private theorem memF_iff_eq {a b c : Nat} : memF a b c = true ↔ c = a ∨ c = b ∨ c = kmul a b := by
  simp only [memF, Bool.or_eq_true, Nat.beq_eq, or_assoc]

private theorem G0_invol_code {x : G0} (hx2 : x * x = 1) (hx1 : x ≠ 1) {c : Nat} (hc : c ∈ gl)
    (hcl : c < 2 ^ 18)
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c)) :
    c ∈ invList := by
  refine mem_invList.mpr ⟨hc, fun h => hx1 (G0_eq_one_of_code (h ▸ hx)), ?_⟩
  apply code_eq_of_toM (kmul_lt c c) kid_lt_pow18
  rw [← G0_code_mul hcl hcl hx hx, hx2, toM_expand_kid_one]
  rfl

private theorem G0_comm_code {x y : G0} (hxy : x * y = y * x) {c d : Nat} (hc : c < 2 ^ 18) (hd : d < 2 ^ 18)
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c))
    (hy : ((y : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand d)) :
    comm c d = true := by
  have h : kmul c d = kmul d c := code_eq_of_toM (kmul_lt c d) (kmul_lt d c) (by
    rw [← G0_code_mul hc hd hx hy, ← G0_code_mul hd hc hy hx, hxy])
  simp only [comm, h, Nat.beq_refl]

private theorem mem_V4set_iff_G0 {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) {A B : G0}
    (hA : ((A : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand a))
    (hB : ((B : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand b))
    (x : G0) : x ∈ V4set a b ↔ x = 1 ∨ x = A ∨ x = B ∨ x = A * B := by
  have hAB := G0_code_mul ha hb hA hB
  constructor
  · rintro (h | ⟨c, hc, hxc⟩)
    · exact Or.inl h
    · rcases memF_iff_eq.mp hc with rfl | rfl | rfl
      · exact Or.inr (Or.inl (G0_eq_of_code hxc hA))
      · exact Or.inr (Or.inr (Or.inl (G0_eq_of_code hxc hB)))
      · exact Or.inr (Or.inr (Or.inr (G0_eq_of_code hxc hAB)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨a, memF_iff_eq.mpr (Or.inl rfl), hA⟩
    · exact Or.inr ⟨b, memF_iff_eq.mpr (Or.inr (Or.inl rfl)), hB⟩
    · exact Or.inr ⟨kmul a b, memF_iff_eq.mpr (Or.inr (Or.inr rfl)), hAB⟩

private theorem G0_mem_four_of_memF {a b c : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) {A B x : G0}
    (hA : ((A : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand a))
    (hB : ((B : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand b))
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c))
    (hc : memF a b c = true) : x = A ∨ x = B ∨ x = A * B := by
  rcases memF_iff_eq.mp hc with rfl | rfl | rfl
  · exact Or.inl (G0_eq_of_code hx hA)
  · exact Or.inr (Or.inl (G0_eq_of_code hx hB))
  · exact Or.inr (Or.inr (G0_eq_of_code hx (G0_code_mul ha hb hA hB)))

private theorem bitSet_fixMask_of_fix {x : G0} {c n : Nat} (hn : n < 64)
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c))
    (hv : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ vecOfBits n =
      vecOfBits n) :
    bitSet (fixMask c) n = true := by
  rw [hx, toM_expand_mulVec] at hv
  exact (bitSet_fixMask c n hn).mpr (vecOfBits_inj ((kapply_lt c n).trans_le (by norm_num)) hn hv)

private theorem card_le_popc {P : (Fin 6 → ZMod 2) → Prop} (m : Nat)
    (hP : ∀ n, n < 64 → P (vecOfBits n) → bitSet m n = true) : Nat.card {v // P v} ≤ popc m := by
  classical
  rw [popc_eq_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine le_trans (Finset.card_le_card fun v hv => ?_) (Finset.card_image_le (f := vecOfBits))
  obtain ⟨n, hn, rfl⟩ := vecOfBits_surj v
  exact Finset.mem_image_of_mem _
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hP n hn (Finset.mem_filter.mp hv).2⟩)

private theorem card_fix_le_fixMask {E : Subgroup G0} {x : G0} (hxE : x ∈ E) {c : Nat}
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c)) :
    Nat.card {v : Fin 6 → ZMod 2 // ∀ e ∈ E,
      (((e : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} ≤
      popc (fixMask c) :=
  card_le_popc _ fun _ hn hv => bitSet_fixMask_of_fix hn hx (hv x hxE)

private theorem card_fix_le_land {E : Subgroup G0} {x y : G0} (hxE : x ∈ E) (hyE : y ∈ E) {c d : Nat}
    (hx : ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c))
    (hy : ((y : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand d)) :
    Nat.card {v : Fin 6 → ZMod 2 // ∀ e ∈ E,
      (((e : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} ≤
      popc (Nat.land (fixMask c) (fixMask d)) :=
  card_le_popc _ fun n hn hv => by
    simp only [bitSet_land, bitSet_fixMask_of_fix hn hx (hv x hxE), bitSet_fixMask_of_fix hn hy (hv y hyE),
      Bool.and_true]

private theorem subgroup_card_le_finset {G : Type*} [Group G] (E : Subgroup G) (T : Finset G)
    (hT : ∀ x ∈ E, x ∈ T) : Nat.card E ≤ T.card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective (fun x : E => (⟨x.1, hT x.1 x.2⟩ : T))
    fun x y hxy => Subtype.ext (congrArg (Subtype.val : T → G) hxy)

private theorem klein_four_iff {G : Type*} [Group G] {A B U W : G} (hAA : A * A = 1) (hBB : B * B = 1)
    (hAB : A * B = B * A) (hU : U = A ∨ U = B ∨ U = A * B) (hW : W = A ∨ W = B ∨ W = A * B) (hUW : U ≠ W)
    (x : G) : (x = 1 ∨ x = U ∨ x = W ∨ x = U * W) ↔ (x = 1 ∨ x = A ∨ x = B ∨ x = A * B) := by
  have e1 : A * (A * B) = B := by rw [← mul_assoc, hAA, one_mul]
  have e2 : B * (A * B) = A := by rw [hAB, ← mul_assoc, hBB, one_mul]
  have e3 : A * B * A = B := by rw [hAB, mul_assoc, hAA, mul_one]
  have e4 : A * B * B = A := by rw [mul_assoc, hBB, mul_one]
  rcases hU with rfl | rfl | rfl <;> rcases hW with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hUW
    | exact Iff.rfl
    | (simp only [e1, e2, e3, e4, ← hAB]; tauto)

private theorem conj_four_iff {G : Type*} [Group G] (g h X Y : G) :
    (h = 1 ∨ h = g * X * g⁻¹ ∨ h = g * Y * g⁻¹ ∨ h = g * X * g⁻¹ * (g * Y * g⁻¹)) ↔
      (g⁻¹ * h * g = 1 ∨ g⁻¹ * h * g = X ∨ g⁻¹ * h * g = Y ∨ g⁻¹ * h * g = X * Y) := by
  have key : ∀ Z : G, h = g * Z * g⁻¹ ↔ g⁻¹ * h * g = Z := fun Z => by
    constructor <;> rintro rfl <;> group
  have h1 : h = 1 ↔ g⁻¹ * h * g = 1 := by
    rw [← key 1, mul_one, mul_inv_cancel]
  have h4 : g * X * g⁻¹ * (g * Y * g⁻¹) = g * (X * Y) * g⁻¹ := by group
  rw [h4, h1, key X, key Y, key (X * Y)]

theorem offender_classification (hF : D35Facts) {E : Subgroup G0} (hE : OffF2 E) :
    ∃ a b, (a, b) ∈ offPairs ∧ ∀ h : G0, h ∈ E ↔ h ∈ V4set a b := by
  obtain ⟨hne, hcomm, hsq, hcard⟩ := hE
  have hinv : ∀ x ∈ E, x ≠ 1 → ∀ c ∈ gl,
      ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c) →
        c ∈ invList := fun x hx hx1 c hc hxc =>
    G0_invol_code ((pow_two x).symm.trans (hsq x hx)) hx1 hc (hF.gl_lt c hc) hxc
  obtain ⟨h, hhE, hh1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left hne
  obtain ⟨a, haG, hha⟩ := G0_code hF h
  have haI := hinv h hhE hh1 a haG hha
  have hal : a < 2 ^ 18 := hF.gl_lt a haG
  by_cases hB : ∃ h' ∈ E, h' ≠ 1 ∧ h' ≠ h
  · obtain ⟨h', hh'E, hh'1, hh'h⟩ := hB
    obtain ⟨b, hbG, hhb⟩ := G0_code hF h'
    have hbI := hinv h' hh'E hh'1 b hbG hhb
    have hbl : b < 2 ^ 18 := hF.gl_lt b hbG
    have hab : a ≠ b := fun e => hh'h (G0_eq_of_code hhb (e ▸ hha))
    have hcab : comm a b = true := G0_comm_code (hcomm h hhE h' hh'E) hal hbl hha hhb
    have hmem : ∀ x : G0, x ∈ E ↔ x ∈ V4set a b := by
      intro x
      constructor
      · intro hx
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · obtain ⟨c, hcG, hxc⟩ := G0_code hF x
          have hcl : c < 2 ^ 18 := hF.gl_lt c hcG
          refine Or.inr ⟨c, memF_iff_eq.mpr (hF.no_rank3 a haI b hbI hab hcab c (hinv x hx hx1 c hcG hxc)
            (G0_comm_code (hcomm h hhE x hx) hal hcl hha hxc) (G0_comm_code (hcomm h' hh'E x hx) hbl hcl hhb hxc)),
            hxc⟩
      · intro hx
        rcases (mem_V4set_iff_G0 hal hbl hha hhb x).mp hx with rfl | rfl | rfl | rfl
        · exact E.one_mem
        · exact hhE
        · exact hh'E
        · exact E.mul_mem hhE hh'E
    refine ⟨a, b, mem_offPairs.mpr ⟨haI, hbI, hab, hcab, ?_⟩, hmem⟩
    have hE4 : Nat.card E ≤ 4 := by
      classical
      refine (subgroup_card_le_finset E {1, h, h', h * h'} fun x hx => ?_).trans Finset.card_le_four
      rcases (mem_V4set_iff_G0 hal hbl hha hhb x).mp ((hmem x).mp hx) with rfl | rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _)))
    have h64 := hcard.trans (Nat.mul_le_mul hE4 (card_fix_le_land hhE hh'E hha hhb))
    omega
  · have hA : ∀ x ∈ E, x = 1 ∨ x = h := fun x hx => by
      by_contra hc
      rw [not_or] at hc
      exact hB ⟨x, hx, hc.1, hc.2⟩
    have hE2 : Nat.card E ≤ 2 := by
      classical
      refine (subgroup_card_le_finset E {1, h} fun x hx => ?_).trans Finset.card_le_two
      rcases hA x hx with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h64 := hcard.trans (Nat.mul_le_mul hE2 (card_fix_le_fixMask hhE hha))
    have h32 := hF.inv_fix a haI
    exfalso
    omega

theorem V4set_conj (hF : D35Facts) {a b : Nat} (hab : (a, b) ∈ offPairs) :
    ∃ g : G0, ∀ h : G0, h ∈ V4set a b ↔ g⁻¹ * h * g ∈ V4set e1 e2 := by
  obtain ⟨haI, hbI, -, hcab, -⟩ := mem_offPairs.mp hab
  obtain ⟨he1I, he2I, -, -, -⟩ := mem_offPairs.mp hF.off_ref
  obtain ⟨γ, γ', hγ, hγ', hγγ', hu, hw, huw⟩ := hF.off_conj (a, b) hab
  obtain ⟨haG, -, haa⟩ := mem_invList.mp haI
  obtain ⟨hbG, -, hbb⟩ := mem_invList.mp hbI
  have he1G := (mem_invList.mp he1I).1
  have he2G := (mem_invList.mp he2I).1
  have hal : a < 2 ^ 18 := hF.gl_lt a haG
  have hbl : b < 2 ^ 18 := hF.gl_lt b hbG
  have he1l : e1 < 2 ^ 18 := hF.gl_lt e1 he1G
  have he2l : e2 < 2 ^ 18 := hF.gl_lt e2 he2G
  have hγl : γ < 2 ^ 18 := hF.gl_lt γ hγ
  have hγ'l : γ' < 2 ^ 18 := hF.gl_lt γ' hγ'
  obtain ⟨A, hA⟩ := exists_G0 hF haG
  obtain ⟨B, hB⟩ := exists_G0 hF hbG
  obtain ⟨E1, hE1⟩ := exists_G0 hF he1G
  obtain ⟨E2, hE2⟩ := exists_G0 hF he2G
  obtain ⟨g, hg⟩ := exists_G0 hF hγ
  have hginv := G0_code_inv hγl hγ'l hγγ' hg
  have hU := G0_code_mul (kmul_lt _ _) hγ'l (G0_code_mul hγl he1l hg hE1) hginv
  have hW := G0_code_mul (kmul_lt _ _) hγ'l (G0_code_mul hγl he2l hg hE2) hginv
  have hAA : A * A = 1 := G0_eq_one_of_code (haa ▸ G0_code_mul hal hal hA hA)
  have hBB : B * B = 1 := G0_eq_one_of_code (hbb ▸ G0_code_mul hbl hbl hB hB)
  have hABc : A * B = B * A :=
    G0_eq_of_code (G0_code_mul hal hbl hA hB) (Nat.eq_of_beq_eq_true hcab ▸ G0_code_mul hbl hal hB hA)
  have hUW : g * E1 * g⁻¹ ≠ g * E2 * g⁻¹ := by
    intro e
    rw [e] at hU
    exact huw (code_eq_of_toM (kmul_lt _ _) (kmul_lt _ _) (hU.symm.trans hW))
  refine ⟨g, fun h => ?_⟩
  rw [mem_V4set_iff_G0 hal hbl hA hB, mem_V4set_iff_G0 he1l he2l hE1 hE2]
  exact (klein_four_iff hAA hBB hABc (G0_mem_four_of_memF hal hbl hA hB hU hu)
    (G0_mem_four_of_memF hal hbl hA hB hW hw) hUW h).symm.trans (conj_four_iff g h E1 E2)

end CFSG.Quasithin.D35ValChk
