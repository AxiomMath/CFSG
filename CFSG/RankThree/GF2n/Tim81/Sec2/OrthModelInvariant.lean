module

public import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelOrder3

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section FieldLemma

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}

private theorem m3as_range_stable {s : ℕ} (hs2 : 2 ≤ s) {Y : AddSubgroup F}
    (hmul : ∀ c : F, c ≠ 0 → ∀ y ∈ Y, c * c⁻¹ ^ s * y ∈ Y) {φ : Fˣ →* Fˣ}
    (hφ : ∀ u : Fˣ, φ u = u ^ (-((s - 1 : ℕ) : ℤ))) :
    ∀ u ∈ φ.range, ∀ y ∈ Y, (u : F) * y ∈ Y := by
  rintro u ⟨c, hc⟩ y hy
  rw [← hc, hφ]
  rw [Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast]
  have hpow : ((c : F) ^ (s - 1))⁻¹ = (c : F) * (c : F)⁻¹ ^ s := by
    rw [← inv_pow]
    conv_rhs => rw [show s = (s - 1) + 1 by omega]
    rw [pow_succ, ← mul_assoc, mul_comm (c : F) ((c : F)⁻¹ ^ (s - 1)), mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero c), mul_one]
  rw [hpow]
  exact hmul (c : F) (Units.ne_zero c) y hy

private theorem m3as_ker_card_le {s : ℕ} (hs2 : 2 ≤ s) {φ : Fˣ →* Fˣ}
    (hφ : ∀ u : Fˣ, φ u = u ^ (-((s - 1 : ℕ) : ℤ))) :
    Nat.card φ.ker ≤ s - 1 := by
  classical
  have hinj : Nat.card φ.ker ≤ Nat.card {u : Fˣ // u ^ (s - 1) = 1} := by
    refine Nat.card_le_card_of_injective
      (fun u : φ.ker => (⟨u.1, ?_⟩ : {u : Fˣ // u ^ (s - 1) = 1})) ?_
    · have h : φ u.1 = 1 := MonoidHom.mem_ker.mp u.2
      have hφval : φ u.1 = (u.1 ^ (s - 1))⁻¹ := by
        rw [hφ, zpow_neg, zpow_natCast]
      rw [hφval] at h
      simpa using congrArg Inv.inv h
    · intro x y hxy
      exact Subtype.ext
        (congrArg (fun z : {u : Fˣ // u ^ (s - 1) = 1} => z.1) hxy)
  refine hinj.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le (α := Fˣ) (n := s - 1) (by omega)

private theorem m3as_range_card_ge {s : ℕ} (hs2 : 2 ≤ s) (hFcard : Nat.card F = s ^ 2)
    {φ : Fˣ →* Fˣ} (hker_le : Nat.card φ.ker ≤ s - 1) :
    s ≤ Nat.card φ.range := by
  have hcard : Nat.card φ.ker * Nat.card φ.range = Nat.card Fˣ :=
    Subgroup.card_ker_mul_card_range φ
  have hunits : Nat.card Fˣ = s ^ 2 - 1 := by
    rw [Nat.card_units, hFcard]
  have heq : Nat.card φ.ker * Nat.card φ.range + 1 = s ^ 2 := by
    rw [hcard, hunits, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega : 0 < s))]
  by_contra h
  have hn : Nat.card φ.range ≤ s - 1 := by omega
  have hs2' : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs2
  have hk' : (Nat.card φ.ker : ℤ) ≤ (s : ℤ) - 1 := by
    have := hker_le
    omega
  have hn' : (Nat.card φ.range : ℤ) ≤ (s : ℤ) - 1 := by
    have := hn
    omega
  have hk0 : (0 : ℤ) ≤ (Nat.card φ.ker : ℤ) := by positivity
  have hn0 : (0 : ℤ) ≤ (Nat.card φ.range : ℤ) := by positivity
  have heq' : (Nat.card φ.ker : ℤ) * (Nat.card φ.range : ℤ) + 1 = (s : ℤ) ^ 2 := by
    exact_mod_cast heq
  have hmul' : (Nat.card φ.ker : ℤ) * (Nat.card φ.range : ℤ) ≤
      ((s : ℤ) - 1) * ((s : ℤ) - 1) :=
    mul_le_mul hk' hn' hn0 (by omega)
  nlinarith [heq', hmul', hs2']

theorem addSubgroup_eq_top_of_mul_sig_mem (hF : Fintype.card F = 2 ^ (2 * l))
    {Y : AddSubgroup F} (hY : Y ≠ ⊥)
    (hmul : ∀ c : F, c ≠ 0 → ∀ y ∈ Y, c * c⁻¹ ^ 2 ^ l * y ∈ Y) : Y = ⊤ := by
  classical
  set s : ℕ := 2 ^ l with hs
  have hl : 0 < l := by
    by_contra h
    have hl0 : l = 0 := by omega
    subst hl0
    norm_num at hF
    have := Fintype.one_lt_card (α := F)
    omega
  have hs2 : 2 ≤ s := by
    rw [hs]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  have hFcard : Nat.card F = s ^ 2 := by
    rw [Nat.card_eq_fintype_card, hF, hs, ← pow_mul, mul_comm]
  obtain ⟨a, haY, ha0⟩ := (AddSubgroup.bot_or_exists_ne_zero Y).resolve_left hY
  let φ : Fˣ →* Fˣ :=
    MonoidHom.mk' (fun u => u ^ (-((s - 1 : ℕ) : ℤ)))
      (fun u v => (Commute.all u v).mul_zpow _)
  have hφ : ∀ u : Fˣ, φ u = u ^ (-((s - 1 : ℕ) : ℤ)) := fun _ => rfl
  have hstab : ∀ u ∈ φ.range, ∀ y ∈ Y, (u : F) * y ∈ Y :=
    m3as_range_stable hs2 hmul hφ
  have hker_le : Nat.card φ.ker ≤ s - 1 := m3as_ker_card_le hs2 hφ
  have hmain : s ≤ Nat.card φ.range := m3as_range_card_ge hs2 hFcard hker_le
  exact CFSG.GH74.Uniqueness.Bender.addSubgroup_eq_top_of_scalar_stable
    hFcard hs2 Y haY ha0 φ.range hstab (by omega)

end FieldLemma

section OrthModel

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] {l : ℕ}

private theorem m1as_exists_t {D : Subgroup SL(2, F)} (hD : D ≤ upperSylow) :
    ∃ tOf : D → F,
      (∀ (d : D) (h : (d : SL(2, F)) ≠ 1), (d : SL(2, F)) = uMat (tOf d)) ∧
        ∀ (d : D) (h : (d : SL(2, F)) ≠ 1), tOf d ≠ 0 := by
  classical
  let tOf : D → F := fun d =>
    if h : (d : SL(2, F)) = 1 then 0
    else Classical.choose (mem_upperSylow_iff.mp (hD d.2))
  have htOf_eq : ∀ (d : D) (h : (d : SL(2, F)) ≠ 1),
      (d : SL(2, F)) = uMat (tOf d) := by
    intro d h
    rw [show tOf d = Classical.choose (mem_upperSylow_iff.mp (hD d.2)) from dif_neg h]
    exact Classical.choose_spec (mem_upperSylow_iff.mp (hD d.2))
  refine ⟨tOf, htOf_eq, fun d h ht => h ?_⟩
  rw [htOf_eq d h, ht, uMat_zero]

private theorem m1as_coord (hF : Fintype.card F = 2 ^ (2 * l))
    {D : Subgroup SL(2, F)} {X : ↥(hermA l F)}
    (hX : X ∈ fixedSub (hermRep l hF) D) {tOf : D → F}
    (htOf_eq : ∀ (d : D) (h : (d : SL(2, F)) ≠ 1), (d : SL(2, F)) = uMat (tOf d))
    (htOf_ne : ∀ (d : D) (h : (d : SL(2, F)) ≠ 1), tOf d ≠ 0) :
    ∀ (d : D) (h : (d : SL(2, F)) ≠ 1),
      ∃ c : F, c ^ 2 ^ l = c ∧ (X : Matrix (Fin 2) (Fin 2) F) 0 1 = tOf d * c := by
  intro d h
  have hfix : X ∈ fixedSub (hermRep l hF) (Subgroup.zpowers (uMat (tOf d))) := by
    rw [mem_fixedSub_zpowers]
    exact (mem_fixedSub.mp hX) (uMat (tOf d)) (by rw [← htOf_eq d h]; exact d.2)
  exact ((mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) (tOf d) (htOf_ne d h) X).mp hfix).2

private theorem m1as_injective {D : Subgroup SL(2, F)} {X : ↥(hermA l F)} {tOf cOf : D → F}
    (hX01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0)
    (htOf_eq : ∀ (d : D) (h : (d : SL(2, F)) ≠ 1), (d : SL(2, F)) = uMat (tOf d))
    (hval : ∀ (d : D) (h : (d : SL(2, F)) ≠ 1),
      (X : Matrix (Fin 2) (Fin 2) F) 0 1 = tOf d * cOf d)
    (hzero : ∀ (d : D), (d : SL(2, F)) = 1 → cOf d = 0) :
    Function.Injective cOf := by
  have hne : ∀ (d : D), (d : SL(2, F)) ≠ 1 → cOf d ≠ 0 := by
    intro d h hc
    exact hX01 (by rw [hval d h, hc, mul_zero])
  intro d1 d2 h12
  by_cases h1 : (d1 : SL(2, F)) = 1
  · by_cases h2 : (d2 : SL(2, F)) = 1
    · exact Subtype.ext (h1.trans h2.symm)
    · exact absurd (h12.symm.trans (hzero d1 h1)) (hne d2 h2)
  · have h2 : (d2 : SL(2, F)) ≠ 1 := by
      intro h2
      exact hne d1 h1 (h12.trans (hzero d2 h2))
    have ht : tOf d1 = tOf d2 := by
      apply mul_right_cancel₀ (hne d1 h1)
      calc tOf d1 * cOf d1 = (X : Matrix (Fin 2) (Fin 2) F) 0 1 := (hval d1 h1).symm
        _ = tOf d2 * cOf d2 := hval d2 h2
        _ = tOf d2 * cOf d1 := by rw [h12]
    exact Subtype.ext (by rw [htOf_eq d1 h1, htOf_eq d2 h2, ht])

private theorem m1a_card_le_of_coord_ne_zero (hF : Fintype.card F = 2 ^ (2 * l))
    {D : Subgroup SL(2, F)} (hD : D ≤ upperSylow) {X : ↥(hermA l F)}
    (hX : X ∈ fixedSub (hermRep l hF) D)
    (hX01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0) :
    Nat.card D ≤ 2 ^ l := by
  classical
  have hl : 1 ≤ l := one_le_of_card hF
  obtain ⟨tOf, htOf_eq, htOf_ne⟩ := m1as_exists_t hD
  have hcoord := m1as_coord (hF := hF) hX htOf_eq htOf_ne
  let cOf : D → F := fun d =>
    if h : (d : SL(2, F)) = 1 then 0 else Classical.choose (hcoord d h)
  have hcOf : ∀ (d : D) (h : (d : SL(2, F)) ≠ 1),
      cOf d ^ 2 ^ l = cOf d ∧
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 = tOf d * cOf d := by
    intro d h
    rw [show cOf d = Classical.choose (hcoord d h) from dif_neg h]
    exact Classical.choose_spec (hcoord d h)
  have hcOf_one : ∀ (d : D), (d : SL(2, F)) = 1 → cOf d = 0 := by
    intro d h
    exact dif_pos h
  have hinj : Function.Injective cOf :=
    m1as_injective hX01 htOf_eq (fun d h => (hcOf d h).2) hcOf_one
  let f : D → {c : F // c ^ 2 ^ l = c} := fun d =>
    ⟨cOf d, by
      by_cases h : (d : SL(2, F)) = 1
      · rw [show cOf d = 0 from dif_pos h]
        simp
      · exact (hcOf d h).1⟩
  have hf : Function.Injective f := fun d1 d2 h => hinj (congrArg Subtype.val h)
  have hle : Nat.card D ≤ Nat.card {c : F // c ^ 2 ^ l = c} :=
    Nat.card_le_card_of_injective f hf
  rw [card_frob_fixed (F := F) (s := l) hl hF] at hle
  exact hle

theorem fixedSub_hermRep_eq_of_card_lt (hF : Fintype.card F = 2 ^ (2 * l))
    {D : Subgroup SL(2, F)} (hD : D ≤ upperSylow) (hcard : 2 ^ l < Nat.card D) :
    fixedSub (hermRep l hF) D = fixedSub (hermRep l hF) upperSylow := by
  refine le_antisymm ?_ ?_
  · intro X hX
    rw [mem_fixedSub_upperSylow l hF]
    have hl : 1 ≤ l := one_le_of_card hF
    have hpow : 2 ≤ 2 ^ l := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    have hX11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have hlt : 1 < Nat.card D := by omega
      let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hlt
      obtain ⟨d, hd⟩ := exists_ne (1 : D)
      have hd1 : (d : SL(2, F)) ≠ 1 := by
        intro h
        exact hd (Subtype.ext h)
      obtain ⟨t, ht_eq⟩ := mem_upperSylow_iff.mp (hD d.2)
      have ht : t ≠ 0 := by
        intro ht0
        apply hd1
        rw [ht_eq, ht0, uMat_zero]
      have hfix : X ∈ fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) := by
        rw [mem_fixedSub_zpowers]
        exact (mem_fixedSub.mp hX) (uMat t) (by rw [← ht_eq]; exact d.2)
      exact ((mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht X).mp hfix).1
    have hX01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      by_contra hne
      have hle := m1a_card_le_of_coord_ne_zero (hF := hF) hD hX hne
      omega
    exact ⟨hX11, hX01⟩
  · intro X hX
    exact mem_fixedSub.mpr fun d hd => (mem_fixedSub.mp hX) d (hD hd)

private theorem m3b_exists_offdiag (hF : Fintype.card F = 2 ^ (2 * l))
    {U : Submodule (ZMod 2) ↥(hermA l F)}
    (hU : ∀ n ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))),
      ∀ X ∈ U, hermRep l hF n X ∈ U)
    (hlt : fixedSub (hermRep l hF) upperSylow < U) :
    ∃ Y ∈ U, (Y : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
      (Y : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
  classical
  have hle : fixedSub (hermRep l hF) upperSylow ≤ U := le_of_lt hlt
  obtain ⟨X, hXU, hXnot⟩ : ∃ X ∈ U, X ∉ fixedSub (hermRep l hF) upperSylow := by
    by_contra h
    refine (ne_of_lt hlt) (le_antisymm hle fun Y hYU => ?_)
    by_contra hY
    exact h ⟨Y, hYU, hY⟩
  by_cases h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
  · refine ⟨X, hXU, h11, ?_⟩
    intro h01
    exact hXnot ((mem_fixedSub_upperSylow l hF).mpr ⟨h11, h01⟩)
  · have hY : ((hermRep l hF (uMat 1) X - X : ↥(hermA l F)) :
        Matrix (Fin 2) (Fin 2) F) =
        !![(X : Matrix (Fin 2) (Fin 2) F) 0 1 + (X : Matrix (Fin 2) (Fin 2) F) 1 0 +
            (X : Matrix (Fin 2) (Fin 2) F) 1 1,
          (X : Matrix (Fin 2) (Fin 2) F) 1 1;
        (X : Matrix (Fin 2) (Fin 2) F) 1 1, 0] := by
      rw [hermRep_apply]
      simpa using hermAct_uMat_sub l hF 1 X
    refine ⟨hermRep l hF (uMat 1) X - X, ?_, ?_, ?_⟩
    · exact U.sub_mem (hU (uMat 1)
        (Subgroup.le_normalizer (mem_upperSylow_iff.mpr ⟨1, rfl⟩)) X hXU) hXU
    · rw [hY]; simp
    · rw [hY]; simpa using h11

private theorem m3b_offdiag_surjective (hF : Fintype.card F = 2 ^ (2 * l))
    {U : Submodule (ZMod 2) ↥(hermA l F)}
    (hU : ∀ n ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))),
      ∀ X ∈ U, hermRep l hF n X ∈ U)
    {Y : ↥(hermA l F)} (hYU : Y ∈ U)
    (hY11 : (Y : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (hY01 : (Y : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0) :
    ∀ z : F, ∃ W ∈ U, (W : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 ∧
      (W : Matrix (Fin 2) (Fin 2) F) 0 1 = z := by
  classical
  set f : ↥(hermA l F) →+ F :=
    { toFun := fun X => (X : Matrix (Fin 2) (Fin 2) F) 0 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl } with hf
  set Y' : AddSubgroup F := (U.toAddSubgroup ⊓ herm11 l F).map f with hY'
  have hY'ne : Y' ≠ ⊥ := by
    intro hbot
    have hmem : f Y ∈ Y' := AddSubgroup.mem_map_of_mem f
      (show Y ∈ U.toAddSubgroup ⊓ herm11 l F from
        ⟨(Submodule.mem_toAddSubgroup U).mpr hYU, hY11⟩)
    rw [hbot] at hmem
    exact hY01 (AddSubgroup.mem_bot.mp hmem)
  have hY'mul : ∀ c : F, c ≠ 0 → ∀ y ∈ Y', c * c⁻¹ ^ 2 ^ l * y ∈ Y' := by
    intro c hc y hy
    rw [hY'] at hy ⊢
    obtain ⟨W, hW, hWf⟩ := AddSubgroup.mem_map.mp hy
    have hWU : W ∈ U := (Submodule.mem_toAddSubgroup U).mp hW.1
    have hW11 : (W : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := hW.2
    have hW01 : (W : Matrix (Fin 2) (Fin 2) F) 0 1 = y := hWf
    refine AddSubgroup.mem_map.mpr ⟨hermRep l hF (tMat c hc) W, ⟨?_, ?_⟩, ?_⟩
    · exact (Submodule.mem_toAddSubgroup U).mpr
        (hU (tMat c hc) (tMat_mem_normalizer c hc) W hWU)
    · show ((hermRep l hF (tMat c hc) W : ↥(hermA l F)) :
          Matrix (Fin 2) (Fin 2) F) 1 1 = 0
      rw [hermRep_apply, hermAct_tMat_11, sig_apply, hW11, mul_zero]
    · show ((hermRep l hF (tMat c hc) W : ↥(hermA l F)) :
          Matrix (Fin 2) (Fin 2) F) 0 1 = c * c⁻¹ ^ 2 ^ l * y
      rw [hermRep_apply, hermAct_tMat_01, sig_apply, hW01]
  have htop : Y' = ⊤ := addSubgroup_eq_top_of_mul_sig_mem hF hY'ne hY'mul
  intro z
  have hz : z ∈ Y' := by rw [htop]; exact AddSubgroup.mem_top z
  rw [hY'] at hz
  obtain ⟨W, hW, hWf⟩ := AddSubgroup.mem_map.mp hz
  exact ⟨W, (Submodule.mem_toAddSubgroup U).mp hW.1, hW.2, hWf⟩

theorem herm11_le_of_normalizer_invariant (hF : Fintype.card F = 2 ^ (2 * l))
    {U : Submodule (ZMod 2) ↥(hermA l F)}
    (hU : ∀ n ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))),
      ∀ X ∈ U, hermRep l hF n X ∈ U)
    (hlt : fixedSub (hermRep l hF) upperSylow < U) :
    AddSubgroup.toZModSubmodule (n := 2) (herm11 l F) ≤ U := by
  classical
  obtain ⟨Y, hYU, hY11, hY01⟩ := m3b_exists_offdiag hF hU hlt
  have hsurj := m3b_offdiag_surjective hF hU hYU hY11 hY01
  intro Z hZ
  rw [AddSubgroup.mem_toZModSubmodule] at hZ
  have hZ11 : (Z : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := hZ
  obtain ⟨W, hWU, hW11, hW01⟩ := hsurj ((Z : Matrix (Fin 2) (Fin 2) F) 0 1)
  have hdiff : Z - W ∈ fixedSub (hermRep l hF) upperSylow := by
    rw [mem_fixedSub_upperSylow l hF]
    refine ⟨?_, ?_⟩
    · change (Z : Matrix (Fin 2) (Fin 2) F) 1 1 - (W : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
      rw [hZ11, hW11, sub_zero]
    · change (Z : Matrix (Fin 2) (Fin 2) F) 0 1 - (W : Matrix (Fin 2) (Fin 2) F) 0 1 = 0
      rw [hW01, sub_self]
  have hdiffU : Z - W ∈ U := le_of_lt hlt hdiff
  have hZW : Z = W + (Z - W) := by abel
  rw [hZW]
  exact U.add_mem hWU hdiffU

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W}

private theorem m1b_map_fixedSub_conj (hF : Fintype.card F = 2 ^ (2 * l)) {x : SL(2, F)} :
    Submodule.map (hermRep l hF x⁻¹)
      (fixedSub (hermRep l hF) (upperSylow.map (MulAut.conj x).toMonoidHom)) =
      fixedSub (hermRep l hF) upperSylow := by
  have hcomp : (hermRep l hF x⁻¹).comp (hermRep l hF x) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, LinearMap.id_apply, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  calc Submodule.map (hermRep l hF x⁻¹)
        (fixedSub (hermRep l hF) (upperSylow.map (MulAut.conj x).toMonoidHom))
      = Submodule.map (hermRep l hF x⁻¹)
          ((fixedSub (hermRep l hF) upperSylow).map (hermRep l hF x)) := by
          rw [fixedSub_map_conj (hermRep l hF) x upperSylow]
    _ = Submodule.map ((hermRep l hF x⁻¹).comp (hermRep l hF x))
          (fixedSub (hermRep l hF) upperSylow) := by
          rw [Submodule.map_comp]
    _ = fixedSub (hermRep l hF) upperSylow := by
          rw [hcomp, Submodule.map_id]

theorem IsOrthModule.fixedSub_eq_of_card_lt (hF : Fintype.card F = 2 ^ (2 * l))
    (hρ : IsOrthModule hF ρ) {A D : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) (hDA : D ≤ A) (hcard : 2 ^ l < Nat.card D) :
    fixedSub ρ D = fixedSub ρ A := by
  obtain ⟨j, β, hβ⟩ := hρ
  have hsA := fieldAut_image_sylow A hA2 hA j
  have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
    rw [hsA.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hsA.1 hAeq
  have hEqA : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom := by
    ext a
    rw [hx a]
    constructor
    · intro ha
      exact ⟨x⁻¹ * a * x, ha, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs, rfl⟩
      change x⁻¹ * (x * s * x⁻¹) * x ∈ upperSylow
      simpa [mul_assoc] using hs
  have hD' : (D.map (fieldAut F j)).map (MulAut.conj x⁻¹).toMonoidHom ≤ upperSylow := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := hd
    obtain ⟨f, hf, rfl⟩ := he
    have hmem : fieldAut F j f ∈ A.map (fieldAut F j) :=
      Subgroup.mem_map_of_mem _ (hDA hf)
    simpa [MulAut.conj_apply] using (hx (fieldAut F j f)).mp hmem
  have hcard' : 2 ^ l <
      Nat.card ((D.map (fieldAut F j)).map (MulAut.conj x⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective,
      Subgroup.card_map_of_injective (fieldAutEquiv j).injective]
    exact hcard
  have hmodel : fixedSub (hermRep l hF)
      ((D.map (fieldAut F j)).map (MulAut.conj x⁻¹).toMonoidHom) =
      fixedSub (hermRep l hF) upperSylow :=
    fixedSub_hermRep_eq_of_card_lt hF hD' hcard'
  have hfixD : Submodule.map (hermRep l hF x⁻¹)
      (fixedSub (hermRep l hF) (D.map (fieldAut F j))) =
      fixedSub (hermRep l hF) upperSylow :=
    (fixedSub_map_conj (hermRep l hF) x⁻¹ (D.map (fieldAut F j))).symm.trans hmodel
  have hfixA : Submodule.map (hermRep l hF x⁻¹)
      (fixedSub (hermRep l hF) (A.map (fieldAut F j))) =
      fixedSub (hermRep l hF) upperSylow := by
    rw [hEqA]
    exact m1b_map_fixedSub_conj hF
  have hinj : Function.Injective (hermRep l hF x⁻¹ : ↥(hermA l F) → ↥(hermA l F)) := by
    intro u v h
    have := congrArg (hermRep l hF x) h
    simpa using this
  have hmod : fixedSub (hermRep l hF) (D.map (fieldAut F j)) =
      fixedSub (hermRep l hF) (A.map (fieldAut F j)) :=
    Submodule.map_injective_of_injective
      (f := (hermRep l hF x⁻¹ : ↥(hermA l F) →ₗ[ZMod 2] ↥(hermA l F))) hinj
      (hfixD.trans hfixA.symm)
  ext w
  constructor
  · intro hw
    have h1 : β w ∈ fixedSub (hermRep l hF) (D.map (fieldAut F j)) :=
      (fixedSub_fieldAut_mem (hF := hF) (j := j) hβ D w).mp hw
    rw [hmod] at h1
    exact (fixedSub_fieldAut_mem (hF := hF) (j := j) hβ A w).mpr h1
  · intro hw d hd
    exact hw d (hDA hd)

theorem IsOrthModule.pow_mul_card_mul_card_fixedSub_le (hF : Fintype.card F = 2 ^ (2 * l))
    (hρ : IsOrthModule hF ρ) {A D : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) (hDA : D ≤ A) (hD : D ≠ ⊥) :
    2 ^ l * Nat.card D * Nat.card ↥(fixedSub ρ D) ≤ Nat.card W := by
  have hl : 1 ≤ l := one_le_of_card hF
  have hW : Nat.card W = 2 ^ (4 * l) := by
    obtain ⟨j, β, hβ⟩ := hρ
    rw [Nat.card_congr β.toEquiv, card_hermA (s := l) hl hF]
  by_cases hDle : Nat.card D ≤ 2 ^ l
  · rw [hW]
    haveI hnt : Nontrivial ↥D := (Subgroup.bot_or_nontrivial D).resolve_left hD
    obtain ⟨d, hd1⟩ := exists_ne (1 : ↥D)
    let S : Submodule (ZMod 2) W := fixedSub ρ (Subgroup.zpowers (d : SL(2, F)))
    have hfixz : Nat.card ↥S = 2 ^ (2 * l) :=
      IsOrthModule.card_fixedSub_zpowers hF hρ A hA2 hA (hDA d.2)
        (fun h => hd1 (Subtype.ext h))
    have hsub : fixedSub ρ D ≤ S := by
      intro w hw x hx
      exact hw x (Subgroup.zpowers_le.mpr d.2 hx)
    let f : ↥(fixedSub ρ D) → ↥S := fun w => ⟨w.1, hsub w.2⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : ↥S => (z : W)) h)
    have hcardC : Nat.card ↥(fixedSub ρ D) ≤ 2 ^ (2 * l) :=
      (Nat.card_le_card_of_injective f hf).trans (le_of_eq hfixz)
    calc 2 ^ l * Nat.card D * Nat.card ↥(fixedSub ρ D)
        ≤ 2 ^ l * 2 ^ l * 2 ^ (2 * l) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hDle) hcardC
      _ = 2 ^ (4 * l) := by
          rw [← pow_add, ← pow_add]
          ring
  · rw [hW]
    have hDcard : 2 ^ l < Nat.card D := lt_of_not_ge hDle
    have hfix : fixedSub ρ D = fixedSub ρ A :=
      IsOrthModule.fixedSub_eq_of_card_lt hF hρ hA2 hA hDA hDcard
    have hcardC : Nat.card ↥(fixedSub ρ D) = 2 ^ l := by
      rw [hfix, IsOrthModule.card_fixedSub hF hρ A hA2 hA]
    have hDcardA : Nat.card D ≤ 2 ^ (2 * l) :=
      (Subgroup.card_le_of_le hDA).trans (le_of_eq hA)
    calc 2 ^ l * Nat.card D * Nat.card ↥(fixedSub ρ D)
        ≤ 2 ^ l * 2 ^ (2 * l) * 2 ^ l :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hDcardA) (le_of_eq hcardC)
      _ = 2 ^ (4 * l) := by
          rw [← pow_add, ← pow_add]
          ring

private theorem m3c_transported_invariant
    (hF : Fintype.card F = 2 ^ (2 * l)) {A : Subgroup SL(2, F)} {j : ℕ}
    {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    {x : SL(2, F)}
    (hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom)
    {U : Submodule (ZMod 2) W}
    (hU : ∀ n ∈ Subgroup.normalizer (A : Set (SL(2, F))), ∀ w ∈ U, ρ n w ∈ U) :
    ∀ n' ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))),
      ∀ w ∈ (U.map (β.toAddMonoidHom.toZModLinearMap 2)).map (hermRep l hF x⁻¹),
        hermRep l hF n' w ∈
          (U.map (β.toAddMonoidHom.toZModLinearMap 2)).map (hermRep l hF x⁻¹) := by
  intro n' hn' w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
  have hm : x * n' * x⁻¹ ∈
      Subgroup.normalizer (A.map (fieldAut F j) : Set (SL(2, F))) := by
    rw [hEq, ← Subgroup.map_normalizer_eq_of_bijective (upperSylow)
      (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).bijective]
    exact Subgroup.mem_map_of_mem _ hn'
  have hmapN : (Subgroup.normalizer (A : Set (SL(2, F)))).map (fieldAut F j) =
      Subgroup.normalizer (A.map (fieldAut F j) : Set (SL(2, F))) := by
    simpa using Subgroup.map_normalizer_eq_of_bijective A (fieldAutEquiv j).bijective
  obtain ⟨n, hn, hfield⟩ := Subgroup.mem_map.1 (by rw [hmapN]; exact hm)
  have hmul : (n' : SL(2, F)) * x⁻¹ = x⁻¹ * fieldAut F j n := by
    rw [hfield]; group
  have hβcoe : (β.toAddMonoidHom.toZModLinearMap 2) u = β u := rfl
  rw [hβcoe]
  have hβu : β (ρ n u) = hermRep l hF (fieldAut F j n) (β u) := by
    rw [hermRep_apply]; exact hβ n u
  have hkey : hermRep l hF n' (hermRep l hF x⁻¹ (β u)) =
      hermRep l hF x⁻¹ (β (ρ n u)) := by
    rw [hβu, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hmul]
  rw [hkey]
  exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (hU n hn u hu))

private theorem m3c_transported_lt
    (hF : Fintype.card F = 2 ^ (2 * l)) {A : Subgroup SL(2, F)} {j : ℕ}
    {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    {x : SL(2, F)}
    (hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom)
    {U : Submodule (ZMod 2) W} (hlt : fixedSub ρ A < U) :
    fixedSub (hermRep l hF) upperSylow <
      (U.map (β.toAddMonoidHom.toZModLinearMap 2)).map (hermRep l hF x⁻¹) := by
  obtain ⟨hleA, u, huU, huC⟩ := SetLike.lt_iff_le_and_exists.1 hlt
  have hle : fixedSub (hermRep l hF) upperSylow ≤
      (U.map (β.toAddMonoidHom.toZModLinearMap 2)).map (hermRep l hF x⁻¹) := by
    intro w hw
    have h1 : hermRep l hF x w ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) := by
      rw [hEq, fixedSub_map_conj]
      exact Submodule.mem_map_of_mem hw
    have h2 : β.symm (hermRep l hF x w) ∈ fixedSub ρ A :=
      (fixedSub_fieldAut_mem (hF := hF) (j := j) hβ A _).mpr (by simpa using h1)
    have h3 : β.symm (hermRep l hF x w) ∈ U := hleA h2
    have hw' : hermRep l hF x⁻¹ (β (β.symm (hermRep l hF x w))) = w := by
      rw [β.apply_symm_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply]
    rw [← hw']
    exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem h3)
  have hnot : hermRep l hF x⁻¹ (β u) ∉ fixedSub (hermRep l hF) upperSylow := by
    intro hmem
    have h2 : hermRep l hF x (hermRep l hF x⁻¹ (β u)) ∈
        fixedSub (hermRep l hF) (A.map (fieldAut F j)) := by
      rw [hEq, fixedSub_map_conj]
      exact Submodule.mem_map_of_mem hmem
    have h3 : β u ∈ fixedSub (hermRep l hF) (A.map (fieldAut F j)) := by
      have h4 := h2
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] at h4
      exact h4
    exact huC ((fixedSub_fieldAut_mem (hF := hF) (j := j) hβ A u).mpr h3)
  exact SetLike.lt_iff_le_and_exists.2
    ⟨hle, hermRep l hF x⁻¹ (β u),
      Submodule.mem_map_of_mem (Submodule.mem_map_of_mem huU), hnot⟩

theorem IsOrthModule.card_le_of_normalizer_invariant (hF : Fintype.card F = 2 ^ (2 * l))
    (hρ : IsOrthModule hF ρ) {A : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l)) {U : Submodule (ZMod 2) W}
    (hU : ∀ n ∈ Subgroup.normalizer (A : Set (SL(2, F))), ∀ w ∈ U, ρ n w ∈ U)
    (hlt : fixedSub ρ A < U) : Nat.card W ≤ 2 ^ l * Nat.card U := by
  obtain ⟨j, β, hβ⟩ := hρ
  have hl : 1 ≤ l := one_le_of_card hF
  have hs := fieldAut_image_sylow A hA2 hA j
  have hAeq : Nat.card (A.map (fieldAut F j)) = Nat.card F := by
    rw [hs.2, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup (A.map (fieldAut F j)) hs.1 hAeq
  have hEq : A.map (fieldAut F j) = upperSylow.map (MulAut.conj x).toMonoidHom := by
    ext a
    rw [hx a]
    constructor
    · intro ha
      exact ⟨x⁻¹ * a * x, ha, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨s, hs', rfl⟩
      change x⁻¹ * (x * s * x⁻¹) * x ∈ upperSylow
      simpa [mul_assoc] using hs'
  let V : Submodule (ZMod 2) ↥(hermA l F) :=
    (U.map (β.toAddMonoidHom.toZModLinearMap 2)).map (hermRep l hF x⁻¹)
  have hV : fixedSub (hermRep l hF) upperSylow < V :=
    m3c_transported_lt hF hβ hEq hlt
  have hVin : ∀ n ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))),
      ∀ w ∈ V, hermRep l hF n w ∈ V :=
    m3c_transported_invariant hF hβ hEq hU
  have hherm11 : AddSubgroup.toZModSubmodule (n := 2) (herm11 l F) ≤ V :=
    herm11_le_of_normalizer_invariant hF hVin hV
  have h11 : 2 ^ (3 * l) ≤ Nat.card ↥V := by
    rw [← card_herm11 (hF := hF)]
    refine Nat.card_le_card_of_injective
      (fun Z : ↥(herm11 l F) =>
        (⟨Z.1, hherm11 ((AddSubgroup.mem_toZModSubmodule (n := 2)
          (S := herm11 l F)).mpr Z.2)⟩ : ↥V)) ?_
    intro Z Z' h
    exact Subtype.ext (congrArg (fun t : ↥V => (t.1 : ↥(hermA l F))) h)
  have hcardV : Nat.card ↥V = Nat.card ↥U := by
    have hinj : Function.Injective (hermRep l hF x⁻¹ : ↥(hermA l F) → ↥(hermA l F)) := by
      intro p q h
      have := congrArg (hermRep l hF x) h
      simpa using this
    have hf_inj : Function.Injective (β.toAddMonoidHom.toZModLinearMap 2) := by
      intro p q h
      exact β.injective (by simpa using h)
    calc Nat.card ↥V = Nat.card ↥(U.map (β.toAddMonoidHom.toZModLinearMap 2)) :=
          (Nat.card_congr (Submodule.equivMapOfInjective (hermRep l hF x⁻¹) hinj
            (U.map (β.toAddMonoidHom.toZModLinearMap 2))).toEquiv).symm
      _ = Nat.card ↥U :=
          (Nat.card_congr (Submodule.equivMapOfInjective
            (β.toAddMonoidHom.toZModLinearMap 2) hf_inj U).toEquiv).symm
  have hW : Nat.card W = 2 ^ (4 * l) := by
    rw [Nat.card_congr β.toEquiv, card_hermA (s := l) hl hF]
  have hpow : 2 ^ (4 * l) = 2 ^ l * 2 ^ (3 * l) := by
    rw [← pow_add, show l + 3 * l = 4 * l by ring]
  calc Nat.card W = 2 ^ (4 * l) := hW
    _ = 2 ^ l * 2 ^ (3 * l) := hpow
    _ ≤ 2 ^ l * Nat.card ↥V := Nat.mul_le_mul_left _ h11
    _ = 2 ^ l * Nat.card U := by rw [hcardV]

end OrthModel

end CFSG.RankThree.GF2n.Tim81.Sec2

end
