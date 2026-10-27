module

public import CFSG.Quasithin.AppendixH.H14.H142Card
public import CFSG.Quasithin.AppendixH.H14.H142HData
public import CFSG.Quasithin.AppendixH.H14.H142Group

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Open
open scoped Pointwise

@[expose] def stdMH : Subgroup S24 := M23g 8 ⊓ MulAction.stabilizer S24 stdH

@[expose] noncomputable def stdEH : Subgroup S24 := tabSub hTabArr hTab_ok

theorem card_stdEH : Nat.card ↥stdEH = 16 := card_tabSub hTab_ok

theorem isElemAbelian_stdEH : IsElemAbelian 2 stdEH := isElemAbelian_tabSub hTab_ok

theorem isPGroup_stdEH : IsPGroup 2 stdEH := isPGroup_tabSub hTab_ok

theorem stdEH_ne_bot : stdEH ≠ ⊥ := tabSub_ne_bot hTab_ok

theorem mem_stdH_iff (x : Fin 24) : x ∈ stdH ↔ (x : ℕ) ∈ hPts := by decide +revert

theorem mem_stdH_11 : (11 : Fin 24) ∈ stdH := by decide

theorem mem_stdH_14 : (14 : Fin 24) ∈ stdH := by decide

theorem mem_stdH_18 : (18 : Fin 24) ∈ stdH := by decide

theorem stab_smul (g : ↥stdMH) : (g : S24) • stdH = stdH :=
  MulAction.mem_stabilizer_iff.mp g.2.2

theorem mem_smul_stdH_iff (g : S24) (hg : g • stdH = stdH) (x : Fin 24) :
    g x ∈ stdH ↔ x ∈ stdH := by
  have h' : g⁻¹ • stdH = stdH := by
    conv_lhs => rw [← hg]
    rw [← mul_smul, inv_mul_cancel, one_smul]
  rw [← Equiv.Perm.smul_def g x]
  have hiff := Finset.inv_smul_mem_iff (a := g⁻¹) (s := stdH) (b := x)
  rw [inv_inv] at hiff
  rw [hiff, h']

theorem tabPerm_mem_M23g (n : ℕ) (hn : n < 16) : tabPerm hTabArr n ∈ M23g 8 :=
  mem_M23g_of_arr (hasArr_tabPerm hTab_ok hn) ((tabOK_spec hTab_ok).2 n hn).1 8
    (hTab_fix n hn).1

theorem tabPerm_smul_stdH (n : ℕ) (hn : n < 16) : tabPerm hTabArr n • stdH = stdH :=
  smul_stdH_of_arr (hasArr_tabPerm hTab_ok hn) (hTab_fix n hn).1 (hTab_mask n hn)

theorem stdEH_le_stdMH : stdEH ≤ stdMH := by
  intro x hx
  obtain ⟨n, hn, hxeq⟩ := (mem_tabSub hTab_ok).mp hx
  rw [hxeq, stdMH, Subgroup.mem_inf]
  exact ⟨tabPerm_mem_M23g n hn, (MulAction.mem_stabilizer_iff).2 (tabPerm_smul_stdH n hn)⟩

theorem pow_stab (g : ↥stdMH) (n : ℕ) : ((g : S24) ^ n) • stdH = stdH := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, stab_smul g, ih]

theorem pow_mem_stdH (g : ↥stdMH) (n : ℕ) (x : Fin 24) (hx : x ∈ stdH) :
    ((g : S24) ^ n) x ∈ stdH :=
  (mem_smul_stdH_iff ((g : S24) ^ n) (pow_stab g n) x).mpr hx

noncomputable def rhoSub : ↥stdMH →* Equiv.Perm ↥stdH where
  toFun g := Equiv.Perm.subtypePerm (g : S24) (mem_smul_stdH_iff (g : S24) (stab_smul g))
  map_one' := by
    apply Equiv.ext
    intro x
    exact Subtype.ext rfl
  map_mul' g h := by
    apply Equiv.ext
    intro x
    exact Subtype.ext rfl

noncomputable def heptadEquiv : ↥stdH ≃ Fin 7 :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; decide)

noncomputable def rhoH : ↥stdMH →* Equiv.Perm (Fin 7) :=
  heptadEquiv.permCongrHom.toMonoidHom.comp rhoSub

theorem rhoH_apply_e (g : ↥stdMH) (x : Fin 24) (hx : x ∈ stdH) (hx' : (g : S24) x ∈ stdH) :
    rhoH g (heptadEquiv ⟨x, hx⟩) = heptadEquiv ⟨(g : S24) x, hx'⟩ := by
  change heptadEquiv.permCongr (rhoSub g) (heptadEquiv ⟨x, hx⟩) =
    heptadEquiv ⟨(g : S24) x, hx'⟩
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact congrArg heptadEquiv (Subtype.ext rfl)

theorem rhoH_pow_apply_e (g : ↥stdMH) (n : ℕ) (x : Fin 24) (hx : x ∈ stdH) :
    ((rhoH g) ^ n) (heptadEquiv ⟨x, hx⟩) =
      heptadEquiv ⟨((g : S24) ^ n) x, pow_mem_stdH g n x hx⟩ := by
  have h1 : (rhoH g) ^ n = heptadEquiv.permCongr ((rhoSub g) ^ n) := by
    change (heptadEquiv.permCongrHom.toMonoidHom (rhoSub g)) ^ n =
      heptadEquiv.permCongr ((rhoSub g) ^ n)
    rw [← map_pow (heptadEquiv.permCongrHom.toMonoidHom) (rhoSub g) n]
    rfl
  rw [h1, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact congrArg heptadEquiv (Subtype.ext
    (Equiv.Perm.subtypePerm_apply_pow_of_mem (g := (g : S24)) (s := stdH)
      (mem_smul_stdH_iff (g : S24) (stab_smul g)) (n := n) hx))

theorem hasArr_pow_apply {σ : S24} {a : Array ℕ} (h : HasArr σ a) (j : ℕ) (x : Fin 24) :
    (((σ ^ j) x : Fin 24) : ℕ) = iterArr a j (x : ℕ) := by
  induction j with
  | zero => simp [iterArr]
  | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, h ((σ ^ j) x), ih]
      change a[iterArr a j (x : ℕ)]! = (fun y => a[y]!)^[j.succ] (x : ℕ)
      rw [Function.iterate_succ_apply']
      rfl

theorem hGens_mem : ∀ a ∈ hGens, inAutOK a = true ∧ ∃ σ ∈ stdMH, HasArr σ a := by
  intro a ha
  obtain ⟨haut, h8, hperm⟩ := hGens_ok a ha
  refine ⟨haut, ?_⟩
  refine ⟨permOfArrD a, ?_, hasArr_permOfArrD haut⟩
  rw [stdMH, Subgroup.mem_inf]
  exact ⟨mem_M23g_of_arr (hasArr_permOfArrD haut) haut 8 h8,
    (MulAction.mem_stabilizer_iff).2 (smul_stdH_of_arr (hasArr_permOfArrD haut) h8 hperm)⟩

theorem hGens_permOfArrD_mem {a : Array ℕ} (ha : a ∈ hGens) : permOfArrD a ∈ stdMH := by
  obtain ⟨haut, σ, hσM, hσarr⟩ := hGens_mem a ha
  rw [hasArr_unique (hasArr_permOfArrD haut) hσarr]
  exact hσM

noncomputable def c7 : ↥stdMH :=
  ⟨permOfArrD hGens[0]!, hGens_permOfArrD_mem (by decide)⟩

noncomputable def h3 : ↥stdMH :=
  ⟨permOfArrD hGens[1]!, hGens_permOfArrD_mem (by decide)⟩

theorem hasArr_c7 : HasArr (c7 : S24) hGens[0]! :=
  hasArr_permOfArrD (hGens_ok hGens[0]! (by decide)).1

theorem hasArr_h3 : HasArr (h3 : S24) hGens[1]! :=
  hasArr_permOfArrD (hGens_ok hGens[1]! (by decide)).1

theorem rhoH_c7_orbit (y : Fin 7) :
    ∃ j : ℕ, ((rhoH c7) ^ j) (heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩) = y := by
  obtain ⟨z, rfl⟩ := heptadEquiv.surjective y
  obtain ⟨j, -, hj⟩ := hGens_cycle ((z : Fin 24) : ℕ) ((mem_stdH_iff (z : Fin 24)).mp z.2)
  refine ⟨j, ?_⟩
  have hpow : ((c7 : S24) ^ j) (11 : Fin 24) = (z : Fin 24) := by
    apply Fin.ext
    show ((((c7 : S24) ^ j) (11 : Fin 24) : Fin 24) : ℕ) = (z : ℕ)
    rw [hasArr_pow_apply hasArr_c7 j (11 : Fin 24)]
    simpa using hj
  rw [rhoH_pow_apply_e c7 j (11 : Fin 24) mem_stdH_11]
  exact congrArg heptadEquiv (Subtype.ext hpow)

theorem rhoH_pretransitive : MulAction.IsPretransitive (↥rhoH.range) (Fin 7) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨jx, hjx⟩ := rhoH_c7_orbit x
  obtain ⟨jy, hjy⟩ := rhoH_c7_orbit y
  refine ⟨⟨((rhoH c7) ^ jy) * (((rhoH c7) ^ jx)⁻¹), ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _
      (rhoH.range.pow_mem (MonoidHom.mem_range.mpr ⟨c7, rfl⟩) jy)
      (Subgroup.inv_mem _ (rhoH.range.pow_mem (MonoidHom.mem_range.mpr ⟨c7, rfl⟩) jx))
  · show ((((rhoH c7) ^ jy) * (((rhoH c7) ^ jx)⁻¹) : Equiv.Perm (Fin 7))) x = y
    have hinv : ((rhoH c7) ^ jx)⁻¹
        (((rhoH c7) ^ jx) (heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩)) =
        heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩ := Equiv.symm_apply_apply _ _
    rw [Equiv.Perm.mul_apply, ← hjx, hinv, hjy]

theorem rhoH_isPreprimitive : MulAction.IsPreprimitive (↥rhoH.range) (Fin 7) := by
  haveI := rhoH_pretransitive
  exact MulAction.IsPreprimitive.of_prime_card (by simpa using Nat.prime_seven)

theorem rhoH_h3_fix (x : Fin 24) (hx : x ∈ stdH) (h11 : x ≠ (11 : Fin 24))
    (h14 : x ≠ (14 : Fin 24)) (h18 : x ≠ (18 : Fin 24)) : (h3 : S24) x = x := by
  have hmem : (x : ℕ) ∈ hPts := (mem_stdH_iff x).mp hx
  simp only [hPts, List.mem_cons, List.not_mem_nil, or_false] at hmem
  apply Fin.ext
  show (((h3 : S24) x : Fin 24) : ℕ) = (x : ℕ)
  rw [hasArr_h3 x]
  rcases hmem with h | h | h | h | h | h | h
  · exact absurd (Fin.ext h) h11
  · rw [h]; exact hGens_three.2.2.2.1
  · exact absurd (Fin.ext h) h14
  · rw [h]; exact hGens_three.2.2.2.2.1
  · exact absurd (Fin.ext h) h18
  · rw [h]; exact hGens_three.2.2.2.2.2.1
  · rw [h]; exact hGens_three.2.2.2.2.2.2

theorem rhoH_h3_isThreeCycle : Equiv.Perm.IsThreeCycle (rhoH h3) := by
  have he11 : rhoH h3 (heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩) =
      heptadEquiv ⟨(14 : Fin 24), mem_stdH_14⟩ := by
    have h : (h3 : S24) (11 : Fin 24) = (14 : Fin 24) := by
      have hidx : ((11 : Fin 24) : ℕ) = 11 := by decide
      apply Fin.ext
      show (((h3 : S24) (11 : Fin 24) : Fin 24) : ℕ) = (14 : ℕ)
      rw [hasArr_h3 (11 : Fin 24), hidx]
      exact hGens_three.1
    rw [rhoH_apply_e h3 (11 : Fin 24) mem_stdH_11 (by rw [h]; exact mem_stdH_14)]
    exact congrArg heptadEquiv (Subtype.ext h)
  have he14 : rhoH h3 (heptadEquiv ⟨(14 : Fin 24), mem_stdH_14⟩) =
      heptadEquiv ⟨(18 : Fin 24), mem_stdH_18⟩ := by
    have h : (h3 : S24) (14 : Fin 24) = (18 : Fin 24) := by
      have hidx : ((14 : Fin 24) : ℕ) = 14 := by decide
      apply Fin.ext
      show (((h3 : S24) (14 : Fin 24) : Fin 24) : ℕ) = (18 : ℕ)
      rw [hasArr_h3 (14 : Fin 24), hidx]
      exact hGens_three.2.1
    rw [rhoH_apply_e h3 (14 : Fin 24) mem_stdH_14 (by rw [h]; exact mem_stdH_18)]
    exact congrArg heptadEquiv (Subtype.ext h)
  have he18 : rhoH h3 (heptadEquiv ⟨(18 : Fin 24), mem_stdH_18⟩) =
      heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩ := by
    have h : (h3 : S24) (18 : Fin 24) = (11 : Fin 24) := by
      have hidx : ((18 : Fin 24) : ℕ) = 18 := by decide
      apply Fin.ext
      show (((h3 : S24) (18 : Fin 24) : Fin 24) : ℕ) = (11 : ℕ)
      rw [hasArr_h3 (18 : Fin 24), hidx]
      exact hGens_three.2.2.1
    rw [rhoH_apply_e h3 (18 : Fin 24) mem_stdH_18 (by rw [h]; exact mem_stdH_11)]
    exact congrArg heptadEquiv (Subtype.ext h)
  have hfix : ∀ x : Fin 7, x ∉ ({heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩,
      heptadEquiv ⟨(14 : Fin 24), mem_stdH_14⟩,
      heptadEquiv ⟨(18 : Fin 24), mem_stdH_18⟩} : Finset (Fin 7)) → rhoH h3 x = x := by
    intro x hx
    obtain ⟨z, rfl⟩ := heptadEquiv.surjective x
    have hz11 : (z : Fin 24) ≠ (11 : Fin 24) := by
      intro hz
      apply hx
      rw [show (heptadEquiv z : Fin 7) = heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩ from
        congrArg heptadEquiv (Subtype.ext hz)]
      exact Finset.mem_insert_self _ _
    have hz14 : (z : Fin 24) ≠ (14 : Fin 24) := by
      intro hz
      apply hx
      rw [show (heptadEquiv z : Fin 7) = heptadEquiv ⟨(14 : Fin 24), mem_stdH_14⟩ from
        congrArg heptadEquiv (Subtype.ext hz)]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hz18 : (z : Fin 24) ≠ (18 : Fin 24) := by
      intro hz
      apply hx
      rw [show (heptadEquiv z : Fin 7) = heptadEquiv ⟨(18 : Fin 24), mem_stdH_18⟩ from
        congrArg heptadEquiv (Subtype.ext hz)]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hzfix : (h3 : S24) (z : Fin 24) = (z : Fin 24) :=
      rhoH_h3_fix (z : Fin 24) z.2 hz11 hz14 hz18
    rw [rhoH_apply_e h3 (z : Fin 24) z.2 (by rw [hzfix]; exact z.2)]
    exact congrArg heptadEquiv (Subtype.ext hzfix)
  have hsupp : (rhoH h3).support = {heptadEquiv ⟨(11 : Fin 24), mem_stdH_11⟩,
      heptadEquiv ⟨(14 : Fin 24), mem_stdH_14⟩,
      heptadEquiv ⟨(18 : Fin 24), mem_stdH_18⟩} := by
    ext x
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hxne
      by_contra hxnot
      exact hxne (hfix x hxnot)
    · intro hxmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
      rcases hxmem with h | h | h
      · rw [h, he11]
        exact fun hh => (by decide : (14 : Fin 24) ≠ (11 : Fin 24))
          (congrArg Subtype.val (heptadEquiv.injective hh))
      · rw [h, he14]
        exact fun hh => (by decide : (18 : Fin 24) ≠ (14 : Fin 24))
          (congrArg Subtype.val (heptadEquiv.injective hh))
      · rw [h, he18]
        exact fun hh => (by decide : (11 : Fin 24) ≠ (18 : Fin 24))
          (congrArg Subtype.val (heptadEquiv.injective hh))
  rw [← card_support_eq_three_iff, hsupp]
  refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · intro hh
    exact (by decide : (11 : Fin 24) ≠ (14 : Fin 24))
      (congrArg Subtype.val (heptadEquiv.injective hh))
  · intro hh
    exact (by decide : (11 : Fin 24) ≠ (18 : Fin 24))
      (congrArg Subtype.val (heptadEquiv.injective hh))
  · intro hh
    exact (by decide : (14 : Fin 24) ≠ (18 : Fin 24))
      (congrArg Subtype.val (heptadEquiv.injective hh))

theorem alternatingGroup_le_rhoH_range : alternatingGroup (Fin 7) ≤ rhoH.range :=
  Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem (G := rhoH.range)
    rhoH_isPreprimitive rhoH_h3_isThreeCycle (MonoidHom.mem_range.mpr ⟨h3, rfl⟩)

theorem hE_le_rhoH_ker : stdEH.subgroupOf stdMH ≤ rhoH.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  obtain ⟨n, hn, hxeq⟩ := (mem_tabSub hTab_ok).mp ((Subgroup.mem_subgroupOf).mp hx)
  have hfix : ∀ y ∈ stdH, (x : S24) y = y := by
    intro y hy
    apply Fin.ext
    show (((x : S24) y : Fin 24) : ℕ) = (y : ℕ)
    rw [hxeq]
    exact (hasArr_tabPerm hTab_ok hn y).trans
      ((hTab_fix n hn).2 (y : ℕ) ((mem_stdH_iff y).mp hy))
  have h1 : rhoSub x = 1 := by
    apply Equiv.ext
    intro y
    exact Subtype.ext (hfix (y : Fin 24) y.2)
  change (heptadEquiv.permCongrHom.toMonoidHom.comp rhoSub) x = 1
  rw [MonoidHom.comp_apply, h1, map_one]

theorem card_alt7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem card_rhoH_range_le : Nat.card ↥rhoH.range ≤ 2520 := by
  have hker16 : 16 ≤ Nat.card ↥rhoH.ker := by
    have hle := Subgroup.card_le_of_le hE_le_rhoH_ker
    have hcard : Nat.card ↥(stdEH.subgroupOf stdMH) = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe stdEH_le_stdMH).toEquiv, card_stdEH]
    rwa [hcard] at hle
  have h := Subgroup.card_ker_mul_card_range rhoH
  have hG : Nat.card ↥stdMH ≤ 40320 := card_MH_le
  have hmain : 16 * Nat.card ↥rhoH.range ≤ 40320 :=
    calc 16 * Nat.card ↥rhoH.range ≤ Nat.card ↥rhoH.ker * Nat.card ↥rhoH.range :=
          Nat.mul_le_mul_right _ hker16
      _ = Nat.card ↥stdMH := h
      _ ≤ 40320 := hG
  rw [show (40320 : ℕ) = 16 * 2520 by norm_num] at hmain
  exact Nat.le_of_mul_le_mul_left hmain (by norm_num)

theorem rhoH_range_eq : rhoH.range = alternatingGroup (Fin 7) := by
  have hle := alternatingGroup_le_rhoH_range
  have hcle := card_rhoH_range_le
  exact (Subgroup.eq_of_le_of_card_ge (H := alternatingGroup (Fin 7)) (K := rhoH.range) hle
    (by rw [card_alt7]; exact hcle)).symm

theorem rhoH_ker_eq : rhoH.ker = stdEH.subgroupOf stdMH := by
  have hcardE : Nat.card ↥(stdEH.subgroupOf stdMH) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe stdEH_le_stdMH).toEquiv, card_stdEH]
  have hcardK : Nat.card ↥rhoH.ker ≤ 16 := by
    have h := Subgroup.card_ker_mul_card_range rhoH
    have hG : Nat.card ↥stdMH ≤ 40320 := card_MH_le
    have hmain : Nat.card ↥rhoH.ker * 2520 ≤ 16 * 2520 :=
      calc Nat.card ↥rhoH.ker * 2520 = Nat.card ↥rhoH.ker * Nat.card ↥rhoH.range := by
            rw [rhoH_range_eq, card_alt7]
        _ = Nat.card ↥stdMH := h
        _ ≤ 40320 := hG
        _ = 16 * 2520 := by norm_num
    exact Nat.le_of_mul_le_mul_right hmain (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hE_le_rhoH_ker (by rw [hcardE]; exact hcardK)).symm

theorem exists_surj_alt7 :
    ∃ π : ↥stdMH →* ↥(alternatingGroup (Fin 7)), Function.Surjective π ∧
      π.ker = stdEH.subgroupOf stdMH := by
  let π : ↥stdMH →* ↥(alternatingGroup (Fin 7)) :=
    rhoH.codRestrict (alternatingGroup (Fin 7)) fun g => by
      rw [← rhoH_range_eq]
      exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  refine ⟨π, ?_, ?_⟩
  · intro y
    have hy : (y : Equiv.Perm (Fin 7)) ∈ rhoH.range := by
      rw [rhoH_range_eq]
      exact y.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hy
    exact ⟨g, Subtype.ext hg⟩
  · have hker : π.ker = rhoH.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hker, rhoH_ker_eq]

theorem stdEH_normal : ∀ g ∈ stdMH, ∀ e ∈ stdEH, g * e * g⁻¹ ∈ stdEH := by
  intro g hg e he
  have hnorm : rhoH.ker.Normal := inferInstance
  have he' : (⟨e, stdEH_le_stdMH he⟩ : ↥stdMH) ∈ rhoH.ker := by
    rw [rhoH_ker_eq, Subgroup.mem_subgroupOf]
    exact he
  have hconj := hnorm.conj_mem (⟨e, stdEH_le_stdMH he⟩ : ↥stdMH) he' (⟨g, hg⟩ : ↥stdMH)
  rw [rhoH_ker_eq, Subgroup.mem_subgroupOf] at hconj
  simpa using hconj

theorem stdEH_selfCentralizing :
    ∀ g ∈ stdMH, (∀ e ∈ stdEH, g * e = e * g) → g ∈ stdEH := by
  intro g hg hcomm
  obtain ⟨π, hsurj, hker⟩ := exists_surj_alt7
  let C : Subgroup ↥stdMH :=
    (stdMH ⊓ Subgroup.centralizer (stdEH : Set S24)).subgroupOf stdMH
  have hCmem : ∀ x : ↥stdMH, x ∈ C ↔ (x : S24) ∈ Subgroup.centralizer (stdEH : Set S24) := by
    intro x
    simp only [C, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hCnormal : C.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hCmem] at hn ⊢
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro e he
    have he' : (g : S24)⁻¹ * e * (g : S24) ∈ stdEH :=
      stdEH_normal ((g : S24)⁻¹) (Subgroup.inv_mem _ g.2) e he
    have hcomm' : ((g : S24)⁻¹ * e * (g : S24)) * (n : S24) =
        (n : S24) * ((g : S24)⁻¹ * e * (g : S24)) := hn _ he'
    calc e * (↑(g * n * g⁻¹) : S24)
        = (g : S24) * (((g : S24)⁻¹ * e * (g : S24)) * (n : S24)) * (g : S24)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (g : S24) * ((n : S24) * ((g : S24)⁻¹ * e * (g : S24))) * (g : S24)⁻¹ := by
          rw [hcomm']
      _ = (↑(g * n * g⁻¹) : S24) * e := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  haveI : (C.map π).Normal := hCnormal.map π hsurj
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hxmem : (⟨g, hg⟩ : ↥stdMH) ∈ C := by
    rw [hCmem, Subgroup.mem_centralizer_iff]
    exact fun e he => (hcomm e he).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map π) with hbot | htop
  · have hmem : π (⟨g, hg⟩ : ↥stdMH) ∈ C.map π := ⟨⟨g, hg⟩, hxmem, rfl⟩
    rw [hbot] at hmem
    have h1 : π (⟨g, hg⟩ : ↥stdMH) = 1 := by simpa using hmem
    have hgker : (⟨g, hg⟩ : ↥stdMH) ∈ π.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hgker
    exact Subgroup.mem_subgroupOf.mp hgker
  · exfalso
    have hc7mem : π c7 ∈ C.map π := by rw [htop]; trivial
    obtain ⟨x, hxC, hxπ⟩ := Subgroup.mem_map.mp hc7mem
    have hk : x⁻¹ * c7 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxπ, inv_mul_cancel]
    rw [hker] at hk
    have hkE : ((x⁻¹ * c7 : ↥stdMH) : S24) ∈ stdEH := Subgroup.mem_subgroupOf.mp hk
    have hxC' : (x : S24) ∈ Subgroup.centralizer (stdEH : Set S24) := (hCmem x).mp hxC
    rw [Subgroup.mem_centralizer_iff] at hxC'
    have hpsi2 : tabPerm hTabArr 2 ∈ stdEH := tabPerm_mem_tabSub hTab_ok (by norm_num)
    have hkcomm : ((x⁻¹ * c7 : ↥stdMH) : S24) * tabPerm hTabArr 2 =
        tabPerm hTabArr 2 * ((x⁻¹ * c7 : ↥stdMH) : S24) :=
      ((isElemAbelian_two_iff stdEH).mp isElemAbelian_stdEH).1 _ hkE _ hpsi2
    have hxcomm : (x : S24) * tabPerm hTabArr 2 = tabPerm hTabArr 2 * (x : S24) :=
      (hxC' _ hpsi2).symm
    have hxk : (c7 : S24) = (x : S24) * ((x⁻¹ * c7 : ↥stdMH) : S24) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hc7comm : (c7 : S24) * tabPerm hTabArr 2 = tabPerm hTabArr 2 * (c7 : S24) := by
      rw [hxk]
      calc (x : S24) * ((x⁻¹ * c7 : ↥stdMH) : S24) * tabPerm hTabArr 2
          = (x : S24) * (((x⁻¹ * c7 : ↥stdMH) : S24) * tabPerm hTabArr 2) := by group
        _ = (x : S24) * (tabPerm hTabArr 2 * ((x⁻¹ * c7 : ↥stdMH) : S24)) := by rw [hkcomm]
        _ = (x : S24) * tabPerm hTabArr 2 * ((x⁻¹ * c7 : ↥stdMH) : S24) := by group
        _ = tabPerm hTabArr 2 * (x : S24) * ((x⁻¹ * c7 : ↥stdMH) : S24) := by rw [hxcomm]
        _ = tabPerm hTabArr 2 * ((x : S24) * ((x⁻¹ * c7 : ↥stdMH) : S24)) := by group
    have hconjval := conj_tabPerm hTab_ok hasArr_c7 (hGens_ok hGens[0]! (by decide)).1
      (by norm_num : 2 < 16) hGens_noncomm.1
    have hne : (c7 : S24) * tabPerm hTabArr 2 * (c7 : S24)⁻¹ ≠ tabPerm hTabArr 2 := by
      rw [hconjval]
      intro hh
      exact hGens_noncomm.2
        (tabPerm_inj hTab_ok hGens_noncomm.1 (by norm_num : 2 < 16) hh)
    apply hne
    rw [hc7comm]
    group

theorem stdEH_irreducible : ∀ W : Subgroup S24, W ≤ stdEH → W ≠ ⊥ →
    (∀ g ∈ stdMH, W.map (MulAut.conj g).toMonoidHom = W) → W = stdEH := by
  intro W hW hWne hWin
  refine irreducible_of_orbit hTab_ok stdEH_le_stdMH ?_ W hW hWne hWin
  intro n hn0 hn16
  obtain ⟨e, he, he1⟩ := hVbfs_cover n hn16 hn0
  obtain ⟨k, hk, hk_eq⟩ := List.mem_iff_getElem.mp he
  have hget : hVbfs.getD k (0, 0, 0) = e := by
    rw [List.getD_eq_getElem hVbfs (0, 0, 0) hk, hk_eq]
  obtain ⟨-, g, hgM, hgconj⟩ := exists_conj_of_vbfs hTab_ok hGens_mem hVbfs_ok k hk
  rw [hget, he1] at hgconj
  exact ⟨g, hgM, hgconj⟩

theorem pCoreOf_stdMH : pCoreOf 2 stdMH = stdEH :=
  pCoreOf_eq_of_selfCentralizing_irreducible (M := stdMH) (E := stdEH) stdEH_le_stdMH
    stdEH_normal isPGroup_stdEH stdEH_ne_bot stdEH_selfCentralizing stdEH_irreducible

end CFSG.Quasithin.AppendixH.H14
