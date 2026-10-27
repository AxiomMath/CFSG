module

public import CFSG.RankThree.Native.ONTripleSigBase
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup Equiv
open CFSG.RankThree.PartTwo

attribute [local irreducible] dotProduct

@[expose] def inL (j : ℕ) (v : Fin 4 → ZMod 3) : Prop :=
  v 3 = 0 ∧ (if j = 0 then v 2 = 0 else v 1 = v 2)

instance (j : ℕ) : DecidablePred (inL j) := fun v => by unfold inL; infer_instance

theorem inL_zero (j : ℕ) : inL j 0 := by
  unfold inL
  split_ifs <;> simp

theorem inL_add {j : ℕ} {u v : Fin 4 → ZMod 3} (hu : inL j u) (hv : inL j v) :
    inL j (u + v) := by
  unfold inL at *
  split_ifs at * with h
  · exact ⟨by simp [hu.1, hv.1], by simp [hu.2, hv.2]⟩
  · exact ⟨by simp [hu.1, hv.1], by simp [hu.2, hv.2]⟩

theorem inL_neg {j : ℕ} {u : Fin 4 → ZMod 3} (hu : inL j u) : inL j (-u) := by
  unfold inL at *
  split_ifs at * with h
  · exact ⟨by rw [Pi.neg_apply, hu.1]; decide, by rw [Pi.neg_apply, hu.2]; decide⟩
  · exact ⟨by rw [Pi.neg_apply, hu.1]; decide, by rw [Pi.neg_apply, Pi.neg_apply, hu.2]⟩

@[expose] def LSub (j : ℕ) : Subgroup (Multiplicative (Fin 4 → ZMod 3)) where
  carrier := {v | inL j (Multiplicative.toAdd v)}
  one_mem' := inL_zero j
  mul_mem' := fun ha hb => inL_add ha hb
  inv_mem' := fun ha => inL_neg ha

@[expose] def AG (j : ℕ) : Subgroup GM := ((LSub j).comap relG.coordHom).map P0G.subtype

theorem mem_AG {j : ℕ} {g : GM} : g ∈ AG j ↔ ∃ h : g ∈ P0G, inL j (relG.coord ⟨g, h⟩) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem AG_le_P0 (j : ℕ) : AG j ≤ P0G := fun _ hg => (mem_AG.1 hg).1

theorem coord_xG0 : relG.coord ⟨xG 0, ThreeQRel.v_mem 0⟩ = Pi.single 0 1 := by
  have e : (⟨xG 0, ThreeQRel.v_mem 0⟩ : P0G) = ⟨threeNF zG xG 0 (Pi.single 0 1),
      ThreeQRel.nf_mem _ _⟩ := Subtype.ext (xG_eq_nf 0)
  rw [e, relG.coord_nf]

theorem coord_xG (i : Fin 4) : relG.coord ⟨xG i, ThreeQRel.v_mem i⟩ = Pi.single i 1 := by
  have e : (⟨xG i, ThreeQRel.v_mem i⟩ : P0G) = ⟨threeNF zG xG 0 (Pi.single i 1),
      ThreeQRel.nf_mem _ _⟩ := Subtype.ext (xG_eq_nf i)
  rw [e, relG.coord_nf]

theorem coord_zG : relG.coord ⟨zG, ThreeQRel.x_mem⟩ = 0 :=
  (relG.coord_eq_zero_iff _).2 (mem_zpowers zG)

theorem coord_mul' {g h : GM} (hg : g ∈ P0G) (hh : h ∈ P0G) :
    relG.coord ⟨g * h, mul_mem hg hh⟩ = relG.coord ⟨g, hg⟩ + relG.coord ⟨h, hh⟩ :=
  relG.coord_mul ⟨g, hg⟩ ⟨h, hh⟩

theorem coord_pow' {g : GM} (hg : g ∈ P0G) (n : ℕ) :
    relG.coord ⟨g ^ n, pow_mem hg n⟩ = n • relG.coord ⟨g, hg⟩ := by
  have e : (⟨g ^ n, pow_mem hg n⟩ : P0G) = (⟨g, hg⟩ : P0G) ^ n := Subtype.ext (by simp)
  have h := congrArg Multiplicative.toAdd (map_pow relG.coordHom ⟨g, hg⟩ n)
  rw [toAdd_pow] at h
  rw [e]
  exact h

theorem yG_mem_P0 {j : ℕ} (hj : j < 2) : yG j ∈ P0G := by
  interval_cases j
  · rw [yG_zero]; exact ThreeQRel.v_mem 1
  · rw [yG_one]; exact mul_mem (ThreeQRel.v_mem 1) (ThreeQRel.v_mem 2)

@[expose] def yv (j : ℕ) : Fin 4 → ZMod 3 := if j = 0 then Pi.single 1 1 else Pi.single 1 1 +
  Pi.single 2 1

theorem coord_yG {j : ℕ} (hj : j < 2) : relG.coord ⟨yG j, yG_mem_P0 hj⟩ = yv j := by
  interval_cases j
  · have e : (⟨yG 0, yG_mem_P0 (by norm_num)⟩ : P0G) = ⟨xG 1, ThreeQRel.v_mem 1⟩ := rfl
    rw [e, coord_xG]
    rfl
  · have e : (⟨yG 1, yG_mem_P0 (by norm_num)⟩ : P0G) = ⟨xG 1 * xG 2,
        mul_mem (ThreeQRel.v_mem 1) (ThreeQRel.v_mem 2)⟩ := Subtype.ext yG_one
    rw [e, coord_mul' (ThreeQRel.v_mem 1) (ThreeQRel.v_mem 2), coord_xG, coord_xG]
    rfl

theorem zG_mem_AG (j : ℕ) : zG ∈ AG j :=
  mem_AG.2 ⟨ThreeQRel.x_mem, by rw [coord_zG]; exact inL_zero j⟩

theorem xG0_mem_AG (j : ℕ) : xG 0 ∈ AG j :=
  mem_AG.2 ⟨ThreeQRel.v_mem 0, by rw [coord_xG0]; unfold inL; split_ifs <;> decide⟩

theorem yG_mem_AG {j : ℕ} (hj : j < 2) : yG j ∈ AG j :=
  mem_AG.2 ⟨yG_mem_P0 hj, by rw [coord_yG hj]; interval_cases j <;> decide⟩

theorem inL_isotropic : ∀ j < 2, ∀ u : Fin 4 → ZMod 3, inL j u → ∀ v : Fin 4 → ZMod 3,
    inL j v → ThreeQRel.threePair omegaZ u v = 0 := by
  decide +kernel

theorem AG_comm {j : ℕ} (hj : j < 2) {a b : GM} (ha : a ∈ AG j) (hb : b ∈ AG j) :
    a * b = b * a := by
  obtain ⟨ha', hla⟩ := mem_AG.1 ha
  obtain ⟨hb', hlb⟩ := mem_AG.1 hb
  have := (relG.commute_iff ⟨a, ha'⟩ ⟨b, hb'⟩).2 (inL_isotropic j hj _ hla _ hlb)
  exact congrArg Subtype.val this

@[expose] def uL (j l : ℕ) : Fin 4 → ZMod 3 := vecWord (lw j l) (Pi.single 0 1)

@[expose] def mL (j l : ℕ) : GM := (nL j l)⁻¹ * xG 0 * nL j l

theorem inL_vecWord : ∀ j < 2, ∀ l < 4, ∀ v : Fin 4 → ZMod 3, inL j v →
    inL j (vecWord (lw j l) v) := by
  decide +kernel

theorem conj_mem_AG {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) {g : GM} (hg : g ∈ AG j) :
    (nL j l)⁻¹ * g * nL j l ∈ AG j := by
  obtain ⟨hg', hl'⟩ := mem_AG.1 hg
  refine mem_AG.2 ⟨conjW_mem _ (lw_lt hj hl) hg', ?_⟩
  rw [coord_conjW (lw j l) (lw_lt hj hl) hg']
  exact inL_vecWord j hj l hl _ hl'

theorem mL_mem_P0 {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) : mL j l ∈ P0G :=
  conjW_mem _ (lw_lt hj hl) (ThreeQRel.v_mem 0)

theorem coord_mL {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) :
    relG.coord ⟨mL j l, mL_mem_P0 hj hl⟩ = uL j l := by
  have := coord_conjW (lw j l) (lw_lt hj hl) (ThreeQRel.v_mem 0)
  rw [coord_xG0] at this
  exact this

theorem mL_mem_AG {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) : mL j l ∈ AG j :=
  conj_mem_AG hj hl (xG0_mem_AG j)

theorem map_conj_AG {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) :
    (AG j).map (MulAut.conj (nL j l)⁻¹).toMonoidHom = AG j := by
  have hle : (AG j).map (MulAut.conj (nL j l)⁻¹).toMonoidHom ≤ AG j := by
    rintro _ ⟨g, hg, rfl⟩
    have := conj_mem_AG hj hl hg
    simpa [MulAut.conj_apply] using this
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective (MulAut.conj (nL j l)⁻¹).injective]

theorem conj_mem_AG' {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) {g : GM} (hg : g ∈ AG j) :
    nL j l * g * (nL j l)⁻¹ ∈ AG j := by
  rw [← map_conj_AG hj hl] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  simpa [MulAut.conj_apply, mul_assoc] using hh

theorem cube_of_mem_P0 {g : GM} (hg : g ∈ P0G) : g ^ 3 = 1 := by
  have := Monoid.pow_exponent_eq_one (⟨g, hg⟩ : P0G)
  rw [relG.exponent_threeQ] at this
  exact congrArg Subtype.val this

theorem eq_mul_zpow_of_coord {g h : GM} (hg : g ∈ P0G) (hh : h ∈ P0G)
    (he : relG.coord ⟨g, hg⟩ = relG.coord ⟨h, hh⟩) : ∃ c : ℕ, g = h * zG ^ c := by
  have hk : (⟨h, hh⟩ : P0G)⁻¹ * ⟨g, hg⟩ ∈ relG.coordHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : relG.coordHom ⟨g, hg⟩ = relG.coordHom ⟨h, hh⟩ := congrArg Multiplicative.ofAdd he
    rw [this]
    exact inv_mul_cancel _
  rw [relG.coordHom_ker, mem_subgroupOf] at hk
  obtain ⟨c, hc⟩ := (mem_powers_iff_mem_zpowers).2 hk
  refine ⟨c, ?_⟩
  have hc' : zG ^ c = h⁻¹ * g := hc
  rw [hc', mul_inv_cancel_left]

theorem centralizer_mul_zpow (g : GM) (c : ℕ) :
    centralizer {g * zG ^ c} = centralizer {g} := by
  ext k
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have hz : Commute k (zG ^ c) := (Commute.pow_right (zG_central k).symm c)
  constructor
  · intro h
    have h' : k * g * zG ^ c = g * k * zG ^ c := by
      calc k * g * zG ^ c = k * (g * zG ^ c) := by rw [mul_assoc]
        _ = g * zG ^ c * k := h
        _ = g * (zG ^ c * k) := by rw [mul_assoc]
        _ = g * (k * zG ^ c) := by rw [hz.eq]
        _ = g * k * zG ^ c := by rw [mul_assoc]
    exact mul_right_cancel h'
  · intro h
    calc k * (g * zG ^ c) = k * g * zG ^ c := by rw [mul_assoc]
      _ = g * k * zG ^ c := by rw [h]
      _ = g * (k * zG ^ c) := by rw [mul_assoc]
      _ = g * (zG ^ c * k) := by rw [hz.eq]
      _ = g * zG ^ c * k := by rw [mul_assoc]

theorem centralizer_pow_of_cube {g : GM} (hg : g ^ 3 = 1) {s : ℕ} (hs : s % 3 ≠ 0) :
    centralizer {g ^ s} = centralizer {g} := by
  apply le_antisymm
  · intro k hk
    rw [mem_centralizer_singleton_iff] at hk ⊢
    have hc : Commute k (g ^ s) := hk
    have e : g = (g ^ s) ^ s := by
      rw [← pow_mul, ← pow_mod_three hg (s * s)]
      have : s * s % 3 = 1 := by
        have : s % 3 = 1 ∨ s % 3 = 2 := by omega
        rcases this with h | h <;> simp [Nat.mul_mod, h]
      rw [this, pow_one]
    rw [e]
    exact (hc.pow_right s).eq
  · intro k hk
    rw [mem_centralizer_singleton_iff] at hk ⊢
    have hc : Commute k g := hk
    exact (hc.pow_right s).eq

theorem centralizer_eq_of_coord {g h : GM} (hg : g ∈ P0G) (hh : h ∈ P0G) {s : ℕ}
    (hs : s % 3 ≠ 0) (he : relG.coord ⟨g, hg⟩ = s • relG.coord ⟨h, hh⟩) :
    centralizer {g} = centralizer {h} := by
  rw [← coord_pow' hh] at he
  obtain ⟨c, hc⟩ := eq_mul_zpow_of_coord hg (pow_mem hh s) he
  rw [hc, centralizer_mul_zpow, centralizer_pow_of_cube (cube_of_mem_P0 hh) hs]

theorem yG_cube {j : ℕ} (hj : j < 2) : yG j ^ 3 = 1 := cube_of_mem_P0 (yG_mem_P0 hj)

@[expose] def eHom (j : ℕ) (hj : j < 2) : Multiplicative (ZMod 3 × ZMod 3) →* GM where
  toFun p := xG 0 ^ (Multiplicative.toAdd p).1.val * yG j ^ (Multiplicative.toAdd p).2.val
  map_one' := by simp
  map_mul' p q := by
    have hc : Commute (xG 0) (yG j) := (yG_comm_x0 hj).symm
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [pow_mod_three xG0_cube, pow_mod_three (yG_cube hj), pow_add, pow_add]
    have h1 : Commute (yG j ^ (Multiplicative.toAdd p).2.val)
        (xG 0 ^ (Multiplicative.toAdd q).1.val) := (hc.symm.pow_pow _ _)
    calc xG 0 ^ (Multiplicative.toAdd p).1.val * xG 0 ^ (Multiplicative.toAdd q).1.val *
          (yG j ^ (Multiplicative.toAdd p).2.val * yG j ^ (Multiplicative.toAdd q).2.val) =
        xG 0 ^ (Multiplicative.toAdd p).1.val *
          (xG 0 ^ (Multiplicative.toAdd q).1.val * yG j ^ (Multiplicative.toAdd p).2.val) *
          yG j ^ (Multiplicative.toAdd q).2.val := by group
      _ = xG 0 ^ (Multiplicative.toAdd p).1.val *
          (yG j ^ (Multiplicative.toAdd p).2.val * xG 0 ^ (Multiplicative.toAdd q).1.val) *
          yG j ^ (Multiplicative.toAdd q).2.val := by rw [h1.eq]
      _ = _ := by group

theorem eHom_mem_P0 {j : ℕ} (hj : j < 2) (p : Multiplicative (ZMod 3 × ZMod 3)) :
    eHom j hj p ∈ P0G :=
  mul_mem (pow_mem (ThreeQRel.v_mem 0) _) (pow_mem (yG_mem_P0 hj) _)

theorem coord_eHom {j : ℕ} (hj : j < 2) (p : Multiplicative (ZMod 3 × ZMod 3)) :
    relG.coord ⟨eHom j hj p, eHom_mem_P0 hj p⟩ =
      (Multiplicative.toAdd p).1.val • Pi.single 0 1 + (Multiplicative.toAdd p).2.val • yv j := by
  have e := coord_mul' (pow_mem (ThreeQRel.v_mem 0) (Multiplicative.toAdd p).1.val)
    (pow_mem (yG_mem_P0 hj) (Multiplicative.toAdd p).2.val)
  rw [coord_pow' (ThreeQRel.v_mem 0), coord_pow' (yG_mem_P0 hj), coord_xG0, coord_yG hj] at e
  exact e

theorem eHom_coord_ne : ∀ j < 2, ∀ a b : ZMod 3, (a, b) ≠ (0, 0) →
    a.val • (Pi.single 0 1 : Fin 4 → ZMod 3) + b.val • yv j ≠ 0 := by
  decide +kernel

theorem eHom_injective {j : ℕ} (hj : j < 2) : Function.Injective (eHom j hj) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  by_contra hne
  have h0 : relG.coord ⟨eHom j hj p, eHom_mem_P0 hj p⟩ = 0 :=
    (relG.coord_eq_zero_iff _).2 (by show eHom j hj p ∈ zpowers zG; rw [hp]; exact one_mem _)
  rw [coord_eHom] at h0
  apply eHom_coord_ne j hj _ _ _ h0
  intro h
  apply hne
  have : Multiplicative.toAdd p = 0 := h
  exact this

@[expose] def EG (j : ℕ) (hj : j < 2) : Subgroup GM := (eHom j hj).range

theorem card_EG {j : ℕ} (hj : j < 2) : Nat.card (EG j hj) = 3 ^ 2 := by
  rw [EG, MonoidHom.range_eq_map, card_map_of_injective (eHom_injective hj), card_top,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
  norm_num

theorem EG_cube {j : ℕ} (hj : j < 2) (e : EG j hj) : e ^ 3 = 1 := by
  obtain ⟨_, p, rfl⟩ := e
  apply Subtype.ext
  show (eHom j hj p) ^ 3 = 1
  rw [← map_pow]
  have : p ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext
    · rw [Prod.smul_fst, Prod.fst_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    · rw [Prod.smul_snd, Prod.snd_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [this, map_one]

theorem EG_le_AG {j : ℕ} (hj : j < 2) : EG j hj ≤ AG j := by
  rintro _ ⟨p, rfl⟩
  exact mul_mem (pow_mem (xG0_mem_AG j) _) (pow_mem (yG_mem_AG hj) _)

theorem line_of_vec : ∀ j < 2, ∀ a b : ZMod 3, (a, b) ≠ (0, 0) → ∃ l < 4, ∃ s < 3, s ≠ 0 ∧
    a.val • (Pi.single 0 1 : Fin 4 → ZMod 3) + b.val • yv j = s • uL j l := by
  decide +kernel

theorem centralizer_EG {j : ℕ} (hj : j < 2) (e : EG j hj) (he : e ≠ 1) :
    ∃ l < 4, centralizer {(e : GM)} = centralizer {mL j l} := by
  obtain ⟨_, p, rfl⟩ := e
  have hp : (Multiplicative.toAdd p).1 ≠ 0 ∨ (Multiplicative.toAdd p).2 ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply Subtype.ext
    show eHom j hj p = 1
    have : p = 1 := by
      show Multiplicative.toAdd p = 0
      ext
      · exact h.1
      · exact h.2
    rw [this, map_one]
  obtain ⟨l, hl, s, hs, hs0, hv⟩ := line_of_vec j hj (Multiplicative.toAdd p).1
    (Multiplicative.toAdd p).2 (by
      intro h
      rcases hp with hp | hp
      · exact hp (congrArg Prod.fst h)
      · exact hp (congrArg Prod.snd h))
  refine ⟨l, hl, ?_⟩
  apply centralizer_eq_of_coord (eHom_mem_P0 hj p) (mL_mem_P0 hj hl) (s := s) (by omega)
  rw [coord_eHom, coord_mL hj hl]
  exact hv

theorem two_pow_of_pi {S : Subgroup GM} (hS : IsPiSubgroup (piOf 2) S) :
    ∃ k, Nat.card S = 2 ^ k :=
  ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdS => hS ⟨d, hd⟩ hdS⟩

theorem two_elem_of_pi {S : Subgroup GM} (hS : IsPiSubgroup (piOf 2) S) {g : GM} (hg : g ∈ S) :
    ∃ n, g ^ (2 ^ n) = 1 := by
  obtain ⟨k, hk⟩ := two_pow_of_pi hS
  refine ⟨k, ?_⟩
  have := pow_card_eq_one' (G := S) (x := ⟨g, hg⟩)
  rw [hk] at this
  exact congrArg Subtype.val this

theorem not_three_dvd_of_pi {S : Subgroup GM} (hS : IsPiSubgroup (piOf 2) S) :
    ¬ 3 ∣ Nat.card S := by
  intro h
  have : (3 : ℕ) = 2 := hS ⟨3, Nat.prime_three⟩ h
  exact absurd this (by norm_num)

theorem eq_one_of_two_three {g : GM} {n : ℕ} (h2 : g ^ (2 ^ n) = 1) (h3 : g ^ 3 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
  have h1' : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
  have : orderOf g ∣ 1 := by
    rw [← hcop]
    exact Nat.dvd_gcd h1 h1'
  rwa [Nat.dvd_one, orderOf_eq_one_iff] at this

@[expose] def VG (j m : ℕ) (hj : j < 2) (hm : m < 3) : Subgroup GM where
  carrier := {g | g = 1 ∨ g = vG j m 0 ∨ g = vG j m 1 ∨ g = vG j m 2}
  one_mem' := Or.inl rfl
  mul_mem' {a b} ha hb := by
    obtain ⟨h01, h10, hsq, -⟩ := chkV_facts hj hm
    have s0 := (hsq 0 (by norm_num)).1
    have s1 := (hsq 1 (by norm_num)).1
    have s2 := (hsq 2 (by norm_num)).1
    have h02 : vG j m 0 * vG j m 2 = vG j m 1 := by
      rw [← h01, ← mul_assoc, s0, one_mul]
    have h20 : vG j m 2 * vG j m 0 = vG j m 1 := by
      rw [← h10, mul_assoc, s0, mul_one]
    have h12 : vG j m 1 * vG j m 2 = vG j m 0 := by
      rw [← h10, ← mul_assoc, s1, one_mul]
    have h21 : vG j m 2 * vG j m 1 = vG j m 0 := by
      rw [← h01, mul_assoc, s1, mul_one]
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp_all
  inv_mem' {a} ha := by
    have hsq := (chkV_facts hj hm).2.2.1
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · rw [inv_eq_of_mul_eq_one_right (hsq 0 (by norm_num)).1]; simp
    · rw [inv_eq_of_mul_eq_one_right (hsq 1 (by norm_num)).1]; simp
    · rw [inv_eq_of_mul_eq_one_right (hsq 2 (by norm_num)).1]; simp

theorem mem_VG {j m : ℕ} {hj : j < 2} {hm : m < 3} {g : GM} :
    g ∈ VG j m hj hm ↔ g = 1 ∨ ∃ i < 3, g = vG j m i := by
  show (g = 1 ∨ g = vG j m 0 ∨ g = vG j m 1 ∨ g = vG j m 2) ↔ _
  constructor
  · rintro (h | h | h | h)
    exacts [Or.inl h, Or.inr ⟨0, by norm_num, h⟩, Or.inr ⟨1, by norm_num, h⟩,
      Or.inr ⟨2, by norm_num, h⟩]
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl h
    · interval_cases i
      exacts [Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]

theorem VG_le_K0 {j m : ℕ} (hj : j < 2) (hm : m < 3) : VG j m hj hm ≤ K0G := by
  intro g hg
  rcases mem_VG.1 hg with rfl | ⟨i, hi, rfl⟩
  · exact one_mem _
  · exact vG_mem_K0 hj hm hi

theorem VG_sq {j m : ℕ} {hj : j < 2} {hm : m < 3} {g : GM} (hg : g ∈ VG j m hj hm) :
    g ^ 2 = 1 := by
  rcases mem_VG.1 hg with rfl | ⟨i, hi, rfl⟩
  · exact one_pow 2
  · rw [sq]; exact vG_sq hj hm hi

@[expose] def XG (j l m : ℕ) (hj : j < 2) (hm : m < 3) : Subgroup GM :=
  (VG j m hj hm).map (MulAut.conj (nL j l)⁻¹).toMonoidHom

theorem mem_XG {j l m : ℕ} {hj : j < 2} {hm : m < 3} {g : GM} :
    g ∈ XG j l m hj hm ↔ nL j l * g * (nL j l)⁻¹ ∈ VG j m hj hm := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hv
  · intro h
    refine ⟨_, h, ?_⟩
    simp [mul_assoc]

@[expose] def blockImage (W : Subgroup GM) : Subgroup (Perm (Fin 6)) :=
  (W.subgroupOf K0G).map actK

theorem mem_blockImage {W : Subgroup GM} {t : Perm (Fin 6)} :
    t ∈ blockImage W ↔ ∃ k : K0G, (k : GM) ∈ W ∧ actK k = t := by
  rw [blockImage, mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem actK_mem_alt (k : K0G) : Perm.sign (actK k) = 1 := by
  have : actK k ∈ actK.range := ⟨k, rfl⟩
  rw [range_actK] at this
  exact this

theorem K0_two_subgroups {j : ℕ} (hj : j < 2) (W : Subgroup GM) (hWK : W ≤ K0G)
    (h2 : ∀ g ∈ W, ∃ n, g ^ (2 ^ n) = 1) (hy : ∀ g ∈ W, (yG j)⁻¹ * g * yG j ∈ W) :
    W = ⊥ ∨ ∃ (m : ℕ) (hm : m < 3), W = VG j m hj hm := by
  have hA : ∀ t ∈ blockImage W, Perm.sign t = 1 := by
    intro t ht
    obtain ⟨k, -, rfl⟩ := mem_blockImage.1 ht
    exact actK_mem_alt k
  have h4 : ∀ t ∈ blockImage W, t ^ 4 = 1 := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_blockImage.1 ht
    obtain ⟨n, hn⟩ := h2 _ hk
    apply perm_six_pow_four_of (n := n)
    rw [← map_pow]
    have : k ^ (2 ^ n) = 1 := Subtype.ext hn
    rw [this, map_one]
  have hinv : ∀ t ∈ blockImage W, cj (sY j) t ∈ blockImage W := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_blockImage.1 ht
    have hmem : ((⟨yG j, yG_mem_K0 hj⟩⁻¹ * k * ⟨yG j, yG_mem_K0 hj⟩ : K0G) : GM) ∈ W := by
      have e : ((⟨yG j, yG_mem_K0 hj⟩⁻¹ * k * ⟨yG j, yG_mem_K0 hj⟩ : K0G) : GM) =
          (yG j)⁻¹ * k * yG j := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      exact hy _ hk
    refine mem_blockImage.2 ⟨_, hmem, ?_⟩
    unfold cj
    rw [map_mul, map_mul, map_inv, actK_yG hj]
  have hlift : ∀ g (hg : g ∈ W) (k : K0G), actK ⟨g, hWK hg⟩ = actK k →
      (∃ n, (k : GM) ^ (2 ^ n) = 1) → g = k := by
    intro g hg k hk ⟨n, hn⟩
    obtain ⟨p, hp⟩ := h2 g hg
    exact congrArg Subtype.val (eq_of_actK_eq hk hp hn)
  rcases two_subgroups hj (blockImage W) hA h4 hinv with hbot | ⟨m, hm, hV⟩
  · left
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    have ht : actK ⟨g, hWK hg⟩ ∈ blockImage W := mem_blockImage.2 ⟨⟨g, hWK hg⟩, hg, rfl⟩
    rw [hbot, mem_bot] at ht
    have := hlift g hg 1 (by rw [ht, map_one]) ⟨0, by simp⟩
    exact this
  · right
    refine ⟨m, hm, ?_⟩
    ext g
    rw [mem_VG]
    constructor
    · intro hg
      have ht : actK ⟨g, hWK hg⟩ ∈ blockImage W := mem_blockImage.2 ⟨⟨g, hWK hg⟩, hg, rfl⟩
      rcases (hV _).1 ht with h1 | ⟨i, hi, hi'⟩
      · left
        exact hlift g hg 1 (by rw [h1, map_one]) ⟨0, by simp⟩
      · right
        refine ⟨i, hi, hlift g hg ⟨vG j m i, vG_mem_K0 hj hm hi⟩
          (by rw [hi', actK_vG hj hm hi]) ⟨1, ?_⟩⟩
        rw [pow_one, sq]
        exact vG_sq hj hm hi
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact one_mem _
      · have ht : sV j m i ∈ blockImage W := (hV _).2 (Or.inr ⟨i, hi, rfl⟩)
        obtain ⟨k, hk, hkt⟩ := mem_blockImage.1 ht
        have e := hlift k hk ⟨vG j m i, vG_mem_K0 hj hm hi⟩
          (by rw [hkt, actK_vG hj hm hi]) ⟨1, by rw [pow_one, sq]; exact vG_sq hj hm hi⟩
        have e' : (k : GM) = vG j m i := e
        rw [← e']
        exact hk

theorem map_conj_centralizer (n g : GM) :
    (centralizer {g}).map (MulAut.conj n).toMonoidHom = centralizer {n * g * n⁻¹} := by
  ext k
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    calc n * c * n⁻¹ * (n * g * n⁻¹) = n * (c * g) * n⁻¹ := by group
      _ = n * (g * c) * n⁻¹ := by rw [hc]
      _ = n * g * n⁻¹ * (n * c * n⁻¹) := by group
  · intro hk
    refine ⟨n⁻¹ * k * n, ?_, by group⟩
    calc n⁻¹ * k * n * g = n⁻¹ * (k * (n * g * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * g * n⁻¹) * k) * n := by rw [hk]
      _ = g * (n⁻¹ * k * n) := by group

theorem piece {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) (S : Subgroup GM)
    (hS : IsPiSubgroup (piOf 2) S) (hA : AG j ≤ normalizer (S : Set GM)) :
    S ⊓ centralizer {mL j l} = ⊥ ∨ ∃ (m : ℕ) (hm : m < 3), S ⊓ centralizer {mL j l} =
      XG j l m hj hm := by
  set N := nL j l
  set W : Subgroup GM := (S ⊓ centralizer {mL j l}).map (MulAut.conj N).toMonoidHom with hW
  have hWc : W ≤ centralizer {xG 0} := by
    rw [hW]
    refine (map_mono inf_le_right).trans ?_
    rw [map_conj_centralizer, mL]
    intro k hk
    have e : N * (N⁻¹ * xG 0 * N) * N⁻¹ = xG 0 := by group
    rwa [e] at hk
  have h2W : ∀ g ∈ W, ∃ n, g ^ (2 ^ n) = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨n, hn⟩ := two_elem_of_pi hS hs.1
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hWK : W ≤ K0G := fun g hg => by
    obtain ⟨n, hn⟩ := h2W g hg
    exact mem_K0_of_two (hWc hg) hn
  have hyW : ∀ g ∈ W, (yG j)⁻¹ * g * yG j ∈ W := by
    rintro _ ⟨s, hs, rfl⟩
    set y' := N⁻¹ * yG j * N with hy'
    have hy'A : y' ∈ AG j := conj_mem_AG hj hl (yG_mem_AG hj)
    have hy'n := hA hy'A
    have hs' : y'⁻¹ * s * y' ∈ S := by
      have := (mem_normalizer_iff.1 (hA (inv_mem hy'A)) s).1 hs.1
      simpa using this
    have hc : y'⁻¹ * s * y' ∈ centralizer {mL j l} := by
      have hm : Commute s (mL j l) := mem_centralizer_singleton_iff.1 hs.2
      have hyc : Commute y' (mL j l) := AG_comm hj hy'A (mL_mem_AG hj hl)
      rw [mem_centralizer_singleton_iff]
      exact ((hyc.inv_left.mul_left hm).mul_left hyc).eq
    refine ⟨y'⁻¹ * s * y', ⟨hs', hc⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hy']
    group
  rcases K0_two_subgroups hj W hWK h2W hyW with hbot | ⟨m, hm, hV⟩
  · left
    have : S ⊓ centralizer {mL j l} = W.map (MulAut.conj N⁻¹).toMonoidHom := by
      rw [hW, map_map]
      conv_lhs => rw [← map_id (S ⊓ centralizer {mL j l})]
      congr 1
      refine MonoidHom.ext fun g => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [this, hbot, Subgroup.map_bot]
  · right
    refine ⟨m, hm, ?_⟩
    have : S ⊓ centralizer {mL j l} = W.map (MulAut.conj N⁻¹).toMonoidHom := by
      rw [hW, map_map]
      conv_lhs => rw [← map_id (S ⊓ centralizer {mL j l})]
      congr 1
      refine MonoidHom.ext fun g => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [this, hV]
    rfl

theorem witData_bool : ((List.range 2).all fun j => (List.range 4).all fun l₁ =>
    (List.range 4).all fun l₂ => !(decide (l₁ < l₂)) || (List.range 3).all fun m₁ =>
      (List.range 3).all fun m₂ => witData.contains (j, l₁, l₂, m₁, m₂)) = true := by
  decide

theorem witData_mem : ∀ j < 2, ∀ l₁ < 4, ∀ l₂ < 4, l₁ < l₂ → ∀ m₁ < 3, ∀ m₂ < 3,
    (j, l₁, l₂, m₁, m₂) ∈ witData := by
  intro j hj l₁ hl₁ l₂ hl₂ hl m₁ hm₁ m₂ hm₂
  have h := witData_bool
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt] at h
  rcases h j hj l₁ hl₁ l₂ hl₂ with h' | h'
  · omega
  · exact List.contains_iff_mem.1 (h' m₁ hm₁ m₂ hm₂)

theorem witness {j : ℕ} (hj : j < 2) {l₁ l₂ : ℕ} (hl₁ : l₁ < 4) (hl₂ : l₂ < 4) (hl : l₁ < l₂)
    {m₁ m₂ : ℕ} (hm₁ : m₁ < 3) (hm₂ : m₂ < 3) :
    let t₀ := (nL j l₁)⁻¹ * vG j m₁ 0 * nL j l₁
    let s₀ := (nL j l₂)⁻¹ * vG j m₂ 0 * nL j l₂
    let s₁ := (nL j l₂)⁻¹ * vG j m₂ 1 * nL j l₂
    (s₁ * (t₀ * (s₀ * t₀))) ^ 3 = 1 ∧ s₁ * (t₀ * (s₀ * t₀)) ≠ 1 := by
  intro t₀ s₀ s₁
  have hd := wit_facts _
    (witData_mem j hj l₁ hl₁ l₂ hl₂ hl m₁ hm₁ m₂ hm₂)
  have hn₁ := eM_rL hj hl₁
  have hn₂ := eM_rL hj hl₂
  have e : (s₁ * (t₀ * (s₀ * t₀))).1 =
      ((eM ((rL.getD j []).getD l₂ 0))⁻¹ * (eM (vReg j m₂ 1) * eM ((rL.getD j []).getD l₂ 0))) *
      (((eM ((rL.getD j []).getD l₁ 0))⁻¹ * (eM (vReg j m₁ 0) * eM ((rL.getD j []).getD l₁ 0))) *
      (((eM ((rL.getD j []).getD l₂ 0))⁻¹ * (eM (vReg j m₂ 0) * eM ((rL.getD j []).getD l₂ 0))) *
      ((eM ((rL.getD j []).getD l₁ 0))⁻¹ * (eM (vReg j m₁ 0) * eM ((rL.getD j []).getD l₁ 0))))) := by
    rw [hn₁, hn₂]
    simp only [t₀, s₀, s₁, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    rfl
  refine ⟨Subtype.ext ?_, fun he => hd.2 ?_⟩
  · rw [Subgroup.coe_pow, e, Subgroup.coe_one]
    exact hd.1
  · rw [← e, he, Subgroup.coe_one]

theorem vG_mem_XG {j l m : ℕ} (hj : j < 2) (hm : m < 3) {i : ℕ} (hi : i < 3) :
    (nL j l)⁻¹ * vG j m i * nL j l ∈ XG j l m hj hm :=
  ⟨vG j m i, mem_VG.2 (Or.inr ⟨i, hi, rfl⟩), by simp⟩

theorem not_two_lines_lt {j : ℕ} (hj : j < 2) {l₁ l₂ : ℕ} (hl₁ : l₁ < 4) (hl₂ : l₂ < 4)
    (hl : l₁ < l₂) {m₁ m₂ : ℕ} (hm₁ : m₁ < 3) (hm₂ : m₂ < 3) (S : Subgroup GM)
    (hS : IsPiSubgroup (piOf 2) S) (h₁ : XG j l₁ m₁ hj hm₁ ≤ S) (h₂ : XG j l₂ m₂ hj hm₂ ≤ S) :
    False := by
  obtain ⟨h3, hne⟩ := witness hj hl₁ hl₂ hl hm₁ hm₂
  have ht := h₁ (vG_mem_XG (l := l₁) hj hm₁ (i := 0) (by norm_num))
  have hs₀ := h₂ (vG_mem_XG (l := l₂) hj hm₂ (i := 0) (by norm_num))
  have hs₁ := h₂ (vG_mem_XG (l := l₂) hj hm₂ (i := 1) (by norm_num))
  have hu := mul_mem hs₁ (mul_mem ht (mul_mem hs₀ ht))
  obtain ⟨n, hn⟩ := two_elem_of_pi hS hu
  exact hne (eq_one_of_two_three hn h3)

theorem not_two_lines {j : ℕ} (hj : j < 2) {l₁ l₂ : ℕ} (hl₁ : l₁ < 4) (hl₂ : l₂ < 4)
    (hl : l₁ ≠ l₂) {m₁ m₂ : ℕ} (hm₁ : m₁ < 3) (hm₂ : m₂ < 3) (S : Subgroup GM)
    (hS : IsPiSubgroup (piOf 2) S) (h₁ : XG j l₁ m₁ hj hm₁ ≤ S) (h₂ : XG j l₂ m₂ hj hm₂ ≤ S) :
    False := by
  rcases Nat.lt_or_gt_of_ne hl with h | h
  · exact not_two_lines_lt hj hl₁ hl₂ h hm₁ hm₂ S hS h₁ h₂
  · exact not_two_lines_lt hj hl₂ hl₁ h hm₂ hm₁ S hS h₂ h₁

theorem iSup_pieces {j : ℕ} (hj : j < 2) (S : Subgroup GM) (hS : IsPiSubgroup (piOf 2) S)
    (hA : AG j ≤ normalizer (S : Set GM)) :
    S = ⨆ (e : EG j hj) (_ : e ≠ 1), S ⊓ centralizer {(e : GM)} :=
  CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three (EG j hj) S (EG_cube hj) (card_EG hj) (not_three_dvd_of_pi hS)
    ((EG_le_AG hj).trans hA)

theorem inv_two_subgroups {j : ℕ} (hj : j < 2) (S : Subgroup GM) (hS : IsPiSubgroup (piOf 2) S)
    (hA : AG j ≤ normalizer (S : Set GM)) :
    S = ⊥ ∨ ∃ l < 4, ∃ (m : ℕ) (hm : m < 3), S = XG j l m hj hm := by
  by_cases hall : ∀ l < 4, S ⊓ centralizer {mL j l} = ⊥
  · left
    rw [iSup_pieces hj S hS hA]
    apply le_antisymm _ bot_le
    refine iSup_le fun e => iSup_le fun he => ?_
    obtain ⟨l, hl, hc⟩ := centralizer_EG hj e he
    rw [hc, hall l hl]
  · right
    push Not at hall
    obtain ⟨l, hl, hne⟩ := hall
    rcases piece hj hl S hS hA with h | ⟨m, hm, hX⟩
    · exact absurd h hne
    refine ⟨l, hl, m, hm, ?_⟩
    apply le_antisymm
    · rw [iSup_pieces hj S hS hA]
      refine iSup_le fun e => iSup_le fun he => ?_
      obtain ⟨l', hl', hc⟩ := centralizer_EG hj e he
      rw [hc]
      by_cases hll : l' = l
      · subst hll
        rw [hX]
      · rcases piece hj hl' S hS hA with h' | ⟨m', hm', hX'⟩
        · rw [h']
          exact bot_le
        · exfalso
          apply not_two_lines hj hl' hl hll hm' hm S hS
          · rw [← hX']; exact inf_le_left
          · rw [← hX]; exact inf_le_left
    · rw [← hX]
      exact inf_le_left

theorem XG_mem_closure {j : ℕ} (hj : j < 2) {g : GM} (hg : g ∈ AG j) :
    g ∈ Subgroup.closure {xG 0, yG j, zG} := by
  obtain ⟨hg', hl⟩ := mem_AG.1 hg
  have hv : relG.coord ⟨g, hg'⟩ = (relG.coord ⟨g, hg'⟩ 0).val • Pi.single 0 1 +
      (relG.coord ⟨g, hg'⟩ 1).val • yv j := by
    revert hl
    generalize relG.coord ⟨g, hg'⟩ = v
    revert v
    interval_cases j <;> decide +kernel
  have hmem : xG 0 ^ (relG.coord ⟨g, hg'⟩ 0).val * yG j ^ (relG.coord ⟨g, hg'⟩ 1).val ∈ P0G :=
    mul_mem (pow_mem (ThreeQRel.v_mem 0) _) (pow_mem (yG_mem_P0 hj) _)
  have hc : relG.coord ⟨g, hg'⟩ = relG.coord ⟨_, hmem⟩ := by
    rw [coord_mul' (pow_mem (ThreeQRel.v_mem 0) _) (pow_mem (yG_mem_P0 hj) _),
      coord_pow' (ThreeQRel.v_mem 0), coord_pow' (yG_mem_P0 hj), coord_xG0, coord_yG hj]
    exact hv
  obtain ⟨c, hc'⟩ := eq_mul_zpow_of_coord hg' hmem hc
  rw [hc']
  refine mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
    (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)

theorem mem_normalizer_of_comm {H : Subgroup GM} {y : GM} (hc : ∀ v ∈ H, y * v = v * y) :
    y ∈ normalizer (H : Set GM) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hc h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have e : y * h * y⁻¹ = h := by
      have := hc (y * h * y⁻¹) hh
      have e2 : y * (y * h * y⁻¹) = y * h := by
        rw [this]
        group
      exact mul_left_cancel e2
    rwa [e] at hh

theorem mem_normalizer_of_conj {H : Subgroup GM} {y : GM} (hy3 : y ^ 3 = 1)
    (hc : ∀ v ∈ H, y⁻¹ * v * y ∈ H) : y ∈ normalizer (H : Set GM) := by
  rw [mem_normalizer_iff]
  intro h
  have hyy : y * y = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three', hy3]
  constructor
  · intro hh
    have e : y * h * y⁻¹ = y⁻¹ * (y⁻¹ * h * y) * y := by
      have h1 : y⁻¹ * y⁻¹ = y := by rw [← mul_inv_rev, hyy, inv_inv]
      calc y * h * y⁻¹ = (y⁻¹ * y⁻¹) * h * (y * y) := by rw [h1, hyy]
        _ = y⁻¹ * (y⁻¹ * h * y) * y := by group
    rw [e]
    exact hc _ (hc _ hh)
  · intro hh
    have := hc _ hh
    simpa [mul_assoc] using this

theorem AG_le_normalizer_VG {j m : ℕ} (hj : j < 2) (hm : m < 3) :
    AG j ≤ normalizer (VG j m hj hm : Set GM) := by
  intro g hg
  have hle : Subgroup.closure {xG 0, yG j, zG} ≤ normalizer (VG j m hj hm : Set GM) := by
    rw [closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · apply mem_normalizer_of_comm
      intro v hv
      rcases mem_VG.1 hv with rfl | ⟨i, hi, rfl⟩
      · rw [mul_one, one_mul]
      · exact (vG_comm_x0 hj hm hi).symm
    · apply mem_normalizer_of_conj (yG_cube hj)
      intro v hv
      rcases mem_VG.1 hv with rfl | ⟨i, hi, rfl⟩
      · rw [mul_one, inv_mul_cancel]
        exact one_mem _
      · obtain ⟨i', hi', he⟩ := (chkV_facts hj hm).2.2.2.1 i hi
        rw [he]
        exact mem_VG.2 (Or.inr ⟨i', hi', rfl⟩)
    · apply mem_normalizer_of_comm
      intro v _
      exact zG_central v
  exact hle (XG_mem_closure hj hg)

theorem AG_le_normalizer_XG {j l m : ℕ} (hj : j < 2) (hl : l < 4) (hm : m < 3) :
    AG j ≤ normalizer (XG j l m hj hm : Set GM) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro g
  rw [mem_XG, mem_XG]
  have ha' : nL j l * a * (nL j l)⁻¹ ∈ AG j := conj_mem_AG' hj hl ha
  have hn := mem_normalizer_iff.1 (AG_le_normalizer_VG hj hm ha') (nL j l * g * (nL j l)⁻¹)
  rw [hn]
  have e : nL j l * a * (nL j l)⁻¹ * (nL j l * g * (nL j l)⁻¹) * (nL j l * a * (nL j l)⁻¹)⁻¹ =
      nL j l * (a * g * a⁻¹) * (nL j l)⁻¹ := by group
  rw [e]

theorem card_VG {j m : ℕ} (hj : j < 2) (hm : m < 3) : Nat.card (VG j m hj hm) = 4 := by
  obtain ⟨h01, h10, hsq, -⟩ := chkV_facts hj hm
  have hne : ∀ i < 3, vG j m i ≠ 1 := fun i hi => (hsq i hi).2
  have s0 := (hsq 0 (by norm_num)).1
  have s1 := (hsq 1 (by norm_num)).1
  have d01 : vG j m 0 ≠ vG j m 1 := fun h => hne 2 (by norm_num) (by rw [← h01, ← h, s0])
  have d02 : vG j m 0 ≠ vG j m 2 := fun h => hne 1 (by norm_num) (by
    have e : vG j m 0 * vG j m 1 = vG j m 0 * 1 := by rw [h01, ← h, mul_one]
    exact mul_left_cancel e)
  have d12 : vG j m 1 ≠ vG j m 2 := fun h => hne 0 (by norm_num) (by
    have e : vG j m 0 * vG j m 1 = 1 * vG j m 1 := by rw [h01, ← h, one_mul]
    exact mul_right_cancel e)
  have e : (VG j m hj hm : Set GM) =
      (({1, vG j m 0, vG j m 1, vG j m 2} : Finset GM) : Set GM) := by
    ext g
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact Iff.rfl
  have hc : Nat.card (VG j m hj hm) = Nat.card ((VG j m hj hm : Set GM)) := rfl
  rw [hc, e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair d12]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨d01, d02⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(hne 0 (by norm_num)).symm, (hne 1 (by norm_num)).symm, (hne 2 (by norm_num)).symm⟩

theorem card_XG {j l m : ℕ} (hj : j < 2) (hm : m < 3) : Nat.card (XG j l m hj hm) = 4 := by
  rw [XG, card_map_of_injective (MulAut.conj (nL j l)⁻¹).injective, card_VG]

theorem XG_sq {j l m : ℕ} {hj : j < 2} {hm : m < 3} {g : GM} (hg : g ∈ XG j l m hj hm) :
    g ^ 2 = 1 := by
  obtain ⟨v, hv, rfl⟩ := hg
  rw [← map_pow, VG_sq hv, map_one]

theorem isKleinFour_XG {j l m : ℕ} (hj : j < 2) (hm : m < 3) : IsKleinFour (XG j l m hj hm) := by
  have h4 := card_XG (l := l) hj hm
  refine ⟨h4, ?_⟩
  have : Nontrivial (XG j l m hj hm) := by
    rw [← Finite.one_lt_card_iff_nontrivial, h4]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  exact orderOf_eq_prime (Subtype.ext (XG_sq g.2)) hg

theorem isPi_XG {j l m : ℕ} (hj : j < 2) (hm : m < 3) : IsPiSubgroup (piOf 2) (XG j l m hj hm) := by
  intro p hp
  rw [card_XG hj hm, show (4 : ℕ) = 2 ^ 2 by norm_num] at hp
  exact (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 (p.2.dvd_of_dvd_pow hp)

theorem XG_mem_inv {j l m : ℕ} (hj : j < 2) (hl : l < 4) (hm : m < 3) :
    XG j l m hj hm ∈ invariantPiSubgroups ⊤ (AG j) (piOf 2) :=
  ⟨le_top, isPi_XG hj hm, AG_le_normalizer_XG hj hl hm⟩

theorem maxInv_AG {j : ℕ} (hj : j < 2) {S : Subgroup GM}
    (hS : S ∈ maxInvariantPiSubgroups ⊤ (AG j) (piOf 2)) :
    ∃ l < 4, ∃ (m : ℕ) (hm : m < 3), S = XG j l m hj hm := by
  rcases inv_two_subgroups hj S hS.1.2.1 hS.1.2.2 with h | h
  · exfalso
    have hX := XG_mem_inv hj (l := 0) (by norm_num) (m := 0) (by norm_num)
    have hle : S ≤ XG j 0 0 hj (by norm_num) := by rw [h]; exact bot_le
    have hXS := hS.2 hX hle
    rw [h, le_bot_iff] at hXS
    have := card_XG (l := 0) hj (m := 0) (by norm_num)
    rw [hXS, card_bot] at this
    exact absurd this (by norm_num)
  · exact h

@[expose] def KL (j l : ℕ) : Subgroup GM := K0G.map (MulAut.conj (nL j l)⁻¹).toMonoidHom

theorem XG_le_K {j l m : ℕ} (hj : j < 2) (hm : m < 3) : XG j l m hj hm ≤ KL j l :=
  map_mono (VG_le_K0 hj hm)

theorem cj_sY_ne : ∀ j < 2, ∀ m < 3, cj (sY j) (sV j m 0) ≠ sV j m 0 := by
  decide

theorem commute_right_of_mul {p q v : GM} (h : Commute (p * q) v) (hp : Commute p v) :
    Commute q v := by
  have e : p * (q * v) = p * (v * q) := by
    calc p * (q * v) = p * q * v := by rw [mul_assoc]
      _ = v * (p * q) := h.eq
      _ = v * p * q := by rw [mul_assoc]
      _ = p * v * q := by rw [hp.eq]
      _ = p * (v * q) := by rw [mul_assoc]
  exact mul_left_cancel e

theorem commute_left_of_mul {p q v : GM} (h : Commute (p * q) v) (hq : Commute q v) :
    Commute p v := by
  have e : p * v * q = v * p * q := by
    calc p * v * q = p * (v * q) := by rw [mul_assoc]
      _ = p * (q * v) := by rw [hq.eq]
      _ = p * q * v := by rw [mul_assoc]
      _ = v * (p * q) := h.eq
      _ = v * p * q := by rw [mul_assoc]
  exact mul_right_cancel e

theorem vecWord_nsmul (w : List ℕ) (n : ℕ) (v : Fin 4 → ZMod 3) :
    vecWord w (n • v) = n • vecWord w v := by
  induction w generalizing v with
  | nil => rfl
  | cons k w ih =>
    simp only [vecWord, List.foldl_cons] at ih ⊢
    rw [show vmul (matN k) (n • v) = n • vmul (matN k) v by
      funext i
      simp only [vmul, Pi.smul_apply, nsmul_eq_mul]
      ring]
    exact ih _

theorem coord_of_centralizes_XG {j l m : ℕ} (hj : j < 2) (hl : l < 4) (hm : m < 3) {a : GM}
    (ha : a ∈ AG j) (hc : a ∈ centralizer (XG j l m hj hm : Set GM)) :
    ∃ s : ℕ, relG.coord ⟨a, AG_le_P0 j ha⟩ = s • uL j l := by
  set N := nL j l
  have ha' : N * a * N⁻¹ ∈ AG j := conj_mem_AG' hj hl ha
  obtain ⟨hP, hL⟩ := mem_AG.1 ha'
  set v := relG.coord ⟨N * a * N⁻¹, hP⟩ with hv
  have hcv : Commute (N * a * N⁻¹) (vG j m 0) := by
    have hx : N⁻¹ * vG j m 0 * N ∈ XG j l m hj hm := vG_mem_XG hj hm (by norm_num)
    have := (mem_centralizer_iff.1 hc) _ hx
    show N * a * N⁻¹ * vG j m 0 = vG j m 0 * (N * a * N⁻¹)
    have e1 : N * a * N⁻¹ * vG j m 0 = N * (a * (N⁻¹ * vG j m 0 * N)) * N⁻¹ := by group
    have e2 : vG j m 0 * (N * a * N⁻¹) = N * ((N⁻¹ * vG j m 0 * N) * a) * N⁻¹ := by group
    rw [e1, e2, this]
  have hdec : v = (v 0).val • Pi.single 0 1 + (v 1).val • yv j := by
    revert hL
    generalize v = w
    revert w
    interval_cases j <;> decide +kernel
  have hmem : xG 0 ^ (v 0).val * yG j ^ (v 1).val ∈ P0G :=
    mul_mem (pow_mem (ThreeQRel.v_mem 0) _) (pow_mem (yG_mem_P0 hj) _)
  have hce : v = relG.coord ⟨_, hmem⟩ := by
    rw [coord_mul' (pow_mem (ThreeQRel.v_mem 0) _) (pow_mem (yG_mem_P0 hj) _),
      coord_pow' (ThreeQRel.v_mem 0), coord_pow' (yG_mem_P0 hj), coord_xG0, coord_yG hj]
    exact hdec
  obtain ⟨c, hc'⟩ := eq_mul_zpow_of_coord hP hmem hce
  have hβ : (v 1).val = 0 := by
    by_contra hβ
    rw [hc'] at hcv
    have h1 := commute_left_of_mul hcv (Commute.pow_left (zG_central _) c)
    have hx : Commute (xG 0) (vG j m 0) := (vG_comm_x0 hj hm (by norm_num : (0 : ℕ) < 3)).symm
    have h2 : Commute (yG j ^ (v 1).val) (vG j m 0) := commute_right_of_mul h1 (hx.pow_left _)
    have hy : Commute (yG j) (vG j m 0) := by
      have hb : (v 1).val = 1 ∨ (v 1).val = 2 := by
        have := ZMod.val_lt (v 1)
        omega
      rcases hb with hb | hb
      · rw [hb, pow_one] at h2
        exact h2
      · rw [hb] at h2
        have e : yG j = (yG j ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, yG_cube hj, one_mul, pow_one]
        rw [e]
        exact h2.pow_left 2
    apply cj_sY_ne j hj m hm
    have hk : (⟨yG j, yG_mem_K0 hj⟩ : K0G)⁻¹ * ⟨vG j m 0, vG_mem_K0 hj hm (by norm_num)⟩ *
        ⟨yG j, yG_mem_K0 hj⟩ = ⟨vG j m 0, vG_mem_K0 hj hm (by norm_num)⟩ := by
      apply Subtype.ext
      show (yG j)⁻¹ * vG j m 0 * yG j = vG j m 0
      rw [mul_assoc, ← hy.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    have := congrArg actK hk
    rw [map_mul, map_mul, map_inv, actK_yG hj, actK_vG hj hm (by norm_num)] at this
    exact this
  refine ⟨(v 0).val, ?_⟩
  have e : a = N⁻¹ * (N * a * N⁻¹) * N := by group
  have hcoord := coord_conjW (lw j l) (lw_lt hj hl) hP
  have ea : (⟨a, AG_le_P0 j ha⟩ : P0G) = ⟨N⁻¹ * (N * a * N⁻¹) * N,
      conjW_mem _ (lw_lt hj hl) hP⟩ := Subtype.ext e
  have hv0 : v = (v 0).val • Pi.single 0 1 := by
    rw [hβ, zero_smul, add_zero] at hdec
    exact hdec
  rw [ea, hcoord, ← hv]
  conv_lhs => rw [hv0]
  rw [vecWord_nsmul]
  rfl

end CFSG.RankThree.Native.ONTriple
