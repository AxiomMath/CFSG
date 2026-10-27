module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E9Bad
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A8
public import CFSG.LieType.Multipliers.G24Bridge
public import Certificates.Certificate148012

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S CFSG.RankThree.PartTwo.Sec4.RonanK429H

section Sylow

variable {S : Type} [Group S] [Finite S]

theorem e9MoveBad_of_sylow {P₀ : Subgroup S} (hP : IsPGroup 3 P₀) (hidx : ¬ 3 ∣ P₀.index)
    (hmv : ∀ B : Subgroup S, B ≤ P₀ → CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
      ∀ s ∈ B, s ≠ 1 → ¬ Good427 (Subgroup.centralizer ({s} : Set S)) →
        ∃ n ∈ Subgroup.normalizer (B : Set S),
          n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)) :
    E9MoveBad S := by
  intro B hB hB9 s hs hs1 hbad
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpB : IsPGroup 3 B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  obtain ⟨Q, hBQ⟩ := hpB.exists_le_sylow
  let P : Sylow 3 S := hP.toSylow hidx
  haveI : Finite (Sylow 3 S) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q P
  have hQP : (Q : Subgroup S).map (MulAut.conj g).toMonoidHom = P₀ := by
    have h := congrArg (fun R : Sylow 3 S => (R : Subgroup S)) hg
    simp only [Sylow.coe_subgroup_smul] at h
    exact h
  have hB'P : B.map (MulAut.conj g).toMonoidHom ≤ P₀ := hQP ▸ Subgroup.map_mono hBQ
  have hB'e : CFSG.Assembly.IsElemAbelian 3 (B.map (MulAut.conj g).toMonoidHom) :=
    isElemAbelian_map _ hB
  have hB'9 : Nat.card (B.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB9]
  have hs' : (MulAut.conj g) s ∈ B.map (MulAut.conj g).toMonoidHom := ⟨s, hs, rfl⟩
  have hs'1 : (MulAut.conj g) s ≠ 1 := by
    rw [Ne, map_eq_one_iff _ (MulAut.conj g).injective]
    exact hs1
  have hbad' : ¬ Good427 (Subgroup.centralizer ({(MulAut.conj g) s} : Set S)) := fun h =>
    hbad (Good427.of_isConj (isConj_iff.mpr ⟨g⁻¹, by rw [MulAut.conj_apply]; group⟩) h)
  obtain ⟨n', hn', hns'⟩ := hmv _ hB'P hB'e hB'9 _ hs' hs'1 hbad'
  rw [← Subgroup.map_equiv_normalizer_eq] at hn'
  obtain ⟨n, hn, rfl⟩ := hn'
  refine ⟨n, hn, fun hn2 => hns' ?_⟩
  have hZ : (Subgroup.zpowers s).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers ((MulAut.conj g) s) := MonoidHom.map_zpowers _ s
  rw [← hZ, ← Subgroup.map_equiv_normalizer_eq]
  exact ⟨n, hn2, rfl⟩

end Sylow

section Heis

variable {S : Type} [Group S] {x y z : S}

structure HeisRel (x y z : S) : Prop where
  hx : x ^ 3 = 1
  hy : y ^ 3 = 1
  hc : x * y * x ^ 2 * y ^ 2 = z
  hzx : z * x = x * z
  hzy : z * y = y * z
  hz : z ≠ 1

theorem heis_pow_mod_three {w : S} (hw : w ^ 3 = 1) (n : ℕ) : w ^ n = w ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hw, one_pow, mul_one]

namespace HeisRel

variable (h : HeisRel x y z)
include h

theorem czx : Commute z x := h.hzx

theorem czy : Commute z y := h.hzy

theorem cz (c a b : ℕ) : Commute (z ^ c) (x ^ a * y ^ b) :=
  (h.czx.pow_pow c a).mul_right (h.czy.pow_pow c b)

theorem inv_x : x⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h.hx])

theorem inv_y : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h.hy])

theorem conj_y : x * y * x⁻¹ = z * y := by
  rw [← h.hc, h.inv_x, mul_assoc (x * y * x ^ 2), ← pow_succ, h.hy, mul_one]

theorem z_cube : z ^ 3 = 1 := by
  calc z ^ 3 = z ^ 3 * y ^ 3 := by rw [h.hy, mul_one]
    _ = (z * y) ^ 3 := (h.czy.mul_pow 3).symm
    _ = (x * y * x⁻¹) ^ 3 := by rw [h.conj_y]
    _ = 1 := by rw [conj_pow, h.hy, mul_one, mul_inv_cancel]

theorem orderOf_z : orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h.z_cube h.hz

theorem pow_z_inj {m n : ℕ} (hm : m < 3) (hn : n < 3) (e : z ^ m = z ^ n) : m = n := by
  have e' := pow_eq_pow_iff_modEq.mp e
  rw [h.orderOf_z, Nat.ModEq] at e'
  omega

theorem conj_yb (b : ℕ) : x * y ^ b * x⁻¹ = z ^ b * y ^ b := by
  rw [← conj_pow, h.conj_y, h.czy.mul_pow]

theorem yx : y * x = z ^ 2 * x * y := by
  calc y * x = z ^ 3 * (y * x) := by rw [h.z_cube, one_mul]
    _ = z ^ 2 * (z * y * x) := by group
    _ = z ^ 2 * (x * y) := by rw [← mul_inv_eq_iff_eq_mul.mp h.conj_y]
    _ = z ^ 2 * x * y := by rw [mul_assoc]

theorem conj_xa (a : ℕ) : y * x ^ a * y⁻¹ = z ^ (2 * a) * x ^ a := by
  have e : y * x * y⁻¹ = z ^ 2 * x := by rw [h.yx, mul_inv_cancel_right]
  rw [← conj_pow, e, (h.czx.pow_left 2).mul_pow, ← pow_mul]

theorem y_xa (a : ℕ) : y * x ^ a = z ^ (2 * a) * x ^ a * y :=
  mul_inv_eq_iff_eq_mul.mp (h.conj_xa a)

theorem lx (a b c : ℕ) : x * (x ^ a * y ^ b * z ^ c) = x ^ (a + 1) * y ^ b * z ^ c := by
  rw [← mul_assoc, ← mul_assoc, ← pow_succ']

theorem ly (a b c : ℕ) : y * (x ^ a * y ^ b * z ^ c) = x ^ a * y ^ (b + 1) * z ^ (2 * a + c) := by
  calc y * (x ^ a * y ^ b * z ^ c) = y * x ^ a * y ^ b * z ^ c := by simp only [mul_assoc]
    _ = z ^ (2 * a) * (x ^ a * (y * y ^ b)) * z ^ c := by rw [h.y_xa]; simp only [mul_assoc]
    _ = x ^ a * y ^ (b + 1) * (z ^ (2 * a) * z ^ c) := by
      rw [← pow_succ', (h.cz (2 * a) a (b + 1)).eq]
      simp only [mul_assoc]
    _ = x ^ a * y ^ (b + 1) * z ^ (2 * a + c) := by rw [pow_add z (2 * a) c]

theorem conj_x (a b c : ℕ) :
    x * (x ^ a * y ^ b * z ^ c) * x⁻¹ = x ^ a * y ^ b * z ^ c * z ^ b := by
  calc x * (x ^ a * y ^ b * z ^ c) * x⁻¹ = x ^ a * (x * y ^ b * x⁻¹) * (x * z ^ c * x⁻¹) := by
        group
    _ = x ^ a * (z ^ b * y ^ b) * z ^ c := by
      rw [h.conj_yb, ← (h.czx.pow_left c).eq, mul_inv_cancel_right]
    _ = x ^ a * y ^ b * z ^ c * z ^ b := by
      rw [(h.czy.pow_pow b b).eq]
      simp only [mul_assoc]
      rw [← pow_add, ← pow_add, Nat.add_comm]

theorem conj_y' (a b c : ℕ) :
    y * (x ^ a * y ^ b * z ^ c) * y⁻¹ = x ^ a * y ^ b * z ^ c * z ^ (2 * a) := by
  calc y * (x ^ a * y ^ b * z ^ c) * y⁻¹ = y * x ^ a * y⁻¹ * y ^ b * (y * z ^ c * y⁻¹) := by
        group
    _ = z ^ (2 * a) * (x ^ a * y ^ b) * z ^ c := by
      rw [h.conj_xa, ← (h.czy.pow_left c).eq, mul_inv_cancel_right, mul_assoc (z ^ (2 * a))]
    _ = x ^ a * y ^ b * z ^ c * z ^ (2 * a) := by
      rw [(h.cz (2 * a) a b).eq]
      simp only [mul_assoc]
      rw [← pow_add, ← pow_add, Nat.add_comm]

theorem mem_closure_nf {g : S} (hg : g ∈ Subgroup.closure ({x, y} : Set S)) :
    ∃ a b c : ℕ, g = x ^ a * y ^ b * z ^ c := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul_left g hg k _ ih =>
    obtain ⟨a, b, c, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨a + 1, b, c, h.lx a b c⟩
    · exact ⟨a, b + 1, 2 * a + c, h.ly a b c⟩
  | inv_mul_cancel g hg k _ ih =>
    obtain ⟨a, b, c, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨a + 1 + 1, b, c, by rw [h.inv_x, sq, mul_assoc, h.lx, h.lx]⟩
    · exact ⟨a, b + 1 + 1, 2 * a + (2 * a + c), by rw [h.inv_y, sq, mul_assoc, h.ly, h.ly]⟩

theorem mem_closure_nf3 {g : S} (hg : g ∈ Subgroup.closure ({x, y} : Set S)) :
    ∃ a b c : ℕ, a < 3 ∧ b < 3 ∧ c < 3 ∧ g = x ^ a * y ^ b * z ^ c := by
  obtain ⟨a, b, c, rfl⟩ := h.mem_closure_nf hg
  exact ⟨a % 3, b % 3, c % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), by
      rw [← heis_pow_mod_three h.hx, ← heis_pow_mod_three h.hy, ← heis_pow_mod_three h.z_cube]⟩

theorem z_mem : z ∈ Subgroup.closure ({x, y} : Set S) := by
  have hxm : x ∈ Subgroup.closure ({x, y} : Set S) := Subgroup.subset_closure (by simp)
  have hym : y ∈ Subgroup.closure ({x, y} : Set S) := Subgroup.subset_closure (by simp)
  rw [← h.hc]
  exact mul_mem (mul_mem (mul_mem hxm hym) (pow_mem hxm 2)) (pow_mem hym 2)

theorem nf_inj {a b c d f g : ℕ} (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (hf : f < 3) (hg : g < 3) (e : x ^ a * y ^ b * z ^ c = x ^ d * y ^ f * z ^ g) :
    a = d ∧ b = f ∧ c = g := by
  have e1 := h.conj_x a b c
  rw [e, h.conj_x d f g] at e1
  have hbf : f = b := h.pow_z_inj hf hb (mul_left_cancel e1)
  have e2 := h.conj_y' a b c
  rw [e, h.conj_y' d f g] at e2
  have e3 := pow_eq_pow_iff_modEq.mp (mul_left_cancel e2)
  rw [h.orderOf_z, Nat.ModEq] at e3
  have had : a = d := by omega
  subst hbf had
  exact ⟨rfl, rfl, h.pow_z_inj hc hg (mul_left_cancel e)⟩

theorem card_closure : Nat.card (Subgroup.closure ({x, y} : Set S)) = 27 := by
  have hxm : x ∈ Subgroup.closure ({x, y} : Set S) := Subgroup.subset_closure (by simp)
  have hym : y ∈ Subgroup.closure ({x, y} : Set S) := Subgroup.subset_closure (by simp)
  let F : Fin 3 × Fin 3 × Fin 3 → Subgroup.closure ({x, y} : Set S) := fun t =>
    ⟨x ^ t.1.val * y ^ t.2.1.val * z ^ t.2.2.val,
      mul_mem (mul_mem (pow_mem hxm _) (pow_mem hym _)) (pow_mem h.z_mem _)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun s t e => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := h.nf_inj s.1.isLt s.2.1.isLt s.2.2.isLt t.1.isLt t.2.1.isLt
        t.2.2.isLt (congrArg Subtype.val e)
      exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
    · obtain ⟨a, b, c, ha, hb, hc, e⟩ := h.mem_closure_nf3 g.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩), Subtype.ext e.symm⟩
  rw [← Nat.card_eq_of_bijective F hF]
  simp [Nat.card_prod]

theorem not_comm : x * y ≠ y * x := by
  intro hxy
  apply h.hz
  calc z = x * y * x ^ 2 * y ^ 2 := h.hc.symm
    _ = y * x ^ 3 * y ^ 2 := by rw [hxy]; group
    _ = 1 := by rw [h.hx, mul_one, ← pow_succ', h.hy]

theorem x_not_mem : x ∉ Subgroup.zpowers z := by
  intro hm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
  have hxy : Commute x y := by
    rw [← hk]
    exact h.czy.zpow_left k
  exact h.not_comm hxy.eq

theorem moved {n s : S} {k : ℕ} (hs3 : s ^ 3 = 1) (hsz : s ∉ Subgroup.zpowers z)
    (hk : z ^ k ≠ 1) (e : n * s * n⁻¹ = s * z ^ k) :
    n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  have hzk : z ^ k ∈ Subgroup.zpowers z := pow_mem (Subgroup.mem_zpowers z) k
  refine not_mem_normalizer_of_conj (not_mem_zpowers_of_ne hs3 ?_ ?_ ?_) <;> rw [e]
  · intro e1
    exact hsz (by rw [eq_inv_of_mul_eq_one_left e1]; exact inv_mem hzk)
  · intro e1
    exact hk (mul_left_cancel (e1.trans (mul_one s).symm))
  · intro e1
    have hsi : s⁻¹ = s ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hs3])
    have e2 : z ^ k = s⁻¹ * s⁻¹ := eq_inv_mul_of_mul_eq e1
    have e3 : s⁻¹ * s⁻¹ = s := by
      rw [hsi, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hs3, one_mul]
    exact hsz (by rw [← e3, ← e2]; exact hzk)

theorem move {s : S} (hs : s ∈ Subgroup.closure ({x, y} : Set S)) (hs3 : s ^ 3 = 1)
    (hsz : s ∉ Subgroup.zpowers z) :
    x ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) ∨
      y ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := h.mem_closure_nf3 hs
  by_cases hb0 : b = 0
  · subst hb0
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · refine (hsz ?_).elim
      rw [pow_zero, pow_zero, one_mul, one_mul]
      exact pow_mem (Subgroup.mem_zpowers z) c
    · refine Or.inr (h.moved hs3 hsz ?_ (h.conj_y' a 0 c))
      intro e
      have e' := pow_eq_one_iff_modEq.mp e
      rw [h.orderOf_z, Nat.ModEq] at e'
      omega
  · exact Or.inl (h.moved hs3 hsz
      (fun e => hb0 (h.pow_z_inj hb (by norm_num) (e.trans (pow_zero z).symm))) (h.conj_x a b c))

end HeisRel

end Heis

namespace G24P

open CFSG.LieType.Multipliers.G24 CFSG.Fischer

section Rows

@[expose] noncomputable def wordElt (w : List (Fin 6 × Bool)) : grp :=
  FreeGroup.lift gen (FreeGroup.mk w)

@[expose] noncomputable def rowsOf (x : grp) : Array (Array F4) :=
  ofMat ((x : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4)

theorem toMat_rowsOf (x : grp) :
    toMat 14 (rowsOf x) = ((x : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) :=
  toMat_ofMat _

theorem ofMat_toMat_mulArr' (A B : Array (Array F4)) :
    ofMat (toMat 14 (mulArr 14 A B)) = mulArr 14 A B := by
  rw [toMat_mulArr]
  rfl

theorem ofMat_toMat_wordArr (w : List (Fin 6 × Bool)) :
    ofMat (toMat 14 (wordArr w)) = wordArr w := by
  cases w with
  | nil => exact congrArg ofMat toMat_one14
  | cons l w => exact ofMat_toMat_mulArr' _ _

theorem rowsOf_wordElt (w : List (Fin 6 × Bool)) : rowsOf (wordElt w) = wordArr w := by
  rw [rowsOf, wordElt, coe_lift_gen, val_lift_genGL, ofMat_toMat_wordArr]

@[expose] noncomputable def z0 : grp := wordElt z0Word

@[expose] noncomputable def p1 : grp := wordElt p1Word

@[expose] noncomputable def p2 : grp := wordElt p2Word

theorem rowsOf_z0 : rowsOf z0 = z0Arr () := rowsOf_wordElt _

theorem rowsOf_p1 : rowsOf p1 = p1Arr () := rowsOf_wordElt _

theorem rowsOf_p2 : rowsOf p2 = p2Arr () := rowsOf_wordElt _

@[expose] noncomputable def matHom : grp →* Matrix (Fin 14) (Fin 14) F4 :=
  (Units.coeHom _).comp grp.subtype

theorem matHom_injective : Function.Injective matHom := fun _ _ e => Subtype.ext (Units.ext e)

theorem matHom_eq {x : grp} {A : Array (Array F4)} (hx : rowsOf x = A) :
    matHom x = toMat 14 A := by
  rw [← hx, toMat_rowsOf]
  rfl

end Rows

section Cert

theorem heis : HeisRel p1 p2 z0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Certificates.certificate148012
  have m1 := matHom_eq rowsOf_p1
  have m2 := matHom_eq rowsOf_p2
  have mz := matHom_eq rowsOf_z0
  refine ⟨matHom_injective ?_, matHom_injective ?_, matHom_injective ?_, matHom_injective ?_,
    matHom_injective ?_, fun e => h6 ?_⟩
  · rw [map_pow, map_one, m1, h1]
  · rw [map_pow, map_one, m2, h2]
  · rw [map_mul, map_mul, map_mul, map_pow, map_pow, m1, m2, mz, h3]
  · rw [map_mul, map_mul, m1, mz, h4]
  · rw [map_mul, map_mul, m2, mz, h5]
  · rw [← mz, e, map_one]

theorem exists_P0 : ∃ P0 : Subgroup grp, p1 ∈ P0 ∧ p2 ∈ P0 ∧ Nat.card P0 = 27 :=
  ⟨Subgroup.closure {p1, p2}, Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp), heis.card_closure⟩

theorem z0_cube : z0 ^ 3 = 1 := heis.z_cube

theorem z0_ne_one : z0 ≠ 1 := heis.hz

theorem e9_grp : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers z0 ⊔ Subgroup.zpowers p1) ∧
    Nat.card ↥(Subgroup.zpowers z0 ⊔ Subgroup.zpowers p1) = 9 :=
  e9_of_commute heis.z_cube heis.hz heis.hx heis.hzx heis.x_not_mem

theorem factorization_card_grp :
    (Nat.card grp).factorization 3 = 3 := by
  rw [card_grp, show (251596800 : ℕ) = 3 ^ 3 * 9318400 by norm_num]
  exact Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)

end Cert

section Main

theorem card_le_nine_grp (E : Subgroup grp) (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 _ g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : 3 ^ k ∣ 251596800 := hk ▸ card_grp ▸ Subgroup.card_subgroup_dvd_card E
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have h81 : 3 ^ 4 ∣ 251596800 := (Nat.pow_dvd_pow 3 h).trans hd
    norm_num at h81
  rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | rfl
  · rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  · exfalso
    obtain ⟨P0, hp1, hp2, hcard⟩ := exists_P0
    let Q : Sylow 3 grp := Sylow.ofCard E (by rw [hk, factorization_card_grp])
    let P : Sylow 3 grp := Sylow.ofCard P0 (by rw [hcard, factorization_card_grp]; norm_num)
    haveI : Finite (Sylow 3 grp) := Sylow.finite_of_finiteIndex Q
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq grp P Q
    have hmap : P0.map (MulAut.conj g).toMonoidHom = E := by
      have h := congrArg (fun R : Sylow 3 grp => (R : Subgroup grp)) hg
      simp only [Sylow.coe_subgroup_smul] at h
      exact h
    have h1 : (MulAut.conj g) p1 ∈ E := hmap ▸ ⟨p1, hp1, rfl⟩
    have h2 : (MulAut.conj g) p2 ∈ E := hmap ▸ ⟨p2, hp2, rfl⟩
    have hc := hE.1.is_comm.comm ⟨_, h1⟩ ⟨_, h2⟩
    have hc' : (MulAut.conj g) (p1 * p2) = (MulAut.conj g) (p2 * p1) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val hc
    exact heis.not_comm ((MulAut.conj g).injective hc')

theorem move_P0 (hz : Good427 (Subgroup.centralizer ({z0} : Set grp))) (B : Subgroup grp)
    (hBP : B ≤ Subgroup.closure {p1, p2}) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (s : grp) (hs : s ∈ B) (hs1 : s ≠ 1)
    (hbad : ¬ Good427 (Subgroup.centralizer ({s} : Set grp))) :
    ∃ n ∈ Subgroup.normalizer (B : Set grp),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set grp) := by
  have hcard := heis.card_closure
  have hnorm : Subgroup.closure {p1, p2} ≤ Subgroup.normalizer (B : Set grp) := by
    have hidx : (B.subgroupOf (Subgroup.closure {p1, p2})).index =
        (Nat.card (Subgroup.closure ({p1, p2} : Set grp))).minFac := by
      have h1 := Subgroup.card_mul_index (B.subgroupOf (Subgroup.closure {p1, p2}))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hB9, hcard] at h1
      rw [hcard, show Nat.minFac 27 = 3 by norm_num]
      omega
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp
      (Subgroup.normal_of_index_eq_minFac_card hidx)
  have hs3 : s ^ 3 = 1 := hB.2 s hs
  by_cases hsz : s ∈ Subgroup.zpowers z0
  · refine absurd ?_ hbad
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hsz
    have h3 : ((orderOf z0 : ℕ) : ℤ) = 3 := by rw [heis.orderOf_z]; rfl
    have e : z0 ^ k = z0 ^ (k % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num)), ← h3,
        zpow_mod_orderOf]
    rw [e] at hs1 ⊢
    have hlt : (k % 3).toNat < 3 := by omega
    generalize (k % 3).toNat = i at hlt hs1 ⊢
    interval_cases i
    · exact absurd (pow_zero z0) hs1
    · rw [pow_one]
      exact hz
    · rw [centralizer_pow_of_pow_three z0_cube (Or.inr rfl)]
      exact hz
  · rcases heis.move (hBP hs) hs3 hsz with hm | hm
    · exact ⟨p1, hnorm (Subgroup.subset_closure (by simp)), hm⟩
    · exact ⟨p2, hnorm (Subgroup.subset_closure (by simp)), hm⟩

theorem e9MoveBad_grp (hz : Good427 (Subgroup.centralizer ({z0} : Set grp))) :
    E9MoveBad grp := by
  have hcard := heis.card_closure
  have hP : IsPGroup 3 (Subgroup.closure ({p1, p2} : Set grp)) :=
    IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hidx : ¬ 3 ∣ (Subgroup.closure ({p1, p2} : Set grp)).index := by
    have h := (Subgroup.closure ({p1, p2} : Set grp)).card_mul_index
    rw [hcard, card_grp] at h
    have hi : (Subgroup.closure ({p1, p2} : Set grp)).index = 9318400 := by omega
    rw [hi]
    norm_num
  exact e9MoveBad_of_sylow hP hidx fun B hBP hB hB9 s hs hs1 hbad =>
    move_P0 hz B hBP hB hB9 s hs hs1 hbad

end Main

end G24P

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
