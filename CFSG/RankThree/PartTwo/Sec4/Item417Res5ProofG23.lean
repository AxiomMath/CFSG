module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCover
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import Certificates.Data.R3E417.G23
public import Certificates.Certificate8176
public import Certificates.Certificate8007
public import Certificates.Certificate8008
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Five

namespace G23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)
local notation "GL14" => GL (Fin 14) (ZMod 3)

theorem getD_map_range {α : Type} (f : ℕ → α) (n : ℕ) (d : α) {i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem entR_mulR (a b : List (List ℕ)) {i j : ℕ} (hi : i < 14) (hj : j < 14) :
    entR (mulR a b) i j = ((List.range 14).map fun k => entR a i k * entR b k j).sum % 3 := by
  rw [entR, mulR, getD_map_range _ _ _ hi, getD_map_range _ _ _ hj]

theorem decR_mulR (a b : List (List ℕ)) : decR (mulR a b) = decR a * decR b := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [decR, Matrix.of_apply]
  rw [entR_mulR a b i.2 j.2, ZMod.natCast_mod, Nat.cast_list_sum, List.map_map, list_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Nat.cast_mul]

@[expose] noncomputable def toM : H3 →* M14 :=
  (Units.coeHom M14).comp R3.subtype

theorem toM_injective : Function.Injective toM :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem coeR_mul {g h : GL14} {c d : List (List ℕ)} (hg : (g : M14) = decR c)
    (hh : (h : M14) = decR d) : ((g * h : GL14) : M14) = decR (mulR c d) := by
  rw [Units.val_mul, hg, hh, decR_mulR]

theorem coeR_sq {g : GL14} {c : List (List ℕ)} (hg : (g : M14) = decR c) :
    ((g ^ 2 : GL14) : M14) = decR (mulR c c) := by
  rw [pow_two]
  exact coeR_mul hg hg

theorem toM_mul {g h : H3} {c d : List (List ℕ)} (hg : toM g = decR c) (hh : toM h = decR d) :
    toM (g * h) = decR (mulR c d) := by
  rw [map_mul, hg, hh, decR_mulR]

theorem toM_pow_three {g : H3} {c : List (List ℕ)} (hg : toM g = decR c) :
    toM (g ^ 3) = decR (mulR (mulR c c) c) := by
  rw [map_pow, hg, pow_succ, pow_two, ← decR_mulR, ← decR_mulR]

theorem mul_eq_mul_of_rows {g h k l : H3} {cg ch ck cl : List (List ℕ)}
    (hg : toM g = decR cg) (hh : toM h = decR ch) (hk : toM k = decR ck) (hl : toM l = decR cl)
    (e : mulR cg ch = mulR ck cl) : g * h = k * l :=
  toM_injective (by rw [toM_mul hg hh, toM_mul hk hl, e])

theorem col_mul (A B : M14) (c : Fin 14) (hB : ∀ r, B r c = (1 : M14) r c) (r : Fin 14) :
    (A * B) r c = A r c := by
  rw [Matrix.mul_apply]
  simp_rw [hB]
  rw [← Matrix.mul_apply, Matrix.mul_one]

@[expose] noncomputable def fixCol (c : Fin 14) : Subgroup H3 where
  carrier := {g | ∀ r, toM g r c = (1 : M14) r c}
  one_mem' := by
    intro r
    rw [map_one]
  mul_mem' := by
    intro g h hg hh r
    have hg' : ∀ r, toM g r c = (1 : M14) r c := hg
    have hh' : ∀ r, toM h r c = (1 : M14) r c := hh
    rw [map_mul, col_mul _ _ c hh', hg']
  inv_mem' := by
    intro g hg r
    have hg' : ∀ r, toM g r c = (1 : M14) r c := hg
    have h1 : toM g⁻¹ * toM g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [← col_mul (toM g⁻¹) (toM g) c hg' r, h1]

theorem mem_fixCol_of_rows {g : H3} {cg : List (List ℕ)} (hg : toM g = decR cg) {c : Fin 14}
    (h : ∀ r : Fin 14, decR cg r c = (1 : M14) r c) : g ∈ fixCol c := by
  show ∀ r, toM g r c = (1 : M14) r c
  rw [hg]
  exact h

theorem not_mem_fixCol_of_rows {g : H3} {cg : List (List ℕ)} (hg : toM g = decR cg)
    {c : Fin 14} (h : ¬ ∀ r : Fin 14, decR cg r c = (1 : M14) r c) : g ∉ fixCol c := by
  intro hm
  apply h
  have hm' : ∀ r, toM g r c = (1 : M14) r c := hm
  rw [hg] at hm'
  exact hm'

theorem ne_one_of_not_mem_fixCol {g : H3} {c : Fin 14} (h : g ∉ fixCol c) : g ≠ 1 :=
  fun h1 => h (h1 ▸ (fixCol c).one_mem)

theorem comm_of_le_centralizer {G : Type} [Group G] {E : Subgroup G} {x : G}
    (h : E ≤ Subgroup.centralizer {x}) : ∀ a ∈ E, a * x = x * a :=
  fun _ ha => Subgroup.mem_centralizer_singleton_iff.mp (h ha)

theorem comm_zpowers_of_le_centralizer {G : Type} [Group G] {E : Subgroup G} {x : G}
    (h : E ≤ Subgroup.centralizer {x}) : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_right (comm_of_le_centralizer h a ha) k).eq

theorem isPGroup_zpowers_of_pow_four {g : H3} (hg : g ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact orderOf_dvd_of_pow_eq_one hg
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])

section Checks


theorem decR_oneR : decR oneR = 1 :=
  Certificates.certificate8176.1

theorem dec14_x0c : dec14 x0c = decR x0r :=
  Certificates.certificate8176.2.1.1

theorem dec14_x1c : dec14 x1c = decR x1r :=
  Certificates.certificate8176.2.1.2.1

theorem dec14_y0c : dec14 y0c = decR y0r :=
  Certificates.certificate8176.2.1.2.2.1

theorem dec14_y1c : dec14 y1c = decR y1r :=
  Certificates.certificate8176.2.1.2.2.2

theorem uR_eq : mulR (mulR (mulR (n0R ()) (n1R ())) x0r) (mulR (n1iR ()) (n0iR ())) = uLit :=
  Certificates.certificate8176.2.2.1

theorem x13R_eq : mulR (mulR (n1R ()) x0r) (n1iR ()) = x13Lit :=
  Certificates.certificate8176.2.2.2.1

theorem x12R_eq : mulR (mulR (n1R ()) (mulR (mulR (n0R ()) x1r) (n0iR ()))) (n1iR ()) = x12Lit :=
  Certificates.certificate8176.2.2.2.2.1

theorem iR_eq : mulR x1r y1r = iLit :=
  Certificates.certificate8176.2.2.2.2.2.1

theorem jR_eq : mulR y1r x1r = jLit :=
  Certificates.certificate8176.2.2.2.2.2.2.1

theorem cubes : mulR (mulR x1r x1r) x1r = oneR ∧ mulR (mulR uLit uLit) uLit = oneR ∧
    mulR (mulR x13Lit x13Lit) x13Lit = oneR ∧ mulR (mulR x12Lit x12Lit) x12Lit = oneR :=
  Certificates.certificate8176.2.2.2.2.2.2.2.1

theorem comms : mulR x13Lit x12Lit = mulR x12Lit x13Lit ∧
    mulR x13Lit uLit = mulR uLit x13Lit ∧ mulR x12Lit uLit = mulR uLit x12Lit ∧
    mulR x13Lit x1r = mulR x1r x13Lit ∧ mulR x12Lit x1r = mulR x1r x12Lit ∧
    mulR uLit x1r = mulR x1r uLit :=
  Certificates.certificate8176.2.2.2.2.2.2.2.2.1

theorem q8_rels : mulR (mulR (mulR iLit iLit) iLit) iLit = oneR ∧
    mulR (mulR (mulR jLit jLit) jLit) jLit = oneR ∧
    mulR jLit iLit = mulR (mulR (mulR iLit iLit) iLit) jLit :=
  Certificates.certificate8176.2.2.2.2.2.2.2.2.2.1

theorem xa_rels : mulR x1r jLit = mulR iLit x1r ∧
    mulR x1r iLit = mulR (mulR (mulR (mulR iLit jLit) jLit) jLit) x1r :=
  Certificates.certificate8176.2.2.2.2.2.2.2.2.2.2.1

theorem u_rels : mulR uLit iLit = mulR iLit uLit ∧ mulR uLit jLit = mulR jLit uLit :=
  Certificates.certificate8176.2.2.2.2.2.2.2.2.2.2.2.1

theorem xa_i_entries : entR (mulR x1r iLit) 1 1 = 0 ∧ entR (mulR iLit x1r) 1 1 = 2 :=
  Certificates.certificate8176.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cols :
    (∀ r : Fin 14, decR x1r r 13 = (1 : M14) r 13) ∧
    ¬ (∀ r : Fin 14, decR uLit r 13 = (1 : M14) r 13) ∧
    ¬ (∀ r : Fin 14, decR x13Lit r 5 = (1 : M14) r 5) ∧
    (∀ r : Fin 14, decR x13Lit r 10 = (1 : M14) r 10) ∧
    ¬ (∀ r : Fin 14, decR x12Lit r 10 = (1 : M14) r 10) ∧
    (∀ r : Fin 14, decR x13Lit r 8 = (1 : M14) r 8) ∧
    (∀ r : Fin 14, decR x12Lit r 8 = (1 : M14) r 8) ∧
    ¬ (∀ r : Fin 14, decR uLit r 8 = (1 : M14) r 8) ∧
    (∀ r : Fin 14, decR x13Lit r 3 = (1 : M14) r 3) ∧
    (∀ r : Fin 14, decR x12Lit r 3 = (1 : M14) r 3) ∧
    (∀ r : Fin 14, decR uLit r 3 = (1 : M14) r 3) ∧
    ¬ (∀ r : Fin 14, decR x1r r 3 = (1 : M14) r 3) :=
  Certificates.certificate8176.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem pow_three_of_rows {g : H3} {c : List (List ℕ)} (hg : toM g = decR c)
    (e : mulR (mulR c c) c = oneR) : g ^ 3 = 1 :=
  toM_injective (by rw [toM_pow_three hg, e, decR_oneR, map_one])

theorem pow_four_of_rows {g : H3} {c : List (List ℕ)} (hg : toM g = decR c)
    (e : mulR (mulR (mulR c c) c) c = oneR) : g ^ 4 = 1 :=
  toM_injective (by
    rw [pow_succ, toM_mul (toM_pow_three hg) hg, e, decR_oneR, map_one])

end Checks

section Elements


theorem mem_n0iU : n0iU ∈ R3 :=
  mul_mem (mul_mem (pow_mem (gX_mem 0) 2) (gY_mem 0)) (pow_mem (gX_mem 0) 2)

theorem mem_n1iU : n1iU ∈ R3 :=
  mul_mem (mul_mem (pow_mem (gX_mem 1) 2) (gY_mem 1)) (pow_mem (gX_mem 1) 2)

@[expose] noncomputable def xa : H3 :=
  ⟨gX 1, gX_mem 1⟩

@[expose] noncomputable def xu : H3 :=
  ⟨uU, uU_mem⟩

@[expose] noncomputable def x13 : H3 :=
  ⟨n1U * gX 0 * n1iU, mul_mem (mul_mem n1U_mem (gX_mem 0)) mem_n1iU⟩

@[expose] noncomputable def x12 : H3 :=
  ⟨n1U * (n0U * gX 1 * n0iU) * n1iU,
    mul_mem (mul_mem n1U_mem (mul_mem (mul_mem n0U_mem (gX_mem 1)) mem_n0iU)) mem_n1iU⟩

@[expose] noncomputable def qi : H3 :=
  ⟨gX 1 * gY 1, mul_mem (gX_mem 1) (gY_mem 1)⟩

@[expose] noncomputable def qj : H3 :=
  ⟨gY 1 * gX 1, mul_mem (gY_mem 1) (gX_mem 1)⟩

@[expose] noncomputable def e9' : Subgroup H3 :=
  Subgroup.zpowers x13 ⊔ Subgroup.zpowers x12

@[expose] noncomputable def e27 : Subgroup H3 :=
  e9' ⊔ Subgroup.zpowers xu

@[expose] noncomputable def e81 : Subgroup H3 :=
  e27 ⊔ Subgroup.zpowers xa

@[expose] noncomputable def e9 : Subgroup H3 :=
  Subgroup.zpowers xa ⊔ Subgroup.zpowers xu

@[expose] noncomputable def q8 : Subgroup H3 :=
  Subgroup.zpowers qj ⊔ Subgroup.zpowers qi

theorem e9_le_e81 : e9 ≤ e81 :=
  sup_le le_sup_right ((le_sup_right : Subgroup.zpowers xu ≤ e27).trans le_sup_left)

end Elements

section Relations


theorem coeR_gX0 : (gX 0 : M14) = decR x0r :=
  coe_gX0.trans dec14_x0c

theorem coeR_gX1 : (gX 1 : M14) = decR x1r :=
  coe_gX1.trans dec14_x1c

theorem coeR_gY0 : (gY 0 : M14) = decR y0r :=
  coe_gY0.trans dec14_y0c

theorem coeR_gY1 : (gY 1 : M14) = decR y1r :=
  coe_gY1.trans dec14_y1c

theorem coeR_n0U : (n0U : M14) = decR (n0R ()) :=
  coeR_mul (coeR_mul coeR_gX0 (coeR_sq coeR_gY0)) coeR_gX0

theorem coeR_n1U : (n1U : M14) = decR (n1R ()) :=
  coeR_mul (coeR_mul coeR_gX1 (coeR_sq coeR_gY1)) coeR_gX1

theorem coeR_n0iU : (n0iU : M14) = decR (n0iR ()) :=
  coeR_mul (coeR_mul (coeR_sq coeR_gX0) coeR_gY0) (coeR_sq coeR_gX0)

theorem coeR_n1iU : (n1iU : M14) = decR (n1iR ()) :=
  coeR_mul (coeR_mul (coeR_sq coeR_gX1) coeR_gY1) (coeR_sq coeR_gX1)

theorem toM_xa : toM xa = decR x1r :=
  coeR_gX1

theorem toM_xu : toM xu = decR uLit := by
  rw [← uR_eq]
  exact coeR_mul (coeR_mul (coeR_mul coeR_n0U coeR_n1U) coeR_gX0) (coeR_mul coeR_n1iU coeR_n0iU)

theorem toM_x13 : toM x13 = decR x13Lit := by
  rw [← x13R_eq]
  exact coeR_mul (coeR_mul coeR_n1U coeR_gX0) coeR_n1iU

theorem toM_x12 : toM x12 = decR x12Lit := by
  rw [← x12R_eq]
  exact coeR_mul (coeR_mul coeR_n1U (coeR_mul (coeR_mul coeR_n0U coeR_gX1) coeR_n0iU)) coeR_n1iU

theorem toM_qi : toM qi = decR iLit := by
  rw [← iR_eq]
  exact coeR_mul coeR_gX1 coeR_gY1

theorem toM_qj : toM qj = decR jLit := by
  rw [← jR_eq]
  exact coeR_mul coeR_gY1 coeR_gX1

theorem orderOf_x13 : orderOf x13 = 3 :=
  orderOf_eq_prime (pow_three_of_rows toM_x13 cubes.2.2.1)
    (ne_one_of_not_mem_fixCol (not_mem_fixCol_of_rows toM_x13 cols.2.2.1))

theorem orderOf_x12 : orderOf x12 = 3 :=
  orderOf_eq_prime (pow_three_of_rows toM_x12 cubes.2.2.2)
    (ne_one_of_not_mem_fixCol (not_mem_fixCol_of_rows toM_x12 cols.2.2.2.2.1))

theorem orderOf_xu : orderOf xu = 3 :=
  orderOf_eq_prime (pow_three_of_rows toM_xu cubes.2.1)
    (ne_one_of_not_mem_fixCol (not_mem_fixCol_of_rows toM_xu cols.2.1))

theorem orderOf_xa : orderOf xa = 3 :=
  orderOf_eq_prime (pow_three_of_rows toM_xa cubes.1)
    (ne_one_of_not_mem_fixCol (not_mem_fixCol_of_rows toM_xa cols.2.2.2.2.2.2.2.2.2.2.2))

theorem zpowers_x13_le : Subgroup.zpowers x13 ≤ Subgroup.centralizer {x12} :=
  Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_eq_mul_of_rows toM_x13 toM_x12 toM_x12 toM_x13 comms.1))

theorem e9'_le : e9' ≤ Subgroup.centralizer {xu} :=
  sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows toM_x13 toM_xu toM_xu toM_x13 comms.2.1)))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows toM_x12 toM_xu toM_xu toM_x12 comms.2.2.1)))

theorem e27_le : e27 ≤ Subgroup.centralizer {xa} :=
  sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows toM_x13 toM_xa toM_xa toM_x13 comms.2.2.2.1)))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows toM_x12 toM_xa toM_xa toM_x12 comms.2.2.2.2.1))))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows toM_xu toM_xa toM_xa toM_xu comms.2.2.2.2.2)))

theorem zpowers_xa_le : Subgroup.zpowers xa ≤ Subgroup.centralizer {xu} :=
  Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_eq_mul_of_rows toM_xu toM_xa toM_xa toM_xu comms.2.2.2.2.2).symm)

theorem x12_not_mem : x12 ∉ Subgroup.zpowers x13 := fun h =>
  not_mem_fixCol_of_rows toM_x12 cols.2.2.2.2.1
    (Subgroup.zpowers_le.mpr (mem_fixCol_of_rows toM_x13 cols.2.2.2.1) h)

theorem xu_not_mem : xu ∉ e9' := fun h =>
  not_mem_fixCol_of_rows toM_xu cols.2.2.2.2.2.2.2.1
    (sup_le (Subgroup.zpowers_le.mpr (mem_fixCol_of_rows toM_x13 cols.2.2.2.2.2.1))
      (Subgroup.zpowers_le.mpr (mem_fixCol_of_rows toM_x12 cols.2.2.2.2.2.2.1)) h)

theorem xa_not_mem : xa ∉ e27 := fun h =>
  not_mem_fixCol_of_rows toM_xa cols.2.2.2.2.2.2.2.2.2.2.2
    (sup_le (sup_le (Subgroup.zpowers_le.mpr (mem_fixCol_of_rows toM_x13 cols.2.2.2.2.2.2.2.2.1))
      (Subgroup.zpowers_le.mpr (mem_fixCol_of_rows toM_x12 cols.2.2.2.2.2.2.2.2.2.1)))
      (Subgroup.zpowers_le.mpr (mem_fixCol_of_rows toM_xu cols.2.2.2.2.2.2.2.2.2.2.1)) h)

theorem xu_not_mem_xa : xu ∉ Subgroup.zpowers xa := fun h =>
  not_mem_fixCol_of_rows toM_xu cols.2.1
    (Subgroup.zpowers_le.mpr (mem_fixCol_of_rows toM_xa cols.1) h)

theorem card_e81 : Nat.card e81 = 3 ^ 4 := by
  rw [e81, card_sup_zpowers_eq_three_mul orderOf_xa xa_not_mem
      (comm_zpowers_of_le_centralizer e27_le), e27,
    card_sup_zpowers_eq_three_mul orderOf_xu xu_not_mem (comm_zpowers_of_le_centralizer e9'_le),
    e9', card_sup_zpowers_eq_three_mul orderOf_x12 x12_not_mem
      (comm_zpowers_of_le_centralizer zpowers_x13_le), Nat.card_zpowers, orderOf_x13]
  norm_num

theorem card_e9 : Nat.card e9 = 9 := by
  rw [e9, card_sup_zpowers_eq_three_mul orderOf_xu xu_not_mem_xa
      (comm_zpowers_of_le_centralizer zpowers_xa_le), Nat.card_zpowers, orderOf_xa]

theorem isElemAbelian_e81 : CFSG.Assembly.IsElemAbelian 3 e81 := by
  have h1 : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x13) := by
    rw [Subgroup.zpowers_eq_closure]
    refine isElemAbelian_closure_of_commute ?_ ?_
    · intro x hx y hy
      rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
      exact Commute.refl _
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact pow_three_of_rows toM_x13 cubes.2.2.1
  have h2 : CFSG.Assembly.IsElemAbelian 3 e9' :=
    isElemAbelian_sup_zpowers_cube h1 (pow_three_of_rows toM_x12 cubes.2.2.2)
      (comm_of_le_centralizer zpowers_x13_le)
  have h3 : CFSG.Assembly.IsElemAbelian 3 e27 :=
    isElemAbelian_sup_zpowers_cube h2 (pow_three_of_rows toM_xu cubes.2.1)
      (comm_of_le_centralizer e9'_le)
  exact isElemAbelian_sup_zpowers_cube h3 (pow_three_of_rows toM_xa cubes.1)
    (comm_of_le_centralizer e27_le)

theorem qj_qi : qj * qi = qi ^ 3 * qj :=
  toM_injective (by rw [toM_mul toM_qj toM_qi, toM_mul (toM_pow_three toM_qi) toM_qj,
    q8_rels.2.2])

theorem xa_qj : xa * qj = qi * xa :=
  mul_eq_mul_of_rows toM_xa toM_qj toM_qi toM_xa xa_rels.1

theorem xa_qi : xa * qi = qi * qj * qj * qj * xa :=
  mul_eq_mul_of_rows toM_xa toM_qi (toM_mul (toM_mul (toM_mul toM_qi toM_qj) toM_qj) toM_qj)
    toM_xa xa_rels.2

theorem xa_qi_ne : xa * qi ≠ qi * xa := by
  intro h
  have h1 := congrArg toM h
  rw [toM_mul toM_xa toM_qi, toM_mul toM_qi toM_xa] at h1
  have h2 := congrFun (congrFun h1 1) 1
  simp only [decR, Matrix.of_apply] at h2
  rw [show ((1 : Fin 14) : ℕ) = 1 from rfl, xa_i_entries.1, xa_i_entries.2] at h2
  exact absurd h2 (by decide)

theorem isPGroup_q8 : IsPGroup 2 q8 := by
  refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_four
    (pow_four_of_rows toM_qj q8_rels.2.1)) (isPGroup_zpowers_of_pow_four
    (pow_four_of_rows toM_qi q8_rels.1)) (Subgroup.zpowers_le.mpr ?_)
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have h : qj * qi * qj⁻¹ = qi ^ 3 := by rw [qj_qi, mul_inv_cancel_right]
  rw [← conj_zpow, h]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers qi) 3) k

theorem xa_mem_normalizer : xa ∈ Subgroup.normalizer (q8 : Set H3) := by
  have hi : qi ∈ q8 := Subgroup.mem_sup_right (Subgroup.mem_zpowers qi)
  have hj : qj ∈ q8 := Subgroup.mem_sup_left (Subgroup.mem_zpowers qj)
  have hle : q8 ≤ q8.comap (MulAut.conj xa).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, xa_qj,
        mul_inv_cancel_right]
      exact hi
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, xa_qi,
        mul_inv_cancel_right]
      exact q8.mul_mem (q8.mul_mem (q8.mul_mem hi hj) hj) hj
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

theorem xu_mem_normalizer : xu ∈ Subgroup.normalizer (q8 : Set H3) := by
  have hle : q8 ≤ Subgroup.centralizer {xu} :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_eq_mul_of_rows toM_xu toM_qj toM_qj toM_xu u_rels.2).symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_eq_mul_of_rows toM_xu toM_qi toM_qi toM_xu u_rels.1).symm))
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have h : n * xu = xu * n := (Subgroup.mem_centralizer_singleton_iff (G := H3)).mp (hle hn)
  rw [← h, mul_inv_cancel_right]
  exact hn

theorem e81_data_R3 : ∃ P E₀ T₀ : Subgroup H3, CFSG.Assembly.IsElemAbelian 3 P ∧
    Nat.card P = 3 ^ 4 ∧ E₀ ≤ P ∧ Nat.card E₀ = 9 ∧ IsPGroup 2 T₀ ∧
    E₀ ≤ Subgroup.normalizer (T₀ : Set H3) ∧ ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set H3) := by
  refine ⟨e81, e9, q8, isElemAbelian_e81, card_e81, e9_le_e81, card_e9, isPGroup_q8,
    sup_le (Subgroup.zpowers_le.mpr xa_mem_normalizer)
      (Subgroup.zpowers_le.mpr xu_mem_normalizer), fun h => xa_qi_ne ?_⟩
  exact Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers qi))) xa
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers xa))

end Relations

end G23

theorem k417E81G23_holds :
    K417E81G23 := by
  intro X _ hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hK, pow_one, ZMod.card]
  let ψ : X ≃* Census.Carrier.G2Three.H3 :=
    (e.trans (CFSG.TauCetiBridge.adjointQuotientCongr
      (FiniteField.ringEquivOfCardEq hcardK))).trans Census.Carrier.G2Three.adjointQuotientEquivR3
  obtain ⟨P, E₀, T₀, h1, h2, h3, h4, h5, h6, h7⟩ := G23.e81_data_R3
  exact ⟨_, _, _, e81_data_map (ψ.symm : Census.Carrier.G2Three.H3 →* X) ψ.symm.injective h1 h2
    h3 h4 h5 h6 h7⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Five
