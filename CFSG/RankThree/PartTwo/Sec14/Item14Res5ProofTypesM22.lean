module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypes
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGen
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Res5TypesM22

open CFSG.RankThree.PartTwo.KFacts.KP4


theorem map_V_eq {τ : MulAut G22} {i : Fin 4} (hτ : τ (lineE i) = lineE i) :
    (V i).map τ.toMonoidHom = V i := by
  rw [← pCore_centralizer_line, KFacts.KS14.map_inSubgroup_pCore_two,
    CFSG.RankThree.PartTwo.map_centralizer_singleton, hτ]

theorem pow_apply_ne {X : Type*} [Group X] {τ : MulAut X} {a : X}
    (h3 : (τ ^ 3) a = a) (h1 : τ a ≠ a) (h2 : (τ ^ 2) a ≠ a) {n : ℕ} (hn : ¬ 3 ∣ n) :
    (τ ^ n) a ≠ a := by
  have hk : ∀ m r : ℕ, (τ ^ (3 * m + r)) a = (τ ^ r) a := by
    intro m r
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 3 * (m + 1) + r = 3 + (3 * m + r) by ring, pow_add, MulAut.mul_apply, ih]
      rw [show (τ ^ 3) ((τ ^ r) a) = (τ ^ r) ((τ ^ 3) a) by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm], h3]
  have hn' : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  have hr : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [hn', hk]
  rcases hr with hr | hr <;> rw [hr]
  · simpa using h1
  · exact h2

theorem fix_V {τ : MulAut G22} (hτ : ∀ p ∈ P0, τ p = p) {n : ℕ} (hn : ¬ 3 ∣ n)
    (hτn : τ ^ n = 1) (i : Fin 4) : τ (vAE i) = vAE i ∧ τ (vBE i) = vBE i := by
  set a := vAE i with ha
  set b := vBE i with hb
  have haa : a * a = 1 := vAE_sq i
  have hbb : b * b = 1 := vBE_sq i
  have hab : a * b = b * a := vAE_vBE_comm i
  have ha1 : a ≠ 1 := vAE_ne_one i
  have hb1 : b ≠ 1 := vBE_ne_one i
  have hne : a ≠ b := vAE_ne_vBE i
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  obtain ⟨t, htP, hta, htb⟩ := exists_tw i
  have hτt : τ t = t := hτ t htP
  have hVi : ∀ v ∈ V i, τ v ∈ V i := fun v hv => by
    rw [← map_V_eq (hτ _ (lineE_mem_P0 i))]
    exact ⟨v, hv, rfl⟩
  have hconj : ∀ v, τ (t * v * t⁻¹) = t * τ v * t⁻¹ := fun v => by
    rw [map_mul, map_mul, map_inv, hτt]
  have hτab : τ (a * b) = t * τ a * t⁻¹ := by rw [← hta, hconj]
  have hτa' : τ a = t * τ b * t⁻¹ := by rw [← hconj, htb]
  have hτb : τ b = (τ a)⁻¹ * τ (a * b) := by rw [map_mul]; group
  have hτa1 : τ a ≠ 1 := fun h => ha1 (τ.injective (h.trans (map_one τ).symm))
  have hτaV := hVi a (mem_V_iff.mpr (Or.inr (Or.inl rfl)))
  rcases mem_V_iff.mp hτaV with h | h | h | h
  · exact absurd h hτa1
  ·
    refine ⟨h, ?_⟩
    rw [hτb, hτab, h, hta, hainv, ← mul_assoc, haa, one_mul]
  ·
    exfalso
    have h2 : τ (a * b) = a := by rw [hτab, h, htb]
    have h3 : τ b = a * b := by rw [hτb, h, h2, hbinv, hab]
    have hpow2 : (τ ^ 2) a = a * b := by rw [pow_two, MulAut.mul_apply, h, h3]
    have hpow3 : (τ ^ 3) a = a := by
      rw [pow_succ, MulAut.mul_apply, h, pow_two, MulAut.mul_apply, h3, h2]
    have hfix : (τ ^ n) a = a := by rw [hτn, MulAut.one_apply]
    refine pow_apply_ne hpow3 (by rw [h]; exact hne.symm) ?_ hn hfix
    rw [hpow2]
    intro h'
    apply hb1
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h', inv_mul_cancel]
  ·
    exfalso
    have h2 : τ (a * b) = b := by
      rw [hτab, h, ← mul_assoc, show t * a * b = (t * a * t⁻¹) * (t * b * t⁻¹) * t by group,
        hta, htb, mul_assoc a b a, ← hab, ← mul_assoc, haa, one_mul, mul_assoc, mul_inv_cancel,
        mul_one]
    have h3 : τ b = a := by
      rw [hτb, h, h2, mul_inv_rev, hbinv, hainv]
      calc b * a * b = a * b * b := by rw [← hab]
        _ = a := by rw [mul_assoc, hbb, mul_one]
    have hpow2 : (τ ^ 2) a = b := by rw [pow_two, MulAut.mul_apply, h, h2]
    have hpow3 : (τ ^ 3) a = a := by
      rw [pow_succ, MulAut.mul_apply, h, pow_two, MulAut.mul_apply, h2, h3]
    have hfix : (τ ^ n) a = a := by rw [hτn, MulAut.one_apply]
    refine pow_apply_ne hpow3 ?_ (by rw [hpow2]; exact hne.symm) hn hfix
    rw [h]
    intro h'
    apply hb1
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h', inv_mul_cancel]

theorem aut_eq_one_G22 {τ : MulAut G22} (hτ : ∀ p ∈ P0, τ p = p) {n : ℕ} (hn : ¬ 3 ∣ n)
    (hτn : τ ^ n = 1) : τ = 1 := by
  set F : Subgroup G22 :=
    { carrier := {g | τ g = g}
      mul_mem' := fun {x y} hx hy => by
        change τ (x * y) = x * y
        rw [map_mul, show τ x = x from hx, show τ y = y from hy]
      one_mem' := map_one τ
      inv_mem' := fun {x} hx => by
        change τ x⁻¹ = x⁻¹
        rw [map_inv, show τ x = x from hx] } with hF
  have hVF : ∀ i, V i ≤ F := by
    intro i
    rw [← V_eq_closure, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact (fix_V hτ hn hτn i).1
    · exact (fix_V hτ hn hτn i).2
  have htop : (⊤ : Subgroup G22) ≤ F := by
    rw [← Res5Gen.iSup_V_eq_top]
    exact iSup_le hVF
  exact MulEquiv.ext fun g => htop (Subgroup.mem_top g)

theorem isElemAbelian_P0 : CFSG.Assembly.IsElemAbelian 3 P0 := by
  have hXY : Commute CFSG.RankThree.Asc83Table.M22.X CFSG.RankThree.Asc83Table.M22.Y :=
    CFSG.RankThree.Asc83Table.M22.XY_comm
  have hX3 : CFSG.RankThree.Asc83Table.M22.X ^ 3 = 1 := CFSG.RankThree.Asc83Table.M22.X_cube
  have hY3 : CFSG.RankThree.Asc83Table.M22.Y ^ 3 = 1 := CFSG.RankThree.Asc83Table.M22.Y_cube
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun g hg => ?_⟩
  · obtain ⟨a, b, -, -, hab⟩ := CFSG.RankThree.Asc83Table.M22.E.exists_pow_mul_pow u.2
    obtain ⟨a', b', -, -, hab'⟩ := CFSG.RankThree.Asc83Table.M22.E.exists_pow_mul_pow v.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hab, hab']
    exact (((Commute.pow_pow_self _ a a').mul_right (hXY.pow_pow a b')).mul_left
      (((hXY.pow_pow a' b).symm).mul_right (Commute.pow_pow_self _ b b'))).eq
  · obtain ⟨a, b, -, -, rfl⟩ := CFSG.RankThree.Asc83Table.M22.E.exists_pow_mul_pow hg
    rw [CFSG.RankThree.Asc83Table.M22.E_a, CFSG.RankThree.Asc83Table.M22.E_b,
      (hXY.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul,
      pow_mul, hX3, hY3, one_pow, one_pow, one_mul]

theorem nine_le_card_P0 : 3 ^ 2 ≤ Nat.card P0 := by
  rw [card_P0]
  norm_num

theorem nonhexad_facts : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
    ((vA i * vA j) ^ 2) ^ 3 = 1 ∧ (vA i * vA j) ^ 2 ≠ 1 := by
  decide +kernel

theorem hexad_comm : ∀ i j : Fin 4, (i, j) = (0, 1) ∨ (i, j) = (2, 3) →
    vA i * vA j = vA j * vA i ∧ vA i * vB j = vB j * vA i ∧ vB i * vA j = vA j * vB i ∧
      vB i * vB j = vB j * vB i := by
  decide +kernel

theorem hexad_disj : ∀ i j : Fin 4, (i, j) = (0, 1) ∨ (i, j) = (2, 3) →
    (vA i ≠ vA j ∧ vA i ≠ vB j ∧ vA i ≠ vA j * vB j) ∧
      (vB i ≠ vA j ∧ vB i ≠ vB j ∧ vB i ≠ vA j * vB j) ∧
      (vA i * vB i ≠ vA j ∧ vA i * vB i ≠ vB j ∧ vA i * vB i ≠ vA j * vB j) := by
  decide +kernel

theorem le_hexad {Yg : Subgroup G22} (hY3 : ¬ 3 ∣ Nat.card Yg)
    (hY : P0 ≤ Subgroup.normalizer (Yg : Set G22)) :
    Yg ≤ V 0 ⊔ V 1 ∨ Yg ≤ V 2 ⊔ V 3 := by
  have hP0ab := isElemAbelian_P0
  have hcap : ∀ i, Yg ⊓ Subgroup.centralizer ({lineE i} : Set G22) = ⊥ ∨
      Yg ⊓ Subgroup.centralizer ({lineE i} : Set G22) = V i := by
    intro i
    have h3 : ¬ 3 ∣ Nat.card (Yg ⊓ Subgroup.centralizer ({lineE i} : Set G22) : Subgroup G22) :=
      fun h => hY3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hPC : P0 ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({lineE i} : Set G22) : Subgroup G22) : Set G22) :=
      le_trans (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hP0ab.1.is_comm.comm ⟨p, hp⟩ ⟨lineE i, lineE_mem_P0 i⟩)))
        Subgroup.le_normalizer
    exact V_minimal i (le_V_of_not_dvd inf_le_right h3) (Late.le_normalizer_inf hY hPC)
  have hno : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val → V i ≤ Yg → V j ≤ Yg → False := by
    intro i j hi hj hVi hVj
    have hA : ∀ k, vAE k ∈ V k := fun k => mem_V_iff.mpr (Or.inr (Or.inl rfl))
    have hmem : (vAE i * vAE j) ^ 2 ∈ Yg := pow_mem (mul_mem (hVi (hA i)) (hVj (hA j))) 2
    obtain ⟨h3, h1⟩ := nonhexad_facts i j hi hj
    have ho : orderOf ((vAE i * vAE j) ^ 2) = 3 :=
      orderOf_eq_prime (Subtype.ext h3) (fun h => h1 (congrArg Subtype.val h))
    exact hY3 (ho ▸ Subgroup.orderOf_dvd_natCard Yg hmem)
  have hgen : ∀ M : Subgroup G22, (∀ i, V i ≤ Yg → V i ≤ M) → Yg ≤ M := by
    intro M hM
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hP0ab nine_le_card_P0 hY
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3) fun e he he1 => ?_
    obtain ⟨i, hi⟩ := exists_centralizer_eq he he1
    rw [hi]
    rcases hcap i with h | h
    · rw [h]
      exact bot_le
    · rw [h]
      exact hM i (h ▸ inf_le_left)
  by_cases h23 : V 2 ≤ Yg ∨ V 3 ≤ Yg
  · right
    refine hgen _ fun i hi => ?_
    fin_cases i
    · exfalso
      rcases h23 with h | h
      · exact hno 0 2 (by decide) (by decide) hi h
      · exact hno 0 3 (by decide) (by decide) hi h
    · exfalso
      rcases h23 with h | h
      · exact hno 1 2 (by decide) (by decide) hi h
      · exact hno 1 3 (by decide) (by decide) hi h
    · exact le_sup_left
    · exact le_sup_right
  · left
    push Not at h23
    refine hgen _ fun i hi => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
    · exact absurd hi h23.1
    · exact absurd hi h23.2

theorem commute_of_mem_V {x : G22} {j : Fin 4} (hA : x * vAE j = vAE j * x)
    (hB : x * vBE j = vBE j * x) {w : G22} (hw : w ∈ V j) : x * w = w * x := by
  rcases mem_V_iff.mp hw with rfl | rfl | rfl | rfl
  · rw [mul_one, one_mul]
  · exact hA
  · exact hB
  · rw [← mul_assoc, hA, mul_assoc, hB, ← mul_assoc]

theorem hexad_pair {i j : Fin 4} (hij : (i, j) = (0, 1) ∨ (i, j) = (2, 3)) :
    (∀ u ∈ V i, ∀ w ∈ V j, u * w = w * u) ∧ V i ⊓ V j = ⊥ ∧
      Nat.card ↥(V i ⊔ V j) = 16 ∧ CFSG.Assembly.IsElemAbelian 2 (V i ⊔ V j) ∧
      P0 ≤ Subgroup.normalizer ((V i ⊔ V j : Subgroup G22) : Set G22) := by
  obtain ⟨c1, c2, c3, c4⟩ := hexad_comm i j hij
  obtain ⟨⟨d1, d2, d3⟩, ⟨d4, d5, d6⟩, ⟨d7, d8, d9⟩⟩ := hexad_disj i j hij
  have hcomm : ∀ u ∈ V i, ∀ w ∈ V j, u * w = w * u := by
    intro u hu w hw
    have hAj : ∀ x ∈ V i, x * vAE j = vAE j * x := by
      intro x hx
      refine (commute_of_mem_V (x := vAE j) (j := i) ?_ ?_ hx).symm
      · exact Subtype.ext c1.symm
      · exact Subtype.ext c3.symm
    have hBj : ∀ x ∈ V i, x * vBE j = vBE j * x := by
      intro x hx
      refine (commute_of_mem_V (x := vBE j) (j := i) ?_ ?_ hx).symm
      · exact Subtype.ext c2.symm
      · exact Subtype.ext c4.symm
    exact commute_of_mem_V (hAj u hu) (hBj u hu) hw
  have hinf : V i ⊓ V j = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxi, hxj⟩
    rw [Subgroup.mem_bot]
    have hne : ∀ {u w : G22}, (u : Equiv.Perm (Fin 22)) ≠ w → u ≠ w := fun h e => h (e ▸ rfl)
    rcases mem_V_iff.mp hxi with rfl | rfl | rfl | rfl
    · rfl
    · rcases mem_V_iff.mp hxj with h | h | h | h
      · exact h
      · exact absurd h (hne d1)
      · exact absurd h (hne d2)
      · exact absurd h (hne d3)
    · rcases mem_V_iff.mp hxj with h | h | h | h
      · exact h
      · exact absurd h (hne d4)
      · exact absurd h (hne d5)
      · exact absurd h (hne d6)
    · rcases mem_V_iff.mp hxj with h | h | h | h
      · exact h
      · exact absurd h (hne d7)
      · exact absurd h (hne d8)
      · exact absurd h (hne d9)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (V i) (V j) hcomm
  rw [hinf, Subgroup.card_bot, mul_one, card_V, card_V] at hcard
  refine ⟨hcomm, hinf, hcard.trans (by norm_num), ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have hx : (x : G22) ∈ ((V i : Set G22) * (V j : Set G22)) := by rw [← hset]; exact x.2
    have hy : (y : G22) ∈ ((V i : Set G22) * (V j : Set G22)) := by rw [← hset]; exact y.2
    obtain ⟨u, hu, w, hw, hxe⟩ := hx
    obtain ⟨u', hu', w', hw', hye⟩ := hy
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxe, ← hye]
    have h1 : u * u' = u' * u :=
      congrArg Subtype.val ((isElementaryAbelian_V i).toIsMulCommutative.is_comm.comm
        ⟨u, hu⟩ ⟨u', hu'⟩)
    have h2 : w * w' = w' * w :=
      congrArg Subtype.val ((isElementaryAbelian_V j).toIsMulCommutative.is_comm.comm
        ⟨w, hw⟩ ⟨w', hw'⟩)
    calc u * w * (u' * w') = (u * u') * (w * w') := by
          rw [mul_assoc, ← mul_assoc w, ← hcomm u' hu' w hw]; group
      _ = (u' * u) * (w' * w) := by rw [h1, h2]
      _ = u' * w' * (u * w) := by
          rw [mul_assoc, ← mul_assoc u, hcomm u hu w' hw']; group
  · have hx' : x ∈ ((V i : Set G22) * (V j : Set G22)) := by rw [← hset]; exact hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx'
    rw [pow_two, show u * w * (u * w) = (u * u) * (w * w) by
      rw [mul_assoc, ← mul_assoc w, ← hcomm u hu w hw]; group,
      sq_eq_one_of_mem_V hu, sq_eq_one_of_mem_V hw, one_mul]
  · exact le_normalizer_sup (A := P0) (P0_le_normalizer_V i) (P0_le_normalizer_V j)

theorem closure_hexad_pair {i j : Fin 4} (hij : (i, j) = (0, 1) ∨ (i, j) = (2, 3)) :
    Subgroup.closure ({lineE i, lineE j} : Set G22) = P0 := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact lineE_mem_P0 i
    · exact lineE_mem_P0 j
  · have hXY : Commute CFSG.RankThree.Asc83Table.M22.X CFSG.RankThree.Asc83Table.M22.Y :=
      CFSG.RankThree.Asc83Table.M22.XY_comm
    have hi : lineE i ∈ Subgroup.closure ({lineE i, lineE j} : Set G22) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hj : lineE j ∈ Subgroup.closure ({lineE i, lineE j} : Set G22) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    change Subgroup.closure ({CFSG.RankThree.Asc83Table.M22.E.a,
      CFSG.RankThree.Asc83Table.M22.E.b} : Set G22) ≤ _
    rw [Subgroup.closure_le, CFSG.RankThree.Asc83Table.M22.E_a,
      CFSG.RankThree.Asc83Table.M22.E_b]
    rcases hij with hij | hij <;> simp only [Prod.mk.injEq] at hij <;> obtain ⟨rfl, rfl⟩ := hij
    · have h0 : lineE 0 = CFSG.RankThree.Asc83Table.M22.X := by
        rw [lineE_eq]; simp [lineA, lineB]
      have h1 : lineE 1 = CFSG.RankThree.Asc83Table.M22.Y := by
        rw [lineE_eq]; simp [lineA, lineB]
      rintro _ (rfl | rfl)
      · exact h0 ▸ hi
      · exact h1 ▸ hj
    · have h2 : lineE 2 = CFSG.RankThree.Asc83Table.M22.X * CFSG.RankThree.Asc83Table.M22.Y := by
        rw [lineE_eq]; simp [lineA, lineB]
      have h3 : lineE 3 =
          CFSG.RankThree.Asc83Table.M22.X * CFSG.RankThree.Asc83Table.M22.Y ^ 2 := by
        rw [lineE_eq]; simp [lineA, lineB]
      have hY : CFSG.RankThree.Asc83Table.M22.Y = (lineE 2)⁻¹ * lineE 3 := by
        rw [h2, h3, pow_two]; group
      have hX : CFSG.RankThree.Asc83Table.M22.X =
          lineE 2 * ((lineE 2)⁻¹ * lineE 3)⁻¹ := by
        rw [← hY, h2]; group
      rintro _ (rfl | rfl)
      · rw [hX]
        exact mul_mem hi (inv_mem (mul_mem (inv_mem hi) hj))
      · rw [hY]
        exact mul_mem (inv_mem hi) hj

end Res5TypesM22

open Res5Gen Res5Types Res5TypesM22 KFacts.KP4 in
theorem step142TypesM22_of
    (h131 : Item131) : Step142TypesM22 := by
  intro G _ _ A c L h Q hQ hK ⟨φ⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspor := Sec13.sporadicModels131
  have hD := h.toSec13Data
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor hD
    (center_eq_bot_of_mulEquiv φ hspor.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hEb
  have hE9 : Nat.card Eb = 9 := card_image_inf h h9
  have hfac : (Nat.card G22).factorization 3 = 2 := by
    rw [KFacts.KS14.card_nativeM22]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 443520 = 3 ^ 2 * 49280 by norm_num) (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card card_P0 (E' := Eb.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hE9]) hfac
  set φ' : (↥L ⧸ θ) ≃* G22 := φ.trans (MulAut.conj g)⁻¹ with hφ'
  have hφ'apply : ∀ x, φ' x = g⁻¹ * φ x * g := fun x => rfl
  have hφ'E : Eb.map φ'.toMonoidHom = P0 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      obtain ⟨p, hp, hpe⟩ := hg (φ e) ⟨e, he, rfl⟩
      change φ' e ∈ P0
      rw [hφ'apply, ← hpe]
      simpa [mul_assoc] using hp
    · rw [card_P0, Subgroup.card_map_of_injective φ'.injective, hE9]
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hcent : ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro r hr l hl
    have hrA : r ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr
    have hrc : r ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A) hrA
    have hrN : r ∈ Subgroup.normalizer (L : Set G) :=
      centralizer_le_normalizer_of_three_dvd h h3L hrc
    set σ := Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨r, hrN⟩) with hσ
    have hσE : ∀ e ∈ Eb, σ e = e := by
      rintro _ ⟨β, hβ, rfl⟩
      have hβA : (β : G) ∈ A := (Subgroup.mem_subgroupOf.mp hβ).1
      have hrβ : r * (β : G) * r⁻¹ = β := by
        rw [← Subgroup.mem_centralizer_iff.mp hrA _ hβA]
        group
      change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨r, hrN⟩ β) = QuotientGroup.mk' θ β
      congr 1
      exact Subtype.ext hrβ
    set n := orderOf r with hn
    have hn3 : ¬ 3 ∣ n := fun h3 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
        (h3.trans (Subgroup.orderOf_dvd_natCard _ hr))
    have hσn : σ ^ n = 1 := by
      have h1 : (⟨r, hrN⟩ : Subgroup.normalizer (L : Set G)) ^ n = 1 :=
        Subtype.ext (by simp [hn, pow_orderOf_eq_one])
      rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
    set τ := MulAut.congr φ' σ with hτ
    have hτP : ∀ p ∈ P0, τ p = p := by
      intro p hp
      rw [← hφ'E] at hp
      obtain ⟨e, he, rfl⟩ := hp
      change φ' (σ (φ'.symm (φ' e))) = φ' e
      rw [MulEquiv.symm_apply_apply, hσE e he]
    have hτn : τ ^ n = 1 := by rw [hτ, ← map_pow, hσn, map_one]
    have hσ1 : σ = 1 :=
      (MulAut.congr φ').injective ((aut_eq_one_G22 hτP hn3 hτn).trans (map_one _).symm)
    have h1 := congrArg (fun f : MulAut (↥L ⧸ θ) => f (QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩))
      hσ1
    change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨r, hrN⟩ ⟨l⁻¹, inv_mem hl⟩) =
      QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩ at h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    refine ⟨_, h1, ?_⟩
    simp [commutatorElement_def, mul_assoc]
  have d : Inner142 A c L := ⟨h, hAc, hK, hcent⟩
  have : (ker142 A (lB A) c).Normal := ker142_normal hD.isElemAbelian.1 hD.mem_A
  obtain ⟨hQL, hQ3, hQE, hQmax⟩ := d.maximal_bar hQ
  set Qb := d.bar (img142 A (lB A) c Q) with hQb
  set Y := Qb.map φ'.toMonoidHom with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hY, Subgroup.card_map_of_injective φ'.injective]
    exact hQ3
  have hEbP : Eb = P0.map φ'.symm.toMonoidHom := by
    rw [← hφ'E, Subgroup.map_map]
    ext x
    simp
  have hYP : P0 ≤ Subgroup.normalizer (Y : Set G22) := by
    rw [← hφ'E, hY, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hQE
  have hYmax : ∀ Y' : Subgroup G22, ¬ 3 ∣ Nat.card Y' →
      P0 ≤ Subgroup.normalizer (Y' : Set G22) → Y ≤ Y' → Y' = Y := by
    intro Y' h3 hP hle
    have hY'' := hQmax (Y'.map φ'.symm.toMonoidHom)
      (by rwa [Subgroup.card_map_of_injective φ'.symm.injective]) (by
        change Eb ≤ _
        rw [hEbP, ← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.map_mono hP) (by
        intro x hx
        exact ⟨φ' x, hle ⟨x, hx, rfl⟩, by simp⟩)
    rw [hY, ← hY'', Subgroup.map_map]
    ext x
    simp
  have hpair : ∃ i j : Fin 4, ((i, j) = (0, 1) ∨ (i, j) = (2, 3)) ∧ Y = V i ⊔ V j := by
    have hpair_eq : ∀ i j : Fin 4, ((i, j) = (0, 1) ∨ (i, j) = (2, 3)) →
        Y ≤ V i ⊔ V j → Y = V i ⊔ V j := by
      intro i j hij hle
      obtain ⟨-, -, hcard, -, hN⟩ := hexad_pair hij
      exact (hYmax _ (by rw [hcard]; norm_num) hN hle).symm
    rcases le_hexad hY3 hYP with h01 | h23
    · exact ⟨0, 1, Or.inl rfl, hpair_eq 0 1 (Or.inl rfl) h01⟩
    · exact ⟨2, 3, Or.inr rfl, hpair_eq 2 3 (Or.inr rfl) h23⟩
  obtain ⟨i, j, hij, hYij⟩ := hpair
  obtain ⟨-, hinfV, hcard16, hEA, -⟩ := hexad_pair hij
  have hlift : ∀ k : Fin 4, ∃ β : G, ∃ hβ : β ∈ A ⊓ L,
      φ' (QuotientGroup.mk' θ ⟨β, hβ.2⟩) = lineE k := by
    intro k
    have hk : lineE k ∈ Eb.map φ'.toMonoidHom := hφ'E ▸ lineE_mem_P0 k
    obtain ⟨e, he, hek⟩ := hk
    obtain ⟨β, hβ, rfl⟩ := he
    exact ⟨β, Subgroup.mem_subgroupOf.mp hβ, hek⟩
  obtain ⟨a, ha, hai⟩ := hlift i
  obtain ⟨b, hb, hbj⟩ := hlift j
  have htheta : ∀ (β : G) (hβ : β ∈ A ⊓ L) (k : Fin 4),
      φ' (QuotientGroup.mk' θ ⟨β, hβ.2⟩) = lineE k →
      d.bar (thetaC142 A (lB A) c (alpha142 A (lB A) c β hβ.1)) =
        (V k).map φ'.symm.toMonoidHom := by
    intro β hβ k hk
    have hid : φ'.symm.toMonoidHom.comp φ'.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun x => φ'.symm_apply_apply x
    rw [(d.thetaC_bar β hβ).2, ← theta_centralizer_line, ← hk,
      ← CFSG.RankThree.PartTwo.map_centralizer_singleton φ',
      ← Sec6.map_inSubgroup_theta_of_injective φ'.toMonoidHom φ'.injective, Subgroup.map_map,
      hid, Subgroup.map_id]
  have hθa := htheta a ha i hai
  have hθb := htheta b hb j hbj
  have hθaL := (d.thetaC_bar a ha).1
  have hθbL := (d.thetaC_bar b hb).1
  have hQbV : Qb = (V i ⊔ V j).map φ'.symm.toMonoidHom := by
    rw [← hYij, hY, Subgroup.map_map]
    ext x
    simp
  have halpha_mem : ∀ (β : G) (hβ : β ∈ A ⊓ L),
      alpha142 A (lB A) c β hβ.1 ∈ img142 A (lB A) c L := fun β hβ =>
    ⟨⟨β, Subgroup.mem_sup_right hβ.1⟩, Subgroup.mem_subgroupOf.mpr hβ.2, rfl⟩
  have halpha_bar : ∀ (β : G) (hβ : β ∈ A ⊓ L),
      d.lbarEquiv.symm ⟨alpha142 A (lB A) c β hβ.1, halpha_mem β hβ⟩ =
        QuotientGroup.mk' θ ⟨β, hβ.2⟩ := by
    intro β hβ
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (d.lbarEquiv_mk ⟨β, hβ.2⟩).symm
  refine ⟨⟨?_, ?_⟩, a, ha.1, b, hb.1, ?_, ?_, ?_⟩
  · refine d.isElemAbelian_of_bar hQL ?_
    rw [← hQb, hQbV]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2 _ _ hEA
  · rw [← d.card_bar hQL, ← hQb, hQbV, Subgroup.card_map_of_injective φ'.symm.injective,
      hcard16]
  · refine d.bar_injective ((Subgroup.closure_le _).mpr ?_) d.img_A_le ?_
    · rintro _ (rfl | rfl)
      · exact halpha_mem a ha
      · exact halpha_mem b hb
    · rw [d.bar_closure_pair (halpha_mem a ha) (halpha_mem b hb), halpha_bar a ha,
        halpha_bar b hb,
        d.bar_A, ← hEb, hEbP, ← closure_hexad_pair hij, MonoidHom.map_closure, Set.image_pair,
        ← hai, ← hbj]
      simp
  · refine d.bar_injective hQL (sup_le hθaL hθbL) ?_
    rw [d.bar_sup hθaL hθbL, hθa, hθb, ← Subgroup.map_sup, ← hQbV]
  · refine d.bar_injective (inf_le_left.trans hθaL) bot_le ?_
    rw [d.bar_inf, hθa, hθb, ← Subgroup.map_inf_eq _ _ _ φ'.symm.injective, hinfV,
      Subgroup.map_bot, d.bar_bot]

end CFSG.RankThree.PartTwo.Sec14
