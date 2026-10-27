module

public import CFSG.Quasithin.H13.NQCoreP134Dich
public import CFSG.Quasithin.H13.NQCoreP134OutThree
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem cube_mul_of_comm {a b e : G} (hba : b * a = e * (a * b)) (hea : e * a = a * e)
    (heb : e * b = b * e) (he3 : e ^ 3 = 1) : (a * b) ^ 3 = a ^ 3 * b ^ 3 := by
  have hae : a * a * e = e * (a * a) := by
    rw [mul_assoc, ← hea, ← mul_assoc, ← hea, mul_assoc]
  have h1 : a * b * (a * b) = e * (a * a * (b * b)) := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (e * (a * b)) * b := by rw [hba]
      _ = (a * e) * a * b * b := by group
      _ = (e * a) * a * b * b := by rw [hea]
      _ = e * (a * a * (b * b)) := by group
  have h2 : b * b * a = e * e * (a * (b * b)) := by
    calc b * b * a = b * (b * a) := by group
      _ = b * (e * (a * b)) := by rw [hba]
      _ = (b * e) * a * b := by group
      _ = (e * b) * a * b := by rw [heb]
      _ = e * (b * a) * b := by group
      _ = e * (e * (a * b)) * b := by rw [hba]
      _ = e * e * (a * (b * b)) := by group
  have he3' : e * e * e = 1 := by rw [← he3, pow_succ, pow_succ, pow_one]
  have hl : (a * b) ^ 3 = a * b * (a * b) * (a * b) := by rw [pow_succ, pow_succ, pow_one]
  have hr : a ^ 3 * b ^ 3 = a * a * a * (b * b * b) := by
    rw [pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]
  rw [hl, hr]
  calc a * b * (a * b) * (a * b) = e * (a * a * (b * b)) * (a * b) := by rw [h1]
    _ = e * (a * a) * (b * b * a) * b := by group
    _ = e * (a * a) * (e * e * (a * (b * b))) * b := by rw [h2]
    _ = e * (a * a * e) * e * (a * (b * b)) * b := by group
    _ = e * (e * (a * a)) * e * (a * (b * b)) * b := by rw [hae]
    _ = e * e * (a * a * e) * (a * (b * b)) * b := by group
    _ = e * e * (e * (a * a)) * (a * (b * b)) * b := by rw [hae]
    _ = (e * e * e) * (a * a * a * (b * b * b)) := by group
    _ = a * a * a * (b * b * b) := by rw [he3', one_mul]

theorem pow_mul_eq_of_comm {a b e : G} (hba : b * a = e * (a * b)) (heb : e * b = b * e)
    (k : ℕ) : b ^ k * a = e ^ k * (a * b ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hek : e ^ k * b = b * e ^ k := ((Commute.pow_left heb k)).eq
    calc b ^ (k + 1) * a = b * (b ^ k * a) := by rw [pow_succ', mul_assoc]
      _ = b * (e ^ k * (a * b ^ k)) := by rw [ih]
      _ = (b * e ^ k) * a * b ^ k := by group
      _ = (e ^ k * b) * a * b ^ k := by rw [hek]
      _ = e ^ k * (b * a) * b ^ k := by group
      _ = e ^ k * (e * (a * b)) * b ^ k := by rw [hba]
      _ = e ^ (k + 1) * (a * b ^ (k + 1)) := by rw [pow_succ, pow_succ']; group

theorem isElemAbelian_sup_of_commute {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

end Group

section Quotient

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem false_of_cyclic_mod {p : ℕ} [hp : Fact p.Prime] {P W : Subgroup Γ} (hWn : W.Normal)
    (hPp : IsPGroup p P) (hexp : ∀ x ∈ P, x ^ p = 1) (hc2 : p ^ 2 ≤ Nat.card P)
    (h : P ⊓ W ≤ ⁅P, P⁆) {u : Γ} (huP : u ∈ P) (hu : P ≤ Subgroup.zpowers u ⊔ W) : False := by
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  have hpsq : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  have huP' : Subgroup.zpowers u ≤ P := Subgroup.zpowers_le.mpr huP
  have h1 : P ≤ Subgroup.zpowers u ⊔ (P ⊓ W) := by
    intro x hx
    have hx' := hu hx
    rw [sup_comm] at hx'
    obtain ⟨d, hd, v, hv, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_normal hWn _)).1 hx'
    have hvP : v ∈ P := huP' hv
    have hdP : d ∈ P := by
      have := P.mul_mem hx (P.inv_mem hvP)
      simpa using this
    rw [sup_comm]
    exact Subgroup.mul_mem_sup ⟨hdP, hd⟩ hv
  have h2 : Subgroup.zpowers u ⊔ frattiniIn P = P :=
    le_antisymm (sup_le huP' (Subgroup.map_subtype_le _))
      (h1.trans (sup_le_sup_left (hΦ ▸ h) _))
  have h3 := eq_of_sup_frattiniIn_eq huP' h2
  have : Nat.card P ≤ p := by
    rw [← h3, Nat.card_zpowers]
    exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one (hexp u huP))
  omega

theorem false_of_three_parts (hrank : Open.pRank 3 (⊤ : Subgroup Γ) ≤ 2) {P L C : Subgroup Γ}
    (hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) (hCN : C ≤ Subgroup.normalizer (L : Set Γ))
    (hZ3 : Nat.card (L ⊓ C : Subgroup Γ) ≤ 3) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hcard : Nat.card P = 3 ^ 2 ∨ Nat.card P = 3 ^ 3) (hPLC : P ≤ L ⊔ C)
    (hPL : P ⊓ L ≤ ⁅P, P⁆) (hPC : P ⊓ C ≤ ⁅P, P⁆) (hPL1 : P ⊓ L ≠ ⊥) (hPC1 : P ⊓ C ≠ ⊥) :
    False := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : 3 ^ 2 ≤ Nat.card P := by
    rcases hcard with h | h <;> rw [h]
    norm_num
  have hc3 : Nat.card P ≤ 3 ^ 3 := by
    rcases hcard with h | h <;> rw [h]
    norm_num
  have h4 := card_commutator_le hexp hc2 hc3
  have hPLeq : P ⊓ L = ⁅P, P⁆ := Subgroup.eq_of_le_of_card_ge hPL
    (h4.trans (le_card_of_ne_bot (hPp.to_le inf_le_left) hPL1))
  have hPCeq : P ⊓ C = ⁅P, P⁆ := Subgroup.eq_of_le_of_card_ge hPC
    (h4.trans (le_card_of_ne_bot (hPp.to_le inf_le_left) hPC1))
  have hK3 : 3 ≤ Nat.card (⁅P, P⁆ : Subgroup Γ) :=
    hPLeq ▸ le_card_of_ne_bot (hPp.to_le inf_le_left) hPL1
  set Z := L ⊓ C with hZdef
  have hKZ : ⁅P, P⁆ ≤ Z := by
    refine le_inf ?_ ?_
    · rw [← hPLeq]; exact inf_le_right
    · rw [← hPCeq]; exact inf_le_right
  have hKeq : ⁅P, P⁆ = Z := Subgroup.eq_of_le_of_card_ge hKZ (hZ3.trans hK3)
  have hZcard : Nat.card Z = 3 := le_antisymm hZ3 (hKeq ▸ hK3)
  have hZP : Z ≤ P := hKeq ▸ commutator_le_left_of_le_normalizer Subgroup.le_normalizer
  have hPL' : P ⊓ L = Z := hPLeq.trans hKeq
  have hPC' : P ⊓ C = Z := hPCeq.trans hKeq
  have hP27 : Nat.card P = 27 := by
    rcases hcard with h | h
    · exfalso
      have hab : IsMulCommutative ↥P := IsPGroup.isMulCommutative_of_card_eq_prime_sq h
      have hK : ⁅P, P⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        have := congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        simp only [Subgroup.coe_mul] at this
        rw [Subgroup.mem_bot, commutatorElement_def, this]
        group
      rw [hK, Subgroup.card_bot] at hK3
      omega
    · rw [h]; norm_num
  obtain ⟨y, hyP, hyZ⟩ : ∃ y ∈ P, y ∉ Z := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx : P ≤ Z)
    omega
  have hy3 : y ^ 3 = 1 := hexp y hyP
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ Z.one_mem)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hZy : Z ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card (Z ⊓ Subgroup.zpowers y : Subgroup Γ) ∣ 3 := by
      rw [← hyo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Z ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hyo])
      exact hyZ ((heq ▸ (Subgroup.mem_zpowers y)).1)
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (Z : Set Γ) := by
    rw [Subgroup.zpowers_le]
    rw [← hKeq]
    exact le_normalizer_commutator Subgroup.le_normalizer hyP
  have hZycard : Nat.card (Z ⊔ Subgroup.zpowers y : Subgroup Γ) = 9 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z _ hyN
      (disjoint_iff.mpr hZy), hZcard, Nat.card_zpowers, hyo]
  obtain ⟨x, hxP, hxZy⟩ : ∃ x ∈ P, x ∉ Z ⊔ Subgroup.zpowers y := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx : P ≤ Z ⊔ Subgroup.zpowers y)
    omega
  have hxyk : ∀ k : ℕ, x * y ^ k ∉ Z := by
    intro k hk
    apply hxZy
    have : x = (x * y ^ k) * (y ^ k)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y k))
  obtain ⟨a, ha, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer hCN).1 (hPLC hxP)
  obtain ⟨b, hb, d, hd, rfl⟩ := (mem_sup_iff_of_le_normalizer hCN).1 (hPLC hyP)
  have hcube : ∀ {l m : Γ}, l ∈ L → m ∈ C → l * m ∈ P → l ^ 3 ∈ Z := by
    intro l m hl hm hlm
    have h1 : l ^ 3 * m ^ 3 = 1 := by
      rw [← (Commute.mul_pow (hLC l hl m hm) 3)]
      exact hexp _ hlm
    have h2 : l ^ 3 = (m ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact ⟨L.pow_mem hl 3, h2 ▸ C.inv_mem (C.pow_mem hm 3)⟩
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => hexp z (hZP hz)
  have hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z := fun z hz l hl => (hLC l hl z hz.2).symm
  set e := b * a * (a * b)⁻¹ with he
  have heL : e ∈ L := L.mul_mem (L.mul_mem hb ha) (L.inv_mem (L.mul_mem ha hb))
  have heC : e ∈ C := by
    have ht : (b * d) * (a * c) * (b * d)⁻¹ * (a * c)⁻¹ ∈ Z :=
      hKeq ▸ Subgroup.commutator_mem_commutator hyP hxP
    have hda : d * a = a * d := (hLC a ha d hd).symm
    have hcb : c * b = b * c := (hLC b hb c hc).symm
    have hdb : d * b = b * d := (hLC b hb d hd).symm
    have hca : c * a = a * c := (hLC a ha c hc).symm
    set γ := d * c * (c * d)⁻¹ with hγ
    have hγC : γ ∈ C := C.mul_mem (C.mul_mem hd hc) (C.inv_mem (C.mul_mem hc hd))
    have hγL : ∀ l ∈ L, γ * l = l * γ := fun l hl => (hLC l hl γ hγC).symm
    have key : (b * d) * (a * c) * (b * d)⁻¹ * (a * c)⁻¹ = γ * e := by
      have e1 : (b * d) * (a * c) = (b * a) * (d * c) := by
        calc (b * d) * (a * c) = b * (d * a) * c := by group
          _ = b * (a * d) * c := by rw [hda]
          _ = (b * a) * (d * c) := by group
      have e2 : (a * c) * (b * d) = (a * b) * (c * d) := by
        calc (a * c) * (b * d) = a * (c * b) * d := by group
          _ = a * (b * c) * d := by rw [hcb]
          _ = (a * b) * (c * d) := by group
      have e3 : (b * d) * (a * c) * (b * d)⁻¹ * (a * c)⁻¹ =
          (b * d) * (a * c) * ((a * c) * (b * d))⁻¹ := by group
      rw [e3, e1, e2]
      have hcdL : (c * d)⁻¹ * (a * b)⁻¹ = (a * b)⁻¹ * (c * d)⁻¹ := by
        have hab : a * b ∈ L := L.mul_mem ha hb
        have hcd : c * d ∈ C := C.mul_mem hc hd
        have := hLC _ (L.inv_mem hab) _ (C.inv_mem hcd)
        exact this.symm
      calc b * a * (d * c) * (a * b * (c * d))⁻¹
          = b * a * (d * c) * ((c * d)⁻¹ * (a * b)⁻¹) := by group
        _ = b * a * (d * c) * ((a * b)⁻¹ * (c * d)⁻¹) := by rw [hcdL]
        _ = b * a * ((d * c) * (a * b)⁻¹) * (c * d)⁻¹ := by group
        _ = b * a * ((a * b)⁻¹ * (d * c)) * (c * d)⁻¹ := by
            rw [hLC _ (L.inv_mem (L.mul_mem ha hb)) _ (C.mul_mem hd hc)]
        _ = (b * a * (a * b)⁻¹) * γ := by rw [hγ]; group
        _ = γ * (b * a * (a * b)⁻¹) := (hγL _ heL).symm
        _ = γ * e := by rw [he]
    have : e = γ⁻¹ * ((b * d) * (a * c) * (b * d)⁻¹ * (a * c)⁻¹) := by rw [key]; group
    rw [this]
    exact C.mul_mem (C.inv_mem hγC) ht.2
  have heZ : e ∈ Z := ⟨heL, heC⟩
  have hba : b * a = e * (a * b) := by rw [he]; group
  have hea : e * a = a * e := hZL e heZ a ha
  have heb : e * b = b * e := hZL e heZ b hb
  have he3 : e ^ 3 = 1 := hZexp e heZ
  obtain ⟨u, hu, w, hw, hgP, hgZ, hu3, hw3⟩ : ∃ u ∈ L, ∃ w ∈ C, u * w ∈ P ∧ u * w ∉ Z ∧
      u ^ 3 = 1 ∧ w ^ 3 = 1 := by
    have hb3 : b ^ 3 ∈ Z := hcube hb hd hyP
    have ha3 : a ^ 3 ∈ Z := hcube ha hc hxP
    have hw3 : ∀ {l m : Γ}, l ∈ L → m ∈ C → l * m ∈ P → l ^ 3 = 1 → m ^ 3 = 1 := by
      intro l m hl hm hlm hl3
      have h1 : l ^ 3 * m ^ 3 = 1 := by
        rw [← (Commute.mul_pow (hLC l hl m hm) 3)]
        exact hexp _ hlm
      rwa [hl3, one_mul] at h1
    by_cases hb1 : b ^ 3 = 1
    · exact ⟨b, hb, d, hd, hyP, hyZ, hb1, hw3 hb hd hyP hb1⟩
    have hbo : orderOf (b ^ 3) = 3 := orderOf_eq_prime (hZexp _ hb3) hb1
    have hZgen : Z = Subgroup.zpowers (b ^ 3) := by
      refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hb3) ?_).symm
      rw [hZcard, Nat.card_zpowers, hbo]
    obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.range (orderOf (b ^ 3)), (b ^ 3) ^ m = a ^ 3 := by
      classical
      have : a ^ 3 ∈ Subgroup.zpowers (b ^ 3) := hZgen ▸ ha3
      exact Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp this)
    set k := 3 - m % 3 with hk
    have hmk : a ^ 3 * (b ^ k) ^ 3 = 1 := by
      have h1 : (b ^ k) ^ 3 = (b ^ 3) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [h1, ← hm, ← pow_add]
      obtain ⟨q, hq⟩ : 3 ∣ m + k := by omega
      rw [hq, pow_mul, hZexp _ hb3, one_pow]
    have hbka : b ^ k * a = e ^ k * (a * b ^ k) := pow_mul_eq_of_comm hba heb k
    have hu3 : (a * b ^ k) ^ 3 = 1 := by
      have hea' : e ^ k * a = a * e ^ k := (Commute.pow_left hea k).eq
      have heb' : e ^ k * b ^ k = b ^ k * e ^ k := (Commute.pow_pow heb k k).eq
      have he3' : (e ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, he3, one_pow]
      rw [cube_mul_of_comm hbka hea' heb' he3', hmk]
    have hdbk : ∀ j : ℕ, (b * d) ^ j = b ^ j * d ^ j := fun j =>
      (Commute.mul_pow (hLC b hb d hd) j)
    have hg : a * c * (b * d) ^ k = (a * b ^ k) * (c * d ^ k) := by
      rw [hdbk k]
      have hcbk : c * b ^ k = b ^ k * c := (hLC _ (L.pow_mem hb k) c hc).symm
      calc a * c * (b ^ k * d ^ k) = a * (c * b ^ k) * d ^ k := by group
        _ = a * (b ^ k * c) * d ^ k := by rw [hcbk]
        _ = (a * b ^ k) * (c * d ^ k) := by group
    have hgP : (a * b ^ k) * (c * d ^ k) ∈ P := hg ▸ P.mul_mem hxP (P.pow_mem hyP k)
    refine ⟨a * b ^ k, L.mul_mem ha (L.pow_mem hb k), c * d ^ k, C.mul_mem hc (C.pow_mem hd k),
      hgP, hg ▸ hxyk k, hu3, hw3 (L.mul_mem ha (L.pow_mem hb k))
        (C.mul_mem hc (C.pow_mem hd k)) hgP hu3⟩
  have huC : u ∉ C := fun h => hgZ (hPC' ▸ ⟨hgP, C.mul_mem h hw⟩)
  have hwL : w ∉ L := fun h => hgZ (hPL' ▸ ⟨hgP, L.mul_mem hu h⟩)
  have hu1 : u ≠ 1 := fun h => huC (h ▸ C.one_mem)
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hEu : IsElemAbelian 3 (Subgroup.zpowers u) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
      show (x : Γ) * y = y * x
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
  have hZel : IsElemAbelian 3 Z :=
    ⟨⟨⟨fun x y => Subtype.ext (hLC x x.2.1 y y.2.2)⟩⟩, hZexp⟩
  have huZ : ∀ v ∈ Subgroup.zpowers u, ∀ z ∈ Z, v * z = z * v := fun v hv z hz =>
    (hZL z hz v ((Subgroup.zpowers_le.mpr hu) hv)).symm
  have hE := isElemAbelian_sup_of_commute hEu hZel huZ
  have huZd : Subgroup.zpowers u ⊓ Z = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers u ⊓ Z : Subgroup Γ) ∣ 3 := by
      rw [← huo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Subgroup.zpowers u ⊓ Z = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Nat.card_zpowers, huo])
      exact huC ((heq ▸ (Subgroup.mem_zpowers u)).2.2)
  have hZN : Z ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup Γ) : Set Γ) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hzu : z * u = u * z := hZL z hz u hu
    constructor
    · intro hv
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have : z * u ^ i * z⁻¹ = u ^ i := by
        rw [(Commute.zpow_right hzu i).eq]; group
      rw [this]
      exact Subgroup.zpow_mem_zpowers u i
    · intro hv
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hv
      have : v = u ^ i := by
        have h1 : z * v * z⁻¹ = u ^ i := hi.symm
        have h2 : z * u ^ i * z⁻¹ = u ^ i := by rw [(Commute.zpow_right hzu i).eq]; group
        have h3 : z * v * z⁻¹ = z * u ^ i * z⁻¹ := h1.trans h2.symm
        simpa using h3
      rw [this]
      exact Subgroup.zpow_mem_zpowers u i
  have hEcard : Nat.card (Subgroup.zpowers u ⊔ Z : Subgroup Γ) = 3 ^ 2 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ Z hZN
      (disjoint_iff.mpr huZd), Nat.card_zpowers, huo, hZcard]
    norm_num
  have hEL : Subgroup.zpowers u ⊔ Z ≤ L := sup_le ((Subgroup.zpowers_le).mpr hu) inf_le_left
  exact false_of_commute' hrank hE hEcard (fun h => hwL (hEL h)) hw3
    fun v hv => hLC v (hEL hv) w hw

theorem le_of_normal_case_three (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ)
    (hO3 : OutThreeFact) {P N L : Subgroup Γ} (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hcard : Nat.card P = 3 ^ 2 ∨ Nat.card P = 3 ^ 3)
    (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    P ≤ L := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : Open.pRank 3 (⊤ : Subgroup Γ) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt) 3 hp.out (by norm_num)
  have hPp : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : 3 ^ 2 ≤ Nat.card P := by
    rcases hcard with h | h <;> rw [h]
    norm_num
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc2
    norm_num at hc2
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  set C := Subgroup.centralizer (L : Set Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hLCn : (L ⊔ C).Normal := Subgroup.sup_normal L C
  obtain ⟨D, hDn, -, hD1, hD2⟩ := hO3 Γ L hyp hLn hL
  have hinv := fun (W : Subgroup Γ) (hW : N ≤ Subgroup.normalizer (W : Set Γ)) =>
    inf_le_or_le_of_irreducible hPp hexp hNP hirr hW
  have hPD : P ≤ D := by
    rcases hinv D (le_normalizer_of_normal hDn N) with h | h
    · obtain ⟨u, huP, hu⟩ := hD1 P hPp
      exact (false_of_cyclic_mod hDn hPp hexp hc2 h huP hu).elim
    · exact h
  have hPLC : P ≤ L ⊔ C := by
    rcases hinv (L ⊔ C) (le_normalizer_of_normal hLCn N) with h | h
    · obtain ⟨u, huP, hu⟩ := hD2 P hPD hPp
      exact (false_of_cyclic_mod hLCn hPp hexp hc2 h huP hu).elim
    · exact h
  have hPC : P ⊓ C ≤ ⁅P, P⁆ := by
    rcases hinv C (le_normalizer_of_normal hCn N) with h | h
    · exact h
    · exact absurd h hLP
  rcases hinv L (le_normalizer_of_normal hLn N) with h | h
  swap
  · exact h
  exfalso
  by_cases hpC : 3 ∣ Nat.card C
  · have hPC1 : P ⊓ C ≠ ⊥ := fun h0 =>
      false_of_normalizes' hrank hexp hc2 (le_normalizer_of_normal hCn P) h0 hpC
    have hPL1 : P ⊓ L ≠ ⊥ := by
      intro h0
      by_cases hpL : 3 ∣ Nat.card L
      · exact false_of_normalizes' hrank hexp hc2 (le_normalizer_of_normal hLn P) h0 hpL
      · apply hLP
        intro x hx
        exact mem_of_mem_sup_of_coprime (M := L) (M' := C) le_rfl hpL (hPLC hx) (hexp x hx)
    have hZ : Nat.card (L ⊓ C : Subgroup Γ) ≤ 3 := by
      rw [card_inf_centralizer]
      rcases card_center_of_a36Common' hL.1 (h36 L hLc).2.1 with h1 | h3 <;> omega
    exact false_of_three_parts hrank (fun l hl c hc => (Subgroup.mem_centralizer_iff.mp hc) l hl)
      (P134.centralizer_le_normalizer_self L) hZ hexp hcard hPLC h hPC hPL1 hPC1
  ·
    have hPL' : P ≤ L := by
      intro x hx
      have hx' : x ∈ C ⊔ L := by rw [sup_comm]; exact hPLC hx
      refine mem_of_mem_sup_of_coprime (M := C) (M' := L) ?_ hpC hx' (hexp x hx)
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact ((Subgroup.mem_centralizer_iff.mp hc) l hl).symm
    have hPc : P ≤ ⁅P, P⁆ := by
      have := (inf_eq_left.mpr hPL') ▸ h
      exact this
    exact frattiniIn_ne_of_ne_bot hP1 (le_antisymm (Subgroup.map_subtype_le _) (hΦ ▸ hPc))

theorem quotient_main_three_dich (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ)
    (h37 : A37Statement Γ) (h38 : A38Part3 Γ) (hO3 : OutThreeFact) (hOA : OutAbelianFact)
    {P T N O : Subgroup Γ} (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hcard : Nat.card P = 3 ^ 2 ∨ Nat.card P = 3 ^ 3)
    (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hPc : P ≤ commutator Γ) :
    P.Normal ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧ L.Normal ∧ P ≤ L) ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧
        ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
          P ≤ L ⊔ L.map (MulAut.conj n).toMonoidHom) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup Γ) ≤ 2 :=
    CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt
  have hPp : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : 3 ^ 2 ≤ Nat.card P := by
    rcases hcard with h | h <;> rw [h]
    norm_num
  have hc3 : Nat.card P ≤ 3 ^ 3 := by
    rcases hcard with h | h <;> rw [h]
    norm_num
  rcases P134.normal_or_centralizes_fitting hyp.o2 hrank (by norm_num) hPp hexp hc2 hc3 hNP hirr
      hPc with hn | ⟨hFit, hrk⟩
  · exact Or.inl hn
  right
  have hrkP : 2 ≤ Open.pRank 3 P := two_le_pRank_of_pow_eq_one hexp hc2
  obtain ⟨L, hL, hLP⟩ := P134.exists_component_not_le_centralizer hPp hrkP hFit hrk
  have hLc : L ∈ cComp (⊤ : Subgroup Γ) := mem_cComp_top_of_isComponent hL
  by_cases hLn : L.Normal
  · exact Or.inl ⟨L, hLc, hL, hLn,
      le_of_normal_case_three hyp h36 hO3 hexp hcard hNP hirr hLc hL hLn hLP⟩
  · exact Or.inr ⟨L, hLc, hL,
      le_sup_of_pair_case_odd hyp h37 h38 hOA (by norm_num) hexp hcard hT hNT hNP hirr hTON hOX
        hLc hL hLn hLP⟩

end Quotient

variable {G : Type} [Group G] [Finite G]

theorem prop134_three_case_dich (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hO3 : OutThreeFact) (hOA : OutAbelianFact) {H S X P : Subgroup G}
    (hsqtk : CFSG.SectionRank.IsSQTKCat ↥H)
    (hS : IsSylowTwoOf S H) (hXH : X ≤ H) (hX : IsXi S X) (hPX : P ≤ X) (hPp : IsPGroup 3 P)
    (hPcard : Nat.card P = (pCoreOf 2 X).relIndex X) :
    H ≤ Subgroup.normalizer (X : Set G) ∨
    ∃ L ∈ cComp H, CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ X ≤ conjClosure L S := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hyp : SQTKHypCat (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHypCat.quotient_pCore ↥H hsqtk
  obtain ⟨hpX, hSyl⟩ := sylow_of_card_eq_relIndex hX hp2 hPX hPp hPcard
  have hPH : P ≤ H := hPX.trans hXH
  have hexp := exp_of_sylow hX hp2 hpX hSyl
  have hPO : P ⊓ pCoreOf 2 H = ⊥ := inf_pCoreOf_eq_bot' hp2 hPp
  have hcard : Nat.card P = 3 ^ 2 ∨ Nat.card P = 3 ^ 3 := by
    obtain ⟨k, hk2, hk3, hk⟩ := hX.relIndex_eq hp.out hp2 hpX
    rw [hPcard, hk]
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcardb : Nat.card (modO2Image H P) = 3 ^ 2 ∨ Nat.card (modO2Image H P) = 3 ^ 3 := by
    rw [card_bar_of_sylow hXH hp2 hSyl]
    exact hcard
  have hirr := irr_modO2Image' hPH (inf_le_left.trans hS.1) inf_le_right
    (irr_of_sylow hS hXH hX hp2 hpX hSyl)
  have hNT : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤ modO2Image H S :=
    P134.modO2Image_mono inf_le_left
  have hNP : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.normalizer (modO2Image H P : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    P134.modO2Image_le_normalizer inf_le_right
  have hXK : ∀ K : Subgroup G, H ≤ Subgroup.normalizer (K : Set G) → P ≤ K → X ≤ K := by
    intro K hHK hPK
    rw [cl_of_sylow hX hp2 hpX hSyl]
    exact conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hHK (hXH hh)) z).mp (hPK hz)
  have hPpull : ∀ K : Subgroup G, pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) →
      modO2Image H P ≤ modO2Image H K → P ≤ K := fun K hOK hPK a ha =>
    mem_of_mem_modO2Image' hp2 hOK (hPH ha) (hexp a ha)
      (hPK (P134.mk_mem_modO2Image ha (hPH ha)))
  rcases quotient_main_three_dich hyp (h36 _ hyp) (h37 _ hyp) (h38 _ hyp) hO3 hOA
      (exp_bar_of_sylow hX hp2 hpX hSyl) hcardb (P134.sylow_bar hS) hNT hNP hirr
      (sup_bar_of_sylow hS hXH hX hp2 hpX hSyl) (oX_bar_of_sylow hXH hX hp2 hpX hSyl)
      (comm_bar_of_sylow hS hXH hX hp2 hpX hSyl) with
    hn | ⟨Lb, hLbc, hLb, hLbn, hPLb⟩ | ⟨Lb, hLbc, hLb, nb, hnbN, -, hPK⟩
  ·
    exact Or.inl (le_normalizer_of_normal_of_sylow hS hXH hX hp2 hpX hSyl hn)
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    have hLH : L ≤ H := le_of_mem_cComp hL
    have hLnH : (L.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hL) hLbn
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLnH
    have hSL : S ≤ Subgroup.normalizer (L : Set G) := hS.1.trans hHL
    have hPL : P ≤ L := hPpull L (P134.pCoreOf_le_normalizer_of_mem_cComp hL) hPLb
    have hcl : conjClosure L S = L := by
      refine le_antisymm (conjClosure_le fun g hg l hl => ?_) (le_conjClosure L S)
      exact (Subgroup.mem_normalizer_iff.mp (hSL hg) l).mp hl
    exact ⟨L, hL, hq, hcl.symm ▸ hXK L hHL hPL⟩
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    obtain ⟨t', ht', rfl⟩ := hnbN
    set t : G := (t' : G) with ht
    have htSN : t ∈ S ⊓ Subgroup.normalizer (P : Set G) := ht'
    have htH : t ∈ H := t'.2
    set Lt := L.map (MulAut.conj t).toMonoidHom with hLt
    have hLtc : Lt ∈ cComp H := map_conj_mem_cComp hL htH
    have hLtb : modO2Image H Lt = (modO2Image H L).map (MulAut.conj (π t')).toMonoidHom :=
      modO2Image_conj t'
    have hOLt : pCoreOf 2 H ≤ Subgroup.normalizer ((L ⊔ Lt : Subgroup G) : Set G) :=
      fun o ho => Subgroup.inf_normalizer_le_normalizer_sup L Lt
        ⟨P134.pCoreOf_le_normalizer_of_mem_cComp hL ho,
          P134.pCoreOf_le_normalizer_of_mem_cComp hLtc ho⟩
    have hPLLt : P ≤ L ⊔ Lt := by
      refine hPpull _ hOLt (hPK.trans ?_)
      rw [← hLtb]
      exact sup_le (P134.modO2Image_mono le_sup_left) (P134.modO2Image_mono le_sup_right)
    have hLLtS : L ⊔ Lt ≤ conjClosure L S := by
      refine sup_le (le_conjClosure L S) ?_
      rintro _ ⟨l, hl, rfl⟩
      exact mem_conjClosure htSN.1 hl
    have hHcl : H ≤ Subgroup.normalizer (conjClosure L S : Set G) :=
      normal_conjClosure_of_subgroup hS hL (h37 _ hyp) (h38 _ hyp)
    exact ⟨L, hL, hq, hXK _ hHcl (hPLLt.trans hLLtS)⟩

theorem prop134Dich_of_out (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hO3 : OutThreeFact) (hOC : OutCyclicFact) (hOA : OutAbelianFact) :
    Prop134Dich := by
  intro G _ _ H S X P p hp hH _ hS hXH hX hp2 _ hPX hPp hPcard
  have hp3 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.out.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · left
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp.out (by decide)
    · exact Or.inr h
  rcases hp3 with rfl | hp5
  · exact prop134_three_case_dich h36 h37 h38 hO3 hOA hH hS hXH hX hPX hPp hPcard
  · exact prop134_odd_case_dich h36 h37 h38 hOC hOA hp5 hH hS hXH hX hPX hPp hPcard

end CFSG.Quasithin.H13.NQCore
