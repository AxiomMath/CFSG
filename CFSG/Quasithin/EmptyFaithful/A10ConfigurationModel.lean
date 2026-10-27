module

public import CFSG.Quasithin.Background.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin

def s4Table : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    [1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17],
    [2, 3, 0, 1, 5, 4, 12, 13, 14, 15, 16, 17, 6, 7, 8, 9, 10, 11, 19, 18, 22, 23, 20, 21],
    [3, 2, 5, 4, 0, 1, 13, 12, 16, 17, 14, 15, 19, 18, 22, 23, 20, 21, 6, 7, 8, 9, 10, 11],
    [4, 5, 1, 0, 3, 2, 18, 19, 20, 21, 22, 23, 7, 6, 10, 11, 8, 9, 13, 12, 16, 17, 14, 15],
    [5, 4, 3, 2, 1, 0, 19, 18, 22, 23, 20, 21, 13, 12, 16, 17, 14, 15, 7, 6, 10, 11, 8, 9],
    [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 14, 15, 12, 13, 17, 16, 20, 21, 18, 19, 23, 22],
    [7, 6, 10, 11, 8, 9, 1, 0, 4, 5, 2, 3, 20, 21, 18, 19, 23, 22, 14, 15, 12, 13, 17, 16],
    [8, 9, 6, 7, 11, 10, 14, 15, 12, 13, 17, 16, 0, 1, 2, 3, 4, 5, 21, 20, 23, 22, 18, 19],
    [9, 8, 11, 10, 6, 7, 15, 14, 17, 16, 12, 13, 21, 20, 23, 22, 18, 19, 0, 1, 2, 3, 4, 5],
    [10, 11, 7, 6, 9, 8, 20, 21, 18, 19, 23, 22, 1, 0, 4, 5, 2, 3, 15, 14, 17, 16, 12, 13],
    [11, 10, 9, 8, 7, 6, 21, 20, 23, 22, 18, 19, 15, 14, 17, 16, 12, 13, 1, 0, 4, 5, 2, 3],
    [12, 13, 14, 15, 16, 17, 2, 3, 0, 1, 5, 4, 8, 9, 6, 7, 11, 10, 22, 23, 19, 18, 21, 20],
    [13, 12, 16, 17, 14, 15, 3, 2, 5, 4, 0, 1, 22, 23, 19, 18, 21, 20, 8, 9, 6, 7, 11, 10],
    [14, 15, 12, 13, 17, 16, 8, 9, 6, 7, 11, 10, 2, 3, 0, 1, 5, 4, 23, 22, 21, 20, 19, 18],
    [15, 14, 17, 16, 12, 13, 9, 8, 11, 10, 6, 7, 23, 22, 21, 20, 19, 18, 2, 3, 0, 1, 5, 4],
    [16, 17, 13, 12, 15, 14, 22, 23, 19, 18, 21, 20, 3, 2, 5, 4, 0, 1, 9, 8, 11, 10, 6, 7],
    [17, 16, 15, 14, 13, 12, 23, 22, 21, 20, 19, 18, 9, 8, 11, 10, 6, 7, 3, 2, 5, 4, 0, 1],
    [18, 19, 20, 21, 22, 23, 4, 5, 1, 0, 3, 2, 10, 11, 7, 6, 9, 8, 16, 17, 13, 12, 15, 14],
    [19, 18, 22, 23, 20, 21, 5, 4, 3, 2, 1, 0, 16, 17, 13, 12, 15, 14, 10, 11, 7, 6, 9, 8],
    [20, 21, 18, 19, 23, 22, 10, 11, 7, 6, 9, 8, 4, 5, 1, 0, 3, 2, 17, 16, 15, 14, 13, 12],
    [21, 20, 23, 22, 18, 19, 11, 10, 9, 8, 7, 6, 17, 16, 15, 14, 13, 12, 4, 5, 1, 0, 3, 2],
    [22, 23, 19, 18, 21, 20, 16, 17, 13, 12, 15, 14, 5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6],
    [23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]]

def s4InvTable : List Nat := [0, 1, 2, 4, 3, 5, 6, 7, 12, 18, 13, 19, 8, 10, 14, 20, 16, 22, 9, 11, 15, 21, 17, 23]

def s4Perms : List (List Nat) :=
  [[0, 1, 2, 3],
    [0, 1, 3, 2],
    [0, 2, 1, 3],
    [0, 2, 3, 1],
    [0, 3, 1, 2],
    [0, 3, 2, 1],
    [1, 0, 2, 3],
    [1, 0, 3, 2],
    [1, 2, 0, 3],
    [1, 2, 3, 0],
    [1, 3, 0, 2],
    [1, 3, 2, 0],
    [2, 0, 1, 3],
    [2, 0, 3, 1],
    [2, 1, 0, 3],
    [2, 1, 3, 0],
    [2, 3, 0, 1],
    [2, 3, 1, 0],
    [3, 0, 1, 2],
    [3, 0, 2, 1],
    [3, 1, 0, 2],
    [3, 1, 2, 0],
    [3, 2, 0, 1],
    [3, 2, 1, 0]]

structure S4 where
  ix : Fin 24

namespace S4

theorem ext {x y : S4} (h : x.ix = y.ix) : x = y := by
  cases x; cases y; simp_all

instance : DecidableEq S4 := fun x y =>
  decidable_of_iff (x.ix = y.ix) ⟨ext, fun h => by rw [h]⟩

instance : Fintype S4 :=
  Fintype.ofEquiv (Fin 24) ⟨S4.mk, S4.ix, fun _ => rfl, fun x => by cases x; rfl⟩

def lookup (i j : Fin 24) : Fin 24 :=
  ⟨((s4Table.getD i.val []).getD j.val 0) % 24, Nat.mod_lt _ (by decide)⟩

instance : Mul S4 := ⟨fun x y => ⟨lookup x.ix y.ix⟩⟩
instance : One S4 := ⟨⟨0⟩⟩
instance : Inv S4 := ⟨fun x => ⟨⟨(s4InvTable.getD x.ix.val 0) % 24, Nat.mod_lt _ (by decide)⟩⟩⟩

theorem mul_assoc' : ∀ x y z : S4, x * y * z = x * (y * z) := by decide +kernel
theorem one_mul' : ∀ x : S4, 1 * x = x := by decide +kernel
theorem mul_one' : ∀ x : S4, x * 1 = x := by decide +kernel
theorem inv_mul_cancel' : ∀ x : S4, x⁻¹ * x = 1 := by decide +kernel

instance : Group S4 where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'

def ofImages (l : List Nat) : S4 := ⟨⟨(s4Perms.idxOf l) % 24, Nat.mod_lt _ (by decide)⟩⟩

def r : S4 := ⟨⟨9, by decide⟩⟩
def tau : S4 := ⟨⟨16, by decide⟩⟩
def r3 : S4 := ⟨⟨18, by decide⟩⟩
def f1 : S4 := ⟨⟨14, by decide⟩⟩
def f2 : S4 := ⟨⟨5, by decide⟩⟩
def v2 : S4 := ⟨⟨7, by decide⟩⟩
def v3 : S4 := ⟨⟨23, by decide⟩⟩

def mk' (n : Nat) (h : n < 24 := by decide) : S4 := ⟨⟨n, h⟩⟩

def c3 : S4 := mk' 8

def trList : List S4 := [mk' 1, mk' 2, mk' 5, mk' 6, mk' 14, mk' 21]

def vnList : List S4 := [tau, v2, v3]

def dList : List S4 := [1, r, tau, r3, f1, f2, v2, v3]
def vList : List S4 := [1, tau, v2, v3]
def v'List : List S4 := [1, tau, f1, f2]

def subOfList (l : List S4) (h1 : (1 : S4) ∈ l) (hm : ∀ x ∈ l, ∀ y ∈ l, x * y ∈ l)
    (hi : ∀ x ∈ l, x⁻¹ ∈ l) : Subgroup S4 where
  carrier := {x | x ∈ l}
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha

def D : Subgroup S4 := subOfList dList (by decide +kernel) (by decide +kernel) (by decide +kernel)
def V : Subgroup S4 := subOfList vList (by decide +kernel) (by decide +kernel) (by decide +kernel)
def V' : Subgroup S4 := subOfList v'List (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem mem_D {x : S4} : x ∈ D ↔ x ∈ dList := Iff.rfl
theorem mem_V {x : S4} : x ∈ V ↔ x ∈ vList := Iff.rfl
theorem mem_V' {x : S4} : x ∈ V' ↔ x ∈ v'List := Iff.rfl

instance : DecidablePred (· ∈ D) := fun x => decidable_of_iff (x ∈ dList) mem_D.symm
instance {H K : Subgroup S4} [DecidablePred (· ∈ H)] [DecidablePred (· ∈ K)] :
    DecidablePred (· ∈ H ⊓ K) := fun x =>
  decidable_of_iff (x ∈ H ∧ x ∈ K) Subgroup.mem_inf.symm
instance : DecidablePred (· ∈ V) := fun x => decidable_of_iff (x ∈ vList) mem_V.symm
instance : DecidablePred (· ∈ V') := fun x => decidable_of_iff (x ∈ v'List) mem_V'.symm

end S4

structure Wc where
  a : S4
  b : S4
  e : Bool

namespace Wc

theorem ext {x y : Wc} (ha : x.a = y.a) (hb : x.b = y.b) (he : x.e = y.e) : x = y := by
  cases x; cases y; simp_all

instance : DecidableEq Wc := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.e = y.e)
    ⟨fun h => ext h.1 h.2.1 h.2.2, fun h => by rw [h]; exact ⟨rfl, rfl, rfl⟩⟩

instance : Fintype Wc :=
  Fintype.ofEquiv (S4 × S4 × Bool)
    ⟨fun x => ⟨x.1, x.2.1, x.2.2⟩, fun x => ⟨x.a, x.b, x.e⟩, fun _ => rfl, fun x => by cases x; rfl⟩

instance : Mul Wc where
  mul x y :=
    match x.e with
    | false => ⟨x.a * y.a, x.b * y.b, y.e⟩
    | true => ⟨x.a * y.b, x.b * y.a, !y.e⟩

instance : One Wc := ⟨⟨1, 1, false⟩⟩

instance : Inv Wc where
  inv x :=
    match x.e with
    | false => ⟨x.a⁻¹, x.b⁻¹, false⟩
    | true => ⟨x.b⁻¹, x.a⁻¹, true⟩

theorem mul_false {a b : S4} {y : Wc} : (⟨a, b, false⟩ : Wc) * y = ⟨a * y.a, b * y.b, y.e⟩ := rfl
theorem mul_true {a b : S4} {y : Wc} : (⟨a, b, true⟩ : Wc) * y = ⟨a * y.b, b * y.a, !y.e⟩ := rfl
theorem inv_false {a b : S4} : (⟨a, b, false⟩ : Wc)⁻¹ = ⟨a⁻¹, b⁻¹, false⟩ := rfl
theorem inv_true {a b : S4} : (⟨a, b, true⟩ : Wc)⁻¹ = ⟨b⁻¹, a⁻¹, true⟩ := rfl
theorem one_def : (1 : Wc) = ⟨1, 1, false⟩ := rfl

instance : Group Wc where
  mul_assoc x y z := by
    rcases x with ⟨a, b, _ | _⟩ <;> rcases y with ⟨a', b', _ | _⟩ <;>
      rcases z with ⟨a'', b'', _ | _⟩ <;>
      refine ext ?_ ?_ ?_ <;> simp [mul_false, mul_true, mul_assoc]
  one_mul x := by
    rcases x with ⟨a, b, e⟩
    exact ext (by simp [one_def, mul_false]) (by simp [one_def, mul_false]) (by simp [one_def, mul_false])
  mul_one x := by
    rcases x with ⟨a, b, _ | _⟩ <;> refine ext ?_ ?_ ?_ <;>
      simp [one_def, mul_false, mul_true]
  inv_mul_cancel x := by
    rcases x with ⟨a, b, _ | _⟩ <;> refine ext ?_ ?_ ?_ <;>
      simp [one_def, mul_false, mul_true, inv_false, inv_true]

theorem card_Wc : Fintype.card Wc = 1152 := by decide +kernel

theorem mul_of_e_false {x : Wc} (h : x.e = false) (y : Wc) :
    x * y = ⟨x.a * y.a, x.b * y.b, y.e⟩ := by
  rcases x with ⟨a, b, e⟩
  simp only at h
  subst h
  rfl

theorem mul_of_e_true {x : Wc} (h : x.e = true) (y : Wc) :
    x * y = ⟨x.a * y.b, x.b * y.a, !y.e⟩ := by
  rcases x with ⟨a, b, e⟩
  simp only at h
  subst h
  rfl

theorem inv_of_e_false {x : Wc} (h : x.e = false) : x⁻¹ = ⟨x.a⁻¹, x.b⁻¹, false⟩ := by
  rcases x with ⟨a, b, e⟩
  simp only at h
  subst h
  rfl

theorem inv_of_e_true {x : Wc} (h : x.e = true) : x⁻¹ = ⟨x.b⁻¹, x.a⁻¹, true⟩ := by
  rcases x with ⟨a, b, e⟩
  simp only at h
  subst h
  rfl

def inclBase : S4 × S4 →* Wc where
  toFun p := ⟨p.1, p.2, false⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inclBase_injective : Function.Injective inclBase := by
  intro p q h
  have h1 := congrArg Wc.a h
  have h2 := congrArg Wc.b h
  exact Prod.ext h1 h2

def baseSub (X Y : Subgroup S4) : Subgroup Wc where
  carrier := {x | x.e = false ∧ x.a ∈ X ∧ x.b ∈ Y}
  one_mem' := ⟨rfl, X.one_mem, Y.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hx, hxa, hxb⟩ ⟨hy, hya, hyb⟩
    rw [mul_of_e_false hx]
    exact ⟨hy, X.mul_mem hxa hya, Y.mul_mem hxb hyb⟩
  inv_mem' := by
    rintro x ⟨hx, hxa, hxb⟩
    rw [inv_of_e_false hx]
    exact ⟨rfl, X.inv_mem hxa, Y.inv_mem hxb⟩

def symSub (X : Subgroup S4) : Subgroup Wc where
  carrier := {x | x.a ∈ X ∧ x.b ∈ X}
  one_mem' := ⟨X.one_mem, X.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxa, hxb⟩ ⟨hya, hyb⟩
    cases hx : x.e
    · rw [mul_of_e_false hx]; exact ⟨X.mul_mem hxa hya, X.mul_mem hxb hyb⟩
    · rw [mul_of_e_true hx]; exact ⟨X.mul_mem hxa hyb, X.mul_mem hxb hya⟩
  inv_mem' := by
    rintro x ⟨hxa, hxb⟩
    cases hx : x.e
    · rw [inv_of_e_false hx]; exact ⟨X.inv_mem hxa, X.inv_mem hxb⟩
    · rw [inv_of_e_true hx]; exact ⟨X.inv_mem hxb, X.inv_mem hxa⟩

theorem mem_baseSub {X Y : Subgroup S4} {x : Wc} :
    x ∈ baseSub X Y ↔ x.e = false ∧ x.a ∈ X ∧ x.b ∈ Y := Iff.rfl

theorem mem_symSub {X : Subgroup S4} {x : Wc} : x ∈ symSub X ↔ x.a ∈ X ∧ x.b ∈ X := Iff.rfl

instance (X Y : Subgroup S4) [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)] :
    DecidablePred (· ∈ baseSub X Y) := fun x =>
  decidable_of_iff (x.e = false ∧ x.a ∈ X ∧ x.b ∈ Y) mem_baseSub.symm

instance (X : Subgroup S4) [DecidablePred (· ∈ X)] : DecidablePred (· ∈ symSub X) := fun x =>
  decidable_of_iff (x.a ∈ X ∧ x.b ∈ X) mem_symSub.symm

instance : DecidablePred (· ∈ (⊥ : Subgroup S4)) := fun x =>
  decidable_of_iff (x = 1) Subgroup.mem_bot.symm

instance : DecidablePred (· ∈ (⊤ : Subgroup S4)) := fun _ => isTrue (Subgroup.mem_top _)

end Wc

section DihedralD

open S4

def dFin : Finset S4 := dList.toFinset
def vFin : Finset S4 := vList.toFinset
def v'Fin : Finset S4 := v'List.toFinset

set_option maxRecDepth 100000 in
theorem elemAbelian_finset_D :
    ∀ S ∈ dFin.powerset, (1 : S4) ∈ S → (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) →
      (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) → (∀ x ∈ S, x * x = 1) →
      S.card ≤ 4 ∧ (S.card = 4 → S = vFin ∨ S = v'Fin) := by
  decide +kernel

theorem card_eq_finset_card {X : Type*} [Group X] [Fintype X] (F : Subgroup X)
    [DecidablePred (· ∈ F)] : Nat.card F = (Finset.univ.filter (· ∈ F)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_le_four_of_elemAbelian {F : Subgroup S4} (hF : F ≤ D) (hE : IsElemAbelian 2 F) :
    Nat.card F ≤ 4 ∧ (Nat.card F = 4 → F = V ∨ F = V') := by
  classical
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy => by
    have := hE.1
    exact setLike_mul_comm hx hy
  have hsq : ∀ x ∈ F, x * x = 1 := fun x hx => by
    have := hE.2 x hx
    rwa [pow_two] at this
  set S : Finset S4 := Finset.univ.filter (· ∈ F) with hS
  have hmemS : ∀ x, x ∈ S ↔ x ∈ F := fun x => by simp [hS]
  have hSD : S ∈ dFin.powerset := by
    rw [Finset.mem_powerset]
    intro x hx
    have := hF ((hmemS x).1 hx)
    simpa [dFin, mem_D] using this
  obtain ⟨h1, h2⟩ := elemAbelian_finset_D S hSD ((hmemS _).2 F.one_mem)
    (fun x hx y hy => (hmemS _).2 (F.mul_mem ((hmemS _).1 hx) ((hmemS _).1 hy)))
    (fun x hx y hy => hcomm x ((hmemS _).1 hx) y ((hmemS _).1 hy))
    (fun x hx => hsq x ((hmemS _).1 hx))
  rw [card_eq_finset_card]
  refine ⟨h1, fun h4 => ?_⟩
  rcases h2 h4 with h | h
  · left
    ext x
    rw [← hmemS, h]
    simp [vFin, mem_V]
  · right
    ext x
    rw [← hmemS, h]
    simp [v'Fin, mem_V']

end DihedralD

section Named

open S4 Wc

def Th : Subgroup Wc := symSub D
def Jh : Subgroup Wc := baseSub D D
def A1 : Subgroup Wc := baseSub V V
def A2 : Subgroup Wc := baseSub V' V'
def A3 : Subgroup Wc := baseSub V' V
def A4 : Subgroup Wc := baseSub V V'
def T1h : Subgroup Wc := baseSub D ⊥
def T2h : Subgroup Wc := baseSub ⊥ D
def M1h : Subgroup Wc := baseSub ⊤ ⊥
def M2h : Subgroup Wc := baseSub ⊥ ⊤
def Mbase : Subgroup Wc := baseSub ⊤ ⊤

instance : DecidablePred (· ∈ Th) := inferInstanceAs (DecidablePred (· ∈ symSub D))
instance : DecidablePred (· ∈ Jh) := inferInstanceAs (DecidablePred (· ∈ baseSub D D))
instance : DecidablePred (· ∈ A1) := inferInstanceAs (DecidablePred (· ∈ baseSub V V))
instance : DecidablePred (· ∈ A2) := inferInstanceAs (DecidablePred (· ∈ baseSub V' V'))
instance : DecidablePred (· ∈ A3) := inferInstanceAs (DecidablePred (· ∈ baseSub V' V))
instance : DecidablePred (· ∈ A4) := inferInstanceAs (DecidablePred (· ∈ baseSub V V'))
instance : DecidablePred (· ∈ T1h) := inferInstanceAs (DecidablePred (· ∈ baseSub D ⊥))
instance : DecidablePred (· ∈ T2h) := inferInstanceAs (DecidablePred (· ∈ baseSub ⊥ D))
instance : DecidablePred (· ∈ M1h) := inferInstanceAs (DecidablePred (· ∈ baseSub ⊤ ⊥))
instance : DecidablePred (· ∈ M2h) := inferInstanceAs (DecidablePred (· ∈ baseSub ⊥ ⊤))
instance : DecidablePred (· ∈ Mbase) := inferInstanceAs (DecidablePred (· ∈ baseSub ⊤ ⊤))

theorem card_Th : Nat.card Th = 128 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem card_Wc' : Nat.card Wc = 1152 := by
  rw [Nat.card_eq_fintype_card]
  exact Wc.card_Wc

theorem baseSub_eq_map (X Y : Subgroup S4) : baseSub X Y = (X.prod Y).map inclBase := by
  ext x
  simp only [mem_baseSub, Subgroup.mem_map, Subgroup.mem_prod]
  constructor
  · rintro ⟨he, ha, hb⟩
    refine ⟨(x.a, x.b), ⟨ha, hb⟩, ?_⟩
    rcases x with ⟨a, b, e⟩
    simp only at he
    subst he
    rfl
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨rfl, ha, hb⟩

theorem card_baseSub (X Y : Subgroup S4) :
    Nat.card (baseSub X Y) = Nat.card X * Nat.card Y := by
  rw [baseSub_eq_map, Subgroup.card_map_of_injective inclBase_injective,
    Nat.card_congr (Subgroup.prodEquiv X Y).toEquiv, Nat.card_prod]

theorem isElemAbelian_baseSub {X Y : Subgroup S4} (hX : IsElemAbelian 2 X)
    (hY : IsElemAbelian 2 Y) : IsElemAbelian 2 (baseSub X Y) := by
  have := hX.1
  have := hY.1
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨hxe, hxa, hxb⟩ := x.2
    obtain ⟨hye, hya, hyb⟩ := y.2
    show (x : Wc) * y = y * x
    rw [mul_of_e_false hxe, mul_of_e_false hye]
    exact ext (setLike_mul_comm hxa hya) (setLike_mul_comm hxb hyb) (by rw [hxe, hye])
  · obtain ⟨hxe, hxa, hxb⟩ := hx
    rw [pow_two, mul_of_e_false hxe]
    refine ext ?_ ?_ ?_
    · have := hX.2 _ hxa
      rwa [pow_two] at this
    · have := hY.2 _ hxb
      rwa [pow_two] at this
    · exact hxe

theorem isElemAbelian_of_forall {X : Type*} [Group X] (F : Subgroup X)
    (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hs : ∀ x ∈ F, x * x = 1) : IsElemAbelian 2 F :=
  ⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, fun x hx => by rw [pow_two]; exact hs x hx⟩

theorem isElemAbelian_map {H K : Type*} [Group H] [Group K] {E : Subgroup H}
    (hE : IsElemAbelian 2 E) (f : H →* K) : IsElemAbelian 2 (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_comap {H K : Type*} [Group H] [Group K] {E : Subgroup K}
    (hE : IsElemAbelian 2 E) {f : H →* K} (hf : Function.Injective f) :
    IsElemAbelian 2 (E.comap f) := by
  have := hE.1
  refine isElemAbelian_of_forall _ ?_ ?_
  · intro x hx y hy
    apply hf
    rw [map_mul, map_mul]
    exact setLike_mul_comm (Subgroup.mem_comap.mp hx) (Subgroup.mem_comap.mp hy)
  · intro x hx
    apply hf
    rw [map_mul, map_one]
    have := hE.2 _ (Subgroup.mem_comap.mp hx)
    rwa [pow_two] at this

theorem isElemAbelian_of_le {X : Type*} [Group X] {E F : Subgroup X} (hE : IsElemAbelian 2 E)
    (h : F ≤ E) : IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE h

theorem elemAbelian_le_Jh {E : Subgroup Wc} (hE : E ≤ Jh) (hEa : IsElemAbelian 2 E) :
    Nat.card E ≤ 16 ∧ (Nat.card E = 16 → ∃ X Y : Subgroup S4, (X = V ∨ X = V') ∧
      (Y = V ∨ Y = V') ∧ E = baseSub X Y) := by
  classical
  set E' : Subgroup (S4 × S4) := E.comap inclBase with hE'
  have hEE' : E = E'.map inclBase := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxe, -, -⟩ := hE hx
      have hx' : inclBase (x.a, x.b) = x := by
        rcases x with ⟨a, b, e⟩
        simp only at hxe
        subst hxe
        rfl
      exact ⟨(x.a, x.b), by show inclBase (x.a, x.b) ∈ E; rw [hx']; exact hx, hx'⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  have hcard : Nat.card E = Nat.card E' := by
    conv_lhs => rw [hEE']
    exact Subgroup.card_map_of_injective inclBase_injective
  have hE'a : IsElemAbelian 2 E' := isElemAbelian_comap hEa inclBase_injective
  set E1 : Subgroup S4 := E'.map (MonoidHom.fst S4 S4) with hE1
  set E2 : Subgroup S4 := E'.map (MonoidHom.snd S4 S4) with hE2
  have hE1D : E1 ≤ D := by
    rintro _ ⟨p, hp, rfl⟩
    have : inclBase p ∈ Jh := hE hp
    exact this.2.1
  have hE2D : E2 ≤ D := by
    rintro _ ⟨p, hp, rfl⟩
    have : inclBase p ∈ Jh := hE hp
    exact this.2.2
  obtain ⟨h1, h1'⟩ := card_le_four_of_elemAbelian hE1D (isElemAbelian_map hE'a _)
  obtain ⟨h2, h2'⟩ := card_le_four_of_elemAbelian hE2D (isElemAbelian_map hE'a _)
  have hle : E' ≤ E1.prod E2 := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  have hprod : Nat.card (E1.prod E2) = Nat.card E1 * Nat.card E2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv E1 E2).toEquiv, Nat.card_prod]
  have hcle : Nat.card E' ≤ Nat.card E1 * Nat.card E2 := hprod ▸ Subgroup.card_le_of_le hle
  refine ⟨by rw [hcard]; nlinarith, fun h16 => ?_⟩
  rw [hcard] at h16
  have e1 : Nat.card E1 = 4 := by nlinarith
  have e2 : Nat.card E2 = 4 := by nlinarith
  have heq : E' = E1.prod E2 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hprod, e1, e2, h16])
  refine ⟨E1, E2, h1' e1, h2' e2, ?_⟩
  rw [hEE', heq, baseSub_eq_map]

theorem V_le_D : V ≤ D := fun x hx => by
  have : ∀ y ∈ vList, y ∈ dList := by decide +kernel
  exact this x hx

theorem V'_le_D : V' ≤ D := fun x hx => by
  have : ∀ y ∈ v'List, y ∈ dList := by decide +kernel
  exact this x hx

theorem card_V : Nat.card V = 4 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem card_V' : Nat.card V' = 4 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem card_D : Nat.card D = 8 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem isElemAbelian_V : IsElemAbelian 2 V := by
  refine isElemAbelian_of_forall _ ?_ ?_
  · intro x hx y hy
    have : ∀ x ∈ vList, ∀ y ∈ vList, x * y = y * x := by decide +kernel
    exact this x hx y hy
  · intro x hx
    have : ∀ x ∈ vList, x * x = 1 := by decide +kernel
    exact this x hx

theorem isElemAbelian_V' : IsElemAbelian 2 V' := by
  refine isElemAbelian_of_forall _ ?_ ?_
  · intro x hx y hy
    have : ∀ x ∈ v'List, ∀ y ∈ v'List, x * y = y * x := by decide +kernel
    exact this x hx y hy
  · intro x hx
    have : ∀ x ∈ v'List, x * x = 1 := by decide +kernel
    exact this x hx

theorem baseSub_le_symSub {X Y D' : Subgroup S4} (hX : X ≤ D') (hY : Y ≤ D') :
    baseSub X Y ≤ symSub D' := fun _ hx => ⟨hX hx.2.1, hY hx.2.2⟩

theorem baseSub_le_baseSub {X Y X' Y' : Subgroup S4} (hX : X ≤ X') (hY : Y ≤ Y') :
    baseSub X Y ≤ baseSub X' Y' := fun _ hx => ⟨hx.1, hX hx.2.1, hY hx.2.2⟩

theorem A1_le_Th : A1 ≤ Th := baseSub_le_symSub V_le_D V_le_D
theorem A2_le_Th : A2 ≤ Th := baseSub_le_symSub V'_le_D V'_le_D
theorem A3_le_Th : A3 ≤ Th := baseSub_le_symSub V'_le_D V_le_D
theorem A4_le_Th : A4 ≤ Th := baseSub_le_symSub V_le_D V'_le_D

theorem card_A1 : Nat.card A1 = 16 := by rw [A1, card_baseSub, card_V]
theorem card_A2 : Nat.card A2 = 16 := by rw [A2, card_baseSub, card_V']
theorem card_A3 : Nat.card A3 = 16 := by rw [A3, card_baseSub, card_V, card_V']
theorem card_A4 : Nat.card A4 = 16 := by rw [A4, card_baseSub, card_V, card_V']

theorem isElemAbelian_A1 : IsElemAbelian 2 A1 := isElemAbelian_baseSub isElemAbelian_V isElemAbelian_V
theorem isElemAbelian_A2 : IsElemAbelian 2 A2 :=
  isElemAbelian_baseSub isElemAbelian_V' isElemAbelian_V'
theorem isElemAbelian_A3 : IsElemAbelian 2 A3 :=
  isElemAbelian_baseSub isElemAbelian_V' isElemAbelian_V
theorem isElemAbelian_A4 : IsElemAbelian 2 A4 :=
  isElemAbelian_baseSub isElemAbelian_V isElemAbelian_V'

theorem card_le_eight_of_exists_swap {E : Subgroup Wc} (hE : E ≤ Th) (hEa : IsElemAbelian 2 E)
    {g : Wc} (hg : g ∈ E) (hge : g.e = true) : Nat.card E ≤ 8 := by
  classical
  set E₀ : Subgroup Wc := E ⊓ Jh with hE₀
  have hE₀a : IsElemAbelian 2 E₀ := isElemAbelian_of_le hEa inf_le_left
  have hmem : ∀ b : E, b ∈ E₀.subgroupOf E ↔ b.1.e = false := by
    intro b
    constructor
    · intro h
      exact h.2.1
    · intro h
      exact ⟨b.2, h, (hE b.2).1, (hE b.2).2⟩
  have hidx : (E₀.subgroupOf E).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hg⟩, fun b => ?_⟩
    have h1 := hmem (b * ⟨g, hg⟩)
    have h2 := hmem b
    rw [Subgroup.coe_mul] at h1
    rw [h1, h2]
    rcases hb : b.1.e with _ | _
    · rw [mul_of_e_false hb]
      simp [hge]
    · rw [mul_of_e_true hb]
      simp [hge]
  have hcardE : Nat.card E = Nat.card E₀ * 2 := by
    have := Subgroup.card_mul_index (E₀.subgroupOf E)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E₀ ≤ E)).toEquiv] at this
    exact this.symm
  have hE₀J : E₀ ≤ Jh := inf_le_right
  set F : Subgroup (S4 × S4) := E₀.comap inclBase with hF
  have hEF : E₀ = F.map inclBase := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxe, -, -⟩ := hE₀J hx
      have hx' : inclBase (x.a, x.b) = x := by
        rcases x with ⟨a, b, e⟩
        simp only at hxe
        subst hxe
        rfl
      exact ⟨(x.a, x.b), by show inclBase (x.a, x.b) ∈ E₀; rw [hx']; exact hx, hx'⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  have hcardF : Nat.card E₀ = Nat.card F := by
    conv_lhs => rw [hEF]
    exact Subgroup.card_map_of_injective inclBase_injective
  set F2 : Subgroup S4 := F.map (MonoidHom.snd S4 S4) with hF2
  have hF2D : F2 ≤ D := by
    rintro _ ⟨p, hp, rfl⟩
    have : inclBase p ∈ Jh := hE₀J hp
    exact this.2.2
  have hF2a : IsElemAbelian 2 F2 :=
    isElemAbelian_map (isElemAbelian_comap hE₀a inclBase_injective) _
  have hcardF2 : Nat.card F2 ≤ 4 := (card_le_four_of_elemAbelian hF2D hF2a).1
  have hrel : ∀ p ∈ F, p.1 = g.a * p.2 * g.a⁻¹ := by
    intro p hp
    have hpE : inclBase p ∈ E := (show inclBase p ∈ E₀ from hp).1
    have hc : inclBase p * g = g * inclBase p := by
      have := hEa.1
      exact setLike_mul_comm hpE hg
    have hc' := congrArg Wc.a hc
    rw [show inclBase p = ⟨p.1, p.2, false⟩ from rfl, mul_of_e_false rfl,
      mul_of_e_true hge] at hc'
    simp only at hc'
    exact eq_mul_inv_of_mul_eq hc'
  have hinj : Function.Injective (fun p : F => (⟨p.1.2, ⟨p.1, p.2, rfl⟩⟩ : F2)) := by
    intro p q hpq
    have h2 : p.1.2 = q.1.2 := congrArg (fun u : F2 => u.1) hpq
    have h1 : p.1.1 = q.1.1 := by rw [hrel p.1 p.2, hrel q.1 q.2, h2]
    exact Subtype.ext (Prod.ext h1 h2)
  have hFle : Nat.card F ≤ Nat.card F2 := Nat.card_le_card_of_injective _ hinj
  omega

theorem elemAbelian_le_Th {E : Subgroup Wc} (hE : E ≤ Th) (hEa : IsElemAbelian 2 E) :
    Nat.card E ≤ 16 ∧ (Nat.card E = 16 → E = A1 ∨ E = A2 ∨ E = A3 ∨ E = A4) := by
  by_cases hbase : ∀ x ∈ E, x.e = false
  · have hEJ : E ≤ Jh := fun x hx => ⟨hbase x hx, (hE hx).1, (hE hx).2⟩
    obtain ⟨h1, h2⟩ := elemAbelian_le_Jh hEJ hEa
    refine ⟨h1, fun h16 => ?_⟩
    obtain ⟨X, Y, hX, hY, rfl⟩ := h2 h16
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  · obtain ⟨g, hg, hge⟩ : ∃ g ∈ E, g.e = true := by
      by_contra hne
      apply hbase
      intro x hx
      by_contra hxe
      exact hne ⟨x, hx, by simpa using hxe⟩
    have := card_le_eight_of_exists_swap hE hEa hg hge
    exact ⟨by omega, fun h16 => by omega⟩

theorem isMaxElemAbelian_Th_iff (E : Subgroup Wc) :
    IsMaxElemAbelian Th E ↔ E = A1 ∨ E = A2 ∨ E = A3 ∨ E = A4 := by
  constructor
  · rintro ⟨hE, hEa, hmax⟩
    have h16 : 16 ≤ Nat.card E := by
      have := hmax A1 A1_le_Th isElemAbelian_A1
      rwa [card_A1] at this
    obtain ⟨hle, hcl⟩ := elemAbelian_le_Th hE hEa
    exact hcl (le_antisymm hle h16)
  · intro h
    have key : ∀ F : Subgroup Wc, F ≤ Th → IsElemAbelian 2 F → Nat.card F = 16 →
        IsMaxElemAbelian Th F := fun F hF hFa hc =>
      ⟨hF, hFa, fun B hB hBa => hc ▸ (elemAbelian_le_Th hB hBa).1⟩
    rcases h with rfl | rfl | rfl | rfl
    · exact key _ A1_le_Th isElemAbelian_A1 card_A1
    · exact key _ A2_le_Th isElemAbelian_A2 card_A2
    · exact key _ A3_le_Th isElemAbelian_A3 card_A3
    · exact key _ A4_le_Th isElemAbelian_A4 card_A4

end Named

end CFSG.Quasithin.A10
