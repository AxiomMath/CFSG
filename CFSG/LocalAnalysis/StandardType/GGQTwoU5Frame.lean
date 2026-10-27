module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeComponent
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeBasic
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.StandardType.QTwo.U5

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

@[expose] def conjHom (P T : Subgroup G) (hPT : P ≤ normalizer (T : Set G)) : P →* MulAut T where
  toFun g :=
    { toFun := fun t => ⟨g * t * (g : G)⁻¹, (mem_normalizer_iff.1 (hPT g.2) t).1 t.2⟩
      invFun := fun t => ⟨(g : G)⁻¹ * t * g, by
        simpa using (mem_normalizer_iff.1 (hPT (inv_mem g.2)) t).1 t.2⟩
      left_inv := fun t => by ext; simp [mul_assoc]
      right_inv := fun t => by ext; simp [mul_assoc]
      map_mul' := fun s t => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun g h => by ext; simp [mul_assoc]

end CFSG.StandardType.QTwo.U5

namespace CFSG.StandardType.QTwo.U5

open Subgroup CFSG.Open
open CFSG.GGQ2Prime (component_normal)

variable {G : Type*} [Group G] [Finite G]

theorem mem_zpowers_of_cyclic_exp_three {P : Subgroup G} [IsCyclic P] (hP : ∀ g ∈ P, g ^ 3 = 1)
    {x w : G} (hxP : x ∈ P) (hx1 : x ≠ 1) (hwP : w ∈ P) : w ∈ zpowers x := by
  have hexp : Monoid.exponent P ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hP g g.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  have hxle : zpowers x ≤ P := (zpowers_le).2 hxP
  have hcx : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    have h3 : x ^ 3 = 1 := hP x hxP
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hcP : Nat.card P = 3 := by
    have := Subgroup.card_dvd_of_le hxle
    rw [hcx] at this
    exact Nat.dvd_antisymm hexp this
  have heq : zpowers x = P := Subgroup.eq_of_le_of_card_ge hxle (by rw [hcx, hcP])
  rw [heq]; exact hwP

theorem lemma_9_2 {B L : Subgroup G} {x : G} (hB : IsElemAbelian 3 B) (hxB : x ∈ B)
    (hx1 : x ≠ 1) (hL : IsComponentOf L (centralizer ({x} : Set G)))
    (hcyc : ∀ S : Subgroup G, S ≤ centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (hinner : ∀ b ∈ B, ∃ l ∈ L, ∀ y ∈ L, b * y * b⁻¹ = l * y * l⁻¹)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center L))
    (hnorm2 : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ normalizer (L : Set G) →
      B ≤ normalizer (T : Set G) → T ≤ centralizer (L : Set G))
    (T : Subgroup G) (hT2 : IsPGroup 2 T) (hTx : T ≤ centralizer ({x} : Set G))
    (hBT : B ≤ normalizer (T : Set G)) : ∀ b ∈ B, ∀ t ∈ T, b * t = t * b := by
  obtain ⟨S, hSL, hSp, hSnc⟩ := hnc
  have hLn : centralizer ({x} : Set G) ≤ normalizer (L : Set G) :=
    component_normal hL hcyc hSL hSp hSnc
  have hTL : T ≤ centralizer (L : Set G) := hnorm2 T hT2 (hTx.trans hLn) hBT
  have hLx : L ≤ centralizer ({x} : Set G) := hL.1
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have := hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  intro b hb t ht
  obtain ⟨l, hl, hly⟩ := hinner b hb
  set c := l⁻¹ * b with hc
  have hcL : c ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have := hly y hy
    simp only [hc]
    calc y * (l⁻¹ * b) = l⁻¹ * (l * y * l⁻¹) * b := by group
      _ = l⁻¹ * (b * y * b⁻¹) * b := by rw [this]
      _ = l⁻¹ * b * y := by group
  have hlt : l * t = t * l := ((mem_centralizer_iff.1 (hTL ht)) l hl)
  have hxc : x * c = c * x := by
    have h1 : x * l = l * x := (mem_centralizer_singleton_iff.1 (hLx hl)).symm
    have h2 : x * b = b * x := hBc x hxB b hb
    simp only [hc]
    calc x * (l⁻¹ * b) = l⁻¹ * (l * x * l⁻¹) * b := by group
      _ = l⁻¹ * x * b := by rw [show l * x * l⁻¹ = x by rw [← h1]; group]
      _ = l⁻¹ * b * x := by rw [mul_assoc, h2, ← mul_assoc]
  have hcl : l * c = c * l := (mem_centralizer_iff.1 hcL l hl)
  have hbeq : b = l * c := by simp [hc]
  have hc3L : c ^ 3 ∈ L := by
    have hb3 : b ^ 3 = 1 := hB.2 b hb
    rw [hbeq, Commute.mul_pow hcl 3] at hb3
    rw [eq_inv_of_mul_eq_one_right hb3]
    exact inv_mem (pow_mem hl 3)
  have hc3C : c ^ 3 ∈ centralizer (L : Set G) := pow_mem hcL 3
  set n := Nat.card (Subgroup.center L) with hn
  have hc3n : (c ^ 3) ^ n = 1 := by
    have hz : (⟨c ^ 3, hc3L⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((mem_centralizer_iff.1 hc3C) y y.2)
    have h1 := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨⟨c ^ 3, hc3L⟩, hz⟩)
    have h2 := congrArg (fun z : Subgroup.center L => ((z : L) : G)) h1
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hZ
  have hbez : ((Nat.gcd 3 n : ℕ) : ℤ) = 3 * Nat.gcdA 3 n + n * Nat.gcdB 3 n :=
    Nat.gcd_eq_gcd_ab 3 n
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set w := (c ^ n) ^ Nat.gcdB 3 n with hw
  have hcsplit : c = (c ^ 3) ^ Nat.gcdA 3 n * w := by
    calc c = c ^ (1 : ℤ) := (zpow_one c).symm
      _ = c ^ ((3 : ℤ) * Nat.gcdA 3 n + (n : ℤ) * Nat.gcdB 3 n) := by rw [← hbez]
      _ = (c ^ 3) ^ Nat.gcdA 3 n * w := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_ofNat, zpow_natCast]
  have hw3 : w ^ 3 = 1 := by
    calc w ^ 3 = w ^ (3 : ℤ) := (zpow_ofNat w 3).symm
      _ = (c ^ n) ^ (Nat.gcdB 3 n * 3) := by rw [hw, zpow_mul]
      _ = (c ^ n) ^ ((3 : ℤ) * Nat.gcdB 3 n) := by rw [mul_comm]
      _ = ((c ^ n) ^ (3 : ℤ)) ^ Nat.gcdB 3 n := by rw [zpow_mul]
      _ = ((c ^ 3) ^ n) ^ Nat.gcdB 3 n := by rw [zpow_ofNat, ← pow_mul, ← pow_mul, mul_comm n 3]
      _ = 1 := by rw [hc3n, one_zpow]
  have hwC : w ∈ centralizer (L : Set G) := zpow_mem (pow_mem hcL n) _
  have hwx : w * x = x * w := by
    have hcx : Commute c x := hxc.symm
    exact (hcx.pow_left n).zpow_left _
  have hxC : x ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_singleton_iff.1 (hLx hy))
  set P := closure ({w, x} : Set G) with hPdef
  have hcomm : ∀ a ∈ ({w, x} : Set G), ∀ a' ∈ ({w, x} : Set G), a * a' = a' * a := by
    intro a ha a' ha'
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · rfl
    · exact hwx
    · exact hwx.symm
    · rfl
  have hPcomm : ∀ a ∈ P, ∀ a' ∈ P, a * a' = a' * a := by
    intro a ha a' ha'
    have := (Subgroup.closureCommGroupOfComm (fun a ha a' ha' _ => hcomm a ha a' ha')).mul_comm ⟨a, ha⟩ ⟨a', ha'⟩
    simpa using congrArg Subtype.val this
  have hP3 : ∀ g ∈ P, g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
        rcases ha with rfl | rfl
        · exact hw3
        · exact hB.2 _ hxB
    | one => simp
    | mul a a' ha ha' iha iha' =>
        rw [Commute.mul_pow (hPcomm a ha a' ha') 3, iha, iha', one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hPC : P ≤ centralizer (L : Set G) := by
    rw [closure_le]
    intro a ha
    rcases ha with rfl | rfl
    · exact hwC
    · exact hxC
  have hPp : IsPGroup 3 P := fun g => ⟨1, Subtype.ext (by simpa using hP3 g g.2)⟩
  haveI := hcyc P hPC hPp
  have hwz : w ∈ zpowers x :=
    mem_zpowers_of_cyclic_exp_three hP3 (subset_closure (by simp)) hx1
      (subset_closure (by simp))
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hwz
  have htx : x * t = t * x := (mem_centralizer_singleton_iff.1 (hTx ht)).symm
  have hwt : w * t = t * w := by
    rw [← hk]
    exact Commute.zpow_left htx k
  have hut : (c ^ 3) ^ Nat.gcdA 3 n * t = t * (c ^ 3) ^ Nat.gcdA 3 n :=
    (mem_centralizer_iff.1 (hTL ht)) _ (zpow_mem hc3L _)
  have hct : c * t = t * c := by
    rw [hcsplit]
    exact Commute.mul_left hut hwt
  rw [hbeq]
  exact Commute.mul_left hlt hct

end CFSG.StandardType.QTwo.U5

end
