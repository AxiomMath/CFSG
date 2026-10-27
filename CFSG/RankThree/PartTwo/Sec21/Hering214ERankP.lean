module

import CFSG.RankThree.PartOne.S11d.Common
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.KFacts.KP14Monomial

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eq_one_of_central_pow_three_pow {L : Subgroup G}
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center L)) (k : ℕ) :
    ∀ y : L, (∀ h : L, h * y = y * h) → y ^ 3 ^ k = 1 → y = 1 := by
  induction k with
  | zero => intro y _ hy; simpa using hy
  | succ k ih =>
    intro y hyc hy
    have hc3 : ∀ h : L, h * y ^ 3 = y ^ 3 * h := fun h =>
      (show Commute h y from hyc h).pow_right 3
    have h3 : (y ^ 3) ^ 3 ^ k = 1 := by
      have e : 3 * 3 ^ k = 3 ^ (k + 1) := by ring
      rw [← pow_mul, e]
      exact hy
    have hy3 : y ^ 3 = 1 := ih (y ^ 3) hc3 h3
    exact CFSG.RankThree.PartOne.S11d.eq_one_of_mem_center_of_pow Nat.prime_three hZ
      (Subgroup.mem_center_iff.mpr hyc) hy3

theorem exists_elemAbelian_nine_le_centralizer {E L : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27)
    (hsplit : ∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Subgroup.centralizer (L : Set G), e = l * z)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center L))
    (hEL : Nat.card (E ⊓ L : Subgroup G) ≤ 3) :
    ∃ P : Subgroup G, P ≤ Subgroup.centralizer (L : Set G) ∧ IsElemAbelian 3 P ∧
      Nat.card P = 9 ∧ P ⊓ L = ⊥ := by
  set C : Subgroup G := Subgroup.centralizer (L : Set G)
  have hcomm : ∀ (x : L) (y : C), Commute (x : G) (y : G) := fun x y =>
    Subgroup.mem_centralizer_iff.mp y.2 (x : G) x.2
  obtain ⟨μ, hμ⟩ : ∃ μ : L × C →* G, ∀ x : L × C, μ x = (x.1 : G) * (x.2 : G) :=
    ⟨L.subtype.noncommCoprod C.subtype hcomm, fun _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : L × C →* G, ∀ x : L × C, ν x = (x.2 : G) :=
    ⟨C.subtype.comp (MonoidHom.snd L C), fun _ => rfl⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    haveI := hE.1
    intro a ha b hb
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEe : ∀ a ∈ E, a ^ 3 = 1 := hE.2
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (L × C), ∀ x : L × C, x ∈ A ↔ μ x ∈ E :=
    ⟨E.comap μ, fun x => Subgroup.mem_comap⟩
  have hA27 : 27 ∣ Nat.card A := by
    have hrange : (μ.comp A.subtype).range = E := by
      ext e
      constructor
      · rintro ⟨a, rfl⟩
        exact (hA a.1).mp a.2
      · intro he
        obtain ⟨l, hl, z, hz, rfl⟩ := hsplit e he
        refine MonoidHom.mem_range.mpr ⟨⟨(⟨l, hl⟩, ⟨z, hz⟩), (hA _).mpr ?_⟩, ?_⟩
        · rw [hμ]
          exact he
        · rw [MonoidHom.comp_apply, hμ]
          rfl
    have h := Subgroup.card_range_dvd (μ.comp A.subtype)
    rw [hrange, hE27] at h
    exact h
  have h27 : 3 ^ 3 ∣ Nat.card A := by
    norm_num
    exact hA27
  obtain ⟨S, hScard, hSA⟩ : ∃ S : Subgroup (L × C), Nat.card S = 27 ∧ S ≤ A := by
    obtain ⟨K, hK⟩ : ∃ K : Subgroup A, Nat.card K = 3 ^ 3 :=
      Sylow.exists_subgroup_card_pow_prime 3 h27
    exact ⟨K.map A.subtype, by rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
      <;> norm_num, Subgroup.map_subtype_le K⟩
  have hSmem : ∀ x ∈ S, μ x ∈ E := fun x hx => (hA x).mp (hSA hx)
  have hμinj : ∀ x ∈ S, μ x = 1 → x = 1 := by
    intro x hx hμx
    have hlC : ((x.1 : L) : G) ∈ C := by
      have h1 : ((x.1 : L) : G) = ((x.2 : C) : G)⁻¹ := by
        have h := hμx
        rw [hμ] at h
        exact eq_inv_of_mul_eq_one_left h
      rw [h1]
      exact C.inv_mem x.2.2
    have hcentre : ∀ h : L, h * x.1 = x.1 * h := fun h =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hlC (h : G) h.2)
    have hx27 : x ^ 27 = 1 := by
      have h := pow_card_eq_one' (G := S) (x := ⟨x, hx⟩)
      rw [hScard] at h
      simpa using congrArg Subtype.val h
    have hl1 : x.1 = 1 := by
      have hpow : x.1 ^ 3 ^ 3 = 1 := by
        simpa using congrArg Prod.fst hx27
      exact eq_one_of_central_pow_three_pow hZ3 3 x.1 hcentre hpow
    have hz1 : ((x.2 : C) : G) = 1 := by
      have h := hμx
      rw [hμ, hl1] at h
      simpa using h
    exact Prod.ext hl1 (Subtype.ext hz1)
  have hinj : ∀ x ∈ S, ∀ y ∈ S, μ x = μ y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ = 1 := hμinj _ (S.mul_mem hx (S.inv_mem hy)) (by
      rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    apply hinj _ (S.mul_mem hx hy) _ (S.mul_mem hy hx)
    rw [map_mul, map_mul]
    exact hEc _ (hSmem x hx) _ (hSmem y hy)
  have hSexp : ∀ x ∈ S, x ^ 3 = 1 := by
    intro x hx
    apply hμinj _ (S.pow_mem hx 3)
    rw [map_pow]
    exact hEe _ (hSmem x hx)
  have hSab : IsElemAbelian 3 S := by
    refine And.intro ?_ ?_
    · exact ⟨⟨fun a b => Subtype.ext (hScomm a a.2 b b.2)⟩⟩
    · exact fun x hx => hSexp x hx
  have hS'ab : IsElemAbelian 3 (S.map ν) := CFSG.SectionRank.isElemAbelian_map hSab ν
  have hker : Nat.card (ν.comp S.subtype).ker ≤ 3 := by
    have hmem : ∀ y : (ν.comp S.subtype).ker, μ ((y : S) : L × C) ∈ E ⊓ L := by
      intro y
      have hy1 : ν ((y : S) : L × C) = 1 := MonoidHom.mem_ker.mp y.2
      rw [hν] at hy1
      rw [Subgroup.mem_inf]
      refine ⟨hSmem _ (y : S).2, ?_⟩
      rw [hμ, hy1, mul_one]
      exact ((y : S) : L × C).1.2
    have hg : Function.Injective (fun y : (ν.comp S.subtype).ker =>
        (⟨μ ((y : S) : L × C), hmem y⟩ : (E ⊓ L : Subgroup G))) := by
      intro y y' h
      have h' : μ ((y : S) : L × C) = μ ((y' : S) : L × C) := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (hinj _ (y : S).2 _ (y' : S).2 h'))
    exact (Nat.card_le_card_of_injective _ hg).trans hEL
  have hrangeP : (ν.comp S.subtype).range = S.map ν := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨⟨y, hy⟩, rfl⟩
  have hprod : Nat.card (ν.comp S.subtype).ker * Nat.card (S.map ν) = 27 := by
    have h := Subgroup.card_ker_mul_card_range (ν.comp S.subtype)
    rw [hrangeP, hScard] at h
    exact h
  have key : ∀ a b : ℕ, a * b = 27 → b ≤ 3 → 9 ∣ a := by
    intro a b h hb
    interval_cases b <;> omega
  have h9 : 3 ^ 2 ∣ Nat.card (S.map ν) :=
    key _ _ (by rw [mul_comm]; exact hprod) hker
  obtain ⟨P, hPle, hPcard⟩ : ∃ P : Subgroup G, P ≤ S.map ν ∧ Nat.card P = 9 := by
    obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (S.map ν), Nat.card Q = 3 ^ 2 :=
      Sylow.exists_subgroup_card_pow_prime 3 h9
    exact ⟨Q.map (S.map ν).subtype, Subgroup.map_subtype_le Q, by
      rw [Subgroup.card_map_of_injective (S.map ν).subtype_injective, hQ] <;> norm_num⟩
  have hS'C : S.map ν ≤ C := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hν]
    exact y.2.2
  have hPC : P ≤ C := hPle.trans hS'C
  have hP'comm : ∀ a ∈ S.map ν, ∀ b ∈ S.map ν, a * b = b * a := by
    intro a ha b hb
    haveI := hS'ab.1
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := S.map ν)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPab : IsElemAbelian 3 P := by
    refine And.intro ?_ ?_
    · exact ⟨⟨fun a b => Subtype.ext (hP'comm a (hPle a.2) b (hPle b.2))⟩⟩
    · exact fun x hx => hS'ab.2 x (hPle hx)
  have hPL : P ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxL⟩ := Subgroup.mem_inf.mp hx
    have hxC : x ∈ C := hPC hxP
    have hcentre : ∀ h : L, h * (⟨x, hxL⟩ : L) = (⟨x, hxL⟩ : L) * h := fun h =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (h : G) h.2)
    have h9x : x ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := P) (x := ⟨x, hxP⟩)
      rw [hPcard] at h
      simpa using congrArg Subtype.val h
    have hx1 : (⟨x, hxL⟩ : L) = 1 :=
      eq_one_of_central_pow_three_pow hZ3 2 ⟨x, hxL⟩ hcentre
        (Subtype.ext (by simpa using h9x))
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1)
  exact ⟨P, hPC, hPab, hPcard, hPL⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
