module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofCube
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG

section Generic

variable {G : Type} [Group G]

theorem i19_isElemAbelian_sup {E₁ E₂ : Subgroup G} (h₁ : CFSG.Assembly.IsElemAbelian 3 E₁)
    (h₂ : CFSG.Assembly.IsElemAbelian 3 E₂) (hc : ∀ x ∈ E₁, ∀ y ∈ E₂, Commute x y) :
    CFSG.Assembly.IsElemAbelian 3 (E₁ ⊔ E₂) := by
  have hpair : (((E₁ : Set G) ∪ (E₂ : Set G))).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact congrArg Subtype.val (h₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · exact hc x hx y hy
    · exact (hc y hy x hx).symm
    · exact congrArg Subtype.val (h₂.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcl : E₁ ⊔ E₂ = Subgroup.closure ((E₁ : Set G) ∪ (E₂ : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hcl]
  refine ⟨Subgroup.isMulCommutative_closure hpair, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact h₁.2 x hx
    · exact h₂.2 x hx
  | one => exact one_pow 3
  | mul x y hx hy hx1 hy1 =>
    have hxy : Commute x y := by
      have hcomm := Subgroup.isMulCommutative_closure hpair
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, hx1, hy1, mul_one]
  | inv x hx hx1 => rw [inv_pow, hx1, inv_one]

theorem i19_isElemAbelian_zpowers {x : G} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := by
  exact CFSG.Open.isElemAbelian_zpowers hx

theorem i19_isPGroup {H : Subgroup G} (hH : CFSG.Assembly.IsElemAbelian 3 H) : IsPGroup 3 H :=
  fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hH.2 g g.2)⟩

theorem i19_sup_zpowers [Finite G] {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    {x : G} (hx : x ^ 3 = 1) (hxE : x ∉ E) (hc : ∀ e ∈ E, Commute e x) :
    CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers x) ∧
      3 * Nat.card E ≤ Nat.card ↥(E ⊔ Subgroup.zpowers x) := by
  have hA : CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers x) := by
    refine i19_isElemAbelian_sup hE (i19_isElemAbelian_zpowers hx) (fun e he y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hc e he).zpow_right k
  refine ⟨hA, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (i19_isPGroup hE)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (i19_isPGroup hA)
  have hle : E ≤ E ⊔ Subgroup.zpowers x := le_sup_left
  have hdvd : Nat.card E ∣ Nat.card ↥(E ⊔ Subgroup.zpowers x) := Subgroup.card_dvd_of_le hle
  have hne : Nat.card E ≠ Nat.card ↥(E ⊔ Subgroup.zpowers x) := by
    intro h
    have hEq : E = E ⊔ Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge hle h.symm.le
    apply hxE
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [ha, hb] at hdvd hne ⊢
  have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hab' : a + 1 ≤ b := by
    rcases Nat.lt_or_ge a b with h | h
    · exact h
    · exact absurd (by rw [le_antisymm hab h]) hne
  calc 3 * 3 ^ a = 3 ^ (a + 1) := by ring
    _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hab'

end Generic

theorem ys03_I19_lift_E81 {Y : Type} [Group Y] [Finite Y] {Z N : Subgroup Y}
    (hZc : Z ≤ Subgroup.center Y) (hZ : CFSG.Assembly.IsElemAbelian 3 Z) (hZ1 : Z ≠ ⊥)
    (hZ9 : Nat.card Z ≤ 9) (hZN : Z ≤ N) (hcomm : ⁅N, N⁆ ≤ Z) (hcube : ∀ x ∈ N, x ^ 3 ∈ Z)
    (hbig : 81 * Nat.card Z ≤ Nat.card N) :
    ∃ E : Subgroup Y, E ≤ N ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ 27 ≤ Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ s ∈ N, ∀ t ∈ N, s * t * s⁻¹ * t⁻¹ ∈ Z := fun s hs t ht => by
    have h := hcomm (Subgroup.commutator_mem_commutator hs ht)
    rwa [commutatorElement_def] at h
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := hZ.2
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  let ω : ↥N →* ↥Z :=
    { toFun := fun c => ⟨(c : Y) ^ 3, hcube _ c.2⟩
      map_one' := by ext; simp
      map_mul' := fun c d => Subtype.ext (by
        have hdc := hc _ d.2 _ c.2
        exact Sec14.Res9ON.mul_pow_three_of_central (hZc hdc) (hz3 _ hdc)) }
  have hker : 81 ≤ Nat.card ω.ker := by
    have h1 := Sec14.Res9ON.card_eq_card_ker_mul_card_range ω
    have h2 : Nat.card ω.range ≤ Nat.card Z := Subgroup.card_le_card_group _
    have h3 : Nat.card N ≤ Nat.card ω.ker * Nat.card Z := h1 ▸ Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right (hbig.trans h3) hZpos
  set Ω : Subgroup Y := ω.ker.map N.subtype with hΩdef
  have hΩcard : Nat.card Ω = Nat.card ω.ker :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hΩmem : ∀ y ∈ Ω, y ∈ N ∧ y ^ 3 = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c.2, congrArg Subtype.val (MonoidHom.mem_ker.mp hc)⟩
  have hmemΩ : ∀ y ∈ N, y ^ 3 = 1 → y ∈ Ω := fun y hy h3 =>
    ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr (Subtype.ext h3), rfl⟩
  obtain ⟨x, hxΩ, hxZ⟩ : ∃ x ∈ Ω, x ∉ Z := by
    by_contra h
    push Not at h
    have : Nat.card Ω ≤ Nat.card Z := Subgroup.card_le_of_le (fun y hy => h y hy)
    omega
  obtain ⟨hxN, hx3⟩ := hΩmem x hxΩ
  have hZx : ∀ z ∈ Z, Commute z x := fun z hz => (Subgroup.mem_center_iff.mp (hZc hz) x).symm
  obtain ⟨hHab, hHcard⟩ := i19_sup_zpowers hZ hx3 hxZ hZx
  have hHN : Z ⊔ Subgroup.zpowers x ≤ N := sup_le hZN (Subgroup.zpowers_le.mpr hxN)
  by_cases h27 : 27 ≤ Nat.card ↥(Z ⊔ Subgroup.zpowers x)
  · exact ⟨_, hHN, hHab, h27⟩
  have hZ3 : Nat.card Z ≤ 3 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (i19_isPGroup hZ)
    have hn1 : n ≤ 1 := by
      by_contra hn1
      have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hcx : ∀ s ∈ Ω, s * x * s⁻¹ * x⁻¹ ∈ Z := fun s hs => hc s (hΩmem s hs).1 x hxN
  set χ := Sec14.Res9ON.commHom hZc x hcx with hχ
  have hχker : 27 ≤ Nat.card χ.ker := by
    have h1 := Sec14.Res9ON.card_eq_card_ker_mul_card_range χ
    have h2 : Nat.card χ.range ≤ 3 := (Subgroup.card_le_card_group _).trans hZ3
    have h3 : Nat.card Ω ≤ Nat.card χ.ker * 3 := h1 ▸ Nat.mul_le_mul_left _ h2
    omega
  set K : Subgroup Y := χ.ker.map Ω.subtype with hKdef
  have hKcard : Nat.card K = Nat.card χ.ker :=
    Subgroup.card_map_of_injective Ω.subtype_injective
  by_cases hKH : K ≤ Z ⊔ Subgroup.zpowers x
  · exact absurd ((hχker.trans hKcard.symm.le).trans (Subgroup.card_le_of_le hKH)) h27
  obtain ⟨y, hyK, hyH⟩ := SetLike.not_le_iff_exists.mp hKH
  obtain ⟨s, hs, rfl⟩ := hyK
  have hsx : ((s : Y)) * x = x * s := (Sec14.Res9ON.mem_ker_commHom hZc hcx s).mp hs
  obtain ⟨hsN, hs3⟩ := hΩmem s s.2
  have hHs : Z ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer {(s : Y)} := by
    refine sup_le (fun z hz => Subgroup.mem_centralizer_iff.mpr ?_) ?_
    · rintro _ rfl
      exact Subgroup.mem_center_iff.mp (hZc hz) _
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ rfl
      exact hsx
  have hcom : ∀ e ∈ Z ⊔ Subgroup.zpowers x, Commute e (s : Y) := fun e he =>
    (Subgroup.mem_centralizer_iff.mp (hHs he) _ rfl).symm
  obtain ⟨hEab, hEcard⟩ := i19_sup_zpowers hHab hs3 hyH hcom
  refine ⟨_, sup_le hHN (Subgroup.zpowers_le.mpr hsN), hEab, ?_⟩
  have : 9 ≤ Nat.card ↥(Z ⊔ Subgroup.zpowers x) := by
    have : 3 ≤ Nat.card Z := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (i19_isPGroup hZ)
      rcases n with _ | n
      · exact absurd (Subgroup.eq_bot_of_card_eq Z (by simpa using hn)) hZ1
      · rw [hn, pow_succ]
        exact Nat.le_mul_of_pos_left 3 (Nat.pos_of_ne_zero (by positivity))
    omega
  omega

end CFSG.RankThree.PartTwo.Sec4
