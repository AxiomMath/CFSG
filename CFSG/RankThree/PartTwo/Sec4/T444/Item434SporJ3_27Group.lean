module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvGroup
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporJ3

open CFSG CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.AGLEmbedding.KFactProofs.J3OuterInv

section Aut

variable {X : Type*} [Group X]

theorem aut_mul_conj_mul_inv (y : MulAut X) (b : X) :
    y * MulAut.conj b * y⁻¹ = MulAut.conj (y b) := by
  ext x
  simp [MulAut.conj_apply]

theorem fix_of_commute_conj (hcen : Subgroup.center X = ⊥) {y : MulAut X} {b : X}
    (h : MulAut.conj b * y = y * MulAut.conj b) : y b = b := by
  apply Item434Kit.conj_injective_of_center_eq_bot hcen
  have h1 := aut_mul_conj_mul_inv y b
  rw [← h, mul_inv_cancel_right] at h1
  exact h1.symm

theorem mem_centralizer_of_conj_fix {B : Subgroup X} {w : X}
    (hw : ∀ b ∈ B, (MulAut.conj w) b = b) : w ∈ Subgroup.centralizer (B : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h : w * b * w⁻¹ = b := hw b hb
  calc b * w = (w * b * w⁻¹) * w := by rw [h]
    _ = w * b := by group

theorem sq_mem_range_of_card_outer_le_two [Finite X] (hOut : Nat.card (Outer X) ≤ 2)
    (y : MulAut X) : y ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := by
  let q : MulAut X →* Outer X := QuotientGroup.mk' (inner X)
  have hq : q y ^ 2 = 1 := by
    have h1 : orderOf (q y) ∣ Nat.card (Outer X) := orderOf_dvd_natCard _
    have h2 : 0 < Nat.card (Outer X) := Nat.card_pos
    rcases (by omega : Nat.card (Outer X) = 1 ∨ Nat.card (Outer X) = 2) with h | h
    · rw [h] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans (one_dvd 2))
    · rw [h] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hq2 : q (y ^ 2) = 1 := by rw [map_pow]; exact hq
  exact (QuotientGroup.eq_one_iff (y ^ 2)).mp hq2

theorem eq_one_of_coprime_of_isPGroup {C : Subgroup X} (hC : IsPGroup 3 C) {x : X} (hx : x ∈ C)
    {m : ℕ} (hm : Nat.Coprime 3 m) (hxm : x ^ m = 1) : x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hC ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have h3 : 3 ^ k ∣ m := hk ▸ orderOf_dvd_of_pow_eq_one hxm
  have h4 : 3 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hm) h3
  rw [h4] at hk
  exact orderOf_eq_one_iff.mp hk

end Aut

section Normalized

variable {X : Type*} [Group X] [Finite X]

theorem eq_bot_of_normalized (hcen : Subgroup.center X = ⊥)
    (hE9 : ∀ B : Subgroup X, IsMulCommutative B → (∀ b ∈ B, b ^ 3 = 1) → Nat.card B = 9 →
      IsPGroup 3 (Subgroup.centralizer (B : Set X)))
    (hOut : Nat.card (Outer X) ≤ 2)
    (hOuter : ∀ α : MulAut X, α ^ 2 = 1 → α ∉ (MulAut.conj : X →* MulAut X).range →
      ∀ B : Subgroup X, IsMulCommutative B → (∀ b ∈ B, b ^ 3 = 1) → Nat.card B = 9 →
        ∃ b ∈ B, α b ≠ b)
    {P : Subgroup X} (hP : IsMulCommutative P) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hP27 : Nat.card P = 27) {Y : Subgroup (MulAut X)} (hY : ¬ 3 ∣ Nat.card Y)
    (hPY : P.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Y : Set (MulAut X))) :
    Y = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  set V := P.map (MulAut.conj : X →* MulAut X) with hV
  have hVe : CFSG.Assembly.IsElemAbelian 3 V :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P ⟨hP, hP3⟩
  have hV27 : Nat.card V = 27 := by rw [hV, Subgroup.card_map_of_injective hinj, hP27]
  refine le_bot_iff.mp (Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) hp hVe
    (by rw [hV27]; norm_num) hPY ((Nat.Prime.coprime_iff_not_dvd hp).mpr hY) ?_)
  intro H hHV hH9
  set B : Subgroup X := P ⊓ H.comap (MulAut.conj : X →* MulAut X) with hB
  have hBH : B.map (MulAut.conj : X →* MulAut X) = H := by
    ext φ
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb.2
    · intro hφ
      obtain ⟨b, hbP, hbφ⟩ := hHV hφ
      exact ⟨b, ⟨hbP, by
        show (MulAut.conj : X →* MulAut X) b ∈ H
        rw [hbφ]
        exact hφ⟩, hbφ⟩
  have hB9 : Nat.card B = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hBH, hH9]
    norm_num
  have hBe := Sec5.isElemAbelian_of_le (E := B) (F := P) ⟨hP, hP3⟩ inf_le_left
  rintro y ⟨hyY, hyC⟩
  have hfix : ∀ b ∈ B, y b = b := by
    intro b hb
    refine fix_of_commute_conj hcen ?_
    have hbH : MulAut.conj b ∈ H := hBH ▸ Subgroup.mem_map_of_mem _ hb
    exact Subgroup.mem_centralizer_iff.mp hyC _ hbH
  have hCB := hE9 B hBe.1 hBe.2 hB9
  have hcop : Nat.Coprime 3 (orderOf y) := by
    have h1 : orderOf y ∣ Nat.card Y := by
      rw [← Subgroup.orderOf_mk y hyY]
      exact orderOf_dvd_natCard _
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hY).coprime_dvd_right h1
  have hy2 : y ^ 2 = 1 := by
    obtain ⟨x, hx⟩ := sq_mem_range_of_card_outer_le_two hOut y
    have hxB : x ∈ Subgroup.centralizer (B : Set X) := by
      refine mem_centralizer_of_conj_fix fun b hb => ?_
      rw [hx, pow_two, MulAut.mul_apply, hfix b hb, hfix b hb]
    have hxm : x ^ orderOf y = 1 := by
      apply hinj
      rw [map_pow, hx, map_one, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hx1 : x = 1 := eq_one_of_coprime_of_isPGroup hCB hxB hcop hxm
    rw [← hx, hx1, map_one]
  by_cases hyin : y ∈ (MulAut.conj : X →* MulAut X).range
  · obtain ⟨w, hw⟩ := hyin
    have hwB : w ∈ Subgroup.centralizer (B : Set X) := by
      refine mem_centralizer_of_conj_fix fun b hb => ?_
      rw [hw]
      exact hfix b hb
    have hw2 : w ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hw, hy2, map_one]
    have hw1 : w = 1 := eq_one_of_coprime_of_isPGroup hCB hwB (by norm_num) hw2
    rw [← hw, hw1, map_one]
    rfl
  · obtain ⟨b, hb, hne⟩ := hOuter y hy2 hyin B hBe.1 hBe.2 hB9
    exact absurd (hfix b hb) hne

end Normalized

section Setup

variable {J : Type*} [Group J] [Finite J]

omit [Finite J] in
theorem exists_centralizer_le {T Z : Subgroup J} {φ : MulAut J} (H : OuterSetup J T Z φ)
    {E : Subgroup J} (hET : E ≤ T) (hE : IsMulCommutative E) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE9 : Nat.card E = 9) : ∃ z ∈ E, Subgroup.centralizer ({z} : Set J) ≤ T := by
  obtain ⟨z, hzE, hzZ, hz1⟩ : ∃ z ∈ E, z ∈ Z ∧ z ≠ 1 := by
    by_contra hno
    push Not at hno
    obtain ⟨W, hW, hW3, hWc⟩ := exists_elem_mul hE hE3 H.Zcomm H.Z3
      (fun a ha b hb => H.Zc b hb a (hET ha))
      (Subgroup.disjoint_def.2 fun {x} hxE hxZ => hno x hxE hxZ)
    exact H.rank ⟨W, hW, hW3, by rw [hWc, hE9, H.Z9]⟩
  have hTC : T ≤ Subgroup.centralizer ({z} : Set J) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (H.Zc z hzZ x hx)
  refine ⟨z, hzE, ?_⟩
  rcases H.overgroup _ hTC with hCN | hCtop
  · exact H.cent z hzZ hz1 hCN
  · exact absurd (H.cen z fun x => Subgroup.mem_centralizer_singleton_iff.1
      (hCtop ▸ Subgroup.mem_top x)) hz1

theorem isPGroup_centralizer {S : Sylow 3 J} {Z : Subgroup J} {φ : MulAut J}
    (H : OuterSetup J (S : Subgroup J) Z φ) {E : Subgroup J} (hE : IsMulCommutative E)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9) :
    IsPGroup 3 (Subgroup.centralizer (E : Set J)) := by
  have hEp : IsPGroup 3 E := fun x => ⟨1, by simpa using Subtype.ext (hE3 x x.2)⟩
  obtain ⟨S', hS'⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J S' S
  have hSc : (S : Subgroup J) = (S' : Subgroup J).map (MulAut.conj c).toMonoidHom := by
    have h2 : ((c • S' : Sylow 3 J) : Subgroup J) =
        (S' : Subgroup J).map (MulAut.conj c).toMonoidHom := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      rfl
    rw [hc] at h2
    exact h2
  set E' := E.map (MulAut.conj c).toMonoidHom with hE'
  have hE'S : E' ≤ (S : Subgroup J) := hSc ▸ Subgroup.map_mono hS'
  have := hE
  obtain ⟨z, hzE', hzC⟩ := exists_centralizer_le H hE'S inferInstance
    (fun y hy => by
      obtain ⟨e, he, rfl⟩ := hy
      change (c * e * c⁻¹) ^ 3 = 1
      rw [conj_pow, hE3 e he]
      group)
    (by rw [hE', Subgroup.card_map_of_injective (MulAut.conj c).injective, hE9])
  have hCE' : IsPGroup 3 (Subgroup.centralizer (E' : Set J)) :=
    S.isPGroup'.to_le ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzE')).trans hzC)
  intro g
  have hg' : c * (g : J) * c⁻¹ ∈ Subgroup.centralizer (E' : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp g.2 e he
    change c * e * c⁻¹ * (c * g * c⁻¹) = c * g * c⁻¹ * (c * e * c⁻¹)
    calc c * e * c⁻¹ * (c * g * c⁻¹) = c * (e * g) * c⁻¹ := by group
      _ = c * (g * e) * c⁻¹ := by rw [h]
      _ = c * g * c⁻¹ * (c * e * c⁻¹) := by group
  obtain ⟨k, hk⟩ := hCE' ⟨_, hg'⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (c * (g : J) * c⁻¹) ^ 3 ^ k = 1 := congrArg Subtype.val hk
  rw [conj_pow] at h1
  change (g : J) ^ 3 ^ k = 1
  calc (g : J) ^ 3 ^ k = c⁻¹ * (c * (g : J) ^ 3 ^ k * c⁻¹) * c := by group
    _ = 1 := by rw [h1]; group

end Setup

end CFSG.RankThree.PartTwo.Sec4.Item434SporJ3
