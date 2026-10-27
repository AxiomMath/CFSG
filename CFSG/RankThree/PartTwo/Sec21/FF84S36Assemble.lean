module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiF
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Cp
public import CFSG.RankThree.PartTwo.Sec21.FF84S36R
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Prod
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Final

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.Quasithin
open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb IsExtraspecialPlus)

variable {G : Type} [Group G] [Finite G]

theorem S36_Ti_for {b t b₁ b₂ : G} {L B : Subgroup G} (hA9 : A9CentralizerStmt)
    (d : F6Data b L B b₁ b₂ t) (h31 : FF84_3_1) {c : G} (hc : c = b₁ ∨ c = b₂) :
    ∃ Q : Subgroup G, Op 2 (Cen t) ⊓ Cen c ≤ Q ∧ Nat.card Q = 32 ∧
      IsExtraspecialPGroup 2 ↥Q ∧ Q = Op 2 (Cen t ⊓ Cen c) ∧ t ∈ Q ∧
      ExtraspecialAt Q t ∧ ∃ A : Subgroup G, A ≤ Q ∧ IsElemAb 2 3 A := by
  rcases hc with rfl | rfl
  · exact F6_Ti hA9 d h31 0
  · exact F6_Ti hA9 d h31 1

theorem S36_inter_zpowers {Q₁ Q₂ : Subgroup G} {t : G} (h₁ : ExtraspecialAt Q₁ t)
    (hc : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) {x : G} (hx1 : x ∈ Q₁) (hx2 : x ∈ Q₂) :
    x ∈ Subgroup.zpowers t := by
  have hcen : ∀ u ∈ Q₁, x * u = u * x := fun u hu => (hc u hu x hx2).symm
  rcases h₁.center_le x hx1 hcen with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact Subgroup.mem_zpowers t

theorem S36_assemble {b t b₁ b₂ : G} {L B : Subgroup G} (hA9 : A9CentralizerStmt)
    (d : F6Data b L B b₁ b₂ t) (h31 : FF84_3_1) (h33 : FF84_3_3) (h34 : FF84_3_4) :
    IsExtraspecialPlus 4 (Op 2 (Cen t)) := by
  have hchar : CFSG.Assembly.IsCharTwoType G := d.sec.hyp.char2
  have hb₁L : b₁ ∈ L := d.sec.hb₁.2
  have hb₂L : b₂ ∈ L := d.sec.hb₂.2
  obtain ⟨Q₁, hT₁Q₁, hQ₁card, _hQ₁p, _hQ₁eq, _ht₁Q₁, hE₁, A₁, hA₁Q₁, hA₁el⟩ :=
    S36_Ti_for hA9 d h31 (c := b₁) (Or.inl rfl)
  obtain ⟨Q₂, hT₂Q₂, hQ₂card, _hQ₂p, _hQ₂eq, _ht₂Q₂, hE₂, A₂, hA₂Q₂, hA₂el⟩ :=
    S36_Ti_for hA9 d h31 (c := b₂) (Or.inr rfl)
  have htCen : t ∈ Cen t := S36_mem_cen_of rfl
  have hzT : Subgroup.zpowers t ≤ Op 2 (Cen t) :=
    S36_zpowers_op2 d.ht htCen (fun g hg => (S36_comm_of_cen hg).symm)
  have hord : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, d.ht]
  have htT₁ : t ∈ Op 2 (Cen t) ⊓ Cen b₁ :=
    Subgroup.mem_inf.2 ⟨hzT (Subgroup.mem_zpowers t),
      S36_mem_cen_of (Subgroup.mem_centralizer_iff.1 d.htL b₁ hb₁L)⟩
  have htT₂ : t ∈ Op 2 (Cen t) ⊓ Cen b₂ :=
    Subgroup.mem_inf.2 ⟨hzT (Subgroup.mem_zpowers t),
      S36_mem_cen_of (Subgroup.mem_centralizer_iff.1 d.htL b₂ hb₂L)⟩
  have hztle : Subgroup.zpowers t ≤ (Op 2 (Cen t) ⊓ Cen b₁) ⊓ (Op 2 (Cen t) ⊓ Cen b₂) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨htT₁, htT₂⟩)
  have hcomm12 := F6_commute d h31 h33
  have hsup : (Op 2 (Cen t) ⊓ Cen b₁) ⊔ (Op 2 (Cen t) ⊓ Cen b₂) = Op 2 (Cen t) := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro g hg
    have hg' : g ∈ (Op 2 (Cen t) : Set G) := hg
    rw [F6_product d h31 h33] at hg'
    obtain ⟨h, hh, k, hk, rfl⟩ := hg'
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Op 2 (Cen t) ⊓ Cen b₁) (Op 2 (Cen t) ⊓ Cen b₂) hcomm12).1
  rw [hsup] at hcard
  obtain ⟨-, -, r, hr⟩ := F6_H d h31 h33
  have hTne : Op 2 (Cen t) ≠ Subgroup.zpowers t := F6_r_pos hchar d
  have hne32 : Nat.card ↥(Op 2 (Cen t)) ≠ 2 ^ 5 :=
    F6_r_ne_one_stmt (G := G) hA9 hchar d h31 h33 h34
  have hx : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) ≤ 32 := by
    have := Subgroup.card_le_of_le hT₁Q₁
    omega
  have hy : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₂) ≤ 32 := by
    have := Subgroup.card_le_of_le hT₂Q₂
    omega
  have hz : 2 ≤ Nat.card ↥((Op 2 (Cen t) ⊓ Cen b₁) ⊓ (Op 2 (Cen t) ⊓ Cen b₂)) := by
    have := Subgroup.card_le_of_le hztle
    rw [hord] at this
    exact this
  have hxy : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) * Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₂) ≤ 32 * 32 :=
    Nat.mul_le_mul hx hy
  have hPle : Nat.card ↥(Op 2 (Cen t)) * 2 ≤
      Nat.card ↥(Op 2 (Cen t)) * Nat.card ↥((Op 2 (Cen t) ⊓ Cen b₁) ⊓ (Op 2 (Cen t) ⊓ Cen b₂)) :=
    Nat.mul_le_mul_left _ hz
  have hPle512 : Nat.card ↥(Op 2 (Cen t)) ≤ 512 := by nlinarith [hPle, hcard, hxy]
  have hr2 : r ≤ 2 := by
    by_contra hcon
    have h3 : 16 ^ 3 ≤ 16 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (16 : ℕ) ^ 3 = 4096 := by norm_num
    linarith
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hTne
    exact (Subgroup.eq_of_le_of_card_ge hzT (by rw [hr, hord] <;> norm_num)).symm
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hne32
    rw [hr] <;> norm_num
  have hr_eq : r = 2 := by omega
  have hP : Nat.card ↥(Op 2 (Cen t)) = 512 := by rw [hr, hr_eq] <;> norm_num
  rw [hP] at hcard
  have hz2 : Nat.card ↥((Op 2 (Cen t) ⊓ Cen b₁) ⊓ (Op 2 (Cen t) ⊓ Cen b₂)) = 2 := by
    omega
  have hx32 : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) = 32 := by
    by_contra hne
    have hx31 : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₁) ≤ 31 := by omega
    nlinarith [Nat.mul_le_mul hx31 hy]
  have hy32 : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₂) = 32 := by
    by_contra hne
    have hy31 : Nat.card ↥(Op 2 (Cen t) ⊓ Cen b₂) ≤ 31 := by omega
    nlinarith [Nat.mul_le_mul hx hy31]
  have hT₁eq : Op 2 (Cen t) ⊓ Cen b₁ = Q₁ :=
    Subgroup.eq_of_le_of_card_ge hT₁Q₁ (by omega)
  have hT₂eq : Op 2 (Cen t) ⊓ Cen b₂ = Q₂ :=
    Subgroup.eq_of_le_of_card_ge hT₂Q₂ (by omega)
  have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := by
    intro x hx' y hy'
    rw [← hT₁eq] at hx'
    rw [← hT₂eq] at hy'
    exact hcomm12 x hx' y hy'
  have hTdec : ∀ g ∈ Op 2 (Cen t), ∃ x ∈ Q₁, ∃ y ∈ Q₂, g = x * y := by
    intro g hg
    have hg' : g ∈ (Op 2 (Cen t) : Set G) := hg
    rw [F6_product d h31 h33] at hg'
    obtain ⟨h, hh, k, hk, rfl⟩ := hg'
    refine ⟨h, ?_, k, ?_, rfl⟩
    · rw [← hT₁eq]; exact hh
    · rw [← hT₂eq]; exact hk
  have hQ₁T : Q₁ ≤ Op 2 (Cen t) := by rw [← hT₁eq]; exact inf_le_left
  have hQ₂T : Q₂ ≤ Op 2 (Cen t) := by rw [← hT₂eq]; exact inf_le_left
  have hTp : IsPGroup 2 (Op 2 (Cen t)) := S36_op2_isPGroup _
  have hcentral : IsExtraspecialPGroup 2 ↥(Op 2 (Cen t)) :=
    S36_ext_central_product hTp hE₁ hE₂ hcommQ hTdec hQ₁T hQ₂T
  have hA₁t : t ∈ A₁ :=
    S36_z_mem_of_card_eight hE₁ hA₁Q₁ (hA₁el.2.trans (by norm_num))
      (fun a ha b hb => S36_elemAb_comm hA₁el ha hb)
  have hA₂t : t ∈ A₂ :=
    S36_z_mem_of_card_eight hE₂ hA₂Q₂ (hA₂el.2.trans (by norm_num))
      (fun a ha b hb => S36_elemAb_comm hA₂el ha hb)
  have hA12 : A₁ ⊓ A₂ = Subgroup.zpowers t := by
    apply le_antisymm
    · intro x hx'
      exact S36_inter_zpowers hE₁ hcommQ (hA₁Q₁ (Subgroup.mem_inf.1 hx').1)
        (hA₂Q₂ (Subgroup.mem_inf.1 hx').2)
    · exact Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hA₁t, hA₂t⟩)
  have hint : Nat.card ↥(A₁ ⊓ A₂) = 2 := by rw [hA12, hord]
  have hAel : IsElemAb 2 5 (A₁ ⊔ A₂) :=
    S36_elemAb_sup hA₁el hA₂el (fun x hx' y hy' => hcommQ x (hA₁Q₁ hx') y (hA₂Q₂ hy')) hint
  have hAT : A₁ ⊔ A₂ ≤ Op 2 (Cen t) := sup_le (hA₁Q₁.trans hQ₁T) (hA₂Q₂.trans hQ₂T)
  unfold IsExtraspecialPlus
  refine ⟨hcentral, ?_, A₁ ⊔ A₂, hAT, hAel⟩
  rw [hP] <;> norm_num

theorem ff84_3_6_of_A9
    (hA9 : A9CentralizerStmt) (h33 : FF84_3_3) (h34 : FF84_3_4) :
    FF84_3_6 := by
  intro G _ _ b L B b₁ b₂ sec t ht htL htb hN
  exact S36_assemble hA9 ⟨sec, ht, htL, htb, hN⟩
    CFSG.RankThree.PartTwo.Sec21.FF84.ff84_3_1 h33 h34

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
