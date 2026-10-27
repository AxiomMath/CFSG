module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensus
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusL37

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

structure A5Data (T : Type) [Group T] [Finite T] : Prop where
  qs : IsQuasisimple T
  dvd : Nat.card T ∣ 1382446517760
  ne : Nat.card T ≠ 1382446517760
  noE16 : ∀ E : Subgroup T, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8
  three : Subgroup.center T = ⊥ → ∀ R : Subgroup T, IsPGroup 3 R →
    CFSG.Assembly.IsElemAbelian 3 R
  aut : ∃ (σ : MulAut T) (F : Subgroup T), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ (∀ x ∈ F, σ x = x) ∧
    60 ∣ Nat.card F ∧ ∀ x ∈ F, x ^ 3 = 1 → (∀ y ∈ F, x * y = y * x) → x = 1

@[expose] def A5Row (Φ : (T : Type) → [Group T] → Prop) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], A5Data T → Φ T → False

namespace A5Data

variable {T : Type} [Group T] [Finite T]

theorem sixty_dvd (h : A5Data T) : 60 ∣ Nat.card T := by
  obtain ⟨σ, F, -, -, -, h60, -⟩ := h.aut
  exact h60.trans (Subgroup.card_subgroup_dvd_card F)

theorem false_of_not_five (h : A5Data T) (h5 : ¬ 5 ∣ Nat.card T) : False :=
  h5 ((by norm_num : 5 ∣ 60).trans h.sixty_dvd)

theorem false_of_card_dvd_sixty (h : A5Data T) (h60 : Nat.card T ∣ 60) : False := by
  obtain ⟨σ, F, -, hσ1, hfix, hF60, -⟩ := h.aut
  have hle : Nat.card T ≤ Nat.card F := by
    have hpos : 0 < Nat.card F := Nat.card_pos
    exact (Nat.le_of_dvd hpos (h60.trans hF60))
  have hF : F = ⊤ := Subgroup.eq_top_of_le_card F hle
  apply hσ1
  ext x
  rw [MulAut.one_apply]
  exact hfix x (hF ▸ Subgroup.mem_top x)

theorem false_of_E16 (h : A5Data T) {E : Subgroup T} (hE : CFSG.Assembly.IsElemAbelian 2 E)
    (h16 : Nat.card E = 16) : False := by
  have := h.noE16 E hE
  omega

theorem false_of_orderOf_nine (h : A5Data T) (hZ : Subgroup.center T = ⊥) {x : T}
    (hx : orderOf x = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers, hx]
    norm_num
  have h3 : x ^ 3 = 1 := (h.three hZ _ hp).2 x (Subgroup.mem_zpowers x)
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hx] at this
  norm_num at this

theorem false_of_nonabelian_three (h : A5Data T) (hZ : Subgroup.center T = ⊥)
    {R : Subgroup T} (hR : IsPGroup 3 R) {a b : T} (ha : a ∈ R) (hb : b ∈ R)
    (hab : a * b ≠ b * a) : False := by
  have hE := h.three hZ R hR
  exact hab (congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem commute_of_conj_eq {σ : MulAut T} {F : Subgroup T} (hfix : ∀ x ∈ F, σ x = x) {s : T}
    (hs : MulAut.conj s = σ) {x : T} (hx : x ∈ F) : s * x = x * s := by
  have h1 : s * x * s⁻¹ = x := by
    rw [← MulAut.conj_apply, hs]
    exact hfix x hx
  calc s * x = s * x * s⁻¹ * s := by group
    _ = x * s := by rw [h1]

theorem false_of_inner (h : A5Data T) {Y : Type} [Group Y] (e : T ⧸ Subgroup.center T ≃* Y)
    (hinn : ∀ σ : MulAut T, σ ^ 3 = 1 → σ ∈ (MulAut.conj : T →* MulAut T).range)
    (h5 : ¬ 5 ∣ Nat.card (Subgroup.center T)) (hY : ∀ y : Y, orderOf y ≠ 15) : False := by
  obtain ⟨σ, F, hσ3, hσ1, hfix, h60, -⟩ := h.aut
  obtain ⟨s, hs⟩ := hinn σ hσ3
  set π : T →* Y := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T)) with hπdef
  have hπ : ∀ x, π x = 1 ↔ x ∈ Subgroup.center T := by
    intro x
    simp only [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hsZ : s ∉ Subgroup.center T := by
    intro hsZ
    apply hσ1
    rw [← hs]
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hsZ x).symm,
      mul_inv_cancel_right]
  have hs3 : s ^ 3 ∈ Subgroup.center T := by
    have hc : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hs, hσ3]
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut T => φ g) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h1]
      _ = s ^ 3 * g := by group
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 5
    ((by norm_num : 5 ∣ 60).trans h60)
  have hg5 : (g : T) ^ 5 = 1 := by
    rw [← SubgroupClass.coe_pow, ← hg, pow_orderOf_eq_one, OneMemClass.coe_one]
  have hgZ : (g : T) ∉ Subgroup.center T := by
    intro hgZ
    have h1 : orderOf (g : T) ∣ Nat.card (Subgroup.center T) :=
      Subgroup.orderOf_dvd_natCard _ hgZ
    rw [Subgroup.orderOf_coe, hg] at h1
    exact h5 h1
  have hπs : orderOf (π s) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, (hπ _).mpr hs3]) fun h1 => hsZ ((hπ s).mp h1)
  have hπg : orderOf (π g) = 5 :=
    orderOf_eq_prime (by rw [← map_pow, hg5, map_one]) fun h1 => hgZ ((hπ g).mp h1)
  have hcomm : Commute (π s) (π g) := by
    change π s * π g = π g * π s
    rw [← map_mul, ← map_mul, commute_of_conj_eq hfix hs g.2]
  have h15 := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hπs, hπg]; norm_num)
  rw [hπs, hπg] at h15
  exact hY _ h15

theorem false_of_inner_nine (h : A5Data T) (hZ : Subgroup.center T = ⊥)
    (hinn : ∀ σ : MulAut T, σ ^ 3 = 1 → σ ∈ (MulAut.conj : T →* MulAut T).range)
    (h9 : ¬ 9 ∣ Nat.card T) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ, F, hσ3, hσ1, hfix, h60, hnc⟩ := h.aut
  obtain ⟨s, hs⟩ := hinn σ hσ3
  have hs3 : s ^ 3 = 1 := by
    have hc : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hs, hσ3]
    have hmem : s ^ 3 ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut T => φ g) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h1]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hσ1 (by rw [← hs, map_one])
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 3
    ((by norm_num : 3 ∣ 60).trans h60)
  have hf3 : (f : T) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, ← hf, pow_orderOf_eq_one, OneMemClass.coe_one]
  have hsf : s * f = f * s := commute_of_conj_eq hfix hs f.2
  have hsf' : s ∉ Subgroup.zpowers (f : T) := by
    intro hmem
    have hsF : s ∈ F := (Subgroup.zpowers_le.mpr f.2) hmem
    exact hs1 (hnc s hsF hs3 fun y hy => commute_of_conj_eq hfix hs hy)
  set H := Subgroup.closure ({s, (f : T)} : Set T) with hH
  have hHp : IsPGroup 3 H := isPGroup_closure_pair hs3 hf3 hsf
  have hfH : Subgroup.zpowers (f : T) ≤ H :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem s rfl))
  have hsH : s ∈ H := Subgroup.subset_closure (Set.mem_insert s _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
  have hlt : Nat.card (Subgroup.zpowers (f : T)) < Nat.card H := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hfH fun heq => hsf' (heq ▸ hsH))
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hf, hk] at hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    interval_cases k <;> norm_num at hlt
  have h9H : 9 ∣ Nat.card H := by
    rw [hk]
    exact (show 9 = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 hk2
  exact h9 (h9H.trans (Subgroup.card_subgroup_dvd_card H))

end A5Data

noncomputable def quotCenterEquivOfBot {T S : Type} [Group T] [Group S]
    (hZ : Subgroup.center T = ⊥) (φ : T ≃* S) : T ⧸ Subgroup.center T ≃* S :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ

structure A5Rows : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    A5Row (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField p e)))
  two_eps : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    A5Row (fun T _ => IsSLThreeEpsAt T (p ^ e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    A5Row (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField p e)))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    A5Row (fun T _ => Nonempty (T ≃* projSU 3 p e))
  three_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    A5Row (fun T _ => Blueprint.ChevalleyExceptionalModel T .G2 p 1)
  three_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    A5Row (fun T _ => Nonempty (T ≃* projSp 2 (GaloisField p 1)))
  three_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    A5Row (fun T _ => Nonempty (T ≃* projSU 4 p 1))
  three_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    A5Row (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField p 1)))
  four_alt : ∀ n : ℕ, n ≤ 9 → A5Row (fun T _ => Nonempty (T ≃* alternatingGroup (Fin n)))
  four_A6 : A5Row (fun T _ => IsExtOf T (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)))
  four_A7 : A5Row (fun T _ => IsExtOf T (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)))
  five_spor : ∀ s ∈ sporadics46,
    A5Row (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier s))
  five_cover : ∀ s ∈ sporadicCovers46,
    A5Row (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3)))
  six_model : A5Row (fun T _ => IsChevTwoRankTwoModel T)
  six_SL3 : ∀ n : ℕ, 1 ≤ n → A5Row (fun T _ => IsSLThreeEpsAt T (2 ^ n))
  seven_SL52 : A5Row (fun T _ => Nonempty (T ≃* projSL 5 (GaloisField 2 1)))
  seven_Sp62 : A5Row (fun T _ => Nonempty (T ≃* projSp 3 (GaloisField 2 1)))
  seven_SU54 : A5Row (fun T _ => Nonempty (T ≃* projSU 5 2 2))
  eight_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 2 →
    A5Row (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField 3 e)))
  eight_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 2 → A5Row (fun T _ => Nonempty (T ≃* projSU 3 3 e))
  eight_SL43 : A5Row (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField 3 1)))
  eight_cover : A5Row (fun T _ => Nat.card (Subgroup.center T) ≤ 3 ∧
    (Blueprint.ChevalleyExceptionalModel (T ⧸ Subgroup.center T) .G2 3 1 ∨
      Nonempty (T ⧸ Subgroup.center T ≃* projSU 4 3 1)))

theorem a5_of_rows (h : A5Rows) (T : Type) [Group T] [Finite T] (hd : A5Data T)
    (hlist : IsList46 T) : False := by
  rcases hlist with ⟨p, e, hp, hp2, he, hL⟩ | ⟨p, e, hp, hp3, he1, he2, hL | hL | hL⟩ |
      ⟨p, hp, hp3, hL | hL | ⟨hp1, hL⟩ | ⟨hp2, hL⟩⟩ | (⟨n, hn, hL⟩ | hL | hL) |
      (⟨s, hs, hL⟩ | ⟨s, hs, hL⟩) | (hL | ⟨n, hn, hL⟩) | (hL | hL | hL) |
      (⟨e, he1, he2, hL | hL⟩ | hL | hL)
  · exact h.one p e hp2 he T hd hL
  · exact h.two_eps p e hp3 he1 he2 T hd hL
  · exact h.two_SL p e hp3 he1 he2 T hd hL
  · exact h.two_SU p e hp3 he1 he2 T hd hL
  · exact h.three_G2 p hp3 T hd hL
  · exact h.three_Sp p hp3 T hd hL
  · exact h.three_SU p hp3 hp1 T hd hL
  · exact h.three_SL p hp3 hp2 T hd hL
  · exact h.four_alt n hn T hd hL
  · exact h.four_A6 T hd hL
  · exact h.four_A7 T hd hL
  · exact h.five_spor s hs T hd hL
  · exact h.five_cover s hs T hd hL
  · exact h.six_model T hd hL
  · exact h.six_SL3 n hn T hd hL
  · exact h.seven_SL52 T hd hL
  · exact h.seven_Sp62 T hd hL
  · exact h.seven_SU54 T hd hL
  · exact h.eight_SL3 e he1 he2 T hd hL
  · exact h.eight_SU3 e he1 he2 T hd hL
  · exact h.eight_SL43 T hd hL
  · exact h.eight_cover T hd hL

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
