module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3Ratio
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3Type3
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3ThetaP
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofLTypeThree
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

variable {H : Type} [Group H] [Finite H]

theorem ofAdd_one_ne_one : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by decide

theorem ofAdd_one_pow_three : Multiplicative.ofAdd (1 : ZMod 3) ^ 3 = 1 := by decide

theorem mem_sup_of_autIn_cyclic {A L : Subgroup H} {a b c : H}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (haA : a ∈ A)
    (haC : a ∈ Subgroup.centralizer (L : Set H)) (ha3 : orderOf a = 3)
    (hLC : L ⊓ Subgroup.centralizer (L : Set H) = ⊥) (hALb : A ⊓ L = Subgroup.zpowers b)
    (hb3 : orderOf b = 3) (hcA : c ∈ A)
    (hWc : Subgroup.normalizer (A : Set H) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set H))
    (φ : autIn L A ≃* Multiplicative (ZMod 3)) :
    c ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.2
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbAL : b ∈ A ⊓ L := hALb ▸ Subgroup.mem_zpowers b
  have hbA : b ∈ A := (Subgroup.mem_inf.mp hbAL).1
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hbAL).2
  set σ : autIn L A := φ.symm (Multiplicative.ofAdd 1) with hσ
  have hσ1 : σ ≠ 1 := fun h => by
    have := congrArg φ h
    rw [hσ, MulEquiv.apply_symm_apply, φ.map_one] at this
    exact ofAdd_one_ne_one this
  have hσ3 : σ ^ 3 = 1 := φ.injective (by
    rw [map_pow φ, hσ, MulEquiv.apply_symm_apply, φ.map_one]
    exact ofAdd_one_pow_three)
  obtain ⟨w, hwN, hwL, hwσ⟩ := mem_autIn_iff.mp σ.2
  have hw3 : ∀ x ∈ A, w ^ 3 * x * (w ^ 3)⁻¹ = x := by
    intro x hx
    have h1 : A.normalizerMonoidHom (⟨w, hwN⟩ ^ 3) = 1 := by
      rw [map_pow, hwσ, ← Subgroup.coe_pow, hσ3, Subgroup.coe_one]
    have h2 := congrArg (fun φ : MulAut A => ((φ ⟨x, hx⟩ : A) : H)) h1
    simp only [MulAut.one_apply] at h2
    have e : (⟨w, hwN⟩ ^ 3 : Subgroup.normalizer (A : Set H)) =
        ⟨w ^ 3, Subgroup.pow_mem _ hwN 3⟩ := Subtype.ext (by simp)
    rw [e, normalizerMonoidHom_apply_coe] at h2
    exact h2
  obtain ⟨x₀, hx₀⟩ : ∃ x : A, w * (x : H) * w⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hσ1
    apply Subtype.ext
    rw [← hwσ, Subgroup.coe_one]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [normalizerMonoidHom_apply_coe, MulAut.one_apply]
    exact hcon x
  have hfix : ∀ x : H, orderOf x = 3 → w * x * w⁻¹ ∈ Subgroup.zpowers x →
      w ^ 3 * x * (w ^ 3)⁻¹ = x → w * x * w⁻¹ = x := by
    intro x hx3 hxw h3
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx3
      omega
    have hxx : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers hx3 hxw with h | h | h
    · exfalso
      apply hx1
      have : x = w⁻¹ * (w * x * w⁻¹) * w := by group
      rw [this, h]
      group
    · exact h
    · exfalso
      have e1 : w ^ 3 * x * (w ^ 3)⁻¹ = w * (w * (w * x * w⁻¹) * w⁻¹) * w⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev]
        group
      rw [h, ← conj_pow, h, ← pow_mul, show x ^ (2 * 2) = x by
        rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, hxx, one_mul], h] at e1
      rw [h3] at e1
      apply hx1
      have h' : x * x = x * 1 := by rw [mul_one, ← pow_two]; exact e1.symm
      exact mul_left_cancel h'
  have hwa : w * a * w⁻¹ = a := by
    rw [Subgroup.mem_centralizer_iff.mp haC w hwL, mul_inv_cancel_right]
  have hwb : w * b * w⁻¹ = b := by
    refine hfix b hb3 ?_ (hw3 b hbA)
    rw [← hALb]
    exact ⟨(Subgroup.mem_normalizer_iff.mp hwN b).mp hbA, L.mul_mem (L.mul_mem hwL hbL)
      (L.inv_mem hwL)⟩
  by_cases hc1 : c = 1
  · rw [hc1]
    exact Subgroup.one_mem _
  have hco : orderOf c = 3 := orderOf_eq_prime (hA3 c hcA) hc1
  have hwc : w * c * w⁻¹ = c :=
    hfix c hco ((Subgroup.mem_normalizer_iff.mp (hWc hwN) c).mp (Subgroup.mem_zpowers c))
      (hw3 c hcA)
  by_contra hcab
  have hzaA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  have hzbA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hbA
  have hzcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hSA0 : (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ≤ A := sup_le hzaA hzbA
  have hab : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x :=
    fun x hx y hy => hcomm x (hzaA hx) y (hzbA hy)
  have hSc0 : ∀ x ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers b), ∀ y ∈ Subgroup.zpowers c,
      x * y = y * x :=
    fun x hx y hy => hcomm x (hSA0 hx) y (hzcA hy)
  have hinfab : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := Subgroup.zpowers_le.mpr hbL (Subgroup.mem_inf.mp hx).2
    have hxC : x ∈ Subgroup.centralizer (L : Set H) :=
      Subgroup.zpowers_le.mpr haC (Subgroup.mem_inf.mp hx).1
    have : x ∈ L ⊓ Subgroup.centralizer (L : Set H) := ⟨hxL, hxC⟩
    rwa [hLC] at this
  have hinfc : (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.mp hx
    by_contra hx1
    have hxo : orderOf x = 3 := orderOf_eq_prime (hA3 x (hSA0 hxS)) hx1
    have heq : Subgroup.zpowers x = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hco])
    exact hcab (Subgroup.zpowers_le.mpr hxS (heq ▸ Subgroup.mem_zpowers c))
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hab
  rw [hinfab, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha3, hb3] at h1
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hSc0
  rw [hinfc, Subgroup.card_bot, mul_one, h1, Nat.card_zpowers, hco] at h2
  have hSA : (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c = A :=
    Subgroup.eq_of_le_of_card_ge (sup_le hSA0 hzcA) (by rw [h2, hA27])
  have hcen : (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c ≤
      Subgroup.centralizer ({w} : Set H) := by
    have hmem : ∀ x : H, w * x * w⁻¹ = x → x ∈ Subgroup.centralizer ({w} : Set H) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * w = w * x * w⁻¹ * w := by rw [hx]
        _ = w * x := by group
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr (hmem a hwa))
      (Subgroup.zpowers_le.mpr (hmem b hwb))) (Subgroup.zpowers_le.mpr (hmem c hwc))
  rw [hSA] at hcen
  apply hx₀
  have := Subgroup.mem_centralizer_singleton_iff.mp (hcen x₀.2)
  rw [← this, mul_inv_cancel_right]

variable {L : Subgroup H} [hLn : L.Normal] {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem false_of_pslPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] (hLq : CFSG.IsQuasisimple L)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) {a : H} (ha3 : orderOf a = 3)
    (hAa : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers a)
    (hpgl : ∀ x ∈ A, ∃ y, IsPGLAtP e x y) {c : H} (hcA : c ∈ A)
    (hca : c ∉ Subgroup.zpowers a) {B : Subgroup H} (hsup : Subgroup.zpowers c ⊔ B = A)
    (hinf : Subgroup.zpowers c ⊓ B = ⊥)
    (hWc : Subgroup.normalizer (A : Set H) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set H))
    (hWB : Subgroup.normalizer (A : Set H) ≤ Subgroup.normalizer (B : Set H))
    {R : Subgroup H} (hRL : R ≤ L) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set H)) (hRc : ⁅R, Subgroup.zpowers c⁆ = R)
    (hR1 : R ≠ ⊥) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have haA : a ∈ A := (hAa ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).1
  have haC : a ∈ Subgroup.centralizer (L : Set H) :=
    (hAa ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).2
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm
  have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpgl) hA3
  have hcardA := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hpgl)
  rw [hAa, Nat.card_zpowers, ha3] at hcardA
  have hR9 : Nat.card (pglHomP hK hq A hpgl).range = 9 := by omega
  rcases frame_or_heis h3K hτ hτ1 _ hRcomm hRexp (by omega) with ⟨b, hb, hd, -⟩ |
    ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  ·
    obtain ⟨P, hPL, T, hTL, hPN, hTN, r, hr1, hrmul, hrker, hrP, hrT⟩ :=
      exists_theta_of_frameP hK hq e hA hA27 ha3 hAa hpgl hb hd
    exact false_of_ratio hA.1 hA27 haA hcA hca hsup hinf (hWc hPN) (hWB hPN) (hWc hTN) (hWB hTN)
      (Subgroup.mem_centralizer_iff.mp haC T hTL) hr1 hrmul hrker hrP hrT
  have htype : ∀ x ∈ A, x ∉ Subgroup.centralizer (L : Set H) → ∀ y, IsPGLAtP e x y →
      Type123 π (p ^ f) K y 1 ∨ Type123 π (p ^ f) K y 3 := fun x hx hxC y hy =>
    type13_of_heisP hK hq hRcomm hy₁ hy₂ hζ1 hζ hy.1 (not_mem_zPi_of_isPGLAtP hK hq hxC hy)
      (pow_three_mem_zPiP hK hq (hA3 x hx) hy) (mk_mem_range_pglHomP hx hy)
  have hinner : ∀ x ∈ A, ∀ y, IsPGLAtP e x y → Type123 π (p ^ f) K y 1 →
      x ∈ L ⊔ Subgroup.centralizer (L : Set H) := by
    intro x hx y hy h1
    obtain ⟨l, hl, hyl⟩ := exists_inner_of_type1 hK hq hy.1 h1
    obtain ⟨v, hv, -, hxv⟩ := exists_inner_mem_of_innerP hK hq hy hl hyl
    have : x = x * v⁻¹ * v := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxv) (Subgroup.mem_sup_left hv)
  have hcardALC := card_inf_sup_centralizer hA hLC ha3 hAa
  by_cases h3 : ∃ x ∈ A, ∃ y, IsPGLAtP e x y ∧ Type123 π (p ^ f) K y 3
  ·
    obtain ⟨a', ha'A, ya', hya', hya'3⟩ := h3
    have ha'LC : a' ∉ L ⊔ Subgroup.centralizer (L : Set H) := fun h =>
      not_inner_of_type3 hK hq hya'.1 hya'3 (exists_inner_of_mem_supP hK hq h hya')
    obtain ⟨v, hv, hv1⟩ := exists_mem_inf_of_type3 hK hq hA hA27 hLC ha3 hAa hpgl ha'A hya' hya'3
    have hdvd : Nat.card (A ⊓ L : Subgroup H) * 3 ∣ 27 := by
      rw [← hcardALC, ← hA27]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne9 : Nat.card (A ⊓ L : Subgroup H) ≠ 9 := by
      intro h9
      apply ha'LC
      have hle : A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardALC, h9, hA27])
      rw [← hle] at ha'A
      exact (Subgroup.mem_inf.mp ha'A).2
    have hne1 : Nat.card (A ⊓ L : Subgroup H) ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      rw [h1] at hv
      exact hv1 (Subgroup.mem_bot.mp hv)
    have hAL3 : Nat.card (A ⊓ L : Subgroup H) = 3 := by
      have h9 : Nat.card (A ⊓ L : Subgroup H) ∣ 3 ^ 2 :=
        Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) (by norm_num; exact hdvd)
      obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
      interval_cases m
      · exact absurd hmeq hne1
      · exact hmeq
      · exact absurd hmeq hne9
    have hvo : orderOf v = 3 := orderOf_eq_prime (hA3 v (Subgroup.mem_inf.mp hv).1) hv1
    have hALv : A ⊓ L = Subgroup.zpowers v :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hv)
        (by rw [hAL3, Nat.card_zpowers, hvo])).symm
    obtain ⟨⟨x₁, hx₁⟩, hx₁y⟩ := hy₁
    obtain ⟨⟨x₂, hx₂⟩, hx₂y⟩ := hy₂
    obtain ⟨z₁, hz₁⟩ := hpgl x₁ hx₁
    obtain ⟨z₂, hz₂⟩ := hpgl x₂ hx₂
    have hm₁ : y₁⁻¹ * z₁ ∈ StatedScalars (Fin 3) K :=
      QuotientGroup.eq.mp (hx₁y.symm.trans (pglHomP_apply ⟨x₁, hx₁⟩ hz₁))
    have hm₂ : y₂⁻¹ * z₂ ∈ StatedScalars (Fin 3) K :=
      QuotientGroup.eq.mp (hx₂y.symm.trans (pglHomP_apply ⟨x₂, hx₂⟩ hz₂))
    have hheis := heis_of_mul_scalar hm₁ hm₂ hζ
    obtain ⟨-, ⟨φ⟩⟩ := k423L3TypeThreeFrame_holds H L π p f K hLq hK hq e A a hA hA27 ha3 hAa
      hpgl ⟨x₁, hx₁, x₂, hx₂, z₁, z₂, ζ, hz₁, hz₂, hζ1, hheis⟩ ⟨v, hALv, hvo⟩
    have hcab := mem_sup_of_autIn_cyclic hA.1 hA27 haA haC ha3 hLC hALv hvo hcA hWc φ
    have hcH : c ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) := by
      refine ⟨hcA, ?_⟩
      refine (sup_le ?_ ?_ : Subgroup.zpowers a ⊔ Subgroup.zpowers v ≤ _) hcab
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right haC)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hv).2)
    refine false_of_gen hA.1 inf_le_left hcH hc1 ha'A (fun h => ha'LC h.2)
      (fun x hx hxH t htL ht2 hxt => ?_) hRL hR2 hAR hRc hR1
    have hxLC : x ∉ L ⊔ Subgroup.centralizer (L : Set H) := fun h => hxH ⟨hx, h⟩
    have hxC : x ∉ Subgroup.centralizer (L : Set H) := fun h => hxLC (Subgroup.mem_sup_right h)
    obtain ⟨y, hy⟩ := hpgl x hx
    rcases htype x hx hxC y hy with h1 | h3
    · exact (hxLC (hinner x hx y hy h1)).elim
    · exact eq_one_of_isPGLAtP_type3 hK hy h3 htL ht2 hxt
  ·
    have h1 : ∀ x ∈ A, x ∉ Subgroup.centralizer (L : Set H) → ∀ y, IsPGLAtP e x y →
        Type123 π (p ^ f) K y 1 := fun x hx hxC y hy =>
      (htype x hx hxC y hy).resolve_right fun h => h3 ⟨x, hx, y, hy, h⟩
    have hALC : A ≤ L ⊔ Subgroup.centralizer (L : Set H) := by
      intro x hx
      by_cases hxC : x ∈ Subgroup.centralizer (L : Set H)
      · exact Subgroup.mem_sup_right hxC
      · obtain ⟨y, hy⟩ := hpgl x hx
        exact hinner x hx y hy (h1 x hx hxC y hy)
    have hAeq : A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) = A := inf_eq_left.mpr hALC
    rw [hAeq, hA27] at hcardALC
    have hAL9 : Nat.card (A ⊓ L : Subgroup H) = 9 := by omega
    have hsupeq := inf_sup_centralizer_eq hA hLC hAa
    rw [hAeq] at hsupeq
    have hsup' : A ⊔ L = Subgroup.zpowers a ⊔ L := by
      apply le_antisymm
      · rw [hsupeq]
        exact sup_le (sup_le (inf_le_right.trans le_sup_right) le_sup_left) le_sup_right
      · refine sup_le ?_ le_sup_right
        rw [← hAa]
        exact inf_le_left.trans le_sup_left
    have hbot : ∀ x ∈ A ⊓ L, x ≠ 1 → x ∉ Subgroup.centralizer (L : Set H) := fun x hx hx1 hxC =>
      hx1 (Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hxC⟩))
    have hE : ∀ x ∈ A ⊓ L, ∃ y, IsPGLAtP e x y := fun x hx => hpgl x (Subgroup.mem_inf.mp hx).1
    have hrange : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
        (pglHomP hK hq A hpgl).range →
          (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq (A ⊓ L) hE).range := by
      intro y hy
      obtain ⟨⟨x, hx⟩, hxy⟩ := hy
      obtain ⟨z, hz⟩ := hpgl x hx
      rw [pglHomP_apply ⟨x, hx⟩ hz] at hxy
      rw [← hxy]
      exact mem_range_inf_of_mem_sup hK hq hA hLC hE hx (hALC hx) hz
    have htrans := transitive_of_range_heis hK hq inf_le_right hAL9
      (fun x hx y hy => hAcomm x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1)
      (fun x hx => hA3 x (Subgroup.mem_inf.mp hx).1) hE (hrange _ hy₁) (hrange _ hy₂) hζ1 hζ
      (fun x hx hx1 y hy => h1 x (Subgroup.mem_inf.mp hx).1 (hbot x hx hx1) y hy)
    exact false_of_transitive hA.1 hA27 haA haC hLC hcA hca hWc hsup' htrans

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3
