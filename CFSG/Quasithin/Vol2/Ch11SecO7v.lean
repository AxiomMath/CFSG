module

public import CFSG.Quasithin.Vol2.Ch11SecO7c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

variable {B : Type} [Group B]

theorem card_modO2_dvd_quot [Finite B] {V : Subgroup B} [hVn : V.Normal] (hV : IsPGroup 2 V) :
    Nat.card (B ⧸ CFSG.pCore 2 B) ∣ Nat.card (B ⧸ V) := by
  have hle : V ≤ CFSG.pCore 2 B := le_sSup ⟨hVn, hV⟩
  have h1 := (CFSG.pCore 2 B).card_eq_card_quotient_mul_card_subgroup
  have h2 := V.card_eq_card_quotient_mul_card_subgroup
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hV0 : 0 < Nat.card V := Nat.card_pos
  refine ⟨k, Nat.eq_of_mul_eq_mul_right hV0 ?_⟩
  rw [← h2, h1, hk]
  ring

theorem pCore_eq_of_quot {V : Subgroup B} [hVn : V.Normal] (hV : IsPGroup 2 V)
    (hQ : CFSG.pCore 2 (B ⧸ V) = ⊥) : CFSG.pCore 2 B = V := by
  refine le_antisymm ?_ (le_sSup ⟨hVn, hV⟩)
  intro x hx
  have himg : (CFSG.pCore 2 B).map (QuotientGroup.mk' V) ≤ CFSG.pCore 2 (B ⧸ V) :=
    le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := B)).map _ (QuotientGroup.mk'_surjective V),
      (CFSG.pCore_isPGroup (p := 2) (G := B)).map _⟩
  have h1 : (x : B ⧸ V) ∈ CFSG.pCore 2 (B ⧸ V) := himg ⟨x, hx, rfl⟩
  rw [hQ, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).mp h1

noncomputable def modO2EquivQuot {V : Subgroup B} [V.Normal] (hV : IsPGroup 2 V)
    (hQ : CFSG.pCore 2 (B ⧸ V) = ⊥) : B ⧸ CFSG.pCore 2 B ≃* B ⧸ V :=
  QuotientGroup.quotientMulEquivOfEq (pCore_eq_of_quot hV hQ)

theorem isPGroup_of_isE2 {V : Type} [Group V] {k : ℕ} (h : IsE2 k V) : IsPGroup 2 V := by
  obtain ⟨e⟩ := (h : Nonempty (V ≃* Multiplicative (Fin k → ZMod 2)))
  refine IsPGroup.of_card (n := k) ?_
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (Fin k → ZMod 2) = 2 ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem isPGroup_of_isExtraspecial2 {V : Type} [Group V] {m : ℕ} (h : IsExtraspecial2 m V) :
    IsPGroup 2 V :=
  IsPGroup.of_card h.2

theorem isPGroup_of_isZ4Cubed {V : Type} [Group V] (h : IsZ4Cubed V) : IsPGroup 2 V := by
  obtain ⟨e⟩ := h
  refine IsPGroup.of_card (n := 6) ?_
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (Fin 3 → ZMod 4) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem isPGroup_of_isZ4StarExtra2 {V : Type} [Group V] (h : IsZ4StarExtra2 V) :
    IsPGroup 2 V := by
  obtain ⟨Z, E, hZ4, -, hE, hZc, hZE, -⟩ := h
  have : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  intro v
  have hv : v ∈ ((E ⊔ Z : Subgroup V) : Set V) := by rw [sup_comm, hZE]; exact Subgroup.mem_top v
  rw [Subgroup.mul_normal] at hv
  obtain ⟨e, he, z, hz, rfl⟩ := hv
  refine ⟨5, ?_⟩
  have hcomm : Commute e z := Subgroup.mem_center_iff.mp (hZc hz) e
  have hE32 : e ^ 32 = 1 := by
    have : (⟨e, he⟩ : E) ^ Nat.card E = 1 := pow_card_eq_one'
    rw [hE.2] at this
    exact congrArg Subtype.val this
  have hZ4' : z ^ 4 = 1 := by
    have : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hZ4] at this
    exact congrArg Subtype.val this
  rw [hcomm.mul_pow, show 2 ^ 5 = 32 from rfl, hE32, show 32 = 4 * 8 from rfl, pow_mul, hZ4',
    one_pow, one_mul]

theorem card_of_surj_sl2 {X : Type} [Group X] [Finite B] (e : B ⧸ CFSG.pCore 2 B ≃* X)
    (hX : CFSG.IsQuasisimple X) (hZ : Nat.card (Subgroup.center X) ∣ 3) {q : ℕ} [hq : Fact q.Prime]
    (hq5 : 5 ≤ q) (φ : B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (hφ : Function.Surjective φ) : ∃ c, c ∣ 3 ∧ Nat.card X * 2 = c * (q * (q ^ 2 - 1)) := by
  have hqp : q.Prime := hq.out
  let ψ : B →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q) := (QuotientGroup.mk' _).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hO : CFSG.pCore 2 B ≤ ψ.ker := by
    have : ((CFSG.pCore 2 B).map φ).Normal := (CFSG.pCore_normal (p := 2) (G := B)).map φ hφ
    rcases A1c.normal_le_center_or_eq_top hq5 ((CFSG.pCore 2 B).map φ) with hz | ht
    · intro x hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (φ x)).mpr (hz ⟨x, hx, rfl⟩)
    · exfalso
      have h2 : IsPGroup 2 ((CFSG.pCore 2 B).map φ) := (CFSG.pCore_isPGroup (p := 2) (G := B)).map φ
      rw [ht] at h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      rw [Subgroup.card_top, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod] at hk
      have h3 : q ∣ 2 ^ k := hk ▸ dvd_mul_right q _
      have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h3)
      omega
  let χ : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q) :=
    (QuotientGroup.lift _ ψ hO).comp e.symm.toMonoidHom
  have hχ : Function.Surjective χ := by
    intro y
    obtain ⟨b, rfl⟩ := hψ y
    exact ⟨e (b : B ⧸ CFSG.pCore 2 B), by simp [χ]⟩
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)) =
      q * (q ^ 2 - 1) / 2 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula (ZMod q) ⟨q, 1, hqp,
      hqp.odd_of_ne_two (by omega), le_rfl, by rw [Nat.card_zmod, pow_one]⟩, Nat.card_zmod]
  have hev : 2 ∣ q * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left (even_iff_two_dvd.mp
      (Nat.Odd.sub_odd ((hqp.odd_of_ne_two (by omega)).pow) odd_one)) q
  have hker : χ.ker ≤ Subgroup.center X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hX χ.normal_ker with ht | hz
    · exfalso
      have h60 : 1 < Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)) := by
        rw [hcard]
        have := cube_sub_le (by norm_num : 1 ≤ 5) hq5
        norm_num at this
        omega
      have := Finite.one_lt_card_iff_nontrivial.mp h60
      obtain ⟨y, hy⟩ := exists_ne (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q))
      obtain ⟨x, rfl⟩ := hχ y
      exact hy (χ.mem_ker.mp (ht ▸ Subgroup.mem_top x))
    · exact hz
  refine ⟨Nat.card χ.ker, (Subgroup.card_dvd_of_le hker).trans hZ, ?_⟩
  rw [χ.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ hχ).toEquiv, hcard,
    mul_right_comm, Nat.div_mul_cancel hev, mul_comm]

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
