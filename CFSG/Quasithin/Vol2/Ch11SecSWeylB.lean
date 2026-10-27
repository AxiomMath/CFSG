module

public import CFSG.Quasithin.Vol2.Ch11SecSWeylA
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl

open CFSG.Open CFSG.Blueprint C11P9A CFSG.QuasithinUnique.Setup.X6

variable {Q : Type} [Group Q] [Finite Q]

theorem part2_of_inverting {M T E P : Subgroup Q} (hM : ¬ 27 ∣ Nat.card ↥M) (hTM : T ≤ M)
    (hT : Nat.card ↥T = 9) (hEM : E ≤ M) (hE : Nat.card ↥E = 9) (hMP : M ≤ P) {w : Q}
    (hw : ∀ t ∈ T, w * t * w⁻¹ = t⁻¹) (hwP : w ∉ P) (E₂ : Subgroup Q) (hE₂ : E₂ ≤ E) :
    ¬ Subgroup.normalizer (E₂ : Set Q) ≤ P := by
  obtain ⟨m, hm, rfl⟩ := exists_conj_of_card_nine hEM hTM hE hT hM
  have hw' : ∀ t ∈ T, w⁻¹ * t * w = t⁻¹ := fun t ht => by
    have h := hw t⁻¹ (T.inv_mem ht)
    rw [inv_inv] at h
    calc w⁻¹ * t * w = w⁻¹ * (w * t⁻¹ * w⁻¹) * w := by rw [h]
      _ = t⁻¹ := by group
  have key : ∀ h ∈ T.map (MulAut.conj m).toMonoidHom,
      (m * w * m⁻¹) * h * (m * w * m⁻¹)⁻¹ = h⁻¹ ∧ (m * w * m⁻¹)⁻¹ * h * (m * w * m⁻¹) = h⁻¹ := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · calc m * w * m⁻¹ * (m * t * m⁻¹) * (m * w * m⁻¹)⁻¹ = m * (w * t * w⁻¹) * m⁻¹ := by group
        _ = (m * t * m⁻¹)⁻¹ := by rw [hw t ht]; group
    · calc (m * w * m⁻¹)⁻¹ * (m * t * m⁻¹) * (m * w * m⁻¹) = m * (w⁻¹ * t * w) * m⁻¹ := by group
        _ = (m * t * m⁻¹)⁻¹ := by rw [hw' t ht]; group
  intro hle
  apply hwP
  have hg : m * w * m⁻¹ ∈ Subgroup.normalizer (E₂ : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [(key h (hE₂ hh)).1]
      exact E₂.inv_mem hh
    · intro hh
      have h1 := (key _ (hE₂ hh)).2
      have h2 : (m * w * m⁻¹)⁻¹ * ((m * w * m⁻¹) * h * (m * w * m⁻¹)⁻¹) * (m * w * m⁻¹) = h := by
        group
      rw [h2] at h1
      rw [h1]
      exact E₂.inv_mem hh
  have hP := hle hg
  have h3 : w = m⁻¹ * (m * w * m⁻¹) * m := by group
  rw [h3]
  exact P.mul_mem (P.mul_mem (P.inv_mem (hMP hm)) hP) (hMP hm)

theorem card_mul_dvd_of_inf_eq_bot {X E M : Subgroup Q} (hEX : E ≤ Subgroup.normalizer (X : Set Q))
    (hd : X ⊓ E = ⊥) (hXM : X ≤ M) (hEM : E ≤ M) : Nat.card ↥X * Nat.card ↥E ∣ Nat.card ↥M := by
  rw [← card_sup_eq_mul hEX hd]
  exact Subgroup.card_dvd_of_le (sup_le hEM hXM)

omit [Finite Q] in
theorem eq_one_of_two_three {x : Q} {A B : Subgroup Q} (hA : IsPGroup 2 ↥A) (hB : IsPGroup 3 ↥B)
    (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  obtain ⟨a, ha⟩ := hA ⟨x, hxA⟩
  obtain ⟨b, hb⟩ := hB ⟨x, hxB⟩
  have ha' : x ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hb' : x ^ 3 ^ b = 1 := congrArg Subtype.val hb
  have h1 := orderOf_dvd_of_pow_eq_one ha'
  have h2 := orderOf_dvd_of_pow_eq_one hb'
  have hc : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc h1 h2)

omit [Finite Q] in
theorem center_le_sectionCentralizer (X K : Subgroup Q) :
    Subgroup.center Q ≤ sectionCentralizer X K := by
  intro z hz
  have hc := Subgroup.mem_center_iff.mp hz
  refine ⟨Subgroup.center_le_normalizer (X : Set Q) hz,
    Subgroup.center_le_normalizer (K : Set Q) hz, fun x _ => ?_⟩
  rw [← hc x, mul_inv_cancel_right, mul_inv_cancel]
  exact K.one_mem

theorem part2_of_center {M E B D : Subgroup Q} (hM : ¬ 27 ∣ Nat.card ↥M) (hEM : E ≤ M)
    (hE : Nat.card ↥E = 9) (hZ : Nat.card ↥(Subgroup.center Q) = 3)
    (hZM : Subgroup.center Q ≤ M) (hMB : M ≤ Subgroup.normalizer (B : Set Q)) (hDB : D ≤ B)
    (hDM : D ≤ M) (hD3 : 3 ∣ Nat.card ↥D)
    (hsc : B ⊓ sectionCentralizer B (pCoreOf 2 B) ≤ pCoreOf 2 B)
    (hBn : Subgroup.normalizer (B : Set Q) ≠ ⊤) (E₂ : Subgroup Q)
    (hE₂ : E₂ ≤ E ⊓ sectionCentralizer B (pCoreOf 2 B)) :
    ¬ Subgroup.normalizer (E₂ : Set Q) ≤ Subgroup.normalizer (B : Set Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE3 : IsPGroup 3 ↥E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  have hZE : Subgroup.center Q ≤ E := by
    by_contra hne
    have hd : Subgroup.center Q ⊓ E = ⊥ := by
      have hdvd : Nat.card ↥(Subgroup.center Q ⊓ E) ∣ 3 :=
        hZ ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hZ])).symm.le.trans
          inf_le_right) hne
    have h := card_mul_dvd_of_inf_eq_bot (X := Subgroup.center Q) (E := E) (M := M)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top) hd hZM hEM
    rw [hZ, hE] at h
    exact hM h
  set C := E ⊓ sectionCentralizer B (pCoreOf 2 B) with hCdef
  have hZC : Subgroup.center Q ≤ C := le_inf hZE (center_le_sectionCentralizer _ _)
  have hCE : ¬ E ≤ sectionCentralizer B (pCoreOf 2 B) := by
    intro hEC
    have hX : E ≤ Subgroup.normalizer ((B ⊓ M : Subgroup Q) : Set Q) := fun e he =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hMB (hEM he), Subgroup.le_normalizer (hEM he)⟩
    have hd : B ⊓ M ⊓ E = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      exact eq_one_of_two_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B) hE3
        (hsc ⟨hx.1.1, hEC hx.2⟩) hx.2
    have h := card_mul_dvd_of_inf_eq_bot hX hd inf_le_right hEM
    rw [hE] at h
    have h3 : 3 ∣ Nat.card ↥(B ⊓ M) := hD3.trans (Subgroup.card_dvd_of_le (le_inf hDB hDM))
    exact hM ((Nat.mul_dvd_mul_right h3 9).trans h)
  have hCZ : C = Subgroup.center Q := by
    have hdvd : Nat.card ↥C ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hE]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have h3 : 3 ∣ Nat.card ↥C := hZ ▸ Subgroup.card_dvd_of_le hZC
    interval_cases i
    · rw [hci] at h3
      norm_num at h3
    · exact (Subgroup.eq_of_le_of_card_ge hZC (by rw [hci, hZ]; norm_num)).symm
    · exact absurd ((Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ E)
        (by rw [hci, hE]; norm_num)).symm.le.trans inf_le_right) hCE
  intro hle
  apply hBn
  rw [eq_top_iff]
  refine le_trans (fun g _ => ?_) hle
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hz := Subgroup.mem_center_iff.mp (hCZ ▸ hE₂ hh) g
    rw [hz, mul_inv_cancel_right]
    exact hh
  · intro hh
    have hz := Subgroup.mem_center_iff.mp (hCZ ▸ hE₂ hh) g⁻¹
    have e : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g * h * g⁻¹ * g⁻¹ * g := by rw [hz]
        _ = g * h * g⁻¹ := by group
    rw [e]
    exact hh

end CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl
