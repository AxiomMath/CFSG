module

public import CFSG.Quasithin.H13.L32A727k
public import CFSG.Quasithin.Background.D2Thirteen
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin.H13.L32A.E9

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.FixR CFSG.LieType.BorelTits
open scoped commutatorElement

variable {W : Type} [CommGroup W]

theorem three_le_rk_commSub [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {b c : MulAut W}
    (hb : b ^ 2 = 1) (hc : c ^ 3 = 1) (hbc : b * c = c * b)
    (h6 : 6 ≤ rk (commV (Subgroup.zpowers c))) :
    3 ≤ rk (commSub (fixV (Subgroup.zpowers b)) (Subgroup.zpowers c)) := by
  set Y := commV (Subgroup.zpowers c) with hY
  have hbC : b ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute c b from hbc.symm) k).eq
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup (MulAut W)) :
      Set (MulAut W)) := Subgroup.centralizer_le_normalizer _ hbC
  have hYb : ∀ x ∈ Subgroup.zpowers b, ∀ w ∈ Y, x w ∈ Y := by
    intro x hx w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact apply_mem_commV (Subgroup.zpowers c) (Subgroup.zpow_mem _ hbN k) hw
  have h1 := rk_commSub_add_rk_inf_fixV hYb
  have h2 := commSub_zpowers_le_inf_fixV hW hb hYb
  have h3 : rk (commSub Y (Subgroup.zpowers b)) ≤
      rk (Y ⊓ fixV (Subgroup.zpowers b) : Subgroup W) := rk_mono h2
  have h4 : Y ⊓ fixV (Subgroup.zpowers b) ≤
      commSub (fixV (Subgroup.zpowers b)) (Subgroup.zpowers c) := by
    rintro w ⟨hwY, hwb⟩
    exact mem_commSub_of_nu3_eq_one hW hwb (commV_le_ker_nu3 hc hwY)
  have h5 := rk_mono h4
  omega

theorem exists_inverted3 {P : Subgroup (MulAut W)} {a : MulAut W} (ha2 : a ^ 2 = 1)
    (haN : ∀ κ ∈ P, a * κ * a⁻¹ ∈ P) (hf : ¬ ∀ κ ∈ P, a * κ = κ * a) :
    ∃ q ∈ P, q ≠ 1 ∧ a * q * a⁻¹ = q⁻¹ := by
  push Not at hf
  obtain ⟨κ, hκ, hne⟩ := hf
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  refine ⟨κ * (a * κ * a⁻¹)⁻¹, P.mul_mem hκ (P.inv_mem (haN κ hκ)), ?_, ?_⟩
  · intro h
    apply hne
    have h1 : κ = a * κ * a⁻¹ := mul_inv_eq_one.mp h
    calc a * κ = a * κ * a⁻¹ * a := by group
      _ = κ * a := by rw [← h1]
  · rw [ha1]
    calc a * (κ * (a * κ * a)⁻¹) * a = a * κ * a⁻¹ * κ⁻¹ * a⁻¹ * a := by group
      _ = a * κ * a⁻¹ * κ⁻¹ := by group
      _ = (κ * (a * κ * a)⁻¹)⁻¹ := by rw [ha1]; group

theorem inverts_of_fix {P : Subgroup (MulAut W)} (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {b : MulAut W} (hb2 : b ^ 2 = 1) (hbN : ∀ κ ∈ P, b * κ * b⁻¹ ∈ P)
    (hfix : ∀ c ∈ P, b * c = c * b → c = 1) : ∀ κ ∈ P, b * κ * b⁻¹ = κ⁻¹ := by
  intro κ hκ
  have hbb : b * b = 1 := by rw [← sq]; exact hb2
  have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hm : κ * (b * κ * b⁻¹) ∈ P := P.mul_mem hκ (hbN κ hκ)
  have h1 : b * (κ * (b * κ * b⁻¹)) * b⁻¹ = (b * κ * b⁻¹) * κ := by
    rw [hb1]
    calc b * (κ * (b * κ * b)) * b = b * κ * b * κ * (b * b) := by group
      _ = b * κ * b * κ := by rw [hbb, mul_one]
  have h2 : (b * κ * b⁻¹) * κ = κ * (b * κ * b⁻¹) := hPc _ (hbN κ hκ) κ hκ
  have hc : b * (κ * (b * κ * b⁻¹)) = (κ * (b * κ * b⁻¹)) * b := by
    calc b * (κ * (b * κ * b⁻¹)) = b * (κ * (b * κ * b⁻¹)) * b⁻¹ * b := by group
      _ = κ * (b * κ * b⁻¹) * b := by rw [h1, h2]
  exact eq_inv_of_mul_eq_one_right (hfix _ hm hc)

theorem conj_eq_or_inv {M : Type*} [Group M] {g c : M} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (h : g * c * g⁻¹ ∈ Subgroup.zpowers c) : g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [zpow_eq_zpow_emod' k hc3] at hk
  simp only [Nat.cast_ofNat] at hk
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk
    apply hc1
    have : g * c * g⁻¹ * g = 1 * g := by rw [← hk]
    simpa using this
  · rw [h1, zpow_one] at hk
    exact Or.inl hk.symm
  · rw [h2, zpow_two] at hk
    refine Or.inr ?_
    rw [← hk]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_three', hc3])

theorem ne_inv_of_three {M : Type*} [Group M] {c : M} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    c ≠ c⁻¹ := by
  intro h
  apply hc1
  have hcc : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel c
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [hc3, hcc, inv_one, one_mul]

theorem mul_comm_of_same {a a' c : MulAut W} (ha : a * c * a⁻¹ = c ∨ a * c * a⁻¹ = c⁻¹)
    (ha' : a' * c * a'⁻¹ = c ∨ a' * c * a'⁻¹ = c⁻¹) (hc : c ≠ c⁻¹)
    (hiff : a * c = c * a ↔ a' * c = c * a') : a * a' * c = c * (a * a') := by
  rcases ha with ha | ha
  · have h1 : a * c = c * a := mul_inv_eq_iff_eq_mul.mp ha
    have h2 : a' * c = c * a' := hiff.mp h1
    calc a * a' * c = a * (a' * c) := by group
      _ = a * (c * a') := by rw [h2]
      _ = (a * c) * a' := by group
      _ = c * (a * a') := by rw [h1]; group
  · have h1 : ¬ a * c = c * a := fun h => hc (by rw [← ha, h]; group)
    have h2 : ¬ a' * c = c * a' := fun h => h1 (hiff.mpr h)
    have ha'' : a' * c * a'⁻¹ = c⁻¹ := by
      rcases ha' with h | h
      · exact absurd (mul_inv_eq_iff_eq_mul.mp h) h2
      · exact h
    have e : a * a' * c * (a * a')⁻¹ = c := by
      calc a * a' * c * (a * a')⁻¹ = a * (a' * c * a'⁻¹) * a⁻¹ := by group
        _ = a * c⁻¹ * a⁻¹ := by rw [ha'']
        _ = (a * c * a⁻¹)⁻¹ := by group
        _ = c := by rw [ha, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp e

theorem exists_reflection [Finite W] {X P A : Subgroup (MulAut W)} [Fintype ↥P]
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 9)
    (hP3 : ∀ κ ∈ P, κ ^ 3 = 1) (hAX : A ≤ X) (hXP : ∀ g ∈ X, ∀ κ ∈ P, g * κ * g⁻¹ ∈ P)
    (hfaith : ∀ a ∈ X, a ^ 2 = 1 → (∀ κ ∈ P, a * κ = κ * a) → a = 1)
    (hA : IsElemAbelian2 A) (hA4 : 4 ≤ Nat.card A) :
    ∃ b ∈ A, b ≠ 1 ∧ Nat.card A = 2 * Nat.card (Subgroup.zpowers b) ∧
      ∃ c ∈ P, c ≠ 1 ∧ b * c = c * b ∧ ∃ a ∈ A, a * c ≠ c * a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : Nat.card P = 9 := by rw [Nat.card_eq_fintype_card, hP]
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2 a ha
  have hAinv : ∀ a ∈ A, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hA2 a ha)
  obtain ⟨b₁, hb₁A, hb₁1⟩ : ∃ b₁ ∈ A, b₁ ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr h
    rw [this, Subgroup.card_bot] at hA4
    omega
  obtain ⟨b₂, hb₂A, hb₂1, hb₂b₁⟩ : ∃ b₂ ∈ A, b₂ ≠ 1 ∧ b₂ ≠ b₁ := by
    by_contra h
    push Not at h
    let S : Finset (MulAut W) := {1, b₁}
    have hS : ∀ a : A, (a : MulAut W) ∈ S := fun a => by
      by_cases ha1 : (a : MulAut W) = 1
      · simp [S, ha1]
      · simp [S, h a a.2 ha1]
    have : Nat.card A ≤ 2 := by
      calc Nat.card A ≤ Nat.card ↥(S : Set (MulAut W)) :=
            Nat.card_le_card_of_injective (fun a => ⟨a, hS a⟩)
              (fun a a' h => Subtype.ext
                (congrArg (fun s : ↥(S : Set (MulAut W)) => (s : MulAut W)) h))
        _ = S.card := by simp
        _ ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨b, hbA, hb1, hbinv⟩ : ∃ b ∈ A, b ≠ 1 ∧ ¬ ∀ κ ∈ P, b * κ * b⁻¹ = κ⁻¹ := by
    by_contra h
    push Not at h
    have e1 := h b₁ hb₁A hb₁1
    have e2 := h b₂ hb₂A hb₂1
    have hprod : b₁ * b₂ = 1 := by
      refine hfaith _ (hAX (A.mul_mem hb₁A hb₂A)) (hA.2 _ (A.mul_mem hb₁A hb₂A)) fun κ hκ => ?_
      have : b₁ * b₂ * κ * (b₁ * b₂)⁻¹ = κ := by
        calc b₁ * b₂ * κ * (b₁ * b₂)⁻¹ = b₁ * (b₂ * κ * b₂⁻¹) * b₁⁻¹ := by group
          _ = b₁ * κ⁻¹ * b₁⁻¹ := by rw [e2 κ hκ]
          _ = (b₁ * κ * b₁⁻¹)⁻¹ := by group
          _ = κ := by rw [e1 κ hκ, inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp this
    apply hb₂b₁
    calc b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right hprod
      _ = b₁ := hAinv b₁ hb₁A
  have hbX : b ∈ X := hAX hbA
  have hb2 : b ^ 2 = 1 := hA.2 b hbA
  obtain ⟨c, hcP, hc1, hbc⟩ : ∃ c ∈ P, c ≠ 1 ∧ b * c = c * b := by
    by_contra h
    push Not at h
    exact hbinv (inverts_of_fix hPc hb2 (hXP b hbX) fun c hc hbc => by
      by_contra hc1
      exact h c hc hc1 hbc)
  have hbf : ¬ ∀ κ ∈ P, b * κ = κ * b := fun h => hb1 (hfaith b hbX hb2 h)
  obtain ⟨i, hiP, hi1, hbi⟩ := exists_inverted3 hb2 (hXP b hbX) hbf
  have hc3 := hP3 c hcP
  have hi3 := hP3 i hiP
  have hcinv := ne_inv_of_three hc3 hc1
  have hiinv := ne_inv_of_three hi3 hi1
  have hcard3 : ∀ u ∈ P, u ≠ 1 → Nat.card (Subgroup.zpowers u) = 3 := fun u hu hu1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hP3 u hu) hu1]
  set C := P ⊓ Subgroup.centralizer ({b} : Set (MulAut W)) with hCdef
  have memC : ∀ {κ : MulAut W}, κ ∈ C ↔ κ ∈ P ∧ b * κ = κ * b := by
    intro κ
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  have hiC : i ∉ C := by
    intro h
    apply hiinv
    have h1 : b * i * b⁻¹ = i := by rw [(memC.mp h).2]; group
    rw [← hbi, h1]
  have hCc : C = Subgroup.zpowers c := by
    have hle : Subgroup.zpowers c ≤ C := (Subgroup.zpowers_le).mpr (memC.mpr ⟨hcP, hbc⟩)
    have hdvd : Nat.card C ∣ 9 := hP' ▸ Subgroup.card_dvd_of_le (inf_le_left : C ≤ P)
    have h3 : 3 ≤ Nat.card C := hcard3 c hcP hc1 ▸ Subgroup.card_le_of_le hle
    have hne9 : Nat.card C ≠ 9 := by
      intro h9
      have hCP : C = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hP', h9])
      exact hiC (by rw [hCP]; exact hiP)
    have hC3 : Nat.card C = 3 := by
      have : Nat.card C ∈ Nat.divisors 9 := by simp [hdvd]
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hC3, hcard3 c hcP hc1])).symm
  let I : Subgroup (MulAut W) :=
    { carrier := {κ | κ ∈ P ∧ b * κ * b⁻¹ = κ⁻¹}
      mul_mem' := fun {κ μ} hκ hμ => ⟨P.mul_mem hκ.1 hμ.1, by
        rw [show b * (κ * μ) * b⁻¹ = (b * κ * b⁻¹) * (b * μ * b⁻¹) by group, hκ.2, hμ.2,
          mul_inv_rev]
        exact hPc κ⁻¹ (P.inv_mem hκ.1) μ⁻¹ (P.inv_mem hμ.1)⟩
      one_mem' := ⟨P.one_mem, by group⟩
      inv_mem' := fun {κ} hκ => ⟨P.inv_mem hκ.1, by
        rw [show b * κ⁻¹ * b⁻¹ = (b * κ * b⁻¹)⁻¹ by group, hκ.2]⟩ }
  have memI : ∀ {κ : MulAut W}, κ ∈ I ↔ κ ∈ P ∧ b * κ * b⁻¹ = κ⁻¹ := Iff.rfl
  have hcI : c ∉ I := by
    intro h
    apply hcinv
    rw [← (memI.mp h).2, hbc]
    group
  have hIi : I = Subgroup.zpowers i := by
    have hle : Subgroup.zpowers i ≤ I := (Subgroup.zpowers_le).mpr (memI.mpr ⟨hiP, hbi⟩)
    have hIP : I ≤ P := fun κ hκ => (memI.mp hκ).1
    have hdvd : Nat.card I ∣ 9 := hP' ▸ Subgroup.card_dvd_of_le hIP
    have h3 : 3 ≤ Nat.card I := hcard3 i hiP hi1 ▸ Subgroup.card_le_of_le hle
    have hne9 : Nat.card I ≠ 9 := by
      intro h9
      have hIP' : I = P := Subgroup.eq_of_le_of_card_ge hIP (by rw [hP', h9])
      exact hcI (by rw [hIP']; exact hcP)
    have hI3 : Nat.card I = 3 := by
      have : Nat.card I ∈ Nat.divisors 9 := by simp [hdvd]
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hI3, hcard3 i hiP hi1])).symm
  have hab : ∀ a ∈ A, a * b = b * a := fun a ha => hA.1 a ha b hbA
  have hac : ∀ a ∈ A, a * c * a⁻¹ = c ∨ a * c * a⁻¹ = c⁻¹ := by
    intro a ha
    refine conj_eq_or_inv hc3 hc1 ?_
    rw [← hCc]
    refine memC.mpr ⟨hXP a (hAX ha) c hcP, ?_⟩
    calc b * (a * c * a⁻¹) = (b * a) * c * a⁻¹ := by group
      _ = a * (b * c) * a⁻¹ := by rw [← hab a ha]; group
      _ = a * (c * b) * a⁻¹ := by rw [hbc]
      _ = a * c * (b * a⁻¹) := by group
      _ = a * c * (a⁻¹ * b) := by
          rw [(show Commute b a⁻¹ from (Commute.inv_right (hab a ha).symm)).eq]
      _ = a * c * a⁻¹ * b := by group
  have hai : ∀ a ∈ A, a * i * a⁻¹ = i ∨ a * i * a⁻¹ = i⁻¹ := by
    intro a ha
    refine conj_eq_or_inv hi3 hi1 ?_
    rw [← hIi]
    refine memI.mpr ⟨hXP a (hAX ha) i hiP, ?_⟩
    have hba : b * a = a * b := (hab a ha).symm
    calc b * (a * i * a⁻¹) * b⁻¹ = (b * a) * i * (b * a)⁻¹ := by group
      _ = (a * b) * i * (a * b)⁻¹ := by rw [hba]
      _ = a * (b * i * b⁻¹) * a⁻¹ := by group
      _ = a * i⁻¹ * a⁻¹ := by rw [hbi]
      _ = (a * i * a⁻¹)⁻¹ := by group
  have hci : Subgroup.zpowers c ≠ Subgroup.zpowers i := by
    intro h
    apply hcI
    rw [hIi, ← h]
    exact Subgroup.mem_zpowers c
  have hPci : Subgroup.zpowers c ⊔ Subgroup.zpowers i = P :=
    sup_eq_of_ne9 hP ((Subgroup.zpowers_le).mpr hcP) ((Subgroup.zpowers_le).mpr hiP)
      (hcard3 c hcP hc1) (hcard3 i hiP hi1) hci
  have htriv : ∀ d ∈ A, d * c = c * d → d * i = i * d → d = 1 := by
    intro d hd hdc hdi
    refine hfaith d (hAX hd) (hA.2 d hd) fun κ hκ => ?_
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers i ≤
        Subgroup.centralizer ({d} : Set (MulAut W)) := by
      refine sup_le ((Subgroup.zpowers_le).mpr ?_) ((Subgroup.zpowers_le).mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact hdc.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact hdi.symm
    rw [hPci] at hle
    exact ((Subgroup.mem_centralizer_singleton_iff).mp (hle hκ)).symm
  have hinj : ∀ a ∈ A, ∀ a' ∈ A, (a * c = c * a ↔ a' * c = c * a') →
      (a * i = i * a ↔ a' * i = i * a') → a = a' := by
    intro a ha a' ha' h1 h2
    have hd := htriv (a * a') (A.mul_mem ha ha')
      (mul_comm_of_same (hac a ha) (hac a' ha') hcinv h1)
      (mul_comm_of_same (hai a ha) (hai a' ha') hiinv h2)
    calc a = a' ⁻¹ := eq_inv_of_mul_eq_one_left hd
      _ = a' := hAinv a' ha'
  have hA4' : Nat.card A ≤ 4 := by
    let χ : A → Bool × Bool := fun a =>
      (decide ((a : MulAut W) * c = c * a), decide ((a : MulAut W) * i = i * a))
    have hχ : Function.Injective χ := by
      intro a a' h
      simp only [χ, Prod.mk.injEq, decide_eq_decide] at h
      exact Subtype.ext (hinj a a.2 a' a'.2 h.1 h.2)
    calc Nat.card A ≤ Nat.card (Bool × Bool) := Nat.card_le_card_of_injective χ hχ
      _ = 4 := by simp
  have hbcard : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb2 hb1
  refine ⟨b, hbA, hb1, by omega, c, hcP, hc1, hbc, ?_⟩
  by_contra h
  push Not at h
  let χ : A → Bool := fun a => decide ((a : MulAut W) * i = i * a)
  have hχ : Function.Injective χ := by
    intro a a' e
    simp only [χ, decide_eq_decide] at e
    exact Subtype.ext (hinj a a.2 a' a'.2
      ⟨fun _ => h a' a'.2, fun _ => h a a.2⟩ e)
  have : Nat.card A ≤ 2 := by
    calc Nat.card A ≤ Nat.card Bool := Nat.card_le_card_of_injective χ hχ
      _ = 2 := by simp
  omega

theorem false_of_qhat [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {X P : Subgroup (MulAut W)}
    (hPX : P ≤ X) (hXP : ∀ g ∈ X, ∀ κ ∈ P, g * κ * g⁻¹ ∈ P)
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP9 : Nat.card P = 9) (hP3 : ∀ κ ∈ P, κ ^ 3 = 1)
    (hfaith : ∀ a ∈ X, a ^ 2 = 1 → (∀ κ ∈ P, a * κ = κ * a) → a = 1)
    (htrans : ∀ x ∈ P, x ≠ 1 → ∃ g ∈ X, g ^ 3 = 1 ∧ g * x * g⁻¹ ∉ Subgroup.zpowers x)
    (hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥P := Fintype.ofFinite _
  have hP : Fintype.card ↥P = 9 := by rw [← Nat.card_eq_fintype_card, hP9]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hq)
  have hr2 : r ≤ 2 := by
    rw [← hr] at hq
    exact_mod_cast hq
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr.symm hr2
  obtain ⟨r', hr', hr'2, ⟨⟨hA2, hAr⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAel := hA2.isElemAbelian2
  have hAX : A ≤ X := hA2.le
  have hN : ∀ c ∈ P, c ≠ 1 → 6 ≤ rk (commV (Subgroup.zpowers c)) := fun c hc hc1 =>
    six_le_rk_commV hW hPc hP hP3 hXP htrans hc hc1
  by_cases hrk : rk A = 1
  ·
    have hAcard : Nat.card A = 2 := by
      rw [card_eq_two_pow_of_isPGroup hAel.isPGroup, hrk, pow_one]
    obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp hA2.ne_bot
    have ht1' : (t : MulAut W) ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hAt : Subgroup.zpowers (t : MulAut W) = A := zpowers_eq_of_prime_card hAcard t.2 ht1'
    have hm : (rk (commV (Subgroup.zpowers (t : MulAut W))) : ℚ) = r' := by
      rw [← hAr, rAV, hAt, hrk, ← hAt, rkIdx_fixV_zpowers]
      simp
    have hm2 : rk (commV (Subgroup.zpowers (t : MulAut W))) ≤ 2 := by
      have : (rk (commV (Subgroup.zpowers (t : MulAut W))) : ℚ) ≤ 2 := hm ▸ hr'2
      exact_mod_cast this
    have ht2 : (t : MulAut W) ^ 2 = 1 := hAel.2 t t.2
    have htX : (t : MulAut W) ∈ X := hAX t.2
    have hf : ¬ ∀ κ ∈ P, (t : MulAut W) * κ = κ * t := fun h => ht1' (hfaith _ htX ht2 h)
    obtain ⟨c, hcP, hc1, hinv⟩ := exists_inverted3 ht2 (hXP _ htX) hf
    have hodd : Odd (orderOf c) := by
      rw [orderOf_eq_prime (hP3 c hcP) hc1]
      decide
    obtain ⟨-, -, h3⟩ := d2_11_core hW ht2 hm2 hc1 hodd hinv
    have h6 := hN c hcP hc1
    rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  ·
    have hrk2 : 1 < rk A := by
      have := hA2.rk_pos
      omega
    have hA4 : 4 ≤ Nat.card A := by
      rw [card_eq_two_pow_of_isPGroup hAel.isPGroup]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) hrk2
    obtain ⟨b, hbA, hb1, hbcard, c, hcP, hc1, hbc, a, haA, hac⟩ :=
      exists_reflection hPc hP hP3 hAX hXP hfaith hAel hA4
    have hBA : Subgroup.zpowers b ≤ A := (Subgroup.zpowers_le).mpr hbA
    have hP3' : IsPGroup 3 ↥P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
    have hPO : P ≤ pCoreOf 3 X := le_pCoreOf_of_le_normalizer 3 hPX
      (fun g hg => Subgroup.mem_normalizer_fintype fun κ hκ => hXP g hg κ hκ) hP3'
    have hcC : c ∈ pCoreOf 3 X ⊓ Subgroup.centralizer
        ((Subgroup.zpowers b : Subgroup (MulAut W)) : Set (MulAut W)) := by
      refine ⟨hPO hcP, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (show Commute b c from hbc) k).eq
    set D := ⁅pCoreOf 3 X ⊓ Subgroup.centralizer
      ((Subgroup.zpowers b : Subgroup (MulAut W)) : Set (MulAut W)), A⁆ with hD
    have hcaD : ⁅c, a⁆ ∈ D := Subgroup.commutator_mem_commutator hcC haA
    have hca1 : ⁅c, a⁆ ≠ 1 := by
      intro h
      apply hac
      rw [commutatorElement_eq_one_iff_mul_comm] at h
      exact h.symm
    have hDne : D ≠ ⊥ := fun h => hca1 (by rw [h] at hcaD; exact Subgroup.mem_bot.mp hcaD)
    obtain ⟨-, -, hDcard, -, -, hDrk⟩ :=
      D2_13_hyperplane hW hr' hA hrk2 (p := 3) (by norm_num) hBA hbcard hD hDne
    have hcaP : ⁅c, a⁆ ∈ P := by
      rw [commutatorElement_def, show c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) by group]
      exact P.mul_mem hcP (hXP a (hAX haA) _ (P.inv_mem hcP))
    have hDz : D = Subgroup.zpowers ⁅c, a⁆ := by
      have hle : Subgroup.zpowers ⁅c, a⁆ ≤ D := (Subgroup.zpowers_le).mpr hcaD
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hP3 _ hcaP) hca1]
    have hbca : b * ⁅c, a⁆ = ⁅c, a⁆ * b := by
      have hbc' : Commute b c := hbc
      have hba' : Commute b a := (hAel.1 a haA b hbA).symm
      rw [commutatorElement_def]
      exact (((hbc'.mul_right hba').mul_right hbc'.inv_right).mul_right hba'.inv_right).eq
    have h3 := three_le_rk_commSub hW (hAel.2 b hbA) (hP3 _ hcaP) hbca (hN _ hcaP hca1)
    rw [hDz] at hDrk
    omega

end CFSG.Quasithin.H13.L32A.E9
