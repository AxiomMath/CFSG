module

public import CFSG.GroupTheory.CoprimeCommutatorCard
public import CFSG.GroupTheory.CoprimeHyperplaneCentralizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem commutator_inf_centralizer_right_eq_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {I P : Subgroup G} (hI : IsElemAbelian 2 I) (hP : IsPGroup p P)
    (hPI : P ≤ Subgroup.normalizer (I : Set G)) :
    ⁅I, P⁆ ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  classical
  have hIPle : (⁅I, P⁆ : Subgroup G) ≤ I := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hxaI : x * a⁻¹ * x⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hPI hx) a⁻¹).mp (I.inv_mem ha)
    have hmem : a * (x * a⁻¹ * x⁻¹) ∈ I := I.mul_mem ha hxaI
    simpa [commutatorElement_def, mul_assoc] using hmem
  obtain ⟨-, hdisj⟩ := CFSG.GroupTheory.card_centralizer_mul_card_commutator_of_coprime
    (W := I) (X := P) hI.1 hI.2 hP hp2 hPI
  refine le_antisymm ?_ bot_le
  intro z hz
  have hmem : z ∈ (I ⊓ Subgroup.centralizer (P : Set G)) ⊓ (⁅I, P⁆ : Subgroup G) :=
    ⟨⟨hIPle hz.1, hz.2⟩, hz.1⟩
  rw [hdisj] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem inf_centralizer_le_commutator_of_sup_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A P B₁ B₂ : Subgroup G} (hA : IsElemAbelian 2 A) (hP : IsPGroup p P)
    (hPab : IsMulCommutative ↥P) (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (hAP : A ⊓ Subgroup.centralizer (P : Set G) = ⊥) (hB₁ : B₁ ≤ P) (hB₂ : B₂ ≤ P)
    (hsup : B₁ ⊔ B₂ = P) :
    A ⊓ Subgroup.centralizer (B₂ : Set G) ≤ ⁅A, B₁⁆ := by
  classical
  let W : Subgroup G := A ⊓ Subgroup.centralizer (B₂ : Set G)
  change W ≤ ⁅A, B₁⁆
  have hW : W = A ⊓ Subgroup.centralizer (B₂ : Set G) := rfl
  have hWleA : W ≤ A := by rw [hW]; exact inf_le_left
  have hWleC : W ≤ Subgroup.centralizer (B₂ : Set G) := by rw [hW]; exact inf_le_right
  have hconj : ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W := by
    intro p hp w hw
    rw [hW] at hw ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hPA hp) w).mp hw.1
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hpc : p * c = c * p :=
        congrArg Subtype.val (hPab.is_comm.comm ⟨p, hp⟩ ⟨c, hB₂ hc⟩)
      have hwc : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hw.2) c hc
      have hpc_inv : c * p⁻¹ = p⁻¹ * c := by
        calc c * p⁻¹ = p⁻¹ * (p * c) * p⁻¹ := by group
          _ = p⁻¹ * (c * p) * p⁻¹ := by rw [hpc]
          _ = p⁻¹ * c := by group
      calc c * (p * w * p⁻¹) = (c * p) * w * p⁻¹ := by group
        _ = (p * c) * w * p⁻¹ := by rw [← hpc]
        _ = p * (c * w) * p⁻¹ := by group
        _ = p * (w * c) * p⁻¹ := by rw [hwc]
        _ = p * w * (c * p⁻¹) := by group
        _ = p * w * (p⁻¹ * c) := by rw [hpc_inv]
        _ = (p * w * p⁻¹) * c := by group
  have hB1normW : B₁ ≤ Subgroup.normalizer (W : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hconj b (hB₁ hb) h hh, fun hh => by
      have hmem := hconj b⁻¹ (P.inv_mem (hB₁ hb)) (b * h * b⁻¹) hh
      have hEq : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rwa [hEq] at hmem⟩
  have hWab : IsMulCommutative ↥W := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro w' hw'
    exact (congrArg Subtype.val (hA.1.is_comm.comm
      ⟨w, hWleA hw⟩ ⟨w', hWleA hw'⟩)).symm
  have hWexp : ∀ w ∈ W, w ^ 2 = 1 := fun w hw => hA.2 w (hWleA hw)
  have hJleW : (⁅W, B₁⁆ : Subgroup G) ≤ W := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hba : b * a⁻¹ * b⁻¹ ∈ W := hconj b (hB₁ hb) a⁻¹ (W.inv_mem ha)
    have hmem : a * (b * a⁻¹ * b⁻¹) ∈ W := W.mul_mem ha hba
    simpa [commutatorElement_def, mul_assoc] using hmem
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_centralizer_mul_card_commutator_of_coprime
    (W := W) (X := B₁) hWab hWexp (hP.to_le hB₁) hp2 hB1normW
  let M : Subgroup G := W ⊓ Subgroup.centralizer (B₁ : Set G)
  have hM : M = W ⊓ Subgroup.centralizer (B₁ : Set G) := rfl
  have hMeq : M = ⊥ := by
    have hB1CM : B₁ ≤ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      rw [hM]
      exact inf_le_right
    have hB2CM : B₂ ≤ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      exact le_trans (by rw [hM]; exact inf_le_left) hWleC
    have hPCM : P ≤ Subgroup.centralizer (M : Set G) := by
      rw [← hsup]
      exact sup_le hB1CM hB2CM
    have hMCP : M ≤ Subgroup.centralizer (P : Set G) :=
      (Subgroup.le_centralizer_iff).mp hPCM
    have hMA : M ≤ A := by
      rw [hM]
      exact le_trans inf_le_left hWleA
    have hle : M ≤ ⊥ := by
      rw [← hAP]
      exact le_inf hMA hMCP
    exact le_bot_iff.mp hle
  have hMeq' : (W ⊓ Subgroup.centralizer (B₁ : Set G) : Subgroup G) = ⊥ := by
    rw [← hM]
    exact hMeq
  rw [hMeq', Subgroup.card_bot, one_mul] at hcard
  have hWeq : (⁅W, B₁⁆ : Subgroup G) = W :=
    Subgroup.eq_of_le_of_card_ge hJleW (le_of_eq hcard)
  rw [← hWeq]
  exact Subgroup.commutator_mono hWleA le_rfl

private theorem seven_nine_mod_eq_or_top {p : ℕ} [Fact p.Prime] {P B Q : Subgroup G}
    (hBQ : B ≤ Q) (hQP : Q ≤ P) (hBcard : Nat.card B * p = Nat.card P) :
    Q = B ∨ Q = P := by
  classical
  have hQdvdP : Nat.card Q ∣ Nat.card P := Subgroup.card_dvd_of_le hQP
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBQ
  have hmdvd : m ∣ p := by
    rw [hm] at hQdvdP
    rw [← hBcard] at hQdvdP
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos (α := B)) hQdvdP
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd m hmdvd with h1 | hp
  · left
    exact (Subgroup.eq_of_le_of_card_ge hBQ (by simp [hm, h1])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hQP (by simp [hm, hp, hBcard])

theorem inf_centralizer_inf_centralizer_eq_of_card_mul_eq {p : ℕ} [Fact p.Prime]
    {A P B : Subgroup G} (hB : B ≤ P) (hBcard : Nat.card B * p = Nat.card P)
    (hAP : A ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hne : A ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥) :
    P ⊓ Subgroup.centralizer ((A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) =
      B := by
  classical
  let C : Subgroup G := A ⊓ Subgroup.centralizer (B : Set G)
  let Q : Subgroup G := P ⊓ Subgroup.centralizer (C : Set G)
  change Q = B
  have hCdef : C = A ⊓ Subgroup.centralizer (B : Set G) := rfl
  have hQdef : Q = P ⊓ Subgroup.centralizer (C : Set G) := rfl
  have hBQ : B ≤ Q := by
    intro b hb
    rw [hQdef]
    refine Subgroup.mem_inf.mpr ⟨hB hb, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcB : c ∈ Subgroup.centralizer (B : Set G) := by
      rw [hCdef] at hc
      exact hc.2
    exact ((Subgroup.mem_centralizer_iff.mp hcB) b hb).symm
  have hQP : Q ≤ P := by rw [hQdef]; exact inf_le_left
  have hQne : Q ≠ P := by
    intro hQP_eq
    have hPC : P ≤ Subgroup.centralizer (C : Set G) := by
      rw [hQdef] at hQP_eq
      rw [← hQP_eq]
      exact inf_le_right
    have hCCP : C ≤ Subgroup.centralizer (P : Set G) := (Subgroup.le_centralizer_iff).mp hPC
    have hCbot : C ≤ ⊥ := by
      rw [← hAP]
      exact le_inf (by rw [hCdef]; exact inf_le_left) hCCP
    have hCbot' : C = ⊥ := le_bot_iff.mp hCbot
    rw [hCdef] at hCbot'
    exact hne hCbot'
  rcases seven_nine_mod_eq_or_top hBQ hQP hBcard with h | h
  · exact h
  · exact absurd h hQne

theorem exists_card_mul_eq_inf_centralizer_ne_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A P : Subgroup G} (hA : IsElemAbelian 2 A) (hP : IsElemAbelian p P)
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥)
    (hAP : A ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    ∃ B : Subgroup G, B ≤ P ∧ Nat.card B * p = Nat.card P ∧
      A ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  classical
  have hP2 : IsPGroup p P := fun y => ⟨1, Subtype.ext (by simpa using hP.2 y y.2)⟩
  have hA2 : IsPGroup 2 A := fun y => ⟨1, Subtype.ext (by simpa using hA.2 y y.2)⟩
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  rcases n with _ | n
  · exfalso
    rw [pow_zero] at hn
    have hPbot : P = ⊥ := Subgroup.eq_bot_of_card_eq P hn
    have hAle : A ≤ A ⊓ Subgroup.centralizer (P : Set G) := by
      refine le_inf le_rfl ?_
      rw [hPbot]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_bot.mp hy]
      simp
    rw [hAP] at hAle
    exact hAne (le_bot_iff.mp hAle)
  rcases n with _ | n
  · rw [pow_one] at hn
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · rw [Subgroup.card_bot, one_mul, hn]
    · have htop : A ⊓ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = A := by
        apply inf_eq_left.mpr
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy1 : y = 1 := Subgroup.mem_bot.mp hy
        rw [hy1]
        simp
      rw [htop]
      exact hAne
  · have hEcard : p ^ 2 ≤ Nat.card P := by
      rw [hn]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    have hfaith : ¬ P ≤ Subgroup.centralizer (A : Set G) := by
      intro h
      have hACP : A ≤ Subgroup.centralizer (P : Set G) := (Subgroup.le_centralizer_iff).mp h
      have hAbot : A ≤ ⊥ := by rw [← hAP]; exact le_inf le_rfl hACP
      exact hAne (le_bot_iff.mp hAbot)
    have hrQ : ¬ p ∣ Nat.card A :=
      CFSG.GroupTheory.not_dvd_card_of_isPGroup (G := ↥A) (p := 2) (q := p) hA2
        (Fact.out : p.Prime) hp2
    obtain ⟨Y, hYP, hYcard, hYfaith⟩ :=
      CFSG.GroupTheory.exists_hyperplane_not_le_centralizer_inf_centralizer
        (r := p) (E := P) (Q := A) hP hEcard hPA hrQ hfaith
    refine ⟨Y, hYP, hYcard, ?_⟩
    intro hbot
    apply hYfaith
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by
      have hy' : y ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact hy
      exact Subgroup.mem_bot.mp hy'
    rw [hy1]
    simp

theorem sup_eq_of_card_mul_eq_of_ne {p : ℕ} [Fact p.Prime] {P B₁ B₂ : Subgroup G}
    (hB₁ : B₁ ≤ P) (hB₂ : B₂ ≤ P) (h₁ : Nat.card B₁ * p = Nat.card P)
    (h₂ : Nat.card B₂ * p = Nat.card P) (hne : B₁ ≠ B₂) : B₁ ⊔ B₂ = P := by
  classical
  have hle : B₁ ⊔ B₂ ≤ P := sup_le hB₁ hB₂
  rcases seven_nine_mod_eq_or_top le_sup_left hle h₁ with h | h
  · exfalso
    have hB2le : B₂ ≤ B₁ := by
      rw [← h]
      exact le_sup_right
    have hcard : Nat.card B₁ = Nat.card B₂ :=
      Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos (h₁.trans h₂.symm)
    exact hne (Subgroup.eq_of_le_of_card_ge hB2le (le_of_eq hcard)).symm
  · exact h

end CFSG.LocalAnalysis.WeakClosure81
