module

public import CFSG.RankThree.PartTwo.Sec3.ThompsonParabolic

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup Sec3

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def pJ1412 (T P : Subgroup G) (j : ℕ) : Subgroup G :=
  sSup {A | A ∈ famG T j ∧ A ≤ P}

omit [Finite G] in
theorem pJ1412_le (T P : Subgroup G) (j : ℕ) : pJ1412 T P j ≤ P := sSup_le fun _ h => h.2

omit [Finite G] in
theorem pJ1412_le_jG (T P : Subgroup G) (j : ℕ) : pJ1412 T P j ≤ jG T j :=
  sSup_le fun _ h => le_jG h.1

omit [Finite G] in
theorem le_pJ1412 {T P A : Subgroup G} {j : ℕ} (h : A ∈ famG T j) (hP : A ≤ P) :
    A ≤ pJ1412 T P j :=
  le_sSup ⟨h, hP⟩

omit [Finite G] in
theorem conj_mem_pJ1412 {T P : Subgroup G} {j : ℕ} (hPT : P ≤ T) {g : G}
    (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) {x : G} (hx : x ∈ pJ1412 T P j) :
    g * x * g⁻¹ ∈ pJ1412 T P j := by
  have hle : (pJ1412 T P j).map (MulAut.conj g).toMonoidHom ≤ pJ1412 T P j := by
    rw [pJ1412, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    refine iSup₂_le fun A hA => le_sSup ⟨map_conj_mem_famG hA.1 g
      (fun a ha => hPT (hgP a (hA.2 ha))), ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hgP a (hA.2 ha)
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_mem_omegaG_pJ1412 {T P : Subgroup G} {j : ℕ} (hPT : P ≤ T) {g : G}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hg' : ∀ p ∈ P, g⁻¹ * p * g ∈ P) {w : G}
    (hw : w ∈ omegaG (pJ1412 T P j)) : g * w * g⁻¹ ∈ omegaG (pJ1412 T P j) :=
  conj_mem_omegaG (fun x hx => conj_mem_pJ1412 hPT hg hx)
    (fun x hx => by
      have := conj_mem_pJ1412 hPT (g := g⁻¹) (fun p hp => by rw [inv_inv]; exact hg' p hp) hx
      rwa [inv_inv] at this) hw

theorem mem_omegaG_pJ1412 {T P A : Subgroup G} {j : ℕ} (hr : j + 1 ≤ CFSG.pRank 2 T)
    (hA : A ∈ famG T j) (hAP : A ≤ P) (hPT : P ≤ T) {e : G} (he : e ∈ omegaG (jG T j))
    (heP : e ∈ P) : e ∈ omegaG (pJ1412 T P j) := by
  obtain ⟨heJ, hec, he2⟩ := he
  refine ⟨?_, fun x hx => hec x (pJ1412_le_jG T P j hx), he2⟩
  by_cases heA : e ∈ A
  · exact le_pJ1412 hA hAP heA
  obtain ⟨hAT, hA2, hAcard⟩ := hA
  have hpow : 2 ^ (CFSG.pRank 2 T - j - 1) ∣ Nat.card A := by
    rw [hAcard]
    exact Nat.pow_dvd_pow 2 (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hpow
  set K := K'.map A.subtype with hKdef
  have hKA : K ≤ A := Subgroup.map_subtype_le K'
  have hKcard : Nat.card K = 2 ^ (CFSG.pRank 2 T - j - 1) := by
    rw [hKdef, Subgroup.card_map_of_injective A.subtype_injective, hK']
  have he1 : e ≠ 1 := fun h => heA (h ▸ A.one_mem)
  have hzp : Nat.card (Subgroup.zpowers e) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact he2) he1
  have hcomm : ∀ k ∈ K, ∀ l ∈ Subgroup.zpowers e, k * l = l * k := by
    intro k hk l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    exact ((Commute.zpow_left (hec k (le_jG ⟨hAT, hA2, hAcard⟩ (hKA hk))) n).symm).eq
  have hinf : K ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxe⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [Subgroup.mem_bot]
    have he2' : e ^ 2 = 1 := by rw [pow_two]; exact he2
    have hmod : e ^ n = e ^ (n % (2 : ℕ)) := zpow_eq_zpow_emod' n he2'
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · exfalso
      apply heA
      have : e ^ n = e := by
        rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
      rw [← this]
      exact hKA hxK
  have hDcard : Nat.card ↥(K ⊔ Subgroup.zpowers e) = 2 ^ (CFSG.pRank 2 T - j) := by
    have h := card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one, hKcard, hzp] at h
    rw [h, ← pow_succ]
    congr 1
    omega
  have hD : K ⊔ Subgroup.zpowers e ∈ famG T j := by
    refine ⟨sup_le (hKA.trans hAT) ((Subgroup.zpowers_le).mpr (hPT heP)), ?_, hDcard⟩
    refine isElemTwo_sup ⟨fun a ha b hb => hA2.1 a (hKA ha) b (hKA hb),
      fun a ha => hA2.2 a (hKA ha)⟩ ⟨fun a ha b hb => ?_, fun a ha => ?_⟩ hcomm
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_add, ← two_mul, zpow_mul, show e ^ (2 : ℤ) = 1 by
        rw [zpow_two]; exact he2, one_zpow]
  have hDP : K ⊔ Subgroup.zpowers e ≤ P :=
    sup_le (hKA.trans hAP) ((Subgroup.zpowers_le).mpr heP)
  exact le_pJ1412 hD hDP (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))

section Parabolic

variable {T Q H P A : Subgroup G} {j : ℕ}
  (hQP : Q ≤ P) (hPT : P ≤ T) (hP2 : IsPGroup 2 P) (hQ2 : IsPGroup 2 Q)
  (hCQ : centralizer (Q : Set G) ≤ Q) (hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P)
  (hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K →
    K ≤ P)
  (hEH : omegaG (jG T j) ≤ H)
  (hEn : ∀ t ∈ T, ∀ e ∈ omegaG (jG T j), t * e * t⁻¹ ∈ omegaG (jG T j))
  (hr : j + 1 ≤ CFSG.pRank 2 T) (hA : A ∈ famG T j) (hAP : A ≤ P)

include hQP hPT hP2 hQ2 hCQ hHP hO2 hEH hEn hr hA hAP in
theorem omegaG_jG_le_of_pJ1412 : omegaG (jG T j) ≤ P := by
  intro e he
  have hHW : ∀ h ∈ H, ∀ w ∈ omegaG (pJ1412 T P j), h * w * h⁻¹ ∈ omegaG (pJ1412 T P j) :=
    fun h hh w hw => conj_mem_omegaG_pJ1412 hPT (hHP h hh)
      (fun p hp => by
        have := hHP h⁻¹ (H.inv_mem hh) p hp
        rwa [inv_inv] at this) hw
  refine mem_of_stabilizes hP2 ((omegaG_le _).trans (pJ1412_le T P j)) hQP hCQ hQ2 hHP hHW hO2
    (hEH he) (fun w hw => ?_) (fun p hp => ?_)
  · have := he.2.1 w (pJ1412_le_jG T P j (omegaG_le _ hw))
    rw [this, mul_inv_cancel_right]
  · have hcE : e * p * e⁻¹ * p⁻¹ ∈ omegaG (jG T j) := by
      have h1 : p * e⁻¹ * p⁻¹ ∈ omegaG (jG T j) :=
        hEn p (hPT hp) e⁻¹ ((omegaG (jG T j)).inv_mem he)
      have : e * p * e⁻¹ * p⁻¹ = e * (p * e⁻¹ * p⁻¹) := by group
      rw [this]
      exact (omegaG (jG T j)).mul_mem he h1
    have hcP : e * p * e⁻¹ * p⁻¹ ∈ P := P.mul_mem (hHP e (hEH he) p hp) (P.inv_mem hp)
    exact mem_omegaG_pJ1412 hr hA hAP hPT hcE hcP

include hQP hPT hP2 hQ2 hCQ hHP hO2 hEH hEn hr hA hAP in
theorem omegaG_jG_le_omegaG_pJ1412 : omegaG (jG T j) ≤ omegaG (pJ1412 T P j) :=
  fun _ he => mem_omegaG_pJ1412 hr hA hAP hPT he
    (omegaG_jG_le_of_pJ1412 hQP hPT hP2 hQ2 hCQ hHP hO2 hEH hEn hr hA hAP he)

end Parabolic

theorem relIndex_centralizer_le_pow_pJ1412 {T P A : Subgroup G} {j : ℕ} (hPT : P ≤ T)
    (hA : A ∈ famG T 0) (hAP : A ⊓ P ∈ famG T j) {t : G} (htA : t ∈ A) :
    (centralizer ({t} : Set G)).relIndex (omegaG (pJ1412 T P j)) ≤ 2 ^ j := by
  set W := omegaG (pJ1412 T P j) with hWdef
  have hAPle : A ⊓ P ≤ pJ1412 T P j := le_pJ1412 hAP inf_le_right
  have hcomm : ∀ a ∈ A ⊓ P, ∀ w ∈ W, a * w = w * a := fun a ha w hw =>
    (hw.2.1 a (hAPle ha)).symm
  have hD := card_sup_mul_card_inf_of_commute hcomm
  have hDel : IsElemTwo ((A ⊓ P) ⊔ W) := isElemTwo_sup hAP.2.1 (isElemTwo_omegaG _) hcomm
  have hDT : (A ⊓ P) ⊔ W ≤ T :=
    sup_le (inf_le_left.trans hA.1) ((omegaG_le _).trans ((pJ1412_le T P j).trans hPT))
  have hle := card_le_two_pow_pRank hDT hDel
  rw [hAP.2.2] at hD
  have h2 : 2 ^ CFSG.pRank 2 T ≤ 2 ^ j * 2 ^ (CFSG.pRank 2 T - j) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : Nat.card W ≤ 2 ^ j * Nat.card ↥((A ⊓ P) ⊓ W) := by
    have hpos : 0 < 2 ^ (CFSG.pRank 2 T - j) := by positivity
    have : 2 ^ (CFSG.pRank 2 T - j) * Nat.card W ≤
        2 ^ (CFSG.pRank 2 T - j) * (2 ^ j * Nat.card ↥((A ⊓ P) ⊓ W)) := by
      rw [← hD]
      calc Nat.card ↥((A ⊓ P) ⊔ W) * Nat.card ↥((A ⊓ P) ⊓ W)
          ≤ 2 ^ j * 2 ^ (CFSG.pRank 2 T - j) * Nat.card ↥((A ⊓ P) ⊓ W) :=
            Nat.mul_le_mul_right _ (hle.trans h2)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hpos
  have hrel : (A ⊓ P).relIndex W ≤ 2 ^ j := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ P) (K := W)
    have hpos : 0 < Nat.card ↥((A ⊓ P) ⊓ W) := Nat.card_pos
    have : (A ⊓ P).relIndex W * Nat.card ↥((A ⊓ P) ⊓ W) ≤
        2 ^ j * Nat.card ↥((A ⊓ P) ⊓ W) := by
      rw [h]; exact hW
    exact Nat.le_of_mul_le_mul_right this hpos
  have hcent : A ⊓ P ≤ centralizer ({t} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hA.2.1.1 a ha.1 t htA
  exact (Subgroup.relIndex_le_of_le_left hcent (relIndex_ne_zero_of_finite _ _)).trans hrel

theorem sup_mem_famG_zero_of_pJ1412 {T P A I : Subgroup G} {j : ℕ} (hPT : P ≤ T)
    (hj : j ≤ CFSG.pRank 2 T) (hA : A ∈ famG T 0) (hAP : A ⊓ P ∈ famG T j)
    (hIW : I ≤ omegaG (pJ1412 T P j)) (hI : 2 ^ j ≤ (centralizer (A : Set G)).relIndex I) :
    (A ⊓ P) ⊔ I ∈ famG T 0 := by
  set W := omegaG (pJ1412 T P j) with hWdef
  have hAPle : A ⊓ P ≤ pJ1412 T P j := le_pJ1412 hAP inf_le_right
  have hcomm : ∀ a ∈ A ⊓ P, ∀ w ∈ I, a * w = w * a := fun a ha w hw =>
    ((hIW hw).2.1 a (hAPle ha)).symm
  have hIel : IsElemTwo I := ⟨fun a ha b hb => (isElemTwo_omegaG _).1 a (hIW ha) b (hIW hb),
    fun a ha => (isElemTwo_omegaG _).2 a (hIW ha)⟩
  have hDel : IsElemTwo ((A ⊓ P) ⊔ I) := isElemTwo_sup hAP.2.1 hIel hcomm
  have hDT : (A ⊓ P) ⊔ I ≤ T :=
    sup_le (inf_le_left.trans hA.1)
      (hIW.trans ((omegaG_le _).trans ((pJ1412_le T P j).trans hPT)))
  have hle := card_le_two_pow_pRank hDT hDel
  have hD := card_sup_mul_card_inf_of_commute hcomm
  rw [hAP.2.2] at hD
  have hBI : (A ⊓ P) ⊓ I ≤ centralizer (A : Set G) ⊓ I := by
    rintro x ⟨⟨hxA, -⟩, hxI⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun a ha => hA.2.1.1 a ha x hxA, hxI⟩
  have hcardBI : Nat.card ↥((A ⊓ P) ⊓ I) ≤ Nat.card ↥(centralizer (A : Set G) ⊓ I) :=
    Subgroup.card_le_of_le hBI
  have hrelI : (centralizer (A : Set G)).relIndex I * Nat.card ↥(centralizer (A : Set G) ⊓ I) =
      Nat.card I :=
    Subgroup.relIndex_mul_card (H := centralizer (A : Set G)) (K := I)
  have hge : 2 ^ CFSG.pRank 2 T ≤ Nat.card ↥((A ⊓ P) ⊔ I) := by
    have hpos : 0 < Nat.card ↥((A ⊓ P) ⊓ I) := Nat.card_pos
    have h1 : 2 ^ CFSG.pRank 2 T * Nat.card ↥((A ⊓ P) ⊓ I) ≤
        Nat.card ↥((A ⊓ P) ⊔ I) * Nat.card ↥((A ⊓ P) ⊓ I) := by
      rw [hD, show 2 ^ CFSG.pRank 2 T = 2 ^ (CFSG.pRank 2 T - j) * 2 ^ j by
        rw [← pow_add]; congr 1; omega, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      calc 2 ^ j * Nat.card ↥((A ⊓ P) ⊓ I)
          ≤ (centralizer (A : Set G)).relIndex I * Nat.card ↥(centralizer (A : Set G) ⊓ I) :=
            Nat.mul_le_mul hI hcardBI
        _ = Nat.card I := hrelI
    exact Nat.le_of_mul_le_mul_right h1 hpos
  refine ⟨hDT, hDel, ?_⟩
  rw [Nat.sub_zero]
  exact le_antisymm hle hge

end CFSG.RankThree.PartTwo.Sec20
