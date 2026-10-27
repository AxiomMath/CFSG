module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackLocal
public import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRadius
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.Timmesfeld.RankOne.Basic
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem Zv_add_two_le_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ : ℕ} (hb₀ : 1 ≤ b₀)
    (h₀ : t.IsFixRadius ε b₀) :
    t.Zv (ε + 2) ≤ pCoreOf 2 (t.Gw (ε + b₀ + 1) (ε + b₀ + 2)) := by
  have h0' : t.IsFixRadius (ε + 2) b₀ := by
    have h := IsFixRadius.shift t h₀ 1
    rwa [show ε + 2 * (1 : ℤ) = ε + 2 by ring] at h
  refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv _) ?_
  have h := h0'.le_Gw
  refine h.trans (win_mono (a := (ε + 2) - (b₀ : ℤ)) (b := (ε + 2) + (b₀ : ℤ))
    (a' := ε + b₀ + 1) (b' := ε + b₀ + 2) ?_ ?_)
  · push_cast; omega
  · push_cast; omega

private theorem Zv_two_mul_le_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ b : ℕ} (hb : b = b₀ + 1) (hb2 : 2 ≤ b)
    (h₀ : t.IsFixRadius ε b₀) :
    t.Zv (ε + 2 * b) ≤ pCoreOf 2 (t.Gw (ε + 1 + b) (ε + 2 + b)) := by
  have h0' : t.IsFixRadius (ε + 2 * b) b₀ := by
    have h := IsFixRadius.shift t h₀ (b : ℤ)
    rwa [show ε + 2 * (b : ℤ) = ε + 2 * b by ring] at h
  refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv _) ?_
  have h := h0'.le_Gw
  refine h.trans (win_mono (a := (ε + 2 * (b : ℤ)) - (b₀ : ℤ))
    (b := (ε + 2 * (b : ℤ)) + (b₀ : ℤ)) (a' := ε + 1 + b) (b' := ε + 2 + b) ?_ ?_)
  · push_cast; omega
  · push_cast; omega

private theorem Lv_le_sup_Zv_pair
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ b : ℕ} (hb : b = b₀ + 1)
    (hb₀ : 1 ≤ b₀) (hb2 : 2 ≤ b) (h₀ : t.IsFixRadius ε b₀) :
    t.Lv (ε + 1 + b) ≤ (t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b)) ⊔ t.Qv (ε + 1 + b) := by
  let A : Subgroup G := t.Zv (ε + 2)
  let B : Subgroup G := t.Zv (ε + 2 * b)
  let E : Subgroup G := A ⊔ B
  let c : ℤ := ε + 1 + b
  have hA : A ≤ pCoreOf 2 (t.Gw (c - 1) c) := by
    have h := Zv_add_two_le_pCoreOf t hfr hb₀ h₀
    dsimp only [A, c]
    rw [show ε + 1 + b - 1 = ε + b₀ + 1 by omega,
      show ε + 1 + b = ε + b₀ + 2 by omega]
    exact h
  have hB : B ≤ pCoreOf 2 (t.Gw c (c + 1)) := by
    have h := Zv_two_mul_le_pCoreOf t hfr hb hb2 h₀
    dsimp only [B, c]
    rw [show ε + 1 + b + 1 = ε + 2 + b by omega]
    exact h
  have hAK : t.K ≤ normalizer (A : Set G) :=
    (t.K_le_Gv (ε + 2)).trans (t.Gv_le_normalizer_Zv (ε + 2))
  have hBK : t.K ≤ normalizer (B : Set G) :=
    (t.K_le_Gv (ε + 2 * b)).trans (t.Gv_le_normalizer_Zv (ε + 2 * b))
  have hA0 : t.IsFixRadius (ε + 2) b₀ := by
    have h := IsFixRadius.shift t h₀ 1
    rwa [show ε + 2 * (1 : ℤ) = ε + 2 by ring] at h
  have hAQ : ¬ A ≤ t.Qv c := by
    intro hle
    have h := hle.trans (t.Qv_le_Gv hfr c).2
    refine hA0.not_le_Gv ?_
    dsimp only [A, c] at h ⊢
    convert h using 2 <;> omega
  have hB0 : t.IsFixRadius (ε + 2 * b) b₀ := by
    have h := IsFixRadius.shift t h₀ (b : ℤ)
    rwa [show ε + 2 * (b : ℤ) = ε + 2 * b by ring] at h
  have hBQ : ¬ B ≤ t.Qv c := by
    intro hle
    have h := hle.trans (t.Qv_le_Gv hfr c).1
    refine IsFixRadius.not_le_Gv_sub t hB0 ?_
    dsimp only [B, c] at h ⊢
    convert h using 2 <;> omega
  have hAGv : A ≤ t.Gv c :=
    (hA.trans (pCoreOf_le 2 _)).trans
      (win_le_qv (a := c - 1) (b := c) (i := c) (by omega) le_rfl)
  have hBGv : B ≤ t.Gv c :=
    (hB.trans (pCoreOf_le 2 _)).trans
      (win_le_qv (a := c) (b := c + 1) (i := c) le_rfl (by omega))
  have hELv : E ≤ t.Lv c :=
    sup_le (t.le_Lv hfr (t.isPGroup_Zv _) hAGv) (t.le_Lv hfr (t.isPGroup_Zv _) hBGv)
  have h1 : ∀ x ∈ pCoreOf 2 (t.Gw c (c + 1)), x ^ 2 ∈ t.Qv c → x ∈ E ⊔ t.Qv c := by
    intro x hx hx2
    have h := t.mem_sup_Qv_of_le_pCoreOf hfr c hB hBK hBQ hx hx2
    exact (sup_le_sup_right (le_sup_right : B ≤ E) (t.Qv c)) h
  have h2 : ∀ x ∈ pCoreOf 2 (t.Gw (c - 1) c), x ^ 2 ∈ t.Qv c → x ∈ E ⊔ t.Qv c := by
    intro x hx hx2
    have h := t.mem_sup_Qv_of_le_pCoreOf_left hfr c hA hAK hAQ hx hx2
    exact (sup_le_sup_right (le_sup_left : A ≤ E) (t.Qv c)) h
  have h := t.Lv_le_sup hfr c h1 h2
  dsimp only [E, A, B, c] at h ⊢
  exact h

private theorem sup_Zv_pair_le_Lv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ b : ℕ} (hb : b = b₀ + 1)
    (hb₀ : 1 ≤ b₀) (hb2 : 2 ≤ b) (h₀ : t.IsFixRadius ε b₀) :
    t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b) ≤ t.Lv (ε + 1 + b) := by
  let A : Subgroup G := t.Zv (ε + 2)
  let B : Subgroup G := t.Zv (ε + 2 * b)
  let c : ℤ := ε + 1 + b
  have hA : A ≤ pCoreOf 2 (t.Gw (c - 1) c) := by
    have h := Zv_add_two_le_pCoreOf t hfr hb₀ h₀
    dsimp only [A, c]
    rw [show ε + 1 + b - 1 = ε + b₀ + 1 by omega,
      show ε + 1 + b = ε + b₀ + 2 by omega]
    exact h
  have hB : B ≤ pCoreOf 2 (t.Gw c (c + 1)) := by
    have h := Zv_two_mul_le_pCoreOf t hfr hb hb2 h₀
    dsimp only [B, c]
    rw [show ε + 1 + b + 1 = ε + 2 + b by omega]
    exact h
  have hAGv : A ≤ t.Gv c :=
    (hA.trans (pCoreOf_le 2 _)).trans
      (win_le_qv (a := c - 1) (b := c) (i := c) (by omega) le_rfl)
  have hBGv : B ≤ t.Gv c :=
    (hB.trans (pCoreOf_le 2 _)).trans
      (win_le_qv (a := c) (b := c + 1) (i := c) le_rfl (by omega))
  have h := sup_le (t.le_Lv hfr (t.isPGroup_Zv _) hAGv)
    (t.le_Lv hfr (t.isPGroup_Zv _) hBGv)
  dsimp only [A, B, c] at h ⊢
  exact h

private theorem pCoreOf_le_centralizer_Zv_pair
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {n b : ℕ}
    (h : t.IsMaxArc ε n) (hn : n = 2 * b + 2) (hb2 : 2 ≤ b) :
    pCoreOf 2 (t.Gw ε (ε + n)) ≤
      centralizer (((t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b)) : Subgroup G) : Set G) := by
  have hQ : pCoreOf 2 (t.Gw ε (ε + n)) ≤ t.Gw ε (ε + n) := pCoreOf_le 2 _
  have hQ2 : pCoreOf 2 (t.Gw ε (ε + n)) ≤ t.Qv (ε + 2) :=
    t.le_Qv_of_le_Gw hfr (show ε < ε + 2 by omega) (show ε + 2 < ε + n by omega)
      (pCoreOf_isPGroup 2 _) hQ
  have hQ2b : pCoreOf 2 (t.Gw ε (ε + n)) ≤ t.Qv (ε + 2 * b) :=
    t.le_Qv_of_le_Gw hfr (show ε < ε + 2 * b by omega) (show ε + 2 * b < ε + n by omega)
      (pCoreOf_isPGroup 2 _) hQ
  have hAcent : pCoreOf 2 (t.Gw ε (ε + n)) ≤ centralizer (t.Zv (ε + 2) : Set G) :=
    hQ2.trans (Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer (ε + 2)))
  have hBcent : pCoreOf 2 (t.Gw ε (ε + n)) ≤ centralizer (t.Zv (ε + 2 * b) : Set G) :=
    hQ2b.trans (Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer (ε + 2 * b)))
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  intro q hq x hx
  rcases hx with hxA | hxB
  · exact (Subgroup.mem_centralizer_iff.mp (hAcent hq)) x hxA
  · exact (Subgroup.mem_centralizer_iff.mp (hBcent hq)) x hxB

private theorem relIndex_Lv_sup_Zv_pair_pow_two
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ b : ℕ}
    (hb : b = b₀ + 1) (hb₀ : 1 ≤ b₀) (hb2 : 2 ≤ b) (h₀ : t.IsFixRadius ε b₀) :
    ∃ j, (t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b)).relIndex (t.Lv (ε + 1 + b)) = 2 ^ j := by
  let A : Subgroup G := t.Zv (ε + 2)
  let B : Subgroup G := t.Zv (ε + 2 * b)
  let E : Subgroup G := A ⊔ B
  let c : ℤ := ε + 1 + b
  have hELv : E ≤ t.Lv c := by
    have h := sup_Zv_pair_le_Lv t hfr hb hb₀ hb2 h₀
    dsimp only [E, A, B, c] at h ⊢
    exact h
  have hQvLv : t.Qv c ≤ t.Lv c := t.le_Lv hfr (t.isPGroup_Qv c) (t.Qv_le_Gv_self c)
  have hLv_le : t.Lv c ≤ E ⊔ t.Qv c := by
    have h := Lv_le_sup_Zv_pair t hfr hb hb₀ hb2 h₀
    dsimp only [E, A, B, c] at h ⊢
    exact h
  have hLvEq : t.Lv c = E ⊔ t.Qv c :=
    le_antisymm hLv_le (sup_le hELv hQvLv)
  have hEcN : E ≤ normalizer (t.Qv c : Set G) :=
    hELv.trans ((t.Lv_le_Gv c).trans (t.Gv_le_normalizer_Qv c))
  have hrel : E.relIndex (t.Lv c) = (E ⊓ t.Qv c).relIndex (t.Qv c) := by
    rw [hLvEq]
    exact (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hEcN).1
  have hdvd : E.relIndex (t.Lv c) ∣ Nat.card (t.Qv c) := by
    rw [hrel]
    exact Subgroup.relIndex_dvd_card (E ⊓ t.Qv c) (t.Qv c)
  obtain ⟨m, hm⟩ := (t.isPGroup_Qv c).exists_card_eq
  have hdvd' : E.relIndex (t.Lv c) ∣ 2 ^ m := by rwa [hm] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  exact ⟨j, by dsimp only [E, A, B, c] at hj ⊢; exact hj⟩

private theorem Kc_le_sup_Zv_pair
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ b : ℕ} (hb : b = b₀ + 1)
    (hb₀ : 1 ≤ b₀) (hb2 : 2 ≤ b) (h₀ : t.IsFixRadius ε b₀) :
    t.K ⊓ t.Lv (ε + 1 + b) ≤ t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b) := by
  obtain ⟨j, hpow⟩ := relIndex_Lv_sup_Zv_pair_pow_two t hfr hb hb₀ hb2 h₀
  let A : Subgroup G := t.Zv (ε + 2)
  let B : Subgroup G := t.Zv (ε + 2 * b)
  let E : Subgroup G := A ⊔ B
  let c : ℤ := ε + 1 + b
  let Kc : Subgroup G := t.K ⊓ t.Lv c
  have hAK : t.K ≤ normalizer (A : Set G) :=
    (t.K_le_Gv (ε + 2)).trans (t.Gv_le_normalizer_Zv (ε + 2))
  have hBK : t.K ≤ normalizer (B : Set G) :=
    (t.K_le_Gv (ε + 2 * b)).trans (t.Gv_le_normalizer_Zv (ε + 2 * b))
  have hKcE : Kc ≤ normalizer (E : Set G) := by
    intro k hk
    have hkK : k ∈ t.K := hk.1
    exact Subgroup.inf_normalizer_le_normalizer_sup A B ⟨hAK hkK, hBK hkK⟩
  have hELv : E ≤ t.Lv c := by
    have h := sup_Zv_pair_le_Lv t hfr hb hb₀ hb2 h₀
    dsimp only [E, A, B, c] at h ⊢
    exact h
  have hoddKc : Odd (Nat.card Kc) :=
    Odd.of_dvd_nat t.hHall.2.1 (Subgroup.card_dvd_of_le (inf_le_left : Kc ≤ t.K))
  have hodd : Odd (E.relIndex (Kc ⊔ E)) := by
    rw [CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hKcE,
      ← Subgroup.inf_relIndex_right E Kc]
    exact Odd.of_dvd_nat hoddKc (Subgroup.relIndex_dvd_card (E ⊓ Kc) Kc)
  have hKcLv : Kc ≤ t.Lv c := inf_le_right
  have hmul : E.relIndex (Kc ⊔ E) * (Kc ⊔ E).relIndex (t.Lv c) = E.relIndex (t.Lv c) :=
    Subgroup.relIndex_mul_relIndex (H := E) (K := Kc ⊔ E) (L := t.Lv c)
      le_sup_right (sup_le hKcLv hELv)
  have hdvd2 : E.relIndex (Kc ⊔ E) ∣ E.relIndex (t.Lv c) := ⟨_, hmul.symm⟩
  have hone : E.relIndex (Kc ⊔ E) = 1 := by
    have hdvd2' : E.relIndex (Kc ⊔ E) ∣ 2 ^ j := by rwa [hpow] at hdvd2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2'
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simpa using hi
    · exfalso
      obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      rw [pow_succ] at hi
      exact (Nat.not_even_iff_odd.mpr hodd) (by rw [hi, mul_comm]; exact even_two_mul (2 ^ i'))
  have hKcE' : Kc ≤ E := (le_sup_left : Kc ≤ Kc ⊔ E).trans (Subgroup.relIndex_eq_one.mp hone)
  dsimp only [Kc, E, A, B, c] at hKcE' ⊢
  exact hKcE'


private theorem Lv_le_sup_normalizer_zpowers
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {v : ℤ} {k : G}
    (hkK : k ∈ t.K) (hodd : Odd (orderOf k))
    (hcent : ∀ l ∈ t.Lv v, ⁅k, l⁆ ∈ t.Qv v) :
    t.Lv v ≤ (t.Gv v ⊓ normalizer ((Subgroup.zpowers k : Subgroup G) : Set G)) ⊔ t.Qv v := by
  intro l hl
  have hkQ : k ∈ normalizer (t.Qv v : Set G) :=
    (t.K_le_Gv v).trans (t.Gv_le_normalizer_Qv v) hkK
  have hlQ : l ∈ normalizer (t.Qv v : Set G) :=
    (t.Gv_le_normalizer_Qv v) (t.Lv_le_Gv v hl)
  have hg : l⁻¹ * (k * l * k⁻¹) ∈ t.Qv v := by
    have hcomm := hcent l hl
    have heq : l⁻¹ * (k * l * k⁻¹) = l⁻¹ * ⁅k, l⁆ * l := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    have hlinv : l⁻¹ ∈ normalizer (t.Qv v : Set G) :=
      (Subgroup.normalizer (t.Qv v : Set G)).inv_mem hlQ
    have h := (Subgroup.mem_normalizer_iff.mp hlinv ⁅k, l⁆).mp hcomm
    simpa [mul_assoc] using h
  have hcop : Nat.Coprime (orderOf k) (Nat.card (t.Qv v)) := by
    obtain ⟨m, hm⟩ := (t.isPGroup_Qv v).exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  obtain ⟨n, hnQ, hfix⟩ := CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (t.Qv v)
    (f := k) (g := l) (fun x hx => (Subgroup.mem_normalizer_iff.mp hkQ x).mp hx) hg hcop
  have hlnGv : l * n ∈ t.Gv v := (t.Gv v).mul_mem (t.Lv_le_Gv v hl) (t.Qv_le_Gv_self v hnQ)
  have hcomm : (l * n) * k = k * (l * n) := by
    have h : k * (l * n) * k⁻¹ * k = (l * n) * k := by rw [hfix]
    simpa [mul_assoc] using h.symm
  have hlnN : l * n ∈ normalizer ((Subgroup.zpowers k : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hl_eq : l = (l * n) * n⁻¹ := by group
  rw [hl_eq]
  exact Subgroup.mul_mem_sup ⟨hlnGv, hlnN⟩ ((t.Qv v).inv_mem hnQ)

private theorem reflection_image_facts {w : ℤ} {X : Subgroup G} {y : G}
    (hyK : y ∈ normalizer (t.K : Set G))
    (hQv : (t.Qv w).map (MulAut.conj y).toMonoidHom = t.Qv w)
    (hZv : (t.Zv w).map (MulAut.conj y).toMonoidHom = t.Zv w)
    (hXK : t.K ≤ normalizer (X : Set G)) (hXQ : ¬ X ≤ t.Qv w)
    (hXZ : X ≤ centralizer (t.Zv w : Set G)) :
    t.K ≤ normalizer ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) ∧
      ¬ X.map (MulAut.conj y).toMonoidHom ≤ t.Qv w ∧
      X.map (MulAut.conj y).toMonoidHom ≤ centralizer (t.Zv w : Set G) := by
  have hKmap : t.K.map (MulAut.conj y).toMonoidHom = t.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyK
  refine ⟨?_, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hXK
    rwa [hKmap, Subgroup.map_equiv_normalizer_eq] at h
  · intro hle
    apply hXQ
    have h := Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hle
    rw [CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj X y,
      (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQv).symm] at h
    exact h
  · have hcomm := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXZ
    have hmap := congrArg (Subgroup.map (MulAut.conj y).toMonoidHom) hcomm
    rw [Subgroup.map_commutator, Subgroup.map_bot, hZv] at hmap
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmap

theorem IsFixRadius.Lv_add_le_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {u : ℤ} {d : ℕ}
    (hd : t.IsFixRadius u d) (hcomm : ⁅t.Zv u, t.Zv (u + d)⁆ = ⊥) :
    t.Lv (u + d) ≤ centralizer (t.Zv (u + d) : Set G) := by
  have hd1 : 1 ≤ d := IsFixRadius.one_le t hfr hd
  have hX : t.Zv u ≤ pCoreOf 2 (t.Gw ((u + d) - 1) (u + d)) := by
    refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv u) ?_
    refine hd.le_Gw.trans (win_mono (a := u - d) (b := u + d)
      (a' := (u + d) - 1) (b' := u + d) ?_ ?_)
    · push_cast; omega
    · push_cast; omega
  have hXK : t.K ≤ normalizer (t.Zv u : Set G) :=
    (t.K_le_Gv u).trans (t.Gv_le_normalizer_Zv u)
  have hXQ : ¬ t.Zv u ≤ t.Qv (u + d) := by
    intro hle
    exact hd.not_le_Gv (hle.trans (t.Qv_le_Gv hfr (u + d)).2)
  have hXZ : t.Zv u ≤ centralizer (t.Zv (u + d) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨y, -, hyK, hGw, hQv, hZv⟩ := t.exists_reflection (u + d)
  have hYw : (t.Zv u).map (MulAut.conj y).toMonoidHom ≤
      pCoreOf 2 (t.Gw (u + d) ((u + d) + 1)) := by
    have hmap : (t.Gw ((u + d) - 1) (u + d)).map (MulAut.conj y).toMonoidHom =
        t.Gw (u + d) ((u + d) + 1) := by
      have h := hGw ((u + d) - 1) (u + d)
      rw [show 2 * (u + d) - (u + d) = u + d by ring,
        show 2 * (u + d) - ((u + d) - 1) = (u + d) + 1 by ring] at h
      exact h
    rw [← hmap, pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hX
  have hQfix : (t.Qv (u + d)).map (MulAut.conj y).toMonoidHom = t.Qv (u + d) := by
    have h := hQv (u + d)
    rwa [show 2 * (u + d) - (u + d) = u + d by ring] at h
  have hZfix : (t.Zv (u + d)).map (MulAut.conj y).toMonoidHom = t.Zv (u + d) := by
    have h := hZv (u + d)
    rwa [show 2 * (u + d) - (u + d) = u + d by ring] at h
  obtain ⟨hYK, hYQ, hYZ⟩ := reflection_image_facts t hyK hQfix hZfix hXK hXQ hXZ
  have hQZ : t.Qv (u + d) ≤ centralizer (t.Zv (u + d) : Set G) :=
    Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer (u + d))
  exact t.Lv_le_centralizer_of_le_pCoreOf hfr (u + d) hYw hX hYK hXK hYQ hXQ hYZ hXZ hQZ

theorem IsFixRadius.Lv_sub_le_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {u : ℤ} {d : ℕ}
    (hd : t.IsFixRadius u d) (hcomm : ⁅t.Zv (u - d), t.Zv u⁆ = ⊥) :
    t.Lv (u - d) ≤ centralizer (t.Zv (u - d) : Set G) := by
  have hd1 : 1 ≤ d := IsFixRadius.one_le t hfr hd
  have hX : t.Zv u ≤ pCoreOf 2 (t.Gw (u - d) ((u - d) + 1)) := by
    refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv u) ?_
    refine hd.le_Gw.trans (win_mono (a := u - d) (b := u + d)
      (a' := u - d) (b' := (u - d) + 1) le_rfl ?_)
    push_cast; omega
  have hXK : t.K ≤ normalizer (t.Zv u : Set G) :=
    (t.K_le_Gv u).trans (t.Gv_le_normalizer_Zv u)
  have hXQ : ¬ t.Zv u ≤ t.Qv (u - d) := by
    intro hle
    exact IsFixRadius.not_le_Gv_sub t hd (hle.trans (t.Qv_le_Gv hfr (u - d)).1)
  have hXZ : t.Zv u ≤ centralizer (t.Zv (u - d) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hz) x hx).symm
  obtain ⟨y, -, hyK, hGw, hQv, hZv⟩ := t.exists_reflection (u - d)
  have hYw : (t.Zv u).map (MulAut.conj y).toMonoidHom ≤
      pCoreOf 2 (t.Gw ((u - d) - 1) (u - d)) := by
    have hmap : (t.Gw (u - d) ((u - d) + 1)).map (MulAut.conj y).toMonoidHom =
        t.Gw ((u - d) - 1) (u - d) := by
      have h := hGw (u - d) ((u - d) + 1)
      rw [show 2 * (u - d) - ((u - d) + 1) = (u - d) - 1 by ring,
        show 2 * (u - d) - (u - d) = u - d by ring] at h
      exact h
    rw [← hmap, pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hX
  have hQfix : (t.Qv (u - d)).map (MulAut.conj y).toMonoidHom = t.Qv (u - d) := by
    have h := hQv (u - d)
    rwa [show 2 * (u - d) - (u - d) = u - d by ring] at h
  have hZfix : (t.Zv (u - d)).map (MulAut.conj y).toMonoidHom = t.Zv (u - d) := by
    have h := hZv (u - d)
    rwa [show 2 * (u - d) - (u - d) = u - d by ring] at h
  obtain ⟨hYK, hYQ, hYZ⟩ := reflection_image_facts t hyK hQfix hZfix hXK hXQ hXZ
  have hQZ : t.Qv (u - d) ≤ centralizer (t.Zv (u - d) : Set G) :=
    Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer (u - d))
  exact t.Lv_le_centralizer_of_le_pCoreOf hfr (u - d) hX hYw hXK hYK hXQ hYQ hXZ hYZ hQZ

theorem IsFixRadius.Lv_le_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {v : ℤ} {b : ℕ}
    (hb : t.IsFixRadius v b) (heven : Even b)
    (hcomm : ⁅t.Zv v, t.Zv (v + b)⁆ = ⊥ ∨ ⁅t.Zv (v - b), t.Zv v⁆ = ⊥) :
    t.Lv v ≤ centralizer (t.Zv v : Set G) := by
  obtain ⟨k, hk⟩ := heven
  rcases hcomm with hcomm | hcomm
  · have hb' : t.IsFixRadius (v + b) b := by
      have h := IsFixRadius.shift t hb (k : ℤ)
      rwa [show v + 2 * (k : ℤ) = v + b by rw [hk]; push_cast; ring] at h
    have hcomm' : ⁅t.Zv ((v + b) - b), t.Zv (v + b)⁆ = ⊥ := by
      rwa [show v + b - (b : ℤ) = v by ring]
    have h := IsFixRadius.Lv_sub_le_centralizer t hfr hb' hcomm'
    rwa [show v + b - (b : ℤ) = v by ring] at h
  · have hb' : t.IsFixRadius (v - b) b := by
      have h := IsFixRadius.shift t hb (-(k : ℤ))
      rwa [show v + 2 * (-(k : ℤ)) = v - b by rw [hk]; push_cast; ring] at h
    have hcomm' : ⁅t.Zv (v - b), t.Zv ((v - b) + b)⁆ = ⊥ := by
      rwa [show v - b + (b : ℤ) = v by ring]
    have h := IsFixRadius.Lv_add_le_centralizer t hfr hb' hcomm'
    rwa [show v - b + (b : ℤ) = v by ring] at h

theorem IsFixRadius.Zv_le_and_lt
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ b₁ : ℕ} (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁) (heven : Even b₁)
    (hcomm : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥) : t.Zv (ε + 1) ≤ t.Zv ε ∧ b₀ < b₁ := by
  have hL : t.Lv (ε + 1) ≤ centralizer (t.Zv (ε + 1) : Set G) :=
    IsFixRadius.Lv_le_centralizer t hfr h₁ heven (Or.inl hcomm)
  have hZleZ : t.Zv (ε + 1) ≤ t.Zv ε :=
    t.Zv_le_of_Lv_le_centralizer hfr (u := ε + 1) (v := ε) (Or.inl (by ring)) hL
  refine ⟨hZleZ, ?_⟩
  by_contra hle
  have hb1le : b₁ ≤ b₀ := by omega
  have hleGv : t.Zv (ε + 1) ≤ t.Gv ((ε + 1) - (b₁ : ℤ) - 1) := by
    have h := hZleZ.trans (h₀.le_Gw.trans (win_mono (a := ε - (b₀ : ℤ))
      (b := ε + (b₀ : ℤ)) (a' := (ε + 1) - (b₁ : ℤ) - 1)
      (b' := (ε + 1) - (b₁ : ℤ) - 1) (by push_cast; omega) (by push_cast; omega)))
    rwa [win_self] at h
  exact IsFixRadius.not_le_Gv_sub t h₁ hleGv

theorem IsMaxArc.add_one {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {ε : ℤ} {n b₁ : ℕ} (h : t.IsMaxArc ε n) (h₁ : t.IsFixRadius (ε + 1) b₁) (heven : Even b₁)
    (hn : n = 2 * b₁) : t.IsMaxArc (ε + 1) n := by
  obtain ⟨k, hk⟩ := heven
  have h₁' : t.IsFixRadius (ε + 1 + b₁) b₁ := by
    have h := IsFixRadius.shift t h₁ (k : ℤ)
    rwa [show (ε + 1) + 2 * (k : ℤ) = ε + 1 + b₁ by rw [hk]; push_cast; ring] at h
  have hn2 : 2 ≤ n := IsMaxArc.two_le t hfr h
  refine ⟨?_, fun a b hab => h.pCoreOf_eq_bot a b hab⟩
  intro hbot
  have hZ : t.Zv (ε + 1 + b₁) ≤ t.Gw (ε + 1) (ε + 1 + n) := by
    refine h₁'.le_Gw.trans (win_mono ?_ ?_)
    · omega
    · omega
  have hX : t.Zv (ε + 1 + b₁) ≤ pCoreOf 2 (t.Gw (ε + 1) (ε + 1 + n)) :=
    t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv _) hZ
  exact t.Zv_ne_bot hfr.hF (ε + 1 + b₁) (le_bot_iff.mp (hX.trans_eq hbot))

private theorem commutator_mem_Qv_of_odd_succ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₁ : ℕ}
    (hb2 : 2 ≤ b₁) (h₁c : t.IsFixRadius (ε + 1 + b₁) b₁)
    {k : G} (hkK : k ∈ t.K)
    (hkZcent : k ∈ centralizer (t.Zv (ε + 1 + b₁) : Set G)) :
    ∀ l ∈ t.Lv (ε + 1), ⁅k, l⁆ ∈ t.Qv (ε + 1) := by
  have hZc_edge : t.Zv (ε + 1 + b₁) ≤ pCoreOf 2 (t.Gw (ε + 1) ((ε + 1) + 1)) := by
    have hZ : t.Zv (ε + 1 + b₁) ≤ t.Gw (ε + 1) (ε + 1 + 2 * b₁) := by
      have h := h₁c.le_Gw
      rwa [show (ε + 1 + b₁) - (b₁ : ℤ) = ε + 1 by ring,
        show (ε + 1 + b₁) + (b₁ : ℤ) = ε + 1 + 2 * b₁ by ring] at h
    have hZ' : t.Zv (ε + 1 + b₁) ≤ t.Gw (ε + 1) ((ε + 1) + 1) :=
      hZ.trans (win_mono (a := ε + 1) (b := ε + 1 + 2 * b₁) (a' := ε + 1)
        (b' := (ε + 1) + 1) le_rfl (by omega))
    exact t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv _) hZ'
  have hZc_K : t.K ≤ normalizer (t.Zv (ε + 1 + b₁) : Set G) :=
    (t.K_le_Gv (ε + 1 + b₁)).trans (t.Gv_le_normalizer_Zv (ε + 1 + b₁))
  have hZc_not : ¬ t.Zv (ε + 1 + b₁) ≤ t.Qv (ε + 1) := by
    intro hle
    refine IsFixRadius.not_le_Gv_sub t h₁c ?_
    have h := hle.trans (t.Qv_le_Gv hfr (ε + 1)).1
    rw [show (ε + 1 + b₁) - (b₁ : ℤ) - 1 = (ε + 1) - 1 by ring]
    exact h
  exact t.commutator_mem_Qv_of_mem_centralizer hfr (ε + 1) hZc_edge hZc_K hZc_not hkK hkZcent

private theorem eq_one_of_forall_commutator_mem_Qv
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {k : G}
    (hkK : k ∈ t.K) (hodd : Odd (orderOf k))
    (hε : ∀ l ∈ t.Lv ε, ⁅k, l⁆ ∈ t.Qv ε)
    (hε1 : ∀ l ∈ t.Lv (ε + 1), ⁅k, l⁆ ∈ t.Qv (ε + 1)) : k = 1 := by
  have h0 := Lv_le_sup_normalizer_zpowers t hfr (v := ε) hkK hodd hε
  have h1 := Lv_le_sup_normalizer_zpowers t hfr (v := ε + 1) hkK hodd hε1
  have hX : Subgroup.zpowers k ≤ t.Gw ε (ε + 1) :=
    Subgroup.zpowers_le.mpr ((t.K_le_Gw ε (ε + 1)) hkK)
  have hbot := t.eq_bot_of_le_Gw hfr ε hX h0 h1
  have hkmem : k ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.mem_zpowers k
  exact Subgroup.mem_bot.mp hkmem

theorem IsMaxArc.false_of_eq_two_mul_add_two
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {n b₀ b₁ : ℕ}
    (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁)
    (heven : Even b₁) (hcomm : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥)
    (hn : n = 2 * b₁ + 2) : False := by
  obtain ⟨k, hk⟩ := heven
  have heven : Even b₁ := ⟨k, hk⟩
  have hb1 : 1 ≤ b₁ := IsFixRadius.one_le t hfr h₁
  have hb2 : 2 ≤ b₁ := by omega
  have hZlt := IsFixRadius.Zv_le_and_lt t hfr h₀ h₁ heven hcomm
  have hb₀lt : b₀ < b₁ := hZlt.2
  have hArc : t.IsMaxArc ε (2 * (b₁ + 1)) := by
    rw [show 2 * (b₁ + 1) = n by omega]
    exact h
  have hself := IsMaxArc.fixRadius_self t hfr hArc h₀
  have hb₀eq : b₀ = b₁ - 1 := by
    have h1 := hself.1
    have h2 := hself.2
    omega
  have hb₀1 : 1 ≤ b₀ := by omega
  have hb : b₁ = b₀ + 1 := by omega
  have h₀1 : t.IsFixRadius (ε + 2) b₀ := by
    have h := IsFixRadius.shift t h₀ (1 : ℤ)
    rwa [show ε + 2 * (1 : ℤ) = ε + 2 by ring] at h
  have h₀b : t.IsFixRadius (ε + 2 * b₁) b₀ := by
    have h := IsFixRadius.shift t h₀ (b₁ : ℤ)
    rwa [show ε + 2 * (b₁ : ℤ) = ε + 2 * b₁ by ring] at h
  have h₁c : t.IsFixRadius (ε + 1 + b₁) b₁ := by
    have h := IsFixRadius.shift t h₁ (k : ℤ)
    rwa [show (ε + 1) + 2 * (k : ℤ) = ε + 1 + b₁ by rw [hk]; push_cast; ring] at h
  have hcommc : ⁅t.Zv ((ε + 1 + b₁) - b₁), t.Zv (ε + 1 + b₁)⁆ = ⊥ := by
    rw [show (ε + 1 + b₁) - (b₁ : ℤ) = ε + 1 by ring,
      show ε + 1 + (b₁ : ℤ) = ε + 1 + b₁ by ring]
    exact hcomm
  have hZLc : t.Lv (ε + 1 + b₁) ≤ centralizer (t.Zv (ε + 1 + b₁) : Set G) :=
    IsFixRadius.Lv_le_centralizer t hfr h₁c heven (Or.inr hcommc)
  have hLv_le : t.Lv (ε + 1 + b₁) ≤
      (t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b₁)) ⊔ t.Qv (ε + 1 + b₁) :=
    Lv_le_sup_Zv_pair t hfr hb hb₀1 hb2 h₀
  have hE_Lv : t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b₁) ≤ t.Lv (ε + 1 + b₁) :=
    sup_Zv_pair_le_Lv t hfr hb hb₀1 hb2 h₀
  have hKc_E : t.K ⊓ t.Lv (ε + 1 + b₁) ≤ t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b₁) :=
    Kc_le_sup_Zv_pair t hfr hb hb₀1 hb2 h₀
  have hQcent : pCoreOf 2 (t.Gw ε (ε + n)) ≤
      centralizer (((t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b₁)) : Subgroup G) : Set G) :=
    pCoreOf_le_centralizer_Zv_pair t hfr h hn hb2
  obtain ⟨⟨k, hkKc⟩, hk1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (t.K_inf_Lv_ne_bot hfr (ε + 1 + b₁))
  have hk_ne : k ≠ 1 := by
    intro h
    apply hk1
    ext
    exact h
  have hkK : k ∈ t.K := hkKc.1
  have hkLv : k ∈ t.Lv (ε + 1 + b₁) := hkKc.2
  have hkE : k ∈ t.Zv (ε + 2) ⊔ t.Zv (ε + 2 * b₁) := hKc_E hkKc
  have hkQcent : k ∈ centralizer (pCoreOf 2 (t.Gw ε (ε + n)) : Set G) :=
    (Subgroup.le_centralizer_iff.mp hQcent) hkE
  have hkZcent : k ∈ centralizer (t.Zv (ε + 1 + b₁) : Set G) := hZLc hkLv
  have hQbig_edge : pCoreOf 2 (t.Gw ε (ε + n)) ≤ pCoreOf 2 (t.Gw ε (ε + 1)) := by
    refine t.le_pCoreOf_Gw hfr (by omega) (pCoreOf_isPGroup 2 _) ?_
    exact (pCoreOf_le 2 _).trans
      (win_mono (a := ε) (b := ε + n) (a' := ε) (b' := ε + 1) le_rfl (by omega))
  have hQbig_K : t.K ≤ normalizer (pCoreOf 2 (t.Gw ε (ε + n)) : Set G) :=
    (t.K_le_Gw ε (ε + n)).trans (le_normalizer_pCoreOf 2 _)
  have hQbig_not : ¬ pCoreOf 2 (t.Gw ε (ε + n)) ≤ t.Qv ε := by
    intro hle
    have hinf : pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε - 1) = ⊥ :=
      (IsMaxArc.inf_Gv_eq_bot t hfr h).1
    have hbot : pCoreOf 2 (t.Gw ε (ε + n)) ≤ (⊥ : Subgroup G) :=
      (le_inf le_rfl (hle.trans (t.Qv_le_Gv hfr ε).1)).trans_eq hinf
    exact h.pCoreOf_ne_bot (le_bot_iff.mp hbot)
  have hoddk : Odd (orderOf k) := by
    have hdvd : orderOf k ∣ Nat.card t.K := by
      rw [← Subgroup.orderOf_mk (H := t.K) k hkK]
      exact orderOf_dvd_natCard (⟨k, hkK⟩ : t.K)
    exact Odd.of_dvd_nat t.hHall.2.1 hdvd
  have hcomplexε : ∀ l ∈ t.Lv ε, ⁅k, l⁆ ∈ t.Qv ε :=
    t.commutator_mem_Qv_of_mem_centralizer hfr ε hQbig_edge hQbig_K hQbig_not hkK hkQcent
  have hcomplexε1 : ∀ l ∈ t.Lv (ε + 1), ⁅k, l⁆ ∈ t.Qv (ε + 1) :=
    commutator_mem_Qv_of_odd_succ t hfr hb2 h₁c hkK hkZcent
  have hk_one := eq_one_of_forall_commutator_mem_Qv t hfr hkK hoddk hcomplexε hcomplexε1
  exact hk_ne hk_one

end Track

end CFSG.Quasithin.Stroth.Rq

end
