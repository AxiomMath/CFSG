module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45CommSub
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45XGen
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem conj_toMonoidHom_comp_subtype (H : Subgroup G) [H.Normal] (g : G) :
    (MulAut.conj g).toMonoidHom.comp H.subtype =
      H.subtype.comp (MulAut.conjNormal g : MulAut ↥H).toMonoidHom := by
  ext y
  simp [MulAut.conj_apply, MulAut.conjNormal_apply]

theorem commSub_conjNormal_normal (H : Subgroup G) [H.Normal] (d : G) :
    (K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).Normal := by
  refine ⟨fun x hx m => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      have hgen₁ : (z * m⁻¹)⁻¹ * (MulAut.conjNormal d : MulAut ↥H) (z * m⁻¹) ∈
          K22p.commSub (MulAut.conjNormal d : MulAut ↥H) :=
        Subgroup.subset_closure ⟨z * m⁻¹, rfl⟩
      have hgen₂ : ((m⁻¹)⁻¹) * (MulAut.conjNormal d : MulAut ↥H) (m⁻¹) ∈
          K22p.commSub (MulAut.conjNormal d : MulAut ↥H) :=
        Subgroup.subset_closure ⟨m⁻¹, rfl⟩
      have hid : m * (z⁻¹ * (MulAut.conjNormal d : MulAut ↥H) z) * m⁻¹ =
          ((z * m⁻¹)⁻¹ * (MulAut.conjNormal d : MulAut ↥H) (z * m⁻¹)) *
            (((m⁻¹)⁻¹ * (MulAut.conjNormal d : MulAut ↥H) (m⁻¹))⁻¹) := by
        simp only [map_mul, map_inv]
        group
      rw [hid]
      exact mul_mem hgen₁ (inv_mem hgen₂)
  | one => simpa using (K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).one_mem
  | mul x y _ _ ihx ihy =>
      have heq : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
      rw [heq]
      exact mul_mem ihx ihy
  | inv x _ ih =>
      have heq : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
      rw [heq]
      exact inv_mem ih

theorem map_subtype_conjNormal_invariant (H : Subgroup G) [H.Normal] (d : G)
    (Q : Subgroup ↥H) (hQ : Q.map (MulAut.conjNormal d : MulAut ↥H).toMonoidHom = Q) :
    (Q.map H.subtype).map (MulAut.conj d).toMonoidHom = Q.map H.subtype := by
  rw [Subgroup.map_map, conj_toMonoidHom_comp_subtype, ← Subgroup.map_map, hQ]

theorem fixesSylow_of_not_dvd (H : Subgroup G) (σ : MulAut ↥H) {q : ℕ} [Fact q.Prime]
    (hnotdvd : ¬ q ∣ Nat.card ↥H) : K22p.FixesSylow σ q := by
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := ↥H)
  unfold K22p.FixesSylow
  refine ⟨Q, ?_⟩
  have hQcard : Nat.card ↥(Q : Subgroup ↥H) = 1 := by
    change Nat.card Q = 1
    rw [Sylow.card_eq_multiplicity Q, Nat.factorization_eq_zero_of_not_dvd hnotdvd, pow_zero]
  have hQbot : (Q : Subgroup ↥H) = ⊥ := Subgroup.eq_bot_of_card_eq (Q : Subgroup ↥H) hQcard
  intro x hx
  have hx1 : x = 1 := by
    have : x ∈ (⊥ : Subgroup ↥H) := hQbot ▸ hx
    simpa using this
  simp [hx1]

theorem not_dvd_card_pPrimeCore_three :
    ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := G))

theorem conjNormal_pow_three (H : Subgroup G) [H.Normal] {d : G} (hd : d ^ 3 = 1) :
    (MulAut.conjNormal d : MulAut ↥H) ^ 3 = 1 := by
  change (MulAut.conjNormal (H := H) d) ^ 3 = 1
  rw [← map_pow, hd, map_one]

theorem exists_zpowers_card_three_conjNormal (H : Subgroup G) [H.Normal] (hD : Nat.card D = 3) :
    ∃ d : G, Subgroup.zpowers d = D ∧ d ^ 3 = 1 ∧
      (MulAut.conjNormal d : MulAut ↥H) ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top D).mp
    (isCyclic_of_prime_card (p := 3) hD)
  have hd3 : d ^ 3 = 1 := by
    have horder : orderOf d = 3 := by rw [← Nat.card_zpowers d, hd, hD]
    rw [← horder]
    exact pow_orderOf_eq_one d
  exact ⟨d, hd, hd3, conjNormal_pow_three H hd3⟩

theorem commutator_normalized_prime_eq_bot (h : Base45 p G D) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hqp : q ≠ p) {Q' : Subgroup G} (hQ'q : IsPGroup q Q')
    (hDnorm : D ≤ Subgroup.normalizer (Q' : Set G)) (hQ'coprime : ¬ 3 ∣ Nat.card Q')
    (hD3 : IsPGroup 3 ↥D) : ⁅Q', D⁆ = ⊥ := by
  have hRQ' : (⁅Q', D⁆ : Subgroup G) ≤ Q' :=
    CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized Q' D hDnorm
  have hRq : IsPGroup q (⁅Q', D⁆ : Subgroup G) := hQ'q.to_le hRQ'
  have hDnormR : D ≤ Subgroup.normalizer ((⁅Q', D⁆ : Subgroup G) : Set G) :=
    CFSG.LargeEvenClassification.Helpers.normalizes_commutator_pair D Q' D hDnorm
      (Subgroup.le_normalizer (H := D))
  have hRidem : ⁅⁅Q', D⁆, D⁆ = (⁅Q', D⁆ : Subgroup G) :=
    CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three D Q' hD3 hQ'coprime hDnorm
  have hcommR : ⁅D, ⁅Q', D⁆⁆ = (⁅Q', D⁆ : Subgroup G) := by
    rw [Subgroup.commutator_comm, hRidem]
  exact h.noOdd q hq hq2 hq3 hqp (⁅Q', D⁆) hRq hDnormR hcommR

theorem fixesSylow_conjNormal_of_dvd_card (h : Base45 p G D) (H : Subgroup G) [H.Normal]
    (hnotdvd : ¬ 3 ∣ Nat.card ↥H) {d : G} (hd : Subgroup.zpowers d = D) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (hqdiv : q ∣ Nat.card ↥H) :
    K22p.FixesSylow (MulAut.conjNormal d : MulAut ↥H) q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq3 : q ≠ 3 := fun hq3 => hnotdvd (hq3 ▸ hqdiv)
  have hD3 : IsPGroup 3 ↥D := IsPGroup.of_card (n := 1) (by rw [h.card_three]; norm_num)
  obtain ⟨Q, hQinv⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime
      3 q hD3 hnotdvd ((MulAut.conjNormal (H := H)).comp D.subtype)
  let Q' : Subgroup G := (Q : Subgroup ↥H).map H.subtype
  have hQ'q : IsPGroup q Q' := Q.isPGroup'.map H.subtype
  have hDnorm : D ≤ Subgroup.normalizer (Q' : Set G) := by
    intro d' hd'
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQd : (Q : Subgroup ↥H).map (MulAut.conjNormal (H := H) d').toMonoidHom = Q := by
      simpa using hQinv ⟨d', hd'⟩
    simpa [Q'] using map_subtype_conjNormal_invariant H d' (Q : Subgroup ↥H) hQd
  have hQ'coprime : ¬ 3 ∣ Nat.card Q' := by
    obtain ⟨n, hn⟩ := hQ'q.exists_card_eq
    rw [hn]
    intro hdiv
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.prime_three.dvd_of_dvd_pow hdiv)).symm
  have hRbot : (⁅Q', D⁆ : Subgroup G) = ⊥ :=
    commutator_normalized_prime_eq_bot h hq hq2 hq3 hqp hQ'q hDnorm hQ'coprime hD3
  unfold K22p.FixesSylow
  refine ⟨Q, ?_⟩
  intro y hy
  have hcentral : Q' ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRbot
  have hyQ' : (y : G) ∈ Q' := Subgroup.mem_map_of_mem H.subtype hy
  have hdD : d ∈ D := hd ▸ Subgroup.mem_zpowers d
  have hcomm : (y : G) * d = d * (y : G) :=
    (Subgroup.mem_centralizer_iff.mp (hcentral hyQ') d hdD).symm
  apply Subtype.ext
  simp only [MulAut.conjNormal_apply]
  exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm

theorem fixesSylow_conjNormal_pPrimeCore (h : Base45 p G D) {d : G}
    (hd : Subgroup.zpowers d = D) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    K22p.FixesSylow (MulAut.conjNormal d : MulAut ↥(CFSG.pPrimeCore 3 G)) q := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqdiv : q ∣ Nat.card ↥(CFSG.pPrimeCore 3 G)
  · exact fixesSylow_conjNormal_of_dvd_card h (CFSG.pPrimeCore 3 G)
      not_dvd_card_pPrimeCore_three hd hq hq2 hqp hqdiv
  · exact fixesSylow_of_not_dvd (CFSG.pPrimeCore 3 G) _ hqdiv

theorem primeSupported_commSub_conjNormal (hAbs : K22p.K22pAbs) (hSz1 : SimpleThreePrimeIsSz)
    (hSz2 : SzOrder3Aut) (H : Subgroup G) [H.Normal] (hnotdvd : ¬ 3 ∣ Nat.card ↥H)
    (hK : CFSG.Open.IsKGroup ↥H) {d : G} (hσ3 : (MulAut.conjNormal d : MulAut ↥H) ^ 3 = 1)
    (hfix : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
      K22p.FixesSylow (MulAut.conjNormal d : MulAut ↥H) q) :
    CFSG.primeSupported ({2, p} : Set ℕ)
      (Nat.card ↥(K22p.commSub (MulAut.conjNormal d : MulAut ↥H))) := by
  have hAbsM := hAbs hSz1 hSz2 p ↥H hK hnotdvd (MulAut.conjNormal d : MulAut ↥H) hσ3 hfix
  intro q hq hqdiv
  rcases hAbsM q hq hqdiv with h | h <;> simp [h]

theorem conj_le_primeSetCore (H : Subgroup G) [H.Normal] {d : G} (hd : Subgroup.zpowers d = D)
    (hMsupp : CFSG.primeSupported ({2, p} : Set ℕ)
      (Nat.card ↥(K22p.commSub (MulAut.conjNormal d : MulAut ↥H)))) :
    ∀ g : G, (⁅H, D⁆).map (MulAut.conj g).toMonoidHom ≤
      (CFSG.primeSetCore ({2, p} : Set ℕ) ↥H).map H.subtype := by
  have hmapL : (K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).map H.subtype = ⁅H, D⁆ :=
    commSub_conjNormal_map H D d hd.symm
  have hMnorm : (K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).Normal :=
    commSub_conjNormal_normal H d
  have hCmax := CFSG.primeSetCore_maximal (G := ↥H) ({2, p} : Set ℕ)
  intro g
  have hαnorm : ((K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).map
      (MulAut.conjNormal g).toMonoidHom) ≤ CFSG.primeSetCore ({2, p} : Set ℕ) ↥H := by
    refine hCmax.2 _ ?_ ?_
    · exact hMnorm.map (MulAut.conjNormal g).toMonoidHom (MulAut.conjNormal g).surjective
    · have hcard : Nat.card ↥((K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).map
            (MulAut.conjNormal g).toMonoidHom) =
            Nat.card ↥(K22p.commSub (MulAut.conjNormal d : MulAut ↥H)) :=
        Subgroup.card_map_of_injective (f := (MulAut.conjNormal g).toMonoidHom)
          (MulAut.conjNormal g).injective
      rw [hcard]
      exact hMsupp
  calc (⁅H, D⁆).map (MulAut.conj g).toMonoidHom
      = ((K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).map H.subtype).map
          (MulAut.conj g).toMonoidHom := by rw [hmapL]
    _ = ((K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).map
          (MulAut.conjNormal g).toMonoidHom).map H.subtype := by
          rw [Subgroup.map_map, Subgroup.map_map, conj_toMonoidHom_comp_subtype]
    _ ≤ (CFSG.primeSetCore ({2, p} : Set ℕ) ↥H).map H.subtype := Subgroup.map_mono hαnorm

theorem kof_le_primeSetCore (hgen : Subgroup.normalClosure (D : Set G) = ⊤)
    (hconj_le : ∀ g : G, (⁅CFSG.pPrimeCore 3 G, D⁆).map (MulAut.conj g).toMonoidHom ≤
      (CFSG.primeSetCore ({2, p} : Set ℕ) ↥(CFSG.pPrimeCore 3 G)).map
        (CFSG.pPrimeCore 3 G).subtype) :
    Kof G ≤ (CFSG.primeSetCore ({2, p} : Set ℕ) ↥(CFSG.pPrimeCore 3 G)).map
      (CFSG.pPrimeCore 3 G).subtype := by
  have hK : Kof G = Subgroup.normalClosure ((⁅CFSG.pPrimeCore 3 G, D⁆ : Subgroup G) : Set G) :=
    commutator_top_eq_normalClosure (N := CFSG.pPrimeCore 3 G) (D := D) hgen
  rw [hK]
  unfold Subgroup.normalClosure
  refine (Subgroup.closure_le _).mpr ?_
  intro y hy
  obtain ⟨x, hxL, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
  obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
  simpa [MulAut.conj_apply] using
    hconj_le g (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hxL)

theorem uc45_K22p_of (hAbs : K22p.K22pAbs) (hSz1 : SimpleThreePrimeIsSz)
    (hSz2 : SzOrder3Aut) (h : Base45 p G D) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Kof G) → q = 2 ∨ q = p := by
  let H : Subgroup G := CFSG.pPrimeCore 3 G
  haveI : H.Normal := CFSG.pPrimeCore_normal
  have hnotdvd : ¬ 3 ∣ Nat.card ↥H := not_dvd_card_pPrimeCore_three
  obtain ⟨d, hd, _, hσ3⟩ := exists_zpowers_card_three_conjNormal H h.card_three
  have hfix : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
      K22p.FixesSylow (MulAut.conjNormal d : MulAut ↥H) q :=
    fun q hq hq2 hqp => fixesSylow_conjNormal_pPrimeCore h hd hq hq2 hqp
  have hMsupp := primeSupported_commSub_conjNormal hAbs hSz1 hSz2 H hnotdvd
    (h.kgroup.subgroup H) hσ3 hfix
  have hconj_le := conj_le_primeSetCore H hd hMsupp
  have hKle := kof_le_primeSetCore h.gen hconj_le
  have hKcard : Nat.card ↥(Kof G) ∣ Nat.card ↥((CFSG.primeSetCore ({2, p} : Set ℕ)
      ↥H).map H.subtype) := Subgroup.card_dvd_of_le hKle
  have hCcard : Nat.card ↥((CFSG.primeSetCore ({2, p} : Set ℕ) ↥H).map H.subtype) =
      Nat.card ↥(CFSG.primeSetCore ({2, p} : Set ℕ) ↥H) :=
    Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective
  have hCmax := CFSG.primeSetCore_maximal (G := ↥H) ({2, p} : Set ℕ)
  intro q hq hqK
  have hqC : q ∣ Nat.card ↥(CFSG.primeSetCore ({2, p} : Set ℕ) ↥H) := by
    rw [← hCcard]
    exact hqK.trans hKcard
  simpa using hCmax.1 q hq hqC

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
