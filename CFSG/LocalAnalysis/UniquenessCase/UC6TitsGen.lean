module

public import CFSG.LocalAnalysis.UniquenessCase.UC6AutKernels
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
  (SignalizerTrivialOn injective_conj_of_center_eq_bot)

theorem conj_comm_of_fix_uc6 {K : Type} [Group K] (α : MulAut K) (e : K) (h : α e = e) :
    MulAut.conj e * α = α * MulAut.conj e := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]

@[expose] def SylowAutSelfCent (K : Type) [Group K] (p : ℕ) : Prop :=
  ∀ R : Sylow p (MulAut K), Nat.card (R : Subgroup (MulAut K)) = p ^ 2 ∧
    Subgroup.centralizer (R : Set (MulAut K)) ≤ (R : Subgroup (MulAut K))

theorem SylowAutSelfCent.eq_conj_of_fix {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hA : SylowAutSelfCent K p) (hcen : Subgroup.center K = ⊥) {E : Subgroup K} (hE : Nat.card E = p ^ 2)
    (α : MulAut K) (hα : ∀ e ∈ E, α e = e) : ∃ e ∈ E, α = MulAut.conj e := by
  have hinj := injective_conj_of_center_eq_bot hcen
  set B : Subgroup (MulAut K) := E.map (MulAut.conj : K →* MulAut K) with hB
  have hBcard : Nat.card B = p ^ 2 := by rw [hB, Subgroup.card_map_of_injective hinj, hE]
  obtain ⟨R, hBR⟩ := (IsPGroup.of_card hBcard).exists_le_sylow
  obtain ⟨hRcard, hRC⟩ := hA R
  have hBR' : B = (R : Subgroup (MulAut K)) :=
    Subgroup.eq_of_le_of_card_ge hBR (by rw [hBcard, hRcard])
  have hmem : α ∈ Subgroup.centralizer (R : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : g ∈ B := by rw [hBR']; exact hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg'
    exact conj_comm_of_fix_uc6 α x (hα x hx)
  have hαB : α ∈ B := by rw [hBR']; exact hRC hmem
  obtain ⟨x, hx, hxα⟩ := Subgroup.mem_map.1 hαB
  exact ⟨x, hx, hxα.symm⟩

theorem AbsKC.of_sylowAutSelfCent {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hA : SylowAutSelfCent K p) (hcen : Subgroup.center K = ⊥) {E : Subgroup K} (hE : Nat.card E = p ^ 2) :
    AbsKC K p E :=
  fun α _ hα => hA.eq_conj_of_fix hcen hE α hα

theorem AbsKInv.of_sylowAutSelfCent {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hA : SylowAutSelfCent K p) (hcen : Subgroup.center K = ⊥) {E : Subgroup K} (hE : Nat.card E = p ^ 2) :
    AbsKInv K E := by
  intro x y ⟨k, hk⟩ _ hx _ hx1 _
  exfalso
  obtain ⟨e, he, hxe⟩ := hA.eq_conj_of_fix hcen hE x hx
  have hP : IsPGroup p E := IsPGroup.of_card hE
  obtain ⟨j, hj⟩ := hP ⟨e, he⟩
  have h5 : e ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h1 : orderOf x ∣ p ^ j := by
    rw [hxe]
    exact (orderOf_map_dvd (MulAut.conj : K →* MulAut K) e).trans (orderOf_dvd_of_pow_eq_one h5)
  have h2 : Nat.Coprime (orderOf x) (p ^ j) := by
    rw [hk]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2 (Ne.symm hp2))
  exact hx1 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h2 h1))

theorem AbsKN.of_signalizerTrivialOn {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (h : SignalizerTrivialOn p K) (P : Sylow p K) (isL34 : Prop) :
    AbsKN K p (P : Subgroup K) isL34 := by
  intro X hnorm hno
  have hcop : Nat.Coprime p (Nat.card X) := by
    rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) p hdvd
    have h1 : x = 1 := by
      have := hno (x : MulAut K) x.2 ⟨1, by simpa using hx⟩
      exact Subtype.ext this
    rw [h1, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  have hX : X = ⊥ := h P X hcop hnorm
  subst hX
  refine ⟨fun x hx e _ => ?_, Or.inl rfl⟩
  rw [Subgroup.mem_bot] at hx
  subst hx
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC6
