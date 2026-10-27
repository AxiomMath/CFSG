module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggBs_le_hyperplane_sup_of_rep {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {r : MulAut ↥Bs} (hr2 : r * r = 1)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {n : G} (hnX : n ∈ X)
    (hact : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) :
    Bs ≤ ggHyperplane Bs r ⊔ X := by
  have hcomm : ∀ a c : ↥Bs, a * c = c * a := fun a c => hBs.1.is_comm.comm a c
  have hrr : ∀ c : ↥Bs, r (r c) = c := fun c => by
    have h := congrArg (fun φ : MulAut ↥Bs => φ c) hr2
    simpa using h
  obtain ⟨k, hk⟩ : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  intro b hb
  set b' : ↥Bs := ⟨b, hb⟩ with hb'
  have hv : ((b' * r b' : ↥Bs) : G) ∈ ggHyperplane Bs r := by
    refine ⟨b' * r b', ?_, rfl⟩
    change r (b' * r b') = b' * r b'
    rw [map_mul, hrr, hcomm]
  have hu : ((b' * (r b')⁻¹ : ↥Bs) : G) ∈ X := by
    have e1 : ((b' * (r b')⁻¹ : ↥Bs) : G) = (b * n * b⁻¹) * n⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hact b']
      simp only [hb']
      group
    rw [e1]
    exact X.mul_mem (((Subgroup.mem_normalizer_iff.mp (hBsN hb)) n).mp hnX) (X.inv_mem hnX)
  have hsq : (b' * r b') * (b' * (r b')⁻¹) = b' ^ 2 :=
    calc (b' * r b') * (b' * (r b')⁻¹) = b' * (r b' * b') * (r b')⁻¹ := by group
      _ = b' * (b' * r b') * (r b')⁻¹ := by rw [hcomm (r b') b']
      _ = b' ^ 2 := by rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, pow_two]
  have hbp : b' ^ p = 1 := Subtype.ext (hBs.2 b hb)
  have hbk : b' = ((b' * r b') * (b' * (r b')⁻¹)) ^ (k + 1) := by
    rw [hsq, ← pow_mul]
    have : b' ^ (2 * (k + 1)) = b' ^ p * b' := by
      rw [show 2 * (k + 1) = p + 1 by omega, pow_succ]
    rw [this, hbp, one_mul]
  have hmem : ((b' * r b' : ↥Bs) : G) * ((b' * (r b')⁻¹ : ↥Bs) : G) ∈ ggHyperplane Bs r ⊔ X :=
    Subgroup.mul_mem_sup hv hu
  have hb_eq : b = (((b' * r b' : ↥Bs) : G) * ((b' * (r b')⁻¹ : ↥Bs) : G)) ^ (k + 1) := by
    have := congrArg (fun z : ↥Bs => (z : G)) hbk
    simpa [Subgroup.coe_pow, Subgroup.coe_mul] using this
  rw [hb_eq]
  exact Subgroup.pow_mem _ hmem _

theorem ggMovingElem_mem_rankOneIn {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {r : MulAut ↥Bs}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {n : G} (hn : n ∈ ggRankOneIn X Bs r)
    (hact : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) (b : ↥Bs) :
    (b : G) * ((r b : ↥Bs) : G)⁻¹ ∈ ggRankOneIn X Bs r := by
  have hcomm : ∀ a c : ↥Bs, a * c = c * a := fun a c => hBs.1.is_comm.comm a c
  have hbN : (b : G) ∈ Subgroup.normalizer (X : Set G) := hBsN b.2
  have ha : ∀ c : ↥Bs, (((1 : MulAut ↥Bs) c : ↥Bs) : G) = (b : G) * c * (b : G)⁻¹ := fun c => by
    have h := congrArg (fun z : ↥Bs => (z : G)) (hcomm b c)
    simp only [Subgroup.coe_mul] at h
    change (c : G) = _
    rw [h]
    group
  have hmap := ggRankOneIn_map_conj (X := X) ha r
  rw [one_mul, inv_one, mul_one, mem_normalizer_iff_map_conj.mp hbN] at hmap
  have hbn : (b : G) * n * (b : G)⁻¹ ∈ ggRankOneIn X Bs r := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have e : (b : G) * ((r b : ↥Bs) : G)⁻¹ = ((b : G) * n * (b : G)⁻¹) * n⁻¹ := by
    rw [hact b]
    group
  rw [e]
  exact Subgroup.mul_mem _ hbn (Subgroup.inv_mem _ hn)

theorem ggMovingElem_noncomm {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {r : MulAut ↥Bs} (hr2 : r * r = 1)
    {n : G} (hact : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) {b : ↥Bs} (hb : r b ≠ b) :
    n * ((b : G) * ((r b : ↥Bs) : G)⁻¹) ≠ ((b : G) * ((r b : ↥Bs) : G)⁻¹) * n := by
  intro hc
  have hrr : ∀ c : ↥Bs, r (r c) = c := fun c => by
    have h := congrArg (fun φ : MulAut ↥Bs => φ c) hr2
    simpa using h
  obtain ⟨k, hk⟩ : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  set w : G := (b : G) * ((r b : ↥Bs) : G)⁻¹ with hw
  have hwB : w ∈ Bs := Bs.mul_mem b.2 (Bs.inv_mem (r b).2)
  have h1 : n * w * n⁻¹ = ((r b : ↥Bs) : G) * (b : G)⁻¹ := by
    have e : n * w * n⁻¹ = (n * (b : G) * n⁻¹) * (n * ((r b : ↥Bs) : G) * n⁻¹)⁻¹ := by
      rw [hw]; group
    rw [e, ← hact b, ← hact (r b), hrr]
  have h2 : n * w * n⁻¹ = w := by rw [hc]; group
  have hwinv : w = w⁻¹ := by
    rw [hw]
    calc (b : G) * ((r b : ↥Bs) : G)⁻¹ = n * w * n⁻¹ := h2.symm
      _ = ((r b : ↥Bs) : G) * (b : G)⁻¹ := h1
      _ = _ := by group
  have hw2 : w ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hwinv
  have hwp : w ^ p = 1 := hBs.2 w hwB
  have hw1 : w = 1 := by
    have : w ^ p = (w ^ 2) ^ k * w := by
      rw [hk, pow_succ, pow_mul]
    rw [this, hw2, one_pow, one_mul] at hwp
    exact hwp
  apply hb
  apply Subtype.ext
  have : (b : G) = ((r b : ↥Bs) : G) := by
    rw [hw] at hw1
    exact mul_inv_eq_one.mp hw1
  exact this.symm

theorem ggExists_moved_of_isReflection {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} {r : MulAut ↥Bs} (hr : GGIsReflection p r) : ∃ b : ↥Bs, r b ≠ b := by
  by_contra h
  have h : ∀ b : ↥Bs, r b = b := fun b => by
    by_contra hb
    exact h ⟨b, hb⟩
  have hall : Nat.card {b : ↥Bs // r b = b} = Nat.card ↥Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv h)
  have h1 := hr.2
  rw [hall] at h1
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  have : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact h1)
  exact hp.one_lt.ne' this

end CFSG.StandardType

end
