module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggF4Orig_card_le_pow_mul {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {ι : Type} [Fintype ι] {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p M A) (N : Subgroup ↥Bs)
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b ∈ N) :
    Nat.card Bs ≤ p ^ Fintype.card ι * Nat.card N := by
  obtain ⟨e, he⟩ := hW
  let φ : ι → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  let F : ι → Subgroup ↥Bs := fun i =>
    { carrier := {b | φ i b = b}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact map_one (φ i)
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hFcard : ∀ i, Nat.card (F i) * p = Nat.card ↥Bs := fun i => (he i).2
  have hFpos : ∀ i, 0 < Nat.card (F i) := fun i => by
    haveI : Nonempty ↥(F i) := ⟨⟨1, by simp [F]⟩⟩
    exact Nat.card_pos
  have hindex : ∀ i, (F i).index = p := fun i => by
    have h1 : Nat.card (F i) * (F i).index = Nat.card ↥Bs := Subgroup.card_mul_index (F i)
    exact Nat.mul_left_cancel (hFpos i) (by rw [h1, hFcard i])
  have hle : (⨅ i, F i) ≤ N := by
    intro b hb
    refine hfix b ?_
    let f : M.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
    have hbfix : ∀ i, φ i b = b := fun i => by
      simpa [F] using Subgroup.mem_iInf.mp hb i
    have hHsimple : ∀ i, M.simple i ∈
        (MulAction.stabilizer (MulAut ↥Bs) b).comap f := by
      intro i
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      simpa [f, MulAut.smul_def] using hbfix i
    have htop : (MulAction.stabilizer (MulAut ↥Bs) b).comap f = ⊤ := by
      rw [eq_top_iff, ← M.toCoxeterSystem.subgroup_closure_range_simple]
      exact (Subgroup.closure_le _).mpr (by rintro x ⟨i, rfl⟩; exact hHsimple i)
    intro ψ hψ
    have hmem : e.symm ⟨ψ, hψ⟩ ∈ (MulAction.stabilizer (MulAut ↥Bs) b).comap f := by
      rw [htop]; exact Subgroup.mem_top _
    have hfixb : f (e.symm ⟨ψ, hψ⟩) • b = b :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp hmem)
    simpa [f, MulAut.smul_def] using hfixb
  calc Nat.card Bs = Nat.card (⨅ i, F i : Subgroup ↥Bs) * (⨅ i, F i : Subgroup ↥Bs).index :=
        (Subgroup.card_mul_index _).symm
    _ ≤ Nat.card N * ∏ i, (F i).index :=
        Nat.mul_le_mul (Subgroup.card_le_of_le hle) (Subgroup.index_iInf_le F)
    _ = Nat.card N * ∏ _i : ι, p :=
        congrArg (fun y => Nat.card N * y) (Finset.prod_congr rfl (fun i _ => hindex i))
    _ = Nat.card N * p ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
    _ = p ^ Fintype.card ι * Nat.card N := Nat.mul_comm _ _

theorem ggF4Orig_three_le_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {x : G} (hx : x ∈ Bs)
    (h4 : p ^ 4 ≤ Nat.card Bs) {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}
    {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p M A)
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → (b : G) ∈ Subgroup.zpowers x) :
    3 ≤ Fintype.card ι := by
  let x' : ↥Bs := ⟨x, hx⟩
  have hx'p : x' ^ p = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 x hx
  have hNcard : Nat.card (Subgroup.zpowers x') ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hx'p)
  have hfixN : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b ∈ Subgroup.zpowers x' := by
    intro b hb
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hfix b hb)
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext ?_⟩
    simpa [Subgroup.coe_zpow, x'] using hn
  have hmain := ggF4Orig_card_le_pow_mul hW (Subgroup.zpowers x') hfixN
  have h5 : p ^ 4 ≤ p ^ (Fintype.card ι + 1) :=
    calc p ^ 4 ≤ Nat.card Bs := h4
      _ ≤ p ^ Fintype.card ι * Nat.card (Subgroup.zpowers x') := hmain
      _ ≤ p ^ Fintype.card ι * p := Nat.mul_le_mul_left _ hNcard
      _ = p ^ (Fintype.card ι + 1) := (pow_succ p _).symm
  have h6 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h5
  omega

end CFSG.StandardType

end
