module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res6

theorem card_centralizer_mul_le {G : Type*} [Group G] [Finite G] (r : G) {N : ℕ} (f : Fin N → G)
    (hf : ∀ i j, f i * r * (f i)⁻¹ = f j * r * (f j)⁻¹ → i = j) :
    Nat.card (Subgroup.centralizer ({r} : Set G)) * N ≤ Nat.card G := by
  set C := Subgroup.centralizer ({r} : Set G)
  have hinj : Function.Injective fun i : Fin N => (QuotientGroup.mk (f i) : G ⧸ C) := by
    intro i j hij
    have hmem : (f i)⁻¹ * f j ∈ C := QuotientGroup.eq.mp hij
    rw [Subgroup.mem_centralizer_singleton_iff] at hmem
    apply hf
    calc f i * r * (f i)⁻¹ = f i * (((f i)⁻¹ * f j) * r * ((f i)⁻¹ * f j)⁻¹) * (f i)⁻¹ := by
          rw [hmem]; group
      _ = f j * r * (f j)⁻¹ := by group
  have hN : N ≤ C.index := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin, ← Subgroup.index] at this
  calc Nat.card C * N ≤ Nat.card C * C.index := Nat.mul_le_mul_left _ hN
    _ = Nat.card G := C.card_mul_index

theorem card_centralizer_conj {G : Type*} [Group G] (g z : G) :
    Nat.card (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  refine (Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun y => ?_)).symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change y * z = z * y ↔ (g * y * g⁻¹) * (g * z * g⁻¹) = (g * z * g⁻¹) * (g * y * g⁻¹)
  constructor
  · intro h
    calc (g * y * g⁻¹) * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [h]
      _ = (g * z * g⁻¹) * (g * y * g⁻¹) := by group
  · intro h
    calc y * z = g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = z * y := by group

theorem exists_conj_mem_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {P : Subgroup G} (hP : Nat.card P = p ^ (Nat.card G).factorization p) {z : G}
    (hz : z ^ p = 1) : ∃ g : G, g⁻¹ * z * g ∈ P := by
  have hzp : IsPGroup p (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := (orderOf z).factorization p) ?_
    rw [Nat.card_zpowers]
    rcases (Nat.dvd_prime hp.out).mp (orderOf_dvd_of_pow_eq_one hz) with h | h
    · rw [h]; simp
    · rw [h, hp.out.factorization_self, pow_one]
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (Sylow.ofCard P hP) Q
  refine ⟨g, ?_⟩
  have hzQ : z ∈ ((g • Sylow.ofCard P hP : Sylow p G) : Subgroup G) := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers z)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at hzQ
  exact hzQ

@[expose] def orFold (l : List ℕ) : ℕ := l.foldr (fun a m => Nat.lor (Nat.shiftLeft 1 a) m) 0

theorem testBit_orFold (l : List ℕ) (b : ℕ) : Nat.testBit (orFold l) b = decide (b ∈ l) := by
  induction l with
  | nil => simp [orFold]
  | cons a l ih =>
    simp only [orFold, List.foldr_cons] at ih ⊢
    change Nat.testBit ((1 <<< a) ||| List.foldr (fun a m => Nat.lor (Nat.shiftLeft 1 a) m) 0 l)
      b = _
    rw [Nat.testBit_lor, ih, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    by_cases h : a = b
    · subst h; simp
    · have h' : b ≠ a := fun e => h e.symm
      simp [h, h']

theorem orFold_eq_of_mem_iff {l l' : List ℕ} (h : ∀ b, b ∈ l ↔ b ∈ l') : orFold l = orFold l' :=
  Nat.eq_of_testBit_eq fun b => by rw [testBit_orFold, testBit_orFold, decide_eq_decide.mpr (h b)]

theorem mem_iff_of_orFold_eq {l l' : List ℕ} (h : orFold l = orFold l') (b : ℕ) :
    b ∈ l ↔ b ∈ l' := by
  have := congrArg (fun m => Nat.testBit m b) h
  simp only [testBit_orFold, decide_eq_decide] at this
  exact this

end CFSG.RankThree.PartTwo.Sec6.Res611Res6
