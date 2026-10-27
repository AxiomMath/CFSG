module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowEp2Lines
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.QuasithinUnique.Setup.X1

private theorem card_eq_prime_of_le_of_relIndex {W : Type} [CommGroup W] {p : ℕ} [Fact p.Prime]
    {A D : Subgroup (MulAut W)} (hDA : D ≤ A) (hDrel : D.relIndex A = p)
    (hAcard : Nat.card ↥A = p ^ 2) : Nat.card ↥D = p := by
  have h := D.relIndex_mul_card A
  rw [inf_of_le_left hDA, hDrel, hAcard, pow_two] at h
  exact Nat.mul_left_cancel (Fact.out : p.Prime).pos h

theorem relIndex_eq_prime_of_le_of_card {W : Type} [CommGroup W] {p : ℕ} [Fact p.Prime]
    {A D : Subgroup (MulAut W)} (hDA : D ≤ A) (hAcard : Nat.card ↥A = p ^ 2)
    (hDcard : Nat.card ↥D = p) : D.relIndex A = p := by
  have h := D.relIndex_mul_card A
  rw [inf_of_le_left hDA, hDcard, hAcard, pow_two] at h
  exact Nat.mul_right_cancel (Fact.out : p.Prime).pos h

private theorem fixV_eq_sup_inf_ker {W : Type} [CommGroup W] [Finite W]
    {A D : Subgroup (MulAut W)} (hDA : D ≤ A)
    (hsup : fixV A ⊔ (normHom A).ker = ⊤) :
    fixV D = fixV A ⊔ (fixV D ⊓ (normHom A).ker) := by
  apply le_antisymm
  · intro w hw
    have hw' : w ∈ fixV A ⊔ (normHom A).ker := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨u, hu, k, hk, huk⟩ := Subgroup.mem_sup.1 hw'
    have hkD : k ∈ fixV D := by
      have hk_eq : k = u⁻¹ * w := by rw [← huk, inv_mul_cancel_left]
      rw [hk_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (fixV_anti hDA hu)) hw
    rw [← huk]
    exact Subgroup.mem_sup.2 ⟨u, hu, k, Subgroup.mem_inf.2 ⟨hkD, hk⟩, rfl⟩
  · exact sup_le (fixV_anti hDA) inf_le_left

theorem index_mul_card_inf_ker_normHom_eq {W : Type} [CommGroup W] [Finite W]
    {A D : Subgroup (MulAut W)} (hDA : D ≤ A)
    (hfix : fixV A ⊓ (normHom A).ker = ⊥)
    (hcard : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W) :
    (fixV D).index * Nat.card ↥(fixV D ⊓ (normHom A).ker) =
      Nat.card ↥(normHom A).ker := by
  have hsup : fixV A ⊔ (normHom A).ker = ⊤ := by
    refine Subgroup.eq_top_of_card_eq (H := fixV A ⊔ (normHom A).ker) ?_
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixV A) (normHom A).ker
      (fun _ _ _ _ => mul_comm _ _)).1
    rw [hfix, Subgroup.card_bot, mul_one, hcard] at h
    exact h
  have hdecomp := fixV_eq_sup_inf_ker hDA hsup
  have hinf : fixV A ⊓ (fixV D ⊓ (normHom A).ker) = ⊥ := by
    refine le_bot_iff.1 ?_
    calc fixV A ⊓ (fixV D ⊓ (normHom A).ker)
        ≤ fixV A ⊓ (normHom A).ker := inf_le_inf_left _ inf_le_right
      _ = ⊥ := hfix
  have hcardD : Nat.card ↥(fixV D) =
      Nat.card ↥(fixV A) * Nat.card ↥(fixV D ⊓ (normHom A).ker) := by
    have hdecomp_card : Nat.card ↥(fixV D) =
        Nat.card ↥(fixV A ⊔ (fixV D ⊓ (normHom A).ker)) := by
      conv_lhs => rw [hdecomp]
    rw [hdecomp_card]
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixV A)
      (fixV D ⊓ (normHom A).ker) (fun _ _ _ _ => mul_comm _ _)).1
    rwa [hinf, Subgroup.card_bot, mul_one] at h
  have hW' : Nat.card ↥(fixV D) * (fixV D).index = Nat.card W :=
    Subgroup.card_mul_index _
  rw [hcardD, ← hcard] at hW'
  have h : Nat.card ↥(fixV A) *
      (Nat.card ↥(fixV D ⊓ (normHom A).ker) * (fixV D).index) =
      Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker := by
    rw [← mul_assoc]
    exact hW'
  have hpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  have := Nat.mul_left_cancel hpos h
  rw [mul_comm]
  exact this

theorem exists_card_eq_two_pow_orderOf_mul_of_fixfree {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    {M : Subgroup W} {σ : MulAut W} (hσM : ∀ m ∈ M, σ m ∈ M)
    (hσp : ∀ m ∈ M, (σ ^ p) m = m) (hfix : ∀ m ∈ M, σ m = m → m = 1) :
    ∃ j : ℕ, Nat.card M = 2 ^ (orderOf (2 : ZMod p) * j) := by
  let f : M → M := fun a => ⟨σ a, hσM a a.2⟩
  have hiter : ∀ (n : ℕ) (a : M), ((f^[n] a : M) : W) = (σ ^ n) a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]
  have hf : ∀ a, f^[p] a = a := fun a => Subtype.ext (by rw [hiter]; exact hσp a a.2)
  have hmod := card_modEq_fix_prime p f hf
  have hfixcard : Nat.card {a | f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (map_one σ)⟩⟩⟩
    have hone : ∀ c : {a | f a = a}, (c.1 : W) = 1 := fun c =>
      hfix c.1 c.1.2 (congrArg Subtype.val c.2)
    apply Subtype.ext
    apply Subtype.ext
    rw [hone a, hone b]
  rw [hfixcard] at hmod
  obtain ⟨m, hm⟩ := card_eq_two_pow_W hW M
  rw [hm] at hmod
  have h2 : ((2 ^ m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  obtain ⟨j, hj⟩ := orderOf_dvd_of_pow_eq_one h2
  exact ⟨j, by rw [hm, hj]⟩

theorem ep2_lines_mem_iff {W : Type} [CommGroup W] [Finite W]
    [DecidableEq (Subgroup (MulAut W))] {p : ℕ} [Fact p.Prime]
    {A : Subgroup (MulAut W)} {a b : MulAut W}
    (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < p, b ≠ a ^ j) (hbo : orderOf b = p)
    (hAcard : Nat.card ↥A = p ^ 2) (𝒟 : Finset (Subgroup (MulAut W)))
    (h𝒟def : 𝒟 = insert (Subgroup.zpowers b)
      ((Finset.range p).image fun i => Subgroup.zpowers (a * b ^ i))) :
    (∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p) ∧ 𝒟.card = p + 1 := by
  classical
  have hmem𝒟 : ∀ D, D ∈ 𝒟 ↔ D = Subgroup.zpowers b ∨
      ∃ i, i < p ∧ D = Subgroup.zpowers (a * b ^ i) := by
    intro D
    rw [h𝒟def, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, Finset.mem_range.1 hi, h.symm⟩
    · rintro (h | ⟨i, hi, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, Finset.mem_range.2 hi, h.symm⟩
  have hmemB : Subgroup.zpowers b ≤ A := by rw [hA]; exact le_sup_right
  have hmemC : ∀ i, Subgroup.zpowers (a * b ^ i) ≤ A := by
    intro i
    rw [hA]
    exact Subgroup.zpowers_le.mpr (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) i))
  have h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p := by
    intro D
    rw [hmem𝒟 D]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨hmemB, relIndex_eq_prime_of_le_of_card hmemB hAcard
          (by rw [Nat.card_zpowers, hbo])⟩
      · exact ⟨hmemC i, relIndex_eq_prime_of_le_of_card (hmemC i) hAcard
          (card_zpowers_mul_pow ha hb ha1 hab hba i)⟩
    · rintro ⟨hDA, hDrel⟩
      have hDcard : Nat.card D = p := card_eq_prime_of_le_of_relIndex hDA hDrel hAcard
      rcases eq_zpowers_of_le_sup_zpowers ha hb hab (by simpa [hA] using hDA) hDcard with
        h | ⟨i, hi, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, h⟩
  have hcard𝒟 : 𝒟.card = p + 1 := by
    have hnot : Subgroup.zpowers b ∉
        (Finset.range p).image (fun i => Subgroup.zpowers (a * b ^ i)) := by
      rw [Finset.mem_image]
      rintro ⟨i, _, h⟩
      exact zpowers_ne_zpowers_mul_pow ha hb ha1 hab hba i h.symm
    have hinj : Set.InjOn (fun i => Subgroup.zpowers (a * b ^ i))
        (↑(Finset.range p) : Set ℕ) := by
      intro i hi j hj hij
      exact eq_of_zpowers_mul_pow_eq ha hb ha1 hab hba (Finset.mem_range.1 hi)
        (Finset.mem_range.1 hj) hij
    rw [h𝒟def, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
      Finset.card_range]
  exact ⟨h𝒟, hcard𝒟⟩

private theorem eq_of_mul_eq_of_index_eq {i j d e K : ℕ} (hi : 0 < i)
    (h1 : i * d = K) (h2 : j * e = K) (hij : i = j) : d = e := by
  have h : i * d = i * e := by
    calc i * d = K := h1
      _ = j * e := h2.symm
      _ = i * e := by rw [hij]
  exact Nat.mul_left_cancel hi h

private theorem ep2_index_pow {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (MulAut W)} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAp : ∀ x ∈ A, x ^ p = 1) (hfix : fixV A ⊓ (normHom A).ker = ⊥)
    (hcardK : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W)
    (𝒟 : Finset (Subgroup (MulAut W)))
    (h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p) (hcard𝒟 : 𝒟.card = p + 1)
    {a : MulAut W}
    (h𝒟idx : ∀ D, D ∈ 𝒟 → (fixV D).index = (fixV (Subgroup.zpowers a)).index)
    (haA : Subgroup.zpowers a ≤ A) :
    (fixV (Subgroup.zpowers a)).index =
      (Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker)) ^ p := by
  classical
  let c : ℕ := Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker)
  have hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker :=
    fun x hx k hk => map_ker_normHom (Subgroup.le_normalizer hx) hk
  have hcD : ∀ D ∈ 𝒟, Nat.card ↥(fixV D ⊓ (normHom A).ker) = c := by
    intro D hDmem
    have hrelD := index_mul_card_inf_ker_normHom_eq (A := A) (D := D)
      ((h𝒟 D).1 hDmem).1 hfix hcardK
    have hrela := index_mul_card_inf_ker_normHom_eq (A := A) (D := Subgroup.zpowers a)
      haA hfix hcardK
    exact eq_of_mul_eq_of_index_eq
      (by rw [Subgroup.index_eq_card]; exact Nat.card_pos) hrelD hrela (h𝒟idx D hDmem)
  have hprod : Nat.card ↥(normHom A).ker =
      ∏ D ∈ 𝒟, Nat.card ↥(fixV D ⊓ (normHom A).ker) :=
    card_eq_prod_card_fixV_inf_hyperplanes (W := W) hW (p := p) hp2 hAc hAp hKinv hfix 𝒟 h𝒟
  have hprodconst : ∏ D ∈ 𝒟, Nat.card ↥(fixV D ⊓ (normHom A).ker) = c ^ (p + 1) := by
    rw [Finset.prod_congr rfl hcD, Finset.prod_const, hcard𝒟]
  have hKc : Nat.card ↥(normHom A).ker = c ^ (p + 1) := by rw [hprod, hprodconst]
  have hrela : (fixV (Subgroup.zpowers a)).index * c = Nat.card ↥(normHom A).ker :=
    index_mul_card_inf_ker_normHom_eq (A := A) (D := Subgroup.zpowers a) haA hfix hcardK
  have h1 : (fixV (Subgroup.zpowers a)).index * c = c ^ p * c := by
    rw [hrela, hKc, pow_succ]
  exact Nat.mul_right_cancel Nat.card_pos h1

private theorem ep2_c_pow {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] {A : Subgroup (MulAut W)}
    {a b : MulAut W} (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hab : a * b = b * a) (hb : b ^ p = 1) (hbA : b ∈ A)
    (hfix : fixV A ⊓ (normHom A).ker = ⊥) :
    ∃ j : ℕ, Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker) =
      2 ^ (orderOf (2 : ZMod p) * j) := by
  classical
  let V : Subgroup W := fixV (Subgroup.zpowers a) ⊓ (normHom A).ker
  have hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker :=
    fun x hx k hk => map_ker_normHom (Subgroup.le_normalizer hx) hk
  have hbV : ∀ v ∈ V, b v ∈ V := by
    intro v hv
    obtain ⟨hvD, hvK⟩ := Subgroup.mem_inf.1 hv
    refine Subgroup.mem_inf.2 ⟨?_, hKinv b hbA v hvK⟩
    rw [mem_fixV_zpowers]
    have habv : a (b v) = b (a v) := by
      simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f v) hab
    rw [habv, mem_fixV_zpowers.1 hvD]
  have hbpV : ∀ v ∈ V, (b ^ p) v = v := by
    intro v _
    rw [hb, MulAut.one_apply]
  have hfpfV : ∀ v ∈ V, b v = v → v = 1 := by
    intro v hv hbv
    obtain ⟨hvD, hvK⟩ := Subgroup.mem_inf.1 hv
    have hvDb : v ∈ fixV (Subgroup.zpowers b) := by
      rw [mem_fixV_zpowers]
      exact hbv
    have hvA : v ∈ fixV A := by
      rw [hA, fixV_sup]
      exact Subgroup.mem_inf.2 ⟨hvD, hvDb⟩
    have hmem : v ∈ fixV A ⊓ (normHom A).ker := Subgroup.mem_inf.2 ⟨hvA, hvK⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    exact hmem
  exact exists_card_eq_two_pow_orderOf_mul_of_fixfree hW hbV hbpV hfpfV

theorem exists_index_eq_two_pow_mul_of_hyperplanes {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : MulAut W}
    (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < p, b ≠ a ^ j)
    (hD : ∀ D : Subgroup (MulAut W), D ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b →
      Nat.card D = p → (fixV D).index = (fixV (Subgroup.zpowers a)).index) :
    ∃ j : ℕ, (fixV (Subgroup.zpowers a)).index = 2 ^ (p * orderOf (2 : ZMod p) * j) := by
  classical
  let A : Subgroup (MulAut W) := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b := rfl
  have hb1 : b ≠ 1 := by
    have := hba 0 (Fact.out : p.Prime).pos
    simpa using this
  have hao : orderOf a = p := orderOf_eq_prime ha ha1
  have hbo : orderOf b = p := orderOf_eq_prime hb hb1
  have hcarda : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hao]
  have hcommXA : ∀ x ∈ Subgroup.zpowers a, x * b = b * x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (show Commute a b from hab) n).eq
  obtain ⟨hAea, hAsupcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := p)
      (X := Subgroup.zpowers a) (v := b) hcarda hbo
      (not_mem_zpowers_of_forall_ne_pow_lt (Fact.out : p.Prime).pos ha hba) hcommXA
  have hAcard : Nat.card ↥A = p ^ 2 := by simpa [A] using hAsupcard
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hAea.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : ∀ x ∈ A, x ^ p = 1 := hAea.2
  have hodd : Odd (Nat.card ↥A) := by
    rw [hAcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hfix : fixV A ⊓ (normHom A).ker = ⊥ := fixV_inf_ker_normHom hW hodd
  have hcardK : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W :=
    card_ker_normHom_mul hW hodd
  have haA : Subgroup.zpowers a ≤ A := by rw [hA]; exact le_sup_left
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    insert (Subgroup.zpowers b) ((Finset.range p).image fun i =>
      Subgroup.zpowers (a * b ^ i))
  have h𝒟def : 𝒟 = insert (Subgroup.zpowers b) ((Finset.range p).image fun i =>
      Subgroup.zpowers (a * b ^ i)) := rfl
  obtain ⟨h𝒟, hcard𝒟⟩ := ep2_lines_mem_iff hA ha hb ha1 hab hba hbo hAcard 𝒟 h𝒟def
  have h𝒟idx : ∀ D, D ∈ 𝒟 → (fixV D).index = (fixV (Subgroup.zpowers a)).index := by
    intro D hDmem
    obtain ⟨hDA, hDrel⟩ := (h𝒟 D).1 hDmem
    exact hD D hDA (card_eq_prime_of_le_of_relIndex hDA hDrel hAcard)
  have hidx := ep2_index_pow hW hp2 hAc hAp hfix hcardK 𝒟 h𝒟 hcard𝒟 h𝒟idx haA
  have hbA : b ∈ A := by
    rw [hA]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  obtain ⟨j, hj⟩ := ep2_c_pow hW hA hab hb hbA hfix
  refine ⟨j, ?_⟩
  calc (fixV (Subgroup.zpowers a)).index
      = (Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ (normHom A).ker)) ^ p := hidx
    _ = (2 ^ (orderOf (2 : ZMod p) * j)) ^ p := by rw [hj]
    _ = 2 ^ ((orderOf (2 : ZMod p) * j) * p) := by rw [← pow_mul]
    _ = 2 ^ (p * orderOf (2 : ZMod p) * j) := by
        congr 1
        ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
