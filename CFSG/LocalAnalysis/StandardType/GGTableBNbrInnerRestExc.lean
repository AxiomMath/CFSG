module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley
  CFSG.RankThree.CentralCover TableB TableBSymp

namespace NbrInnerRest

section Refl

theorem cartanE_edge {r : ℕ} {i j : Fin r} (hij : i ≠ j)
    (h : (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨ (i.val = 1 ∧ j.val = 3) ∨
      (i.val = 3 ∧ j.val = 1) ∨ (2 ≤ i.val ∧ j.val = i.val + 1) ∨
      (2 ≤ j.val ∧ i.val = j.val + 1)) : Tag.cartanE r i j ≠ 0 := by
  unfold Tag.cartanE
  simp [hij, h]

theorem cartanE_entry (r : ℕ) (i j : Fin r) :
    Tag.cartanE r i j = 2 ∨ Tag.cartanE r i j = 0 ∨ Tag.cartanE r i j = -1 := by
  unfold Tag.cartanE
  split_ifs <;> simp

theorem cartanE_connected {r : ℕ} (hr : 4 ≤ r) (S : Finset (Fin r)) (hS : S.Nonempty)
    (hcl : ∀ i ∈ S, ∀ j, Tag.cartanE r i j ≠ 0 → j ∈ S) : S = Finset.univ := by
  have step : ∀ (a b : ℕ) (ha : a < r) (hb : b < r), a ≠ b →
      ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨
        (2 ≤ a ∧ b = a + 1) ∨ (2 ≤ b ∧ a = b + 1)) →
      (⟨a, ha⟩ : Fin r) ∈ S → (⟨b, hb⟩ : Fin r) ∈ S := by
    intro a b ha hb hab h haS
    exact hcl _ haS _ (cartanE_edge (i := ⟨a, ha⟩) (j := ⟨b, hb⟩)
      (fun e => hab (congrArg Fin.val e)) h)
  have h2 : (⟨2, by omega⟩ : Fin r) ∈ S := by
    obtain ⟨⟨i, hi⟩, hiS⟩ := hS
    have hdown : ∀ m, ∀ (hm : m + 2 < r), (⟨m + 2, hm⟩ : Fin r) ∈ S →
        (⟨2, by omega⟩ : Fin r) ∈ S := by
      intro m
      induction m with
      | zero => intro hm h; exact h
      | succ k ih =>
        intro hm h
        exact ih (by omega) (step (k + 1 + 2) (k + 2) hm (by omega) (by omega)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))) h)
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
    · exact step 0 2 hi (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩) hiS
    · have h3 := step 1 3 hi (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hiS
      exact step 3 2 (by omega) (by omega) (by omega)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨le_refl _, rfl⟩))))) h3
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
      exact hdown m hi hiS
  have hup : ∀ m, ∀ (hm : m + 2 < r), (⟨m + 2, hm⟩ : Fin r) ∈ S := by
    intro m
    induction m with
    | zero => intro hm; exact h2
    | succ k ih =>
      intro hm
      exact step (k + 2) (k + 1 + 2) (by omega) hm (by omega)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))) (ih (by omega))
  rw [Finset.eq_univ_iff_forall]
  rintro ⟨j, hj⟩
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
  · exact step 2 0 (by omega) hj (by omega) (Or.inr (Or.inl ⟨rfl, rfl⟩)) h2
  · exact step 3 1 (by omega) hj (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      (hup 1 (by omega))
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    exact hup m hj

theorem cartanE_entry_ne_zero {r p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i j : Fin r)
    (h : Tag.cartanE r i j ≠ 0) : ((Tag.cartanE r i j : ℤ) : ZMod p) ≠ 0 := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have h2 : (2 : ZMod p) ≠ 0 := fun h2 => hp2 (by
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rcases cartanE_entry r i j with h' | h' | h'
  · rw [h']
    exact_mod_cast h2
  · exact absurd h' h
  · rw [h']
    push_cast
    exact neg_ne_zero.mpr one_ne_zero

variable {p : ℕ} [NeZero p]

theorem eq_bot_or_eq_top_of_refl (τ : Tag) (hp : p.Prime)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hconn : ∀ S : Finset (Fin τ.rank), S.Nonempty →
      (∀ i ∈ S, ∀ j, τ.cartan i j ≠ 0 → j ∈ S) → S = Finset.univ)
    (hent : ∀ i j, τ.cartan i j ≠ 0 → ((τ.cartan i j : ℤ) : ZMod p) ≠ 0)
    (F : Subgroup (Multiplicative (Fin τ.rank → ZMod p)))
    (hinv : ∀ i v, Multiplicative.ofAdd v ∈ F →
      Multiplicative.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1) ∈ F) :
    F = ⊥ ∨ F = ⊤ := by
  classical
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  by_cases hF : F = ⊥
  · exact Or.inl hF
  right
  have hsmul : ∀ (i : Fin τ.rank) (b : ZMod p), b ≠ 0 →
      Multiplicative.ofAdd (b • (Pi.single i 1 : Fin τ.rank → ZMod p)) ∈ F →
      ∀ a : ZMod p, Multiplicative.ofAdd (a • (Pi.single i 1 : Fin τ.rank → ZMod p)) ∈ F := by
    intro i b hb hbF a
    obtain ⟨n, hn⟩ := NbrOrth.exists_pow_eq_of_ne_one hp (a := Multiplicative.ofAdd b)
      (fun h => hb (by simpa using congrArg Multiplicative.toAdd h)) (Multiplicative.ofAdd a)
    have hnb : n • b = a := by simpa using congrArg Multiplicative.toAdd hn
    have h := F.pow_mem hbF n
    rwa [← ofAdd_nsmul, ← smul_assoc, hnb] at h
  have hsub : ∀ v w : Fin τ.rank → ZMod p, Multiplicative.ofAdd v ∈ F →
      Multiplicative.ofAdd w ∈ F → Multiplicative.ofAdd (v - w) ∈ F := fun v w hv hw => by
    rw [ofAdd_sub, div_eq_mul_inv]
    exact F.mul_mem hv (F.inv_mem hw)
  have hcancel : ∀ v w : Fin τ.rank → ZMod p, v - (v - w) = w := fun v w => by abel
  obtain ⟨⟨x, hxF⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
  set v := Multiplicative.toAdd x with hv
  have hvF : Multiplicative.ofAdd v ∈ F := by rw [hv, ofAdd_toAdd]; exact hxF
  have hv0 : v ≠ 0 := by
    intro h
    apply hx1
    apply Subtype.ext
    change x = 1
    rw [← ofAdd_toAdd x, ← hv, h, ofAdd_zero]
  obtain ⟨i, hi⟩ : ∃ i, cartanFunctional τ p i v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    have hdet' : ((τ.cartan.map (Int.castRingHom (ZMod p))).transpose).det ≠ 0 := by
      rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        Int.coe_castRingHom]
      exact hdet.ne_zero
    have hmul : (τ.cartan.map (Int.castRingHom (ZMod p))).transpose.mulVec v = 0 := by
      funext j
      rw [Pi.zero_apply, ← h j, cartanFunctional_apply]
      simp [Matrix.mulVec, dotProduct]
    have := Fact.mk hp
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet' hmul
  have hiF : ∀ a : ZMod p,
      Multiplicative.ofAdd (a • (Pi.single i 1 : Fin τ.rank → ZMod p)) ∈ F := by
    refine hsmul i _ hi ?_
    have h := hsub v _ hvF (hinv i v hvF)
    rwa [hcancel] at h
  set S : Finset (Fin τ.rank) := Finset.univ.filter fun j =>
    ∀ a : ZMod p, Multiplicative.ofAdd (a • (Pi.single j 1 : Fin τ.rank → ZMod p)) ∈ F
    with hS
  have hSall : S = Finset.univ := by
    refine hconn S ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiF⟩⟩ ?_
    intro j hj k hjk
    have hjF := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hsmul k ((τ.cartan j k : ℤ) : ZMod p) (hent j k hjk) ?_⟩
    have h1 := hjF 1
    rw [one_smul] at h1
    have h := hsub _ _ h1 (hinv k _ h1)
    rwa [hcancel, cartanFunctional_single_apply] at h
  have hall : ∀ j (a : ZMod p),
      Multiplicative.ofAdd (a • (Pi.single j 1 : Fin τ.rank → ZMod p)) ∈ F := by
    intro j
    have hj : j ∈ S := hSall ▸ Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  rw [eq_top_iff]
  intro y _
  rw [← ofAdd_toAdd y, ← Finset.univ_sum_single (Multiplicative.toAdd y), ofAdd_sum]
  refine Subgroup.prod_mem _ fun j _ => ?_
  have := hall j (Multiplicative.toAdd y j)
  rwa [← Pi.single_smul', smul_eq_mul, mul_one] at this

end Refl

section Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem ggTorusReflElt_adjoint [Finite K] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hconn : ∀ S : Finset (Fin τ.rank), S.Nonempty →
      (∀ i ∈ S, ∀ j, τ.cartan i j ≠ 0 → j ∈ S) → S = Finset.univ)
    (hent : ∀ i j, τ.cartan i j ≠ 0 → ((τ.cartan i j : ℤ) : ZMod p) ≠ 0)
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank) (hT : GGExcToralRankInput τ K p) :
    GGTorusReflElt p τ.rank (adjointGroup τ K) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  intro E hE hr _
  obtain ⟨g, hg⟩ := hT E hE hr
  have hrange := TableBExc.range_chevTorus_eq_torusPow hζo hζ hdet hV
  have hmemE : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ (chevTorus τ ζ hζ).range := by
    intro x
    rw [hrange, ← hg]
    constructor
    · intro hx
      exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rintro ⟨y, hy, hyx⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : y = x := mul_left_cancel (mul_right_cancel hyx)
      exact this ▸ hy
  set e : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (chevTorus τ ζ hζ) with he
  have heapp : ∀ x, e x = g⁻¹ * chevTorus τ ζ hζ x * g := fun x => by
    rw [he, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  set n : Fin τ.rank → adjointGroup τ K := fun i =>
    g⁻¹ * ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ * g with hn
  have hrefl : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ =
      e (.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1)) := by
    intro i v
    rw [heapp, heapp, ← weylElt_conj_chevTorus ζ hζ i v, hn]
    group
  have heE : e.range = E := by
    ext x
    rw [MonoidHom.mem_range, hmemE]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [heapp]; group⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [heapp, hy]; group⟩
  refine ⟨τ.rank, e, cartanFunctional τ p, n, heE, fun i => cartanFunctional_single i,
    hrefl, fun E' hE' hinv => ?_⟩
  have hinvF : ∀ i v, Multiplicative.ofAdd v ∈ E'.comap e →
      Multiplicative.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1) ∈ E'.comap e := by
    intro i v hv
    rw [Subgroup.mem_comap, ← hrefl]
    exact hinv i _ hv
  have hEe : ∀ x ∈ E, ∃ y, e y = x := fun x hx => by
    rw [← heE] at hx
    exact hx
  rcases eq_bot_or_eq_top_of_refl τ hp hdet hconn hent _ hinvF with hbot | htop
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hEe x (hE' hx)
    have hy : y ∈ E'.comap e := hx
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy, map_one]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hE' fun x hx => ?_
    obtain ⟨y, rfl⟩ := hEe x hx
    have hy : y ∈ E'.comap e := htop ▸ Subgroup.mem_top y
    exact hy

end Adjoint

theorem ggTorusNbr_of_pow {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusNbr p r R {φ | φ ∈ I ∧ φ ^ p = 1}) : GGTorusNbr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  refine h L' ψ hψ hker hperf A hA (fun a ha => ?_) hr h3
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨φ, ⟨hφ, ?_⟩, hφa⟩
  have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [hk p l, hA.2 a ha]
  rfl

end NbrInnerRest

open NbrInnerRest

section Exc

variable {K : Type} [Field K]

theorem ggTorusNbr_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusNbr p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  ggTorusNbr_of_secElt hp (TableBExc.idImage_subset_inn_E8 K)
    (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (ggTorusSecElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ggTorusSecElt_of_reflElt hp hp2 (ggTorusReflElt_adjoint (τ := .E8) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8
          (Nat.coprime_one_left p))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E8 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq))))

theorem ggTorusNbr_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusNbr p 7 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) :=
  ggTorusNbr_of_secElt hp (TableBExc.idImage_subset_inn_E7 K)
    (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (ggTorusSecElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
      (ggTorusSecElt_of_reflElt hp hp2 (ggTorusReflElt_adjoint (τ := .E7) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E7
          ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E7 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2 hpq))))

theorem mem_range_conj_of_mem_recipeID_E6 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {φ : MulAut (TableBExc.RecipeGroup .E6 K)} (hφ : φ ∈ TableBExc.RecipeID .E6 K)
    (hφp : φ ^ p = 1) :
    φ ∈ Set.range (MulAut.conj : TableBExc.RecipeGroup .E6 K →*
      MulAut (TableBExc.RecipeGroup .E6 K)) := by
  set N := (MulAut.conj : TableBExc.RecipeGroup .E6 K →*
    MulAut (TableBExc.RecipeGroup .E6 K)).range with hN
  have h3 : (φ : MulAut (TableBExc.RecipeGroup .E6 K) ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact TableBExc.pow_three_mem_inn_of_mem_recipeID_E6 hφ
  have hp' : (φ : MulAut (TableBExc.RecipeGroup .E6 K) ⧸ N) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hφp, QuotientGroup.mk_one]
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  have h1 : orderOf (φ : MulAut (TableBExc.RecipeGroup .E6 K) ⧸ N) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hp') (orderOf_dvd_of_pow_eq_one h3)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem ggTorusNbr_E6 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusNbr p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggTorusNbr_of_pow (ggTorusNbr_of_secElt hp
    (fun _ hφ => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ.1 hφ.2)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (ggTorusSecElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggTorusSecElt_of_reflElt hp hp2 (ggTorusReflElt_adjoint (τ := .E6) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E6
          ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E6 hp hp3 hpq)
        (TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq)))))

theorem recipeChevalleyExc_torusNbr {τ : Tag} {n p : ℕ}
    (hτ : (τ = .E6 ∧ p ≠ 3) ∨ τ = .E7 ∨ τ = .E8) (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  rcases hτ with ⟨rfl, hp3⟩ | rfl | rfl
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 6,
      TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, ggTorusNbr_E6 hp hp2 hp3 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 7,
      TableBExc.ggTorusLift_E7 hp hp2 hpq, ggTorusNbr_E7 hp hp2 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 8,
      TableBExc.ggTorusLift_E8 hp hp2 hpq, ggTorusNbr_E8 hp hp2 hpq⟩

end Exc

@[expose] def GGTableBNbrInnerExcSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .E6 ∧ p ≠ 3) ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1

section Labels


theorem largeEvenLabelAll_torusNbr_excSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerExcSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with ⟨ht, hp3⟩ | ht | ht <;> dsimp only at ht hpn <;> subst ht
  · exact recipeChevalleyExc_torusNbr (τ := .E6) (Or.inl ⟨rfl, hp3⟩) hn hp hpn hQ
  · exact recipeChevalleyExc_torusNbr (τ := .E7) (Or.inr (Or.inl rfl)) hn hp hpn hQ
  · exact recipeChevalleyExc_torusNbr (τ := .E8) (Or.inr (Or.inr rfl)) hn hp hpn hQ

theorem ggTableBNbrInnerInputOn_excSplit :
    GGTableBNbrInnerInputOn GGTableBNbrInnerExcSplitLabel :=
  ggTableBNbrInnerInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbr_excSplit hp hlab h

end Labels

end CFSG.StandardType

end
