module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Open.LocalVocabulary

import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LinearAlgebra.SL2CharTwoFixedVector

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped Matrix MatrixGroups commutatorElement

variable {G : Type*} [Group G] {F : Type*} [Field F]

private def conjOn (X : Subgroup G) (g : G) (hg : ∀ u ∈ X, g * u * g⁻¹ ∈ X) : ↥X →* ↥X where
  toFun u := ⟨g * u * g⁻¹, hg u u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem coe_conjOn (X : Subgroup G) (g : G) (hg : ∀ u ∈ X, g * u * g⁻¹ ∈ X) (u : ↥X) :
    ((conjOn X g hg u : ↥X) : G) = g * u * g⁻¹ := rfl

private theorem exists_addHom_conj {X : Subgroup G} {V : Type*} [AddCommGroup V]
    (γ : ↥X →* Multiplicative V) (hγ : Function.Surjective γ) {g : G}
    (hg : ∀ u ∈ X, g * u * g⁻¹ ∈ X)
    (hker : ∀ u : ↥X, γ u = 1 → γ (conjOn X g hg u) = 1) :
    ∃ A : V →+ V, ∀ u : ↥X,
      A (Multiplicative.toAdd (γ u)) = Multiplicative.toAdd (γ (conjOn X g hg u)) := by
  have hle : γ.ker ≤ (γ.comp (conjOn X g hg)).ker := fun u hu => by
    rw [MonoidHom.mem_ker] at hu ⊢
    exact hker u hu
  refine ⟨AddMonoidHom.toMultiplicative.symm
    (γ.liftOfSurjective hγ ⟨γ.comp (conjOn X g hg), hle⟩), fun u => ?_⟩
  change Multiplicative.toAdd ((γ.liftOfSurjective hγ ⟨γ.comp (conjOn X g hg), hle⟩)
    (Multiplicative.ofAdd (Multiplicative.toAdd (γ u)))) = _
  rw [ofAdd_toAdd]
  exact congrArg Multiplicative.toAdd
    (MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨γ.comp (conjOn X g hg), hle⟩ u)

private theorem conj_addHom_commute_SL2 {L E : Subgroup G}
    {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    {β : ↥E →* Multiplicative (Fin 2 → F)} (hβsurj : Function.Surjective β)
    (hβeq : ∀ (ℓ : ↥L) (u v : ↥E), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β u))
    {c : G} {hg : ∀ u ∈ E, c * u * c⁻¹ ∈ E}
    (hLE : ∀ ℓ : ↥L, ∀ u ∈ E, (ℓ : G) * u * (ℓ : G)⁻¹ ∈ E)
    (hcL : ∀ ℓ : ↥L, ∃ ℓ' : ↥L, (ℓ' : G) = c * ℓ * c⁻¹ ∧ α ℓ' = α ℓ)
    {A : (Fin 2 → F) →+ (Fin 2 → F)}
    (hA : ∀ u : ↥E, A (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β (conjOn E c hg u))) :
    ∀ (M : SL(2, F)) (w : Fin 2 → F),
      A ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ w) = (M : Matrix (Fin 2) (Fin 2) F) *ᵥ A w := by
  intro M w
  obtain ⟨ℓ, rfl⟩ := hα M
  obtain ⟨u, hu⟩ := hβsurj (Multiplicative.ofAdd w)
  obtain ⟨ℓ', hℓ', hαℓ'⟩ := hcL ℓ
  have hw : w = Multiplicative.toAdd (β u) := by rw [hu]; rfl
  have e1 := hβeq ℓ u (conjOn E ℓ (hLE ℓ) u) rfl
  have e2 := hβeq ℓ' (conjOn E c hg u) (conjOn E c hg (conjOn E ℓ (hLE ℓ) u)) (by
    simp only [coe_conjOn, Subgroup.coe_inv, hℓ']
    group)
  rw [hw, ← e1, hA, e2, hαℓ', ← hA]

private theorem conj_addHom_iterate {E : Subgroup G}
    {β : ↥E →* Multiplicative (Fin 2 → F)} {c : G} {hg : ∀ u ∈ E, c * u * c⁻¹ ∈ E}
    {A : (Fin 2 → F) →+ (Fin 2 → F)}
    (hA : ∀ u : ↥E, A (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β (conjOn E c hg u)))
    (hmem : ∀ (j : ℕ) (u : ↥E), c ^ j * (u : G) * (c ^ j)⁻¹ ∈ E)
    (j : ℕ) (u : ↥E) :
    A^[j] (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β ⟨c ^ j * (u : G) * (c ^ j)⁻¹, hmem j u⟩) := by
  induction j with
  | zero =>
    have h0 : (⟨c ^ 0 * (u : G) * (c ^ 0)⁻¹, hmem 0 u⟩ : ↥E) = u := Subtype.ext (by simp)
    rw [Function.iterate_zero_apply, h0]
  | succ j ih =>
    have h1 : conjOn E c hg ⟨c ^ j * (u : G) * (c ^ j)⁻¹, hmem j u⟩ =
        ⟨c ^ (j + 1) * (u : G) * (c ^ (j + 1))⁻¹, hmem (j + 1) u⟩ :=
      Subtype.ext (by simp only [coe_conjOn, pow_succ]; group)
    rw [Function.iterate_succ_apply', ih, hA, h1]

private theorem conj_addHom_eq_self [CharP F 2] {E : Subgroup G}
    {β : ↥E →* Multiplicative (Fin 2 → F)} (hβsurj : Function.Surjective β)
    {c : G} (hcE : c ∈ Subgroup.normalizer (E : Set G)) (hc2 : ∃ m : ℕ, c ^ 2 ^ m = 1)
    {hg : ∀ u ∈ E, c * u * c⁻¹ ∈ E} {A : (Fin 2 → F) →+ (Fin 2 → F)}
    (hA : ∀ u : ↥E, A (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β (conjOn E c hg u)))
    {z : F} (hz : ∀ v : Fin 2 → F, A v = z • v) : ∀ v : Fin 2 → F, A v = v := by
  have hmem : ∀ (j : ℕ) (u : ↥E), c ^ j * (u : G) * (c ^ j)⁻¹ ∈ E :=
    fun j u => (Subgroup.mem_normalizer_iff.mp (pow_mem hcE j) (u : G)).mp u.2
  have hScalar : ∀ (j : ℕ) (v : Fin 2 → F), A^[j] v = z ^ j • v := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, hz, smul_smul, pow_succ, mul_comm]
  obtain ⟨m, hm⟩ := hc2
  have hAiter : ∀ u : ↥E, A^[2 ^ m] (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β u) := by
    intro u
    rw [conj_addHom_iterate hA hmem (2 ^ m) u]
    have h1 : c ^ 2 ^ m * (u : G) * (c ^ 2 ^ m)⁻¹ = (u : G) := by rw [hm]; simp
    exact congrArg (fun x => Multiplicative.toAdd (β x)) (Subtype.ext h1)
  have hzpow : z ^ 2 ^ m = 1 := by
    obtain ⟨u₀, hu₀⟩ := hβsurj (Multiplicative.ofAdd (Pi.single 0 (1 : F) : Fin 2 → F))
    have hu₀' : Multiplicative.toAdd (β u₀) = Pi.single 0 (1 : F) := by rw [hu₀, toAdd_ofAdd]
    have h1 : A^[2 ^ m] (Multiplicative.toAdd (β u₀)) =
        z ^ 2 ^ m • Multiplicative.toAdd (β u₀) := hScalar (2 ^ m) _
    rw [hAiter u₀] at h1
    simpa [hu₀'] using congrFun h1.symm 0
  have hz1 : z = 1 := by
    have h0 : (z - 1) ^ 2 ^ m = 0 := by
      rw [sub_pow_char_pow, hzpow, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero m two_ne_zero)).mp h0)
  exact fun v => by rw [hz, hz1, one_smul]

theorem IsNatSecOf.mem_of_forall_commutator_mem {L E N : Subgroup G} {α : ↥L →* SL(2, F)}
    (h : IsNatSecOf L E N α) (hα : Function.Surjective α)
    (hLE : L ≤ Subgroup.normalizer (E : Set G)) {x : G} (hx : x ∈ E)
    (hxN : ∀ ℓ ∈ L, ℓ * x * ℓ⁻¹ * x⁻¹ ∈ N) : x ∈ N := by
  obtain ⟨β, _, hβker, hβeq⟩ := h
  have hmemN : ∀ u : ↥E, β u = 1 ↔ (u : G) ∈ N := by
    intro u
    rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
  set xe : ↥E := ⟨x, hx⟩
  suffices hβxe : β xe = 1 by exact (hmemN xe).mp hβxe
  have hfix : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) *ᵥ
      Multiplicative.toAdd (β xe) = Multiplicative.toAdd (β xe) := by
    intro g
    obtain ⟨ℓ, rfl⟩ := hα g
    set u : ↥E := ⟨ℓ * x * ℓ⁻¹, (Subgroup.mem_normalizer_iff.mp (hLE ℓ.2) x).mp hx⟩
    have hu_eq : β u = β xe := by
      have hdiff : u * xe⁻¹ ∈ β.ker := by
        rw [hβker, Subgroup.mem_subgroupOf]
        exact hxN ℓ ℓ.2
      rw [MonoidHom.mem_ker, map_mul, map_inv] at hdiff
      exact mul_inv_eq_one.mp hdiff
    have heq := hβeq ℓ xe u rfl
    rw [hu_eq] at heq
    exact heq.symm
  have h1 : Multiplicative.toAdd (β xe) 1 = 0 := by
    have hg := hfix ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
    rw [Matrix.SpecialLinearGroup.coe_mk, Matrix.mulVec_fin_two] at hg
    have h0 := congrFun hg 0
    simp at h0
    linear_combination h0
  have h0 : Multiplicative.toAdd (β xe) 0 = 0 := by
    have hg := hfix ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
    rw [Matrix.SpecialLinearGroup.coe_mk, Matrix.mulVec_fin_two] at hg
    have h0 := congrFun hg 1
    simp at h0
    linear_combination h0
  have hv : Multiplicative.toAdd (β xe) = 0 := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  exact toAdd_eq_zero.mp hv

theorem IsNatSecOf.mem_of_commute_of_odd [CharP F 2] {L E N : Subgroup G}
    {α : ↥L →* SL(2, F)} (h : IsNatSecOf L E N α) {k : ↥L} (hk : Odd (orderOf k))
    (hk1 : α k ≠ 1) {x : G} (hx : x ∈ E) (hkx : (k : G) * x = x * k) : x ∈ N := by
  obtain ⟨β, _, hβker, hβeq⟩ := h
  have hmemN : ∀ u : ↥E, β u = 1 ↔ (u : G) ∈ N := by
    intro u
    rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
  set xe : ↥E := ⟨x, hx⟩
  suffices hβxe : β xe = 1 by exact (hmemN xe).mp hβxe
  have hfix : (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β xe) =
      Multiplicative.toAdd (β xe) := by
    have hval : x = (k : G) * x * (k : G)⁻¹ := by
      rw [hkx, mul_assoc, mul_inv_cancel, mul_one]
    exact (hβeq k xe xe hval).symm
  by_contra hne
  have hv : Multiplicative.toAdd (β xe) ≠ 0 := fun h0 => hne (toAdd_eq_zero.mp h0)
  have hsq : (α k : Matrix (Fin 2) (Fin 2) F) * (α k : Matrix (Fin 2) (Fin 2) F) = 1 :=
    CFSG.LinearAlgebra.mul_self_eq_one_of_mulVec_eq_self _ (α k).2 hv hfix
  have hsq' : α k ^ 2 = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, hsq, Matrix.SpecialLinearGroup.coe_one]
  have h2 : orderOf (α k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq'
  have hdvd : orderOf (α k) ∣ orderOf k := orderOf_map_dvd α k
  have hg1 : orderOf (α k) = 1 := by
    have h := Nat.dvd_gcd h2 hdvd
    rw [Nat.coprime_two_left.mpr hk] at h
    exact Nat.dvd_one.mp h
  exact hk1 (orderOf_eq_one_iff.mp hg1)

theorem IsNatSecOf.commutatorElement_mem_of_conj [CharP F 2] {L E N : Subgroup G}
    {α : ↥L →* SL(2, F)} (h : IsNatSecOf L E N α) (hα : Function.Surjective α)
    (hLE : L ≤ Subgroup.normalizer (E : Set G)) {c : G} (hc2 : ∃ m : ℕ, c ^ 2 ^ m = 1)
    (hcE : c ∈ Subgroup.normalizer (E : Set G)) (hcN : ∀ x ∈ E, x ∈ N → c * x * c⁻¹ ∈ N)
    (hcL : ∀ ℓ : ↥L, ∃ ℓ' : ↥L, (ℓ' : G) = c * ℓ * c⁻¹ ∧ α ℓ' = α ℓ) :
    ∀ e ∈ E, ⁅c, e⁆ ∈ N := by
  obtain ⟨β, hβsurj, hβker, hβeq⟩ := h
  have hcE' : ∀ u ∈ E, c * u * c⁻¹ ∈ E :=
    fun u hu => (Subgroup.mem_normalizer_iff.mp hcE u).mp hu
  have hLE' : ∀ ℓ : ↥L, ∀ u ∈ E, (ℓ : G) * u * (ℓ : G)⁻¹ ∈ E :=
    fun ℓ u hu => (Subgroup.mem_normalizer_iff.mp (hLE ℓ.2) u).mp hu
  obtain ⟨A, hA⟩ := exists_addHom_conj β hβsurj hcE' (fun u hu => by
    have huN : (u : G) ∈ N := by
      rw [← Subgroup.mem_subgroupOf, ← hβker, MonoidHom.mem_ker]
      exact hu
    rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
    exact hcN u u.2 huN)
  have hAc := conj_addHom_commute_SL2 hα hβsurj hβeq hLE' hcL hA
  obtain ⟨z, hz⟩ := exists_eq_smul_of_commute_SL2 A hAc
  have hAz := conj_addHom_eq_self hβsurj hcE hc2 hA hz
  intro e he
  have hβfix : β (conjOn E c hcE' ⟨e, he⟩) = β ⟨e, he⟩ := by
    apply Multiplicative.toAdd.injective
    rw [← hA, hAz]
  have hmemN : (conjOn E c hcE' ⟨e, he⟩ * ⟨e, he⟩⁻¹ : ↥E) ∈ N.subgroupOf E := by
    rw [← hβker, MonoidHom.mem_ker, map_mul, map_inv, hβfix, mul_inv_cancel]
  have hN : ((conjOn E c hcE' ⟨e, he⟩ * ⟨e, he⟩⁻¹ : ↥E) : G) ∈ N :=
    Subgroup.mem_subgroupOf.mp hmemN
  have hv : ((conjOn E c hcE' ⟨e, he⟩ * ⟨e, he⟩⁻¹ : ↥E) : G) = c * e * c⁻¹ * e⁻¹ := by
    simp [coe_conjOn]
  rw [commutatorElement_def, ← hv]
  exact hN

theorem IsNatSecOf.commutatorElement_mem [CharP F 2] {L E N : Subgroup G}
    {α : ↥L →* SL(2, F)} (h : IsNatSecOf L E N α) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (hLE : L ≤ Subgroup.normalizer (E : Set G)) {c : G}
    (hc2 : ∃ m : ℕ, c ^ 2 ^ m = 1) (hcE : c ∈ Subgroup.normalizer (E : Set G))
    (hcN : ∀ x ∈ E, x ∈ N → c * x * c⁻¹ ∈ N) (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcq : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) :
    ∀ e ∈ E, ⁅c, e⁆ ∈ N := by
  refine h.commutatorElement_mem_of_conj hα hLE hc2 hcE hcN ?_
  intro ℓ
  have hconjL : c * (ℓ : G) * c⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hcL (ℓ : G)).mp ℓ.2
  refine ⟨⟨c * (ℓ : G) * c⁻¹, hconjL⟩, rfl, ?_⟩
  have hx : ((⟨c * (ℓ : G) * c⁻¹, hconjL⟩ : ↥L) * ℓ⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L :=
    (CFSG.mem_openPCoreOf_iff _).mp (hcq (ℓ : G) ℓ.2)
  have h1 : α ((⟨c * (ℓ : G) * c⁻¹, hconjL⟩ : ↥L) * ℓ⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hx
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

end CFSG.Quasithin.F112R.St84

end
