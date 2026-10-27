module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcW1
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.HardMathSupport.C14G2Three

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Torus
  CFSG.HardMathSupport.Timmesfeld.Torality

theorem cartan_self' (τ : Tag) (i : Fin τ.rank) : τ.cartan i i = 2 := by
  cases τ <;> revert i <;> decide

theorem dvd_of_dvd_reflect {τ : Tag} (i : Fin τ.rank) {v : Fin τ.rank → ℤ} {n : ℤ}
    (h : ∀ j, n ∣ reflect τ i v j) (j : Fin τ.rank) : n ∣ v j := by
  classical
  have hne : ∀ k, k ≠ i → n ∣ v k := fun k hk => by
    have := h k
    simpa [reflect, Pi.single_apply, hk] using this
  by_cases hj : j = i
  · subst hj
    have hi := h j
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at hi
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), cartan_self'] at hi
    have hs : n ∣ ∑ k ∈ Finset.univ.erase j, τ.cartan j k * v k :=
      Finset.dvd_sum fun k hk => dvd_mul_of_dvd_right (hne k (Finset.ne_of_mem_erase hk)) _
    have : v j = -(v j - (2 * v j + ∑ k ∈ Finset.univ.erase j, τ.cartan j k * v k)) -
        ∑ k ∈ Finset.univ.erase j, τ.cartan j k * v k := by ring
    rw [this]
    exact dvd_sub (dvd_neg.2 hi) hs
  · exact hne j hj

theorem not_forall_dvd_of_isRoot {τ : Tag} {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) {n : ℤ}
    (hn : ¬ IsUnit n) : ¬ ∀ j, n ∣ v j := by
  induction hv with
  | basis j =>
    intro h
    exact hn (isUnit_of_dvd_one (by simpa using h j))
  | reflect i _ ih => exact fun h => ih (dvd_of_dvd_reflect i h)

@[expose] noncomputable def rootDiagHom (τ : Tag) (K : Type) [Field K] :
    (Fin τ.rank → Kˣ) →* ModGL τ K where
  toFun := rootDiagUnit τ
  map_one' := C14W1.rootDiagUnit_one'
  map_mul' := C14W1.rootDiagUnit_mul'

@[expose] def rootCharHom (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) :
    (Fin τ.rank → Kˣ) →* Kˣ where
  toFun t := rootChar t α
  map_one' := rootChar_one_left α
  map_mul' s t := rootChar_mul_left s t α

@[expose] def mu3sq (τ : Tag) (K : Type) [Field K] : Subgroup (Fin τ.rank → Kˣ) where
  carrier := {b | ∀ j, b j ^ 3 = 1}
  one_mem' := fun _ => one_pow _
  mul_mem' := fun ha hb j => by rw [Pi.mul_apply, mul_pow, ha j, hb j, one_mul]
  inv_mem' := fun ha j => by rw [Pi.inv_apply, inv_pow, ha j, inv_one]

theorem card_mu3sq_le {K : Type} [Field K] (τ : Tag) :
    Nat.card (mu3sq τ K) ≤ Nat.card (rootsOfUnity 3 K) ^ τ.rank := by
  let f : mu3sq τ K → (Fin τ.rank → rootsOfUnity 3 K) :=
    fun b j => ⟨b.1 j, (mem_rootsOfUnity _ _).2 (b.2 j)⟩
  have hf : Function.Injective f := fun b b' h => Subtype.ext (funext fun j =>
    congrArg Subtype.val (congrFun h j))
  haveI : Finite (rootsOfUnity 3 K) := inferInstance
  calc Nat.card (mu3sq τ K) ≤ Nat.card (Fin τ.rank → rootsOfUnity 3 K) :=
        Nat.card_le_card_of_injective f hf
    _ = _ := by rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin τ.rank), Fintype.card_fin]

instance {K : Type} [Field K] {τ : Tag} : Finite (mu3sq τ K) := by
  let f : mu3sq τ K → (Fin τ.rank → rootsOfUnity 3 K) :=
    fun b j => ⟨b.1 j, (mem_rootsOfUnity _ _).2 (b.2 j)⟩
  exact Finite.of_injective f fun b b' h => Subtype.ext (funext fun j =>
    congrArg Subtype.val (congrFun h j))

theorem familyKernel_empty_G2_three {K : Type} [Field K] {ι : Type}
    (a : ι → Fin Tag.G2.rank → Kˣ) (ha : ∀ i j, a i j ^ 3 = 1)
    (hcard : 9 ≤ Nat.card (Subgroup.closure (Set.range fun i => rootDiagUnit Tag.G2 (a i)))) :
    familyKernel a = ∅ := by
  set φ := rootDiagHom Tag.G2 K
  have hφ : Function.Injective φ := C14W1.rootDiagUnit_injective'
  set C := Subgroup.closure (Set.range fun i => rootDiagUnit Tag.G2 (a i))
  have hgen : ∀ (H : Subgroup (Fin Tag.G2.rank → Kˣ)), (∀ i, a i ∈ H) → C ≤ H.map φ :=
    fun H hH => (Subgroup.closure_le _).2 fun _ ⟨i, hi⟩ => hi ▸ ⟨a i, hH i, rfl⟩
  have hCcomap : ∀ (H : Subgroup (Fin Tag.G2.rank → Kˣ)), (∀ i, a i ∈ H) → C.comap φ ≤ H :=
    fun H hH => (Subgroup.comap_mono (hgen H hH)).trans
      (Subgroup.comap_map_eq_self_of_injective hφ H).le
  have haP : ∀ i, a i ∈ mu3sq Tag.G2 K := fun i j => ha i j
  have hCP : C.comap φ ≤ mu3sq Tag.G2 K := hCcomap _ haP
  have hCcard : Nat.card (C.comap φ) = Nat.card C := by
    rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self]
    exact (hgen _ haP).trans (Subgroup.map_le_range _ _)
  have hPC : C.comap φ = mu3sq Tag.G2 K :=
    Subgroup.eq_of_le_of_card_ge hCP (by
      have h1 : Nat.card (mu3sq Tag.G2 K) ≤ Nat.card (rootsOfUnity 3 K) ^ 2 :=
        card_mu3sq_le (K := K) Tag.G2
      have h2 := card_rootsOfUnity (R := K) (k := 3)
      calc Nat.card (mu3sq Tag.G2 K) ≤ 3 ^ 2 := h1.trans (Nat.pow_le_pow_left h2 2)
        _ ≤ _ := by rw [hCcard]; exact hcard)
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 := by
    have h1 : Nat.card (mu3sq Tag.G2 K) ≤ Nat.card (rootsOfUnity 3 K) ^ 2 :=
      card_mu3sq_le (K := K) Tag.G2
    have h2 := card_rootsOfUnity (R := K) (k := 3)
    rw [← hPC, hCcard] at h1
    have : 9 ≤ Nat.card (rootsOfUnity 3 K) ^ 2 := hcard.trans h1
    by_contra hne
    have : Nat.card (rootsOfUnity 3 K) ≤ 2 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity 3 K) 3 (by rw [hμ])
  have hζ' : orderOf (ζ : Kˣ) = 3 := by rw [Subgroup.orderOf_coe, hζ]
  ext α
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hα
  have hker : mu3sq Tag.G2 K ≤ (rootCharHom Tag.G2 K α).ker := by
    rw [← hPC]
    exact hCcomap _ fun i => hα.2 i
  apply not_forall_dvd_of_isRoot hα.1 (n := 3) (by decide)
  intro j
  have hb : Function.update (1 : Fin Tag.G2.rank → Kˣ) j (ζ : Kˣ) ∈ mu3sq Tag.G2 K := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; exact (mem_rootsOfUnity _ _).1 ζ.2
    · rw [Function.update_of_ne hk, Pi.one_apply, one_pow]
  have h1 : rootChar (Function.update (1 : Fin Tag.G2.rank → Kˣ) j (ζ : Kˣ)) α = 1 := hker hb
  rw [C14W1.rootChar_update_one] at h1
  have := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hζ'] at this
  exact_mod_cast this

end CFSG.HardMathSupport.C14G2Three
