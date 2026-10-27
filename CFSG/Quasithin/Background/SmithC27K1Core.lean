module

public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Module

open G6

variable {n : ℕ}

private theorem zmod_two_add_eq_zero_iff : ∀ x y : ZMod 2, x + y = 0 ↔ x = y := by decide

private theorem multiplicative_zmod_two_cases :
    ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide

private def pairVec (i j : Fin n) : PermMod n :=
  Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1)

private theorem toAdd_pairVec (i j k : Fin n) :
    Multiplicative.toAdd (pairVec i j) k =
      (Pi.single i 1 : Fin n → ZMod 2) k + (Pi.single j 1 : Fin n → ZMod 2) k := rfl

private theorem pairVec_mem_coreMod (i j : Fin n) : pairVec i j ∈ coreMod n := by
  rw [mem_coreMod]
  simp only [toAdd_pairVec, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  decide

private theorem permAct_pairVec (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permAct n σ (pairVec i j) = pairVec (σ i) (σ j) := by
  apply Multiplicative.toAdd.injective
  funext k
  rw [permAct_apply, toAdd_pairVec, toAdd_pairVec]
  simp only [Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

private theorem coreAct_swap_eq_iff {p q : Fin n} (x : coreMod n) :
    coreAct n (Equiv.swap p q) x = x ↔
      Multiplicative.toAdd (x : PermMod n) p = Multiplicative.toAdd (x : PermMod n) q := by
  constructor
  · intro h
    have h1 := congrArg (fun y : coreMod n => Multiplicative.toAdd (y : PermMod n) p) h
    simp only [coreAct_coe, permAct_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [coreAct_coe, permAct_apply, Equiv.swap_inv]
    by_cases hip : i = p
    · subst hip
      rw [Equiv.swap_apply_left]
      exact h.symm
    · by_cases hiq : i = q
      · subst hiq
        rw [Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]

private theorem coreAct_pairVec_ne {π : Equiv.Perm (Fin n)} {f e : Fin n} (hfe : f ≠ e)
    (he : π e = e) (hf : π f ≠ f) :
    coreAct n π ⟨pairVec f e, pairVec_mem_coreMod f e⟩ ≠
      ⟨pairVec f e, pairVec_mem_coreMod f e⟩ := by
  intro h
  have h1 := congrArg (fun y : coreMod n => Multiplicative.toAdd (y : PermMod n) f) h
  simp only [coreAct_coe, permAct_pairVec, he, toAdd_pairVec] at h1
  rw [Pi.single_eq_of_ne (Ne.symm hf), Pi.single_eq_of_ne hfe, Pi.single_eq_same] at h1
  exact absurd h1 (by decide)

private theorem coreAct_eq_of_vanish {p q e : Fin n} {c : Equiv.Perm (Fin n)}
    (hc : ∀ i, i ≠ p → i ≠ q → i ≠ e → c⁻¹ i = i)
    (hcp : c⁻¹ p = p ∨ c⁻¹ p = q ∨ c⁻¹ p = e) (hcq : c⁻¹ q = p ∨ c⁻¹ q = q ∨ c⁻¹ q = e)
    (hce : c⁻¹ e = p ∨ c⁻¹ e = q ∨ c⁻¹ e = e) (w : coreMod n)
    (hw : Multiplicative.toAdd (w : PermMod n) p = 0 ∧ Multiplicative.toAdd (w : PermMod n) q = 0 ∧
      Multiplicative.toAdd (w : PermMod n) e = 0) :
    coreAct n c w = w := by
  obtain ⟨hwp, hwq, hwe⟩ := hw
  have hzero : ∀ j, (j = p ∨ j = q ∨ j = e) → Multiplicative.toAdd (w : PermMod n) j = 0 := by
    rintro j (rfl | rfl | rfl)
    · exact hwp
    · exact hwq
    · exact hwe
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  rw [coreAct_coe, permAct_apply]
  by_cases hip : i = p
  · subst hip
    rw [hzero _ hcp, hwp]
  · by_cases hiq : i = q
    · subst hiq
      rw [hzero _ hcq, hwq]
    · by_cases hie : i = e
      · subst hie
        rw [hzero _ hce, hwe]
      · rw [hc i hip hiq hie]

private theorem vanish_mul_inv_coreAct {p q e : Fin n} {π : Equiv.Perm (Fin n)}
    (hπp : π⁻¹ p = p ∨ π⁻¹ p = q) (hπq : π⁻¹ q = p ∨ π⁻¹ q = q) (hπe : π⁻¹ e = e)
    (v : coreMod n) (hv : Multiplicative.toAdd (v : PermMod n) p =
      Multiplicative.toAdd (v : PermMod n) q) :
    Multiplicative.toAdd ((v * (coreAct n π v)⁻¹ : coreMod n) : PermMod n) p = 0 ∧
      Multiplicative.toAdd ((v * (coreAct n π v)⁻¹ : coreMod n) : PermMod n) q = 0 ∧
      Multiplicative.toAdd ((v * (coreAct n π v)⁻¹ : coreMod n) : PermMod n) e = 0 := by
  have key : ∀ i, Multiplicative.toAdd ((v * (coreAct n π v)⁻¹ : coreMod n) : PermMod n) i =
      Multiplicative.toAdd (v : PermMod n) i - Multiplicative.toAdd (v : PermMod n) (π⁻¹ i) := by
    intro i
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coreAct_coe, toAdd_mul, toAdd_inv, Pi.add_apply,
      Pi.neg_apply, permAct_apply, sub_eq_add_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [key]
    rcases hπp with h | h <;> rw [h] <;> simp [hv]
  · rw [key]
    rcases hπq with h | h <;> rw [h] <;> simp [hv]
  · rw [key, hπe, sub_self]

private theorem eq_one_of_forall_alternatingGroup (hn : Odd n) (h3 : 2 < n) (v : coreMod n)
    (hv : ∀ σ ∈ alternatingGroup (Fin n), coreAct n σ v = v) : v = 1 := by
  have hconst : ∀ i j : Fin n,
      Multiplicative.toAdd (v : PermMod n) i = Multiplicative.toAdd (v : PermMod n) j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j h3
    have hσ : Equiv.swap i k * Equiv.swap i j ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hki),
        Equiv.Perm.sign_swap hij]
      decide
    have h1 := congrArg (fun y : coreMod n => Multiplicative.toAdd (y : PermMod n) j) (hv _ hσ)
    simp only [coreAct_coe, permAct_apply, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm hkj), Equiv.swap_apply_right] at h1
    exact h1
  have hsum := (mem_coreMod.mp v.2)
  have hc : ∀ i, Multiplicative.toAdd (v : PermMod n) i =
      Multiplicative.toAdd (v : PermMod n) ⟨0, by omega⟩ := fun i => hconst i _
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn1 : (n : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp hn, Nat.cast_one]
  rw [hn1, one_mul] at hsum
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  rw [hc i, hsum]
  rfl

end Module

section Perm

variable {n : ℕ}

private theorem perm_pair_of_commute {p q : Fin n} (hpq : p ≠ q) {π : Equiv.Perm (Fin n)}
    (h : π * Equiv.swap p q = Equiv.swap p q * π) :
    (π p = p ∧ π q = q) ∨ (π p = q ∧ π q = p) := by
  have hs : Equiv.swap (π p) (π q) = Equiv.swap p q := by
    rw [Equiv.swap_apply_apply, h, mul_inv_cancel_right]
  have h1 : Equiv.swap p q (π p) = π q := by
    rw [← hs, Equiv.swap_apply_left]
  by_cases hp : π p = p
  · left
    refine ⟨hp, ?_⟩
    rw [← h1, hp, Equiv.swap_apply_left]
  · by_cases hq : π p = q
    · right
      refine ⟨hq, ?_⟩
      rw [← h1, hq, Equiv.swap_apply_right]
    · exfalso
      rw [Equiv.swap_apply_of_ne_of_ne hp hq] at h1
      exact hpq (π.injective h1)

private theorem perm_eq_one_or_swap {p q : Fin n} {π : Equiv.Perm (Fin n)}
    (h : (π p = p ∧ π q = q) ∨ (π p = q ∧ π q = p)) (hf : ∀ f, f ≠ p → f ≠ q → π f = f) :
    π = 1 ∨ π = Equiv.swap p q := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · left
    ext f
    by_cases hfp : f = p
    · rw [hfp, hp]; rfl
    · by_cases hfq : f = q
      · rw [hfq, hq]; rfl
      · rw [hf f hfp hfq]; rfl
  · right
    ext f
    by_cases hfp : f = p
    · rw [hfp, hp, Equiv.swap_apply_left]
    · by_cases hfq : f = q
      · rw [hfq, hq, Equiv.swap_apply_right]
      · rw [hf f hfp hfq, Equiv.swap_apply_of_ne_of_ne hfp hfq]

private theorem cycle_mem_alternatingGroup {p q e : Fin n} (hpq : p ≠ q) (hep : e ≠ p) :
    Equiv.swap p e * Equiv.swap p q ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hep),
    Equiv.Perm.sign_swap hpq]
  decide

private theorem cycle_mul_swap_ne {p q e : Fin n} (hpq : p ≠ q) (hep : e ≠ p) (heq : e ≠ q) :
    Equiv.swap p e * Equiv.swap p q * Equiv.swap p q ≠
      Equiv.swap p q * (Equiv.swap p e * Equiv.swap p q) := by
  intro h
  have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => σ q) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hpq) (Ne.symm heq),
    Equiv.swap_apply_of_ne_of_ne hep heq] at h1
  exact heq h1.symm

private theorem cycle_inv_apply {p q e : Fin n} (hpq : p ≠ q) (hep : e ≠ p) (heq : e ≠ q) :
    (Equiv.swap p e * Equiv.swap p q)⁻¹ p = e ∧ (Equiv.swap p e * Equiv.swap p q)⁻¹ q = p ∧
      (Equiv.swap p e * Equiv.swap p q)⁻¹ e = q ∧
      ∀ i, i ≠ p → i ≠ q → i ≠ e → (Equiv.swap p e * Equiv.swap p q)⁻¹ i = i := by
  simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
  refine ⟨?_, ?_, ?_, fun i hip hiq hie => ?_⟩
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hep heq]
  · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hpq) (Ne.symm heq), Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne hip hie, Equiv.swap_apply_of_ne_of_ne hip hiq]

private theorem exists_fixed_of_isPGroup {P : Subgroup (Equiv.Perm (Fin n))} (hP : IsPGroup 2 P)
    (hn : Odd n) {p q : Fin n} (hpq : p ≠ q) (hs : Equiv.swap p q ∈ P) :
    ∃ e : Fin n, e ≠ p ∧ e ≠ q ∧ ∀ π ∈ P, π e = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.not_even_iff_odd.mpr hn ∘ even_iff_two_dvd.mpr
  obtain ⟨e, he⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Fin n) hnd
  have hfix : ∀ π ∈ P, π e = e := fun π hπ => he ⟨π, hπ⟩
  have hse := hfix _ hs
  refine ⟨e, fun hep => ?_, fun heq => ?_, hfix⟩
  · rw [hep, Equiv.swap_apply_left] at hse
    exact hpq hse.symm
  · rw [heq, Equiv.swap_apply_right] at hse
    exact hpq hse

end Perm

section Conj

variable {G : Type} [Group G]

private theorem conjAct_apply_coe' {V : Subgroup G} (g : ↥(Subgroup.normalizer (V : Set G)))
    (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = (g : G) * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

private theorem conjAct_eq_one_iff' {V : Subgroup G}
    (g : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

private theorem conjAct_mem_autOn {V Y : Subgroup G} (y : ↥(Subgroup.normalizer (V : Set G)))
    (hy : (y : G) ∈ Y) : conjAct V y ∈ autOn Y V :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)

private theorem exists_of_mem_autOn {V Y : Subgroup G} {g : MulAut ↥V} (hg : g ∈ autOn Y V) :
    ∃ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ Y ∧ conjAct V y = g := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩

private noncomputable def starOf {V Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) {x : G} (hx : x ∈ Y) : ↥(autOn Y V) :=
  ⟨conjAct V ⟨x, hY hx⟩, conjAct_mem_autOn _ hx⟩

private theorem coe_starOf {V Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (V : Set G)) {x : G}
    (hx : x ∈ Y) : ((starOf hY hx : ↥(autOn Y V)) : MulAut ↥V) = conjAct V ⟨x, hY hx⟩ := rfl

private theorem starOf_eq_one_iff {V Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) {x : G} (hx : x ∈ Y) :
    starOf hY hx = 1 ↔ x ∈ Subgroup.centralizer (V : Set G) := by
  rw [← conjAct_eq_one_iff' ⟨x, hY hx⟩, ← coe_starOf hY hx]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

private theorem eq_one_or_eq_of_mem_zpowers {Γ : Type*} [Group Γ] {g x : Γ} (hg : g * g = 1)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

end Conj

section Elem

variable {G : Type} [Group G] [Finite G]

private theorem le_of_isMaxElemAbelian' {S A U : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hUS : U ≤ S) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hUA : U ≤ Subgroup.centralizer (A : Set G)) :
    U ≤ A := by
  rw [eq_omegaOneOf_centralizer hA]
  intro u hu
  exact Subgroup.subset_closure ⟨⟨hUS hu, hUA hu⟩, hU2 u hu⟩

omit [Finite G] in
private theorem characteristic_commutator_subgroupOf' {P E : Subgroup G} (hEP : E ≤ P)
    (hE : (E.subgroupOf P).Characteristic) : ((⁅E, P⁆).subgroupOf P).Characteristic := by
  have h : (⁅E, P⁆).subgroupOf P = ⁅E.subgroupOf P, (⊤ : Subgroup P)⁆ := by
    have hmap : ⁅E.subgroupOf P, (⊤ : Subgroup P)⁆.map P.subtype = ⁅E, P⁆ := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEP,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hmap, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  rw [h]
  infer_instance

end Elem

section Main

variable {G : Type} [Group G] [Finite G]

theorem autOn_eq_zpowers_of_k1 {H R M K V U : Subgroup G} (h : Hyp27 H R M K)
    (hV : V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))
    (hQ : pCoreOf 2 (K ⊔ R) = R ⊓ Subgroup.centralizer (V : Set G))
    (hUV : U ≤ V) (hUn : K ⊔ R ≤ Subgroup.normalizer (U : Set G))
    (hQU : pCoreOf 2 (K ⊔ R) ≤ U ⊔ (pCoreOf 2 (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G)))
    {n : ℕ} (hn : Odd n) (ι : ↥(autOn (K ⊔ R) V) →* Equiv.Perm (Fin n))
    (hι : Function.Injective ι)
    (hιK : ∀ σ ∈ alternatingGroup (Fin n),
      ∃ g : ↥(autOn (K ⊔ R) V), (g : MulAut ↥V) ∈ autOn K V ∧ ι g = σ)
    (θ : ↥U ≃* ↥(G6.coreMod n))
    (hθ : ∀ (g : ↥(autOn (K ⊔ R) V)) (u : ↥U)
      (hgu : (((g : MulAut ↥V) ⟨u, hUV u.2⟩ : ↥V) : G) ∈ U),
      θ ⟨_, hgu⟩ = G6.coreAct n (ι g) (θ u))
    (τ : ↥(autOn (K ⊔ R) V)) {p q : Fin n} (hpq : p ≠ q) (hτ : ι τ = Equiv.swap p q)
    (hJ : autOn (thompsonJ R) V = Subgroup.zpowers (τ : MulAut ↥V))
    (hMK : ∀ g ∈ autOn (M ⊓ K) V, g * (τ : MulAut ↥V) = (τ : MulAut ↥V) * g) :
    autOn R V = Subgroup.zpowers (τ : MulAut ↥V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) :=
    hV ▸ le_normalizer_omegaOneCenterOf_pCoreOf _
  have hVQ : V ≤ pCoreOf 2 (K ⊔ R) := hV ▸ A4.omegaOneCenterOf_le _
  have hVc : V ≤ Subgroup.centralizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    hV ▸ ((A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _))
  have hVe : IsElemAbelian 2 V := hV ▸ isElemAbelian_omegaOneCenterOf _
  have hQR : pCoreOf 2 (K ⊔ R) ≤ R := hQ ▸ inf_le_left
  have hUQ : U ≤ pCoreOf 2 (K ⊔ R) := hUV.trans hVQ
  have hUR : U ≤ R := hUQ.trans hQR
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := fun u hu => hVe.2 u (hUV hu)
  have hUc : U ≤ Subgroup.centralizer (pCoreOf 2 (K ⊔ R) : Set G) := hUV.trans hVc
  have hRX : R ≤ K ⊔ R := le_sup_right
  have hKX : K ≤ K ⊔ R := le_sup_left
  have h3 : 2 < n := by
    have hp := p.isLt
    have hq := q.isLt
    have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    have h2 : n ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hn) even_two
    omega
  have hconjU : ∀ x ∈ K ⊔ R, ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.mp (hUn hx) u).mp hu
  have hθc : ∀ (x : G) (hx : x ∈ K ⊔ R) (u : ↥U),
      θ ⟨x * u * x⁻¹, hconjU x hx u u.2⟩ = G6.coreAct n (ι (starOf hXV hx)) (θ u) := by
    intro x hx u
    have hgu : ((((starOf hXV hx : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) ⟨u, hUV u.2⟩ : ↥V) : G) ∈
        U := by
      rw [coe_starOf, conjAct_apply_coe']
      exact hconjU x hx u u.2
    rw [← hθ (starOf hXV hx) u hgu]
    congr 1
  have hcomm_iff : ∀ (x : G) (hx : x ∈ K ⊔ R) (u : ↥U),
      x * u * x⁻¹ = u ↔ G6.coreAct n (ι (starOf hXV hx)) (θ u) = θ u := by
    intro x hx u
    rw [← hθc x hx u]
    constructor
    · intro h1
      congr 1
      exact Subtype.ext h1
    · intro h1
      exact congrArg Subtype.val (θ.injective h1)
  have hτ2 : (τ : MulAut ↥V) * τ = 1 := by
    have h1 : τ * τ = 1 := hι (by rw [map_mul, hτ, map_one, Equiv.swap_mul_self])
    exact congrArg Subtype.val h1
  have hτ1 : (τ : MulAut ↥V) ≠ 1 := by
    intro h1
    have h2 : τ = 1 := Subtype.ext h1
    have h3 := congrArg (fun σ : Equiv.Perm (Fin n) => σ p) (hτ.symm.trans (by rw [h2, map_one]))
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h3
    exact hpq h3.symm
  have hzp : ∀ g : MulAut ↥V, g ∈ Subgroup.zpowers (τ : MulAut ↥V) → g = 1 ∨ g = τ :=
    fun g hg => eq_one_or_eq_of_mem_zpowers hτ2 hg
  have hJR : thompsonJ R ≤ K ⊔ R := (B6.thompsonJ_le R).trans hRX
  have hJst : ∀ (y : G) (hy : y ∈ thompsonJ R),
      starOf hXV (hJR hy) = 1 ∨ starOf hXV (hJR hy) = τ := by
    intro y hy
    have hmem : conjAct V ⟨y, hXV (hJR hy)⟩ ∈ autOn (thompsonJ R) V := conjAct_mem_autOn _ hy
    rw [hJ] at hmem
    rcases hzp _ hmem with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  have hιJ : ∀ (y : G) (hy : y ∈ thompsonJ R),
      ι (starOf hXV (hJR hy)) = 1 ∨ ι (starOf hXV (hJR hy)) = Equiv.swap p q := by
    intro y hy
    rcases hJst y hy with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1, hτ])
  have hτJ : (τ : MulAut ↥V) ∈ autOn (thompsonJ R) V := hJ ▸ Subgroup.mem_zpowers _
  obtain ⟨y₀, hy₀J, hy₀τ⟩ := exists_of_mem_autOn hτJ
  have hRcomm : ∀ (r : G) (hr : r ∈ R),
      starOf hXV (hRX hr) * τ = τ * starOf hXV (hRX hr) := by
    intro r hr
    have hry : r * y₀ * r⁻¹ ∈ thompsonJ R :=
      (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_thompsonJ R hr) _).mp hy₀J
    have hmem : conjAct V ⟨r * y₀ * r⁻¹, hXV (hJR hry)⟩ ∈ autOn (thompsonJ R) V :=
      conjAct_mem_autOn _ hry
    have heq : conjAct V ⟨r * y₀ * r⁻¹, hXV (hJR hry)⟩ =
        conjAct V ⟨r, hXV (hRX hr)⟩ * (τ : MulAut ↥V) * (conjAct V ⟨r, hXV (hRX hr)⟩)⁻¹ := by
      rw [← hy₀τ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hJ, heq] at hmem
    apply Subtype.ext
    show conjAct V ⟨r, hXV (hRX hr)⟩ * (τ : MulAut ↥V) = τ * conjAct V ⟨r, hXV (hRX hr)⟩
    rcases hzp _ hmem with h1 | h1
    · exfalso
      apply hτ1
      have h2 := congrArg (fun z => (conjAct V ⟨r, hXV (hRX hr)⟩)⁻¹ * z *
        conjAct V ⟨r, hXV (hRX hr)⟩) h1
      simpa [mul_assoc] using h2
    · exact mul_inv_eq_iff_eq_mul.mp h1
  have hRpair : ∀ (r : G) (hr : r ∈ R),
      (ι (starOf hXV (hRX hr)) p = p ∧ ι (starOf hXV (hRX hr)) q = q) ∨
        (ι (starOf hXV (hRX hr)) p = q ∧ ι (starOf hXV (hRX hr)) q = p) := by
    intro r hr
    apply perm_pair_of_commute hpq
    rw [← hτ, ← map_mul, ← map_mul, hRcomm r hr]
  have hRs2 : IsPGroup 2 (autOn R V) := h.isPGroup.comap_subtype.map (conjAct V)
  have hP2 : IsPGroup 2 (((autOn R V).subgroupOf (autOn (K ⊔ R) V)).map ι) :=
    hRs2.comap_subtype.map ι
  have hτR : (τ : MulAut ↥V) ∈ autOn R V := autOn_le_autOn V (B6.thompsonJ_le R) hτJ
  have hsP : Equiv.swap p q ∈ ((autOn R V).subgroupOf (autOn (K ⊔ R) V)).map ι :=
    ⟨τ, Subgroup.mem_subgroupOf.mpr hτR, hτ⟩
  obtain ⟨e, hep, heq, he⟩ := exists_fixed_of_isPGroup hP2 hn hpq hsP
  have hRe : ∀ (r : G) (hr : r ∈ R), ι (starOf hXV (hRX hr)) e = e := fun r hr =>
    he _ ⟨starOf hXV (hRX hr), Subgroup.mem_subgroupOf.mpr (conjAct_mem_autOn _ hr), rfl⟩
  obtain ⟨A, hA, hAc⟩ : ∃ A : Subgroup G, IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hne
    push Not at hne
    apply hτ1
    have hJc : thompsonJ R ≤ Subgroup.centralizer (V : Set G) := iSup₂_le fun A hA => hne A hA
    obtain ⟨y, hy, hyτ⟩ := exists_of_mem_autOn hτJ
    rw [← hyτ]
    exact (conjAct_eq_one_iff' y).mpr (hJc hy)
  obtain ⟨a, haA, haC⟩ := Set.not_subset.mp hAc
  have haJ : a ∈ thompsonJ R := B6.le_thompsonJ hA haA
  have haX : a ∈ K ⊔ R := hJR haJ
  have hsta : starOf hXV haX = τ := by
    rcases hJst a haJ with h1 | h1
    · exact absurd ((starOf_eq_one_iff hXV haX).mp h1) haC
    · exact h1
  have hιa : ι (starOf hXV haX) = Equiv.swap p q := by rw [hsta, hτ]
  set U₀ : Subgroup G := U ⊓ Subgroup.centralizer (thompsonJ R : Set G) with hU₀
  have hU₀_iff : ∀ u : ↥U, (u : G) ∈ U₀ ↔
      Multiplicative.toAdd ((θ u : ↥(G6.coreMod n)) : G6.PermMod n) p =
        Multiplicative.toAdd ((θ u : ↥(G6.coreMod n)) : G6.PermMod n) q := by
    intro u
    constructor
    · rintro ⟨-, hu⟩
      have h1 : a * u * a⁻¹ = u := by
        rw [Subgroup.mem_centralizer_iff.mp hu a haJ, mul_inv_cancel_right]
      rw [hcomm_iff a haX u, hιa] at h1
      exact (coreAct_swap_eq_iff _).mp h1
    · intro hu
      refine ⟨u.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h1 : y * u * y⁻¹ = u := by
        rw [hcomm_iff y (hJR hy) u]
        rcases hιJ y hy with h2 | h2
        · rw [h2, map_one, MulAut.one_apply]
        · rw [h2]
          exact (coreAct_swap_eq_iff _).mpr hu
      calc y * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [h1]
  have hU₀A : U₀ ≤ A := le_of_isMaxElemAbelian' hA (inf_le_left.trans hUR)
    (fun u hu => hU2 u hu.1)
    (fun u hu => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (B6.le_thompsonJ hA)) hu.2)
  have hUA : U ⊓ A ≤ U₀ := by
    rintro u ⟨huU, huA⟩
    have h1 : a * u * a⁻¹ = u := by
      rw [B2F.isElemAbelian_comm hA.2.1 haA huA, mul_inv_cancel_right]
    have h2 := (hcomm_iff a haX ⟨u, huU⟩).mp h1
    rw [hιa] at h2
    exact (hU₀_iff ⟨u, huU⟩).mpr ((coreAct_swap_eq_iff _).mp h2)
  have hUAeq : U ⊓ A = U₀ := le_antisymm hUA (le_inf inf_le_left hU₀A)
  set Z₁ : Subgroup G := omegaOneCenterOf (thompsonJ R) with hZ₁
  have hU₀Z : U₀ ≤ Z₁ := fun u hu =>
    Subgroup.subset_closure ⟨⟨B6.le_thompsonJ hA (hU₀A hu), hu.2⟩, hU2 u hu.1⟩
  let lam : ↥U →* Multiplicative (ZMod 2) :=
    { toFun := fun u => Multiplicative.ofAdd
        (Multiplicative.toAdd ((θ u : ↥(G6.coreMod n)) : G6.PermMod n) p +
          Multiplicative.toAdd ((θ u : ↥(G6.coreMod n)) : G6.PermMod n) q)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, Subgroup.coe_mul, toAdd_mul, Pi.add_apply]
        rw [← ofAdd_add]
        congr 1
        ring }
  have hlam : ∀ u : ↥U, lam u = Multiplicative.ofAdd
      (Multiplicative.toAdd ((θ u : ↥(G6.coreMod n)) : G6.PermMod n) p +
        Multiplicative.toAdd ((θ u : ↥(G6.coreMod n)) : G6.PermMod n) q) := fun _ => rfl
  have hker : lam.ker = U₀.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hU₀_iff u, hlam, ofAdd_eq_one]
    exact zmod_two_add_eq_zero_iff _ _
  have hsurj : Function.Surjective lam := by
    have h1 : lam (θ.symm ⟨pairVec p e, pairVec_mem_coreMod p e⟩) = Multiplicative.ofAdd 1 := by
      rw [hlam, MulEquiv.apply_symm_apply]
      show Multiplicative.ofAdd (Multiplicative.toAdd (pairVec p e) p +
        Multiplicative.toAdd (pairVec p e) q) = _
      rw [toAdd_pairVec, toAdd_pairVec, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hep),
        Pi.single_eq_of_ne hpq.symm, Pi.single_eq_of_ne (Ne.symm heq)]
      rfl
    intro z
    rcases multiplicative_zmod_two_cases z with rfl | rfl
    · exact ⟨1, map_one lam⟩
    · exact ⟨_, h1⟩
  have hUidx : U₀.relIndex U = 2 := by
    show (U₀.subgroupOf U).index = 2
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := (hA.1.trans hRX).trans hXV
  have hAs : autOn A V = Subgroup.zpowers (τ : MulAut ↥V) := by
    refine le_antisymm (hJ ▸ autOn_le_autOn V (B6.le_thompsonJ hA)) ?_
    rw [Subgroup.zpowers_le, ← hsta, coe_starOf]
    exact conjAct_mem_autOn _ haA
  have hτord : orderOf (τ : MulAut ↥V) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1
  have hAQ : A ⊓ pCoreOf 2 (K ⊔ R) = A ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hQ, ← inf_assoc, inf_eq_left.mpr hA.1]
  have hAidx : (A ⊓ pCoreOf 2 (K ⊔ R)).relIndex A = 2 := by
    rw [hAQ, ← card_autOn_eq_relIndex hAn, hAs, Nat.card_zpowers, hτord]
  have hA₀Q : (A ⊓ pCoreOf 2 (K ⊔ R)) ⊔ U ≤ pCoreOf 2 (K ⊔ R) := sup_le inf_le_right hUQ
  have hA₀e : IsElemAbelian 2 ((A ⊓ pCoreOf 2 (K ⊔ R)) ⊔ U) := by
    refine B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left hA.2.1)
      (B2F.isElemAbelian_mono hUV hVe) fun x hx u hu => ?_
    exact Subgroup.mem_centralizer_iff.mp (hUc hu) x hx.2
  have hA₀card : Nat.card ↥((A ⊓ pCoreOf 2 (K ⊔ R)) ⊔ U) = Nat.card A := by
    have hTU : A ⊓ pCoreOf 2 (K ⊔ R) ≤ Subgroup.normalizer (U : Set G) :=
      (inf_le_right.trans (pCoreOf_le 2 _)).trans hUn
    have h1 := B6.relIndex_inf_eq_relIndex_sup hTU
    have h2 : A ⊓ pCoreOf 2 (K ⊔ R) ⊓ U = U₀ := by
      rw [← hUAeq, inf_assoc, inf_eq_right.mpr hUQ, inf_comm]
    rw [h2, hUidx] at h1
    have e1 := Subgroup.relIndex_mul_card (A ⊓ pCoreOf 2 (K ⊔ R))
      ((A ⊓ pCoreOf 2 (K ⊔ R)) ⊔ U)
    have e2 := Subgroup.relIndex_mul_card (A ⊓ pCoreOf 2 (K ⊔ R)) A
    rw [inf_eq_left.mpr (le_sup_left : A ⊓ pCoreOf 2 (K ⊔ R) ≤ (A ⊓ pCoreOf 2 (K ⊔ R)) ⊔ U)]
      at e1
    rw [inf_eq_left.mpr (inf_le_left : A ⊓ pCoreOf 2 (K ⊔ R) ≤ A)] at e2
    rw [← e1, ← e2, ← h1, hAidx]
  have hA₀max : IsMaxElemAbelian R ((A ⊓ pCoreOf 2 (K ⊔ R)) ⊔ U) :=
    ⟨hA₀Q.trans hQR, hA₀e, fun B hBR hB => (hA.2.2 B hBR hB).trans hA₀card.ge⟩
  have hZ₁R : Z₁ ≤ R := (A4.omegaOneCenterOf_le _).trans (B6.thompsonJ_le R)
  have hZ₁2 : ∀ z ∈ Z₁, z ^ 2 = 1 := fun z hz => A4.sq_eq_one_of_mem_omegaOneCenterOf hz
  have hZ₁cJ : Z₁ ≤ Subgroup.centralizer (thompsonJ R : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _)
  have hZ₁B : ∀ B : Subgroup G, IsMaxElemAbelian R B → Z₁ ≤ B := fun B hB =>
    le_of_isMaxElemAbelian' hB hZ₁R hZ₁2
      (hZ₁cJ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (B6.le_thompsonJ hB))))
  have hZ₁Q : Z₁ ≤ pCoreOf 2 (K ⊔ R) := (hZ₁B _ hA₀max).trans hA₀Q
  have hZ₁char : (Z₁.subgroupOf R).Characteristic :=
    C1GN.characteristic_subgroupOf_trans (B6.thompsonJ_le R) (A4.omegaOneCenterOf_le _)
      (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ R)
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)
  have hCchar : ((⁅Z₁, R⁆ : Subgroup G).subgroupOf R).Characteristic :=
    characteristic_commutator_subgroupOf' hZ₁R hZ₁char
  have hCR : (⁅Z₁, R⁆ : Subgroup G) ≤ R := Subgroup.commutator_le.mpr fun z hz r hr => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem (hZ₁R hz) hr) (R.inv_mem (hZ₁R hz))) (R.inv_mem hr)
  have hUD : ∀ y ∈ U, y ∈ Subgroup.centralizer (K : Set G) → y = 1 := by
    intro y hyU hyK
    have hfix : ∀ σ ∈ alternatingGroup (Fin n),
        G6.coreAct n σ (θ ⟨y, hyU⟩) = θ ⟨y, hyU⟩ := by
      intro σ hσ
      obtain ⟨g₂, hg₂K, hg₂σ⟩ := hιK σ hσ
      obtain ⟨k₀, hk₀K, hk₀g⟩ := exists_of_mem_autOn hg₂K
      have hkX : (k₀ : G) ∈ K ⊔ R := hKX hk₀K
      have hst : starOf hXV hkX = g₂ := Subtype.ext (by rw [coe_starOf, ← hk₀g])
      have h1 : (k₀ : G) * y * (k₀ : G)⁻¹ = y := by
        rw [Subgroup.mem_centralizer_iff.mp hyK k₀ hk₀K, mul_inv_cancel_right]
      have h2 := (hcomm_iff _ hkX ⟨y, hyU⟩).mp h1
      rwa [hst, hg₂σ] at h2
    have h1 := eq_one_of_forall_alternatingGroup hn h3 _ hfix
    have h2 : (⟨y, hyU⟩ : ↥U) = 1 := θ.injective (h1.trans (map_one θ).symm)
    exact congrArg Subtype.val h2
  have hDn : ∀ x ∈ K ⊔ R, ∀ d ∈ pCoreOf 2 (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G),
      x * d * x⁻¹ ∈ pCoreOf 2 (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G) := by
    intro x hx d hd
    refine Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (K ⊔ R) hx) d).mp hd.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : x⁻¹ * k * x ∈ K :=
      (Subgroup.mem_normalizer_iff''.mp (h.sup_le_normalizer hx) k).mp hk
    have h1 := Subgroup.mem_centralizer_iff.mp hd.2 _ hk'
    calc k * (x * d * x⁻¹) = x * ((x⁻¹ * k * x) * d) * x⁻¹ := by group
      _ = x * (d * (x⁻¹ * k * x)) * x⁻¹ := by rw [h1]
      _ = x * d * x⁻¹ * k := by group
  have hDU : pCoreOf 2 (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.normalizer (U : Set G) := inf_le_left.trans ((pCoreOf_le 2 _).trans hUn)
  refine le_antisymm ?_ (hJ ▸ autOn_le_autOn V (B6.thompsonJ_le R))
  intro g hg
  by_contra hgτ
  obtain ⟨r₀, hr₀R, hr₀g⟩ := exists_of_mem_autOn hg
  have hrX : (r₀ : G) ∈ K ⊔ R := hRX hr₀R
  have hstr : ((starOf hXV hrX : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) = g := by
    rw [coe_starOf, ← hr₀g]
  have hπ1 : ι (starOf hXV hrX) ≠ 1 := by
    intro h1
    apply hgτ
    have h2 : starOf hXV hrX = 1 := hι (h1.trans (map_one ι).symm)
    rw [← hstr, h2]
    exact Subgroup.one_mem _
  have hπs : ι (starOf hXV hrX) ≠ Equiv.swap p q := by
    intro h1
    apply hgτ
    have h2 : starOf hXV hrX = τ := hι (h1.trans hτ.symm)
    rw [← hstr, h2]
    exact Subgroup.mem_zpowers _
  obtain ⟨f, hfp, hfq, hπf⟩ : ∃ f, f ≠ p ∧ f ≠ q ∧ ι (starOf hXV hrX) f ≠ f := by
    by_contra hne
    push Not at hne
    rcases perm_eq_one_or_swap (hRpair _ hr₀R) hne with h1 | h1
    · exact hπ1 h1
    · exact hπs h1
  have hfe : f ≠ e := fun hfe => hπf (hfe ▸ hRe _ hr₀R)
  have hθu₁ : θ (θ.symm ⟨pairVec f e, pairVec_mem_coreMod f e⟩) =
      ⟨pairVec f e, pairVec_mem_coreMod f e⟩ := MulEquiv.apply_symm_apply _ _
  have hu₁Z : ((θ.symm ⟨pairVec f e, pairVec_mem_coreMod f e⟩ : ↥U) : G) ∈ Z₁ := by
    refine hU₀Z ((hU₀_iff _).mpr ?_)
    rw [hθu₁]
    show Multiplicative.toAdd (pairVec f e) p = Multiplicative.toAdd (pairVec f e) q
    rw [toAdd_pairVec, toAdd_pairVec, Pi.single_eq_of_ne hfp.symm, Pi.single_eq_of_ne hep.symm,
      Pi.single_eq_of_ne hfq.symm, Pi.single_eq_of_ne heq.symm]
  have hu₁r : (r₀ : G) * (θ.symm ⟨pairVec f e, pairVec_mem_coreMod f e⟩ : ↥U) * (r₀ : G)⁻¹ ≠
      (θ.symm ⟨pairVec f e, pairVec_mem_coreMod f e⟩ : ↥U) := by
    rw [Ne, hcomm_iff _ hrX, hθu₁]
    exact coreAct_pairVec_ne hfe (hRe _ hr₀R) hπf
  have hCne : (⁅Z₁, R⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hu₁r
    have h1 : ⁅((θ.symm ⟨pairVec f e, pairVec_mem_coreMod f e⟩ : ↥U) : G), (r₀ : G)⁆ ∈
        (⁅Z₁, R⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hu₁Z hr₀R
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h1
    set u₁ : G := ((θ.symm ⟨pairVec f e, pairVec_mem_coreMod f e⟩ : ↥U) : G)
    calc (r₀ : G) * u₁ * (r₀ : G)⁻¹ = (u₁ * r₀ * u₁⁻¹ * (r₀ : G)⁻¹)⁻¹ * u₁ := by group
      _ = u₁ := by rw [h1, inv_one, one_mul]
  obtain ⟨g₁, hg₁K, hg₁c⟩ := hιK _ (cycle_mem_alternatingGroup hpq hep)
  obtain ⟨ρ₀, hρ₀K, hρ₀g⟩ := exists_of_mem_autOn hg₁K
  have hρX : (ρ₀ : G) ∈ K ⊔ R := hKX hρ₀K
  have hstρ : starOf hXV hρX = g₁ := Subtype.ext (by rw [coe_starOf, ← hρ₀g])
  have hιρ : ι (starOf hXV hρX) = Equiv.swap p e * Equiv.swap p q := by rw [hstρ, hg₁c]
  have hρC : ∀ z ∈ Z₁, ∀ r ∈ R, (ρ₀ : G) * ⁅z, r⁆ * (ρ₀ : G)⁻¹ = ⁅z, r⁆ := by
    intro z hz r hr
    have hzUD : z ∈ ((U ⊔ (pCoreOf 2 (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G)) :
        Subgroup G) : Set G) := hQU (hZ₁Q hz)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U _ hDU] at hzUD
    obtain ⟨u, hu, d, hd, rfl⟩ := hzUD
    have hrX' : r ∈ K ⊔ R := hRX hr
    have hcomm : a * (u * d) * a⁻¹ = u * d := by
      rw [B2F.isElemAbelian_comm hA.2.1 haA (hZ₁B A hA hz), mul_inv_cancel_right]
    have hau : a * u * a⁻¹ = u := by
      have h1 : a * u * a⁻¹ ∈ U := hconjU a haX u hu
      have h2 := hDn a haX d hd
      have h5 : (a * u * a⁻¹) * (a * d * a⁻¹) = u * d := by
        rw [← hcomm]
        group
      have h4 : u⁻¹ * (a * u * a⁻¹) = d * (a * d * a⁻¹)⁻¹ := by
        calc u⁻¹ * (a * u * a⁻¹) =
            u⁻¹ * ((a * u * a⁻¹) * (a * d * a⁻¹)) * (a * d * a⁻¹)⁻¹ := by group
          _ = u⁻¹ * (u * d) * (a * d * a⁻¹)⁻¹ := by rw [h5]
          _ = d * (a * d * a⁻¹)⁻¹ := by group
      have h6 : u⁻¹ * (a * u * a⁻¹) = 1 := hUD _ (U.mul_mem (U.inv_mem hu) h1)
        (by rw [h4]; exact (Subgroup.mul_mem _ hd (Subgroup.inv_mem _ h2)).2)
      calc a * u * a⁻¹ = u * (u⁻¹ * (a * u * a⁻¹)) := by group
        _ = u := by rw [h6, mul_one]
    have huθ : Multiplicative.toAdd ((θ ⟨u, hu⟩ : ↥(G6.coreMod n)) : G6.PermMod n) p =
        Multiplicative.toAdd ((θ ⟨u, hu⟩ : ↥(G6.coreMod n)) : G6.PermMod n) q := by
      have h1 := (hcomm_iff a haX ⟨u, hu⟩).mp hau
      rw [hιa] at h1
      exact (coreAct_swap_eq_iff _).mp h1
    have hw₁ : u * (r * u⁻¹ * r⁻¹) ∈ U := U.mul_mem hu (hconjU r hrX' _ (U.inv_mem hu))
    have hw₂ : d * (r * d⁻¹ * r⁻¹) ∈ pCoreOf 2 (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G) :=
      Subgroup.mul_mem _ hd (hDn r hrX' _ (Subgroup.inv_mem _ hd))
    have hc2 : (r * u⁻¹ * r⁻¹) * (d * (r * d⁻¹ * r⁻¹)) =
        (d * (r * d⁻¹ * r⁻¹)) * (r * u⁻¹ * r⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hUc (hconjU r hrX' _ (U.inv_mem hu))) _ hw₂.1).symm
    have hdecomp : ⁅u * d, r⁆ = (u * (r * u⁻¹ * r⁻¹)) * (d * (r * d⁻¹ * r⁻¹)) := by
      rw [commutatorElement_def]
      calc u * d * r * (u * d)⁻¹ * r⁻¹ = u * ((d * (r * d⁻¹ * r⁻¹)) * (r * u⁻¹ * r⁻¹)) := by
            group
        _ = u * ((r * u⁻¹ * r⁻¹) * (d * (r * d⁻¹ * r⁻¹))) := by rw [hc2]
        _ = (u * (r * u⁻¹ * r⁻¹)) * (d * (r * d⁻¹ * r⁻¹)) := by group
    rw [hdecomp]
    have hρw₂ : (ρ₀ : G) * (d * (r * d⁻¹ * r⁻¹)) * (ρ₀ : G)⁻¹ = d * (r * d⁻¹ * r⁻¹) := by
      rw [Subgroup.mem_centralizer_iff.mp hw₂.2 _ hρ₀K, mul_inv_cancel_right]
    have hρw₁ : (ρ₀ : G) * (u * (r * u⁻¹ * r⁻¹)) * (ρ₀ : G)⁻¹ = u * (r * u⁻¹ * r⁻¹) := by
      refine (hcomm_iff _ hρX ⟨_, hw₁⟩).mpr ?_
      rw [hιρ]
      have hθw : θ ⟨u * (r * u⁻¹ * r⁻¹), hw₁⟩ =
          θ ⟨u, hu⟩ * (G6.coreAct n (ι (starOf hXV hrX')) (θ ⟨u, hu⟩))⁻¹ := by
        have e1 : (⟨u * (r * u⁻¹ * r⁻¹), hw₁⟩ : ↥U) =
            ⟨u, hu⟩ * ⟨r * u⁻¹ * r⁻¹, hconjU r hrX' _ (U.inv_mem hu)⟩ := rfl
        rw [e1, map_mul]
        congr 1
        have e2 := hθc r hrX' (⟨u, hu⟩⁻¹)
        rw [map_inv, map_inv] at e2
        exact e2
      rw [hθw]
      obtain ⟨hcp, hcq, hce, hcoth⟩ := cycle_inv_apply hpq hep heq
      refine coreAct_eq_of_vanish hcoth (Or.inr (Or.inr hcp)) (Or.inl hcq) (Or.inr (Or.inl hce))
        _ ?_
      refine vanish_mul_inv_coreAct ?_ ?_ ?_ _ huθ
      · rcases hRpair r hr with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact Or.inl (Equiv.Perm.inv_eq_iff_eq.mpr h1.symm)
        · exact Or.inr (Equiv.Perm.inv_eq_iff_eq.mpr h2.symm)
      · rcases hRpair r hr with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact Or.inr (Equiv.Perm.inv_eq_iff_eq.mpr h2.symm)
        · exact Or.inl (Equiv.Perm.inv_eq_iff_eq.mpr h1.symm)
      · exact Equiv.Perm.inv_eq_iff_eq.mpr (hRe r hr).symm
    calc (ρ₀ : G) * ((u * (r * u⁻¹ * r⁻¹)) * (d * (r * d⁻¹ * r⁻¹))) * (ρ₀ : G)⁻¹ =
        ((ρ₀ : G) * (u * (r * u⁻¹ * r⁻¹)) * (ρ₀ : G)⁻¹) *
          ((ρ₀ : G) * (d * (r * d⁻¹ * r⁻¹)) * (ρ₀ : G)⁻¹) := by group
      _ = (u * (r * u⁻¹ * r⁻¹)) * (d * (r * d⁻¹ * r⁻¹)) := by rw [hρw₁, hρw₂]
  have hρcent : (ρ₀ : G) ∈ Subgroup.centralizer ((⁅Z₁, R⁆ : Subgroup G) : Set G) := by
    have hle : (⁅Z₁, R⁆ : Subgroup G) ≤ Subgroup.centralizer ({(ρ₀ : G)} : Set G) := by
      rw [Subgroup.commutator_le]
      intro z hz r hr
      rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      calc (ρ₀ : G) * ⁅z, r⁆ = ((ρ₀ : G) * ⁅z, r⁆ * (ρ₀ : G)⁻¹) * ρ₀ := by group
        _ = ⁅z, r⁆ * ρ₀ := by rw [hρC z hz r hr]
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact ((Subgroup.mem_centralizer_iff.mp (hle hc)) _ rfl).symm
  have hρM : (ρ₀ : G) ∈ M := h.hyp.cgs (inf_normalizer_le_cgsIn_of_char hCR hCne hCchar
    ⟨h.K_le hρ₀K, Subgroup.centralizer_le_normalizer _ hρcent⟩)
  have hρMK : conjAct V ρ₀ ∈ autOn (M ⊓ K) V := conjAct_mem_autOn _ ⟨hρM, hρ₀K⟩
  have h1 : starOf hXV hρX * τ = τ * starOf hXV hρX := Subtype.ext (hMK _ hρMK)
  have h2 := congrArg ι h1
  rw [map_mul, map_mul, hιρ, hτ] at h2
  exact cycle_mul_swap_ne hpq hep heq h2

omit [Finite G] in
theorem orderOf_eq_two_of_map_eq_swap {Γ : Type*} [Group Γ] {n : ℕ} {ι : Γ →* Equiv.Perm (Fin n)}
    (hι : Function.Injective ι) {τ : Γ} {p q : Fin n} (hpq : p ≠ q)
    (hτ : ι τ = Equiv.swap p q) : orderOf τ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (hι ?_) ?_
  · rw [map_pow, hτ, map_one, pow_two, Equiv.swap_mul_self]
  · intro h1
    rw [h1, map_one] at hτ
    have h2 := congrArg (fun σ : Equiv.Perm (Fin n) => σ p) hτ
    simp only [Equiv.Perm.one_apply, Equiv.swap_apply_left] at h2
    exact hpq h2

theorem exists_eq_zpowers_of_k1 {H R M K V U : Subgroup G} (h : Hyp27 H R M K)
    (hV : V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))
    (hQ : pCoreOf 2 (K ⊔ R) = R ⊓ Subgroup.centralizer (V : Set G))
    (hUV : U ≤ V) (hUn : K ⊔ R ≤ Subgroup.normalizer (U : Set G))
    (hQU : pCoreOf 2 (K ⊔ R) ≤ U ⊔ (pCoreOf 2 (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G)))
    {n : ℕ} (hn : Odd n) (ι : ↥(autOn (K ⊔ R) V) →* Equiv.Perm (Fin n))
    (hι : Function.Injective ι)
    (hιK : ∀ σ ∈ alternatingGroup (Fin n),
      ∃ g : ↥(autOn (K ⊔ R) V), (g : MulAut ↥V) ∈ autOn K V ∧ ι g = σ)
    (θ : ↥U ≃* ↥(G6.coreMod n))
    (hθ : ∀ (g : ↥(autOn (K ⊔ R) V)) (u : ↥U)
      (hgu : (((g : MulAut ↥V) ⟨u, hUV u.2⟩ : ↥V) : G) ∈ U),
      θ ⟨_, hgu⟩ = G6.coreAct n (ι g) (θ u))
    (τ : ↥(autOn (K ⊔ R) V)) {p q : Fin n} (hpq : p ≠ q) (hτ : ι τ = Equiv.swap p q)
    (hJ : autOn (thompsonJ R) V = Subgroup.zpowers (τ : MulAut ↥V))
    (hMK : ∀ g ∈ autOn (M ⊓ K) V, g * (τ : MulAut ↥V) = (τ : MulAut ↥V) * g) :
    ∃ t : G, t ∈ R ∧ ∃ htV : t ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨t, htV⟩ = (τ : MulAut ↥V) ∧
      autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩) ∧
      orderOf (conjAct V ⟨t, htV⟩) = 2 := by
  have hmain := autOn_eq_zpowers_of_k1 h hV hQ hUV hUn hQU hn ι hι hιK θ hθ τ hpq hτ hJ hMK
  have hτJ : (τ : MulAut ↥V) ∈ autOn (thompsonJ R) V := hJ ▸ Subgroup.mem_zpowers _
  obtain ⟨t, htJ, htτ⟩ := exists_of_mem_autOn hτJ
  refine ⟨t, B6.thompsonJ_le R htJ, t.2, htτ, ?_, ?_⟩
  · rw [htτ]
    exact hmain
  · rw [htτ, Subgroup.orderOf_coe]
    exact orderOf_eq_two_of_map_eq_swap hι hpq hτ

end Main

end CFSG.Quasithin.SmithC27
