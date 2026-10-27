module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import TauCeti.GroupTheory.Coset.Fiber

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

theorem diagMap_mul_permMap_eq (f : Module.Basis (Fin n) (ZMod p) U)
    {d d' : Fin n → (ZMod p)ˣ} {σ σ' : Equiv.Perm (Fin n)}
    (h : diagMap p f d * permMap p f σ = diagMap p f d' * permMap p f σ') :
    d = d' ∧ σ = σ' := by
  have happ : ∀ i : Fin n,
      (d (σ i) : ZMod p) • f (σ i) = (d' (σ' i) : ZMod p) • f (σ' i) := by
    intro i
    have h' := congrArg (fun g : U ≃ₗ[ZMod p] U => g (f i)) h
    simpa only [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis] using h'
  have hσd : ∀ i : Fin n, σ i = σ' i ∧ d (σ i) = d' (σ' i) := by
    intro i
    have hrepr : (Finsupp.single (σ i) (↑(d (σ i))) : Fin n →₀ ZMod p) =
        Finsupp.single (σ' i) (↑(d' (σ' i))) := by
      have h' := congrArg f.repr (happ i)
      simpa [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul] using h'
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp hrepr with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact ⟨h1, Units.ext h2⟩
    · exact absurd h1 (Units.ne_zero (d (σ i)))
  have hσfun : ∀ i : Fin n, σ i = σ' i := fun i => (hσd i).1
  have hσ : σ = σ' := Equiv.ext hσfun
  have hd : d = d' := by
    funext k
    obtain ⟨i, rfl⟩ := σ.surjective k
    have h1 := (hσd i).2
    rw [← hσfun i] at h1
    exact h1
  exact ⟨hd, hσ⟩

private theorem natCard_of_monomial (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Type*} (φ : A → Fin n → (ZMod p)ˣ) (hφ : Function.Injective φ)
    {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hS : ∀ a, diagMap p f (φ a) ∈ G)
    (hP : ∀ σ : Equiv.Perm (Fin n), permMap p f σ ∈ G)
    (hG : ∀ g ∈ G, ∃ a, ∃ σ : Equiv.Perm (Fin n),
      g = diagMap p f (φ a) * permMap p f σ) :
    Nat.card G = Nat.card A * n.factorial := by
  have hmul : ∀ (a : A) (σ : Equiv.Perm (Fin n)),
      diagMap p f (φ a) * permMap p f σ ∈ G := fun a σ => Subgroup.mul_mem _ (hS a) (hP σ)
  let e : A × Equiv.Perm (Fin n) → G := fun x =>
    ⟨diagMap p f (φ x.1) * permMap p f x.2, hmul x.1 x.2⟩
  have hbij : Function.Bijective e := by
    constructor
    · rintro ⟨a, σ⟩ ⟨a', σ'⟩ h
      have h' : diagMap p f (φ a) * permMap p f σ = diagMap p f (φ a') * permMap p f σ' :=
        congrArg (fun x : G => (x : U ≃ₗ[ZMod p] U)) h
      have h1 : φ a = φ a' ∧ σ = σ' := diagMap_mul_permMap_eq (p := p) f h'
      exact Prod.ext (hφ h1.1) h1.2
    · rintro ⟨g, hg⟩
      obtain ⟨a, σ, hgs⟩ := hG g hg
      exact ⟨(a, σ), Subtype.ext hgs.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective e hbij), Nat.card_prod, Nat.card_perm, Nat.card_fin]

private noncomputable def prodHom {H : Subgroup (ZMod p)ˣ} :
    (Fin n → H) →* H where
  toFun d := ∏ i, d i
  map_one' := by simp
  map_mul' d d' := by simp [Finset.prod_mul_distrib]

private theorem prodHom_surjective {H : Subgroup (ZMod p)ˣ} (hn : 0 < n) :
    Function.Surjective (prodHom (p := p) (n := n) (H := H)) := by
  intro h
  refine ⟨fun i => if i = ⟨0, hn⟩ then h else 1, ?_⟩
  show ∏ i : Fin n, (if i = ⟨0, hn⟩ then h else 1) = h
  rw [Fintype.prod_eq_mul_prod_compl ⟨0, hn⟩]
  have hc : ∏ i ∈ ({⟨0, hn⟩}ᶜ : Finset (Fin n)), (if i = ⟨0, hn⟩ then h else 1) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_compl, Finset.mem_singleton] at hi
    simp [hi]
  rw [hc, mul_one]
  simp

private theorem card_prodHom_ker {H : Subgroup (ZMod p)ˣ} (hn : 0 < n) :
    Nat.card (prodHom (p := p) (n := n) (H := H)).ker = Nat.card H ^ (n - 1) := by
  have hsurj := prodHom_surjective (p := p) (n := n) (H := H) hn
  have h := Subgroup.card_ker_mul_card_of_surjective
    (f := prodHom (p := p) (n := n) (H := H)) hsurj
  rw [Nat.card_fun, Nat.card_fin] at h
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hpow : Nat.card H ^ n = Nat.card H ^ (n - 1) * Nat.card H := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.succ_pred_eq_of_pos hn).symm]
    rw [pow_succ]
  rw [hpow] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h

private theorem eq_prod_pairUnit_of_prod_eq_one {d : Fin n → (ZMod p)ˣ} (k₀ : Fin n)
    (hprod : ∏ k, d k = 1) :
    d = ∏ k ∈ Finset.univ.erase k₀, pairUnit p k k₀ (d k) := by
  funext j
  rw [Finset.prod_apply]
  by_cases hjk₀ : j = k₀
  · rw [hjk₀]
    have h1 : ∏ k ∈ Finset.univ.erase k₀, pairUnit p k k₀ (d k) k₀ =
        ∏ k ∈ Finset.univ.erase k₀, (d k)⁻¹ := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Finset.mem_erase] at hk
      simp [pairUnit, Ne.symm hk.1]
    rw [h1, Finset.prod_inv_distrib]
    have h2 : d k₀ * ∏ k ∈ Finset.univ.erase k₀, d k = 1 := by
      rw [Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k₀), hprod]
    rw [eq_inv_of_mul_eq_one_right h2, inv_inv]
  · have hjmem : j ∈ Finset.univ.erase k₀ := by
      rw [Finset.mem_erase]; exact ⟨hjk₀, Finset.mem_univ j⟩
    rw [Finset.prod_eq_single j]
    · simp [pairUnit]
    · intro k hk hkj
      rw [Finset.mem_erase] at hk
      simp [pairUnit, Ne.symm hkj, hjk₀]
    · intro hj; exact absurd hjmem hj

private theorem diagMap_prod_pairUnit_mem_gmmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {k₀ : Fin n} (s : Finset (Fin n))
    (hs : ∀ k ∈ s, k ≠ k₀) {d : Fin n → (ZMod p)ˣ} (hd : ∀ k, d k ∈ Subgroup.zpowers ζ) :
    diagMap p f (∏ k ∈ s, pairUnit p k k₀ (d k)) ∈ gmmn p f i₀ i₁ ζ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, diagMap_one]; exact Subgroup.one_mem _
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ← diagMap_mul]
      refine Subgroup.mul_mem _
        (diagMap_pairUnit_mem_gmmn f hi (hs a (Finset.mem_insert_self a s)) (hd a)) ?_
      exact ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))

private theorem diagMap_mem_gmmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {d : Fin n → (ZMod p)ˣ}
    (hd : ∀ k, d k ∈ Subgroup.zpowers ζ) (hprod : ∏ k, d k = 1) :
    diagMap p f d ∈ gmmn p f i₀ i₁ ζ := by
  rw [eq_prod_pairUnit_of_prod_eq_one (p := p) (n := n) i₀ hprod]
  exact diagMap_prod_pairUnit_mem_gmmn f hi (Finset.univ.erase i₀)
    (fun k hk => (Finset.mem_erase.mp hk).1) hd

theorem card_gmmn {n : ℕ} (hn : 2 ≤ n) (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    Nat.card (gmmn p f i₀ i₁ ζ) = orderOf ζ ^ (n - 1) * n.factorial := by
  have hn0 : 0 < n := by omega
  let φ : (prodHom (p := p) (n := n) (H := Subgroup.zpowers ζ)).ker → Fin n → (ZMod p)ˣ :=
    fun a i => (a.1 i : (ZMod p)ˣ)
  have hφ : Function.Injective φ := by
    intro a a' h
    refine Subtype.ext (funext fun i => ?_)
    exact Subtype.ext (congrFun h i)
  have hS : ∀ a : (prodHom (p := p) (n := n) (H := Subgroup.zpowers ζ)).ker,
      diagMap p f (φ a) ∈ gmmn p f i₀ i₁ ζ := by
    intro a
    refine diagMap_mem_gmmn f hi (fun k => (a.1 k).2) ?_
    have h2 := MonoidHom.mem_ker.mp a.2
    have h3 := congrArg (Subgroup.subtype (Subgroup.zpowers ζ)) h2
    simpa [φ, prodHom, map_prod] using h3
  have hP : ∀ σ : Equiv.Perm (Fin n), permMap p f σ ∈ gmmn p f i₀ i₁ ζ :=
    fun σ => Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))
  have hG : ∀ g ∈ gmmn p f i₀ i₁ ζ,
      ∃ a : (prodHom (p := p) (n := n) (H := Subgroup.zpowers ζ)).ker,
        ∃ σ : Equiv.Perm (Fin n), g = diagMap p f (φ a) * permMap p f σ := by
    intro g hg
    obtain ⟨d, σ, hd, hprod, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hg
    refine ⟨⟨fun i => ⟨d i, hd i⟩, ?_⟩, σ, ?_⟩
    · rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      simpa [prodHom, map_prod] using hprod
    · rw [hgeq]
  rw [natCard_of_monomial f φ hφ hS hP hG,
    card_prodHom_ker (p := p) (n := n) (H := Subgroup.zpowers ζ) hn0, Nat.card_zpowers]

private theorem diagMap_prod_pairUnit_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {k₀ : Fin n} (s : Finset (Fin n))
    (hs : ∀ k ∈ s, k ≠ k₀) {d : Fin n → (ZMod p)ˣ}
    (hd : ∀ k, d k ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ)) :
    diagMap p f (∏ k ∈ s, pairUnit p k k₀ (d k)) ∈ g2mmn p f i₀ i₁ ζ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, diagMap_one]; exact Subgroup.one_mem _
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ← diagMap_mul]
      refine Subgroup.mul_mem _
        (diagMap_pairUnit_mem_g2mmn f hi (hs a (Finset.mem_insert_self a s)) (hd a)) ?_
      exact ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))

private theorem diagMap_mem_g2mmn_of_prod_eq_one (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {d : Fin n → (ZMod p)ˣ}
    (hd : ∀ k, d k ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ)) (hprod : ∏ k, d k = 1) :
    diagMap p f d ∈ g2mmn p f i₀ i₁ ζ := by
  rw [eq_prod_pairUnit_of_prod_eq_one (p := p) (n := n) i₀ hprod]
  exact diagMap_prod_pairUnit_mem_g2mmn f hi (Finset.univ.erase i₀)
    (fun k hk => (Finset.mem_erase.mp hk).1) hd

private theorem diagMap_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {d : Fin n → (ZMod p)ˣ}
    (hd : ∀ k, d k ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ))
    (hprod : ∏ k, d k = 1 ∨ ∏ k, d k = -1) :
    diagMap p f d ∈ g2mmn p f i₀ i₁ ζ := by
  rcases hprod with hprod | hprod
  · exact diagMap_mem_g2mmn_of_prod_eq_one f hi hd hprod
  · let s : Fin n → (ZMod p)ˣ := fun i => if i = i₀ then -1 else 1
    have hsC : ∀ k, s k ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ) := by
      intro k
      by_cases hk : k = i₀
      · rw [show s k = (if k = i₀ then -1 else 1) from rfl, if_pos hk]
        exact Subgroup.subset_closure (by simp)
      · rw [show s k = (if k = i₀ then -1 else 1) from rfl, if_neg hk]
        exact Subgroup.one_mem _
    have hprods : ∏ k, s k = -1 := by
      rw [Fintype.prod_eq_mul_prod_compl i₀]
      have h1 : ∏ k ∈ ({i₀}ᶜ : Finset (Fin n)), s k = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp only [Finset.mem_compl, Finset.mem_singleton] at hk
        rw [show s k = (if k = i₀ then -1 else 1) from rfl, if_neg hk]
      rw [h1, mul_one]
      simp [s]
    have hprod' : ∏ k, (d * s) k = 1 := by
      simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, hprod, hprods]
      simp
    have hmem' : diagMap p f (d * s) ∈ g2mmn p f i₀ i₁ ζ :=
      diagMap_mem_g2mmn_of_prod_eq_one f hi (fun k => Subgroup.mul_mem _ (hd k) (hsC k)) hprod'
    have hs_mem : diagMap p f s ∈ g2mmn p f i₀ i₁ ζ := by
      have hgen : diagMap p f (fun i => if i = i₀ then -1 else 1) ∈ g2mmn p f i₀ i₁ ζ :=
        Subgroup.subset_closure (by simp)
      rwa [show s = (fun i => if i = i₀ then -1 else 1) from rfl]
    have hss : (d * s) * s = d := by
      funext k
      have hs2 : s k * s k = 1 := by
        by_cases hk : k = i₀
        · rw [show s k = (if k = i₀ then -1 else 1) from rfl, if_pos hk]
          exact Units.ext (by simp)
        · rw [show s k = (if k = i₀ then -1 else 1) from rfl, if_neg hk]; exact mul_one 1
      simp only [Pi.mul_apply, mul_assoc, hs2, mul_one]
    have heq : diagMap p f (d * s) * diagMap p f s = diagMap p f d := by
      rw [diagMap_mul, hss]
    rw [← heq]
    exact Subgroup.mul_mem _ hmem' hs_mem

private theorem card_closure_pair (ζ : (ZMod p)ˣ) (hp : p ≠ 2) :
    Nat.card (Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ)) = Nat.lcm 2 (orderOf ζ) := by
  set C : Subgroup (ZMod p)ˣ := Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ) with hC
  have hζC : ζ ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hmC : (-1 : (ZMod p)ˣ) ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have h2 : orderOf (-1 : (ZMod p)ˣ) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, neg_mul_neg, one_mul]
    · intro h
      have h' : (-1 : ZMod p) = 1 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
      rw [ZMod.neg_one_eq_one_iff] at h'
      rcases h' with h' | h'
      · exact (Fact.out : p.Prime).ne_one h'
      · exact hp h'
  have hdvd : Nat.lcm 2 (orderOf ζ) ∣ Nat.card C := by
    rw [← h2]
    exact Nat.lcm_dvd (Subgroup.orderOf_dvd_natCard C hmC) (Subgroup.orderOf_dvd_natCard C hζC)
  have hLpos : 0 < Nat.lcm 2 (orderOf ζ) := Nat.lcm_pos (by norm_num) (orderOf_pos ζ)
  have hle : Nat.card C ≤ Nat.lcm 2 (orderOf ζ) := by
    have hmem : ∀ x : (ZMod p)ˣ, x ∈ C → x ^ Nat.lcm 2 (orderOf ζ) = 1 := by
      intro x hx
      rw [hC] at hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
          rcases hy with hy | hy
          · rw [hy]
            exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_lcm_right 2 (orderOf ζ))
          · rw [hy]
            exact (orderOf_dvd_iff_pow_eq_one).mp
              (by rw [h2]; exact Nat.dvd_lcm_left 2 (orderOf ζ))
      | one => rw [one_pow]
      | mul y z _ _ ihy ihz => rw [mul_pow, ihy, ihz, one_mul]
      | inv y _ ihy => rw [inv_pow, ihy, inv_one]
    calc Nat.card C ≤ Nat.card {x : (ZMod p)ˣ // x ^ Nat.lcm 2 (orderOf ζ) = 1} :=
          Nat.card_le_card_of_injective (fun x : C =>
              (⟨(x : (ZMod p)ˣ), hmem x x.2⟩ : {x : (ZMod p)ˣ // x ^ Nat.lcm 2 (orderOf ζ) = 1}))
            (fun a b h => Subtype.ext (congrArg
              (fun y : {x : (ZMod p)ˣ // x ^ Nat.lcm 2 (orderOf ζ) = 1} => (y : (ZMod p)ˣ)) h))
      _ = Fintype.card {x : (ZMod p)ˣ // x ^ Nat.lcm 2 (orderOf ζ) = 1} :=
          Nat.card_eq_fintype_card
      _ ≤ Nat.lcm 2 (orderOf ζ) := by
          have hcyc : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime (Fact.out)
          have h := @IsCyclic.card_pow_eq_one_le (ZMod p)ˣ _ _ _ hcyc
            (Nat.lcm 2 (orderOf ζ)) hLpos
          simpa only [Fintype.card_subtype] using h
  exact le_antisymm hle (Nat.le_of_dvd (Nat.card_pos) hdvd)

private theorem card_D2 {C : Subgroup (ZMod p)ˣ} {g : C} (hg : g ≠ 1) (hn : 0 < n) :
    Nat.card {d : Fin n → C // prodHom (p := p) (n := n) (H := C) d = 1 ∨
        prodHom (p := p) (n := n) (H := C) d = g} = 2 * Nat.card C ^ (n - 1) := by
  have hker := card_prodHom_ker (p := p) (n := n) (H := C) hn
  have h1 : Nat.card {d : Fin n → C // prodHom (p := p) (n := n) (H := C) d = 1} =
      Nat.card (prodHom (p := p) (n := n) (H := C)).ker :=
    MonoidHom.card_fiber_eq_card_ker _ (map_one _)
  have hpre : prodHom (p := p) (n := n) (H := C)
      (fun i => if i = ⟨0, hn⟩ then g else 1) = g := by
    show ∏ i : Fin n, (if i = ⟨0, hn⟩ then g else 1) = g
    rw [Fintype.prod_eq_mul_prod_compl ⟨0, hn⟩]
    have hc : ∏ i ∈ ({⟨0, hn⟩}ᶜ : Finset (Fin n)), (if i = ⟨0, hn⟩ then g else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp only [Finset.mem_compl, Finset.mem_singleton] at hi
      simp [hi]
    rw [hc, mul_one]
    simp
  have h2 : Nat.card {d : Fin n → C // prodHom (p := p) (n := n) (H := C) d = g} =
      Nat.card (prodHom (p := p) (n := n) (H := C)).ker :=
    MonoidHom.card_fiber_eq_card_ker _ hpre
  have hdisj : Disjoint (fun d : Fin n → C => prodHom (p := p) (n := n) (H := C) d = 1)
      (fun d : Fin n → C => prodHom (p := p) (n := n) (H := C) d = g) := by
    intro c h1' h2' x hx
    exact hg (((h1' x hx).symm.trans (h2' x hx))).symm
  rw [Nat.card_congr (subtypeOrEquiv _ _ hdisj), Nat.card_sum, h1, h2, hker]
  ring

private noncomputable def g2Closure (ζ : (ZMod p)ˣ) : Subgroup (ZMod p)ˣ :=
  Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ)

private noncomputable def g2Sign (ζ : (ZMod p)ˣ) : g2Closure ζ :=
  ⟨-1, Subgroup.subset_closure (by simp)⟩

private theorem card_g2Closure (ζ : (ZMod p)ˣ) (hp : p ≠ 2) :
    Nat.card (g2Closure ζ) = Nat.lcm 2 (orderOf ζ) := by
  change Nat.card (Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ)) = Nat.lcm 2 (orderOf ζ)
  exact card_closure_pair ζ hp

private theorem g2Sign_ne_one (ζ : (ZMod p)ˣ) (hp : p ≠ 2) : g2Sign ζ ≠ 1 := by
  intro h
  have hnegone : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h'
    have h'' : (-1 : ZMod p) = 1 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h'
    rw [ZMod.neg_one_eq_one_iff] at h''
    rcases h'' with h'' | h''
    · exact (Fact.out : p.Prime).ne_one h''
    · exact hp h''
  have h' : (g2Sign ζ : (ZMod p)ˣ) = 1 := congrArg (fun x : g2Closure ζ => (x : (ZMod p)ˣ)) h
  exact hnegone (by simpa [g2Sign] using h')

private theorem diagMap_mem_g2mmn_subtype (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (a : {d : Fin n → g2Closure ζ // prodHom (p := p) (n := n) (H := g2Closure ζ) d = 1 ∨
      prodHom (p := p) (n := n) (H := g2Closure ζ) d = g2Sign ζ}) :
    diagMap p f (fun i => (a.1 i : (ZMod p)ˣ)) ∈ g2mmn p f i₀ i₁ ζ := by
  refine diagMap_mem_g2mmn f hi (fun k => (a.1 k).2) ?_
  rcases a.2 with h2 | h2
  · left
    have h3 := congrArg (Subgroup.subtype (g2Closure ζ)) h2
    simpa [prodHom, map_prod] using h3
  · right
    have h3 := congrArg (Subgroup.subtype (g2Closure ζ)) h2
    simpa [prodHom, map_prod, g2Sign] using h3

private theorem exists_diagMap_mul_permMap_of_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {h : U ≃ₗ[ZMod p] U}
    (hh : h ∈ g2mmn p f i₀ i₁ ζ) :
    ∃ a : {d : Fin n → g2Closure ζ // prodHom (p := p) (n := n) (H := g2Closure ζ) d = 1 ∨
        prodHom (p := p) (n := n) (H := g2Closure ζ) d = g2Sign ζ},
      ∃ σ : Equiv.Perm (Fin n),
        h = diagMap p f (fun i => (a.1 i : (ZMod p)ˣ)) * permMap p f σ := by
  obtain ⟨d, σ, hd, hprod, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi hh
  refine ⟨⟨fun i => ⟨d i, hd i⟩, ?_⟩, σ, ?_⟩
  · rcases hprod with hprod | hprod
    · left
      refine Subtype.ext ?_
      simpa [prodHom, map_prod] using hprod
    · right
      refine Subtype.ext ?_
      simpa [prodHom, map_prod, g2Sign] using hprod
  · rw [hgeq]

theorem card_g2mmn (hp : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    Nat.card (g2mmn p f i₀ i₁ ζ) = 2 * Nat.lcm 2 (orderOf ζ) ^ (n - 1) * n.factorial := by
  have hn0 : 0 < n := by omega
  have hCcard := card_g2Closure (p := p) ζ hp
  have hg := g2Sign_ne_one (p := p) ζ hp
  let φ : {d : Fin n → g2Closure ζ // prodHom (p := p) (n := n) (H := g2Closure ζ) d = 1 ∨
      prodHom (p := p) (n := n) (H := g2Closure ζ) d = g2Sign ζ} → Fin n → (ZMod p)ˣ :=
    fun a i => (a.1 i : (ZMod p)ˣ)
  have hφ : Function.Injective φ := by
    intro a a' h
    refine Subtype.ext (funext fun i => ?_)
    exact Subtype.ext (congrFun h i)
  have hS : ∀ a : {d : Fin n → g2Closure ζ // prodHom (p := p) (n := n) (H := g2Closure ζ) d = 1 ∨
        prodHom (p := p) (n := n) (H := g2Closure ζ) d = g2Sign ζ},
      diagMap p f (φ a) ∈ g2mmn p f i₀ i₁ ζ :=
    fun a => diagMap_mem_g2mmn_subtype f hi a
  have hP : ∀ σ : Equiv.Perm (Fin n), permMap p f σ ∈ g2mmn p f i₀ i₁ ζ :=
    fun σ => Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))
  have hG : ∀ h ∈ g2mmn p f i₀ i₁ ζ,
      ∃ a : {d : Fin n → g2Closure ζ // prodHom (p := p) (n := n) (H := g2Closure ζ) d = 1 ∨
          prodHom (p := p) (n := n) (H := g2Closure ζ) d = g2Sign ζ},
        ∃ σ : Equiv.Perm (Fin n), h = diagMap p f (φ a) * permMap p f σ :=
    fun h hh => exists_diagMap_mul_permMap_of_mem_g2mmn f hi hh
  rw [natCard_of_monomial f φ hφ hS hP hG,
    card_D2 (p := p) (n := n) (C := g2Closure ζ) (g := g2Sign ζ) hg hn0, hCcard]

end CFSG.StandardType.ZS

end
