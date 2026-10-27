module

public import CFSG.RankThree.GF2n.Stroth80.FieldModelClass

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

section ClassGroups

variable {K : Type} [Field K]

theorem conj_mem_classGroup' {τ : G} (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) {γ : G → K} {x : G}
    (hx : x ∈ classGroup V Q γ) :
    τ * x * τ⁻¹ ∈ classGroup V Q (fun v => γ (τ⁻¹ * v * τ)) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact V_le_classGroup ((mem_iff_conj_of_normalizer hV x).mp hx)
    · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
      refine le_classGroup_of_mem (conj_mem_classOf hV hQ hU) ?_
      exact mem_conjSubgroup.mpr
        (by rw [show τ⁻¹ * (τ * x * τ⁻¹) * τ = x by group]; exact hxU)
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    rwa [show τ * (x * y) * τ⁻¹ = τ * x * τ⁻¹ * (τ * y * τ⁻¹) by group]
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    rwa [show τ * x⁻¹ * τ⁻¹ = (τ * x * τ⁻¹)⁻¹ by group]

theorem classGroup_congr {γ γ' : G → K} (h : classOf V Q γ = classOf V Q γ') :
    classGroup V Q γ = classGroup V Q γ' := by
  simp only [classGroup, h]

theorem commute_of_closure' {S T : Set G} (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure T ≤ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.closure_le _).mpr fun t ht =>
        Subgroup.mem_centralizer_iff.mpr fun z hz => by
          rw [Set.mem_singleton_iff.mp hz]
          exact h x hx t ht
    exact Subgroup.mem_centralizer_iff.mp (hle hy) x rfl
  intro x hx y hy
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({y} : Set G) :=
    (Subgroup.closure_le _).mpr fun s hs =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact (h1 s hs y hy).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y rfl).symm

theorem commute_classGroup (H : Hyp79 M V Q) {n : ℕ} {U₀ : Subgroup G}
    (D₀ : MulData V U₀ Q (GaloisField 2 n)) {γ' : G → GaloisField 2 n}
    (hne : classOf V Q γ' ≠ classOf V Q D₀.γ) :
    ∀ x ∈ classGroup V Q γ', ∀ y ∈ classGroup V Q D₀.γ, x * y = y * x := by
  refine commute_of_closure' ?_
  rintro x (hx | hx) y (hy | hy)
  · exact H.V_central hx (H.V_le_Q hy)
  · obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.mp hy
    exact H.V_central hx (hU.2.1 hyU)
  · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
    exact (H.V_central hy (hU.2.1 hxU)).symm
  · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨U', hU', hyU'⟩ := Set.mem_iUnion₂.mp hy
    have hUnot : U ∉ classOf V Q D₀.γ := fun h => hne (classOf_eq_of_mem_of_mem hU h)
    exact (H.commute_of_not_class D₀ hU' hU.1 hU.2.1 hU.2.2.1 hUnot y hyU' x hxU).symm

theorem classGroup_central_le (H : Hyp79 M V Q) {n : ℕ} {U₀ : Subgroup G}
    (D₀ : MulData V U₀ Q (GaloisField 2 n)) (hU₀g : ∃ g : G, U₀ = conjSubgroup g V)
    (hU₀Q : U₀ ≤ Q) (hU₀V : U₀ ≠ V) {u : G} (hu : u ∈ classGroup V Q D₀.γ)
    (huc : ∀ z ∈ classGroup V Q D₀.γ, z * u = u * z) : u ∈ V := by
  have hQ := Hyp79.eq_classGroup_sup_centralizer H D₀ hU₀g hU₀Q hU₀V
  have huQ : u ∈ Q := classGroup_le H.V_le_Q hu
  refine (H.modelCtx D₀).center_le u huQ fun y hy => ?_
  have hle : classGroup V Q D₀.γ ⊔ (Q ⊓ Subgroup.centralizer (classGroup V Q D₀.γ : Set G)) ≤
      Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun z hz => ?_) (fun c hc => ?_)
    · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      rw [Set.mem_singleton_iff.mp hw]
      exact (huc z hz).symm
    · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      rw [Set.mem_singleton_iff.mp hw]
      exact Subgroup.mem_centralizer_iff.mp hc.2 u hu
  have hy' : y ∈ classGroup V Q D₀.γ ⊔
      (Q ⊓ Subgroup.centralizer (classGroup V Q D₀.γ : Set G)) := by
    rw [← hQ]; exact hy
  exact Subgroup.mem_centralizer_iff.mp (hle hy') u rfl

end ClassGroups

section PolyLemmas

noncomputable def liftPoly (m : (ZMod 2)[X]) : ℕ[X] :=
  ∑ i ∈ Finset.range (m.natDegree + 1), monomial i (m.coeff i).val

theorem coeff_liftPoly (m : (ZMod 2)[X]) (i : ℕ) : (liftPoly m).coeff i = (m.coeff i).val := by
  simp only [liftPoly, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · have : m.natDegree < i := by omega
    rw [coeff_eq_zero_of_natDegree_lt this]
    simp

theorem exists_nat_poly {n : ℕ} (hn : n ≠ 0) (b : GaloisField 2 n) :
    ∃ p : ℕ[X], p.Monic ∧ p.natDegree ≤ n ∧
      p.eval₂ (Nat.castRingHom (GaloisField 2 n)) b = 0 := by
  classical
  set m := minpoly (ZMod 2) b with hm
  have hint : IsIntegral (ZMod 2) b := Algebra.IsIntegral.isIntegral b
  have hmon : m.Monic := minpoly.monic hint
  have hdeg : m.natDegree ≤ n := by
    have := minpoly.natDegree_le (A := ZMod 2) b
    rwa [GaloisField.finrank 2 hn] at this
  set p := liftPoly m with hp
  have hcoeff : ∀ i, p.coeff i = (m.coeff i).val := coeff_liftPoly m
  have hnat : p.natDegree = m.natDegree := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hcoeff, coeff_eq_zero_of_natDegree_lt hN]
      simp
    · apply le_natDegree_of_ne_zero
      rw [hcoeff, hmon.coeff_natDegree]
      simp
  refine ⟨p, ?_, hnat ▸ hdeg, ?_⟩
  · rw [Monic, leadingCoeff, hnat, hcoeff, hmon.coeff_natDegree]
    rfl
  · rw [eval₂_eq_sum_range]
    have h0 := minpoly.aeval (ZMod 2) b
    rw [aeval_eq_sum_range] at h0
    rw [hnat, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoeff, Algebra.smul_def]
    congr 1
    calc (Nat.castRingHom (GaloisField 2 n)) (m.coeff i).val
        = algebraMap (ZMod 2) (GaloisField 2 n) (((m.coeff i).val : ℕ) : ZMod 2) := by
          rw [map_natCast]; rfl
      _ = algebraMap (ZMod 2) (GaloisField 2 n) (m.coeff i) := by
          rw [ZMod.natCast_zmod_val]

theorem addmap_one {K : Type} [Field K] {V : Subgroup G} {f : G → K}
    (hadd : ∀ x ∈ V, ∀ y ∈ V, f (x * y) = f x + f y) : f 1 = 0 := by
  have := hadd 1 V.one_mem 1 V.one_mem
  rw [mul_one] at this
  exact left_eq_add.mp this

theorem addmap_pow {K : Type} [Field K] {V : Subgroup G} {f : G → K}
    (hadd : ∀ x ∈ V, ∀ y ∈ V, f (x * y) = f x + f y) {x : G} (hx : x ∈ V) (k : ℕ) :
    f (x ^ k) = k • f x := by
  induction k with
  | zero => simp [addmap_one hadd]
  | succ k ih => rw [pow_succ, hadd _ (Subgroup.pow_mem _ hx _) _ hx, ih, succ_nsmul]

theorem addmap_prod_range {K : Type} [Field K] {V : Subgroup G} {f : G → K}
    (hadd : ∀ x ∈ V, ∀ y ∈ V, f (x * y) = f x + f y) (ws : ℕ → G) (hws : ∀ i, ws i ∈ V)
    (c : ℕ → ℕ) (m : ℕ) :
    f (((List.range m).map fun i => (ws i) ^ (c i)).prod) =
      ∑ i ∈ Finset.range m, c i • f (ws i) := by
  induction m with
  | zero => simp [addmap_one hadd]
  | succ m ih =>
    have hpre : ((List.range m).map fun i => (ws i) ^ (c i)).prod ∈ V := by
      apply Subgroup.list_prod_mem
      intro z hz
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      exact Subgroup.pow_mem _ (hws i) _
    rw [List.range_succ, List.map_append, List.prod_append, Finset.sum_range_succ, ← ih]
    rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      hadd _ hpre _ (Subgroup.pow_mem _ (hws m) _), addmap_pow hadd (hws m)]

theorem poly_transfer {K : Type} [Field K] {V : Subgroup G} {f₁ f₂ : G → K} {τ : G} {α β : K}
    (hτV : ∀ v ∈ V, τ * v * τ⁻¹ ∈ V)
    (h₁add : ∀ x ∈ V, ∀ y ∈ V, f₁ (x * y) = f₁ x + f₁ y)
    (h₁inj : ∀ x ∈ V, f₁ x = 0 → x = 1)
    (h₂add : ∀ x ∈ V, ∀ y ∈ V, f₂ (x * y) = f₂ x + f₂ y)
    (h₂inj : ∀ x ∈ V, f₂ x = 0 → x = 1)
    (hα : ∀ v ∈ V, f₁ (τ * v * τ⁻¹) = α * f₁ v) (hβ : ∀ v ∈ V, f₂ (τ * v * τ⁻¹) = β * f₂ v)
    {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀1 : v₀ ≠ 1) (p : ℕ[X])
    (hp : p.eval₂ (Nat.castRingHom K) α = 0) : p.eval₂ (Nat.castRingHom K) β = 0 := by
  have hws : ∀ i : ℕ, τ ^ i * v₀ * (τ ^ i)⁻¹ ∈ V := by
    intro i
    induction i with
    | zero => simpa using hv₀
    | succ i ih =>
      have := hτV _ ih
      rwa [show τ * (τ ^ i * v₀ * (τ ^ i)⁻¹) * τ⁻¹ = τ ^ (i + 1) * v₀ * (τ ^ (i + 1))⁻¹ by
        rw [pow_succ']; group] at this
  have hconj : ∀ i : ℕ, τ ^ (i + 1) * v₀ * (τ ^ (i + 1))⁻¹ =
      τ * (τ ^ i * v₀ * (τ ^ i)⁻¹) * τ⁻¹ := by
    intro i; rw [pow_succ']; group
  have hf₁ : ∀ i : ℕ, f₁ (τ ^ i * v₀ * (τ ^ i)⁻¹) = α ^ i * f₁ v₀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [hconj i, hα _ (hws i), ih, pow_succ]; ring
  have hf₂ : ∀ i : ℕ, f₂ (τ ^ i * v₀ * (τ ^ i)⁻¹) = β ^ i * f₂ v₀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [hconj i, hβ _ (hws i), ih, pow_succ]; ring
  have hℓV : (((List.range (p.natDegree + 1)).map fun i =>
      (τ ^ i * v₀ * (τ ^ i)⁻¹) ^ p.coeff i).prod) ∈ V := by
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
    exact Subgroup.pow_mem _ (hws i) _
  have hcast : ∀ n : ℕ, (Nat.castRingHom K) n = (n : K) := fun n => rfl
  have hs₁ := addmap_prod_range h₁add (fun i => τ ^ i * v₀ * (τ ^ i)⁻¹) hws (fun i => p.coeff i)
    (p.natDegree + 1)
  have hs₂ := addmap_prod_range h₂add (fun i => τ ^ i * v₀ * (τ ^ i)⁻¹) hws (fun i => p.coeff i)
    (p.natDegree + 1)
  have e₁ : f₁ (((List.range (p.natDegree + 1)).map fun i =>
      (τ ^ i * v₀ * (τ ^ i)⁻¹) ^ p.coeff i).prod) =
      p.eval₂ (Nat.castRingHom K) α * f₁ v₀ := by
    rw [hs₁, eval₂_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf₁ i, nsmul_eq_mul, hcast]
    ring
  have e₂ : f₂ (((List.range (p.natDegree + 1)).map fun i =>
      (τ ^ i * v₀ * (τ ^ i)⁻¹) ^ p.coeff i).prod) =
      p.eval₂ (Nat.castRingHom K) β * f₂ v₀ := by
    rw [hs₂, eval₂_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf₂ i, nsmul_eq_mul, hcast]
    ring
  have hℓ1 := h₁inj _ hℓV (by rw [e₁, hp, zero_mul])
  have h0 : f₂ (((List.range (p.natDegree + 1)).map fun i =>
      (τ ^ i * v₀ * (τ ^ i)⁻¹) ^ p.coeff i).prod) = 0 := by
    rw [hℓ1]; exact addmap_one h₂add
  have hne : f₂ v₀ ≠ 0 := fun h => hv₀1 (h₂inj v₀ hv₀ h)
  rw [e₂] at h0
  exact (mul_eq_zero.mp h0).resolve_right hne

end PolyLemmas

section NatRel

theorem natData_transfer {g : G} {n : ℕ} (N : NatData V Q g n)
    (D : MulData V (conjSubgroup g V) Q (GaloisField 2 n)) {τ : G}
    (hτH : τ ∈ Q ⊔ conjSubgroup g Q) (hτV : τ ∈ Subgroup.normalizer (V : Set G))
    {a : GaloisField 2 n} (hγ : ∀ v ∈ V, D.γ (τ * v * τ⁻¹) = a * D.γ v)
    {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀1 : v₀ ≠ 1) :
    ((N.φ ⟨τ, hτH⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 1 0 = 0 ∧
    ∀ p : ℕ[X], p.eval₂ (Nat.castRingHom (GaloisField 2 n)) a = 0 →
      p.eval₂ (Nat.castRingHom (GaloisField 2 n))
        (((N.φ ⟨τ, hτH⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 0) = 0 := by
  classical
  have hVW : V ≤ V ⊔ conjSubgroup g V := le_sup_left
  set A : Matrix (Fin 2) (Fin 2) (GaloisField 2 n) :=
    ((N.φ ⟨τ, hτH⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) with hA
  let c : G → GaloisField 2 n := fun v =>
    if h : v ∈ V ⊔ conjSubgroup g V then Multiplicative.toAdd (N.ψ ⟨v, h⟩) 0 else 0
  have hc : ∀ v (hv : v ∈ V), c v = Multiplicative.toAdd (N.ψ ⟨v, hVW hv⟩) 0 := by
    intro v hv
    simp only [c, dif_pos (hVW hv)]
  have hτV' : ∀ v ∈ V, τ * v * τ⁻¹ ∈ V := fun v hv => (mem_iff_conj_of_normalizer hτV v).mp hv
  have hcadd : ∀ x ∈ V, ∀ y ∈ V, c (x * y) = c x + c y := by
    intro x hx y hy
    rw [hc _ (V.mul_mem hx hy), hc x hx, hc y hy]
    have : (⟨x * y, hVW (V.mul_mem hx hy)⟩ : ↥(V ⊔ conjSubgroup g V)) =
        ⟨x, hVW hx⟩ * ⟨y, hVW hy⟩ := rfl
    rw [this, map_mul, toAdd_mul]
    rfl
  have hsecond : ∀ v (hv : v ∈ V), Multiplicative.toAdd (N.ψ ⟨v, hVW hv⟩) 1 = 0 :=
    fun v hv => (N.hV ⟨v, hVW hv⟩).mp hv
  have hcinj : ∀ x ∈ V, c x = 0 → x = 1 := by
    intro x hx h0
    rw [hc x hx] at h0
    have h2 : N.ψ ⟨x, hVW hx⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      funext i
      fin_cases i
      · exact h0
      · exact hsecond x hx
    have := (N.ψ.map_eq_one_iff).mp h2
    exact congrArg Subtype.val this
  have hcomp : ∀ v (hv : v ∈ V),
      Multiplicative.toAdd (N.ψ ⟨τ * v * τ⁻¹, hVW (hτV' v hv)⟩) =
        A *ᵥ Multiplicative.toAdd (N.ψ ⟨v, hVW hv⟩) :=
    fun v hv => N.compat ⟨τ, hτH⟩ ⟨v, hVW hv⟩ ⟨τ * v * τ⁻¹, hVW (hτV' v hv)⟩ rfl
  have hscale : ∀ v ∈ V, c (τ * v * τ⁻¹) = A 0 0 * c v := by
    intro v hv
    rw [hc _ (hτV' v hv), hc v hv, hcomp v hv]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsecond v hv]
  have hlow : ∀ v ∈ V, A 1 0 * c v = 0 := by
    intro v hv
    have e := congrFun (hcomp v hv) 1
    rw [hsecond _ (hτV' v hv)] at e
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsecond v hv] at e
    rw [hc v hv]
    rcases e with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  have hc0 : c v₀ ≠ 0 := fun h => hv₀1 (hcinj v₀ hv₀ h)
  refine ⟨?_, fun p hp => ?_⟩
  · exact (mul_eq_zero.mp (hlow v₀ hv₀)).resolve_right hc0
  · exact poly_transfer hτV' D.γ_add D.γ_inj hcadd hcinj hγ hscale hv₀ hv₀1 p hp

end NatRel

end CFSG.RankThree.GF2n.Stroth80.FieldModel
