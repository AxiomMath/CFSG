module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenCfg
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenHeartNorm
import CFSG.CGT.PushingUpLit.SolK.PermBlock
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Theta

theorem exists_addEquiv_of_surjective {A B : Type*} [Group A] [AddGroup B]
    (β : A →* Multiplicative B) (hβ : Function.Surjective β) (c : A ≃* A)
    (hc : ∀ u, β (c u) = 1 ↔ β u = 1) :
    ∃ γ : B ≃+ B, ∀ u, γ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (c u)) := by
  let g : Multiplicative B →* Multiplicative B :=
    β.liftOfSurjective hβ ⟨β.comp c.toMonoidHom, fun u hu => by
      rw [MonoidHom.mem_ker] at hu ⊢
      exact (hc u).2 hu⟩
  have hg : ∀ u, g (β u) = β (c u) := fun u => by
    simp only [g, MonoidHom.liftOfRightInverse_comp_apply, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom]
  let γ₀ : B →+ B := AddMonoidHom.toMultiplicative.symm g
  have hγ₀ : ∀ u, γ₀ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (c u)) := fun u =>
    congrArg Multiplicative.toAdd (hg u)
  have hinj : Function.Injective γ₀ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd b)
    have hb' : b = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    rw [hb', hγ₀] at hb
    have h1 : β (c u) = 1 := by simpa using hb
    rw [hb', (hc u).1 h1]
    rfl
  have hsurj : Function.Surjective γ₀ := by
    intro b
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd b)
    refine ⟨Multiplicative.toAdd (β (c.symm u)), ?_⟩
    rw [hγ₀, MulEquiv.apply_symm_apply, hu]
    rfl
  exact ⟨AddEquiv.ofBijective γ₀ ⟨hinj, hsurj⟩, hγ₀⟩

structure TypeData (G : Type) [Group G] (X : Subgroup G) (n : ℕ) where
  α : ↥X →* alternatingGroup (Fin n)
  α_surj : Function.Surjective α
  α_ker : α.ker = CFSG.pCore 2 ↥X
  β : ↥(blockU X) →* Multiplicative (altHeart n)
  β_surj : Function.Surjective β
  β_ker : β.ker = (blockZ X).subgroupOf (blockU X)
  equivar : ∀ (ℓ : ↥X) (u v : ↥(blockU X)), (v : G) = ℓ * u * ℓ⁻¹ → ∀ x : evenWeight n,
    Multiplicative.toAdd (β u) = (x : altHeart n) →
    Multiplicative.toAdd (β v) = (evenWeightPerm (α ℓ : Equiv.Perm (Fin n)) x : altHeart n)

namespace TypeData

variable {G : Type} [Group G] {X : Subgroup G} {n : ℕ} (T : TypeData G X n)

theorem nonempty_of_isAltNaturalType (h : IsAltNaturalType X n) : Nonempty (TypeData G X n) := by
  obtain ⟨α, hα, hαk, β, hβ, hβk, heq⟩ := h
  exact ⟨⟨α, hα, hαk, β, hβ, hβk, heq⟩⟩

theorem beta_equivar (ℓ : ↥X) (u v : ↥(blockU X)) (h : (v : G) = ℓ * u * ℓ⁻¹) :
    Multiplicative.toAdd (T.β v) =
      altAct (T.α ℓ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (T.β u)) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (T.β u))
  rw [← hx, altAct_mk]
  exact T.equivar ℓ u v h x hx.symm

theorem beta_eq_one_iff (u : ↥(blockU X)) :
    T.β u = 1 ↔ (u : G) ∈ Subgroup.centralizer (X : Set G) := by
  rw [← MonoidHom.mem_ker, T.β_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨u.2, h⟩⟩

end TypeData

section Action

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : Setting G M X n)

include S in
theorem conj_mem_centralizer_of_mem {m : G} (hm : m ∈ M) {z : G}
    (hz : z ∈ Subgroup.centralizer (X : Set G)) :
    m * z * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro x hx
  have hx' : m⁻¹ * x * m ∈ X := by simpa using S.normal (M.inv_mem hm) hx
  have h := hz _ hx'
  calc x * (m * z * m⁻¹) = m * ((m⁻¹ * x * m) * z) * m⁻¹ := by group
    _ = m * (z * (m⁻¹ * x * m)) * m⁻¹ := by rw [h]
    _ = m * z * m⁻¹ * x := by group

@[expose] def conjU {m : G} (hm : m ∈ M) : MulAut ↥(blockU X) where
  toFun w := ⟨m * (w : G) * m⁻¹, S.W_normalized hm w.2⟩
  invFun w := ⟨m⁻¹ * (w : G) * m, by simpa using S.W_normalized (M.inv_mem hm) w.2⟩
  left_inv w := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjU_apply {m : G} (hm : m ∈ M) (w : ↥(blockU X)) :
    ((conjU S hm w : ↥(blockU X)) : G) = m * (w : G) * m⁻¹ := rfl

namespace TypeData

variable (T : TypeData G X n)

theorem beta_conjU_eq_one_iff {m : G} (hm : m ∈ M) (u : ↥(blockU X)) :
    T.β (conjU S hm u) = 1 ↔ T.β u = 1 := by
  rw [T.beta_eq_one_iff, T.beta_eq_one_iff, conjU_apply]
  refine ⟨fun h => ?_, conj_mem_centralizer_of_mem S hm⟩
  have := conj_mem_centralizer_of_mem S (M.inv_mem hm) h
  simpa [mul_assoc] using this

def ActsAs (m : G) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v : ↥(blockU X), (v : G) = m * u * m⁻¹ →
    Multiplicative.toAdd (T.β v) = altAct π (Multiplicative.toAdd (T.β u))

include S in
theorem ActsAs.unique (hn : 5 ≤ n) {m : G} (hm : m ∈ M) {π π' : Equiv.Perm (Fin n)}
    (h : T.ActsAs m π) (h' : T.ActsAs m π') : π = π' := by
  refine (altAct_eq_iff hn).1 fun w => ?_
  obtain ⟨u, hu⟩ := T.β_surj (Multiplicative.ofAdd w)
  have hw : w = Multiplicative.toAdd (T.β u) := by rw [hu]; rfl
  rw [hw, ← h u (conjU S hm u) rfl, ← h' u (conjU S hm u) rfl]

include S in
theorem ActsAs.mul {a b : G} (hb : b ∈ M) {π π' : Equiv.Perm (Fin n)} (ha : T.ActsAs a π)
    (hb' : T.ActsAs b π') : T.ActsAs (a * b) (π * π') := by
  intro u v h
  have h1 := hb' u (conjU S hb u) rfl
  have h2 := ha (conjU S hb u) v (by rw [h, conjU_apply]; group)
  rw [h2, h1, altAct_mul]

theorem actsAs_of_mem (x : ↥X) : T.ActsAs (x : G) (T.α x : Equiv.Perm (Fin n)) :=
  fun u v h => T.beta_equivar x u v h

include S in
theorem exists_actsAs (hN : NormalizerIsSym n) {m : G} (hm : m ∈ M) :
    ∃ π : Equiv.Perm (Fin n), T.ActsAs m π := by
  have hc : ∀ u : ↥(blockU X), T.β (conjU S hm u) = 1 ↔ T.β u = 1 :=
    T.beta_conjU_eq_one_iff S hm
  obtain ⟨γ, hγ⟩ := exists_addEquiv_of_surjective T.β T.β_surj (conjU S hm) hc
  have key : ∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
      ∀ v, γ (altAct σ v) = altAct σ' (γ v) := by
    intro σ hσ
    obtain ⟨x, hx⟩ := T.α_surj ⟨σ, hσ⟩
    let x' : ↥X := ⟨m * (x : G) * m⁻¹, S.normal hm x.2⟩
    refine ⟨(T.α x' : Equiv.Perm (Fin n)), (T.α x').2, fun v => ?_⟩
    obtain ⟨u, hu⟩ := T.β_surj (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (T.β u) := by rw [hu]; rfl
    have hσx : σ = (T.α x : Equiv.Perm (Fin n)) := by rw [hx]
    let u₁ : ↥(blockU X) := ⟨(x : G) * u * (x : G)⁻¹, S.W_normalized (S.le x.2) u.2⟩
    have h1 : altAct σ v = Multiplicative.toAdd (T.β u₁) := by
      rw [hσx, hv]
      exact (T.beta_equivar x u u₁ rfl).symm
    have h2 : γ v = Multiplicative.toAdd (T.β (conjU S hm u)) := by rw [hv, hγ]
    rw [h1, hγ u₁, h2]
    exact T.beta_equivar x' (conjU S hm u) (conjU S hm u₁) (by
      rw [conjU_apply, conjU_apply]
      show m * ((x : G) * u * (x : G)⁻¹) * m⁻¹ = (m * (x : G) * m⁻¹) * (m * (u : G) * m⁻¹) *
        (m * (x : G) * m⁻¹)⁻¹
      group)
  obtain ⟨π, hπ⟩ := hN γ key
  refine ⟨π, fun u v h => ?_⟩
  have hvu : v = conjU S hm u := Subtype.ext h
  rw [hvu, ← hγ u, hπ]

noncomputable def thetaFun (hN : NormalizerIsSym n) (m : ↥M) : Equiv.Perm (Fin n) :=
  Classical.choose (T.exists_actsAs S hN m.2)

theorem thetaFun_spec (hN : NormalizerIsSym n) (m : ↥M) : T.ActsAs (m : G) (T.thetaFun S hN m) :=
  Classical.choose_spec (T.exists_actsAs S hN m.2)

@[expose] noncomputable def theta (hn : 5 ≤ n) (hN : NormalizerIsSym n) :
    ↥M →* Equiv.Perm (Fin n) :=
  MonoidHom.mk' (T.thetaFun S hN) fun a b =>
    ActsAs.unique S T hn (M.mul_mem a.2 b.2) (T.thetaFun_spec S hN (a * b))
      (ActsAs.mul S T b.2 (T.thetaFun_spec S hN a) (T.thetaFun_spec S hN b))

theorem theta_spec (hn : 5 ≤ n) (hN : NormalizerIsSym n) (m : ↥M) :
    T.ActsAs (m : G) (T.theta S hn hN m) :=
  T.thetaFun_spec S hN m

theorem theta_X (hn : 5 ≤ n) (hN : NormalizerIsSym n) (x : ↥X) :
    T.theta S hn hN ⟨(x : G), S.le x.2⟩ = (T.α x : Equiv.Perm (Fin n)) :=
  ActsAs.unique S T hn (S.le x.2) (T.theta_spec S hn hN ⟨(x : G), S.le x.2⟩)
    (T.actsAs_of_mem x)

end TypeData

end Action

end Theta

theorem Setting.five_le_degree {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}
    (S : Setting G M X n) : 5 ≤ n := by
  rcases S.n_mem with h | h | h <;> omega

theorem exists_cfg_of_normalizer {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}
    (S : Setting G M X n) (hn : 5 ≤ n) (hN : NormalizerIsSym n) : Nonempty (Cfg G M X n) := by
  obtain ⟨T⟩ := Theta.TypeData.nonempty_of_isAltNaturalType S.type
  exact ⟨{ S := S
           α := T.α
           α_surj := T.α_surj
           α_ker := T.α_ker
           β := T.β
           β_surj := T.β_surj
           β_ker := T.β_ker
           θ := T.theta S hn hN
           θ_spec := fun m u v h => T.theta_spec S hn hN m u v h
           θ_X := fun x => T.theta_X S hn hN x }⟩

theorem exists_cfg_six {G : Type} [Group G] [Finite G] {M X : Subgroup G}
    (S : Setting G M X 6) : Nonempty (Cfg G M X 6) :=
  exists_cfg_of_normalizer S (by norm_num) normalizerIsSym_six

theorem exists_cfg_of_setting {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}
    (S : Setting G M X n) : Nonempty (Cfg G M X n) :=
  exists_cfg_of_normalizer S S.five_le_degree
    (normalizerIsSym_of_six_or_seven_le (by rcases S.n_mem with h | h | h <;> omega))

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

theorem theta_eq_one_iff (hn : 5 ≤ n) (m : ↥M) :
    C.θ m = 1 ↔ ∀ (u v : ↥(blockU X)), (v : G) = m * u * m⁻¹ → C.β v = C.β u := by
  constructor
  · intro h u v hv
    have h1 := C.θ_spec m u v hv
    rw [h, altAct_one] at h1
    exact Multiplicative.toAdd.injective h1
  · intro h
    refine (altAct_eq_iff hn).1 fun w => ?_
    obtain ⟨u, hu⟩ := C.β_surj (Multiplicative.ofAdd w)
    have hw : w = Multiplicative.toAdd (C.β u) := by rw [hu]; rfl
    let v : ↥(blockU X) := ⟨(m : G) * u * (m : G)⁻¹, C.S.W_normalized m.2 u.2⟩
    have h1 := C.θ_spec m u v rfl
    rw [h u v rfl] at h1
    rw [altAct_one, hw, ← h1]

theorem exists_lift {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    ∃ x : ↥X, C.θ ⟨(x : G), C.S.le x.2⟩ = σ := by
  obtain ⟨x, hx⟩ := C.α_surj ⟨σ, hσ⟩
  refine ⟨x, ?_⟩
  rw [C.θ_X x, hx]

theorem theta_Q (hn : 5 ≤ n) {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) :
    C.θ ⟨q, pCoreOf_le_self M hq⟩ = 1 := by
  obtain ⟨q', hq', hq'q⟩ := Subgroup.mem_map.1 hq
  have hqq : (⟨q, pCoreOf_le_self M hq⟩ : ↥M) = q' := Subtype.ext hq'q.symm
  rw [hqq]
  let N : Subgroup (Equiv.Perm (Fin n)) := (CFSG.pCore 2 ↥M).map C.θ
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup.map C.θ
  have hnorm : ∀ τ ∈ altOn (Finset.univ : Finset (Fin n)), ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := by
    intro τ hτ σ hσ
    have hτA : τ ∈ alternatingGroup (Fin n) :=
      Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2
    obtain ⟨x, hx⟩ := C.exists_lift hτA
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hσ
    refine Subgroup.mem_map.2 ⟨⟨(x : G), C.S.le x.2⟩ * s * ⟨(x : G), C.S.le x.2⟩⁻¹,
      Subgroup.Normal.conj_mem inferInstance s hs _, ?_⟩
    rw [map_mul, map_mul, map_inv, hx]
  have hfix := block_fixes hN2 (fun σ _ x => by simp) hnorm
    (Or.inr (Or.inr (by simpa using hn)))
  exact Equiv.ext fun a => hfix _ (Subgroup.mem_map_of_mem _ hq') a (Finset.mem_univ a)

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven
