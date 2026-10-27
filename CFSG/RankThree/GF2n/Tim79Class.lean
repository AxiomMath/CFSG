module

public import CFSG.RankThree.GF2n.Tim79CentBasic

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

@[expose] def classOf (V Q : Subgroup G) {K : Type} [Field K] (γ₀ : G → K) : Set (Subgroup G) :=
  {U | (∃ g : G, U = conjSubgroup g V) ∧ U ≤ Q ∧ U ≠ V ∧
    ∃ D : MulData V U Q K, ∃ (c : K) (σ : K ≃+* K), c ≠ 0 ∧ ∀ v ∈ V, D.γ v = c * σ (γ₀ v)}

@[expose] def classGroup (V Q : Subgroup G) {K : Type} [Field K] (γ₀ : G → K) : Subgroup G :=
  Subgroup.closure ((V : Set G) ∪ ⋃ U ∈ classOf V Q γ₀, (U : Set G))

@[expose] def GammaCompat (V : Subgroup G) {K : Type} [Field K] (γ γ' : G → K) : Prop :=
  ∃ (c : K) (σ : K ≃+* K), c ≠ 0 ∧ ∀ v ∈ V, γ' v = c * σ (γ v)

namespace GammaCompat

variable {V : Subgroup G} {K : Type} [Field K] {γ γ' γ'' : G → K}

theorem refl (V : Subgroup G) (γ : G → K) : GammaCompat V γ γ :=
  ⟨1, RingEquiv.refl K, one_ne_zero, fun v _ => by simp⟩

theorem symm (h : GammaCompat V γ γ') : GammaCompat V γ' γ := by
  obtain ⟨c, σ, hc, h⟩ := h
  refine ⟨σ.symm c⁻¹, σ.symm, by simpa using hc, fun v hv => ?_⟩
  rw [h v hv, ← map_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, RingEquiv.symm_apply_apply]

theorem trans (h : GammaCompat V γ γ') (h' : GammaCompat V γ' γ'') : GammaCompat V γ γ'' := by
  obtain ⟨c, σ, hc, h⟩ := h
  obtain ⟨c', σ', hc', h'⟩ := h'
  refine ⟨c' * σ' c, σ.trans σ', mul_ne_zero hc' (by simpa using hc), fun v hv => ?_⟩
  rw [h' v hv, h v hv, map_mul, RingEquiv.trans_apply, mul_assoc]

end GammaCompat

section Class

variable {V Q U : Subgroup G} {K : Type} [Field K] {γ γ' : G → K}

theorem classOf_congr (h : GammaCompat V γ γ') : classOf V Q γ' = classOf V Q γ := by
  ext U
  constructor
  · rintro ⟨hg, hUQ, hUV, D, hD⟩
    exact ⟨hg, hUQ, hUV, D, GammaCompat.trans h (hD : GammaCompat V γ' D.γ)⟩
  · rintro ⟨hg, hUQ, hUV, D, hD⟩
    exact ⟨hg, hUQ, hUV, D, GammaCompat.trans h.symm (hD : GammaCompat V γ D.γ)⟩

theorem classOf_eq_of_mem {V Q U₀ U : Subgroup G} {K : Type} [Field K] [Finite K]
    (D₀ : MulData V U₀ Q K) (hU : U ∈ classOf V Q D₀.γ) (D : MulData V U Q K) :
    classOf V Q D.γ = classOf V Q D₀.γ := by
  obtain ⟨-, -, -, D'', hD''⟩ := hU
  exact classOf_congr (GammaCompat.trans (hD'' : GammaCompat V D₀.γ D''.γ)
    (MulData.compat_same D'' D : GammaCompat V D''.γ D.γ))

theorem mem_classOf_self {U₀ : Subgroup G} (D₀ : MulData V U₀ Q K)
    (hg : ∃ g : G, U₀ = conjSubgroup g V) (hQ : U₀ ≤ Q) (hV : U₀ ≠ V) :
    U₀ ∈ classOf V Q D₀.γ :=
  ⟨hg, hQ, hV, D₀, GammaCompat.refl V D₀.γ⟩

theorem classOf_eq_of_mem_of_mem {γ' : G → K} (h : U ∈ classOf V Q γ) (h' : U ∈ classOf V Q γ') :
    classOf V Q γ = classOf V Q γ' := by
  obtain ⟨-, -, -, D, hD⟩ := h
  obtain ⟨-, -, -, D', hD'⟩ := h'
  have h1 : GammaCompat V γ γ' :=
    GammaCompat.trans (GammaCompat.trans (hD : GammaCompat V γ D.γ)
      (MulData.compat_same D D' : GammaCompat V D.γ D'.γ))
      (GammaCompat.symm (hD' : GammaCompat V γ' D'.γ))
  exact (classOf_congr h1).symm

theorem le_classGroup_of_mem (hU : U ∈ classOf V Q γ) : U ≤ classGroup V Q γ :=
  fun _ hu => Subgroup.subset_closure (Or.inr (Set.mem_iUnion₂.mpr ⟨U, hU, hu⟩))

theorem V_le_classGroup : V ≤ classGroup V Q γ :=
  fun _ hv => Subgroup.subset_closure (Or.inl hv)

theorem classGroup_ne_of_mem [Finite G] (hU : U ∈ classOf V Q γ) : classGroup V Q γ ≠ V := by
  obtain ⟨⟨g, hg⟩, -, hUV, -⟩ := id hU
  intro h
  apply hUV
  have hle : U ≤ V := h ▸ le_classGroup_of_mem hU
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hg, card_conjSubgroup])

theorem classGroup_le (hVQ : V ≤ Q) : classGroup V Q γ ≤ Q := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (hx | hx)
  · exact hVQ hx
  · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
    exact hU.2.1 hxU

end Class

theorem mem_iff_conj_of_normalizer {S : Subgroup G} {τ : G}
    (h : τ ∈ Subgroup.normalizer (S : Set G)) (x : G) : x ∈ S ↔ τ * x * τ⁻¹ ∈ S :=
  Subgroup.mem_normalizer_iff.mp h x

theorem mem_iff_conj_inv_of_normalizer {S : Subgroup G} {τ : G}
    (h : τ ∈ Subgroup.normalizer (S : Set G)) (x : G) : x ∈ S ↔ τ⁻¹ * x * τ ∈ S := by
  simpa using Subgroup.mem_normalizer_iff.mp (inv_mem h) x

theorem eq_one_of_conj_inv_eq_one {τ a : G} (h : τ⁻¹ * a * τ = 1) : a = 1 := by
  calc a = τ * (τ⁻¹ * a * τ) * τ⁻¹ := by group
    _ = 1 := by rw [h]; group

namespace MulData

variable {V U Q : Subgroup G} {K : Type} [Field K]

theorem natCard_V (D : MulData V U Q K) : Nat.card V = Nat.card K := by
  refine Nat.card_congr (Equiv.ofBijective (fun v : V => D.γ v) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (D.eq_of_γ_eq a.2 b.2 h)
  · intro s
    obtain ⟨a, ha, hs⟩ := D.γ_surj s
    exact ⟨⟨a, ha⟩, hs⟩

@[expose] def mapRingEquiv {K' : Type} [Field K'] (D : MulData V U Q K) (e : K ≃+* K') :
    MulData V U Q K' where
  γ := fun v => e (D.γ v)
  ψ := fun u => e (D.ψ u)
  t := fun y => e (D.t y)
  γ_add := fun a ha b hb => by
    show e (D.γ (a * b)) = e (D.γ a) + e (D.γ b)
    rw [D.γ_add a ha b hb, map_add]
  γ_inj := fun a ha h => D.γ_inj a ha (e.injective (by rw [map_zero]; exact h))
  γ_surj := fun s => by
    obtain ⟨a, ha, h⟩ := D.γ_surj (e.symm s)
    exact ⟨a, ha, by show e (D.γ a) = s; rw [h, RingEquiv.apply_symm_apply]⟩
  ψ_add := fun a ha b hb => by
    show e (D.ψ (a * b)) = e (D.ψ a) + e (D.ψ b)
    rw [D.ψ_add a ha b hb, map_add]
  ψ_inj := fun a ha h => D.ψ_inj a ha (e.injective (by rw [map_zero]; exact h))
  ψ_surj := fun s => by
    obtain ⟨a, ha, h⟩ := D.ψ_surj (e.symm s)
    exact ⟨a, ha, by show e (D.ψ a) = s; rw [h, RingEquiv.apply_symm_apply]⟩
  t_add := fun a ha b hb => by
    show e (D.t (a * b)) = e (D.t a) + e (D.t b)
    rw [D.t_add a ha b hb, map_add]
  t_surj := fun s => by
    obtain ⟨a, ha, h⟩ := D.t_surj (e.symm s)
    exact ⟨a, ha, by show e (D.t a) = s; rw [h, RingEquiv.apply_symm_apply]⟩
  t_ker := fun a ha => by
    rw [← D.t_ker a ha]
    exact map_eq_zero_iff e e.injective
  comm := fun y hy u hu => by
    obtain ⟨h1, h2⟩ := D.comm y hy u hu
    exact ⟨h1, by show e (D.γ ⁅y, u⁆) = e (D.t y) * e (D.ψ u); rw [h2, map_mul]⟩

@[simp] theorem mapRingEquiv_γ {K' : Type} [Field K'] (D : MulData V U Q K) (e : K ≃+* K')
    (v : G) : (D.mapRingEquiv e).γ v = e (D.γ v) := rfl

@[simp] theorem mapRingEquiv_ψ {K' : Type} [Field K'] (D : MulData V U Q K) (e : K ≃+* K')
    (u : G) : (D.mapRingEquiv e).ψ u = e (D.ψ u) := rfl

@[simp] theorem mapRingEquiv_t {K' : Type} [Field K'] (D : MulData V U Q K) (e : K ≃+* K')
    (y : G) : (D.mapRingEquiv e).t y = e (D.t y) := rfl

@[expose] def conjData (D : MulData V U Q K) {τ : G} (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) : MulData V (conjSubgroup τ U) Q K where
  γ := fun v => D.γ (τ⁻¹ * v * τ)
  ψ := fun u => D.ψ (τ⁻¹ * u * τ)
  t := fun y => D.t (τ⁻¹ * y * τ)
  γ_add := fun a ha b hb => by
    show D.γ (τ⁻¹ * (a * b) * τ) = D.γ (τ⁻¹ * a * τ) + D.γ (τ⁻¹ * b * τ)
    rw [show τ⁻¹ * (a * b) * τ = (τ⁻¹ * a * τ) * (τ⁻¹ * b * τ) by group]
    exact D.γ_add _ ((mem_iff_conj_inv_of_normalizer hV a).mp ha) _
      ((mem_iff_conj_inv_of_normalizer hV b).mp hb)
  γ_inj := fun a ha h =>
    eq_one_of_conj_inv_eq_one (D.γ_inj _ ((mem_iff_conj_inv_of_normalizer hV a).mp ha) h)
  γ_surj := fun s => by
    obtain ⟨b, hb, hs⟩ := D.γ_surj s
    refine ⟨τ * b * τ⁻¹, (mem_iff_conj_of_normalizer hV b).mp hb, ?_⟩
    show D.γ (τ⁻¹ * (τ * b * τ⁻¹) * τ) = s
    rw [show τ⁻¹ * (τ * b * τ⁻¹) * τ = b by group]
    exact hs
  ψ_add := fun a ha b hb => by
    show D.ψ (τ⁻¹ * (a * b) * τ) = D.ψ (τ⁻¹ * a * τ) + D.ψ (τ⁻¹ * b * τ)
    rw [show τ⁻¹ * (a * b) * τ = (τ⁻¹ * a * τ) * (τ⁻¹ * b * τ) by group]
    exact D.ψ_add _ (mem_conjSubgroup.mp ha) _ (mem_conjSubgroup.mp hb)
  ψ_inj := fun a ha h => eq_one_of_conj_inv_eq_one (D.ψ_inj _ (mem_conjSubgroup.mp ha) h)
  ψ_surj := fun s => by
    obtain ⟨b, hb, hs⟩ := D.ψ_surj s
    refine ⟨τ * b * τ⁻¹, mem_conjSubgroup.mpr
      (by rw [show τ⁻¹ * (τ * b * τ⁻¹) * τ = b by group]; exact hb), ?_⟩
    show D.ψ (τ⁻¹ * (τ * b * τ⁻¹) * τ) = s
    rw [show τ⁻¹ * (τ * b * τ⁻¹) * τ = b by group]
    exact hs
  t_add := fun a ha b hb => by
    show D.t (τ⁻¹ * (a * b) * τ) = D.t (τ⁻¹ * a * τ) + D.t (τ⁻¹ * b * τ)
    rw [show τ⁻¹ * (a * b) * τ = (τ⁻¹ * a * τ) * (τ⁻¹ * b * τ) by group]
    exact D.t_add _ ((mem_iff_conj_inv_of_normalizer hQ a).mp ha) _
      ((mem_iff_conj_inv_of_normalizer hQ b).mp hb)
  t_surj := fun s => by
    obtain ⟨b, hb, hs⟩ := D.t_surj s
    refine ⟨τ * b * τ⁻¹, (mem_iff_conj_of_normalizer hQ b).mp hb, ?_⟩
    show D.t (τ⁻¹ * (τ * b * τ⁻¹) * τ) = s
    rw [show τ⁻¹ * (τ * b * τ⁻¹) * τ = b by group]
    exact hs
  t_ker := fun a ha => by
    show D.t (τ⁻¹ * a * τ) = 0 ↔ a ∈ Subgroup.centralizer (conjSubgroup τ U : Set G)
    rw [D.t_ker _ ((mem_iff_conj_inv_of_normalizer hQ a).mp ha), Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h w hw
      have h1 := h (τ⁻¹ * w * τ) (mem_conjSubgroup.mp hw)
      have e1 : τ⁻¹ * (w * a) * τ = τ⁻¹ * w * τ * (τ⁻¹ * a * τ) := by group
      have e2 : τ⁻¹ * (a * w) * τ = τ⁻¹ * a * τ * (τ⁻¹ * w * τ) := by group
      have h2 : τ⁻¹ * (w * a) * τ = τ⁻¹ * (a * w) * τ := by rw [e1, e2, h1]
      simpa using h2
    · intro h u hu
      have hw : τ * u * τ⁻¹ ∈ conjSubgroup τ U := mem_conjSubgroup.mpr
        (by rw [show τ⁻¹ * (τ * u * τ⁻¹) * τ = u by group]; exact hu)
      have h1 := h _ hw
      have e1 : τ⁻¹ * (τ * u * τ⁻¹ * a) * τ = u * (τ⁻¹ * a * τ) := by group
      have e2 : τ⁻¹ * (a * (τ * u * τ⁻¹)) * τ = τ⁻¹ * a * τ * u := by group
      have h2 : τ⁻¹ * (τ * u * τ⁻¹ * a) * τ = τ⁻¹ * (a * (τ * u * τ⁻¹)) * τ := by rw [h1]
      rwa [e1, e2] at h2
  comm := fun y hy u hu => by
    have hy' : τ⁻¹ * y * τ ∈ Q := (mem_iff_conj_inv_of_normalizer hQ y).mp hy
    have hu' : τ⁻¹ * u * τ ∈ U := mem_conjSubgroup.mp hu
    obtain ⟨h1, h2⟩ := D.comm _ hy' _ hu'
    have e : τ⁻¹ * ⁅y, u⁆ * τ = ⁅τ⁻¹ * y * τ, τ⁻¹ * u * τ⁆ := by
      simp only [commutatorElement_def]
      group
    refine ⟨(mem_iff_conj_inv_of_normalizer hV _).mpr (by rw [e]; exact h1), ?_⟩
    show D.γ (τ⁻¹ * ⁅y, u⁆ * τ) = D.t (τ⁻¹ * y * τ) * D.ψ (τ⁻¹ * u * τ)
    rw [e]
    exact h2

@[simp] theorem conjData_γ (D : MulData V U Q K) {τ : G} (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) (v : G) :
    (D.conjData hV hQ).γ v = D.γ (τ⁻¹ * v * τ) := rfl

@[simp] theorem conjData_ψ (D : MulData V U Q K) {τ : G} (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) (u : G) :
    (D.conjData hV hQ).ψ u = D.ψ (τ⁻¹ * u * τ) := rfl

@[simp] theorem conjData_t (D : MulData V U Q K) {τ : G} (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) (y : G) :
    (D.conjData hV hQ).t y = D.t (τ⁻¹ * y * τ) := rfl

end MulData

section Conj

variable {V Q U : Subgroup G} {K : Type} [Field K] {γ : G → K} {τ : G} {a : K}

theorem gamma_conj_inv (hV : τ ∈ Subgroup.normalizer (V : Set G)) (ha : a ≠ 0)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) {v : G} (hv : v ∈ V) :
    γ (τ⁻¹ * v * τ) = a⁻¹ * γ v := by
  have hw : τ⁻¹ * v * τ ∈ V := (mem_iff_conj_inv_of_normalizer hV v).mp hv
  have h := hγ _ hw
  rw [show τ * (τ⁻¹ * v * τ) * τ⁻¹ = v by group] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem conjSubgroup_mem_classOf (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) (ha : a ≠ 0)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) (hU : U ∈ classOf V Q γ) :
    conjSubgroup τ U ∈ classOf V Q γ := by
  obtain ⟨⟨g, hg⟩, hUQ, hUV, D, c, σ, hc, hcσ⟩ := hU
  refine ⟨⟨τ * g, by rw [hg, conjSubgroup_mul]⟩, ?_, ?_, D.conjData hV hQ, c * σ a⁻¹, σ, ?_, ?_⟩
  · intro x hx
    have h1 : τ⁻¹ * x * τ ∈ U := mem_conjSubgroup.mp hx
    have h2 : τ * (τ⁻¹ * x * τ) * τ⁻¹ ∈ Q := (mem_iff_conj_of_normalizer hQ _).mp (hUQ h1)
    rwa [show τ * (τ⁻¹ * x * τ) * τ⁻¹ = x by group] at h2
  · intro h
    apply hUV
    have h1 : conjSubgroup τ⁻¹ (conjSubgroup τ U) = U := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have h2 : conjSubgroup τ⁻¹ V = V :=
      conjSubgroup_eq_self_iff.mpr (inv_mem hV)
    rw [← h1, h, h2]
  · exact mul_ne_zero hc (by simpa using ha)
  · intro v hv
    show D.γ (τ⁻¹ * v * τ) = c * σ a⁻¹ * σ (γ v)
    rw [hcσ _ ((mem_iff_conj_inv_of_normalizer hV v).mp hv), gamma_conj_inv hV ha hγ hv, map_mul,
      mul_assoc]

theorem conj_mem_classGroup (hV : τ ∈ Subgroup.normalizer (V : Set G))
    (hQ : τ ∈ Subgroup.normalizer (Q : Set G)) (ha : a ≠ 0)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) {x : G} (hx : x ∈ classGroup V Q γ) :
    τ * x * τ⁻¹ ∈ classGroup V Q γ := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact V_le_classGroup ((mem_iff_conj_of_normalizer hV x).mp hx)
    · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
      refine le_classGroup_of_mem (conjSubgroup_mem_classOf hV hQ ha hγ hU) ?_
      exact mem_conjSubgroup.mpr
        (by rw [show τ⁻¹ * (τ * x * τ⁻¹) * τ = x by group]; exact hxU)
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    rwa [show τ * (x * y) * τ⁻¹ = τ * x * τ⁻¹ * (τ * y * τ⁻¹) by group]
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    rwa [show τ * x⁻¹ * τ⁻¹ = (τ * x * τ⁻¹)⁻¹ by group]

end Conj

private theorem exists_ringEquiv_of_natCard_eq {K K' : Type} [Field K] [Field K'] [Finite K]
    [Finite K'] (h : Nat.card K = Nat.card K') : Nonempty (K ≃+* K') := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact h

theorem Hyp79.commute_of_not_class [Finite G] {M V Q : Subgroup G}
    (H : Hyp79 M V Q) {n : ℕ} {U₀ : Subgroup G} (D₀ : MulData V U₀ Q (GaloisField 2 n))
    {U : Subgroup G} (hU : U ∈ classOf V Q D₀.γ) {U' : Subgroup G}
    (hU'g : ∃ g : G, U' = conjSubgroup g V) (hU'Q : U' ≤ Q) (hU'V : U' ≠ V)
    (hU' : U' ∉ classOf V Q D₀.γ) : ∀ a ∈ U, ∀ b ∈ U', a * b = b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, hab⟩ := hcon
  obtain ⟨-, hUQ, -, D, hD⟩ := hU
  obtain ⟨g', rfl⟩ := hU'g
  obtain ⟨n', -, ⟨D'⟩⟩ := H.exists_mulData hU'V hU'Q
  obtain ⟨e⟩ := exists_ringEquiv_of_natCard_eq (K := GaloisField 2 n') (K' := GaloisField 2 n)
    (D'.natCard_V.symm.trans D.natCard_V)
  obtain ⟨c, σ, hc, hcσ⟩ := MulData.compat_of_noncomm hUQ hU'Q D (D'.mapRingEquiv e)
    ⟨a, ha, b, hb, hab⟩
  exact hU' ⟨⟨g', rfl⟩, hU'Q, hU'V, D'.mapRingEquiv e,
    GammaCompat.trans (hD : GammaCompat V D₀.γ D.γ)
      (⟨c, σ, hc, hcσ⟩ : GammaCompat V D.γ (D'.mapRingEquiv e).γ)⟩

theorem Hyp79.eq_classGroup_sup_centralizer [Finite G]
    {M V Q : Subgroup G} (H : Hyp79 M V Q) {n : ℕ} {U₀ : Subgroup G}
    (D₀ : MulData V U₀ Q (GaloisField 2 n)) (hU₀g : ∃ g : G, U₀ = conjSubgroup g V)
    (hU₀Q : U₀ ≤ Q) (hU₀V : U₀ ≠ V) :
    Q = classGroup V Q D₀.γ ⊔ (Q ⊓ Subgroup.centralizer (classGroup V Q D₀.γ : Set G)) := by
  refine le_antisymm (H.gen.le.trans (iSup₂_le fun g hg => ?_))
    (sup_le (classGroup_le H.V_le_Q) inf_le_left)
  by_cases h1 : conjSubgroup g V = V
  · exact h1.le.trans (V_le_classGroup.trans le_sup_left)
  by_cases h2 : conjSubgroup g V ∈ classOf V Q D₀.γ
  · exact (le_classGroup_of_mem h2).trans le_sup_left
  have hc : classGroup V Q D₀.γ ≤ Subgroup.centralizer (conjSubgroup g V : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · exact Subgroup.mem_centralizer_iff.mpr fun u hu => (H.V_central hx (hg hu)).symm
    · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
      exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (H.commute_of_not_class D₀ hU ⟨g, rfl⟩ hg h1 h2 x hxU u hu).symm
  have hle : conjSubgroup g V ≤ Q ⊓ Subgroup.centralizer (classGroup V Q D₀.γ : Set G) := by
    intro u hu
    refine ⟨hg hu, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hc hx) u hu).symm
  exact hle.trans le_sup_right

end CFSG.RankThree.GF2n.Tim79
