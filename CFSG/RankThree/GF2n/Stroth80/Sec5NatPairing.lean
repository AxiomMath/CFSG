module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm
public import CFSG.ClassicalGroups.Symplectic.InvariantPairing
public import CFSG.ClassicalGroups.Orthogonal.InvariantPairing

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.Open
open QuadraticMap Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

structure NatCommData (Q V Z R : Subgroup G) (t : G) : Prop where
  VQ : V ≤ Q
  ZV : Z ≤ V
  comm_Z : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z
  Z_central : ∀ z ∈ Z, ∀ x ∈ Q, x * z = z * x
  comm_t_mem : ∀ y ∈ Q, ⁅y, t⁆ ∈ V
  lift : ∀ v ∈ V, ∃ y ∈ Q, ⁅y, t⁆ * v⁻¹ ∈ Z
  ker_central : ∀ y ∈ Q, ⁅y, t⁆ ∈ Z → ∀ v ∈ V, ⁅v, y⁆ = 1
  R_normQ : ∀ r ∈ R, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q
  R_centZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ = z
  R_equiv : ∀ r ∈ R, ∀ x ∈ Q, ⁅r * x * r⁻¹, t⁆ * (r * ⁅x, t⁆ * r⁻¹)⁻¹ ∈ Z

section Identities

variable {Q V Z R : Subgroup G} {t : G}

theorem NatCommData.comm_mul_right (D : NatCommData Q V Z R t) {v y₁ y₂ : G} (hv : v ∈ Q)
    (hy₁ : y₁ ∈ Q) (hy₂ : y₂ ∈ Q) : ⁅v, y₁ * y₂⁆ = ⁅v, y₁⁆ * ⁅v, y₂⁆ := by
  have hid : ⁅v, y₁ * y₂⁆ = ⁅v, y₁⁆ * (y₁ * ⁅v, y₂⁆ * y₁⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hc : y₁ * ⁅v, y₂⁆ = ⁅v, y₂⁆ * y₁ := D.Z_central _ (D.comm_Z v hv y₂ hy₂) y₁ hy₁
  rw [hid, hc, mul_inv_cancel_right]

theorem NatCommData.comm_mul_left (D : NatCommData Q V Z R t) {v₁ v₂ y : G} (hv₁ : v₁ ∈ Q)
    (hv₂ : v₂ ∈ Q) (hy : y ∈ Q) : ⁅v₁ * v₂, y⁆ = ⁅v₁, y⁆ * ⁅v₂, y⁆ := by
  have hid : ⁅v₁ * v₂, y⁆ = (v₁ * ⁅v₂, y⁆ * v₁⁻¹) * ⁅v₁, y⁆ := by
    simp only [commutatorElement_def]
    group
  have hc : v₁ * ⁅v₂, y⁆ = ⁅v₂, y⁆ * v₁ := D.Z_central _ (D.comm_Z v₂ hv₂ y hy) v₁ hv₁
  have hz : ⁅v₁, y⁆ * ⁅v₂, y⁆ = ⁅v₂, y⁆ * ⁅v₁, y⁆ :=
    D.Z_central _ (D.comm_Z v₂ hv₂ y hy) _ (D.VQ (D.ZV (D.comm_Z v₁ hv₁ y hy)))
  rw [hid, hc, mul_inv_cancel_right]
  exact hz.symm

theorem NatCommData.comm_conj (D : NatCommData Q V Z R t) {r v y : G} (hr : r ∈ R) (hv : v ∈ Q)
    (hy : y ∈ Q) : ⁅r * v * r⁻¹, r * y * r⁻¹⁆ = ⁅v, y⁆ := by
  have hid : ⁅r * v * r⁻¹, r * y * r⁻¹⁆ = r * ⁅v, y⁆ * r⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hid, D.R_centZ r hr _ (D.comm_Z v hv y hy)]

theorem NatCommData.comm_Z_left (D : NatCommData Q V Z R t) {z y : G} (hz : z ∈ Z) (hy : y ∈ Q) :
    ⁅z, y⁆ = 1 := by
  have h := D.Z_central z hz y hy
  rw [commutatorElement_def, ← h]
  group

end Identities

section Kap

variable {Q V Z R : Subgroup G} {t : G} {ι : Type} [Fintype ι] [DecidableEq ι]
  {K : Type} [Field K] [(Z.subgroupOf V).Normal]

@[expose] def kapVec (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (y : ↥Q) : ι → K :=
  secVec ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩

theorem kapVec_mul (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (y₁ y₂ : ↥Q) :
    kapVec D ψ (y₁ * y₂) = kapVec D ψ y₁ + kapVec D ψ y₂ := by
  have ha₂ : ⁅(y₂ : G), t⁆ ∈ V := D.comm_t_mem y₂ y₂.2
  have hz : ⁅(y₁ : G), ⁅(y₂ : G), t⁆⁆ ∈ Z := D.comm_Z y₁ y₁.2 _ (D.VQ ha₂)
  have e : (⟨⁅((y₁ * y₂ : ↥Q) : G), t⁆, D.comm_t_mem _ (y₁ * y₂).2⟩ : ↥V) =
      ⟨⁅(y₁ : G), ⁅(y₂ : G), t⁆⁆, D.ZV hz⟩ * ⟨⁅(y₂ : G), t⁆, ha₂⟩ *
        ⟨⁅(y₁ : G), t⁆, D.comm_t_mem y₁ y₁.2⟩ := by
    apply Subtype.ext
    show ⁅(y₁ : G) * (y₂ : G), t⁆ = ⁅(y₁ : G), ⁅(y₂ : G), t⁆⁆ * ⁅(y₂ : G), t⁆ * ⁅(y₁ : G), t⁆
    simp only [commutatorElement_def]
    group
  unfold kapVec
  rw [e, secVec_mul, secVec_mul, (secVec_eq_zero_iff ψ ⟨_, D.ZV hz⟩).mpr hz, zero_add, add_comm]

theorem kapVec_one (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) : kapVec D ψ (1 : ↥Q) = 0 := by
  unfold kapVec
  rw [secVec_eq_zero_iff]
  have h : ⁅(1 : G), t⁆ = 1 := by simp [commutatorElement_def]
  show ⁅(1 : G), t⁆ ∈ Z
  rw [h]
  exact Z.one_mem

theorem kapVec_inv (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (y : ↥Q) :
    kapVec D ψ y⁻¹ = -kapVec D ψ y := by
  have h := kapVec_mul D ψ y y⁻¹
  rw [mul_inv_cancel, kapVec_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem kapVec_conj (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) {φ : ↥R →* GL ι K}
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) (r : ↥R) (y : ↥Q) :
    kapVec D ψ ⟨(r : G) * y * (r : G)⁻¹, D.R_normQ r r.2 y y.2⟩ =
      (φ r : Matrix ι ι K) *ᵥ kapVec D ψ y := by
  have hy : ⁅(y : G), t⁆ ∈ V := D.comm_t_mem y y.2
  set a : ↥V := ⟨⁅(y : G), t⁆, hy⟩ with ha
  set w : ↥V := ⟨(r : G) * a * (r : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hVR r.2) a).mp a.2⟩ with hw
  have h1 : secVec ψ w = (φ r : Matrix ι ι K) *ᵥ secVec ψ a := hψ r a w rfl
  have h2 : secVec ψ ⟨⁅(r : G) * y * (r : G)⁻¹, t⁆, D.comm_t_mem _ (D.R_normQ r r.2 y y.2)⟩ =
      secVec ψ w := by
    rw [secVec_eq_iff]
    exact D.R_equiv r r.2 y y.2
  exact h2.trans h1

theorem exists_kapVec (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (x : ι → K) :
    ∃ y : ↥Q, kapVec D ψ y = x := by
  obtain ⟨v, hv⟩ := exists_secVec_eq ψ x
  obtain ⟨y, hyQ, hy⟩ := D.lift v v.2
  refine ⟨⟨y, hyQ⟩, ?_⟩
  rw [← hv]
  exact (secVec_eq_iff ψ _ v).mpr hy

@[expose] noncomputable def pairVec (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (b : ↥V) (x : ι → K) : G :=
  ⁅(b : G), ((Classical.choose (exists_kapVec D ψ x) : ↥Q) : G)⁆

theorem pairVec_eq (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (b : ↥V) {x : ι → K} (y : ↥Q)
    (hy : kapVec D ψ y = x) : pairVec D ψ b x = ⁅(b : G), (y : G)⁆ := by
  set y₀ : ↥Q := Classical.choose (exists_kapVec D ψ x) with hy₀def
  have hy₀ : kapVec D ψ y₀ = x := Classical.choose_spec (exists_kapVec D ψ x)
  have hq : kapVec D ψ (y * y₀⁻¹) = 0 := by
    rw [kapVec_mul, kapVec_inv, hy, hy₀, add_neg_cancel]
  have hqZ : ⁅((y * y₀⁻¹ : ↥Q) : G), t⁆ ∈ Z := (secVec_eq_zero_iff ψ _).mp hq
  have h1 : ⁅(b : G), ((y * y₀⁻¹ : ↥Q) : G)⁆ = 1 := D.ker_central _ (y * y₀⁻¹).2 hqZ b b.2
  have h2 : (y : G) = ((y * y₀⁻¹ : ↥Q) : G) * (y₀ : G) := by simp
  unfold pairVec
  rw [h2, D.comm_mul_right (D.VQ b.2) (y * y₀⁻¹).2 y₀.2, h1, one_mul]

theorem pairVec_add (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (b : ↥V) (x₁ x₂ : ι → K) :
    pairVec D ψ b (x₁ + x₂) = pairVec D ψ b x₁ * pairVec D ψ b x₂ := by
  obtain ⟨y₁, h₁⟩ := exists_kapVec D ψ x₁
  obtain ⟨y₂, h₂⟩ := exists_kapVec D ψ x₂
  rw [pairVec_eq D ψ b (y₁ * y₂) (by rw [kapVec_mul, h₁, h₂]), pairVec_eq D ψ b y₁ h₁,
    pairVec_eq D ψ b y₂ h₂]
  exact D.comm_mul_right (D.VQ b.2) y₁.2 y₂.2

@[expose] noncomputable def pairHom (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (b : ↥V) : (ι → K) →+ Additive G :=
  AddMonoidHom.mk' (fun x => Additive.ofMul (pairVec D ψ b x)) fun x₁ x₂ => by
    rw [pairVec_add, ofMul_mul]

theorem pairVec_conj (D : NatCommData Q V Z R t)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) {φ : ↥R →* GL ι K}
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) (b : ↥V) (r : ↥R)
    (hr : (φ r : Matrix ι ι K) *ᵥ secVec ψ b = secVec ψ b) (x : ι → K) :
    pairVec D ψ b ((φ r : Matrix ι ι K) *ᵥ x) = pairVec D ψ b x := by
  obtain ⟨y, hy⟩ := exists_kapVec D ψ x
  have hy' : kapVec D ψ ⟨(r : G) * y * (r : G)⁻¹, D.R_normQ r r.2 y y.2⟩ =
      (φ r : Matrix ι ι K) *ᵥ x := by
    rw [kapVec_conj D ψ hψ hVR r y, hy]
  rw [pairVec_eq D ψ b _ hy', pairVec_eq D ψ b y hy]
  set w : ↥V := ⟨(r : G) * b * (r : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hVR r.2) b).mp b.2⟩
    with hw
  have hb : secVec ψ w = secVec ψ b := (hψ r b w rfl).trans hr
  have hz : (r : G) * b * (r : G)⁻¹ * (b : G)⁻¹ ∈ Z := (secVec_eq_iff ψ w b).mp hb
  have hbQ : (b : G) ∈ Q := D.VQ b.2
  have hqQ : (r : G) * y * (r : G)⁻¹ ∈ Q := D.R_normQ r r.2 y y.2
  have hrb : (r : G) * b * (r : G)⁻¹ = ((r : G) * b * (r : G)⁻¹ * (b : G)⁻¹) * b := by group
  have hz0Q : (r : G) * b * (r : G)⁻¹ * (b : G)⁻¹ ∈ Q := D.VQ (D.ZV hz)
  have h1 : ⁅(r : G) * b * (r : G)⁻¹, (r : G) * y * (r : G)⁻¹⁆ = ⁅(b : G), (y : G)⁆ :=
    D.comm_conj r.2 hbQ y.2
  have h2 : ⁅(r : G) * b * (r : G)⁻¹, (r : G) * y * (r : G)⁻¹⁆ =
      ⁅(b : G), (r : G) * y * (r : G)⁻¹⁆ := by
    rw [hrb, D.comm_mul_left hz0Q hbQ hqQ, D.comm_Z_left hz hqQ, one_mul]
  exact h2.symm.trans h1

theorem spForm_ne_zero_of_commData {m : ℕ} {B C : Subgroup G} (D : NatCommData Q V Z R t)
    (φ : ↥R →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) {u u' : Fin m ⊕ Fin m → K} (hBV : B ≤ V)
    (hB : ∀ b : ↥V, (b : G) ∈ B → ∃ c : K, secVec ψ b = c • u)
    (hC : ∀ c : ↥V, (c : G) ∈ C ⊔ Z → ∃ c' : K, secVec ψ c = c' • u') {ĉ b : G} (hĉ : ĉ ∈ Q)
    (hĉC : ⁅ĉ, t⁆ ∈ C ⊔ Z) (hb : b ∈ B) (hne : ⁅b, ĉ⁆ ≠ 1) : spForm m K u u' ≠ 0 := by
  intro h0
  obtain ⟨c₁, hc₁⟩ := hB ⟨b, hBV hb⟩ hb
  obtain ⟨c₂, hc₂⟩ := hC ⟨⁅ĉ, t⁆, D.comm_t_mem ĉ hĉ⟩ hĉC
  have hk : kapVec D ψ ⟨ĉ, hĉ⟩ = c₂ • u' := hc₂
  have hxy : spForm m K (secVec ψ ⟨b, hBV hb⟩) (kapVec D ψ ⟨ĉ, hĉ⟩) = 0 := by
    rw [hc₁, hk]
    simp [h0]
  have hg0 := additive_eq_zero_of_range_spForm φ hφ (pairHom D ψ ⟨b, hBV hb⟩)
    (x := secVec ψ ⟨b, hBV hb⟩)
    (fun r hr z => by
      show Additive.ofMul (pairVec D ψ _ _) = Additive.ofMul (pairVec D ψ _ _)
      rw [pairVec_conj D ψ hψ hVR _ r hr z]) hxy
  have h1 : pairVec D ψ ⟨b, hBV hb⟩ (kapVec D ψ ⟨ĉ, hĉ⟩) = 1 := ofMul_eq_zero.mp hg0
  rw [pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨ĉ, hĉ⟩ rfl] at h1
  exact hne h1

theorem polar_ne_zero_of_commData {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} {B C : Subgroup G}
    [(Z.subgroupOf V).Normal] (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (D : NatCommData Q V Z R t) (φ : ↥R →* GL ι K)
    (hφ : φ.range = X) (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G)) {u u' : ι → K} (hu : Q' u = 0) (hu0 : u ≠ 0)
    (hBV : B ≤ V) (hB : ∀ b : ↥V, (b : G) ∈ B → ∃ c : K, secVec ψ b = c • u)
    (hC : ∀ c : ↥V, (c : G) ∈ C ⊔ Z → ∃ c' : K, secVec ψ c = c' • u') {ĉ b : G} (hĉ : ĉ ∈ Q)
    (hĉC : ⁅ĉ, t⁆ ∈ C ⊔ Z) (hb : b ∈ B) (hne : ⁅b, ĉ⁆ ≠ 1) : polar Q' u u' ≠ 0 := by
  intro h0
  obtain ⟨c₁, hc₁⟩ := hB ⟨b, hBV hb⟩ hb
  obtain ⟨c₂, hc₂⟩ := hC ⟨⁅ĉ, t⁆, D.comm_t_mem ĉ hĉ⟩ hĉC
  have hk : kapVec D ψ ⟨ĉ, hĉ⟩ = c₂ • u' := hc₂
  by_cases hc0 : c₁ = 0
  · have hz : (b : G) ∈ Z := (secVec_eq_zero_iff ψ ⟨b, hBV hb⟩).mp (by rw [hc₁, hc0, zero_smul])
    exact hne (D.comm_Z_left hz hĉ)
  · have hxs : Q' (secVec ψ ⟨b, hBV hb⟩) = 0 := by
      rw [hc₁, QuadraticMap.map_smul, hu, smul_zero]
    have hx0 : secVec ψ ⟨b, hBV hb⟩ ≠ 0 := by
      rw [hc₁]
      exact smul_ne_zero hc0 hu0
    have hxy : polar Q' (secVec ψ ⟨b, hBV hb⟩) (kapVec D ψ ⟨ĉ, hĉ⟩) = 0 := by
      rw [hc₁, hk, polar_smul_left_eq, polar_smul_right_eq, h0]
      simp
    have hg0 := E.additive_eq_zero_of_range_polar hQ h3 φ hφ (pairHom D ψ ⟨b, hBV hb⟩) hxs hx0
      (fun r hr z => by
        show Additive.ofMul (pairVec D ψ _ _) = Additive.ofMul (pairVec D ψ _ _)
        rw [pairVec_conj D ψ hψ hVR _ r hr z]) hxy
    have h1 : pairVec D ψ ⟨b, hBV hb⟩ (kapVec D ψ ⟨ĉ, hĉ⟩) = 1 := ofMul_eq_zero.mp hg0
    rw [pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨ĉ, hĉ⟩ rfl] at h1
    exact hne h1

end Kap

end CFSG.RankThree.GF2n.Stroth80
