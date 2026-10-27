module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommuteBasic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.S14110.Commute

open CFSG.Open CFSG.LieType.BorelTits Subgroup

variable {Γ : Type*} [Group Γ]

theorem le_pCore_of_isSubnormal [Finite Γ] (p : ℕ) [Fact p.Prime] {K : Subgroup Γ}
    (hK : K.IsSubnormal) :
    ∀ {U : Subgroup Γ}, U ≤ K → (U.subgroupOf K).Normal → IsPGroup p U →
      U ≤ CFSG.Open.pCore p Γ := by
  induction hK with
  | top =>
    intro U _ hUn hU
    have hnorm : U.Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top, top_le_iff,
        Subgroup.normalizer_eq_top_iff] at hUn
      exact hUn
    exact le_pCore p hnorm hU
  | step H K hHK hKs hN ih =>
    intro U hUH hUn hU
    have h1 : U ≤ pCoreOf p H := le_pCoreOf p hUH hUn hU
    refine h1.trans (ih ?_ ?_ (pCoreOf_isPGroup p H))
    · exact (pCoreOf_le p H).trans hHK
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le p H).trans hHK)]
      have hKH : K ≤ normalizer (H : Set Γ) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).1 hN
      exact hKH.trans (normalizer_le_normalizer_pCoreOf p H)

@[expose] def cmtD (c : Γ) (T : Subgroup Γ) : Subgroup Γ :=
  Subgroup.closure ((fun x => x⁻¹ * (c * x * c⁻¹)) '' (T : Set Γ))

theorem mem_cmtD {c : Γ} {T : Subgroup Γ} {x : Γ} (hx : x ∈ T) :
    x⁻¹ * (c * x * c⁻¹) ∈ cmtD c T :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

theorem cmtD_mono {c : Γ} {T T' : Subgroup Γ} (h : T ≤ T') : cmtD c T ≤ cmtD c T' :=
  Subgroup.closure_mono (Set.image_mono h)

theorem cmtD_le {c : Γ} {T : Subgroup Γ} (hT : ∀ x ∈ T, c * x * c⁻¹ ∈ T) : cmtD c T ≤ T := by
  rw [cmtD, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact T.mul_mem (T.inv_mem hx) (hT x hx)

theorem conj_mem_cmtD {c : Γ} {T : Subgroup Γ} (hT : ∀ x ∈ T, c * x * c⁻¹ ∈ T) :
    ∀ y ∈ cmtD c T, c * y * c⁻¹ ∈ cmtD c T := by
  intro y hy
  unfold cmtD at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have : c * (x⁻¹ * (c * x * c⁻¹)) * c⁻¹ =
        (c * x * c⁻¹)⁻¹ * (c * (c * x * c⁻¹) * c⁻¹) := by group
    rw [this]; exact mem_cmtD (hT x hx)
  | one => simp
  | mul y z _ _ hy hz =>
    have : c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) := by group
    rw [this]; exact mul_mem hy hz
  | inv y _ hy =>
    have : c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hy

theorem inv_mul_mul_mem_cmtD {c : Γ} {T : Subgroup Γ} :
    ∀ t ∈ T, ∀ y ∈ cmtD c T, t⁻¹ * y * t ∈ cmtD c T := by
  intro t ht y hy
  unfold cmtD at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have : t⁻¹ * (x⁻¹ * (c * x * c⁻¹)) * t =
        ((x * t)⁻¹ * (c * (x * t) * c⁻¹)) * (t⁻¹ * (c * t * c⁻¹))⁻¹ := by group
    rw [this]; exact mul_mem (mem_cmtD (T.mul_mem hx ht)) (inv_mem (mem_cmtD ht))
  | one => simp
  | mul y z _ _ hy hz =>
    have : t⁻¹ * (y * z) * t = (t⁻¹ * y * t) * (t⁻¹ * z * t) := by group
    rw [this]; exact mul_mem hy hz
  | inv y _ hy =>
    have : t⁻¹ * y⁻¹ * t = (t⁻¹ * y * t)⁻¹ := by group
    rw [this]; exact inv_mem hy

theorem cmtD_le_cmtD_cmtD {c : Γ} (hc3 : c ^ 3 = 1) {T : Subgroup Γ}
    (hT : ∀ x ∈ T, c * x * c⁻¹ ∈ T) (h2 : ∀ x ∈ T, ∃ m : ℕ, x ^ 2 ^ m = 1) :
    cmtD c T ≤ cmtD c (cmtD c T) := by
  have hA : ∀ y ∈ cmtD c T, c * y * c⁻¹ ∈ cmtD c T := conj_mem_cmtD hT
  have hB : ∀ y ∈ cmtD c (cmtD c T), c * y * c⁻¹ ∈ cmtD c (cmtD c T) := conj_mem_cmtD hA
  have hAT : cmtD c T ≤ T := cmtD_le hT
  have hccc : c * c * c = 1 := by rw [← pow_three']; exact hc3
  change Subgroup.closure ((fun x => x⁻¹ * (c * x * c⁻¹)) '' (T : Set Γ)) ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  have haA : x⁻¹ * (c * x * c⁻¹) ∈ cmtD c T := mem_cmtD hx
  show x⁻¹ * (c * x * c⁻¹) ∈ cmtD c (cmtD c T)
  generalize ha_def : x⁻¹ * (c * x * c⁻¹) = a at haA ⊢
  have hbB : a⁻¹ * (c * a * c⁻¹) ∈ cmtD c (cmtD c T) := mem_cmtD haA
  generalize hb_def : a⁻¹ * (c * a * c⁻¹) = b at hbB
  have e1 : c * x * c⁻¹ = x * a := by rw [← ha_def]; group
  have e2 : c * a * c⁻¹ = a * b := by rw [← hb_def]; group
  have e3 : c * (x * a * a * b) * c⁻¹ = (x * a) * (a * b) * (a * b) * (c * b * c⁻¹) := by
    calc c * (x * a * a * b) * c⁻¹
        = (c * x * c⁻¹) * (c * a * c⁻¹) * (c * a * c⁻¹) * (c * b * c⁻¹) := by group
      _ = (x * a) * (a * b) * (a * b) * (c * b * c⁻¹) := by rw [e1, e2]
  have e4 : c * (c * x * c⁻¹) * c⁻¹ = x * a * a * b := by
    rw [e1]
    calc c * (x * a) * c⁻¹ = (c * x * c⁻¹) * (c * a * c⁻¹) := by group
      _ = x * a * a * b := by rw [e1, e2]; group
  have e5 : c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = x := by
    have : c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ := by group
    rw [this, hccc]; simp
  rw [e4, e3] at e5
  have e6 : a * (a * b) * (a * b) * (c * b * c⁻¹) = 1 := by
    have : x * a * (a * b) * (a * b) * (c * b * c⁻¹) =
        x * (a * (a * b) * (a * b) * (c * b * c⁻¹)) := by group
    rw [this] at e5
    exact (mul_eq_left.1 e5)
  have e7 : a ^ 3 * ((a⁻¹ * b * a) * b * (c * b * c⁻¹)) = 1 := by
    rw [← e6]; rw [pow_three']; group
  have hmemB : (a⁻¹ * b * a) * b * (c * b * c⁻¹) ∈ cmtD c (cmtD c T) :=
    mul_mem (mul_mem (inv_mul_mul_mem_cmtD a haA b hbB) hbB) (hB b hbB)
  have ha3 : a ^ 3 ∈ cmtD c (cmtD c T) := by
    have : a ^ 3 = ((a⁻¹ * b * a) * b * (c * b * c⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left e7
    rw [this]; exact inv_mem hmemB
  exact mem_of_pow_three_mem ha3 (h2 a (hAT haA))

variable {Q X W : Subgroup Γ} {c : Γ}

theorem comm_mem_of_isSubnormal [Q.Normal] (hQ2 : ∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1)
    (hX : A4Data X W c) (hXs : X.IsSubnormal) : ∀ q ∈ Q, q * c * q⁻¹ * c⁻¹ ∈ W := by
  obtain ⟨n, f, hmono, hnorm, hf0, hfn⟩ := Subgroup.IsSubnormal.isSubnormal_iff.1 hXs
  have hnorm' : ∀ i, ∀ x ∈ f (i + 1), ∀ y ∈ f i, x * y * x⁻¹ ∈ f i := fun i x hx y hy =>
    (Subgroup.normal_subgroupOf_iff (hmono (Nat.le_succ i))).1 (hnorm i) y x hy hx
  have hcmem : ∀ i, c ∈ f i := fun i => by
    have h0 : c ∈ f 0 := by rw [hf0]; exact hX.mem_X
    exact hmono (Nat.zero_le i) h0
  have hcinv : ∀ i, ∀ x ∈ Q ⊓ f i, c * x * c⁻¹ ∈ Q ⊓ f i := fun i x hx => by
    obtain ⟨hxQ, hxf⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨Subgroup.Normal.conj_mem inferInstance x hxQ c,
      mul_mem (mul_mem (hcmem i) hxf) (inv_mem (hcmem i))⟩
  have h2 : ∀ i, ∀ x ∈ Q ⊓ f i, ∃ m : ℕ, x ^ 2 ^ m = 1 := fun i x hx =>
    hQ2 x (Subgroup.mem_inf.1 hx).1
  have hsub : ∀ i, cmtD c (Q ⊓ f (i + 1)) ≤ Q ⊓ f i := by
    intro i
    rw [cmtD, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxQ, hxf⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hxQ)
      (Subgroup.Normal.conj_mem inferInstance x hxQ c), ?_⟩
    have h1 : x⁻¹ * c * x⁻¹⁻¹ ∈ f i := hnorm' i x⁻¹ (inv_mem hxf) c (hcmem i)
    have : x⁻¹ * (c * x * c⁻¹) = (x⁻¹ * c * x⁻¹⁻¹) * c⁻¹ := by group
    show x⁻¹ * (c * x * c⁻¹) ∈ f i
    rw [this]
    exact mul_mem h1 (inv_mem (hcmem i))
  have hmain : ∀ i, cmtD c (Q ⊓ f i) ≤ W := by
    intro i
    induction i with
    | zero =>
      refine (cmtD_le (hcinv 0)).trans ?_
      intro x hx
      refine mem_W_of_pow_two_pow_eq_one hX ?_ (h2 0 x hx)
      have := (Subgroup.mem_inf.1 hx).2
      rwa [hf0] at this
    | succ i ih =>
      have h1 := hsub i
      have h3 : cmtD c (cmtD c (Q ⊓ f (i + 1))) ≤ W := (cmtD_mono h1).trans ih
      exact (cmtD_le_cmtD_cmtD hX.c_pow_three (hcinv (i + 1)) (h2 (i + 1))).trans h3
  have hfin := hmain n
  rw [hfn, inf_top_eq] at hfin
  intro q hq
  have := hfin (mem_cmtD (c := c) (inv_mem hq))
  have e : (q⁻¹)⁻¹ * (c * q⁻¹ * c⁻¹) = q * c * q⁻¹ * c⁻¹ := by group
  rwa [e] at this

theorem map_le_pCore_three [Finite Γ] [Q.Normal] (hX : A4Data X W c) (hXs : X.IsSubnormal)
    (hWQ : W ≤ Q) : X.map (QuotientGroup.mk' Q) ≤ CFSG.Open.pCore 3 (Γ ⧸ Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : (X.map (QuotientGroup.mk' Q)).IsSubnormal :=
    hXs.map (QuotientGroup.mk'_surjective Q)
  refine le_pCore_of_isSubnormal 3 hsub le_rfl ?_ ?_
  · rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top
  · intro g
    obtain ⟨y, hy⟩ := g
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have h3 : x ^ 3 ∈ Q := hWQ (pow_three_mem_W hX hx)
    have h4 := (QuotientGroup.eq_one_iff (N := Q) (x ^ 3)).2 h3
    simpa using h4

theorem exists_pow_mem_of_isSubnormal [Finite Γ] [Q.Normal] {Y W' : Subgroup Γ} {c' : Γ}
    (hX : A4Data X W c) (hY : A4Data Y W' c') (hXs : X.IsSubnormal) (hYs : Y.IsSubnormal)
    (hWQ : W ≤ Q) (hW'Q : W' ≤ Q) :
    ∃ R : Subgroup Γ, c ∈ R ∧ c' ∈ R ∧ ∀ g ∈ R, ∃ k : ℕ, g ^ 3 ^ k ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcX := map_le_pCore_three hX hXs hWQ
  have hcY := map_le_pCore_three hY hYs hW'Q
  refine ⟨(CFSG.Open.pCore 3 (Γ ⧸ Q)).comap (QuotientGroup.mk' Q),
    hcX ⟨c, hX.mem_X, rfl⟩, hcY ⟨c', hY.mem_X, rfl⟩, ?_⟩
  intro g hg
  obtain ⟨k, hk⟩ :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 3 (G := Γ ⧸ Q)) ⟨QuotientGroup.mk' Q g, hg⟩
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk' Q g) ^ 3 ^ k = 1 := congrArg Subtype.val hk
  rw [← map_pow] at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

end CFSG.Quasithin.S14110.Commute
