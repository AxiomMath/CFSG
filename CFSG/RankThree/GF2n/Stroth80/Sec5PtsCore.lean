module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatField
public import CFSG.RankThree.GF2n.Stroth80.Sec310NotQB
public import CFSG.RankThree.GF2n.Stroth80.Sec310Perp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_globalRingEquiv (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {X : Subgroup (GL ι K)} (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ (nn : ℕ) (γ : G → GaloisField 2 nn) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 nn) γ)
      (_ : GlobalModelData M Q Z γ M₀) (θ : GaloisField 2 nn ≃+* K),
      ∀ (c : GaloisField 2 nn) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
        secVec ψ w = θ c • secVec ψ v := by
  classical
  obtain ⟨nn, γ, M₀, hn, h⟩ := stroth_globalModelDataGF hc.hyp
  have hcard : Nat.card (GaloisField 2 nn) = Nat.card K := by rw [h.card, hK]
  have hlin : ∀ r ∈ Rt M (LB M Q B) t, ∃ T : M₀.E →ₗ[GaloisField 2 nn] M₀.E,
      ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x) := by
    intro r hr
    have hr0 : r ∈ H0 M Z := hc.Rt_le_H0 t hr
    obtain ⟨T, hT, -⟩ := h.linear_of_centralizes hr0.1 (fun z hz => by
      have := Subgroup.mem_centralizer_iff.mp hr0.2 z hz
      rw [← this]; group)
    exact ⟨T, hT⟩
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcard M₀ (hc.Vt_le_Q t) hX
    (fun c e he => hc.smul_mem_img_Vt h t c he) hlin φ hφ (hc.Rt_normalizes_Vt ht) ψ hψ
  exact ⟨nn, γ, M₀, h, θ, hθ⟩

theorem Ctx.exists_point_of_le {D V : Subgroup G} (hD : Ctx M Q Z D) (hDV : D ≤ V) {K : Type}
    [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] [(Z.subgroupOf V).Normal]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    {Kg : Type} [Field Kg] [Finite Kg] {γ : G → Kg} {M₀ : Tim79.QuadModel Q Z Kg γ}
    (h : GlobalModelData M Q Z γ M₀) (θ : Kg ≃+* K)
    (hθ : ∀ (c : Kg) (v w : ↥V), M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v) :
    ∃ b₀ : ↥V, (b₀ : G) ∈ D ∧ secVec ψ b₀ ≠ 0 ∧
      ∀ x : ι → K, (∃ b : ↥V, (b : G) ∈ D ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • secVec ψ b₀ := by
  classical
  obtain ⟨b, hb0, -, hB, -, -⟩ := hD.dictB h
  obtain ⟨u₀, hu₀B, hu₀Q, hu₀⟩ : b ∈ M₀.img D := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
  refine ⟨⟨u₀, hDV hu₀B⟩, hu₀B, ?_, fun x => ⟨?_, ?_⟩⟩
  · intro h0
    have hz : u₀ ∈ Z := (secVec_eq_zero_iff ψ ⟨u₀, hDV hu₀B⟩).mp h0
    exact hb0 (hu₀ ▸ (M₀.π_ker u₀ hu₀Q).mpr hz)
  · rintro ⟨b', hb'B, rfl⟩
    obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hb'B (hD.le hb'B))
    exact ⟨θ s, hθ s ⟨u₀, hDV hu₀B⟩ b' (by rw [hs, hu₀])⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨x₁, hx₁B, hx₁Q, hx₁⟩ : θ.symm c • b ∈ M₀.img D := (hB _).mpr ⟨_, rfl⟩
    refine ⟨⟨x₁, hDV hx₁B⟩, hx₁B, ?_⟩
    have key := hθ (θ.symm c) ⟨u₀, hDV hu₀B⟩ ⟨x₁, hDV hx₁B⟩ (by rw [hx₁, hu₀])
    rw [RingEquiv.apply_symm_apply] at key
    exact key

theorem Ctx.exists_scalar_lift (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (D : NatCommData Q (Vt M (LB M Q B) B Z t) Z (Rt M (LB M Q B) t) t) {K : Type} [Field K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    {Kg : Type} [Field Kg] [Finite Kg] {γ : G → Kg} {M₀ : Tim79.QuadModel Q Z Kg γ}
    (h : GlobalModelData M Q Z γ M₀) (θ : Kg ≃+* K)
    (hθ : ∀ (c : Kg) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
      secVec ψ w = θ c • secVec ψ v) (c : Kg) {y : G} (hy : y ∈ Q) :
    ∃ y' : ↥Q, M₀.π (y' : G) = c • M₀.π y ∧
      kapVec D ψ y' = θ c • kapVec D ψ ⟨y, hy⟩ := by
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨T, hTπ, -⟩ := h.linear_of_centralizes htM (hc.LB_centralizes_Z ht)
  obtain ⟨htQ, -⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨y', hy'Q, hy'⟩ := M₀.π_surj (c • M₀.π y)
  refine ⟨⟨y', hy'Q⟩, hy', ?_⟩
  have h1 : M₀.π ⁅y', t⁆ = c • M₀.π ⁅y, t⁆ := by
    rw [pi_comm_eq_sub htQ hTπ hy'Q, pi_comm_eq_sub htQ hTπ hy, hy', map_smul, smul_sub]
  exact hθ c ⟨⁅y, t⁆, D.comm_t_mem y hy⟩ ⟨⁅y', t⁆, D.comm_t_mem y' hy'Q⟩ h1


theorem Ctx.pairVec_eq_one_iff_of_forward (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) (D : NatCommData Q (Vt M (LB M Q B) B Z t) Z (Rt M (LB M Q B) t) t)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    {Kg : Type} [Field Kg] [Finite Kg] {γ : G → Kg} {M₀ : Tim79.QuadModel Q Z Kg γ}
    (h : GlobalModelData M Q Z γ M₀) (θ : Kg ≃+* K)
    (hθ : ∀ (c : Kg) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
      secVec ψ w = θ c • secVec ψ v) {b₀ : ↥(Vt M (LB M Q B) B Z t)}
    (hu0 : secVec ψ b₀ ≠ 0) (f : (ι → K) →ₗ[K] K)
    (hbwd : ∀ y : ι → K, f y = 0 → pairVec D ψ b₀ y = 1) (x : ι → K) :
    pairVec D ψ b₀ x = 1 ↔ f x = 0 := by
  refine ⟨fun hx => ?_, hbwd x⟩
  by_contra hne
  set u := secVec ψ b₀ with hu
  set a := f x with ha
  have hscal : ∀ lam : K, pairVec D ψ b₀ (lam • x) = 1 := by
    intro lam
    obtain ⟨ĉ, hĉ⟩ := exists_kapVec D ψ x
    have hcomm : ⁅(b₀ : G), (ĉ : G)⁆ = 1 := by rw [← pairVec_eq D ψ b₀ ĉ hĉ]; exact hx
    obtain ⟨ĉ', hπ, hk⟩ := hc.exists_scalar_lift ht D ψ h θ hθ (θ.symm lam) ĉ.2
    have hk' : kapVec D ψ ĉ' = lam • x := by
      rw [hk, RingEquiv.apply_symm_apply]
      congr 1
    rw [pairVec_eq D ψ b₀ ĉ' hk']
    have hb0Q : (b₀ : G) ∈ Q := D.VQ b₀.2
    have h1 : γ ⁅(b₀ : G), (ĉ' : G)⁆ = M₀.B (M₀.π b₀) (M₀.π ĉ') := M₀.comm_eq _ hb0Q _ ĉ'.2
    have h2 : γ ⁅(b₀ : G), (ĉ : G)⁆ = M₀.B (M₀.π b₀) (M₀.π ĉ) := M₀.comm_eq _ hb0Q _ ĉ.2
    rw [hcomm, h.reg.one] at h2
    have h3 : γ ⁅(b₀ : G), (ĉ' : G)⁆ = 0 := by
      rw [h1, hπ, map_smul, ← h2]
      simp
    exact h.reg.inj _ (M₀.comm_mem _ hb0Q _ ĉ'.2) h3
  have hall : ∀ y : ι → K, pairVec D ψ b₀ y = 1 := by
    intro y
    have ha0 : a ≠ 0 := hne
    have hy1 : f (y - (f y / a) • x) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, ← ha, div_mul_cancel₀ _ ha0, sub_self]
    have h1 := hbwd _ hy1
    have h2 := hscal (f y / a)
    have h3 := pairVec_add D ψ b₀ (y - (f y / a) • x) ((f y / a) • x)
    rw [sub_add_cancel, h1, h2, one_mul] at h3
    exact h3
  have hcentral : (b₀ : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := pairVec_eq D ψ b₀ ⟨y, hy⟩ rfl
    rw [hall] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this.symm).symm
  have hbZ : (b₀ : G) ∈ Z := by
    have : (b₀ : G) ∈ cen Q := by
      rw [cen_eq]
      exact ⟨D.VQ b₀.2, hcentral⟩
    rwa [← hc.hyp.hZ] at this
  exact hu0 ((secVec_eq_zero_iff ψ b₀).mpr hbZ)

theorem Ctx.pairVec_eq_one_iff_spForm (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (D : NatCommData Q (Vt M (LB M Q B) B Z t) Z (Rt M (LB M Q B) t) t) {K : Type} [Field K]
    {m : ℕ} (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {Kg : Type} [Field Kg] [Finite Kg] {γ : G → Kg} {M₀ : Tim79.QuadModel Q Z Kg γ}
    (h : GlobalModelData M Q Z γ M₀) (θ : Kg ≃+* K)
    (hθ : ∀ (c : Kg) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
      secVec ψ w = θ c • secVec ψ v) {b₀ : ↥(Vt M (LB M Q B) B Z t)}
    (hu0 : secVec ψ b₀ ≠ 0) (x : Fin m ⊕ Fin m → K) :
    pairVec D ψ b₀ x = 1 ↔ spForm m K (secVec ψ b₀) x = 0 := by
  have hVR := hc.Rt_normalizes_Vt ht
  refine hc.pairVec_eq_one_iff_of_forward ht D ψ h θ hθ hu0 (spForm m K (secVec ψ b₀)) ?_ x
  intro y hy
  have hg0 := additive_eq_zero_of_range_spForm φ hφ (pairHom D ψ b₀) (x := secVec ψ b₀)
    (fun r hr z => by
      show Additive.ofMul (pairVec D ψ _ _) = Additive.ofMul (pairVec D ψ _ _)
      rw [pairVec_conj D ψ hψ hVR _ r hr z]) hy
  exact ofMul_eq_zero.mp hg0

open CFSG.ClassicalGroups.Alternating (Lsp)

theorem Ctx.sp_points_core (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) {m : ℕ} (hm : 2 ≤ m)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ u : Fin m ⊕ Fin m → K, u ≠ 0 ∧
      (∀ x : Fin m ⊕ Fin m → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u) ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u ∧
      ∀ r : ↥(Rt M (LB M Q B) t),
        (HypPlane Q Z B (conjSubgroup (r : G) B) t ↔
          spForm m K u ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0) ∧
        ((conjSubgroup (r : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          LspGL m K ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hnat : SpNat hc t :=
    ⟨K, inferInstance, inferInstance, hK, m, hm, φ, hφ, hker, hc.Rt_normalizes_Vt ht, hn, ψ, hψ⟩
  have hchi := stroth310Chi_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  have hnotQB := stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  have hperp := stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnotQB
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  let D := hc.natCommData ht hchi.1 hchi.2
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ :=
    hc.exists_globalRingEquiv ht hK addCommutantScalar_statedSp φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ h θ hθ
  set u := secVec ψ b₀ with hu
  have C' : ∀ (b : ↥(Vt M (LB M Q B) B Z t)), secVec ψ b ≠ 0 → ∀ x : Fin m ⊕ Fin m → K,
      pairVec D ψ b x = 1 ↔ spForm m K (secVec ψ b) x = 0 :=
    fun b hb x => hc.pairVec_eq_one_iff_spForm ht D φ hφ ψ hψ h θ hθ hb x
  have hsym : ∀ x y : Fin m ⊕ Fin m → K, spForm m K x y = 0 ↔ spForm m K y x = 0 := by
    intro x y
    rw [← spForm_isAlt.neg_eq x y, neg_eq_zero]
  have hW : ∀ x : Fin m ⊕ Fin m → K,
      (∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧
        secVec ψ w = x) ↔ spForm m K x u = 0 := by
    intro x
    constructor
    · rintro ⟨w, ⟨-, hwQB⟩, rfl⟩
      have hw := (hperp (w : G) w.2).mp hwQB
      obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ w)
      have h1 : ⁅(y : G), t⁆ * (w : G)⁻¹ ∈ Z := (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩
        w).mp hy
      have h2 : ⁅(b₀ : G), (y : G)⁆ = 1 := hw b₀ hb₀B y y.2 h1
      have h3 : pairVec D ψ b₀ (secVec ψ w) = 1 := by rw [pairVec_eq D ψ b₀ y hy]; exact h2
      exact (hsym _ _).mp ((C' b₀ hu0 _).mp h3)
    · intro hx
      obtain ⟨w, hw⟩ := exists_secVec_eq ψ x
      refine ⟨w, ⟨w.2, (hperp (w : G) w.2).mpr fun b hb y hy hyt => ?_⟩, hw⟩
      have hk : kapVec D ψ ⟨y, hy⟩ = x := by
        rw [← hw]
        exact (secVec_eq_iff ψ ⟨⁅y, t⁆, D.comm_t_mem y hy⟩ w).mpr hyt
      rw [← pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
      obtain ⟨c, hcc⟩ := (hBiff (secVec ψ ⟨b, hBV hb⟩)).mp ⟨⟨b, hBV hb⟩, hb, rfl⟩
      by_cases hc0 : c = 0
      · have hz : b ∈ Z := (secVec_eq_zero_iff ψ ⟨b, hBV hb⟩).mp (by rw [hcc, hc0, zero_smul])
        have := D.comm_Z_left hz hy
        rw [pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
        exact this
      · have hbu : secVec ψ ⟨b, hBV hb⟩ ≠ 0 := by
          rw [hcc]; exact smul_ne_zero hc0 hu0
        refine (C' ⟨b, hBV hb⟩ hbu x).mpr ?_
        rw [hcc, map_smul, LinearMap.smul_apply, smul_eq_mul, (hsym _ _).mp hx, mul_zero]
  have hL : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u := by
    refine map_subgroupOf_eq_LspGL_of_commFlag (N := hc.CN t) (L := LB M Q B) (B := B)
      (W := Vt M (LB M Q B) B Z t ⊓ QB B) φ hφ hker (fun x hx => hx.1) (le_Rt (LB M Q B) ht)
      ψ hψ hVR hZV hBV inf_le_left (le_inf hZV (hc.Z_le_QB).1)
      (fun y hy => exists_mul_of_mem_sup (fun b hb z hz => by
        have := hc.conj_Z_of_mem_Q (hc.le hb) hz
        calc b * z = (b * z * b⁻¹) * b := by group
          _ = z * b := by rw [this]) hy) hu0 hBiff hW (fun r => ?_)
    exact hRoot G M Q Z B hc n t hs (Or.inl hnat) _ rfl r r.2
  refine ⟨u, hu0, hBiff, hL, fun r => ⟨⟨fun hyp => ?_, fun hne => ?_⟩, ?_⟩⟩
  ·
    obtain ⟨ĉ, hĉ, hĉC, b, hb, hne⟩ := hyp
    refine spForm_ne_zero_of_commData D φ hφ ψ hψ hVR hBV
      (fun b' hb' => (hBiff (secVec ψ b')).mp ⟨b', hb', rfl⟩) (fun c hcC => ?_) hĉ hĉC hb hne
    obtain ⟨c₁, hc₁, z, hz, hcz⟩ := exists_mul_of_mem_sup (fun x hx z hz => by
      have := hc.conj_Z_of_mem_Q ((hc.conj_of_mem (hc.Rt_le_M t r.2)).le hx) hz
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [this]) hcC
    have hb1 : (r : G)⁻¹ * c₁ * r ∈ B := mem_conjSubgroup.mp hc₁
    have hb1V : (r : G)⁻¹ * c₁ * r ∈ Vt M (LB M Q B) B Z t := hBV hb1
    have hc₁V : c₁ ∈ Vt M (LB M Q B) B Z t := by
      have := (Subgroup.mem_normalizer_iff.mp (hVR r.2) _).mp hb1V
      rwa [show (r : G) * ((r : G)⁻¹ * c₁ * r) * (r : G)⁻¹ = c₁ by group] at this
    obtain ⟨a, haa⟩ := (hBiff (secVec ψ ⟨_, hb1V⟩)).mp ⟨⟨_, hb1V⟩, hb1, rfl⟩
    refine ⟨a, ?_⟩
    have e1 : secVec ψ ⟨c₁, hc₁V⟩ = (φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        secVec ψ ⟨_, hb1V⟩ := hψ r ⟨_, hb1V⟩ ⟨c₁, hc₁V⟩ (by group)
    have hzV : z ∈ Vt M (LB M Q B) B Z t := hZV hz
    have e2 : c = ⟨c₁, hc₁V⟩ * ⟨z, hzV⟩ := Subtype.ext hcz
    rw [e2, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz, add_zero, e1, haa,
      Matrix.mulVec_smul]
  ·
    have hr0 : (r : G) * (b₀ : G) * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR r.2) b₀).mp b₀.2
    set c₀ : ↥(Vt M (LB M Q B) B Z t) := ⟨(r : G) * b₀ * (r : G)⁻¹, hr0⟩ with hc₀
    have hc₀vec : secVec ψ c₀ = (φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u :=
      hψ r b₀ c₀ rfl
    obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ c₀)
    refine ⟨(y : G), y.2, ?_, (b₀ : G), hb₀B, ?_⟩
    · have h1 : ⁅(y : G), t⁆ * (c₀ : G)⁻¹ ∈ Z :=
        (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩ c₀).mp hy
      have hc₀C : (c₀ : G) ∈ conjSubgroup (r : G) B := by
        rw [mem_conjSubgroup]
        show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) ∈ B
        rw [show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) = (b₀ : G) by group]
        exact hb₀B
      have e : ⁅(y : G), t⁆ = (⁅(y : G), t⁆ * (c₀ : G)⁻¹) * (c₀ : G) := by group
      rw [e]
      exact (conjSubgroup (r : G) B ⊔ Z).mul_mem (Subgroup.mem_sup_right h1)
        (Subgroup.mem_sup_left hc₀C)
    · have h2 : pairVec D ψ b₀ (secVec ψ c₀) ≠ 1 := fun h1 => hne (by
        have := (C' b₀ hu0 _).mp h1
        rwa [hc₀vec] at this)
      rwa [pairVec_eq D ψ b₀ y hy] at h2
  · have hr₀ : (φ r) ∈ StatedSp m K := hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
    refine map_conjSubgroup_subgroupOf (e := spEquiv (m := m) (K := K)) φ hφ r
      (S := Lsp (spForm m K) spForm_isAlt u)
      (S' := Lsp (spForm m K) spForm_isAlt
        ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)) (fun h' => ?_) hL
    exact mem_Lsp_app_iff spForm_isAlt (spEquiv (m := m) (K := K) ⟨φ r, hr₀⟩) u h'

theorem Ctx.sp_points (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) {m : ℕ} (hm : 2 ≤ m)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    (hact : SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
      (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))) :
    ∃ u : Fin m ⊕ Fin m → K, u ≠ 0 ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u ∧
      ∀ r : ↥(Rt M (LB M Q B) t),
        (HypPlane Q Z B (conjSubgroup (r : G) B) t ↔
          spForm m K u ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0) ∧
        ((conjSubgroup (r : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          LspGL m K ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  obtain ⟨u, hu0, -, hL, hr⟩ := hc.sp_points_core h34 hRoot hs hK hm φ hφ hker ψ hψ
  exact ⟨u, hu0, hL, hr⟩

end CFSG.RankThree.GF2n.Stroth80
