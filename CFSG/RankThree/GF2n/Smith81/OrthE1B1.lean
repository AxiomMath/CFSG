module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Small

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


section GroupHelpers

theorem mem_sup_of_commute {Γ : Type} [Group Γ] {H K : Subgroup Γ}
    (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : Γ} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  let T : Subgroup Γ :=
    { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, x = a * b}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', H.mul_mem ha ha', b * b', K.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hc a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (Commute.inv_inv (hc a ha b hb : Commute a b)).symm }
  have hT : H ⊔ K ≤ T := sup_le
    (fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩) (fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩)
  exact hT hx

theorem exists_mul_of_sup_eq {Γ : Type} [Group Γ] {R N X : Subgroup Γ} (hNR : N ≤ R)
    (hXn : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X) (hsup : N ⊔ X = R) {r : Γ} (hr : r ∈ R) :
    ∃ n ∈ N, ∃ x ∈ X, r = n * x := by
  let T : Subgroup Γ :=
    { carrier := {g | ∃ n ∈ N, ∃ x ∈ X, g = n * x}
      one_mem' := ⟨1, N.one_mem, 1, X.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, x, hx, rfl⟩ ⟨n', hn', x', hx', rfl⟩
        have h1 : n'⁻¹ * x * n' ∈ X := by
          have := hXn n'⁻¹ (R.inv_mem (hNR hn')) x hx
          rwa [inv_inv] at this
        refine ⟨n * n', N.mul_mem hn hn', n'⁻¹ * x * n' * x', X.mul_mem h1 hx', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, x, hx, rfl⟩
        refine ⟨n⁻¹, N.inv_mem hn, n * x⁻¹ * n⁻¹, hXn n (hNR hn) x⁻¹ (X.inv_mem hx), ?_⟩
        group }
  have hT : N ⊔ X ≤ T := sup_le
    (fun n hn => ⟨n, hn, 1, X.one_mem, by simp⟩) (fun x hx => ⟨1, N.one_mem, x, hx, by simp⟩)
  have hR : R ≤ T := hsup ▸ hT
  obtain ⟨n, hn, x, hx, h⟩ := hR hr
  exact ⟨n, hn, x, hx, h⟩

theorem isSLModel_of_mulEquiv {n q : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSLModel n q Y) : IsSLModel n q X := by
  obtain ⟨L, hL, hfin, hq, ⟨e'⟩⟩ := h
  exact ⟨L, hL, hfin, hq, ⟨e.trans e'⟩⟩

end GroupHelpers

section Coord

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
  {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def ActsOn (φ : E ≃ₗ[K] E) (V : Submodule K E) (c : ↥V ≃ₗ[K] (ι → K))
    (a : GL ι K) : Prop :=
  ∀ v : ↥V, ∃ hw : φ (v : E) ∈ V, c ⟨φ v, hw⟩ = (a : Matrix ι ι K) *ᵥ c v

theorem ActsOn.unique {φ : E ≃ₗ[K] E} {V : Submodule K E} {c : ↥V ≃ₗ[K] (ι → K)}
    {a a' : GL ι K} (h : ActsOn φ V c a) (h' : ActsOn φ V c a') : a = a' := by
  refine Units.ext (Matrix.ext_iff_mulVec.mpr fun w => ?_)
  obtain ⟨hw, h1⟩ := h (c.symm w)
  obtain ⟨hw', h2⟩ := h' (c.symm w)
  rw [LinearEquiv.apply_symm_apply] at h1 h2
  rw [← h1, ← h2]

theorem ActsOn.congr {φ φ' : E ≃ₗ[K] E} {V : Submodule K E} {c : ↥V ≃ₗ[K] (ι → K)}
    {a : GL ι K} (h : ActsOn φ V c a) (he : ∀ v ∈ V, φ' v = φ v) : ActsOn φ' V c a := by
  intro v
  obtain ⟨hw, h1⟩ := h v
  have e : φ' (v : E) = φ v := he v v.2
  have hw' : φ' (v : E) ∈ V := by rw [e]; exact hw
  refine ⟨hw', ?_⟩
  rw [← h1]
  exact congrArg c (Subtype.ext e)

theorem actsOn_one_of_fix {φ : E ≃ₗ[K] E} {V : Submodule K E} {c : ↥V ≃ₗ[K] (ι → K)}
    (he : ∀ v ∈ V, φ v = v) : ActsOn φ V c 1 := by
  intro v
  have hw : φ (v : E) ∈ V := by rw [he v v.2]; exact v.2
  refine ⟨hw, ?_⟩
  rw [Units.val_one, Matrix.one_mulVec]
  exact congrArg c (Subtype.ext (he v v.2))

theorem rep_exists {P : Type} [Group P] (φ : P →* (E ≃ₗ[K] E)) (V : Submodule K E)
    (c : ↥V ≃ₗ[K] (ι → K)) (Ω : Subgroup (GL ι K)) (N X : Subgroup P)
    (hdec : ∀ r : P, ∃ n ∈ N, ∃ x ∈ X, r = n * x)
    (hN : ∀ n ∈ N, ∀ v ∈ V, φ n v = v) (hX : ∀ x ∈ X, ∀ v ∈ V, φ x v ∈ V)
    (hXrep : ∀ x ∈ X, ∃ a ∈ Ω, ActsOn (φ x) V c a) :
    ∃ ρ : P →* GL ι K, (∀ r, ρ r ∈ Ω) ∧ (∀ r, ActsOn (φ r) V c (ρ r)) ∧
      (∀ n ∈ N, ρ n = 1) := by
  have hfact : ∀ r : P, ∀ n ∈ N, ∀ x ∈ X, r = n * x → ∀ v ∈ V, φ r v = φ x v := by
    intro r n hn x hx hr v hv
    rw [hr, map_mul, LinearEquiv.mul_apply, hN n hn _ (hX x hx v hv)]
  have hex : ∀ r : P, ∃ a : GL ι K, a ∈ Ω ∧ ActsOn (φ r) V c a := by
    intro r
    obtain ⟨n, hn, x, hx, hr⟩ := hdec r
    obtain ⟨a, ha, hact⟩ := hXrep x hx
    refine ⟨a, ha, fun v => ?_⟩
    obtain ⟨hw, h1⟩ := hact v
    have e : φ r (v : E) = φ x v := hfact r n hn x hx hr v v.2
    have hw' : φ r (v : E) ∈ V := by rw [e]; exact hw
    refine ⟨hw', ?_⟩
    rw [← h1]
    exact congrArg c (Subtype.ext e)
  choose ρ0 hρ0Ω hρ0 using hex
  have hmul : ∀ r s : P, ρ0 (r * s) = ρ0 r * ρ0 s := by
    intro r s
    refine ActsOn.unique (hρ0 (r * s)) ?_
    intro v
    obtain ⟨hws, h1⟩ := hρ0 s v
    obtain ⟨hwr, h2⟩ := hρ0 r ⟨φ s v, hws⟩
    have h2' : c ⟨φ r (φ s v), hwr⟩ = (ρ0 r : Matrix ι ι K) *ᵥ c ⟨φ s v, hws⟩ := h2
    have e : φ (r * s) (v : E) = φ r (φ s v) := by rw [map_mul, LinearEquiv.mul_apply]
    have hw' : φ (r * s) (v : E) ∈ V := by rw [e]; exact hwr
    refine ⟨hw', ?_⟩
    calc c ⟨φ (r * s) v, hw'⟩ = c ⟨φ r (φ s v), hwr⟩ := congrArg c (Subtype.ext e)
      _ = (ρ0 r : Matrix ι ι K) *ᵥ c ⟨φ s v, hws⟩ := h2'
      _ = (ρ0 r : Matrix ι ι K) *ᵥ ((ρ0 s : Matrix ι ι K) *ᵥ c v) := by rw [h1]
      _ = ((ρ0 r * ρ0 s : GL ι K) : Matrix ι ι K) *ᵥ c v := by
          rw [Units.val_mul, Matrix.mulVec_mulVec]
  refine ⟨MonoidHom.mk' ρ0 hmul, fun r => hρ0Ω r, fun r => hρ0 r, fun n hn => ?_⟩
  exact ActsOn.unique (hρ0 n) (actsOn_one_of_fix fun v hv => hN n hn v hv)

end Coord

section Line

variable {K : Type} [Field K] [CharP K 2] {E : Type} [AddCommGroup E] [Module K E]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem line_card {P : Type} [Group P] (φ : P →* (E ≃ₗ[K] E)) (V : Submodule K E)
    (c : ↥V ≃ₗ[K] (ι → K)) (Ω : Subgroup (GL ι K)) (ρ : P →* GL ι K)
    (hΩ : ∀ r, ρ r ∈ Ω) (hρ : ∀ r, ActsOn (φ r) V c (ρ r))
    (N : Subgroup P) (γ : E → E) (hγV : ∀ v ∈ V, γ v ∈ V) (hγγ : ∀ e, γ (γ e) = 0)
    (hline : ∀ y ∈ N, ∃ k : K, ∀ e, φ y e = e + k • γ e)
    (hsurj : ∀ k : K, ∃ y ∈ N, ∀ e, φ y e = e + k • γ e)
    (hγne : ∃ v ∈ V, γ v ≠ 0) :
    N.map ρ ≤ Ω ∧ IsPGroup 2 (N.map ρ) ∧ Nat.card (N.map ρ) = Nat.card K ∧
      ∃ Γ : Matrix ι ι K, Γ ≠ 0 ∧
        ∀ k : K, ∃ a ∈ N.map ρ, (a : Matrix ι ι K) - 1 = k • Γ := by
  obtain ⟨v0, hv0, hγv0⟩ := hγne
  choose yk hykN hyk using hsurj
  have key : ∀ (y : P) (k : K), (∀ e, φ y e = e + k • γ e) → ∀ v : ↥V,
      (ρ y : Matrix ι ι K) *ᵥ c v = c v + k • c ⟨γ v, hγV v v.2⟩ := by
    intro y k hy v
    obtain ⟨hw, h1⟩ := hρ y v
    have e : (⟨φ y (v : E), hw⟩ : ↥V) = v + k • ⟨γ v, hγV v v.2⟩ := by
      apply Subtype.ext
      simp [hy]
    rw [← h1, e, map_add, map_smul]
  have hcw : c ⟨γ v0, hγV v0 hv0⟩ ≠ 0 := by
    intro h
    apply hγv0
    have h' := c.injective (h.trans (map_zero c).symm)
    exact congrArg Subtype.val h'
  have hsq : ∀ y ∈ N, ρ y ^ 2 = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hline y hy
    have hfix : ∀ v ∈ V, φ (y ^ 2) v = v := by
      intro v hv
      have hkk : k + k = 0 := CharTwo.add_self_eq_zero k
      rw [pow_two, map_mul, LinearEquiv.mul_apply, hk v, map_add, map_smul, hk v, hk (γ v),
        hγγ v, smul_zero, add_zero]
      have : v + k • γ v + k • γ v = v + (k + k) • γ v := by rw [add_smul]; abel
      rw [this, hkk, zero_smul, add_zero]
    rw [← map_pow]
    exact ActsOn.unique (hρ (y ^ 2)) (actsOn_one_of_fix hfix)
  have hle : N.map ρ ≤ Ω := by
    rintro _ ⟨r, _, rfl⟩
    exact hΩ r
  have hpg : IsPGroup 2 (N.map ρ) := by
    rintro ⟨a, ha⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, OneMemClass.coe_one]
    exact hsq y hy
  let f : K → ↥(N.map ρ) := fun k => ⟨ρ (yk k), Subgroup.mem_map_of_mem ρ (hykN k)⟩
  have hf_inj : Function.Injective f := by
    intro k l hkl
    have hρeq : ρ (yk k) = ρ (yk l) := congrArg Subtype.val hkl
    have h1 := key (yk k) k (hyk k) ⟨v0, hv0⟩
    have h2 := key (yk l) l (hyk l) ⟨v0, hv0⟩
    rw [hρeq] at h1
    have h3 := add_left_cancel (h1.symm.trans h2)
    have h4 : (k - l) • c ⟨γ v0, hγV v0 hv0⟩ = 0 := by rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.mp h4 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hcw
  have hf_surj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨k, hk⟩ := hline y hy
    refine ⟨k, Subtype.ext ?_⟩
    show ρ (yk k) = ρ y
    exact ActsOn.unique ((hρ (yk k)).congr fun v _ => by rw [hk v, hyk k v]) (hρ y)
  have hΓne : (ρ (yk 1) : Matrix ι ι K) - 1 ≠ 0 := by
    intro h
    have h1 : ρ (yk 1) = 1 := Units.ext (sub_eq_zero.mp h)
    have h2 := key (yk 1) 1 (hyk 1) ⟨v0, hv0⟩
    rw [h1, Units.val_one, Matrix.one_mulVec, one_smul] at h2
    exact hcw (add_eq_left.mp h2.symm)
  have hline_eq : ∀ k : K, (ρ (yk k) : Matrix ι ι K) - 1 = k • ((ρ (yk 1) : Matrix ι ι K) - 1) := by
    intro k
    refine Matrix.ext_iff_mulVec.mpr fun w => ?_
    have H : ∀ v : ↥V, ((ρ (yk k) : Matrix ι ι K) - 1) *ᵥ c v =
        (k • ((ρ (yk 1) : Matrix ι ι K) - 1)) *ᵥ c v := by
      intro v
      have h1 := key (yk k) k (hyk k) v
      have h2 := key (yk 1) 1 (hyk 1) v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec, h2]
      simp only [one_smul, smul_add, smul_sub]
      abel
    have := H (c.symm w)
    rwa [LinearEquiv.apply_symm_apply] at this
  refine ⟨hle, hpg, (Nat.card_eq_of_bijective f ⟨hf_inj, hf_surj⟩).symm,
    (ρ (yk 1) : Matrix ι ι K) - 1, hΓne, fun k => ⟨ρ (yk k), Subgroup.mem_map_of_mem ρ (hykN k),
      hline_eq k⟩⟩

end Line

section Pre

variable {Gp : Type} [Group Gp] {ι K : Type} [Field K] [Fintype ι] [DecidableEq ι]

structure XRep (Q : Subgroup Gp) {R X : Subgroup Gp} (hXR : X ≤ R) (ρ : R →* GL ι K)
    (Ω : Subgroup (GL ι K)) : Prop where
  mem : ∀ x (hx : x ∈ X), ρ ⟨x, hXR hx⟩ ∈ Ω
  faith : ∀ x (hx : x ∈ X), ρ ⟨x, hXR hx⟩ = 1 → x ∈ Q
  surj : ∀ a ∈ Ω, ∃ x, ∃ hx : x ∈ X, ρ ⟨x, hXR hx⟩ = a
  one_Q : ∀ q ∈ Q, ∀ hq : q ∈ X, ρ ⟨q, hXR hq⟩ = 1

@[expose] def preIm {R X : Subgroup Gp} (hXR : X ≤ R) (ρ : R →* GL ι K)
    (F : Subgroup (GL ι K)) : Subgroup Gp :=
  (F.comap (ρ.comp (Subgroup.inclusion hXR))).map X.subtype

theorem mem_preIm {R X : Subgroup Gp} (hXR : X ≤ R) (ρ : R →* GL ι K) (F : Subgroup (GL ι K))
    {x : Gp} : x ∈ preIm hXR ρ F ↔ ∃ hx : x ∈ X, ρ ⟨x, hXR hx⟩ ∈ F := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hx, hF⟩
    exact ⟨⟨x, hx⟩, hF, rfl⟩

theorem quotSat_preIm {R X Q : Subgroup Gp} (hQX : Q ≤ X) (hXR : X ≤ R) (ρ : R →* GL ι K)
    {Ω : Subgroup (GL ι K)} (D : XRep Q hXR ρ Ω) (q : ℕ) (F : Subgroup (GL ι K)) (hFΩ : F ≤ Ω)
    (hSL : IsSLModel 2 q ↥F) : QuotSat (preIm hXR ρ F) Q (IsSLModel 2 q) := by
  have hPX : preIm hXR ρ F ≤ X := fun x hx => ((mem_preIm hXR ρ F).1 hx).1
  let ψ0 : ↥(preIm hXR ρ F) →* GL ι K :=
    ρ.comp ((Subgroup.inclusion hXR).comp (Subgroup.inclusion hPX))
  let ψ : ↥(preIm hXR ρ F) →* ↥F :=
    ψ0.codRestrict F (fun x => ((mem_preIm hXR ρ F).1 x.2).2)
  have hker : ψ.ker = Q.subgroupOf (preIm hXR ρ F) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : ρ ⟨x.1, hXR (hPX x.2)⟩ = 1 := congrArg Subtype.val h
      exact D.faith x.1 (hPX x.2) h'
    · intro h
      apply Subtype.ext
      exact D.one_Q x.1 h (hQX h)
  have hsurjψ : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, hρx⟩ := D.surj a (hFΩ ha)
    have hxP : x ∈ preIm hXR ρ F := (mem_preIm hXR ρ F).2 ⟨hx, by rw [hρx]; exact ha⟩
    exact ⟨⟨x, hxP⟩, Subtype.ext hρx⟩
  have hnorm : (Q.subgroupOf (preIm hXR ρ F)).Normal := by
    rw [← hker]
    infer_instance
  haveI := hnorm
  let e1 := QuotientGroup.quotientKerEquivOfSurjective ψ hsurjψ
  let e2 := QuotientGroup.quotientMulEquivOfEq (N := ψ.ker) hker.symm
  exact ⟨hnorm, isSLModel_of_mulEquiv (e2.trans e1) hSL⟩

theorem twoFactors_preIm {R X Q : Subgroup Gp} (hQX : Q ≤ X) (hXR : X ≤ R) (ρ : R →* GL ι K)
    {Ω : Subgroup (GL ι K)} (D : XRep Q hXR ρ Ω) (q : ℕ) (F₁ F₂ : Subgroup (GL ι K))
    (hsup : F₁ ⊔ F₂ = Ω) (hinf : F₁ ⊓ F₂ = ⊥) (hcomm : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a)
    (h₁ : IsSLModel 2 q ↥F₁) (h₂ : IsSLModel 2 q ↥F₂) :
    TwoFactors Q X (preIm hXR ρ F₁) (preIm hXR ρ F₂) q := by
  have hle₁ : F₁ ≤ Ω := hsup ▸ le_sup_left
  have hle₂ : F₂ ≤ Ω := hsup ▸ le_sup_right
  have hQ₁ : Q ≤ preIm hXR ρ F₁ := fun q hq =>
    (mem_preIm hXR ρ F₁).2 ⟨hQX hq, by rw [D.one_Q q hq (hQX hq)]; exact F₁.one_mem⟩
  have hQ₂ : Q ≤ preIm hXR ρ F₂ := fun q hq =>
    (mem_preIm hXR ρ F₂).2 ⟨hQX hq, by rw [D.one_Q q hq (hQX hq)]; exact F₂.one_mem⟩
  have hX₁ : preIm hXR ρ F₁ ≤ X := fun x hx => ((mem_preIm hXR ρ F₁).1 hx).1
  have hX₂ : preIm hXR ρ F₂ ≤ X := fun x hx => ((mem_preIm hXR ρ F₂).1 hx).1
  unfold TwoFactors
  refine ⟨hQ₁, hQ₂, hX₁, hX₂, ?_, ?_, ?_, quotSat_preIm hQX hXR ρ D q F₁ hle₁ h₁,
    quotSat_preIm hQX hXR ρ D q F₂ hle₂ h₂⟩
  · apply le_antisymm (sup_le hX₁ hX₂)
    intro x hx
    have hΩx : ρ ⟨x, hXR hx⟩ ∈ F₁ ⊔ F₂ := by rw [hsup]; exact D.mem x hx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcomm hΩx
    obtain ⟨x₁, hx₁, hρ₁⟩ := D.surj a (hle₁ ha)
    have hx₂ : x₁⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hx₁) hx
    have hρ₂ : ρ ⟨x₁⁻¹ * x, hXR hx₂⟩ = b := by
      have e : (⟨x₁⁻¹ * x, hXR hx₂⟩ : R) = (⟨x₁, hXR hx₁⟩ : R)⁻¹ * ⟨x, hXR hx⟩ := rfl
      rw [e, map_mul, map_inv, hρ₁, hab, ← mul_assoc, inv_mul_cancel, one_mul]
    have hm₁ : x₁ ∈ preIm hXR ρ F₁ := (mem_preIm hXR ρ F₁).2 ⟨hx₁, by rw [hρ₁]; exact ha⟩
    have hm₂ : x₁⁻¹ * x ∈ preIm hXR ρ F₂ :=
      (mem_preIm hXR ρ F₂).2 ⟨hx₂, by rw [hρ₂]; exact hb⟩
    have hprod := Subgroup.mul_mem_sup hm₁ hm₂
    rwa [mul_inv_cancel_left] at hprod
  · apply le_antisymm
    · intro x hx
      obtain ⟨h₁', h₂'⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxX, hF₁⟩ := (mem_preIm hXR ρ F₁).1 h₁'
      obtain ⟨hxX₂, hF₂⟩ := (mem_preIm hXR ρ F₂).1 h₂'
      have h0 : ρ ⟨x, hXR hxX⟩ ∈ (⊥ : Subgroup (GL ι K)) := by
        rw [← hinf]; exact Subgroup.mem_inf.mpr ⟨hF₁, hF₂⟩
      exact D.faith x hxX (Subgroup.mem_bot.mp h0)
    · exact le_inf hQ₁ hQ₂
  · intro a ha b hb
    obtain ⟨haX, haF⟩ := (mem_preIm hXR ρ F₁).1 ha
    obtain ⟨hbX, hbF⟩ := (mem_preIm hXR ρ F₂).1 hb
    have hcX : ⁅a, b⁆ ∈ X := by
      rw [commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem haX hbX) (X.inv_mem haX)) (X.inv_mem hbX)
    apply D.faith _ hcX
    have e : (⟨⁅a, b⁆, hXR hcX⟩ : R) = ⁅(⟨a, hXR haX⟩ : R), (⟨b, hXR hbX⟩ : R)⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ haF _ hbF

end Pre

section E1Rep

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

@[expose] def phiRt (AM : ActionModel M Q Z) (hRH : Rt M (LB M Q B) t ≤ H0 M Z) :
    ↥(Rt M (LB M Q B) t) →* (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) :=
  AM.φ.comp (Subgroup.inclusion hRH)

theorem mem_actImage_of (AM : ActionModel M Q Z) {S : Subgroup G} (x : ↥(H0 M Z))
    (hx : (x : G) ∈ S) : AM.φ x ∈ AM.actImage S :=
  Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem b1_rep (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    (hdec : ∀ r ∈ Rt M (LB M Q B) t, ∃ n ∈ Nt M (LB M Q B) t, ∃ x ∈ E1Xpre M Q B t, r = n * x)
    (hXRt : E1Xpre M Q B t ≤ Rt M (LB M Q B) t)
    (hNfix : ∀ n : ↥(H0 M Z), (n : G) ∈ Nt M (LB M Q B) t →
      ∀ v ∈ AM.Vsp hH.ctx t, AM.φ n v = v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → AM.K) → AM.K)
    (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (hact : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c f) :
    ∃ ρ : ↥(Rt M (LB M Q B) t) →* GL ι AM.K,
      (∀ r, ρ r ∈ StatedOmega f) ∧
      (∀ r, ActsOn (phiRt AM (hH.ctx.Rt_le_H0 t) r) (AM.Vsp hH.ctx t) c (ρ r)) ∧
      (∀ n : ↥(Rt M (LB M Q B) t), (n : G) ∈ Nt M (LB M Q B) t → ρ n = 1) := by
  classical
  have hc := hH.ctx
  obtain ⟨hXst, h1, -, -⟩ := hact
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNRt : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  let N' : Subgroup ↥(Rt M (LB M Q B) t) := (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)
  let X' : Subgroup ↥(Rt M (LB M Q B) t) := (E1Xpre M Q B t).subgroupOf (Rt M (LB M Q B) t)
  have hdec' : ∀ r : ↥(Rt M (LB M Q B) t), ∃ n ∈ N', ∃ x ∈ X', r = n * x := by
    intro r
    obtain ⟨n, hn, x, hx, hrx⟩ := hdec r.1 r.2
    exact ⟨⟨n, hNRt hn⟩, Subgroup.mem_subgroupOf.mpr hn, ⟨x, hXRt hx⟩,
      Subgroup.mem_subgroupOf.mpr hx, Subtype.ext hrx⟩
  have hN : ∀ n ∈ N', ∀ v ∈ AM.Vsp hc t, phiRt AM hRH n v = v := fun n hn v hv =>
    hNfix ⟨n.1, hRH n.2⟩ (Subgroup.mem_subgroupOf.mp hn) v hv
  have hX : ∀ x ∈ X', ∀ v ∈ AM.Vsp hc t, phiRt AM hRH x v ∈ AM.Vsp hc t := fun x hx v hv =>
    hXst (AM.φ ⟨x.1, hRH x.2⟩) (mem_actImage_of AM _ (Subgroup.mem_subgroupOf.mp hx)) v hv
  have hXrep : ∀ x ∈ X', ∃ a ∈ StatedOmega f, ActsOn (phiRt AM hRH x) (AM.Vsp hc t) c a := by
    intro x hx
    obtain ⟨A, hA, hcl⟩ := h1 (AM.φ ⟨x.1, hRH x.2⟩)
      (mem_actImage_of AM _ (Subgroup.mem_subgroupOf.mp hx))
    refine ⟨A, hA, fun v => ⟨hXst _ (mem_actImage_of AM _ (Subgroup.mem_subgroupOf.mp hx)) v v.2,
      ?_⟩⟩
    exact hcl v v.2
  obtain ⟨ρ, hΩ, hρ, hNρ⟩ := rep_exists (phiRt AM hRH) (AM.Vsp hc t) c (StatedOmega f) N' X'
    hdec' hN hX hXrep
  exact ⟨ρ, hΩ, hρ, fun n hn => hNρ ⟨n, hNRt hn⟩ (Subgroup.mem_subgroupOf.mpr hn)⟩

theorem b1_XRep (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → AM.K) → AM.K)
    (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (hact : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c f)
    (hXRt : E1Xpre M Q B t ≤ Rt M (LB M Q B) t)
    (ρ : ↥(Rt M (LB M Q B) t) →* GL ι AM.K)
    (hΩ : ∀ r, ρ r ∈ StatedOmega f)
    (hρ : ∀ r, ActsOn (phiRt AM (hH.ctx.Rt_le_H0 t) r) (AM.Vsp hH.ctx t) c (ρ r)) :
    XRep Q hXRt ρ (StatedOmega f) := by
  classical
  obtain ⟨hXst, -, h2, h3⟩ := hact
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hH.ctx.Rt_le_H0 t
  refine ⟨fun x _ => hΩ _, ?_, ?_, ?_⟩
  · intro x hx hρx
    have hfix : ∀ v ∈ AM.Vsp hH.ctx t, AM.φ ⟨x, hRH (hXRt hx)⟩ v = v := by
      intro v hv
      obtain ⟨hw, h⟩ := hρ ⟨x, hXRt hx⟩ ⟨v, hv⟩
      rw [hρx, Units.val_one, Matrix.one_mulVec] at h
      exact congrArg Subtype.val (c.injective h)
    have hone := h3 (AM.φ ⟨x, hRH (hXRt hx)⟩)
      (mem_actImage_of AM ⟨x, hRH (hXRt hx)⟩ hx) hfix
    exact (AM.φ_ker ⟨x, hRH (hXRt hx)⟩).mp hone
  · intro a ha
    obtain ⟨g, hg, hcl⟩ := h2 a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hyX : y.1 ∈ E1Xpre M Q B t := Subgroup.mem_subgroupOf.mp hy
    refine ⟨y.1, hyX, ActsOn.unique (hρ ⟨y.1, hXRt hyX⟩) ?_⟩
    intro v
    exact ⟨hXst _ (mem_actImage_of AM y hyX) v v.2, hcl v v.2⟩
  · intro q hq hqX
    have hφ : AM.φ ⟨q, hRH (hXRt hqX)⟩ = 1 := (AM.φ_ker ⟨q, hRH (hXRt hqX)⟩).mpr hq
    have hfix : ∀ v ∈ AM.Vsp hH.ctx t,
        phiRt AM (hH.ctx.Rt_le_H0 t) ⟨q, hXRt hqX⟩ v = v := by
      intro v hv
      show AM.φ ⟨q, hRH (hXRt hqX)⟩ v = v
      rw [hφ]
      rfl
    exact ActsOn.unique (hρ ⟨q, hXRt hqX⟩) (actsOn_one_of_fix hfix)

@[expose] def conjNtR (g : G) : Subgroup ↥(Rt M (LB M Q B) t) :=
  (conjSubgroup g (Nt M (LB M Q B) t)).subgroupOf (Rt M (LB M Q B) t)

theorem b1_line (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    (β : AM.M₀.E →ₗ[AM.K] AM.M₀.E) (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hN1 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ k : AM.K, ∀ e, AM.φ x e = e + k • β e)
    (hN2 : ∀ k : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + k • β e)
    (hdec : ∀ r ∈ Rt M (LB M Q B) t, ∃ n ∈ Nt M (LB M Q B) t, ∃ x ∈ E1Xpre M Q B t, r = n * x)
    (hXRt : E1Xpre M Q B t ≤ Rt M (LB M Q B) t)
    (hLBRt : LB M Q B ≤ Rt M (LB M Q B) t)
    (hNfix : ∀ n : ↥(H0 M Z), (n : G) ∈ Nt M (LB M Q B) t →
      ∀ v ∈ AM.Vsp hH.ctx t, AM.φ n v = v)
    (hXV : ∀ x : ↥(H0 M Z), (x : G) ∈ E1Xpre M Q B t →
      ∀ v ∈ AM.Vsp hH.ctx t, AM.φ x v ∈ AM.Vsp hH.ctx t)
    (hfix : ∀ x : ↥(H0 M Z), (x : G) ∈ E1Xpre M Q B t →
      (∀ v ∈ AM.Vsp hH.ctx t, AM.φ x v = v) → (x : G) ∈ Q)
    (g : G) (hg : E1CaseBHyp M Q B t g)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → AM.K) → AM.K)
    (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (ρ : ↥(Rt M (LB M Q B) t) →* GL ι AM.K)
    (hΩ : ∀ r, ρ r ∈ StatedOmega f)
    (hρ : ∀ r, ActsOn (phiRt AM (hH.ctx.Rt_le_H0 t) r) (AM.Vsp hH.ctx t) c (ρ r)) :
    (conjNtR g).map ρ ≤ StatedOmega f ∧ IsPGroup 2 ((conjNtR g).map ρ) ∧
      Nat.card ((conjNtR g).map ρ) = Nat.card AM.K ∧
      ∃ Γ : Matrix ι ι AM.K, Γ ≠ 0 ∧
        ∀ k : AM.K, ∃ a ∈ (conjNtR g).map ρ, (a : Matrix ι ι AM.K) - 1 = k • Γ := by
  classical
  have hc := hH.ctx
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hβββ : ∀ x, β (β x) = 0 := fun x => hβ.kills _ (hβ.range x)
  have hgH : g ∈ H0 M Z := Lgen_le_H0 hc hg.1
  let gH : ↥(H0 M Z) := ⟨g, hgH⟩
  let gφ := AM.φ gH
  let γ : AM.M₀.E → AM.M₀.E := fun e => gφ (β (gφ.symm e))
  have hconj : ∀ (x : ↥(H0 M Z)) (k : AM.K), (∀ e, AM.φ x e = e + k • β e) →
      ∀ e, AM.φ (gH * x * gH⁻¹) e = e + k • γ e := by
    intro x k hx e
    rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change gφ (AM.φ x (gφ.symm e)) = e + k • γ e
    rw [hx, map_add, map_smul, LinearEquiv.apply_symm_apply]
  have hsurj : ∀ k : AM.K, ∃ y ∈ conjNtR g, ∀ e, phiRt AM hRH y e = e + k • γ e := by
    intro k
    obtain ⟨x, hxN, hx⟩ := hN2 k
    have hyG : g * (x : G) * g⁻¹ ∈ conjSubgroup g (Nt M (LB M Q B) t) := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hxN
    have hyR : g * (x : G) * g⁻¹ ∈ Rt M (LB M Q B) t := hLBRt (hg.2.2.1 hyG)
    refine ⟨⟨g * (x : G) * g⁻¹, hyR⟩, Subgroup.mem_subgroupOf.mpr hyG, fun e => ?_⟩
    have hel : (⟨g * (x : G) * g⁻¹, hRH hyR⟩ : ↥(H0 M Z)) = gH * x * gH⁻¹ := rfl
    exact (congrArg (fun z => AM.φ z e) hel).trans (hconj x k hx e)
  have hline : ∀ y ∈ conjNtR g, ∃ k : AM.K, ∀ e, phiRt AM hRH y e = e + k • γ e := by
    rintro ⟨y, hyR⟩ hy
    have hyC : y ∈ conjSubgroup g (Nt M (LB M Q B) t) := Subgroup.mem_subgroupOf.mp hy
    rw [mem_conjSubgroup] at hyC
    let x : ↥(H0 M Z) := gH⁻¹ * ⟨y, hRH hyR⟩ * gH
    have hxN : (x : G) ∈ Nt M (LB M Q B) t := hyC
    obtain ⟨k, hk⟩ := hN1 x hxN
    refine ⟨k, fun e => ?_⟩
    have hel : (⟨y, hRH hyR⟩ : ↥(H0 M Z)) = gH * x * gH⁻¹ := by
      simp only [x]
      group
    exact (congrArg (fun z => AM.φ z e) hel).trans (hconj x k hk e)
  have hγV : ∀ v ∈ AM.Vsp hc t, γ v ∈ AM.Vsp hc t := by
    intro v hv
    obtain ⟨y, -, hy⟩ := hsurj 1
    obtain ⟨hw, -⟩ := hρ y ⟨v, hv⟩
    have hw' : v + γ v ∈ AM.Vsp hc t := by
      have e1 : phiRt AM hRH y v = v + γ v := by
        rw [hy v, one_smul]
      rw [← e1]
      exact hw
    exact (Submodule.add_mem_iff_right _ hv).mp hw'
  have hγγ : ∀ e, γ (γ e) = 0 := by
    intro e
    simp only [γ, LinearEquiv.symm_apply_apply]
    rw [hβββ, map_zero]
  have hγne : ∃ v ∈ AM.Vsp hc t, γ v ≠ 0 := by
    by_contra hcon'
    have hcon : ∀ v ∈ AM.Vsp hc t, γ v = 0 := fun v hv => by_contra fun h => hcon' ⟨v, hv, h⟩
    apply hg.2.2.2
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      have hyR : y ∈ Rt M (LB M Q B) t := hLBRt (hg.2.2.1 hy)
      obtain ⟨n, hn, x, hx, hyx⟩ := hdec y hyR
      have hxH : x ∈ H0 M Z := hRH (hXRt hx)
      have hnH : n ∈ H0 M Z := hRH (orthE1_Nt_le_Rt M (LB M Q B) t hn)
      have hyN : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈ conjNtR g :=
        Subgroup.mem_subgroupOf.mpr hy
      obtain ⟨k, hk⟩ := hline _ hyN
      have hfixy : ∀ v ∈ AM.Vsp hc t, AM.φ (⟨y, hRH hyR⟩ : ↥(H0 M Z)) v = v := by
        intro v hv
        show phiRt AM hRH ⟨y, hyR⟩ v = v
        rw [hk v, hcon v hv, smul_zero, add_zero]
      have hel : (⟨y, hRH hyR⟩ : ↥(H0 M Z)) = (⟨n, hnH⟩ : ↥(H0 M Z)) * ⟨x, hxH⟩ :=
        Subtype.ext hyx
      have hfixx : ∀ v ∈ AM.Vsp hc t, AM.φ (⟨x, hxH⟩ : ↥(H0 M Z)) v = v := by
        intro v hv
        have hxv : AM.φ (⟨x, hxH⟩ : ↥(H0 M Z)) v ∈ AM.Vsp hc t := hXV ⟨x, hxH⟩ hx v hv
        have h1 := hfixy v hv
        rw [hel, map_mul, LinearEquiv.mul_apply, hNfix ⟨n, hnH⟩ hn _ hxv] at h1
        exact h1
      have hxQ : x ∈ Q := hfix ⟨x, hxH⟩ hx hfixx
      have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc hH.mem
      rw [hyx]
      exact (Nt M (LB M Q B) t).mul_mem hn (hQN hxQ)
    · exact (card_conjSubgroup g _).ge
  exact line_card (phiRt AM hRH) (AM.Vsp hc t) c (StatedOmega f) ρ hΩ hρ (conjNtR g) γ hγV hγγ
    hline hsurj hγne


theorem b1_core (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    (β : AM.M₀.E →ₗ[AM.K] AM.M₀.E) (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hN1 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ k : AM.K, ∀ e, AM.φ x e = e + k • β e)
    (hN2 : ∀ k : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + k • β e)
    (hdec : ∀ r ∈ Rt M (LB M Q B) t, ∃ n ∈ Nt M (LB M Q B) t, ∃ x ∈ E1Xpre M Q B t, r = n * x)
    (hXRt : E1Xpre M Q B t ≤ Rt M (LB M Q B) t)
    (hLBRt : LB M Q B ≤ Rt M (LB M Q B) t)
    (g : G) (hg : E1CaseBHyp M Q B t g)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → AM.K) → AM.K)
    (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (hact : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c f) :
    ∃ ρ : ↥(Rt M (LB M Q B) t) →* GL ι AM.K,
      XRep Q hXRt ρ (StatedOmega f) ∧
      (∀ n : ↥(Rt M (LB M Q B) t), (n : G) ∈ Nt M (LB M Q B) t → ρ n = 1) ∧
      ((conjNtR g).map ρ ≤ StatedOmega f ∧ IsPGroup 2 ((conjNtR g).map ρ) ∧
        Nat.card ((conjNtR g).map ρ) = Nat.card AM.K ∧
        ∃ Γ : Matrix ι ι AM.K, Γ ≠ 0 ∧
          ∀ k : AM.K, ∃ a ∈ (conjNtR g).map ρ, (a : Matrix ι ι AM.K) - 1 = k • Γ) := by
  have hNfix : ∀ n : ↥(H0 M Z), (n : G) ∈ Nt M (LB M Q B) t →
      ∀ v ∈ AM.Vsp hH.ctx t, AM.φ n v = v := by
    intro n hn v hv
    obtain ⟨k, hk⟩ := hN1 n hn
    rw [hk v, hβ.kills v hv, smul_zero, add_zero]
  obtain ⟨hXst, h1, h2, h3⟩ := hact
  obtain ⟨ρ, hΩ, hρ, hNρ⟩ := b1_rep hH AM hdec hXRt hNfix f c ⟨hXst, h1, h2, h3⟩
  have hXRep := b1_XRep hH AM f c ⟨hXst, h1, h2, h3⟩ hXRt ρ hΩ hρ
  have hXV : ∀ x : ↥(H0 M Z), (x : G) ∈ E1Xpre M Q B t →
      ∀ v ∈ AM.Vsp hH.ctx t, AM.φ x v ∈ AM.Vsp hH.ctx t := fun x hx v hv =>
    hXst (AM.φ x) (mem_actImage_of AM x hx) v hv
  have hfix : ∀ x : ↥(H0 M Z), (x : G) ∈ E1Xpre M Q B t →
      (∀ v ∈ AM.Vsp hH.ctx t, AM.φ x v = v) → (x : G) ∈ Q := fun x hx hfv =>
    (AM.φ_ker x).mp (h3 (AM.φ x) (mem_actImage_of AM x hx) hfv)
  exact ⟨ρ, hXRep, hNρ, b1_line hH AM β hβ hN1 hN2 hdec hXRt hLBRt hNfix hXV hfix g hg f c ρ hΩ hρ⟩

theorem twoFactors_symm' {Gp : Type} [Group Gp] {Q X F₁ F₂ : Subgroup Gp} {q : ℕ}
    (h : TwoFactors Q X F₁ F₂ q) : TwoFactors Q X F₂ F₁ q := by
  unfold TwoFactors at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h2, h1, h4, h3, by rw [sup_comm]; exact h5, by rw [inf_comm]; exact h6,
    fun a ha b hb => ?_, h9, h8⟩
  have e : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by rw [commutatorElement_inv]
  rw [e]
  exact Q.inv_mem (h7 b hb a ha)

theorem b1_of (hLine : NtLineStatement) (_hTI : NtTIStatement) (hSplit : RtSplitStatement)
    (hNK : E1NaturalKStatement) (hKF3' : OmegaLineStatement) : B1Statement := by
  intro G _ _ M Q Z B t hH g hg
  classical
  have hc := hH.ctx
  obtain ⟨AM⟩ := ActionModel.nonempty hc.hyp
  obtain ⟨β, hβ, -, hN1, hN2⟩ := hLine G M Q Z B t hH AM
  obtain ⟨-, -, hNX, hXn, -, hLBs, -, -, -⟩ := hSplit G M Q Z B t hH
  have hNRt : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  have hXRt : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by
    rw [← hNX]
    exact le_sup_right
  have hLBRt : LB M Q B ≤ Rt M (LB M Q B) t :=
    (le_of_eq hLBs).trans (sup_le hNRt (inf_le_right.trans hXRt))
  have hdec : ∀ r ∈ Rt M (LB M Q B) t, ∃ n ∈ Nt M (LB M Q B) t, ∃ x ∈ E1Xpre M Q B t,
      r = n * x := fun r hr => exists_mul_of_sup_eq hNRt hXn hNX hr
  have hQX : Q ≤ E1Xpre M Q B t := by
    unfold E1Xpre
    exact le_sup_right
  have hq4 : 4 ≤ Nat.card AM.K := by
    rw [AM.glob.card]
    exact hc.hyp.q4
  have hKZ : Nat.card AM.K = Nat.card Z := AM.glob.card
  obtain ⟨hPlus, hMinus⟩ := hNK G M Q Z B t hH AM
  refine ⟨fun hE => ?_, fun hE => ?_⟩
  · obtain ⟨b, c', hirr, c, hact⟩ := hMinus hE
    obtain ⟨ρ, -, -, hA⟩ := b1_core hH AM β hβ hN1 hN2 hdec hXRt hLBRt g hg _ c hact
    obtain ⟨hAΩ, hpg, hcard, hΓ⟩ := hA
    exact (hKF3' AM.K hq4).2 b c' hirr _ hAΩ hpg hcard hΓ
  · obtain ⟨c, hact⟩ := hPlus hE
    obtain ⟨ρ, hX, hNρ, hA⟩ := b1_core hH AM β hβ hN1 hN2 hdec hXRt hLBRt g hg _ c hact
    obtain ⟨hAΩ, hpg, hcard, hΓ⟩ := hA
    obtain ⟨F₁, F₂, hsup, hinf, hcomm, hSL₁, hSL₂, hKF⟩ := (hKF3' AM.K hq4).1
    have hT := twoFactors_preIm hQX hXRt ρ hX (Nat.card Z) F₁ F₂ hsup hinf hcomm
      (hKZ ▸ hSL₁) (hKZ ▸ hSL₂)
    have hconjsup : ∀ F : Subgroup (GL (Fin 2 ⊕ Fin 2) AM.K),
        (conjNtR g).map ρ ≤ F → conjSubgroup g (Nt M (LB M Q B) t) ≤
          Nt M (LB M Q B) t ⊔ preIm hXRt ρ F := by
      intro F hF y hy
      have hyR : y ∈ Rt M (LB M Q B) t := hLBRt (hg.2.2.1 hy)
      obtain ⟨n, hn, x, hx, hyx⟩ := hdec y hyR
      have hρy : ρ ⟨y, hyR⟩ ∈ F :=
        hF (Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hy))
      have hxR : x ∈ Rt M (LB M Q B) t := hXRt hx
      have e : ρ ⟨y, hyR⟩ = ρ ⟨n, hNRt hn⟩ * ρ ⟨x, hxR⟩ := by
        rw [← map_mul]
        congr 1
        exact Subtype.ext hyx
      rw [hNρ ⟨n, hNRt hn⟩ hn, one_mul] at e
      have hxpre : x ∈ preIm hXRt ρ F := (mem_preIm hXRt ρ F).2 ⟨hx, by rw [← e]; exact hρy⟩
      rw [hyx]
      exact Subgroup.mul_mem_sup hn hxpre
    rcases hKF _ hAΩ hpg hcard hΓ with hF₁ | hF₂
    · exact ⟨preIm hXRt ρ F₁, preIm hXRt ρ F₂, hT, hconjsup F₁ hF₁⟩
    · exact ⟨preIm hXRt ρ F₂, preIm hXRt ρ F₁, twoFactors_symm' hT, hconjsup F₂ hF₂⟩

end E1Rep

end CFSG.RankThree.GF2n.Smith81.Smith23E1
