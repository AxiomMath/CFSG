module

public import CFSG.RankThree.GF2n.Smith81.Orth28Sim

public section

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

namespace OrthEps

section Sqrt

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

theorem sq_injective {a b : K} (h : a ^ 2 = b ^ 2) : a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · rwa [CharTwo.neg_eq] at h

theorem exists_linear_sq (β : V → K) (hadd : ∀ x y, β (x + y) = β x + β y)
    (hsmul : ∀ (c : K) x, β (c • x) = c ^ 2 * β x) : ∃ ℓ : V →ₗ[K] K, ∀ x, ℓ x ^ 2 = β x := by
  have hsq : ∀ a : K, ∃ r : K, r ^ 2 = a := fun a => by
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
    exact ⟨r, by rw [hr, pow_two]⟩
  choose s hs using fun x => hsq (β x)
  refine ⟨{ toFun := s, map_add' := fun x y => ?_, map_smul' := fun c x => ?_ }, hs⟩
  · apply sq_injective
    rw [CharTwo.add_sq, hs, hs, hs, hadd]
  · apply sq_injective
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [mul_pow, hs, hs, hsmul]

theorem finrank_le_finrank_ker_add_one [FiniteDimensional K V] (ℓ : V →ₗ[K] K) :
    Module.finrank K V ≤ Module.finrank K (LinearMap.ker ℓ) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ℓ
  have hr : Module.finrank K (LinearMap.range ℓ) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range ℓ)
  omega

end Sqrt

section Involution

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : QuadraticForm K V} {o : V ≃ₗ[K] V}

theorem exists_singular_mem_commSpace (ho : o ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hoo : o * o = 1) (hrk : 2 ≤ Module.finrank K (OrthogonalInvolutions.commSpace o)) :
    ∃ p ∈ OrthogonalInvolutions.commSpace o, p ≠ 0 ∧ q p = 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_linear_sq (K := K) (V := OrthogonalInvolutions.commSpace o)
    (fun p => q (p : V))
    (fun x y => by
      have := QuadraticMap.map_add q (x : V) (y : V)
      rw [OrthogonalInvolutions.polar_commSpace_eq_zero ho hoo x.2 y.2, add_zero] at this
      exact this)
    (fun c x => by rw [Submodule.coe_smul, QuadraticMap.map_smul, smul_eq_mul, pow_two])
  have h1 := finrank_le_finrank_ker_add_one ℓ
  have h2 : 0 < Module.finrank K (LinearMap.ker ℓ) := by omega
  obtain ⟨p, hpk, hp0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.mp h2)
  refine ⟨p, p.2, fun h => hp0 (Subtype.ext h), ?_⟩
  have := hℓ p
  rw [LinearMap.mem_ker.mp hpk] at this
  simpa using this.symm

end Involution

section Key

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : QuadraticForm K V}

theorem plane_singular {s t : V} (hs : q s = 0) (ht : q t = 0) (hst : polar q s t = 0)
    {z : V} (hz : z ∈ Submodule.span K {s, t}) : q z = 0 := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [QuadraticMap.map_add q, QuadraticMap.map_smul, QuadraticMap.map_smul, hs, ht,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hst]
  simp

theorem plane_orth {s t : V} (hs : q s = 0) (ht : q t = 0) (hst : polar q s t = 0)
    {z w : V} (hz : z ∈ Submodule.span K {s, t}) (hw : w ∈ Submodule.span K {s, t}) :
    polar q z w = 0 := by
  have hss : polar q s s = 0 := by rw [QuadraticMap.polar_self, hs]; simp
  have htt : polar q t t = 0 := by rw [QuadraticMap.polar_self, ht]; simp
  have hts : polar q t s = 0 := by rw [QuadraticMap.polar_comm]; exact hst
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hz
  obtain ⟨c', d', rfl⟩ := Submodule.mem_span_pair.mp hw
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hss, htt, hst, hts]
  simp

theorem exists_singular_not_orth (hq : q.polarBilin.Nondegenerate) (H : Submodule K V)
    (hH : Module.finrank K V ≤ Module.finrank K H + 1)
    {s t : V} (hs : q s = 0) (ht : q t = 0) (hst : polar q s t = 0)
    (hind : ∀ a b : K, a • s + b • t = 0 → a = 0 ∧ b = 0) :
    ∃ z ∈ H, q z = 0 ∧ ∃ y ∈ H, polar q z y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set T : Submodule K V := Submodule.span K {s, t} with hT
  have hTfin : Module.finrank K T = 2 := by
    have hli : LinearIndependent K ![s, t] := by
      rw [LinearIndependent.pair_iff]
      exact hind
    have h1 := finrank_span_eq_card hli
    have hr : Set.range ![s, t] = ({s, t} : Set V) := by
      ext x
      simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [hr] at h1
    simpa using h1
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq H T
  have hsup : Module.finrank K ↥(H ⊔ T) ≤ Module.finrank K V := Submodule.finrank_le _
  have hge : 1 ≤ Module.finrank K ↥(H ⊓ T) := by omega
  have hle : H ⊓ T ≤ LinearMap.BilinForm.orthogonal q.polarBilin H := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show polar q y z = 0
    rw [QuadraticMap.polar_comm]
    exact hcon z hz.1 (plane_singular hs ht hst hz.2) y hy
  have horth := LinearMap.BilinForm.finrank_orthogonal hq H
  have hle1 : Module.finrank K ↥(H ⊓ T) ≤ 1 := by
    have := Submodule.finrank_mono hle
    omega
  have hne : H ⊓ T ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hge
    omega
  obtain ⟨z₀, hz₀, hz₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨F, hF⟩ : ∃ F : Submodule K V, F = LinearMap.ker (q.polarBilin z₀) := ⟨_, rfl⟩
  have hHF : H ≤ F := fun y hy => by
    rw [hF, LinearMap.mem_ker]
    exact hcon z₀ hz₀.1 (plane_singular hs ht hst hz₀.2) y hy
  have hTF : T ≤ F := fun w hw => by
    rw [hF, LinearMap.mem_ker]
    exact plane_orth hs ht hst hz₀.2 hw
  have hsupF : H ⊔ T ≤ F := sup_le hHF hTF
  have hFdim : Module.finrank K F + 1 ≤ Module.finrank K V := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (q.polarBilin z₀)
    rw [← hF] at h1
    have h2 : 1 ≤ Module.finrank K (LinearMap.range (q.polarBilin z₀)) := by
      rw [Submodule.one_le_finrank_iff]
      intro hbot
      apply hz₀0
      refine hq.1 z₀ fun y => ?_
      have : q.polarBilin z₀ y ∈ LinearMap.range (q.polarBilin z₀) := ⟨y, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      exact this
    have h3 : Module.finrank K K = 1 := Module.finrank_self K
    have h4 : Module.finrank K (LinearMap.range (q.polarBilin z₀)) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range (q.polarBilin z₀))
    omega
  have := Submodule.finrank_mono hsupF
  omega

end Key

section S2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : QuadraticForm K V} {o : V ≃ₗ[K] V}

theorem map_sub_add_apply (ho : o ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hoo : o * o = 1)
    (x y : V) : q (o (x + y) - (x + y)) = q (o x - x) + q (o y - y) := by
  have e : o (x + y) - (x + y) = (o x - x) + (o y - y) := by rw [map_add]; abel
  rw [e, QuadraticMap.map_add q,
    OrthogonalInvolutions.polar_commSpace_eq_zero ho hoo
      (OrthogonalInvolutions.sub_mem_commSpace o x) (OrthogonalInvolutions.sub_mem_commSpace o y),
    add_zero]

theorem map_sub_smul_apply (c : K) (x : V) :
    q (o (c • x) - c • x) = c ^ 2 * q (o x - x) := by
  have e : o (c • x) - c • x = c • (o x - x) := by rw [map_smul, smul_sub]
  rw [e, QuadraticMap.map_smul, smul_eq_mul, pow_two]

theorem exists_singular_not_fixed (hq : q.polarBilin.Nondegenerate)
    (ho : o ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hoo : o * o = 1)
    (hrk : 2 ≤ Module.finrank K (OrthogonalInvolutions.commSpace o))
    {s t : V} (hs : q s = 0) (ht : q t = 0) (hst : polar q s t = 0)
    (hind : ∀ a b : K, a • s + b • t = 0 → a = 0 ∧ b = 0) :
    ∃ v : V, q v = 0 ∧ o v ≠ v ∧ q (o v - v) = 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_linear_sq (K := K) (V := V) (fun v => q (o v - v))
    (map_sub_add_apply ho hoo) map_sub_smul_apply
  have hmem : ∀ x : V, x ∈ LinearMap.ker ℓ ↔ q (o x - x) = 0 := fun x => by
    rw [LinearMap.mem_ker, ← hℓ x]
    exact ⟨fun h => by rw [h]; ring, fun h => (pow_eq_zero_iff two_ne_zero).mp h⟩
  obtain ⟨p, hpP, hp0, hqp⟩ := exists_singular_mem_commSpace ho hoo hrk
  obtain ⟨h, hh⟩ := OrthogonalInvolutions.mem_commSpace.mp hpP
  have hhH : h ∈ LinearMap.ker ℓ := (hmem h).mpr (by rw [hh]; exact hqp)
  have hhC : o h ≠ h := fun e => hp0 (by rw [← hh, e, sub_self])
  obtain ⟨z, hzH, hqz, y, hyH, hzy⟩ := exists_singular_not_orth hq (LinearMap.ker ℓ)
    (finrank_le_finrank_ker_add_one ℓ) hs ht hst hind
  by_cases hzC : o z = z
  ·
    obtain ⟨y₂, hy₂H, hzy₂, hy₂C⟩ : ∃ y₂ ∈ LinearMap.ker ℓ, polar q z y₂ ≠ 0 ∧ o y₂ ≠ y₂ := by
      by_cases hy : o y = y
      · by_cases hzh : polar q z h = 0
        · refine ⟨y + h, Submodule.add_mem _ hyH hhH, ?_, ?_⟩
          · rw [QuadraticMap.polar_add_right, hzh, add_zero]; exact hzy
          · intro e
            rw [map_add, hy] at e
            exact hhC (add_left_cancel e)
        · exact ⟨h, hhH, hzh, hhC⟩
      · exact ⟨y, hyH, hzy, hy⟩
    set a := polar q z y₂ with ha
    have ha0 : a ≠ 0 := hzy₂
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : V, y₁ = a⁻¹ • y₂ := ⟨_, rfl⟩
    have hy₁H : y₁ ∈ LinearMap.ker ℓ := hy₁ ▸ Submodule.smul_mem _ _ hy₂H
    have hzy₁ : polar q z y₁ = 1 := by
      rw [hy₁, QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ ha0]
    have hy₁C : o y₁ ≠ y₁ := by
      intro e
      apply hy₂C
      have : a • o y₁ = a • y₁ := by rw [e]
      rwa [hy₁, map_smul, smul_smul, smul_smul, mul_inv_cancel₀ ha0, one_smul, one_smul] at this
    refine ⟨y₁ + q y₁ • z, ?_, ?_, ?_⟩
    · rw [QuadraticMap.map_add q, QuadraticMap.map_smul, hqz, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_comm, hzy₁]
      simp only [smul_eq_mul, mul_zero, mul_one]
      rw [add_zero]
      exact CharTwo.add_self_eq_zero _
    · intro e
      rw [map_add, map_smul, hzC] at e
      exact hy₁C (add_right_cancel e)
    · exact (hmem _).mp (Submodule.add_mem _ hy₁H (Submodule.smul_mem _ _ hzH))
  · exact ⟨z, hqz, hzC, (hmem z).mp hzH⟩

theorem exists_singular_fixed (hq : q.polarBilin.Nondegenerate)
    (ho : o ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hoo : o * o = 1)
    (heven : Even (Module.finrank K (OrthogonalInvolutions.commSpace o)))
    (hsing : ∃ u : V, u ≠ 0 ∧ q u = 0) : ∃ v : V, v ≠ 0 ∧ q v = 0 ∧ o v = v := by
  by_cases h1 : o = 1
  · obtain ⟨u, hu0, hu⟩ := hsing
    exact ⟨u, hu0, hu, by rw [h1]; rfl⟩
  · have h1' := OrthogonalInvolutions.one_le_finrank_commSpace h1
    have h2 : 2 ≤ Module.finrank K (OrthogonalInvolutions.commSpace o) := by
      obtain ⟨r, hr⟩ := heven
      omega
    obtain ⟨p, hpP, hp0, hqp⟩ := exists_singular_mem_commSpace ho hoo h2
    refine ⟨p, hp0, hqp, ?_⟩
    exact OrthogonalInvolutions.mem_fixSpace.mp
      (OrthogonalInvolutions.commSpace_le_fixSpace hoo hpP)

end S2

end OrthEps

section Witness

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem OrthEps.phi_pi_commutator (C : OrthCtx M Q Z B) {x q' : G} (hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hq' : q' ∈ Q) {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) :
    C.φ (C.M₀.π ⁅q', x⁆) = C.φ (C.M₀.π q') - orthTensor g o (C.φ (C.M₀.π q')) := by
  have hw : x * q' * x⁻¹ ∈ Q := hxQ q' hq'
  have e : ⁅q', x⁆ = q' * (x * q' * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e, C.M₀.π_mul q' hq' _ (Q.inv_mem hw), Tim79.QuadModel.pi_inv C.M₀ hw, ← sub_eq_add_neg,
    map_sub, hact q' hq']

theorem OrthEps.pairTypeA_ne_zero {K ι : Type} [Field K] {q : QuadraticForm K (ι → K)}
    {p : (ι → K) × (ι → K)} (hp : PairTypeA q p) : p ≠ 0 := by
  obtain ⟨c₁, c₂, u, hc, hu, -, rfl⟩ := hp
  intro h0
  rw [Prod.mk_eq_zero] at h0
  rcases hc with hc | hc
  · exact hu ((smul_eq_zero.mp h0.1).resolve_left hc)
  · exact hu ((smul_eq_zero.mp h0.2).resolve_left hc)

theorem exists_orthValid_of_tensors (h52 : Smith52ActStatement) (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) {p : (C.ι → C.K) × (C.ι → C.K)}
    (hp : PairTypeA C.qU p) {c₁ c₂ : C.K} {u : C.ι → C.K} (hc12 : c₁ ≠ 0 ∨ c₂ ≠ 0) (hu0 : u ≠ 0)
    (hqu : C.qU u = 0) (hcomm : p - orthTensor g o p = (c₁ • u, c₂ • u))
    (hmem : ∃ (w : C.ι → C.K) (s t : C.K), QuadraticMap.polar C.qU w u = 0 ∧
      p = (c₁ • w + s • u, c₂ • w + t • u)) :
    ∃ q', OrthValid M Q Z x q' := by
  have H := hc.ctx.hyp
  obtain ⟨g₀, hg₀⟩ := hs.conj
  have hz₀ : g₀⁻¹ * x * g₀ ∈ Z := mem_conjSubgroup.mp (hg₀ ▸ hs.mem)
  have hz₀1 : g₀⁻¹ * x * g₀ ≠ 1 := by
    intro h
    apply hs.ne_one
    have : x = g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ := by group
    rw [this, h]; group
  have hz₀x : IsConj (g₀⁻¹ * x * g₀) x := isConj_iff.mpr ⟨g₀, by group⟩
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  obtain ⟨q', hq'Q, hq'p⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) p
  have hq'Z : q' ∉ Z := fun h => OrthEps.pairTypeA_ne_zero hp (by
    rw [← hq'p, (C.M₀.π_ker q' hq'Q).mpr h, map_zero])
  have hcφ : C.φ (C.M₀.π ⁅q', x⁆) = (c₁ • u, c₂ • u) := by
    rw [OrthEps.phi_pi_commutator C hxQ hq'Q hact, hq'p, hcomm]
  have hcQ : ⁅q', x⁆ ∈ Q := comm_mem_Q H hs.memM hq'Q
  have hcZ : ⁅q', x⁆ ∉ Z := fun h => by
    have h0 := (C.M₀.π_ker _ hcQ).mpr h
    rw [h0, map_zero] at hcφ
    have := Prod.mk_eq_zero.mp hcφ.symm
    rcases hc12 with hc | hc
    · exact hu0 ((smul_eq_zero.mp this.1).resolve_left hc)
    · exact hu0 ((smul_eq_zero.mp this.2).resolve_left hc)
  have hc1 : ⁅q', x⁆ ≠ 1 := fun h => hcZ (h ▸ Z.one_mem)
  refine ⟨q', hq'Q, ?_, ?_, ?_⟩
  · exact hz₀x.symm.trans ((C.hF.root _ hz₀ hz₀1 q' hq'Q hq'Z).mpr (hq'p ▸ hp))
  · exact hz₀x.symm.trans ((C.hF.root _ hz₀ hz₀1 _ hcQ hcZ).mpr ⟨c₁, c₂, u, hc12, hu0, hqu, hcφ⟩)
  · intro C₀ hC₀ hcC₀
    have hC₀Q : C₀ ≤ Q := root_le_Q H hC₀ hcC₀ hcQ hc1
    have hC₀Z : C₀ ≠ Z := by
      rintro rfl
      exact hcZ hcC₀
    obtain ⟨-, hex⟩ := h52 G M Q Z B hc C.K C.γ C.M₀ C.hD C.ι C.qU C.φ C.hF C.hA C₀ hC₀ hC₀Q hC₀Z
      c₁ c₂ u hc12 hu0 hqu ⟨⁅q', x⁆, hcC₀, hc1, hcφ⟩
    obtain ⟨w, s, t, hw, hpe⟩ := hmem
    obtain ⟨v', hv'mem, hv'φ⟩ := hex w s t hw
    have hv'Q : v' ∈ Q := (Subgroup.mem_inf.mp hv'mem).1
    have hπ : C.M₀.π v' = C.M₀.π q' := C.φ.injective (hv'φ.trans (hpe.symm.trans hq'p.symm))
    have hqv : q' * v'⁻¹ ∈ Z := by
      refine (C.M₀.π_ker _ (Q.mul_mem hq'Q (Q.inv_mem hv'Q))).mp ?_
      rw [C.M₀.π_mul _ hq'Q _ (Q.inv_mem hv'Q), Tim79.QuadModel.pi_inv C.M₀ hv'Q, hπ,
        add_neg_cancel]
    have hZle : Z ≤ QB C₀ :=
      (IsZConjugate.le_QB_iff H hC₀ (IsZConjugate.self Z)).mpr (by
        rw [StrothHyp.QB_Z H]; exact hC₀Q)
    have : q' = (q' * v'⁻¹) * v' := by group
    rw [this]
    exact (QB C₀).mul_mem (hZle hqv) (Subgroup.mem_inf.mp hv'mem).2

theorem OrthEps.exists_mulVec_ne_of_ne_one {K : Type} [Field K] {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ≠ 1) : ∃ e : Fin 2 → K, g *ᵥ e ≠ e := by
  by_contra h
  push Not at h
  apply hg
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
      Pi.single_apply] using this

theorem exists_orthValid_of_ne_one (h52 : Smith52ActStatement) (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g ⇑o) (hg : g ≠ 1) {v : C.ι → C.K} (hv0 : v ≠ 0)
    (hqv : C.qU v = 0) (hov : o v = v) : ∃ q', OrthValid M Q Z x q' := by
  obtain ⟨e, he⟩ := OrthEps.exists_mulVec_ne_of_ne_one hg
  have hotv : ∀ c : C.K, o (c • v) = c • v := fun c => by rw [map_smul, hov]
  have he0 : e 0 ≠ 0 ∨ e 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    have : e = 0 := funext fun i => by fin_cases i <;> simp [h.1, h.2]
    rw [this, Matrix.mulVec_zero]
  have hten : orthTensor g (⇑o) ((e 0 • v, e 1 • v) : (C.ι → C.K) × (C.ι → C.K)) =
      ((g *ᵥ e) 0 • v, (g *ᵥ e) 1 • v) := by
    simp only [orthTensor, hotv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    refine Prod.ext ?_ ?_ <;> simp only <;> module
  refine exists_orthValid_of_tensors h52 hc C hs hact (p := (e 0 • v, e 1 • v))
    ⟨e 0, e 1, v, he0, hv0, hqv, rfl⟩ (c₁ := e 0 - (g *ᵥ e) 0) (c₂ := e 1 - (g *ᵥ e) 1)
    (u := v) ?_ hv0 hqv ?_ ?_
  · by_contra h
    push Not at h
    apply he
    funext i
    fin_cases i
    · exact (sub_eq_zero.mp h.1).symm
    · exact (sub_eq_zero.mp h.2).symm
  · rw [hten]
    refine Prod.ext ?_ ?_ <;> simp [sub_smul]
  · refine ⟨v, (g *ᵥ e) 0, (g *ᵥ e) 1, ?_, ?_⟩
    · rw [QuadraticMap.polar_self, hqv]
      simp
    · refine Prod.ext ?_ ?_ <;> simp only <;> module

theorem exists_orthValid_of_one (h52 : Smith52ActStatement) (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o)
    (hiso : ∀ v, C.qU (o v) = C.qU v) {v : C.ι → C.K} (hqv : C.qU v = 0) (hov : o v ≠ v)
    (hb : C.qU (o v - v) = 0) : ∃ q', OrthValid M Q Z x q' := by
  have hv0 : v ≠ 0 := fun h => hov (by rw [h, map_zero])
  have hO := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hpol : QuadraticMap.polar C.qU v (o v) = 0 := by
    rw [QuadraticMap.polar_comm, ← OrthogonalInvolutions.map_sub_eq_polar hO v]
    exact hb
  have hu0 : v - o v ≠ 0 := sub_ne_zero.mpr (Ne.symm hov)
  have hqu : C.qU (v - o v) = 0 := by
    rw [← neg_sub (o v) v, QuadraticMap.map_neg]
    exact hb
  refine exists_orthValid_of_tensors h52 hc C hs hact (p := (v, 0))
    ⟨1, 0, v, Or.inl one_ne_zero, hv0, hqv, by simp⟩ (c₁ := 1) (c₂ := 0) (u := v - o v)
    (Or.inl one_ne_zero) hu0 hqu ?_ ?_
  · refine Prod.ext ?_ ?_ <;> simp [orthTensor, Matrix.one_apply]
  · refine ⟨v, 0, 0, ?_, ?_⟩
    · rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_self, hqv, hpol]
      simp
    · refine Prod.ext ?_ ?_ <;> simp

end Witness

@[expose] def OrthEpsFourMinusStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ C : OrthCtx M Q Z B, NoTotallySingularPlane C.qU →
      ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
        ∀ o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K), ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o →
          (∀ v, C.qU (o v) = C.qU v) → (∀ v, o (o v) = v) →
          Even (Module.finrank C.K (OrthogonalInvolutions.commSpace o)) →
            ∃ v ∈ Jx Q X x, v ≠ 1 ∧ IsConj x v

theorem orthEps_of (h24 : Smith24ActStatement)
    (h52 : Smith52ActStatement) (hT : OrthTacitStatement) (h4 : OrthEpsFourMinusStatement) :
    OrthEpsStatement := by
  intro G _ _ M Q Z B hc X x hs hxL
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  have hno := noA2_of_tacit hT hc
  obtain ⟨g, o, hact, hgg, hoo, hiso, heven⟩ := lgen_involution_normalized hc hno C hxL hs.x_sq
  have hO := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hoo' : o * o = 1 := LinearEquiv.ext fun v => hoo v
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  obtain ⟨u, hu0, hqu⟩ := exists_singular_of_ctx hc.ctx C
  by_cases hg1 : g = 1
  · subst hg1
    by_cases hTSP : NoTotallySingularPlane C.qU
    · exact Or.inr (h4 G M Q Z B hc C hTSP X x hs hxL o hact hiso hoo heven)
    · refine Or.inl ?_
      unfold NoTotallySingularPlane at hTSP
      push Not at hTSP
      obtain ⟨s, t, hs0, ht0, hst, hind⟩ := hTSP
      have ho1 : o ≠ 1 := by
        intro h1
        refine hs.notQ (mem_Q_of_pi_conj_eq (M₀ := C.M₀) hc.ctx.hyp hs.memM fun y hy => ?_)
        apply C.φ.injective
        rw [hact y hy, h1]
        simp [orthTensor, Matrix.one_apply]
      have hrk : 2 ≤ Module.finrank C.K (OrthogonalInvolutions.commSpace o) := by
        have h1 := OrthogonalInvolutions.one_le_finrank_commSpace ho1
        obtain ⟨r, hr⟩ := heven
        omega
      obtain ⟨v, hqv, hov, hb⟩ := OrthEps.exists_singular_not_fixed hnd hO hoo' hrk hs0 ht0 hst hind
      exact exists_orthValid_of_one h52 hc C hs hact hiso hqv hov hb
  · refine Or.inl ?_
    obtain ⟨v, hv0, hqv, hov⟩ := OrthEps.exists_singular_fixed hnd hO hoo' heven ⟨u, hu0, hqu⟩
    exact exists_orthValid_of_ne_one h52 hc C hs hact hg1 hv0 hqv hov

end CFSG.RankThree.GF2n.Smith81
