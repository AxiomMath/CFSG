module

public import CFSG.RankThree.PartOne.CTP.LinearEdge

public section

namespace CFSG.RankThree.PartOne.CTP

open scoped commutatorElement MatrixGroups

section Transfer

variable {S P G : Type*} [Group S] [Group P] [Group G] (θ : S →* G)

theorem mem_center_range_iff_gen [Group.IsPerfect S] (hker : θ.ker ≤ Subgroup.center S) (g : S) :
    θ.rangeRestrict g ∈ Subgroup.center θ.range ↔ g ∈ Subgroup.center S := by
  constructor
  · intro hg
    refine mem_center_of_commutator_mem_center fun x => hker ?_
    rw [MonoidHom.mem_ker]
    have h1 := Subgroup.mem_center_iff.mp hg (θ.rangeRestrict x)
    have h2 : θ g * θ x = θ x * θ g := by
      simpa using congrArg Subtype.val h1.symm
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  · intro hg
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, x, rfl⟩
    refine Subtype.ext ?_
    simp only [MonoidHom.coe_rangeRestrict, Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hg x)]

@[expose] noncomputable def toCenterQuotientGen : S →* θ.range ⧸ Subgroup.center θ.range :=
  (QuotientGroup.mk' (Subgroup.center θ.range)).comp θ.rangeRestrict

theorem toCenterQuotientGen_surjective : Function.Surjective (toCenterQuotientGen θ) :=
  (QuotientGroup.mk'_surjective _).comp (MonoidHom.rangeRestrict_surjective θ)

theorem toCenterQuotientGen_ker [Group.IsPerfect S] (hker : θ.ker ≤ Subgroup.center S) :
    (toCenterQuotientGen θ).ker = Subgroup.center S := by
  ext g
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk' (Subgroup.center θ.range)) (θ.rangeRestrict g) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_range_iff_gen θ hker]

@[expose] noncomputable def projEquivGen [Group.IsPerfect S] (hker : θ.ker ≤ Subgroup.center S)
    {π : S →* P} (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) :
    P ≃* θ.range ⧸ Subgroup.center θ.range :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hπk.trans (toCenterQuotientGen_ker θ hker).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (toCenterQuotientGen_surjective θ)))

theorem projEquivGen_apply [Group.IsPerfect S] (hker : θ.ker ≤ Subgroup.center S)
    {π : S →* P} (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) (g : S) :
    projEquivGen θ hker hπ hπk (π g) = QuotientGroup.mk (θ.rangeRestrict g) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) = QuotientGroup.mk g := by
    rw [MulEquiv.symm_apply_eq]; rfl
  unfold projEquivGen
  rw [MulEquiv.trans_apply, h1, MulEquiv.trans_apply]
  rfl

theorem exists_aut_of_conj_gen [Group.IsPerfect S] (hker : θ.ker ≤ Subgroup.center S)
    {π : S →* P} (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) {e : G}
    (he : e ∈ Subgroup.normalizer (θ.range : Set G)) :
    ∃ α : MulAut P, ∀ g g' : S, θ g' = e * θ g * e⁻¹ → α (π g) = π g' := by
  let c : MulAut ↥θ.range := θ.range.normalizerMonoidHom ⟨e, he⟩
  refine ⟨(projEquivGen θ hker hπ hπk).trans
    ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient c).trans
      (projEquivGen θ hker hπ hπk).symm), fun g g' hg => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq,
    projEquivGen_apply θ hker hπ hπk g, projEquivGen_apply θ hker hπ hπk g']
  have h1 : c (θ.rangeRestrict g) = θ.rangeRestrict g' := by
    refine Subtype.ext ?_
    simp only [MonoidHom.coe_rangeRestrict]
    rw [hg]
    rfl
  have := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk c
    (θ.rangeRestrict g)
  simp only [h1] at this
  exact this

end Transfer

section Edge

variable {S P G : Type*} [Group S] [Group P] [Group G] (θ : S →* G) {π : S →* P}

theorem aut_pow_eq_one_gen (hπk : π.ker = Subgroup.center S)
    (hπ : Function.Surjective π) (hker : θ.ker ≤ Subgroup.center S) {e : G}
    (he : e ∈ Subgroup.normalizer (θ.range : Set G))
    {α : MulAut P} (hα : ∀ g g' : S, θ g' = e * θ g * e⁻¹ → α (π g) = π g') {p : ℕ}
    (hep : e ^ p = 1) : α ^ p = 1 := by
  have hex : ∀ x ∈ θ.range, e * x * e⁻¹ ∈ θ.range := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp he x).mp hx
  have key : ∀ k : ℕ, ∀ g : S, ∃ g' : S, θ g' = e ^ k * θ g * (e ^ k)⁻¹ ∧
      (α ^ k) (π g) = π g' := by
    intro k
    induction k with
    | zero => intro g; exact ⟨g, by simp, by simp⟩
    | succ k ih =>
      intro g
      obtain ⟨g', hg', hαg'⟩ := ih g
      obtain ⟨g'', hg''⟩ := hex (θ g') ⟨g', rfl⟩
      refine ⟨g'', ?_, ?_⟩
      · rw [hg'', hg']
        group
      · rw [pow_succ', MulAut.mul_apply, hαg']
        exact hα g' g'' hg''
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := hπ x
  obtain ⟨g', hg', hαg'⟩ := key p g
  rw [hαg']
  have hθ : θ g' = θ g := by rw [hg', hep]; simp
  have h1 : g'⁻¹ * g ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ]; simp
  have h2 : π g' = π g := by
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, hπk]; exact hker h1
  rw [h2]
  rfl

theorem edge_aut_data_gen {C D : Subgroup G} {KC KD : Type} [Field KC] [Field KD] [CharP KD 2]
    (hπk : π.ker = Subgroup.center S)
    (ρC : SL(2, KC) ≃* ↥C) (ρD : SL(2, KD) ≃* ↥D)
    (φC : SL(2, KC) →* S) (φD : SL(2, KD) →* S)
    (hφC : ∀ a, θ (φC a) = (ρC a : G)) (hφD : ∀ b, θ (φD b) = (ρD b : G))
    {e : G} {α : MulAut P}
    (hα : ∀ g g' : S, θ g' = e * θ g * e⁻¹ → α (π g) = π g')
    (hcen : ∀ x ∈ C, e * x = x * e) (hnorm : ∀ y ∈ D, e * y * e⁻¹ ∈ D)
    (hmov : ∃ y ∈ D, e * y ≠ y * e) :
    (∀ a, α (π (φC a)) = π (φC a)) ∧
      (∀ b, ∃ b', α (π (φD b)) = π (φD b')) ∧
      ∃ b, α (π (φD b)) ≠ π (φD b) := by
  have hfix : ∀ a, α (π (φC a)) = π (φC a) := by
    intro a
    refine hα _ _ ?_
    rw [hφC a, eq_comm, mul_inv_eq_iff_eq_mul]
    exact hcen _ (ρC a).2
  have hstab : ∀ b, ∃ b', θ (φD b') = e * θ (φD b) * e⁻¹ := by
    intro b
    set y : G := e * θ (φD b) * e⁻¹ with hy
    have hyD : y ∈ D := by rw [hy, hφD b]; exact hnorm _ (ρD b).2
    refine ⟨ρD.symm ⟨y, hyD⟩, ?_⟩
    rw [hφD, MulEquiv.apply_symm_apply]
  refine ⟨hfix, fun b => ?_, ?_⟩
  · obtain ⟨b', hb'⟩ := hstab b
    exact ⟨b', hα _ _ hb'⟩
  · obtain ⟨y, hy, hyne⟩ := hmov
    let b0 := ρD.symm ⟨y, hy⟩
    obtain ⟨b', hb'⟩ := hstab b0
    have hθb0 : θ (φD b0) = y := by rw [hφD, MulEquiv.apply_symm_apply]
    refine ⟨b0, fun h => ?_⟩
    rw [hα _ _ hb'] at h
    have hz : (φD b0)⁻¹ * φD b' ∈ Subgroup.center S := by
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have hzD : b0⁻¹ * b' ∈ Subgroup.center SL(2, KD) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := Subgroup.mem_center_iff.mp hz (φD x)
      have h2 : θ ((φD b0)⁻¹ * φD b') * θ (φD x) = θ (φD x) * θ ((φD b0)⁻¹ * φD b') := by
        rw [← map_mul, ← map_mul, h1]
      simp only [map_mul, map_inv, hφD] at h2
      apply ρD.injective
      apply Subtype.ext
      simpa [map_mul, map_inv] using h2.symm
    rw [center_sl2_eq_bot (K := KD), Subgroup.mem_bot, inv_mul_eq_one] at hzD
    subst hzD
    apply hyne
    have := hb'
    rw [hθb0] at this
    exact mul_inv_eq_iff_eq_mul.mp this.symm

theorem edge_half_gen [Group.IsPerfect S] (hπk : π.ker = Subgroup.center S)
    (hπ : Function.Surjective π) (hker : θ.ker ≤ Subgroup.center S) {p : ℕ} (hp : p.Prime)
    {E A B : Subgroup G} [CFSG.IsElementaryAbelian p E]
    (hE : EdgeTorus p E A B) (hAB : A ⊔ B = θ.range) {KA KB : Type} [Field KA] [Field KB]
    [CharP KB 2] (ρA : SL(2, KA) ≃* ↥A) (ρB : SL(2, KB) ≃* ↥B)
    (φA : SL(2, KA) →* S) (φB : SL(2, KB) →* S)
    (hφA : ∀ a, θ (φA a) = (ρA a : G)) (hφB : ∀ b, θ (φB b) = (ρB b : G)) :
    ∃ α : MulAut P, α ^ p = 1 ∧
      (∀ a, α (π (φA a)) = π (φA a)) ∧
      (∀ b, ∃ b', α (π (φB b)) = π (φB b')) ∧
      ∃ b, α (π (φB b)) ≠ π (φB b) := by
  obtain ⟨e, heE, hcen, hmov, hnorm, hord⟩ := hE.exists_centralizing hp
  have heA : e ∈ Subgroup.normalizer (A : Set G) := le_normalizer_of_dec hE.decA heE
  have heB : e ∈ Subgroup.normalizer (B : Set G) := le_normalizer_of_dec hE.decB heE
  have hX : e ∈ Subgroup.normalizer (θ.range : Set G) := by
    rw [← hAB]; exact mem_normalizer_sup heA heB
  obtain ⟨α, hα⟩ := exists_aut_of_conj_gen θ hker hπ hπk hX
  have hep : e ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one e
  obtain ⟨h1, h2, h3⟩ := edge_aut_data_gen θ hπk ρA ρB φA φB hφA hφB hα hcen hnorm hmov
  exact ⟨α, aut_pow_eq_one_gen θ hπk hπ hker hX hα hep, h1, h2, h3⟩

theorem exists_sl2_lift_gen [Finite S] (hker : θ.ker ≤ Subgroup.center S)
    (hodd : ¬ 2 ∣ Nat.card (Subgroup.center S)) {K : Type} [Field K] [Finite K] [CharP K 2]
    {C : Subgroup G} (hC : C ≤ θ.range) (ρ : SL(2, K) →* ↥C) :
    ∃ φ : SL(2, K) →* S, ∀ a, θ (φ a) = (ρ a : G) := by
  have hπ : Function.Surjective θ.rangeRestrict := MonoidHom.rangeRestrict_surjective θ
  have hcen : θ.rangeRestrict.ker ≤ Subgroup.center S := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hodd' : ¬ 2 ∣ Nat.card θ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro h2
    exact hodd (h2.trans (Subgroup.card_dvd_of_le hker))
  obtain ⟨φ, hφ, -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := 2) hπ hcen hodd'
    ((Subgroup.inclusion hC).comp ρ)
  refine ⟨φ, fun a => ?_⟩
  have := DFunLike.congr_fun hφ a
  simpa using congrArg Subtype.val this

theorem map_range_eq_of_central {K₁ : Type*} [Group K₁] [Finite K₁] [Group.IsPerfect K₁]
    (hπk : π.ker ≤ Subgroup.center S) (φ : K₁ →* S)
    (χ : S ≃* S) (h : ∀ b, ∃ b', π (χ (φ b)) = π (φ b')) :
    φ.range.map χ.toMonoidHom = φ.range := by
  let ψ : K₁ →* S := χ.toMonoidHom.comp φ
  have hchi : ∀ x, ∃ x' z, z ∈ Subgroup.center S ∧ ψ x = φ x' * z := by
    intro x
    obtain ⟨x', hx'⟩ := h x
    refine ⟨x', (φ x')⁻¹ * ψ x, hπk ?_, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : π (ψ x) = π (φ x') := hx'
    rw [this, inv_mul_cancel]
  have hD : (φ.range).comap ψ = ⊤ := by
    rw [eq_top_iff]
    have hc : commutator K₁ = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [← hc]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    obtain ⟨x', zx, hzx, hx⟩ := hchi x
    obtain ⟨y', zy, hzy, hy⟩ := hchi y
    rw [Subgroup.mem_comap, map_commutatorElement, hx, hy]
    have h1 : ⁅φ x' * zx, φ y' * zy⁆ = ⁅φ x', φ y'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have hx1 := Subgroup.mem_center_iff.mp hzx
      have hy1 := Subgroup.mem_center_iff.mp hzy
      calc φ x' * zx * (φ y' * zy) * (φ x' * zx)⁻¹ * (φ y' * zy)⁻¹
          = φ x' * (zx * (φ y' * zy)) * zx⁻¹ * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ := by group
        _ = φ x' * ((φ y' * zy) * zx) * zx⁻¹ * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ := by rw [hx1]
        _ = φ x' * φ y' * zy * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ := by group
        _ = _ := by
          rw [show φ x' * φ y' * zy * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ =
            φ x' * φ y' * (zy * (φ x')⁻¹ * zy⁻¹) * (φ y')⁻¹ by group, ← hy1 (φ x')⁻¹]
          group
    rw [h1, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hle : φ.range.map χ.toMonoidHom ≤ φ.range := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have : b ∈ (φ.range).comap ψ := by rw [hD]; trivial
    exact this
  have : Finite φ.range :=
    Finite.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective χ.injective]

end Edge

end CFSG.RankThree.PartOne.CTP
