module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertSpec
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.StandardType.StepTwoToralSmall

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.StepTwoToralCert CFSG.StandardType CFSG.Assembly

open scoped Matrix

theorem latChar_latPerm {N p : ℕ} (π : Equiv.Perm (Fin N)) {g : Fin N → ZMod p}
    (hg : ∀ i, g (π i) = g i) (α : Fin N → ℤ) : latChar p g (latPerm π α) = latChar p g α := by
  have h1 : (∑ i, (α (π.symm i) : ZMod p) * g i) = ∑ j, (α j : ZMod p) * g (π j) := by
    rw [← Equiv.sum_comp π.symm (fun j => (α j : ZMod p) * g (π j))]
    exact Finset.sum_congr rfl fun i _ => by rw [Equiv.apply_symm_apply]
  have h2 : (∑ j, (α j : ZMod p) * g (π j)) = ∑ j, (α j : ZMod p) * g j :=
    Finset.sum_congr rfl fun j _ => by rw [hg j]
  simp only [latChar, latPerm]
  rw [h1, h2]

@[expose] def eigenSub (p : ℕ) [NeZero p] {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (O : Set (Fin N → ℤ)) : Submodule (ZMod p) (Fin N → ZMod p) where
  carrier := latEigenCoroot p S π O
  add_mem' := by
    rintro f g ⟨x, hx, hxf, z, hz, hzx⟩ ⟨y, hy, hyg, w, hw, hwy⟩
    refine ⟨x + y, Submodule.add_mem _ hx hy, fun i => ?_, z + w, Submodule.add_mem _ hz hw, ?_⟩
    · simp [hxf i, hyg i]
    · funext i
      have h1 := congrFun hzx i
      have h2 := congrFun hwy i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h1 h2 ⊢
      linear_combination h1 + h2
  zero_mem' :=
    ⟨0, Submodule.zero_mem _, fun i => by simp, 0, Submodule.zero_mem _, by funext i; simp⟩
  smul_mem' := by
    rintro c f ⟨x, hx, hxf, z, hz, hzx⟩
    refine ⟨(c.val : ℤ) • x, Submodule.smul_mem _ _ hx, fun i => ?_, (c.val : ℤ) • z,
      Submodule.smul_mem _ _ hz, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_zmod_val, hxf i]
    · funext i
      have h1 := congrFun hzx i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      linear_combination (c.val : ℤ) * h1

section Scale

variable {N : ℕ}

private theorem latGram_smul (k : ℤ) (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram (k • S) α β = k * latGram S α β := by
  simp only [latGram, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem latLinked_smul {k : ℤ} (hk : k ≠ 0) (S : Matrix (Fin N) (Fin N) ℤ)
    (Φ : Set (Fin N → ℤ)) : latLinked (k • S) Φ = latLinked S Φ := by
  have h : (fun α β : Fin N → ℤ => α ∈ Φ ∧ β ∈ Φ ∧ latGram (k • S) α β ≠ 0) =
      (fun α β : Fin N → ℤ => α ∈ Φ ∧ β ∈ Φ ∧ latGram S α β ≠ 0) := by
    funext α β
    simp only [latGram_smul, ne_eq, mul_eq_zero, hk, false_or]
  unfold latLinked
  rw [h]

theorem isCompOrbit_smul_iff {k : ℤ} (hk : k ≠ 0) (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (Φ O : Set (Fin N → ℤ)) :
    IsCompOrbit (k • S) π Φ O ↔ IsCompOrbit S π Φ O := by
  unfold IsCompOrbit
  rw [latLinked_smul hk]

private theorem latCorootZ_smul {k : ℤ} (hk : 0 < k) (S : Matrix (Fin N) (Fin N) ℤ)
    (α : Fin N → ℤ) : latCorootZ (k • S) α = latCorootZ S α := by
  funext i
  unfold latCorootZ
  rw [latGram_smul, latGram_smul, show 2 * (k * latGram S (Pi.single i 1) α) =
    k * (2 * latGram S (Pi.single i 1) α) by ring, Int.mul_ediv_mul_of_pos _ _ hk]

theorem latEigenCoroot_smul {k : ℤ} (hk : 0 < k) (p : ℕ) (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (O : Set (Fin N → ℤ)) :
    latEigenCoroot p (k • S) π O = latEigenCoroot p S π O := by
  have h : latCorootZ (k • S) = latCorootZ S := funext fun α => latCorootZ_smul hk S α
  simp only [latEigenCoroot, h]

end Scale

section Orbit

variable {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {π : Equiv.Perm (Fin N)}

private theorem latLinked_mem_iff {Φ : Set (Fin N → ℤ)} {α β : Fin N → ℤ}
    (h : latLinked S Φ α β) : α ∈ Φ ↔ β ∈ Φ := by
  change Relation.EqvGen _ α β at h
  induction h with
  | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private theorem iterate_latPerm_mem {Φ : Set (Fin N → ℤ)} (hΦ : ∀ β ∈ Φ, latPerm π β ∈ Φ)
    {α : Fin N → ℤ} (hα : α ∈ Φ) (k : ℕ) : (latPerm π)^[k] α ∈ Φ := by
  induction k with
  | zero => simpa using hα
  | succ k ih => rw [Function.iterate_succ_apply']; exact hΦ _ ih

theorem isCompOrbit_subset {Φ O : Set (Fin N → ℤ)} (hΦ : ∀ β ∈ Φ, latPerm π β ∈ Φ)
    (h : IsCompOrbit S π Φ O) : O ⊆ Φ := by
  obtain ⟨α, hα, rfl⟩ := h
  rintro β ⟨k, hk⟩
  exact (latLinked_mem_iff hk).mp (iterate_latPerm_mem hΦ hα k)

theorem isCompOrbit_exists_mem {Φ O : Set (Fin N → ℤ)} (h : IsCompOrbit S π Φ O) :
    ∃ α ∈ Φ, α ∈ O := by
  obtain ⟨α, hα, rfl⟩ := h
  exact ⟨α, hα, 0, Relation.EqvGen.refl _⟩

end Orbit

section T0

variable {τ : Tag} {p : ℕ}

theorem mem_t0Sub_iff (g : Fin τ.rank → ZMod p) :
    g ∈ t0Sub τ p ↔
      ∃ c : Fin τ.rank → ZMod p, ∀ i, g i = ∑ j, c j * ((τ.cartan j i : ℤ) : ZMod p) := by
  unfold t0Sub
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun i => by simp [Finset.sum_apply]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun i => by simp [Finset.sum_apply, hc i]⟩

theorem exists_int_of_mem_t0Sub [NeZero p] {g : Fin τ.rank → ZMod p} (hg : g ∈ t0Sub τ p) :
    ∃ c : Fin τ.rank → ℤ,
      ∀ i, g i = ∑ j, (c j : ZMod p) * ((τ.cartan j i : ℤ) : ZMod p) := by
  obtain ⟨c, hc⟩ := (mem_t0Sub_iff g).1 hg
  refine ⟨fun j => ((c j).val : ℤ), fun i => ?_⟩
  rw [hc i]
  simp [ZMod.natCast_zmod_val]

theorem t0Sub_eq_top (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ τ.cartan.det) : t0Sub τ p = ⊤ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  refine eq_top_iff.mpr fun f _ => ?_
  rw [mem_t0Sub_iff]
  let A : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p) := τ.cartan.map fun x => (x : ZMod p)
  have hAdet : A.det = ((τ.cartan.det : ℤ) : ZMod p) := (Int.cast_det τ.cartan).symm
  have hAne : A.det ≠ 0 := by
    rw [hAdet]
    exact fun h => hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hAne
  refine ⟨(Aᵀ)⁻¹ *ᵥ f, fun i => ?_⟩
  have hmul : Aᵀ *ᵥ ((Aᵀ)⁻¹ *ᵥ f) = f := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Aᵀ (by rwa [Matrix.det_transpose]),
      Matrix.one_mulVec]
  rw [← congrFun hmul i, Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

end T0

section CowAct

variable {τ : Tag} {p : ℕ}

private theorem latChar_single (f : Fin τ.rank → ZMod p) (i : Fin τ.rank) :
    latChar p f (Pi.single i 1) = f i := by
  simp [latChar, Pi.single_apply]

theorem cowAct_one (f : Fin τ.rank → ZMod p) : cowAct 1 f = f := by
  funext i
  simp [cowAct, latChar_single]

private theorem latPerm_one (α : Fin τ.rank → ℤ) : latPerm 1 α = α := rfl

theorem commutesPi_one_left (u : WeylGroup τ) : CommutesPi (1 : Equiv.Perm (Fin τ.rank)) u := by
  intro α
  rw [latPerm_one, latPerm_one]

theorem commutesPi_one_right (π : Equiv.Perm (Fin τ.rank)) : CommutesPi π (1 : WeylGroup τ) := by
  intro α
  rw [one_smul, one_smul]

theorem exists_normal_cowAct
    [NeZero p] (K : KacData τ) (b₀ : Fin τ.rank → ZMod p) :
    ∃ (w : WeylGroup τ) (μ : Fin τ.rank → ℤ), K.IsNormal p μ ∧ cowAct w b₀ = modP p μ := by
  obtain ⟨w, μ, hw, hμ⟩ := K.exists_normal p (NeZero.pos p) (fun j => ((b₀ j).val : ℤ))
  refine ⟨w, μ, hμ, funext fun i => ?_⟩
  have h := hw (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))
  rw [smul_inv_smul] at h
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  rw [Int.cast_sub, sub_eq_zero] at h0
  have h1 : ((Pi.single i 1 : Fin τ.rank → ℤ) ⬝ᵥ μ : ℤ) = μ i := by simp
  rw [h1] at h0
  have h2 : (((w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) ⬝ᵥ fun j => ((b₀ j).val : ℤ) : ℤ) :
      ZMod p) = cowAct w b₀ i := by
    simp only [dotProduct, cowAct, latChar, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val]
  rw [h2] at h0
  exact h0.symm

end CowAct

section E6

local instance : NeZero Tag.E6.rank := ⟨by decide⟩

private def cE6 (i j : Fin Tag.E6.rank) : ℤ := Tag.cartan .E6 i j

private def cE6s (i j : Fin 6) : ℤ := Tag.cartan .E6 i j

private def e6Func (g : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  g 0 + 2 * g 2 + g 4 + 2 * g 5

private def e6Inv : Fin 6 → Fin 6 → ZMod 3 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 1, 2], ![0, 0, 2, 0, 1, 2], ![0, 0, 0, 0, 2, 1],
    ![0, 1, 1, 2, 2, 1], ![0, 2, 2, 1, 1, 1]]

private theorem e6_three_key : ∀ g0 g1 g2 g3 g4 g5 : ZMod 3, g0 + 2 * g2 + g4 + 2 * g5 = 0 →
    ∀ i : Fin 6, (![g0, g1, g2, g3, g4, g5] : Fin 6 → ZMod 3) i =
      ∑ j : Fin 6, (∑ k : Fin 6, e6Inv j k * (![g0, g1, g2, g3, g4, g5] : Fin 6 → ZMod 3) k) *
        ((cE6s j i : ℤ) : ZMod 3) := by
  decide +kernel

private theorem e6_row_ker : ∀ j : Fin Tag.E6.rank, ((cE6 j 0 : ℤ) : ZMod 3) +
    2 * ((cE6 j 2 : ℤ) : ZMod 3) + ((cE6 j 4 : ℤ) : ZMod 3) +
      2 * ((cE6 j 5 : ℤ) : ZMod 3) = 0 := by
  decide +kernel

private theorem mem_t0Sub_E6_three {g : Fin Tag.E6.rank → ZMod 3} :
    g ∈ t0Sub .E6 3 ↔ e6Func g = 0 := by
  rw [mem_t0Sub_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hc' : ∀ i, g i = ∑ j, c j * ((cE6 j i : ℤ) : ZMod 3) := hc
    unfold e6Func
    rw [hc' 0, hc' 2, hc' 4, hc' 5]
    have : ∀ j : Fin Tag.E6.rank, c j * ((cE6 j 0 : ℤ) : ZMod 3) +
        2 * (c j * ((cE6 j 2 : ℤ) : ZMod 3)) + c j * ((cE6 j 4 : ℤ) : ZMod 3) +
        2 * (c j * ((cE6 j 5 : ℤ) : ZMod 3)) = 0 := by
      intro j
      have := e6_row_ker j
      linear_combination c j * this
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => this j
  · intro h
    refine ⟨fun j => ∑ k : Fin Tag.E6.rank, e6Inv j k * g k, fun i => ?_⟩
    have := e6_three_key (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) h i
    have hg : (![g 0, g 1, g 2, g 3, g 4, g 5] : Fin Tag.E6.rank → ZMod 3) = g := by
      funext k
      fin_cases k <;> rfl
    rw [hg] at this
    exact this

theorem fixedSub_e6Gamma_le_t0Sub_three : fixedSub 3 e6Gamma ≤ t0Sub .E6 3 := by
  intro g hg
  rw [mem_t0Sub_E6_three]
  have h0 : g 5 = g 0 := hg 0
  have h2 : g 4 = g 2 := hg 2
  unfold e6Func
  rw [h0, h2]
  have h3 : (3 : ZMod 3) = 0 := by decide
  calc g 0 + 2 * g 2 + g 2 + 2 * g 0 = 3 * g 0 + 3 * g 2 := by ring
    _ = 0 := by rw [h3]; ring

theorem eq_t0Sub_or_top_E6 {V : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)}
    (h : t0Sub .E6 3 ≤ V) : V = t0Sub .E6 3 ∨ V = ⊤ := by
  by_cases hV : V ≤ t0Sub .E6 3
  · exact Or.inl (le_antisymm hV h)
  · right
    obtain ⟨v, hvV, hvn⟩ := SetLike.not_le_iff_exists.mp hV
    have hφv : e6Func v ≠ 0 := fun h0 => hvn ((mem_t0Sub_E6_three).2 h0)
    refine eq_top_iff.mpr fun w _ => ?_
    have hlin : ∀ (c : ZMod 3) (a : Fin Tag.E6.rank → ZMod 3), e6Func (a - c • v) =
        e6Func a - c * e6Func v := by
      intro c a
      simp only [e6Func, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hmem : w - (e6Func w * (e6Func v)⁻¹) • v ∈ t0Sub .E6 3 := by
      rw [mem_t0Sub_E6_three, hlin, mul_assoc, inv_mul_cancel₀ hφv, mul_one, sub_self]
    have := V.add_mem (h hmem) (V.smul_mem (e6Func w * (e6Func v)⁻¹) hvV)
    simpa using this

end E6

section Conj

variable {G : Type} [Group G]

private theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj m).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hm

theorem isComponentOf_conj_pair {G₀ : Subgroup G} {m : G} (hm : m ∈ G₀) {b : G}
    {L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer ({b} : Set G))) :
    IsComponentOf (L₁.map (MulAut.conj m).toMonoidHom)
      (G₀ ⊓ Subgroup.centralizer ({m * b * m⁻¹} : Set G)) := by
  have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hL₁ m
  have e : (G₀ ⊓ Subgroup.centralizer ({b} : Set G)).map (MulAut.conj m).toMonoidHom =
      G₀ ⊓ Subgroup.centralizer ({m * b * m⁻¹} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj m).injective,
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hm),
      CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
  rwa [e] at h

theorem card_inf_centralizer_conj {Bs L₁ : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (Bs : Set G)) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer
      ((L₁.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) =
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (L₁ : Set G)) := by
  have h1 : Bs ⊓ Subgroup.centralizer
      ((L₁.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
      (Bs ⊓ Subgroup.centralizer (L₁ : Set G)).map (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj m).injective, map_conj_eq_of_mem_normalizer hm]
    congr 1
    exact (CFSG.LocalAnalysis.ComponentInitial.conjSub_centralizer m L₁).symm
  rw [h1]
  exact CFSG.LocalAnalysis.ComponentInitial.card_conjSub m _

end Conj

section Frame

variable {G : Type} [Group G]

structure ToralFrame (τ : Tag) (p : ℕ) (G₀ Bs : Subgroup G) (π : Equiv.Perm (Fin τ.rank)) where
  coord : Bs →* Multiplicative (Fin τ.rank → ZMod p)
  coord_inj : Function.Injective coord
  coord_fixed : ∀ (b : Bs) (i : Fin τ.rank),
    Multiplicative.toAdd (coord b) (π i) = Multiplicative.toAdd (coord b) i
  coord_surj : ∀ g ∈ t0Sub τ p, (∀ i, g (π i) = g i) →
    ∃ b : Bs, Multiplicative.toAdd (coord b) = g
  weyl : ∀ u : WeylGroup τ, CommutesPi π u →
    ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), ∀ b b' : Bs, (b' : G) = m * b * m⁻¹ →
      Multiplicative.toAdd (coord b') = cowAct u (Multiplicative.toAdd (coord b))
  orbit : ∀ b : Bs, b ≠ 1 → ∀ L : Subgroup G,
    IsComponentOf L (G₀ ⊓ Subgroup.centralizer ({(b : G)} : Set G)) →
      ∃ O, IsCompOrbit τ.symmetrizedCartan π
          (latPhi {α | IsRoot τ α} p (Multiplicative.toAdd (coord b))) O ∧
        (∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
          ∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0) ∧
        ∀ b' : Bs, Multiplicative.toAdd (coord b') ∈ latEigenCoroot p τ.symmetrizedCartan π O →
          (b' : G) ∈ L
  orbitU : ∀ U : Subgroup G, U ≤ Bs → U ≠ ⊥ → ∀ K : Subgroup G,
    IsComponentOf K (G₀ ⊓ Subgroup.centralizer (U : Set G)) →
      ∃ O, IsCompOrbit τ.symmetrizedCartan π {α | IsRoot τ α ∧ ∀ u : Bs, (u : G) ∈ U →
          latChar p (Multiplicative.toAdd (coord u)) α = 0} O ∧
        ∀ b' : Bs, (∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0) →
          (b' : G) ∈ Subgroup.centralizer (K : Set G)

namespace ToralFrame

variable {τ : Tag} {p : ℕ} [NeZero p] {G₀ Bs : Subgroup G} {π : Equiv.Perm (Fin τ.rank)}
  (fr : ToralFrame τ p G₀ Bs π)

@[expose] def imageSub (H : Subgroup G) : Submodule (ZMod p) (Fin τ.rank → ZMod p) where
  carrier := {g | ∃ b : Bs, (b : G) ∈ H ∧ Multiplicative.toAdd (fr.coord b) = g}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, H.mul_mem ha hb, by simp⟩
  zero_mem' := ⟨1, H.one_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    refine ⟨a ^ c.val, ?_, ?_⟩
    · rw [Subgroup.coe_pow]
      exact H.pow_mem ha c.val
    · rw [map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

@[expose] def V : Submodule (ZMod p) (Fin τ.rank → ZMod p) := fr.imageSub ⊤

theorem mem_imageSub {H : Subgroup G} {g : Fin τ.rank → ZMod p} :
    g ∈ fr.imageSub H ↔ ∃ b : Bs, (b : G) ∈ H ∧ Multiplicative.toAdd (fr.coord b) = g :=
  Iff.rfl

theorem mem_V {g : Fin τ.rank → ZMod p} :
    g ∈ fr.V ↔ ∃ b : Bs, Multiplicative.toAdd (fr.coord b) = g := by
  simp [V, mem_imageSub]

theorem imageSub_le_V (H : Subgroup G) : fr.imageSub H ≤ fr.V := by
  rintro g ⟨b, -, rfl⟩
  exact (fr.mem_V).2 ⟨b, rfl⟩

theorem toAdd_coord_mem_V (b : Bs) : Multiplicative.toAdd (fr.coord b) ∈ fr.V :=
  (fr.mem_V).2 ⟨b, rfl⟩

theorem coord_ne_zero {b : Bs} (hb : b ≠ 1) : Multiplicative.toAdd (fr.coord b) ≠ 0 := by
  intro h
  apply hb
  apply fr.coord_inj
  rw [map_one]
  exact Multiplicative.toAdd.injective (by rw [h]; rfl)

theorem card_imageSub (H : Subgroup G) (hH : H ≤ Bs) :
    Nat.card (fr.imageSub H) = Nat.card H := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun h : H => (⟨Multiplicative.toAdd (fr.coord ⟨h, hH h.2⟩), ⟨⟨h, hH h.2⟩, h.2, rfl⟩⟩ :
      fr.imageSub H)) ⟨?_, ?_⟩)
  · intro h₁ h₂ h
    have h' := Multiplicative.toAdd.injective (congrArg Subtype.val h)
    have h2 := fr.coord_inj h'
    exact Subtype.ext (congrArg (Subtype.val : Bs → G) h2)
  · rintro ⟨g, b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

theorem card_le_of_forall [Finite G] (S : Submodule (ZMod p) (Fin τ.rank → ZMod p))
    (hS : S ≤ fr.V) (H : Subgroup G)
    (hH : ∀ b : Bs, Multiplicative.toAdd (fr.coord b) ∈ S → (b : G) ∈ H) :
    Nat.card S ≤ Nat.card ↥(Bs ⊓ H) := by
  classical
  have hex : ∀ g : S, ∃ b : Bs, Multiplicative.toAdd (fr.coord b) = g := fun g =>
    (fr.mem_V).1 (hS g.2)
  choose f hf using hex
  refine Nat.card_le_card_of_injective
    (fun g : S => (⟨(f g : G), (f g).2, hH (f g) (by rw [hf g]; exact g.2)⟩ : ↥(Bs ⊓ H))) ?_
  intro g₁ g₂ h
  have h1 : f g₁ = f g₂ := Subtype.ext (congrArg (Subtype.val : ↥(Bs ⊓ H) → G) h)
  exact Subtype.ext ((hf g₁).symm.trans ((congrArg (fun b => Multiplicative.toAdd (fr.coord b))
    h1).trans (hf g₂)))

theorem qualPlane [Finite G] (hp : p.Prime) (hπR : ∀ α, IsRoot τ α → IsRoot τ (latPerm π α))
    {D J : Subgroup G} (hDBs : D ≤ Bs) (hDcard : Nat.card D = p ^ 2)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set G)))
    (hJcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    QualPlane p fr.V (fr.imageSub D) := by
  have hDne : D ≠ ⊥ := by
    rintro rfl
    have h1 : (1 : ℕ) = p ^ 2 := by rw [← hDcard]; simp
    have h2 := hp.one_lt
    nlinarith
  obtain ⟨O, hO, hann⟩ := fr.orbitU D hDBs hDne J hJ
  set Φ : Set (Fin τ.rank → ℤ) := {α | IsRoot τ α ∧ ∀ u : Bs, (u : G) ∈ D →
    latChar p (Multiplicative.toAdd (fr.coord u)) α = 0} with hΦdef
  have hΦ : Φ = phiSet p ((fr.imageSub D : Submodule (ZMod p) (Fin τ.rank → ZMod p)) :
      Set (Fin τ.rank → ZMod p)) := by
    ext α
    constructor
    · rintro ⟨hα, h⟩
      refine ⟨hα, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      exact h u hu
    · rintro ⟨hα, h⟩
      exact ⟨hα, fun u hu => h _ ⟨u, hu, rfl⟩⟩
  have hΦperm : ∀ β ∈ Φ, latPerm π β ∈ Φ := fun β hβ =>
    ⟨hπR β hβ.1, fun u hu => by
      rw [latChar_latPerm π (fr.coord_fixed u) β]
      exact hβ.2 u hu⟩
  have hOsub : O ⊆ Φ := isCompOrbit_subset hΦperm hO
  refine ⟨fr.imageSub_le_V D, ?_, ?_, ?_⟩
  · rw [fr.card_imageSub D hDBs]
    exact hDcard
  · obtain ⟨α, hα, -⟩ := isCompOrbit_exists_mem hO
    exact ⟨α, hΦ ▸ hα⟩
  · refine (fr.card_le_of_forall _ inf_le_left (Subgroup.centralizer (J : Set G)) ?_).trans hJcard
    intro b hb
    refine hann b fun α hα => ?_
    exact hb.2 α (hΦ ▸ hOsub hα)

theorem V_eq_fixedSub (h : fixedSub p π ≤ t0Sub τ p) : fr.V = fixedSub p π := by
  refine le_antisymm ?_ fun g hg => ?_
  · intro g hg
    obtain ⟨b, rfl⟩ := (fr.mem_V).1 hg
    exact fun i => fr.coord_fixed b i
  · obtain ⟨b, hb⟩ := fr.coord_surj g (h hg) hg
    exact (fr.mem_V).2 ⟨b, hb⟩

theorem t0Sub_le_V (hπ : π = 1) : t0Sub τ p ≤ fr.V := fun g hg => by
  obtain ⟨b, hb⟩ := fr.coord_surj g hg fun i => by rw [hπ]; rfl
  exact (fr.mem_V).2 ⟨b, hb⟩

theorem V_eq_top (hπ : π = 1) (h : t0Sub τ p = ⊤) : fr.V = ⊤ :=
  eq_top_iff.mpr (h ▸ fr.t0Sub_le_V hπ)

end ToralFrame

end Frame

section Cert

variable {τ : Tag} {p : ℕ}

@[expose] def CertGood (τ : Tag) (p : ℕ) (π : Equiv.Perm (Fin τ.rank))
    (V : Submodule (ZMod p) (Fin τ.rank → ZMod p)) (b₁ : Fin τ.rank → ZMod p) : Prop :=
  ∀ O : Set (Fin τ.rank → ℤ),
    IsCompOrbit τ.symmetrizedCartan π (latPhi {α | IsRoot τ α} p b₁) O →
      Nat.card ↥(V ⊓ annSub p O) ≤ p ^ 2 →
        ∀ D : Submodule (ZMod p) (Fin τ.rank → ZMod p), QualPlane p V D →
          CertConcl p π V b₁ O D

@[expose] def RepGood (τ : Tag) (p : ℕ) (π : Equiv.Perm (Fin τ.rank))
    (V : Submodule (ZMod p) (Fin τ.rank → ZMod p)) : Prop :=
  ∀ b₀ ∈ V, b₀ ≠ 0 → ∃ w : WeylGroup τ, CommutesPi π w ∧
    (cowAct w b₀ ∈ V → cowAct w b₀ ≠ 0 → CertGood τ p π V (cowAct w b₀))

theorem repGood_of_split
    [NeZero p] {V : Submodule (ZMod p) (Fin τ.rank → ZMod p)} (hS : SplitCertSpec τ p V) :
    RepGood τ p 1 V := by
  intro b₀ _ _
  obtain ⟨w, μ, hμ, hcow⟩ := exists_normal_cowAct (kacOf τ) b₀
  refine ⟨w, commutesPi_one_left w, fun hV hne => ?_⟩
  rw [hcow] at hV hne ⊢
  exact hS μ hμ hV hne

theorem repGood_of_twist {γ : Equiv.Perm (Fin Tag.E6.rank)} (hT : TwistCertSpec p γ) :
    RepGood Tag.E6 p γ (fixedSub p γ) := by
  intro b₀ hb₀V hb₀ne
  refine ⟨1, commutesPi_one_right γ, fun _ _ => ?_⟩
  rw [cowAct_one]
  exact hT b₀ hb₀V hb₀ne

end Cert

section Witness

variable {G : Type} [Group G] [Finite G]

theorem witness_of_frame {τ : Tag} {p : ℕ} [NeZero p] {G₀ Bs D J : Subgroup G}
    {π : Equiv.Perm (Fin τ.rank)} (fr : ToralFrame τ p G₀ Bs π) (hp : p.Prime)
    (hπR : ∀ α, IsRoot τ α → IsRoot τ (latPerm π α)) (hrep : RepGood τ p π fr.V)
    (hDBs : D ≤ Bs) (hDcard : Nat.card D = p ^ 2)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set G)))
    (hJcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    {b : G} {L₁ : Subgroup G} (hb : b ∈ Bs) (hb1 : b ≠ 1)
    (hL₁ : IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer ({b} : Set G)))
    (hL₁card : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L₁ : Set G)) ≤ p ^ 2) :
    ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
      ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D := by
  have hD' := fr.qualPlane hp hπR hDBs hDcard hJ hJcard
  let bB : Bs := ⟨b, hb⟩
  have hbB : bB ≠ 1 := fun h => hb1 (congrArg (Subtype.val : Bs → G) h)
  obtain ⟨w, hcomm, hgood⟩ := hrep _ (fr.toAdd_coord_mem_V bB) (fr.coord_ne_zero hbB)
  obtain ⟨m, hm, hmcoord⟩ := fr.weyl w hcomm
  obtain ⟨hmG₀, hmN⟩ := Subgroup.mem_inf.mp hm
  have hb'mem : m * b * m⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hmN b).mp hb
  let b'B : Bs := ⟨m * b * m⁻¹, hb'mem⟩
  have hb'coord : Multiplicative.toAdd (fr.coord b'B) =
      cowAct w (Multiplicative.toAdd (fr.coord bB)) := hmcoord bB b'B rfl
  have hb'ne : b'B ≠ 1 := by
    intro h
    apply hb1
    have h' : m * b * m⁻¹ = 1 := congrArg (Subtype.val : Bs → G) h
    simpa using h'
  have hb₁V : cowAct w (Multiplicative.toAdd (fr.coord bB)) ∈ fr.V :=
    hb'coord ▸ fr.toAdd_coord_mem_V b'B
  have hb₁ne : cowAct w (Multiplicative.toAdd (fr.coord bB)) ≠ 0 :=
    hb'coord ▸ fr.coord_ne_zero hb'ne
  have hgood' := hgood hb₁V hb₁ne
  set L₁' : Subgroup G := L₁.map (MulAut.conj m).toMonoidHom with hL₁'def
  have hL₁' : IsComponentOf L₁' (G₀ ⊓ Subgroup.centralizer ({(b'B : G)} : Set G)) :=
    isComponentOf_conj_pair hmG₀ hL₁
  have hL₁'card : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L₁' : Set G)) ≤ p ^ 2 := by
    rw [hL₁'def, card_inf_centralizer_conj hmN]
    exact hL₁card
  obtain ⟨O, hO, hcent, hmem⟩ := fr.orbit b'B hb'ne L₁' hL₁'
  rw [hb'coord] at hO
  have hOcard : Nat.card ↥(fr.V ⊓ annSub p O) ≤ p ^ 2 := by
    refine (fr.card_le_of_forall _ inf_le_left (Subgroup.centralizer (L₁' : Set G))
      ?_).trans hL₁'card
    intro b'' hb''
    exact (hcent b'').mpr hb''.2
  obtain ⟨s, hs, hs0, u, hucomm, hu⟩ := hgood' O hO hOcard _ hD'
  obtain ⟨c, e, he, hse⟩ := Submodule.mem_span_insert.1 hs
  have hset : ((fr.V : Set (Fin τ.rank → ZMod p)) ∩
      latEigenCoroot p τ.symmetrizedCartan π O) =
      ((fr.V ⊓ eigenSub p τ.symmetrizedCartan π O :
        Submodule (ZMod p) (Fin τ.rank → ZMod p)) : Set (Fin τ.rank → ZMod p)) := rfl
  rw [hset, Submodule.span_eq] at he
  obtain ⟨heV, heE⟩ := he
  obtain ⟨eB, heB⟩ := (fr.mem_V).1 heV
  have heL : (eB : G) ∈ L₁' := hmem eB (by rw [heB]; exact heE)
  set k : ℕ := c.val with hk
  let a'B : Bs := b'B ^ k * eB
  have ha'G : (a'B : G) = (m * b * m⁻¹) ^ k * (eB : G) := by simp [a'B, b'B]
  have ha'coord : Multiplicative.toAdd (fr.coord a'B) = s := by
    rw [hse]
    simp only [a'B, map_mul, map_pow, toAdd_mul, toAdd_pow, hb'coord, heB]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), hk, ZMod.natCast_zmod_val]
  obtain ⟨m', hm', hm'coord⟩ := fr.weyl u hucomm
  obtain ⟨hm'G₀, hm'N⟩ := Subgroup.mem_inf.mp hm'
  have ha''mem : m' * (a'B : G) * m'⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hm'N _).mp a'B.2
  let a''B : Bs := ⟨m' * (a'B : G) * m'⁻¹, ha''mem⟩
  have ha''coord : Multiplicative.toAdd (fr.coord a''B) = cowAct u s := by
    rw [hm'coord a'B a''B rfl, ha'coord]
  obtain ⟨d, hdD, hdcoord⟩ := hu
  have hd : d = a''B :=
    fr.coord_inj (Multiplicative.toAdd.injective (hdcoord.trans ha''coord.symm))
  have hmD : m' * (a'B : G) * m'⁻¹ ∈ D := by
    have h1 : ((d : Bs) : G) ∈ D := hdD
    rw [hd] at h1
    exact h1
  refine ⟨m⁻¹ * (a'B : G) * m, ?_, ?_, (m' * m)⁻¹, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) _).mp a'B.2
      simpa using h1
    · obtain ⟨l₀, hl₀, hl₀eq⟩ := heL
      have hl : (eB : G) = m * l₀ * m⁻¹ := by
        rw [← hl₀eq]
        simp [MulAut.conj_apply]
      have h2 : m⁻¹ * (a'B : G) * m = b ^ k * l₀ := by
        rw [ha'G, hl, conj_pow]
        group
      rw [h2]
      exact Subgroup.mul_mem_sup ((Subgroup.zpowers b).pow_mem (Subgroup.mem_zpowers b) k) hl₀
  · intro h
    have h1 : (a'B : G) = 1 := by
      have h2 : m * (m⁻¹ * (a'B : G) * m) * m⁻¹ = (a'B : G) := by group
      rw [← h2, h]
      group
    have h3 : a'B = 1 := Subtype.ext h1
    apply hs0
    rw [← ha'coord, h3, map_one]
    rfl
  · exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hm' hm)
  · have h1 : ((m' * m)⁻¹)⁻¹ * (m⁻¹ * (a'B : G) * m) * (m' * m)⁻¹ = m' * (a'B : G) * m'⁻¹ := by
      group
    rw [h1]
    exact hmD

variable {p : ℕ} [NeZero p] {G₀ Bs D J : Subgroup G}

theorem witness_of_split {τ : Tag}
    (fr : ToralFrame τ p G₀ Bs 1) (hp : p.Prime) (hS : SplitCertSpec τ p fr.V)
    (hDBs : D ≤ Bs) (hDcard : Nat.card D = p ^ 2)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set G)))
    (hJcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    {b : G} {L₁ : Subgroup G} (hb : b ∈ Bs) (hb1 : b ≠ 1)
    (hL₁ : IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer ({b} : Set G)))
    (hL₁card : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L₁ : Set G)) ≤ p ^ 2) :
    ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
      ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D :=
  witness_of_frame fr hp (fun α hα => by rw [latPerm_one]; exact hα) (repGood_of_split hS) hDBs
    hDcard hJ hJcard hb hb1 hL₁ hL₁card

theorem witness_of_twist (fr : ToralFrame Tag.E6 p G₀ Bs e6Gamma) (hp : p.Prime)
    (hV : fr.V = fixedSub p e6Gamma) (hT : TwistCertSpec p e6Gamma)
    (hDBs : D ≤ Bs) (hDcard : Nat.card D = p ^ 2)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set G)))
    (hJcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    {b : G} {L₁ : Subgroup G} (hb : b ∈ Bs) (hb1 : b ≠ 1)
    (hL₁ : IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer ({b} : Set G)))
    (hL₁card : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L₁ : Set G)) ≤ p ^ 2) :
    ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
      ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D := by
  refine witness_of_frame fr hp (fun α hα => IsRoot.permLattice
    (fun i j => TwistTag.cartan_perm .E6 i j) hα) ?_ hDBs hDcard hJ hJcard hb hb1 hL₁ hL₁card
  rw [hV]
  exact repGood_of_twist hT

end Witness

end CFSG.StandardType.StepTwoToralSmall
