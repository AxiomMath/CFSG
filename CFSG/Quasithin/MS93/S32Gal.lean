module

public import CFSG.Quasithin.MS93.S32Desc
public import CFSG.Quasithin.MS93.S32Nat

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

section Aux

variable {V : Type} [CommGroup V] {F : Type} [Field F]

private theorem exists_coord_one {K : Subgroup (MulAut V)} {I : Subgroup V}
    {π : ↥(StatedSL 3 F) →* ↥K} (h : (FFModel.nat (StatedSL 3 F)).RealizesVia K I ⊥ π) :
    ∃ ψ : (Fin 3 → F) → V, (∀ x x', ψ (x + x') = ψ x * ψ x') ∧ Function.Injective ψ ∧
      (∀ v, v ∈ I ↔ ∃ x, ψ x = v) ∧
      ∀ (γ : ↥(StatedSL 3 F)) x, ((π γ : ↥K) : MulAut V) (ψ x) =
        ψ (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := natReal_coord h
  have hinv : ∀ k : ↥K, ∀ u ∈ I, (k : MulAut V) u ∈ I := h.2.2.2.1
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e : ↥I ≃* Multiplicative (Fin 3 → F) := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  refine ⟨fun x => ((e.symm (Multiplicative.ofAdd x) : ↥I) : V), fun x x' => ?_, ?_, ?_, ?_⟩
  · simp only [ofAdd_add, map_mul, Subgroup.coe_mul]
  · intro x x' hxx'
    exact Multiplicative.ofAdd.injective (e.symm.injective (Subtype.ext hxx'))
  · intro v
    refine ⟨fun hv => ⟨Multiplicative.toAdd (β ⟨v, hv⟩), ?_⟩, ?_⟩
    · exact congrArg Subtype.val (e.symm_apply_apply ⟨v, hv⟩)
    · rintro ⟨x, rfl⟩
      exact (e.symm _).2
  · intro γ x
    have hmem := hinv (π γ) _ (e.symm (Multiplicative.ofAdd x)).2
    have h1 := hβe γ _ hmem
    have h2 : β (e.symm (Multiplicative.ofAdd x)) = Multiplicative.ofAdd x :=
      e.apply_symm_apply _
    rw [h2, toAdd_ofAdd] at h1
    have h3 : (⟨_, hmem⟩ : ↥I) = e.symm (Multiplicative.ofAdd
        (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) := by
      rw [← h1]
      exact (e.symm_apply_apply _).symm
    exact congrArg Subtype.val h3

private theorem exists_coord_two {K : Subgroup (MulAut V)} {I : Fin 2 → Subgroup V}
    {π : ↥(StatedSL 3 F) →* ↥K} (hind : iSupIndep I)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia K (I i) ⊥ π) :
    ∃ Φ : (Fin 3 → F) × (Fin 3 → F) → V, (∀ w w', Φ (w + w') = Φ w * Φ w') ∧
      Function.Injective Φ ∧ (∀ v, v ∈ I 0 ⊔ I 1 ↔ ∃ w, Φ w = v) ∧
      ∀ (γ : GL (Fin 3) F) (hγ : γ ∈ StatedSL 3 F) w,
        ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (Φ w) = Φ (dg γ w) := by
  obtain ⟨ψ₀, h0a, h0i, h0m, h0e⟩ := exists_coord_one (hreal 0)
  obtain ⟨ψ₁, h1a, h1i, h1m, h1e⟩ := exists_coord_one (hreal 1)
  have hdisj : Disjoint (I 0) (I 1) := hind.pairwiseDisjoint (by decide)
  refine ⟨fun w => ψ₀ w.1 * ψ₁ w.2, fun w w' => ?_, fun w w' h => ?_, fun v => ?_,
    fun γ hγ w => ?_⟩
  · simp only [Prod.fst_add, Prod.snd_add, h0a, h1a]
    exact mul_mul_mul_comm _ _ _ _
  · have hq : ψ₀ w.1 / ψ₀ w'.1 = ψ₁ w'.2 / ψ₁ w.2 :=
      div_eq_div_iff_mul_eq_mul.mpr (h.trans (mul_comm _ _))
    have hm0 : ψ₀ w.1 / ψ₀ w'.1 ∈ I 0 :=
      (I 0).div_mem ((h0m _).mpr ⟨_, rfl⟩) ((h0m _).mpr ⟨_, rfl⟩)
    have hm1 : ψ₀ w.1 / ψ₀ w'.1 ∈ I 1 := by
      rw [hq]
      exact (I 1).div_mem ((h1m _).mpr ⟨_, rfl⟩) ((h1m _).mpr ⟨_, rfl⟩)
    have e0 : ψ₀ w.1 / ψ₀ w'.1 = 1 := Subgroup.disjoint_def.mp hdisj hm0 hm1
    have e1 : ψ₁ w'.2 / ψ₁ w.2 = 1 := hq ▸ e0
    exact Prod.ext (h0i (div_eq_one.mp e0)) (h1i (div_eq_one.mp e1)).symm
  · rw [Subgroup.mem_sup]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      obtain ⟨a, rfl⟩ := (h0m y).mp hy
      obtain ⟨b, rfl⟩ := (h1m z).mp hz
      exact ⟨(a, b), rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨_, (h0m _).mpr ⟨_, rfl⟩, _, (h1m _).mpr ⟨_, rfl⟩, rfl⟩
  · show ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (ψ₀ w.1 * ψ₁ w.2) = ψ₀ (dg γ w).1 * ψ₁ (dg γ w).2
    rw [map_mul, h0e, h1e, dg_fst, dg_snd]

private structure GalCoord (V F : Type) [CommGroup V] [Field F] (N : Subgroup V) where
  Φ : (Fin 3 → F) × (Fin 3 → F) → V
  add : ∀ w w', Φ (w + w') = Φ w * Φ w'
  inj : Function.Injective Φ
  mem : ∀ v, v ∈ N ↔ ∃ w, Φ w = v

namespace GalCoord

variable {N : Subgroup V}

private theorem map_zero' (C : GalCoord V F N) : C.Φ 0 = 1 :=
  (left_eq_mul (a := C.Φ 0)).mp (by rw [← C.add, add_zero])

private theorem map_neg' (C : GalCoord V F N) (w : (Fin 3 → F) × (Fin 3 → F)) :
    C.Φ (-w) = (C.Φ w)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← C.add, add_neg_cancel, C.map_zero'])

private theorem mem_of (C : GalCoord V F N) (w : (Fin 3 → F) × (Fin 3 → F)) : C.Φ w ∈ N :=
  (C.mem _).mpr ⟨w, rfl⟩

private noncomputable def tr (C : GalCoord V F N) (g : MulAut V)
    (w : (Fin 3 → F) × (Fin 3 → F)) : (Fin 3 → F) × (Fin 3 → F) :=
  Function.invFun C.Φ (g (C.Φ w))

private theorem Φ_tr (C : GalCoord V F N) {g : MulAut V} (hg : ∀ v ∈ N, g v ∈ N)
    (w : (Fin 3 → F) × (Fin 3 → F)) : C.Φ (C.tr g w) = g (C.Φ w) :=
  Function.invFun_eq ((C.mem _).mp (hg _ (C.mem_of w)))

private theorem tr_add (C : GalCoord V F N) {g : MulAut V} (hg : ∀ v ∈ N, g v ∈ N)
    (w w' : (Fin 3 → F) × (Fin 3 → F)) : C.tr g (w + w') = C.tr g w + C.tr g w' :=
  C.inj (by rw [C.Φ_tr hg, C.add, map_mul, C.add, C.Φ_tr hg, C.Φ_tr hg])

private theorem tr_mul (C : GalCoord V F N) {g h : MulAut V} (hg : ∀ v ∈ N, g v ∈ N)
    (hh : ∀ v ∈ N, h v ∈ N) (w : (Fin 3 → F) × (Fin 3 → F)) :
    C.tr (g * h) w = C.tr g (C.tr h w) :=
  C.inj (by
    rw [C.Φ_tr (fun v hv => hg (h v) (hh v hv)), C.Φ_tr hg, C.Φ_tr hh, MulAut.mul_apply])

private theorem tr_one (C : GalCoord V F N) (w : (Fin 3 → F) × (Fin 3 → F)) : C.tr 1 w = w :=
  C.inj (by rw [C.Φ_tr (fun v hv => hv), MulAut.one_apply])

private noncomputable def trEquiv (C : GalCoord V F N) {g : MulAut V} (hg : ∀ v ∈ N, g v ∈ N)
    (hg' : ∀ v ∈ N, g⁻¹ v ∈ N) :
    ((Fin 3 → F) × (Fin 3 → F)) ≃+ ((Fin 3 → F) × (Fin 3 → F)) where
  toFun := C.tr g
  invFun := C.tr g⁻¹
  left_inv w := C.inj (by rw [C.Φ_tr hg', C.Φ_tr hg, MulAut.inv_apply_self])
  right_inv w := C.inj (by rw [C.Φ_tr hg, C.Φ_tr hg', MulAut.apply_inv_self])
  map_add' := C.tr_add hg

private theorem tr_conj (C : GalCoord V F N) {K X : Subgroup (MulAut V)}
    {π : ↥(StatedSL 3 F) →* ↥K} (hπ : Function.Surjective π)
    (hCK : ∀ (γ : GL (Fin 3) F) (hγ : γ ∈ StatedSL 3 F) w,
      ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (C.Φ w) = C.Φ (dg γ w))
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V))) (hXI : ∀ x ∈ X, ∀ v ∈ N, x v ∈ N)
    {g : MulAut V} (hg : g ∈ X) :
    ∀ γ ∈ StatedSL 3 F, ∃ γ' ∈ StatedSL 3 F, ∀ w, C.tr g (dg γ (C.tr g⁻¹ w)) = dg γ' w := by
  intro γ hγ
  have hkK : g * ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) * g⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hXN hg) _).mp (π ⟨γ, hγ⟩).2
  obtain ⟨⟨δ, hδ⟩, hδπ⟩ := hπ ⟨_, hkK⟩
  refine ⟨δ, hδ, fun w => C.inj ?_⟩
  have e1 := hCK γ hγ (C.tr g⁻¹ w)
  have e2 := hCK δ hδ w
  rw [C.Φ_tr (hXI g hg), ← e1, C.Φ_tr (hXI _ (X.inv_mem hg)), ← e2, hδπ]
  rfl

private theorem form (C : GalCoord V F N) {K : Subgroup (MulAut V)}
    {π : ↥(StatedSL 3 F) →* ↥K}
    (hCK : ∀ (γ : GL (Fin 3) F) (hγ : γ ∈ StatedSL 3 F) w,
      ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (C.Φ w) = C.Φ (dg γ w))
    {U : Subgroup V} (hUI : U ≤ N) (hUK : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) (hU0 : U ≠ ⊥)
    (hU1 : U ≠ N) :
    (∀ w, C.Φ w ∈ U ↔ w.1 = 0) ∨ ∃ d : F, ∀ w, C.Φ w ∈ U ↔ w.2 = d • w.1 := by
  let B : AddSubgroup ((Fin 3 → F) × (Fin 3 → F)) :=
    { carrier := {w | C.Φ w ∈ U}
      add_mem' := by
        intro a b ha hb
        show C.Φ (a + b) ∈ U
        rw [C.add]
        exact U.mul_mem ha hb
      zero_mem' := by
        show C.Φ 0 ∈ U
        rw [C.map_zero']
        exact U.one_mem
      neg_mem' := by
        intro a ha
        show C.Φ (-a) ∈ U
        rw [C.map_neg']
        exact U.inv_mem ha }
  have hB : ∀ w, w ∈ B ↔ C.Φ w ∈ U := fun w => Iff.rfl
  have hBinv : ∀ γ ∈ StatedSL 3 F, ∀ w ∈ B, dg γ w ∈ B := by
    intro γ hγ w hw
    rw [hB] at hw ⊢
    rw [← hCK γ hγ]
    exact hUK _ (π ⟨γ, hγ⟩).2 _ hw
  rcases addSubgroup_cases_dg B hBinv with h | h | h | ⟨d, h⟩
  · refine absurd ?_ hU0
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨w, rfl⟩ := (C.mem u).mp (hUI hu)
    have hw : w ∈ B := (hB w).mpr hu
    rw [h, AddSubgroup.mem_bot] at hw
    rw [hw, C.map_zero']
    exact Subgroup.one_mem _
  · refine absurd (le_antisymm hUI fun v hv => ?_) hU1
    obtain ⟨w, rfl⟩ := (C.mem v).mp hv
    exact (hB w).mp (by rw [h]; exact AddSubgroup.mem_top w)
  · exact Or.inl fun w => (hB w).symm.trans (h w)
  · exact Or.inr ⟨d, fun w => (hB w).symm.trans (h w)⟩

private theorem faithful (C : GalCoord V F N) {K : Subgroup (MulAut V)}
    {π : ↥(StatedSL 3 F) →* ↥K} (hπ : Function.Surjective π)
    (hCK : ∀ (γ : GL (Fin 3) F) (hγ : γ ∈ StatedSL 3 F) w,
      ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (C.Φ w) = C.Φ (dg γ w))
    {U : Subgroup V}
    (hform : (∀ w, C.Φ w ∈ U ↔ w.1 = 0) ∨ ∃ d : F, ∀ w, C.Φ w ∈ U ↔ w.2 = d • w.1) :
    ∀ k ∈ K, (∀ u ∈ U, k u = u) → k = 1 := by
  intro k hk hku
  obtain ⟨⟨δ, hδ⟩, hδπ⟩ := hπ ⟨k, hk⟩
  have hfix : ∀ w, C.Φ w ∈ U → dg δ w = w := by
    intro w hw
    apply C.inj
    rw [← hCK δ hδ, hδπ]
    exact hku _ hw
  have hδ1 : ∀ x : Fin 3 → F, (δ : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
    intro x
    rcases hform with h | ⟨d, h⟩
    · exact congrArg Prod.snd (hfix (0, x) ((h _).mpr rfl))
    · exact congrArg Prod.fst (hfix (x, d • x) ((h _).mpr rfl))
  have hδ' : (⟨δ, hδ⟩ : ↥(StatedSL 3 F)) = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, hδ1]
    simp
  have h1 : (⟨k, hk⟩ : ↥K) = 1 := by rw [← hδπ, hδ', map_one]
  exact congrArg Subtype.val h1

private theorem charP_two (C : GalCoord V F N) (hV : ∀ v : V, v ^ 2 = 1) : CharP F 2 := by
  refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
  have h : ((fun _ => 1, 0) : (Fin 3 → F) × (Fin 3 → F)) + (fun _ => 1, 0) = 0 :=
    C.inj (by rw [C.add, ← pow_two, hV, C.map_zero'])
  have h' : (1 : F) + 1 = 0 := congrArg (fun w : (Fin 3 → F) × (Fin 3 → F) => w.1 0) h
  rw [← one_add_one_eq_two]
  exact h'

end GalCoord

private theorem eq_of_agree_on {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hcent : ∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1)
    {U : Subgroup V} (hUK : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U)
    (hfaith : ∀ k ∈ K, (∀ u ∈ U, k u = u) → k = 1)
    {p g : MulAut V} (hp : p ∈ X) (hg : g ∈ K) {e : ℕ} (hpe : p ^ 2 ^ e = 1)
    (hge : g ^ 2 ^ e = 1) (hpg : ∀ u ∈ U, p u = g u) : p = g := by
  set c := p * g⁻¹ with hc
  have hcX : c ∈ X := X.mul_mem hp (X.inv_mem (hKX hg))
  have hcU : ∀ u ∈ U, c u = u := by
    intro u hu
    rw [hc, MulAut.mul_apply, hpg _ (hUK _ (K.inv_mem hg) u hu), MulAut.apply_inv_self]
  have hcU' : ∀ u ∈ U, c⁻¹ u = u := by
    intro u hu
    conv_lhs => rw [← hcU u hu]
    exact MulAut.inv_apply_self _ _ _
  have hcomm : ∀ k ∈ K, c * k = k * c := by
    intro k hk
    have hck : c * k * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hXN hcX) k).mp hk
    have h1 : c * k * c⁻¹ * k⁻¹ = 1 := by
      refine hfaith _ (K.mul_mem hck (K.inv_mem hk)) fun u hu => ?_
      simp only [MulAut.mul_apply]
      rw [hcU' _ (hUK _ (K.inv_mem hk) u hu), MulAut.apply_inv_self, hcU u hu]
    have h2 := mul_inv_eq_one.mp h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hpcg : p = c * g := by rw [hc, inv_mul_cancel_right]
  have hce : c ^ 2 ^ e = 1 := by
    have h1 : p ^ 2 ^ e = c ^ 2 ^ e * g ^ 2 ^ e := by
      rw [hpcg, Commute.mul_pow (hcomm g hg)]
    rw [hpe, hge, mul_one] at h1
    exact h1.symm
  rw [hpcg, hcent c hcX hcomm e hce, one_mul]

private theorem exists_common_fixed [Finite F] (h2F : 2 ∣ Nat.card F) {G : Type} [Group G]
    (hG : IsPGroup 2 G) (A : G → (Fin 3 → F) × (Fin 3 → F) → (Fin 3 → F) × (Fin 3 → F))
    (hA1 : ∀ w, A 1 w = w) (hAmul : ∀ g h w, A (g * h) w = A g (A h w))
    (hAdg : ∀ g, ∃ γ : GL (Fin 3) F, ∀ w, A g w = dg γ w) :
    ∃ c : Fin 3 → F, c ≠ 0 ∧ ∀ g, A g (c, 0) = (c, 0) ∧ A g (0, c) = (0, c) := by
  let _ : MulAction G ((Fin 3 → F) × (Fin 3 → F)) :=
    { smul := A
      one_smul := hA1
      mul_smul := hAmul }
  have hcard : 2 ∣ Nat.card ((Fin 3 → F) × (Fin 3 → F)) := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    exact Dvd.dvd.mul_right (dvd_pow h2F (by norm_num)) _
  have h0 : (0 : (Fin 3 → F) × (Fin 3 → F)) ∈ MulAction.fixedPoints G _ := by
    refine MulAction.mem_fixedPoints.mpr fun g => ?_
    obtain ⟨γ, hγ⟩ := hAdg g
    show A g 0 = 0
    rw [hγ]
    simp [dg]
  obtain ⟨b, hb, hb0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard h0
  have hfx : ∀ g (γ : GL (Fin 3) F), (∀ w, A g w = dg γ w) →
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ b.1 = b.1 ∧
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ b.2 = b.2 := by
    intro g γ hγ
    have h : dg γ b = b := (hγ b).symm.trans (MulAction.mem_fixedPoints.mp hb g)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨c, hc0, hcf⟩ : ∃ c : Fin 3 → F, c ≠ 0 ∧ ∀ g (γ : GL (Fin 3) F),
      (∀ w, A g w = dg γ w) → (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ c = c := by
    by_cases h1 : b.1 = 0
    · exact ⟨b.2, fun h2 => hb0 (Prod.ext h1.symm h2.symm), fun g γ hγ => (hfx g γ hγ).2⟩
    · exact ⟨b.1, h1, fun g γ hγ => (hfx g γ hγ).1⟩
  refine ⟨c, hc0, fun g => ?_⟩
  obtain ⟨γ, hγ⟩ := hAdg g
  have hc := hcf g γ hγ
  rw [hγ, hγ]
  exact ⟨Prod.ext hc (by simp), Prod.ext (by simp) hc⟩

private theorem main_of_coord [Finite V] [Finite F] [CharP F 2] (h2F : 2 ∣ Nat.card F)
    {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hcent : ∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1)
    {π : ↥(StatedSL 3 F) →* ↥K} (hπ : Function.Surjective π) {N : Subgroup V}
    (C : GalCoord V F N)
    (hCK : ∀ (γ : GL (Fin 3) F) (hγ : γ ∈ StatedSL 3 F) w,
      ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (C.Φ w) = C.Φ (dg γ w))
    (hXI : ∀ x ∈ X, ∀ v ∈ N, x v ∈ N) {P : Subgroup (MulAut V)} (hPX : P ≤ X)
    (hP : IsPGroup 2 P) {U : Subgroup V} (hUI : U ≤ N) (hUK : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U)
    (hUP : ∀ p ∈ P, ∀ u ∈ U, p u ∈ U) (hU0 : U ≠ ⊥) (hU1 : U ≠ N) :
    ∃ v ∈ N, v ∉ U ∧ ∀ p ∈ P, p v = v := by
  have hform := C.form hCK hUI hUK hU0 hU1
  have hfaith := C.faithful hπ hCK hform
  let S : Submodule F ((Fin 3 → F) × (Fin 3 → F)) :=
    { carrier := {w | C.Φ w ∈ U}
      add_mem' := by
        intro a b ha hb
        show C.Φ (a + b) ∈ U
        rw [C.add]
        exact U.mul_mem ha hb
      zero_mem' := by
        show C.Φ 0 ∈ U
        rw [C.map_zero']
        exact U.one_mem
      smul_mem' := by
        intro c w hw
        show C.Φ (c • w) ∈ U
        change C.Φ w ∈ U at hw
        rcases hform with h | ⟨d, h⟩
        · rw [h] at hw ⊢
          rw [Prod.smul_fst, hw, smul_zero]
        · rw [h] at hw ⊢
          rw [Prod.smul_fst, Prod.smul_snd, hw]
          exact smul_comm c d _ }
  have hS : ∀ w, w ∈ S ↔ C.Φ w ∈ U := fun w => Iff.rfl
  have hPN : ∀ t : ↥P, ∀ v ∈ N, (t : MulAut V) v ∈ N := fun t => hXI _ (hPX t.2)
  have hPN' : ∀ t : ↥P, ∀ v ∈ N, (t : MulAut V)⁻¹ v ∈ N :=
    fun t => hXI _ (X.inv_mem (hPX t.2))
  let E : ↥P → ((Fin 3 → F) × (Fin 3 → F)) ≃+ ((Fin 3 → F) × (Fin 3 → F)) :=
    fun t => C.trEquiv (hPN t) (hPN' t)
  let act : ↥P → ((Fin 3 → F) × (Fin 3 → F)) →+ ((Fin 3 → F) × (Fin 3 → F)) :=
    fun t => (E t).toAddMonoidHom
  have hact : ∀ t w, act t w = C.tr t w := fun _ _ => rfl
  have hmul : ∀ s t w, act (s * t) w = act s (act t w) := by
    intro s t w
    rw [hact, hact, hact, Subgroup.coe_mul, C.tr_mul (hPN s) (hPN t)]
  have hinj : ∀ t, Function.Injective (act t) := fun t => (E t).injective
  have hsemi : ∀ t, ∃ σ : F ≃+* F, ∀ (c : F) w, act t (c • w) = σ c • act t w := by
    intro t
    have h2 := C.tr_conj hπ hCK hXN hXI (X.inv_mem (hPX t.2))
    rw [inv_inv] at h2
    obtain ⟨σ, hσ⟩ :=
      exists_ringEquiv_of_normalizes (E t) (C.tr_conj hπ hCK hXN hXI (hPX t.2)) h2
    exact ⟨σ, hσ⟩
  obtain ⟨σ, hσ⟩ := exists_hom_ringAut_of_semilinear act hmul hinj hsemi
  have hlin : ∀ t : ↥P, σ t = 1 → ∃ γ : GL (Fin 3) F, ∀ w, act t w = dg γ w := by
    intro t ht
    obtain ⟨e, he⟩ := hP t
    have hl : ∀ (c : F) w, E t (c • w) = c • E t w := by
      intro c w
      have h := hσ t c w
      rw [ht] at h
      exact h
    have hit : ∀ (k : ℕ) w, (⇑(E t))^[k] w = C.tr ((t : MulAut V) ^ k) w := by
      intro k
      induction k with
      | zero =>
        intro w
        rw [pow_zero, C.tr_one]
        rfl
      | succ k ih =>
        intro w
        rw [Function.iterate_succ_apply', ih, pow_succ',
          C.tr_mul (hPN t) (hXI _ (X.pow_mem (hPX t.2) k))]
        rfl
    have hte : (t : MulAut V) ^ 2 ^ e = 1 := by
      rw [← Subgroup.coe_pow, he, Subgroup.coe_one]
    have hit' : ∀ w, (⇑(E t))^[2 ^ e] w = w := fun w => by rw [hit, hte, C.tr_one]
    have hU' : ∀ w ∈ S.toAddSubgroup, E t w ∈ S.toAddSubgroup := by
      intro w hw
      show C.Φ (C.tr t w) ∈ U
      rw [C.Φ_tr (hPN t)]
      exact hUP _ t.2 _ hw
    have hform' : (∀ w, w ∈ S.toAddSubgroup ↔ w.1 = 0) ∨
        ∃ d : F, ∀ w, w ∈ S.toAddSubgroup ↔ w.2 = d • w.1 := hform
    obtain ⟨γ, hγ, hγe, hγU⟩ := exists_sl3_of_linear (E t) hl hit' S.toAddSubgroup hU' hform'
    have hagree : ∀ u ∈ U, (t : MulAut V) u = ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) u := by
      intro u hu
      obtain ⟨w, rfl⟩ := (C.mem u).mp (hUI hu)
      rw [← C.Φ_tr (hPN t), hCK]
      exact congrArg C.Φ (hγU w hu)
    have hge : ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) ^ 2 ^ e = 1 := by
      have h1 : (⟨γ, hγ⟩ : ↥(StatedSL 3 F)) ^ 2 ^ e = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hγe)
      rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
    have heq := eq_of_agree_on hKX hXN hcent hUK hfaith (hPX t.2) (π ⟨γ, hγ⟩).2 hte hge hagree
    refine ⟨γ, fun w => C.inj ?_⟩
    rw [hact, C.Φ_tr (hPN t), heq, hCK]
  obtain ⟨c, hc0, hc⟩ := exists_common_fixed h2F (hP.to_subgroup σ.ker)
    (fun g w => act (g : ↥P) w) (fun w => C.tr_one w) (fun g h w => hmul g h w)
    (fun g => hlin g (MonoidHom.mem_ker.mp g.2))
  let V₀ : Submodule F ((Fin 3 → F) × (Fin 3 → F)) :=
    { carrier := {w | ∀ t : ↥P, σ t = 1 → act t w = w}
      add_mem' := by
        intro a b ha hb t ht
        rw [map_add, ha t ht, hb t ht]
      zero_mem' := by
        intro t _
        exact map_zero (act t)
      smul_mem' := by
        intro c w hw t ht
        rw [hσ, hw t ht, ht]
        rfl }
  have hV₀ : ∀ w, w ∈ V₀ ↔ ∀ t : ↥P, σ t = 1 → act t w = w := fun w => Iff.rfl
  have hV : ∀ t, ∀ v ∈ V₀, act t v ∈ V₀ := by
    intro t v hv
    rw [hV₀] at hv ⊢
    intro s hs
    have hk : σ (t⁻¹ * s * t) = 1 := by
      rw [map_mul, map_mul, hs, mul_one, map_inv, inv_mul_cancel]
    calc act s (act t v) = act (t * (t⁻¹ * s * t)) v := by
          rw [← hmul, show t * (t⁻¹ * s * t) = s * t by group]
      _ = act t (act (t⁻¹ * s * t) v) := hmul _ _ _
      _ = act t v := by rw [hv _ hk]
  have hVS : ¬ V₀ ≤ S := by
    intro hle
    have h1 := (hS _).mp (hle ((hV₀ _).mpr fun t ht => (hc ⟨t, MonoidHom.mem_ker.mpr ht⟩).1))
    have h2 := (hS _).mp (hle ((hV₀ _).mpr fun t ht => (hc ⟨t, MonoidHom.mem_ker.mpr ht⟩).2))
    rcases hform with h | ⟨d, h⟩
    · exact hc0 ((h _).mp h1)
    · have h3 : c = d • (0 : Fin 3 → F) := (h _).mp h2
      rw [smul_zero] at h3
      exact hc0 h3
  obtain ⟨w, -, hwfix, hwS⟩ := exists_fixed_not_mem act hmul σ hσ V₀ hV
    (fun t ht v hv => (hV₀ v).mp hv t ht) S hVS
  refine ⟨C.Φ w, C.mem_of w, fun h => hwS ((hS w).mpr h), fun p hp => ?_⟩
  rw [← C.Φ_tr (hXI p (hPX hp))]
  exact congrArg C.Φ (hwfix ⟨p, hp⟩)

end Aux

theorem exists_fixed_not_mem_of_two_copies {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hcent : ∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1)
    {I : Fin 2 → Subgroup V} {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥K}
    (hind : iSupIndep I)
    (hreal : ∀ i, (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).RealizesVia K (I i) ⊥ π)
    (hXI : ∀ x ∈ X, ∀ v ∈ I 0 ⊔ I 1, x v ∈ I 0 ⊔ I 1)
    {P : Subgroup (MulAut V)} (hPX : P ≤ X) (hP : IsPGroup 2 P)
    {U : Subgroup V} (hUI : U ≤ I 0 ⊔ I 1) (hUK : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U)
    (hUP : ∀ p ∈ P, ∀ u ∈ U, p u ∈ U) (hU0 : U ≠ ⊥) (hU1 : U ≠ I 0 ⊔ I 1) :
    ∃ v ∈ I 0 ⊔ I 1, v ∉ U ∧ ∀ p ∈ P, p v = v := by
  obtain ⟨Φ, hadd, hinj, hmem, hK⟩ := exists_coord_two hind hreal
  let C : GalCoord V F (I 0 ⊔ I 1) := ⟨Φ, hadd, hinj, hmem⟩
  have : CharP F 2 := C.charP_two hV
  have h2F : 2 ∣ Nat.card F := by
    rw [hF]
    refine dvd_pow_self 2 fun hn => ?_
    have h1 := Finite.one_lt_card (α := F)
    rw [hF, hn, pow_zero] at h1
    exact lt_irrefl _ h1
  exact main_of_coord h2F hKX hXN hcent (hreal 0).1 C hK hXI hPX hP hUI hUK hUP hU0 hU1

end CFSG.Quasithin.MS93.S32
