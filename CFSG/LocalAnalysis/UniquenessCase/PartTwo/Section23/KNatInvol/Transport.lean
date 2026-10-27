module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatInvol.Semilinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol

open CFSG.Quasithin Matrix

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private noncomputable def coordAut (e : W ≃* Multiplicative (ι → K)) (s : MulAut W) :
    (ι → K) ≃+ (ι → K) where
  toFun v := Multiplicative.toAdd (e (s (e.symm (Multiplicative.ofAdd v))))
  invFun v := Multiplicative.toAdd (e (s⁻¹ (e.symm (Multiplicative.ofAdd v))))
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp only [ofAdd_add, map_mul, toAdd_mul]

@[simp] private theorem coordAut_apply (e : W ≃* Multiplicative (ι → K)) (s : MulAut W)
    (v : ι → K) :
    coordAut e s v = Multiplicative.toAdd (e (s (e.symm (Multiplicative.ofAdd v)))) := rfl

private theorem coordAut_apply_toAdd (e : W ≃* Multiplicative (ι → K)) (s : MulAut W)
    (w : W) :
    coordAut e s (Multiplicative.toAdd (e w)) = Multiplicative.toAdd (e (s w)) := by
  simp

private theorem coordAut_apply_toAdd_ne {e : W ≃* Multiplicative (ι → K)}
    {s : MulAut W} {w : W} (hw : s w ≠ w) :
    coordAut e s (Multiplicative.toAdd (e w)) ≠ Multiplicative.toAdd (e w) := by
  rw [coordAut_apply_toAdd]
  intro h
  exact hw (e.injective (Multiplicative.toAdd.injective h))

private theorem coordAut_normalizes {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W),
      Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W))) :
    ∀ γ ∈ Γ, ∃ γ' ∈ Γ, ∀ v : ι → K,
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ coordAut e s v =
        coordAut e s (((γ' : GL ι K) : Matrix ι ι K) *ᵥ v) := by
  intro γ hγ
  let h : MulAut W := s⁻¹ * ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) * s
  have hmem : h ∈ H := by
    have hiff := (Subgroup.mem_set_normalizer_iff.mp hs) h
    refine hiff.mpr ?_
    have hsm : s * h * s⁻¹ = ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) := by
      simp only [h]
      group
    rw [hsm]
    exact (π ⟨γ, hγ⟩).2
  let γ' : ↥Γ := π.symm ⟨h, hmem⟩
  have hh : ((π γ' : ↥H) : MulAut W) = h := by
    simp only [γ', MulEquiv.apply_symm_apply]
  have hconj : s * h = ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) * s := by
    simp only [h]
    group
  have happ : ∀ x : W, s (h x) = ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) (s x) := by
    intro x
    rw [← MulAut.mul_apply, hconj, MulAut.mul_apply]
  refine ⟨(γ' : GL ι K), γ'.2, fun v => ?_⟩
  set y : W := e.symm (Multiplicative.ofAdd v) with hy
  have hσv : coordAut e s v = Multiplicative.toAdd (e (s y)) := by
    simpa [y] using coordAut_apply_toAdd e s y
  have h2 : Multiplicative.toAdd (e (((π γ' : ↥H) : MulAut W) y)) =
      ((γ' : GL ι K) : Matrix ι ι K) *ᵥ v := by
    have h2' := he γ' y
    simpa [y] using h2'
  calc ((γ : GL ι K) : Matrix ι ι K) *ᵥ coordAut e s v
      = ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e (s y)) := by rw [hσv]
    _ = Multiplicative.toAdd (e (((π ⟨γ, hγ⟩ : ↥H) : MulAut W) (s y))) := by
        rw [he ⟨γ, hγ⟩ (s y)]
    _ = Multiplicative.toAdd (e (s (((π γ' : ↥H) : MulAut W) y))) := by
        rw [← happ y, ← hh]
    _ = coordAut e s (Multiplicative.toAdd (e (((π γ' : ↥H) : MulAut W) y))) := by
        rw [coordAut_apply_toAdd]
    _ = coordAut e s (((γ' : GL ι K) : Matrix ι ι K) *ᵥ v) := by rw [h2]

private theorem fixV_zpowers_eq_comap {e : W ≃* Multiplicative (ι → K)} {s : MulAut W}
    {C : AddSubgroup (ι → K)} (hC : ∀ v, v ∈ C ↔ coordAut e s v = v) :
    fixV (Subgroup.zpowers s) = (AddSubgroup.toSubgroup C).comap e.toMonoidHom := by
  ext w
  rw [Subgroup.mem_comap, mem_fixV]
  constructor
  · intro hw
    change Multiplicative.toAdd (e w) ∈ C
    exact (hC _).2 (by
      rw [coordAut_apply_toAdd, hw s (Subgroup.mem_zpowers s)])
  · intro hw x hx
    have hCw : Multiplicative.toAdd (e w) ∈ C := hw
    have hsw : s w = w := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [← coordAut_apply_toAdd e s w]
      exact (hC _).1 hCw
    have hle : Subgroup.zpowers s ≤ MulAction.stabilizer (MulAut W) w := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hsw
    have hx' := hle hx
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hx'

private theorem index_fixV_zpowers {e : W ≃* Multiplicative (ι → K)} {s : MulAut W}
    {C : AddSubgroup (ι → K)} (hC : ∀ v, v ∈ C ↔ coordAut e s v = v) :
    (fixV (Subgroup.zpowers s)).index = C.index := by
  rw [fixV_zpowers_eq_comap hC,
    Subgroup.index_comap_of_surjective (AddSubgroup.toSubgroup C) e.surjective,
    AddSubgroup.index_toSubgroup]

theorem le_rkIdx_of_realizes [Finite W] [Finite K] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥)
    (hsemi : SemilinearNormalizer Γ) (hι : 2 ≤ Fintype.card ι) {k : ℕ}
    (hK : Nat.card K = 2 ^ k) {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hs1 : s ≠ 1) : k ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, e, he⟩ := KTabC.exists_natEquiv hreal
  obtain ⟨w, hw⟩ : ∃ w : W, s w ≠ w := by
    by_contra h
    have h' : ∀ x, s x = x := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    exact hs1 (MulEquiv.ext fun x => by simpa using h' x)
  let C : AddSubgroup (ι → K) :=
    { carrier := {v | coordAut e s v = v}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change coordAut e s a = a at ha
        change coordAut e s b = b at hb
        change coordAut e s (a + b) = a + b
        rw [map_add, ha, hb]
      neg_mem' := by
        intro a ha
        change coordAut e s a = a at ha
        change coordAut e s (-a) = -a
        rw [map_neg, ha] }
  have hC : ∀ v, v ∈ C ↔ coordAut e s v = v := fun v => Iff.rfl
  have hσne : coordAut e s (Multiplicative.toAdd (e w)) ≠ Multiplicative.toAdd (e w) :=
    coordAut_apply_toAdd_ne hw
  have hsem : ∀ c : K, ∃ c' : K, ∀ v : ι → K,
      coordAut e s (c • v) = c' • coordAut e s v :=
    hsemi (coordAut e s) (coordAut_normalizes π e he hs)
  have hcard : Nat.card K ≤ C.index :=
    card_le_index_of_semilinear hι (coordAut e s) hsem hσne C hC
  have hidx : (fixV (Subgroup.zpowers s)).index = C.index :=
    index_fixV_zpowers hC
  have hcardW : Nat.card W = 2 ^ (k * Fintype.card ι) := by
    calc Nat.card W = Nat.card (Multiplicative (ι → K)) := Nat.card_congr e.toEquiv
      _ = Nat.card (ι → K) := Nat.card_congr Multiplicative.toAdd
      _ = Nat.card K ^ Nat.card ι := Nat.card_fun
      _ = Nat.card K ^ Fintype.card ι := by
          congr 1
          exact Nat.card_eq_fintype_card
      _ = (2 ^ k) ^ Fintype.card ι := by rw [hK]
      _ = 2 ^ (k * Fintype.card ι) := by rw [pow_mul]
  have hdvd : (fixV (Subgroup.zpowers s)).index ∣ 2 ^ (k * Fintype.card ι) := by
    rw [← hcardW]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hle : 2 ^ k ≤ 2 ^ j := by
    calc 2 ^ k = Nat.card K := hK.symm
      _ ≤ C.index := hcard
      _ = (fixV (Subgroup.zpowers s)).index := hidx.symm
      _ = 2 ^ j := hj
  have hkj : k ≤ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  calc k ≤ j := hkj
    _ = rkIdx (fixV (Subgroup.zpowers s)) := by
        unfold rkIdx
        rw [hj, padicValNat.prime_pow]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol
