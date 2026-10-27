module

public import CFSG.Quasithin.EmptyFaithful.SBc13Pair
public import CFSG.Quasithin.EmptyFaithful.SBc13Mod
public import CFSG.Quasithin.EmptyFaithful.SBc13Gen
public import CFSG.Quasithin.EmptyFaithful.SBc13Stab
public import CFSG.Quasithin.EmptyFaithful.S146P12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc13

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem core_shapeTwo (S : Setting146 G T M) {PQ : Subgroup G} (hp : p.Prime)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hK₁ : K₁ = oTwoUpper H₁) (hK₂ : K₂ = oTwoUpper H₂) {K' : Subgroup G} (hK'le : K' ≤ K₁ ⊔ K₂)
    (hK'perf : oTwoUpper K' = K') {z' : G} (hz'U : z' ∈ uHi T M H H₁)
    (hz'Z : z' ∉ quasithinOmegaOneCenter T) (hcent : ∀ k ∈ K', k * z' = z' * k) : K' ≤ K₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hK₁H₁ : K₁ ≤ H₁ := hK₁ ▸ oTwoUpper_le H₁
  have hK₂H₂ : K₂ ≤ H₂ := hK₂ ▸ oTwoUpper_le H₂
  have hK₁G : K₁ ≤ mcOf T := hK₁H₁.trans (hH₁H.trans hHG)
  have hK₂G : K₂ ≤ mcOf T := hK₂H₂.trans (hH₂H.trans hHG)
  have hQ₂ : pCoreOf 2 H ≤ H₂ := hdec.Q₂
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := fun y hy => by
    rw [hK₂]
    exact normalizer_le_normalizer_oTwoUpper_P (hdec.H₁_le_normalizer_H₂ (hK₁H₁ hy))
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hK₁N
  have hH₂Z : ∀ x ∈ H₂, x ∈ zStab T z' := by
    intro x hx
    refine ⟨hH₂H.trans hHG hx, ?_⟩
    have h1 : ⁅z', x⁆ ∈ quasithinOmegaOneCenter T :=
      hdec.cent₁ (Subgroup.commutator_mem_commutator hz'U hx)
    have h2 := (quasithinOmegaOneCenter T).inv_mem h1
    rw [commutatorElement_inv, commutatorElement_def] at h2
    exact h2
  have hK'sub : K' ≤ K₂ ⊔ pCoreOf 2 H := by
    intro k hk
    have hk' : k ∈ ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hK'le hk
    rw [hmul] at hk'
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Set.mem_mul.mp hk'
    have hkS : k₁ * k₂ ∈ zStab T z' :=
      mem_zStab_of_commute ((mcOf T).mul_mem (hK₁G hk₁) (hK₂G hk₂)) (hcent _ hk)
    have hk₁S : k₁ ∈ zStab T z' := by
      have := (zStab T z').mul_mem hkS ((zStab T z').inv_mem (hH₂Z k₂ (hK₂H₂ hk₂)))
      simpa using this
    have hk₁Q : k₁ ∈ pCoreOf 2 H := by
      by_contra hk₁Q
      obtain ⟨x, hx, hxc⟩ := exists_comm_notin_of_isDecP S hred hdec hz'U hz'Z
      have hxK₁ : x ∈ K₁ := hK₁ ▸ hx
      have hk₁X : k₁ ∈ oTwoUpper H₁ := hK₁ ▸ hk₁
      obtain ⟨n, hn⟩ := hdec.exists_pow_of_notin hp hk₁X hk₁Q hx
      have hxS : x ∈ zStab T z' := by
        have e : x = (x * (k₁ ^ n)⁻¹) * k₁ ^ n := by group
        rw [e]
        exact (zStab T z').mul_mem (hH₂Z _ (hQ₂ hn)) ((zStab T z').pow_mem hk₁S n)
      exact hxc hxS.2
    exact (K₂ ⊔ pCoreOf 2 H).mul_mem (Subgroup.mem_sup_right hk₁Q) (Subgroup.mem_sup_left hk₂)
  have hN : K₂ ⊔ pCoreOf 2 H ≤ Subgroup.normalizer (K₂ : Set G) := by
    refine sup_le Subgroup.le_normalizer fun q hq => ?_
    rw [hK₂]
    exact normalizer_le_normalizer_oTwoUpper_P (Subgroup.le_normalizer (hQ₂ hq))
  have hO : oTwoUpper (K₂ ⊔ pCoreOf 2 H) ≤ K₂ :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hN)
      (pCoreOf_isPGroup 2 H) le_sup_right (by rw [sup_comm])
  calc K' = oTwoUpper K' := hK'perf.symm
    _ ≤ oTwoUpper (K₂ ⊔ pCoreOf 2 H) := oTwoUpper_mono hK'sub
    _ ≤ K₂ := hO

theorem g_mem_g2_of_theta_shapeTwo (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hK₁ : K₁ = oTwoUpper H₁) (hK₂ : K₂ = oTwoUpper H₂)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) (hθ : Gap3Theta T K₁ K₂)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hF8 : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g)
    (hZ : quasithinOmegaOneCenter T ≤ conjSub (g : G) (uHi T M H H₁))
    (hcent : K₂ ≤ Subgroup.centralizer
      (F8.A₁ (quasithinOmegaOneCenter T) (g : G) : Set G)) :
    (g : G) ∈ g2_14615 K₂ := by
  have hp : p.Prime := hred.prime
  have hH : IsHTM T M H := hred.isHTM
  have hK₂H₂ : K₂ ≤ H₂ := hK₂ ▸ oTwoUpper_le H₂
  have hgen : K₂ ≤ conjSub (g : G) (K₁ ⊔ K₂) := by
    refine hK₂.le.trans ((Subgroup.closure_le _).mpr fun y hy => ?_)
    obtain ⟨hyH, hyodd⟩ := hy
    have hyK₂ : y ∈ K₂ := hK₂ ▸ mem_oTwoUpper_of_odd hyH hyodd
    have hord : orderOf y ∣ 5 := by
      have := hdec.swap.orderOf_dvd_of_odd hp hyH hyodd
      rwa [hp5] at this
    rcases (Nat.dvd_prime (by norm_num)).mp hord with h1 | h5
    · rw [orderOf_eq_one_iff.mp h1]
      exact Subgroup.one_mem _
    · have hyC : y ∈ Subgroup.centralizer
          (F8.A₁ (quasithinOmegaOneCenter T) (g : G) : Set G) := hcent hyK₂
      have hgyG : (g : G)⁻¹ * y * (g : G) ∈ mcOf T := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hzA : (g : G) * z * (g : G)⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (g : G) :=
          mem_conjSub.mpr (by simpa [mul_assoc] using hz)
        have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hzA
        have e : z * ((g : G)⁻¹ * y * (g : G)) = (g : G)⁻¹ * (((g : G) * z * (g : G)⁻¹) * y) *
            (g : G) := by group
        have e' : ((g : G)⁻¹ * y * (g : G)) * z = (g : G)⁻¹ * (y * ((g : G) * z * (g : G)⁻¹)) *
            (g : G) := by group
        rw [e, e', h1]
      have hord' : orderOf ((g : G)⁻¹ * y * (g : G)) = 5 := by
        rw [← h5]
        have := orderOf_injective (MulAut.conj (g : G)⁻¹).toMonoidHom (MulAut.conj (g : G)⁻¹).injective y
        simpa [MulAut.conj_apply, mul_assoc] using this
      exact mem_conjSub.mpr (hθ _ hgyG hord')
  have hK'le : conjSub (g : G)⁻¹ K₂ ≤ K₁ ⊔ K₂ := by
    intro k' hk'
    have h1 : (g : G) * k' * (g : G)⁻¹ ∈ K₂ := by
      have := mem_conjSub.mp hk'
      simpa using this
    have h2 := mem_conjSub.mp (hgen h1)
    simpa [mul_assoc] using h2
  have hK'perf : oTwoUpper (conjSub (g : G)⁻¹ K₂) = conjSub (g : G)⁻¹ K₂ := by
    rw [oTwoUpper_conjSub_P, hset.perf₂]
  obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
  have hz'U : (g : G)⁻¹ * z * (g : G) ∈ uHi T M H H₁ := mem_conjSub.mp (hZ hz)
  have hz'Z : (g : G)⁻¹ * z * (g : G) ∉ quasithinOmegaOneCenter T := by
    intro hz'
    have hz'1 : (g : G)⁻¹ * z * (g : G) ≠ 1 := by
      intro h
      apply hz1
      calc z = (g : G) * ((g : G)⁻¹ * z * (g : G)) * (g : G)⁻¹ := by group
        _ = 1 := by rw [h]; group
    apply S.conj_not_mem_Z hH hF8 hz' hz'1
    have e : (g : G) * ((g : G)⁻¹ * z * (g : G)) * (g : G)⁻¹ = z := by group
    rw [e]
    exact hz
  have hcent' : ∀ k ∈ conjSub (g : G)⁻¹ K₂,
      k * ((g : G)⁻¹ * z * (g : G)) = ((g : G)⁻¹ * z * (g : G)) * k := by
    intro k hk
    have h1 : (g : G) * k * (g : G)⁻¹ ∈ K₂ := by
      have := mem_conjSub.mp hk
      simpa using this
    have h2 := S146T.comm_Z (hset.le_mcOf S hred h1) hz
    calc k * ((g : G)⁻¹ * z * (g : G)) = (g : G)⁻¹ * (((g : G) * k * (g : G)⁻¹) * z) * (g : G) := by
          group
      _ = (g : G)⁻¹ * (z * ((g : G) * k * (g : G)⁻¹)) * (g : G) := by rw [h2]
      _ = ((g : G)⁻¹ * z * (g : G)) * k := by group
  have hle := core_shapeTwo S hp hred hdec hK₁ hK₂ hK'le hK'perf hz'U hz'Z hcent'
  have heq : conjSub (g : G)⁻¹ K₂ = K₂ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_conjSub']
  have := CosetGeom.mem_normalizer_of_conjSub_eq heq
  exact (Subgroup.inv_mem_iff _).mp this

end SBc13

end CFSG.Quasithin
