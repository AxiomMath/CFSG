module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Gen
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.CZL32
open scoped commutatorElement

namespace X3324

@[expose] def rSet : Finset L3.Γ :=
  Finset.univ.filter fun g : L3.Γ => ∀ v, L3.act g v - v ∈ ({0, e1} : Finset L3.Vec)

@[expose] def tSet : Finset L3.Γ :=
  Finset.univ.filter fun g : L3.Γ => L3.act g e1 = e1 ∧ g * g * g = 1

theorem mem_rSet {g : L3.Γ} : g ∈ rSet ↔ g ∈ rSub := by
  rw [rSet, Finset.mem_filter, mem_rSub]
  simp

theorem mem_tSet {g : L3.Γ} : g ∈ tSet ↔ g ∈ L3.ptSub e1 ∧ g * g * g = 1 := by
  rw [tSet, Finset.mem_filter, L3.mem_ptSub]
  simp

theorem comm_check : ∀ γ ∈ rSet, ∃ δ ∈ rSet, ∃ τ ∈ tSet, γ = δ * τ * δ * (τ * τ) := by
  unfold rSet tSet e1
  decide +kernel

theorem sum_check : ∀ w : L3.Vec, ∃ τ₁ ∈ tSet, ∃ τ₂ ∈ tSet, ∃ u₁ u₂ : L3.Vec,
    w = (L3.act τ₁ u₁ + u₁) + (L3.act τ₂ u₂ + u₂) := by
  unfold tSet e1
  decide +kernel

theorem irr_check : ∀ w : L3.Vec, w ≠ 0 → w ≠ e1 → ∃ τ ∈ tSet, ∀ v : L3.Vec,
    v ∈ ({0, e1, w, e1 + w, L3.act τ w, L3.act τ w + e1, L3.act τ w + w,
      L3.act τ w + w + e1} : Finset L3.Vec) := by
  unfold tSet e1
  decide +kernel

theorem b2_check : (∀ v, L3.act b2 v - v ∈ ({0, e1} : Finset L3.Vec)) ∧
    L3.act b2 e2 + e2 = e1 := by
  unfold b2 e1 e2
  decide +kernel

theorem bSub_e2 : ∀ b : L3.Γ, (L3.act b e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act b v ∈ P12) →
    L3.act b e2 + e2 ∈ ({0, e1} : Finset L3.Vec) := by
  unfold P12 e1 e2
  decide +kernel

theorem move_check : ∀ w : L3.Vec, w ≠ 0 → w ≠ e1 → ∃ γ ∈ rSet, L3.act γ w ≠ w := by
  unfold rSet e1
  decide +kernel

theorem trans_check : ∀ v w : L3.Vec, v ≠ 0 → w ≠ 0 → ∃ g : L3.Γ, L3.act g v = w := by
  decide +kernel

theorem e23_check : (![0, 1, 0] : L3.Vec) ≠ 0 ∧ (![0, 1, 0] : L3.Vec) ≠ e1 ∧
    (![0, 0, 1] : L3.Vec) ≠ 0 ∧ (![0, 0, 1] : L3.Vec) ≠ e1 ∧
    (![0, 1, 0] + ![0, 0, 1] : L3.Vec) ≠ 0 ∧ (![0, 1, 0] + ![0, 0, 1] : L3.Vec) ≠ e1 := by
  unfold e1
  decide

theorem e12_check : e1 ≠ 0 ∧ e2 ≠ 0 ∧ e2 ≠ e1 := by
  unfold e1 e2
  decide

theorem vec_add_self : ∀ v : L3.Vec, v + v = 0 := by decide

theorem vec_sub_eq : ∀ v w : L3.Vec, v - w = v + w := by decide

theorem vec_neg : ∀ v : L3.Vec, -v = v := by decide

theorem vec_add_comm : ∀ v w : L3.Vec, v + w = w + v := by decide

section RhoV

variable {G : Type} [Group G] {W : Subgroup G} (β : ↥W ≃* Multiplicative L3.Vec)

@[expose] def conjW (g : ↥(Subgroup.normalizer (W : Set G))) (u : ↥W) : ↥W :=
  ⟨(g : G) * u * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 u).mp u.2⟩

theorem coe_conjW (g : ↥(Subgroup.normalizer (W : Set G))) (u : ↥W) :
    (conjW g u : G) = (g : G) * u * (g : G)⁻¹ := rfl

@[expose] def linV (g : ↥(Subgroup.normalizer (W : Set G))) (v : L3.Vec) : L3.Vec :=
  Multiplicative.toAdd (β (conjW g (β.symm (Multiplicative.ofAdd v))))

theorem exists_beta (v : L3.Vec) : ∃ u, Multiplicative.toAdd (β u) = v :=
  ⟨β.symm (Multiplicative.ofAdd v), by simp⟩

theorem linV_beta (g : ↥(Subgroup.normalizer (W : Set G))) (u : ↥W) :
    linV β g (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (conjW g u)) := by
  simp only [linV, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem linV_add (g : ↥(Subgroup.normalizer (W : Set G))) (v w : L3.Vec) :
    linV β g (v + w) = linV β g v + linV β g w := by
  obtain ⟨u, rfl⟩ := exists_beta β v
  obtain ⟨u', rfl⟩ := exists_beta β w
  rw [← toAdd_mul, ← map_mul β, linV_beta, linV_beta, linV_beta, ← toAdd_mul, ← map_mul β]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_conjW]
  group

theorem linV_mul (g h : ↥(Subgroup.normalizer (W : Set G))) (v : L3.Vec) :
    linV β (g * h) v = linV β g (linV β h v) := by
  obtain ⟨u, rfl⟩ := exists_beta β v
  rw [linV_beta, linV_beta, linV_beta]
  congr 2
  apply Subtype.ext
  simp only [coe_conjW, Subgroup.coe_mul]
  group

theorem linV_one (v : L3.Vec) : linV β 1 v = v := by
  obtain ⟨u, rfl⟩ := exists_beta β v
  rw [linV_beta]
  congr 2
  apply Subtype.ext
  simp [coe_conjW]

theorem linV_zero (g : ↥(Subgroup.normalizer (W : Set G))) : linV β g 0 = 0 := by
  have h := linV_beta β g 1
  have e : conjW g (1 : ↥W) = 1 := Subtype.ext (by simp [coe_conjW])
  rw [e, map_one] at h
  exact h

theorem linV_smul (g : ↥(Subgroup.normalizer (W : Set G))) (c : ZMod 2) (v : L3.Vec) :
    linV β g (c • v) = c • linV β g v := by
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, zero_smul, linV_zero]
  · rw [one_smul, one_smul]

@[expose] def linMapV (g : ↥(Subgroup.normalizer (W : Set G))) : L3.Vec →ₗ[ZMod 2] L3.Vec where
  toFun := linV β g
  map_add' := linV_add β g
  map_smul' := linV_smul β g

@[expose] noncomputable def matV (g : ↥(Subgroup.normalizer (W : Set G))) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  LinearMap.toMatrix' (linMapV β g)

theorem matV_mulVec (g : ↥(Subgroup.normalizer (W : Set G))) (v : L3.Vec) :
    Matrix.mulVec (matV β g) v = linV β g v := by
  rw [matV, LinearMap.toMatrix'_mulVec]
  rfl

theorem matV_mul (g h : ↥(Subgroup.normalizer (W : Set G))) :
    matV β (g * h) = matV β g * matV β h :=
  matrix_ext fun v => by
    rw [← Matrix.mulVec_mulVec, matV_mulVec, matV_mulVec, matV_mulVec, linV_mul]

theorem matV_one : matV β 1 = 1 :=
  matrix_ext fun v => by rw [matV_mulVec, linV_one, Matrix.one_mulVec]

theorem det_matV (g : ↥(Subgroup.normalizer (W : Set G))) : (matV β g).det = 1 := by
  have h : matV β g * matV β g⁻¹ = 1 := by
    rw [← matV_mul, mul_inv_cancel, matV_one]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact zmod2_eq_one _ _ h2

@[expose] noncomputable def rhoV : ↥(Subgroup.normalizer (W : Set G)) →* L3.Γ where
  toFun g := ⟨matV β g, det_matV β g⟩
  map_one' := Subtype.ext (matV_one β)
  map_mul' g h := Subtype.ext (matV_mul β g h)

theorem act_rhoV (g : ↥(Subgroup.normalizer (W : Set G))) (v : L3.Vec) :
    L3.act (rhoV β g) v = linV β g v :=
  matV_mulVec β g v

theorem rhoV_equiv (g : ↥(Subgroup.normalizer (W : Set G))) (u u' : ↥W)
    (h : (u' : G) = g * u * g⁻¹) :
    Multiplicative.toAdd (β u') = L3.act (rhoV β g) (Multiplicative.toAdd (β u)) := by
  rw [act_rhoV, linV_beta]
  congr 2
  exact Subtype.ext h

theorem toAdd_beta_mul (u u' : ↥W) : Multiplicative.toAdd (β (u * u')) =
    Multiplicative.toAdd (β u) + Multiplicative.toAdd (β u') := by
  rw [map_mul, toAdd_mul]

theorem toAdd_beta_inv (u : ↥W) :
    Multiplicative.toAdd (β u⁻¹) = Multiplicative.toAdd (β u) := by
  rw [map_inv, toAdd_inv]
  exact vec_neg _

theorem toAdd_beta_one : Multiplicative.toAdd (β 1) = 0 := by
  rw [map_one, toAdd_one]

theorem eq_of_toAdd_beta {u u' : ↥W}
    (h : Multiplicative.toAdd (β u) = Multiplicative.toAdd (β u')) : u = u' :=
  β.injective (Multiplicative.toAdd.injective h)

theorem act_rhoV_of_conj {g : ↥(Subgroup.normalizer (W : Set G))} {u : ↥W}
    (h : (g : G) * u * (g : G)⁻¹ = u) :
    L3.act (rhoV β g) (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β u) :=
  (rhoV_equiv β g u u h.symm).symm

theorem rhoV_eq_one {g : ↥(Subgroup.normalizer (W : Set G))}
    (hg : (g : G) ∈ Subgroup.centralizer (W : Set G)) : rhoV β g = 1 := by
  apply L3.act_ext
  intro v
  obtain ⟨u, rfl⟩ := exists_beta β v
  rw [L3.act_one]
  refine act_rhoV_of_conj β ?_
  have := Subgroup.mem_centralizer_iff.mp hg u u.2
  rw [← this]
  group

theorem rhoV_eq {L : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G)) (α : ↥L →* L3.Γ)
    (hβe : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = L3.act (α ℓ) (Multiplicative.toAdd (β u)))
    (ℓ : ↥L) : rhoV β ⟨ℓ, hLW ℓ.2⟩ = α ℓ := by
  apply L3.act_ext
  intro v
  obtain ⟨u, rfl⟩ := exists_beta β v
  rw [← rhoV_equiv β ⟨ℓ, hLW ℓ.2⟩ u (conjW ⟨ℓ, hLW ℓ.2⟩ u) rfl]
  exact hβe ℓ u _ rfl

@[expose] def actEquiv (σ : L3.Γ) : Multiplicative L3.Vec ≃* Multiplicative L3.Vec where
  toFun x := Multiplicative.ofAdd (L3.act σ (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (L3.act σ⁻¹ (Multiplicative.toAdd x))
  left_inv x := by simp [L3.act_inv_act]
  right_inv x := by simp [L3.act_act_inv]
  map_mul' x y := by simp [L3.act_add]

theorem toAdd_actEquiv (σ : L3.Γ) (u : ↥W) :
    Multiplicative.toAdd ((β.trans (actEquiv σ)) u) =
      L3.act σ (Multiplicative.toAdd (β u)) := rfl

theorem rhoV_twist (σ : L3.Γ) (g : ↥(Subgroup.normalizer (W : Set G))) :
    rhoV (β.trans (actEquiv σ)) g = σ * rhoV β g * σ⁻¹ := by
  apply L3.act_ext
  intro v
  obtain ⟨u, rfl⟩ := exists_beta (β.trans (actEquiv σ)) v
  rw [← rhoV_equiv _ g u (conjW g u) rfl, toAdd_actEquiv, toAdd_actEquiv,
    rhoV_equiv β g u (conjW g u) rfl, L3.act_mul, L3.act_mul, L3.act_inv_act]

end RhoV

variable {G : Type} [Group G]

theorem exists_twist {W T : Subgroup G} (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hT2 : IsPGroup 2 T) (β : ↥W ≃* Multiplicative L3.Vec) :
    ∃ σ : L3.Γ, ∀ t (ht : t ∈ T), rhoV (β.trans (actEquiv σ)) ⟨t, hTW ht⟩ ∈ bSub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥T →* L3.Γ := (rhoV β).comp (Subgroup.inclusion hTW)
  have hf : IsPGroup 2 ↥f.range := hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let P : Sylow 2 L3.Γ := isPGroup_bSub.toSylow not_two_dvd_index_bSub
  obtain ⟨Q, hQ⟩ := hf.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L3.Γ Q P
  refine ⟨g, fun t ht => ?_⟩
  have h1 : f ⟨t, ht⟩ ∈ (Q : Subgroup L3.Γ) := hQ ⟨⟨t, ht⟩, rfl⟩
  have h2 : g * f ⟨t, ht⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 _) : Subgroup L3.Γ) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, h1, rfl⟩
  rw [hg] at h2
  rw [rhoV_twist]
  exact h2

theorem image_bSub {K T : Subgroup G} (f : ↥K →* L3.Γ) (hTK : T ≤ K) (hTidx : ¬ 2 ∣ T.index)
    (hfT : ∀ t (ht : t ∈ T), f ⟨t, hTK ht⟩ ∈ bSub) (hf : Function.Surjective f) {x : L3.Γ}
    (hx : x ∈ bSub) : ∃ t, ∃ ht : t ∈ T, f ⟨t, hTK ht⟩ = x := by
  set I := (T.subgroupOf K).map f with hI
  have hle : I ≤ bSub := by
    rintro _ ⟨y, hy, rfl⟩
    exact hfT y hy
  have hodd : ¬ 2 ∣ I.index := by
    have h1 := Subgroup.index_map_dvd (T.subgroupOf K) hf
    exact fun h3 => hTidx ((h3.trans h1).trans (Subgroup.relIndex_dvd_index_of_le hTK))
  have hmul := Subgroup.card_mul_index I
  rw [card_L3Γ] at hmul
  have hdvd : Nat.card I ∣ 8 := by
    rw [← card_bSub]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨c, hc⟩ : ∃ c, Nat.card I = c := ⟨_, rfl⟩
  rw [hc] at hmul hdvd
  have hc8 : c ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hc8' : c = 8 := by interval_cases c <;> omega
  have hIeq : I = bSub := Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc8', card_bSub])
  rw [← hIeq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, hy, hyx⟩

theorem mem_qL_of_ker [Finite G] {Γ' : Type} [Group Γ'] {T L : Subgroup G}
    (ρ : ↥(L ⊔ T) →* Γ') (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : IsPGroup 2 T)
    (hL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.mem_sup_left hℓ⟩ = 1 → ℓ ∈ pCoreOf 2 L)
    (g : ↥(L ⊔ T)) (h1 : ρ g = 1) : (g : G) ∈ qL L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : IsPGroup 2 ↥(ρ.ker.map (L ⊔ T).subtype) := by
    rintro ⟨_, ⟨k', hk', rfl⟩⟩
    obtain ⟨ℓ, hℓ, t, ht, hkt⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp k'.2
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hstep : ∀ n : ℕ, ∃ ℓ' ∈ L, (ℓ * t) ^ n = ℓ' * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨ℓ', hℓ', e⟩ := ih
        refine ⟨ℓ' * (t ^ n * ℓ * (t ^ n)⁻¹), L.mul_mem hℓ' ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) ℓ).mp hℓ
        · rw [pow_succ, e]
          group
    obtain ⟨ℓ', hℓ', e⟩ := hstep (2 ^ a)
    rw [ha', mul_one] at e
    have hkL : (k' : G) ^ 2 ^ a ∈ L := by
      rw [hkt, e]
      exact hℓ'
    have h3 : ρ ⟨(k' : G) ^ 2 ^ a, Subgroup.mem_sup_left hkL⟩ = 1 := by
      have e2 : (⟨(k' : G) ^ 2 ^ a, Subgroup.mem_sup_left hkL⟩ : ↥(L ⊔ T)) = k' ^ 2 ^ a :=
        Subtype.ext (by simp)
      have hk1 : ρ k' = 1 := hk'
      rw [e2, map_pow, hk1, one_pow]
    have hker := hL _ hkL h3
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hker⟩
    have h4 : ((k' : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    refine ⟨a + b, Subtype.ext ?_⟩
    show (k' : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact h4
  have hgK : (g : G) ∈ ρ.ker.map (L ⊔ T).subtype := ⟨g, h1, rfl⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _)
    (by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective]
      infer_instance) hK2 hgK

theorem fix_T {K T : Subgroup G} (f : ↥K →* L3.Γ) (hTK : T ≤ K) (hTidx : ¬ 2 ∣ T.index)
    (hfT : ∀ t (ht : t ∈ T), f ⟨t, hTK ht⟩ ∈ bSub) (hf : Function.Surjective f) {v : L3.Vec}
    (hv : ∀ t (ht : t ∈ T), L3.act (f ⟨t, hTK ht⟩) v = v) : v = 0 ∨ v = e1 := by
  obtain ⟨t₁, ht₁, e₁⟩ := image_bSub f hTK hTidx hfT hf b1_mem
  obtain ⟨t₂, ht₂, e₂⟩ := image_bSub f hTK hTidx hfT hf b2_mem
  apply fix_B
  · rw [← e₁]
    exact hv t₁ ht₁
  · rw [← e₂]
    exact hv t₂ ht₂

theorem mem_zpowers_iff_of_sq {z g : G} (hz : z * z = 1) :
    g ∈ Subgroup.zpowers z ↔ g = 1 ∨ g = z := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h2 : z ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact hz
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (h | h)
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers z

theorem four_pow_mod (k : ℕ) : ∃ j, 4 ^ k = 3 * j + 1 := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    exact ⟨4 * j + 1, by rw [pow_succ, hj]; ring⟩

theorem exists_odd_pow [Finite G] (ℓ : G) : ∃ a : ℕ, Odd (orderOf (ℓ ^ 4 ^ a)) := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos ℓ).ne'
  refine ⟨a, Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)⟩
  have e : 4 ^ a * m = orderOf ℓ * 2 ^ a := by
    rw [hn, show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
    ring
  rw [← pow_mul, e, pow_mul, pow_orderOf_eq_one, one_pow]

section XStruct

variable [Finite G] {T M L D : Subgroup G}

open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ChiefCount Gen3324

theorem xStruct (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hWq : W ≤ qL L T)
    (hqW : qL L T ≤ Subgroup.centralizer (W : Set G)) (β : ↥W ≃* Multiplicative L3.Vec)
    (hρT : ∀ t (ht : t ∈ T), rhoV β ⟨t, hTW ht⟩ ∈ bSub)
    (hρL : ∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ L, rhoV β ⟨ℓ, hLW hℓ⟩ = γ)
    (hρK : ∀ ℓ (hℓ : ℓ ∈ L), rhoV β ⟨ℓ, hLW hℓ⟩ = 1 → ℓ ∈ pCoreOf 2 L)
    {z₀ : G} (hz₀W : z₀ ∈ W) (hz₀Z : z₀ ∈ quasithinOmegaOneCenter T) (hz₀ : z₀ ≠ 1)
    (hZ : ∀ y (hy : y ∈ L), L3.act (rhoV β ⟨y, hLW hy⟩) e1 = e1 →
      y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ∃ X : Subgroup G, oTwoUpper X = X ∧ T ≤ Subgroup.normalizer (X : Set G) ∧
      Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
      X ⊔ T = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T ∧
      X ≤ L ∧ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
      W ≤ ⁅W, X⁆ ∧ W ≤ pCoreOf 2 X ∧
      (∀ W' : Subgroup G, W' ≤ W → z₀ ∈ W' → X ≤ Subgroup.normalizer (W' : Set G) →
        (∃ w ∈ W', w ∉ Subgroup.zpowers z₀) → W ≤ W') ∧
      (∃ r₀ ∈ pCoreOf 2 X, ∃ v₀ ∈ pCoreOf 2 X, ⁅r₀, v₀⁆ = z₀) ∧
      (∃ v₁ ∈ W, v₁ ∉ Subgroup.zpowers z₀ ∧ ∀ t ∈ T, ⁅v₁, t⁆ ∈ Subgroup.zpowers z₀) ∧
      (∀ γ ∈ rSub, ∃ r ∈ ⁅pCoreOf 2 X, X⁆, ∃ hr : r ∈ L, rhoV β ⟨r, hLW hr⟩ = γ) ∧
      NCAtMost X (X ⊓ pCoreOf 2 L) X 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTW : L ⊔ T ≤ Subgroup.normalizer (W : Set G) := sup_le hLW hTW
  have hconjW : ∀ {g : G}, g ∈ Subgroup.normalizer (W : Set G) → ∀ {u : G}, u ∈ W →
      g * u * g⁻¹ ∈ W := fun hg u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hcz : ∀ t ∈ T, t * z₀ * t⁻¹ = z₀ := fun t ht => by
    have := Subgroup.mem_centralizer_iff.mp (hTZ ht) z₀ hz₀Z
    rw [← this]
    group
  have hsurj : Function.Surjective (rhoV β) := fun γ => by
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨_, e⟩
  have hW2 : ∀ w ∈ W, w * w = 1 := fun w hw => by
    have := eq_of_toAdd_beta β (u := ⟨w, hw⟩ * ⟨w, hw⟩) (u' := 1)
      (by rw [toAdd_beta_mul, toAdd_beta_one, vec_add_self])
    exact congrArg Subtype.val this
  have hWp : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
    exact hW2 w w.2)⟩
  have hθz : Multiplicative.toAdd (β ⟨z₀, hz₀W⟩) = e1 := by
    rcases fix_T (rhoV β) hTW hTidx hρT hsurj (v := Multiplicative.toAdd (β ⟨z₀, hz₀W⟩))
        (fun t ht => act_rhoV_of_conj β (g := ⟨t, hTW ht⟩) (u := ⟨z₀, hz₀W⟩) (hcz t ht))
      with h0 | h1
    · exact absurd (congrArg Subtype.val (eq_of_toAdd_beta β (u := ⟨z₀, hz₀W⟩) (u' := 1)
        (by rw [toAdd_beta_one]; exact h0))) hz₀
    · exact h1
  set ρ : ↥(L ⊔ T) →* L3.Γ := (rhoV β).comp (Subgroup.inclusion hLTW) with hρdef
  have hsurjK : ∀ γ, ∃ k : ↥(L ⊔ T), ρ k = γ := fun γ => by
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have htop : ρ.range = ⊤ := eq_top_iff.mpr fun γ _ => MonoidHom.mem_range.mpr (hsurjK γ)
  have h6 : Nat.card ↥(ρ.range ⊓ L3.ptSub e1) = 6 * Nat.card ↥(ρ.range ⊓ rSub) := by
    rw [htop, top_inf_eq, top_inf_eq, card_ptSub, card_rSub]
  obtain ⟨ka, ea⟩ := hsurjK aW
  obtain ⟨kb, eb⟩ := hsurjK bW
  have hρK' : ∀ g : ↥(L ⊔ T), ρ g = 1 → (g : G) ∈ pCoreOf 2 (L ⊔ T) :=
    fun g hg => mem_qL_of_ker ρ hTL hT2 (fun ℓ hℓ h1 => hρK ℓ hℓ h1) g hg
  obtain ⟨hXX, hTX, hXT, ⟨eS3⟩, hO2, -⟩ := parabolic_gen₀ ρ le_sup_right hT2 hTidx hρK'
    (p := L3.ptSub e1) (r := rSub) (fun t ht => bSub_le_ptSub (hρT t ht)) rSub_le_ptSub
    ptSub_le_normalizer (fun x hx => sq_eq_one_of_mem_rSub hx) h6 (ka := ka) (kb := kb)
    (by rw [ea]; exact aW_mem) (by rw [eb]; exact bW_mem) (by rw [ea, eb]; exact comm_not_mem)
  set P := pre₀ ρ (L3.ptSub e1) with hP
  set R := pre₀ ρ rSub with hR
  set X := oTwoUpper P with hX
  have hXP : X ≤ P := oTwoUpper_le P
  have hPLT : P ≤ L ⊔ T := pre₀_le ρ _
  have hmemP : ∀ {g : G} (hg : g ∈ L ⊔ T), rhoV β ⟨g, hLTW hg⟩ ∈ L3.ptSub e1 → g ∈ P :=
    fun hg h1 => (mem_pre₀ ρ).mpr ⟨hg, h1⟩
  have hmemR : ∀ {g : G} (hg : g ∈ L ⊔ T), rhoV β ⟨g, hLTW hg⟩ ∈ rSub → g ∈ R :=
    fun hg h1 => (mem_pre₀ ρ).mpr ⟨hg, h1⟩
  have hTP : T ≤ P := fun t ht => hmemP (Subgroup.mem_sup_right ht) (bSub_le_ptSub (hρT t ht))
  have hRP : R ≤ P := pre₀_mono ρ rSub_le_ptSub
  have hPN : P ≤ Subgroup.normalizer (R : Set G) := pre₀_le_normalizer ρ ptSub_le_normalizer
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := le_normalizer_oTwoUpper P
  have hR2 : IsPGroup 2 R := by
    rw [← hO2]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hoddP : ∀ x ∈ P, Odd (orderOf x) → x ∈ L ⊓ Subgroup.centralizer (Z : Set G) := by
    intro x hx ho
    obtain ⟨hxLT, hxp⟩ := (mem_pre₀ ρ).mp hx
    have hxL : x ∈ L := One3323.mem_of_odd hT2 hTL hxLT ho
    exact ⟨hxL, hZ x hxL hxp⟩
  have hXLZ : X ≤ L ⊓ Subgroup.centralizer (Z : Set G) := by
    rw [hX, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hx, ho⟩
    exact hoddP x hx ho
  have hXL : X ≤ L := hXLZ.trans inf_le_left
  have hXZ : X ≤ Subgroup.centralizer (Z : Set G) := hXLZ.trans inf_le_right
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := hXL.trans hLW
  have hLZP : L ⊓ Subgroup.centralizer (Z : Set G) ≤ P := by
    rintro y ⟨hyL, hyZ⟩
    refine hmemP (Subgroup.mem_sup_left hyL) ?_
    rw [L3.mem_ptSub, ← hθz]
    refine act_rhoV_of_conj β (g := ⟨y, hLTW (Subgroup.mem_sup_left hyL)⟩)
      (u := ⟨z₀, hz₀W⟩) ?_
    have := Subgroup.mem_centralizer_iff.mp hyZ z₀ hz₀Z
    show y * z₀ * y⁻¹ = z₀
    rw [← this]
    group
  have hXTe : X ⊔ T = L ⊓ Subgroup.centralizer (Z : Set G) ⊔ T :=
    le_antisymm (sup_le_sup_right hXLZ T) (by rw [hXT]; exact sup_le hLZP hTP)
  have hS3 : Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)) :=
    Par32.nonempty_quot_pCore_congr hXT ⟨eS3⟩
  have hqR : ∀ x ∈ qL L T, x ∈ R := fun x hx => hmemR (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
    (by
      rw [rhoV_eq_one β (g := ⟨x, hLTW (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)⟩) (hqW hx)]
      exact rSub.one_mem)
  have hWR : W ≤ R := fun w hw => hqR w (hWq hw)
  have hOR : pCoreOf 2 L ≤ R := fun x hx => hqR x
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T)
      le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL)) hx)
  have hlift3 : ∀ τ ∈ tSet, ∃ x ∈ X, ∃ hx : x ∈ L, rhoV β ⟨x, hLW hx⟩ = τ := by
    intro τ hτ
    obtain ⟨hτp, hτ3⟩ := mem_tSet.mp hτ
    obtain ⟨ℓ, hℓ, e⟩ := hρL τ
    obtain ⟨a, ha⟩ := exists_odd_pow ℓ
    have hxL : ℓ ^ 4 ^ a ∈ L := L.pow_mem hℓ _
    have hρx : rhoV β ⟨ℓ ^ 4 ^ a, hLW hxL⟩ = τ := by
      have e1' : (⟨ℓ ^ 4 ^ a, hLW hxL⟩ : ↥(Subgroup.normalizer (W : Set G))) =
          ⟨ℓ, hLW hℓ⟩ ^ 4 ^ a := Subtype.ext (by simp)
      obtain ⟨j, hj⟩ := four_pow_mod a
      have h3 : τ ^ 3 = 1 := by
        rw [pow_succ, pow_two]
        exact hτ3
      rw [e1', map_pow, e, hj, pow_succ, pow_mul, h3, one_pow, one_mul]
    refine ⟨ℓ ^ 4 ^ a, mem_oTwoUpper_of_odd (hmemP (Subgroup.mem_sup_left hxL) ?_) ha, hxL, hρx⟩
    show rhoV β ⟨ℓ ^ 4 ^ a, hLW hxL⟩ ∈ L3.ptSub e1
    rw [hρx]
    exact hτp
  have hliftR : ∀ δ ∈ rSub, ∃ d ∈ R, ∃ hd : d ∈ L, rhoV β ⟨d, hLW hd⟩ = δ := by
    intro δ hδ
    obtain ⟨ℓ, hℓ, e⟩ := hρL δ
    refine ⟨ℓ, hmemR (Subgroup.mem_sup_left hℓ) ?_, hℓ, e⟩
    show rhoV β ⟨ℓ, hLW hℓ⟩ ∈ rSub
    rw [e]
    exact hδ
  have hXR2 : X ⊓ R ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (hPN (hXP hx)))
      (hR2.to_le inf_le_right)
  have hρcomm : ∀ (d x : G) (hd : d ∈ L) (hx : x ∈ L) (hdx : ⁅d, x⁆ ∈ L) {δ τ : L3.Γ},
      δ ∈ rSub → τ ∈ tSet → rhoV β ⟨d, hLW hd⟩ = δ → rhoV β ⟨x, hLW hx⟩ = τ →
        rhoV β ⟨⁅d, x⁆, hLW hdx⟩ = δ * τ * δ * (τ * τ) := by
    intro d x hd hx hdx δ τ hδ hτ ed ex
    have e : (⟨⁅d, x⁆, hLW hdx⟩ : ↥(Subgroup.normalizer (W : Set G))) =
        ⟨d, hLW hd⟩ * ⟨x, hLW hx⟩ * (⟨d, hLW hd⟩)⁻¹ * (⟨x, hLW hx⟩)⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    have hδ2 := sq_eq_one_of_mem_rSub hδ
    have hτ3 : τ * (τ * τ) = 1 := by
      rw [← mul_assoc]
      exact (mem_tSet.mp hτ).2
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ed, ex,
      inv_eq_of_mul_eq_one_right hδ2, inv_eq_of_mul_eq_one_right hτ3]
  have hcommL : ∀ {d x : G}, d ∈ L → x ∈ L → ⁅d, x⁆ ∈ L := fun hd hx => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hd hx) (L.inv_mem hd)) (L.inv_mem hx)
  have hliftO : ∀ γ ∈ rSub, ∃ o ∈ pCoreOf 2 X, ∃ ho : o ∈ L, rhoV β ⟨o, hLW ho⟩ = γ := by
    intro γ hγ
    obtain ⟨δ, hδ, τ, hτ, rfl⟩ := comm_check γ (mem_rSet.mpr hγ)
    obtain ⟨d, hdR, hdL, ed⟩ := hliftR δ (mem_rSet.mp hδ)
    obtain ⟨x, hxX, hxL, ex⟩ := hlift3 τ hτ
    have hoX : ⁅d, x⁆ ∈ X := by
      rw [commutatorElement_def]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPX (hRP hdR)) x).mp hxX) (X.inv_mem hxX)
    have hoR : ⁅d, x⁆ ∈ R := by
      have e : ⁅d, x⁆ = d * (x * d⁻¹ * x⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact R.mul_mem hdR ((Subgroup.mem_normalizer_iff.mp (hPN (hXP hxX)) d⁻¹).mp
        (R.inv_mem hdR))
    exact ⟨⁅d, x⁆, hXR2 ⟨hoX, hoR⟩, hcommL hdL hxL,
      hρcomm d x hdL hxL (hcommL hdL hxL) (mem_rSet.mp hδ) hτ ed ex⟩
  have hliftC : ∀ γ ∈ rSub, ∃ r ∈ ⁅pCoreOf 2 X, X⁆, ∃ hr : r ∈ L, rhoV β ⟨r, hLW hr⟩ = γ := by
    intro γ hγ
    obtain ⟨δ, hδ, τ, hτ, rfl⟩ := comm_check γ (mem_rSet.mpr hγ)
    obtain ⟨o, hoO, hoL, eo⟩ := hliftO δ (mem_rSet.mp hδ)
    obtain ⟨x, hxX, hxL, ex⟩ := hlift3 τ hτ
    exact ⟨⁅o, x⁆, Subgroup.commutator_mem_commutator hoO hxX, hcommL hoL hxL,
      hρcomm o x hoL hxL (hcommL hoL hxL) (mem_rSet.mp hδ) hτ eo ex⟩
  have hWXc : W ≤ ⁅W, X⁆ := by
    intro w hw
    obtain ⟨τ₁, hτ₁, τ₂, hτ₂, u₁, u₂, hsum⟩ := sum_check (Multiplicative.toAdd (β ⟨w, hw⟩))
    obtain ⟨x₁, hx₁X, hx₁L, ex₁⟩ := hlift3 τ₁ hτ₁
    obtain ⟨x₂, hx₂X, hx₂L, ex₂⟩ := hlift3 τ₂ hτ₂
    have hcomm : ∀ (x : G) (hxX : x ∈ X) (hxL : x ∈ L) (u : L3.Vec), ∃ c ∈ ⁅W, X⁆,
        ∃ hc : c ∈ W, Multiplicative.toAdd (β ⟨c, hc⟩) = L3.act (rhoV β ⟨x, hLW hxL⟩) u + u := by
      intro x hxX hxL u
      obtain ⟨wu, hwu⟩ := exists_beta β u
      have h1 : x * (wu : G) * x⁻¹ ∈ W := hconjW (hLW hxL) wu.2
      refine ⟨x * wu * x⁻¹ * (wu : G)⁻¹, ?_, W.mul_mem h1 (W.inv_mem wu.2), ?_⟩
      · rw [Subgroup.commutator_comm]
        have := Subgroup.commutator_mem_commutator hxX wu.2
        rwa [commutatorElement_def] at this
      · have e : (⟨x * wu * x⁻¹ * (wu : G)⁻¹, W.mul_mem h1 (W.inv_mem wu.2)⟩ : ↥W) =
            ⟨_, h1⟩ * wu⁻¹ := rfl
        rw [e, toAdd_beta_mul, toAdd_beta_inv, rhoV_equiv β ⟨x, hLW hxL⟩ wu ⟨_, h1⟩ rfl, hwu]
    obtain ⟨c₁, hc₁, hc₁W, e₁⟩ := hcomm x₁ hx₁X hx₁L u₁
    obtain ⟨c₂, hc₂, hc₂W, e₂⟩ := hcomm x₂ hx₂X hx₂L u₂
    have hwc : (⟨w, hw⟩ : ↥W) = ⟨c₁, hc₁W⟩ * ⟨c₂, hc₂W⟩ := by
      apply eq_of_toAdd_beta β
      rw [toAdd_beta_mul, e₁, e₂, ex₁, ex₂, hsum]
    have hw' : w = c₁ * c₂ := congrArg Subtype.val hwc
    rw [hw']
    exact Subgroup.mul_mem _ hc₁ hc₂
  have hWX : W ≤ X :=
    hWXc.trans (commutator_le_right_of_le_normalizer fun w hw => hPX (hRP (hWR hw)))
  have hWO : W ≤ pCoreOf 2 X := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWX hXW hWp
  have hz2 : z₀ * z₀ = 1 := hW2 z₀ hz₀W
  have hirr : ∀ W' : Subgroup G, W' ≤ W → z₀ ∈ W' → X ≤ Subgroup.normalizer (W' : Set G) →
      (∃ w ∈ W', w ∉ Subgroup.zpowers z₀) → W ≤ W' := by
    rintro W' hW'W hz₀' hXW' ⟨w, hw', hwz⟩
    have hwW := hW'W hw'
    rw [mem_zpowers_iff_of_sq hz2, not_or] at hwz
    have hw0 : Multiplicative.toAdd (β ⟨w, hwW⟩) ≠ 0 := fun h0 => hwz.1 (congrArg Subtype.val
      (eq_of_toAdd_beta β (u := ⟨w, hwW⟩) (u' := 1) (by rw [toAdd_beta_one]; exact h0)))
    have hwe : Multiplicative.toAdd (β ⟨w, hwW⟩) ≠ e1 := fun h1 => hwz.2 (congrArg Subtype.val
      (eq_of_toAdd_beta β (u := ⟨w, hwW⟩) (u' := ⟨z₀, hz₀W⟩) (by rw [hθz]; exact h1)))
    obtain ⟨τ, hτ, hall⟩ := irr_check _ hw0 hwe
    obtain ⟨x, hxX, hxL, ex⟩ := hlift3 τ hτ
    have hxw : x * w * x⁻¹ ∈ W' := (Subgroup.mem_normalizer_iff.mp (hXW' hxX) w).mp hw'
    have hxwW : x * w * x⁻¹ ∈ W := hconjW (hLW hxL) hwW
    let S : Set L3.Vec := {v | ∃ u : ↥W, (u : G) ∈ W' ∧ Multiplicative.toAdd (β u) = v}
    have hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
      exact ⟨u * u', W'.mul_mem hu hu', toAdd_beta_mul β u u'⟩
    have h0 : (0 : L3.Vec) ∈ S := ⟨1, W'.one_mem, toAdd_beta_one β⟩
    have he : e1 ∈ S := ⟨⟨z₀, hz₀W⟩, hz₀', hθz⟩
    have hwS : Multiplicative.toAdd (β ⟨w, hwW⟩) ∈ S := ⟨_, hw', rfl⟩
    have hτS : L3.act τ (Multiplicative.toAdd (β ⟨w, hwW⟩)) ∈ S :=
      ⟨⟨_, hxwW⟩, hxw, by rw [← ex]; exact rhoV_equiv β ⟨x, hLW hxL⟩ ⟨w, hwW⟩ ⟨_, hxwW⟩ rfl⟩
    intro v hv
    have hvS : Multiplicative.toAdd (β ⟨v, hv⟩) ∈ S := by
      have hmem := hall (Multiplicative.toAdd (β ⟨v, hv⟩))
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h | h | h | h | h <;> rw [h]
      · exact h0
      · exact he
      · exact hwS
      · exact hS _ he _ hwS
      · exact hτS
      · exact hS _ hτS _ he
      · exact hS _ hτS _ hwS
      · exact hS _ (hS _ hτS _ hwS) _ he
    obtain ⟨u, hu, hue⟩ := hvS
    have huv : (u : G) = v := congrArg Subtype.val (eq_of_toAdd_beta β hue)
    rw [← huv]
    exact hu
  obtain ⟨r₀, hr₀O, hr₀L, er₀⟩ := hliftO b2 (mem_rSub.mpr b2_check.1)
  obtain ⟨v₀, hv₀e⟩ := exists_beta β e2
  have hcz₀ : ⁅r₀, (v₀ : G)⁆ = z₀ := by
    have h1 : r₀ * v₀ * r₀⁻¹ ∈ W := hconjW (hLW hr₀L) v₀.2
    have e : (⟨⁅r₀, (v₀ : G)⁆, W.mul_mem h1 (W.inv_mem v₀.2)⟩ : ↥W) = ⟨_, h1⟩ * v₀⁻¹ := rfl
    have := eq_of_toAdd_beta β (u := ⟨⁅r₀, (v₀ : G)⁆, W.mul_mem h1 (W.inv_mem v₀.2)⟩)
      (u' := ⟨z₀, hz₀W⟩) (by
        rw [e, toAdd_beta_mul, toAdd_beta_inv, rhoV_equiv β ⟨r₀, hLW hr₀L⟩ v₀ ⟨_, h1⟩ rfl, er₀,
          hv₀e, hθz]
        exact b2_check.2)
    exact congrArg Subtype.val this
  have hv₀z : (v₀ : G) ∉ Subgroup.zpowers z₀ := by
    rw [mem_zpowers_iff_of_sq hz2, not_or]
    refine ⟨fun h1 => e12_check.2.1 ?_, fun h1 => e12_check.2.2 ?_⟩
    · rw [← hv₀e, show v₀ = 1 from Subtype.ext h1, toAdd_beta_one]
    · rw [← hv₀e, ← hθz, show v₀ = ⟨z₀, hz₀W⟩ from Subtype.ext h1]
  have hv₁T : ∀ t ∈ T, ⁅(v₀ : G), t⁆ ∈ Subgroup.zpowers z₀ := by
    intro t ht
    rw [mem_zpowers_iff_of_sq hz2]
    have h1 : t * v₀ * t⁻¹ ∈ W := hconjW (hTW ht) v₀.2
    have e : ⁅(v₀ : G), t⁆ = ((v₀ * (⟨_, h1⟩ : ↥W)⁻¹ : ↥W) : G) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hc : Multiplicative.toAdd (β (v₀ * (⟨_, h1⟩ : ↥W)⁻¹)) ∈ ({0, e1} : Finset L3.Vec) := by
      rw [toAdd_beta_mul, toAdd_beta_inv, rhoV_equiv β ⟨t, hTW ht⟩ v₀ ⟨_, h1⟩ rfl, hv₀e,
        vec_add_comm]
      exact bSub_e2 _ (mem_bSub.mp (hρT t ht))
    rw [e]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h0 | h1'
    · left
      rw [eq_of_toAdd_beta β (u := v₀ * (⟨_, h1⟩ : ↥W)⁻¹) (u' := 1)
        (by rw [toAdd_beta_one]; exact h0)]
      rfl
    · right
      rw [eq_of_toAdd_beta β (u := v₀ * (⟨_, h1⟩ : ↥W)⁻¹) (u' := ⟨z₀, hz₀W⟩)
        (by rw [hθz]; exact h1')]
  have hXRn : X ≤ Subgroup.normalizer ((X ⊓ R : Subgroup G) : Set G) := fun x hx =>
    ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (hPN (hXP hx))
  have s4 : NCAtMost X (X ⊓ pCoreOf 2 L) (X ⊓ R) 1 := by
    refine ncAtMost_of_relIndex_lt (lt_of_le_of_lt ?_ (by norm_num : (4 : ℕ) < 4 ^ (1 + 1)))
    have hN : X ⊓ R ≤ L ⊔ T := fun x hx => hPLT (hXP hx.1)
    let f : ↥(X ⊓ R) →* L3.Γ := ρ.comp (Subgroup.inclusion hN)
    have hfr : f.range ≤ rSub := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨hx', hxr⟩ := (mem_pre₀ ρ).mp x.2.2
      exact hxr
    have hfk : f.ker ≤ (X ⊓ pCoreOf 2 L).subgroupOf (X ⊓ R) := by
      intro x hx
      exact ⟨x.2.1, hρK x (hXL x.2.1) hx⟩
    calc (X ⊓ pCoreOf 2 L).relIndex (X ⊓ R)
        ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hfk)
      _ = Nat.card f.range := Subgroup.index_ker f
      _ ≤ Nat.card rSub := Subgroup.card_le_of_le hfr
      _ = 4 := card_rSub
  have s5 : NCAtMost X (X ⊓ R) X 0 := by
    let ψ : ↥P →* Equiv.Perm (Fin 3) :=
      eS3.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
    have hsign : ∀ x (hx : x ∈ X), Equiv.Perm.sign (ψ ⟨x, hXP hx⟩) = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        apply One3323.sign_eq_one_of_odd
        refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ψ _)
        rw [Subgroup.orderOf_mk]
        exact hy.2
      | one =>
        show Equiv.Perm.sign (ψ 1) = 1
        rw [map_one, map_one]
      | mul y z hy hz ihy ihz =>
        have e1 : (⟨y * z, hXP (Subgroup.mul_mem _ hy hz)⟩ : ↥P) = ⟨y, hXP hy⟩ * ⟨z, hXP hz⟩ :=
          rfl
        rw [e1, map_mul, map_mul, ihy, ihz, mul_one]
      | inv y hy ihy =>
        have e1 : (⟨y⁻¹, hXP (Subgroup.inv_mem _ hy)⟩ : ↥P) = (⟨y, hXP hy⟩ : ↥P)⁻¹ := rfl
        rw [e1, map_inv, map_inv, ihy, inv_one]
    refine One3323.ncAtMost_zero_top_of_three ψ hXP
      (fun x hx => One3323.pow_three_of_sign _ (hsign x hx)) fun x hx h1 => ⟨hx, ?_⟩
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨x, hXP hx⟩ = 1 :=
      (map_eq_one_iff eS3.toMonoidHom eS3.injective).mp h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    rw [← hO2]
    exact (Lem3328.mem_pCore_iff _).mp h2
  exact ⟨X, hXX, hTX, hS3, hXTe, hXL, hXZ, hWXc, hWO, hirr, ⟨r₀, hr₀O, v₀, hWO v₀.2, hcz₀⟩,
    ⟨v₀, v₀.2, hv₀z, hv₁T⟩, hliftC, s4.add s5 (inf_le_inf_left X hOR) inf_le_left le_rfl hXRn⟩

end XStruct

end X3324

end CFSG.Quasithin.H13
