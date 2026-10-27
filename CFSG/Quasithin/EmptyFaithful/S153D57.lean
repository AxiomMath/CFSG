module

public import CFSG.Quasithin.EmptyFaithful.S153D56

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

section ConjPerm

variable {G : Type} [Group G]

abbrev NeV (V : Subgroup G) : Type := {v : G // v ∈ V ∧ v ≠ 1}

@[expose] noncomputable def conjPermNe (V X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    ↥X →* Equiv.Perm (NeV V) where
  toFun x :=
    { toFun := fun v => ⟨x * v.1 * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hX x.2) v.1).mp v.2.1,
        fun h => v.2.2 (by
          have := congrArg (fun w => (x : G)⁻¹ * w * x) h
          simpa [mul_assoc] using this)⟩
      invFun := fun v => ⟨(x : G)⁻¹ * v.1 * x,
        (Subgroup.mem_normalizer_iff.mp (hX (X.inv_mem x.2)) v.1).mp v.2.1 |> fun h => by
          simpa using h,
        fun h => v.2.2 (by
          have := congrArg (fun w => (x : G) * w * (x : G)⁻¹) h
          simpa [mul_assoc] using this)⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc]) }
  map_one' := Equiv.ext fun v => Subtype.ext (by simp)
  map_mul' := fun x y => Equiv.ext fun v => Subtype.ext (by simp [mul_assoc])

theorem conjPermNe_apply_coe (V X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (x : ↥X) (v : NeV V) : ((conjPermNe V X hX x v : NeV V) : G) = x * v.1 * (x : G)⁻¹ := rfl

theorem conjPermNe_eq_one_iff (V X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (x : ↥X) : conjPermNe V X hX x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]; simp
    · have h1 := congrArg (fun p : Equiv.Perm (NeV V) => ((p ⟨v, hv, hv1⟩ : NeV V) : G)) h
      simp only [conjPermNe_apply_coe, Equiv.Perm.coe_one] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
  · intro h
    refine Equiv.ext fun v => Subtype.ext ?_
    rw [conjPermNe_apply_coe, Equiv.Perm.coe_one, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp h v.1 v.2.1).symm

end ConjPerm

section Generic
variable {G : Type} [Group G]

theorem card_NeV_of_card_four [Finite G] {V : Subgroup G} (h : Nat.card V = 4) :
    Nat.card (NeV V) = 3 := by
  have e : NeV V ≃ {u : ↥V // u ≠ 1} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, fun h1 => v.2.2 (congrArg Subtype.val h1)⟩
      invFun := fun u => ⟨u.1.1, u.1.2, fun h1 => u.2 (Subtype.ext h1)⟩
      left_inv := fun v => rfl
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  classical
  have : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Nat.card_eq_fintype_card] at h
  omega

set_option maxRecDepth 100000 in
theorem perm3_key : ∀ m : Equiv.Perm (Fin 3), m ≠ 1 → m ^ 2 = 1 →
    ∃ c : Equiv.Perm (Fin 3), (m * c * m⁻¹ * c⁻¹) ^ 3 = 1 ∧ m * c * m⁻¹ * c⁻¹ ≠ 1 := by
  decide

theorem perm3_pow_six : ∀ m : Equiv.Perm (Fin 3), m ^ 6 = 1 := by decide

theorem eq_bot_of_normal_two_group (N : Subgroup (Equiv.Perm (Fin 3))) (hN : N.Normal)
    (h2 : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k = 1) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_contra hn1
  obtain ⟨k, hk⟩ := h2 n hn
  have h6 : n ^ 6 = 1 := perm3_pow_six n
  have hsq : n ^ 2 = 1 := by
    have hd : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have hd6 : 2 ^ j ∣ 6 := hj ▸ orderOf_dvd_of_pow_eq_one h6
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have h46 : 4 ∣ 6 := by simpa using h4.trans hd6
      omega
    interval_cases j
    · exact absurd (orderOf_eq_one_iff.mp hj) hn1
    · have := pow_orderOf_eq_one n
      rwa [hj, pow_one] at this
  obtain ⟨c, hc3, hc1⟩ := perm3_key n hn1 hsq
  have hcN : n * c * n⁻¹ * c⁻¹ ∈ N := by
    have h1 : c * n * c⁻¹ ∈ N := hN.conj_mem n hn c
    have h2' : n * (c * n * c⁻¹)⁻¹ ∈ N := N.mul_mem hn (N.inv_mem h1)
    have e : n * c * n⁻¹ * c⁻¹ = n * (c * n * c⁻¹)⁻¹ := by group
    rw [e]
    exact h2'
  obtain ⟨k', hk'⟩ := h2 _ hcN
  have hd3 : orderOf (n * c * n⁻¹ * c⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have hd2 : orderOf (n * c * n⁻¹ * c⁻¹) ∣ 2 ^ k' := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k') := Nat.Coprime.pow_right _ (by norm_num)
  exact hc1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd3 hd2))

end Generic

end S153D

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_mem_Sgp153_nontrivial_V₂ (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ∃ s ∈ Sgp153 T V₁, ∃ u ∈ V₂, s * u * s⁻¹ ≠ u := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := D.model
  by_contra hcon
  push Not at hcon
  have hT' : IsSylowTwoOf (autI hV T) (autI hV M) := h.isSylowTwoOf_autI
  have hcard : Nat.card ↥(autI hV T ⊓ (L₁ ⊔ L₂)) = 4 := hS.card_S hT'
  have hle : autI hV T ⊓ (L₁ ⊔ L₂) ≤ L₁ := by
    intro σ hσ
    obtain ⟨hσT, hσL⟩ := hσ
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hV).1 hσT
    have hg1 : (g : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
      rw [hV₁]
      exact (mem_normalizer_map_inclMod_iff hV g.2 (commV L₁)).2 (hS.sup_le_stab₁ hσL)
    have hgS : (g : G) ∈ Sgp153 T V₁ := ⟨hgT, hg1⟩
    have hσM : convI hV g ∈ autI hV M := by
      have := convI_mem_autI hV (h.T_le hgT) g.2
      simpa using this
    refine (hS.mem_L₁_iff hσM).2 fun u hu => ?_
    apply IntMod.val_injective
    rw [convI_apply_val]
    have hu2 : u.val ∈ V₂ := by
      rw [hV₂]
      exact ⟨u, hu, rfl⟩
    exact hcon g hgS u.val hu2
  have hdvd : 4 ∣ 6 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard, hS.card_L₁] at this
  omega

end Hyp153

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_Yplus_fpf (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    ∃ y ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)),
      y ^ 3 ∈ Subgroup.centralizer (V₂ : Set G) ∧ ∀ u ∈ V₂, u ≠ 1 → y * u * y⁻¹ ≠ u := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, y, hy, hyY, hyL, hyord⟩ := h.exists_mem_Yplus_acts h113 D
  refine ⟨y, hyY, ?_, ?_⟩
  · have h3 : convI hV ⟨y, hy⟩ ^ 3 = 1 := by
      rw [← hyord]
      exact pow_orderOf_eq_one _
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [hV₂] at hv
    obtain ⟨w, hw, rfl⟩ := (mem_map_inclMod_iff hV).1 hv
    have h4 : (convI hV (⟨y, hy⟩ ^ 3) w).val = w.val := by
      rw [map_pow, h3]
      rfl
    rw [convI_apply_val] at h4
    have h5 : y ^ 3 * w.val = w.val * y ^ 3 := by
      have h6 : y ^ 3 * w.val * (y ^ 3)⁻¹ = w.val := h4
      calc y ^ 3 * w.val = (y ^ 3 * w.val * (y ^ 3)⁻¹) * y ^ 3 := by group
        _ = w.val * y ^ 3 := by rw [h6]
    exact h5.symm
  · set x' := convI hV ⟨y, hy⟩ with hx'
    have hx'odd : Odd (orderOf x') := by rw [hyord]; decide
    have hx'1 : x' ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hyord
      exact absurd hyord (by norm_num)
    have hfpf : ∀ u ∈ commV L₂, u ≠ 1 → x' u ≠ u := fun u hu hu1 hxu =>
      hx'1 (eq_one_of_odd_of_fixed hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hyL hx'odd hu
        hu1 hxu)
    intro u hu hu1 hyu
    rw [hV₂] at hu
    obtain ⟨w, hw, rfl⟩ := (mem_map_inclMod_iff hV).1 hu
    refine hfpf w hw (fun hw1 => hu1 (by rw [hw1]; rfl)) (IntMod.val_injective ?_)
    rw [hx', convI_apply_val]
    exact hyu

end Hyp153

namespace Hyp15310

open S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem Yp_le_normalizer_V₂ (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (h2 : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) :
    Yp ≤ Subgroup.normalizer (V₂ : Set G) := by
  have hMN : M ⊓ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (V₂ : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right (VZ T M)
      (M ⊓ Subgroup.centralizer (V₁ : Set G))
    rwa [h.decomp.comm₂] at this
  rw [h2]
  exact ((oTwoUpper_le _).trans (inf_le_inf_right _ (Y153_le Mc M))).trans hMN

theorem s3_and_R_of_pRank_one (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hr : CFSG.Open.pRank 3 Yp = 1) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    (∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
        φ.ker = (R153 T V₁ Yp).subgroupOf (Yp ⊔ Sgp153 T V₁)) ∧
      R153 T V₁ Yp = Sgp153 T V₁ ⊓ Subgroup.centralizer (V₂ : Set G) := by
  have hF := h.lemma_15_3_11_one h11 h113 hI
  have h2 := h.case_two_of_pRank_one h113 hr
  have hYpY : Yp ≤ Y153 Mc M := h.Yp_le_Y153
  have hSN₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    h.hyp.Sgp153_le_normalizer_V₂ h.decomp
  have hYN₂ : Yp ≤ Subgroup.normalizer (V₂ : Set G) := Yp_le_normalizer_V₂ h h2.2
  have hXN₂ : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) := sup_le hYN₂ hSN₂
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := Sgp153_le_normalizer_Yp h
  have hS2 : IsPGroup 2 (Sgp153 T V₁) := h.hyp.qtfe.sylow.1.to_le inf_le_left
  have hSylX : IsSylowTwoOf (Sgp153 T V₁) (Yp ⊔ Sgp153 T V₁) :=
    A4.isSylowTwoOf_mono hF le_sup_right hI.1.1
  have hcard3 : Nat.card (NeV V₂) = 3 := card_NeV_of_card_four h.decomp.card₂
  let e : NeV V₂ ≃ Fin 3 := (Finite.equivFin (NeV V₂)).trans (finCongr hcard3)
  let φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (conjPermNe V₂ (Yp ⊔ Sgp153 T V₁) hXN₂)
  have hφ1 : ∀ x : ↥(Yp ⊔ Sgp153 T V₁), φ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro x
    rw [← conjPermNe_eq_one_iff V₂ (Yp ⊔ Sgp153 T V₁) hXN₂ x]
    show (Equiv.permCongrHom e) (conjPermNe V₂ (Yp ⊔ Sgp153 T V₁) hXN₂ x) = 1 ↔ _
    exact MulEquiv.map_eq_one_iff _
  obtain ⟨y, hyY, hy3, hyfpf⟩ := h.hyp.exists_Yplus_fpf h113 h.decomp
  have hyYp : y ∈ Yp := by rw [h2.2]; exact hyY
  have hyX : y ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_left hyYp
  obtain ⟨s, hsS, u₀, hu₀, hsu₀⟩ := h.hyp.exists_mem_Sgp153_nontrivial_V₂ h.decomp
  have hsX : s ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_right hsS
  have hV₂ne : ∃ u ∈ V₂, u ≠ 1 := by
    have hne : V₂ ≠ ⊥ := by
      intro hb
      have := h.decomp.card₂
      rw [hb, Subgroup.card_bot] at this
      omega
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨u, hu, fun h1 => hu1 (Subtype.ext h1)⟩
  have hφy : φ ⟨y, hyX⟩ ≠ 1 := by
    intro h1
    have hyC := (hφ1 _).1 h1
    obtain ⟨u, hu, hu1⟩ := hV₂ne
    have hc : u * y = y * u := Subgroup.mem_centralizer_iff.mp hyC u hu
    exact hyfpf u hu hu1 (by rw [mul_inv_eq_iff_eq_mul]; exact hc.symm)
  have hφy3 : (φ ⟨y, hyX⟩) ^ 3 = 1 := by
    rw [← map_pow]
    exact (hφ1 _).2 hy3
  have hφs : φ ⟨s, hsX⟩ ≠ 1 := by
    intro h1
    have hsC := (hφ1 _).1 h1
    have hc : u₀ * s = s * u₀ := Subgroup.mem_centralizer_iff.mp hsC u₀ hu₀
    exact hsu₀ (by rw [mul_inv_eq_iff_eq_mul]; exact hc.symm)
  obtain ⟨k, hk⟩ := hS2 ⟨s, hsS⟩
  have hφs2 : (φ ⟨s, hsX⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨s, hsX⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord3 : orderOf (φ ⟨y, hyX⟩) = 3 := orderOf_eq_prime hφy3 hφy
  have h3dvd : 3 ∣ Nat.card φ.range := by
    have := Subgroup.orderOf_dvd_natCard φ.range (MonoidHom.mem_range.2 ⟨⟨y, hyX⟩, rfl⟩)
    rwa [hord3] at this
  have h2dvd : 2 ∣ Nat.card φ.range := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hφs2)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      exact hφs (orderOf_eq_one_iff.mp hj)
    have : 2 ∣ orderOf (φ ⟨s, hsX⟩) := by rw [hj]; exact dvd_pow_self 2 hj0
    exact this.trans (Subgroup.orderOf_dvd_natCard _ (MonoidHom.mem_range.2 ⟨_, rfl⟩))
  have hrange6 : Nat.card φ.range = 6 := by
    have hd : Nat.card φ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [card_perm_three] at this
    have h6dvd : 6 ∣ Nat.card φ.range := by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
      simpa using this
    exact Nat.dvd_antisymm hd h6dvd
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [hrange6, card_perm_three]
  have hXcard : ∃ n : ℕ, Nat.card ↥(Yp ⊔ Sgp153 T V₁) = 3 * 2 ^ n := by
    have hYp3 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 3 :=
      Hyp153.card_OTwoQuot_of_pRank_one h113 h.hyp hYpY hr
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Yp) 2).exists_card_eq
    have hYcard : Nat.card ↥Yp = 3 * 2 ^ a := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
      rw [hYp3, ha] at this
      exact this
    have hrel : Yp.relIndex (Yp ⊔ Sgp153 T V₁) = Yp.relIndex (Sgp153 T V₁) := by
      rw [sup_comm]
      exact B6.relIndex_sup_eq_of_le_normalizer hSN
    obtain ⟨j, hj⟩ := hS2.index (Yp.subgroupOf (Sgp153 T V₁))
    have hrel2 : Yp.relIndex (Sgp153 T V₁) = 2 ^ j := hj
    have h1 := Subgroup.relIndex_mul_card Yp (Yp ⊔ Sgp153 T V₁)
    rw [inf_eq_left.mpr le_sup_left, hrel, hrel2, hYcard] at h1
    exact ⟨j + a, by rw [← h1]; ring⟩
  obtain ⟨n, hn⟩ := hXcard
  have hKp : IsPGroup 2 ↥φ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hrange6, hn] at h1
    have hdvd : Nat.card ↥φ.ker ∣ 2 ^ n := ⟨2, by omega⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card hj
  have hsub : (pCoreOf 2 (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁) =
      CFSG.Open.pCore 2 ↥(Yp ⊔ Sgp153 T V₁) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hker : φ.ker = (pCoreOf 2 (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁) := by
    rw [hsub]
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker φ) hKp
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hN0 : ((pCoreOf 2 (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
          (le_normalizer_pCoreOf 2 _)
      have hN : (((pCoreOf 2 (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)).map φ).Normal :=
        hN0.map φ hsurj
      have hbot := eq_bot_of_normal_two_group _ hN (by
        rintro _ ⟨x₀, hx₀, rfl⟩
        obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (Yp ⊔ Sgp153 T V₁) ⟨(x₀ : G), hx₀⟩
        refine ⟨m, ?_⟩
        rw [← map_pow]
        have : x₀ ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
        rw [this, map_one])
      have hx' : x ∈ (pCoreOf 2 (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁) := by
        rw [hsub]; exact hx
      have : φ x ∈ ((pCoreOf 2 (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)).map φ :=
        Subgroup.mem_map_of_mem φ hx'
      rw [hbot, Subgroup.mem_bot] at this
      exact this
  refine ⟨⟨φ, hsurj, hker⟩, ?_⟩
  have hRS : pCoreOf 2 (Yp ⊔ Sgp153 T V₁) ≤ Sgp153 T V₁ := B6.pCoreOf_two_le_of_isSylowTwoOf hSylX
  show pCoreOf 2 (Yp ⊔ Sgp153 T V₁) = Sgp153 T V₁ ⊓ Subgroup.centralizer (V₂ : Set G)
  apply le_antisymm
  · intro x hx
    refine ⟨hRS hx, ?_⟩
    have hxX : x ∈ Yp ⊔ Sgp153 T V₁ := pCoreOf_le 2 _ hx
    have hmem : (⟨x, hxX⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ∈ φ.ker := by
      rw [hker]
      exact hx
    exact (hφ1 _).1 (MonoidHom.mem_ker.mp hmem)
  · rintro x ⟨hxS, hxC⟩
    have hxX : x ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_right hxS
    have hmem : (⟨x, hxX⟩ : ↥(Yp ⊔ Sgp153 T V₁)) ∈ φ.ker := MonoidHom.mem_ker.mpr ((hφ1 _).2 hxC)
    rw [hker] at hmem
    exact hmem

end Hyp15310


namespace S153D

theorem input15311FiveII_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113) :
    Input15311FiveII := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr I hI
  obtain ⟨hs3, hR⟩ := h.s3_and_R_of_pRank_one h11 h113 hr hI
  exact ⟨h.case_two_of_pRank_one h113 hr, hs3, h.yp_eq_oPrimeResidual h113 hr hI, hR⟩

end S153D

end CFSG.Quasithin
