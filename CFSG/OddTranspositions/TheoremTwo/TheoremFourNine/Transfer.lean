module

public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.SylowSixteen
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.FiniteA5
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.IndexTwo
public import CFSG.OddTranspositions.ConfigS5
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8D8

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions Equiv

variable {G : Type} [Group G] [Finite G]
variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

namespace Config

theorem mul_self_of_mem_D (hQ : Config D u w v z a K₁ S') {d : G} (hd : d ∈ D) : d * d = 1 :=
  hQ.setup.oddT.mul_self_eq_one hd

theorem commute_z_of_mem_K₁ (hQ : Config D u w v z a K₁ S') {k : G} (hk : k ∈ K₁) :
    Commute k z :=
  Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hk)

theorem mul_ne_z (hQ : Config D u w v z a K₁ S') {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : Commute x y) : x * y ≠ z := by
  intro h
  have hxz : Commute x z := h ▸ (Commute.refl x).mul_right hxy
  have hzx : z * x ∈ K₁ := hQ.delta_sub x (mem_Delta_iff.mpr ⟨hx, hxz⟩)
  have hyK : y ∈ K₁ := by
    have : y = z * x := by
      calc y = x * x * y := by rw [hQ.mul_self_of_mem_D hx, one_mul]
        _ = x * (x * y) := by group
        _ = x * z := by rw [h]
        _ = z * x := hxz.eq
    rw [this]; exact hzx
  have hzy : z * y ∈ K₁ := hQ.delta_sub y (mem_Delta_iff.mpr ⟨hy, hQ.commute_z_of_mem_K₁ hyK⟩)
  apply hQ.z_not_mem_K₁
  have := K₁.mul_mem hzy (K₁.inv_mem hyK)
  simpa using this

theorem z_mul_mem_D (hQ : Config D u w v z a K₁ S') {k : G} (hk : k ∈ K₁) (hk2 : k * k = 1)
    (hk1 : k ≠ 1) : z * k ∈ D := by
  obtain ⟨eK⟩ := hQ.K₁_A5
  obtain ⟨hz2, -, huΔ, -, -, hzD⟩ := hQ.z_facts
  have hu := mem_Delta_iff.mp huΔ
  have hk₀ : z * u ∈ K₁ := hQ.delta_sub u huΔ
  have hk₀2 : (z * u) * (z * u) = 1 := by
    calc (z * u) * (z * u) = z * (u * z) * u := by group
      _ = z * (z * u) * u := by rw [hu.2.eq]
      _ = (z * z) * (u * u) := by group
      _ = 1 := by rw [hz2, hQ.mul_self_of_mem_D hu.1, one_mul]
  have hk₀1 : z * u ≠ 1 := by
    intro h
    have : u = z := by
      calc u = z * z * u := by rw [hz2, one_mul]
        _ = z := by rw [mul_assoc, h, mul_one]
    exact hzD (this ▸ hu.1)
  obtain ⟨η, hη⟩ := A5_involutions_conj (eK ⟨_, hk₀⟩) (eK ⟨k, hk⟩)
    (by rw [← map_mul]; rw [show (⟨z * u, hk₀⟩ : K₁) * ⟨z * u, hk₀⟩ = 1 from Subtype.ext hk₀2,
      map_one])
    (by rw [Ne, MulEquiv.map_eq_one_iff]; exact fun h => hk₀1 (congrArg Subtype.val h))
    (by rw [← map_mul]; rw [show (⟨k, hk⟩ : K₁) * ⟨k, hk⟩ = 1 from Subtype.ext hk2, map_one])
    (by rw [Ne, MulEquiv.map_eq_one_iff]; exact fun h => hk1 (congrArg Subtype.val h))
  set h : K₁ := eK.symm η
  have hkh : (h : G) * (z * u) * (h : G)⁻¹ = k := by
    have := congrArg (fun x => ((eK.symm x : K₁) : G)) hη
    simpa [h] using this
  have hhz : Commute (h : G) z := hQ.commute_z_of_mem_K₁ h.2
  have : z * k = (h : G) * u * (h : G)⁻¹ := by
    rw [← hkh]
    calc z * ((h : G) * (z * u) * (h : G)⁻¹) = (z * h) * z * u * (h : G)⁻¹ := by group
      _ = (h * z) * z * u * (h : G)⁻¹ := by rw [hhz.eq]
      _ = (h : G) * (z * z) * u * (h : G)⁻¹ := by group
      _ = (h : G) * u * (h : G)⁻¹ := by rw [hz2, mul_one]
  rw [this]
  exact hQ.setup.conj_mem _ hu.1

theorem not_isConj_z_of_mem_K₁ (hQ : Config D u w v z a K₁ S') {t : G} (ht : t ∈ K₁) :
    ¬ IsConj z t := by
  intro hzt
  obtain ⟨eK⟩ := hQ.K₁_A5
  obtain ⟨hz2, hz1, -⟩ := hQ.z_facts
  obtain ⟨g, rfl⟩ := isConj_iff.mp hzt
  have ht2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have ht1 : g * z * g⁻¹ ≠ 1 := by
    intro h; apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨k₁, k₂, h1, h2, h11, h21, h12c, h12⟩ := A5_involution_eq_mul (eK ⟨_, ht⟩)
    (by rw [← map_mul]; rw [show (⟨_, ht⟩ : K₁) * ⟨_, ht⟩ = 1 from Subtype.ext ht2, map_one])
    (by rw [Ne, MulEquiv.map_eq_one_iff]; exact fun h => ht1 (congrArg Subtype.val h))
  set x₁ : G := ((eK.symm k₁ : K₁) : G)
  set x₂ : G := ((eK.symm k₂ : K₁) : G)
  have hx₁ : x₁ ∈ K₁ := (eK.symm k₁).2
  have hx₂ : x₂ ∈ K₁ := (eK.symm k₂).2
  have hval : ∀ {p q : alternatingGroup (Fin 5)}, p = q → ((eK.symm p : K₁) : G) = eK.symm q :=
    fun h => by rw [h]
  have hx₁2 : x₁ * x₁ = 1 := by
    have := hval h1; simpa [x₁] using this
  have hx₂2 : x₂ * x₂ = 1 := by
    have := hval h2; simpa [x₂] using this
  have hx₁1 : x₁ ≠ 1 := by simpa [x₁] using h11
  have hx₂1 : x₂ ≠ 1 := by simpa [x₂] using h21
  have hc : x₁ * x₂ = x₂ * x₁ := by have := hval h12c; simpa [x₁, x₂] using this
  have hprod : x₁ * x₂ = g * z * g⁻¹ := by
    have := hval h12; simpa [x₁, x₂] using this
  have hd₁ := hQ.z_mul_mem_D hx₁ hx₁2 hx₁1
  have hd₂ := hQ.z_mul_mem_D hx₂ hx₂2 hx₂1
  have hzc₁ := hQ.commute_z_of_mem_K₁ hx₁
  have hzc₂ := hQ.commute_z_of_mem_K₁ hx₂
  apply hQ.mul_ne_z (hQ.setup.conj_mem g⁻¹ hd₁) (hQ.setup.conj_mem g⁻¹ hd₂)
  · have hzz : ∀ p q : G, Commute p z → (z * p) * (z * q) = z * z * (p * q) := fun p q hp => by
      calc (z * p) * (z * q) = z * (p * z) * q := by group
        _ = z * z * (p * q) := by rw [hp.eq]; group
    have : Commute (z * x₁) (z * x₂) := by
      show (z * x₁) * (z * x₂) = (z * x₂) * (z * x₁)
      rw [hzz _ _ hzc₁, hzz _ _ hzc₂, hc]
    exact this.conj g⁻¹
  · calc g⁻¹ * (z * x₁) * g⁻¹⁻¹ * (g⁻¹ * (z * x₂) * g⁻¹⁻¹)
        = g⁻¹ * (z * x₁ * z * x₂) * g := by group
      _ = g⁻¹ * (z * z * (x₁ * x₂)) * g := by
          rw [show z * x₁ * z * x₂ = z * (x₁ * z) * x₂ by group, hzc₁.eq]; group
      _ = z := by rw [hz2, one_mul, hprod]; group

theorem a_mem_normalizer (hQ : Config D u w v z a K₁ S') :
    a ∈ Subgroup.normalizer (K₁ : Set G) :=
  hQ.mem_normalizer_K₁_of_commute (hQ.commute_z_of_mem hQ.a_mem)

theorem conj_a_of_mul_sq (hQ : Config D u w v z a K₁ S') {t : G} (ht : t ∈ K₁)
    (hta : (t * a) * (t * a) = 1) : ∃ h ∈ K₁, h * a * h⁻¹ = t * a := by
  obtain ⟨eK⟩ := hQ.K₁_A5
  set N := Subgroup.normalizer (K₁ : Set G)
  set A : N := ⟨a, hQ.a_mem_normalizer⟩
  set T : N := ⟨t, Subgroup.le_normalizer ht⟩
  have hsign := sign_rhoA5_of_not_inner eK A hQ.a_outer
  have hAA : A * A = 1 := Subtype.ext (a_mul_self hQ)
  have hTA : (T * A) * (T * A) = 1 := Subtype.ext hta
  have hπ2 : rhoA5 eK A * rhoA5 eK A = 1 := by rw [← map_mul, hAA, map_one]
  have hτ : rhoA5 eK T = (eK ⟨t, ht⟩ : Perm (Fin 5)) := rhoA5_of_mem eK ht
  have hτs : Perm.sign (rhoA5 eK T) = 1 := by rw [hτ]; exact (eK ⟨t, ht⟩).2
  have hτπ : (rhoA5 eK T * rhoA5 eK A) * (rhoA5 eK T * rhoA5 eK A) = 1 := by
    rw [← map_mul, ← map_mul, hTA, map_one]
  obtain ⟨η, hηs, hη⟩ := S5_odd_involutions_conj _ _ hsign hπ2 hτs hτπ
  set hK : K₁ := eK.symm ⟨η, hηs⟩
  have hρh : rhoA5 eK ⟨(hK : G), Subgroup.le_normalizer hK.2⟩ = η := by
    rw [rhoA5_of_mem eK hK.2]; simp [hK]
  set H : N := ⟨(hK : G), Subgroup.le_normalizer hK.2⟩
  have hkey : ((H * A * H⁻¹ : N) : G) = ((T * A : N) : G) := by
    refine eq_of_rhoA5_eq eK _ _ ?_ ?_
    · show (hK : G) * a * (hK : G)⁻¹ * (t * a)⁻¹ ∈ K₁
      have h1 : a * (hK : G)⁻¹ * a⁻¹ ∈ K₁ :=
        hQ.conj_mem_K₁_of_commute (hQ.commute_z_of_mem hQ.a_mem) _ (K₁.inv_mem hK.2)
      have := K₁.mul_mem (K₁.mul_mem hK.2 h1) (K₁.inv_mem ht)
      convert this using 1; group
    · rw [map_mul, map_mul, map_inv, map_mul, hρh, hη]
  exact ⟨hK, hK.2, hkey⟩

theorem az_mem_normalizer_T₁ (hQ : Config D u w v z a K₁ S') :
    a * z ∈ Subgroup.normalizer ((S' ⊓ K₁ : Subgroup G) : Set G) := by
  have hc : ∀ s ∈ S', ∀ x ∈ S' ⊓ K₁, s * x * s⁻¹ ∈ S' ⊓ K₁ := fun s hs x hx =>
    Subgroup.mem_inf.mpr ⟨S'.mul_mem (S'.mul_mem hs (Subgroup.mem_inf.mp hx).1) (S'.inv_mem hs),
      hQ.conj_mem_K₁_of_commute (hQ.commute_z_of_mem hs) _ (Subgroup.mem_inf.mp hx).2⟩
  have haz : a * z ∈ S' := S'.mul_mem hQ.a_mem hQ.z_central.1
  exact mem_normalizer_of_conj (hc _ haz) (hc _ (S'.inv_mem haz))

theorem transfer_hyp (hQ : Config D u w v z a K₁ S') (x : G) :
    x⁻¹ * z * x ∉ (S' ⊓ K₁) ⊔ Subgroup.zpowers (a * z) := by
  intro hq
  obtain ⟨hz2, -⟩ := hQ.z_facts
  have hza : Commute a z := hQ.commute_z_of_mem hQ.a_mem
  have hzq : IsConj z (x⁻¹ * z * x) := isConj_iff.mpr ⟨x⁻¹, by group⟩
  have haz2 : (a * z) * (a * z) = 1 := by
    calc (a * z) * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [hza.eq]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [(a_mul_self hQ), hz2, one_mul]
  have hsup := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers (a * z))
    (S' ⊓ K₁) ((Subgroup.zpowers_le).mpr hQ.az_mem_normalizer_T₁)
  rw [sup_comm] at hq
  have hq' : x⁻¹ * z * x ∈ ((Subgroup.zpowers (a * z) ⊔ (S' ⊓ K₁) : Subgroup G) : Set G) := hq
  rw [hsup] at hq'
  obtain ⟨c, hc, t, ht, hct⟩ := hq'
  simp only at hct
  have htK : t ∈ K₁ := (Subgroup.mem_inf.mp ht).2
  rcases eq_one_or_eq_of_mem_zpowers haz2 hc with hc1 | hc1
  · rw [hc1, one_mul] at hct
    exact hQ.not_isConj_z_of_mem_K₁ htK (hct ▸ hzq)
  · rw [hc1] at hct
    set t' := (a * z) * t * (a * z)⁻¹
    have ht' : t' ∈ K₁ := hQ.conj_mem_K₁_of_commute
      ((hza).mul_left (Commute.refl z)) t htK
    have hqt : x⁻¹ * z * x = t' * (a * z) := by rw [← hct]; simp only [t']; group
    have hzt' : Commute t' z := hQ.commute_z_of_mem_K₁ ht'
    have hsq : (t' * a) * (t' * a) = 1 := by
      have hq2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
        calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
          _ = 1 := by rw [hz2]; group
      rw [hqt] at hq2
      calc (t' * a) * (t' * a) = t' * (a * z) * (t' * (a * z)) * (z * z)⁻¹ := by
            rw [hz2, inv_one, mul_one]
            calc t' * a * (t' * a) = t' * a * (t' * a) * (z * z) := by rw [hz2, mul_one]
              _ = t' * a * (t' * (a * z)) * z := by group
              _ = t' * a * ((t' * a) * z) * z := by group
              _ = t' * (a * z) * (t' * (a * z)) := by
                  rw [show t' * a * (t' * a * z) * z = t' * a * (t' * (a * z)) * z by group]
                  rw [show t' * (a * z) * (t' * (a * z)) = t' * (a * z) * t' * (a * z) by group]
                  rw [show t' * a * (t' * (a * z)) * z = t' * a * t' * a * (z * z) by group]
                  rw [show t' * (a * z) * t' * (a * z) = t' * a * (z * t') * a * z by group,
                    ← hzt'.eq, show t' * a * (t' * z) * a * z = t' * a * t' * (z * a) * z by group,
                    ← hza.eq]
                  group
        _ = 1 := by rw [hq2, hz2, inv_one, mul_one]
    obtain ⟨h, hh, hha⟩ := hQ.conj_a_of_mul_sq ht' hsq
    have hhz : Commute h z := hQ.commute_z_of_mem_K₁ hh
    have hconj : IsConj (a * z) (x⁻¹ * z * x) := by
      refine isConj_iff.mpr ⟨h, ?_⟩
      rw [hqt]
      calc h * (a * z) * h⁻¹ = h * a * (z * h⁻¹) := by group
        _ = h * a * (h⁻¹ * z) := by rw [(hhz.inv_left).eq.symm]
        _ = (h * a * h⁻¹) * z := by group
        _ = t' * (a * z) := by rw [hha]; group
    exact hQ.az_not_conj ((hQ.a_conj.symm.trans hzq).trans hconj.symm)

theorem az_not_mem_K₁ (hQ : Config D u w v z a K₁ S') : a * z ∉ K₁ := by
  intro h
  apply hQ.a_outer
  refine ⟨a * z, h, fun x hx => ?_⟩
  have hzx : Commute x z := hQ.commute_z_of_mem_K₁ hx
  have hx' : z * x * z⁻¹ = x := by rw [← hzx.eq]; group
  calc a * x * a⁻¹ = a * (z * x * z⁻¹) * a⁻¹ := by rw [hx']
    _ = a * z * x * (a * z)⁻¹ := by group

theorem relIndex_Q (hQ : Config D u w v z a K₁ S')
    (h48 : S' ⊓ Subgroup.centralizer (thirdK D z : Set G) = Subgroup.zpowers z) :
    ((S' ⊓ K₁) ⊔ Subgroup.zpowers (a * z)).relIndex S' = 2 := by
  set Q := (S' ⊓ K₁) ⊔ Subgroup.zpowers (a * z)
  have haz : a * z ∈ S' := S'.mul_mem hQ.a_mem hQ.z_central.1
  have hQS : Q ≤ S' := sup_le inf_le_left ((Subgroup.zpowers_le).mpr haz)
  have h16 := hQ.card_sylow_eq_sixteen h48
  have hT : S' ⊓ K₁ < Q := lt_of_le_of_ne le_sup_left fun h => hQ.az_not_mem_K₁
    ((Subgroup.mem_inf.mp (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (a * z)) :
      a * z ∈ S' ⊓ K₁)).2)
  have hlt : Q < S' := lt_of_le_of_ne hQS fun h =>
    hQ.transfer_hyp 1 (by rw [inv_one, one_mul, mul_one]; exact (SetLike.ext_iff.mp h z).mpr hQ.z_central.1)
  have h1 := Subgroup.card_lt_of_lt hT
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [hQ.card_sylow_inf_K₁] at h1
  rw [h16] at h2
  have hp : IsPGroup 2 Q := hQ.sylow.1.to_le hQS
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : Nat.card Q ∣ 16 := h16 ▸ Subgroup.card_dvd_of_le hQS
  have h8 : Nat.card Q = 8 := by
    rw [hk] at h1 h2 hdvd ⊢
    have hk4 : k ≤ 4 := by
      by_contra h
      have : 2 ^ 5 ∣ 16 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    interval_cases k <;> simp_all
  have := Subgroup.relIndex_mul_card (H := Q) (K := S')
  rw [inf_eq_left.mpr hQS, h8, h16] at this
  omega

theorem exists_index_two (hQ : Config D u w v z a K₁ S')
    (h48 : S' ⊓ Subgroup.centralizer (thirdK D z : Set G) = Subgroup.zpowers z) :
    ∃ L : Subgroup G, L.Normal ∧ L.index = 2 ∧ z ∉ L ∧ K₁ ≤ L ∧ (∀ d ∈ D, d ∉ L) ∧
      (∀ P : Sylow 2 L, Nonempty (P ≃* DihedralGroup 4)) ∧
      Odd ((⁅L, L⁆).relIndex L) := by
  classical
  obtain ⟨eK⟩ := hQ.K₁_A5
  obtain ⟨hz2, hz1, -⟩ := hQ.z_facts
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  set Q := (S' ⊓ K₁) ⊔ Subgroup.zpowers (a * z)
  have haz : a * z ∈ S' := S'.mul_mem hQ.a_mem hQ.z_central.1
  have hQS : Q ≤ S' := sup_le inf_le_left ((Subgroup.zpowers_le).mpr haz)
  have hPidx : ¬ 2 ∣ S'.relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]; exact hQ.not_two_dvd_index_sylow
  obtain ⟨N, -, hNn, hsq, hzN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
    (X := ⊤) le_top hQ.sylow.1 hPidx hQS (hQ.relIndex_Q h48) (Subgroup.mem_top z) hzo
    (fun x _ => hQ.transfer_hyp x)
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := hNn.conj_mem ⟨n, Subgroup.mem_top n⟩ (by simpa [Subgroup.mem_subgroupOf] using hn)
      ⟨g, Subgroup.mem_top g⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hsq' : ∀ x : G, x * x ∈ N := fun x => by rw [← pow_two]; exact hsq x (Subgroup.mem_top x)
  have hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N := by
    intro x y
    have h1 := hsq' (x * y)
    have h2 := N.inv_mem (hsq' x)
    have h3 := N.inv_mem (hsq' y)
    have hy : y⁻¹ * (x * x)⁻¹ * y ∈ N := by
      have := hN.conj_mem _ h2 y⁻¹; simpa using this
    have := N.mul_mem (N.mul_mem h1 hy) h3
    convert this using 1; group
  have hDN : ∀ d ∈ D, d ∉ N := by
    intro d hd hdN
    apply hzN
    have hle : Subgroup.closure D ≤ N := (Subgroup.closure_le N).mpr fun x hx => by
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hQ.setup.isConj hd hx)
      exact hN.conj_mem d hdN g
    rw [hQ.setup.gen] at hle
    exact hle (Subgroup.mem_top z)
  have hidx : N.index = 2 := by
    obtain ⟨d₀, hd₀⟩ := hQ.setup.nonempty
    have hle : N ⊔ Subgroup.zpowers d₀ = ⊤ := by
      rw [eq_top_iff, ← hQ.setup.gen, Subgroup.closure_le]
      intro x hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hQ.setup.isConj hd₀ hx)
      have : g * d₀ * g⁻¹ = (g * d₀ * g⁻¹ * d₀⁻¹) * d₀ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcomm g d₀))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d₀))
    have hd2 : d₀ * d₀ = 1 := hQ.mul_self_of_mem_D hd₀
    have hidx2 : N.index ≤ 2 := by
      have h1 : N.index = N.relIndex (Subgroup.zpowers d₀) := by
        rw [← Subgroup.relIndex_sup_left (K := N), hle, Subgroup.relIndex_top_right]
      have h2 := Subgroup.relIndex_mul_card (H := N) (K := Subgroup.zpowers d₀)
      have h3 : Nat.card (Subgroup.zpowers d₀) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, hd2])
      have h4 : 0 < Nat.card (N ⊓ Subgroup.zpowers d₀ : Subgroup G) := Nat.card_pos
      rw [h1]
      nlinarith
    have hne : N.index ≠ 1 := fun h => hzN (Subgroup.index_eq_one.mp h ▸ Subgroup.mem_top z)
    have hpos : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hK₁N : K₁ ≤ N := by
    rw [← CFSG.GH74.Generic.S45.a5_perfect eK, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def]
    exact hcomm x y
  refine ⟨N, hN, hidx, hzN, hK₁N, hDN, ?_, ?_⟩
  ·
    intro P
    have hS : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      exact ⟨le_top, hQ.sylow.1, hPidx⟩
    have hSN := hS.inf_of_le_normalizer (N := N) le_top (by rw [@Subgroup.normalizer_eq_top _ _ N hN])
    obtain ⟨Q₀, hQ₀⟩ := hSN
    have h16 := hQ.card_sylow_eq_sixteen h48
    have hrel : N.relIndex S' = 2 := by
      have h1 : N.relIndex S' ∣ 2 := hidx ▸ Subgroup.relIndex_dvd_index_of_normal N S'
      have h2 : N.relIndex S' ≠ 1 := fun h =>
        hzN ((Subgroup.relIndex_eq_one.mp h) hQ.z_central.1)
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact absurd h h2
      · exact h
    have h8 : Nat.card (S' ⊓ N : Subgroup G) = 8 := by
      have := Subgroup.relIndex_mul_card (H := N) (K := S')
      rw [hrel, h16, inf_comm] at this
      omega
    have eQ : Q₀ ≃* (S' ⊓ N : Subgroup G) :=
      (Subgroup.equivMapOfInjective _ _ N.subtype_injective).trans (MulEquiv.subgroupCongr hQ₀)
    have eP : P ≃* (S' ⊓ N : Subgroup G) := (Sylow.equiv P Q₀).trans eQ
    suffices hW : Nonempty ((S' ⊓ N : Subgroup G) ≃* DihedralGroup 4) by
      obtain ⟨f⟩ := hW; exact ⟨eP.trans f⟩
    set W : Subgroup G := S' ⊓ N
    have hTW : S' ⊓ K₁ ≤ W := inf_le_inf_left _ hK₁N
    set V : Subgroup W := (S' ⊓ K₁).subgroupOf W
    have hV4 : Nat.card V = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv]
      exact hQ.card_sylow_inf_K₁
    have hT2 : ∀ x ∈ S' ⊓ K₁, x * x = 1 := by
      intro x hx
      have hx4 : (⟨x, hx⟩ : (S' ⊓ K₁ : Subgroup G)) ^ 4 = 1 := by
        rw [← hQ.card_sylow_inf_K₁]; exact pow_card_eq_one'
      have hK : x ∈ K₁ := (Subgroup.mem_inf.mp hx).2
      have : (eK ⟨x, hK⟩) ^ 4 = 1 := by
        rw [← map_pow]
        have := congrArg Subtype.val hx4
        rw [show (⟨x, hK⟩ : K₁) ^ 4 = 1 from Subtype.ext (by simpa using this), map_one]
      have h2 := A5_sq_of_pow_four _ this
      rw [← map_mul, MulEquiv.map_eq_one_iff] at h2
      exact congrArg Subtype.val h2
    refine CFSG.OddStandard.SmallF3.Omega.sec5g8_nonempty_dihedral_of_card_eight h8 hV4
      (fun v hv => Subtype.ext (hT2 _ hv)) ?_
    have hTne : S' ⊓ K₁ ≠ ⊥ := by
      intro h; have := hQ.card_sylow_inf_K₁; rw [h, Subgroup.card_bot] at this; omega
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hTne)
    have hzx : Subgroup.zpowers (x : G) < S' ⊓ K₁ := by
      refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr x.2) fun h => ?_
      have h1 : Nat.card (Subgroup.zpowers (x : G)) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, hT2 _ x.2])
      rw [h, hQ.card_sylow_inf_K₁] at h1; omega
    obtain ⟨y, hy, hyx⟩ := SetLike.exists_of_lt hzx
    have hy1 : y ≠ 1 := fun h => hyx (h ▸ one_mem _)
    have hyx' : y ≠ x := fun h => hyx (h ▸ Subgroup.mem_zpowers _)
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨b, hbW, hbca⟩ : ∃ b ∈ W, ∀ k ∈ K₁, Commute b k → Commute a k := by
      by_cases haN : a ∈ N
      · exact ⟨a, Subgroup.mem_inf.mpr ⟨hQ.a_mem, haN⟩, fun _ _ h => h⟩
      · have hazN : a * z ∈ N := by
          rw [Subgroup.mul_mem_iff_of_index_two hidx]; exact iff_of_false haN hzN
        refine ⟨a * z, Subgroup.mem_inf.mpr ⟨haz, hazN⟩, fun k hk h => ?_⟩
        have hkz : Commute k z := hQ.commute_z_of_mem_K₁ hk
        have : a = (a * z) * z := by rw [mul_assoc, hz2, mul_one]
        rw [this]; exact h.mul_left hkz.symm
    by_contra hall
    push Not at hall
    have hxK : (x : G) ∈ K₁ := (Subgroup.mem_inf.mp x.2).2
    have hyK : y ∈ K₁ := (Subgroup.mem_inf.mp hy).2
    have hax : Commute a x := hbca _ hxK
      (congrArg Subtype.val (hall ⟨b, hbW⟩ ⟨x, hTW x.2⟩))
    have hay : Commute a y := hbca _ hyK
      (congrArg Subtype.val (hall ⟨b, hbW⟩ ⟨y, hTW hy⟩))
    set Nz := Subgroup.normalizer (K₁ : Set G)
    set A : Nz := ⟨a, hQ.a_mem_normalizer⟩
    have hsign := sign_rhoA5_of_not_inner eK A hQ.a_outer
    have hρc : ∀ k (hk : k ∈ K₁), Commute a k →
        rhoA5 eK A * (eK ⟨k, hk⟩ : Perm (Fin 5)) = (eK ⟨k, hk⟩ : Perm (Fin 5)) * rhoA5 eK A := by
      intro k hk hc
      rw [← rhoA5_of_mem eK hk, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hc.eq
    have hxy : (x : G) * y = y * x := by
      have h1 := hT2 _ x.2; have h2 := hT2 _ hy; have h3 := hT2 _ ((S' ⊓ K₁).mul_mem x.2 hy)
      calc (x : G) * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
        _ = y⁻¹ * (x : G)⁻¹ := mul_inv_rev _ _
        _ = y * x := by rw [inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h2]
    have hmap : ∀ {p q : G} (hp : p ∈ K₁) (hq : q ∈ K₁), p * q = q * p →
        (eK ⟨p, hp⟩ : Perm (Fin 5)) * eK ⟨q, hq⟩ = eK ⟨q, hq⟩ * eK ⟨p, hp⟩ := by
      intro p q hp hq h
      rw [← Subgroup.coe_mul, ← map_mul, ← Subgroup.coe_mul, ← map_mul]
      congr 2; exact Subtype.ext h
    have hsq1 : ∀ {p : G} (hp : p ∈ K₁), p * p = 1 →
        (eK ⟨p, hp⟩ : Perm (Fin 5)) * eK ⟨p, hp⟩ = 1 := by
      intro p hp h
      rw [← Subgroup.coe_mul, ← map_mul, show (⟨p, hp⟩ : K₁) * ⟨p, hp⟩ = 1 from Subtype.ext h,
        map_one]; rfl
    have hne1 : ∀ {p : G} (hp : p ∈ K₁), p ≠ 1 → (eK ⟨p, hp⟩ : Perm (Fin 5)) ≠ 1 := by
      intro p hp h h'
      apply h
      have : eK ⟨p, hp⟩ = 1 := Subtype.ext h'
      rw [MulEquiv.map_eq_one_iff] at this
      exact congrArg Subtype.val this
    have hne : (eK ⟨y, hyK⟩ : Perm (Fin 5)) ≠ eK ⟨x, hxK⟩ := by
      intro h
      apply hyx'
      have : eK ⟨y, hyK⟩ = eK ⟨x, hxK⟩ := Subtype.ext h
      exact congrArg Subtype.val (eK.injective this)
    rcases S5_odd_not_centralize_four _ hsign _ (eK ⟨x, hxK⟩).2 (hne1 hxK hx1')
      (hsq1 hxK (hT2 _ x.2)) (hρc _ hxK hax) _ (eK ⟨y, hyK⟩).2 (hne1 hyK hy1) hne
      (hsq1 hyK (hT2 _ hy)) (hmap hxK hyK hxy) with h
    exact h (hρc _ hyK hay)
  · exact odd_relIndex_commutator_of_index_two
      hQ.setup.isClass (fun d hd => hQ.mul_self_of_mem_D hd) hQ.setup.gen hN hidx hDN

end Config

end CFSG.OddTranspositions.QZ
