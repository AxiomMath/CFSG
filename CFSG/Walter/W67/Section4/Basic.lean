module

public import CFSG.Walter.W67.W2Lemma26B

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_one_of_orderOf_eq_two {x : G} (h2 : orderOf x = 2) : x ≠ 1 := fun h1 => by
  rw [h1, orderOf_one] at h2
  omega

theorem conj_mem_oddPart_of_mem_normalizer {Y : Subgroup G} {y x : G}
    (hy : y ∈ Subgroup.normalizer (Y : Set G)) (hx : x ∈ oddPart Y) :
    y * x * y⁻¹ ∈ oddPart Y := by
  set W := (oddPart Y).map (MulAut.conj y).toMonoidHom
  have hWY : W ≤ Y := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hy w).mp (oddPart_le Y hw)
  have hWn : (W.subgroupOf Y).Normal := by
    refine ⟨fun w hw z => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    obtain ⟨o, ho, ho'⟩ := hw
    have hzY : y⁻¹ * (z : G) * y ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * (z : G) * y)).mpr
      apply this
      simp [mul_assoc]
    have h1 := conj_mem_oddPart hzY ho
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ho' ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← ho']
    group
  have hWodd : Nat.Coprime 2 (Nat.card (W.subgroupOf Y)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact coprime_card_oddPart Y
  have hle : W.subgroupOf Y ≤ CFSG.pPrimeCore 2 Y := le_sSup ⟨hWn, hWodd⟩
  have hxW : y * x * y⁻¹ ∈ W := ⟨x, hx, rfl⟩
  exact ⟨⟨_, hWY hxW⟩, hle hxW, rfl⟩

omit [Finite G] in
theorem exists_zpow_conj_eq_of_three {V : Subgroup G} (hV : IsKleinFour V) {z : G}
    (hz3 : orderOf z = 3) (hzN : z ∈ Subgroup.normalizer (V : Set G))
    (hzC : z ∉ Subgroup.centralizer (V : Set G)) {s t : G} (hs : s ∈ V) (hs1 : s ≠ 1)
    (ht : t ∈ V) (ht1 : t ≠ 1) : ∃ i : ℕ, z ^ i * t * (z ^ i)⁻¹ = s := by
  have hfix : ∀ v ∈ V, z * v * z⁻¹ = v → v = 1 := fun v hv =>
    JT.eq_one_of_conj_eq_of_orderOf_eq_three hV hz3 hzN hzC hv
  have hconj : ∀ v ∈ V, z * v * z⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hzN v).mp hv
  have hz3' : z ^ 3 = 1 := by rw [← hz3, pow_orderOf_eq_one]
  set t' := z * t * z⁻¹
  set t'' := z ^ 2 * t * (z ^ 2)⁻¹
  have ht'V : t' ∈ V := hconj t ht
  have ht''V : t'' ∈ V := by
    have : t'' = z * t' * z⁻¹ := by simp only [t'', t', pow_two]; group
    rw [this]
    exact hconj _ ht'V
  have ht'1 : t' ≠ 1 := fun h1 => ht1 (by
    have := congrArg (fun x => z⁻¹ * x * z) h1
    simpa [t', mul_assoc] using this)
  have ht't : t' ≠ t := fun h1 => ht1 (hfix t ht h1)
  have ht''1 : t'' ≠ 1 := fun h1 => ht1 (by
    have := congrArg (fun x => (z ^ 2)⁻¹ * x * z ^ 2) h1
    simpa [t'', mul_assoc] using this)
  have ht''t : t'' ≠ t := by
    intro h1
    apply ht't
    have h2 : z ^ 4 * t * (z ^ 4)⁻¹ = t := by
      calc z ^ 4 * t * (z ^ 4)⁻¹ = z ^ 2 * t'' * (z ^ 2)⁻¹ := by simp only [t'']; group
        _ = t := by rw [h1]; exact h1
    have hz4 : z ^ 4 = z := by
      rw [show 4 = 3 + 1 by norm_num, pow_succ, hz3', one_mul]
    rw [hz4] at h2
    exact h2
  have ht''t' : t'' ≠ t' := by
    intro h1
    apply ht't
    have := congrArg (fun x => z⁻¹ * x * z) h1
    simp only [t'', t'] at this
    calc z * t * z⁻¹ = z⁻¹ * (z ^ 2 * t * (z ^ 2)⁻¹) * z := by group
      _ = z⁻¹ * (z * t * z⁻¹) * z := this
      _ = t := by group
  by_cases hst : s = t
  · exact ⟨0, by rw [hst]; group⟩
  by_cases hst' : s = t'
  · exact ⟨1, by rw [hst', pow_one]⟩
  refine ⟨2, ?_⟩
  have : IsKleinFour V := hV
  have e1 := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨t, ht⟩) (y := ⟨t', ht'V⟩)
    (z := ⟨s, hs⟩) (fun h => ht1 (congrArg Subtype.val h)) (fun h => ht'1 (congrArg Subtype.val h))
    (fun h => ht't (congrArg Subtype.val h).symm) (fun h => hs1 (congrArg Subtype.val h))
    (fun h => hst (congrArg Subtype.val h)) (fun h => hst' (congrArg Subtype.val h))
  have e2 := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨t, ht⟩) (y := ⟨t', ht'V⟩)
    (z := ⟨t'', ht''V⟩) (fun h => ht1 (congrArg Subtype.val h))
    (fun h => ht'1 (congrArg Subtype.val h)) (fun h => ht't (congrArg Subtype.val h).symm)
    (fun h => ht''1 (congrArg Subtype.val h)) (fun h => ht''t (congrArg Subtype.val h))
    (fun h => ht''t' (congrArg Subtype.val h))
  have := congrArg Subtype.val (e2.trans e1.symm)
  exact this

omit [Finite G] in
theorem le_commutator_of_orderOf_three' {V W₁ W₂ : Subgroup G} (hV : IsKleinFour V)
    (hVW : V ≤ W₂) {z : G} (hzW : z ∈ W₁) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (V : Set G)) (hzC : z ∉ Subgroup.centralizer (V : Set G)) :
    V ≤ ⁅W₁, W₂⁆ := by
  have : Finite V := by
    have := hV.card_four
    exact Nat.finite_of_card_ne_zero (by omega)
  set c : V → V := fun t => ⟨z * t * z⁻¹ * (t : G)⁻¹, V.mul_mem
    ((Subgroup.mem_normalizer_iff.mp hzN t).mp t.2) (V.inv_mem t.2)⟩ with hc
  have hcinj : Function.Injective c := by
    intro s t hst
    have h1 : z * s * z⁻¹ * (s : G)⁻¹ = z * t * z⁻¹ * (t : G)⁻¹ := congrArg Subtype.val hst
    have hfix : z * ((t : G)⁻¹ * s) * z⁻¹ = (t : G)⁻¹ * s := by
      have hab := hV.isMulCommutative
      have hts : (s : G)⁻¹ * (t : G) = (t : G) * (s : G)⁻¹ :=
        congrArg Subtype.val (hab.is_comm.comm (s⁻¹) t)
      calc z * ((t : G)⁻¹ * s) * z⁻¹ = (z * t * z⁻¹)⁻¹ * (z * s * z⁻¹) := by group
        _ = (z * t * z⁻¹ * (t : G)⁻¹ * t)⁻¹ * (z * s * z⁻¹ * (s : G)⁻¹ * s) := by group
        _ = (z * s * z⁻¹ * (s : G)⁻¹ * t)⁻¹ * (z * s * z⁻¹ * (s : G)⁻¹ * s) := by rw [h1]
        _ = (t : G)⁻¹ * s := by group
    have := JT.eq_one_of_conj_eq_of_orderOf_eq_three hV hz3 hzN hzC
      (V.mul_mem (V.inv_mem t.2) s.2) hfix
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  have hcsurj := Finite.injective_iff_surjective.mp hcinj
  intro t ht
  obtain ⟨s, hs⟩ := hcsurj ⟨t, ht⟩
  have := congrArg Subtype.val hs
  change z * s * z⁻¹ * (s : G)⁻¹ = t at this
  rw [← this]
  exact Subgroup.commutator_mem_commutator hzW (hVW s.2)

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem exists_three_E :
    ∃ u ∈ h.K, orderOf u = 3 ∧ u ∈ Subgroup.normalizer (fr.T : Set G) ∧
    u ∈ Subgroup.centralizer (fr.E : Set G) ∧ u ∉ Subgroup.centralizer (fr.T : Set G) := by
  obtain ⟨e', P₀, hT⟩ := fr.exists_coords
  obtain ⟨y, hy3, hyN, hyfix⟩ :=
    PSL2Sub.exists_fixed_three e' h.odd_p hT h.mod_eight
  set u := psl2Emb e' y with hu
  have huK : u ∈ h.K := PSL2Sub.emb_mem e' y
  have hu3 : orderOf u = 3 := by
    rw [hu, orderOf_injective _ (PSL2Sub.emb_injective e'), hy3]
  refine ⟨u, huK, hu3, hyN, ?_, fun huC => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨σ, hσ⟩ := fr.conj_eq_fieldAut hT hx
    have := hσ y
    rw [hyfix σ] at this
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [show x * u * x⁻¹ = u from this]
  · have : u ∈ h.K ⊓ Subgroup.centralizer (fr.T : Set G) := ⟨huK, huC⟩
    rw [PSL2Sub.inf_centralizer_eq h.iso h.odd_p h.f_pos fr.T_le_K fr.isKleinFour_T] at this
    have h4 : orderOf u ∣ 4 := fr.card_T ▸ Subgroup.orderOf_dvd_natCard _ this
    rw [hu3] at h4
    omega

theorem mem_normalizer_S_of_K {u : G} (huK : u ∈ h.K)
    (huN : u ∈ Subgroup.normalizer (fr.T : Set G)) :
    u ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) := by
  have : u ∈ h.H ⊓ Subgroup.normalizer (fr.T : Set G) := ⟨h.K_le_H huK, huN⟩
  rw [← fr.normalizer_S_inf_H] at this
  exact this.1

variable {T₂ : G}

theorem T₂_mem_S (hT₂ : T₂ ∈ fr.T) : T₂ ∈ (fr.S : Subgroup G) := fr.T_le_S hT₂

theorem V_eq : fr.V T₂ = Subgroup.zpowers h.J ⊔ Subgroup.zpowers T₂ := by
  rw [Frame.V, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Set.singleton_union]

theorem J_mem_V : h.J ∈ fr.V T₂ := Subgroup.subset_closure (Set.mem_insert _ _)

theorem T₂_mem_V : T₂ ∈ fr.V T₂ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem V_le_S (hT₂ : T₂ ∈ fr.T) : fr.V T₂ ≤ (fr.S : Subgroup G) := by
  rw [Frame.V, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact fr.J_mem
  · exact fr.T₂_mem_S hT₂

theorem centralizer_V : Subgroup.centralizer (fr.V T₂ : Set G) =
    h.H ⊓ Subgroup.centralizer ({T₂} : Set G) := by
  ext x
  rw [Frame.V, Subgroup.centralizer_closure, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    refine ⟨fun g hg => hx g ?_, fun g hg => hx g ?_⟩
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Set.mem_insert _ _
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Set.mem_insert_of_mem _ rfl
  · rintro ⟨h1, h2⟩ g hg
    rcases hg with rfl | hg
    · exact h1 _ rfl
    · exact h2 g hg

theorem mem_V_iff {v : G} (hT₂ : T₂ ∈ fr.T) :
    v ∈ fr.V T₂ ↔ ∃ a ∈ Subgroup.zpowers h.J, ∃ b ∈ Subgroup.zpowers T₂, a * b = v := by
  have hN : Subgroup.zpowers T₂ ≤ Subgroup.normalizer (Subgroup.zpowers h.J : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro j hj
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
    exact (Commute.zpow_left (fr.comm_of_mem_S fr.J_mem (fr.T₂_mem_S hT₂)) n).eq
  rw [fr.V_eq]
  exact mem_sup_iff_of_le_normalizer hN

theorem V_inf_K (hT₂ : T₂ ∈ fr.T) {v : G} (hv : v ∈ fr.V T₂) (hvK : v ∈ h.K) :
    v ∈ Subgroup.zpowers T₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (fr.mem_V_iff hT₂).mp hv
  rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J ha with rfl | rfl
  · rwa [one_mul]
  · exfalso
    apply h.J_not_mem_K
    have hbK : b ∈ h.K := (Subgroup.zpowers_le.mpr hT₂.2) hb
    have : h.J = h.J * b * b⁻¹ := by group
    rw [this]
    exact h.K.mul_mem hvK (h.K.inv_mem hbK)

theorem card_V (hT₂ : T₂ ∈ fr.T) (h2 : orderOf T₂ = 2) : Nat.card (fr.V T₂) = 4 := by
  have hc : ∀ x ∈ Subgroup.zpowers h.J, ∀ y ∈ Subgroup.zpowers T₂, x * y = y * x := by
    intro x hx y hy
    exact fr.comm_of_mem_S ((Subgroup.zpowers_le.mpr fr.J_mem) hx)
      ((Subgroup.zpowers_le.mpr (fr.T₂_mem_S hT₂)) hy)
  have hd : Subgroup.zpowers h.J ⊓ Subgroup.zpowers T₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hx.1 with h1 | h1
    · exact h1
    · exact absurd ((Subgroup.zpowers_le.mpr hT₂.2) (h1 ▸ hx.2)) h.J_not_mem_K
  obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
  rw [hd, Subgroup.card_bot, mul_one, h.card_zpowers_J, Nat.card_zpowers, h2] at hcard
  rw [fr.V_eq]
  exact hcard

theorem isKleinFour_V (hT₂ : T₂ ∈ fr.T) (h2 : orderOf T₂ = 2) : IsKleinFour (fr.V T₂) := by
  have hsq : ∀ v : fr.V T₂, v ^ 2 = 1 := fun v => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one]
    exact fr.mul_self_of_mem_S (fr.V_le_S hT₂ v.2)
  have hdvd : Monoid.exponent (fr.V T₂) ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  have hne : Monoid.exponent (fr.V T₂) ≠ 1 := by
    intro h1
    have := Monoid.pow_exponent_eq_one (⟨h.J, fr.J_mem_V⟩ : fr.V T₂)
    rw [h1, pow_one] at this
    exact h.J_ne_one (congrArg Subtype.val this)
  refine ⟨fr.card_V hT₂ h2, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem A_le (T₂ : G) : fr.A T₂ ≤ h.K ⊓ Subgroup.centralizer ({T₂} : Set G) := oddPart_le _

theorem odd_card_A (T₂ : G) : Odd (Nat.card (fr.A T₂)) := odd_card_oddPart _

theorem A_inf_T (T₂ : G) : fr.A T₂ ⊓ fr.T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact eq_one_of_odd_of_isPGroup fr.isPGroup_T hx.2 (odd_orderOf_of_mem_oddPart hx.1)

theorem T_le_centralizer_T₂ (hT₂ : T₂ ∈ fr.T) :
    fr.T ≤ h.K ⊓ Subgroup.centralizer ({T₂} : Set G) := fun _ ht =>
  ⟨ht.2, Subgroup.mem_centralizer_singleton_iff.mpr (fr.comm_of_mem_S (fr.T_le_S ht)
    (fr.T₂_mem_S hT₂))⟩

theorem mem_T_of_normalizer_T
    (hT₂ : T₂ ∈ fr.T) (h2 : orderOf T₂ = 2) {n : G}
    (hnK : n ∈ h.K) (hnT₂ : n * T₂ = T₂ * n)
    (hnN : n ∈ Subgroup.normalizer (fr.T : Set G)) : n ∈ fr.T := by
  have : IsKleinFour fr.T := fr.isKleinFour_T
  have hT₂1 := ne_one_of_orderOf_eq_two h2
  have hnT : ∀ t ∈ fr.T, n * t * n⁻¹ ∈ fr.T := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp hnN t).mp ht
  have hn2 : n ^ 2 ∈ fr.T := by
    have hC : n ^ 2 ∈ h.K ⊓ Subgroup.centralizer (fr.T : Set G) := by
      refine ⟨h.K.pow_mem hnK 2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have hfix : n * T₂ * n⁻¹ = T₂ := by rw [hnT₂, mul_inv_cancel_right]
      have key : n ^ 2 * t * (n ^ 2)⁻¹ = t := by
        by_cases ht1 : t = 1
        · rw [ht1]; group
        by_cases htT₂ : t = T₂
        · rw [htT₂, pow_two]
          calc n * n * T₂ * (n * n)⁻¹ = n * (n * T₂ * n⁻¹) * n⁻¹ := by group
            _ = T₂ := by rw [hfix, hfix]
        have hnt := hnT t ht
        have hnt1 : n * t * n⁻¹ ≠ 1 := fun h1 => ht1 (by
          have := congrArg (fun x => n⁻¹ * x * n) h1
          simpa [mul_assoc] using this)
        have hntT₂ : n * t * n⁻¹ ≠ T₂ := fun h1 => htT₂ (by
          rw [← hfix] at h1
          have := congrArg (fun x => n⁻¹ * x * n) h1
          simpa [mul_assoc] using this)
        by_cases hntt : n * t * n⁻¹ = t
        · rw [pow_two]
          calc n * n * t * (n * n)⁻¹ = n * (n * t * n⁻¹) * n⁻¹ := by group
            _ = t := by rw [hntt, hntt]
        · have e1 := IsKleinFour.eq_mul_of_ne_all (G := fr.T) (x := ⟨t, ht⟩) (y := ⟨T₂, hT₂⟩)
            (z := ⟨_, hnt⟩) (fun h => ht1 (congrArg Subtype.val h))
            (fun h => hT₂1 (congrArg Subtype.val h)) (fun h => htT₂ (congrArg Subtype.val h))
            (fun h => hnt1 (congrArg Subtype.val h)) (fun h => hntt (congrArg Subtype.val h))
            (fun h => hntT₂ (congrArg Subtype.val h))
          have e1' : n * t * n⁻¹ = t * T₂ := congrArg Subtype.val e1
          have hTT : T₂ * T₂ = 1 := fr.mul_self_of_mem_S (fr.T₂_mem_S hT₂)
          rw [pow_two]
          calc n * n * t * (n * n)⁻¹ = n * (n * t * n⁻¹) * n⁻¹ := by group
            _ = n * (t * T₂) * n⁻¹ := by rw [e1']
            _ = (n * t * n⁻¹) * (n * T₂ * n⁻¹) := by group
            _ = t * T₂ * T₂ := by rw [e1', hfix]
            _ = t := by rw [mul_assoc, hTT, mul_one]
      calc t * n ^ 2 = (n ^ 2 * t * (n ^ 2)⁻¹) * n ^ 2 := by rw [key]
        _ = n ^ 2 * t := by group
    rwa [PSL2Sub.inf_centralizer_eq h.iso h.odd_p h.f_pos fr.T_le_K fr.isKleinFour_T] at hC
  have hn3 : n ^ 3 ∈ fr.T := by
    set Nk := h.K ⊓ Subgroup.normalizer (fr.T : Set G)
    have hTNk : fr.T ≤ Nk := le_inf fr.T_le_K Subgroup.le_normalizer
    have hn : (fr.T.subgroupOf Nk).Normal :=
      normal_subgroupOf_of_le_normalizer (fun x hx => hx.2)
    have hidx : (fr.T.subgroupOf Nk).index = 3 := by
      have h12 := PSL2Sub.card_inf_normalizer h.iso h.odd_p h.f_pos h.mod_eight fr.T_le_K
        fr.isKleinFour_T
      have h1 := Subgroup.relIndex_mul_card (H := fr.T) (K := Nk)
      rw [inf_eq_left.mpr hTNk, h12, fr.card_T] at h1
      change (fr.T.subgroupOf Nk).index * 4 = 12 at h1
      omega
    have := Subgroup.pow_index_mem (fr.T.subgroupOf Nk) (⟨n, hnK, hnN⟩ : Nk)
    rw [hidx] at this
    exact this
  have : n = n ^ 3 * (n ^ 2)⁻¹ := by group
  rw [this]
  exact fr.T.mul_mem hn3 (fr.T.inv_mem hn2)

theorem K_inf_centralizer_eq
    (hT₂ : T₂ ∈ fr.T) (h2 : orderOf T₂ = 2) :
    h.K ⊓ Subgroup.centralizer ({T₂} : Set G) = fr.T ⊔ fr.A T₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₀ := h.K ⊓ Subgroup.centralizer ({T₂} : Set G)
  have hTC := fr.T_le_centralizer_T₂ hT₂
  refine le_antisymm ?_ (sup_le hTC (fr.A_le T₂))
  have hT2 : IsPGroup 2 (fr.T.subgroupOf C₀) :=
    fr.isPGroup_T.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  obtain ⟨P, hP⟩ := hT2.exists_le_sylow
  have hPT : (P : Subgroup C₀) = fr.T.subgroupOf C₀ := by
    refine (Subgroup.eq_of_le_of_card_ge hP ?_).symm
    have hcT : Nat.card (fr.T.subgroupOf C₀) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv, fr.card_T]
    rw [hcT]
    have h4 := PSL2Sub.card_dvd_four h.iso h.odd_p h.f_pos h.mod_eight
      ((Subgroup.map_subtype_le (P : Subgroup C₀)).trans inf_le_left) (P.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective C₀.subtype_injective] at h4
    exact Nat.le_of_dvd (by norm_num) h4
  have hN : Subgroup.normalizer ((P : Subgroup C₀) : Set C₀) ≤
      Subgroup.centralizer ((P : Subgroup C₀) : Set C₀) := by
    intro n hn
    have hnN : (n : G) ∈ Subgroup.normalizer (fr.T : Set G) :=
      JT.mem_normalizer_of_conj_mem fun t ht => by
        have := (Subgroup.mem_normalizer_iff.mp hn ⟨t, hTC ht⟩).mp (hPT ▸ ht)
        rw [hPT] at this
        exact this
    have hnT := fr.mem_T_of_normalizer_T hT₂ h2 n.2.1
      (Subgroup.mem_centralizer_singleton_iff.mp n.2.2) hnN
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rw [hPT] at hp
    exact Subtype.ext (fr.comm_of_mem_S (fr.T_le_S hp) (fr.T_le_S hnT))
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hN
  set N := (MonoidHom.transferSylow P hN).ker
  have hNodd : Nat.Coprime 2 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hN)
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hNO : N ≤ CFSG.pPrimeCore 2 C₀ := le_sSup ⟨hNn, hNodd⟩
  intro x hx
  have hxN : (⟨x, hx⟩ : C₀) ∈ N ⊔ (P : Subgroup C₀) := hcomp.sup_eq_top ▸ Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_le_normalizer
    (Subgroup.le_normalizer_of_normal (H := N))).mp hxN
  have hx' : x = (a : G) * (b : G) := by
    rw [← Subgroup.coe_mul, hab]
  rw [hx', sup_comm]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, hNO ha, rfl⟩)
    (Subgroup.mem_sup_right ?_)
  rw [hPT] at hb
  exact hb

theorem conj_mem_A {y : G} (hyK : y ∈ Subgroup.normalizer (h.K : Set G))
    (hyT₂ : y * T₂ = T₂ * y) {x : G} (hx : x ∈ fr.A T₂) : y * x * y⁻¹ ∈ fr.A T₂ := by
  have hyC : y ∈ Subgroup.normalizer (Subgroup.centralizer ({T₂} : Set G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hyT₂)
  exact conj_mem_oddPart_of_mem_normalizer
    (normalizer_inf_normalizer_le h.K _ ⟨hyK, hyC⟩) hx

omit [Finite G] in
theorem _root_.CFSG.Walter.W67.mem_kleinFour_cases {V : Subgroup G} (hV : IsKleinFour V)
    {a b : G} (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {x : G}
    (hx : x ∈ V) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have : IsKleinFour V := hV
  by_cases h1 : x = 1
  · exact Or.inl h1
  by_cases h2 : x = a
  · exact Or.inr (Or.inl h2)
  by_cases h3 : x = b
  · exact Or.inr (Or.inr (Or.inl h3))
  right; right; right
  have := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) (z := ⟨x, hx⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem E_conj_mem_A {e : G} (he : e ∈ fr.E) {x : G} (hx : x ∈ fr.A T₂) (hT₂ : T₂ ∈ fr.T) :
    e * x * e⁻¹ ∈ fr.A T₂ :=
  fr.conj_mem_A (h.H_le_normalizer (fr.E_le_H he))
    (Subgroup.mem_centralizer_iff.mp (fr.E_le_CS he) T₂ (fr.T₂_mem_S hT₂)).symm hx

theorem S_conj_mem_A {s : G} (hs : s ∈ (fr.S : Subgroup G)) {x : G} (hx : x ∈ fr.A T₂)
    (hT₂ : T₂ ∈ fr.T) : s * x * s⁻¹ ∈ fr.A T₂ :=
  fr.conj_mem_A (h.H_le_normalizer (fr.S_le_H hs)) (fr.comm_of_mem_S hs (fr.T₂_mem_S hT₂)) hx

theorem T_inv_A
    (hT₂ : T₂ ∈ fr.T) (h2 : orderOf T₂ = 2) {t : G} (ht : t ∈ fr.T)
    (htT₂ : t ∉ Subgroup.zpowers T₂) {x : G} (hx : x ∈ fr.A T₂) : t * x * t⁻¹ = x⁻¹ := by
  have ht1 : t ≠ 1 := fun h1 => htT₂ (h1 ▸ Subgroup.one_mem _)
  have htT₂' : t ≠ T₂ := fun h1 => htT₂ (h1 ▸ Subgroup.mem_zpowers _)
  have hfix : fr.A T₂ ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA, hyt⟩
    have hyKT₂ := fr.A_le T₂ hyA
    have hyT : y ∈ h.K ⊓ Subgroup.centralizer (fr.T : Set G) := by
      refine ⟨hyKT₂.1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      have hyT₂c : T₂ * y = y * T₂ := (Subgroup.mem_centralizer_singleton_iff.mp hyKT₂.2).symm
      have hytc : t * y = y * t := (Subgroup.mem_centralizer_singleton_iff.mp hyt).symm
      rcases mem_kleinFour_cases fr.isKleinFour_T hT₂ ht (ne_one_of_orderOf_eq_two h2) ht1
        htT₂'.symm hs with rfl | rfl | rfl | rfl
      · group
      · exact hyT₂c
      · exact hytc
      · rw [mul_assoc, hytc, ← mul_assoc, hyT₂c, mul_assoc]
    rw [PSL2Sub.inf_centralizer_eq h.iso h.odd_p h.f_pos fr.T_le_K fr.isKleinFour_T] at hyT
    have : y ∈ fr.A T₂ ⊓ fr.T := ⟨hyA, hyT⟩
    rwa [fr.A_inf_T] at this
  have htN : t ∈ Subgroup.normalizer (fr.A T₂ : Set G) :=
    JT.mem_normalizer_of_conj_mem fun y hy => fr.S_conj_mem_A (fr.T_le_S ht) hy hT₂
  exact JT.inv_of_inf_centralizer_eq_bot (fr.mul_self_of_mem_S (fr.T_le_S ht)) htN hfix x hx

theorem S_inv_A
    (hT₂ : T₂ ∈ fr.T) (h2 : orderOf T₂ = 2) {s : G}
    (hs : s ∈ (fr.S : Subgroup G)) (hsV : s ∉ fr.V T₂) {x : G} (hx : x ∈ fr.A T₂) :
    s * x * s⁻¹ = x⁻¹ := by
  have hTN : Subgroup.zpowers h.J ≤ Subgroup.normalizer (fr.T : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact h.commute_J (h.K_le_H hy.2)
  rw [← fr.zpowers_J_sup_T, sup_comm] at hs
  obtain ⟨t, ht, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hTN).mp hs
  have htT₂ : t ∉ Subgroup.zpowers T₂ := fun htT₂ => hsV (by
    rw [fr.V_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right htT₂) (Subgroup.mem_sup_left hj))
  have hjx : j * x * j⁻¹ = x := by
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
    · group
    · rw [← h.commute_J (h.K_le_H (fr.A_le T₂ hx).1), mul_inv_cancel_right]
  calc t * j * x * (t * j)⁻¹ = t * (j * x * j⁻¹) * t⁻¹ := by group
    _ = x⁻¹ := by rw [hjx, fr.T_inv_A hT₂ h2 ht htT₂ hx]

theorem exists_conj_T_V
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hT₂ : T₂ ∈ fr.T)
    (h2 : orderOf T₂ = 2) :
    ∃ n ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (fr.E : Set G), ∀ t ∈ fr.T, n * t * n⁻¹ ∈ fr.V T₂ := by
  obtain ⟨z, hzK, hz3, hzN, hzE, hzC⟩ := fr.exists_three_E
  have hzS := fr.mem_normalizer_S_of_K hzK hzN
  have hT₂1 := ne_one_of_orderOf_eq_two h2
  obtain ⟨t₁, ht₁, ht₁T₂⟩ : ∃ t₁ ∈ fr.T, t₁ ∉ Subgroup.zpowers T₂ := by
    by_contra hcon
    push Not at hcon
    have hle : fr.T ≤ Subgroup.zpowers T₂ := fun t ht => hcon t ht
    have := Subgroup.card_le_of_le hle
    rw [fr.card_T, Nat.card_zpowers, h2] at this
    omega
  have ht₁1 : t₁ ≠ 1 := fun h1 => ht₁T₂ (h1 ▸ Subgroup.one_mem _)
  have ht₁T₂' : t₁ ≠ T₂ := fun h1 => ht₁T₂ (h1 ▸ Subgroup.mem_zpowers _)
  obtain ⟨c, hc, hct⟩ := fr.exists_conj_of_cover hidx (fr.T_le_S ht₁) ht₁1
  have hsS : c * T₂ * c⁻¹ ∈ (fr.S : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hc.1 T₂).mp (fr.T₂_mem_S hT₂)
  have hTN : Subgroup.zpowers h.J ≤ Subgroup.normalizer (fr.T : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact h.commute_J (h.K_le_H hy.2)
  have hsS' := hsS
  rw [← fr.zpowers_J_sup_T, sup_comm] at hsS'
  obtain ⟨t, ht, j, hj, htj⟩ := (mem_sup_iff_of_le_normalizer hTN).mp hsS'
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [one_mul] at htj
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with h1 | h1
    · apply hT₂1
      have := congrArg (fun x => c⁻¹ * x * c) (htj.symm.trans h1)
      simpa [mul_assoc] using this
    · apply ht₁T₂'
      have e1 : c * t₁ * c⁻¹ = c * T₂ * c⁻¹ := by rw [hct, ← htj, h1]
      have := congrArg (fun x => c⁻¹ * x * c) e1
      simpa [mul_assoc] using this
  obtain ⟨i, hi⟩ := exists_zpow_conj_eq_of_three fr.isKleinFour_T hz3 hzN hzC hT₂ hT₂1 ht ht1
  refine ⟨z ^ i * c, ⟨Subgroup.mul_mem _ (Subgroup.pow_mem _ hzS i) hc.1,
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hzE i) hc.2⟩, fun t' ht' => ?_⟩
  have hzJ : z ^ i * h.J * (z ^ i)⁻¹ = h.J := by
    rw [(Commute.pow_left (h.commute_J (h.K_le_H hzK)) i).eq, mul_inv_cancel_right]
  have hzj : z ^ i * j * (z ^ i)⁻¹ = j := by
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
    · group
    · exact hzJ
  have h1 : z ^ i * c * t₁ * (z ^ i * c)⁻¹ = h.J := by
    calc z ^ i * c * t₁ * (z ^ i * c)⁻¹ = z ^ i * (c * t₁ * c⁻¹) * (z ^ i)⁻¹ := by group
      _ = h.J := by rw [hct, hzJ]
  have h2' : z ^ i * c * T₂ * (z ^ i * c)⁻¹ = T₂ * j := by
    calc z ^ i * c * T₂ * (z ^ i * c)⁻¹ = z ^ i * (c * T₂ * c⁻¹) * (z ^ i)⁻¹ := by group
      _ = (z ^ i * t * (z ^ i)⁻¹) * (z ^ i * j * (z ^ i)⁻¹) := by rw [← htj]; group
      _ = T₂ * j := by rw [hi, hzj]
  have hjV : j ∈ fr.V T₂ := (Subgroup.zpowers_le.mpr fr.J_mem_V) hj
  rcases mem_kleinFour_cases fr.isKleinFour_T hT₂ ht₁ hT₂1 ht₁1 ht₁T₂'.symm ht' with
    rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h2']
    exact Subgroup.mul_mem _ fr.T₂_mem_V hjV
  · rw [h1]
    exact fr.J_mem_V
  · have : z ^ i * c * (T₂ * t₁) * (z ^ i * c)⁻¹ =
        (z ^ i * c * T₂ * (z ^ i * c)⁻¹) * (z ^ i * c * t₁ * (z ^ i * c)⁻¹) := by group
    rw [this, h1, h2']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ fr.T₂_mem_V hjV) fr.J_mem_V

end Frame

end CFSG.Walter.W67
