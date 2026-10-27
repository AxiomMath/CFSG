module

public import CFSG.Monster.B.GSide.HSylowBetaF4
public import CFSG.Monster.B.GSide.HSylowCenter
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeOuterFinal
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.Blueprint.Chevalley

section Generic

variable {G : Type*} [Group G]

theorem mem_center_map_subtype_iff {X : Subgroup G} {z : G} :
    z ∈ (Subgroup.center X).map X.subtype ↔ z ∈ X ∧ ∀ y ∈ X, z * y = y * z := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨y, hy⟩).symm⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (h y y.2).symm, rfl⟩

theorem exists_conj_fixed_of_odd {X : Subgroup G} (hX : IsPGroup 2 X) {Ω : Set G}
    (hΩ : Ω.Finite) (hodd : Odd Ω.ncard) (hinv : ∀ x ∈ X, ∀ z ∈ Ω, x * z * x⁻¹ ∈ Ω) :
    ∃ z ∈ Ω, ∀ x ∈ X, x * z * x⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Ω := hΩ.to_subtype
  let act : MulAction X Ω :=
    { smul := fun x z => ⟨x * z * (x : G)⁻¹, hinv x x.2 z z.2⟩
      one_smul := fun z => Subtype.ext (by
        change ((1 : X) : G) * (z : G) * ((1 : X) : G)⁻¹ = z
        simp)
      mul_smul := fun x y z => Subtype.ext (by
        change ((x * y : X) : G) * (z : G) * ((x * y : X) : G)⁻¹ =
          (x : G) * ((y : G) * (z : G) * (y : G)⁻¹) * (x : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hcard : ¬ 2 ∣ Nat.card Ω := by
    rw [Nat.card_coe_set_eq]
    exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  obtain ⟨⟨z, hz⟩, hfix⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card Ω hcard
  refine ⟨z, hz, fun x hx => ?_⟩
  have h := congrArg Subtype.val (hfix ⟨x, hx⟩)
  exact h

theorem mem_of_commute_of_odd_relIndex [Finite G] {R X : Subgroup G} (hXR : X ≤ R)
    (hX : IsPGroup 2 X) (hodd : Odd (X.relIndex R)) {z : G} (hzR : z ∈ R) (hz : z * z = 1)
    (hzX : ∀ y ∈ X, z * y = y * z) : z ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX' : IsPGroup 2 (X.subgroupOf R) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXR).symm
  have hidx : ¬ 2 ∣ (X.subgroupOf R).index := fun h =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hzP : IsPGroup 2 (Subgroup.zpowers (⟨z, hzR⟩ : R)) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : (⟨z, hzR⟩ : R) ^ 2 = 1 := Subtype.ext (by rw [sq]; exact hz)
    show ((⟨z, hzR⟩ : R) ^ k) ^ (2 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  have hcomm : ∀ y : R, (⟨z, hzR⟩ : R) * y = y * ⟨z, hzR⟩ →
      (⟨z, hzR⟩ : R) * y * (⟨z, hzR⟩)⁻¹ = y :=
    fun y h => by rw [h, mul_inv_cancel_right]
  have hN : (⟨z, hzR⟩ : R) ∈ Subgroup.normalizer ((X.subgroupOf R : Subgroup R) : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      have h1 : (⟨z, hzR⟩ : R) * y = y * ⟨z, hzR⟩ := Subtype.ext (hzX y hy)
      rw [hcomm y h1]
      exact hy
    · intro hy
      have h1 := hzX _ hy
      have h2 : (y : G) = z⁻¹ * ((⟨z, hzR⟩ : R) * y * (⟨z, hzR⟩)⁻¹ : R) * z := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h2, mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hy
  have h := hzP.inf_normalizer_sylow (hX'.toSylow hidx)
  have hmem : (⟨z, hzR⟩ : R) ∈ Subgroup.zpowers (⟨z, hzR⟩ : R) ⊓
      (hX'.toSylow hidx : Subgroup R) := by
    rw [← h]
    refine ⟨Subgroup.mem_zpowers _, ?_⟩
    show (⟨z, hzR⟩ : R) ∈ Subgroup.normalizer ((hX'.toSylow hidx : Subgroup R) : Set R)
    rw [IsPGroup.toSylow_coe]
    exact hN
  exact Subgroup.mem_subgroupOf.1 ((IsPGroup.mem_toSylow hX' hidx).1 hmem.2)

section Decomp

variable {R F V X : Subgroup G}

theorem natCard_inf_mul_natCard (hFV : F ⊓ V = ⊥) (hRFV : ∀ r ∈ R, ∃ f ∈ F, ∃ v ∈ V, r = f * v)
    (hXR : X ≤ R) (hVX : V ≤ X) : Nat.card (X ⊓ F : Subgroup G) * Nat.card V = Nat.card X := by
  let μ : (X ⊓ F : Subgroup G) × V → X := fun p => ⟨p.1 * p.2, X.mul_mem p.1.2.1 (hVX p.2.2)⟩
  have hinj : Function.Injective μ := by
    rintro ⟨⟨f, hf⟩, ⟨v, hv⟩⟩ ⟨⟨f', hf'⟩, ⟨v', hv'⟩⟩ h
    have h1 : f * v = f' * v' := congrArg Subtype.val h
    have h2 : f'⁻¹ * f ∈ F ⊓ V := by
      refine ⟨F.mul_mem (F.inv_mem hf'.2) hf.2, ?_⟩
      have : f'⁻¹ * f = v' * v⁻¹ := by
        calc f'⁻¹ * f = f'⁻¹ * (f * v) * v⁻¹ := by group
          _ = f'⁻¹ * (f' * v') * v⁻¹ := by rw [h1]
          _ = v' * v⁻¹ := by group
      rw [this]
      exact V.mul_mem hv' (V.inv_mem hv)
    rw [hFV, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    have hvv : v = v' := mul_left_cancel h1
    subst hvv
    rfl
  have hsurj : Function.Surjective μ := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf, v, hv, rfl⟩ := hRFV x (hXR hx)
    have hfX : f ∈ X := by
      have := X.mul_mem hx (X.inv_mem (hVX hv))
      rwa [mul_inv_cancel_right] at this
    exact ⟨(⟨f, hfX, hf⟩, ⟨v, hv⟩), rfl⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective μ ⟨hinj, hsurj⟩)

theorem exists_center_decomp (hVc : ∀ v ∈ V, ∀ r ∈ R, v * r = r * v)
    (hRFV : ∀ r ∈ R, ∃ f ∈ F, ∃ v ∈ V, r = f * v) (hXR : X ≤ R) (hVX : V ≤ X) {z : G}
    (hzX : z ∈ X) (hz : ∀ y ∈ X, z * y = y * z) :
    ∃ f ∈ X ⊓ F, (∀ y ∈ X, f * y = y * f) ∧ ∃ v ∈ V, z = f * v := by
  obtain ⟨f, hf, v, hv, rfl⟩ := hRFV z (hXR hzX)
  have hfX : f ∈ X := by
    have := X.mul_mem hzX (X.inv_mem (hVX hv))
    rwa [mul_inv_cancel_right] at this
  refine ⟨f, ⟨hfX, hf⟩, fun y hy => ?_, v, hv, rfl⟩
  have h1 := hz y hy
  have h2 := hVc v hv y (hXR hy)
  calc f * y = f * v * y * v⁻¹ := by rw [mul_assoc f v y, h2]; group
    _ = y * (f * v) * v⁻¹ := by rw [h1]
    _ = y * f := by group

theorem mul_mem_center_of (hVc : ∀ v ∈ V, ∀ r ∈ R, v * r = r * v)
    (hRFV : ∀ r ∈ R, ∃ f ∈ F, ∃ v ∈ V, r = f * v) (hXR : X ≤ R) (hVX : V ≤ X) {f v : G}
    (hf : f ∈ X ⊓ F) (hfc : ∀ y ∈ X ⊓ F, f * y = y * f) (hv : v ∈ V) :
    ∀ y ∈ X, f * v * y = y * (f * v) := by
  intro y hy
  obtain ⟨f', hf', v', hv', rfl⟩ := hRFV y (hXR hy)
  have hf'X : f' ∈ X := by
    have := X.mul_mem hy (X.inv_mem (hVX hv'))
    rwa [mul_inv_cancel_right] at this
  have h1 := hfc f' ⟨hf'X, hf'⟩
  have h2 := hVc v hv f' (hXR hf'X)
  have h3 := hVc v' hv' f (hXR hf.1)
  have h4 := hVc v' hv' v (hXR (hVX hv))
  calc f * v * (f' * v') = f * (v * f') * v' := by group
    _ = f * (f' * v) * v' := by rw [h2]
    _ = (f * f') * (v * v') := by group
    _ = (f' * f) * (v' * v) := by rw [h1, h4]
    _ = f' * (v' * f) * v := by rw [h3]; group
    _ = f' * v' * (f * v) := by group

end Decomp

end Generic

section Native

variable {u : CVert} {β : vStab cv0}

@[expose] def hc5F (u : CVert) : Subgroup (vStab cv0) := (pairF4 cv0 u).subgroupOf (vStab cv0)

theorem mem_hc5F {y : vStab cv0} : y ∈ hc5F u ↔ (y : Shat) ∈ pairF4 cv0 u :=
  Subgroup.mem_subgroupOf

theorem centralizer_beta_eq
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u) :
    Subgroup.centralizer {β} = (vStab u).subgroupOf (vStab cv0) := by
  obtain ⟨s, hs, hR, -⟩ := native_distance_three_pair_is_full_local_centralizer_final hvu
  have e : s = β := Subtype.ext (hs.trans hβ.symm)
  rw [← e, hR]

theorem mem_centralizer_beta_iff
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    {y : vStab cv0} : y ∈ Subgroup.centralizer {β} ↔ (y : Shat) ∈ vStab u := by
  rw [centralizer_beta_eq hvu hβ, Subgroup.mem_subgroupOf]

theorem natCard_centralizer_beta
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u) :
    Nat.card (Subgroup.centralizer ({β} : Set (vStab cv0))) = 2 ^ 26 * 197358525 := by
  obtain ⟨-, -, -, -, -, hcard, -⟩ := native_distance_three_pair_is_full_local_centralizer_final hvu
  rw [centralizer_beta_eq hvu hβ, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hcard]
  norm_num

theorem hc5F_le_centralizer
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u) :
    hc5F u ≤ Subgroup.centralizer {β} := fun y hy => by
  rw [mem_centralizer_beta_iff hvu hβ]
  exact (pairF4_le_inf cv0 u (mem_hc5F.1 hy)).2

theorem closure_le_center
    (β : vStab cv0) :
    ∀ v ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0)), ∀ r ∈ Subgroup.centralizer {β},
      v * r = r * v := by
  intro v hv r hr
  have hle : Subgroup.closure ({cV0, β} : Set (vStab cv0)) ≤
      Subgroup.centralizer (Subgroup.centralizer ({β} : Set (vStab cv0)) : Set (vStab cv0)) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · refine Subgroup.mem_centralizer_iff.2 fun y _ => ?_
      have hc : cV0 ∈ Subgroup.center (vStab cv0) := by
        rw [center_vStab_cv0]
        exact Subgroup.mem_zpowers _
      exact (Subgroup.mem_center_iff.1 hc y)
    · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hv) r hr).symm

theorem map_closure_cV0_beta (hβ : (β : Shat) = clabelS u) :
    (Subgroup.closure ({cV0, β} : Set (vStab cv0))).map (vStab cv0).subtype =
      Subgroup.closure ({clabelS cv0, clabelS u} : Set Shat) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  show Subgroup.closure {(cV0 : Shat), (β : Shat)} = _
  rw [coe_cV0, hβ]

theorem mem_closure_cV0_beta_iff (hβ : (β : Shat) = clabelS u) {v : vStab cv0} :
    v ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0)) ↔
      (v : Shat) ∈ Subgroup.closure ({clabelS cv0, clabelS u} : Set Shat) := by
  rw [← map_closure_cV0_beta hβ]
  exact (Subgroup.mem_map_iff_mem (vStab cv0).subtype_injective).symm

theorem closure_pair_le_vStab (hβ : (β : Shat) = clabelS u) :
    Subgroup.closure ({clabelS cv0, clabelS u} : Set Shat) ≤ vStab cv0 := by
  rw [← map_closure_cV0_beta hβ]
  exact Subgroup.map_subtype_le _

theorem exists_pairF4_mul_equiv
    (hvu : cgraph.dist cv0 u = 3) :
    ∃ e : pairF4 cv0 u × Subgroup.closure ({clabelS cv0, clabelS u} : Set Shat) ≃*
        (vStab cv0 ⊓ vStab u : Subgroup Shat), ∀ x, (e x : Shat) = x.1 * x.2 := by
  have h := native_distance_three_pair_split_pinned_F4_final hvu
  exact h.2.1

theorem nonempty_pairF4_equiv
    (hvu : cgraph.dist cv0 u = 3) :
    Nonempty (pairF4 cv0 u ≃* adjointGroup .F4 (ZMod 2)) := by
  have h := native_distance_three_pair_split_pinned_F4_final hvu
  obtain ⟨-, -, ⟨s₀, hs₀, ρ₀, iv₀, hρ₀, hρ₀s⟩, Ψ, -, hall⟩ := h
  have h' := hall ρ₀ hρ₀.1 hρ₀.2.1 s₀ hs₀ hρ₀s
  obtain ⟨-, -, ⟨eF, -⟩, -⟩ := h'
  exact ⟨eF⟩

theorem natCard_pairF4
    (hvu : cgraph.dist cv0 u = 3) :
    Nat.card (pairF4 cv0 u) = 2 ^ 24 * 197358525 := by
  obtain ⟨e⟩ := nonempty_pairF4_equiv hvu
  exact (Nat.card_congr e.toEquiv).trans natCard_adjointGroup_F4_zmod_two

theorem natCard_vStab_inf
    (hvu : cgraph.dist cv0 u = 3) :
    Nat.card (vStab cv0 ⊓ vStab u : Subgroup Shat) = 2 ^ 26 * 197358525 := by
  have h := native_distance_three_pair_is_full_local_centralizer_final hvu
  obtain ⟨-, -, -, -, -, hcard, -⟩ := h
  rw [hcard]
  norm_num

theorem nonempty_hc5F_equiv
    (hvu : cgraph.dist cv0 u = 3) :
    Nonempty (hc5F u ≃* adjointGroup .F4 (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_pairF4_equiv hvu
  exact ⟨(Subgroup.subgroupOfEquivOfLe (pairF4_le_vStab cv0 u)).trans e⟩

theorem pairF4_inf_closure
    (hvu : cgraph.dist cv0 u = 3) :
    pairF4 cv0 u ⊓ Subgroup.closure ({clabelS cv0, clabelS u} : Set Shat) = ⊥ := by
  obtain ⟨e, he⟩ := exists_pairF4_mul_equiv hvu
  rw [Subgroup.eq_bot_iff_forall]
  rintro y ⟨hyF, hyV⟩
  have h1 : e (⟨y, hyF⟩, 1) = e (1, ⟨y, hyV⟩) := Subtype.ext (calc
    (e (⟨y, hyF⟩, 1) : Shat) = y * 1 := he (⟨y, hyF⟩, 1)
    _ = 1 * y := by rw [mul_one, one_mul]
    _ = e (1, ⟨y, hyV⟩) := (he (1, ⟨y, hyV⟩)).symm)
  have h2 := congrArg (fun p => (p.1 : Shat)) (e.injective h1)
  exact h2

theorem pairF4_mul_decomp
    (hvu : cgraph.dist cv0 u = 3) :
    ∀ r ∈ (vStab cv0 ⊓ vStab u : Subgroup Shat), ∃ f ∈ pairF4 cv0 u,
      ∃ v ∈ Subgroup.closure ({clabelS cv0, clabelS u} : Set Shat), r = f * v := by
  obtain ⟨e, he⟩ := exists_pairF4_mul_equiv hvu
  intro r hr
  obtain ⟨⟨⟨f, hf⟩, ⟨v, hv⟩⟩, hfv⟩ := e.surjective ⟨r, hr⟩
  exact ⟨f, hf, v, hv, (congrArg Subtype.val hfv).symm.trans (he _)⟩

theorem hc5F_inf_closure
    (hβ : (β : Shat) = clabelS u) (hvu : cgraph.dist cv0 u = 3) :
    hc5F u ⊓ Subgroup.closure {cV0, β} = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro y ⟨hyF, hyV⟩
  have h : (y : Shat) ∈ pairF4 cv0 u ⊓ Subgroup.closure ({clabelS cv0, clabelS u} : Set Shat) :=
    ⟨mem_hc5F.1 hyF, (mem_closure_cV0_beta_iff hβ).1 hyV⟩
  rw [pairF4_inf_closure hvu, Subgroup.mem_bot] at h
  exact Subtype.ext h

theorem exists_hc5F_mul
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u) :
    ∀ r ∈ Subgroup.centralizer {β}, ∃ f ∈ hc5F u,
      ∃ v ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0)), r = f * v := by
  intro r hr
  obtain ⟨f, hf, v, hv, hfv⟩ :=
    pairF4_mul_decomp hvu r ⟨r.2, (mem_centralizer_beta_iff hvu hβ).1 hr⟩
  exact ⟨⟨f, pairF4_le_vStab cv0 u hf⟩, mem_hc5F.2 hf, ⟨v, closure_pair_le_vStab hβ hv⟩,
    (mem_closure_cV0_beta_iff hβ).2 hv, Subtype.ext hfv⟩

theorem natCard_closure_cV0_beta
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u) :
    Nat.card (Subgroup.closure ({cV0, β} : Set (vStab cv0))) = 4 := by
  obtain ⟨e, -⟩ := exists_pairF4_mul_equiv hvu
  have h1 := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, natCard_pairF4 hvu, natCard_vStab_inf hvu] at h1
  rw [← Subgroup.card_map_of_injective (vStab cv0).subtype_injective, map_closure_cV0_beta hβ]
  omega

theorem commutator_centralizer_le_hc5F
    (hvu : cgraph.dist cv0 u = 3)
    (hβ : (β : Shat) = clabelS u) :
    ⁅Subgroup.centralizer ({β} : Set (vStab cv0)), Subgroup.centralizer {β}⁆ ≤ hc5F u := by
  have hcomm : pairF4 cv0 u = ⁅vStab cv0 ⊓ vStab u, vStab cv0 ⊓ vStab u⁆ := by
    have h := native_distance_three_pair_split_pinned_F4_final hvu
    exact h.1
  intro y hy
  rw [mem_hc5F, hcomm]
  have hmap : (Subgroup.centralizer ({β} : Set (vStab cv0))).map (vStab cv0).subtype =
      vStab cv0 ⊓ vStab u := by
    rw [centralizer_beta_eq hvu hβ, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← hmap, ← Subgroup.map_commutator]
  exact Subgroup.mem_map_of_mem _ hy

theorem cV0_mem_center_H :
    cV0 ∈ Subgroup.center (vStab cv0) := by
  rw [center_vStab_cv0]
  exact Subgroup.mem_zpowers _

theorem beta_mul_self
    (hβ : (β : Shat) = clabelS u) : β * β = 1 :=
  Subtype.ext (by rw [Subgroup.coe_mul, hβ, Subgroup.coe_one]; exact clabelS_mul_clabelS u)

end Native

section XLevel

variable {u : CVert} {β : vStab cv0} {X : Subgroup (vStab cv0)}

theorem odd_relIndex_centralizer
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    Odd (X.relIndex (Subgroup.centralizer {β})) := by
  have h := Subgroup.relIndex_mul_card X (Subgroup.centralizer {β})
  rw [inf_eq_left.2 hXβ, hX, natCard_centralizer_beta hvu hβ, mul_comm (2 ^ 26)] at h
  rw [Nat.eq_of_mul_eq_mul_right (by positivity) h]
  decide

theorem mem_X_of_commute
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {z : vStab cv0}
    (hzR : z ∈ Subgroup.centralizer {β}) (hz : z * z = 1) (hzX : ∀ y ∈ X, z * y = y * z) :
    z ∈ X :=
  mem_of_commute_of_odd_relIndex hXβ (IsPGroup.of_card hX)
    (odd_relIndex_centralizer hvu hβ hXβ hX) hzR hz hzX

theorem cV0_mem_X
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) : cV0 ∈ X :=
  mem_X_of_commute hvu hβ hXβ hX
    (Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 cV0_mem_center_H β).symm)
    cV0_mul_self fun y _ => (Subgroup.mem_center_iff.1 cV0_mem_center_H y).symm

theorem beta_mem_X
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) : β ∈ X :=
  mem_X_of_commute hvu hβ hXβ hX (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    (beta_mul_self hβ) fun _ hy => (Subgroup.mem_centralizer_singleton_iff.1 (hXβ hy)).symm

theorem closure_le_X
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    Subgroup.closure ({cV0, β} : Set (vStab cv0)) ≤ X := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact cV0_mem_X hvu hβ hXβ hX
  · exact beta_mem_X hvu hβ hXβ hX

theorem natCard_inf_hc5F
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    Nat.card (X ⊓ hc5F u : Subgroup (vStab cv0)) = 2 ^ 24 := by
  have h := natCard_inf_mul_natCard (hc5F_inf_closure hβ hvu) (exists_hc5F_mul hvu hβ) hXβ
    (closure_le_X hvu hβ hXβ hX)
  rw [natCard_closure_cV0_beta hvu hβ, hX] at h
  omega

@[expose] def hc5ZP (u : CVert) (X : Subgroup (vStab cv0)) : Subgroup (vStab cv0) :=
  (Subgroup.center (X ⊓ hc5F u : Subgroup (vStab cv0))).map (X ⊓ hc5F u).subtype

theorem mem_hc5ZP {z : vStab cv0} :
    z ∈ hc5ZP u X ↔ z ∈ X ⊓ hc5F u ∧ ∀ y ∈ X ⊓ hc5F u, z * y = y * z :=
  mem_center_map_subtype_iff

theorem hc5ZP_facts
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    Nat.card (hc5ZP u X) ≤ 4 ∧ hc5ZP u X ≤ ⁅X, X⁆ := by
  obtain ⟨e⟩ := nonempty_hc5F_equiv hvu
  obtain ⟨h1, h2⟩ := center_facts_of_le_of_mulEquiv_F4 e inf_le_right
    (natCard_inf_hc5F hvu hβ hXβ hX)
  exact ⟨h1, h2.trans (Subgroup.commutator_mono inf_le_left inf_le_left)⟩

theorem mem_center_X_iff
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {z : vStab cv0} :
    (z ∈ X ∧ ∀ y ∈ X, z * y = y * z) ↔
      ∃ f ∈ hc5ZP u X, ∃ v ∈ Subgroup.closure ({cV0, β} : Set (vStab cv0)), z = f * v := by
  have hVX := closure_le_X hvu hβ hXβ hX
  have hVc := closure_le_center β
  have hRFV := exists_hc5F_mul hvu hβ
  constructor
  · rintro ⟨hzX, hz⟩
    obtain ⟨f, hf, hfc, v, hv, rfl⟩ := exists_center_decomp hVc hRFV hXβ hVX hzX hz
    exact ⟨f, mem_hc5ZP.2 ⟨hf, fun y hy => hfc y hy.1⟩, v, hv, rfl⟩
  · rintro ⟨f, hf, v, hv, rfl⟩
    obtain ⟨hf1, hf2⟩ := mem_hc5ZP.1 hf
    exact ⟨X.mul_mem hf1.1 (hVX hv), mul_mem_center_of hVc hRFV hXβ hVX hf1 hf2 hv⟩

theorem center_inf_commutator_eq
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ = hc5ZP u X := by
  ext z
  rw [Subgroup.mem_inf, mem_center_map_subtype_iff]
  constructor
  · rintro ⟨⟨hzX, hz⟩, hzc⟩
    have hzF : z ∈ hc5F u := commutator_centralizer_le_hc5F hvu hβ
      (Subgroup.commutator_mono hXβ hXβ hzc)
    exact mem_hc5ZP.2 ⟨⟨hzX, hzF⟩, fun y hy => hz y hy.1⟩
  · intro hz
    have h := (mem_center_X_iff hvu hβ hXβ hX).2 ⟨z, hz, 1, Subgroup.one_mem _, (mul_one z).symm⟩
    exact ⟨h, (hc5ZP_facts hvu hβ hXβ hX).2 hz⟩

end XLevel

end CFSG.Monster.B.GSide
