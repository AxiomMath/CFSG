module

public import CFSG.Quasithin.EmptyFaithful.S153EGen
public import CFSG.Quasithin.EmptyFaithful.S153EDefs3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

section N8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem N8Data153.v_mem {cx : Ctx15350 T Mc M V₁ V₂ t} {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) : v ∈ V₁ :=
  (hN.v_gen ▸ Subgroup.mem_zpowers v : v ∈ ZS153 T M V₁ ⊓ V₁).2

theorem N8Data153.v_mul_self {cx : Ctx15350 T Mc M V₁ V₂ t} {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) : v * v = 1 := by
  have := cx.c.hyp.elemAbelian.2 v (cx.c.decomp.le₁ hN.v_mem)
  rwa [pow_two] at this

theorem N8Data153.sylow_centralizer {cx : Ctx15350 T Mc M V₁ V₂ t} {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) :
    IsSylowTwoOf (T ⊓ JM) (M ⊓ Subgroup.centralizer (DM : Set G)) := by
  have hK : M ⊓ Subgroup.centralizer (DM : Set G) = DM ⊔ JM := hN.cent_eq
  have hJK : JM ≤ M ⊓ Subgroup.centralizer (DM : Set G) := hK ▸ le_sup_right
  have hTJ : T ⊓ JM ≤ M ⊓ Subgroup.centralizer (DM : Set G) := inf_le_right.trans hJK
  refine ⟨hTJ, hN.TJ_syl.2.1, ?_⟩
  have hcard : Nat.card ↥(DM ⊔ JM) * Nat.card ↥(DM ⊓ JM) = Nat.card DM * Nat.card JM :=
    B2F.card_sup_mul_card_inf_of_commute hN.comm
  rw [hN.inf_eq, Subgroup.card_bot, mul_one, hN.card_DM] at hcard
  have h1 := Subgroup.relIndex_mul_card JM (M ⊓ Subgroup.centralizer (DM : Set G))
  rw [inf_eq_left.mpr hJK, hK, hcard] at h1
  have hJpos : 0 < Nat.card JM := Nat.card_pos
  have h3 : JM.relIndex (M ⊓ Subgroup.centralizer (DM : Set G)) = 3 := by
    have : JM.relIndex (M ⊓ Subgroup.centralizer (DM : Set G)) * Nat.card JM = 3 * Nat.card JM := by
      rw [hK]; exact h1
    exact Nat.eq_of_mul_eq_mul_right hJpos this
  have h2 := Subgroup.relIndex_mul_relIndex (T ⊓ JM) JM (M ⊓ Subgroup.centralizer (DM : Set G))
    hN.TJ_syl.1 hJK
  rw [h3] at h2
  show ¬ 2 ∣ (T ⊓ JM).relIndex (M ⊓ Subgroup.centralizer (DM : Set G))
  rw [← h2]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
  · exact hN.TJ_syl.2.2 h
  · omega

theorem N8Data153.exists_involution {cx : Ctx15350 T Mc M V₁ V₂ t} {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) : ∃ t₂ : G, t₂ ∈ T ⊓ JM ∧ orderOf t₂ = 2 ∧ t₂ ∉ V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hN.TJ_dih
  by_contra hcon
  push Not at hcon
  have hmem : ∀ x : {x : ↥(T ⊓ JM) // x * x = 1}, ((x.1 : ↥(T ⊓ JM)) : G) ∈ V₁ := by
    intro x
    by_cases h1 : ((x.1 : ↥(T ⊓ JM)) : G) = 1
    · rw [h1]
      exact V₁.one_mem
    · apply hcon _ x.1.2
      have hsq : ((x.1 : ↥(T ⊓ JM)) : G) ^ 2 = 1 := by
        have := congrArg Subtype.val x.2
        simpa [pow_two] using this
      exact orderOf_eq_prime hsq h1
  let φ : {x : ↥(T ⊓ JM) // x * x = 1} → ↥V₁ := fun x => ⟨((x.1 : ↥(T ⊓ JM)) : G), hmem x⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have h6 : Nat.card {x : ↥(T ⊓ JM) // x * x = 1} = 6 := by
    have hequiv : {x : ↥(T ⊓ JM) // x * x = 1} ≃ {y : DihedralGroup 4 // y * y = 1} :=
      e.toEquiv.subtypeEquiv fun x => by
        show x * x = 1 ↔ e x * e x = 1
        constructor
        · intro h
          rw [← map_mul, h, map_one]
        · intro h
          apply e.injective
          rw [map_mul, map_one]
          exact h
    rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card]
    decide
  have h4 : Nat.card ↥V₁ = 4 := cx.c.decomp.card₁
  have := Nat.card_le_card_of_injective φ hφ
  omega

end N8

namespace S153E

section Sylow

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers_sq {b x : G} (hb : b * b = 1) (hx : x ∈ Subgroup.zpowers b) :
    x = 1 ∨ x = b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_ofNat, hb2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hb2, one_zpow, one_mul, zpow_one]

theorem card_sylow_centralizer_DM (cx : Ctx15350 T Mc M V₁ V₂ t) {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) {R' : Subgroup G}
    (hR' : R' ≤ Subgroup.centralizer (DM : Set G) ∧ IsPGroup 2 R' ∧
      ¬ 2 ∣ R'.relIndex (Subgroup.centralizer (DM : Set G))) : Nat.card R' = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR₀S := hN.sylow_centralizer
  have hR₀dih := hN.TJ_dih
  have hR₀Z := hN.TJ_center
  set R₀ : Subgroup G := T ⊓ JM with hR₀def
  have hR₀S' : R₀ ≤ M ⊓ Subgroup.centralizer (DM : Set G) ∧ IsPGroup 2 R₀ ∧
      ¬ 2 ∣ R₀.relIndex (M ⊓ Subgroup.centralizer (DM : Set G)) := hR₀S
  have hR₀le : R₀ ≤ M ⊓ Subgroup.centralizer (DM : Set G) := hR₀S'.1
  have hR₀2 : IsPGroup 2 R₀ := hR₀S'.2.1
  have hR₀card : Nat.card R₀ = 8 := by
    obtain ⟨e⟩ := hR₀dih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hR₀C : R₀ ≤ Subgroup.centralizer (DM : Set G) := hR₀le.trans inf_le_right
  obtain ⟨R'', hR₀R'', hR''C, hR''2, hR''i⟩ := exists_sylow_ge (p := 2) hR₀2 hR₀C
  have heq : R'' = R₀ := by
    by_contra hne
    have hlt : R₀ < R'' := lt_of_le_of_ne hR₀R'' (Ne.symm hne)
    obtain ⟨x, hxR'', hxN, hxnot⟩ := exists_mem_normalizer_not_mem_of_lt hR''2 hlt
    have hvZ : v ∈ centerOf R₀ := hR₀Z ▸ Subgroup.mem_zpowers v
    have hxvZ : x * v * x⁻¹ ∈ centerOf R₀ := by
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxN v).mp hvZ.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro w hw
      have hw' : x⁻¹ * w * x ∈ R₀ := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) w).mp hw
        simpa using this
      have hcomm : (x⁻¹ * w * x) * v = v * (x⁻¹ * w * x) :=
        Subgroup.mem_centralizer_iff.mp hvZ.2 _ hw'
      calc w * (x * v * x⁻¹) = x * ((x⁻¹ * w * x) * v) * x⁻¹ := by group
        _ = x * (v * (x⁻¹ * w * x)) * x⁻¹ := by rw [hcomm]
        _ = (x * v * x⁻¹) * w := by group
    rw [hR₀Z] at hxvZ
    have hxv : x * v * x⁻¹ = v := by
      rcases eq_one_or_eq_of_mem_zpowers_sq hN.v_mul_self hxvZ with h1 | h1
      · exfalso
        apply hN.v_ne
        have : x * v * x⁻¹ = 1 := h1
        simpa using this
      · exact h1
    have hxcv : x ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      calc v * x = (x * v * x⁻¹) * x := by rw [hxv]
        _ = x * v := by group
    have hxM : x ∈ M := cx.r46.centralizer_nonsingular v hN.v_ne (Or.inl hN.v_mem) hxcv
    have hxMC : x ∈ M ⊓ Subgroup.centralizer (DM : Set G) := ⟨hxM, hR''C hxR''⟩
    set A : Subgroup G := R₀ ⊔ Subgroup.zpowers x with hA
    have hAR'' : A ≤ R'' := sup_le hR₀R'' (Subgroup.zpowers_le.mpr hxR'')
    have hAMC : A ≤ M ⊓ Subgroup.centralizer (DM : Set G) :=
      sup_le hR₀le (Subgroup.zpowers_le.mpr hxMC)
    obtain ⟨R₃, hAR₃, hR₃le, hR₃2, hR₃i⟩ := exists_sylow_ge (p := 2) (hR''2.to_le hAR'') hAMC
    have hcard : Nat.card R₀ = Nat.card R₃ :=
      card_eq_of_isSylow (p := 2) hR₀S' ⟨hR₃le, hR₃2, hR₃i⟩
    have hAle : Nat.card A ≤ Nat.card R₃ := Subgroup.card_le_of_le hAR₃
    have hR₀A : R₀ ≤ A := le_sup_left
    have hAeq : R₀ = A := Subgroup.eq_of_le_of_card_ge hR₀A (hcard ▸ hAle)
    exact hxnot (hAeq ▸ (le_sup_right : Subgroup.zpowers x ≤ A) (Subgroup.mem_zpowers x))
  have hR'' : R'' ≤ Subgroup.centralizer (DM : Set G) ∧ IsPGroup 2 R'' ∧
      ¬ 2 ∣ R''.relIndex (Subgroup.centralizer (DM : Set G)) := ⟨hR''C, hR''2, hR''i⟩
  rw [card_eq_of_isSylow (p := 2) hR' hR'', heq, hR₀card]

theorem lemma_15_3_60_one (cx : Ctx15350 T Mc M V₁ V₂ t) {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) {DH : Subgroup G}
    (hH : ∃ R : Subgroup G, IsSylowTwoOf R (Mc ⊓ Subgroup.centralizer (DH : Set G)) ∧
      Nat.card R = 16) : ¬ ∃ g : G, conjSubgroup DH g = DM := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨g, hg⟩
  obtain ⟨R, hR, hR16⟩ := hH
  have hR' : R ≤ Mc ⊓ Subgroup.centralizer (DH : Set G) ∧ IsPGroup 2 R ∧
      ¬ 2 ∣ R.relIndex (Mc ⊓ Subgroup.centralizer (DH : Set G)) := hR
  have hRgC : conjSubgroup R g ≤ Subgroup.centralizer (DM : Set G) := by
    intro r hr
    rw [mem_conjSubgroup_iff] at hr
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    rw [← hg] at hd
    have hd' : d ∈ conjSubgroup DH g := hd
    rw [mem_conjSubgroup_iff] at hd'
    have hcomm : (g * d * g⁻¹) * (g * r * g⁻¹) = (g * r * g⁻¹) * (g * d * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hR'.1 hr).2 _ hd'
    calc d * r = g⁻¹ * ((g * d * g⁻¹) * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * (g * d * g⁻¹)) * g := by rw [hcomm]
      _ = r * d := by group
  obtain ⟨R3, hRgR3, hR3C, hR3_2, hR3i⟩ :=
    exists_sylow_ge (p := 2) (isPGroup_conjSubgroup153 hR'.2.1 g) hRgC
  have h8 := card_sylow_centralizer_DM cx hN ⟨hR3C, hR3_2, hR3i⟩
  have h16 : Nat.card (conjSubgroup R g) = 16 := by rw [card_conjSubgroup153, hR16]
  have := Subgroup.card_le_of_le hRgR3
  omega

theorem mem_Mc_of_commute (cx : Ctx15350 T Mc M V₁ V₂ t) {z : G}
    (hz : Subgroup.zpowers z = quasithinOmegaOneCenter T) {x : G} (hx : z * x = x * z) :
    x ∈ Mc := by
  refine cx.c.hyp.qtfe.centralizer_le_mc ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [← hz] at hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ((Commute.zpow_left (show Commute z x from hx) k)).eq

theorem lemma_15_3_60_two_z (cx : Ctx15350 T Mc M V₁ V₂ t) {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) {DH : Subgroup G} (hDH : IsSylowThreeOf153 DH Mc)
    (hDHc : Nat.card DH = 3) (hone : ¬ ∃ g : G, conjSubgroup DH g = DM) {t₂ : G} (ht₂ : t₂ ∈ JM)
    (g : G) : g * z * g⁻¹ ≠ t₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hgz
  have hDMg : conjSubgroup DM g ≤ Mc := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hcomm : (g * x * g⁻¹) * t₂ = t₂ * (g * x * g⁻¹) := hN.comm _ hx t₂ ht₂
    rw [← hgz] at hcomm
    refine mem_Mc_of_commute cx hN.z_gen ?_
    calc z * x = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹)) * g := by rw [← hcomm]
      _ = x * z := by group
  have hD3 : IsPGroup 3 (conjSubgroup DM g) := isPGroup_conjSubgroup153 hN.DM_syl.2.1 g
  obtain ⟨k, hkMc, hkle⟩ := exists_conj_of_isSylow (p := 3) hDH hD3 hDMg
  have hc1 : Nat.card (conjSubgroup DM g) = 3 := by rw [card_conjSubgroup153, hN.card_DM]
  have hc2 : Nat.card (conjSubgroup DH k) = 3 := by rw [card_conjSubgroup153, hDHc]
  have hDeq : conjSubgroup DM g = conjSubgroup DH k :=
    Subgroup.eq_of_le_of_card_ge hkle (by omega)
  refine hone ⟨k * g⁻¹, ?_⟩
  ext x
  have e1 : x ∈ DM ↔ g⁻¹ * x * g ∈ conjSubgroup DM g := by
    rw [mem_conjSubgroup_iff]
    simp [mul_assoc]
  rw [e1, hDeq, mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have : k * (g⁻¹ * x * g) * k⁻¹ = (k * g⁻¹) * x * (k * g⁻¹)⁻¹ := by group
  rw [this]

end Sylow


section Transvection

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem autI_zpowers_eq {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    autI hV (Subgroup.zpowers g) = Subgroup.zpowers (convI hV ⟨g, hg⟩) := by
  ext φ
  rw [mem_autI hV]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext hk
  · rintro hφ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hφ
    refine ⟨⟨g ^ k, Subgroup.zpow_mem _ hg k⟩, Subgroup.zpow_mem_zpowers g k, ?_⟩
    rw [← map_zpow]
    rfl

theorem rk_commV_zpowers_convI {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (h : Nat.card ↥⁅V, Subgroup.zpowers g⁆ = 2) :
    rk (commV (Subgroup.zpowers (convI hV ⟨g, hg⟩))) = 1 := by
  have hz : Subgroup.zpowers g ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le]; exact hg
  have h1 := commutator_eq_map_commV hV hz
  rw [autI_zpowers_eq hV hg] at h1
  have h2 : Nat.card ↥(commV (Subgroup.zpowers (convI hV ⟨g, hg⟩))) = 2 := by
    rw [← h]
    have := Nat.card_congr (Subgroup.equivMapOfInjective
      (commV (Subgroup.zpowers (convI hV ⟨g, hg⟩))) (inclMod hV) (inclMod_injective hV)).toEquiv
    rw [this]
    exact congrArg Nat.card (congrArg (fun H : Subgroup G => ↥H) h1.symm)
  unfold rk
  rw [h2]
  simp

end Transvection


section Lemma60

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem isDicksonEven_of_mem_autOn_U (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx)
    (h52 : Concl15352 cx) {u : MulAut ↥(VZ T M)} (hu : u ∈ autOn (UH153 T M V₁ Mc) (VZ T M)) :
    IsDicksonEven153 cx.c.hyp.elemAbelian u := by
  rcases h51.two with ⟨-, -, -, -, Ω, hΩ, hsyl⟩ | ⟨hab, -, -, -⟩
  · exact ((hΩ u).mp (hsyl.1 hu)).2
  · exfalso
    obtain ⟨a, ha, b, hb, hne⟩ := h52
    exact hne (congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem lemma_15_3_60_two_UCT (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx)
    (h52 : Concl15352 cx) {DM JM : Subgroup G} {v z : G} (hN : N8Data153 cx DM JM v z) {t₂ : G}
    (ht₂T : t₂ ∈ T) (ht₂J : t₂ ∈ JM) (hord : orderOf t₂ = 2) (hV : t₂ ∉ V₁) :
    t₂ ∉ UCT153 T M V₁ Mc := by
  intro hmem
  have hVe := cx.c.hyp.elemAbelian
  have hTM : T ≤ M := cx.c.hyp.T_le
  have hMN := cx.c.hyp.le_normalizer
  have ht₂N : t₂ ∈ Subgroup.normalizer (VZ T M : Set G) := hMN (hTM ht₂T)
  have htr := hN.transv t₂ ht₂J hord hV
  have hCle : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤
      Subgroup.normalizer (UH153 T M V₁ Mc : Set G) :=
    inf_le_left.trans (cx.c.hyp.qtfe.t_le_mc.trans (le_normalizer_conjClosure _ _))
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right
    (T ⊓ Subgroup.centralizer (VZ T M : Set G)) (UH153 T M V₁ Mc) hCle
  have hmem' : t₂ ∈ ((T ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ UH153 T M V₁ Mc : Subgroup G) := by
    rw [sup_comm]; exact hmem
  have hmem'' : t₂ ∈ ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) *
      (UH153 T M V₁ Mc : Set G) := by
    rw [← hmul]; exact hmem'
  obtain ⟨c, hc, u, hu, hcu⟩ := hmem''
  have huN : u ∈ Subgroup.normalizer (VZ T M : Set G) := by
    have huT : u ∈ T := by
      have hUT : UH153 T M V₁ Mc ≤ T :=
        (cx.hF.conjClosure_Vp_le_pCoreOf).trans
          (pCoreOf_two_le_of_isSylowTwoOf cx.hF.sylow_H)
      exact hUT hu
    exact hMN (hTM huT)
  have hφ : convI hVe ⟨t₂, ht₂N⟩ = convI hVe ⟨u, huN⟩ := by
    ext w
    apply IntMod.val_injective
    rw [convI_apply_val, convI_apply_val]
    show t₂ * w.val * t₂⁻¹ = u * w.val * u⁻¹
    have hcu' : c * u = t₂ := hcu
    have hcw : ∀ y ∈ VZ T M, c * y * c⁻¹ = y := fun y hy => by
      have := Subgroup.mem_centralizer_iff.mp hc.2 y hy
      calc c * y * c⁻¹ = (y * c) * c⁻¹ := by rw [← this]
        _ = y := by group
    have huw : u * w.val * u⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp huN w.val).mp w.val_mem
    rw [← hcu']
    calc c * u * w.val * (c * u)⁻¹ = c * (u * w.val * u⁻¹) * c⁻¹ := by group
      _ = u * w.val * u⁻¹ := hcw _ huw
  have hmemU : convI hVe ⟨t₂, ht₂N⟩ ∈ autOn (UH153 T M V₁ Mc) (VZ T M) := by
    rw [hφ]
    exact convI_mem_autI hVe hu huN
  have hd := isDicksonEven_of_mem_autOn_U cx h51 h52 hmemU
  have hrk := rk_commV_zpowers_convI hVe ht₂N htr
  unfold IsDicksonEven153 at hd
  have hd' : Even (rk (commV (Subgroup.zpowers (convI hVe ⟨t₂, ht₂N⟩)))) := hd
  rw [hrk] at hd'
  exact absurd hd' (by decide)

theorem lemma_15_3_60 (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx) (h52 : Concl15352 cx)
    {DM JM : Subgroup G} {v z : G} (hN : N8Data153 cx DM JM v z) {DH : Subgroup G}
    (hDH : IsSylowThreeOf153 DH Mc) (hDHc : Nat.card DH = 3)
    (hH : ∃ R : Subgroup G, IsSylowTwoOf R (Mc ⊓ Subgroup.centralizer (DH : Set G)) ∧
      Nat.card R = 16) : Concl15360 cx DM DH JM z := by
  have hone := lemma_15_3_60_one cx hN hH
  exact ⟨hone,
    fun t₂ ht₂ hord hV => lemma_15_3_60_two_UCT cx h51 h52 hN ht₂.1 ht₂.2 hord hV,
    fun t₂ ht₂ _ _ g => lemma_15_3_60_two_z cx hN hDH hDHc hone ht₂.2 g⟩


theorem lemma_15_3_61_one (cx : Ctx15350 T Mc M V₁ V₂ t) {DM JM : Subgroup G} {v z : G}
    (hN : N8Data153 cx DM JM v z) {DH : Subgroup G} (hDH : IsSylowThreeOf153 DH Mc)
    (hDHc : Nat.card DH = 3) (hone : ¬ ∃ g : G, conjSubgroup DH g = DM) {t₂ : G}
    (hcent : ∃ h ∈ Mc, ∀ d ∈ DH, t₂ * (h * d * h⁻¹) = (h * d * h⁻¹) * t₂) :
    ∀ g : G, g * v * g⁻¹ ≠ t₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g hgv
  obtain ⟨h, -, hh⟩ := hcent
  have hD₂c : ∀ d ∈ conjSubgroup DH h⁻¹, t₂ * d = d * t₂ := by
    intro d hd
    rw [mem_conjSubgroup_iff] at hd
    have := hh _ hd
    simpa [mul_assoc] using this
  have hD₃le : conjSubgroup (conjSubgroup DH h⁻¹) g ≤ Subgroup.centralizer ({v} : Set G) := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    have h1 := hD₂c _ hx
    rw [← hgv] at h1
    calc v * x = g⁻¹ * ((g * v * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h1]
      _ = x * v := by group
  have hD₃p : IsPGroup 3 (conjSubgroup (conjSubgroup DH h⁻¹) g) :=
    isPGroup_conjSubgroup153 (isPGroup_conjSubgroup153 hDH.2.1 h⁻¹) g
  obtain ⟨k, -, hkle⟩ := exists_conj_of_isSylow (p := 3) hN.DM_syl_v hD₃p hD₃le
  have hc1 : Nat.card (conjSubgroup (conjSubgroup DH h⁻¹) g) = 3 := by
    rw [card_conjSubgroup153, card_conjSubgroup153, hDHc]
  have hc2 : Nat.card (conjSubgroup DM k) = 3 := by rw [card_conjSubgroup153, hN.card_DM]
  have hDeq : conjSubgroup (conjSubgroup DH h⁻¹) g = conjSubgroup DM k :=
    Subgroup.eq_of_le_of_card_ge hkle (by omega)
  refine hone ⟨h⁻¹ * g * k⁻¹, ?_⟩
  have e1 := congrArg (fun A => conjSubgroup A k⁻¹) hDeq
  simp only [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at e1
  exact e1

end Lemma60

end S153E

end CFSG.Quasithin
