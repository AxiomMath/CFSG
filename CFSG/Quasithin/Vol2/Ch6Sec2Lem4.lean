module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem2
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Sub
public import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem IsInvolutoryFieldAut.conj_ch6 {t x : G} (ht : IsInvolutoryFieldAut L t)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) : IsInvolutoryFieldAut L (x⁻¹ * t * x) := by
  have hxO : x ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hx
  obtain ⟨htN, ht2, htout⟩ := ht
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) htN) hx,
    fun y hy => ?_, ?_⟩
  · have hy' : x * y * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxO) _).mp (ht2 _ hy')
    convert h2 using 1
    simp only [sq]
    group
  · rintro ⟨y, hy, hyx⟩
    apply htout
    refine ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y).mp hy, fun z hz => ?_⟩
    have hz' : x⁻¹ * z * x⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) z).mp hz
    rw [inv_inv] at hz'
    have h2 := (Subgroup.mem_normalizer_iff.mp hxO _).mp (hyx _ hz')
    convert h2 using 1
    group

omit [Finite G] in
theorem mem_normalizer_centralizer_ch62 {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * x := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g * x * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have := hc _ hx'
    calc x * c = g⁻¹ * ((g * x * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by rw [this]
      _ = c * x := by group

omit [Finite G] in
theorem mem_centralizer_of_odd_ch62 {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    {g : G} {o : ℕ} (ho : Odd o) (hgo : g ^ o = 1) (hgU : ∀ u ∈ U, g * u = u * g)
    (hgV : ∀ a ∈ V, g * a * g⁻¹ * a⁻¹ ∈ U) : g ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨u, hudef⟩ : ∃ u, u = g * a * g⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hu : u ∈ U := hudef ▸ hgV a ha
  have hga : g * a * g⁻¹ = u * a := by rw [hudef]; group
  have hk : ∀ k : ℕ, g ^ k * a * (g ^ k)⁻¹ = u ^ k * a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hgu : g * u ^ k * g⁻¹ = u ^ k := by
        rw [hgU _ (U.pow_mem hu k), mul_inv_cancel_right]
      calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (u ^ k * a) * g⁻¹ := by rw [ih]
        _ = (g * u ^ k * g⁻¹) * (g * a * g⁻¹) := by group
        _ = u ^ (k + 1) * a := by rw [hgu, hga, pow_succ]; group
  have h1 := hk o
  rw [hgo, one_mul, inv_one, mul_one] at h1
  have huo : u ^ o = 1 := by
    have := congrArg (· * a⁻¹) h1
    simpa using this.symm
  have hu2 : u ^ 2 = 1 := hV.2 u (hUV hu)
  obtain ⟨m, rfl⟩ := ho
  have hu1 : u = 1 := by
    have : u ^ (2 * m + 1) = (u ^ 2) ^ m * u := by rw [pow_succ, pow_mul]
    rw [this, hu2, one_pow, one_mul] at huo
    exact huo
  have : g * a * g⁻¹ = a := by rw [hga, hu1, one_mul]
  calc a * g = (g * a * g⁻¹) * g := by rw [this]
    _ = g * a := by group

omit [Finite G] in
theorem mem_normalizer_conjClosure_ch62 {Z H : Subgroup G} {g : G}
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ k : G, k ∈ Subgroup.normalizer (Z : Set G) →
      k ∈ Subgroup.normalizer (H : Set G) →
      ∀ x ∈ conjClosure Z H, k * x * k⁻¹ ∈ conjClosure Z H := by
    intro k hkZ hkH x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, z, hz, rfl⟩ := hx
      have ha' : k * a * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hkH a).mp ha
      have hz' : k * z * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hkZ z).mp hz
      have := mem_conjClosure ha' hz'
      convert this using 1
      group
    | one => simp
    | mul x y _ _ ihx ihy =>
      have := (conjClosure Z H).mul_mem ihx ihy
      convert this using 1
      group
    | inv x _ ih =>
      have := (conjClosure Z H).inv_mem ih
      convert this using 1
      group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hgZ hgH x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hgZ) (Subgroup.inv_mem _ hgH) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_centralizerMod_ch62 {V₁ X U : Subgroup G} {g : G}
    (h1 : g ∈ Subgroup.normalizer (V₁ : Set G)) (h2 : g ∈ Subgroup.normalizer (X : Set G))
    (h3 : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer (centralizerMod V₁ X U : Set G) := by
  have key : ∀ k : G, k ∈ Subgroup.normalizer (V₁ : Set G) →
      k ∈ Subgroup.normalizer (X : Set G) → k ∈ Subgroup.normalizer (U : Set G) →
      ∀ x ∈ centralizerMod V₁ X U, k * x * k⁻¹ ∈ centralizerMod V₁ X U := by
    intro k hk1 hk2 hk3 x hx
    obtain ⟨hxX, hxN, hxU⟩ := mem_centralizerMod.mp hx
    refine mem_centralizerMod.mpr ⟨(Subgroup.mem_normalizer_iff.mp hk2 x).mp hxX,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk1 hxN) (Subgroup.inv_mem _ hk1), fun u hu => ?_⟩
    have hu' : k⁻¹ * u * k ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk3) u).mp hu
      rwa [inv_inv] at this
    have h4 := (Subgroup.mem_normalizer_iff.mp hk1 _).mp (hxU _ hu')
    convert h4 using 1
    group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g h1 h2 h3 x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ h1) (Subgroup.inv_mem _ h2) (Subgroup.inv_mem _ h3) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_ch62 {x : G} {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro y
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem card_of_mQuot_two {U : Subgroup G} (hUV : U ≤ V) (hm : mQuot V U = 2) :
    Nat.card U = 4 := by
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  have h1 := card_eq_two_pow_mul hV2 hUV
  rw [hm, h.natural.card_eq] at h1
  omega

theorem exists_fieldAut_of_not_le (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612)
    {U : Subgroup G} (hUV : U ≤ V) (hm : mQuot V U = 2)
    (hH : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hTU : IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G))
      (M ⊓ Subgroup.normalizer (U : Set G))) :
    ∃ t ∈ T, IsInvolutoryFieldAut L t ∧ U = V ⊓ Subgroup.centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUcard := h.card_of_mQuot_two hUV hm
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hUcard
    omega
  rcases stmt6_1_13 h432 h6110 hE612 G T M L V 2 h.toHyp611Nat U hUV hm with
    hC | ⟨l, hl, hl'⟩ | ⟨-, t, htM, hinv, htU⟩
  · exact absurd hC hH
  ·
    exfalso
    apply hH
    have hlN : l ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.L_le_normalizer hl
    have h1 := conjSubgroup_mono_left l h.centralizer_ZS_le_normalizer_V
    rw [conjSubgroup_centralizer, conjSubgroup_normalizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr hlN] at h1
    rw [hl']
    exact h1
  obtain ⟨t₂, ht₂M, ⟨k, hk⟩, hinv₂, hCt⟩ :=
    h.toHyp611Nat.exists_two_element_fieldAut htM hinv (le_of_eq (by rw [← htU, hUcard]; rfl))
  have htU₂ : U = V ⊓ Subgroup.centralizer ({t₂} : Set G) := htU.trans hCt
  have ht₂C : t₂ ∈ Subgroup.centralizer (U : Set G) := by
    rw [htU₂]
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hu.2 t₂ rfl).symm
  have ht₂N : t₂ ∈ M ⊓ Subgroup.normalizer (U : Set G) :=
    ⟨ht₂M, Subgroup.centralizer_le_normalizer _ ht₂C⟩
  have hzP : IsPGroup 2 (Subgroup.zpowers t₂) := by
    intro x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨x, hx, hle⟩ := F7.isSylowTwoOf_exists_conj_le hTU (Subgroup.zpowers_le.mpr ht₂N) hzP
  obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_zpowers t₂))
  have hyt' : y = x⁻¹ * t₂ * x := by
    rw [← hyt]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := (h.toHyp611Nat.normalizer_le hU1 hUV hx).2
  refine ⟨y, hy.1, hyt' ▸ hinv₂.conj_ch6 (h.normal hx.1), ?_⟩
  ext u
  have hiff : u ∈ U ↔ x * u * x⁻¹ ∈ U := Subgroup.mem_normalizer_iff.mp hx.2 u
  have hiffV : u ∈ V ↔ x * u * x⁻¹ ∈ V := Subgroup.mem_normalizer_iff.mp hxV u
  rw [hiff]
  conv_lhs => rw [htU₂]
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hiffV, hyt']
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    calc u * (x⁻¹ * t₂ * x) = x⁻¹ * ((x * u * x⁻¹) * t₂) * x := by group
      _ = x⁻¹ * (t₂ * (x * u * x⁻¹)) * x := by rw [hc]
      _ = x⁻¹ * t₂ * x * u := by group
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    calc x * u * x⁻¹ * t₂ = x * (u * (x⁻¹ * t₂ * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * t₂ * x) * u) * x⁻¹ := by rw [hc]
      _ = t₂ * (x * u * x⁻¹) := by group

end Hyp6Sec2

namespace Hyp611Nat

variable (h : Hyp611Nat G T M L V 2)
include h

theorem card_stabSub_fix_two {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t) :
    Nat.card ↥(stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩)) = 6 := by
  classical
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, hc⟩ := h.exists_fieldAut_data htT ht
  have h2 : Nat.card ↥(stabFixField σ) = 2 := Nat.mul_self_inj.mp (by rw [hc]; norm_num)
  rw [← range_slFormHom hσ hu₁ hu₂ hdet,
    ← Nat.card_congr (MonoidHom.ofInjective (slFormHom_injective (σ := σ) hdet)).toEquiv]
  have : Fintype ↥(stabFixField σ) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, h2]
  decide

theorem rho_mem_stabSub_fix {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t) {ℓ : ↥L}
    (hℓ : (ℓ : G) ∈ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)) :
    h.data.rho ℓ ∈ stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩) := by
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, -⟩ := h.exists_fieldAut_data htT ht
  have hfix : ∀ {w}, h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ w = w →
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩
        (((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
          Matrix (Fin 2) (Fin 2) h.data.K).mulVec w) =
        ((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
          Matrix (Fin 2) (Fin 2) h.data.K).mulVec w := by
    intro w hw
    rw [← h.data.conj_eq_rho, ← h.mem_addSub_fix_iff htT]
    exact h.conj_mem_addSub _ hℓ ((h.mem_addSub_fix_iff htT w).mpr hw)
  exact mem_stabSub_of_basis hσ hu₁ hu₂ hdet (hfix hu₁) (hfix hu₂)

theorem card_map_lOne_fix_two {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t) :
    Nat.card ↥(((lOne L (V ⊓ Subgroup.centralizer ({t} : Set G))).subgroupOf L).map
      h.data.rho) = 3 := by
  classical
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set g := h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ with hg
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, -⟩ := h.exists_fieldAut_data htT ht
  obtain ⟨B₀, hB₀S, hB₀1, hB₀3⟩ := exists_mem_stabSub_order_three hσ hu₁ hu₂ hdet
  have horder : orderOf B₀ = 3 := orderOf_eq_prime hB₀3 hB₀1
  have hP : Nat.card ↥(Subgroup.zpowers B₀) = 3 := by rw [Nat.card_zpowers, horder]
  have hPS : Subgroup.zpowers B₀ ≤ stabSub g := Subgroup.zpowers_le.mpr hB₀S
  have hidx : ((Subgroup.zpowers B₀).subgroupOf (stabSub g)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((Subgroup.zpowers B₀).subgroupOf (stabSub g))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv, hP,
      h.card_stabSub_fix_two htT ht] at h1
    omega
  have hodd : ∀ B ∈ stabSub g, Odd (orderOf B) → B ∈ Subgroup.zpowers B₀ := by
    intro B hB hBo
    have hsq := Subgroup.sq_mem_of_index_two hidx ⟨B, hB⟩
    rw [Subgroup.mem_subgroupOf] at hsq
    obtain ⟨k, hk⟩ := hBo
    have e : B = (B ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf B + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [e]
    exact Subgroup.pow_mem _ (by simpa using hsq) _
  have hle : ((lOne L U).subgroupOf L).map h.data.rho ≤ Subgroup.zpowers B₀ := by
    have key : lOne L U ≤ ((Subgroup.zpowers B₀).comap h.data.rho).map L.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨⟨hxL, hxN⟩, hxo⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      show h.data.rho ⟨x, hxL⟩ ∈ Subgroup.zpowers B₀
      refine hodd _ (h.rho_mem_stabSub_fix htT ht hxN) ?_
      have h1 : orderOf (h.data.rho ⟨x, hxL⟩) ∣ orderOf (⟨x, hxL⟩ : ↥L) := orderOf_map_dvd _ _
      have h2 : orderOf (⟨x, hxL⟩ : ↥L) = orderOf x := Subgroup.orderOf_mk x hxL
      rw [h2] at h1
      exact hxo.of_dvd_nat h1
    rintro _ ⟨ℓ, hℓ, rfl⟩
    obtain ⟨ℓ', hℓ', hℓℓ'⟩ := key (Subgroup.mem_subgroupOf.mp hℓ)
    have : ℓ' = ℓ := Subtype.ext hℓℓ'
    rw [← this]
    exact hℓ'
  have hB₀Y : B₀ ∈ ((lOne L U).subgroupOf L).map h.data.rho := by
    obtain ⟨ℓ, hℓ, hρ⟩ := h.exists_mem_lOne_of_comm htT B₀ (fun w => (mem_stabSub.mp hB₀S w))
      (by decide : Odd 3) hB₀3
    exact ⟨ℓ, Subgroup.mem_subgroupOf.mpr hℓ, hρ⟩
  have heq : ((lOne L U).subgroupOf L).map h.data.rho = Subgroup.zpowers B₀ :=
    le_antisymm hle (Subgroup.zpowers_le.mpr hB₀Y)
  rw [heq, hP]

theorem lOne_fix_two {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t) :
    Nat.card ↥(lOne L (V ⊓ Subgroup.centralizer ({t} : Set G))) =
        3 * Nat.card ↥(pCoreOf 2 (lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)))) ∧
      pCoreOf 2 (lOne L (V ⊓ Subgroup.centralizer ({t} : Set G))) =
        lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) ⊓
          Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set LU := lOne L U with hLU
  have hLUL : LU ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hLUN : LU ≤ Subgroup.normalizer (U : Set G) := (oTwoUpper_le _).trans inf_le_right
  have hLUV : LU ≤ Subgroup.normalizer (V : Set G) := hLUL.trans h.data.le_normalizer
  have h3 := h.card_map_lOne_fix_two htT ht
  have hker : (Subgroup.centralizer (V : Set G)).comap L.subtype = h.data.rho.ker := by
    ext ℓ
    rw [Subgroup.mem_comap, h.data.mem_ker_rho_iff]
    rfl
  have hidx : (Subgroup.centralizer (V : Set G)).relIndex LU = 3 := by
    have h1 := Subgroup.relIndex_comap (H := Subgroup.centralizer (V : Set G)) L.subtype
      (LU.subgroupOf L)
    rw [hker, Subgroup.relIndex_ker, Subgroup.map_subgroupOf_eq_of_le hLUL, h3] at h1
    exact h1.symm
  have hUV : U ≤ V := inf_le_left
  have hK₀ : Subgroup.centralizer (V : Set G) ⊓ LU =
      LU ⊓ Subgroup.centralizer (U : Set G) := by
    apply le_antisymm
    · rintro x ⟨hxV, hx⟩
      exact ⟨hx, Subgroup.centralizer_le (show (U : Set G) ⊆ V from hUV) hxV⟩
    · rintro x ⟨hx, hxU⟩
      exact ⟨h.mem_centralizer_V_of_U htT ht (hLUL hx) hxU, hx⟩
  have hO2 : pCoreOf 2 LU = Subgroup.centralizer (V : Set G) ⊓ LU := by
    apply le_antisymm
    · intro x hx
      have hxLU : x ∈ LU := CFSG.LieType.BorelTits.pCoreOf_le 2 LU hx
      refine ⟨?_, hxLU⟩
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LU) ⟨x, hx⟩
      have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      set ℓ : ↥L := ⟨x, hLUL hxLU⟩ with hℓ
      have hρY : h.data.rho ℓ ∈ (LU.subgroupOf L).map h.data.rho :=
        ⟨ℓ, Subgroup.mem_subgroupOf.mpr hxLU, rfl⟩
      have hd3 : orderOf (h.data.rho ℓ) ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard _ hρY
        rwa [h3] at this
      have hd2 : orderOf (h.data.rho ℓ) ∣ 2 ^ k := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow]
        have : ℓ ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
        rw [this, map_one]
      have hd1 : orderOf (h.data.rho ℓ) = 1 := by
        have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
        exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd3 hcop) hd2
      have h1 : h.data.rho ℓ = 1 := orderOf_eq_one_iff.mp hd1
      exact (h.data.mem_ker_rho_iff ℓ).mp h1
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
      · intro x hx
        have hxC := mem_normalizer_centralizer_ch62 (hLUV hx)
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hxC y]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, LU.mul_mem (LU.mul_mem hx h2) (LU.inv_mem hx)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := LU.mul_mem (LU.mul_mem (LU.inv_mem hx) h2) hx
          simpa [mul_assoc] using this
      · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le (fun x hx =>
          h.mem_pCoreOf_of_rho_eq_one (ℓ := ⟨x, hLUL hx.2⟩)
            ((h.data.mem_ker_rho_iff _).mpr hx.1))
  have hcard := Subgroup.relIndex_mul_card (Subgroup.centralizer (V : Set G)) LU
  rw [hidx] at hcard
  refine ⟨?_, hO2.trans hK₀⟩
  rw [hO2, ← hcard]

theorem exists_mem_normalizer_not_centralizer_fix {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    ∃ ℓ ∈ L, ℓ ∈ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
      ℓ ∉ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
      ℓ * ℓ ∈ Subgroup.centralizer (V : Set G) := by
  classical
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, -⟩ := h.exists_fieldAut_data htT ht
  set B := slFormHom σ u₁ u₂ hdet (SL2Model.e12 1) with hB
  have hBS : B ∈ stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩) := by
    rw [← range_slFormHom hσ hu₁ hu₂ hdet]
    exact ⟨_, rfl⟩
  have hB1 : B ≠ 1 := by
    intro h1
    have h2 : SL2Model.e12 (1 : ↥(stabFixField σ)) = SL2Model.e12 0 := by
      apply slFormHom_injective hdet
      rw [← hB, h1, SL2Model.e12_zero, map_one]
    exact one_ne_zero (SL2Model.e12_injective h2)
  have hB2 : B * B = 1 := by
    have h11 : (1 : ↥(stabFixField σ)) + 1 = 0 :=
      Subtype.ext (by simpa using CharTwo.add_self_eq_zero (1 : h.data.K))
    rw [hB, ← map_mul, ← SL2Model.e12_add, h11, SL2Model.e12_zero, map_one]
  obtain ⟨ℓ, hℓ⟩ := h.data.rho_surjective B
  have hℓU : (ℓ : G) ∈ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    refine h.mem_normalizer_fix_of_comm htT ⟨ℓ, h.data.le_normalizer ℓ.2⟩ fun w => ?_
    rw [h.data.conj_eq_rho, h.data.conj_eq_rho, hℓ]
    exact mem_stabSub.mp hBS w
  refine ⟨ℓ, ℓ.2, hℓU, fun hC => hB1 ?_, ?_⟩
  · have hV := h.mem_centralizer_V_of_U htT ht ℓ.2 hC
    rw [← hℓ]
    exact (h.data.mem_ker_rho_iff ℓ).mpr hV
  · have : ℓ * ℓ ∈ h.data.rho.ker := by rw [MonoidHom.mem_ker, map_mul, hℓ, hB2]
    exact (h.data.mem_ker_rho_iff _).mp this

end Hyp611Nat

omit [Finite G] in
theorem mem_normalizer_oTwoUpper_ch62 {C P : Subgroup G} {x : G} (hP : IsPGroup 2 P)
    (hPY : P ≤ Subgroup.normalizer (oTwoUpper C : Set G))
    (hx : ∀ y ∈ oTwoUpper C, x * y * x⁻¹ * y⁻¹ ∈ P)
    (hx' : ∀ y ∈ oTwoUpper C, x⁻¹ * y * x * y⁻¹ ∈ P) :
    x ∈ Subgroup.normalizer (oTwoUpper C : Set G) := by
  have key : ∀ k : G, (∀ y ∈ oTwoUpper C, k * y * k⁻¹ * y⁻¹ ∈ P) →
      ∀ y ∈ oTwoUpper C, k * y * k⁻¹ ∈ oTwoUpper C := by
    intro k hk y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyC, hyo⟩ := hy
      have hyY : y ∈ oTwoUpper C := Subgroup.subset_closure ⟨hyC, hyo⟩
      set p := k * y * k⁻¹ * y⁻¹ with hp
      have hpP : p ∈ P := hk y hyY
      have hpN := hPY hpP
      set y₁ := p * y * p⁻¹ with hy₁
      have hy₁Y : y₁ ∈ oTwoUpper C := (Subgroup.mem_normalizer_iff.mp hpN y).mp hyY
      have hxe : k * y * k⁻¹ = y₁ * p := by rw [hy₁, hp]; group
      obtain ⟨j, hj⟩ := hP ⟨p, hpP⟩
      have hpj : p ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have hpow := mul_pow_mul_inv_pow_mem_ch6 hy₁Y hpN (2 ^ j)
      rw [hpj, inv_one, mul_one, ← hxe] at hpow
      have hord : orderOf (k * y * k⁻¹) = orderOf y := by
        have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
        simpa [MulAut.conj_apply] using this
      have hodd : Odd (orderOf (k * y * k⁻¹)) := hord ▸ hyo
      have hcop : Nat.Coprime (2 ^ j) (orderOf (k * y * k⁻¹)) :=
        Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
      exact (Subgroup.zpowers_le.mpr hpow) (A4.mem_zpowers_pow_of_coprime hcop)
    | one => simp
    | mul a b _ _ iha ihb =>
      have := (oTwoUpper C).mul_mem iha ihb
      convert this using 1
      group
    | inv a _ ih =>
      have := (oTwoUpper C).inv_mem ih
      convert this using 1
      group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (by simpa using hx') _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem relIndex_sup_zpowers_eq_two_ch62 {Q : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (Q : Set G)) (htQ : t ∉ Q) (ht2 : t * t ∈ Q) :
    Q.relIndex (Subgroup.zpowers t ⊔ Q) = 2 := by
  have hN : Subgroup.zpowers t ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr htN
  have : (Q.subgroupOf (Subgroup.zpowers t ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hN
  have : (Q.subgroupOf (Subgroup.zpowers t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hN
  have h1 : Q.relIndex (Subgroup.zpowers t ⊔ Q) = Q.relIndex (Subgroup.zpowers t) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient _ Q hN).toEquiv.symm
  rw [h1]
  show (Q.subgroupOf (Subgroup.zpowers t)).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t, Subgroup.mem_zpowers t⟩, ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hev : ∀ j : ℤ, t ^ (2 * j) ∈ Q := fun j => by
    rw [zpow_mul, zpow_two]
    exact Q.zpow_mem ht2 j
  have hodd : ∀ j : ℤ, t ^ (2 * j + 1) ∉ Q := fun j hj => by
    apply htQ
    have := Q.mul_mem hj (Q.inv_mem (hev j))
    rwa [show t ^ (2 * j + 1) = t * t ^ (2 * j) by rw [add_comm, zpow_add, zpow_one],
      mul_inv_cancel_right] at this
  have e : t ^ k * t = t ^ (k + 1) := by rw [zpow_add_one]
  rw [e]
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j + 1 = 2 * j + 1 by ring, show j + j = 2 * j by ring]
    exact Or.inr ⟨hev j, hodd j⟩
  · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    exact Or.inl ⟨hev (j + 1), hodd j⟩

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem relIndex_Q_T (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) : (ch6Q T V).relIndex T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := h.card_autOn_sup h331 h615
  rw [card_autOn_eq_relIndex h.toHyp611.sup_le_normalizer] at hX
  have hQ : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = ch6Q T V := by
    apply le_antisymm
    · intro x hx
      have hxT : x ∈ T :=
        ((h.toHyp5_0_1.sup_inf_centralizer_le_pCoreOf h.toHyp611.sup_le_normalizer
          h.module.2.2).trans (by rw [← h.toHyp611.centralizer_eq]; exact inf_le_left)) hx
      exact ⟨hxT, hx.2⟩
    · exact fun x hx => ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
  rw [hQ] at hX
  have hmul := Subgroup.relIndex_mul_relIndex (ch6Q T V) T (L ⊔ T) inf_le_left le_sup_right
  rw [hX] at hmul
  have hodd : ¬ 2 ∣ T.relIndex (L ⊔ T) := (h.toHyp5_0_1.isSylowTwoOf le_sup_right).2.2
  obtain ⟨b, hb⟩ := h.sylow.1.exists_card_eq
  have hdvd : (ch6Q T V).relIndex T ∣ 2 ^ b := hb ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [ha] at hmul ⊢
  have ha7 : a < 7 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hc
    have hpos : 0 < T.relIndex (L ⊔ T) := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hmul
    nlinarith
  interval_cases a <;> omega

theorem relIndex_normalizer_fix (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))) :
    (T ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)).relIndex T = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set TU := T ⊓ Subgroup.normalizer (U : Set G) with hTU
  set R := T ⊓ Subgroup.centralizer (U : Set G) with hRdef
  set Q := ch6Q T V with hQdef
  have hUV : U ≤ V := inf_le_left
  have htC : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  have hQC : Q ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.centralizer_le (show (U : Set G) ⊆ V from hUV) hx.2
  have hR : R = Subgroup.zpowers t ⊔ Q := by
    apply le_antisymm
    · have := h.toHyp611Nat.centralizer_fix_le htT ht
      rwa [sup_comm] at this
    · refine sup_le ?_ fun x hx => ⟨hx.1, hQC hx⟩
      rw [Subgroup.zpowers_le]
      exact ⟨htT, htC⟩
  have htQN : t ∈ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ⟨T.mul_mem (T.mul_mem htT hx.1)
      (T.inv_mem htT), ?_⟩, fun hx => ⟨?_, ?_⟩⟩
    · exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_ch62
        (h.toHyp611.T_le_normalizer htT)) x).mp hx.2
    · have := T.mul_mem (T.mul_mem (T.inv_mem htT) hx.1) htT
      simpa [mul_assoc] using this
    · exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_ch62
        (h.toHyp611.T_le_normalizer htT)) x).mpr hx.2
  have htQ : t ∉ Q := fun hq => h.toHyp611Nat.not_mem_centralizer_of_fieldAut htT ht hq.2
  have ht2Q : t * t ∈ Q :=
    ⟨T.mul_mem htT htT, h.toHyp611Nat.sq_mem_centralizer_of_fieldAut htT ht⟩
  have hQR : Q.relIndex R = 2 := by
    rw [hR]
    exact relIndex_sup_zpowers_eq_two_ch62 htQN htQ ht2Q
  have hRTU_le : R ≤ TU := fun x hx => ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  have hTUR : TU ⊓ Subgroup.centralizer (U : Set G) = R := by
    ext x
    simp only [hTU, hRdef, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩,
      hx.2⟩⟩
  have hRTU : R.relIndex TU = 2 := by
    have hcardA := card_autOn_eq_relIndex (V := U) (inf_le_right : TU ≤ _)
    rw [hTUR] at hcardA
    have hU4 : Nat.card U = 4 := by
      have := h.toHyp611Nat.card_fix_of_fieldAut htT ht
      rw [← hU] at this
      rw [this]; norm_num
    have hKlein : IsKleinFour ↥U := by
      refine ⟨hU4, ?_⟩
      have hsq : ∀ x : ↥U, x ^ 2 = 1 := fun x =>
        Subtype.ext (by simpa using h.toHyp611.isElemAbelian.2 x (hUV x.2))
      rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
        h1 | h1
      · have : Subsingleton ↥U := Monoid.exp_eq_one_iff.mp h1
        have := Nat.card_of_subsingleton (1 : ↥U)
        omega
      · exact h1
    have h6 : Nat.card (MulAut ↥U) = 6 := CFSG.GorensteinWalter.kleinFourAut_card ↥U
    have hdvd6 : R.relIndex TU ∣ 6 := by
      rw [← hcardA, ← h6]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨c, hc⟩ := (h.sylow.1.to_le (inf_le_left : TU ≤ T)).exists_card_eq
    have hdvd2 : R.relIndex TU ∣ 2 ^ c := hc ▸ Subgroup.relIndex_dvd_card _ _
    obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
    rw [hd] at hdvd6 ⊢
    have hd0 : d ≠ 0 := by
      rintro rfl
      obtain ⟨ℓ, hℓL, hℓN, hℓC, hℓ2⟩ := h.toHyp611Nat.exists_mem_normalizer_not_centralizer_fix
        htT ht
      have hℓO : ℓ * ℓ ∈ pCoreOf 2 L :=
        h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one (ℓ := ⟨ℓ * ℓ, L.mul_mem hℓL hℓL⟩)
          ((h.data.mem_ker_rho_iff _).mpr hℓ2)
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨ℓ * ℓ, hℓO⟩
      have hk' : ℓ ^ 2 ^ (k + 1) = 1 := by
        have : (ℓ * ℓ) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [pow_succ', pow_mul, sq]
        exact this
      have hsylN := (h.toHyp611Nat.lemma_6_1_14_one h432 htT ht hSyl).2.2
      obtain ⟨x, hx, hle⟩ := F7.isSylowTwoOf_exists_conj_le hsylN
        (Subgroup.zpowers_le.mpr hℓN) (isPGroup_zpowers_of_pow_ch62 hk')
      obtain ⟨y, hy, hyℓ⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_zpowers ℓ))
      have hyR : y ∈ R := by
        have hle1 : TU ≤ R := by
          have := Subgroup.relIndex_eq_one.mp (by rw [pow_zero] at hd; exact hd)
          exact this
        exact hle1 hy
      apply hℓC
      rw [← hyℓ]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have hu' : x⁻¹ * u * x ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) u).mp hu
        rwa [inv_inv] at this
      have hc := Subgroup.mem_centralizer_iff.mp hyR.2 _ hu'
      calc u * (x * y * x⁻¹) = x * ((x⁻¹ * u * x) * y) * x⁻¹ := by group
        _ = x * (y * (x⁻¹ * u * x)) * x⁻¹ := by rw [hc]
        _ = x * y * x⁻¹ * u := by group
    have hd1 : d ≤ 1 := by
      by_contra hc
      push Not at hc
      have h4 : 2 ^ 2 ∣ 2 ^ d := pow_dvd_pow 2 hc
      have := h4.trans hdvd6
      norm_num at this
    interval_cases d
    · exact absurd rfl hd0
    · rfl
  have hQTU : Q.relIndex TU = 4 := by
    rw [← Subgroup.relIndex_mul_relIndex Q R TU (hR ▸ le_sup_right) hRTU_le, hQR, hRTU]
  have h8 := h.relIndex_Q_T h331 h615
  have hmul := Subgroup.relIndex_mul_relIndex Q TU T (hRTU_le.trans' (hR ▸ le_sup_right))
    inf_le_left
  rw [hQTU, h8] at hmul
  omega

theorem not_TL_le_normalizer_fix {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t) :
    ¬ T ⊓ L ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  intro hle
  obtain ⟨v, hv, hlev⟩ := h.toHyp611Nat.exists_line
  have h4 : Nat.card ↥h.toHyp611Nat.rhoTL = 4 := by
    rw [h.toHyp611Nat.rhoTL_eq_stab hv hlev, card_sl2Stab hv, h.data.card]
    norm_num
  have hsub : h.toHyp611Nat.rhoTL ≤ stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩) := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact h.toHyp611Nat.rho_mem_stabSub_fix htT ht (hle (Subgroup.mem_subgroupOf.mp hℓ))
  have hdvd := Subgroup.card_dvd_of_le hsub
  rw [h4, h.toHyp611Nat.card_stabSub_fix_two htT ht] at hdvd
  norm_num at hdvd

theorem lemma_6_2_4_four (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)))
    (hH : ¬ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V : Set G)) :
    let U := V ⊓ Subgroup.centralizer ({t} : Set G)
    let H := Subgroup.centralizer (U : Set G)
    IsElemAbelian 2 (conjClosure V H) ∧ conjClosure V H ≤ pCoreOf 2 H ∧
      ⁅conjClosure V H, pCoreOf 2 H⁆ ≤ U ∧ centralizerMod U H (conjClosure V H) = pCoreOf 2 H ∧
      IsReducedMod H (conjClosure V H) U := by
  classical
  intro U H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (U : Set G) with hN
  set UH := conjClosure V H with hUH
  set VU := conjClosure V N with hVU
  obtain ⟨hVUab, -, hcomm⟩ := h.toHyp611Nat.lemma_6_1_14_four h432 h6110 htT ht hSyl
  have hUV : U ≤ V := inf_le_left
  have hV := h.toHyp611.isElemAbelian
  have hU4 : Nat.card U = 4 := by
    have := h.toHyp611Nat.card_fix_of_fieldAut htT ht
    rw [this]; norm_num
  have hU1 : U ≠ ⊥ := by
    intro h0
    have : Nat.card U = 1 := by rw [h0, Subgroup.card_bot]
    omega
  have hHN : H ≤ N := Subgroup.centralizer_le_normalizer _
  have hVH : V ≤ H := fun v hv => Subgroup.mem_centralizer_iff.mpr fun u hu =>
    B2F.isElemAbelian_comm hV (hUV hu) hv
  have hUHH : UH ≤ H :=
    conjClosure_le fun a ha z hz => H.mul_mem (H.mul_mem ha (hVH hz)) (H.inv_mem ha)
  have hHUH : H ≤ Subgroup.normalizer (UH : Set G) := le_normalizer_conjClosure V H
  have hUHVU : UH ≤ VU := conjClosure_mono le_rfl hHN
  have hUHab : IsElemAbelian 2 UH :=
    ⟨isMulCommutative_iff.mpr fun a b =>
        Subtype.ext (B2F.isElemAbelian_comm hVUab (hUHVU a.2) (hUHVU b.2)),
      fun x hx => hVUab.2 x (hUHVU hx)⟩
  have hUH2 : IsPGroup 2 UH := B2F.isPGroup_of_isElemAbelian hUHab
  have hUHO : UH ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUHH hHUH hUH2
  have hO2 : pCoreOf 2 H ≤ pCoreOf 2 N := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHN) (fun g hg => ?_)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H
      (mem_normalizer_centralizer_ch62 hg)
  have hcommUH : ⁅UH, pCoreOf 2 H⁆ ≤ U :=
    calc ⁅UH, pCoreOf 2 H⁆ ≤ ⁅VU, pCoreOf 2 N⁆ := Subgroup.commutator_mono hUHVU hO2
      _ = ⁅pCoreOf 2 N, VU⁆ := Subgroup.commutator_comm _ _
      _ ≤ U := hcomm
  set C := centralizerMod U H UH with hC
  have hCH : C ≤ H := fun x hx => (mem_centralizerMod.mp hx).1
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizerMod_ch62 (hHN hg) (Subgroup.le_normalizer hg) (hHUH hg)
  have hOC : pCoreOf 2 H ≤ C := by
    intro x hx
    refine mem_centralizerMod.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H hx,
      hHN (CFSG.LieType.BorelTits.pCoreOf_le 2 H hx), fun u hu => ?_⟩
    have := Subgroup.commutator_mem_commutator hx hu
    rw [Subgroup.commutator_comm] at this
    exact hcommUH this
  have hY : oTwoUpper C = ⊥ := by
    by_contra hYne
    set Y := oTwoUpper C with hYdef
    have hYC : Y ≤ C := oTwoUpper_le C
    have hCV : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
      intro c hc v hv
      obtain ⟨-, -, hcU⟩ := mem_centralizerMod.mp hc
      have h1 := hcU v (le_conjClosure V H hv)
      have : c * v * c⁻¹ = (c * v * c⁻¹ * v⁻¹) * v := by group
      rw [this]
      exact V.mul_mem (hUV h1) hv
    have hCNV : C ≤ Subgroup.normalizer (V : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro v
      refine ⟨hCV c hc v, fun hv => ?_⟩
      have := hCV c⁻¹ (C.inv_mem hc) _ hv
      simpa [mul_assoc] using this
    have hYM : Y ≤ M := (hYC.trans hCNV).trans (Hyp6Sec2.normalizer_V_le h432 h)
    have hYV : Y ≤ Subgroup.centralizer (V : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro c ⟨hcC, hco⟩
      obtain ⟨hcH, -, hcU⟩ := mem_centralizerMod.mp hcC
      exact mem_centralizer_of_odd_ch62 hV hUV hco (pow_orderOf_eq_one c)
        (fun u hu => (Subgroup.mem_centralizer_iff.mp hcH u hu).symm)
        (fun a ha => hcU a (le_conjClosure V H ha))
    have hYL : ∀ y ∈ Y, ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
      intro y hy l hl
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := h.normal (hYM hy)
      have h1 : l * y * l⁻¹ * y⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp hyN l⁻¹).mp (L.inv_mem hl)
        have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
        rw [e]
        exact L.mul_mem hl this
      have h2 : l * y * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
        have hlC : l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_ch62
            (h.toHyp611.L_le_normalizer hl)) y).mp (hYV hy)
        exact Subgroup.mul_mem _ hlC (Subgroup.inv_mem _ (hYV hy))
      exact h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one (ℓ := ⟨_, h1⟩)
        ((h.data.mem_ker_rho_iff _).mpr h2)
    have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
      hHC.trans (normalizer_le_normalizer_oTwoUpper C)
    have hO2LH : pCoreOf 2 L ≤ H := fun x hx =>
      Subgroup.centralizer_le (show (U : Set G) ⊆ V from hUV) (h.toHyp611.pCoreOf_le_centralizer hx)
    have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
      intro l hl
      refine mem_normalizer_oTwoUpper_ch62 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
        (hO2LH.trans hHY) (fun y hy => hYL y hy l hl)
        (fun y hy => by simpa using hYL y hy l⁻¹ (L.inv_mem hl))
    have hTUY : T ⊓ N ≤ Subgroup.normalizer (Y : Set G) := by
      rintro g ⟨hgT, hgU⟩
      have hgV : g ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer hgT
      have hgH : g ∈ Subgroup.normalizer (H : Set G) := mem_normalizer_centralizer_ch62 hgU
      have hgUH : g ∈ Subgroup.normalizer (UH : Set G) := mem_normalizer_conjClosure_ch62 hgV hgH
      exact normalizer_le_normalizer_oTwoUpper C
        (mem_normalizer_centralizerMod_ch62 hgU hgH hgUH)
    have hidx := h.relIndex_normalizer_fix h331 h432 h615 htT ht hSyl
    have hTY : T ≤ Subgroup.normalizer (Y : Set G) := by
      obtain ⟨s, hs, hsN⟩ : ∃ s ∈ T ⊓ L, s ∉ N := by
        by_contra hcon
        push Not at hcon
        exact h.not_TL_le_normalizer_fix htT ht hcon
      intro x hxT
      by_cases hxN : x ∈ N
      · exact hTUY ⟨hxT, hxN⟩
      · have hidx' : ((T ⊓ N).subgroupOf T).index = 2 := hidx
        set a : ↥T := ⟨s, hs.1⟩⁻¹ with ha
        set b : ↥T := ⟨x, hxT⟩ with hb
        have hanot : a ∉ (T ⊓ N).subgroupOf T := by
          rw [Subgroup.mem_subgroupOf]
          intro h1
          apply hsN
          have := (T ⊓ N).inv_mem h1
          simpa [ha] using this.2
        have hbnot : b ∉ (T ⊓ N).subgroupOf T := by
          rw [Subgroup.mem_subgroupOf]
          exact fun h1 => hxN h1.2
        have hmem := (Subgroup.mul_mem_iff_of_index_two hidx' (a := a) (b := b)).mpr
          ⟨fun h1 => absurd h1 hanot, fun h1 => absurd h1 hbnot⟩
        rw [Subgroup.mem_subgroupOf] at hmem
        have e : x = s * (s⁻¹ * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ (hLY hs.2) (hTUY (by simpa [ha, hb] using hmem))
    have hHchar : CharTwo H := (h.toHyp611Nat.lemma_6_1_14_two htT).2
    have hYchar : CharTwo Y := A4.charTwo_of_normal (hYC.trans hCH) hHY hHchar
    have hY2 : pCoreOf 2 Y ≠ ⊥ := by
      intro h0
      apply hYne
      refine le_bot_iff.mp fun y hy => ?_
      have hyC : y ∈ Y ⊓ Subgroup.centralizer (pCoreOf 2 Y : Set G) := by
        refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        rw [h0] at hx
        rw [Subgroup.mem_bot.mp hx, one_mul, mul_one]
      have := hYchar hyC
      rwa [h0] at this
    have hNO : Subgroup.normalizer (pCoreOf 2 Y : Set G) ≤ M :=
      le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM h432)
        (sup_le (hLY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
          (hTY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)))
        ⟨pCoreOf 2 Y, hY2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩
    apply hH
    intro x hx
    have hxM : x ∈ M := hNO (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y (hHY hx))
    exact (h.toHyp611Nat.normalizer_le hU1 hUV ⟨hxM, hHN hx⟩).2
  have hCeq : C = pCoreOf 2 H := by
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCH hHC ?_) hOC
    refine A4.isPGroup_two_of_odd_order_eq_one fun c hc hodd => ?_
    have : c ∈ oTwoUpper C := mem_oTwoUpper_of_odd hc hodd
    rw [hY] at this
    exact Subgroup.mem_bot.mp this
  refine ⟨hUHab, hUHO, hcommUH, hCeq, ⟨hUV.trans (le_conjClosure V H), hUHH, hHUH, hHN,
    fun u hu w hw => ?_, ?_⟩⟩
  · have hc := B2F.isElemAbelian_comm hUHab hu hw
    have h1 : u * w * u⁻¹ * w⁻¹ = 1 := by rw [hc]; group
    exact ⟨by rw [h1]; exact U.one_mem, by rw [hUHab.2 u hu]; exact U.one_mem⟩
  · rw [← hC, hCeq]
    intro P hPH hHP hP2
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPH hHP ?_
    intro p
    obtain ⟨k, hk⟩ := hP2 p p.2
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hk⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have : ((p : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul]
    exact this

theorem lemma_6_2_4_one_five (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {U : Subgroup G} (hUV : U ≤ V) (hm : mQuot V U = 2)
    (hH : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hTU : IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G))
      (M ⊓ Subgroup.normalizer (U : Set G))) :
    ∃ t ∈ T, IsInvolutoryFieldAut L t ∧ U = V ⊓ Subgroup.centralizer ({t} : Set G) ∧
      (QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G)) ∧
        IsSylowIn 2 (ch6Q T V ⊔ Subgroup.zpowers t) (Subgroup.centralizer (U : Set G)) ∧
        Subgroup.normalizer ((ch6Q T V ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤
          Subgroup.normalizer (thompsonJ (ch6Q T V ⊔ Subgroup.zpowers t) : Set G) ∧
        Subgroup.normalizer (thompsonJ (ch6Q T V ⊔ Subgroup.zpowers t) : Set G) ≤ M ∧
        IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (Subgroup.normalizer (U : Set G)) ∧
        (T ⊓ Subgroup.normalizer (U : Set G)).relIndex T = 2) ∧
      wClos V 0 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V ∧
      (IsElemAbelian 2 (conjClosure V (Subgroup.centralizer (U : Set G))) ∧
        conjClosure V (Subgroup.centralizer (U : Set G)) ≤
          pCoreOf 2 (Subgroup.centralizer (U : Set G)) ∧
        ⁅conjClosure V (Subgroup.centralizer (U : Set G)),
          pCoreOf 2 (Subgroup.centralizer (U : Set G))⁆ ≤ U ∧
        centralizerMod U (Subgroup.centralizer (U : Set G))
            (conjClosure V (Subgroup.centralizer (U : Set G))) =
          pCoreOf 2 (Subgroup.centralizer (U : Set G)) ∧
        IsReducedMod (Subgroup.centralizer (U : Set G))
          (conjClosure V (Subgroup.centralizer (U : Set G))) U) ∧
      (Nat.card ↥(oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G))) =
          3 * Nat.card ↥(pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G)))) ∧
        pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G))) =
          oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G)) ⊓ Subgroup.centralizer (U : Set G)) := by
  obtain ⟨t, htT, ht, hUt⟩ := h.exists_fieldAut_of_not_le h432 h6110 hE612 hUV hm hH hTU
  subst hUt
  obtain ⟨h1a, h1b, h1c⟩ := h.toHyp611Nat.lemma_6_1_14_one h432 htT ht hTU
  refine ⟨t, htT, ht, rfl, ⟨(h.toHyp611Nat.lemma_6_1_14_two htT).2, h1a,
    CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ _, h1b, h1c,
    h.relIndex_normalizer_fix h331 h432 h615 htT ht hTU⟩,
    (h.toHyp611Nat.lemma_6_1_14_three h6110 htT ht).1,
    h.lemma_6_2_4_four h331 h432 h615 h6110 htT ht hTU hH,
    h.toHyp611Nat.lOne_fix_two htT ht⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
