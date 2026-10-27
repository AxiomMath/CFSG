module

public import CFSG.Quasithin.MS93.S33LamP
public import CFSG.Quasithin.MS93.S33LamW

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem commutator_sup_pCore_le (h : PUHyp M T L) {E : Subgroup G} (hEM : E ≤ M) {Y : Subgroup G}
    (hY : Y ≤ E ⊔ pCoreOf 2 M) : ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆ := by
  have hN : E ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    hEM.trans (le_normalizer_pCoreOf M)
  rw [Subgroup.commutator_le]
  intro u hu y hy
  have hy' : y ∈ ((E ⊔ pCoreOf 2 M : Subgroup G) : Set G) := hY hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy'
  obtain ⟨e, he, k, hk, rfl⟩ := hy'
  have hku := Subgroup.mem_centralizer_iff.mp (h.pCoreOf_le_centralizer_Z0q hk) u
    (Uq_le_Z0q h.L_le hu)
  have hku' : k * u⁻¹ = u⁻¹ * k := by
    calc k * u⁻¹ = u⁻¹ * (u * k) * u⁻¹ := by group
      _ = u⁻¹ * (k * u) * u⁻¹ := by rw [hku]
      _ = u⁻¹ * k := by group
  have e1 : ⁅u, e * k⁆ = ⁅u, e⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc u * (e * k) * u⁻¹ * (e * k)⁻¹ = u * e * (k * u⁻¹) * k⁻¹ * e⁻¹ := by group
      _ = u * e * (u⁻¹ * k) * k⁻¹ * e⁻¹ := by rw [hku']
      _ = u * e * u⁻¹ * e⁻¹ := by group
  rw [e1]
  exact Subgroup.commutator_mem_commutator hu he

theorem imM_closure_triple (h : PUHyp M T L) (m₁ m₂ m₃ : ↥M) :
    imM h.le (Subgroup.closure ({(m₁ : G), (m₂ : G), (m₃ : G)} : Set G)) =
      Subgroup.closure ({(puAmalgam h.le).ofA m₁, (puAmalgam h.le).ofA m₂,
        (puAmalgam h.le).ofA m₃} : Set (puAmalgam h.le).Universal) := by
  have e1 : Subgroup.closure ({(m₁ : G), (m₂ : G), (m₃ : G)} : Set G) =
      (Subgroup.closure ({m₁, m₂, m₃} : Set ↥M)).map M.subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [e1, imM_map_subtype, MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

section MLevel

variable {F : Type} [Field F] [Fintype F] {A : Subgroup G} {α : ↥A →* ↥(StatedSp 2 F)}
  {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → MSP.V4 F)}
  (h : PUHyp M T L) (hAM : A ≤ M) (hβ : Function.Surjective β)
  (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
  (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec)
  (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L,
    m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) → m * u * m⁻¹ = u)
include h hAM hβ hβker hAβ hlift

omit [Fintype F] hlift in
theorem mem_closure_sup_of_map (hq : Nat.card F = 2) {v v' : MSP.V4 F} (hv0 : v ≠ 0)
    (hv'0 : v' ≠ 0) (hvv : MSP.form F v v' = 0) {e₁ e₂ : ↥A} (he₁T : (e₁ : G) ∈ T)
    (he₂T : (e₂ : G) ∈ T) (he₁ : α e₁ = MSP.transv v 1) (he₂ : α e₂ = MSP.transv v' 1)
    {x : ↥A} (hxT : (x : G) ∈ T) (hx : α x ∈ MSP.xPoint (F ∙ v) ⊔ MSP.xPoint (F ∙ v')) :
    (x : G) ∈ Subgroup.closure ({(e₁ : G), (e₂ : G)} : Set G) ⊔ pCoreOf 2 M := by
  have hkerT : ∀ a : ↥A, (a : G) ∈ T → α a = 1 → (a : G) ∈ pCoreOf 2 M := fun a haT ha =>
    mem_pCoreOf_of_actTriv h haT ((image_eq_one_iff h hAM (natCoordOf β hβ hβker hAβ) a).1 ha)
  obtain ⟨a, b, hab⟩ := exists_eq_of_mem_sup hv0 hv'0 hvv hx
  have hpow : ∀ (w : MSP.V4 F) (z : F), ∃ n : ℕ, MSP.transv w z = MSP.transv w 1 ^ n := by
    intro w z
    rcases MSP.eq_zero_or_eq_one_of_card_two hq z with rfl | rfl
    · exact ⟨0, by rw [MSP.transv_zero, pow_zero]⟩
    · exact ⟨1, (pow_one _).symm⟩
  obtain ⟨n, hn⟩ := hpow v a
  obtain ⟨m, hm⟩ := hpow v' b
  have hwα : α (e₁ ^ n * e₂ ^ m) = α x := by
    rw [map_mul, map_pow, map_pow, he₁, he₂, hab, hn, hm]
  have hwG : ((e₁ ^ n * e₂ ^ m : ↥A) : G) = (e₁ : G) ^ n * (e₂ : G) ^ m := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  have hwcl : (e₁ : G) ^ n * (e₂ : G) ^ m ∈
      Subgroup.closure ({(e₁ : G), (e₂ : G)} : Set G) :=
    mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) n)
      (pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) m)
  have hwT : (e₁ : G) ^ n * (e₂ : G) ^ m ∈ T := mul_mem (pow_mem he₁T n) (pow_mem he₂T m)
  have hkα : α (x * (e₁ ^ n * e₂ ^ m)⁻¹) = 1 := by
    rw [map_mul, map_inv, hwα, mul_inv_cancel]
  have hkG : ((x * (e₁ ^ n * e₂ ^ m)⁻¹ : ↥A) : G) = (x : G) * ((e₁ : G) ^ n * (e₂ : G) ^ m)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hwG]
  have hkQ : (x : G) * ((e₁ : G) ^ n * (e₂ : G) ^ m)⁻¹ ∈ pCoreOf 2 M := by
    have hT' : ((x * (e₁ ^ n * e₂ ^ m)⁻¹ : ↥A) : G) ∈ T := by
      rw [hkG]
      exact mul_mem hxT (inv_mem hwT)
    have := hkerT _ hT' hkα
    rwa [hkG] at this
  have e' : (x : G) = ((x : G) * ((e₁ : G) ^ n * (e₂ : G) ^ m)⁻¹) *
      ((e₁ : G) ^ n * (e₂ : G) ^ m) := by group
  rw [e']
  exact mul_mem (Subgroup.mem_sup_right hkQ) (Subgroup.mem_sup_left hwcl)

omit [Fintype F] in
theorem lam_triple (hq : Nat.card F = 2) (hTA : T ≤ A) {E : Subgroup G} (hET : E ≤ T)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hUE : ⁅Uq M T L, E⁆ ≤ E)
    {p p' : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) (hp' : MSP.IsPoint p')
    (hpp : p' ≤ MSP.perp p) (hΓ : (E.subgroupOf A).map α = MSP.xPoint p ⊔ MSP.xPoint p')
    (h4 : 4 ≤ Nat.card ((E.subgroupOf A).map α))
    (hl : MSP.IsLine (MSP.commSp ((E.subgroupOf A).map α))) {Y : Subgroup G} (hYT : Y ≤ T)
    (hYR : Y ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G))
    (hYn : ¬ ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆) :
    ∃ t₁ ∈ E, ∃ t₂ ∈ E, ∃ t₃ ∈ T ⊓ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G),
      (Subgroup.centralizer ({t₁} : Set G)).relIndex (Z0q M T) = 2 ∧
      (Subgroup.centralizer ({t₂} : Set G)).relIndex (Z0q M T) = 2 ∧
      (Subgroup.centralizer ({t₃} : Set G)).relIndex (Z0q M T) = 2 ∧ t₁ * t₂⁻¹ ∉ pCoreOf 2 M ∧
      E ⊔ pCoreOf 2 M = Subgroup.closure ({t₁, t₂} : Set G) ⊔ pCoreOf 2 M ∧
      T ⊓ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) ⊔ pCoreOf 2 M =
        Subgroup.closure ({t₁, t₂, t₃} : Set G) ⊔ pCoreOf 2 M ∧
      ¬ Y ≤ Subgroup.closure ({t₁, t₂} : Set G) ⊔ pCoreOf 2 M := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hq]; norm_num)
  have : Finite (MSP.Sp4 F) := Subtype.finite
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    have hc : Fintype.card F = 2 ^ 1 := by rw [← Nat.card_eq_fintype_card, hq, pow_one]
    exact charP_of_card_eq_prime_pow hc
  have hEA : E ≤ A := hET.trans hTA
  obtain ⟨v, hv0, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
  obtain ⟨v', hv'0, rfl⟩ := MSP.exists_eq_span_of_isPoint hp'
  have hvv : MSP.form F v v' = 0 := MSP.mem_perp_span.1 (hpp (Submodule.mem_span_singleton_self v'))
  have hind : v' ∉ F ∙ v := by
    intro hv'
    have hle : F ∙ v' ≤ F ∙ v := (Submodule.span_singleton_le_iff_mem _ _).2 hv'
    have heq : F ∙ v' = F ∙ v := Submodule.eq_of_le_of_finrank_eq hle (by rw [hp', hp])
    rw [hΓ, heq, sup_idem, MSP.card_xPoint hp, hq] at h4
    omega
  have hsum : v + v' ≠ 0 := by
    intro h0
    apply hind
    have : v' = (-1 : F) • v := by
      rw [neg_one_smul]
      exact (neg_eq_of_add_eq_zero_right h0).symm
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  set c := natCoordOf β hβ hβker hAβ with hc
  have hQker : ∀ a : ↥A, (a : G) ∈ pCoreOf 2 M → α a = 1 := by
    intro a ha
    refine (image_eq_one_iff h hAM c a).2 ((mem_actTriv h).2 ⟨hAM a.2, fun u hu => ?_⟩)
    have hcu := Subgroup.mem_centralizer_iff.mp (h.pCoreOf_le_centralizer_Z0q ha) u
      (Uq_le_Z0q h.L_le hu)
    rw [commutatorElement_def, hcu, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  set Γ := (E.subgroupOf A).map α with hΓdef
  set l := MSP.commSp Γ with hldef
  have hq' := commSp_le_fixSp_of_quadratic h hAM hβ hβker hAβ hEA hEab hUE
  have hΓl : Γ ≤ MSP.qLine l := MSP.le_fixer_iff.2 hq'
  have hvl : ∀ {w : MSP.V4 F}, w ≠ 0 → MSP.xPoint (F ∙ w) ≤ Γ → w ∈ l := by
    intro w hw hX
    have := MSP.commSp_mono hX
    rw [MSP.commSp_xPoint (MSP.isPoint_span hw)] at this
    exact this (Submodule.mem_span_singleton_self w)
  have hvΓ : MSP.xPoint (F ∙ v) ≤ Γ := hΓ ▸ le_sup_left
  have hv'Γ : MSP.xPoint (F ∙ v') ≤ Γ := hΓ ▸ le_sup_right
  have hsl : v + v' ∈ l := add_mem (hvl hv0 hvΓ) (hvl hv'0 hv'Γ)
  set τ := MSP.transv (v + v') 1 with hτ
  have hτl : τ ∈ MSP.qLine l := MSP.transv_mem_qLine hl hsl 1
  have hτΓ : τ ∉ Γ := by
    rw [hΓ]
    exact transv_add_not_mem_sup hq hv0 hv'0 hvv hind
  have h8 : Nat.card (MSP.qLine l) = 8 := by rw [MSP.card_qLine hl, hq]; norm_num
  have hΓsub : Nat.card ↥(Γ.subgroupOf (MSP.qLine l)) = Nat.card Γ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓl).toEquiv
  have hΓ4 : Nat.card Γ = 4 := by
    have hd : Nat.card Γ ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hΓl
    have hne : Nat.card Γ ≠ 8 := fun h8' => hτΓ
      ((Subgroup.eq_of_le_of_card_ge hΓl (by rw [h8, h8'])) ▸ hτl)
    have hdiv : Nat.card Γ ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
    have h8d : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [h8d] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    omega
  have hidx : (Γ.subgroupOf (MSP.qLine l)).index = 2 := by
    have := Subgroup.card_mul_index (Γ.subgroupOf (MSP.qLine l))
    rw [hΓsub, hΓ4, h8] at this
    omega
  have hmulΓ : ∀ {x : MSP.Sp4 F}, x ∈ MSP.qLine l → x ∉ Γ → x * τ⁻¹ ∈ Γ := by
    intro x hx hxΓ
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩)
      (b := (⟨τ, hτl⟩ : ↥(MSP.qLine l))⁻¹)).2 (by
        simp only [Subgroup.mem_subgroupOf, inv_mem_iff]
        exact iff_of_false hxΓ hτΓ)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv] using this
  obtain ⟨e₁, he₁, he₁v⟩ : MSP.transv v 1 ∈ Γ := hvΓ (MSP.transv_mem_xPoint v 1)
  obtain ⟨e₂, he₂, he₂v⟩ : MSP.transv v' 1 ∈ Γ := hv'Γ (MSP.transv_mem_xPoint v' 1)
  have he₁E : (e₁ : G) ∈ E := Subgroup.mem_subgroupOf.1 he₁
  have he₂E : (e₂ : G) ∈ E := Subgroup.mem_subgroupOf.1 he₂
  have hmemcl : ∀ {x : ↥A}, (x : G) ∈ T →
      α x ∈ MSP.xPoint (F ∙ v) ⊔ MSP.xPoint (F ∙ v') →
      (x : G) ∈ Subgroup.closure ({(e₁ : G), (e₂ : G)} : Set G) ⊔ pCoreOf 2 M :=
    fun hxT hx => mem_closure_sup_of_map h hAM hβ hβker hAβ hq hv0 hv'0 hvv (hET he₁E)
      (hET he₂E) he₁v he₂v hxT hx
  have hERC : E ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hEab _ (hUE hr) _ he
  have hYA : Y ≤ A := hYT.trans hTA
  have hnot := not_map_le h hAM hβ hβker hAβ hYA hYn
  obtain ⟨_, ⟨y, hy, rfl⟩, hyΓ⟩ := Set.not_subset.1 hnot
  have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.1 hy
  have hyl : α y ∈ MSP.qLine l := mem_fixer_of_centralizer h hAM hβ hβker hAβ hEA (hYR hyY)
  obtain ⟨e₃, he₃, he₃v⟩ := hmulΓ hyl hyΓ
  have he₃E : (e₃ : G) ∈ E := Subgroup.mem_subgroupOf.1 he₃
  set t₃ : ↥A := e₃⁻¹ * y with ht₃
  have ht₃α : α t₃ = τ := by
    rw [ht₃, map_mul, map_inv, he₃v]
    group
  have ht₃G : (t₃ : G) = (e₃ : G)⁻¹ * y := by
    rw [ht₃, Subgroup.coe_mul, Subgroup.coe_inv]
  have ht₃T : (t₃ : G) ∈ T := by
    rw [ht₃G]
    exact mul_mem (inv_mem (hET he₃E)) (hYT hyY)
  have ht₃C : (t₃ : G) ∈ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := by
    rw [ht₃G]
    exact mul_mem (inv_mem (hERC he₃E)) (hYR hyY)
  have hsupE : E ⊔ pCoreOf 2 M = Subgroup.closure ({(e₁ : G), (e₂ : G)} : Set G) ⊔ pCoreOf 2 M := by
    apply le_antisymm
    · refine sup_le (fun e he => ?_) le_sup_right
      exact hmemcl (x := ⟨e, hEA he⟩) (hET he) (by
        rw [← hΓ]
        exact ⟨⟨e, hEA he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩)
    · refine sup_le ((Subgroup.closure_le _).2 ?_) le_sup_right
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_left he₁E
      · exact Subgroup.mem_sup_left he₂E
  refine ⟨e₁, he₁E, e₂, he₂E, t₃, ⟨ht₃T, ht₃C⟩,
    relIndex_centralizer_Z0q_eq_two h hAM hβ hβker hAβ hlift hq (hET he₁E) hv0 he₁v,
    relIndex_centralizer_Z0q_eq_two h hAM hβ hβker hAβ hlift hq (hET he₂E) hv'0 he₂v,
    relIndex_centralizer_Z0q_eq_two h hAM hβ hβker hAβ hlift hq ht₃T hsum ht₃α, ?_, hsupE, ?_, ?_⟩
  · intro hmem
    have h1 := hQker (e₁ * e₂⁻¹) hmem
    rw [map_mul, map_inv, he₁v, he₂v, mul_inv_eq_one] at h1
    have hvv' : v' = v := (MSP.transv_eq_transv_iff hv0).1 h1.symm
    exact hind (by rw [hvv']; exact Submodule.mem_span_singleton_self v)
  · apply le_antisymm
    · refine sup_le (fun x hx => ?_) le_sup_right
      obtain ⟨hxT, hxC⟩ := hx
      have hxA : x ∈ A := hTA hxT
      have hcl2 : Subgroup.closure ({(e₁ : G), (e₂ : G)} : Set G) ⊔ pCoreOf 2 M ≤
          Subgroup.closure ({(e₁ : G), (e₂ : G), (t₃ : G)} : Set G) ⊔ pCoreOf 2 M :=
        sup_le_sup_right (Subgroup.closure_mono (by
          intro z hz
          rcases hz with rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))) _
      have hxl : α ⟨x, hxA⟩ ∈ MSP.qLine l :=
        mem_fixer_of_centralizer h hAM hβ hβker hAβ hEA (y := ⟨x, hxA⟩) hxC
      by_cases hxΓ : α ⟨x, hxA⟩ ∈ Γ
      · exact hcl2 (hmemcl (x := ⟨x, hxA⟩) hxT (by rw [← hΓ]; exact hxΓ))
      · have h1 := hmulΓ hxl hxΓ
        have h2 : α (⟨x, hxA⟩ * t₃⁻¹) ∈ MSP.xPoint (F ∙ v) ⊔ MSP.xPoint (F ∙ v') := by
          rw [map_mul, map_inv, ht₃α, ← hΓ]
          exact h1
        have hxt : ((⟨x, hxA⟩ * t₃⁻¹ : ↥A) : G) = x * (t₃ : G)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
        have h3 := hmemcl (x := ⟨x, hxA⟩ * t₃⁻¹) (by rw [hxt]; exact mul_mem hxT (inv_mem ht₃T))
          h2
        rw [hxt] at h3
        have e' : x = (x * (t₃ : G)⁻¹) * t₃ := by group
        rw [e']
        exact mul_mem (hcl2 h3) (Subgroup.mem_sup_left (Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
    · refine sup_le ((Subgroup.closure_le _).2 ?_) le_sup_right
      rintro _ (rfl | rfl | rfl)
      · exact Subgroup.mem_sup_left ⟨hET he₁E, hERC he₁E⟩
      · exact Subgroup.mem_sup_left ⟨hET he₂E, hERC he₂E⟩
      · exact Subgroup.mem_sup_left ⟨ht₃T, ht₃C⟩
  · intro hle
    apply hYn
    rw [← hsupE] at hle
    exact commutator_sup_pCore_le h (hET.trans h.le) hle

end MLevel

theorem hat_of_pre (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {g : (puAmalgam h.le).Universal} (hgα : g • baseA (puAmalgam h.le) = α')
    (hgβ : g • baseB (puAmalgam h.le) = geo _ α' (baseA _) 1)
    (hμ : IsCritical (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _))
    (hET : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ T)
    {Y : Subgroup (puAmalgam h.le).Universal} {t₁ t₂ t₃ : G} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (ht₃ : t₃ ∈ T) (hi₁ : (Subgroup.centralizer ({t₁} : Set G)).relIndex (Z0q M T) = 2)
    (hi₂ : (Subgroup.centralizer ({t₂} : Set G)).relIndex (Z0q M T) = 2)
    (hi₃ : (Subgroup.centralizer ({t₃} : Set G)).relIndex (Z0q M T) = 2)
    (h12 : t₁ * t₂⁻¹ ∉ pCoreOf 2 M)
    (hsup : pre h.le (ZM _ (g⁻¹ • baseA _)) ⊔ pCoreOf 2 M =
      Subgroup.closure ({t₁, t₂} : Set G) ⊔ pCoreOf 2 M)
    (hsup3 : T ⊓ Subgroup.centralizer
        ((⁅Uq M T L, pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le)))⁆ : Subgroup G) : Set G) ⊔
        pCoreOf 2 M = Subgroup.closure ({t₁, t₂, t₃} : Set G) ⊔ pCoreOf 2 M)
    (hYn : ¬ pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤
      Subgroup.closure ({t₁, t₂} : Set G) ⊔ pCoreOf 2 M) :
    ∃ t₁ ∈ Qv _ (geo _ α' (baseA _) 1), ∃ t₂ ∈ Qv _ (geo _ α' (baseA _) 1),
      ∃ t₃ ∈ Qv _ (geo _ α' (baseA _) 1),
      (∀ t ∈ ({t₁, t₂, t₃} : Set (puAmalgam h.le).Universal),
        (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2) ∧
      t₁ * t₂⁻¹ ∉ Qv _ α' ∧
      ZM _ (baseA _) ⊔ Qv _ α' =
        Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ∧
      Qv _ (geo _ α' (baseA _) 1) ⊓
          Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal) ⊔
        Qv _ α' = Subgroup.closure ({t₁, t₂, t₃} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ∧
      ¬ Y ≤ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
  have hgμ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hM₁ : t₁ ∈ M := h.le ht₁
  have hM₂ : t₂ ∈ M := h.le ht₂
  have hM₃ : t₃ ∈ M := h.le ht₃
  have hQα : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hZ : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  obtain ⟨-, -, -, -, hEim⟩ := pre_zm_props h hμ
  have hcomm := imM_commutator_pre h hμ hET
  have hRM : ⁅Uq M T L, pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le)))⁆ ≤ M :=
    (commutator_le_left_of_le_normalizer ((pre_le h.le _).trans
      (le_normalizer_Uq h.le_normalizer))).trans ((Uq_le_Z0q h.L_le).trans (Z0q_le M T))
  have hR : critR (puAmalgam h.le) (baseA _) α' =
      (critR (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [critR, critR, Subgroup.map_commutator, ← zm_smul, ← zm_smul, hgμ, hgα]
  have hmemQ : ∀ {t : G} (ht : t ∈ T), (MulAut.conj g).toMonoidHom
      ((puAmalgam h.le).ofA ⟨t, h.le ht⟩) ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) := by
    intro t ht
    rw [← hgβ, qv_smul, puAmalgam.qv_baseB]
    exact ⟨_, (ofA_mem_imM_iff h.le _).2 ht, rfl⟩
  have hidx : ∀ {t : G} (ht : t ∈ T),
      (Subgroup.centralizer ({t} : Set G)).relIndex (Z0q M T) = 2 →
      (Subgroup.centralizer ({(MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t, h.le ht⟩)} :
        Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2 := by
    intro t ht hi
    rw [centralizer_singleton_conj, ← hgα, zm_smul,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hZ,
      relIndex_centralizer_ofA h ⟨t, h.le ht⟩ (Z0q_le M T)]
    exact hi
  have e5 : ZM (puAmalgam h.le) (baseA _) =
      (ZM (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [← zm_smul, hgμ]
  have e6 : Qv (puAmalgam h.le) α' =
      (Qv (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [← hgα, qv_smul]
  have e7 : Qv (puAmalgam h.le) (geo _ α' (baseA _) 1) =
      (imM h.le T).map (MulAut.conj g).toMonoidHom := by
    rw [← hgβ, qv_smul, puAmalgam.qv_baseB]
  have hcl2 : Subgroup.closure ({(MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t₁, hM₁⟩),
      (MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t₂, hM₂⟩)} :
        Set (puAmalgam h.le).Universal) =
      (Subgroup.closure ({(puAmalgam h.le).ofA ⟨t₁, hM₁⟩, (puAmalgam h.le).ofA ⟨t₂, hM₂⟩} :
        Set (puAmalgam h.le).Universal)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton]
  have hcl3 : Subgroup.closure ({(MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t₁, hM₁⟩),
      (MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t₂, hM₂⟩),
      (MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t₃, hM₃⟩)} :
        Set (puAmalgam h.le).Universal) =
      (Subgroup.closure ({(puAmalgam h.le).ofA ⟨t₁, hM₁⟩, (puAmalgam h.le).ofA ⟨t₂, hM₂⟩,
        (puAmalgam h.le).ofA ⟨t₃, hM₃⟩} : Set (puAmalgam h.le).Universal)).map
        (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton]
  have hcl2M : Subgroup.closure ({t₁, t₂} : Set G) ≤ M := (Subgroup.closure_le _).2 (by
    rintro _ (rfl | rfl)
    · exact hM₁
    · exact hM₂)
  have hcl3M : Subgroup.closure ({t₁, t₂, t₃} : Set G) ≤ M := (Subgroup.closure_le _).2 (by
    rintro _ (rfl | rfl | rfl)
    · exact hM₁
    · exact hM₂
    · exact hM₃)
  have himcl2 : imM h.le (Subgroup.closure ({t₁, t₂} : Set G) ⊔ pCoreOf 2 M) =
      Subgroup.closure ({(puAmalgam h.le).ofA ⟨t₁, hM₁⟩, (puAmalgam h.le).ofA ⟨t₂, hM₂⟩} :
        Set (puAmalgam h.le).Universal) ⊔ Qv (puAmalgam h.le) (baseA _) := by
    rw [imM_sup h.le hcl2M (pCoreOf_le' M), imM_closure_pair h ⟨t₁, hM₁⟩ ⟨t₂, hM₂⟩, hQα]
  have hbase : ZM (puAmalgam h.le) (g⁻¹ • baseA _) ⊔ Qv (puAmalgam h.le) (baseA _) =
      Subgroup.closure ({(puAmalgam h.le).ofA ⟨t₁, hM₁⟩, (puAmalgam h.le).ofA ⟨t₂, hM₂⟩} :
        Set (puAmalgam h.le).Universal) ⊔ Qv (puAmalgam h.le) (baseA _) := by
    rw [← hEim, hQα, ← imM_sup h.le (pre_le h.le _) (pCoreOf_le' M), hsup, ← hQα, himcl2]
  have hbase3 : imM h.le T ⊓ Subgroup.centralizer (critR (puAmalgam h.le) (g⁻¹ • baseA _)
        (baseA _) : Set (puAmalgam h.le).Universal) ⊔ Qv (puAmalgam h.le) (baseA _) =
      Subgroup.closure ({(puAmalgam h.le).ofA ⟨t₁, hM₁⟩, (puAmalgam h.le).ofA ⟨t₂, hM₂⟩,
        (puAmalgam h.le).ofA ⟨t₃, hM₃⟩} : Set (puAmalgam h.le).Universal) ⊔
        Qv (puAmalgam h.le) (baseA _) := by
    rw [← hcomm, ← imM_inf_centralizer h.le T hRM, hQα,
      ← imM_sup h.le (inf_le_left.trans h.le) (pCoreOf_le' M), hsup3,
      imM_sup h.le hcl3M (pCoreOf_le' M), imM_closure_triple h ⟨t₁, hM₁⟩ ⟨t₂, hM₂⟩ ⟨t₃, hM₃⟩]
  refine ⟨_, hmemQ ht₁, _, hmemQ ht₂, _, hmemQ ht₃, ?_, ?_, ?_, ?_, ?_⟩
  · rintro t (rfl | rfl | rfl)
    · exact hidx ht₁ hi₁
    · exact hidx ht₂ hi₂
    · exact hidx ht₃ hi₃
  · intro hmem
    rw [← map_inv, ← map_mul, e6, Subgroup.mem_map_iff_mem (MulAut.conj g).injective, hQα,
      ← map_inv, ← map_mul, ofA_mem_imM_iff] at hmem
    exact h12 hmem
  · rw [hcl2, e5, e6, ← Subgroup.map_sup, ← Subgroup.map_sup, hbase]
  · rw [e7, hR, PU.centralizer_map_mulEquiv, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      hcl3, e6, ← Subgroup.map_sup, ← Subgroup.map_sup, hbase3]
  · intro hle
    apply hYn
    apply pre_le_of_le_imM h
    rw [himcl2]
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hle hy
    rw [hcl2, e6, ← Subgroup.map_sup] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    have hzz : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom z) = z := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hzz]
    exact hz

end CFSG.Quasithin.MS93.S33
