module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterRootNormalizers
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMBinaryAffinePlane

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterRadical

open Subgroup GomiFusion RootAxisTwoCore FullCenter
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Cores

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

open ComponentInitial.BinaryAffinePlane in
theorem translations_mem_E (h : FCHyp L K n φ t) (i : Axis) (b : Fin 2 → K) :
    ∃ e : 𝐍[i], (e : G) ∈ 𝐄[i] ∧ ∀ x, (h.actHyp i).aff e x = x + b := by
  have hA := h.actHyp i
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, h.setup.card_K]
  have hFA : ∀ g ∈ hA.aff.range, ∃ (b : Fin 2 → K) (f : (Fin 2 → K) ≃+ (Fin 2 → K)),
      ∀ x, g x = b + f x := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hA.linAdd g, fun x => (hA.aff_eq g x).trans (add_comm _ _)⟩
  have hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ hA.aff.range := by
    intro M
    obtain ⟨g, -, hg⟩ := h.aff_linear i M
    exact ⟨g, Equiv.ext hg⟩
  have hΓL : ∀ g ∈ hA.aff.range, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => x j ^ 2 ^ k := by
    rintro _ ⟨g, rfl⟩ hg0
    obtain ⟨M, k, hk, hM⟩ := h.aff_semilinear i g ((h.aff_zero_eq_zero_iff i g).mp hg0)
    exact ⟨M, k, hk, hM⟩
  have hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ hA.aff.range, g x = y := by
    intro x y
    obtain ⟨g, hg⟩ := h.aff_trans i x y
    exact ⟨hA.aff g, ⟨g, rfl⟩, hg⟩
  have hTF := translations_le h.setup.two_le hq hFA hGL hΓL hFtr
  set R := (translations (Fin 2 → K)).comap hA.aff
  have hRn : R.Normal := ⟨fun r hr g => by
    refine mem_comap.mpr ?_
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_translations hFA ⟨g, rfl⟩ (mem_comap.mp hr)⟩
  have hT2 : IsPGroup 2 (translations (Fin 2 → K)) := by
    intro x
    refine ⟨1, Subtype.ext (Equiv.ext fun y => ?_)⟩
    obtain ⟨c, hc⟩ := x.2
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_two, Equiv.Perm.mul_apply, hc, hc, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Equiv.Perm.one_apply]
  have hDN : 𝐃[i] ≤ 𝐍[i] := (map_subtype_le _).trans (h.twoCore.M_le_normalizer_B φ i)
  have hker : hA.aff.ker = (𝐃[i]).subgroupOf 𝐍[i] := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, h.aff_eq_one_iff_mem_D]
  have hker2 : IsPGroup 2 hA.aff.ker := by
    rw [hker]
    exact (CFSG.pCore_isPGroup.map _).of_equiv (subgroupOfEquivOfLe hDN).symm
  have hR2 : IsPGroup 2 R := hT2.comap_of_ker_isPGroup hA.aff hker2
  have hRE : R ≤ CFSG.pCore 2 𝐍[i] := le_sSup ⟨hRn, hR2⟩
  obtain ⟨e, he⟩ := hTF (show Equiv.addRight b ∈ translations (Fin 2 → K) from
    ⟨b, fun _ => rfl⟩)
  have heR : e ∈ R := by
    refine mem_comap.mpr ?_
    rw [he]
    exact ⟨b, fun _ => rfl⟩
  exact ⟨e, ⟨e, hRE heR, rfl⟩, fun x => DFunLike.congr_fun he x⟩

theorem card_E (h : FCHyp L K n φ t) (i : Axis) : Nat.card 𝐄[i] = 2 * Nat.card K ^ 6 := by
  obtain ⟨-, -, -, -, -, hcard⟩ := h.quotient_E i (translations_mem_E h i)
  have h1 := card_eq_card_quotient_mul_card_subgroup ((𝐃[i]).subgroupOf 𝐄[i])
  rw [hcard, Nat.card_congr (subgroupOfEquivOfLe (h.D_le_E i)).toEquiv, h.card_D i] at h1
  rw [h1]
  ring

theorem D_lt_E (h : FCHyp L K n φ t) (i : Axis) : 𝐃[i] < 𝐄[i] := by
  refine lt_of_le_of_ne (h.D_le_E i) fun heq => ?_
  have h1 := card_E h i
  rw [← heq, h.card_D i] at h1
  have h4 := h.four_le_card
  have h5 : Nat.card K ^ 4 < Nat.card K ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem E_mul_C0 (h : FCHyp L K n φ t) (i : Axis) :
    (𝐄[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) = 𝐍[i] := by
  have hEM := (h.E_mul_M i (translations_mem_E h i)).1
  ext g
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨e, he, c, hc, rfl⟩
    exact mul_mem (map_subtype_le _ he) (mem_inf.mp hc).2
  · intro hg
    have hg' : g ∈ (𝐄[i] : Set G) * (𝐌[i] : Set G) := by
      rw [hEM]
      exact hg
    obtain ⟨e, he, m, hm, rfl⟩ := hg'
    obtain ⟨h₁, -, -, -⟩ := h.twoCore.cond φ i (h.M_not_le_C i)
    obtain ⟨d, hd, c, hc, rfl⟩ := h₁ m hm
    rw [h.twoCore.inf_normalizer_eq φ i] at hc
    exact ⟨e * d, mul_mem he (h.D_le_E i hd), c, hc, mul_assoc _ _ _⟩

theorem E_inf_C (h : FCHyp L K n φ t) (i : Axis) : 𝐄[i] ⊓ 𝐂 = 𝐁[i] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxE, hxC⟩ := mem_inf.mp hx
    have hxM : x ∈ 𝐌[i] := by
      have h1 : x ∈ 𝐂 ⊓ 𝐍[i] := mem_inf.mpr ⟨hxC, map_subtype_le _ hxE⟩
      rw [← h.twoCore.inf_normalizer_eq φ i] at h1
      exact (mem_inf.mp h1).2
    have hxD : x ∈ 𝐃[i] := by
      have h1 : x ∈ 𝐄[i] ⊓ 𝐌[i] := mem_inf.mpr ⟨hxE, hxM⟩
      rwa [(h.E_mul_M i (translations_mem_E h i)).2] at h1
    have h1 : x ∈ 𝐃[i] ⊓ 𝐂 := mem_inf.mpr ⟨hxD, hxC⟩
    rwa [h.D_inf_C i] at h1
  · calc 𝐁[i] = 𝐃[i] ⊓ 𝐂 := (h.D_inf_C i).symm
      _ ≤ 𝐄[i] ⊓ 𝐂 := inf_le_inf_right _ (h.D_le_E i)

theorem E_inf_C0 (h : FCHyp L K n φ t) (i : Axis) : 𝐄[i] ⊓ (𝐂 ⊓ 𝐍[i]) = 𝐁[i] := by
  rw [← inf_assoc, E_inf_C h i]
  exact inf_of_le_left le_normalizer

theorem orbit_E (h : FCHyp L K n φ t) (i : Axis) :
    {x : G | ∃ e ∈ 𝐄[i], x = e⁻¹ * t * e} = {x | ∃ a ∈ 𝐀[i], x = t * a} := by
  rw [← h.orbit_N i]
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, map_subtype_le _ he, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    have hg' : g⁻¹ ∈ (𝐄[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) := by
      rw [E_mul_C0 h i]
      exact inv_mem hg
    obtain ⟨e, he, c, hc, hec⟩ := hg'
    have hec' : e * c = g⁻¹ := hec
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).1
    have hg2 : g = c⁻¹ * e⁻¹ := by rw [← mul_inv_rev, hec', inv_inv]
    refine ⟨e⁻¹, inv_mem he, ?_⟩
    rw [hg2]
    calc (c⁻¹ * e⁻¹)⁻¹ * t * (c⁻¹ * e⁻¹) = e * (c * t * c⁻¹) * e⁻¹ := by group
      _ = e⁻¹⁻¹ * t * e⁻¹ := by rw [hct, mul_inv_cancel_right, inv_inv]

theorem kernel_A (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐍[i]) :
    (∀ a ∈ 𝐀[i], a⁻¹ * (g * a * g⁻¹) ∈ 𝐔[i]) ↔ g ∈ 𝐄[i] := by
  have hA := h.actHyp i
  constructor
  · intro hk
    have hg' : g ∈ (𝐄[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) := by
      rw [E_mul_C0 h i]
      exact hg
    obtain ⟨e, he, c, hc, rfl⟩ := hg'
    have hcB : c ∈ 𝐁[i] := by
      refine h.mem_B_of_lin_eq_one i (mem_inf.mp hc).1 (mem_inf.mp hc).2 fun a ha => ?_
      have h1 : e * c * a * (e * c)⁻¹ ∈ 𝐀[i] := hA.conj_A _ hg a ha
      have hca : c * a * c⁻¹ = e⁻¹ * (e * c * a * (e * c)⁻¹) * e⁻¹⁻¹ := by group
      rw [hca, h.E_lin i (inv_mem he) h1]
      exact ((hA.psi_eq_iff ha h1).mpr (hk a ha)).symm
    exact mul_mem he (h.D_le_E i (h.B_le_D i hcB))
  · intro hgE a ha
    exact (hA.psi_eq_iff ha (hA.conj_A g hg a ha)).mp (h.E_lin i hgE ha).symm

theorem linear_action (h : FCHyp L K n φ t) (i : Axis) :
    ∃ μ : 𝐍[i] →* Equiv.Perm (Fin 2 → K),
      (∀ g : 𝐍[i], ∀ a ∈ 𝐀[i], μ g (psiG φ i a) = psiG φ i ((g : G) * a * (g : G)⁻¹)) ∧
      μ.ker = (𝐄[i]).subgroupOf 𝐍[i] ∧
      (∀ g : 𝐍[i], ∃ (A₀ : GL (Fin 2) K) (k : ℕ), k < n ∧
        ∀ x : Fin 2 → K, μ g x = (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => x j ^ 2 ^ k) ∧
      (∀ A₀ : GL (Fin 2) K, ∃ g : 𝐍[i], (g : G) ∈ 𝐂 ∧
        ∀ x : Fin 2 → K, μ g x = (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ x) ∧
      ∃ _ : ((𝐄[i]).subgroupOf 𝐍[i]).Normal,
        ∃ μq : (↥𝐍[i] ⧸ (𝐄[i]).subgroupOf 𝐍[i]) →* Equiv.Perm (Fin 2 → K),
          Function.Injective μq ∧ (∀ g : 𝐍[i], μq g = μ g) ∧
          ∃ _ : ((𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i])).Normal,
            ∃ μc : (↥(𝐂 ⊓ 𝐍[i]) ⧸ (𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i])) →* Equiv.Perm (Fin 2 → K),
              Function.Injective μc ∧
              (∀ g : ↥(𝐂 ⊓ 𝐍[i]), μc g = μ (Subgroup.inclusion inf_le_right g)) ∧
              μc.range = μq.range := by
  have hA := h.actHyp i
  have hlinC : ∀ g : 𝐍[i], (g : G) ∈ 𝐂 → hA.lin g = hA.aff g := by
    intro g hgC
    refine Equiv.ext fun x => ?_
    rw [hA.aff_eq]
    have e1 : t⁻¹ * ((g : G) * t * (g : G)⁻¹) = 1 := by
      rw [mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right, inv_mul_cancel]
    rw [e1, hA.psi_one, add_zero]
  have hker' : ∀ g : 𝐍[i], hA.lin g = 1 ↔ (g : G) ∈ 𝐄[i] := by
    intro g
    rw [hA.lin_eq_one_iff, ← kernel_A h i g.2]
    refine forall₂_congr fun a ha => ?_
    rw [eq_comm]
    exact hA.psi_eq_iff ha (hA.conj_A _ g.2 a ha)
  have hker : hA.lin.ker = (𝐄[i]).subgroupOf 𝐍[i] := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, hker' g]
  have hC0 : ∀ g : 𝐍[i], ∃ c : 𝐍[i], (c : G) ∈ 𝐂 ∧ hA.lin c = hA.lin g := by
    intro g
    have hg' : (g : G) ∈ (𝐄[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) := by
      rw [E_mul_C0 h i]
      exact g.2
    obtain ⟨e, he, c, hc, hec⟩ := hg'
    have hec' : e * c = g := hec
    refine ⟨⟨c, (mem_inf.mp hc).2⟩, (mem_inf.mp hc).1, ?_⟩
    have hg : g = ⟨e, map_subtype_le _ he⟩ * ⟨c, (mem_inf.mp hc).2⟩ := Subtype.ext hec'.symm
    rw [hg, map_mul, (hker' ⟨e, map_subtype_le _ he⟩).mpr he, one_mul]
  have hEn : ((𝐄[i]).subgroupOf 𝐍[i]).Normal :=
    ⟨fun x hx g => mem_subgroupOf.mpr (conj_mem_pCore_map g.2 (mem_subgroupOf.mp hx))⟩
  have hBn : ((𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i])).Normal := ⟨fun b hb c => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (mem_inf.mp c.2).2 b).mp (mem_subgroupOf.mp hb))⟩
  have hBk : (𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i]) ≤
      (hA.lin.comp (Subgroup.inclusion (inf_le_right : 𝐂 ⊓ 𝐍[i] ≤ 𝐍[i]))).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (hker' _).mpr (h.D_le_E i (h.B_le_D i (mem_subgroupOf.mp hx)))
  refine ⟨hA.lin, fun g a ha => hA.lin_psi g ha, hker, fun g => ?_, fun A₀ => ?_, hEn,
    QuotientGroup.lift _ hA.lin hker.ge, ?_, fun g => QuotientGroup.lift_mk _ _ _, hBn,
    QuotientGroup.lift _ _ hBk, ?_, fun g => QuotientGroup.lift_mk _ _ _, ?_⟩
  ·
    obtain ⟨c, hcC, hcg⟩ := hC0 g
    have hcM : (c : G) ∈ 𝐌[i] := by
      have h1 : (c : G) ∈ 𝐂 ⊓ 𝐍[i] := mem_inf.mpr ⟨hcC, c.2⟩
      rw [← h.twoCore.inf_normalizer_eq φ i] at h1
      exact (mem_inf.mp h1).2
    obtain ⟨A₀, k, hk, hA₀⟩ := h.aff_semilinear i c hcM
    refine ⟨A₀, k, hk, fun x => ?_⟩
    rw [← hcg, hlinC c hcC, hA₀]
  ·
    obtain ⟨g, hgC, hg⟩ := h.aff_linear i A₀
    exact ⟨g, hgC, fun x => by rw [hlinC g hgC, hg]⟩
  ·
    refine (injective_iff_map_eq_one _).mpr fun q hq => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.lift_mk, ← MonoidHom.mem_ker, hker] at hq
    exact (QuotientGroup.eq_one_iff g).mpr hq
  ·
    refine (injective_iff_map_eq_one _).mpr fun q hq => ?_
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.lift_mk, MonoidHom.comp_apply, hker'] at hq
    refine (QuotientGroup.eq_one_iff c).mpr (mem_subgroupOf.mpr ?_)
    have h1 : (c : G) ∈ 𝐄[i] ⊓ (𝐂 ⊓ 𝐍[i]) := mem_inf.mpr ⟨hq, c.2⟩
    rwa [E_inf_C0 h i] at h1
  ·
    ext f
    simp only [MonoidHom.mem_range]
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨(Subgroup.inclusion (inf_le_right : 𝐂 ⊓ 𝐍[i] ≤ 𝐍[i]) c : 𝐍[i]), by
        rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk, MonoidHom.comp_apply]⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨c, hcC, hcg⟩ := hC0 g
      refine ⟨((⟨c, mem_inf.mpr ⟨hcC, c.2⟩⟩ : ↥(𝐂 ⊓ 𝐍[i])) :
        ↥(𝐂 ⊓ 𝐍[i]) ⧸ (𝐁[i]).subgroupOf (𝐂 ⊓ 𝐍[i])), ?_⟩
      rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk, MonoidHom.comp_apply, ← hcg]
      rfl

theorem E_comm_U (h : FCHyp L K n φ t) (i : Axis) {e : G} (he : e ∈ 𝐄[i]) {u : G}
    (hu : u ∈ 𝐔[i]) : e * u * e⁻¹ = u := by
  have hNU := h.N_le_normalizer_U i
  have heN : e ∈ 𝐍[i] := map_subtype_le _ he
  set ψ : G → K := Function.invFun (coordG φ i)
  have hψc : ∀ v ∈ 𝐔[i], coordG φ i (ψ v) = v := fun v hv =>
    Function.invFun_eq (exists_coordG_eq φ i hv)
  have hψx : ∀ y : K, ψ (coordG φ i y) = y := fun y =>
    Function.leftInverse_invFun (coordG_injective φ i) y
  have hA : ActHyp ψ 1 𝐔[i] ⊥ 𝐍[i] :=
    { U_le := bot_le
      add := fun a ha b hb => coordG_injective φ i (by
        rw [coordG_add, hψc a ha, hψc b hb, hψc _ (mul_mem ha hb)])
      ker := fun a ha => by
        rw [mem_bot]
        constructor
        · intro h0
          rw [← hψc a ha, h0, coordG_zero]
        · rintro rfl
          rw [← coordG_zero φ i, hψx]
      surj := fun v => ⟨coordG φ i v, coordG_mem φ i v, hψx v⟩
      conj_A := fun g hg a ha => (mem_normalizer_iff.mp (hNU hg) a).mp ha
      conj_U := fun g _ u hu => by
        rw [mem_bot] at hu ⊢
        rw [hu]
        group
      conj_t := fun _ _ => by
        rw [inv_one, one_mul, mul_one, mul_inv_cancel]
        exact one_mem _ }
  have h2K : 2 ∣ Nat.card K := by
    rw [h.setup.card_K]
    exact dvd_pow_self 2 (by have := h.setup.two_le; omega)
  have htrans : ∀ v w : K, v ≠ 0 → w ≠ 0 → ∃ g ∈ 𝐍[i], hA.linFun g v = w := by
    intro v w hv hw
    obtain ⟨δ, hδ, hδc⟩ := FCHyp.torus_trans (φ := φ) i hv hw
    refine ⟨δ, h.torus_le_N i hδ, ?_⟩
    rw [← hψx v, hA.linFun_psi (h.torus_le_N i hδ) (coordG_mem φ i v), hδc, hψx]
  have hfix := hA.linFun_eq_of_normal le_rfl (map_subtype_le _)
    (fun g hg r hr => conj_mem_pCore_map hg hr) (CFSG.pCore_isPGroup.map _) h2K htrans he (ψ u)
  rw [hA.linFun_psi heN hu] at hfix
  rw [← hψc _ ((mem_normalizer_iff.mp (hNU heN) u).mp hu), hfix, hψc u hu]

theorem U_le_center_E (h : FCHyp L K n φ t) (i : Axis) :
    𝐔[i] ≤ (center 𝐄[i]).map 𝐄[i].subtype := by
  intro u hu
  refine mem_center_map_iff.mpr ⟨?_, fun y hy => ?_⟩
  · exact h.D_le_E i (h.B_le_D i (mem_sup_right (pull_mono φ (rootU_le_rootA i) hu)))
  · calc y * u = (y * u * y⁻¹) * y := by group
      _ = u * y := by rw [E_comm_U h i hy hu]

theorem commutator_E_A (h : FCHyp L K n φ t) (i : Axis) : ⁅𝐄[i], 𝐀[i]⁆ ≤ 𝐔[i] := by
  rw [commutator_le]
  intro e he a ha
  have h1 : a⁻¹ * (e * a * e⁻¹) ∈ 𝐔[i] := (kernel_A h i (map_subtype_le _ he)).mpr he a ha
  have haN : a ∈ 𝐍[i] := le_normalizer (mem_sup_right ha)
  rw [commutatorElement_def, show e * a * e⁻¹ * a⁻¹ = a * (a⁻¹ * (e * a * e⁻¹)) * a⁻¹ by group]
  exact (h.actHyp i).conj_U a haN _ h1

theorem commD_mem_U (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {a : G}
    (ha : a ∈ 𝐀[i]) : d * a * d⁻¹ * a⁻¹ ∈ 𝐔[i] := by
  have h1 := commutator_le.mp (commutator_E_A h i) d (h.D_le_E i hd) a ha
  rwa [commutatorElement_def] at h1

omit [Finite G] [Finite K] in
theorem A_mul_comm (h : FCHyp L K n φ t) (i : Axis) {x y : G} (hx : x ∈ 𝐀[i]) (hy : y ∈ 𝐀[i]) :
    x * y = y * x :=
  h.B_comm i (mem_sup_right hx) (mem_sup_right hy)

theorem commD_mul (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {a b : G}
    (ha : a ∈ 𝐀[i]) (hb : b ∈ 𝐀[i]) :
    d * (a * b) * d⁻¹ * (a * b)⁻¹ = (d * a * d⁻¹ * a⁻¹) * (d * b * d⁻¹ * b⁻¹) := by
  have hdN : d ∈ 𝐍[i] := h.twoCore.M_le_normalizer_B φ i (map_subtype_le _ hd)
  have hda : d * a * d⁻¹ ∈ 𝐀[i] := (h.actHyp i).conj_A d hdN a ha
  have hdb : d * b * d⁻¹ ∈ 𝐀[i] := (h.actHyp i).conj_A d hdN b hb
  have hcb : d * b * d⁻¹ * b⁻¹ ∈ 𝐀[i] := mul_mem hdb (inv_mem hb)
  have hca : d * a * d⁻¹ * a⁻¹ ∈ 𝐀[i] := mul_mem hda (inv_mem ha)
  calc d * (a * b) * d⁻¹ * (a * b)⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹ * b⁻¹) * a⁻¹ := by group
    _ = (d * b * d⁻¹ * b⁻¹) * (d * a * d⁻¹) * a⁻¹ := by rw [A_mul_comm h i hda hcb]
    _ = (d * b * d⁻¹ * b⁻¹) * (d * a * d⁻¹ * a⁻¹) := by group
    _ = (d * a * d⁻¹ * a⁻¹) * (d * b * d⁻¹ * b⁻¹) := A_mul_comm h i hcb hca

theorem commD_U (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {u : G}
    (hu : u ∈ 𝐔[i]) : d * u * d⁻¹ * u⁻¹ = 1 := by
  rw [E_comm_U h i (h.D_le_E i hd) hu, mul_inv_cancel]

theorem commD_eq_of_psiG_eq (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i])
    {a b : G} (ha : a ∈ 𝐀[i]) (hb : b ∈ 𝐀[i]) (hab : psiG φ i a = psiG φ i b) :
    d * b * d⁻¹ * b⁻¹ = d * a * d⁻¹ * a⁻¹ := by
  have hu : a⁻¹ * b ∈ 𝐔[i] := (psiG_eq_iff h.twoCore φ i ha hb).mp hab
  have e1 : b = a * (a⁻¹ * b) := by group
  rw [e1, commD_mul h i hd ha (pull_mono φ (rootU_le_rootA i) hu), commD_U h i hd hu, mul_one]

theorem conj_D_mul_inv_mem_B (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {s : G}
    (hsC : s ∈ 𝐂) (hsM : s ∈ 𝐌[i]) (hsU : ∀ u ∈ 𝐔[i], u * s = s * u) :
    s * d * s⁻¹ * d⁻¹ ∈ 𝐁[i] := by
  have hd'D : s * d * s⁻¹ ∈ 𝐃[i] := conj_mem_pCore_map hsM hd
  have hu : t * (d⁻¹ * t * d) ∈ 𝐔[i] := h.twoCore.conj_t_mem φ i (map_subtype_le _ hd)
  have hst : s * t = t * s := mem_centralizer_singleton_iff.mp hsC
  have hsts : s⁻¹ * t * s = t := by rw [mul_assoc, ← hst, inv_mul_cancel_left]
  set u := t * (d⁻¹ * t * d) with hu_def
  have e1 : d⁻¹ * t * d = t * u := by rw [hu_def, ← mul_assoc t t, h.setup.t_mul_t, one_mul]
  have h1 : (s * d * s⁻¹)⁻¹ * t * (s * d * s⁻¹) = d⁻¹ * t * d := by
    calc (s * d * s⁻¹)⁻¹ * t * (s * d * s⁻¹) = s * (d⁻¹ * (s⁻¹ * t * s) * d) * s⁻¹ := by group
      _ = s * (t * u) * s⁻¹ := by rw [hsts, e1]
      _ = (s * t * s⁻¹) * (s * u * s⁻¹) := by group
      _ = t * u := by rw [hst, mul_inv_cancel_right, ← hsU u hu, mul_inv_cancel_right]
      _ = d⁻¹ * t * d := e1.symm
  have hC : s * d * s⁻¹ * d⁻¹ ∈ 𝐂 := by
    rw [mem_centralizer_singleton_iff]
    calc s * d * s⁻¹ * d⁻¹ * t = (s * d * s⁻¹) * (d⁻¹ * t * d) * d⁻¹ := by group
      _ = (s * d * s⁻¹) * ((s * d * s⁻¹)⁻¹ * t * (s * d * s⁻¹)) * d⁻¹ := by rw [h1]
      _ = t * (s * d * s⁻¹ * d⁻¹) := by group
  have h2 : s * d * s⁻¹ * d⁻¹ ∈ 𝐃[i] ⊓ 𝐂 := mem_inf.mpr ⟨mul_mem hd'D (inv_mem hd), hC⟩
  rwa [h.D_inf_C i] at h2

theorem commD_conj_s (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {a : G}
    (ha : a ∈ 𝐀[i]) (M : SL₂ K) :
    d * (((φ.symm (sHom K i M) : L) : G) * a * ((φ.symm (sHom K i M) : L) : G)⁻¹) * d⁻¹ *
      (((φ.symm (sHom K i M) : L) : G) * a * ((φ.symm (sHom K i M) : L) : G)⁻¹)⁻¹ =
      d * a * d⁻¹ * a⁻¹ := by
  set s : G := ((φ.symm (sHom K i M) : L) : G)
  obtain ⟨hsC, -, -, -⟩ := h.symm_s_mem i M
  have hsU : ∀ u ∈ 𝐔[i], u * s = s * u :=
    ((TwoCoreSetup.mem_pull_rootC_iff φ i).mp (symm_s_mem_rootC h.twoCore φ i M)).2
  have hb := conj_D_mul_inv_mem_B h i hd hsC (h.symm_s_mem_M i M) hsU
  have hdN : d ∈ 𝐍[i] := h.twoCore.M_le_normalizer_B φ i (map_subtype_le _ hd)
  have ha' : s * a * s⁻¹ ∈ 𝐀[i] := (psiG_conj_s h.twoCore φ i M ha).1
  have hda' : d * (s * a * s⁻¹) * d⁻¹ ∈ 𝐀[i] := (h.actHyp i).conj_A d hdN _ ha'
  have hbc := h.B_comm i hb (mem_sup_right hda')
  have hc := commD_mem_U h i hd ha
  calc d * (s * a * s⁻¹) * d⁻¹ * (s * a * s⁻¹)⁻¹
      = (s * d * s⁻¹ * d⁻¹) * (d * (s * a * s⁻¹) * d⁻¹) * (s * d * s⁻¹ * d⁻¹)⁻¹ *
          (s * a * s⁻¹)⁻¹ := by rw [hbc, mul_inv_cancel_right]
    _ = s * (d * a * d⁻¹ * a⁻¹) * s⁻¹ := by group
    _ = d * a * d⁻¹ * a⁻¹ := by rw [← hsU _ hc, mul_inv_cancel_right]

theorem D_comm_A (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) {a : G}
    (ha : a ∈ 𝐀[i]) : d * a = a * d := by
  obtain ⟨a₁, ha₁, hψ₁⟩ := exists_psiG_eq h.twoCore φ i ![1, 0]
  obtain ⟨a₂, ha₂, hψ₂⟩ := exists_psiG_eq h.twoCore φ i ![0, 1]
  have hne : (![1, 0] : Fin 2 → K) ≠ 0 := fun h0 => by
    have := congrFun h0 0
    simp at this
  have hconst : ∀ x ∈ 𝐀[i], psiG φ i x ≠ 0 →
      d * x * d⁻¹ * x⁻¹ = d * a₁ * d⁻¹ * a₁⁻¹ := by
    intro x hx hx0
    obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq hne hx0
    obtain ⟨hs1, hs2⟩ := psiG_conj_s h.twoCore φ i M ha₁
    rw [commD_eq_of_psiG_eq h i hd hs1 hx (by rw [hs2, hψ₁, hM]), commD_conj_s h i hd ha₁ M]
  have h12 : psiG φ i (a₁ * a₂) ≠ 0 := by
    rw [psiG_mul h.twoCore φ i ha₁ ha₂, hψ₁, hψ₂]
    intro h0
    have := congrFun h0 0
    simp at this
  have h2 : psiG φ i a₂ ≠ 0 := by
    rw [hψ₂]
    intro h0
    have := congrFun h0 1
    simp at this
  have hz := commD_mul h i hd ha₁ ha₂
  rw [hconst _ (mul_mem ha₁ ha₂) h12, hconst _ ha₂ h2] at hz
  have hc1 : d * a₁ * d⁻¹ * a₁⁻¹ = 1 := mul_eq_left.mp hz.symm
  have hca : d * a * d⁻¹ * a⁻¹ = 1 := by
    by_cases ha0 : psiG φ i a = 0
    · exact commD_U h i hd ((psiG_eq_zero_iff h.twoCore φ i ha).mp ha0)
    · rw [hconst a ha ha0, hc1]
  calc d * a = d * a * d⁻¹ * a⁻¹ * (a * d) := by group
    _ = a * d := by rw [hca, one_mul]

theorem commutator_D_A (h : FCHyp L K n φ t) (i : Axis) : ⁅𝐃[i], 𝐀[i]⁆ = ⊥ :=
  commutator_eq_bot_iff_le_centralizer.mpr fun _ hd =>
    mem_centralizer_iff.mpr fun _ ha => (D_comm_A h i hd ha).symm

theorem center_D (h : FCHyp L K n φ t) (i : Axis) : (center 𝐃[i]).map 𝐃[i].subtype = 𝐀[i] := by
  have hAD : 𝐀[i] ≤ 𝐃[i] := le_sup_right.trans (h.B_le_D i)
  apply le_antisymm
  · intro x hx
    obtain ⟨hxD, hxc⟩ := mem_center_map_iff.mp hx
    have htD : t ∈ 𝐃[i] := h.B_le_D i (mem_sup_left (mem_zpowers t))
    have hxC : x ∈ 𝐂 := mem_centralizer_singleton_iff.mpr (hxc t htD).symm
    have hxB : x ∈ 𝐁[i] := by
      have h1 : x ∈ 𝐃[i] ⊓ 𝐂 := mem_inf.mpr ⟨hxD, hxC⟩
      rwa [h.D_inf_C i] at h1
    rcases (mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)).mp hxB with
      hxA | hxA
    · exact hxA
    · exfalso
      have htc : ∀ y ∈ 𝐃[i], y * t = t * y := by
        intro y hy
        have h1 := hxc y hy
        have h2 := D_comm_A h i hy hxA
        calc y * t = y * (t * x) * x⁻¹ := by group
          _ = t * x * y * x⁻¹ := by rw [h2]
          _ = t * x * (x⁻¹ * (y * x) * x⁻¹) := by rw [h1]; group
          _ = t * y := by group
      have hDB : 𝐃[i] = 𝐁[i] := by
        rw [← h.D_inf_C i]
        exact (inf_of_le_left fun y hy => mem_centralizer_singleton_iff.mpr (htc y hy)).symm
      have h1 := h.card_D i
      rw [hDB, h.card_B i] at h1
      have h4 := h.four_le_card
      have h5 : Nat.card K ^ 3 < Nat.card K ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
  · intro a ha
    exact mem_center_map_iff.mpr ⟨hAD ha, fun y hy => D_comm_A h i hy ha⟩

end Cores

structure CoreFacts {G : Type} [Group G] {K : Type} [Field K] (n : ℕ) (t : G)
    (C U A B M N D E : Subgroup G) (ψ : G → Fin 2 → K) : Prop where
  D_lt_E : D < E
  card_D : Nat.card D = 2 * (2 ^ n) ^ 4
  card_E : Nat.card E = 2 * (2 ^ n) ^ 6
  E_mul_M : (E : Set G) * (M : Set G) = N
  E_mul_C0 : (E : Set G) * ((C ⊓ N : Subgroup G) : Set G) = N
  E_inf_M : E ⊓ M = D
  E_inf_C0 : E ⊓ (C ⊓ N) = B
  orbit_E : {x : G | ∃ e ∈ E, x = e⁻¹ * t * e} = {x | ∃ a ∈ A, x = t * a}
  E_inf_C : E ⊓ C = B
  quotient_E : ∃ _ : (D.subgroupOf E).Normal, ∃ _ : (U.subgroupOf A).Normal,
    ∃ e : (↥E ⧸ D.subgroupOf E) ≃* (↥A ⧸ U.subgroupOf A),
      (∀ x : E, ∃ a : A, (a : G) = t⁻¹ * ((x : G)⁻¹ * t * x) ∧ e x = a) ∧
      (∀ h ∈ C ⊓ N, ∀ x : E, ∃ x' : E, (x' : G) = h⁻¹ * x * h ∧
        ∀ a a' : A, (a' : G) = h⁻¹ * a * h → e x = a → e x' = a')
  kernel : ∀ g ∈ N, (∀ a ∈ A, a⁻¹ * (g * a * g⁻¹) ∈ U) ↔ g ∈ E
  psi_iso : (∀ a ∈ A, ∀ b ∈ A, ψ (a * b) = ψ a + ψ b) ∧ (∀ a ∈ A, ψ a = 0 ↔ a ∈ U) ∧
    ∀ v : Fin 2 → K, ∃ a ∈ A, ψ a = v
  action : ∃ μ : N →* Equiv.Perm (Fin 2 → K),
    (∀ g : N, ∀ a ∈ A, μ g (ψ a) = ψ ((g : G) * a * (g : G)⁻¹)) ∧
    μ.ker = E.subgroupOf N ∧
    (∀ g : N, ∃ (A₀ : GL (Fin 2) K) (k : ℕ), k < n ∧
      ∀ x : Fin 2 → K, μ g x = (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => x j ^ 2 ^ k) ∧
    (∀ A₀ : GL (Fin 2) K, ∃ g : N, (g : G) ∈ C ∧
      ∀ x : Fin 2 → K, μ g x = (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ x) ∧
    ∃ _ : (E.subgroupOf N).Normal,
      ∃ μq : (↥N ⧸ E.subgroupOf N) →* Equiv.Perm (Fin 2 → K),
        Function.Injective μq ∧ (∀ g : N, μq g = μ g) ∧
        ∃ _ : (B.subgroupOf (C ⊓ N)).Normal,
          ∃ μc : (↥(C ⊓ N) ⧸ B.subgroupOf (C ⊓ N)) →* Equiv.Perm (Fin 2 → K),
            Function.Injective μc ∧
            (∀ g : ↥(C ⊓ N), μc g = μ (Subgroup.inclusion (inf_le_right : C ⊓ N ≤ N) g)) ∧
            μc.range = μq.range
  U_le_center : U ≤ (Subgroup.center E).map E.subtype
  commutator_E_A : ⁅E, A⁆ ≤ U
  commutator_D_A : ⁅D, A⁆ = ⊥
  center_D : (Subgroup.center D).map D.subtype = A

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

theorem coreFacts (h : FCHyp L K n φ t) (i : Axis) :
    CoreFacts n t (centralizer ({t} : Set G)) (pull φ (rootU K i)) (pull φ (rootA K i))
      (zpowers t ⊔ pull φ (rootA K i)) (normalizer ((zpowers t ⊔ pull φ (rootU K i) :
        Subgroup G) : Set G)) (normalizer ((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Set G))
      ((CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
        Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
        Set G)).subtype)
      ((CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
        Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
        Set G)).subtype) (psiG φ i) := by
  have htr := translations_mem_E h i
  have hq := h.setup.card_K
  obtain ⟨hDE, hUA, e, he1, he2, -⟩ := h.quotient_E i htr
  have hA := h.actHyp i
  exact
    { D_lt_E := D_lt_E h i
      card_D := by rw [h.card_D, hq]
      card_E := by rw [card_E h i, hq]
      E_mul_M := (h.E_mul_M i htr).1
      E_mul_C0 := E_mul_C0 h i
      E_inf_M := (h.E_mul_M i htr).2
      E_inf_C0 := E_inf_C0 h i
      orbit_E := orbit_E h i
      E_inf_C := E_inf_C h i
      quotient_E := ⟨hDE, hUA, e, he1, he2⟩
      kernel := fun _ hg => kernel_A h i hg
      psi_iso := ⟨hA.add, hA.ker, hA.surj⟩
      action := linear_action h i
      U_le_center := U_le_center_E h i
      commutator_E_A := commutator_E_A h i
      commutator_D_A := commutator_D_A h i
      center_D := center_D h i }

end FullCenterRadical

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

theorem standard_symplectic_four_full_center_radical_two_cores
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let C := centralizer ({(t : G)} : Set G)
    let U : Axis → Subgroup G := fun i => ((rootU K i).comap φ.toMonoidHom).map L.subtype
    let A : Axis → Subgroup G := fun i => ((rootA K i).comap φ.toMonoidHom).map L.subtype
    let V : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ U i
    let B : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ A i
    let M : Axis → Subgroup G := fun i => normalizer (V i : Set G)
    let N : Axis → Subgroup G := fun i => normalizer (B i : Set G)
    let D : Axis → Subgroup G := fun i => (CFSG.pCore 2 (M i)).map (M i).subtype
    let E : Axis → Subgroup G := fun i => (CFSG.pCore 2 (N i)).map (N i).subtype
    let ψ : Axis → G → Fin 2 → K := fun i => psiG φ i
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z} →
    (∀ i : Axis, CoreFacts n (t : G) C (U i) (A i) (B i) (M i) (N i) (D i) (E i) (ψ i)) ∧
      ((∀ a b c : K, ψ Axis.two ((φ.symm (uElt a b c 0) : L) : G) = ![b, a]) ∧
        ∀ b c d : K,
          ψ Axis.one ((φ.symm (uElt 0 b c d) : L) : G) = ![c ^ 2 ^ (n - 1), d ^ 2 ^ (n - 1)]) := by
  intro TG PG Q ZP C U A V B M N D E ψ hfull
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    change (center ↥PG).map PG.subtype = _
    rw [hPG, center_pull_antiUnipotent]
  have hfull' : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) :
      Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z} := by
    rw [← hPG, ← hZP]
    exact hfull
  obtain ⟨-, hF⟩ := FCHyp.of_setup hS (hO := hO) hLn hfull'
  exact ⟨fun i => coreFacts hF i, psiG_two_uElt φ, psiG_one_uElt hK (by omega) φ⟩

end CFSG.LocalAnalysis.SymplecticFourStandard
