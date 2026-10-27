module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommSquareFactors

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace NextCores

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem conj_mem_pCore_of_mem_normalizer {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ normalizer (J : Set G)) {x : G} (hx : x ∈ (CFSG.pCore p J).map J.subtype) :
    g * x * g⁻¹ ∈ (CFSG.pCore p J).map J.subtype := by
  let σ : J ≃* J :=
    { toFun := fun y => ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp y.2⟩
      invFun := fun y => ⟨g⁻¹ * y * g, (mem_normalizer_iff.mp hg _).mpr (by
        rw [show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y by group]
        exact y.2)⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group)
      map_mul' := fun y y' => Subtype.ext (by simp only [coe_mul]; group) }
  obtain ⟨y, hy, rfl⟩ := hx
  have hc := (CFSG.pCore_characteristic (p := p) (G := J)).fixed σ.symm
  have hσy : σ y ∈ CFSG.pCore p J := by
    rw [← hc]
    show σ.symm (σ y) ∈ CFSG.pCore p J
    rwa [MulEquiv.symm_apply_apply]
  exact ⟨σ y, hσy, rfl⟩

theorem exists_quotient_equiv_of_hom {P E U : Subgroup G} (f : G → G)
    (hf : ∀ x ∈ P, f x ∈ U) (hmul : ∀ x ∈ P, ∀ y ∈ P, f (x * y) = f x * f y)
    (hker : ∀ x ∈ P, f x = 1 ↔ x ∈ E) (hsurj : ∀ u ∈ U, ∃ x ∈ P, f x = u) :
    ∃ _ : (E.subgroupOf P).Normal, ∃ e : (↥P ⧸ E.subgroupOf P) ≃* ↥U,
      ∀ x : P, (e (x : ↥P ⧸ E.subgroupOf P) : G) = f x := by
  let θ : P →* U :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      map_one' := Subtype.ext ((hker 1 (one_mem P)).mpr (one_mem E))
      map_mul' := fun x y => Subtype.ext (hmul x x.2 y y.2) }
  have hkerEq : E.subgroupOf P = θ.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun hx => Subtype.ext ((hker x x.2).mpr hx), fun hx =>
      (hker x x.2).mp (congrArg Subtype.val hx)⟩
  have hN : (E.subgroupOf P).Normal := hkerEq ▸ θ.normal_ker
  have hθs : Function.Surjective θ := fun u => by
    obtain ⟨x, hx, hxu⟩ := hsurj u u.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxu⟩
  refine ⟨hN, (QuotientGroup.quotientMulEquivOfEq hkerEq).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs), fun x => rfl⟩

end General

section FirstCore

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
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
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐃𝐧[" i "]" => normalizer ((𝐃[i] : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype

variable (φ t) in
@[expose] noncomputable def psiK (i : Axis) (x : G) : K :=
  Function.invFun (coordG φ i) (t⁻¹ * (x⁻¹ * t * x))

omit [Finite G] [Finite K] in
theorem coordG_psiK {i : Axis} {x : G} (hx : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔[i]) :
    coordG φ i (psiK φ t i x) = t⁻¹ * (x⁻¹ * t * x) := by
  obtain ⟨y, hy⟩ := exists_coordG_eq φ i hx
  exact Function.invFun_eq ⟨y, hy⟩

omit [Finite G] [Finite K] in
theorem psiK_eq_iff {i : Axis} {x : G} (hx : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔[i]) {y : K} :
    psiK φ t i x = y ↔ t⁻¹ * (x⁻¹ * t * x) = coordG φ i y := by
  rw [← coordG_psiK hx]
  exact (coordG_injective φ i).eq_iff.symm

theorem kappa_K_mem_U (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐊[i]) :
    t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔[i] :=
  kappa_mem_U h i (K_le_D h i hx)

theorem psiK_mul (h : FCHyp L K n φ t) (i : Axis) {x y : G} (hx : x ∈ 𝐊[i]) (hy : y ∈ 𝐊[i]) :
    psiK φ t i (x * y) = psiK φ t i x + psiK φ t i y := by
  rw [psiK_eq_iff (kappa_K_mem_U h i (mul_mem hx hy)), coordG_add, coordG_psiK
    (kappa_K_mem_U h i hx), coordG_psiK (kappa_K_mem_U h i hy)]
  exact kappa_mul h (K_le_H h i hx) (K_le_H h i hy)

theorem psiK_eq_zero_iff (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐊[i]) :
    psiK φ t i x = 0 ↔ x ∈ 𝐀[i] := by
  rw [psiK_eq_iff (kappa_K_mem_U h i hx), coordG_zero, kappa_eq_one_iff, ← K_inf_C h i]
  exact ⟨fun hc => ⟨hx, hc⟩, fun hc => hc.2⟩

theorem exists_psiK_eq (h : FCHyp L K n φ t) (i : Axis) (v : K) :
    ∃ x ∈ 𝐊[i], psiK φ t i x = v := by
  obtain ⟨f, hf, hfv⟩ := exists_kappa_eq_Fi h i (coordG_mem φ i v)
  have hfK : f ∈ 𝐊[i] := mem_sup_right hf
  exact ⟨f, hfK, (psiK_eq_iff (kappa_K_mem_U h i hfK)).mpr hfv⟩

theorem conj_mem_A_of_normalizer_D (h : FCHyp L K n φ t) (i : Axis) {g : G}
    (hg : g ∈ 𝐃𝐧[i]) {a : G} (ha : a ∈ 𝐀[i]) : g * a * g⁻¹ ∈ 𝐀[i] :=
  (mem_normalizer_iff.mp (normalizer_D_le_normalizer_A h i hg) a).mp ha

theorem conj_t_mem_K (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐃𝐧[i]) :
    t⁻¹ * (g * t * g⁻¹) ∈ 𝐊[i] := by
  have hgt : g * t * g⁻¹ ∈ 𝐃[i] := (mem_normalizer_iff.mp hg t).mp (t_mem_D h i)
  rw [← (K_sup_t h i).2] at hgt
  have htD : t ∈ 𝐃𝐧[i] := le_normalizer (t_mem_D h i)
  have htK : t ∈ normalizer (𝐊[i] : Set G) :=
    mem_normalizer_of_conj_le fun x hx => conj_mem_K_of_normalizer_D h i htD hx
  rcases mem_or_mul_mem h.setup.t_mul_t htK hgt with h1 | h1
  · exfalso
    apply t_not_mem_K h i
    have := conj_mem_K_of_normalizer_D h i (inv_mem hg) h1
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
  · rwa [h.twoCore.t_inv]

theorem actHyp₁ (h : FCHyp L K n φ t) (i : Axis) :
    FullCenter.ActHyp (psiK φ t i) t 𝐊[i] 𝐀[i] 𝐃𝐧[i] where
  U_le := le_sup_left
  add := fun _ hx _ hy => psiK_mul h i hx hy
  ker := fun _ hx => psiK_eq_zero_iff h i hx
  surj := exists_psiK_eq h i
  conj_A := fun _ hg _ hx => conj_mem_K_of_normalizer_D h i hg hx
  conj_U := fun _ hg _ ha => conj_mem_A_of_normalizer_D h i hg ha
  conj_t := fun _ hg => conj_t_mem_K h i hg

theorem aff₁_zero_eq_zero_iff (h : FCHyp L K n φ t) (i : Axis) (g : 𝐃𝐧[i]) :
    (actHyp₁ h i).aff g 0 = 0 ↔ (g : G) ∈ 𝐍[i] := by
  rw [(actHyp₁ h i).aff_zero, psiK_eq_zero_iff h i (conj_t_mem_K h i g.2)]
  constructor
  · intro ha
    refine mem_normalizer_zpowers_sup ?_ fun w hw => conj_mem_A_of_normalizer_D h i g.2 hw
    rw [show (g : G) * t * (g : G)⁻¹ = t * (t⁻¹ * ((g : G) * t * (g : G)⁻¹)) by group]
    exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right ha)
  · intro hgN
    have hmem : (g : G) * t * (g : G)⁻¹ ∈
        {x : G | ∃ g ∈ 𝐍[i], x = g⁻¹ * t * g} := ⟨(g : G)⁻¹, inv_mem hgN, by rw [inv_inv]⟩
    rw [h.orbit_N i] at hmem
    obtain ⟨a, ha, he⟩ := hmem
    rw [he, ← mul_assoc, inv_mul_cancel, one_mul]
    exact ha

theorem kappa_conj_N (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐍[i]) {d : G}
    (hd : d ∈ 𝐃[i]) :
    t⁻¹ * ((g * d * g⁻¹)⁻¹ * t * (g * d * g⁻¹)) = g * (t⁻¹ * (d⁻¹ * t * d)) * g⁻¹ := by
  obtain ⟨a, ha, hga⟩ : ∃ a ∈ 𝐀[i], g * t * g⁻¹ = t * a := by
    have hmem : g * t * g⁻¹ ∈ {x : G | ∃ g ∈ 𝐍[i], x = g⁻¹ * t * g} :=
      ⟨g⁻¹, inv_mem hg, by rw [inv_inv]⟩
    rw [h.orbit_N i] at hmem
    exact hmem
  have hd' : g * d * g⁻¹ ∈ 𝐃[i] := h.conj_mem_D i hg hd
  set d' := g * d * g⁻¹ with hd'def
  have h1 : a * d' = d' * a := A_comm_D h i ha hd'
  have h2 : a * t = t * a := (h.twoCore.comm (pull_le φ _ ha)).symm
  have hX : Commute a (t⁻¹ * (d'⁻¹ * t * d')) :=
    (Commute.inv_right h2).mul_right
      (((Commute.inv_right h1).mul_right h2).mul_right h1)
  have e : g * (t⁻¹ * (d⁻¹ * t * d)) * g⁻¹ = (g * t * g⁻¹)⁻¹ * (d'⁻¹ * (g * t * g⁻¹) * d') := by
    rw [hd'def]
    group
  rw [e, hga]
  calc t⁻¹ * (d'⁻¹ * t * d') = a⁻¹ * (a * (t⁻¹ * (d'⁻¹ * t * d'))) := by group
    _ = a⁻¹ * ((t⁻¹ * (d'⁻¹ * t * d')) * a) := by rw [hX.eq]
    _ = (t * a)⁻¹ * (d'⁻¹ * (t * a) * d') := by
      rw [show d'⁻¹ * (t * a) * d' = d'⁻¹ * t * (a * d') by group, h1]
      group

theorem coordG_aff₁_of_N (h : FCHyp L K n φ t) (i : Axis) (g : 𝐃𝐧[i]) (hgN : (g : G) ∈ 𝐍[i])
    (v : K) : coordG φ i ((actHyp₁ h i).aff g v) = (g : G) * coordG φ i v * (g : G)⁻¹ := by
  obtain ⟨k, hk, rfl⟩ := exists_psiK_eq h i v
  have hgk : (g : G) * k * (g : G)⁻¹ ∈ 𝐊[i] := conj_mem_K_of_normalizer_D h i g.2 hk
  rw [(actHyp₁ h i).aff_eq, (actHyp₁ h i).lin_psi g hk]
  have h0 : psiK φ t i (t⁻¹ * ((g : G) * t * (g : G)⁻¹)) = 0 := by
    rw [← (actHyp₁ h i).aff_zero]
    exact (aff₁_zero_eq_zero_iff h i g).mpr hgN
  rw [h0, add_zero, coordG_psiK (kappa_K_mem_U h i hgk), coordG_psiK (kappa_K_mem_U h i hk)]
  exact kappa_conj_N h i hgN (K_le_D h i hk)

theorem aff₁_of_scalar (h : FCHyp L K n φ t) (i : Axis) (g : 𝐃𝐧[i]) (hgN : (g : G) ∈ 𝐍[i])
    {μ : K} (hμ : ∀ x, (g : G) * coordG φ i x * (g : G)⁻¹ = coordG φ i (μ * x)) (v : K) :
    (actHyp₁ h i).aff g v = μ * v := by
  apply coordG_injective φ i
  rw [coordG_aff₁_of_N h i g hgN, hμ]

variable (φ t) in
@[expose] def kerJ (i : Axis) : Subgroup G :=
  normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G) ⊓
    centralizer ((pull φ (rootU K i) : Subgroup G) : Set G)

theorem aff₁_eq_one_iff (h : FCHyp L K n φ t) (i : Axis) (g : 𝐃𝐧[i]) :
    (actHyp₁ h i).aff g = 1 ↔ (g : G) ∈ kerJ φ t i := by
  constructor
  · intro h1
    have hgN : (g : G) ∈ 𝐍[i] := (aff₁_zero_eq_zero_iff h i g).mp (by rw [h1]; rfl)
    refine ⟨hgN, mem_centralizer_iff.mpr fun u hu => ?_⟩
    obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
    have := coordG_aff₁_of_N h i g hgN x
    rw [h1] at this
    change coordG φ i x = _ at this
    calc coordG φ i x * (g : G) = (g : G) * coordG φ i x * (g : G)⁻¹ * g := by rw [← this]
      _ = (g : G) * coordG φ i x := by group
  · rintro ⟨hgN, hgU⟩
    refine Equiv.ext fun v => coordG_injective φ i ?_
    rw [coordG_aff₁_of_N h i g hgN, ← mem_centralizer_iff.mp hgU _ (coordG_mem φ i v),
      mul_inv_cancel_right]
    rfl

theorem kerJ_le (h : FCHyp L K n φ t) (i : Axis) : kerJ φ t i ≤ 𝐃𝐧[i] :=
  fun _ hy => N_le_normalizer_D h i hy.1

theorem conj_mem_kerJ (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐃𝐧[i]) {y : G}
    (hy : y ∈ kerJ φ t i) : g * y * g⁻¹ ∈ kerJ φ t i := by
  have hyD := kerJ_le h i hy
  have hgy : g * y * g⁻¹ ∈ 𝐃𝐧[i] := mul_mem (mul_mem hg hyD) (inv_mem hg)
  have hρy := (aff₁_eq_one_iff h i ⟨y, hyD⟩).mpr hy
  refine (aff₁_eq_one_iff h i ⟨_, hgy⟩).mp ?_
  have e : (⟨g * y * g⁻¹, hgy⟩ : 𝐃𝐧[i]) = ⟨g, hg⟩ * ⟨y, hyD⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, hρy, mul_one, map_inv, mul_inv_cancel]

theorem E_le_kerJ (h : FCHyp L K n φ t) (i : Axis) : 𝐄[i] ≤ kerJ φ t i := fun e he =>
  ⟨map_subtype_le _ he, mem_centralizer_iff.mpr fun u hu => by
    have := E_comm_U h i he hu
    calc u * e = e * u * e⁻¹ * e := by rw [this]
      _ = e * u := by group⟩

theorem cent_le_kerJ (h : FCHyp L K n φ t) (i : Axis) :
    centralizer ((𝐕[i] : Subgroup G) : Set G) ≤ kerJ φ t i := fun _ hc =>
  ⟨h.twoCore.M_le_normalizer_B φ i (centralizer_le_normalizer _ hc),
    (mem_centralizer_sup_iff.mp hc).2⟩

theorem exists_kerJ_decomp (h : FCHyp L K n φ t) (i : Axis) {y : G} (hy : y ∈ kerJ φ t i) :
    ∃ e ∈ 𝐄[i], ∃ c ∈ centralizer ((𝐕[i] : Subgroup G) : Set G), y = e * c := by
  have hyN : y ∈ (𝐄[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) := by
    rw [E_mul_C0 h i]
    exact hy.1
  obtain ⟨e, he, c, hc, rfl⟩ := hyN
  refine ⟨e, he, c, ?_, rfl⟩
  have hcJ : c ∈ kerJ φ t i := by
    have := mul_mem (inv_mem (E_le_kerJ h i he)) hy
    rwa [inv_mul_cancel_left] at this
  refine mem_centralizer_sup_iff.mpr ⟨mem_centralizer_zpowers_iff'.mpr ?_, hcJ.2⟩
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp hc).1

theorem E_eq_pCore_kerJ (h : FCHyp L K n φ t) (i : Axis) :
    𝐄[i] = (CFSG.pCore 2 (kerJ φ t i)).map (kerJ φ t i).subtype := by
  set J := kerJ φ t i with hJ
  apply le_antisymm
  · intro e he
    have heJ := E_le_kerJ h i he
    have hn : ((𝐄[i]).subgroupOf J).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      exact conj_mem_pCore_map (g.2.1) hx⟩
    have hp : IsPGroup 2 ((𝐄[i]).subgroupOf J) :=
      (CFSG.pCore_isPGroup.map _).of_equiv (subgroupOfEquivOfLe (E_le_kerJ h i)).symm
    have hle : (𝐄[i]).subgroupOf J ≤ CFSG.pCore 2 J := le_sSup ⟨hn, hp⟩
    exact mem_map.mpr ⟨⟨e, heJ⟩, hle (mem_subgroupOf.mpr he), rfl⟩
  · intro x hx
    set R0 := (CFSG.pCore 2 J).map J.subtype with hR0
    have hR0N : R0 ≤ 𝐍[i] := (map_subtype_le _).trans inf_le_left
    have hn : (R0.subgroupOf 𝐍[i]).Normal := ⟨fun y hy g => by
      rw [mem_subgroupOf] at hy ⊢
      refine conj_mem_pCore_of_mem_normalizer ?_ hy
      exact mem_normalizer_of_conj_le fun z hz =>
        conj_mem_kerJ h i (N_le_normalizer_D h i g.2) hz⟩
    have hp : IsPGroup 2 (R0.subgroupOf 𝐍[i]) :=
      (CFSG.pCore_isPGroup.map _).of_equiv (subgroupOfEquivOfLe hR0N).symm
    have hle : R0.subgroupOf 𝐍[i] ≤ CFSG.pCore 2 𝐍[i] := le_sSup ⟨hn, hp⟩
    exact mem_map.mpr ⟨⟨x, hR0N hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

theorem conj_mem_E_of_normalizer_D (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐃𝐧[i])
    {e : G} (he : e ∈ 𝐄[i]) : g * e * g⁻¹ ∈ 𝐄[i] := by
  rw [E_eq_pCore_kerJ h i] at he ⊢
  exact conj_mem_pCore_of_mem_normalizer
    (mem_normalizer_of_conj_le fun z hz => conj_mem_kerJ h i hg hz) he

@[expose] noncomputable def quotZ (h : FCHyp L K n φ t) (i : Axis) : Subgroup G :=
  quotCent 𝐃𝐧[i] (kerJ φ t i) 𝐄[i] (fun _ hg _ hy => conj_mem_kerJ h i hg hy)
    (fun _ hg _ he => conj_mem_E_of_normalizer_D h i hg he)

theorem mem_quotZ (h : FCHyp L K n φ t) (i : Axis) {g : G} :
    g ∈ quotZ h i ↔ g ∈ 𝐃𝐧[i] ∧ ∀ y ∈ kerJ φ t i, g * y * g⁻¹ * y⁻¹ ∈ 𝐄[i] :=
  mem_quotCent

theorem conj_mem_quotZ (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐃𝐧[i]) {z : G}
    (hz : z ∈ quotZ h i) : g * z * g⁻¹ ∈ quotZ h i :=
  conj_mem_quotCent hg hz

theorem E_le_quotZ (h : FCHyp L K n φ t) (i : Axis) : 𝐄[i] ≤ quotZ h i := by
  intro e he
  refine (mem_quotZ h i).mpr ⟨N_le_normalizer_D h i (map_subtype_le _ he), fun y hy => ?_⟩
  rw [show e * y * e⁻¹ * y⁻¹ = e * (y * e⁻¹ * y⁻¹) by group]
  exact mul_mem he (conj_mem_pCore_map hy.1 (inv_mem he))

theorem d_mem_N (h : FCHyp L K n φ t) (i : Axis) (l : Kˣ) :
    ((φ.symm (dHom K i l) : L) : G) ∈ 𝐍[i] :=
  h.torus_le_N i (symm_mem_pull.mpr (dHom_mem i l))

theorem d_mem_quotZ (h : FCHyp L K n φ t) (i : Axis) (l : Kˣ) :
    ((φ.symm (dHom K i l) : L) : G) ∈ quotZ h i := by
  set d := ((φ.symm (dHom K i l) : L) : G) with hd
  have hdN : d ∈ 𝐍[i] := d_mem_N h i l
  refine (mem_quotZ h i).mpr ⟨N_le_normalizer_D h i hdN, fun y hy => ?_⟩
  obtain ⟨e, he, c, hc, rfl⟩ := exists_kerJ_decomp h i hy
  have hdc : d * c * d⁻¹ * c⁻¹ ∈ 𝐄[i] :=
    h.D_le_E i (h.B_le_D i (h.twoCore.torus_mem_quotCent φ i l c hc))
  rw [show d * (e * c) * d⁻¹ * (e * c)⁻¹ = (d * e * d⁻¹) * (d * c * d⁻¹ * c⁻¹) * e⁻¹ by group]
  exact mul_mem (mul_mem (conj_mem_pCore_map hdN he) hdc) (inv_mem he)

theorem aff₁_d (h : FCHyp L K n φ t) (i : Axis) (l : Kˣ) (v : K) :
    (actHyp₁ h i).aff ⟨_, N_le_normalizer_D h i (d_mem_N h i l)⟩ v = (l : K) ^ 2 * v :=
  aff₁_of_scalar h i _ (d_mem_N h i l) (fun x => h.twoCore.torus_conj φ i l x) v

theorem aff₁_scalar_of_mem_quotZ (h : FCHyp L K n φ t) (i : Axis) (z : 𝐃𝐧[i])
    (hz : (z : G) ∈ quotZ h i) (hz0 : (actHyp₁ h i).aff z 0 = 0) :
    (actHyp₁ h i).aff z ∈ scalarPerm K := by
  have hzN : (z : G) ∈ 𝐍[i] := (aff₁_zero_eq_zero_iff h i z).mp hz0
  have hzN' : (z : G) ∈ (𝐄[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) := by
    rw [E_mul_C0 h i]
    exact hzN
  obtain ⟨e, he, c, hc, hzec⟩ := hzN'
  obtain ⟨hcC, hcN⟩ := mem_inf.mp hc
  have hcZ : c ∈ quotZ h i := by
    have := mul_mem (inv_mem (E_le_quotZ h i he)) hz
    rwa [← hzec, inv_mul_cancel_left] at this
  have hcM : c ∈ 𝐌[i] := by
    have : c ∈ 𝐂 ⊓ 𝐌[i] := by
      rw [h.twoCore.inf_normalizer_eq φ i]
      exact ⟨hcC, hcN⟩
    exact this.2
  have hzZ : ∀ y ∈ centralizer ((𝐕[i] : Subgroup G) : Set G), c * y * c⁻¹ * y⁻¹ ∈ 𝐁[i] := by
    intro y hy
    have h1 := ((mem_quotZ h i).mp hcZ).2 y (cent_le_kerJ h i hy)
    have hyC : y ∈ (𝐂 : Subgroup G) := by
      have := (mem_centralizer_sup_iff.mp hy).1
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_zpowers_iff'.mp this)
    rw [← E_inf_C h i]
    exact mem_inf.mpr ⟨h1, mul_mem (mul_mem (mul_mem hcC hyC) (inv_mem hcC)) (inv_mem hyC)⟩
  obtain ⟨l, hl⟩ := h.twoCore.exists_scalar φ i (h.M_not_le_C i) hcM hcC hzZ
  have heJ : e ∈ kerJ φ t i := E_le_kerJ h i he
  have hceD : c ∈ 𝐃𝐧[i] := N_le_normalizer_D h i hcN
  have hzdec : z = ⟨e, kerJ_le h i heJ⟩ * ⟨c, hceD⟩ := Subtype.ext hzec.symm
  have he1 : (actHyp₁ h i).aff ⟨e, kerJ_le h i heJ⟩ = 1 := (aff₁_eq_one_iff h i _).mpr heJ
  refine ⟨(l : K) ^ 2, pow_ne_zero 2 l.ne_zero, fun x => ?_⟩
  rw [hzdec, map_mul, he1, one_mul]
  exact aff₁_of_scalar h i ⟨c, hceD⟩ hcN hl x

theorem mem_E_of_mem_quotZ_kerJ (h : FCHyp L K n φ t) (i : Axis) {y : G}
    (hyZ : y ∈ quotZ h i) (hyJ : y ∈ kerJ φ t i) : y ∈ 𝐄[i] := by
  obtain ⟨e, he, c, hc, rfl⟩ := exists_kerJ_decomp h i hyJ
  have hcZ : c ∈ quotZ h i := by
    have := mul_mem (inv_mem (E_le_quotZ h i he)) hyZ
    rwa [inv_mul_cancel_left] at this
  have hcC : c ∈ (𝐂 : Subgroup G) := by
    have := (mem_centralizer_sup_iff.mp hc).1
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_zpowers_iff'.mp this)
  have hcB : c ∈ 𝐁[i] := by
    refine h.twoCore.mem_B_of_comm φ i hc fun y hy => ?_
    have h1 := ((mem_quotZ h i).mp hcZ).2 y (cent_le_kerJ h i hy)
    have hyC : y ∈ (𝐂 : Subgroup G) := by
      have := (mem_centralizer_sup_iff.mp hy).1
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_zpowers_iff'.mp this)
    rw [← E_inf_C h i]
    exact mem_inf.mpr ⟨h1, mul_mem (mul_mem (mul_mem hcC hyC) (inv_mem hcC)) (inv_mem hyC)⟩
  exact mul_mem he (h.D_le_E i (h.B_le_D i hcB))

theorem aff₁_translations (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (∀ b : K, ∃ z : 𝐃𝐧[i], (z : G) ∈ quotZ h i ∧ ∀ x, (actHyp₁ h i).aff z x = x + b) ∧
    ∀ R : Subgroup G, R ≤ 𝐃𝐧[i] → (∀ g ∈ 𝐃𝐧[i], ∀ r ∈ R, g * r * g⁻¹ ∈ R) → IsPGroup 2 R →
      ∀ r : 𝐃𝐧[i], (r : G) ∈ R → (actHyp₁ h i).aff r ∈ translPerm K := by
  set ρ := (actHyp₁ h i).aff with hρ
  set Z := quotZ h i with hZ
  have hscalar : ∀ a : K, a ≠ 0 → ∃ z : 𝐃𝐧[i], (z : G) ∈ Z ∧ ∀ x, ρ z x = a * x := by
    intro a ha
    obtain ⟨y, hy⟩ := exists_sq_eq a
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact ha (by rw [← hy]; ring)
    set l := Units.mk0 y hy0
    refine ⟨⟨_, N_le_normalizer_D h i (d_mem_N h i l)⟩, d_mem_quotZ h i l, fun x => ?_⟩
    rw [hρ, aff₁_d h i l x]
    simp only [l, Units.val_mk0, hy]
  set H : Subgroup (Equiv.Perm K) := ρ.range with hH
  set F : Subgroup (Equiv.Perm K) := (Z.subgroupOf 𝐃𝐧[i]).map ρ with hF
  have hHaff : H ≤ affPerm K := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(actHyp₁ h i).linAdd g, _, fun x => (actHyp₁ h i).aff_eq g x⟩
  have hSH : scalarPerm K ≤ H := by
    rintro s ⟨a, ha, hs⟩
    obtain ⟨z, -, hz⟩ := hscalar a ha
    exact ⟨z, Equiv.ext fun x => (hz x).trans (hs x).symm⟩
  have hFH : F ≤ H := map_le_range _ _
  have hFn : (F.subgroupOf H).Normal := by
    refine ⟨fun f hf h' => ?_⟩
    rw [mem_subgroupOf] at hf ⊢
    obtain ⟨z, hz, hzf⟩ := hf
    obtain ⟨g, hg⟩ := h'.2
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf] at hz ⊢
      exact conj_mem_quotZ h i g.2 hz
    · rw [map_mul, map_mul, map_inv, hg, hzf]
      rfl
  have hK2 : 2 < Nat.card K := by
    have := h.four_le_card
    omega
  have hfrom0 : ∀ y : K, ∃ f ∈ F, f 0 = y := by
    obtain ⟨m, hmD, hmB⟩ := exists_mem_normalizer_D_not_B h i hne hbot
    set g : 𝐃𝐧[i] := ⟨m, hmD⟩
    have hw : ρ g⁻¹ 0 ≠ 0 := by
      rw [Ne, hρ, aff₁_zero_eq_zero_iff h i]
      intro hm
      have hm' : m⁻¹⁻¹ ∈ 𝐍[i] := inv_mem (show m⁻¹ ∈ 𝐍[i] from hm)
      rw [inv_inv] at hm'
      exact hmB hm'
    obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne hK2 (1 : K)
    obtain ⟨z, hzZ, hz⟩ := hscalar a ha0
    have hfF : ρ (g * z * g⁻¹) ∈ F :=
      ⟨g * z * g⁻¹, mem_subgroupOf.mpr (conj_mem_quotZ h i g.2 hzZ), rfl⟩
    have hf0 : ρ (g * z * g⁻¹) 0 ≠ 0 := by
      obtain ⟨σ, b, hσ⟩ := hHaff ⟨g, rfl⟩
      have h1 : ρ (g * z * g⁻¹) 0 = ρ g (a * ρ g⁻¹ 0) := by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hz]
      have h2 : ρ g (ρ g⁻¹ 0) = 0 := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h1, hσ]
      rw [hσ] at h2
      intro h3
      have h4 : σ (a * ρ g⁻¹ 0 - ρ g⁻¹ 0) = 0 := by
        rw [map_sub]
        linear_combination h3 - h2
      have h5 : a * ρ g⁻¹ 0 - ρ g⁻¹ 0 = 0 := σ.injective (h4.trans (map_zero σ).symm)
      have h6 : (a - 1) * ρ g⁻¹ 0 = 0 := by linear_combination h5
      rcases mul_eq_zero.mp h6 with h7 | h7
      · exact ha1 (sub_eq_zero.mp h7).symm
      · exact hw h7
    intro y
    by_cases hy : y = 0
    · exact ⟨1, one_mem F, by rw [hy]; rfl⟩
    · obtain ⟨z', hz'Z, hz'⟩ := hscalar (y / ρ (g * z * g⁻¹) 0) (div_ne_zero hy hf0)
      refine ⟨ρ z' * ρ (g * z * g⁻¹), mul_mem ⟨z', mem_subgroupOf.mpr hz'Z, rfl⟩ hfF, ?_⟩
      rw [Equiv.Perm.mul_apply, hz', div_mul_cancel₀ y hf0]
  have htrans : ∀ x y : K, ∃ f ∈ F, f x = y := by
    intro x y
    obtain ⟨f₁, hf₁, h₁⟩ := hfrom0 x
    obtain ⟨f₂, hf₂, h₂⟩ := hfrom0 y
    refine ⟨f₂ * f₁⁻¹, mul_mem hf₂ (inv_mem hf₁), ?_⟩
    rw [Equiv.Perm.mul_apply, ← h₁, show f₁⁻¹ (f₁ 0) = 0 from Equiv.Perm.inv_eq_iff_eq.mpr rfl,
      h₂]
  have hF0 : ∀ f : Equiv.Perm K, f ∈ F ∧ f 0 = 0 ↔ f ∈ scalarPerm K := by
    intro f
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, h0⟩
      exact aff₁_scalar_of_mem_quotZ h i z (mem_subgroupOf.mp hz) h0
    · rintro ⟨a, ha, hf⟩
      obtain ⟨z, hzZ, hz⟩ := hscalar a ha
      have e : ρ z = f := Equiv.ext fun x => (hz x).trans (hf x).symm
      exact ⟨⟨z, mem_subgroupOf.mpr hzZ, e⟩, by rw [hf, mul_zero]⟩
  obtain ⟨-, hcore, hTF, -⟩ :=
    affine_scalar_sharply_two_transitive_normal_translations K H F hHaff hSH hFH hFn htrans hF0
  refine ⟨fun b => ?_, fun R hRD hRn hR2 r hr => ?_⟩
  · obtain ⟨z, hz, hzρ⟩ := hTF (show Equiv.addRight b ∈ translPerm K from ⟨b, fun _ => rfl⟩)
    exact ⟨z, mem_subgroupOf.mp hz, fun x => by rw [hzρ]; rfl⟩
  · set R' : Subgroup (Equiv.Perm K) := (R.subgroupOf 𝐃𝐧[i]).map ρ with hR'
    have hR'H : R' ≤ H := map_le_range _ _
    have hR'n : (R'.subgroupOf H).Normal := by
      refine ⟨fun f hf h' => ?_⟩
      rw [mem_subgroupOf] at hf ⊢
      obtain ⟨r', hr', hrf⟩ := hf
      obtain ⟨g, hg⟩ := h'.2
      refine ⟨g * r' * g⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf] at hr' ⊢
        exact hRn g g.2 r' hr'
      · rw [map_mul, map_mul, map_inv, hg, hrf]
        rfl
    have hR'2 : IsPGroup 2 (R'.subgroupOf H) :=
      ((hR2.of_equiv (subgroupOfEquivOfLe hRD).symm).map ρ).of_equiv
        (subgroupOfEquivOfLe hR'H).symm
    have hle : R'.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hR'n, hR'2⟩
    rw [hcore] at hle
    have hmem : (⟨ρ r, r, rfl⟩ : H) ∈ R'.subgroupOf H :=
      mem_subgroupOf.mpr ⟨r, mem_subgroupOf.mpr hr, rfl⟩
    exact mem_subgroupOf.mp (hle hmem)

omit [Finite G] [CharP K 2] [Finite K] in
theorem conj_mem_translPerm {f τ : Equiv.Perm K} (hf : f ∈ affPerm K) (hτ : τ ∈ translPerm K) :
    f * τ * f⁻¹ ∈ translPerm K := by
  obtain ⟨σ, b, hfσ⟩ := hf
  obtain ⟨c, hc⟩ := hτ
  refine ⟨σ c, fun x => ?_⟩
  have hy : f (f⁻¹ x) = x := perm_apply_inv_self f x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc, hfσ, map_add, add_right_comm, ← hfσ, hy]

omit [Finite G] [CharP K 2] [Finite K] in
theorem eq_one_of_mem_translPerm {τ : Equiv.Perm K} (hτ : τ ∈ translPerm K) {x : K}
    (hx : τ x = x) : τ = 1 := by
  obtain ⟨c, hc⟩ := hτ
  have hc0 : c = 0 := by
    have := hc x
    rw [hx] at this
    exact (add_eq_left.mp this.symm)
  exact Equiv.ext fun y => by rw [hc, hc0, add_zero]; rfl

theorem sq_eq_kappa (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {k : G} (hk : k ∈ 𝐊[i]) :
    k * k = t⁻¹ * (k⁻¹ * t * k) := by
  have hk' := hk
  rw [← SetLike.mem_coe, ← K_mul h i] at hk'
  obtain ⟨a, ha, f, hf, hkf⟩ := hk'
  rw [← W_mul_U h i] at hf
  obtain ⟨w, hw, u, hu, hfwu⟩ := hf
  have hkdec : k = a * (w * u) := by rw [← hkf, ← hfwu]
  subst hkdec
  have huA : u ∈ 𝐀[i] := pull_mono φ ((rootU_le_center _).trans (center_le_rootA i)) hu
  have hwK : w ∈ 𝐊[i] := mem_sup_right (W_le_Fi h i hw)
  have huK : u ∈ 𝐊[i] := mem_sup_left huA
  have haK : a ∈ 𝐊[i] := mem_sup_left ha
  have hwu : w * u = u * w := K_comm h i hwK huK
  set a' := a * u with ha'
  have ha'A : a' ∈ 𝐀[i] := mul_mem ha huA
  have he : a * (w * u) = a' * w := by rw [hwu, ← mul_assoc]
  rw [he]
  obtain ⟨x, hx⟩ := exists_coordG_eq φ i (kappa_mem_U h i (W_le_Fi h i hw).2)
  have hww : w * w = t⁻¹ * (w⁻¹ * t * w) := by
    rw [W_sq_eq h i hne hbot hw hx.symm, hx]
  have ha'w : a' * w = w * a' := K_comm h i (mem_sup_left ha'A) hwK
  have ha't : a' * t = t * a' := (h.twoCore.comm (pull_le φ _ ha'A)).symm
  have ha'a' : a' * a' = 1 := A_mul_self h i ha'A
  calc a' * w * (a' * w) = a' * a' * (w * w) := by
        rw [mul_assoc, ← mul_assoc w, ← ha'w]; group
    _ = t⁻¹ * (w⁻¹ * t * w) := by rw [ha'a', one_mul, hww]
    _ = t⁻¹ * ((a' * w)⁻¹ * t * (a' * w)) := by
        rw [show (a' * w)⁻¹ * t * (a' * w) = w⁻¹ * a'⁻¹ * (t * a') * w by group, ← ha't]
        group

variable (h) in
@[expose] noncomputable def transZ (h : FCHyp L K n φ t) (i : Axis) : Subgroup G :=
  quotZ h i ⊓ ((translPerm K).comap (actHyp₁ h i).aff).map 𝐃𝐧[i].subtype

theorem mem_transZ_iff (h : FCHyp L K n φ t) (i : Axis) (g : 𝐃𝐧[i]) :
    (g : G) ∈ transZ h i ↔ (g : G) ∈ quotZ h i ∧ (actHyp₁ h i).aff g ∈ translPerm K := by
  constructor
  · rintro ⟨hgZ, g', hg', hgg'⟩
    have e : g' = g := Subtype.ext hgg'
    exact ⟨hgZ, e ▸ hg'⟩
  · rintro ⟨hgZ, hg⟩
    exact ⟨hgZ, g, hg, rfl⟩

theorem transZ_le (h : FCHyp L K n φ t) (i : Axis) : transZ h i ≤ 𝐃𝐧[i] := fun _ hg =>
  ((mem_quotZ h i).mp hg.1).1

theorem conj_mem_transZ (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐃𝐧[i]) {x : G}
    (hx : x ∈ transZ h i) : g * x * g⁻¹ ∈ transZ h i := by
  have hxD := transZ_le h i hx
  obtain ⟨hxZ, hxT⟩ := (mem_transZ_iff h i ⟨x, hxD⟩).mp hx
  have hgx : g * x * g⁻¹ ∈ 𝐃𝐧[i] := mul_mem (mul_mem hg hxD) (inv_mem hg)
  refine (mem_transZ_iff h i ⟨_, hgx⟩).mpr ⟨conj_mem_quotZ h i hg hxZ, ?_⟩
  have e : (⟨g * x * g⁻¹, hgx⟩ : 𝐃𝐧[i]) = ⟨g, hg⟩ * ⟨x, hxD⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact conj_mem_translPerm ⟨(actHyp₁ h i).linAdd _, _, fun y => (actHyp₁ h i).aff_eq _ y⟩ hxT

theorem E_le_transZ (h : FCHyp L K n φ t) (i : Axis) : 𝐄[i] ≤ transZ h i := by
  intro e he
  have heD : e ∈ 𝐃𝐧[i] := kerJ_le h i (E_le_kerJ h i he)
  refine (mem_transZ_iff h i ⟨e, heD⟩).mpr ⟨E_le_quotZ h i he, ?_⟩
  rw [(aff₁_eq_one_iff h i ⟨e, heD⟩).mpr (E_le_kerJ h i he)]
  exact one_mem _

theorem mem_E_of_mem_transZ (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ transZ h i)
    (hxN : x ∈ 𝐍[i]) : x ∈ 𝐄[i] := by
  have hxD := transZ_le h i hx
  obtain ⟨hxZ, hxT⟩ := (mem_transZ_iff h i ⟨x, hxD⟩).mp hx
  have h0 : (actHyp₁ h i).aff ⟨x, hxD⟩ 0 = 0 := (aff₁_zero_eq_zero_iff h i _).mpr hxN
  have h1 := eq_one_of_mem_translPerm hxT h0
  exact mem_E_of_mem_quotZ_kerJ h i hxZ ((aff₁_eq_one_iff h i _).mp h1)

theorem isPGroup_transZ (h : FCHyp L K n φ t) (i : Axis) : IsPGroup 2 (transZ h i) := by
  intro g
  have hgD := transZ_le h i g.2
  obtain ⟨-, hgT⟩ := (mem_transZ_iff h i ⟨g, hgD⟩).mp g.2
  have hsq : (actHyp₁ h i).aff (⟨g, hgD⟩ ^ 2) = 1 := by
    obtain ⟨b, hb⟩ := hgT
    ext x
    rw [map_pow, pow_two, Equiv.Perm.mul_apply, hb, hb, add_assoc, CharTwo.add_self_eq_zero,
      add_zero]
    rfl
  have hg2E : (g : G) ^ 2 ∈ 𝐄[i] :=
    mem_E_of_mem_quotZ_kerJ h i (pow_mem ((mem_transZ_iff h i ⟨g, hgD⟩).mp g.2).1 2)
      ((aff₁_eq_one_iff h i _).mp hsq)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup.map (𝐍[i]).subtype) ⟨_, hg2E⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' := congrArg Subtype.val hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk' ⊢
  rw [pow_succ', pow_mul]
  exact hk'

theorem le_transZ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {R : Subgroup G} (hRD : R ≤ 𝐃𝐧[i])
    (hRn : ∀ g ∈ 𝐃𝐧[i], ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR2 : IsPGroup 2 R) : R ≤ transZ h i := by
  have hRJ : R ⊓ kerJ φ t i ≤ 𝐄[i] := by
    intro x hx
    have hxN : x ∈ 𝐍[i] := (mem_inf.mp hx).2.1
    have hn : ((R ⊓ kerJ φ t i).subgroupOf 𝐍[i]).Normal := ⟨fun y hy g => by
      rw [mem_subgroupOf] at hy ⊢
      have hgD := N_le_normalizer_D h i g.2
      exact mem_inf.mpr ⟨hRn _ hgD _ (mem_inf.mp hy).1, conj_mem_kerJ h i hgD (mem_inf.mp hy).2⟩⟩
    have hle' : R ⊓ kerJ φ t i ≤ 𝐍[i] := fun y hy => (mem_inf.mp hy).2.1
    have hp : IsPGroup 2 ((R ⊓ kerJ φ t i).subgroupOf 𝐍[i]) :=
      ((hR2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe hle').symm)
    have hle : (R ⊓ kerJ φ t i).subgroupOf 𝐍[i] ≤ CFSG.pCore 2 𝐍[i] := le_sSup ⟨hn, hp⟩
    exact mem_map.mpr ⟨⟨x, hxN⟩, hle (mem_subgroupOf.mpr hx), rfl⟩
  intro r hr
  have hrD := hRD hr
  refine (mem_transZ_iff h i ⟨r, hrD⟩).mpr ⟨(mem_quotZ h i).mpr ⟨hrD, fun y hy => ?_⟩,
    (aff₁_translations h i hne hbot).2 R hRD hRn hR2 _ hr⟩
  refine hRJ (mem_inf.mpr ⟨?_, ?_⟩)
  · rw [show r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) by group]
    exact mul_mem hr (hRn y (kerJ_le h i hy) _ (inv_mem hr))
  · exact mul_mem (conj_mem_kerJ h i hrD hy) (inv_mem hy)

theorem pCore_eq_transZ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] = transZ h i :=
  pCore_map_eq (transZ_le h i) (fun _ hg _ hx => conj_mem_transZ h i hg hx)
    (isPGroup_transZ h i) fun _ hRD hRn hR2 => le_transZ h i hne hbot hRD hRn hR2

theorem aff₁_transZ (h : FCHyp L K n φ t) (i : Axis) (x : 𝐃𝐧[i])
    (hx : (x : G) ∈ transZ h i) (v : K) :
    (actHyp₁ h i).aff x v = v + (actHyp₁ h i).aff x 0 := by
  obtain ⟨b, hb⟩ := ((mem_transZ_iff h i x).mp hx).2
  rw [hb, hb, zero_add]

theorem E_le_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐄[i] ≤ 𝐏₁[i] := by
  rw [pCore_eq_transZ h i hne hbot]
  exact E_le_transZ h i

omit [Finite G] [Finite K] in
theorem P₁_le (i : Axis) : 𝐏₁[i] ≤ 𝐃𝐧[i] := map_subtype_le _

omit [Finite G] [Finite K] in
theorem conj_mem_P₁ (i : Axis) {g : G} (hg : g ∈ 𝐃𝐧[i]) {x : G} (hx : x ∈ 𝐏₁[i]) :
    g * x * g⁻¹ ∈ 𝐏₁[i] :=
  conj_mem_pCore_map hg hx

theorem P₁_inf_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐏₁[i] ⊓ 𝐍[i] = 𝐄[i] := by
  apply le_antisymm
  · intro x hx
    rw [pCore_eq_transZ h i hne hbot] at hx
    exact mem_E_of_mem_transZ h i hx.1 hx.2
  · exact le_inf (E_le_P₁ h i hne hbot) (map_subtype_le _)

theorem P₁_mul_N (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    (𝐏₁[i] : Set G) * (𝐍[i] : Set G) = (𝐃𝐧[i] : Set G) := by
  ext g
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (P₁_le i hx) (N_le_normalizer_D h i hy)
  · intro hg
    obtain ⟨z, hzZ, hz⟩ := (aff₁_translations h i hne hbot).1 ((actHyp₁ h i).aff ⟨g, hg⟩ 0)
    have hzT : (z : G) ∈ transZ h i :=
      (mem_transZ_iff h i z).mpr ⟨hzZ, ⟨_, hz⟩⟩
    refine ⟨z, (pCore_eq_transZ h i hne hbot).symm ▸ hzT, (z : G)⁻¹ * g, ?_, by group⟩
    have e : (⟨(z : G)⁻¹ * g, mul_mem (inv_mem z.2) hg⟩ : 𝐃𝐧[i]) = z⁻¹ * ⟨g, hg⟩ := rfl
    refine (aff₁_zero_eq_zero_iff h i ⟨_, mul_mem (inv_mem z.2) hg⟩).mp ?_
    rw [e, map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.inv_eq_iff_eq, hz, zero_add]

theorem kappa_P₁ (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐃𝐧[i]) :
    t⁻¹ * (x⁻¹ * t * x) ∈ 𝐊[i] ∧
      psiK φ t i (t⁻¹ * (x⁻¹ * t * x)) = (actHyp₁ h i).aff ⟨x, hx⟩⁻¹ 0 := by
  have h1 := conj_t_mem_K h i (inv_mem hx)
  rw [inv_inv] at h1
  refine ⟨h1, ?_⟩
  rw [(actHyp₁ h i).aff_zero]
  simp only [coe_inv, inv_inv]

theorem quotient_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ _ : ((𝐄[i]).subgroupOf 𝐏₁[i]).Normal, ∃ e : (↥𝐏₁[i] ⧸ (𝐄[i]).subgroupOf 𝐏₁[i]) ≃* ↥𝐔[i],
      ∀ x : 𝐏₁[i], (e (x : ↥𝐏₁[i] ⧸ (𝐄[i]).subgroupOf 𝐏₁[i]) : G) =
        (t⁻¹ * ((x : G)⁻¹ * t * x)) * (t⁻¹ * ((x : G)⁻¹ * t * x)) := by
  set ρ := (actHyp₁ h i).aff with hρ
  have hsq : ∀ x (hx : x ∈ 𝐃𝐧[i]), (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) =
      coordG φ i (ρ ⟨x, hx⟩⁻¹ 0) := by
    intro x hx
    obtain ⟨hK, hψ⟩ := kappa_P₁ h i hx
    rw [sq_eq_kappa h i hne hbot hK, hρ, ← hψ, coordG_psiK (kappa_K_mem_U h i hK)]
  have hT : ∀ x (hx : x ∈ 𝐏₁[i]), (x : G) ∈ transZ h i := fun x hx =>
    (pCore_eq_transZ h i hne hbot) ▸ hx
  refine exists_quotient_equiv_of_hom
    (fun x => (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))) ?_ ?_ ?_ ?_
  · intro x hx
    rw [hsq x (P₁_le i hx)]
    exact coordG_mem φ i _
  · intro x hx y hy
    rw [hsq x (P₁_le i hx), hsq y (P₁_le i hy), hsq (x * y) (mul_mem (P₁_le i hx) (P₁_le i hy)),
      ← coordG_add]
    congr 1
    have e : (⟨x * y, mul_mem (P₁_le i hx) (P₁_le i hy)⟩ : 𝐃𝐧[i])⁻¹ =
        (⟨y, P₁_le i hy⟩ : 𝐃𝐧[i])⁻¹ * (⟨x, P₁_le i hx⟩ : 𝐃𝐧[i])⁻¹ := by
      rw [← mul_inv_rev]
      rfl
    rw [e, map_mul, Equiv.Perm.mul_apply, aff₁_transZ h i _ (inv_mem (hT y hy)), add_comm]
  · intro x hx
    rw [hsq x (P₁_le i hx), ← coordG_zero φ i, (coordG_injective φ i).eq_iff,
      aff₁_zero_eq_zero_iff h i]
    constructor
    · intro hxN
      rw [← P₁_inf_N h i hne hbot]
      have hx' : x⁻¹⁻¹ ∈ 𝐍[i] := inv_mem (show x⁻¹ ∈ 𝐍[i] from hxN)
      rw [inv_inv] at hx'
      exact mem_inf.mpr ⟨hx, hx'⟩
    · intro hxE
      exact inv_mem (map_subtype_le _ hxE)
  · intro u hu
    obtain ⟨b, rfl⟩ := exists_coordG_eq φ i hu
    obtain ⟨z, hzZ, hz⟩ := (aff₁_translations h i hne hbot).1 b
    have hzT : (z : G) ∈ transZ h i := (mem_transZ_iff h i z).mpr ⟨hzZ, ⟨_, hz⟩⟩
    have hzP : (z : G)⁻¹ ∈ 𝐏₁[i] := (pCore_eq_transZ h i hne hbot).symm ▸ inv_mem hzT
    refine ⟨(z : G)⁻¹, hzP, ?_⟩
    rw [hsq _ (P₁_le i hzP)]
    have e : (⟨(z : G)⁻¹, P₁_le i hzP⟩ : 𝐃𝐧[i])⁻¹ = z := by
      apply Subtype.ext
      show ((z : G)⁻¹)⁻¹ = z
      rw [inv_inv]
    rw [e, hz, zero_add]

theorem card_P₁ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐏₁[i] = 2 * Nat.card K ^ 7 := by
  obtain ⟨_, e, -⟩ := quotient_P₁ h i hne hbot
  have h1 := card_eq_card_quotient_mul_card_subgroup ((𝐄[i]).subgroupOf 𝐏₁[i])
  rw [Nat.card_congr e.toEquiv, card_U, Nat.card_congr (subgroupOfEquivOfLe
    (E_le_P₁ h i hne hbot)).toEquiv, card_E h i] at h1
  rw [h1]
  ring

end FirstCore

end NextCores

end CFSG.LocalAnalysis.SymplecticFourStandard
