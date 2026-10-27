module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresComplement
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RootStandard

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem exists_mul_of_coprime [Finite G] {p : ℕ} (hp : p.Prime) {J Q : Subgroup G}
    (hJQ : J ≤ normalizer (Q : Set G)) (hQ : IsPGroup p Q) (hJ : ¬ p ∣ Nat.card J) {x : G}
    (hx : x ∈ Q) :
    ∃ d ∈ closure {y : G | ∃ q ∈ Q, ∃ b ∈ J, y = q⁻¹ * (b * q * b⁻¹)},
      ∃ c ∈ Q ⊓ centralizer (J : Set G), x = d * c := by
  let : MulDistribMulAction J Q := Subgroup.conjMulDistribMulActionOfLeNormalizer J Q hJQ
  obtain ⟨hfac, -⟩ := CFSG.LocalAnalysis.ComponentInitial.coprime_pgroup_commutator_factorization
    (A := J) (Q := Q) hp hQ hJ
  obtain ⟨d, hd, c, hc, hxdc⟩ := hfac ⟨x, hx⟩
  refine ⟨d, ?_, c, ⟨c.2, mem_centralizer_iff.mpr fun b hb => ?_⟩, congrArg Subtype.val hxdc⟩
  · have hle : (CFSG.LocalAnalysis.ComponentInitial.actionCommutator J (⊤ : Subgroup Q)).map
        Q.subtype ≤ closure {y : G | ∃ q ∈ Q, ∃ b ∈ J, y = q⁻¹ * (b * q * b⁻¹)} := by
      rw [CFSG.LocalAnalysis.ComponentInitial.actionCommutator, MonoidHom.map_closure,
        closure_le]
      rintro _ ⟨y, ⟨q, -, b, rfl⟩, rfl⟩
      exact subset_closure ⟨q, q.2, b, b.2, rfl⟩
    exact hle ⟨d, hd, rfl⟩
  · have h1 : (⟨b, hb⟩ : J) • c = c := hc ⟨b, hb⟩
    have h2 : (b : G) * c * b⁻¹ = c := congrArg Subtype.val h1
    calc b * (c : G) = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [h2]

theorem not_two_dvd_card_of_pow [Finite G] {J : Subgroup G} {m : ℕ} (hm : Odd m)
    (hJ : ∀ j ∈ J, j ^ m = 1) : ¬ 2 ∣ Nat.card J := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h3 : x ^ m = 1 := Subtype.ext (by simpa using hJ x x.2)
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hx] at h4
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h4)

theorem conj_mem_inf_centralizer {M J : Subgroup G} {g : G} (hgM : g ∈ normalizer (M : Set G))
    (hgJ : ∀ b ∈ J, Commute b g) {x : G} (hx : x ∈ M ⊓ centralizer (J : Set G)) :
    g * x * g⁻¹ ∈ M ⊓ centralizer (J : Set G) :=
  ⟨(mem_normalizer_iff.mp hgM x).mp hx.1, mem_centralizer_iff.mpr fun b hb =>
    (((hgJ b hb).mul_right (mem_centralizer_iff.mp hx.2 b hb)).mul_right
      (hgJ b hb).inv_right).eq⟩

theorem exists_quotient_equiv_of_hom {V W U : Subgroup G} (f : G → G) (hf : ∀ x ∈ V, f x ∈ U)
    (hmul : ∀ x ∈ V, ∀ y ∈ V, f (x * y) = f x * f y) (hker : ∀ x ∈ V, f x = 1 ↔ x ∈ W)
    (hsurj : ∀ u ∈ U, ∃ x ∈ V, f x = u) :
    ∃ _ : (W.subgroupOf V).Normal, ∃ e : (↥V ⧸ W.subgroupOf V) ≃* ↥U,
      ∀ x : V, (e (x : ↥V ⧸ W.subgroupOf V) : G) = f x := by
  have h1 : f 1 = 1 := by
    have h := hmul 1 (one_mem V) 1 (one_mem V)
    rw [mul_one] at h
    exact mul_eq_left.mp h.symm
  let θ : V →* U :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      map_one' := Subtype.ext h1
      map_mul' := fun x y => Subtype.ext (hmul x x.2 y y.2) }
  have hkerEq : W.subgroupOf V = θ.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    change (x : G) ∈ W ↔ (⟨f x, hf x x.2⟩ : U) = 1
    rw [← Subtype.coe_inj]
    exact (hker x x.2).symm
  have hθs : Function.Surjective θ := fun u => by
    obtain ⟨x, hx, hxu⟩ := hsurj u u.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxu⟩
  have hN : (W.subgroupOf V).Normal := hkerEq ▸ θ.normal_ker
  exact ⟨hN, (QuotientGroup.quotientMulEquivOfEq hkerEq).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs), fun x => rfl⟩

end General

section Torus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
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
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}
set_option quotPrecheck false in
local notation "𝐕[" i "," k "]" => (𝐌₀[i] ⊓ centralizer (𝐉[k] : Set G) : Subgroup G)

omit [Finite G] [Finite K] [CharP K 2] in
theorem exists_mul_axisTorus {j : G} (hj : j ∈ 𝐉) :
    ∃ b₁ ∈ 𝐉[Axis.one], ∃ b₂ ∈ 𝐉[Axis.two], j = b₁ * b₂ := by
  obtain ⟨δ, ⟨r, s, hr, hs, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
  obtain ⟨δ₁, -, hδ₁⟩ := exists_diagTorus (K := K) hr (inv_ne_zero hr)
  obtain ⟨δ₂, -, hδ₂⟩ := exists_diagTorus (K := K) one_ne_zero (mul_ne_zero hr hs)
  refine ⟨_, symm_mem_pull.mpr ⟨r, hr, hδ₁⟩, _, symm_mem_pull.mpr ⟨r * s, mul_ne_zero hr hs, hδ₂⟩,
    ?_⟩
  have e : δ = δ₁ * δ₂ := by
    apply antiSp_ext
    change glMat (δ : GL (Fin 4) K) = glMat (δ₁ : GL (Fin 4) K) * glMat (δ₂ : GL (Fin 4) K)
    rw [hδ, hδ₁, hδ₂, diagMat_mul_diagMat, mul_one, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  rw [e, map_mul, coe_mul]

omit [Finite G] [Finite K] [CharP K 2] in
theorem mem_centralizer_J0 (i : Axis) {x : G} (h1 : x ∈ centralizer (𝐉[i] : Set G))
    (h2 : x ∈ centralizer (𝐉[i.swap] : Set G)) : x ∈ centralizer (𝐉 : Set G) := by
  have key : x ∈ centralizer (𝐉[Axis.one] : Set G) → x ∈ centralizer (𝐉[Axis.two] : Set G) →
      x ∈ centralizer (𝐉 : Set G) := fun e1 e2 => mem_centralizer_iff.mpr fun j hj => by
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mul_axisTorus hj
    rw [mul_assoc, mem_centralizer_iff.mp e2 b₂ hb₂, ← mul_assoc,
      mem_centralizer_iff.mp e1 b₁ hb₁, mul_assoc]
  cases i
  · exact key h1 h2
  · exact key h2 h1

theorem not_two_dvd_card_J (h : FCHyp L K n φ t) (k : Axis) : ¬ 2 ∣ Nat.card 𝐉[k] :=
  not_two_dvd_card_of_pow (odd_card_sub_one h) fun _ hj =>
    torus_pow_card_sub_one (axisTorus_le_J0 k hj)

theorem F_eq_W_sup_W (h : FCHyp L K n φ t) (i : Axis) : 𝐅 = 𝐖[i] ⊔ 𝐖[i.swap] := by
  have h1 : 𝐅 = 𝐖[Axis.one] ⊔ 𝐖[Axis.two] := by
    refine le_antisymm (fun f hf => ?_) (sup_le (W_le_F _) (W_le_F _))
    rw [← SetLike.mem_coe, ← W_mul_W h] at hf
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  cases i
  · exact h1
  · exact h1.trans (sup_comm _ _)

theorem W_inf_W_swap_eq (h : FCHyp L K n φ t) (i : Axis) : 𝐖[i] ⊓ 𝐖[i.swap] = ⊥ := by
  cases i
  · exact W_inf_W h
  · rw [inf_comm]
    exact W_inf_W h

theorem isPGroup_M (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : IsPGroup 2 𝐌₀[i] :=
  IsPGroup.of_card (n := n * 5) (by rw [card_M h i hne hbot, h.setup.card_K, ← pow_mul])

theorem isPGroup_W (h : FCHyp L K n φ t) (k : Axis) : IsPGroup 2 𝐖[k] :=
  IsPGroup.of_card (n := n * 2) (by rw [card_W h k, h.setup.card_K, ← pow_mul])

theorem W_le_M (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐖[k] ≤ 𝐌₀[i] :=
  (W_le_F k).trans (F_le_M h i hne hbot)

theorem conj_M_mem_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {m : G} (hm : m ∈ 𝐌₀[i]) {f : G} (hf : f ∈ 𝐅) :
    m * f * m⁻¹ ∈ 𝐅 :=
  conj_P₀_mem_F h i hne hbot (M_le_P₀ h i hm) hf

theorem eq_one_of_mem_W_of_fix (h : FCHyp L K n φ t) {j₀ : G} (hj₀ : GoodTorus φ j₀) (k : Axis)
    {w : G} (hw : w ∈ 𝐖[k]) (hfix : j₀⁻¹ * w * j₀ = w) : w = 1 := by
  have hκU : t⁻¹ * (w⁻¹ * t * w) ∈ 𝐔[k] := kappa_mem_U h k (mem_inf.mp (W_le_Fi h k hw)).2
  have hκ1 : t⁻¹ * (w⁻¹ * t * w) = 1 := by
    refine hj₀.fpf _ (pull_mono φ (rootU_le_center k) hκU) ?_
    rw [← kappa_conj_torus h hj₀.mem, hfix]
  have hwU : w ∈ 𝐔[k] := (W_inf_C h k).le ⟨hw, kappa_eq_one_iff.mp hκ1⟩
  exact hj₀.fpf _ (pull_mono φ (rootU_le_center k) hwU) hfix

theorem eq_one_of_mem_F_of_fix (h : FCHyp L K n φ t) {j₀ : G} (hj₀ : GoodTorus φ j₀) {f : G}
    (hf : f ∈ 𝐅) (hfix : j₀⁻¹ * f * j₀ = f) : f = 1 := by
  have hf' : f ∈ (𝐖[Axis.one] : Set G) * (𝐖[Axis.two] : Set G) := by
    rw [W_mul_W h]
    exact hf
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hf'
  subst hab
  rw [SetLike.mem_coe] at ha hb
  have ha' := conj_torus_mem_W h Axis.one hj₀.mem ha
  have hb' := conj_torus_mem_W h Axis.two hj₀.mem hb
  have e : (j₀⁻¹ * a * j₀) * (j₀⁻¹ * b * j₀) = a * b := by
    rw [← hfix]
    group
  have hab : a⁻¹ * (j₀⁻¹ * a * j₀) = b * (j₀⁻¹ * b * j₀)⁻¹ := by
    calc a⁻¹ * (j₀⁻¹ * a * j₀) = a⁻¹ * ((j₀⁻¹ * a * j₀) * (j₀⁻¹ * b * j₀)) *
          (j₀⁻¹ * b * j₀)⁻¹ := by group
      _ = b * (j₀⁻¹ * b * j₀)⁻¹ := by rw [e]; group
  have h1 : a⁻¹ * (j₀⁻¹ * a * j₀) ∈ 𝐖[Axis.one] ⊓ 𝐖[Axis.two] :=
    mem_inf.mpr ⟨mul_mem (inv_mem ha) ha', hab ▸ mul_mem hb (inv_mem hb')⟩
  rw [W_inf_W h, mem_bot] at h1
  have hafix : j₀⁻¹ * a * j₀ = a := by
    calc j₀⁻¹ * a * j₀ = a * (a⁻¹ * (j₀⁻¹ * a * j₀)) := by group
      _ = a := by rw [h1, mul_one]
  have hbfix : j₀⁻¹ * b * j₀ = b := by
    have h2 : b * (j₀⁻¹ * b * j₀)⁻¹ = 1 := hab ▸ h1
    calc j₀⁻¹ * b * j₀ = (b * (j₀⁻¹ * b * j₀)⁻¹)⁻¹ * b := by group
      _ = b := by rw [h2, inv_one, one_mul]
  rw [eq_one_of_mem_W_of_fix h hj₀ _ ha hafix, eq_one_of_mem_W_of_fix h hj₀ _ hb hbfix,
    mul_one]

theorem eq_one_of_mem_M_of_fix (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {j₀ : G}
    (hj₀ : GoodTorus φ j₀) {x : G} (hx : x ∈ 𝐌₀[i]) (hfix : j₀⁻¹ * x * j₀ = x) : x = 1 := by
  have hxP : x ∈ 𝐏₁[i] := (mem_inf.mp (M_le_P₀ h i hx)).1
  have hκU := sq_kappa_mem_U h i hne hbot hxP
  have hκ1 : (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) = 1 := by
    refine hj₀.fpf _ (pull_mono φ (rootU_le_center i) hκU) ?_
    have := sq_kappa_conj_torus h (inv_mem hj₀.mem) x
    rw [inv_inv, hfix] at this
    exact this.symm
  have hxE : x ∈ 𝐄[i] := (sq_kappa_eq_one_iff h i hne hbot hxP).mp hκ1
  have hxF : x ∈ 𝐅 := by
    rw [← M_inf_E h i hne hbot]
    exact ⟨hx, hxE⟩
  exact eq_one_of_mem_F_of_fix h hj₀ hxF hfix

theorem sq_kappa_inv (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐏₁[i]) :
    (t⁻¹ * (x⁻¹⁻¹ * t * x⁻¹)) * (t⁻¹ * (x⁻¹⁻¹ * t * x⁻¹)) *
      ((t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))) = 1 := by
  rw [← sq_kappa_mul h i hne hbot (inv_mem hx) hx, inv_mul_cancel]
  simp

theorem inv_mul_conj_mem_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {b : G} (hb : b ∈ 𝐉[i]) {x : G} (hx : x ∈ 𝐌₀[i]) :
    x⁻¹ * (b * x * b⁻¹) ∈ 𝐅 := by
  have hbx : b * x * b⁻¹ ∈ 𝐌₀[i] :=
    (mem_normalizer_iff.mp (J_le_normalizer_M h i hne hbot (axisTorus_le_J0 i hb)) x).mp hx
  have hxP : x ∈ 𝐏₁[i] := (mem_inf.mp (M_le_P₀ h i hx)).1
  have hyP : b * x * b⁻¹ ∈ 𝐏₁[i] := (mem_inf.mp (M_le_P₀ h i hbx)).1
  have hU := sq_kappa_mem_U h i hne hbot hxP
  have hfixU := axisTorus_cent i (inv_mem hb) hU
  rw [inv_inv] at hfixU
  have h1 := sq_kappa_conj_torus h (axisTorus_le_J0 i hb) x
  rw [hfixU] at h1
  have h3 : (t⁻¹ * ((x⁻¹ * (b * x * b⁻¹))⁻¹ * t * (x⁻¹ * (b * x * b⁻¹)))) *
      (t⁻¹ * ((x⁻¹ * (b * x * b⁻¹))⁻¹ * t * (x⁻¹ * (b * x * b⁻¹)))) = 1 := by
    rw [sq_kappa_mul h i hne hbot (inv_mem hxP) hyP, h1]
    exact sq_kappa_inv h i hne hbot hxP
  have hE : x⁻¹ * (b * x * b⁻¹) ∈ 𝐄[i] :=
    (sq_kappa_eq_one_iff h i hne hbot (mul_mem (inv_mem hxP) hyP)).mp h3
  rw [← M_inf_E h i hne hbot]
  exact mem_inf.mpr ⟨mul_mem (inv_mem hx) hbx, hE⟩

theorem exists_F_mul_V (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐌₀[i]) :
    ∃ f ∈ 𝐅, ∃ a ∈ 𝐕[i, i], x = f * a := by
  obtain ⟨d, hd, c, hc, rfl⟩ := exists_mul_of_coprime Nat.prime_two
    ((axisTorus_le_J0 i).trans (J_le_normalizer_M h i hne hbot)) (isPGroup_M h i hne hbot)
    (not_two_dvd_card_J h i) hx
  refine ⟨d, ?_, c, hc, rfl⟩
  refine (closure_le _).mpr ?_ hd
  rintro _ ⟨q, hq, b, hb, rfl⟩
  exact inv_mul_conj_mem_F h i hne hbot hb hq

theorem V_inf_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐕[i, k] ⊓ 𝐅 = 𝐖[k] :=
  le_antisymm (fun _ hx => ⟨hx.2, hx.1.2⟩)
    (fun _ hx => ⟨⟨F_le_M h i hne hbot hx.1, hx.2⟩, hx.1⟩)

theorem W_le_V (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐖[k] ≤ 𝐕[i, k] :=
  fun _ hx => ⟨W_le_M h i hne hbot k hx, hx.2⟩

theorem exists_V_mul_W (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐌₀[i]) :
    ∃ a ∈ 𝐕[i, i], ∃ w ∈ 𝐖[i.swap], x = a * w := by
  obtain ⟨f, hf, a, ha, rfl⟩ := exists_F_mul_V h i hne hbot hx
  have hf' : a⁻¹ * f * a ∈ 𝐅 := by
    have := conj_M_mem_F h i hne hbot (inv_mem (mem_inf.mp ha).1) hf
    rwa [inv_inv] at this
  have hfW : a⁻¹ * f * a ∈ 𝐖[i] ⊔ 𝐖[i.swap] := by
    rw [← F_eq_W_sup_W h i]
    exact hf'
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := (mem_sup_of_commute fun x hx y hy =>
    F_comm h (W_le_F _ hx) (W_le_F _ hy)).mp hfW
  refine ⟨a * w₁, mul_mem ha (W_le_V h i hne hbot i hw₁), w₂, hw₂, ?_⟩
  rw [mul_assoc, hw]
  group

theorem W_swap_inf_centralizer (h : FCHyp L K n φ t) (i : Axis) :
    𝐖[i.swap] ⊓ centralizer (𝐉[i] : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ 𝐖[i] ⊓ 𝐖[i.swap] := ⟨⟨W_le_F _ hx.1, hx.2⟩, hx.1⟩
  rwa [W_inf_W_swap_eq h i] at h1

theorem W_swap_le_closure (h : FCHyp L K n φ t) (i : Axis) :
    𝐖[i.swap] ≤ closure {y : G | ∃ q ∈ 𝐖[i.swap], ∃ b ∈ 𝐉[i], y = q⁻¹ * (b * q * b⁻¹)} := by
  intro w hw
  have hJW : 𝐉[i] ≤ normalizer (𝐖[i.swap] : Set G) := fun b hb =>
    mem_normalizer_of_conj_le fun _ hx => by
      simpa using conj_torus_mem_W h i.swap (inv_mem (axisTorus_le_J0 i hb)) hx
  obtain ⟨d, hd, c, hc, rfl⟩ := exists_mul_of_coprime Nat.prime_two hJW (isPGroup_W h i.swap)
    (not_two_dvd_card_J h i) hw
  have hc1 : c = 1 := by
    have := hc
    rwa [W_swap_inf_centralizer h i, mem_bot] at this
  rw [hc1, mul_one]
  exact hd

theorem inv_mul_conj_mem_W_swap (h : FCHyp L K n φ t) (i : Axis) {f : G} (hf : f ∈ 𝐅) {b : G}
    (hb : b ∈ 𝐉[i]) : f⁻¹ * (b * f * b⁻¹) ∈ 𝐖[i.swap] := by
  have hfW : f ∈ 𝐖[i] ⊔ 𝐖[i.swap] := by
    rw [← F_eq_W_sup_W h i]
    exact hf
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := (mem_sup_of_commute fun x hx y hy =>
    F_comm h (W_le_F _ hx) (W_le_F _ hy)).mp hfW
  have hc : b * w₁ = w₁ * b := mem_centralizer_iff.mp (mem_inf.mp hw₁).2 b hb
  have hb' : b * w₂ * b⁻¹ ∈ 𝐖[i.swap] := by
    simpa using conj_torus_mem_W h i.swap (inv_mem (axisTorus_le_J0 i hb)) hw₂
  have e : (w₁ * w₂)⁻¹ * (b * (w₁ * w₂) * b⁻¹) = w₂⁻¹ * (b * w₂ * b⁻¹) := by
    calc (w₁ * w₂)⁻¹ * (b * (w₁ * w₂) * b⁻¹) = w₂⁻¹ * w₁⁻¹ * ((b * w₁) * w₂ * b⁻¹) := by group
      _ = w₂⁻¹ * (b * w₂ * b⁻¹) := by rw [hc]; group
  rw [e]
  exact mul_mem (inv_mem hw₂) hb'

theorem conj_V_mem_W_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {a : G} (ha : a ∈ 𝐕[i, i]) {w : G}
    (hw : w ∈ 𝐖[i.swap]) : a * w * a⁻¹ ∈ 𝐖[i.swap] := by
  have hle : (closure {y : G | ∃ q ∈ 𝐖[i.swap], ∃ b ∈ 𝐉[i], y = q⁻¹ * (b * q * b⁻¹)}).map
      (MulAut.conj a).toMonoidHom ≤ 𝐖[i.swap] := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, ⟨q, hq, b, hb, rfl⟩, rfl⟩
    have hab : Commute b a := mem_centralizer_iff.mp (mem_inf.mp ha).2 b hb
    have hqF : a * q * a⁻¹ ∈ 𝐅 := conj_M_mem_F h i hne hbot (mem_inf.mp ha).1 (W_le_F _ hq)
    have e : (MulAut.conj a).toMonoidHom (q⁻¹ * (b * q * b⁻¹)) =
        (a * q * a⁻¹)⁻¹ * (b * (a * q * a⁻¹) * b⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc a * (q⁻¹ * (b * q * b⁻¹)) * a⁻¹ = a * q⁻¹ * a⁻¹ * ((a * b) * q * (b⁻¹ * a⁻¹)) := by
            group
        _ = a * q⁻¹ * a⁻¹ * ((b * a) * q * (a⁻¹ * b⁻¹)) := by
            rw [hab.eq.symm, show b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ by
              rw [← mul_inv_rev, ← mul_inv_rev, hab.eq]]
        _ = (a * q * a⁻¹)⁻¹ * (b * (a * q * a⁻¹) * b⁻¹) := by group
    rw [e]
    exact inv_mul_conj_mem_W_swap h i hqF hb
  exact hle ⟨w, W_swap_le_closure h i hw, rfl⟩

theorem V_inf_centralizer_swap (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐕[i, i] ⊓ centralizer (𝐉[i.swap] : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨hxM, hxJ⟩, hxJ'⟩
  obtain ⟨j₀, hj₀⟩ := exists_goodTorus h
  have hc := mem_centralizer_iff.mp (mem_centralizer_J0 i hxJ hxJ') j₀ hj₀.mem
  refine (mem_bot).mpr (eq_one_of_mem_M_of_fix h i hne hbot hj₀ hxM ?_)
  rw [mul_assoc, ← hc, inv_mul_cancel_left]

theorem V_le_closure (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐕[i, i] ≤ closure {y : G | ∃ q ∈ 𝐕[i, i], ∃ c ∈ 𝐉[i.swap], y = q⁻¹ * (c * q * c⁻¹)} := by
  intro a ha
  have hJV : 𝐉[i.swap] ≤ normalizer (𝐕[i, i] : Set G) := fun c hc =>
    mem_normalizer_of_conj_le fun _ hx => conj_mem_inf_centralizer
      (J_le_normalizer_M h i hne hbot (axisTorus_le_J0 _ hc))
      (fun b hb => torus_comm (axisTorus_le_J0 _ hb) (axisTorus_le_J0 _ hc)) hx
  obtain ⟨d, hd, c, hc, rfl⟩ := exists_mul_of_coprime Nat.prime_two hJV
    ((isPGroup_M h i hne hbot).to_le inf_le_left) (not_two_dvd_card_J h i.swap) ha
  have hc1 : c = 1 := by
    have := hc
    rwa [V_inf_centralizer_swap h i hne hbot, mem_bot] at this
  rw [hc1, mul_one]
  exact hd

theorem V_comm_W_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {a : G} (ha : a ∈ 𝐕[i, i]) {w : G}
    (hw : w ∈ 𝐖[i.swap]) : a * w = w * a := by
  have hle : closure {y : G | ∃ q ∈ 𝐕[i, i], ∃ c ∈ 𝐉[i.swap], y = q⁻¹ * (c * q * c⁻¹)} ≤
      centralizer (𝐖[i.swap] : Set G) := by
    rw [closure_le]
    rintro _ ⟨q, hq, c, hc, rfl⟩
    refine mem_centralizer_iff.mpr fun v hv => ?_
    have hcv : Commute c v := mem_centralizer_iff.mp (mem_inf.mp hv).2 c hc
    have hqv : q * v * q⁻¹ ∈ 𝐖[i.swap] := conj_V_mem_W_swap h i hne hbot hq hv
    have hcqv : Commute c (q * v * q⁻¹) := mem_centralizer_iff.mp (mem_inf.mp hqv).2 c hc
    have e1 : c * q * c⁻¹ * v * (c * q * c⁻¹)⁻¹ = q * v * q⁻¹ := by
      calc c * q * c⁻¹ * v * (c * q * c⁻¹)⁻¹ = c * q * (c⁻¹ * v * c) * q⁻¹ * c⁻¹ := by group
        _ = c * (q * v * q⁻¹) * c⁻¹ := by
            rw [show c⁻¹ * v * c = v by rw [mul_assoc, ← hcv.eq, inv_mul_cancel_left]]
            group
        _ = q * v * q⁻¹ := by rw [hcqv.eq, mul_inv_cancel_right]
    calc v * (q⁻¹ * (c * q * c⁻¹)) = q⁻¹ * (q * v * q⁻¹) * (c * q * c⁻¹) := by group
      _ = q⁻¹ * (c * q * c⁻¹ * v * (c * q * c⁻¹)⁻¹) * (c * q * c⁻¹) := by rw [e1]
      _ = q⁻¹ * (c * q * c⁻¹) * v := by group
  exact (mem_centralizer_iff.mp (hle (V_le_closure h i hne hbot ha)) w hw).symm

theorem V_inf_W_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐕[i, i] ⊓ 𝐖[i.swap] = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ 𝐖[i] ⊓ 𝐖[i.swap] := ⟨(V_inf_F h i hne hbot i).le ⟨hx.1, hx.2.1⟩, hx.2⟩
  rwa [W_inf_W_swap_eq h i] at h1

theorem V_sup_W_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐕[i, i] ⊔ 𝐖[i.swap] = 𝐌₀[i] := by
  refine le_antisymm (sup_le inf_le_left (W_le_M h i hne hbot _)) fun x hx => ?_
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_V_mul_W h i hne hbot hx
  exact mul_mem (mem_sup_left ha) (mem_sup_right hw)

theorem V_swap_eq (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐕[i, i.swap] = 𝐖[i.swap] := by
  refine le_antisymm (fun x hx => ?_) (W_le_V h i hne hbot _)
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_V_mul_W h i hne hbot (mem_inf.mp hx).1
  have ha1 : a = 1 := by
    have h1 : a ∈ 𝐕[i, i] ⊓ centralizer (𝐉[i.swap] : Set G) := by
      refine ⟨ha, mem_centralizer_iff.mpr fun c hc => ?_⟩
      have e1 := mem_centralizer_iff.mp (mem_inf.mp hx).2 c hc
      have e2 := mem_centralizer_iff.mp (mem_inf.mp hw).2 c hc
      calc c * a = c * (a * w) * w⁻¹ := by group
        _ = a * w * c * w⁻¹ := by rw [e1]
        _ = a * (w * c) * w⁻¹ := by group
        _ = a * (c * w) * w⁻¹ := by rw [e2]
        _ = a * c := by group
    rwa [V_inf_centralizer_swap h i hne hbot, mem_bot] at h1
  rw [ha1, one_mul]
  exact hw

theorem card_V (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐕[i, i] = Nat.card K ^ 3 := by
  have h1 := card_sup_of_commute (fun x hx y hy => V_comm_W_swap h i hne hbot hx hy)
    (V_inf_W_swap h i hne hbot)
  rw [V_sup_W_swap h i hne hbot, card_M h i hne hbot, card_W h i.swap] at h1
  have hq : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
  rw [show Nat.card K ^ 5 = Nat.card K ^ 3 * Nat.card K ^ 2 by ring] at h1
  exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

theorem closure_sq_V_le (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    closure {x : G | ∃ y ∈ 𝐕[i, i], x = y * y} ≤ 𝐖[i] := by
  rw [closure_le]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨sq_P₀_mem_F h i hne hbot (M_le_P₀ h i (mem_inf.mp hy).1),
    mul_mem (mem_inf.mp hy).2 (mem_inf.mp hy).2⟩

theorem t_mem_normalizer_V (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : t ∈ normalizer (𝐕[i, k] : Set G) :=
  mem_normalizer_of_conj_le fun _ hx => conj_mem_inf_centralizer
    (t_mem_normalizer_M h i hne hbot) (fun _ hb => (h.twoCore.comm (pull_le φ _ hb)).symm) hx

theorem J_le_normalizer_V (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐉 ≤ normalizer (𝐕[i, k] : Set G) :=
  fun _ hj => mem_normalizer_of_conj_le fun _ hx => conj_mem_inf_centralizer
    (J_le_normalizer_M h i hne hbot hj) (fun _ hb => torus_comm (axisTorus_le_J0 k hb) hj) hx

omit [Finite G] [Finite K] in
theorem exists_U_mul_U (i : Axis) {z : G} (hz : z ∈ 𝐙) :
    ∃ u ∈ 𝐔[i], ∃ v ∈ 𝐔[i.swap], z = u * v := by
  obtain ⟨b, c, rfl⟩ := exists_zc hz
  have e : zc φ b c = zc φ b 0 * zc φ 0 c := by rw [zc_mul, add_zero, zero_add]
  have e' : zc φ b c = zc φ 0 c * zc φ b 0 := by rw [zc_mul, add_zero, zero_add]
  have hU1 : zc φ b 0 ∈ pull φ (rootU K Axis.one) := zc_mem_U_one.mpr rfl
  have hU2 : zc φ 0 c ∈ pull φ (rootU K Axis.two) := zc_mem_U_two.mpr rfl
  cases i
  · exact ⟨_, hU1, _, hU2, e⟩
  · exact ⟨_, hU2, _, hU1, e'⟩

theorem V_inf_C (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐕[i, i] ⊓ 𝐂 = 𝐔[i] := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxC⟩ := mem_inf.mp hx
    have hxZ : x ∈ 𝐙 := (M_inf_C h i hne hbot).le ⟨(mem_inf.mp hxV).1, hxC⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_U_mul_U i hxZ
    have huV : u ∈ 𝐕[i, i] := W_le_V h i hne hbot i (U_le_W h i hu)
    have hvV : v ∈ 𝐕[i, i] := by
      have := mul_mem (inv_mem huV) hxV
      rwa [inv_mul_cancel_left] at this
    have h1 : v ∈ 𝐕[i, i] ⊓ 𝐖[i.swap] := mem_inf.mpr ⟨hvV, U_le_W h i.swap hv⟩
    rw [V_inf_W_swap h i hne hbot, mem_bot] at h1
    rw [h1, mul_one]
    exact hu
  · exact le_inf ((U_le_W h i).trans (W_le_V h i hne hbot i))
      ((pull_le φ _).trans h.setup.L_le)

theorem exists_V_sq_kappa_eq (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {u : G}
    (hu : u ∈ 𝐔[i]) : ∃ a ∈ 𝐕[i, i], (t⁻¹ * (a⁻¹ * t * a)) * (t⁻¹ * (a⁻¹ * t * a)) = u := by
  obtain ⟨j₀, hj₀, χ, hχ, hj₀c, heq⟩ := exists_M_eq_dSub h i hne hbot
  obtain ⟨x, hx, hxu⟩ := exists_dSub_sq_kappa_eq h i hne hbot hj₀ hχ hj₀c hu
  rw [← heq] at hx
  obtain ⟨f, hf, a, ha, rfl⟩ := exists_F_mul_V h i hne hbot hx
  have hfP : f ∈ 𝐏₁[i] := (mem_inf.mp (M_le_P₀ h i (F_le_M h i hne hbot hf))).1
  have haP : a ∈ 𝐏₁[i] := (mem_inf.mp (M_le_P₀ h i (mem_inf.mp ha).1)).1
  have hf1 : (t⁻¹ * (f⁻¹ * t * f)) * (t⁻¹ * (f⁻¹ * t * f)) = 1 :=
    (sq_kappa_eq_one_iff h i hne hbot hfP).mpr ((F_le_E0 h).trans (E0_le_E i) hf)
  refine ⟨a, ha, ?_⟩
  rw [← hxu, sq_kappa_mul h i hne hbot hfP haP, hf1, one_mul]

theorem quotient_V (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    ∃ _ : (𝐖[i].subgroupOf 𝐕[i, i]).Normal,
      ∃ e : (↥𝐕[i, i] ⧸ 𝐖[i].subgroupOf 𝐕[i, i]) ≃* ↥𝐔[i],
        ∀ x : 𝐕[i, i], (e (x : ↥𝐕[i, i] ⧸ 𝐖[i].subgroupOf 𝐕[i, i]) : G) =
          (t⁻¹ * ((x : G)⁻¹ * t * x)) * (t⁻¹ * ((x : G)⁻¹ * t * x)) := by
  have hP : ∀ x ∈ 𝐕[i, i], x ∈ 𝐏₁[i] := fun x hx =>
    (mem_inf.mp (M_le_P₀ h i (mem_inf.mp hx).1)).1
  refine exists_quotient_equiv_of_hom (V := 𝐕[i, i]) (W := 𝐖[i]) (U := 𝐔[i])
    (fun x => (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)))
    (fun x hx => sq_kappa_mem_U h i hne hbot (hP x hx))
    (fun x hx y hy => sq_kappa_mul h i hne hbot (hP x hx) (hP y hy)) (fun x hx => ?_)
    (fun u hu => exists_V_sq_kappa_eq h i hne hbot hu)
  rw [sq_kappa_eq_one_iff h i hne hbot (hP x hx), ← V_inf_F h i hne hbot i]
  constructor
  · intro hxE
    refine mem_inf.mpr ⟨hx, ?_⟩
    rw [← M_inf_E h i hne hbot]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1, hxE⟩
  · intro hxF
    exact (F_le_E0 h).trans (E0_le_E i) (mem_inf.mp hxF).2

end Torus

end RootStandard

end CFSG.LocalAnalysis.SymplecticFourStandard
