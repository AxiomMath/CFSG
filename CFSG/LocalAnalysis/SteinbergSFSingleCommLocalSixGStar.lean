module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGSquares
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFElementary
public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresComplement

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixG

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Irreducible

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
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅ʷ[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐘[" i "," k "]" => (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐑[" k "]" => (normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐃𝐧[" i "]" => normalizer ((𝐃[i] : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐓₁[" i "]" => (𝐑[i] ⊔ 𝐏₁[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀[" j "]" => (𝐑[j] ⊔ 𝐏₂[j] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₂[" j "]" => (𝐓₀[j] ⊓ normalizer (𝐑[j] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₃[" i "]" => (𝐓₁[i] ⊓ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓̄[" i "]" => (𝐓₁[i] ⊔ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)

set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}

theorem comm_A_mem_ZP_of_two_group (h : FCHyp L K n φ t) (k : Axis) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hRA : R ≤ normalizer (𝐀[k] : Set G))
    (hRZ : R ≤ normalizer (𝐙 : Set G)) (hJR : 𝐉 ≤ normalizer (R : Set G)) {x : G}
    (hx : x ∈ R) {a : G} (ha : a ∈ 𝐀[k]) : x * a * x⁻¹ * a⁻¹ ∈ 𝐙 := by
  set H₀ := R ⊔ 𝐉 with hH₀
  have hH₀A : H₀ ≤ normalizer (𝐀[k] : Set G) := sup_le hRA (FCHyp.torus_le_normalizer_A k)
  have hJZ : 𝐉 ≤ normalizer (𝐙 : Set G) := torus_le_normalizer_pull fun δ hδ z hz => by
    obtain ⟨r, s, hr, hs, hδm⟩ := hδ
    obtain ⟨b, c, rfl⟩ := hz
    rw [diagTorus_conj hr hs hδm]
    simp only [mul_zero]
    exact ⟨_, _, rfl⟩
  have hH₀Z : H₀ ≤ normalizer (𝐙 : Set G) := sup_le hRZ hJZ
  have hH₀R : H₀ ≤ normalizer (R : Set G) := sup_le le_normalizer hJR
  have hA : ActHyp (fun g => psiG φ k g 1) 1 𝐀[k] 𝐙 H₀ :=
    { U_le := pull_mono φ (center_le_rootA k)
      add := fun a ha b hb => by
        rw [psiG_mul h.twoCore φ k ha hb, Pi.add_apply]
      ker := fun a ha => psiG_one_eq_zero_iff h k ha
      surj := fun v => by
        obtain ⟨a, ha, hav⟩ := exists_psiG_eq h.twoCore φ k ![0, v]
        exact ⟨a, ha, by simp [hav]⟩
      conj_A := fun g hg a ha => (mem_normalizer_iff.mp (hH₀A hg) a).mp ha
      conj_U := fun g hg z hz => (mem_normalizer_iff.mp (hH₀Z hg) z).mp hz
      conj_t := fun _ _ => by
        rw [inv_one, one_mul, mul_one, mul_inv_cancel]
        exact one_mem _ }
  have h2K : 2 ∣ Nat.card K := by
    rw [h.setup.card_K]
    exact dvd_pow_self 2 (by have := h.setup.two_le; omega)
  have htrans : ∀ v w : K, v ≠ 0 → w ≠ 0 → ∃ g ∈ H₀, hA.linFun g v = w := by
    intro v w hv hw
    obtain ⟨a₀, ha₀, hψ⟩ := hA.surj v
    have hc : w * v⁻¹ ≠ 0 := mul_ne_zero hw (inv_ne_zero hv)
    obtain ⟨r, s, hr, hs, hrs⟩ : ∃ r s : K, r ≠ 0 ∧ s ≠ 0 ∧ radChar k r s = w * v⁻¹ := by
      cases k
      · exact ⟨1, w * v⁻¹, one_ne_zero, hc, rfl⟩
      · exact ⟨w * v⁻¹, 1, hc, one_ne_zero, by simp [radChar]⟩
    obtain ⟨δ, hδD, hδ⟩ := exists_diagTorus hr hs
    have hτ : ((φ.symm δ : L) : G) ∈ 𝐉 := symm_mem_pull.mpr hδD
    refine ⟨((φ.symm δ : L) : G)⁻¹, mem_sup_right (inv_mem hτ), ?_⟩
    rw [← hψ, hA.linFun_psi (mem_sup_right (inv_mem hτ)) ha₀]
    simp only [inv_inv]
    rw [psiG_conj_torus h k hr hs hδ ha₀, hrs, hψ, mul_assoc, inv_mul_cancel₀ hv, mul_one]
  have hfix := hA.linFun_eq_of_normal le_rfl (le_sup_left : R ≤ H₀)
    (fun g hg r hr => (mem_normalizer_iff.mp (hH₀R hg) r).mp hr) hR2 h2K htrans hx
    (psiG φ k a 1)
  rw [hA.linFun_psi (mem_sup_left hx) ha] at hfix
  have hxa : x * a * x⁻¹ ∈ 𝐀[k] := (mem_normalizer_iff.mp (hRA hx) a).mp ha
  have h1 := (hA.ker _ (mul_mem hxa (inv_mem ha))).mp (by
    rw [psiG_mul h.twoCore φ k hxa (inv_mem ha), Pi.add_apply, psiG_inv h.twoCore φ k ha,
      Pi.neg_apply, hfix, add_neg_cancel])
  exact h1

theorem comm_K_mem_A_of_two_group (h : FCHyp L K n φ t) (k : Axis) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hRK : R ≤ normalizer (𝐊[k] : Set G))
    (hRA : R ≤ normalizer (𝐀[k] : Set G)) (hJR : 𝐉 ≤ normalizer (R : Set G)) {x : G}
    (hx : x ∈ R) {y : G} (hy : y ∈ 𝐊[k]) : y⁻¹ * (x * y * x⁻¹) ∈ 𝐀[k] := by
  set H₀ := R ⊔ 𝐉 with hH₀
  have hJK : 𝐉 ≤ normalizer (𝐊[k] : Set G) := fun j hj =>
    mem_normalizer_of_conj_le fun y hy => conj_torus_mem_K h k hj hy
  have hH₀K : H₀ ≤ normalizer (𝐊[k] : Set G) := sup_le hRK hJK
  have hH₀A : H₀ ≤ normalizer (𝐀[k] : Set G) := sup_le hRA (FCHyp.torus_le_normalizer_A k)
  have hH₀R : H₀ ≤ normalizer (R : Set G) := sup_le le_normalizer hJR
  have hA : ActHyp (psiK φ t k) 1 𝐊[k] 𝐀[k] H₀ :=
    { U_le := le_sup_left
      add := fun a ha b hb => psiK_mul h k ha hb
      ker := fun a ha => psiK_eq_zero_iff h k ha
      surj := fun v => exists_psiK_eq h k v
      conj_A := fun g hg a ha => (mem_normalizer_iff.mp (hH₀K hg) a).mp ha
      conj_U := fun g hg z hz => (mem_normalizer_iff.mp (hH₀A hg) z).mp hz
      conj_t := fun _ _ => by
        rw [inv_one, one_mul, mul_one, mul_inv_cancel]
        exact one_mem _ }
  have h2K : 2 ∣ Nat.card K := by
    rw [h.setup.card_K]
    exact dvd_pow_self 2 (by have := h.setup.two_le; omega)
  have htrans : ∀ v w : K, v ≠ 0 → w ≠ 0 → ∃ g ∈ H₀, hA.linFun g v = w := by
    intro v w hv hw
    obtain ⟨k₀, hk₀, hk₀v⟩ := hA.surj v
    obtain ⟨m, hm, hmw⟩ := hA.surj w
    have hk₀A : k₀ ∉ 𝐀[k] := fun hA' => hv (hk₀v ▸ (hA.ker k₀ hk₀).mpr hA')
    have hmA : m ∉ 𝐀[k] := fun hA' => hw (hmw ▸ (hA.ker m hm).mpr hA')
    obtain ⟨j, hj, hjm⟩ := exists_torus_K h k hk₀ hk₀A hm hmA
    refine ⟨j, mem_sup_right hj, ?_⟩
    rw [← hk₀v, hA.linFun_psi (mem_sup_right hj) hk₀, ← hmw]
    have hjk : j * k₀ * j⁻¹ ∈ 𝐊[k] := conj_torus_mem_K h k hj hk₀
    exact (hA.psi_eq_iff hjk hm).mpr hjm
  have hfix := hA.linFun_eq_of_normal le_rfl (le_sup_left : R ≤ H₀)
    (fun g hg r hr => (mem_normalizer_iff.mp (hH₀R hg) r).mp hr) hR2 h2K htrans hx
    (psiK φ t k y)
  rw [hA.linFun_psi (mem_sup_left hx) hy] at hfix
  have hxy : x * y * x⁻¹ ∈ 𝐊[k] := (mem_normalizer_iff.mp (hRK hx) y).mp hy
  exact (hA.psi_eq_iff hy hxy).mp hfix.symm

omit [Finite G] [CharP K 2] [Finite K] in
theorem comm_mem_sup {X Y Z : Subgroup G} {x : G} (hZ : X ⊔ Y ≤ normalizer (Z : Set G))
    (hX : ∀ a ∈ X, x * a * x⁻¹ * a⁻¹ ∈ Z) (hY : ∀ b ∈ Y, x * b * x⁻¹ * b⁻¹ ∈ Z) :
    ∀ y ∈ X ⊔ Y, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ X ⊔ Y ∧ x * y * x⁻¹ * y⁻¹ ∈ Z}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, ?_⟩
        have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha.2 ((mem_normalizer_iff.mp (hZ ha.1) _).mp hb.2)
      one_mem' := ⟨(X ⊔ Y).one_mem, by
        rw [mul_one, mul_inv_cancel, one_mul, inv_one]; exact Z.one_mem⟩
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, ?_⟩
        have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (mem_normalizer_iff.mp (hZ (inv_mem ha.1)) _).mp (inv_mem ha.2) }
  have hle : X ⊔ Y ≤ S := sup_le (fun a ha => ⟨mem_sup_left ha, hX a ha⟩)
    (fun b hb => ⟨mem_sup_right hb, hY b hb⟩)
  exact fun y hy => (hle hy).2

theorem isPGroup_T₃ (h : FCHyp L K n φ t) (i : Axis) : IsPGroup 2 𝐓₃[i] :=
  (isPGroup_T₁ h i).to_le inf_le_left

theorem T₃_le_Nhat (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₃[i] ≤ 𝐍ₕ[i] :=
  inf_le_left.trans (T₁_le_Nhat h i hne hbot)

theorem J_le_normalizer_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ normalizer (𝐓₃[i] : Set G) := fun _ hj =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_T₃ h i hne hbot (J_le_Nhat h i hne hbot hj) hx

theorem le_normalizer_A_of_E (h : FCHyp L K n φ t) (k : Axis) {X : Subgroup G}
    (hX : X ≤ normalizer (𝐄[k] : Set G)) : X ≤ normalizer (𝐀[k] : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun a ha => ?_
  rw [← closure_sq_E h k] at ha ⊢
  have hle : (closure {x : G | ∃ y ∈ 𝐄[k], x = y * y}).map (MulAut.conj g).toMonoidHom ≤
      closure {x : G | ∃ y ∈ 𝐄[k], x = y * y} := by
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, (mem_normalizer_iff.mp (hX hg) y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle ⟨a, ha, rfl⟩

theorem le_normalizer_ZP_of_H (h : FCHyp L K n φ t) {X : Subgroup G}
    (hX : X ≤ normalizer (𝐇 : Set G)) : X ≤ normalizer (𝐙 : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun z hz => ?_
  rw [← closure_sq_H h] at hz ⊢
  have hle : (closure {x : G | ∃ y ∈ 𝐇, x = y * y}).map (MulAut.conj g).toMonoidHom ≤
      closure {x : G | ∃ y ∈ 𝐇, x = y * y} := by
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, (mem_normalizer_iff.mp (hX hg) y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle ⟨z, hz, rfl⟩

theorem T₃_le_normalizer_A (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐓₃[i] ≤ normalizer (𝐀[k] : Set G) := by
  rcases SingleComm.eq_or_eq_swap i k with rfl | rfl
  · exact (inf_le_left.trans (T₁_le_Dn h k)).trans (normalizer_D_le_normalizer_A h k)
  · exact le_normalizer_A_of_E h _ (inf_le_right.trans (inf_le_left.trans
      ((T₀_le_En h _).trans inf_le_left)))

theorem T₃_le_normalizer_K (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐓₃[i] ≤ normalizer (𝐊[k] : Set G) := by
  rcases SingleComm.eq_or_eq_swap i k with rfl | rfl
  · exact fun g hg => mem_normalizer_of_conj_le fun x hx =>
      conj_mem_K_of_normalizer_D h k (T₁_le_Dn h k (mem_inf.mp hg).1) hx
  · exact (T₃_le_Nhat h i hne hbot).trans
      (Nhat_le_normalizer_K_swap h i hne hbot (W_sq_eq' h i hne hbot) one_ne_zero)

theorem T₃_le_normalizer_ZP (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓₃[i] ≤ normalizer (𝐙 : Set G) :=
  le_normalizer_ZP_of_H h fun _ hg => (mem_inf.mp (T₃_le_Nhat h i hne hbot hg)).1

theorem comm_T₃_A (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) {x : G} (hx : x ∈ 𝐓₃[i]) {a : G}
    (ha : a ∈ 𝐀[k]) : x * a * x⁻¹ * a⁻¹ ∈ 𝐙 :=
  comm_A_mem_ZP_of_two_group h k (isPGroup_T₃ h i) (T₃_le_normalizer_A h i hne hbot k)
    (T₃_le_normalizer_ZP h i hne hbot) (J_le_normalizer_T₃ h i hne hbot) hx ha

theorem comm_T₃_F (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) {x : G} (hx : x ∈ 𝐓₃[i]) {f : G}
    (hf : f ∈ 𝐅 ⊓ 𝐃[k]) : x * f * x⁻¹ * f⁻¹ ∈ 𝐙 := by
  have hfK : f ∈ 𝐊[k] := mem_sup_right hf
  have h1 := comm_K_mem_A_of_two_group h k (isPGroup_T₃ h i) (T₃_le_normalizer_K h i hne hbot k)
    (T₃_le_normalizer_A h i hne hbot k) (J_le_normalizer_T₃ h i hne hbot) hx hfK
  have hxf : x * f * x⁻¹ ∈ 𝐅 :=
    (mem_normalizer_iff.mp (Nhat_le_normalizer_F h i hbot (T₃_le_Nhat h i hne hbot hx)) f).mp
      (mem_inf.mp hf).1
  have h2 : f⁻¹ * (x * f * x⁻¹) ∈ 𝐙 := by
    rw [← A_inf_F h k]
    exact mem_inf.mpr ⟨h1, mul_mem (inv_mem (mem_inf.mp hf).1) hxf⟩
  have e : x * f * x⁻¹ * f⁻¹ = f * (f⁻¹ * (x * f * x⁻¹)) * f⁻¹ := by group
  rw [e, F_comm h (mem_inf.mp hf).1 (ZP_le_F h h2), mul_inv_cancel_right]
  exact h2

theorem comm_T₃_Ks (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐓₃[i]) {y : G} (hy : y ∈ 𝐊⋆) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝐙 := by
  have hKZ : 𝐊⋆ ≤ normalizer (𝐙 : Set G) := le_normalizer_ZP_of_H h fun _ hg =>
    mem_normalizer_of_conj_le fun _ hz => mul_mem (mul_mem (Ks_le_H h hg) hz)
      (inv_mem (Ks_le_H h hg))
  have hK : ∀ k : Axis, ∀ z ∈ 𝐊[k], x * z * x⁻¹ * z⁻¹ ∈ 𝐙 := fun k =>
    comm_mem_sup ((K_le_Ks h k).trans hKZ) (fun a ha => comm_T₃_A h i hne hbot k hx ha)
      (fun f hf => comm_T₃_F h i hne hbot k hx hf)
  exact comm_mem_sup hKZ (hK _) (hK _) y hy

set_option quotPrecheck false in
local notation "𝐁⋆[" i "]" => (𝐌₀[i] ⊔ 𝐊⋆ : Subgroup G)

theorem M_le_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ≤ 𝐓₃[i] :=
  (M_le_P₀ h i).trans (P₀_le_T₃ h i hne hbot)

theorem M_le_normalizer_Ks (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ≤ normalizer (𝐊⋆ : Set G) :=
  ((M_le_T₃ h i hne hbot).trans (T₃_le_Nhat h i hne hbot)).trans (Nhat_le_normalizer_Ks h i hbot)

theorem M_inf_H (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐇 = 𝐅 := by
  refine le_antisymm (fun x hx => ?_) (le_inf (F_le_M h i hne hbot) ((F_le_Ks h).trans (Ks_le_H h)))
  have hxP : x ∈ 𝐏₁[i] ⊓ 𝐇 := mem_inf.mpr ⟨(mem_inf.mp (M_le_P₀ h i hx.1)).1, hx.2⟩
  rw [P₁_inf_H h i hne hbot] at hxP
  rw [← M_inf_E h i hne hbot]
  exact mem_inf.mpr ⟨hx.1, hxP.2⟩

theorem M_inf_Ks (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐌₀[i] ⊓ 𝐊⋆ = 𝐅 :=
  le_antisymm (fun _ hx => M_inf_H h i hne hbot ▸ mem_inf.mpr ⟨hx.1, Ks_le_H h hx.2⟩)
    (le_inf (F_le_M h i hne hbot) (F_le_Ks h))

theorem card_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : Nat.card 𝐁⋆[i] = Nat.card K ^ 7 := by
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐊⋆) (B := 𝐌₀[i]) (M_le_normalizer_Ks h i hne hbot)
  rw [sup_comm 𝐊⋆ 𝐌₀[i], inf_comm 𝐊⋆ 𝐌₀[i], M_inf_Ks h i hne hbot, card_Ks h,
    card_M h i hne hbot, card_F h] at h1
  have hq : 0 < Nat.card K ^ 4 := pow_pos Nat.card_pos 4
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem mem_Bstar_iff (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} :
    x ∈ 𝐁⋆[i] ↔ ∃ m ∈ 𝐌₀[i], ∃ k ∈ 𝐊⋆, m * k = x := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ (M_le_normalizer_Ks h i hne hbot),
    Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem Bstar_le_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐁⋆[i] ≤ 𝐓₃[i] :=
  sup_le (M_le_T₃ h i hne hbot) ((Ks_le_H h).trans (H_le_T₃ h i))

theorem Bstar_inf_H (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐁⋆[i] ⊓ 𝐇 = 𝐊⋆ := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right (Ks_le_H h))
  obtain ⟨m, hm, k, hk, rfl⟩ := (mem_Bstar_iff h i hne hbot).mp hx.1
  have hmH : m ∈ 𝐇 := by
    have := mul_mem (mem_inf.mp hx).2 (inv_mem (Ks_le_H h hk))
    rwa [mul_inv_cancel_right] at this
  have hmF : m ∈ 𝐅 := M_inf_H h i hne hbot ▸ mem_inf.mpr ⟨hm, hmH⟩
  exact mul_mem (F_le_Ks h hmF) hk

theorem t_not_mem_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : t ∉ 𝐁⋆[i] := fun ht => by
  have htH : t ∈ 𝐇 := by
    rw [← (Ks_sup_t h).2]
    exact mem_sup_right (mem_zpowers t)
  have h1 : t ∈ 𝐁⋆[i] ⊓ 𝐇 := mem_inf.mpr ⟨ht, htH⟩
  rw [Bstar_inf_H h i hne hbot] at h1
  exact t_not_mem_Ks h h1

theorem t_mem_normalizer_Bstar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    t ∈ normalizer (𝐁⋆[i] : Set G) := by
  have htH : t ∈ 𝐇 := by
    rw [← (Ks_sup_t h).2]
    exact mem_sup_right (mem_zpowers t)
  have htK : t ∈ normalizer (𝐊⋆ : Set G) := mem_normalizer_of_conj_le fun _ hk =>
    conj_H_mem_Ks h htH hk
  exact mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hy => (mem_normalizer_iff.mp (t_mem_normalizer_M h i hne hbot) _).mp hy)
    (fun _ hy => (mem_normalizer_iff.mp htK _).mp hy) hx

theorem Bstar_sup_t (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐁⋆[i] ⊔ zpowers t = 𝐓₃[i] ∧ 𝐁⋆[i] ⊓ zpowers t = ⊥ := by
  have htt : t * t = 1 := SixF.t_mul_t h
  have hinf : 𝐁⋆[i] ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx.2
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_zero]
      exact one_mem _
    · exfalso
      have := hx.1
      rw [← zpow_mod_orderOf, h.setup.order_t, Nat.cast_ofNat, hk, zpow_one] at this
      exact t_not_mem_Bstar h i hne hbot this
  refine ⟨?_, hinf⟩
  have hle : 𝐁⋆[i] ⊔ zpowers t ≤ 𝐓₃[i] :=
    sup_le (Bstar_le_T₃ h i hne hbot) ((zpowers_le).2 (H_le_T₃ h i (by
      rw [← (Ks_sup_t h).2]
      exact mem_sup_right (mem_zpowers t))))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := 𝐁⋆[i]) (B := zpowers t) ((zpowers_le).2 (t_mem_normalizer_Bstar h i hne hbot))
  rw [hinf, card_bot, mul_one, card_Bstar h i hne hbot, Nat.card_zpowers, h.setup.order_t] at h1
  rw [card_T₃ h i hne hbot, h1, mul_comm]

omit [Finite G] [CharP K 2] [Finite K] in
theorem comm_mem_of_sq {X Z : Subgroup G} (hX : ∀ a ∈ X, a * a ∈ Z) {a b : G} (ha : a ∈ X)
    (hb : b ∈ X) : a * b * a⁻¹ * b⁻¹ ∈ Z := by
  have e : a * b * a⁻¹ * b⁻¹ =
      ((a * b) * (a * b)) * ((b⁻¹ * a⁻¹ * b) * (b⁻¹ * a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem (hX _ (mul_mem ha hb))
    (hX _ (mul_mem (mul_mem (inv_mem hb) (inv_mem ha)) hb))) (hX _ (inv_mem hb))

omit [Finite G] [CharP K 2] [Finite K] in
theorem comm_sup_of_comm {X Y Z : Subgroup G} (hZ : X ⊔ Y ≤ normalizer (Z : Set G))
    (hXX : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hYY : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Z) {x y : G} (hx : x ∈ X ⊔ Y)
    (hy : y ∈ X ⊔ Y) : x * y * x⁻¹ * y⁻¹ ∈ Z := by
  have hinv : ∀ {a b : G}, a * b * a⁻¹ * b⁻¹ ∈ Z → b * a * b⁻¹ * a⁻¹ ∈ Z := fun {a b} hab => by
    have := inv_mem hab
    rwa [show (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ by group] at this
  have h1 : ∀ z ∈ X, ∀ w ∈ X ⊔ Y, z * w * z⁻¹ * w⁻¹ ∈ Z := fun z hz =>
    comm_mem_sup hZ (fun a ha => hXX z hz a ha) (fun b hb => hXY z hz b hb)
  have h2 : ∀ z ∈ Y, ∀ w ∈ X ⊔ Y, z * w * z⁻¹ * w⁻¹ ∈ Z := fun z hz =>
    comm_mem_sup hZ (fun a ha => hinv (hXY a ha z hz)) (fun b hb => hYY z hz b hb)
  exact comm_mem_sup hZ (fun a ha => hinv (h1 a ha x hx)) (fun b hb => hinv (h2 b hb x hx)) y hy

theorem comm_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {x y : G}
    (hx : x ∈ 𝐁⋆[i]) (hy : y ∈ 𝐁⋆[i]) : x * y * x⁻¹ * y⁻¹ ∈ 𝐙 := by
  have hUZ : 𝐔[i] ≤ 𝐙 := pull_mono φ (rootU_le_center i)
  have hHsq : ∀ a ∈ 𝐇, a * a ∈ 𝐙 := fun a ha => by
    rw [← closure_sq_H h]
    exact subset_closure ⟨a, ha, rfl⟩
  exact comm_sup_of_comm ((Bstar_le_T₃ h i hne hbot).trans (T₃_le_normalizer_ZP h i hne hbot))
    (fun a ha b hb => comm_mem_of_sq (fun c hc => hUZ (hM2 c hc)) ha hb)
    (fun a ha b hb => comm_T₃_Ks h i hne hbot (M_le_T₃ h i hne hbot ha) hb)
    (fun a ha b hb => comm_mem_of_sq hHsq (Ks_le_H h ha) (Ks_le_H h hb)) hx hy

theorem sq_Bstar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {x : G}
    (hx : x ∈ 𝐁⋆[i]) : x * x ∈ 𝐙 := by
  obtain ⟨m, hm, k, hk, rfl⟩ := (mem_Bstar_iff h i hne hbot).mp hx
  have hUZ : 𝐔[i] ≤ 𝐙 := pull_mono φ (rootU_le_center i)
  have hkk : k * k ∈ 𝐙 := by
    rw [← closure_sq_H h]
    exact subset_closure ⟨k, Ks_le_H h hk, rfl⟩
  have hc : k * m * k⁻¹ * m⁻¹ ∈ 𝐙 := by
    have := inv_mem (comm_T₃_Ks h i hne hbot (M_le_T₃ h i hne hbot hm) hk)
    rwa [show (m * k * m⁻¹ * k⁻¹)⁻¹ = k * m * k⁻¹ * m⁻¹ by group] at this
  have hmZ : m ∈ normalizer (𝐙 : Set G) :=
    T₃_le_normalizer_ZP h i hne hbot (M_le_T₃ h i hne hbot hm)
  have e : m * k * (m * k) = (m * (k * m * k⁻¹ * m⁻¹) * m⁻¹) * (m * m) * (k * k) := by group
  rw [e]
  exact mul_mem (mul_mem ((mem_normalizer_iff.mp hmZ _).mp hc) (hUZ (hM2 m hm))) hkk

end Irreducible

end SixG

end CFSG.LocalAnalysis.SymplecticFourStandard
