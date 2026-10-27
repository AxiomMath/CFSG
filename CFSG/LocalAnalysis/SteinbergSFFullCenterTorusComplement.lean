module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplementBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterTorus

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Square

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
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
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
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

omit [Finite G] [Finite K] in
theorem exists_coordEquiv (i : Axis) :
    ∃ ι : Multiplicative K ≃* ↥𝐔[i], ∀ x : K, (ι (Multiplicative.ofAdd x) : G) = coordG φ i x := by
  let f : Multiplicative K →* ↥𝐔[i] :=
    { toFun := fun x => ⟨coordG φ i (Multiplicative.toAdd x), coordG_mem φ i _⟩
      map_one' := Subtype.ext (coordG_zero φ i)
      map_mul' := fun x y => Subtype.ext (by
        change coordG φ i (Multiplicative.toAdd x + Multiplicative.toAdd y) = _
        rw [coordG_add]
        rfl) }
  have hbij : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun u => ?_⟩
    · have h1 := congrArg (fun u : ↥𝐔[i] => (u : G)) hxy
      exact Multiplicative.toAdd.injective (coordG_injective φ i h1)
    · obtain ⟨x, hx⟩ := exists_coordG_eq φ i u.2
      exact ⟨Multiplicative.ofAdd x, Subtype.ext hx⟩
  exact ⟨MulEquiv.ofBijective f hbij, fun x => rfl⟩

omit [Finite G] in
theorem exists_axisTorusHom (h : FCHyp L K n φ t) (i : Axis) :
    ∃ τ : Kˣ →* G, ∀ l : Kˣ, τ l ∈ 𝐉[i.swap] ∧
      ∀ a : K, (τ l)⁻¹ * coordG φ i a * τ l = coordG φ i (l * a) := by
  cases i
  · obtain ⟨τX, hτX⟩ := exists_diagHom (K := K) 1 (MonoidHom.id Kˣ)
    have hδ : ∀ l : Kˣ, glMat (τX l : GL (Fin 4) K) = diagMat 1 (l : K) := fun l => by
      rw [hτX]
      simp
    refine ⟨(L.subtype.comp φ.symm.toMonoidHom).comp τX, fun l => ⟨?_, fun a => ?_⟩⟩
    · exact symm_mem_pull.mpr ⟨l, l.ne_zero, hδ l⟩
    · change ((φ.symm (τX l) : L) : G)⁻¹ * coordG φ Axis.one a * ((φ.symm (τX l) : L) : G) = _
      rw [coordG_one_eq, conj_zc one_ne_zero l.ne_zero (hδ l), coordG_one_eq, one_pow, mul_zero,
        one_mul]
  · have hn : 1 ≤ n := by have := h.setup.two_le; omega
    have hsq : ∀ x : K, (x ^ 2 ^ (n - 1)) ^ 2 = x := by
      intro x
      have := Fintype.ofFinite K
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, ← h.setup.card_K, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card x
    obtain ⟨τX, hτX⟩ := exists_diagHom (K := K) (powMonoidHom (2 ^ (n - 1)))
      (invMonoidHom.comp (powMonoidHom (2 ^ (n - 1))))
    have hδ : ∀ l : Kˣ, glMat (τX l : GL (Fin 4) K) =
        diagMat ((l : K) ^ 2 ^ (n - 1)) ((l : K) ^ 2 ^ (n - 1))⁻¹ := fun l => by
      rw [hτX]
      simp
    have hr : ∀ l : Kˣ, (l : K) ^ 2 ^ (n - 1) ≠ 0 := fun l => pow_ne_zero _ l.ne_zero
    refine ⟨(L.subtype.comp φ.symm.toMonoidHom).comp τX, fun l => ⟨?_, fun a => ?_⟩⟩
    · exact symm_mem_pull.mpr ⟨_, hr l, hδ l⟩
    · change ((φ.symm (τX l) : L) : G)⁻¹ * coordG φ Axis.two a * ((φ.symm (τX l) : L) : G) = _
      rw [coordG_two_eq, conj_zc (hr l) (inv_ne_zero (hr l)) (hδ l), coordG_two_eq,
        mul_inv_cancel₀ (hr l), one_mul, hsq]

theorem square_map (h : FCHyp L K n φ t) (i : Axis) :
    (∀ x ∈ 𝐖[i], ∀ y ∈ 𝐖[i], x * y = y * x) ∧
    ∃ lam : K, (∀ w ∈ 𝐖[i], ∀ a : K, t⁻¹ * (w⁻¹ * t * w) = coordG φ i a →
        w * w = coordG φ i (lam * a)) ∧
      (∀ lam' : K, (∀ w ∈ 𝐖[i], ∀ a : K, t⁻¹ * (w⁻¹ * t * w) = coordG φ i a →
        w * w = coordG φ i (lam' * a)) → lam' = lam) ∧
      (lam = 0 → IsElementaryAbelian 2 𝐖[i] ∧ Group.rank 𝐖[i] = 2 * n) ∧
      (lam ≠ 0 → closure {x : G | ∃ y ∈ 𝐖[i], x = y * y} = 𝐔[i] ∧
        closure {x : G | x ∈ 𝐖[i] ∧ x * x = 1} = 𝐔[i] ∧
        {x : G | x ∈ 𝐖[i] ∧ x * x = 1} = 𝐔[i] ∧
        Nonempty (Multiplicative (Fin n → ZMod 4) ≃* 𝐖[i])) := by
  obtain ⟨hn, θq, hθq, -⟩ := quotient_W h i
  obtain ⟨ι, hι⟩ := exists_coordEquiv (φ := φ) i
  obtain ⟨τ, hτ⟩ := exists_axisTorusHom h i
  have hτJ : ∀ l, τ l ∈ 𝐉 := fun l => axisTorus_le_J0 _ (hτ l).1
  have hcoord : ∀ (u : ↥𝐔[i]) (c : K),
      Multiplicative.toAdd (ι.symm u) = c ↔ (u : G) = coordG φ i c := by
    intro u c
    rw [← hι c, Subtype.coe_inj, ← MulEquiv.symm_apply_eq]
    exact ⟨fun e => by rw [← e]; rfl, fun e => by rw [e]; rfl⟩
  let A' : Subgroup ↥𝐖[i] := 𝐔[i].subgroupOf 𝐖[i]
  have : A'.Normal := hn
  have hAZ : A' ≤ center ↥𝐖[i] := fun a ha => mem_center_iff.mpr fun g => Subtype.ext
    (comm_ZP h (F_le_H h (W_le_F i g.2)) (pull_mono φ (rootU_le_center i) (mem_subgroupOf.mp ha)))
  let α : A' ≃* Multiplicative K := (subgroupOfEquivOfLe (U_le_W h i)).trans ι.symm
  let β : (↥𝐖[i] ⧸ A') ≃* Multiplicative K := θq.trans ι.symm
  have hαc : ∀ (a : A') (c : K), Multiplicative.toAdd (α a) = c ↔
      ((a : ↥𝐖[i]) : G) = coordG φ i c := fun a c => hcoord _ c
  have hβc : ∀ (w : ↥𝐖[i]) (c : K), Multiplicative.toAdd (β w) = c ↔
      t⁻¹ * ((w : G)⁻¹ * t * w) = coordG φ i c := fun w c => by
    rw [← hθq w]
    exact hcoord _ c
  let θ' : Kˣ →* MulAut ↥𝐖[i] :=
    { toFun := fun l =>
        { toFun := fun w => ⟨(τ l)⁻¹ * w * τ l, conj_torus_mem_W h i (hτJ l) w.2⟩
          invFun := fun w => ⟨τ l * w * (τ l)⁻¹, by
            simpa using conj_torus_mem_W h i (inv_mem (hτJ l)) w.2⟩
          left_inv := fun w => Subtype.ext (by simp only; group)
          right_inv := fun w => Subtype.ext (by simp only; group)
          map_mul' := fun w w' => Subtype.ext (by simp only [coe_mul]; group) }
      map_one' := MulEquiv.ext fun w => Subtype.ext (by simp)
      map_mul' := fun l l' => MulEquiv.ext fun w => Subtype.ext (by
        change (τ (l * l'))⁻¹ * w * τ (l * l') = (τ l)⁻¹ * ((τ l')⁻¹ * w * τ l') * τ l
        rw [map_mul, torus_comm (hτJ l) (hτJ l')]
        group) }
  have hθ' : ∀ (l : Kˣ) (w : ↥𝐖[i]), ((θ' l w : ↥𝐖[i]) : G) = (τ l)⁻¹ * w * τ l :=
    fun _ _ => rfl
  have hα : ∀ (l : Kˣ) (a a' : A'), (a' : ↥𝐖[i]) = θ' l a →
      Multiplicative.toAdd (α a') = l * Multiplicative.toAdd (α a) := by
    intro l a a' ha'
    rw [hαc, ha', hθ', (hαc a _).mp rfl, (hτ l).2]
  have hβ : ∀ (l : Kˣ) (w : ↥𝐖[i]),
      Multiplicative.toAdd (β (θ' l w : ↥𝐖[i] ⧸ A')) = l * Multiplicative.toAdd (β w) := by
    intro l w
    rw [hβc, hθ', kappa_conj_torus h (hτJ l), (hβc w _).mp rfl, (hτ l).2]
  obtain ⟨hcomm, hcard, hsq, c, hform, huniq, h0, hne⟩ :=
    SteinbergCD.scalar_equivariant_central_two_extension_square_map n K h.setup.card_K ↥𝐖[i] A'
      hAZ α β θ' hα hβ
  have hsqG : ∀ w : ↥𝐖[i], ((w ^ 2 : ↥𝐖[i]) : G) = (w : G) * w := fun w => by
    rw [SubgroupClass.coe_pow, pow_two]
  refine ⟨fun x hx y hy => congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩), c, ?_, ?_, ?_, ?_⟩
  · intro w hw a hκ
    have h1 := hform ⟨w, hw⟩ ⟨_, hsq ⟨w, hw⟩⟩ rfl
    rw [(hβc ⟨w, hw⟩ a).mpr hκ, hαc] at h1
    rw [← h1]
    exact (hsqG ⟨w, hw⟩).symm
  · intro lam' hlam'
    refine huniq lam' fun g a ha => ?_
    have h1 := hlam' g g.2 _ ((hβc g _).mp rfl)
    rw [hαc, ha, hsqG]
    exact h1
  · intro hc0
    have hE := h0 hc0
    refine ⟨hE, ?_⟩
    have h2 : ∀ x ∈ 𝐖[i], x * x = 1 := fun x hx => by
      rw [← pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    have h3 := CFSG.LocalAnalysis.SymplecticFourRankThompson.two_pow_rank_eq_card_of_elementary
      𝐖[i] h2
    rw [hcard, ← pow_mul, mul_comm] at h3
    exact Nat.pow_right_injective le_rfl h3
  · intro hc0
    obtain ⟨hcl, hom, -, -, φ', -⟩ := hne hc0
    have hU : 𝐔[i] ≤ 𝐖[i] := U_le_W h i
    have hset : {x : G | x ∈ 𝐖[i] ∧ x * x = 1} = 𝐔[i] := by
      ext x
      constructor
      · rintro ⟨hxW, hx1⟩
        have hmem : (⟨x, hxW⟩ : ↥𝐖[i]) ∈ {g : ↥𝐖[i] | g ^ 2 = 1} :=
          Subtype.ext (by rw [hsqG]; exact hx1)
        rw [hom] at hmem
        exact mem_subgroupOf.mp hmem
      · intro hxU
        have hmem : (⟨x, hU hxU⟩ : ↥𝐖[i]) ∈ (A' : Set ↥𝐖[i]) := mem_subgroupOf.mpr hxU
        rw [← hom] at hmem
        refine ⟨hU hxU, ?_⟩
        have := congrArg Subtype.val (hmem : (⟨x, hU hxU⟩ : ↥𝐖[i]) ^ 2 = 1)
        rwa [hsqG] at this
    refine ⟨?_, by rw [hset]; exact closure_eq _, hset, ⟨φ'⟩⟩
    have h1 := congrArg (Subgroup.map 𝐖[i].subtype) hcl
    rw [MonoidHom.map_closure, subgroupOf_map_subtype, inf_of_le_left hU] at h1
    rw [← h1]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩ ^ 2, ⟨⟨y, hy⟩, rfl⟩, hsqG ⟨y, hy⟩⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, g.2, hsqG g⟩

theorem F_comm (h : FCHyp L K n φ t) {x y : G} (hx : x ∈ 𝐅) (hy : y ∈ 𝐅) : x * y = y * x := by
  have hx' : x ∈ (𝐖[Axis.one] : Set G) * (𝐖[Axis.two] : Set G) := by
    rw [W_mul_W h]
    exact hx
  have hy' : y ∈ (𝐖[Axis.one] : Set G) * (𝐖[Axis.two] : Set G) := by
    rw [W_mul_W h]
    exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨c, hc, d, hd, rfl⟩ := hy'
  have h1 := (square_map h Axis.one).1
  have h2 := (square_map h Axis.two).1
  calc a * b * (c * d) = a * (b * c) * d := by group
    _ = a * (c * b) * d := by rw [← W_comm h hc hb]
    _ = (a * c) * (b * d) := by group
    _ = (c * a) * (d * b) := by rw [h1 a ha c hc, h2 b hb d hd]
    _ = c * (a * d) * b := by group
    _ = c * (d * a) * b := by rw [W_comm h ha hd]
    _ = c * d * (a * b) := by group

end Square

end FullCenterTorus

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
