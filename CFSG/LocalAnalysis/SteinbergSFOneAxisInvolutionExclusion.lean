module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisWeakClosure

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisInvolutionExclusion

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisSecondAxis OneAxisWeakClosure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped Matrix commutatorElement Pointwise

section Model

variable {K : Type} [Field K]

theorem exists_SL_mulVec_eq {u : Fin 2 → K} (hu : u ≠ 0) :
    ∃ N : SL₂ K, (N : Matrix (Fin 2) (Fin 2) K) *ᵥ u = ![1, 0] := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := fun h1 => hu (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, (u 1)⁻¹; -u 1, 0], by simp [Matrix.det_fin_two_of, h1]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  · refine ⟨⟨!![(u 0)⁻¹, 0; -u 1, u 0], by simp [Matrix.det_fin_two_of, h0]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    ring

end Model

section Conj

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {t : G}

theorem hAct_zero_iff {g : G} {x y : K} :
    HAct φ t g x y 0 ↔
      ∀ v : Fin 2 → K, g * coord φ t (qgPoint v) * g⁻¹ = coord φ t (qgPoint (v + ![y, x])) := by
  have e : ∀ v : Fin 2 → K, (![v 0 + 0 * v 1 + y, v 1 + x] : Fin 2 → K) = v + ![y, x] := by
    intro v
    ext i
    fin_cases i <;> simp
  exact forall_congr' fun v => by rw [e v]

theorem sElt_conj_coord (hS : TwoCoreSetup L K n t) (N : SL₂ K) (v : Fin 2 → K) :
    ((φ.symm (sElt N) : L) : G) * coord φ t (qgPoint v) * ((φ.symm (sElt N) : L) : G)⁻¹ =
      coord φ t (qgPoint ((N : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) := by
  have hgt : ((φ.symm (sElt N) : L) : G) * t = t * ((φ.symm (sElt N) : L) : G) :=
    (hS.comm (φ.symm _).2).symm
  have h1 : sElt N * aElt v 0 * (sElt N)⁻¹ = aElt ((N : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 0 := by
    rw [sElt_mul_aElt, mul_inv_cancel_right]
  rw [coord_qgPoint, coord_qgPoint, ← h1, ← symm_conj_eq]
  calc ((φ.symm (sElt N) : L) : G) * (t * ((φ.symm (aElt v 0) : L) : G)) *
        ((φ.symm (sElt N) : L) : G)⁻¹
      = (((φ.symm (sElt N) : L) : G) * t) * ((φ.symm (aElt v 0) : L) : G) *
          ((φ.symm (sElt N) : L) : G)⁻¹ := by group
    _ = _ := by rw [hgt]; group

theorem hAct_sElt_conj (hS : TwoCoreSetup L K n t) (N : SL₂ K) {g : G} {x y x' y' : K}
    (h : HAct φ t g x y 0) (hN : (N : Matrix (Fin 2) (Fin 2) K) *ᵥ ![y, x] = ![y', x']) :
    HAct φ t (((φ.symm (sElt N) : L) : G) * g * ((φ.symm (sElt N) : L) : G)⁻¹) x' y' 0 := by
  rw [hAct_zero_iff] at h ⊢
  intro v
  have hinv : ((φ.symm (sElt N) : L) : G)⁻¹ = ((φ.symm (sElt N⁻¹) : L) : G) := by
    rw [← coe_inv, ← map_inv, show (sElt N)⁻¹ = sElt N⁻¹ from (map_inv (sHom₂ K) N).symm]
  have e1 := sElt_conj_coord (φ := φ) hS N⁻¹ v
  rw [← hinv, inv_inv] at e1
  have e2 : (N : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((N⁻¹ : SL₂ K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v + ![y, x]) = v + ![y', x'] := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, hN]
  calc ((φ.symm (sElt N) : L) : G) * g * ((φ.symm (sElt N) : L) : G)⁻¹ * coord φ t (qgPoint v) *
        (((φ.symm (sElt N) : L) : G) * g * ((φ.symm (sElt N) : L) : G)⁻¹)⁻¹
      = ((φ.symm (sElt N) : L) : G) * (g * (((φ.symm (sElt N) : L) : G)⁻¹ *
          coord φ t (qgPoint v) * ((φ.symm (sElt N) : L) : G)) * g⁻¹) *
          ((φ.symm (sElt N) : L) : G)⁻¹ := by group
    _ = _ := by rw [e1, h, sElt_conj_coord hS, e2]

end Conj

section Rank

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {φ : L ≃* antiSp K}
  {TG : Subgroup G} {t : G}

theorem rank_le_of_le_centralizer [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) {E : Subgroup G} (hEC : E ≤ centralizer ({t} : Set G))
    (hE : IsElementaryAbelian 2 E) :
    Group.rank E ≤ 3 * n + 1 ∧ Nat.card E ≤ 2 ^ (3 * n + 1) := by
  set C := centralizer ({t} : Set G) with hC
  obtain ⟨R, hQR⟩ := (hS.Q_two.of_equiv (subgroupOfEquivOfLe hS.Q_le_C).symm).exists_le_sylow
  set RG := (R : Subgroup C).map C.subtype with hRG
  have hRGC : RG ≤ C := map_subtype_le _
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map _
  have hQRG : pull φ (antiUnipotent K) ⊔ TG ≤ RG := fun q hq =>
    ⟨⟨q, hS.Q_le_C hq⟩, hQR (mem_subgroupOf.mpr hq), rfl⟩
  have : IsElementaryAbelian 2 E := hE
  obtain ⟨c, -, hc⟩ := Setup.exists_conj_le_sylow R hEC (IsElementaryAbelian.isPGroup 2 E)
  have hE'R : E.map (MulAut.conj c⁻¹).toMonoidHom ≤ RG := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hc y hy
  have : IsMulCommutative (E.map (MulAut.conj c⁻¹).toMonoidHom) :=
    (elemAb_map hE (MulAut.conj c⁻¹).toMonoidHom).toIsMulCommutative
  have hrk : Group.rank (E.map (MulAut.conj c⁻¹).toMonoidHom) = Group.rank E :=
    (Group.rank_congr (E.equivMapOfInjective _ (MulAut.conj c⁻¹).injective)).symm
  have h1 := (hS.rank_bound hRGC hRG2 hQRG hE'R).1
  rw [hrk] at h1
  refine ⟨h1, ?_⟩
  rw [← two_pow_rank_eq_card_of_sq fun x : E => Subtype.ext (elemAb_mul_self hE x.2)]
  exact Nat.pow_le_pow_right (by norm_num) h1

end Rank

section Main

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
local notation "𝐍₂" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
local notation "𝐂₂" => (L ⊓ centralizer (pull φ (rootU K Axis.two) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₂" =>
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₀" => (M ⊔ pull φ (rootA K Axis.two) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐕" => (M ⊔ pull φ (rootA K Axis.one) ⊔
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom) : Subgroup G)

theorem C₂_le_N₂ [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) : 𝐂₂ ≤ 𝐍₂ := by
  intro c hc
  have hcK : c ∈ centralizer ((zpowers t ⊔ 𝐔₂ : Subgroup G) : Set G) := by
    rw [hS.centralizer_eq φ Axis.two]
    exact mem_sup_right ((TwoCoreSetup.pull_rootC_eq φ Axis.two).ge hc)
  exact mem_normalizer_of_conj_le fun b hb => hS.conj_mem_B φ Axis.two hcK hb

theorem sElt_mem_C₂ (N : SL₂ K) : ((φ.symm (sElt N) : L) : G) ∈ 𝐂₂ :=
  (TwoCoreSetup.pull_rootC_eq φ Axis.two).le (symm_mem_pull.mpr (sElt_mem_rootC₂ N))

theorem C₂_le_normalizer [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    𝐂₂ ≤ normalizer (𝐌₂ : Set G) := fun _ hc =>
  ax.normalizer_D₂_le (by rw [← ax.normalizer_B₂_eq]; exact C₂_le_N₂ ax.heis.sec.two hc)

theorem mem_M₀_of_hAct [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐌₂)
    {b : K} (h : HAct φ t x 0 b 0) : x ∈ 𝐌₀ := by
  obtain ⟨m, hm, m', hm', a, b', rfl, -, ha, hx'⟩ := ax.exists_of_mem_M₂ hx
  obtain ⟨rfl, -, -⟩ := HAct.unique ax.heis.sec.two hx' h
  have hm'A : m' ∈ 𝐀₂ := mem_A₂_of_conj_mem_ZP
    (ax.mem_ZP_of_hAct (mem_map_conj_inv_iff.mp hm') (hAct_w_conj ax.heis.sec.two ha))
  exact mul_mem (mem_sup_left hm) (mem_sup_right hm'A)

theorem exists_conj_mem_M [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {y : G}
    (hy : y ∈ 𝐌₂) (hyy : y * y = 1) : ∃ c ∈ 𝐂₂, c * y * c⁻¹ ∈ M := by
  have hS := ax.heis.sec.two
  obtain ⟨x₀, y₀, h⟩ := hAct_of_mem_D ax.heis.sec (ax.M₂_le_D₂ hy)
  by_cases hu : (![y₀, x₀] : Fin 2 → K) = 0
  · have hx₀ : x₀ = 0 := by simpa using congrFun hu 1
    have hy₀ : y₀ = 0 := by simpa using congrFun hu 0
    subst hx₀ hy₀
    have hyA : y ∈ 𝐀₂ := by
      rw [← ax.M₂_inf_B₂]
      exact mem_inf.mpr ⟨hy, mem_B₂_of_hAct ax.heis (SecondHyp.D_le_N (ax.M₂_le_D₂ hy)) h⟩
    obtain ⟨a, ha, rfl⟩ := exists_eq_symm_of_mem_pull hyA
    obtain ⟨v, c₀, rfl⟩ := mem_radA2_iff.mp ha
    by_cases hv : v = 0
    · subst hv
      refine ⟨1, one_mem _, ?_⟩
      rw [one_mul, inv_one, mul_one]
      exact ax.U₂_le (symm_mem_pull.mpr (aElt_zero_mem_rootU₂ c₀))
    · obtain ⟨N, hN⟩ := exists_SL_mulVec_eq hv
      refine ⟨_, sElt_mem_C₂ N, ?_⟩
      rw [symm_conj_eq, sElt_mul_aElt, mul_inv_cancel_right, hN]
      exact ax.ZP_le (symm_mem_pull.mpr ⟨1, c₀, by simp [aElt]⟩)
  · obtain ⟨N, hN⟩ := exists_SL_mulVec_eq hu
    have hg := sElt_mem_C₂ (φ := φ) N
    refine ⟨_, hg, ?_⟩
    have h' := hAct_sElt_conj hS N h hN
    have hy' : ((φ.symm (sElt N) : L) : G) * y * ((φ.symm (sElt N) : L) : G)⁻¹ ∈ 𝐌₂ :=
      (mem_normalizer_iff.mp (C₂_le_normalizer ax hg) y).mp hy
    have hsq : ((φ.symm (sElt N) : L) : G) * y * ((φ.symm (sElt N) : L) : G)⁻¹ *
        (((φ.symm (sElt N) : L) : G) * y * ((φ.symm (sElt N) : L) : G)⁻¹) = 1 := by
      rw [show ((φ.symm (sElt N) : L) : G) * y * ((φ.symm (sElt N) : L) : G)⁻¹ *
          (((φ.symm (sElt N) : L) : G) * y * ((φ.symm (sElt N) : L) : G)⁻¹) =
          ((φ.symm (sElt N) : L) : G) * (y * y) * ((φ.symm (sElt N) : L) : G)⁻¹ by group, hyy,
        mul_one, mul_inv_cancel]
    rcases mem_M_or_A₂ ax (mem_M₀_of_hAct ax hy' h') hsq with hM | hA
    · exact hM
    · exfalso
      obtain ⟨-, h10, -⟩ := HAct.unique hS h' (hAct_of_mem_B ax.heis.sec (mem_sup_right hA))
      exact one_ne_zero h10

theorem inv_M₂_eq [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) :
    {y : G | y ∈ 𝐌₂ ∧ orderOf y = 2} =
      {y | ∃ c ∈ 𝐂₂, ∃ m ∈ M, m ≠ 1 ∧ y = c⁻¹ * m * c} := by
  ext y
  constructor
  · rintro ⟨hy, ho⟩
    obtain ⟨hyy, hy1⟩ := orderOf_eq_prime_iff.mp ho
    rw [pow_two] at hyy
    obtain ⟨c, hc, hcy⟩ := exists_conj_mem_M ax hy hyy
    refine ⟨c, hc, _, hcy, fun h => hy1 ?_, by group⟩
    have e : y = c⁻¹ * (c * y * c⁻¹) * c := by group
    rw [e, h]
    group
  · rintro ⟨c, hc, m, hm, hm1, rfl⟩
    refine ⟨(mem_normalizer_iff''.mp (C₂_le_normalizer ax hc) m).mp (mem_sup_left hm), ?_⟩
    refine orderOf_eq_prime_iff.mpr ⟨?_, fun h => hm1 ?_⟩
    · rw [pow_two, show c⁻¹ * m * c * (c⁻¹ * m * c) = c⁻¹ * (m * m) * c by group,
        ax.mul_self m hm, mul_one, inv_mul_cancel]
    · have e : m = c * (c⁻¹ * m * c) * c⁻¹ := by group
      rw [e, h]
      group

theorem exists_conj_mem_M₁ [Finite G] [Finite K] (ax : AxisHyp L K n φ TG t M) {y : G}
    (hy : y ∈ 𝐕) (hyy : y * y = 1) : ∃ g : G, g⁻¹ * y * g ∈ 𝐌₁ := by
  rcases mem_M₁_or_M₂ ax hy (by rw [hyy]; exact one_mem _) with h | h
  · exact ⟨1, by simpa using h⟩
  · obtain ⟨c, -, hc⟩ := exists_conj_mem_M ax h hyy
    exact ⟨c⁻¹, by simpa using mem_sup_left hc⟩

theorem conj_not_mem_M₁ [Finite G] [Finite K]
    (ax : AxisHyp L K n φ TG t M) (hM₁ : IsElementaryAbelian 2 𝐌₁) (g : G) :
    g⁻¹ * t * g ∉ 𝐌₁ := by
  intro hg
  have hEC : 𝐌₁.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := elemAb_comm hM₁ hm hg
    calc g * m * g⁻¹ * t = g * (m * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * m) * g⁻¹ := by rw [hc]
      _ = t * (g * m * g⁻¹) := by group
  have h := (rank_le_of_le_centralizer ax.heis.hyp.setup hEC (elemAb_map hM₁ _)).2
  rw [card_map_of_injective (MulAut.conj g).injective, ax.card₁, ← pow_mul] at h
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have h2 := ax.heis.sec.two.two_le
  omega

theorem conj_not_mem_V [Finite G] [Finite K]
    (ax : AxisHyp L K n φ TG t M) (hM₁ : IsElementaryAbelian 2 𝐌₁) (g : G) :
    g⁻¹ * t * g ∉ 𝐕 := by
  intro hg
  have hsq : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group,
      ax.heis.sec.two.t_mul_t, mul_one, inv_mul_cancel]
  obtain ⟨h, hh⟩ := exists_conj_mem_M₁ ax hg hsq
  refine conj_not_mem_M₁ ax hM₁ (g * h) ?_
  rw [show (g * h)⁻¹ * t * (g * h) = h⁻¹ * (g⁻¹ * t * g) * h by group]
  exact hh

theorem main [Finite G] [Finite K] (hh : HeisHyp L K n φ TG t)
    (Q ZP PG : Subgroup G) (hPG : PG = pull φ (antiUnipotent K)) (hQ : Q = PG ⊔ TG)
    (hZP : ZP = pull φ (antiUnipotentCenter K)) (w : antiSp K)
    (hw : glMat (w : GL (Fin 4) K) = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1])
    (M : Subgroup G) :
    let C := centralizer ({t} : Set G)
    let U₂ := pull φ (rootU K Axis.two)
    let A₁ := pull φ (rootA K Axis.one)
    let A₂ := pull φ (rootA K Axis.two)
    let B₁ := zpowers t ⊔ A₁
    let B₂ := zpowers t ⊔ A₂
    let N₁ := normalizer (B₁ : Set G)
    let N₂ := normalizer (B₂ : Set G)
    let D₁ := (CFSG.pCore 2 N₁).map N₁.subtype
    let D₂ := (CFSG.pCore 2 N₂).map N₂.subtype
    let S := Q ⊔ D₂
    let J₀ := pull φ (diagTorus K)
    let w₂ : G := ((φ.symm w : L) : G)
    let Mw := M.map (MulAut.conj w₂⁻¹).toMonoidHom
    let M₁ := M ⊔ A₁
    let M₂ := M ⊔ Mw
    let V := M₁ ⊔ M₂
    let C₂ := L ⊓ centralizer (U₂ : Set G)
    J₀ ≤ normalizer (M : Set G) → M ≤ D₁ ⊓ D₂ → IsElementaryAbelian 2 M →
    Nat.card M = (2 ^ n) ^ 3 → ZP ≤ M → IsElementaryAbelian 2 M₁ →
    Nat.card M₁ = (2 ^ n) ^ 4 → (M₁ ≤ S ∧ (M₁.subgroupOf S).Normal) →
    (M₁ ≤ D₁ ∧ (M₁.subgroupOf D₁).Normal ∧ M₁ ⊓ zpowers t = ⊥ ∧ M₁ ⊔ zpowers t = D₁) →
      (∀ E : Subgroup G, E ≤ C → IsElementaryAbelian 2 E →
        Group.rank E ≤ 3 * n + 1 ∧ Nat.card E ≤ 2 ^ (3 * n + 1)) ∧
      C₂ ≤ normalizer (M₂ : Set G) ∧
      {y : G | y ∈ M₂ ∧ orderOf y = 2} = {y | ∃ c ∈ C₂, ∃ m ∈ M, m ≠ 1 ∧ y = c⁻¹ * m * c} ∧
      (∀ y ∈ V, orderOf y = 2 → ∃ g : G, g⁻¹ * y * g ∈ M₁) ∧
      {x : G | ∃ g : G, x = g⁻¹ * t * g} ∩ (V : Set G) = ∅ := by
  subst hQ hPG hZP
  obtain rfl : w = sElt swapSL := antiSp_ext (hw.trans glMat_sElt_swap.symm)
  intro C U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ S J₀ w₂ Mw M₁ M₂ V C₂ _ hMD hMab hMcard hZM hM₁
    hM₁card hM₁S hM₁D
  have hM₁n := (normal_subgroupOf_iff_le_normalizer hM₁S.1).mp hM₁S.2
  have ax : AxisHyp L K n φ TG t M :=
    { heis := hh
      le_D₁ := hMD.trans inf_le_left
      le_D₂ := hMD.trans inf_le_right
      comm := fun _ hx _ hy => elemAb_comm hMab hx hy
      mul_self := fun _ hx => elemAb_mul_self hMab hx
      card := hMcard
      ZP_le := hZM
      card₁ := hM₁card
      conj₁ := fun s hs x hx => (mem_normalizer_iff.mp (hM₁n hs) x).mp hx
      t_not_mem₁ := fun h => by
        have h1 : t ∈ M₁ ⊓ zpowers t := mem_inf.mpr ⟨h, mem_zpowers t⟩
        rw [hM₁D.2.2.1, mem_bot] at h1
        exact hh.hyp.setup.t_ne_one h1 }
  refine ⟨fun E hEC hE => rank_le_of_le_centralizer hh.hyp.setup hEC hE, C₂_le_normalizer ax,
    inv_M₂_eq ax, fun y hy ho => ?_, ?_⟩
  · obtain ⟨hyy, -⟩ := orderOf_eq_prime_iff.mp ho
    rw [pow_two] at hyy
    exact exists_conj_mem_M₁ ax hy hyy
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨g, rfl⟩, hg⟩
    exact conj_not_mem_V ax hM₁ g hg

end Main

end OneAxisInvolutionExclusion

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

theorem standard_symplectic_four_given_first_overgroup_involution_exclusion
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) (w : antiSp K)
    (hw : glMat (w : GL (Fin 4) K) = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1])
    (M : Subgroup G) :
    let C := centralizer ({(t : G)} : Set G)
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    let U₂ := ((rootU K Axis.two).comap φ.toMonoidHom).map L.subtype
    let A₁ := ((rootA K Axis.one).comap φ.toMonoidHom).map L.subtype
    let A₂ := ((rootA K Axis.two).comap φ.toMonoidHom).map L.subtype
    let B₁ := zpowers (t : G) ⊔ A₁
    let B₂ := zpowers (t : G) ⊔ A₂
    let N₁ := normalizer (B₁ : Set G)
    let N₂ := normalizer (B₂ : Set G)
    let D₁ := (CFSG.pCore 2 N₁).map N₁.subtype
    let D₂ := (CFSG.pCore 2 N₂).map N₂.subtype
    let S := Q ⊔ D₂
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let w₂ : G := ((φ.symm w : L) : G)
    let Mw := M.map (MulAut.conj w₂⁻¹).toMonoidHom
    let M₁ := M ⊔ A₁
    let M₂ := M ⊔ Mw
    let V := M₁ ⊔ M₂
    let C₂ := L ⊓ centralizer (U₂ : Set G)
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
    J₀ ≤ normalizer (M : Set G) → M ≤ D₁ ⊓ D₂ → IsElementaryAbelian 2 M →
    Nat.card M = (2 ^ n) ^ 3 → ZP ≤ M → IsElementaryAbelian 2 M₁ →
    Nat.card M₁ = (2 ^ n) ^ 4 → (M₁ ≤ S ∧ (M₁.subgroupOf S).Normal) →
    (M₁ ≤ D₁ ∧ (M₁.subgroupOf D₁).Normal ∧ M₁ ⊓ zpowers (t : G) = ⊥ ∧
      M₁ ⊔ zpowers (t : G) = D₁) →
      (∀ E : Subgroup G, E ≤ C → IsElementaryAbelian 2 E →
        Group.rank E ≤ 3 * n + 1 ∧ Nat.card E ≤ 2 ^ (3 * n + 1)) ∧
      C₂ ≤ normalizer (M₂ : Set G) ∧
      {y : G | y ∈ M₂ ∧ orderOf y = 2} = {y | ∃ c ∈ C₂, ∃ m ∈ M, m ≠ 1 ∧ y = c⁻¹ * m * c} ∧
      (∀ y ∈ V, orderOf y = 2 → ∃ g : G, g⁻¹ * y * g ∈ M₁) ∧
      {x : G | ∃ g : G, x = g⁻¹ * (t : G) * g} ∩ (V : Set G) = ∅ := by
  intro C TG PG Q ZP U₁ U₂ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ S J₀ w₂ Mw M₁ M₂ V C₂ hone
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hT' := hS.T_eq_zpowers hO hLn
  have hS2 : TwoCoreSetup L K n (t : G) :=
    { two_le := hn
      card_K := hK
      t_mul_t := hS.t_mul_t
      L_le := hS.L_le
      cent_le := hS.cent_le
      cent_inf := hS.cent_inf.trans hT'
      not_conj := hS.conj_not_mem_L hO hLn }
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hQ : Q = pull φ (antiUnipotent K) ⊔ TG := by
    show PG ⊔ TG = _
    rw [hPG]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    have h := center_pull_antiUnipotent (G := G) φ
    rw [← hPG] at h
    exact h
  have hH : Hyp L K n φ TG t := ⟨hS, hS2, hT', by rw [← hQ]; exact hone⟩
  have hNQ := hH.normalizer_Q_le
  have hNC := (hS.orbits hO hLn).2.2.2.2
  have hmove : ∃ g ∈ N₂, g * t ≠ t * g := by
    obtain ⟨m, hm, hmC⟩ := Set.not_subset.mp hNC
    exact ⟨m, (hNQ hm).2, fun hmt => hmC (mem_centralizer_singleton_iff.mpr hmt)⟩
  have h2 : SecondHyp L K n φ (t : G) := ⟨hS2, hH.fus_two.1, hmove⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hinf₁, -, _, e, he, -, -, -⟩ :=
    standard_symplectic_four_one_axis_radical_fusion_normalizers hO hL hLn hn hK T hT htT ht
      hcore P φ hφP hone
  have hh : HeisHyp L K n φ TG t :=
    { hyp := hH
      sec := h2
      normQ := hNQ
      inf₁ := hinf₁
      conj₁ := fun d hd => by
        rw [← he ⟨d, hd⟩]
        exact (e (⟨d, hd⟩ : D₁)).2
      mul₁ := fun d hd d' hd' => by
        have h1 := he (⟨d, hd⟩ * ⟨d', hd'⟩)
        rw [QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul, he, he] at h1
        exact h1.symm
      surj₁ := fun u hu => by
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm ⟨u, hu⟩)
        refine ⟨x, x.2, ?_⟩
        have h1 := he x
        rw [hx, MulEquiv.apply_symm_apply] at h1
        exact h1.symm }
  exact OneAxisInvolutionExclusion.main hh Q ZP PG hPG rfl hZP w hw M

end CFSG.LocalAnalysis.SymplecticFourStandard
