module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKDefs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section KConjAux

variable {G : Type} [Group G]

theorem sixK_k7_aux_comm (M U : Subgroup G)
    (hsq : ∀ z ∈ M, z * z ∈ U) (hcen : ∀ v ∈ U, ∀ z ∈ M, z * v = v * z)
    {x y : G} (hx : x ∈ M) (hy : y ∈ M) : x⁻¹ * y⁻¹ * x * y ∈ U := by
  have ha : x * x ∈ U := hsq x hx
  have hb : y * y ∈ U := hsq y hy
  have hc : (x * y) * (x * y) ∈ U := hsq (x * y) (M.mul_mem hx hy)
  obtain ⟨c, hc_def⟩ : ∃ c : G, c = (x * y) * (x * y) := ⟨_, rfl⟩
  rw [← hc_def] at hc
  have hinv : x⁻¹ * y⁻¹ = y * c⁻¹ * x := by
    rw [hc_def]
    group
  have hya : y * (x * x) = (x * x) * y := hcen _ ha y hy
  have hyc : y * c⁻¹ = c⁻¹ * y := hcen _ (U.inv_mem hc) y hy
  have key : x⁻¹ * y⁻¹ * x * y = c⁻¹ * (x * x) * (y * y) := by
    rw [hinv]
    calc y * c⁻¹ * x * x * y = (y * c⁻¹) * (x * x) * y := by group
      _ = (c⁻¹ * y) * (x * x) * y := by rw [hyc]
      _ = c⁻¹ * (y * (x * x)) * y := by group
      _ = c⁻¹ * ((x * x) * y) * y := by rw [hya]
      _ = c⁻¹ * (x * x) * (y * y) := by group
  rw [key]
  exact U.mul_mem (U.mul_mem (U.inv_mem hc) ha) hb

theorem sixK_k7_aux_mul (M U : Subgroup G)
    (hcen : ∀ v ∈ U, ∀ z ∈ M, z * v = v * z) {x y z : G} (hx : x ∈ M) (hz : z ∈ M)
    (hp : x⁻¹ * y⁻¹ * x * y ∈ U) :
    x⁻¹ * (y * z)⁻¹ * x * (y * z) = (x⁻¹ * y⁻¹ * x * y) * (x⁻¹ * z⁻¹ * x * z) := by
  have hq : x⁻¹ * z⁻¹ * x * z ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem (M.inv_mem hx) (M.inv_mem hz)) hx) hz
  have hc : (x⁻¹ * z⁻¹ * x * z) * (x⁻¹ * y⁻¹ * x * y)
      = (x⁻¹ * y⁻¹ * x * y) * (x⁻¹ * z⁻¹ * x * z) :=
    hcen _ hp _ hq
  have hpz : (x⁻¹ * y⁻¹ * x * y) * z = z * (x⁻¹ * y⁻¹ * x * y) := (hcen _ hp z hz).symm
  have hyx : y⁻¹ * x * y = x * (x⁻¹ * y⁻¹ * x * y) := by group
  calc x⁻¹ * (y * z)⁻¹ * x * (y * z) = x⁻¹ * z⁻¹ * (y⁻¹ * x * y) * z := by group
    _ = x⁻¹ * z⁻¹ * (x * (x⁻¹ * y⁻¹ * x * y)) * z := by rw [hyx]
    _ = x⁻¹ * z⁻¹ * x * ((x⁻¹ * y⁻¹ * x * y) * z) := by group
    _ = x⁻¹ * z⁻¹ * x * (z * (x⁻¹ * y⁻¹ * x * y)) := by rw [hpz]
    _ = (x⁻¹ * z⁻¹ * x * z) * (x⁻¹ * y⁻¹ * x * y) := by group
    _ = (x⁻¹ * y⁻¹ * x * y) * (x⁻¹ * z⁻¹ * x * z) := hc

theorem sixK_k7_aux_four_mul_lt (n : ℕ) (hn : 2 ≤ n) : 4 * n < 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    linarith

theorem sixK_k7_aux_cent [Finite G] (M U : Subgroup G) (q : ℕ) (hq : 0 < q)
    (hsq : ∀ z ∈ M, z * z ∈ U) (hcen : ∀ v ∈ U, ∀ z ∈ M, z * v = v * z)
    (hU : Nat.card U = q) (hM : Nat.card M = q ^ 7) (hM2 : IsPGroup 2 M) {x : G} (hx : x ∈ M) :
    ∃ C : Subgroup M, q ^ 6 ≤ Nat.card C ∧ IsPGroup 2 C ∧
      ∀ y ∈ C, x * (y : G) = (y : G) * x := by
  let f : M →* G :=
    { toFun := fun y => x⁻¹ * (y : G)⁻¹ * x * (y : G)
      map_one' := by simp
      map_mul' := fun y z => by
        show x⁻¹ * ((y * z : M) : G)⁻¹ * x * ((y * z : M) : G) =
          (x⁻¹ * (y : G)⁻¹ * x * (y : G)) * (x⁻¹ * (z : G)⁻¹ * x * (z : G))
        rw [Subgroup.coe_mul]
        exact sixK_k7_aux_mul M U hcen hx z.2 (sixK_k7_aux_comm M U hsq hcen hx y.2) }
  have hrange : f.range ≤ U := by
    rintro _ ⟨y, rfl⟩
    exact sixK_k7_aux_comm M U hsq hcen hx y.2
  have hcardR : Nat.card f.range ≤ q := (Subgroup.card_le_of_le hrange).trans hU.le
  have hindex : f.ker.index ≤ q := by
    rw [Subgroup.index_ker]
    exact hcardR
  have hmul : Nat.card f.ker * f.ker.index = q ^ 7 := by
    rw [Subgroup.card_mul_index, hM]
  have hcardK : q ^ 6 ≤ Nat.card f.ker := by
    have h1 : q ^ 7 ≤ Nat.card f.ker * q := by
      rw [← hmul]
      exact Nat.mul_le_mul_left _ hindex
    have h2 : q ^ 6 * q ≤ Nat.card f.ker * q := by
      calc q ^ 6 * q = q ^ 7 := by ring
        _ ≤ Nat.card f.ker * q := h1
    exact Nat.le_of_mul_le_mul_right h2 hq
  refine ⟨f.ker, hcardK, hM2.to_subgroup f.ker, ?_⟩
  intro y hy
  have h1 : x⁻¹ * (y : G)⁻¹ * x * (y : G) = 1 := MonoidHom.mem_ker.mp hy
  have h2 : (y : G)⁻¹ * x * (y : G) = x := by
    calc (y : G)⁻¹ * x * (y : G) = x * (x⁻¹ * (y : G)⁻¹ * x * (y : G)) := by group
      _ = x * 1 := by rw [h1]
      _ = x := mul_one x
  calc x * (y : G) = (y : G) * ((y : G)⁻¹ * x * (y : G)) := by group
    _ = (y : G) * x := by rw [h2]

theorem sixK_k7_aux_conj (g t c : G) (hxc : g⁻¹ * t * g * c = c * (g⁻¹ * t * g)) :
    t * (g * c * g⁻¹) = g * c * g⁻¹ * t := by
  calc t * (g * c * g⁻¹) = g * (g⁻¹ * t * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by rw [hxc]
    _ = g * c * g⁻¹ * t := by group

theorem sixK_k7_aux_arith (n : ℕ) (hn : 2 ≤ n) (N : ℕ) (hN : N = 2 ^ n)
    (h : N ^ 6 ≤ 4 * n * N ^ 4) : False := by
  have hpos : 0 < N ^ 4 := by
    have hN0 : 0 < N := by
      rw [hN]
      positivity
    exact pow_pos hN0 4
  have h2 : N ^ 2 ≤ 4 * n := by
    have h6 : N ^ 4 * N ^ 2 ≤ N ^ 4 * (4 * n) := by
      calc N ^ 4 * N ^ 2 = N ^ 6 := by ring
        _ ≤ 4 * n * N ^ 4 := h
        _ = N ^ 4 * (4 * n) := by ring
    exact Nat.le_of_mul_le_mul_left h6 hpos
  have h4 : N ^ 2 = 4 ^ n := by
    rw [hN, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hlt := sixK_k7_aux_four_mul_lt n hn
  rw [h4] at h2
  exact lt_irrefl _ (lt_of_le_of_lt h2 hlt)

end KConjAux

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixK_k7
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (k6 : K6Concl n φ t) : K7Concl φ t i := by
  intro g hg
  have hn : 2 ≤ n := hS.fc.setup.two_le
  have hKc : Nat.card K = 2 ^ n := hS.fc.setup.card_K
  have hq : 0 < Nat.card K := Nat.card_pos
  have hM : Nat.card (Mhat φ t i i) = Nat.card K ^ 7 :=
    SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have hM2 : IsPGroup 2 (Mhat φ t i i) := by
    rw [IsPGroup.iff_card]
    exact ⟨7 * n, by rw [hM, hKc, ← pow_mul, mul_comm]⟩
  have hsq : ∀ z ∈ Mhat φ t i i, z * z ∈ U φ i := by
    intro z hz
    rw [← hH.sq_Mhat_i]
    exact Subgroup.subset_closure ⟨z, hz, rfl⟩
  have hcen : ∀ v ∈ U φ i, ∀ z ∈ Mhat φ t i i, z * v = v * z := by
    intro v hv z hz
    rw [← hH.center_Mhat_i] at hv
    obtain ⟨v', hv', hvv⟩ := Subgroup.mem_map.mp hv
    rw [← hvv]
    have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hv' ⟨z, hz⟩)
    exact h3
  have hU : Nat.card (U φ i) = Nat.card K := RootAxisTwoCore.card_U φ i
  obtain ⟨C, hC6, hC2, hCcent⟩ :=
    sixK_k7_aux_cent (Mhat φ t i i) (U φ i) (Nat.card K) hq hsq hcen hU hM hM2 hg
  let ψ : Mhat φ t i i →* G := (MulAut.conj g).toMonoidHom.comp (Mhat φ t i i).subtype
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    have h1 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := hab
    exact mul_left_cancel (mul_right_cancel h1)
  have hR2 : IsPGroup 2 (C.map ψ) := hC2.map ψ
  have hRcard : Nat.card (C.map ψ) = Nat.card C := Subgroup.card_map_of_injective hψ
  have hRcent : C.map ψ ≤ centralizer ({t} : Set G) := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hr
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact sixK_k7_aux_conj g t (c : G) (hCcent c hc)
  have h6 := k6 (C.map ψ) hR2 hRcent
  have h7 : Nat.card K ^ 6 ≤ 4 * n * Nat.card K ^ 4 := by
    calc Nat.card K ^ 6 ≤ Nat.card C := hC6
      _ = Nat.card (C.map ψ) := hRcard.symm
      _ ≤ 4 * n * Nat.card K ^ 4 := h6
  exact sixK_k7_aux_arith n hn (Nat.card K) hKc h7

theorem sixK_k8
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (k5 : K5Concl n φ t) : K8Concl φ t i := by
  intro g hg
  have hn : 2 ≤ n := hS.fc.setup.two_le
  have hKc : Nat.card K = 2 ^ n := hS.fc.setup.card_K
  have hcardKc : Nat.card (Kc φ t i.swap) = Nat.card K ^ 4 :=
    FullCenterWeyl.card_K hS.fc i.swap
  have hKsq : ∀ x ∈ Kc φ t i.swap, x * x = 1 := fun x hx =>
    SingleComm.K_sq hS.fc i.swap (fun w hw => SingleComm.sq_W_swap hS.fc i hS.ne_bot hS.eq_bot hw) hx
  have hKcomm : ∀ x ∈ Kc φ t i.swap, ∀ y ∈ Kc φ t i.swap, x * y = y * x := fun x hx y hy =>
    FullCenterWeyl.K_comm hS.fc i.swap hx hy
  have hcent : ∀ y ∈ Kc φ t i.swap, g⁻¹ * t * g * y = y * (g⁻¹ * t * g) := by
    intro y hy
    rw [← hH.center_Mhat_j] at hy
    obtain ⟨v', hv', hvv⟩ := Subgroup.mem_map.mp hy
    rw [← hvv]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hv' ⟨g⁻¹ * t * g, hg⟩)
  let ψ : G →* G := (MulAut.conj g).toMonoidHom
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 : g * a * g⁻¹ = g * b * g⁻¹ := hab
    exact mul_left_cancel (mul_right_cancel h1)
  have hEcent : (Kc φ t i.swap).map ψ ≤ centralizer ({t} : Set G) := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hr
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact sixK_k7_aux_conj g t c (hcent c hc)
  have hEsq : ∀ r ∈ (Kc φ t i.swap).map ψ, r * r = 1 := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hr
    show g * c * g⁻¹ * (g * c * g⁻¹) = 1
    rw [show g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ by group, hKsq c hc]
    group
  have hEcomm : ∀ r ∈ (Kc φ t i.swap).map ψ, ∀ s ∈ (Kc φ t i.swap).map ψ, r * s = s * r := by
    intro r hr s hs
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hs
    show g * c * g⁻¹ * (g * d * g⁻¹) = g * d * g⁻¹ * (g * c * g⁻¹)
    rw [show g * c * g⁻¹ * (g * d * g⁻¹) = g * (c * d) * g⁻¹ by group, hKcomm c hc d hd]
    group
  have hcardE : Nat.card ((Kc φ t i.swap).map ψ) = 2 ^ (4 * n) := by
    rw [Subgroup.card_map_of_injective hψ, hcardKc, hKc, ← pow_mul, mul_comm]
  have h5 := k5 ((Kc φ t i.swap).map ψ) hEcent hEsq hEcomm
  rw [hcardE] at h5
  have hbig : 2 ^ (3 * n + 1) < 2 ^ (4 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact absurd h5 (not_le.mpr hbig)

theorem sixK_k9 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (k4 : K4Concl φ t i) (k7 : K7Concl φ t i) (k8 : K8Concl φ t i) :
    K9Concl φ t i := by
  intro g hg
  have htt : t * t = 1 := hS.fc.setup.t_mul_t
  have hinv : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, htt]
    group
  obtain ⟨h, hh⟩ := k4 (g⁻¹ * t * g) hg hinv
  have hconj : (g * h)⁻¹ * t * (g * h) = h⁻¹ * (g⁻¹ * t * g) * h := by group
  rcases hh with hh | hh
  · exact k7 (g * h) (by rw [hconj]; exact hh)
  · exact k8 (g * h) (by rw [hconj]; exact hh)

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
