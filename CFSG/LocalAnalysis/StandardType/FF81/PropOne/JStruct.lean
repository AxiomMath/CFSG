module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.Mathlib.GroupTheory.SLCentralizerOrderThree
public import CFSG.LocalAnalysis.StandardType.GGFFModelSL
import CFSG.Adapters.StatedSLTwoField
import CFSG.Open.StatedZModTwo
import CFSG.Adapters.ProjectiveSpecialLinear

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.StandardType.GGFF
open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single vecElt_single_one)

open scoped MatrixGroups

structure JData {G : Type} [Group G] (n : ℕ) (L : Subgroup G) (z : Fin 3 → ↥L)
    (J : Subgroup G) : Prop where
  le : J ≤ L
  inf : Subgroup.zpowers (GGFF.zs z 0) ⊓ J = ⊥
  cen : L ⊓ Subgroup.centralizer ({GGFF.zs z 0} : Set G) = Subgroup.zpowers (GGFF.zs z 0) ⊔ J
  comm : ∀ x ∈ J, x * GGFF.zs z 0 = GGFF.zs z 0 * x
  z₁ : GGFF.zs z 1 ∈ J
  z₂ : GGFF.zs z 2 ∈ J
  model : StatedClassicalModel ↥J .PSL (n - 1) 2 1

private abbrev mat {n : ℕ} (x : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2) := x

private theorem zmod_three_ne_zero : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by
  decide

private theorem map_centralizer_mulEquiv {H H' : Type} [Group H] [Group H'] (f : H ≃* H')
    (s : Set H) : (Subgroup.centralizer s).map f.toMonoidHom =
      Subgroup.centralizer (f '' s) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image s f.toMonoidHom
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro h hh
    have h1 := hy (f h) ⟨h, hh, rfl⟩
    apply f.injective
    simpa using h1

private theorem wt_image_eq_one {H : Type} [Group H] {T T' : Fin 3 → H}
    (hT : Model H T) (hT' : Model H T')
    (f : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)) (hf : ∀ v, vecElt T' v = vecElt T (f v))
    (hfi : Function.Injective f) (hfne : ∀ v, v ≠ 0 → f v ≠ 0)
    (hconj : ∀ v w, IsConj (vecElt T (f v)) (vecElt T (f w)) ↔
      IsConj (vecElt T' v) (vecElt T' w))
    (u : Fin 3 → ZMod 3) (hu : u ≠ 0) (hwu : wt u = 1) : wt (f u) = 1 := by
  have hf0 : f 0 = 0 := hT.vecElt_inj (by rw [← hf 0, vecElt_zero, vecElt_zero])
  have key : ∀ w, w ≠ 0 → (wt (f w) = wt (f u) ↔ wt w = 1) := fun w hw =>
    (hT.conj_iff (f w) (f u) (hfne w hw) (hfne u hu)).symm.trans
      ((hconj w u).trans ((hT'.conj_iff w u hw hu).trans (by rw [hwu])))
  have hset : (Finset.univ.filter fun w => wt w = wt (f u)) =
      (Finset.univ.filter fun w => wt w = 1).image f := by
    ext w'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hw'
      obtain ⟨w, rfl⟩ := Finite.surjective_of_injective hfi w'
      have hw : w ≠ 0 := fun h0 => by
        rw [h0, hf0] at hw'
        exact hfne u hu ((wt_eq_zero_iff _).mp (hw'.symm.trans ((wt_eq_zero_iff 0).mpr rfl)))
      exact ⟨w, (key w hw).mp hw', rfl⟩
    · rintro ⟨w, hw1, rfl⟩
      have hw : w ≠ 0 := fun h0 => by
        rw [h0, (wt_eq_zero_iff 0).mpr rfl] at hw1
        exact absurd hw1 (by decide)
      exact (key w hw).mpr hw1
  have hcard := congrArg Finset.card hset
  rw [Finset.card_image_of_injective _ hfi, card_wt, card_wt] at hcard
  have hne : wt (f u) ≠ 0 := fun h0 => hfne u hu ((wt_eq_zero_iff _).mp h0)
  have hle : wt (f u) ≤ 3 := (Finset.card_filter_le _ _).trans (by simp)
  interval_cases hx : wt (f u) <;> simp_all

private theorem exists_monomial_of_model {H : Type} [Group H] {T T' : Fin 3 → H}
    (hT : Model H T) (hT' : Model H T') (hmem : ∀ i, T' i ∈ tor T) :
    ∃ (j : Fin 3 → Fin 3) (ε : Fin 3 → ZMod 3), Function.Injective j ∧ (∀ i, ε i ≠ 0) ∧
      ∀ i, T' i = T (j i) ^ (ε i).val := by
  have hsub : tor T' ≤ tor T :=
    (Subgroup.closure_le (K := tor T)).mpr (by rintro x ⟨i, rfl⟩; exact hmem i)
  choose f hf using fun v => (hT.mem_tor').mp (hsub (vecElt_mem_tor T' v))
  have hfi : Function.Injective f := fun v w hvw =>
    hT'.vecElt_inj (by rw [hf v, hvw, ← hf w])
  have hfne : ∀ v, v ≠ 0 → f v ≠ 0 := fun v hv h0 =>
    hv (hT'.inj v (by rw [hf v, h0, vecElt_zero]))
  have hconj : ∀ v w, IsConj (vecElt T (f v)) (vecElt T (f w)) ↔
      IsConj (vecElt T' v) (vecElt T' w) := fun v w => by
    rw [hf v, hf w]
  have hsingle : ∀ i : Fin 3, (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) ≠ 0 := by
    intro i h; have := congrFun h i; simp at this
  have hwt : ∀ i : Fin 3, wt (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) = 1 := by
    intro i; fin_cases i <;> decide
  choose j ε hε0 hεe using fun i =>
    eq_single_of_wt_eq_one (f (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3))
      (wt_image_eq_one hT hT' f hf hfi hfne hconj
        (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) (hsingle i) (hwt i))
  have hi : ∀ i, T' i = T (j i) ^ (ε i).val := fun i => by
    rw [← vecElt_single_one (z := T') i, hf, hεe i, vecElt_single]
  have ha' : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := zmod_three_ne_zero
  refine ⟨j, ε, ?_, hε0, hi⟩
  intro i i' hjj
  apply hT'.eq_of_z_eq
  have hi2 := hi i'
  rw [← hjj] at hi2
  rcases ha' (ε i) (hε0 i) with h1 | h1 <;> rcases ha' (ε i') (hε0 i') with h2 | h2
  · left; rw [hi i, hi2, h1, h2, ZMod.val_one, pow_one]
  · right
    rw [hi i, hi2, h1, h2, ZMod.val_one, (show (2 : ZMod 3).val = 2 from rfl), pow_one,
      eq_inv_iff_mul_eq_one, ← pow_succ']
    exact hT.pow_z (j i)
  · right
    rw [hi i, hi2, h1, h2, ZMod.val_one, (show (2 : ZMod 3).val = 2 from rfl),
      eq_inv_iff_mul_eq_one, pow_one, ← pow_succ]
    exact hT.pow_z (j i)
  · left; rw [hi i, hi2, h1, h2, (show (2 : ZMod 3).val = 2 from rfl)]

private theorem finrank_ker_eq_of_card {N : ℕ}
    (P : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin N → ZMod 2))
    (hcard : (Finset.univ.filter fun v : Fin N → ZMod 2 => P v = 0).card = 2 ^ (N - 2)) :
    Module.finrank (ZMod 2) (LinearMap.ker P) = N - 2 := by
  have h1 : Nat.card ↥(LinearMap.ker P) = Nat.card {v : Fin N → ZMod 2 // P v = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => LinearMap.mem_ker))
  have h2 : Nat.card {v : Fin N → ZMod 2 // P v = 0} =
      (Finset.univ.filter fun v : Fin N → ZMod 2 => P v = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfin : Nat.card ↥(LinearMap.ker P) = 2 ^ (N - 2) := by rw [h1, h2, hcard]
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker P)
  rw [Nat.card_zmod] at h
  rw [h] at hfin
  exact Nat.pow_right_injective (by norm_num) hfin

private theorem orderOf_pow_zmod_three {m : ℕ} {T : Fin 3 → SL(m + 2, ZMod 2)}
    {a : Fin 3} (h : orderOf (T a) = 3) {ε : ZMod 3} (hε : ε ≠ 0) :
    orderOf (T a ^ (ε).val) = 3 := by
  have h3 : (T a) ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one (T a)
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  · intro h1
    have hk : (ε).val = 1 ∨ (ε).val = 2 := by
      rcases zmod_three_ne_zero ε hε with hε1 | hε2
      · left; rw [hε1]; decide
      · right; rw [hε2]; decide
    rcases hk with hk | hk
    · rw [hk, pow_one] at h1
      rw [h1, orderOf_one] at h
      omega
    · rw [hk] at h1
      have hdvd : orderOf (T a) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [h] at hdvd
      omega

private theorem W6_orderOf (a : Fin 3) : orderOf (W6.T a) = 3 := by
  apply orderOf_eq_prime
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel

private theorem W6_finrank (a : Fin 3) (ε : ZMod 3) (hε : ε ≠ 0) :
    Module.finrank (ZMod 2)
      (LinearMap.ker (Matrix.toLin' (mat ((W6.T a) ^ (ε).val) - 1))) = 4 := by
  apply finrank_ker_eq_of_card
  rcases zmod_three_ne_zero (ε) hε with h1 | h1
  · rw [h1]; fin_cases a <;> decide +kernel
  · rw [h1]; fin_cases a <;> decide +kernel

private theorem W6_comm (a b : Fin 3) : W6.T b * W6.T a = W6.T a * W6.T b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem W6_mul_sub (a b : Fin 3) (h : a ≠ b) (εa εb : ZMod 3)
    (hεa : εa ≠ 0) (hεb : εb ≠ 0) :
    (mat ((W6.T b) ^ (εb).val) - 1) * (mat ((W6.T a) ^ (εa).val) - 1) = 0 := by
  rcases zmod_three_ne_zero (εa) hεa with rfl | rfl <;>
    rcases zmod_three_ne_zero (εb) hεb with rfl | rfl <;>
    fin_cases a <;> fin_cases b <;> simp_all <;> decide +kernel

private theorem W7_orderOf (a : Fin 3) : orderOf (W7.T a) = 3 := by
  apply orderOf_eq_prime
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel

private theorem W7_finrank (a : Fin 3) (ε : ZMod 3) (hε : ε ≠ 0) :
    Module.finrank (ZMod 2)
      (LinearMap.ker (Matrix.toLin' (mat ((W7.T a) ^ (ε).val) - 1))) = 5 := by
  apply finrank_ker_eq_of_card
  rcases zmod_three_ne_zero (ε) hε with h1 | h1
  · rw [h1]; fin_cases a <;> decide +kernel
  · rw [h1]; fin_cases a <;> decide +kernel

private theorem W7_comm (a b : Fin 3) : W7.T b * W7.T a = W7.T a * W7.T b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem W7_mul_sub (a b : Fin 3) (h : a ≠ b) (εa εb : ZMod 3)
    (hεa : εa ≠ 0) (hεb : εb ≠ 0) :
    (mat ((W7.T b) ^ (εb).val) - 1) * (mat ((W7.T a) ^ (εa).val) - 1) = 0 := by
  rcases zmod_three_ne_zero (εa) hεa with rfl | rfl <;>
    rcases zmod_three_ne_zero (εb) hεb with rfl | rfl <;>
    fin_cases a <;> fin_cases b <;> simp_all <;> decide +kernel

private theorem aux_transport {G : Type} [Group G] {m : ℕ} {L : Subgroup G} {z : Fin 3 → ↥L}
    (e : ↥L ≃* SL(m + 2, ZMod 2))
    (g₀ X Y1 Y2 : SL(m + 2, ZMod 2))
    (hX : orderOf X = 3)
    (hfix : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' (mat X - 1))) = m)
    (hY1c : Y1 * X = X * Y1) (hY1f : (mat Y1 - 1) * (mat X - 1) = 0)
    (hY2c : Y2 * X = X * Y2) (hY2f : (mat Y2 - 1) * (mat X - 1) = 0)
    (hXg : X = g₀⁻¹ * e (z 0) * g₀) (hY1g : Y1 = g₀⁻¹ * e (z 1) * g₀)
    (hY2g : Y2 = g₀⁻¹ * e (z 2) * g₀) :
    ∃ J : Subgroup G, J ≤ L ∧ Subgroup.zpowers (GGFF.zs z 0) ⊓ J = ⊥ ∧
      L ⊓ Subgroup.centralizer ({GGFF.zs z 0} : Set G) =
        Subgroup.zpowers (GGFF.zs z 0) ⊔ J ∧
      (∀ x ∈ J, x * GGFF.zs z 0 = GGFF.zs z 0 * x) ∧
      GGFF.zs z 1 ∈ J ∧ GGFF.zs z 2 ∈ J ∧ Nonempty (↥J ≃* SL(m, ZMod 2)) := by
  obtain ⟨JX, hJXle, hJXinf, hJXcen, hJXeq, hJXmem⟩ :=
    CFSG.SLCentralizerOrderThree.exists_subgroup_centralizer_eq X hX hfix
  let ψ : SL(m + 2, ZMod 2) ≃* ↥L := (MulAut.conj g₀).trans e.symm
  have hψX : ψ X = z 0 := by
    have h : g₀ * X * g₀⁻¹ = e (z 0) := by rw [hXg]; group
    simp only [ψ, MulEquiv.trans_apply, MulAut.conj_apply, h]
    simp
  have hψY1 : ψ Y1 = z 1 := by
    have h : g₀ * Y1 * g₀⁻¹ = e (z 1) := by rw [hY1g]; group
    simp only [ψ, MulEquiv.trans_apply, MulAut.conj_apply, h]
    simp
  have hψY2 : ψ Y2 = z 2 := by
    have h : g₀ * Y2 * g₀⁻¹ = e (z 2) := by rw [hY2g]; group
    simp only [ψ, MulEquiv.trans_apply, MulAut.conj_apply, h]
    simp
  let φ : SL(m + 2, ZMod 2) →* G := L.subtype.comp ψ.toMonoidHom
  have hφinj : Function.Injective φ := L.subtype_injective.comp ψ.injective
  have hφX : φ X = GGFF.zs z 0 := by simp [φ, hψX]
  have hφY1 : φ Y1 = GGFF.zs z 1 := by simp [φ, hψY1]
  have hφY2 : φ Y2 = GGFF.zs z 2 := by simp [φ, hψY2]
  have hY1C : Y1 ∈ Subgroup.centralizer ({X} : Set SL(m + 2, ZMod 2)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hY1c.symm
  have hY2C : Y2 ∈ Subgroup.centralizer ({X} : Set SL(m + 2, ZMod 2)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hY2c.symm
  have hfix_range : ∀ (Y : SL(m + 2, ZMod 2)),
      Y ∈ Subgroup.centralizer ({X} : Set SL(m + 2, ZMod 2)) →
      (mat Y - 1) * (mat X - 1) = 0 →
      ∀ v ∈ LinearMap.range (Matrix.toLin' (mat X - 1)), (mat Y).mulVec v = v := by
    intro Y _ hYf v hv
    obtain ⟨u, rfl⟩ := hv
    have h0 : (mat Y - 1).mulVec ((mat X - 1).mulVec u) = 0 := by
      rw [Matrix.mulVec_mulVec, hYf, Matrix.zero_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0
  have hY1mem : Y1 ∈ JX := (hJXmem Y1 hY1C).mpr (hfix_range Y1 hY1C hY1f)
  have hY2mem : Y2 ∈ JX := (hJXmem Y2 hY2C).mpr (hfix_range Y2 hY2C hY2f)
  let J : Subgroup G := JX.map φ
  have hJle : J ≤ L := by
    rintro x ⟨y, hy, rfl⟩
    exact (ψ y).2
  have hinf : Subgroup.zpowers (GGFF.zs z 0) ⊓ J = ⊥ := by
    have h := congrArg (fun K : Subgroup SL(m + 2, ZMod 2) => K.map φ) hJXinf
    rwa [Subgroup.map_inf _ _ _ hφinj, MonoidHom.map_zpowers, hφX, Subgroup.map_bot] at h
  have hsub : Subgroup.centralizer ({z 0} : Set ↥L) =
      (Subgroup.centralizer ({(z 0 : G)} : Set G)).subgroupOf L := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact congrArg Subtype.val (h (z 0) (by simp))
    · intro h h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact Subtype.ext (h (z 0) (by simp))
  have hcenψ : Subgroup.centralizer ({z 0} : Set ↥L) =
      Subgroup.zpowers (z 0) ⊔ JX.map ψ.toMonoidHom := by
    have h1 : (Subgroup.zpowers X).map ψ.toMonoidHom = Subgroup.zpowers (ψ X) := by
      rw [MonoidHom.map_zpowers]; rfl
    have h := congrArg (fun K : Subgroup SL(m + 2, ZMod 2) => K.map ψ.toMonoidHom) hJXcen
    rw [map_centralizer_mulEquiv, Set.image_singleton, Subgroup.map_sup, h1, hψX] at h
    exact h
  have hcen : L ⊓ Subgroup.centralizer ({GGFF.zs z 0} : Set G) =
      Subgroup.zpowers (GGFF.zs z 0) ⊔ J := by
    have h := congrArg (fun K : Subgroup ↥L => K.map L.subtype) hcenψ
    rw [hsub, Subgroup.subgroupOf_map_subtype, Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_map] at h
    rw [show GGFF.zs z 0 = (z 0 : G) from rfl, inf_comm]
    simpa [J, φ] using h
  have hcomm : ∀ x ∈ J, x * GGFF.zs z 0 = GGFF.zs z 0 * x := by
    rintro x ⟨y, hy, rfl⟩
    have hyc := hJXle hy
    rw [Subgroup.mem_centralizer_iff] at hyc
    have h1 := hyc X (by simp)
    rw [← hφX]
    rw [← map_mul, ← map_mul, h1]
  refine ⟨J, hJle, hinf, hcen, hcomm, ?_, ?_, ?_⟩
  · rw [← hφY1]
    exact Subgroup.mem_map_of_mem φ hY1mem
  · rw [← hφY2]
    exact Subgroup.mem_map_of_mem φ hY2mem
  · obtain ⟨eJX⟩ := hJXeq
    exact ⟨(Subgroup.equivMapOfInjective JX φ hφinj).symm.trans eJX⟩

private theorem exists_J_standard {G : Type} [Group G] {m : ℕ} {L : Subgroup G} {z : Fin 3 → ↥L}
    (e : ↥L ≃* SL(m + 2, ZMod 2)) (hL : GGFF.Model ↥L z)
    (T : Fin 3 → SL(m + 2, ZMod 2)) (hT : GGFF.Model SL(m + 2, ZMod 2) T)
    (hTord : ∀ a : Fin 3, orderOf (T a) = 3)
    (hTfix : ∀ (a : Fin 3) (ε : ZMod 3), ε ≠ 0 →
      Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' (mat (T a ^ (ε).val) - 1))) = m)
    (hTcomm : ∀ a b : Fin 3, T b * T a = T a * T b)
    (hTsub : ∀ (a b : Fin 3), a ≠ b → ∀ (εa εb : ZMod 3), εa ≠ 0 → εb ≠ 0 →
      (mat (T b ^ (εb).val) - 1) * (mat (T a ^ (εa).val) - 1) = 0) :
    ∃ J : Subgroup G, J ≤ L ∧ Subgroup.zpowers (GGFF.zs z 0) ⊓ J = ⊥ ∧
      L ⊓ Subgroup.centralizer ({GGFF.zs z 0} : Set G) = Subgroup.zpowers (GGFF.zs z 0) ⊔ J ∧
      (∀ x ∈ J, x * GGFF.zs z 0 = GGFF.zs z 0 * x) ∧
      GGFF.zs z 1 ∈ J ∧ GGFF.zs z 2 ∈ J ∧ Nonempty (↥J ≃* SL(m, ZMod 2)) := by
  let z' : Fin 3 → SL(m + 2, ZMod 2) := fun i => e (z i)
  have hz' : GGFF.Model SL(m + 2, ZMod 2) z' := hL.ofMulEquiv e
  obtain ⟨g₀, hg₀⟩ := hT.torus (tor z') hz'.isElemAbelian_tor' hz'.card_tor'
  let T' : Fin 3 → SL(m + 2, ZMod 2) := fun i => g₀⁻¹ * z' i * g₀
  have hT' : GGFF.Model SL(m + 2, ZMod 2) T' := by
    have h := hz'.conj g₀⁻¹
    simpa [T'] using h
  have hmem : ∀ i, T' i ∈ tor T := by
    intro i
    have hz'i : z' i ∈ tor z' := Subgroup.subset_closure (Set.mem_range_self i)
    obtain ⟨v, hv⟩ := (hg₀ (z' i)).mp hz'i
    have hTi : T' i = vecElt T v := by
      simp only [T']
      rw [hv]
      group
    rw [hTi]
    exact vecElt_mem_tor T v
  obtain ⟨j, ε, hjinj, hε0, hT'i⟩ := exists_monomial_of_model hT hT' hmem
  let X := T (j 0) ^ (ε 0).val
  let Y1 := T (j 1) ^ (ε 1).val
  let Y2 := T (j 2) ^ (ε 2).val
  have hX : orderOf X = 3 := orderOf_pow_zmod_three (hTord (j 0)) (hε0 0)
  have hfix : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' (mat X - 1))) = m :=
    hTfix (j 0) (ε 0) (hε0 0)
  have hY1c : Y1 * X = X * Y1 := (Commute.pow_pow (hTcomm (j 0) (j 1)) _ _).eq
  have hY2c : Y2 * X = X * Y2 := (Commute.pow_pow (hTcomm (j 0) (j 2)) _ _).eq
  have hY1f : (mat Y1 - 1) * (mat X - 1) = 0 :=
    hTsub (j 0) (j 1) (fun hjj => by have h := hjinj hjj; exact absurd h (by decide))
      (ε 0) (ε 1) (hε0 0) (hε0 1)
  have hY2f : (mat Y2 - 1) * (mat X - 1) = 0 :=
    hTsub (j 0) (j 2) (fun hjj => by have h := hjinj hjj; exact absurd h (by decide))
      (ε 0) (ε 2) (hε0 0) (hε0 2)
  have hXg : X = g₀⁻¹ * e (z 0) * g₀ := by
    rw [show X = T (j 0) ^ (ε 0).val from rfl, ← hT'i 0]
  have hY1g : Y1 = g₀⁻¹ * e (z 1) * g₀ := by
    rw [show Y1 = T (j 1) ^ (ε 1).val from rfl, ← hT'i 1]
  have hY2g : Y2 = g₀⁻¹ * e (z 2) * g₀ := by
    rw [show Y2 = T (j 2) ^ (ε 2).val from rfl, ← hT'i 2]
  exact aux_transport e g₀ X Y1 Y2 hX hfix hY1c hY1f hY2c hY2f hXg hY1g hY2g

private theorem statedClassicalModel_of_mulEquiv_SL {m : ℕ} (hm : 3 ≤ m) {X : Type} [Group X]
    (e : X ≃* SL(m, ZMod 2)) : StatedClassicalModel X .PSL m 2 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two hm
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m (ZMod 2)))

theorem exists_jData {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : ∃ J : Subgroup G, JData n L z J := by
  rcases h.hypA.n_cases with rfl | rfl
  · obtain ⟨e⟩ :=
      CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl h.hypA.model
    obtain ⟨J, hle, hinf, hcen, hcomm, hz1, hz2, hmodel⟩ :=
      exists_J_standard e h.model W6.T GGFF.model_SL6 W6_orderOf W6_finrank W6_comm W6_mul_sub
    refine ⟨J, hle, hinf, hcen, hcomm, hz1, hz2, ?_⟩
    obtain ⟨eJ⟩ := hmodel
    exact statedClassicalModel_of_mulEquiv_SL (by norm_num) eJ
  · obtain ⟨e⟩ :=
      CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl h.hypA.model
    obtain ⟨J, hle, hinf, hcen, hcomm, hz1, hz2, hmodel⟩ :=
      exists_J_standard e h.model W7.T GGFF.model_SL7 W7_orderOf W7_finrank W7_comm W7_mul_sub
    refine ⟨J, hle, hinf, hcen, hcomm, hz1, hz2, ?_⟩
    obtain ⟨eJ⟩ := hmodel
    exact statedClassicalModel_of_mulEquiv_SL (by norm_num) eJ

end CFSG.StandardType.FF81.PropOne

end
