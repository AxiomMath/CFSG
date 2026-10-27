module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.Open.LocalVocabulary
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Sylow
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] Subgroup.pointwiseMulAction

public section

namespace CFSG.StandardType.GGFF.Setting

open SettingCore

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor conjBy)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

private theorem conjAut_pow_apply (h : Setting b K z) {r : G} (hr : r ∈ Cen b) (m : ℕ) (y : K) :
    ((((conjAut (h.nor r hr)) ^ m) y : K) : G) = r ^ m * (y : G) * (r ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply]
    calc (((conjAut (h.nor r hr)) (((conjAut (h.nor r hr)) ^ m) y) : K) : G)
        = r * ((((conjAut (h.nor r hr)) ^ m) y : K) : G) * r⁻¹ := by rw [conjAut_apply]
      _ = r * (r ^ m * (y : G) * (r ^ m)⁻¹) * r⁻¹ := by rw [ih]
      _ = r ^ (m + 1) * (y : G) * (r ^ (m + 1))⁻¹ := by
            rw [pow_succ]
            group

omit [Finite G] in
private theorem mem_cenS_Bt_of_comm (h : Setting b K z) {d : G} (hdb : d ∈ Cen b)
    (hz : ∀ i, d * zs z i = zs z i * d) : d ∈ CenS (Bt b z) := by
  rw [Bt_eq_closure]
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hle : Subgroup.closure ({b, zs z 0, zs z 1, zs z 2} : Set G) ≤
      Subgroup.centralizer ({d} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hdb).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hz 0).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hz 1).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hz 2).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

omit [Finite G] in
private theorem mem_cenS_Bt_of_cenS_K (h : Setting b K z) {d : G} (hdb : d ∈ Cen b)
    (hdK : d ∈ CenS K) : d ∈ CenS (Bt b z) :=
  mem_cenS_Bt_of_comm h hdb fun i =>
    (Subgroup.mem_centralizer_iff.mp hdK (zs z i) (zs_mem z i)).symm



omit [Finite G] in
private theorem map_smul_subgroup {C : Subgroup G} (H : Subgroup C) (c : C) :
    (MulAut.conj c • H).map C.subtype = MulAut.conj (c : G) • (H.map C.subtype) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨z, hz, hzy⟩ := (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj c) H).mp hy
    refine ⟨(z : G), Subgroup.mem_map_of_mem C.subtype hz, ?_⟩
    rw [← hyx, ← hzy]
    rfl
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    refine ⟨(MulAut.conj c) w, ?_, ?_⟩
    · exact (Subgroup.mem_smul_pointwise_iff_exists _ _ H).mpr ⟨w, hw, rfl⟩
    · rw [← hzx, ← hwz]
      rfl

omit [Finite G] in
private theorem conj_mem_cenS_of_mem_nor {H : Subgroup G} {n x : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) (hx : x ∈ Subgroup.centralizer (H : Set G)) :
    n * x * n⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  have hh' : n⁻¹ * h * n ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) h).mp hh
    simpa using this
  have hcomm := Subgroup.mem_centralizer_iff.mp hx (n⁻¹ * h * n) hh'
  calc h * (n * x * n⁻¹) = n * ((n⁻¹ * h * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * h * n)) * n⁻¹ := by rw [hcomm]
    _ = (n * x * n⁻¹) * h := by group

private theorem exists_sylow_conj {C : Subgroup G} (P : Sylow 2 C) {τ : G}
    (hτC : τ ∈ Subgroup.normalizer (C : Set G)) :
    ∃ c : C, MulAut.conj (c : G) • ((P : Subgroup C).map C.subtype) =
      conjBy τ ((P : Subgroup C).map C.subtype) := by
  let σ : MulAut C := conjAut fun k hk => (Subgroup.mem_normalizer_iff.mp hτC k).mp hk
  let Pτ : Sylow 2 C := Sylow.mapSurjective (f := σ.toMonoidHom) σ.surjective P
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P Pτ
  refine ⟨c, ?_⟩
  have hsm : ((c • P : Sylow 2 C) : Subgroup C) = ((Pτ : Sylow 2 C) : Subgroup C) := by
    rw [hc]
  have hPτcoe : (Pτ : Subgroup C) = (P : Subgroup C).map σ.toMonoidHom :=
    Sylow.coe_mapSurjective (f := σ.toMonoidHom) σ.surjective P
  rw [Sylow.coe_subgroup_smul, hPτcoe] at hsm
  have hsmG := congrArg (fun H : Subgroup C => H.map C.subtype) hsm
  rw [map_smul_subgroup] at hsmG
  have hσcoe : C.subtype.comp σ.toMonoidHom = (MulAut.conj τ).toMonoidHom.comp C.subtype := by
    ext y
    change ((σ y : C) : G) = τ * (y : G) * τ⁻¹
    rw [show σ y = conjAut (fun k hk => (Subgroup.mem_normalizer_iff.mp hτC k).mp hk) y from rfl,
      conjAut_apply]
  rw [hsmG, Subgroup.map_map, hσcoe, ← Subgroup.map_map]

omit [Finite G] in
private theorem cenS_Bt_le_cen (_h : Setting b K z) : CenS (Bt b z) ≤ Cen b := by
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hx b (b_mem_Bt b z)).symm

private def conjHom (h : Setting b K z) : CenS (Bt b z) →* MulAut K where
  toFun c := conjAut (h.nor c (cenS_Bt_le_cen h c.2))
  map_one' := by
    ext y
    simp only [MulAut.one_apply, conjAut_apply, Subgroup.coe_one]
    group
  map_mul' c d := by
    ext y
    simp only [MulAut.mul_apply, conjAut_apply, Subgroup.coe_mul]
    group

private theorem conjHom_apply (h : Setting b K z) (c : CenS (Bt b z)) (y : K) :
    ((conjHom h c y : K) : G) = (c : G) * y * (c : G)⁻¹ :=
  rfl

omit [Finite G] in
private theorem eq_one_of_inner_of_two_pow (h : Setting b K z) (hN : ModelN K z)
    {α : MulAut K} (hfix : ∀ i, α (z i) = z i) (hpow : ∃ n, α ^ 2 ^ n = 1)
    {k : K} (hk : α = MulAut.conj k) : α = 1 := by
  obtain ⟨n, hn⟩ := hpow
  have hkpow : k ^ 2 ^ n = 1 := by
    apply h.model.eq_one_of_forall_comm
    intro y
    have hconj : MulAut.conj (k ^ 2 ^ n) = 1 := by
      rw [map_pow, ← hk, hn]
    have h1 := congrArg (fun β : MulAut K => ((β y : K) : G)) hconj
    simp only [MulAut.one_apply, MulAut.conj_apply] at h1
    have h1K : k ^ 2 ^ n * y * (k ^ 2 ^ n)⁻¹ = y := by
      apply Subtype.ext
      simpa using h1
    calc k ^ 2 ^ n * y = (k ^ 2 ^ n * y * (k ^ 2 ^ n)⁻¹) * k ^ 2 ^ n := by group
      _ = y * k ^ 2 ^ n := by rw [h1K]
  have hkcomm : ∀ i, k * z i = z i * k := fun i => by
    have h1 : (MulAut.conj k) (z i) = z i := by rw [← hk]; exact hfix i
    rw [MulAut.conj_apply] at h1
    calc k * z i = (k * z i * k⁻¹) * k := by group
      _ = z i * k := by rw [h1]
  obtain ⟨v, hv⟩ := hN.cen k hkcomm
  have hk3 : k ^ 3 = 1 := by
    have hmem : k ∈ tor z := hv ▸ vecElt_mem_tor z v
    exact h.model.isElemAbelian_tor'.2 k hmem
  have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
  have hdvd3 : orderOf k ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hk3
  have hdvd2 : orderOf k ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hkpow
  have hdvd1 : orderOf k ∣ 1 := by
    have hg := Nat.dvd_gcd hdvd3 hdvd2
    rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
  have hk1 : k = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  rw [hk, hk1, map_one]

omit [Finite G] in
private theorem inf_centralizer_singleton_le_of_pow {a g : G} {Q : Subgroup G}
    (k : ℕ) (hg : g = a ^ k) :
    Q ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Q ⊓ Subgroup.centralizer ({g} : Set G) := by
  intro x hx
  rw [Subgroup.mem_inf] at hx ⊢
  refine ⟨hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  have hxa : a * x = x * a := hx.2 a (by simp)
  rw [hg]
  exact (Commute.pow_left (show Commute a x from hxa) k).eq

theorem cenB_two_eq_bot (h : Setting b K z) (hN : ModelN K z) (hchar : CFSG.Open.IsCharTwoType G)
    {τ : G} (hτ : τ ∈ Nor (Bt b z)) (hτb : τ * b * τ⁻¹ = b * zetaOf (zs z) ^ 2)
    (hτζ : τ * zetaOf (zs z) * τ⁻¹ = zetaOf (zs z)) :
    ∀ S : Subgroup G, S ≤ CenS (Bt b z) → IsPGroup 2 S → S = ⊥ := by
  intro S hSC hSp
  by_contra hSne
  classical
  let C : Subgroup G := CenS (Bt b z)
  let S' : Subgroup C := S.subgroupOf C
  have hS'p : IsPGroup 2 S' := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
  obtain ⟨P, hS'P⟩ := hS'p.exists_le_sylow
  have hS'ne : S' ≠ ⊥ := by
    intro hbot
    apply hSne
    have hmap : S'.map C.subtype = (⊥ : Subgroup G) := by rw [hbot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le hSC] at hmap
  have hPne : (P : Subgroup C) ≠ ⊥ := by
    intro hbot
    exact hS'ne (le_bot_iff.mp (hS'P.trans (le_of_eq hbot)))
  let P_G : Subgroup G := (P : Subgroup C).map C.subtype
  have hPGp : IsPGroup 2 P_G := P.isPGroup'.map C.subtype
  have hPGleC : P_G ≤ C := Subgroup.map_subtype_le _
  have hPGne : P_G ≠ ⊥ := by
    intro hbot
    apply hPne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxPG : (x : G) ∈ P_G := Subgroup.mem_map_of_mem C.subtype hx
    rw [hbot, Subgroup.mem_bot] at hxPG
    exact Subtype.ext hxPG
  have hτC : τ ∈ Subgroup.normalizer (C : Set G) :=
    mem_nor_of_conj_mem fun x hx => conj_mem_cenS_of_mem_nor hτ hx
  obtain ⟨c, hcs⟩ := exists_sylow_conj (C := C) P hτC
  have hcs' : MulAut.conj (c : G) • P_G = conjBy τ P_G := by
    simpa [P_G] using hcs
  have hnc : (c : G)⁻¹ * τ ∈ Subgroup.normalizer (P_G : Set G) := by
    refine mem_nor_of_conj_mem fun x hx => ?_
    have hxτ : τ * x * τ⁻¹ ∈ conjBy τ P_G := by
      rw [conjBy]
      exact Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hx
    rw [← hcs'] at hxτ
    obtain ⟨y, hy, hyx⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists (τ * x * τ⁻¹) (MulAut.conj (c : G)) P_G).mp hxτ
    have e : (c : G)⁻¹ * τ * x * ((c : G)⁻¹ * τ)⁻¹ = y := by
      rw [show (c : G)⁻¹ * τ * x * ((c : G)⁻¹ * τ)⁻¹ =
        (c : G)⁻¹ * (τ * x * τ⁻¹) * (c : G) by group, ← hyx, MulAut.smul_def,
        MulAut.conj_apply]
      group
    rwa [e]
  have hcN : (c : G) ∈ Nor (Bt b z) :=
    Subgroup.centralizer_le_normalizer (Bt b z : Set G) c.2
  have hτ₁N : (c : G)⁻¹ * τ ∈ Nor (Bt b z) :=
    (Nor (Bt b z)).mul_mem ((Nor (Bt b z)).inv_mem hcN) hτ
  have hccen : (c : G) ∈ Cen b := cenS_Bt_le_cen h c.2
  have hcb' : (c : G) * b = b * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hccen
  have hζBt : zetaOf (zs z) ∈ Bt b z := by
    refine tor_le_Bt b z ?_
    rw [show zetaOf (zs z) = vecElt (zs z) (fun _ => (1 : ZMod 3)) by
      simp [vecElt, zetaOf, ZMod.val_one]]
    exact vecElt_mem_tor _ _
  have hcζ : (c : G) * zetaOf (zs z) = zetaOf (zs z) * (c : G) :=
    (Subgroup.mem_centralizer_iff.mp c.2 (zetaOf (zs z)) hζBt).symm
  have hζsq : (c : G) * zetaOf (zs z) ^ 2 = zetaOf (zs z) ^ 2 * (c : G) :=
    (Commute.pow_right hcζ 2).eq
  have hbζcomm : (b * zetaOf (zs z) ^ 2) * (c : G) = (c : G) * (b * zetaOf (zs z) ^ 2) := by
    calc (b * zetaOf (zs z) ^ 2) * (c : G) = b * (zetaOf (zs z) ^ 2 * (c : G)) := by group
      _ = b * ((c : G) * zetaOf (zs z) ^ 2) := by rw [← hζsq]
      _ = (b * (c : G)) * zetaOf (zs z) ^ 2 := by group
      _ = ((c : G) * b) * zetaOf (zs z) ^ 2 := by rw [hcb']
      _ = (c : G) * (b * zetaOf (zs z) ^ 2) := by group
  have hτ₁b : (c : G)⁻¹ * τ * b * ((c : G)⁻¹ * τ)⁻¹ = b * zetaOf (zs z) ^ 2 := by
    rw [show (c : G)⁻¹ * τ * b * ((c : G)⁻¹ * τ)⁻¹ =
      (c : G)⁻¹ * (τ * b * τ⁻¹) * (c : G) by group, hτb]
    rw [show (c : G)⁻¹ * (b * zetaOf (zs z) ^ 2) * (c : G) = b * zetaOf (zs z) ^ 2 by
      calc (c : G)⁻¹ * (b * zetaOf (zs z) ^ 2) * (c : G) =
          (c : G)⁻¹ * ((b * zetaOf (zs z) ^ 2) * (c : G)) := by group
        _ = (c : G)⁻¹ * ((c : G) * (b * zetaOf (zs z) ^ 2)) := by rw [hbζcomm]
        _ = b * zetaOf (zs z) ^ 2 := by group]
  have hτ₁ζ : (c : G)⁻¹ * τ * zetaOf (zs z) * ((c : G)⁻¹ * τ)⁻¹ = zetaOf (zs z) := by
    rw [show (c : G)⁻¹ * τ * zetaOf (zs z) * ((c : G)⁻¹ * τ)⁻¹ =
      (c : G)⁻¹ * (τ * zetaOf (zs z) * τ⁻¹) * (c : G) by group, hτζ]
    rw [show (c : G)⁻¹ * zetaOf (zs z) * (c : G) = zetaOf (zs z) by
      calc (c : G)⁻¹ * zetaOf (zs z) * (c : G) = (c : G)⁻¹ * (zetaOf (zs z) * (c : G)) := by group
        _ = (c : G)⁻¹ * ((c : G) * zetaOf (zs z)) := by rw [hcζ]
        _ = zetaOf (zs z) := by group]
  let H : Subgroup G := Subgroup.normalizer (P_G : Set G)
  have hHtwo : CFSG.Open.IsTwoLocal H := ⟨P_G, hPGne, hPGp, rfl⟩
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 H
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQleH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hPGQ : P_G ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 P_G hPGp
  have hQnorm : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hτ₁H : (c : G)⁻¹ * τ ∈ H := hnc
  have hτ₁Q : (c : G)⁻¹ * τ ∈ Subgroup.normalizer (Q : Set G) := hQnorm hτ₁H
  have hbH : b ∈ H := by
    refine Subgroup.centralizer_le_normalizer (P_G : Set G) ?_
    exact Subgroup.mem_centralizer_iff.mpr fun p hp =>
      (Subgroup.mem_centralizer_iff.mp (hPGleC hp) b (b_mem_Bt b z)).symm
  have hζH : zetaOf (zs z) ∈ H := by
    refine Subgroup.centralizer_le_normalizer (P_G : Set G) ?_
    exact Subgroup.mem_centralizer_iff.mpr fun p hp =>
      (Subgroup.mem_centralizer_iff.mp (hPGleC hp) (zetaOf (zs z)) hζBt).symm
  have hziH : ∀ i, zs z i ∈ H := by
    intro i
    refine Subgroup.centralizer_le_normalizer (P_G : Set G) ?_
    refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hPGleC hp) (zs z i)
      (tor_le_Bt b z (Subgroup.subset_closure ⟨i, rfl⟩))).symm
  have hcharH := hchar H hHtwo
  have hΦfix : ∀ (s : P) (i : Fin 3), conjHom h (s : C) (z i) = z i := by
    intro s i
    apply Subtype.ext
    rw [conjHom_apply]
    have hziBt : zs z i ∈ Bt b z := tor_le_Bt b z (Subgroup.subset_closure ⟨i, rfl⟩)
    have hcomm := Subgroup.mem_centralizer_iff.mp ((s : C).2) (zs z i) hziBt
    rw [← hcomm]
    group
  have hΦpow : ∀ s : P, ∃ n, conjHom h (s : C) ^ 2 ^ n = 1 := by
    intro s
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') s
    refine ⟨n, ?_⟩
    have hs1 : (s : C) ^ 2 ^ n = 1 := by
      have h2 : ((s ^ 2 ^ n : P) : C) = 1 := by
        have h3 : s ^ 2 ^ n = 1 := by
          rw [← hn]
          exact pow_orderOf_eq_one s
        rw [h3]
        rfl
      simpa using h2
    have hpow : conjHom h (s : C) ^ 2 ^ n = 1 := by
      rw [← map_pow, hs1, map_one]
    exact hpow
  have hΦsq : ∀ s : P, conjHom h (s : C) * conjHom h (s : C) = 1 := by
    intro s
    set α : MulAut K := conjHom h (s : C) with hαdef
    have hfix : ∀ i, α (z i) = z i := hΦfix s
    have hpow : ∃ n, α ^ 2 ^ n = 1 := hΦpow s
    rcases hN.out α α with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
    · have h1 := eq_one_of_inner_of_two_pow h hN hfix hpow hk
      rw [h1, one_mul]
    · have h1 := eq_one_of_inner_of_two_pow h hN hfix hpow hk
      rw [h1, one_mul]
    · have hfix2 : ∀ i, (α * α) (z i) = z i := fun i => by
        rw [MulAut.mul_apply, hfix i, hfix i]
      have hpow2 : ∃ n, (α * α) ^ 2 ^ n = 1 := by
        obtain ⟨n, hn⟩ := hpow
        refine ⟨n, ?_⟩
        calc (α * α) ^ 2 ^ n = (α ^ 2) ^ 2 ^ n := by rw [pow_two]
          _ = α ^ (2 * 2 ^ n) := (pow_mul α 2 (2 ^ n)).symm
          _ = α ^ (2 ^ n * 2) := by rw [mul_comm]
          _ = (α ^ 2 ^ n) ^ 2 := pow_mul α (2 ^ n) 2
          _ = 1 := by rw [hn, one_pow]
      exact eq_one_of_inner_of_two_pow h hN hfix2 hpow2 hk
  have hex : ∃ σ : MulAut K, σ * σ = 1 ∧ (∀ i, σ (z i) = z i) ∧
      (∀ s : P, conjHom h (s : C) = 1 ∨ conjHom h (s : C) = σ) ∧
      (∀ n : K, (∀ s : P, conjHom h (s : C) n = n) → σ n = n) := by
    by_cases hex' : ∃ s : P, conjHom h (s : C) ≠ 1
    · obtain ⟨s₀, hs₀⟩ := hex'
      refine ⟨conjHom h (s₀ : C), hΦsq s₀, hΦfix s₀, fun s => ?_, fun n hn => hn s₀⟩
      by_cases hs : conjHom h (s : C) = 1
      · exact Or.inl hs
      · right
        have hpair : conjHom h (s : C) * conjHom h (s₀ : C) = 1 := by
          rcases hN.out (conjHom h (s : C)) (conjHom h (s₀ : C)) with
            ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
          · exact absurd (eq_one_of_inner_of_two_pow h hN (hΦfix s) (hΦpow s) hk) hs
          · exact absurd (eq_one_of_inner_of_two_pow h hN (hΦfix s₀) (hΦpow s₀) hk) hs₀
          · have hfix2 : ∀ i,
                (conjHom h (s : C) * conjHom h (s₀ : C)) (z i) = z i := fun i => by
              rw [MulAut.mul_apply, hΦfix s₀ i, hΦfix s i]
            have hpow2 : ∃ n, (conjHom h (s : C) * conjHom h (s₀ : C)) ^ 2 ^ n = 1 := by
              obtain ⟨n, hn⟩ := hΦpow (s * s₀)
              refine ⟨n, ?_⟩
              rw [show conjHom h (s : C) * conjHom h (s₀ : C) =
                conjHom h (((s * s₀ : P) : C)) by
                rw [show ((s * s₀ : P) : C) = (s : C) * (s₀ : C) from rfl, map_mul]]
              exact hn
            exact eq_one_of_inner_of_two_pow h hN hfix2 hpow2 hk
        calc conjHom h (s : C) = conjHom h (s : C) *
              (conjHom h (s₀ : C) * conjHom h (s₀ : C)) := by rw [hΦsq s₀, mul_one]
          _ = (conjHom h (s : C) * conjHom h (s₀ : C)) * conjHom h (s₀ : C) := by group
          _ = 1 * conjHom h (s₀ : C) := by rw [hpair]
          _ = conjHom h (s₀ : C) := one_mul _
    · push Not at hex'
      exact ⟨1, by simp, fun i => rfl, fun s => Or.inl (hex' s), fun n hn => rfl⟩
  obtain ⟨σ, hσsq, hσfix, hσmem, hσapp⟩ := hex
  let Fix : Subgroup K :=
    { carrier := {k | σ k = k}
      one_mem' := map_one σ
      mul_mem' := fun {a b} ha hb => by
        change σ (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        change σ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let N : Subgroup K := (Q.comap K.subtype) ⊓ Fix
  have hNp : IsPGroup 2 N := hQp.comap_subtype.to_inf_left
  have hNfix : ∀ n ∈ N, σ n = n := fun n hn => hn.2
  have hNnorm : ∀ c : K, σ c = c → ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    have hσcP : ∀ s : P, conjHom h (s : C) c = c := by
      intro s
      rcases hσmem s with h1 | h2
      · rw [h1]
        rfl
      · rw [h2]
        exact hc
    have hcP : (c : G) ∈ Subgroup.centralizer (P_G : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
      obtain ⟨x, hx, hxp⟩ := Subgroup.mem_map.mp hp
      have h4 : ((conjHom h (x : C) c : K) : G) = (c : G) := by
        have h5 := congrArg (fun y : K => (y : G)) (hσcP ⟨x, hx⟩)
        simpa using h5
      rw [conjHom_apply] at h4
      have h3 : (x : G) * (c : G) = (c : G) * (x : G) := by
        calc (x : G) * (c : G) = ((x : G) * (c : G) * (x : G)⁻¹) * (x : G) := by group
          _ = (c : G) * (x : G) := by rw [h4]
      have hxp' : (x : G) = p := hxp
      rw [hxp'] at h3
      exact h3
    have hcH : (c : G) ∈ H := Subgroup.centralizer_le_normalizer (P_G : Set G) hcP
    have hcQ : (c : G) ∈ Subgroup.normalizer (Q : Set G) := hQnorm hcH
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_comap.mpr (by
        have h1 := (Subgroup.mem_normalizer_iff.mp hcQ (n : G)).mp (show (n : G) ∈ Q from hn.1)
        simpa using h1)
    · change σ (c * n * c⁻¹) = c * n * c⁻¹
      rw [map_mul, map_mul, map_inv, hc, hNfix n hn]
  have hNbot : N = ⊥ := hN.o2 σ hσsq hσfix N hNp hNfix hNnorm
  have hQK : Q ⊓ K = ⊥ := by
    by_contra hne
    let W : Subgroup G := Q ⊓ Cen b
    have hWp : IsPGroup 2 W := hQp.to_inf_left
    have hPW : P_G ≤ W := fun p hp => ⟨hPGQ hp, cenS_Bt_le_cen h (hPGleC hp)⟩
    have hWne : W ≠ ⊥ := fun hbot => hPGne (le_bot_iff.mp (hPW.trans (le_of_eq hbot)))
    let M : Subgroup W := K.subgroupOf W
    have hMnormal : M.Normal := by
      refine ⟨fun m hm w => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      exact h.nor w w.2.2 m hm
    have hMne : M ≠ ⊥ := by
      intro hMbot
      apply hne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxW : x ∈ W := ⟨hx.1, h.le hx.2⟩
      have hxM : (⟨x, hxW⟩ : W) ∈ M := by
        rw [Subgroup.mem_subgroupOf]
        exact hx.2
      rw [hMbot, Subgroup.mem_bot] at hxM
      exact Subtype.ext_iff.mp hxM
    have hcenter : M ⊓ Subgroup.center W ≠ ⊥ :=
      @Group.IsNilpotent.inf_center_ne_bot_of_normal W _ (hWp.isNilpotent) M hMnormal hMne
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
    have haM : (a : W) ∈ M := (Subgroup.mem_inf.mp a.2).1
    have haZ : (a : W) ∈ Subgroup.center W := (Subgroup.mem_inf.mp a.2).2
    have haK : (a : G) ∈ K := by
      have := haM
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    let wK : K := ⟨(a : G), haK⟩
    have hwσ : σ wK = wK := by
      apply hσapp
      intro s
      apply Subtype.ext
      rw [conjHom_apply]
      change (s : G) * (a : G) * (s : G)⁻¹ = (a : G)
      have hc := Subgroup.mem_center_iff.mp haZ
        (⟨(s : G), hPW (Subgroup.mem_map_of_mem C.subtype s.2)⟩ : W)
      have hcG : (s : G) * (a : G) = (a : G) * (s : G) := by
        have := congrArg (fun x : W => (x : G)) hc
        simpa using this
      rw [hcG]
      group
    have hwKN : wK ∈ N := by
      refine ⟨?_, hwσ⟩
      exact Subgroup.mem_comap.mpr ((a : W).2.1)
    rw [hNbot, Subgroup.mem_bot] at hwKN
    apply ha1
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ((a : W) : G) = 1 := by
      simpa [wK] using congrArg Subtype.val hwKN
    exact h1
  have hζtor : zetaOf (zs z) ∈ tor (zs z) := by
    rw [show zetaOf (zs z) = vecElt (zs z) (fun _ => (1 : ZMod 3)) by
      simp [vecElt, zetaOf, ZMod.val_one]]
    exact vecElt_mem_tor _ _
  have hζK : zetaOf (zs z) ∈ K := tor_le z hζtor
  have hζ3 : zetaOf (zs z) ^ 3 = 1 := by
    have hmem : zetaOf z ∈ tor z := by
      rw [h.model.mem_tor']
      refine ⟨fun _ => (1 : ZMod 3), ?_⟩
      simp [vecElt, zetaOf, ZMod.val_one]
    have h3 : zetaOf z ^ 3 = 1 := h.model.isElemAbelian_tor'.2 (zetaOf z) hmem
    have h4 := congrArg (fun y : K => (y : G)) h3
    simpa [zetaOf] using h4
  have hζ4 : zetaOf (zs z) ^ 4 = zetaOf (zs z) := by
    calc zetaOf (zs z) ^ 4 = zetaOf (zs z) ^ 3 * zetaOf (zs z) := by group
      _ = 1 * zetaOf (zs z) := by rw [hζ3]
      _ = zetaOf (zs z) := one_mul _
  have hWleC : Q ⊓ Cen b ≤ C := by
    intro w hw
    refine mem_cenS_Bt_of_comm h hw.2 fun i => ?_
    have hziQ : zs z i ∈ Subgroup.normalizer (Q : Set G) := hQnorm (hziH i)
    have hcommQ : zs z i * w * (zs z i)⁻¹ * w⁻¹ ∈ Q :=
      Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hziQ w).mp hw.1) (Q.inv_mem hw.1)
    have hwzK : w * zs z i * w⁻¹ ∈ K := h.nor w hw.2 (zs z i) (zs_mem z i)
    have hcommK : zs z i * w * (zs z i)⁻¹ * w⁻¹ ∈ K := by
      rw [show zs z i * w * (zs z i)⁻¹ * w⁻¹ = zs z i * (w * zs z i * w⁻¹)⁻¹ by
        group]
      exact K.mul_mem (zs_mem z i) (K.inv_mem hwzK)
    have hcomm1 : zs z i * w * (zs z i)⁻¹ * w⁻¹ = 1 := by
      have hmem : zs z i * w * (zs z i)⁻¹ * w⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hQK]
        exact ⟨hcommQ, hcommK⟩
      simpa using hmem
    have h2 : zs z i * w = w * zs z i := by
      calc zs z i * w = (zs z i * w * (zs z i)⁻¹ * w⁻¹) * (w * zs z i) := by group
        _ = 1 * (w * zs z i) := by rw [hcomm1]
        _ = w * zs z i := one_mul _
    exact h2.symm
  have hcC : (c : G) ∈ Nor C := Subgroup.le_normalizer (H := C) c.2
  have hτ₁C : (c : G)⁻¹ * τ ∈ Nor C :=
    (Nor C).mul_mem ((Nor C).inv_mem hcC) hτC
  have hτ₁ζ2 : (c : G)⁻¹ * τ * zetaOf (zs z) ^ 2 * ((c : G)⁻¹ * τ)⁻¹ =
      zetaOf (zs z) ^ 2 := by
    have hg : (c : G)⁻¹ * τ * zetaOf (zs z) ^ 2 * ((c : G)⁻¹ * τ)⁻¹ =
        ((c : G)⁻¹ * τ * zetaOf (zs z) * ((c : G)⁻¹ * τ)⁻¹) ^ 2 := by
      simp only [pow_two]
      group
    rw [hg, hτ₁ζ]
  have hτ₁bζ2 : (c : G)⁻¹ * τ * (b * zetaOf (zs z) ^ 2) * ((c : G)⁻¹ * τ)⁻¹ =
      b * zetaOf (zs z) := by
    rw [show (c : G)⁻¹ * τ * (b * zetaOf (zs z) ^ 2) * ((c : G)⁻¹ * τ)⁻¹ =
      ((c : G)⁻¹ * τ * b * ((c : G)⁻¹ * τ)⁻¹) *
        ((c : G)⁻¹ * τ * zetaOf (zs z) ^ 2 * ((c : G)⁻¹ * τ)⁻¹) by group,
      hτ₁b, hτ₁ζ2]
    calc b * zetaOf (zs z) ^ 2 * zetaOf (zs z) ^ 2 =
        b * (zetaOf (zs z) ^ 2 * zetaOf (zs z) ^ 2) := by group
      _ = b * zetaOf (zs z) ^ 4 := by
        rw [show zetaOf (zs z) ^ 2 * zetaOf (zs z) ^ 2 = zetaOf (zs z) ^ 4 by group]
      _ = b * zetaOf (zs z) := by rw [hζ4]
  have hτ₁2b : ((c : G)⁻¹ * τ) * ((c : G)⁻¹ * τ) * b *
      (((c : G)⁻¹ * τ) * ((c : G)⁻¹ * τ))⁻¹ = b * zetaOf (zs z) := by
    calc ((c : G)⁻¹ * τ) * ((c : G)⁻¹ * τ) * b *
          (((c : G)⁻¹ * τ) * ((c : G)⁻¹ * τ))⁻¹ =
        ((c : G)⁻¹ * τ) * (((c : G)⁻¹ * τ) * b * ((c : G)⁻¹ * τ)⁻¹) *
          ((c : G)⁻¹ * τ)⁻¹ := by group
      _ = ((c : G)⁻¹ * τ) * (b * zetaOf (zs z) ^ 2) * ((c : G)⁻¹ * τ)⁻¹ := by
        rw [hτ₁b]
      _ = b * zetaOf (zs z) := hτ₁bζ2
  have hconj_step : ∀ (s t w : G), s ∈ Subgroup.normalizer (Q : Set G) →
      s ∈ Nor (Bt b z) → s * b * s⁻¹ = t → w ∈ Q ⊓ Cen t → w ∈ C := by
    intro s t w hsQ hsC hsb hw
    let u : G := s⁻¹ * w * s
    have huQ : u ∈ Q := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsQ) w).mp hw.1
      simpa [u] using h1
    have hub : u * b * u⁻¹ = b := by
      have hw2 := Subgroup.mem_centralizer_singleton_iff.mp hw.2
      calc u * b * u⁻¹ = s⁻¹ * (w * (s * b * s⁻¹) * w⁻¹) * s := by
            simp only [u]
            group
        _ = s⁻¹ * (w * t * w⁻¹) * s := by rw [hsb]
        _ = s⁻¹ * (t * w * w⁻¹) * s := by rw [hw2]
        _ = s⁻¹ * t * s := by group
        _ = b := by rw [← hsb]; group
    have huCen : u ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc u * b = (u * b * u⁻¹) * u := by group
        _ = b * u := by rw [hub]
    have huC : u ∈ C := hWleC ⟨huQ, huCen⟩
    have hwu : w = s * u * s⁻¹ := by simp only [u]; group
    rw [hwu]
    exact conj_mem_cenS_of_mem_nor hsC huC
  have hWbζ2 : Q ⊓ Cen (b * zetaOf (zs z) ^ 2) ≤ C := fun w hw =>
    hconj_step ((c : G)⁻¹ * τ) (b * zetaOf (zs z) ^ 2) w hτ₁Q hτ₁N hτ₁b hw
  have hτ₁2Q : ((c : G)⁻¹ * τ) * ((c : G)⁻¹ * τ) ∈
      Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).mul_mem hτ₁Q hτ₁Q
  have hτ₁2N : ((c : G)⁻¹ * τ) * ((c : G)⁻¹ * τ) ∈ Nor (Bt b z) :=
    (Nor (Bt b z)).mul_mem hτ₁N hτ₁N
  have hWbζ : Q ⊓ Cen (b * zetaOf (zs z)) ≤ C := fun w hw =>
    hconj_step (((c : G)⁻¹ * τ) * ((c : G)⁻¹ * τ)) (b * zetaOf (zs z)) w hτ₁2Q hτ₁2N
      hτ₁2b hw
  let D : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers (zetaOf (zs z))
  have hbζcomm : Commute b (zetaOf (zs z)) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.tor_le_cen hζtor)).symm
  have hDcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers (zetaOf (zs z)),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((hbζcomm.zpow_left i).zpow_right j).eq
  have hDab : CFSG.Assembly.IsElemAbelian 3 D := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute ?_ ?_ ?_
    · exact CFSG.Open.isElemAbelian_zpowers h.b_cube
    · exact CFSG.Open.isElemAbelian_zpowers hζ3
    · intro x hx y hy
      exact hDcomm x hx y hy
  have hDdisj : Disjoint (Subgroup.zpowers b) (Subgroup.zpowers (zetaOf (zs z))) := by
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact h.zpow_eq_one_of_mem (tor_le z ((Subgroup.zpowers_le.mpr hζtor) hx'))
  have hζorder : orderOf (zetaOf (zs z)) = 3 := by
    have hdvd : orderOf (zetaOf (zs z)) ∣ 3 := orderOf_dvd_of_pow_eq_one hζ3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
    · exfalso
      have hζne : zetaOf z ≠ 1 := by
        intro hcon
        have h2 : vecElt z (fun _ => (1 : ZMod 3)) = 1 := by
          simpa [vecElt, zetaOf, ZMod.val_one] using hcon
        have h3 : (fun _ => (1 : ZMod 3)) = 0 := h.model.inj _ h2
        have h4 : (1 : ZMod 3) = 0 := congrFun h3 0
        norm_num at h4
      apply hζne
      apply Subtype.ext
      simpa [zetaOf] using (orderOf_eq_one_iff.mp h1)
    · exact h3
  have hDcard : Nat.card D = 9 := by
    have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, h.ord]
    have hζcard : Nat.card (Subgroup.zpowers (zetaOf (zs z))) = 3 := by
      rw [Nat.card_zpowers, hζorder]
    have hζNor : zetaOf (zs z) ∈
        Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      refine mem_nor_of_conj_mem fun x hx => ?_
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← conj_zpow]
      have hbase : zetaOf (zs z) * b * (zetaOf (zs z))⁻¹ = b := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp (h.tor_le_cen hζtor)]
        group
      rw [hbase]
      exact Subgroup.zpow_mem_zpowers b i
    have hnormal : Subgroup.zpowers (zetaOf (zs z)) ≤
        Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
      Subgroup.zpowers_le.mpr hζNor
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers b) (Subgroup.zpowers (zetaOf (zs z))) hnormal hDdisj
    dsimp only [D]
    rw [hcard, hbcard, hζcard]
  have hDleH : D ≤ H := by
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr hbH
    · exact Subgroup.zpowers_le.mpr hζH
  have hDnorm : D ≤ Subgroup.normalizer (Q : Set G) := hDleH.trans hQnorm
  obtain ⟨n, hnQ⟩ := hQp.exists_card_eq
  have hQcop : Nat.Coprime 3 (Nat.card Q) := by
    rw [hnQ]
    exact (by norm_num : Nat.Coprime 3 2).pow_right n
  have hDgen : ⨆ (a : G) (_ : a ∈ D) (_ : a ≠ 1),
      Q ⊓ Subgroup.centralizer ({a} : Set G) = Q := by
    refine CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
      (p := 3) (A := D) (X := Q) (by norm_num) hDab ?_
      hDnorm hQcop
    rw [hDcard]
    norm_num
  have hCleζ : C ≤ Cen (zetaOf (zs z)) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx (zetaOf (zs z)) hζBt).symm
  have hWbC : Q ⊓ Cen b ≤ Cen (zetaOf (zs z)) := hWleC.trans hCleζ
  have hWbζC : Q ⊓ Cen (b * zetaOf (zs z)) ≤ Cen (zetaOf (zs z)) :=
    hWbζ.trans hCleζ
  have hWbζ2C : Q ⊓ Cen (b * zetaOf (zs z) ^ 2) ≤ Cen (zetaOf (zs z)) :=
    hWbζ2.trans hCleζ
  have hb4 : b ^ 4 = b := by
    calc b ^ 4 = b ^ 3 * b := by group
      _ = 1 * b := by rw [h.b_cube]
      _ = b := one_mul _
  have hQleCζ : Q ≤ Cen (zetaOf (zs z)) := by
    rw [← hDgen]
    refine iSup_le fun a => iSup_le fun haD => iSup_le fun ha1 => ?_
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hDcomm haD
    obtain ⟨I, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨J, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    set i : ℤ := I % 3 with hi
    set j : ℤ := J % 3 with hj
    have hbI : b ^ I = b ^ i := by
      rw [hi, ← zpow_mod_orderOf b I, h.ord]
      norm_num
    have hζJ : zetaOf (zs z) ^ J = zetaOf (zs z) ^ j := by
      rw [hj, ← zpow_mod_orderOf (zetaOf (zs z)) J, hζorder]
      norm_num
    have hi0 : 0 ≤ i := Int.emod_nonneg I (by norm_num)
    have hi2 : i < 3 := Int.emod_lt_of_pos I (by norm_num)
    have hj0 : 0 ≤ j := Int.emod_nonneg J (by norm_num)
    have hj2 : j < 3 := Int.emod_lt_of_pos J (by norm_num)
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    have ha_eq : a = b ^ i * zetaOf (zs z) ^ j := by
      rw [← hxy, hbI, hζJ]
    interval_cases i <;> interval_cases j <;>
      rw [ha_eq] <;>
      simp only [zpow_ofNat, pow_zero, pow_one, one_mul, mul_one]
    · exfalso
      apply ha1
      simpa using ha_eq
    · exact inf_le_right
    · have hg : zetaOf (zs z) = (zetaOf (zs z) ^ 2) ^ 2 := by
        rw [show (zetaOf (zs z) ^ 2) ^ 2 = zetaOf (zs z) ^ 4 by group, hζ4]
      exact (inf_centralizer_singleton_le_of_pow (Q := Q) 2 hg).trans inf_le_right
    · exact hWbC
    · exact hWbζC
    · exact hWbζ2C
    · have hg : b = (b ^ 2) ^ 2 := by
        rw [show (b ^ 2) ^ 2 = b ^ 4 by group, hb4]
      exact (inf_centralizer_singleton_le_of_pow (Q := Q) 2 hg).trans hWbC
    · have hg : b * zetaOf (zs z) ^ 2 = (b ^ 2 * zetaOf (zs z)) ^ 2 := by
        rw [Commute.mul_pow (hbζcomm.pow_left 2) 2]
        rw [show (b ^ 2) ^ 2 = b ^ 4 by group, hb4]
      exact (inf_centralizer_singleton_le_of_pow (Q := Q) 2 hg).trans hWbζ2C
    · have hg : b * zetaOf (zs z) = (b ^ 2 * zetaOf (zs z) ^ 2) ^ 2 := by
        rw [Commute.mul_pow (hbζcomm.pow_pow 2 2) 2]
        rw [show (b ^ 2) ^ 2 = b ^ 4 by group,
          show (zetaOf (zs z) ^ 2) ^ 2 = zetaOf (zs z) ^ 4 by group, hb4, hζ4]
      exact (inf_centralizer_singleton_le_of_pow (Q := Q) 2 hg).trans hWbζC
  have hζCQ : zetaOf (zs z) ∈ Subgroup.centralizer (Q : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    simpa [Subgroup.mem_centralizer_singleton_iff] using hQleCζ hq
  have hζQ : zetaOf (zs z) ∈ Q := hcharH ⟨hζH, hζCQ⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQp) ⟨zetaOf (zs z), hζQ⟩
  have hζord2 : orderOf (zetaOf (zs z)) = 2 ^ n := by simpa using hn
  have h3dvd : 3 ∣ 2 ^ n := by
    rw [← hζorder, hζord2]
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3dvd
  norm_num at h32

theorem exists_inner_of_cen (h : Setting b K z)
    (hS : ∀ S : Subgroup G, S ≤ CenS (Bt b z) → IsPGroup 2 S → S = ⊥)
    {c : G} (hc : c ∈ Cen b) : ∃ k ∈ K, ∀ y ∈ K, c * y * c⁻¹ = k * y * k⁻¹ := by
  classical
  have hEK : conjBy c (tor (zs z)) ≤ K := by
    rintro x ⟨y, hy, rfl⟩
    exact h.nor c hc y (tor_le z hy)
  have hEabG : CFSG.Assembly.IsElemAbelian 3 (conjBy c (tor (zs z))) :=
    (isElemAbelian_tor h.zs_pow h.zs_comm).map (MulAut.conj c).toMonoidHom
  have hEcardG : Nat.card (conjBy c (tor (zs z))) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, h.card_torG]
  let E : Subgroup K := (conjBy c (tor (zs z))).subgroupOf K
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := hEabG.subgroupOf K
  have hEcard : Nat.card E = 27 := by
    rw [show Nat.card E = Nat.card (conjBy c (tor (zs z))) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hEcardG]
  obtain ⟨g, hg⟩ := h.model.torus E hEab hEcard
  let c₁ : G := (g : G)⁻¹ * c
  have hc₁ : c₁ ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (h.le g.2)) hc
  have hB1 : ∀ x ∈ tor (zs z), c₁ * x * c₁⁻¹ ∈ tor (zs z) := by
    intro x hx
    have hxE : c * x * c⁻¹ ∈ conjBy c (tor (zs z)) := by
      rw [mem_conjBy, show c⁻¹ * (c * x * c⁻¹) * c = x by group]
      exact hx
    have hxEK : c * x * c⁻¹ ∈ K := hEK hxE
    have hxE' : (⟨c * x * c⁻¹, hxEK⟩ : K) ∈ E := by
      rw [Subgroup.mem_subgroupOf]
      exact hxE
    obtain ⟨v, hv⟩ := (hg ⟨c * x * c⁻¹, hxEK⟩).mp hxE'
    have hvG : c * x * c⁻¹ = (g : G) * vecElt (zs z) v * (g : G)⁻¹ := by
      have h1 := congrArg Subtype.val hv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← vecElt_zs] at h1
      exact h1
    have e : c₁ * x * c₁⁻¹ = (g : G)⁻¹ * (c * x * c⁻¹) * (g : G) := by
      simp only [c₁]
      group
    rw [e, hvG, show (g : G)⁻¹ * ((g : G) * vecElt (zs z) v * (g : G)⁻¹) * (g : G) =
      vecElt (zs z) v by group]
    exact vecElt_mem_tor _ v
  have hc₁b : c₁ * b * c₁⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc₁]
    group
  have hc₁N : c₁ ∈ Nor (Bt b z) :=
    mem_nor_Bt (by rw [hc₁b]; exact b_mem_Bt b z) fun i =>
      tor_le_Bt b z (hB1 _ (Subgroup.subset_closure ⟨i, rfl⟩))
  have hc₁Nor : c₁ ∈ Nor (Subgroup.zpowers b) := by
    refine mem_nor_of_conj_mem fun x hx => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hc₁b]
    exact Subgroup.zpow_mem_zpowers b j
  have hKc₁ : ∀ k ∈ K, c₁ * k * c₁⁻¹ ∈ K := fun k hk => h.nor_K hc₁Nor hk
  obtain ⟨k', hk'⟩ := h.model.exists_conj_of_aut (conjAut hKc₁) (h.tor_stable hc₁N hKc₁)
  have hk'G : ∀ i, c₁ * zs z i * c₁⁻¹ = (k' : G) * zs z i * (k' : G)⁻¹ := by
    intro i
    have h1 := congrArg Subtype.val (hk' i)
    simpa [conjAut_apply] using h1
  let c₂ : G := (k' : G)⁻¹ * c₁
  have hc₂ : c₂ ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (h.le k'.2)) hc₁
  have hc₂z : ∀ i, c₂ * zs z i * c₂⁻¹ = zs z i := by
    intro i
    have e : c₂ * zs z i * c₂⁻¹ = (k' : G)⁻¹ * (c₁ * zs z i * c₁⁻¹) * (k' : G) := by
      simp only [c₂]
      group
    rw [e, hk'G i]
    group
  have hc₂C : c₂ ∈ CenS (Bt b z) := by
    refine mem_cenS_Bt_of_comm h hc₂ fun i => ?_
    have h1 := congrArg (fun t => t * c₂) (hc₂z i)
    simpa [mul_assoc] using h1
  have hodd : Odd (orderOf c₂) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2 : 2 ∣ orderOf c₂ := even_iff_two_dvd.mp heven
    let t : G := c₂ ^ (orderOf c₂ / 2)
    have htord : orderOf t = 2 := orderOf_pow_orderOf_div (orderOf_pos c₂).ne' h2
    have htC : t ∈ CenS (Bt b z) := (CenS (Bt b z)).pow_mem hc₂C _
    have hzP : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (G := Subgroup.zpowers t) (n := 1) (by
        rw [Nat.card_zpowers, htord, pow_one])
    have hzle : Subgroup.zpowers t ≤ CenS (Bt b z) := Subgroup.zpowers_le.mpr htC
    have hbot := hS _ hzle hzP
    have ht1 : t = 1 := by
      have hmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    rw [ht1, orderOf_one] at htord
    omega
  have hpow : (conjAut (h.nor c₂ hc₂)) ^ orderOf c₂ = 1 := by
    ext y
    rw [conjAut_pow_apply h hc₂, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  obtain ⟨k₂, hk₂⟩ := h.model.inner_odd (conjAut (h.nor c₂ hc₂)) (orderOf c₂) hodd hpow
  have hk₂G : ∀ y ∈ K, c₂ * y * c₂⁻¹ = (k₂ : G) * y * (k₂ : G)⁻¹ := by
    intro y hy
    have h1 := congrArg (fun α : MulAut K => ((α ⟨y, hy⟩ : K) : G)) hk₂
    simpa [conjAut_apply, MulAut.conj_apply] using h1
  refine ⟨(g : G) * k' * k₂, K.mul_mem (K.mul_mem g.2 k'.2) k₂.2, fun y hy => ?_⟩
  have hc : c = (g : G) * k' * c₂ := by
    simp only [c₂, c₁]
    group
  calc c * y * c⁻¹ = ((g : G) * k') * (c₂ * y * c₂⁻¹) * ((g : G) * k')⁻¹ := by
        rw [hc]
        group
    _ = ((g : G) * k') * ((k₂ : G) * y * (k₂ : G)⁻¹) * ((g : G) * k')⁻¹ := by
          rw [hk₂G y hy]
    _ = ((g : G) * k' * k₂) * y * ((g : G) * k' * k₂)⁻¹ := by group

theorem mem_of_two (h : Setting b K z)
    (hS : ∀ S : Subgroup G, S ≤ CenS (Bt b z) → IsPGroup 2 S → S = ⊥)
    {c : G} (hc : c ∈ Cen b) {m : ℕ} (hcm : c ^ 2 ^ m = 1) : c ∈ K := by
  obtain ⟨k, hkK, hk⟩ := h.exists_inner_of_cen hS hc
  let u : G := (k : G)⁻¹ * c
  have huCen : u ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (h.le hkK)) hc
  have huK : ∀ y ∈ K, u * y * u⁻¹ = y := by
    intro y hy
    calc u * y * u⁻¹ = (k : G)⁻¹ * (c * y * c⁻¹) * (k : G) := by
          simp only [u]
          group
      _ = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * (k : G) := by rw [hk y hy]
      _ = y := by group
  have huCenK : u ∈ CenS K := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have h1 := huK y hy
    rw [eq_comm]
    calc u * y = (u * y * u⁻¹) * u := by group
      _ = y * u := by rw [h1]
  have huC : u ∈ CenS (Bt b z) := mem_cenS_Bt_of_cenS_K h huCen huCenK
  have hcomm : Commute k u := by
    show (k : G) * u = u * (k : G)
    exact Subgroup.mem_centralizer_iff.mp huCenK (k : G) hkK
  have hc_eq : c = (k : G) * u := by
    simp only [u]
    group
  have hpow : (k : G) ^ 2 ^ m * u ^ 2 ^ m = 1 := by
    rw [← hcomm.mul_pow, ← hc_eq, hcm]
  have huKpow : u ^ 2 ^ m ∈ K := by
    have hkpow : (k : G) ^ 2 ^ m ∈ K := K.pow_mem hkK _
    have h1 : u ^ 2 ^ m = ((k : G) ^ 2 ^ m)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact mul_eq_one_comm.mpr hpow
    rw [h1]
    exact K.inv_mem hkpow
  have hucentral : ∀ y ∈ K, u ^ 2 ^ m * y = y * u ^ 2 ^ m := by
    intro y hy
    have h1 := huK y hy
    have hcommuy : Commute u y := by
      show u * y = y * u
      calc u * y = (u * y * u⁻¹) * u := by group
        _ = y * u := by rw [h1]
    exact (hcommuy.pow_left _).eq
  have hu1 : u ^ 2 ^ m = 1 := h.eq_one_of_mem huKpow hucentral
  have hu : u = 1 := by
    have hP : IsPGroup 2 (Subgroup.zpowers u) := by
      have hdvd : orderOf u ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr hu1
      obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      refine IsPGroup.of_card (G := Subgroup.zpowers u) (n := n) ?_
      rw [Nat.card_zpowers, hn]
    have hle : Subgroup.zpowers u ≤ CenS (Bt b z) := Subgroup.zpowers_le.mpr huC
    have hbot := hS _ hle hP
    have hmem : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  rw [show c = (k : G) * u from hc_eq, hu, mul_one]
  exact hkK

end CFSG.StandardType.GGFF.Setting

end
