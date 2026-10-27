module

public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTIBasic
public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTISzInputs
public import CFSG.GroupTheory.QuasiDihedralFusion.Structure
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22Red
public import CFSG.Timmesfeld.Bridge.SchurNarrow
public import CFSG.Timmesfeld.Bridge.OddLocalRootCore
public import CFSG.RankThree.PartOne.KE.SuzukiPlane

public section

namespace CFSG.RankThree.GF2n.Tim81.CentralTI

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Blueprint
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.RankThree.GF2n.Tim81.Sec4

variable {Y : Type} [Group Y] [Finite Y] {T Z : Subgroup Y} [Z.Normal]

private theorem eq_one_or_eq_of_mem_zpowers_order_two {G : Type*} [Group G] {x y : G}
    (hx : orderOf x = 2) (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hx]
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

private theorem isPGroup_two_of_sz_quotient
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hZ : Z ≤ Subgroup.center Y) (hcenterY : Z = Subgroup.center Y)
    (hperf : commutator Y = ⊤)
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F) : IsPGroup 2 Z := by
  classical
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  let P : Sylow 2 ↥Z := Classical.choice (inferInstance : Nonempty (Sylow 2 ↥Z))
  let Z2 : Subgroup Y := (P : Subgroup ↥Z).map Z.subtype
  have hZ2le : Z2 ≤ Z := Subgroup.map_subtype_le _
  have hZ2normal : Z2.Normal := Subgroup.normal_of_le_center (hZ2le.trans hZ)
  let K := Y ⧸ Z2
  haveI : Group.IsPerfect Y := ⟨hperf⟩
  have hperfK : commutator K = ⊤ := Group.isPerfect_def.mp inferInstance
  have hcenterK : Subgroup.center K = Z.map (QuotientGroup.mk' Z2) := by
    rw [hcenterY]
    exact CFSG.Quasithin.H13.Ch4.center_quotient_eq_map Z2 (hZ2le.trans hZ)
  have hoddCenter : Odd (Nat.card (Subgroup.center K)) := by
    rw [hcenterK, CFSG.natCard_map_mk'_eq Z Z2, ← Subgroup.index_eq_card]
    have hsub : Z2.subgroupOf Z = (P : Subgroup ↥Z) := by
      ext z
      simp [Z2, Subgroup.mem_subgroupOf]
    rw [hsub]
    exact Nat.not_even_iff_odd.mp fun he => P.not_dvd_index (even_iff_two_dvd.mp he)
  have hcenterBot : Subgroup.center K = ⊥ :=
    CFSG.Timmesfeld.Bridge.OddLocal.center_eq_bot_of_sz hperfK hoddCenter
      (((QuotientGroup.quotientMulEquivOfEq hcenterK).trans
        (QuotientGroup.quotientQuotientEquivQuotient Z2 Z hZ2le)).trans
        (szModelEquivOfMulEquiv hF e))
  have hmapbot : Z.map (QuotientGroup.mk' Z2) = ⊥ := by
    rw [← hcenterK, hcenterBot]
  have hZle : Z ≤ Z2 := by
    have h := (Subgroup.map_eq_bot_iff Z).1 hmapbot
    simpa [QuotientGroup.ker_mk'] using h
  have hZeq : Z = Z2 := le_antisymm hZle hZ2le
  rw [hZeq]
  exact P.isPGroup'.map Z.subtype


private theorem exists_index_two_subgroup
    (hZ : Z ≤ Subgroup.center Y) (hZ2 : IsPGroup 2 Z) (hZne : Z ≠ ⊥) :
    ∃ (M : Subgroup ↥Z) (Z0 : Subgroup Y) (z : ↥Z),
      Z0 = M.map Z.subtype ∧ M.index = 2 ∧ Z0 ≤ Z ∧ Z0.Normal ∧ z ∉ M := by
  classical
  haveI : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ2
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk
      have hlt : 1 < Nat.card ↥Z := Finite.one_lt_card
      omega
    · exact h
  have h2dvd : 2 ∣ Nat.card ↥Z := by
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨M, hMindex⟩ := CFSG.QuasiDihedralFusion.exists_index_two_of_isPGroup hZ2 h2dvd
  let Z0 : Subgroup Y := M.map Z.subtype
  have hZ0le : Z0 ≤ Z := Subgroup.map_subtype_le _
  have hZ0normal : Z0.Normal := Subgroup.normal_of_le_center (hZ0le.trans hZ)
  haveI : Z0.Normal := hZ0normal
  let E := Y ⧸ Z0
  have hMneTop : M ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hMindex
    omega
  obtain ⟨z, hzM⟩ : ∃ z : ↥Z, z ∉ M := by
    by_contra h
    push Not at h
    exact hMneTop ((Subgroup.eq_top_iff' M).mpr h)
  exact ⟨M, Z0, z, rfl, hMindex, hZ0le, hZ0normal, hzM⟩

private theorem exists_involution_with_center_and_zpowers
    (hZ : Z ≤ Subgroup.center Y) (hperf : commutator Y = ⊤)
    {M : Subgroup ↥Z} {Z0 : Subgroup Y} [Z0.Normal] {z : ↥Z}
    (hZ0 : Z0 = M.map Z.subtype) (hMindex : M.index = 2) (hzM : z ∉ M) :
    ∃ x : Y ⧸ Z0,
      x = QuotientGroup.mk' Z0 (z : Y) ∧ x * x = 1 ∧ x ≠ 1 ∧ orderOf x = 2 ∧
      x ∈ Subgroup.center (Y ⧸ Z0) ∧ x ∈ commutator (Y ⧸ Z0) ∧
      Nat.card (Z.map (QuotientGroup.mk' Z0)) = 2 ∧
      Subgroup.zpowers x = Z.map (QuotientGroup.mk' Z0) := by
  classical
  let E := Y ⧸ Z0
  let x : Y ⧸ Z0 := QuotientGroup.mk' Z0 (z : Y)
  have hx2 : x * x = 1 := by
    have hz2M : z * z ∈ M := by
      simpa [pow_two] using Subgroup.sq_mem_of_index_two hMindex z
    show QuotientGroup.mk' Z0 ((z : Y) * (z : Y)) = 1
    refine (QuotientGroup.eq_one_iff _).2 ?_
    rw [hZ0]
    exact Subgroup.mem_map.2 ⟨z * z, hz2M, rfl⟩
  have hx1 : x ≠ 1 := by
    intro hx
    have hz0 : (z : Y) ∈ Z0 := (QuotientGroup.eq_one_iff _).1 hx
    rw [hZ0] at hz0
    obtain ⟨z', hz'M, hz'eq⟩ := Subgroup.mem_map.1 hz0
    have hzz : z' = z := Z.subtype_injective hz'eq
    rw [hzz] at hz'M
    exact hzM hz'M
  have hxorder : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  have hxcenter : x ∈ Subgroup.center E := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective Z0 y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ z.2) y0]
  haveI : Group.IsPerfect Y := ⟨hperf⟩
  have hperfE : commutator E = ⊤ := Group.isPerfect_def.mp inferInstance
  have hxcomm : x ∈ commutator E := by
    rw [hperfE]
    exact Subgroup.mem_top x
  have hzpowers_normal : (Subgroup.zpowers x).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hxcenter)
  have hZmap_card : Nat.card (Z.map (QuotientGroup.mk' Z0)) = 2 := by
    rw [CFSG.natCard_map_mk'_eq Z Z0, ← Subgroup.index_eq_card]
    have hsub : Z0.subgroupOf Z = M := by
      ext y
      simp [Subgroup.mem_subgroupOf, hZ0]
    rw [hsub, hMindex]
  have hx_mem : x ∈ Z.map (QuotientGroup.mk' Z0) :=
    Subgroup.mem_map_of_mem _ z.2
  have hzpowers_eq : Subgroup.zpowers x = Z.map (QuotientGroup.mk' Z0) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx_mem) ?_
    rw [Nat.card_zpowers, hxorder, hZmap_card]
  exact ⟨x, rfl, hx2, hx1, hxorder, hxcenter, hxcomm, hZmap_card, hzpowers_eq⟩

private theorem exists_quotient_map_with_kernel
    {Z0 : Subgroup Y} [Z0.Normal] (hZ0le : Z0 ≤ Z) {x : Y ⧸ Z0}
    (hzpowers : Subgroup.zpowers x = Z.map (QuotientGroup.mk' Z0)) :
    ∃ πE : (Y ⧸ Z0) →* (Y ⧸ Z),
      (∀ y : Y, πE (QuotientGroup.mk' Z0 y) = QuotientGroup.mk' Z y) ∧
      Function.Surjective πE ∧ πE.ker = Subgroup.zpowers x ∧ πE x = 1 := by
  classical
  let πE : (Y ⧸ Z0) →* Y ⧸ Z := QuotientGroup.map Z0 Z (MonoidHom.id Y) (by
    intro y hy
    exact hZ0le hy)
  have hπE_mk (y : Y) : πE (QuotientGroup.mk' Z0 y) = QuotientGroup.mk' Z y := by
    simpa [πE] using
      (QuotientGroup.map_mk' Z0 Z (MonoidHom.id Y)
        (by intro y hy; exact hZ0le hy) y)
  have hπEsurj : Function.Surjective πE := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨QuotientGroup.mk' Z0 y, hπE_mk y⟩
  have hkerπE : πE.ker = Subgroup.zpowers x := by
    rw [hzpowers]
    ext y
    constructor
    · intro hy
      obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective Z0 y
      rw [MonoidHom.mem_ker, hπE_mk] at hy
      exact Subgroup.mem_map_of_mem _ ((QuotientGroup.eq_one_iff _).1 hy)
    · intro hy
      obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.1 hy
      rw [MonoidHom.mem_ker, hπE_mk]
      exact (QuotientGroup.eq_one_iff _).2 hz0
  have hxker : πE x = 1 := by
    rw [← MonoidHom.mem_ker, hkerπE]
    exact Subgroup.mem_zpowers x
  exact ⟨πE, hπE_mk, hπEsurj, hkerπE, hxker⟩

private theorem exists_narrow_element_and_conjugate
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    {Z0 : Subgroup Y} [Z0.Normal] {x : Y ⧸ Z0}
    (hxcenter : x ∈ Subgroup.center (Y ⧸ Z0))
    (hxorder : orderOf x = 2) (hxcomm : x ∈ commutator (Y ⧸ Z0))
    (πE : (Y ⧸ Z0) →* (Y ⧸ Z))
    (hπEsurj : Function.Surjective πE) (hkerπE : πE.ker = Subgroup.zpowers x)
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F) :
    ∃ (zE : Y ⧸ Z0) (c : CFSG.Blueprint.suzukiGroup a F),
      zE * zE = 1 ∧ zE ≠ x ∧ IsConj zE (zE * x) ∧
      πE zE * πE zE = 1 ∧ πE zE ≠ 1 ∧
      e (πE zE) * e (πE zE) = 1 ∧ e (πE zE) ≠ 1 ∧
      e (πE zE) ∈ conjSubgroup c (szZ a F) := by
  classical
  let E := Y ⧸ Z0
  have hzpowers_normal : (Subgroup.zpowers x).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hxcenter)
  let σ : E ⧸ Subgroup.zpowers x ≃* Y ⧸ Z :=
    (QuotientGroup.quotientMulEquivOfEq hkerπE.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective πE hπEsurj)
  let τ : (⊤ : Subgroup (E ⧸ Subgroup.zpowers x)) ⧸
      (⊥ : Subgroup (E ⧸ Subgroup.zpowers x)).subgroupOf ⊤ ≃* CFSG.Open.Sz a :=
    ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot).trans
        (Subgroup.topEquiv.trans (σ.trans (openSzEquivOfMulEquiv hF e)))
  obtain ⟨zE, hzE2, hzEx, hzEconj⟩ :=
    (CFSG.Timmesfeld.Bridge.schurNarrowInput (E := E) x hzpowers_normal hxcenter hxorder hxcomm
      ⊥ ⊤ inferInstance inferInstance inferInstance bot_le
      (by rw [Subgroup.card_bot]; exact odd_one)
      (by rw [Subgroup.index_top]; exact odd_one) (Or.inr ⟨a, ha, ⟨τ⟩⟩))
  have hzEx' : zE ≠ x := by
    intro h
    exact hzEx (h ▸ Subgroup.mem_zpowers x)
  have hzE2' : zE * zE = 1 := by
    rw [← pow_two, ← hzE2, pow_orderOf_eq_one]
  have hπz2 : πE zE * πE zE = 1 := by
    rw [← map_mul, hzE2', map_one]
  have hπz1 : πE zE ≠ 1 := by
    intro h
    apply hzEx
    have hmem : zE ∈ πE.ker := h
    rwa [hkerπE] at hmem
  have hxG2 : e (πE zE) * e (πE zE) = 1 := by
    rw [← map_mul, hπz2, map_one]
  have hxG1 : e (πE zE) ≠ 1 := by
    intro h
    exact hπz1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨c, hc⟩ := exists_conjSubgroup_szZ_of_involution hF hxG2 hxG1
  exact ⟨zE, c, hzE2', hzEx', hzEconj, hπz2, hπz1, hxG2, hxG1, hc⟩

private theorem exists_conjugate_with_weak_closure
    (hT : CFSG.Assembly.IsElemAbelian 2 T) (hTZ : T ⊓ Z = ⊥)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) {a : ℕ} {F : Type} [Field F]
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F)
    {c c₀ : CFSG.Blueprint.suzukiGroup a F} :
    ∃ (gY : Y) (T' : Subgroup Y),
      T' = conjSubgroup gY T ∧ T' ⊓ Z = ⊥ ∧
      (∀ t ∈ T', t * t = 1) ∧
      Subgroup.normalizer (T' : Set Y) =
        conjSubgroup gY (Subgroup.normalizer (T : Set Y)) ∧
      WeaklyClosedIn T' (Subgroup.normalizer (T' : Set Y)) ∧
      e (QuotientGroup.mk' Z gY) = c * c₀⁻¹ := by
  classical
  obtain ⟨gY, hgY⟩ := QuotientGroup.mk'_surjective Z (e.symm (c * c₀⁻¹))
  let T' : Subgroup Y := conjSubgroup gY T
  have hT'Z : T' ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huT, huZ⟩ := Subgroup.mem_inf.1 hu
    rw [show T' = conjSubgroup gY T from rfl, mem_conjSubgroup] at huT
    have hmem : gY⁻¹ * u * gY ∈ T ⊓ Z := by
      refine ⟨huT, ?_⟩
      rw [show gY⁻¹ * u * gY = u by
        calc gY⁻¹ * u * gY = gY⁻¹ * (u * gY) := by group
          _ = gY⁻¹ * (gY * u) := by rw [Subgroup.mem_center_iff.mp (hZ huZ) gY]
          _ = u := by group]
      exact huZ
    rw [hTZ, Subgroup.mem_bot] at hmem
    calc u = gY * (gY⁻¹ * u * gY) * gY⁻¹ := by group
      _ = 1 := by rw [hmem]; group
  have hT'el : ∀ t ∈ T', t * t = 1 := by
    intro t ht
    rw [show T' = conjSubgroup gY T from rfl] at ht
    obtain ⟨t0, ht0, rfl⟩ := Subgroup.mem_map.1 ht
    show (gY * t0 * gY⁻¹) * (gY * t0 * gY⁻¹) = 1
    have hsq : t0 * t0 = 1 := by rw [← pow_two]; exact hT.2 t0 ht0
    calc (gY * t0 * gY⁻¹) * (gY * t0 * gY⁻¹) = gY * (t0 * t0) * gY⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  have hnormalizer_conj : Subgroup.normalizer (T' : Set Y) =
      conjSubgroup gY (Subgroup.normalizer (T : Set Y)) := by
    simpa [T', conjSubgroup] using
      (Subgroup.map_equiv_normalizer_eq T (MulAut.conj gY)).symm
  have hwc' : WeaklyClosedIn T' (Subgroup.normalizer (T' : Set Y)) := by
    refine ⟨Subgroup.le_normalizer, ?_⟩
    intro h hh
    have hhN : conjSubgroup (gY⁻¹ * h * gY) T ≤ Subgroup.normalizer (T : Set Y) := by
      have hh' : conjSubgroup h (conjSubgroup gY T) ≤
          conjSubgroup gY (Subgroup.normalizer (T : Set Y)) := by
        simpa [T', hnormalizer_conj] using hh
      have hle := (conjSubgroup_le_iff (g := gY⁻¹)).2 (by simpa using hh')
      simpa [conjSubgroup_conjSubgroup, mul_assoc] using hle
    have heq : conjSubgroup (gY⁻¹ * h * gY) T = T := hwc.2 _ hhN
    calc conjSubgroup h T' = conjSubgroup h (conjSubgroup gY T) := by
          rw [show T' = conjSubgroup gY T from rfl]
      _ = conjSubgroup (h * gY) T := by rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup (gY * (gY⁻¹ * h * gY)) T := by congr 1; group
      _ = conjSubgroup gY (conjSubgroup (gY⁻¹ * h * gY) T) := by rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup gY T := by rw [heq]
      _ = T' := by rw [show T' = conjSubgroup gY T from rfl]
  have hge : e ((QuotientGroup.mk' Z) gY) = c * c₀⁻¹ := by
    rw [hgY, e.apply_symm_apply]
  exact ⟨gY, T', rfl, hT'Z, hT'el, hnormalizer_conj, hwc', hge⟩

private theorem map_conj_and_mem_of_conjugate
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    {Z0 : Subgroup Y} [Z0.Normal] {zE : Y ⧸ Z0}
    (πE : (Y ⧸ Z0) →* (Y ⧸ Z))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F)
    {gY : Y} {T' : Subgroup Y} (hT' : T' = conjSubgroup gY T)
    {c c₀ : CFSG.Blueprint.suzukiGroup a F}
    (hS_eq : (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom =
      conjSubgroup c₀ (szZ a F))
    (hge : e (QuotientGroup.mk' Z gY) = c * c₀⁻¹)
    (hc : e (πE zE) ∈ conjSubgroup c (szZ a F)) :
    (T'.map (QuotientGroup.mk' Z)).map e.toMonoidHom = conjSubgroup c (szZ a F) ∧
      πE zE ∈ T'.map (QuotientGroup.mk' Z) := by
  have hmapT'bar : (T'.map (QuotientGroup.mk' Z)).map e.toMonoidHom =
      conjSubgroup c (szZ a F) := by
    rw [hT',
      map_conjSubgroup (QuotientGroup.mk' Z) gY T,
      map_conjSubgroup e.toMonoidHom
        (QuotientGroup.mk' Z gY) (T.map (QuotientGroup.mk' Z)),
      hS_eq, conjSubgroup_conjSubgroup]
    congr 1
    change e ((QuotientGroup.mk' Z) gY) * c₀ = c
    rw [hge]
    group
  have hmemTbar : πE zE ∈ T'.map (QuotientGroup.mk' Z) := by
    apply (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [hmapT'bar]
    exact hc
  exact ⟨hmapT'bar, hmemTbar⟩

private theorem exists_decomposition_in_TE
    (hZ : Z ≤ Subgroup.center Y)
    {Z0 : Subgroup Y} [Z0.Normal] {x zE : Y ⧸ Z0} (hxorder : orderOf x = 2)
    {T' : Subgroup Y} (hT'el : ∀ t ∈ T', t * t = 1)
    (πE : (Y ⧸ Z0) →* (Y ⧸ Z))
    (hπE_mk : ∀ y : Y, πE (QuotientGroup.mk' Z0 y) = QuotientGroup.mk' Z y)
    (hkerπE : πE.ker = Subgroup.zpowers x)
    (hmemTbar : πE zE ∈ T'.map (QuotientGroup.mk' Z)) :
    ∃ (TE : Subgroup (Y ⧸ Z0)) (tE cE : Y ⧸ Z0),
      TE = T'.map (QuotientGroup.mk' Z0) ∧
      (∀ t ∈ TE, t * t = 1) ∧ tE ∈ TE ∧ cE = tE⁻¹ * zE ∧ zE = tE * cE ∧
      cE ∈ Subgroup.zpowers x ∧ (cE = 1 ∨ cE = x) ∧
      Z.map (QuotientGroup.mk' Z0) ≤ Subgroup.center (Y ⧸ Z0) := by
  classical
  let E := Y ⧸ Z0
  let TE : Subgroup E := T'.map (QuotientGroup.mk' Z0)
  have hTE_sq : ∀ t ∈ TE, t * t = 1 := by
    intro t ht
    obtain ⟨t0, ht0, rfl⟩ := Subgroup.mem_map.1 ht
    rw [← map_mul, hT'el t0 ht0, map_one]
  obtain ⟨t, htT', htπ⟩ := Subgroup.mem_map.1 hmemTbar
  let tE : E := QuotientGroup.mk' Z0 t
  have htTE : tE ∈ TE := Subgroup.mem_map_of_mem _ htT'
  have htEπ : πE tE = πE zE := by
    rw [show πE tE = QuotientGroup.mk' Z t from hπE_mk t, htπ]
  let cE : E := tE⁻¹ * zE
  have hdecomp : zE = tE * cE := by
    show zE = tE * (tE⁻¹ * zE)
    group
  have hcE_ker : cE ∈ Subgroup.zpowers x := by
    rw [← hkerπE, MonoidHom.mem_ker]
    change πE (tE⁻¹ * zE) = 1
    rw [map_mul, map_inv, htEπ, inv_mul_cancel]
  have hcE_cases : cE = 1 ∨ cE = x :=
    eq_one_or_eq_of_mem_zpowers_order_two hxorder hcE_ker
  have hZmap_center : Z.map (QuotientGroup.mk' Z0) ≤ Subgroup.center E := by
    intro y hy
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective Z0 y'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ hz') y0]
  exact ⟨TE, tE, cE, rfl, hTE_sq, htTE, rfl, hdecomp, hcE_ker, hcE_cases, hZmap_center⟩

private theorem exists_nontrivial_conjugate_in_TE
    {Z0 : Subgroup Y} [Z0.Normal] {x zE : Y ⧸ Z0}
    {TE : Subgroup (Y ⧸ Z0)} {tE cE : Y ⧸ Z0}
    (hx2 : x * x = 1)
    (hTE_sq : ∀ t ∈ TE, t * t = 1) (htE : tE ∈ TE)
    (hcE_ker : cE ∈ Subgroup.zpowers x) (hdecomp : zE = tE * cE)
    (hcE_cases : cE = 1 ∨ cE = x) (hzE2 : zE * zE = 1)
    (hzEconj : IsConj zE (zE * x))
    (hZmap_center : Z.map (QuotientGroup.mk' Z0) ≤ Subgroup.center (Y ⧸ Z0))
    (hzpowers_eq : Subgroup.zpowers x = Z.map (QuotientGroup.mk' Z0))
    (πE : (Y ⧸ Z0) →* (Y ⧸ Z))
    (hπz1 : πE zE ≠ 1) (hxker : πE x = 1) :
    ∃ w : Y ⧸ Z0, w ∈ TE ∧ IsConj w (w * x) ∧ w ≠ 1 := by
  classical
  let E := Y ⧸ Z0
  have hcE_central : cE ∈ Subgroup.center E := by
    apply hZmap_center
    rwa [hzpowers_eq] at hcE_ker
  have hcE2 : cE * cE = 1 := by
    have htsq : tE * tE = 1 := hTE_sq tE htE
    have hcomm : tE * cE = cE * tE :=
      Subgroup.mem_center_iff.mp hcE_central tE
    calc cE * cE = (tE * tE) * (cE * cE) := by rw [htsq, one_mul]
      _ = (tE * cE) * (tE * cE) := by
          calc (tE * tE) * (cE * cE) = tE * (tE * cE) * cE := by group
            _ = tE * (cE * tE) * cE := by rw [hcomm]
            _ = (tE * cE) * (tE * cE) := by group
      _ = zE * zE := by rw [← hdecomp]
      _ = 1 := hzE2
  let w : E := if cE = 1 then zE else zE * x
  have hcx_of_ne (hc1 : cE ≠ 1) : cE = x := by
    rcases hcE_cases with h | h
    · exact absurd h hc1
    · exact h
  have hwTE : w ∈ TE := by
    by_cases hc1 : cE = 1
    · have hz : zE = tE := by rw [hdecomp, hc1, mul_one]
      rw [show w = tE by simp [w, hc1, hz]]
      exact htE
    · have hzx : zE * x = tE := by
        rw [hdecomp, hcx_of_ne hc1, mul_assoc, hx2, mul_one]
      rw [show w = tE by simp [w, hc1, hzx]]
      exact htE
  have hwConj : IsConj w (w * x) := by
    by_cases hc1 : cE = 1
    · rw [show w = zE by simp [w, hc1]]
      exact hzEconj
    · have hw_eq : w = zE * x := by simp [w, hc1]
      have hwx : w * x = zE := by rw [hw_eq, mul_assoc, hx2, mul_one]
      rw [hwx, hw_eq]
      exact hzEconj.symm
  have hw1 : w ≠ 1 := by
    intro hw
    have hπw : πE w = πE zE := by
      by_cases hc1 : cE = 1
      · rw [show w = zE by simp [w, hc1]]
      · have hw_eq : w = zE * x := by simp [w, hc1]
        rw [hw_eq, map_mul, hxker, mul_one]
    have hone : πE w = 1 := by rw [hw, map_one]
    exact hπz1 (by rw [← hπw]; exact hone)
  exact ⟨w, hwTE, hwConj, hw1⟩

private theorem inf_map_and_map_ne_one
    {Z0 : Subgroup Y} [Z0.Normal] {x : Y ⧸ Z0}
    {T' : Subgroup Y} {TE : Subgroup (Y ⧸ Z0)} {w : Y ⧸ Z0}
    (hZ0le : Z0 ≤ Z) (hT'Z : T' ⊓ Z = ⊥) (hTE : TE = T'.map (QuotientGroup.mk' Z0))
    (hwTE : w ∈ TE) (hw1 : w ≠ 1)
    (hzpowers : Subgroup.zpowers x = Z.map (QuotientGroup.mk' Z0))
    (πE : (Y ⧸ Z0) →* (Y ⧸ Z)) (hkerπE : πE.ker = Subgroup.zpowers x) :
    TE ⊓ Z.map (QuotientGroup.mk' Z0) = ⊥ ∧ πE w ≠ 1 := by
  classical
  have hTE_inf : TE ⊓ Z.map (QuotientGroup.mk' Z0) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huTE, huZ⟩ := Subgroup.mem_inf.1 hu
    rw [hTE] at huTE
    obtain ⟨t0, ht0, ht0eq⟩ := Subgroup.mem_map.1 huTE
    obtain ⟨z0, hz0, hz0eq⟩ := Subgroup.mem_map.1 huZ
    have htz : t0⁻¹ * z0 ∈ Z0 := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change QuotientGroup.mk' Z0 (t0⁻¹ * z0) = 1
      rw [map_mul, map_inv, hz0eq, ← ht0eq]
      group
    have htZ : t0 ∈ Z := by
      have htzZ : t0⁻¹ * z0 ∈ Z := hZ0le htz
      have ht : t0 = z0 * (t0⁻¹ * z0)⁻¹ := by group
      rw [ht]
      exact Z.mul_mem hz0 (Z.inv_mem htzZ)
    have htbot : t0 ∈ T' ⊓ Z := ⟨ht0, htZ⟩
    rw [hT'Z, Subgroup.mem_bot] at htbot
    have hu1 : u = 1 := by rw [← ht0eq, htbot, map_one]
    simpa [hu1]
  have hπw1 : πE w ≠ 1 := by
    intro h
    have hwker : w ∈ πE.ker := h
    rw [hkerπE] at hwker
    have hwZ : w ∈ Z.map (QuotientGroup.mk' Z0) := by rwa [hzpowers] at hwker
    have hmem : w ∈ TE ⊓ Z.map (QuotientGroup.mk' Z0) := ⟨hwTE, hwZ⟩
    rw [hTE_inf, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  exact ⟨hTE_inf, hπw1⟩

private theorem normalizer_image_of_conj
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    {Z0 : Subgroup Y} [Z0.Normal] {x w kE : Y ⧸ Z0}
    (πE : (Y ⧸ Z0) →* (Y ⧸ Z))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F)
    {T' : Subgroup Y} {c : CFSG.Blueprint.suzukiGroup a F}
    (hmap : (T'.map (QuotientGroup.mk' Z)).map e.toMonoidHom =
      conjSubgroup c (szZ a F))
    (hπw1 : πE w ≠ 1)
    (hπwTbar : πE w ∈ T'.map (QuotientGroup.mk' Z))
    (hkE : kE * w * kE⁻¹ = w * x)
    (hxker : πE x = 1) :
    πE kE ∈ Subgroup.normalizer (T'.map (QuotientGroup.mk' Z) : Set (Y ⧸ Z)) := by
  classical
  have hπwConj : πE w ∈ conjSubgroup (πE kE) (T'.map (QuotientGroup.mk' Z)) := by
    rw [mem_conjSubgroup]
    have hfix : πE kE * πE w * (πE kE)⁻¹ = πE w := by
      have := congrArg πE hkE
      simpa [map_mul, map_inv, hxker] using this
    have hcomm : πE kE * πE w = πE w * πE kE := by
      calc πE kE * πE w = (πE kE * πE w * (πE kE)⁻¹) * πE kE := by group
        _ = πE w * πE kE := by rw [hfix]
    have hconj : (πE kE)⁻¹ * πE w * πE kE = πE w := by
      calc (πE kE)⁻¹ * πE w * πE kE = (πE kE)⁻¹ * (πE w * πE kE) := by group
        _ = (πE kE)⁻¹ * (πE kE * πE w) := by rw [← hcomm]
        _ = πE w := by group
    rwa [hconj]
  have hNconj : e (πE kE) ∈ Subgroup.normalizer (conjSubgroup c (szZ a F) :
      Set (CFSG.Blueprint.suzukiGroup a F)) := by
    refine mem_normalizer_conjSubgroup_szZ_of_inf_ne_bot (hF := hF) (c := c)
      (g := e (πE kE)) (u := e (πE w)) ?_ ?_ ?_
    · intro h
      exact hπw1 (e.injective (h.trans (map_one e).symm))
    · have hmem : e (πE w) ∈ (T'.map (QuotientGroup.mk' Z)).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hπwTbar
      rwa [hmap] at hmem
    · have hmem : e (πE w) ∈
          (conjSubgroup (πE kE) (T'.map (QuotientGroup.mk' Z))).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hπwConj
      rwa [map_conjSubgroup e.toMonoidHom (πE kE)
        (T'.map (QuotientGroup.mk' Z)), hmap] at hmem
  have hN : πE kE ∈ Subgroup.normalizer (T'.map (QuotientGroup.mk' Z) : Set (Y ⧸ Z)) := by
    have hmem : e (πE kE) ∈
        (Subgroup.normalizer (T'.map (QuotientGroup.mk' Z) : Set (Y ⧸ Z))).map e.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq, hmap]
      exact hNconj
    exact (Subgroup.mem_map_iff_mem e.injective).1 hmem
  exact hN

private theorem false_of_weak_closure_and_conj
    {Z0 : Subgroup Y} [Z0.Normal]
    {T' : Subgroup Y} {x : Y ⧸ Z0} (hx1 : x ≠ 1)
    {TE : Subgroup (Y ⧸ Z0)} {w kE : Y ⧸ Z0}
    (hwc' : WeaklyClosedIn T' (Subgroup.normalizer (T' : Set Y)))
    (hZ : Z ≤ Subgroup.center Y)
    (hTE : TE = T'.map (QuotientGroup.mk' Z0))
    (hTE_inf : TE ⊓ Z.map (QuotientGroup.mk' Z0) = ⊥)
    (hwTE : w ∈ TE)
    (hxZ : x ∈ Z.map (QuotientGroup.mk' Z0))
    (πE : (Y ⧸ Z0) →* (Y ⧸ Z))
    (hπE_mk : ∀ y : Y, πE (QuotientGroup.mk' Z0 y) = QuotientGroup.mk' Z y)
    (hN : πE kE ∈
      Subgroup.normalizer (T'.map (QuotientGroup.mk' Z) : Set (Y ⧸ Z)))
    (hkE : kE * w * kE⁻¹ = w * x) : False := by
  classical
  obtain ⟨kY, hkY⟩ := QuotientGroup.mk'_surjective Z0 kE
  have hπkY : πE kE = QuotientGroup.mk' Z kY := by
    rw [← hkY, hπE_mk]
  have hconjT : conjSubgroup kY T' ≤ T' ⊔ Z := by
    have hmap : (conjSubgroup kY T').map (QuotientGroup.mk' Z) =
        T'.map (QuotientGroup.mk' Z) := by
      rw [map_conjSubgroup (QuotientGroup.mk' Z) kY T', ← hπkY]
      exact mem_normalizer_iff_conjSubgroup_eq.1 hN
    simpa [QuotientGroup.ker_mk'] using
      (Subgroup.map_le_map_iff (f := QuotientGroup.mk' Z) (H := conjSubgroup kY T')
        (K := T')).1 (le_of_eq hmap)
  have hleN : conjSubgroup kY T' ≤ Subgroup.normalizer (T' : Set Y) :=
    hconjT.trans (sup_le_normalizer (T := T') hZ)
  have hT'k : conjSubgroup kY T' = T' := hwc'.2 kY hleN
  have hTEinv : conjSubgroup (QuotientGroup.mk' Z0 kY) TE = TE := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' Z0)) hT'k
    rw [hTE, ← map_conjSubgroup (QuotientGroup.mk' Z0) kY T']
    exact h
  have hwxTE : w * x ∈ TE := by
    have hmem : QuotientGroup.mk' Z0 kY * w * (QuotientGroup.mk' Z0 kY)⁻¹ ∈
        conjSubgroup (QuotientGroup.mk' Z0 kY) TE :=
      conj_mem_conjSubgroup _ hwTE
    rw [hTEinv] at hmem
    rwa [hkY, hkE] at hmem
  have hxTE : x ∈ TE := by
    have h := TE.mul_mem (TE.inv_mem hwTE) hwxTE
    rwa [show w⁻¹ * (w * x) = x by group] at h
  have hmem : x ∈ TE ⊓ Z.map (QuotientGroup.mk' Z0) := ⟨hxTE, hxZ⟩
  rw [hTE_inf, Subgroup.mem_bot] at hmem
  exact hx1 hmem

private theorem false_of_isPGroup_two
    (hT : CFSG.Assembly.IsElemAbelian 2 T) (hTZ : T ⊓ Z = ⊥)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) (hZ2 : IsPGroup 2 Z) (hZne : Z ≠ ⊥)
    (hperf : commutator Y = ⊤) {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F)
    {c₀ : CFSG.Blueprint.suzukiGroup a F}
    (hS_eq : (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom =
      conjSubgroup c₀ (szZ a F)) : False := by
  classical
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  obtain ⟨M, Z0, z, hZ0, hMindex, hZ0le, hZ0normal, hzM⟩ :=
    exists_index_two_subgroup hZ hZ2 hZne
  haveI : Z0.Normal := hZ0normal
  obtain ⟨x, hx, hx2, hx1, hxorder, hxcenter, hxcomm, hZmap_card, hzpowers_eq⟩ :=
    exists_involution_with_center_and_zpowers hZ hperf hZ0 hMindex hzM
  obtain ⟨πE, hπE_mk, hπEsurj, hkerπE, hxker⟩ :=
    exists_quotient_map_with_kernel hZ0le hzpowers_eq
  obtain ⟨zE, c, hzE2, hzEx, hzEconj, hπz2, hπz1, hxG2, hxG1, hc⟩ :=
    exists_narrow_element_and_conjugate hF ha hxcenter hxorder hxcomm πE hπEsurj hkerπE e
  obtain ⟨gY, T', hT'eq, hT'Z, hT'el, hnormalizer_conj, hwc', hge⟩ :=
    exists_conjugate_with_weak_closure hT hTZ hwc hZ e (c := c) (c₀ := c₀)
  obtain ⟨hmapT'bar, hmemTbar⟩ :=
    map_conj_and_mem_of_conjugate πE e hT'eq hS_eq hge hc
  obtain ⟨TE, tE, cE, hTE, hTE_sq, htE, hcE, hdecomp, hcE_ker, hcE_cases,
    hZmap_center⟩ :=
    exists_decomposition_in_TE hZ hxorder hT'el πE hπE_mk hkerπE hmemTbar
  obtain ⟨w, hwTE, hwConj, hw1⟩ :=
    exists_nontrivial_conjugate_in_TE hx2 hTE_sq htE hcE_ker hdecomp hcE_cases hzE2
      hzEconj hZmap_center hzpowers_eq πE hπz1 hxker
  obtain ⟨hTE_inf, hπw1⟩ :=
    inf_map_and_map_ne_one hZ0le hT'Z hTE hwTE hw1 hzpowers_eq πE hkerπE
  obtain ⟨kE, hkE⟩ := isConj_iff.1 hwConj
  have hwT' : w ∈ T'.map (QuotientGroup.mk' Z0) := hTE ▸ hwTE
  have hπwTbar : πE w ∈ T'.map (QuotientGroup.mk' Z) := by
    obtain ⟨t0, ht0, rfl⟩ := Subgroup.mem_map.1 hwT'
    rw [hπE_mk t0]
    exact Subgroup.mem_map_of_mem _ ht0
  have hN := normalizer_image_of_conj (x := x) (w := w) (kE := kE) hF πE e
    hmapT'bar hπw1 hπwTbar hkE hxker
  have hxZ : x ∈ Z.map (QuotientGroup.mk' Z0) := by
    rw [← hzpowers_eq]
    exact Subgroup.mem_zpowers x
  exact false_of_weak_closure_and_conj hx1 hwc' hZ hTE hTE_inf hwTE hxZ πE hπE_mk hN hkE

private theorem sz_TZ
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hT : CFSG.Assembly.IsElemAbelian 2 T)
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤) (hTI : IsTI T)
    (hZ : Z ≤ Subgroup.center Y) (ha : 1 ≤ a)
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F) : T ⊓ Z = ⊥ := by

  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  haveI hperfG : Group.IsPerfect (CFSG.Blueprint.suzukiGroup a F) :=
    (CFSG.LieType.Ree.suzuki_perfect ha hK).2
  haveI hntG : Nontrivial (CFSG.Blueprint.suzukiGroup a F) :=
    (CFSG.LieType.Ree.suzuki_simple ha hK).2.1
  have hqG : ¬ IsMulCommutative (CFSG.Blueprint.suzukiGroup a F) :=
    Group.IsPerfect.not_isMulCommutative _
  have hq : ¬ IsMulCommutative (Y ⧸ Z) := by
    intro hcomm
    apply hqG
    rw [isMulCommutative_iff] at hcomm ⊢
    intro x y
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hcomm a b]
  exact inf_eq_bot_of_not_isMulCommutative hT hgen hTI hZ hq

private theorem sz_Tbar_data
    (hT : CFSG.Assembly.IsElemAbelian 2 T)
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) (hTZ : T ⊓ Z = ⊥) {a : ℕ} (ha : 1 ≤ a) {F : Type}
    [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F) :
    ∃ (Tbar : Subgroup (Y ⧸ Z)) (S : Subgroup (CFSG.Blueprint.suzukiGroup a F))
      (c₀ : CFSG.Blueprint.suzukiGroup a F),
      IsPGroup 2 Tbar ∧ Tbar ≠ ⊥ ∧ (∀ x ∈ Tbar, x * x = 1) ∧
      (∀ g : Y ⧸ Z, conjSubgroup g Tbar ≤
        Subgroup.normalizer (Tbar : Set (Y ⧸ Z)) → conjSubgroup g Tbar = Tbar) ∧
      S = Tbar.map e.toMonoidHom ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
      (∀ x ∈ S, x * x = 1) ∧
      (∀ g : CFSG.Blueprint.suzukiGroup a F, conjSubgroup g S ≤
        Subgroup.normalizer (S : Set (CFSG.Blueprint.suzukiGroup a F)) →
          conjSubgroup g S = S) ∧
      S = conjSubgroup c₀ (szZ a F) ∧ Nat.card S = 2 ^ (2 * a + 1) ∧
      Tbar = T.map (QuotientGroup.mk' Z) := by
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  haveI hntG : Nontrivial (CFSG.Blueprint.suzukiGroup a F) :=
    (CFSG.LieType.Ree.suzuki_simple (by omega) hK).2.1
  haveI : Nontrivial (Y ⧸ Z) := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [Nat.card_congr e.toEquiv]
    exact Finite.one_lt_card)
  have hTne : T ≠ ⊥ := by
    intro hbot
    have htopbot : (⊤ : Subgroup Y) = ⊥ := by
      rw [← hgen, hbot]
      simp
    haveI : Subsingleton Y := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup Y) := by rw [← htopbot]; trivial
      have hb : b ∈ (⊥ : Subgroup Y) := by rw [← htopbot]; trivial
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    haveI : Subsingleton (Y ⧸ Z) := inferInstance
    exact (not_subsingleton (Y ⧸ Z)) inferInstance
  let π : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  let Tbar : Subgroup (Y ⧸ Z) := T.map π
  have hTbarP : IsPGroup 2 Tbar := hT.isPGroup.map π
  have hTbarNe : Tbar ≠ ⊥ := (isPGroup_map_mk'_and_ne_bot hT.isPGroup hTZ hTne).2
  have hTbarSq : ∀ x ∈ Tbar, x * x = 1 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_mul, show t * t = 1 by rw [← pow_two]; exact hT.2 t ht, map_one]
  have hTbarWc : ∀ g : Y ⧸ Z, conjSubgroup g Tbar ≤
      Subgroup.normalizer (Tbar : Set (Y ⧸ Z)) → conjSubgroup g Tbar = Tbar :=
    weaklyClosed_map_mk' hZ hwc
  let S : Subgroup (CFSG.Blueprint.suzukiGroup a F) := Tbar.map e.toMonoidHom
  have hSP : IsPGroup 2 S := hTbarP.map _
  have hSNe : S ≠ ⊥ := by
    intro hbot
    apply hTbarNe
    exact (Subgroup.map_eq_bot_iff_of_injective Tbar e.injective).1 hbot
  have hSSq : ∀ x ∈ S, x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_mul, hTbarSq y hy, map_one]
  have hSWc : ∀ g : CFSG.Blueprint.suzukiGroup a F, conjSubgroup g S ≤
      Subgroup.normalizer (S : Set (CFSG.Blueprint.suzukiGroup a F)) →
        conjSubgroup g S = S :=
    weaklyClosed_map_mulEquiv e hTbarWc
  obtain ⟨c₀, hS_eq, hScard⟩ := exists_conj_eq_szZ hK hSP hSNe hSSq hSWc
  exact ⟨Tbar, S, c₀, hTbarP, hTbarNe, hTbarSq, hTbarWc, rfl, hSP, hSNe, hSSq, hSWc,
    hS_eq, hScard, rfl⟩

private theorem sz_perfect_of_torus
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) (hTZ : T ⊓ Z = ⊥) {a : ℕ} (ha : 1 ≤ a) {F : Type}
    [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F)
    {Tbar : Subgroup (Y ⧸ Z)} {S : Subgroup (CFSG.Blueprint.suzukiGroup a F)}
    (hS : S = Tbar.map e.toMonoidHom) (hSP : IsPGroup 2 S) (hSNe : S ≠ ⊥)
    (hSSq : ∀ x ∈ S, x * x = 1)
    (hSWc : ∀ g : CFSG.Blueprint.suzukiGroup a F, conjSubgroup g S ≤
      Subgroup.normalizer (S : Set (CFSG.Blueprint.suzukiGroup a F)) →
        conjSubgroup g S = S)
    (hScard : Nat.card S = 2 ^ (2 * a + 1))
    (hTbarDef : Tbar = T.map (QuotientGroup.mk' Z)) : commutator Y = ⊤ := by
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF

  obtain ⟨D, hDN, hDcard, hDcomm, hDfpf⟩ := exists_frobeniusComplement_sz hK hSP hSNe hSSq hSWc
  have hDcard_gt : 1 < Nat.card D := by
    rw [hDcard, hScard]
    have hge : 2 ^ 3 ≤ 2 ^ (2 * a + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith [ha])
    omega
  haveI : Nontrivial D := Finite.one_lt_card_iff_nontrivial.1 hDcard_gt
  obtain ⟨dD, hdD1⟩ := exists_ne (1 : D)
  let d : CFSG.Blueprint.suzukiGroup a F := dD
  have hdD : d ∈ D := dD.2
  have hd1 : d ≠ 1 := fun h => hdD1 (Subtype.ext h)
  have hdN : e.symm d ∈ Subgroup.normalizer (Tbar : Set (Y ⧸ Z)) := by
    have hmem : d ∈ (Subgroup.normalizer (Tbar : Set (Y ⧸ Z))).map e.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq Tbar e, show Tbar.map e.toMonoidHom = S from hS.symm]
      exact hDN hdD
    have hmem' : e (e.symm d) ∈ (Subgroup.normalizer (Tbar : Set (Y ⧸ Z))).map e.toMonoidHom := by
      simpa using hmem
    exact (Subgroup.mem_map_iff_mem e.injective).1 hmem'
  have hfpfBar : ∀ x ∈ Tbar, e.symm d * x * (e.symm d)⁻¹ = x → x = 1 := by
    intro x hx hfix
    apply e.injective
    have hxS : e x ∈ S := by
      rw [hS]; exact Subgroup.mem_map_of_mem _ hx
    have hfixS : d * e x * d⁻¹ = e x := by
      have := congrArg e hfix
      simpa [d, mul_assoc] using this
    simpa using hDfpf d hdD hd1 (e x) hxS hfixS
  obtain ⟨dY, hdY⟩ := QuotientGroup.mk'_surjective Z (e.symm d)
  have hdN' : e.symm d ∈ Subgroup.normalizer
      (T.map (QuotientGroup.mk' Z) : Set (Y ⧸ Z)) := by rwa [hTbarDef] at hdN
  have hfpfBar' : ∀ x ∈ T.map (QuotientGroup.mk' Z),
      e.symm d * x * (e.symm d)⁻¹ = x → x = 1 := by
    intro x hx
    exact hfpfBar x (hTbarDef ▸ hx)
  have hlift := normalize_and_fixedPointFree_of_map (T := T) (Z := Z) hZ hTZ hwc hdY hdN' hfpfBar' 
  have hperfY : commutator Y = ⊤ :=
    commutator_eq_top_of_fixedPointFree hlift.1 hlift.2 hgen
  exact hperfY


private theorem sz_center
    (hZ : Z ≤ Subgroup.center Y) {a : ℕ} (ha : 1 ≤ a) {F : Type}
    [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F) : Z = Subgroup.center Y := by
  have hcenterQuot : Subgroup.center (Y ⧸ Z) = ⊥ := by
    have hmap : (Subgroup.center (Y ⧸ Z)).map e.toMonoidHom =
        Subgroup.center (CFSG.Blueprint.suzukiGroup a F) := Subgroup.map_center_eq e
    rw [show Subgroup.center (CFSG.Blueprint.suzukiGroup a F) = ⊥ from
      CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha
        (by rw [Nat.card_eq_fintype_card]; exact hF)] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap
  exact center_eq_of_center_quotient_eq_bot hZ hcenterQuot

theorem centralTI_sz
    {Y : Type} [Group Y] [Finite Y] {T Z : Subgroup Y} [Z.Normal]
    (hT : CFSG.Assembly.IsElemAbelian 2 T) (hgen : Subgroup.normalClosure (T : Set Y) = ⊤)
    (hTI : IsTI T) (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ (2 * a + 1))
    (e : Y ⧸ Z ≃* CFSG.Blueprint.suzukiGroup a F) : Z = ⊥ := by
  classical
  have hTZ : T ⊓ Z = ⊥ := sz_TZ hT hgen hTI hZ ha hF e
  obtain ⟨Tbar, S, c₀, hTbarP, hTbarNe, hTbarSq, hTbarWc, hS, hSP, hSNe, hSSq,
    hSWc, hS_eq, hScard, hTbarDef⟩ :=
    sz_Tbar_data hT hgen hwc hZ hTZ ha hF e
  have hperfY : commutator Y = ⊤ :=
    sz_perfect_of_torus hgen hwc hZ hTZ ha hF e hS hSP hSNe hSSq hSWc hScard hTbarDef
  have hcenterY : Z = Subgroup.center Y := sz_center hZ ha hF e
  have hZ2 : IsPGroup 2 Z := isPGroup_two_of_sz_quotient hZ hcenterY hperfY hF e
  by_cases hZbot : Z = ⊥
  · exact hZbot
  · have hS_eq' : (T.map (QuotientGroup.mk' Z)).map e.toMonoidHom =
        conjSubgroup c₀ (szZ a F) := by
      rw [← hTbarDef, ← hS]
      exact hS_eq
    exact False.elim (false_of_isPGroup_two (a := a) (F := F) hT hTZ hwc hZ hZ2 hZbot
      hperfY ha hF e (c₀ := c₀) hS_eq')



end CFSG.RankThree.GF2n.Tim81.CentralTI
