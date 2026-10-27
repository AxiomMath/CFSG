module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1R0
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.RankThree.PartTwo.Sec15.Item15Type

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_subgroupOf_of_mem_normalizer {Q : Type*} [Group Q]
    {H K : Subgroup Q} {w : Q} (hwK : w ∈ K)
    (hwH : w ∈ Subgroup.normalizer (H : Set Q)) :
    (⟨w, hwK⟩ : K) ∈ Subgroup.normalizer ((H.subgroupOf K : Subgroup K) : Set K) := by
  have hwK' : w ∈ Subgroup.normalizer (K : Set Q) := Subgroup.le_normalizer hwK
  have hwHK : w ∈ Subgroup.normalizer ((H ⊓ K : Subgroup Q) : Set Q) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hwH, hwK'⟩)
  have hEq : (H ⊓ K).subgroupOf K = H.subgroupOf K := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [← hEq, ← Subgroup.subgroupOf_normalizer_eq inf_le_right]
  exact Subgroup.mem_subgroupOf.mpr hwHK

theorem inf_centralizer_eq_bot_of_isComponent_of_isSimple {Q : Type*} [Group Q]
    {Y : Subgroup Q} (hYcomp : CFSG.IsComponent Y) (hsimple : IsSimpleGroup Y) :
    Y ⊓ Subgroup.centralizer (Y : Set Q) = ⊥ := by
  have hZ : Subgroup.center Y = ⊥ := by
    obtain ⟨a, b, hab⟩ := hYcomp.1.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine center_eq_bot_of_isSimpleGroup hsimple ⟨x, y, fun hxy => hab ?_⟩
    rw [← QuotientGroup.mk_mul (Subgroup.center Y) x y,
      ← QuotientGroup.mk_mul (Subgroup.center Y) y x, hxy]
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have hx' : x ∈ (Subgroup.center Y).map Y.subtype :=
    (CFSG.LocalCores.mem_map_center_iff Y).mpr hx
  rw [hZ, Subgroup.map_bot] at hx'
  exact Subgroup.mem_bot.mp hx'

theorem res1_isPGroup_two_inf_sup_centralizer {Q : Type*} [Group Q]
    {Y O C : Subgroup Q} [C.Normal] (hO2 : IsPGroup 2 O)
    (hC : C = Subgroup.centralizer (Y : Set Q)) (hYC : Y ⊓ C = ⊥) :
    IsPGroup 2 ((Y ⊓ (O ⊔ C)).subgroupOf Y) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro r
  have hrSup : ((r : Y) : Q) ∈ ((O ⊔ C : Subgroup Q) : Set Q) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp r.2)).2
  rw [Subgroup.mul_normal] at hrSup
  obtain ⟨o, ho, z, hz, hoz⟩ := Set.mem_mul.mp hrSup
  obtain ⟨k, hk⟩ := hO2.exists_pow_pow_eq_one ⟨o, ho⟩
  have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute ((r : Y) : Q) z := by
    have hz' : z ∈ Subgroup.centralizer (Y : Set Q) := hC ▸ hz
    exact Subgroup.mem_centralizer_iff.mp hz' ((r : Y) : Q) (r : Y).2
  have ho_eq : o = ((r : Y) : Q) * z⁻¹ := by
    rw [← hoz]
    group
  have hpow : ((r : Y) : Q) ^ 2 ^ k * (z ^ 2 ^ k)⁻¹ = 1 := by
    have h1 : (((r : Y) : Q) * z⁻¹) ^ 2 ^ k = 1 := by rw [← ho_eq]; exact hok
    simpa [inv_pow, (hcomm.inv_right).mul_pow] using h1
  have hrz : ((r : Y) : Q) ^ 2 ^ k = z ^ 2 ^ k := by
    have := congrArg (fun t => t * z ^ 2 ^ k) hpow
    simpa [mul_assoc] using this
  refine ⟨k, Subtype.ext ?_⟩
  have hmem : ((r : Y) : Q) ^ 2 ^ k ∈ Y ⊓ C := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Y.pow_mem (r : Y).2 _
    · rw [hrz]
      exact C.pow_mem hz _
  rw [hYC] at hmem
  apply Subtype.ext
  exact Subgroup.mem_bot.mp hmem

theorem res1_subgroupOf_inf_sup_ne_bot {Q : Type*} [Group Q]
    {Y O C : Subgroup Q} {w y : Q} (hwO : w ∈ O)
    (hC : C = Subgroup.centralizer (Y : Set Q)) (hyY : y ∈ Y) (hynot : y ≠ 1)
    (hact : ∀ z ∈ Y, w * z * w⁻¹ = y * z * y⁻¹) :
    (Y ⊓ (O ⊔ C)).subgroupOf Y ≠ ⊥ := by
  have hu : w⁻¹ * y ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : y * z = w * z * w⁻¹ * y := by
      rw [hact z hz]
      group
    calc z * (w⁻¹ * y) = w⁻¹ * (w * z * w⁻¹ * y) := by group
      _ = w⁻¹ * (y * z) := by rw [← h1]
      _ = (w⁻¹ * y) * z := by group
  have hRhat : y ∈ Y ⊓ (O ⊔ C) :=
    Subgroup.mem_inf.mpr ⟨hyY, by simpa using Subgroup.mul_mem_sup hwO hu⟩
  let r : (Y ⊓ (O ⊔ C)).subgroupOf Y :=
    ⟨⟨y, hyY⟩, by rw [Subgroup.mem_subgroupOf]; exact hRhat⟩
  have hrne : r ≠ 1 := by
    intro h
    apply hynot
    exact congrArg (fun x : Y => (x : Q)) (Subtype.ext_iff.mp h)
  intro hbot
  have hr_eq_one : r = 1 := by
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (by simpa [hbot] using r.2)
  exact hrne hr_eq_one

theorem res1_normalizer_sylow_map_of_le {Q : Type*} [Group Q] [Finite Q]
    {Y : Subgroup Q} [Y.Normal]
    {Rhat : Subgroup Q} {R : Subgroup Y} {n : Q}
    (hR : R = Rhat.subgroupOf Y) (hnRhat : n ∈ Subgroup.normalizer (Rhat : Set Q))
    (hRne : R ≠ ⊥) (U : Sylow 2 Y) (hRU : R ≤ (U : Subgroup Y))
    (hT : ∀ U V : Sylow 2 Y, U ≠ V → (U : Subgroup Y) ⊓ V = ⊥) :
    n ∈ Subgroup.normalizer ((((U : Subgroup Y).map Y.subtype : Subgroup Q)) : Set Q) := by
  classical
  let φ : MulAut Y := MulAut.conjNormal n
  let U' : Sylow 2 Y := Sylow.mapSurjective (G' := Y) (f := φ.toMonoidHom) φ.surjective U
  have hU'coe : (U' : Subgroup Y) = (U : Subgroup Y).map φ.toMonoidHom := by
    simpa [U'] using Sylow.coe_mapSurjective (f := φ.toMonoidHom) (P := U)
  have hmemR_iff : ∀ x : Y, (x : Q) ∈ Rhat ↔ (φ.symm x : Q) ∈ Rhat := by
    intro x
    have hninv : n⁻¹ ∈ Subgroup.normalizer (Rhat : Set Q) :=
      (Subgroup.normalizer (Rhat : Set Q)).inv_mem hnRhat
    have h := Subgroup.mem_normalizer_iff.mp hninv (x : Q)
    simpa [φ, MulAut.conjNormal_symm_apply] using h
  have hRU' : R ≤ (U' : Subgroup Y) := by
    rw [hU'coe]
    intro r hr
    have hrinvR : φ.symm r ∈ R := by
      rw [hR] at hr ⊢
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      exact (hmemR_iff r).mp hr
    refine Subgroup.mem_map.mpr ⟨φ.symm r, hRU hrinvR, ?_⟩
    exact MulEquiv.apply_symm_apply φ r
  have hU'eq : U' = U := by
    by_contra hne
    have hbot : (U : Subgroup Y) ⊓ (U' : Subgroup Y) = ⊥ := hT U U' (fun h => hne h.symm)
    have hle : R ≤ (U : Subgroup Y) ⊓ (U' : Subgroup Y) := le_inf hRU hRU'
    have hRbot : R ≤ ⊥ := hbot ▸ hle
    exact hRne (le_bot_iff.mp hRbot)
  have hUmap : (U : Subgroup Y).map φ.toMonoidHom = (U : Subgroup Y) := by
    have := congrArg (fun S : Sylow 2 Y => (S : Subgroup Y)) hU'eq
    rwa [hU'coe] at this
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcomp : (MulAut.conj n).toMonoidHom.comp Y.subtype =
      Y.subtype.comp φ.toMonoidHom := by
    ext y
    simp [φ, MulAut.conj_apply, MulAut.conjNormal_apply]
  calc ((U : Subgroup Y).map Y.subtype).map (MulAut.conj n).toMonoidHom
      = (U : Subgroup Y).map ((MulAut.conj n).toMonoidHom.comp Y.subtype) :=
        Subgroup.map_map _ _ _
    _ = (U : Subgroup Y).map (Y.subtype.comp φ.toMonoidHom) := by rw [hcomp]
    _ = ((U : Subgroup Y).map φ.toMonoidHom).map Y.subtype := (Subgroup.map_map _ _ _).symm
    _ = (U : Subgroup Y).map Y.subtype := by rw [hUmap]

theorem mem_of_mem_map_comap_subtype {G Q : Type*} [Group G] [Group Q]
    {C : Subgroup G} {π : C →* Q} {Y : Subgroup Q} {c : G} {c' : C}
    (hcY : c ∈ (Y.comap π).map C.subtype) (hc : (c' : G) = c) : π c' ∈ Y := by
  obtain ⟨x, hx, hxval⟩ := hcY
  have hxeq : x = c' := Subtype.ext (hxval.trans hc.symm)
  rw [hxeq] at hx
  exact Subgroup.mem_comap.mp hx

theorem orderOf_mk'_eq_three_of_coprime {C : Type*} [Group C] [Finite C]
    {N : Subgroup C} [N.Normal] (hN : Nat.Coprime 3 (Nat.card N)) {x : C}
    (hx3 : orderOf x = 3) : orderOf (QuotientGroup.mk' N x) = 3 := by
  have hne : QuotientGroup.mk' N x ≠ 1 := by
    intro h1
    have hmem : x ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hdvd : 3 ∣ Nat.card N := by
      have h := orderOf_dvd_natCard (⟨x, hmem⟩ : N)
      rwa [Subgroup.orderOf_mk, hx3] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN hdvd
  have hdvd : orderOf (QuotientGroup.mk' N x) ∣ 3 := by
    simpa [hx3] using orderOf_map_dvd (QuotientGroup.mk' N) x
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h3

theorem conj_mem_normalizer_and_orderOf {Q : Type*} [Group Q]
    {Y H : Subgroup Q} [Y.Normal] {n y : Q} (hyY : y ∈ Y)
    (hyH : y ∈ Subgroup.normalizer (H : Set Q))
    (hnH : n ∈ Subgroup.normalizer (H : Set Q)) :
    n * y * n⁻¹ ∈ Y ∧ n * y * n⁻¹ ∈ Subgroup.normalizer (H : Set Q) ∧
      orderOf (n * y * n⁻¹) = orderOf y := by
  refine ⟨Subgroup.Normal.conj_mem (inferInstance : Y.Normal) y hyY n, ?_, ?_⟩
  · exact (Subgroup.normalizer (H : Set Q)).mul_mem
      ((Subgroup.normalizer (H : Set Q)).mul_mem hnH hyH)
      ((Subgroup.normalizer (H : Set Q)).inv_mem hnH)
  · exact (SemiconjBy.orderOf_eq n (SemiconjBy.conj_mk n y)).symm

theorem mem_normalizer_subgroupOf_map_subtype {Q : Type*} [Group Q]
    {Y : Subgroup Q} {U : Subgroup Y} {n : Q} (hnY : n ∈ Y)
    (hn : n ∈ Subgroup.normalizer ((U.map Y.subtype : Subgroup Q) : Set Q)) :
    (⟨n, hnY⟩ : Y) ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y) := by
  have hHY : U.map Y.subtype ≤ Y := Subgroup.map_subtype_le U
  have hsub : (U.map Y.subtype).subgroupOf Y = U := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHY]
  rw [← hsub, ← Subgroup.subgroupOf_normalizer_eq hHY]
  exact Subgroup.mem_subgroupOf.mpr hn


private theorem res1_exists_sylow_two_candidate {A L M : Subgroup G} {c : G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) (hAM : A ≤ M)
    (h142 : Concl142 A (lB A)) (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc) :
    ∃ (U : Sylow 2 ↥Yc) (Rhat : Subgroup (Res1Q A L)),
      Rhat = Yc ⊓ (((CFSG.Open.pCoreOf 2 M).subgroupOf (Res1C A L)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))) ⊔
        Subgroup.centralizer (Yc : Set (Res1Q A L))) ∧
      (Rhat.subgroupOf Yc) ≠ ⊥ ∧ (Rhat.subgroupOf Yc) ≤ (U : Subgroup ↥Yc) := by
  classical
  haveI hYn : Yc.Normal :=
    Sylow155R1.res1_isComponent_normal hS hY.1 hY.2.2.2.1.1
  let π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))
  let Cc : Subgroup (Res1Q A L) := Subgroup.centralizer (Yc : Set (Res1Q A L))
  haveI hCc : Cc.Normal := Subgroup.normal_centralizer
  let Oh : Subgroup ↥(Res1C A L) := (CFSG.Open.pCoreOf 2 M).subgroupOf (Res1C A L)
  let Rhat : Subgroup (Res1Q A L) := Yc ⊓ (Oh.map π ⊔ Cc)
  let R : Subgroup ↥Yc := Rhat.subgroupOf Yc
  have hYcomp : CFSG.IsComponent Yc := hY.2.2.2.1.1
  have hcenter : Yc ⊓ Cc = ⊥ := by
    simpa [Cc] using inf_centralizer_eq_bot_of_isComponent_of_isSimple hYcomp hsimple
  have hO2 : IsPGroup 2 Oh :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).comap_subtype
  have hOmap2 : IsPGroup 2 (Oh.map π) := hO2.map π
  have hR2 : IsPGroup 2 R :=
    res1_isPGroup_two_inf_sup_centralizer (Y := Yc) (O := Oh.map π) (C := Cc)
      hOmap2 rfl hcenter
  obtain ⟨w0, hw0O, y0, hy0Y, hy0ne, hy0act⟩ :=
    Sylow155R1.res1_exists_inner hS hAM h142 hY
  have hRne : R ≠ ⊥ := by
    apply res1_subgroupOf_inf_sup_ne_bot (Y := Yc) (O := Oh.map π) (C := Cc)
      (w := π w0) (y := y0)
    · exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hw0O)
    · rfl
    · exact hy0Y
    · exact hy0ne
    · exact hy0act
  obtain ⟨U, hRU⟩ := IsPGroup.exists_le_sylow hR2
  exact ⟨U, Rhat, rfl, hRne, hRU⟩

theorem res1_orderOf_pi_c'_eq_three {A L : Subgroup G} {c : G}
    {c' : ↥(Res1C A L)} (hS : Sec14Std G A c L) (hc' : (c' : G) = c) :
    orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') = 3 := by
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).2.1
  have hc'3 : orderOf c' = 3 := by
    rw [← Subgroup.orderOf_coe c', hc', hc3]
  exact orderOf_mk'_eq_three_of_coprime
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(Res1C A L))) hc'3

theorem map_mem_sup_zpowers {Q : Type*} [Group Q] {Y : Subgroup Q}
    (U : Subgroup Y) (y : Y) {z : Y} (hz : z ∈ U ⊔ Subgroup.zpowers y) :
    (z : Q) ∈ U.map Y.subtype ⊔ Subgroup.zpowers (y : Q) := by
  have h := Subgroup.mem_map_of_mem Y.subtype hz
  rwa [Subgroup.map_sup, MonoidHom.map_zpowers] at h

theorem map_commutator_eq_conj_mul_inv {C Q : Type*} [Group C] [Group Q]
    (π : C →* Q) (w x : C) :
    π (w * x * w⁻¹ * x⁻¹) = (π w * π x * (π w)⁻¹) * (π x)⁻¹ := by
  simp [map_mul]

theorem mul_inv_mem_sup_zpowers {Q : Type*} [Group Q] {U : Subgroup Q}
    {y z : Q} (hz : z ∈ U ⊔ Subgroup.zpowers y) : z * y⁻¹ ∈ U ⊔ Subgroup.zpowers y := by
  exact (U ⊔ Subgroup.zpowers y).mul_mem hz
    ((U ⊔ Subgroup.zpowers y).inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))

theorem res1_exists_sylow_two_normalized {A L M : Subgroup G} {c : G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) (hAM : A ≤ M)
    (h142 : Concl142 A (lB A)) (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hT : ∀ U V : Sylow 2 ↥Yc, U ≠ V → (U : Subgroup ↥Yc) ⊓ V = ⊥) :
    ∃ U : Sylow 2 ↥Yc, ∀ w : ↥(Res1C A L),
      (w : G) ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) →
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w ∈
          Subgroup.normalizer
            (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)) := by
  obtain ⟨U, Rhat, hRhat_eq, hRne, hRU⟩ :=
    res1_exists_sylow_two_candidate hS hAM h142 hY hsimple
  refine ⟨U, ?_⟩
  intro w hwO
  haveI hYn : Yc.Normal :=
    Sylow155R1.res1_isComponent_normal hS hY.1 hY.2.2.2.1.1
  let π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))
  let Cc : Subgroup (Res1Q A L) := Subgroup.centralizer (Yc : Set (Res1Q A L))
  let Oh : Subgroup ↥(Res1C A L) := (CFSG.Open.pCoreOf 2 M).subgroupOf (Res1C A L)
  haveI hCc : Cc.Normal := Subgroup.normal_centralizer
  let n : Res1Q A L := π w
  have hwOh : w ∈ Subgroup.normalizer (Oh : Set ↥(Res1C A L)) := by
    simpa [Oh] using mem_normalizer_subgroupOf_of_mem_normalizer w.2 hwO
  have hnO : n ∈ Subgroup.normalizer ((Oh.map π : Subgroup (Res1Q A L)) : Set (Res1Q A L)) := by
    simpa [n] using Subgroup.le_normalizer_map (H := Oh) π
      (Subgroup.mem_map_of_mem π hwOh)
  have hnY : n ∈ Subgroup.normalizer (Yc : Set (Res1Q A L)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top n
  have hnRhat' : n ∈ Subgroup.normalizer
      ((Yc ⊓ (Oh.map π ⊔ Cc) : Subgroup (Res1Q A L)) : Set (Res1Q A L)) := by
    have hnC : n ∈ Subgroup.normalizer (Cc : Set (Res1Q A L)) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top n
    have hnSup : n ∈ Subgroup.normalizer
        ((Oh.map π ⊔ Cc : Subgroup (Res1Q A L)) : Set (Res1Q A L)) :=
      Subgroup.inf_normalizer_le_normalizer_sup (Oh.map π) Cc
        (Subgroup.mem_inf.mpr ⟨hnO, hnC⟩)
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := Yc) (K := Oh.map π ⊔ Cc)
      (Subgroup.mem_inf.mpr ⟨hnY, hnSup⟩)
  have hnRhat : n ∈ Subgroup.normalizer (Rhat : Set (Res1Q A L)) := by
    rw [hRhat_eq]
    simpa [π, Cc, Oh] using hnRhat'
  exact res1_normalizer_sylow_map_of_le (Y := Yc) (Rhat := Rhat) (R := Rhat.subgroupOf Yc)
    (n := n) rfl hnRhat hRne U hRU hT

theorem res1_commutator_mem_sup {A L M : Subgroup G} {c : G} {Yc : Subgroup (Res1Q A L)}
    (hS : Sec14Std G A c L) (hY : Res1AtOf A c L M Yc) (hYF : Res1HJYFacts ↥Yc)
    (U : Sylow 2 ↥Yc) {c' w : ↥(Res1C A L)} (hc' : (c' : G) = c)
    (hcU : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈
      Subgroup.normalizer
        (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L)))
    (hwU : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w ∈
      Subgroup.normalizer
        (((U : Subgroup ↥Yc).map Yc.subtype : Subgroup (Res1Q A L)) : Set (Res1Q A L))) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) (w * c' * w⁻¹ * c'⁻¹) ∈
      (U : Subgroup ↥Yc).map Yc.subtype ⊔
        Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c') := by
  classical
  let π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))
  let y : Res1Q A L := π c'
  haveI hYn : Yc.Normal :=
    Sylow155R1.res1_isComponent_normal hS hY.1 hY.2.2.2.1.1
  have hyY : y ∈ Yc := mem_of_mem_map_comap_subtype hY.2.2.2.1.2.1 hc'
  have hy3 : orderOf y = 3 := by
    simpa [y, π] using res1_orderOf_pi_c'_eq_three hS hc'
  let n : Res1Q A L := π w
  let z : Res1Q A L := n * y * n⁻¹
  let H : Subgroup (Res1Q A L) := (U : Subgroup ↥Yc).map Yc.subtype
  have hyNorm := mem_normalizer_subgroupOf_map_subtype hyY hcU
  have hzdata := conj_mem_normalizer_and_orderOf (Y := Yc) (H := H)
    (n := n) (y := y) hyY hcU hwU
  have hzY : z ∈ Yc := by simpa [z] using hzdata.1
  have hz3 : orderOf z = 3 := by
    rw [show z = n * y * n⁻¹ from rfl, hzdata.2.2]
    exact hy3
  have hzNorm := mem_normalizer_subgroupOf_map_subtype hzY hzdata.2.1
  have hyN3 : orderOf (⟨y, hyY⟩ : ↥Yc) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨y, hyY⟩ : ↥Yc)]
    exact hy3
  have hzN3 : orderOf (⟨z, hzY⟩ : ↥Yc) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨z, hzY⟩ : ↥Yc)]
    exact hz3
  have hmem : (⟨z, hzY⟩ : ↥Yc) ∈
      (U : Subgroup ↥Yc) ⊔ Subgroup.zpowers (⟨y, hyY⟩ : ↥Yc) :=
    hYF.2.1 U ⟨y, hyY⟩ ⟨z, hzY⟩ hyNorm hzNorm hyN3 hzN3
  have hmapmem : z ∈ (U : Subgroup ↥Yc).map Yc.subtype ⊔ Subgroup.zpowers y :=
    map_mem_sup_zpowers (U := (U : Subgroup ↥Yc)) (y := ⟨y, hyY⟩) hmem
  rw [map_commutator_eq_conj_mul_inv π w c']
  change z * y⁻¹ ∈ (U : Subgroup ↥Yc).map Yc.subtype ⊔ Subgroup.zpowers y
  exact mul_inv_mem_sup_zpowers hmapmem

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
