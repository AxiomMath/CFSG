module

public import CFSG.Quasithin.Background.E6TwentyThreeJ
public import CFSG.Quasithin.Background.ONanE68Lin3
public import CFSG.Quasithin.H13.KGFactE623A3L34
public import CFSG.Quasithin.H13.KGFactE623A3Sp4
public import CFSG.Quasithin.H13.KGFactE623U34
public import CFSG.Quasithin.H13.KGFactE623Sp4Cent
public import CFSG.Quasithin.SteinbergUnitaryOuterPrimeControl
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.KGE623A3

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom onCenterQuotient_apply_mk onCenterQuotient_eq_one_imp)

section Generic

theorem mk_eq_of_mul_inv_mem_center {G : Type*} [Group G] {g h : G}
    (hgh : g * h⁻¹ ∈ Subgroup.center G) : (g : G ⧸ Subgroup.center G) = h := by
  rw [QuotientGroup.eq]
  have h1 : h * g⁻¹ ∈ Subgroup.center G := by simpa using inv_mem hgh
  exact (Subgroup.Normal.mem_comm_iff inferInstance).mp h1

theorem mem_inner_of_pow_three {J : Type*} [Group J] (hO : Nat.card (Outer J) ∣ 4)
    {τ : MulAut J} (hτ : τ ^ 3 = 1) : τ ∈ inner J := by
  set o : Outer J := QuotientGroup.mk τ with ho
  have ho3 : o ^ 3 = 1 := by rw [ho, ← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
  have h1 : orderOf o ∣ Nat.gcd 3 4 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ho3) ((orderOf_dvd_natCard o).trans hO)
  have h2 : orderOf o = 1 := Nat.dvd_one.mp (by simpa using h1)
  rw [orderOf_eq_one_iff, ho, QuotientGroup.eq_one_iff] at h2
  exact h2

theorem pCoreOf_map_subtype {Y : Type*} [Group Y] (X : Subgroup Y) (C : Subgroup ↥X) :
    CFSG.Open.pCoreOf 2 (C.map X.subtype) = (CFSG.Open.pCoreOf 2 C).map X.subtype := by
  let e : C ≃* C.map X.subtype := C.equivMapOfInjective X.subtype X.subtype_injective
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  unfold CFSG.Open.pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H] (e : G ≃* H) (c : G) :
    (Subgroup.centralizer ({c} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e c} : Set H) := by
  ext z
  obtain ⟨g, rfl⟩ := e.surjective z
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem exists_mulEquiv_map_eq_of_two {G Γ : Type*} [Group G] [Group Γ] [Finite G]
    (e₁ : G ≃* Γ) {T : Subgroup G} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) {S₀ : Subgroup Γ}
    (hS₀ : IsPGroup 2 S₀) (hS₀i : ¬ 2 ∣ S₀.index) : ∃ e : G ≃* Γ, T.map e.toMonoidHom = S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Γ := Finite.of_equiv G e₁.toEquiv
  have hU1 : IsPGroup 2 (T.map e₁.toMonoidHom) := hT.map _
  have hU1i : ¬ 2 ∣ (T.map e₁.toMonoidHom).index := by
    rw [show T.map e₁.toMonoidHom = T.map (e₁ : G →* Γ) from rfl, Subgroup.index_map_equiv]
    exact hTi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hS₀.toSylow hS₀i) (hU1.toSylow hU1i)
  have hmem : ∀ z, z ∈ T.map e₁.toMonoidHom ↔ g⁻¹ * z * g ∈ S₀ := by
    intro z
    have h1 : T.map e₁.toMonoidHom = ((g • hS₀.toSylow hS₀i : Sylow 2 Γ) : Subgroup Γ) := by
      rw [hg]
      rfl
    rw [h1, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨e₁.trans (MulAut.conj g⁻¹), ?_⟩
  have he : ∀ y : G, (e₁.trans (MulAut.conj g⁻¹)) y = g⁻¹ * e₁ y * g := fun y => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (e₁.trans (MulAut.conj g⁻¹)) y ∈ _
    rw [he]
    exact (hmem _).mp ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, hye⟩ := (hmem (g * x * g⁻¹)).mpr (by
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group])
    refine ⟨y, hy, ?_⟩
    change (e₁.trans (MulAut.conj g⁻¹)) y = x
    rw [he]
    change e₁ y = g * x * g⁻¹ at hye
    rw [hye]
    group

end Generic

section PSL2

theorem eq_one_of_comm_alt5 : ∀ (π : Equiv.Perm (Fin 5)) (c : alternatingGroup (Fin 5)),
    π ^ 3 = 1 → c ^ 2 = 1 → c ≠ 1 →
      π * (c : Equiv.Perm (Fin 5)) = (c : Equiv.Perm (Fin 5)) * π → π = 1 := by
  decide +kernel

theorem eq_one_of_psl2 {X : Type} [Group X] [Group.IsPerfect X]
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 2) {τ : MulAut X}
    (hτ3 : τ ^ 3 = 1) {c : X} (hcZ : c ∉ Subgroup.center X) (hc2 : c * c ∈ Subgroup.center X)
    (hτc : τ c * c⁻¹ ∈ Subgroup.center X) : τ = 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := h
  obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl (by rw [hK]; norm_num))
  set eA : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 5) := e₀.trans e₅ with heA
  set τb : MulAut (X ⧸ Subgroup.center X) := centerQuotientHom X τ with hτb
  set cb : X ⧸ Subgroup.center X := (c : X ⧸ Subgroup.center X) with hcb
  have hτbc : τb cb = cb :=
    (onCenterQuotient_apply_mk τ c).trans (mk_eq_of_mul_inv_mem_center hτc)
  have hcb1 : cb ≠ 1 := fun h1 => hcZ ((QuotientGroup.eq_one_iff c).mp h1)
  have hcb2 : cb * cb = 1 := by
    rw [hcb, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff (c * c)).mpr hc2
  have hτb3 : τb ^ 3 = 1 := by rw [hτb, ← map_pow, hτ3, map_one]
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 (MulAut.congr eA τb)
  have hπ3 : π ^ 3 = 1 := hbij.1 (by rw [map_pow, hπ, ← map_pow, hτb3, map_one, map_one])
  set c' := eA cb with hc'
  have hc'2 : c' ^ 2 = 1 := by rw [hc', pow_two, ← map_mul, hcb2, map_one]
  have hc'1 : c' ≠ 1 := fun h1 => hcb1 (eA.injective (h1.trans (map_one eA).symm))
  have hπc : π * (c' : Equiv.Perm (Fin 5)) = (c' : Equiv.Perm (Fin 5)) * π := by
    have h1 : MulAut.congr eA τb c' = c' := by
      rw [hc', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hτbc]
    rw [← hπ] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    calc π * (c' : Equiv.Perm (Fin 5)) = (π * c' * π⁻¹) * π := by group
      _ = c' * π := by rw [h2]
  have hπ1 := eq_one_of_comm_alt5 π c' hπ3 hc'2 hc'1 hπc
  have hb1 : τb = 1 := (MulAut.congr eA).injective (by rw [← hπ, hπ1, map_one, map_one])
  exact onCenterQuotient_eq_one_imp τ hb1

end PSL2

section PSU3

theorem eq_one_of_psu3 {X : Type}
    [Group X] [Finite X] (hqs : CFSG.IsQuasisimple X)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 2) {τ : MulAut X}
    (hτ3 : τ ^ 3 = 1) {c : X} (hcZ : c ∉ Subgroup.center X) (hc2 : c * c ∈ Subgroup.center X)
    (hτc : τ c * c⁻¹ ∈ Subgroup.center X) : τ = 1 := by
  obtain ⟨hperf, hsimp, hnab⟩ := hqs
  have hin : τ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := h
    have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 K :=
      ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
    have hO := (OuterPrimeControl.perfect_unitary_central_quotient_outer_prime_control hu
      (n := 3) le_rfl (by norm_num) X
      (e₀.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hu (by norm_num)).symm)).1
    exact mem_inner_of_pow_three (by norm_num at hO; exact hO) hτ3
  obtain ⟨w, rfl⟩ := hin
  have hw3 : (w : X ⧸ Subgroup.center X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    have h1 : (MulAut.conj w ^ 3) g = (1 : MulAut X) g := by rw [hτ3]
    rw [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * w ^ 3 = (w ^ 3 * g * (w ^ 3)⁻¹) * w ^ 3 := by rw [h1]
      _ = w ^ 3 * g := by group
  have hwc : (w : X ⧸ Subgroup.center X) * c = c * w := by
    rw [MulAut.conj_apply] at hτc
    have h1 : ((w * c * w⁻¹ : X) : X ⧸ Subgroup.center X) = c := mk_eq_of_mul_inv_mem_center hτc
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    calc (w : X ⧸ Subgroup.center X) * c =
        ((w : X ⧸ Subgroup.center X) * c * (w : X ⧸ Subgroup.center X)⁻¹) * w := by group
      _ = c * w := by rw [h1]
  have hcb2 : (c : X ⧸ Subgroup.center X) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hc2
  have hcb1 : (c : X ⧸ Subgroup.center X) ≠ 1 := fun h1 =>
    hcZ ((QuotientGroup.eq_one_iff c).mp h1)
  have := hsimp
  have hw1 := KGE623.eq_one_of_psu34 hnab h hw3 hcb2 hcb1 hwc
  have hwZ : w ∈ Subgroup.center X := (QuotientGroup.eq_one_iff w).mp hw1
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hwZ g).symm,
    mul_inv_cancel_right]

end PSU3

section PSL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Lin2.L3Core

theorem false_of_psl3 {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hZ2 : IsPGroup 2 (Subgroup.center X))
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 2) {S : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) {τ : MulAut X} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {c : X} (hcS : ∀ s ∈ S, c * s = s * c) (hcZ : c ∉ Subgroup.center X)
    (hc2 : c * c ∈ Subgroup.center X) (hτc : τ c * c⁻¹ ∈ Subgroup.center X) {E : Finset X}
    (hE : E.card ≤ 4)
    (hbd : ∀ r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set X)), τ r * r⁻¹ ∈ E) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := h
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])
  set q := QuotientGroup.mk' (Subgroup.center X) with hq
  have hq1 : ∀ g, q g = 1 ↔ g ∈ Subgroup.center X := fun g => by
    rw [← MonoidHom.mem_ker, hq, QuotientGroup.ker_mk']
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hZS : Subgroup.center X ≤ S := hZ2.le_sylow_of_normal (hS2.toSylow hSi)
  set Sb := S.map q with hSb
  have hmemS : ∀ g : X, q g ∈ Sb ↔ g ∈ S := by
    intro g
    constructor
    · rintro ⟨s, hs, hsg⟩
      have h1 : q (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
      simpa using mul_mem hs (hZS ((hq1 _).mp h1))
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hSb2 : IsPGroup 2 Sb := hS2.map q
  have hSbi : ¬ 2 ∣ Sb.index := fun h2 => hSi (h2.trans (Subgroup.index_map_dvd S hqsurj))
  let e₁ : X ⧸ Subgroup.center X ≃* projectiveSL 3 F :=
    (e₀.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  obtain ⟨e, he⟩ := E6.E68Proof.Lin3.exists_mulEquiv_map_eq_projUnitriangular e₁ hSb2 hSbi
  set cb := q c with hcb
  have hcb1 : cb ≠ 1 := fun h1 => hcZ ((hq1 c).mp h1)
  have hcbb : cb * cb = 1 := by rw [hcb, ← map_mul]; exact (hq1 _).mpr hc2
  have hcbS : ∀ t ∈ Sb, cb * t = t * cb := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hcb, ← map_mul, ← map_mul, hcS s hs]
  have hcbSb : cb ∈ Sb := (KG68.mem_omegaZ_of_commute (hSb2.toSylow hSbi) hcbS hcbb).1
  have hecU : e cb ∈ projUnitriangular 3 F := (E6.E68Proof.Lin3.mem_iff_of_map he cb).mpr hcbSb
  have hecC : ∀ y ∈ projUnitriangular 3 F, e cb * y = y * e cb := by
    intro y hy
    rw [← he] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    change e cb * e t = e t * e cb
    rw [← map_mul, ← map_mul, hcbS t ht]
  have hecc : e cb * e cb = 1 := by rw [← map_mul, hcbb, map_one]
  obtain ⟨c₀, hc₀⟩ := E6.E68Proof.Lin3.mem_omegaCenter_iff.mp ⟨hecU, hecC, hecc⟩
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    apply hcb1
    apply e.injective
    rw [hc₀, map_one, hei_zero_zero, wP_eq_one_iff]
  have hecw : e cb = proj 3 F (wMat c₀) := hc₀.trans (hei_zero_zero c₀)
  have hCN : Subgroup.centralizer ({c} : Set X) ≤ Subgroup.normalizer (S : Set X) := by
    intro g hg
    have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have h1 : e (q g) * hei 0 0 c₀ = hei 0 0 c₀ * e (q g) := by
      rw [← hc₀, ← map_mul, ← map_mul, hcb, ← map_mul, ← map_mul, hgc]
    have h2 := (E6.E68Proof.Lin3.map_mem_normalizer_iff he (q g)).mp
      (E6.E68Proof.Lin3.mem_normalizer_of_comm_hei hc₀0 h1)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [← hmemS t, ← hmemS (g * t * g⁻¹), map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp h2 (q t)
  have hSC : S ≤ Subgroup.centralizer ({c} : Set X) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcS s hs).symm
  have hSO : S ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set X)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSC hCN hS2
  set τb : MulAut (X ⧸ Subgroup.center X) := centerQuotientHom X τ with hτb
  have hτbq : ∀ g, τb (q g) = q (τ g) := fun g => onCenterQuotient_apply_mk τ g
  set τ' : MulAut (projectiveSL 3 F) := MulAut.congr e τb with hτ'
  have hτ'e : ∀ t, τ' (e t) = e (τb t) := fun t => by
    rw [hτ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hτ'3 : τ' ^ 3 = 1 := by rw [hτ', hτb, ← map_pow, ← map_pow, hτ3, map_one, map_one]
  have hτ'1 : τ' ≠ 1 := by
    intro h1
    apply hτ1
    apply onCenterQuotient_eq_one_imp τ
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  have hτ'c : τ' (proj 3 F (wMat c₀)) = proj 3 F (wMat c₀) := by
    have h1 : τb cb = cb := by
      rw [hcb, hτbq]
      have h2 : q (τ c * c⁻¹) = 1 := (hq1 _).mpr hτc
      rwa [map_mul, map_inv, mul_inv_eq_one] at h2
    rw [← hecw, hτ'e, h1]
  set E' := E.image (fun g => e (q g)) with hE'
  have hE'4 : E'.card ≤ 4 := Finset.card_image_le.trans hE
  have hbd' : ∀ u ∈ projUnitriangular 3 F, τ' u * u⁻¹ ∈ E' := by
    intro u hu
    rw [← he] at hu
    obtain ⟨t, ⟨s, hs, rfl⟩, rfl⟩ := hu
    refine Finset.mem_image.mpr ⟨τ s * s⁻¹, hbd s (hSO hs), ?_⟩
    change e (q (τ s * s⁻¹)) = τ' (e (q s)) * (e (q s))⁻¹
    rw [hτ'e, hτbq]
    simp only [map_mul, map_inv]
  exact false_of_aut_projSL3_four hF4 hτ'3 hτ'1 hc₀0 hτ'c hE'4 hbd'

end PSL3

section PSp4

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (perfect_symplectic_central_quotient_outer_prime_control)

theorem false_of_psp4 (hSp : KGE623.Sp44OrderThreeCent) {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] (h : StatedClassicalModel X .PSp 2 2 2) {S : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) {τ : MulAut X} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {c : X} (hcS : ∀ s ∈ S, c * s = s * c) (hcZ : c ∉ Subgroup.center X)
    (hc2 : c * c ∈ Subgroup.center X) (hτc : τ c * c⁻¹ ∈ Subgroup.center X) {E : Finset X}
    (hE : E.card ≤ 4)
    (hbd : ∀ r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set X)), τ r * r⁻¹ ∈ E) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  have hZ : Subgroup.center X = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => φ.injective ?_
    rw [map_one]
    refine Id2519.USp4.eq_one_of_central fun p => ?_
    obtain ⟨g, rfl⟩ := φ.surjective p
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz g).symm]
  have hO := (perfect_symplectic_central_quotient_outer_prime_control
    Nat.prime_two (f := 2) (r := 2) (by norm_num) le_rfl hK X
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ⟩).2.2.1
  obtain ⟨w, hw⟩ := mem_inner_of_pow_three (by norm_num at hO; exact hO) hτ3
  have hw3 : w ^ 3 = 1 := KG68.conj_injective_of_center hZ (by rw [map_pow, hw, hτ3, map_one])
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hτ1 (by rw [← hw, map_one])
  have hcc : c * c = 1 := by
    rw [hZ] at hc2
    exact Subgroup.mem_bot.mp hc2
  have hc1 : c ≠ 1 := fun h1 => hcZ (by rw [h1]; exact Subgroup.one_mem _)
  have hwc : w * c = c * w := by
    have h1 : τ c * c⁻¹ = 1 := by
      rw [hZ] at hτc
      exact Subgroup.mem_bot.mp hτc
    rw [← hw, MulAut.conj_apply, mul_inv_eq_one] at h1
    calc w * c = (w * c * w⁻¹) * w := by group
      _ = c * w := by rw [h1]
  have hcSS : c ∈ S := (KG68.mem_omegaZ_of_commute (hS2.toSylow hSi) hcS hcc).1
  obtain ⟨-, -, hU2, hUi⟩ := card_and_isSylowTwoOf_antiUnipotent (K := K)
  have hUi' : ¬ 2 ∣ (antiUnipotent K).index := by
    rw [← Subgroup.relIndex_top_right]
    exact hUi
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_map_eq_of_two (φ.trans (antiProjEquiv K).symm) hS2 hSi hU2 hUi'
  set b' := ψ c with hb'
  have hb'Z : b' ∈ antiUnipotentCenter K := by
    refine (mem_antiUnipotentCenter_iff_central b').mpr ⟨?_, ?_⟩
    · rw [← hψ]
      exact ⟨c, hcSS, rfl⟩
    · intro u hu
      rw [← hψ] at hu
      obtain ⟨s, hs, rfl⟩ := hu
      change ψ c * ψ s = ψ s * ψ c
      rw [← map_mul, ← map_mul, hcS s hs]
  have hb'1 : b' ≠ 1 := fun h1 => hc1 (ψ.injective (h1.trans (map_one ψ).symm))
  set y := ψ w with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, hw3, map_one]
  have hy1 : y ≠ 1 := fun h1 => hw1 (ψ.injective (h1.trans (map_one ψ).symm))
  have hyb : y * b' = b' * y := by rw [hy, hb', ← map_mul, ← map_mul, hwc]
  set E' := E.image ψ with hE'
  have hE'4 : E'.card ≤ 4 := Finset.card_image_le.trans hE
  have hbd' : ∀ r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({b'} : Set (antiSp K))),
      y * r * y⁻¹ * r⁻¹ ∈ E' := by
    intro r hr
    obtain ⟨r₀, rfl⟩ := ψ.surjective r
    have hr₀ : r₀ ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set X)) := by
      rw [hb', ← map_centralizer_singleton ψ c,
        CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 ψ] at hr
      rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hr
    refine Finset.mem_image.mpr ⟨τ r₀ * r₀⁻¹, hbd r₀ hr₀, ?_⟩
    rw [← hw, MulAut.conj_apply, hy]
    simp only [map_mul, map_inv]
  exact false_of_antiSp_four hK4 hSp hy3 hy1 hb'Z hb'1 hyb hE'4 hbd'

end PSp4

section Main

theorem e623CentA3Comp_holds :
    E6.E623CentA3Comp := by
  classical
  intro Y _ _ X S E a b x hqs hZ2 htype hS haS haN ha2 haC hbX hab hxN hx3 hxa hE hbd
  have : Group.IsPerfect ↥X := hqs.1
  rw [← KG68.conjOn_eq_one_iff X hxN]
  set τ := KG68.conjOn X x hxN with hτ
  set b₀ : ↥X := ⟨b, hbX⟩ with hb₀
  have hτ3 : τ ^ 3 = 1 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
    show x * (x * (x * (g : Y) * x⁻¹) * x⁻¹) * x⁻¹ = g
    have hx3' : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
    calc x * (x * (x * (g : Y) * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * g * (x * (x * x))⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = g := by rw [hx3', one_mul, inv_one, mul_one]
  have hbS : ∀ s ∈ S, b * s = s * b := by
    intro s hs
    have h1 := hab s (hS.1 hs)
    have h2 : a * s * a⁻¹ = s := by rw [haS s hs]; group
    rw [h2] at h1
    calc b * s = (b * s * b⁻¹) * b := by group
      _ = s * b := by rw [← h1]
  have hcZ : b₀ ∉ Subgroup.center ↥X := by
    intro hZ
    apply haC
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := hab g hg
    have h2 : g * b = b * g := congrArg Subtype.val (Subgroup.mem_center_iff.mp hZ ⟨g, hg⟩)
    have h3 : b * g * b⁻¹ = g := by rw [← h2]; group
    rw [h3] at h1
    calc g * a = (a * g * a⁻¹) * a := by rw [h1]
      _ = a * g := by group
  have hc2 : b₀ * b₀ ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Y) * (b * b) = b * b * g
    have h1 := hab g g.2
    have hg' : b * g * b⁻¹ ∈ X := mul_mem (mul_mem hbX g.2) (inv_mem hbX)
    have h2 := hab _ hg'
    have haa : a * a = 1 := by rw [← pow_two]; exact ha2
    have h3 : b * b * g * (b * b)⁻¹ = g := by
      calc b * b * g * (b * b)⁻¹ = b * (b * g * b⁻¹) * b⁻¹ := by group
        _ = a * (b * g * b⁻¹) * a⁻¹ := by rw [h2]
        _ = a * (a * g * a⁻¹) * a⁻¹ := by rw [h1]
        _ = (a * a) * g * (a * a)⁻¹ := by group
        _ = g := by rw [haa]; group
    calc (g : Y) * (b * b) = (b * b * g * (b * b)⁻¹) * (b * b) := by rw [h3]
      _ = b * b * g := by group
  have hτc : τ b₀ * b₀⁻¹ ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Y) * (x * b * x⁻¹ * b⁻¹) = x * b * x⁻¹ * b⁻¹ * g
    have hxa' : x * a * x⁻¹ = a := by rw [hxa]; group
    have key : ∀ h ∈ X, (x * b * x⁻¹) * h * (x * b * x⁻¹)⁻¹ = b * h * b⁻¹ := by
      intro h hh
      have h1 : x⁻¹ * h * x ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) h).mp hh
        simpa using this
      have h2 := hab _ h1
      calc (x * b * x⁻¹) * h * (x * b * x⁻¹)⁻¹ = x * (b * (x⁻¹ * h * x) * b⁻¹) * x⁻¹ := by
            group
        _ = x * (a * (x⁻¹ * h * x) * a⁻¹) * x⁻¹ := by rw [h2]
        _ = (x * a * x⁻¹) * h * (x * a * x⁻¹)⁻¹ := by group
        _ = a * h * a⁻¹ := by rw [hxa']
        _ = b * h * b⁻¹ := hab h hh
    have hg' : b⁻¹ * g * b ∈ X := mul_mem (mul_mem (inv_mem hbX) g.2) hbX
    have h3 := key _ hg'
    have h4 : b * (b⁻¹ * g * b) * b⁻¹ = g := by group
    rw [h4] at h3
    calc (g : Y) * (x * b * x⁻¹ * b⁻¹) =
        ((x * b * x⁻¹) * (b⁻¹ * g * b) * (x * b * x⁻¹)⁻¹) * (x * b * x⁻¹ * b⁻¹) := by rw [h3]
      _ = x * b * x⁻¹ * b⁻¹ * g := by group
  have hS2 : IsPGroup 2 (S.subgroupOf X) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSi : ¬ 2 ∣ (S.subgroupOf X).index := hS.2.2
  have hcS : ∀ s ∈ S.subgroupOf X, b₀ * s = s * b₀ := fun s hs => Subtype.ext (hbS s hs)
  have hCmap : (Subgroup.centralizer ({b₀} : Set ↥X)).map X.subtype =
      X ⊓ Subgroup.centralizer ({a} : Set Y) := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      have h0 : g' * b₀ = b₀ * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'
      have h1 : (g' : Y) * b = b * g' := congrArg Subtype.val h0
      have h2 := hab g' g'.2
      have h3 : b * g' * b⁻¹ = g' := by rw [← h1]; group
      rw [h3] at h2
      refine Subgroup.mem_inf.mpr ⟨g'.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      show (g' : Y) * a = a * g'
      calc (g' : Y) * a = (a * g' * a⁻¹) * a := by rw [h2]
        _ = a * g' := by group
    · intro hg
      obtain ⟨hgX, hga'⟩ := Subgroup.mem_inf.mp hg
      have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hga'
      refine ⟨⟨g, hgX⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
      show g * b = b * g
      have h2 := hab g hgX
      have h3 : a * g * a⁻¹ = g := by rw [← hga]; group
      rw [h3] at h2
      calc g * b = (b * g * b⁻¹) * b := by rw [← h2]
        _ = b * g := by group
  have : Fintype ↥X := Fintype.ofFinite _
  set EX := Finset.univ.filter (fun g : ↥X => (g : Y) ∈ E) with hEX
  have hEX4 : EX.card ≤ 4 := by
    refine le_trans ?_ hE
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun g => (⟨(g.1 : Y), (Finset.mem_filter.mp g.2).2⟩ : ↥E)) fun g h hgh => ?_
    have h1 : ((g.1 : ↥X) : Y) = ((h.1 : ↥X) : Y) := congrArg (fun z : ↥E => (z : Y)) hgh
    exact Subtype.ext (Subtype.ext h1)
  have hbdX : ∀ r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({b₀} : Set ↥X)), τ r * r⁻¹ ∈ EX := by
    intro r hr
    have h1 : (r : Y) ∈ CFSG.Open.pCoreOf 2 (X ⊓ Subgroup.centralizer ({a} : Set Y)) := by
      rw [← hCmap, pCoreOf_map_subtype]
      exact ⟨r, hr, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbd _ h1⟩
  rcases htype with h2 | h3 | hu | hsp
  · exact eq_one_of_psl2 h2 hτ3 hcZ hc2 hτc
  · by_contra hτ1
    exact false_of_psl3 hZ2 h3 hS2 hSi hτ3 hτ1 hcS hcZ hc2 hτc hEX4 hbdX
  · exact eq_one_of_psu3 hqs hu hτ3 hcZ hc2 hτc
  · by_contra hτ1
    exact false_of_psp4 KGE623.sp44OrderThreeCent_holds hsp hS2 hSi hτ3 hτ1 hcS hcZ hc2 hτc
      hEX4 hbdX

end Main

end CFSG.Quasithin.H13.KGE623A3
