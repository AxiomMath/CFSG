module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ACore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification

@[expose] def GGLBalanceInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.lBalanceIsKGroup X → ∀ (p : ℕ), p.Prime →
    ∀ (P : Subgroup X), IsPGroup p P →
      CFSG.Open.lBalancePLayer p (Subgroup.centralizer (P : Set X)) ≤
        CFSG.Open.lBalancePLayer p ⊤

theorem ggLBalanceInput_of_milestone
    (h : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.lBalanceIsKGroup X → ∀ (p : ℕ),
      p.Prime → ∀ (P : Subgroup X), IsPGroup p P →
        CFSG.Open.lBalancePLayer p (Subgroup.normalizer (P : Set X)) ≤
            CFSG.Open.lBalancePLayer p ⊤ ∧
          CFSG.Open.lBalancePLayer p (Subgroup.centralizer (P : Set X)) ≤
            CFSG.Open.lBalancePLayer p ⊤ ∧
          (CFSG.Open.lBalancePrimeCore p (⊤ : Subgroup X) = ⊥ →
            ∀ a ∈ CFSG.Open.lBalancePLayer p (Subgroup.normalizer (P : Set X)),
              ∀ b ∈ CFSG.Open.lBalancePrimeCore p (Subgroup.normalizer (P : Set X)),
                a * b = b * a)) :
    GGLBalanceInput :=
  fun X _ _ hK p hp P hP => (h X hK p hp P hP).2.1

@[expose] def GGStdSubPrimeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp p B x L → LargeEvenStdSub p B x L D J → p ∣ Nat.card J

section Prelim

variable {G : Type} [Group G]

theorem centralizer_singleton_ne_top_of_isSimpleGroup [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {y : G} (hy : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≠ ⊤ := by
  intro htop
  have hz : y ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact hy hz
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center G := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem lBalanceIsKGroup_of_kProper (hK : KProper InCatalog G) {X : Subgroup G} (hX : X ≠ ⊤) :
    CFSG.Open.lBalanceIsKGroup ↥X :=
  CFSG.KCore.KProperNonab.kGroupNonab inCatalog_isoInvariant hK X hX

variable [Finite G]

theorem lBalancePLayer_inf_centralizer_le_of_input (hL : GGLBalanceInput) {p : ℕ}
    (hp : p.Prime) {X : Subgroup G} (hX : CFSG.Open.lBalanceIsKGroup ↥X) {x : G} (hxX : x ∈ X)
    (hxp : x ^ p = 1) :
    CFSG.Open.lBalancePLayer p (X ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      CFSG.Open.lBalancePLayer p X := by
  set x' : X := ⟨x, hxX⟩
  have hx'p : x' ^ p = 1 := Subtype.ext (by simp [x', hxp])
  have hP : IsPGroup p (Subgroup.zpowers x') := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hx'p, one_zpow, Subgroup.coe_one]
  have hC : (X ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf X =
      Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup X) : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem, true_and,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [← LBalance.pLayer_nested_map p (X ⊓ Subgroup.centralizer ({x} : Set G)) X inf_le_left, hC,
    ← LBalance.pLayer_nested_map p X X le_rfl, Subgroup.subgroupOf_self]
  exact Subgroup.map_mono (hL X hX p hp _ hP)

theorem isComponentOf_inf_centralizer_of_stdSub {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : LargeEvenSStar p B x L) (hDJ : LargeEvenStdSubPre p B x L D J)
    {y : G} (hD : D = Subgroup.closure {x, y}) :
    IsComponentOf J (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hDJ.2.2.2.2.2.1
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hL.1]
  rw [hLD] at hJc
  have h := isComponentOf_of_isSubnormal_of_isComponentOf hJc
    (LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hL.2.1
      (Subgroup.centralizer ({y} : Set G)))
  rwa [inf_comm (Subgroup.centralizer ({x} : Set G))] at h

omit [Finite G] in
theorem prime_dvd_card_of_not_commutator_le {p : ℕ} (hp : p.Prime) {K : Subgroup G} {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (h : ¬ (⁅K, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K) :
    p ∣ Nat.card K := by
  by_contra hnd
  apply h
  have htop : LargeEvenPPrimeCore p ↥K = ⊤ := by
    refine top_le_iff.mp (le_sSup ⟨inferInstance, ?_⟩)
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have hcore : LargeEvenPPrimeCoreOf p K = K := by
    unfold LargeEvenPPrimeCoreOf
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hcore, Subgroup.commutator_le]
  intro k hk z hz
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := (Subgroup.zpowers_le.mpr hxK) hz
  have hkz : k * z * k⁻¹ * z⁻¹ = k * (z * k⁻¹ * z⁻¹) := by group
  rw [commutatorElement_def, hkz]
  exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hzN k⁻¹).mp (K.inv_mem hk))

end Prelim

section Main

variable {G : Type} [Group G] [Finite G]

theorem largeEvenPLayer_le_sup_centralizer_of_ggNbr {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) {y : G}
    {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G)) ≤
      K ⊔ Subgroup.centralizer (K : Set G) := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hBK⟩ := isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hDJ hnbr)
  have hpK : p ∣ Nat.card K :=
    prime_dvd_card_of_not_commutator_le hp (hBK hI.2.2.2.2.2.2.1.2.1) hnbr.2.2.2
  rw [largeEvenPLayer_eq_lBalancePLayer]
  exact lBalancePLayer_le_sup_centralizer hKc (not_le_lBalancePrimeCore_of_dvd hpK)

theorem not_le_centralizer_of_ggNbr
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K) :
    ¬ J ≤ Subgroup.centralizer (K : Set G) := by
  intro hJC
  have hEK := largeEvenPLayer_le_sup_centralizer_of_ggNbr hI hDJ hnbr
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hDJ hnbr)
  have hNK : LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G)) ≤
      Subgroup.normalizer (K : Set G) :=
    hEK.trans (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
  have hKC : K ≤ Subgroup.centralizer (K : Set G) := by
    refine hnbr.2.2.1.trans (iSup₂_le fun a ha => ?_)
    have ha' : a⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
      normalizer_le_normalizer_centralizer K (hNK (Subgroup.inv_mem _ ha))
    calc J.map (MulAut.conj a⁻¹).toMonoidHom ≤
          (Subgroup.centralizer (K : Set G)).map (MulAut.conj a⁻¹).toMonoidHom :=
        Subgroup.map_mono hJC
      _ = Subgroup.centralizer (K : Set G) := map_conj_eq_of_mem_normalizer ha'
  exact commutator_ne_bot_of_isQuasisimple hKc.2.2
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKC)

theorem le_of_ggNbr_of_le_sup_centralizer
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K)
    (hJSup : J ≤ K ⊔ Subgroup.centralizer (K : Set G)) : J ≤ K := by
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  obtain ⟨hKc, hBK⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hnbr)
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hBK hS.2.1
  have hJY := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnbr.2.1
  rcases isComponentOf_le_or_commutator_eq_bot hJY
      (LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hKc.2.1
        (Subgroup.centralizer ({x} : Set G))) with h | h
  · exact h.trans inf_le_left
  · exfalso
    have hJC := le_centralizer_of_le_sup_centralizer
      (commutator_self_eq_of_isQuasisimple hJY.2.2) hJSup
      (hJY.1.trans inf_le_right) hxK h
    exact not_le_centralizer_of_ggNbr hI hDJ hnbr hJC

theorem le_normalizer_of_ggNbr_of_noncentral_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K)
    (hfixed : ∃ z ∈ K ⊓ Subgroup.centralizer ({x} : Set G),
      z ∉ Subgroup.centralizer (K : Set G)) :
    J ≤ Subgroup.normalizer (K : Set G) := by
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf
    hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hnbr)
  have hJc := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnbr.2.1
  rcases isComponentOf_le_or_commutator_eq_bot hJc
      (LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hKc.2.1
        (Subgroup.centralizer ({x} : Set G))) with hJK | hcomm
  · exact hJK.trans (inf_le_left.trans Subgroup.le_normalizer)
  · obtain ⟨z, hz, hznc⟩ := hfixed
    intro j hj
    have hjy : j * y = y * j :=
      Subgroup.mem_centralizer_singleton_iff.mp ((hJc.1 hj).1)
    have hjline : j ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
      apply mem_normalizer_iff_map_conj.mpr
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (j * y * j⁻¹) = Subgroup.zpowers y
      rw [hjy, mul_inv_cancel_right]
    rcases map_conj_eq_or_le_centralizer hKc hjline with heq | hcen
    · exact mem_normalizer_iff_map_conj.mpr heq
    · have hzj : z * j = j * z :=
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hj) z hz
      have hzmap : z ∈ K.map (MulAut.conj j).toMonoidHom := by
        refine ⟨z, hz.1, ?_⟩
        change j * z * j⁻¹ = z
        rw [← hzj, mul_inv_cancel_right]
      exact False.elim (hznc (hcen hzmap))

theorem le_of_ggNbr_of_normalizes_of_outer_solvable
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K)
    (hJN : J ≤ Subgroup.normalizer (K : Set G))
    (hOut : Group.IsSolvable (OuterAutomorphisms.Outer K)) : J ≤ K := by
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hJY := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnbr.2.1
  have : Group.IsPerfect J := ⟨hJY.2.2.1⟩
  have : Group.IsSolvable (OuterAutomorphisms.Outer K) := hOut
  have hJSup : J ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
    let action : J →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hJN)
    intro j hj
    obtain ⟨k, heq⟩ := OuterAutomorphisms.perfect_action_inner action ⟨j, hj⟩
    have hconj : ∀ z ∈ K, j * z * j⁻¹ = (k : G) * z * (k : G)⁻¹ := by
      intro z hz
      exact congrArg (fun a : MulAut K => (a ⟨z, hz⟩).val) heq
    have hcent : (k : G)⁻¹ * j ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h := hconj z hz
      calc
        z * ((k : G)⁻¹ * j) = (k : G)⁻¹ * ((k : G) * z * (k : G)⁻¹) * j := by group
        _ = (k : G)⁻¹ * (j * z * j⁻¹) * j := by rw [h]
        _ = ((k : G)⁻¹ * j) * z := by group
    have hmem := Subgroup.mul_mem_sup k.2 hcent
    simpa only [mul_inv_cancel_left] using hmem
  exact le_of_ggNbr_of_le_sup_centralizer hI hDJ hnbr hJSup

theorem le_of_ggNbr_of_noncentral_fixed_of_outer_solvable
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K)
    (hfixed : ∃ z ∈ K ⊓ Subgroup.centralizer ({x} : Set G),
      z ∉ Subgroup.centralizer (K : Set G))
    (hOut : Group.IsSolvable (OuterAutomorphisms.Outer K)) : J ≤ K :=
  le_of_ggNbr_of_normalizes_of_outer_solvable hI hDJ hnbr
    (le_normalizer_of_ggNbr_of_noncentral_fixed hI hDJ hnbr hfixed) hOut

theorem noncentral_fixed_of_ggNbr_of_prime_not_dvd_center
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : CFSG.Assembly.LargeEvenStdSub p B x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) :
    ∃ z ∈ K ⊓ Subgroup.centralizer ({x} : Set G),
      z ∉ Subgroup.centralizer (K : Set G) := by
  have hS : CFSG.Assembly.LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hBK⟩ := isComponentOf_of_isNeighborOf
    hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hnbr)
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hBK hS.2.1
  have hpK : p ∣ Nat.card K :=
    prime_dvd_card_of_not_commutator_le hp hxK hnbr.2.2.2
  have hx : orderOf x = p := orderOf_eq_prime (hS.1.1.2 x hS.2.1) hS.2.2.1
  obtain ⟨z, hzK, hzp, hzx⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L122A.exists_fixed_elt hp hpK hx hxK
  refine ⟨z, ⟨hzK, Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm⟩, ?_⟩
  intro hzC
  have hzZ : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
    apply Subgroup.mem_center_iff.mpr
    intro k
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC k k.2
  have ho : orderOf (⟨⟨z, hzK⟩, hzZ⟩ : Subgroup.center K) = p := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hzp
  exact hZ (ho ▸ orderOf_dvd_natCard (⟨⟨z, hzK⟩, hzZ⟩ : Subgroup.center K))

theorem le_of_ggNbr_of_prime_not_dvd_center_of_outer_solvable
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : CFSG.Assembly.LargeEvenStdSub p B x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)) :
    J ≤ K :=
  le_of_ggNbr_of_noncentral_fixed_of_outer_solvable hI hDJ hnbr
    (noncentral_fixed_of_ggNbr_of_prime_not_dvd_center hI hDJ hnbr hZ) hOut


theorem le_of_ggNbr (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) : J ≤ K := by
  have hEK := largeEvenPLayer_le_sup_centralizer_of_ggNbr hI hDJ hnbr
  have hICopy := hI
  obtain ⟨hsimple, hnab, hKP, -, -, hβ, hS, hst⟩ := hICopy
  have : IsSimpleGroup G := hsimple
  have hp : p.Prime := hβ.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hBK⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hnbr)
  have hxB : x ∈ B := hS.2.1
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hBK hxB
  have hyB : y ∈ B := hnbr.1.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hxy : x * y = y * x :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨y, hyB⟩)
  have hxX : x ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxy
  have hJY := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnbr.2.1
  have hJE : J ≤ CFSG.Open.lBalancePLayer p
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    le_sSup (lBalanceIsPComponent_of_isComponentOf hJY (not_le_lBalancePrimeCore_of_dvd hpJ))
  have hYX := lBalancePLayer_inf_centralizer_le_of_input hL hp
    (lBalanceIsKGroup_of_kProper hKP
      (centralizer_singleton_ne_top_of_isSimpleGroup hnab hnbr.1.2.2.1)) hxX hxp
  rw [largeEvenPLayer_eq_lBalancePLayer] at hEK
  exact le_of_ggNbr_of_le_sup_centralizer hI hDJ hnbr ((hJE.trans hYX).trans hEK)

theorem ggNbrSubcomponentInput_of_lBalance (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGNbrSubcomponentInput :=
  fun G _ _ p B x L D J hI hDJ _ _ hnbr =>
    le_of_ggNbr hL hI hDJ (hP G p B x L D J hI hDJ) hnbr

theorem ggNbr_eq_iSup (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    K = ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G))),
      J.map (MulAut.conj a⁻¹).toMonoidHom := by
  have hJK := le_of_ggNbr hL hI hDJ hpJ hnbr
  have hNK : LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G)) ≤
      Subgroup.normalizer (K : Set G) :=
    (largeEvenPLayer_le_sup_centralizer_of_ggNbr hI hDJ hnbr).trans
      (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
  refine le_antisymm hnbr.2.2.1 (iSup₂_le fun a ha => ?_)
  exact (Subgroup.map_mono hJK).trans
    (map_conj_eq_of_mem_normalizer (hNK (Subgroup.inv_mem _ ha))).le

theorem ggNbr_unique (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y y' : G} {K K' : Subgroup G} (hnbr : GGNbr p B x D J y K)
    (hnbr' : GGNbr p B x D J y' K') (hyy' : Subgroup.zpowers y = Subgroup.zpowers y') :
    K = K' := by
  rw [ggNbr_eq_iSup hL hI hDJ hpJ hnbr, ggNbr_eq_iSup hL hI hDJ hpJ hnbr',
    centralizer_singleton_eq_of_zpowers_eq hyy']

theorem ggNbr_eq_of_le (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K)
    {K' : Subgroup G} (hK' : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K')
    (hJK' : J ≤ K') : K' = K := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hJK := le_of_ggNbr hL hI hDJ hpJ hnbr
  obtain ⟨hKc, hBK⟩ := isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hDJ hnbr)
  have hpK : p ∣ Nat.card K :=
    prime_dvd_card_of_not_commutator_le hp (hBK hI.2.2.2.2.2.2.1.2.1) hnbr.2.2.2
  rcases lBalanceIsPComponent_eq_or_commute hKc (not_le_lBalancePrimeCore_of_dvd hpK)
      ((largeEvenPComponent_iff_lBalance p _ K').1 hK').2 with h | h
  · exact h
  · exfalso
    apply commutator_ne_bot_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
    exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono hJK' hJK)

theorem normalizer_inf_le_of_ggNbr (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊓ Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  rintro g ⟨hgy, hgJ⟩
  have hzy : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers y := by
    have h1 : Subgroup.zpowers (g * y * g⁻¹) =
        (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp
    rw [h1]
    exact map_conj_eq_of_mem_normalizer hgy
  have hCy : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
    exact centralizer_singleton_eq_of_zpowers_eq hzy
  have hK' := largeEvenPComponent_map_conj' hnbr.1.2.2.2.2.1 g
  rw [hCy] at hK'
  have hJK' : J ≤ K.map (MulAut.conj g).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer hgJ]
    exact Subgroup.map_mono (le_of_ggNbr hL hI hDJ hpJ hnbr)
  exact mem_normalizer_iff_map_conj.mpr (ggNbr_eq_of_le hL hI hDJ hpJ hnbr hK' hJK')

theorem normalizer_inf_normalizer_le_of_ggNbr (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers y : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hND : Subgroup.normalizer (Subgroup.zpowers x : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers y : Set G) ≤ Subgroup.normalizer (D : Set G) := by
    rintro g ⟨hgx, hgy⟩
    rw [mem_normalizer_iff_map_conj, hnbr.2.1, closure_pair_eq_sup, Subgroup.map_sup,
      map_conj_eq_of_mem_normalizer hgx, map_conj_eq_of_mem_normalizer hgy]
  have hNJ : Subgroup.normalizer (Subgroup.zpowers x : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers y : Set G) ≤ Subgroup.normalizer (J : Set G) := by
    rw [hDJ.1.2.2.2.2.1]
    exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
      (mem_normalizer_inf (mem_normalizer_of_sstar' hS hnc hg.1)
        (normalizer_le_normalizer_centralizer D (hND hg)))
  intro g hg
  exact normalizer_inf_le_of_ggNbr hL hI hDJ hpJ hnbr ⟨hg.2, hNJ hg⟩

theorem eq_of_le_of_stdSub {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) (hpJ : p ∣ Nat.card J) :
    J ≤ L ∧ LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L ∧
      ∀ L' : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L' →
        J ≤ L' → L' = L := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hI.2.2.2.2.2.2.1.2.2.2.1
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  have hLO : ¬ L ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)) :=
    not_le_lBalancePrimeCore_of_dvd (hpJ.trans (Subgroup.card_dvd_of_le hJL))
  refine ⟨hJL, (largeEvenPComponent_iff_lBalance p _ L).2
    ⟨hL.1, lBalanceIsPComponent_of_isComponentOf hL hLO⟩, fun L' hL' hJL' => ?_⟩
  rcases lBalanceIsPComponent_eq_or_commute hL hLO
      ((largeEvenPComponent_iff_lBalance p _ L').1 hL').2 with h | h
  · exact h
  · exfalso
    apply commutator_ne_bot_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
    exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono hJL' hJL)

end Main


section Prime

variable {G : Type} [Group G] [Finite G]

theorem prime_dvd_card_of_config_small {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hs : Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3 →
      ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G)) :
    p ∣ Nat.card J := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  by_cases hR : p ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G)
  · have hpg : IsPGroup p (Bs ⊓ J : Subgroup G) := fun g =>
      ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hBs.2 g g.2.1, Subgroup.coe_one])⟩
    rcases hpg.card_eq_or_dvd with h1 | h1
    · exfalso
      rw [h1] at hR
      exact absurd hR (not_le.mpr (Nat.one_lt_pow (by norm_num) hp.one_lt))
    · exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)
  · obtain ⟨b, hb, hbC⟩ := hs (not_le.mp hR)
    have hb1 : b ≠ 1 := fun h => hbC (h ▸ Subgroup.one_mem _)
    have hob : orderOf b = p := orderOf_eq_prime (hBs.2 b hb.1) hb1
    rw [← hob, ← Subgroup.orderOf_mk b hb.2]
    exact orderOf_dvd_natCard _

theorem ggStdSubPrimeInput_of_small (hB : GGBstarInput) (hs : GGStdSubSmallInput) :
    GGStdSubPrimeInput := fun G _ _ p B x L D J hI hDJ => by
  obtain ⟨Bs, hBs⟩ := hB G p B x L hI
  have hcfg : GGConfig p B Bs x L D J := ⟨hI, hBs, hDJ⟩
  exact prime_dvd_card_of_config_small hcfg fun h => (hs G p B Bs x L D J hcfg h).2

theorem ggStdSubPrimeInput_of_bstarMeet (hB : GGBstarInput) (h2 : GGStdSubBstarMeetInput) :
    GGStdSubPrimeInput := fun G _ _ p B x L D J hI hDJ => by
  obtain ⟨Bs, hBs⟩ := hB G p B x L hI
  have hcfg : GGConfig p B Bs x L D J := ⟨hI, hBs, hDJ⟩
  exact prime_dvd_card_of_config_small hcfg fun _ => h2 G p B Bs x L D J hcfg

theorem ggNbrSubcomponentInput_of_small (hL : GGLBalanceInput) (hB : GGBstarInput)
    (hs : GGStdSubSmallInput) : GGNbrSubcomponentInput :=
  ggNbrSubcomponentInput_of_lBalance hL (ggStdSubPrimeInput_of_small hB hs)

theorem ggFieldNbrCanonicalInput_of_lBalance (hL : GGLBalanceInput) (h4 : GGFieldNbrInnerInput)
    (hs : GGStdSubSmallInput) : GGFieldNbrCanonicalInput :=
  fun G _ _ p B Bs x L D J hcfg =>
    ggFieldNbrCanonical_of_small hcfg
      (fun _ _ hnbr => le_of_ggNbr hL hcfg.1 hcfg.2.2
        (prime_dvd_card_of_config_small hcfg fun h => (hs G p B Bs x L D J hcfg h).2) hnbr)
      (h4 G p B Bs x L D J hcfg) (hs G p B Bs x L D J hcfg)

end Prime


section Pumpup

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_largeEvenPPrimeCoreOf {p : ℕ} {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (LargeEvenPPrimeCoreOf p A : Set G) := by
  rw [mem_normalizer_iff_map_conj, ← largeEvenPPrimeCoreOf_map_conj,
    map_conj_eq_of_mem_normalizer hg]

theorem le_normalizer_of_largeEvenStandardType {p : ℕ} {B : Subgroup G} {x : G}
    {L : Subgroup G} (hst : LargeEvenStandardType p B x L) :
    B ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, lab, -, hraw⟩ := hst.1
  obtain ⟨R, _, I, F, -, -, θ, -, hBN, -⟩ := largeEvenRawDatum_exists hraw
  exact hBN

theorem le_normalizer_of_stdSub {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L)
    (hDJ : LargeEvenStdSubPre p B x L D J) : B ≤ Subgroup.normalizer (J : Set G) := by
  have hBD : B ≤ Subgroup.centralizer (D : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨d, hDJ.1 hd⟩ : ↥B) ⟨b, hb⟩)
  rw [hDJ.2.2.2.2.1]
  exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
    (mem_normalizer_inf_centralizer (le_normalizer_of_largeEvenStandardType hst hg) (hBD hg))

omit [Finite G] in
theorem commutator_le_of_le_sup {p : ℕ} {A J : Subgroup G} {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hJA : J ≤ A) (hle : A ≤ J ⊔ LargeEvenPPrimeCoreOf p A) :
    (⁅A, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p A := by
  set O := LargeEvenPPrimeCoreOf p A with hOdef
  have hOA : O ≤ A := Subgroup.map_subtype_le _
  have hON : A ≤ Subgroup.normalizer (O : Set G) := fun a ha =>
    mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer ha)
  have hxO : x ∈ Subgroup.normalizer (O : Set G) := mem_normalizer_largeEvenPPrimeCoreOf hxA
  rw [Subgroup.commutator_le]
  intro a ha z hz
  have hzO : z ∈ Subgroup.normalizer (O : Set G) := (Subgroup.zpowers_le.mpr hxO) hz
  have hzJ : ∀ j ∈ J, z * j = j * z := fun j hj =>
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun j' hj' =>
      Subgroup.mem_centralizer_singleton_iff.mp (hJx hj')) hz |>
      fun h => (Subgroup.mem_centralizer_iff.mp h j hj).symm)
  have ha' : a ∈ ((O ⊔ J : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hle ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O J (hJA.trans hON)] at ha'
  obtain ⟨o, ho, j, hj, rfl⟩ := ha'
  have h1 : ⁅o * j, z⁆ = o * (z * o⁻¹ * z⁻¹) := by
    rw [commutatorElement_def]
    calc o * j * z * (o * j)⁻¹ * z⁻¹ = o * (j * z) * j⁻¹ * o⁻¹ * z⁻¹ := by group
      _ = o * (z * j) * j⁻¹ * o⁻¹ * z⁻¹ := by rw [hzJ j hj]
      _ = o * (z * o⁻¹ * z⁻¹) := by group
  rw [h1]
  exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.mp hzO o⁻¹).mp (O.inv_mem ho))

theorem not_le_sup_of_ggNbr (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    ¬ K ≤ J ⊔ LargeEvenPPrimeCoreOf p K := fun hle => by
  obtain ⟨-, hBK⟩ := isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hDJ hnbr)
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) :=
    (isComponentOf_inf_centralizer_of_stdSub hI.2.2.2.2.2.2.1 hDJ.1 hnbr.2.1).1.trans
      inf_le_right
  exact hnbr.2.2.2 (commutator_le_of_le_sup (hBK hI.2.2.2.2.2.2.1.2.1) hJx
    (le_of_ggNbr hL hI hDJ hpJ hnbr) hle)

theorem lt_of_ggNbr (hL : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) : J < K :=
  lt_of_le_of_ne (le_of_ggNbr hL hI hDJ hpJ hnbr) fun h =>
    not_le_sup_of_ggNbr hL hI hDJ hpJ hnbr (h ▸ le_sup_left)

omit [Finite G] in
theorem mem_centralizer_of_commutator_le_coprime {p : ℕ} (hp : p.Prime) {J N : Subgroup G}
    {b : G} (hJq : CFSG.Assembly.IsQuasisimple J) (hpJ : p ∣ Nat.card J)
    (hN : Nat.Coprime p (Nat.card N)) (hJN : J ≤ Subgroup.normalizer (N : Set G))
    (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (h : (⁅J, Subgroup.zpowers b⁆ : Subgroup G) ≤ N) :
    b ∈ Subgroup.centralizer (J : Set G) := by
  have hJq' : CFSG.Open.IsQuasisimple J := hJq
  have h1 : (⁅J, Subgroup.zpowers b⁆ : Subgroup G) ≤ J ⊓ N := by
    refine le_inf ?_ h
    rw [Subgroup.commutator_le]
    intro j hj z hz
    have hzN : z ∈ Subgroup.normalizer (J : Set G) := (Subgroup.zpowers_le.mpr hbJ) hz
    have hjz : j * z * j⁻¹ * z⁻¹ = j * (z * j⁻¹ * z⁻¹) := by group
    rw [commutatorElement_def, hjz]
    exact J.mul_mem hj ((Subgroup.mem_normalizer_iff.mp hzN j⁻¹).mp (J.inv_mem hj))
  have hJO : ¬ J ≤ N := fun hle =>
    (Nat.Prime.coprime_iff_not_dvd hp).mp hN (hpJ.trans (Subgroup.card_dvd_of_le hle))
  have hcen : (J ⊓ N).subgroupOf J ≤ Subgroup.center J := by
    have hn : ((J ⊓ N).subgroupOf J).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro c j hc hj
      exact ⟨J.mul_mem (J.mul_mem hj hc.1) (J.inv_mem hj),
        (Subgroup.mem_normalizer_iff.mp (hJN hj) c).mp hc.2⟩
    have hne : (J ⊓ N).subgroupOf J ≠ ⊤ := fun htop =>
      hJO ((Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right)
    exact Quasisimple.normal_le_center_of_ne_top hJq' _ hne
  have h2 : (⁅⁅J, Subgroup.zpowers b⁆, J⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hc' := h1 hc
    have hz := Subgroup.mem_center_iff.mp
      (hcen (show (⟨c, hc'.1⟩ : J) ∈ (J ⊓ N).subgroupOf J from hc')) ⟨j, hj⟩
    exact congrArg Subtype.val hz
  have : Group.IsPerfect J := ⟨hJq'.1⟩
  have h3 := CFSG.LocalCores.perfect_double_commutator this h2
  rw [Subgroup.commutator_comm] at h3
  exact Subgroup.zpowers_le.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)

theorem ggNbr_of_pComponent {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) (hpJ : p ∣ Nat.card J)
    {d : G} (hD : D = Subgroup.closure {x, d}) {A : Subgroup G}
    (hA : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) A) (hJA : J ≤ A)
    (hAJ : A ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({d} : Set G))),
      J.map (MulAut.conj a⁻¹).toMonoidHom)
    (hxA : ¬ (⁅A, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p A) :
    GGNbr p B x D J d A := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hdD : d ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hdB : d ∈ B := hDJ.1.1 hdD
  have hxd : x * d = d * x :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨d, hdB⟩)
  have hd1 : d ≠ 1 := by
    rintro rfl
    have hD' : D = Subgroup.zpowers x := by
      rw [hD, closure_pair_eq_sup, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    have hcard := hDJ.1.2.2.1
    rw [hD', Nat.card_zpowers] at hcard
    have hle := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
    rw [hcard] at hle
    nlinarith [hp.two_le]
  have hdA : d ∈ Subgroup.centralizer (A : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun a ha => (Subgroup.mem_centralizer_singleton_iff.mp (hA.1 ha))
  have hzdA : Subgroup.zpowers d ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hdA
  refine ⟨⟨hS.1, hdB, hd1, hA.1, hA, fun b => ⟨?_, ?_⟩⟩, hD, hAJ, hxA⟩
  · rintro ⟨hbB, hbA, hbO⟩
    set O := LargeEvenPPrimeCoreOf p A with hOdef
    have hJN : B ≤ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_stdSub hS hI.2.2.2.2.2.2.2 hDJ.1
    have hOcop : Nat.Coprime p (Nat.card O) := by
      rw [hOdef, LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective A.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hbJ : b ∈ Subgroup.centralizer (J : Set G) :=
      mem_centralizer_of_commutator_le_coprime hp hDJ.1.2.2.2.2.2.1.2.2 hpJ hOcop
        (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hJA hj)))
        (hJN hbB) ((Subgroup.commutator_mono hJA le_rfl).trans hbO)
    have hbD : b ∈ D := by
      rw [hDJ.1.2.2.2.2.2.2]
      exact ⟨hbB, hbJ⟩
    have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.zpowers_le]
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ((Commute.zpow_left hxd k).symm).eq.symm
    have hb' : b ∈ ((Subgroup.zpowers x : Set G) * (Subgroup.zpowers d : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hdN, ← closure_pair_eq_sup, ← hD]
      exact hbD
    obtain ⟨u, hu, e, he, rfl⟩ := hb'
    have heA : e ∈ Subgroup.centralizer (A : Set G) := hzdA he
    have huO : (⁅A, Subgroup.zpowers u⁆ : Subgroup G) ≤ O := by
      rw [Subgroup.commutator_le]
      intro a ha w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hue : Commute u e := by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
        exact (Commute.zpow_left hxd i).zpow_right j
      have hea : Commute a e := Subgroup.mem_centralizer_iff.mp heA a ha
      have hk : u ^ k = (u * e) ^ k * (e ^ k)⁻¹ := by
        rw [hue.mul_zpow, mul_inv_cancel_right]
      have hcomm : ⁅a, u ^ k⁆ = ⁅a, (u * e) ^ k⁆ := by
        rw [hk, commutatorElement_def, commutatorElement_def]
        have hea' : Commute a (e ^ k)⁻¹ := (hea.zpow_right k).inv_right
        calc a * ((u * e) ^ k * (e ^ k)⁻¹) * a⁻¹ * ((u * e) ^ k * (e ^ k)⁻¹)⁻¹
            = a * (u * e) ^ k * ((e ^ k)⁻¹ * a⁻¹) * (e ^ k) * ((u * e) ^ k)⁻¹ := by group
          _ = a * (u * e) ^ k * (a⁻¹ * (e ^ k)⁻¹) * (e ^ k) * ((u * e) ^ k)⁻¹ := by
              rw [(hea'.inv_left).eq.symm]
          _ = a * (u * e) ^ k * a⁻¹ * ((u * e) ^ k)⁻¹ := by group
      rw [hcomm]
      exact hbO (Subgroup.commutator_mem_commutator ha (Subgroup.zpow_mem_zpowers _ k))
    have hu1 : u = 1 := by
      by_contra hu1
      exact hxA ((Subgroup.commutator_mono le_rfl
        (Subgroup.zpowers_le.mpr (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp hu hu1))).trans
        huO)
    simp only [hu1, one_mul]
    exact he
  · intro hb
    have hbA : b ∈ Subgroup.centralizer (A : Set G) := hzdA hb
    refine ⟨Subgroup.zpowers_le.mpr hdB hb, Subgroup.centralizer_le_normalizer _ hbA, ?_⟩
    have hbot : (⁅A, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.zpowers_le.mpr hbA
    rw [hbot]
    exact bot_le

end Pumpup

end CFSG.StandardType

end
