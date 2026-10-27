module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCor81
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

private def ggQ2x_cent {G : Type} [Group G] (p : ℕ) (X : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧
    ∀ x ∈ X, ⁅x, g⁆ ∈ LargeEvenPPrimeCoreOf p X}
  one_mem' := ⟨Subgroup.one_mem _, by intro x hx; simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hgO⟩ ⟨hhN, hhO⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun x hx => ?_⟩
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅x, g⁆ ∈ LargeEvenPPrimeCoreOf p X := hgO x hx
    have h2 : g * ⁅x, h⁆ * g⁻¹ ∈ LargeEvenPPrimeCoreOf p X :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_largeEvenPPrimeCoreOf hgN) _).mp
        (hhO x hx)
    have hgoal : (⁅x, g⁆ * g * ⁅x, h⁆ * g⁻¹) = ⁅x, g⁆ * (g * ⁅x, h⁆ * g⁻¹) := by
      group
    rw [hgoal]
    exact Subgroup.mul_mem _ h1 h2
  inv_mem' := by
    rintro g ⟨hgN, hgO⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun x hx => ?_⟩
    rw [commutatorElement_inv_right, ← commutatorElement_inv x g]
    have h1 : ⁅x, g⁆ ∈ LargeEvenPPrimeCoreOf p X := hgO x hx
    simpa using (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.inv_mem _ hgN)) _).mp
        (Subgroup.inv_mem _ h1)

private theorem ggQ2x_cent_commutator {G : Type} [Group G] {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ ggQ2x_cent (G := G) p X) :
    ⁅X, Subgroup.zpowers g⁆ ≤ LargeEvenPPrimeCoreOf p X := by
  rw [Subgroup.commutator_le]
  intro x hx h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Subgroup.zpow_mem _ hg k).2 x hx

private theorem ggQ2x_cent_mem_commutator {G : Type} [Group G] {p : ℕ} {X : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (X : Set G))
    (hg : ⁅X, Subgroup.zpowers g⁆ ≤ LargeEvenPPrimeCoreOf p X) :
    g ∈ ggQ2x_cent (G := G) p X := by
  refine ⟨hgN, fun x hx => ?_⟩
  exact (Subgroup.commutator_le.mp hg) x hx g (Subgroup.mem_zpowers g)

private def ggQ2x_centOf {G : Type} [Group G] (O X : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (O : Set G) ∧ ∀ x ∈ X, ⁅x, g⁆ ∈ O}
  one_mem' := ⟨Subgroup.one_mem _, by intro x hx; simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hgO⟩ ⟨hhN, hhO⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun x hx => ?_⟩
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅x, g⁆ ∈ O := hgO x hx
    have h2 : g * ⁅x, h⁆ * g⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp (hhO x hx)
    have hgoal : (⁅x, g⁆ * g * ⁅x, h⁆ * g⁻¹) = ⁅x, g⁆ * (g * ⁅x, h⁆ * g⁻¹) := by
      group
    rw [hgoal]
    exact Subgroup.mul_mem _ h1 h2
  inv_mem' := by
    rintro g ⟨hgN, hgO⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun x hx => ?_⟩
    rw [commutatorElement_inv_right, ← commutatorElement_inv x g]
    have h1 : ⁅x, g⁆ ∈ O := hgO x hx
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp
      (Subgroup.inv_mem _ h1)

private theorem ggQ2x_centOf_commutator {G : Type} [Group G] {O X : Subgroup G} {g : G}
    (hg : g ∈ ggQ2x_centOf (G := G) O X) :
    ⁅X, Subgroup.zpowers g⁆ ≤ O := by
  rw [Subgroup.commutator_le]
  intro x hx h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Subgroup.zpow_mem _ hg k).2 x hx

private theorem ggQ2x_pcore_eq {G : Type} [Group G] (p : ℕ) (H : Subgroup G) :
    LargeEvenPPrimeCoreOf p H = CFSG.Open.lBalancePrimeCore p H := by
  rw [ComponentClassification.LBalance.primeCore_eq_map]
  rfl

private noncomputable def ggQ2x_restrict {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (t : MulAut ↥Bs) (hDt : Subgroup.map t.toMonoidHom D' = D') :
    MulAut ↥D' :=
  (Subgroup.equivMapOfInjective D' t.toMonoidHom t.injective).trans
    (MulEquiv.subgroupCongr hDt)

private theorem ggQ2x_restrict_apply {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (t : MulAut ↥Bs) (hDt : Subgroup.map t.toMonoidHom D' = D')
    (x : ↥D') : ((ggQ2x_restrict D' t hDt x : ↥D') : ↥Bs) = t x := rfl

private theorem ggQ2x_restrict_mul {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (s t : MulAut ↥Bs)
    (hs : Subgroup.map s.toMonoidHom D' = D') (ht : Subgroup.map t.toMonoidHom D' = D')
    (hst : Subgroup.map (s * t).toMonoidHom D' = D') :
    ggQ2x_restrict D' (s * t) hst = ggQ2x_restrict D' s hs * ggQ2x_restrict D' t ht := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change (ggQ2x_restrict D' (s * t) hst x : ↥Bs) =
    ((ggQ2x_restrict D' s hs) ((ggQ2x_restrict D' t ht) x) : ↥Bs)
  rw [ggQ2x_restrict_apply, ggQ2x_restrict_apply, ggQ2x_restrict_apply, MulAut.mul_apply]

private theorem ggQ2x_restrict_one {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (hD1 : Subgroup.map (1 : MulAut ↥Bs).toMonoidHom D' = D')
    (x : ↥D') : ggQ2x_restrict D' 1 hD1 x = x := by
  apply Subtype.ext
  rw [ggQ2x_restrict_apply]
  rfl

private theorem ggQ2x_restrict_fixes {G : Type} [Group G] {Bs : Subgroup G}
    (D' : Subgroup ↥Bs) (t : MulAut ↥Bs) (hDt : Subgroup.map t.toMonoidHom D' = D')
    (x : ↥D') (hx : t (x : ↥Bs) = (x : ↥Bs)) : ggQ2x_restrict D' t hDt x = x := by
  apply Subtype.ext
  rw [ggQ2x_restrict_apply]
  exact hx

private theorem ggQ2x_conj_commutator_gen {G : Type} [Group G] [Finite G] {p : ℕ}
    {X : Subgroup G} {g d : G}
    (h : ⁅X, Subgroup.zpowers d⁆ ≤ LargeEvenPPrimeCoreOf p X) :
    ⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers (g * d * g⁻¹)⁆ ≤
      LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) := by
  have hmap : (⁅X, Subgroup.zpowers d⁆).map (MulAut.conj g).toMonoidHom =
      ⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers (g * d * g⁻¹)⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    simp
  rw [← hmap]
  calc (⁅X, Subgroup.zpowers d⁆).map (MulAut.conj g).toMonoidHom
      ≤ (LargeEvenPPrimeCoreOf p X).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono h
    _ = LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) :=
        (largeEvenPPrimeCoreOf_map_conj p X g).symm

private noncomputable def ggQ2x_X {G : Type} [Group G] (p : ℕ) (u : G) (J : Subgroup G) :
    Subgroup G :=
  ggLayerClosure p (Subgroup.centralizer ({u} : Set G)) J

theorem ggQ2_trivialLine_cent {G : Type} [Group G] [Finite G] {p : ℕ} {x u : G}
    {D X : Subgroup G} (hD : D = Subgroup.closure {x, u})
    (hXcomp : LargeEvenPComponent p (Subgroup.centralizer ({u} : Set G)) X)
    (hxNX : x ∈ Subgroup.normalizer (X : Set G))
    (hxc : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X) :
    ∀ d ∈ D, (⁅X, Subgroup.zpowers d⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X := by
  have hXleU : X ≤ Subgroup.centralizer ({u} : Set G) := hXcomp.1
  have hcent : D ≤ ggQ2x_cent (G := G) p X := by
    rw [hD, Subgroup.closure_le]
    rintro z (rfl | hzu)
    · exact ggQ2x_cent_mem_commutator hxNX hxc
    · rw [hzu]
      refine ggQ2x_cent_mem_commutator ?_ ?_
      · exact Subgroup.centralizer_le_normalizer _ (fun x' hx' =>
          Subgroup.mem_centralizer_singleton_iff.mp (hXleU hx'))
      · rw [Subgroup.commutator_le]
        intro x' hx' h hh
        have hxuc : x' * u = u * x' :=
          Subgroup.mem_centralizer_singleton_iff.mp (hXleU hx')
        have h1 : ⁅x', h⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          exact (Commute.zpow_right hxuc k).eq
        rw [h1]
        exact Subgroup.one_mem _
  intro d hd
  exact ggQ2x_cent_commutator (hcent hd)

theorem ggQ2_trivialLine_memD {G : Type} [Group G] [Finite G] {p : ℕ} {Bs J D X : Subgroup G}
    (hprime : p.Prime) (hJq : CFSG.Assembly.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hI1 : GGQTwoI1 Bs D J) (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G)) (hJX : J ≤ X) :
    ∀ b ∈ Bs, (⁅X, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X → b ∈ D := by
  have : Fact p.Prime := ⟨hprime⟩
  intro b hb hbO
  have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p X)) := by
    rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hbJ : b ∈ Subgroup.centralizer (J : Set G) :=
    mem_centralizer_of_commutator_le_coprime hprime hJq hpJ hOcop
      (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hJX hj)))
      (hBsJ hb) ((Subgroup.commutator_mono hJX le_rfl).trans hbO)
  exact hI1 b hb (fun j hj => (Subgroup.mem_centralizer_iff.mp hbJ j hj).symm)

theorem ggTrivialLine_setup {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {Rest : Prop}
    (hR : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hpJ : p ∣ Nat.card J) (hI1 : GGQTwoI1 Bs D J) {u : ↥Bs} (hu : (u : G) ∈ D) (hu1 : u ≠ 1)
    (htr : GGTrivialLine p B x D J u) :
    LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G))
        (ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J) ∧
      J ≤ ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J ∧
      Bs ≤ Subgroup.normalizer
        (ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J : Set G) ∧
      (∀ d ∈ D, (⁅ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J,
          Subgroup.zpowers d⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p
          (ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J)) ∧
      (∀ b ∈ Bs, (⁅ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J,
          Subgroup.zpowers b⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p
          (ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J) → b ∈ D) := by
  have hI : GGThmIHyp p B x L := hR.1.1
  have hBstar : GGBstar p B Bs := hR.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hR.1.2.2
  have hprime : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hprime⟩
  have hPU : GGPumpupInput := ggPumpupInput_of_lBalance hLB
  have hSstar : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hBle : B ≤ Bs := hBstar.1
  have huBs : (u : G) ∈ Bs := hBle (hDJ.1.1 hu)
  have hBsC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hBsC hBle hDJ.1 hBsL
  have hux : (u : G) ∉ Subgroup.zpowers x := by
    intro huz
    apply htr.1
    have hxu : x ∈ Subgroup.zpowers (u : G) :=
      mem_zpowers_of_mem_zpowers_of_ne_one hprime (hSstar.1.1.2 x hSstar.2.1) huz
        (by simpa using hu1)
    exact le_antisymm (Subgroup.zpowers_le.mpr huz) (Subgroup.zpowers_le.mpr hxu)
  have hD : D = Subgroup.closure {x, (u : G)} := eq_closure_pair_of_mem hI hDJ hu hux
  have hpump := pumpup_of_stdSub (hPU := hPU) hI hDJ hpJ hD
  have hXcomp : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G))
      (ggQ2x_X p (u : G) J) := hpump.1
  have hJX : J ≤ ggQ2x_X p (u : G) J := hpump.2.1
  have hxNX : x ∈ Subgroup.normalizer (ggQ2x_X p (u : G) J : Set G) := hpump.2.2.1
  have hxc : (⁅ggQ2x_X p (u : G) J, Subgroup.zpowers x⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (ggQ2x_X p (u : G) J) := by
    rcases hpump.2.2.2 with h | h
    · exact absurd ⟨(u : G), ggQ2x_X p (u : G) J, h, rfl⟩ htr.2
    · exact h
  have hBsN : Bs ≤ Subgroup.normalizer (ggQ2x_X p (u : G) J : Set G) := by
    refine GGDichotomy.le_normalizer_of_pComponent (d := (u : G)) ?_ hXcomp hJX hJJ hpJ hBsJ
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hBsC b hb (u : G) huBs
  have hmemD := ggQ2_trivialLine_memD hprime hDJ.1.2.2.2.2.2.1.2.2 hpJ hI1 hBsJ hJX
  have hcentD := ggQ2_trivialLine_cent hD hXcomp hxNX hxc
  exact ⟨hXcomp, hJX, hBsN, hcentD, hmemD⟩

private theorem ggQ2x_case_normalizer {G : Type} [Group G] [Finite G]
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hK1 : GGQTwoK1 p B Bs x D J)
    (h4 : 4 ∣ Nat.card (ggAutomizer J Bs)) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    rw [hbot] at h4
    simp at h4
  exact ggQ2_normalizer_inf_le hLB hP hS.1 hAJ hK1 ⟨hgN, hgD⟩

private theorem ggQ2x_count {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (Dsub : Subgroup ↥Bs) (uD : ↥Dsub)
    (hDcard : Nat.card Dsub = 9) (hu1 : uD ≠ 1)
    (hcomm : ∀ a b : ↥Dsub, a * b = b * a)
    (hexp : ∀ d : ↥Dsub, d ^ 3 = 1)
    (hcommBs : ∀ a b : ↥Bs, a * b = b * a)
    (A : Subgroup (MulAut ↥Bs))
    (hDshift : ∀ t ∈ A, ∀ b : ↥Bs, b⁻¹ * t b ∈ Dsub)
    (huinv : ∀ t ∈ A, t (uD : ↥Bs) = (uD : ↥Bs))
    (hA4 : 4 ∣ Nat.card A) : False := by
  let : CommGroup ↥Dsub := { mul_comm := hcomm }
  let : CommGroup ↥Bs := { mul_comm := hcommBs }
  set U : Subgroup ↥Dsub := Subgroup.zpowers uD with hUdef
  have hUcard : Nat.card U = 3 := by
    rw [hUdef, Nat.card_zpowers]
    exact orderOf_eq_prime (hexp uD) hu1
  have : U.Normal := Subgroup.normal_of_comm U
  have hQcard : Nat.card (↥Dsub ⧸ U) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup U
    rw [hDcard, hUcard] at h
    omega
  have : IsCyclic (↥Dsub ⧸ U) := isCyclic_of_prime_card (p := 3) hQcard
  have hMA : Nat.card (MulAut (↥Dsub ⧸ U)) = 2 := by
    rw [IsCyclic.card_mulAut, hQcard, Nat.totient_prime (by norm_num)]
  have hDinv : ∀ t ∈ A, Subgroup.map t.toMonoidHom Dsub = Dsub := by
    intro t ht
    have hle : Subgroup.map t.toMonoidHom Dsub ≤ Dsub := by
      rintro _ ⟨d, hd, rfl⟩
      have h := hDshift t ht d
      change t d ∈ Dsub
      rw [show t d = d * (d⁻¹ * t d) by group]
      exact Dsub.mul_mem hd h
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective t.injective])
  have hUmap : ∀ t : A,
      Subgroup.map (↑(ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) :
        ↥Dsub →* ↥Dsub) U = U := by
    intro t
    rw [hUdef, MonoidHom.map_zpowers]
    congr 1
    exact ggQ2x_restrict_fixes Dsub (t : MulAut ↥Bs) (hDinv t t.2) uD (huinv t t.2)
  let ρ : A →* MulAut (↥Dsub ⧸ U) :=
  { toFun := fun t =>
      QuotientGroup.congr U U (ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) (hUmap t)
    map_one' := by
      refine MulEquiv.ext fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.congr_mk]
        change (QuotientGroup.mk ((ggQ2x_restrict Dsub (1 : MulAut ↥Bs)
            (hDinv 1 A.one_mem)) x) : ↥Dsub ⧸ U) = QuotientGroup.mk x
        rw [ggQ2x_restrict_one]
    map_mul' := by
      intro s t
      refine MulEquiv.ext fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk,
          QuotientGroup.congr_mk]
        change (QuotientGroup.mk ((ggQ2x_restrict Dsub (s * t : MulAut ↥Bs)
            (hDinv (s * t) (A.mul_mem s.2 t.2))) x) : ↥Dsub ⧸ U) =
          QuotientGroup.mk ((ggQ2x_restrict Dsub (s : MulAut ↥Bs) (hDinv s s.2))
            ((ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) x))
        rw [ggQ2x_restrict_mul, MulAut.mul_apply] }
  let W : Subgroup ↥Bs := Subgroup.map Dsub.subtype U
  have hWzp : W = Subgroup.zpowers (uD : ↥Bs) := by
    dsimp only [W]
    rw [hUdef, MonoidHom.map_zpowers]
    rfl
  have hWcard : Nat.card W = 3 := by
    rw [Subgroup.card_map_of_injective Dsub.subtype_injective, hUcard]
  have hWexp : ∀ w ∈ W, w ^ 3 = 1 := by
    intro w hw
    have h : orderOf w ∣ Nat.card W := by
      rw [← Subgroup.orderOf_mk w hw]
      exact orderOf_dvd_natCard _
    rw [hWcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hker3 : ∀ t : A, ρ t = 1 → (t : MulAut ↥Bs) ^ 3 = 1 := by
    intro t ht
    have hmemW : ∀ d : ↥Dsub, (d : ↥Bs)⁻¹ * ((t : MulAut ↥Bs) (d : ↥Bs)) ∈ W := by
      intro d
      have h1 : (QuotientGroup.mk ((ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) d) :
          ↥Dsub ⧸ U) = (QuotientGroup.mk d : ↥Dsub ⧸ U) := by
        have h2 := congrArg (fun f : MulAut (↥Dsub ⧸ U) => f (QuotientGroup.mk d)) ht
        rw [show ρ t = QuotientGroup.congr U U
            (ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) (hUmap t) from rfl,
          QuotientGroup.congr_mk] at h2
        simpa using h2
      have h3 : ((ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) d)⁻¹ * d ∈ U :=
        QuotientGroup.eq.mp h1
      have h3' : d⁻¹ * ((ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) d) ∈ U := by
        have := U.inv_mem h3
        simpa only [mul_inv_rev, inv_inv] using this
      have h4 : (d : ↥Bs)⁻¹ * ((t : MulAut ↥Bs) (d : ↥Bs)) ∈ W := by
        have hm : Dsub.subtype (d⁻¹ *
            ((ggQ2x_restrict Dsub (t : MulAut ↥Bs) (hDinv t t.2)) d)) ∈ W :=
          Subgroup.mem_map_of_mem Dsub.subtype h3'
        simpa only [map_mul, map_inv, Subgroup.coe_subtype, ggQ2x_restrict_apply] using hm
      exact h4
    refine MulEquiv.ext fun b => ?_
    set T : MulAut ↥Bs := (t : MulAut ↥Bs) with hT
    obtain ⟨db, hdbeq⟩ : ∃ db : ↥Dsub, (db : ↥Bs) = b⁻¹ * T b :=
      ⟨⟨b⁻¹ * T b, hDshift (t : MulAut ↥Bs) t.2 b⟩, rfl⟩
    have htb : T b = b * (db : ↥Bs) := by rw [hdbeq]; group
    set udb : ↥Bs := (db : ↥Bs)⁻¹ * T (db : ↥Bs) with hudbdef
    have hudbW : udb ∈ W := by rw [hudbdef]; exact hmemW db
    have htdb : T (db : ↥Bs) = (db : ↥Bs) * udb := by rw [hudbdef]; group
    have htudb : T udb = udb := by
      have hmem : udb ∈ Subgroup.zpowers (uD : ↥Bs) := by rw [← hWzp]; exact hudbW
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk, map_zpow, huinv (t : MulAut ↥Bs) t.2]
    have hdb3 : (db : ↥Bs) ^ 3 = 1 := by
      have := congrArg Subtype.val (hexp db)
      simpa using this
    have hudb3 : udb ^ 3 = 1 := hWexp udb hudbW
    have ht2 : T (T b) = b * (db : ↥Bs) ^ 2 * udb := by
      rw [htb, map_mul, htb, htdb, pow_two]
      simp only [mul_assoc]
    have ht3 : T (T (T b)) = b := by
      rw [ht2]
      simp only [map_mul, map_pow]
      rw [htdb, htudb, htb]
      have hkey : (b * (db : ↥Bs)) * ((db : ↥Bs) * udb) ^ 2 * udb =
          b * ((db : ↥Bs) ^ 3 * udb ^ 3) := by
        rw [pow_two,
          show (db : ↥Bs) ^ 3 = (db : ↥Bs) * (db : ↥Bs) * (db : ↥Bs) by rw [pow_succ, pow_two],
          show udb ^ 3 = udb * udb * udb by rw [pow_succ, pow_two]]
        ac_rfl
      rw [hkey, hdb3, hudb3, one_mul, mul_one]
    have hT3 : (T : MulAut ↥Bs) ^ 3 = T * T * T := by rw [pow_succ, pow_succ, pow_one]
    rw [hT3, MulAut.mul_apply, MulAut.mul_apply]
    exact ht3
  have hK3 : IsPGroup 3 (MonoidHom.ker ρ) := by
    intro t
    refine ⟨1, ?_⟩
    have ht : ρ (t : A) = 1 := t.2
    have h3 : ((t : A) : MulAut ↥Bs) ^ 3 = 1 := hker3 (t : A) ht
    exact Subtype.ext (Subtype.ext (by simpa using h3))
  have hKcop : Nat.Coprime 2 (Nat.card (MonoidHom.ker ρ)) := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hK3
    rw [hn]
    exact (show Nat.Coprime 2 3 by norm_num).pow_right n
  have hJdvd : Nat.card (MonoidHom.range ρ) ∣ 2 :=
    (by simpa only [hMA, Subgroup.card_top] using
      Subgroup.card_dvd_of_le (le_top : MonoidHom.range ρ ≤ ⊤))
  have hcard : Nat.card A = Nat.card (MonoidHom.ker ρ) * Nat.card (MonoidHom.range ρ) :=
    (Subgroup.card_ker_mul_card_range ρ).symm
  have h4' : 4 ∣ Nat.card (MonoidHom.ker ρ) * Nat.card (MonoidHom.range ρ) := by
    rw [← hcard]; exact hA4
  have h4r : 4 ∣ Nat.card (MonoidHom.range ρ) :=
    (hKcop.pow_left 2).dvd_of_dvd_mul_right (by rw [Nat.mul_comm]; exact h4')
  have hle2 : Nat.card (MonoidHom.range ρ) ≤ 2 := Nat.le_of_dvd (by norm_num) hJdvd
  have h4le : 4 ≤ Nat.card (MonoidHom.range ρ) := Nat.le_of_dvd Nat.card_pos h4r
  omega

theorem ggQ2_trivialLine_conj_automizer_le {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {J : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) {X : Subgroup G} (hJX : J ≤ X) :
    (ggAutomizer J Bs).map (MulAut.conj (ggConjAut Bs hgN)).toMonoidHom ≤
      ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs := by
  rintro _ ⟨φ, hφ, rfl⟩
  change φ ∈ ggAutomizer J Bs at hφ
  rw [mem_ggAutomizer_iff] at hφ
  rw [mem_ggAutomizer_iff]
  obtain ⟨n, hnJ, hnN, hnφ⟩ := hφ
  refine ⟨g * n * g⁻¹, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hJX hnJ)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hnN) (Subgroup.inv_mem _ hgN)
  · intro b
    change ↑((ggConjAut Bs hgN * φ * (ggConjAut Bs hgN)⁻¹) b) =
      g * n * g⁻¹ * ↑b * (g * n * g⁻¹)⁻¹
    rw [MulAut.mul_apply, MulAut.mul_apply, ggConjAut_apply, hnφ,
      inv_apply_of_forall (ggConjAut_apply Bs hgN)]
    group

theorem ggQ2_trivialLine_conj_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {u g : G}
    (hprime : p.Prime) (hup : u ^ p = 1) (hu1 : u ≠ 1)
    (hgu : g * u * g⁻¹ ∈ Subgroup.zpowers u) :
    Subgroup.zpowers (g * u * g⁻¹) = Subgroup.zpowers u ∧
      (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer ({u} : Set G) := by
  have hguz : Subgroup.zpowers (g * u * g⁻¹) = Subgroup.zpowers u := by
    refine le_antisymm (Subgroup.zpowers_le.mpr hgu) (Subgroup.zpowers_le.mpr ?_)
    exact mem_zpowers_of_mem_zpowers_of_ne_one hprime hup hgu (by simpa using hu1)
  refine ⟨hguz, ?_⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
  exact centralizer_singleton_eq_of_zpowers_eq hguz

theorem ggQ2_trivialLine_conj_normalizer {G : Type} [Group G] {Bs X : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    Bs ≤ Subgroup.normalizer (X.map (MulAut.conj g).toMonoidHom : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨(g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹, ?_, ?_⟩
    · change (g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹ ∈ X
      simpa only [inv_inv, mul_assoc] using (Subgroup.mem_normalizer_iff.mp
        (hBsN ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) b).mp hb)) x).mp hx
    · change (MulAut.conj g) ((g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹) = b * y * b⁻¹
      rw [show (MulAut.conj g) ((g⁻¹ * b * g) * x * (g⁻¹ * b * g)⁻¹) =
            b * ((MulAut.conj g) x) * b⁻¹ by
          simp only [MulAut.conj_apply]; group,
        show (MulAut.conj g) x = y from hxy]
  · rintro ⟨x, hx, hxy⟩
    refine ⟨(g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g), ?_, ?_⟩
    · change (g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g) ∈ X
      have hmem := (Subgroup.mem_normalizer_iff.mp
        (hBsN ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) b⁻¹).mp
          (Bs.inv_mem hb))) x).mp hx
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hmem
    · change (MulAut.conj g) ((g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g)) = y
      rw [show (MulAut.conj g) ((g⁻¹ * b * g)⁻¹ * x * (g⁻¹ * b * g)) =
            b⁻¹ * ((MulAut.conj g) x) * b by
          simp only [MulAut.conj_apply]; group,
        show (MulAut.conj g) x = b * y * b⁻¹ from hxy]
      group

theorem ggQ2_trivialLine_conj_pComp {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hpJ : p ∣ Nat.card J) (hI1 : GGQTwoI1 Bs D J) {u : ↥Bs} (hu : (u : G) ∈ D) (hu1 : u ≠ 1)
    (htr : GGTrivialLine p B x D J u) {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgu : g * (u : G) * g⁻¹ ∈ Subgroup.zpowers (u : G))
    (hDg : D.map (MulAut.conj g).toMonoidHom ≠ D) :
    let X := ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J
    let X' := X.map (MulAut.conj g).toMonoidHom
    LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X' ∧ X' ≠ X ∧
      (⁅X, X'⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G)) ∧
      Bs ≤ Subgroup.normalizer (X' : Set G) := by
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hprime : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hprime⟩
  have hBle : B ≤ Bs := hBstar.1
  have hup : (u : G) ^ p = 1 := hBstar.2.1.2 _ (hBle (hDJ.1.1 hu))
  have hBle' : D ≤ Bs := hDJ.1.1.trans hBle
  let X : Subgroup G := ggQ2x_X p (u : G) J
  obtain ⟨hXcomp, -, hBsN, hcommD, hmemD⟩ :=
    ggTrivialLine_setup hLB hS.1 hpJ hI1 hu hu1 htr
  obtain ⟨hguz, hHg⟩ := ggQ2_trivialLine_conj_centralizer hprime hup (by simpa using hu1) hgu
  let X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom
  have hX'comp' := largeEvenPComponent_map_conj' hXcomp g
  rw [hHg] at hX'comp'
  have hX'comp : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X' := hX'comp'
  have hXne : X' ≠ X := by
    intro hXeq
    apply hDg
    have hgX : g ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_iff_map_conj.mpr hXeq
    have hDle : D.map (MulAut.conj g).toMonoidHom ≤ D := by
      rintro _ ⟨d, hd, rfl⟩
      have hcommd := hcommD d hd
      have hconj := ggQ2x_conj_commutator_gen (g := g) (d := d) hcommd
      have hXmap : Subgroup.map (MulAut.conj g).toMonoidHom
          (ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J) = X := hXeq
      rw [hXmap] at hconj
      exact hmemD (g * d * g⁻¹) ((Subgroup.mem_normalizer_iff.mp hgN d).mp (hBle' hd)) hconj
    exact Subgroup.eq_of_le_of_card_ge hDle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hXX' : (⁅X, X'⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G)) := by
    rw [ggQ2x_pcore_eq]
    exact GGDichotomy.commutator_le_primeCore_of_ne
      ((largeEvenPComponent_iff_lBalance p _ X).1 hXcomp).2
      ((largeEvenPComponent_iff_lBalance p _ X').1 hX'comp).2 hXne.symm
  have hBsN' : Bs ≤ Subgroup.normalizer (X' : Set G) :=
    ggQ2_trivialLine_conj_normalizer hgN hBsN
  exact ⟨hX'comp, hXne, hXX', hBsN'⟩

theorem ggQ2_trivialLine_conj_cent {G : Type} [Group G] [Finite G] {p : ℕ} {u : G}
    {J X X' : Subgroup G}
    (hX' : LargeEvenPComponent p (Subgroup.centralizer ({u} : Set G)) X')
    (hJX : J ≤ X)
    (hXX' : (⁅X, X'⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({u} : Set G)))
    {m n : G} (hmX' : m ∈ X') (hnX' : n ∈ X') :
    (⁅J, Subgroup.zpowers (m * n⁻¹)⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G)) := by
  have hmH : m ∈ Subgroup.centralizer ({(u : G)} : Set G) := hX'.1 hmX'
  have hnH : n ∈ Subgroup.centralizer ({(u : G)} : Set G) := hX'.1 hnX'
  have hJm : (⁅J, Subgroup.zpowers m⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G)) :=
    (Subgroup.commutator_mono hJX (Subgroup.zpowers_le.mpr hmX')).trans hXX'
  have hJn : (⁅J, Subgroup.zpowers n⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G)) :=
    (Subgroup.commutator_mono hJX (Subgroup.zpowers_le.mpr hnX')).trans hXX'
  have hmCent : m ∈ ggQ2x_centOf (G := G)
      (LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G))) J :=
    ⟨mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hmH),
      fun x hx => (Subgroup.commutator_le.mp hJm) x hx m (Subgroup.mem_zpowers m)⟩
  have hnCent : n ∈ ggQ2x_centOf (G := G)
      (LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G))) J :=
    ⟨mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hnH),
      fun x hx => (Subgroup.commutator_le.mp hJn) x hx n (Subgroup.mem_zpowers n)⟩
  have hcCent : m * n⁻¹ ∈ ggQ2x_centOf (G := G)
      (LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G))) J :=
    Subgroup.mul_mem _ hmCent (Subgroup.inv_mem _ hnCent)
  exact ggQ2x_centOf_commutator hcCent

theorem ggQ2_trivialLine_shift {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hpJ : p ∣ Nat.card J) (hI1 : GGQTwoI1 Bs D J) {u : ↥Bs} (hu : (u : G) ∈ D)
    {X X' : Subgroup G} (hX : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X)
    (hX' : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X')
    (hJX : J ≤ X)
    (hXX' : (⁅X, X'⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({(u : G)} : Set G)))
    (hBsN' : Bs ≤ Subgroup.normalizer (X' : Set G)) :
    ∀ t ∈ ggAutomizer X' Bs, ∀ b : ↥Bs, b⁻¹ * t b ∈ D.subgroupOf Bs := by
  have := hu
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hprime : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hprime⟩
  have hBsC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hBsC hBstar.1 hDJ.1
      (GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1)
  intro t ht b
  rw [Subgroup.mem_subgroupOf]
  rw [mem_ggAutomizer_iff] at ht
  obtain ⟨n, hnX', hnN, hnφ⟩ := ht
  set m : G := (b : G)⁻¹ * n * (b : G) with hm
  have hmX' : m ∈ X' := by
    rw [hm]
    simpa using (Subgroup.mem_normalizer_iff.mp (hBsN' (Bs.inv_mem b.2)) n).mp hnX'
  have hJc := ggQ2_trivialLine_conj_cent hX' hJX hXX' hmX' hnX'
  have hcBs : m * n⁻¹ ∈ Bs := by
    rw [hm, show (b : G)⁻¹ * n * (b : G) * n⁻¹ = (b : G)⁻¹ * (n * (b : G) * n⁻¹) by group,
      ← hnφ b]
    exact Bs.mul_mem (Bs.inv_mem b.2) (t b).2
  have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p
      (Subgroup.centralizer ({(u : G)} : Set G)))) := by
    rw [LargeEvenPPrimeCoreOf,
      Subgroup.card_map_of_injective
        (Subgroup.centralizer ({(u : G)} : Set G)).subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hcJ : m * n⁻¹ ∈ Subgroup.centralizer (J : Set G) :=
    mem_centralizer_of_commutator_le_coprime hprime hDJ.1.2.2.2.2.2.1.2.2 hpJ hOcop
      (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf
        (Subgroup.le_normalizer (hX.1 (hJX hj))))
      (hBsJ hcBs) hJc
  have hcD : m * n⁻¹ ∈ D := hI1 (m * n⁻¹) hcBs
    (fun j hj => (Subgroup.mem_centralizer_iff.mp hcJ j hj).symm)
  have hceq : ((b⁻¹ * t b : ↥Bs) : G) = m * n⁻¹ := by
    change (b : G)⁻¹ * (t b : G) = m * n⁻¹
    rw [hnφ b, hm]
    group
  rwa [hceq]

theorem ggQ2_trivialLine_conj_displ_le {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hpJ : p ∣ Nat.card J) (hI1 : GGQTwoI1 Bs D J) {u : ↥Bs} (hu : (u : G) ∈ D) (hu1 : u ≠ 1)
    (htr : GGTrivialLine p B x D J u) {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgu : g * (u : G) * g⁻¹ ∈ Subgroup.zpowers (u : G))
    (hDg : D.map (MulAut.conj g).toMonoidHom ≠ D) :
    (Subgroup.closure {y | ∃ φ ∈ ggAutomizer J Bs, ∃ b : ↥Bs,
      y = ((b⁻¹ * φ b : ↥Bs) : G)}).map (MulAut.conj g).toMonoidHom ≤ D := by
  let X : Subgroup G := ggLayerClosure p (Subgroup.centralizer ({(u : G)} : Set G)) J
  let X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom
  obtain ⟨hX'comp, -, hXX', hBsN'⟩ :=
    ggQ2_trivialLine_conj_pComp hLB hS hpJ hI1 hu hu1 htr hgN hgu hDg
  have hset := ggTrivialLine_setup hLB hS.1 hpJ hI1 hu hu1 htr
  have hXcomp : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X := hset.1
  have hJX : J ≤ X := hset.2.1
  have hmaple := ggQ2_trivialLine_conj_automizer_le hgN hJX
  have hDshift := ggQ2_trivialLine_shift hS hpJ hI1 hu hXcomp hX'comp hJX hXX' hBsN'
  have key : ∀ (t : MulAut ↥Bs) (b : ↥Bs),
      g * ((b⁻¹ * t b : ↥Bs) : G) * g⁻¹ =
        (((ggConjAut Bs hgN b)⁻¹ *
          ((MulAut.conj (ggConjAut Bs hgN)) t) (ggConjAut Bs hgN b) : ↥Bs) : G) := by
    intro t b
    rw [show g * ((b⁻¹ * t b : ↥Bs) : G) * g⁻¹ =
        ((ggConjAut Bs hgN (b⁻¹ * t b) : ↥Bs) : G) from rfl]
    congr 1
    rw [map_mul, map_inv, MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.inv_apply_self]
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro y ⟨w, ⟨φ, hφ, b, rfl⟩, rfl⟩
  have ht : (MulAut.conj (ggConjAut Bs hgN)) φ ∈ ggAutomizer X' Bs := hmaple ⟨φ, hφ, rfl⟩
  have hd := hDshift ((MulAut.conj (ggConjAut Bs hgN)) φ) ht (ggConjAut Bs hgN b)
  rw [Subgroup.mem_subgroupOf] at hd
  change g * ((b⁻¹ * φ b : ↥Bs) : G) * g⁻¹ ∈ D
  rwa [key φ b]

private theorem ggQ2x_case_contra {G : Type} [Group G] [Finite G]
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) (hK1 : GGQTwoK1 p B Bs x D J) (hI1 : GGQTwoI1 Bs D J) {u : ↥Bs}
    (hu : (u : G) ∈ D) (hu1 : u ≠ 1) (htr : GGTrivialLine p B x D J u)
    (h4 : 4 ∣ Nat.card (ggAutomizer J Bs)) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgu : g * (u : G) * g⁻¹ ∈ Subgroup.zpowers (u : G))
    (hDg : D.map (MulAut.conj g).toMonoidHom ≠ D) : False := by
  have := hK1
  have hI : GGThmIHyp p B x L := hS.1.1.1
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hHyp : GGCorFiveTwentyHyp p B Bs x L D J := hS.1
  have hprime : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hprime⟩
  have hBle : B ≤ Bs := hBstar.1
  have huBs : (u : G) ∈ Bs := hBle (hDJ.1.1 hu)
  have hBsC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hup : (u : G) ^ p = 1 := hBstar.2.1.2 (u : G) huBs
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  have hBle' : D ≤ Bs := hDJ.1.1.trans hBle
  let X : Subgroup G := ggQ2x_X p (u : G) J
  let X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom
  obtain ⟨hX'comp, -, hXX', hBsN'⟩ :=
    ggQ2_trivialLine_conj_pComp hLB hS hpJ hI1 hu hu1 htr hgN hgu hDg
  have hset := ggTrivialLine_setup hLB hS.1 hpJ hI1 hu hu1 htr
  have hXcomp : LargeEvenPComponent p (Subgroup.centralizer ({(u : G)} : Set G)) X := hset.1
  have hJX : J ≤ X := hset.2.1
  have hcommD : ∀ d ∈ D, (⁅X, Subgroup.zpowers d⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p X := hset.2.2.2.1
  have hguD : g⁻¹ * (u : G) * g ∈ D := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgu
    have hwk : (g⁻¹ * (u : G) * g) ^ k = (u : G) := by
      rw [show g⁻¹ * (u : G) * g = (MulAut.conj g⁻¹) (u : G) by
        rw [MulAut.conj_apply, inv_inv], ← map_zpow, hk]
      simp only [MulAut.conj_apply]
      group
    have hwp : (g⁻¹ * (u : G) * g) ^ p = 1 := by
      rw [show g⁻¹ * (u : G) * g = (MulAut.conj g⁻¹) (u : G) by
        rw [MulAut.conj_apply, inv_inv], ← map_pow, hup, map_one]
    have hwu : (u : G) ∈ Subgroup.zpowers (g⁻¹ * (u : G) * g) :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, hwk⟩
    exact Subgroup.zpowers_le.mpr hu
      (mem_zpowers_of_mem_zpowers_of_ne_one hprime hwp hwu (by simpa using hu1))
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hBsC hBle hDJ.1
      (GGDichotomy.le_normalizer_of_innerDiagOn hHyp.2.2.1.1)
  let uD : ↥(D.subgroupOf Bs) := ⟨u, hu⟩
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer X' Bs
  have hA4 : 4 ∣ Nat.card A := by
    have hmaple := ggQ2_trivialLine_conj_automizer_le hgN hJX
    have heq : Nat.card (ggAutomizer J Bs) =
        Nat.card ((ggAutomizer J Bs).map
          (MulAut.conj (ggConjAut Bs hgN)).toMonoidHom) :=
      (Subgroup.card_map_of_injective (MulAut.conj (ggConjAut Bs hgN)).injective).symm
    exact dvd_trans (heq ▸ h4) (Subgroup.card_dvd_of_le hmaple)
  have hDshift := ggQ2_trivialLine_shift hS hpJ hI1 hu hXcomp hX'comp hJX hXX' hBsN'
  have huinv : ∀ t ∈ A, t (uD : ↥Bs) = (uD : ↥Bs) := by
    intro t ht
    rw [mem_ggAutomizer_iff] at ht
    obtain ⟨n, hnX', hnN, hnφ⟩ := ht
    have hXu : (⁅X', Subgroup.zpowers (u : G)⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p X' := by
      have h1 := hcommD (g⁻¹ * (u : G) * g) hguD
      have h2 := ggQ2x_conj_commutator_gen (g := g) (d := g⁻¹ * (u : G) * g) h1
      rwa [show g * (g⁻¹ * (u : G) * g) * g⁻¹ = (u : G) by group] at h2
    have hnu : ⁅n, (u : G)⁆ = 1 := by
      have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p X')) := by
        rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective X'.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
      have h1 : ⁅n, (u : G)⁆ ∈ LargeEvenPPrimeCoreOf p X' :=
        (Subgroup.commutator_le.mp hXu) n hnX' (u : G) (Subgroup.mem_zpowers _)
      have h2 : ⁅n, (u : G)⁆ ∈ Bs := by
        rw [commutatorElement_def]
        exact Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp hnN u).mp huBs) (Bs.inv_mem huBs)
      have h3 : (⁅n, (u : G)⁆) ^ p = 1 := hBstar.2.1.2 _ h2
      exact GGDichotomy.eq_one_of_mem_of_coprime hOcop h1 h3
    apply Subtype.ext
    rw [hnφ]
    show n * (u : G) * n⁻¹ = (u : G)
    rw [commutatorElement_eq_one_iff_mul_comm] at hnu
    rw [hnu]; group
  exact ggQ2x_count (D.subgroupOf Bs) uD
    (by
      have h1 : Nat.card (D.subgroupOf Bs) = Nat.card D :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle').toEquiv
      rw [h1, hDJ.1.2.2.1, hp]; norm_num)
    (by
      intro h
      apply hu1
      apply Subtype.ext
      exact congrArg (fun z : ↥(D.subgroupOf Bs) => ((z : ↥Bs) : G)) h)
    (fun a b => Subtype.ext (Subtype.ext
      (hBsC (a : ↥Bs) (a : ↥Bs).2 (b : ↥Bs) (b : ↥Bs).2)))
    (fun d => Subtype.ext (Subtype.ext (by
      have h := hBstar.2.1.2 (d : ↥Bs) (d : ↥Bs).2
      rw [hp] at h
      simpa using h)))
    (fun a b => hBstar.2.1.1.is_comm.comm a b)
    A hDshift huinv hA4

theorem ggQ2_gammaTrivial {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) (hK1 : GGQTwoK1 p B Bs x D J) (hI1 : GGQTwoI1 Bs D J) {u : ↥Bs}
    (hu : (u : G) ∈ D) (hu1 : u ≠ 1) (htr : GGTrivialLine p B x D J u)
    (h4 : 4 ∣ Nat.card (ggAutomizer J Bs)) : GGGammaAt p B Bs x L D J u := by
  intro φ hφ hφu
  rw [mem_ggAutomizer_iff] at hφ
  obtain ⟨g, -, hgN, hgφ⟩ := hφ
  rw [mem_ggAutomizer_iff]
  refine ⟨g, ?_, hgN, hgφ⟩
  by_cases hDg : D.map (MulAut.conj g).toMonoidHom = D
  · exact ggQ2x_case_normalizer hLB hP hS hK1 h4 hgN
      (mem_normalizer_iff_map_conj.mpr hDg)
  · exfalso
    have hgu : g * (u : G) * g⁻¹ ∈ Subgroup.zpowers (u : G) := by
      have hmem : (φ u : G) ∈ Subgroup.zpowers (u : G) := by
        have h := Subgroup.mem_map_of_mem Bs.subtype hφu
        rw [MonoidHom.map_zpowers] at h
        exact h
      rwa [hgφ u] at hmem
    exact ggQ2x_case_contra hLB hP hS hp hK1 hI1 hu hu1 htr h4 hgN hgu hDg

end CFSG.StandardType

end
