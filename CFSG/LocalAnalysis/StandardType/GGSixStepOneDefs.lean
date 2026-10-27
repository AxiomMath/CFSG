module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGSixCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Kd

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def ggKd (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) (d : G) :
    Subgroup G :=
  ⨆ (a : G) (_ : a ∈ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d})),
    J.map (MulAut.conj a).toMonoidHom

omit [Finite G] in
theorem largeEvenLayer_le (H : Subgroup G) : LargeEvenLayer H ≤ H :=
  sSup_le fun _ hK => hK.1

theorem le_ggKd (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) (d : G) :
    J ≤ ggKd p B x L D J d := by
  refine le_trans ?_ (le_iSup₂ (f := fun (a : G)
    (_ : a ∈ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d})) =>
      J.map (MulAut.conj a).toMonoidHom) 1 (Subgroup.one_mem _))
  intro j hj
  exact ⟨j, hj, by simp⟩

theorem ggKd_le {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} {d : G}
    (hJ : J ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) :
    ggKd p B x L D J d ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer {d} := by
  refine iSup₂_le fun a ha => ?_
  rintro _ ⟨j, hj, rfl⟩
  have ha' := largeEvenLayer_le _ ha
  have hj' := hJ hj
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' hj') (Subgroup.inv_mem _ ha')

end Kd

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

namespace GGSixCtxV2

variable (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
include h

theorem thmI : GGThmIHyp p B x L := h.1

theorem prime : p.Prime := h.1.2.2.2.2.2.1.1

theorem ne_two : p ≠ 2 := h.1.2.2.2.2.2.1.2.1

theorem charTwo : IsCharTwoType G := h.1.2.2.2.1

theorem sstar : LargeEvenSStar p B x L := h.1.2.2.2.2.2.2.1

theorem stdType : LargeEvenStandardType p B x L := h.1.2.2.2.2.2.2.2

theorem beta : p ∈ LargeEvenBeta 4 G := h.1.2.2.2.2.2.1

theorem bstar : GGBstar p B Bs := h.2.1

theorem stdSub : LargeEvenStdSub p B x L D J := h.2.2.1

theorem config : GGConfig p B Bs x L D J := ⟨h.1, h.2.1, h.2.2.1⟩

theorem range_eq : ψ.range = ggG0 p B x L D J := h.2.2.2.2.1.1

theorem perfect : commutator ↥(ggG0 p B x L D J) = ⊤ := h.2.2.2.2.2.1.1

theorem lieModel :
    LieModel (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) t n 2 f :=
  h.2.2.2.2.2.1.2

theorem bstar_le_normalizer : Bs ≤ ggM p B x L D J := h.2.2.2.2.2.2.1.1

theorem normalizer_bstar_le : Subgroup.normalizer (Bs : Set G) ≤ ggM p B x L D J :=
  h.2.2.2.2.2.2.2.2

theorem normalizer_b_le : Subgroup.normalizer (B : Set G) ≤ ggM p B x L D J :=
  h.2.2.2.2.2.2.2.1

theorem j_le_inf : J ≤ L ⊓ Subgroup.centralizer (D : Set G) := h.stdSub.1.2.2.2.2.2.1.1

theorem le_ggG0 : J ≤ ggG0 p B x L D J := h.j_le_inf.trans (inf_le_left.trans le_sup_left)

theorem le_centralizer_J : D ≤ Subgroup.centralizer (J : Set G) :=
  Subgroup.le_centralizer_iff.mp (h.j_le_inf.trans inf_le_right)

theorem d_le_bstar : D ≤ Bs := h.stdSub.1.1.trans h.bstar.1

theorem d_le_ggM : D ≤ ggM p B x L D J := h.d_le_bstar.trans h.bstar_le_normalizer

theorem d_elem : IsElemAbelian p D := h.stdSub.1.2.1

theorem card_d : Nat.card D = p ^ 2 := h.stdSub.1.2.2.1

theorem le_ggG0_inf {d : G} (hd : d ∈ D) :
    J ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer {d} := by
  refine _root_.le_inf h.le_ggG0 fun j hj => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (h.le_centralizer_J hd) j hj)

theorem ggKd_le_ggG0 {d : G} (hd : d ∈ D) : ggKd p B x L D J d ≤ ggG0 p B x L D J :=
  (ggKd_le (h.le_ggG0_inf hd)).trans inf_le_left

theorem ggKd_le_centralizer {d : G} (hd : d ∈ D) :
    ggKd p B x L D J d ≤ Subgroup.centralizer {d} :=
  (ggKd_le (h.le_ggG0_inf hd)).trans inf_le_right

end GGSixCtxV2

end Ctx

section LemmaTwoThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}

theorem centralizer_le_ggM_of_nbr (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hDJ : LargeEvenStdSubPre p B x L D J)
    (hnbr : ∀ g ∈ Subgroup.centralizer (D : Set G), ∀ (y : G) (K : Subgroup G),
      GGNbr p B x D J y K → g ∈ Subgroup.normalizer (K : Set G)) :
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J := by
  intro g hg
  have hgx : g ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hDJ.2.2.2.1) hg
  exact mem_normalizer_ggG0 (mem_normalizer_of_sstar hS hnc hgx) fun y K hK => hnbr g hg y K hK

theorem mem_normalizer_ggG0_of_stdSub (hS : LargeEvenSStar p B x L)
    (hst : LargeEvenStandardType p B x L) (hDJ : LargeEvenStdSub p B x L D J) :
    x ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  exact mem_normalizer_ggG0 (Subgroup.centralizer_le_normalizer (L : Set G) hxCL)
    fun y K hK => (hst.2.2.1 y K ⟨hK.1, D, J, hDJ, hK.2⟩).1 hS.2.1

theorem not_mem_centralizer_ggG0_of_stdSub (hst : LargeEvenStandardType p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) :
    x ∉ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
  obtain ⟨⟨y, K, hK⟩, -⟩ := hst.2.2.2 D J hDJ
  intro hx
  apply hK.2.2.2
  have hxK : x ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le (fun k hk => le_ggG0_of_neighbor hK hk) hx
  have hbot : ⁅K, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr hxK
  rw [hbot]
  exact bot_le

theorem not_dvd_card_centralizer_ggG0_of_stdSub (hp : p.Prime) (hS : LargeEvenSStar p B x L)
    (hst : LargeEvenStandardType p B x L) (hDJ : LargeEvenStdSub p B x L D J) :
    ¬ p ∣ Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G)) := by
  have hxn := mem_normalizer_ggG0_of_stdSub hS hst hDJ
  have hxc := not_mem_centralizer_ggG0_of_stdSub hst hDJ
  have : Fact p.Prime := ⟨hp⟩
  have hox : orderOf x = p := orderOf_eq_prime (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  exact not_dvd_card_of_isCyclic_of_mem_normalizer hox hxc (mem_normalizer_centralizer hxn)
    (Subgroup.centralizer_le (fun l hl => (le_sup_left : L ≤ ggG0 p B x L D J) hl)) hxCL
    hS.2.2.2.2

end LemmaTwoThree

section Transvection

variable {G : Type} [Group G]

theorem ggIsTransvection_of_ggTransvection {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {a : G} (ha : a ∈ Subgroup.normalizer (Bs : Set G))
    (h : GGTransvection p Bs a) : ∃ φ ∈ ggInduced ⊤ Bs, GGIsTransvection p φ := by
  have hBsa : Bs.map (MulAut.conj a).toMonoidHom = Bs := map_conj_eq_of_mem_normalizer ha
  let φ : MulAut ↥Bs := ((MulAut.conj a).subgroupMap Bs).trans (MulEquiv.subgroupCongr hBsa)
  have hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = a * b * a⁻¹ := fun _ => rfl
  have hcomm : ∀ u ∈ Bs, ∀ v ∈ Bs, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hBs.1.is_comm.comm (⟨u, hu⟩ : ↥Bs) ⟨v, hv⟩)
  have hconj : ∀ b ∈ Bs, a * b * a⁻¹ ∈ Bs := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp ha b).mp hb
  have hcommut : ∀ b : G, b⁻¹ * (a * b * a⁻¹) = ⁅b⁻¹, a⁆ := fun b => by
    rw [commutatorElement_def]; group
  refine ⟨φ, ⟨a, Subgroup.mem_top a, ha, hφ⟩, ?_, ?_⟩
  · let fh : ↥Bs →* G :=
      { toFun := fun b => (b : G)⁻¹ * (a * b * a⁻¹)
        map_one' := by simp
        map_mul' := fun b c => by
          have h1 : ((c : G))⁻¹ * ((b : G)⁻¹ * (a * b * a⁻¹)) =
              ((b : G)⁻¹ * (a * b * a⁻¹)) * ((c : G))⁻¹ :=
            hcomm _ (Bs.inv_mem c.2) _ (Bs.mul_mem (Bs.inv_mem b.2) (hconj _ b.2))
          simp only [Subgroup.coe_mul, mul_inv_rev]
          calc (c : G)⁻¹ * (b : G)⁻¹ * (a * ((b : G) * (c : G)) * a⁻¹)
              = ((c : G)⁻¹ * ((b : G)⁻¹ * (a * b * a⁻¹))) * (a * c * a⁻¹) := by group
            _ = ((b : G)⁻¹ * (a * b * a⁻¹)) * ((c : G))⁻¹ * (a * c * a⁻¹) := by rw [h1]
            _ = (b : G)⁻¹ * (a * b * a⁻¹) * (((c : G))⁻¹ * (a * c * a⁻¹)) := by group }
    have hfh : ∀ b : ↥Bs, fh b = (b : G)⁻¹ * (a * b * a⁻¹) := fun _ => rfl
    have hker : Nat.card {b : ↥Bs // φ b = b} = Nat.card fh.ker := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
      rw [MonoidHom.mem_ker, hfh, ← Subtype.coe_inj, hφ, inv_mul_eq_one, eq_comm]
    have hrange : fh.range ≤ ⁅Bs, Subgroup.zpowers a⁆ := by
      rintro _ ⟨b, rfl⟩
      rw [hfh, hcommut]
      exact Subgroup.commutator_mem_commutator (Bs.inv_mem b.2) (Subgroup.mem_zpowers a)
    have hdvd : Nat.card fh.range ∣ p := h.1 ▸ Subgroup.card_dvd_of_le hrange
    have hne : Nat.card fh.range ≠ 1 := by
      intro h1
      have hbot : fh.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hcen : a ∈ Subgroup.centralizer (Bs : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have hb1 : fh ⟨b, hb⟩ = 1 := by
          have : fh ⟨b, hb⟩ ∈ fh.range := ⟨⟨b, hb⟩, rfl⟩
          rwa [hbot, Subgroup.mem_bot] at this
        rw [hfh, inv_mul_eq_one] at hb1
        calc b * a = a * b * a⁻¹ * a := by rw [← hb1]
          _ = a * b := by group
      have hc : ⁅Bs, Subgroup.zpowers a⁆ = ⊥ := by
        rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact Subgroup.zpowers_le.mpr hcen
      have := h.1
      rw [hc, Subgroup.card_bot] at this
      exact hp.one_lt.ne this
    have hcard : Nat.card fh.range = p :=
      ((Nat.dvd_prime hp).mp hdvd).resolve_left hne
    rw [hker, ← hcard]
    exact Subgroup.card_ker_mul_card_range fh
  · intro b
    apply Subtype.ext
    rw [hφ]
    have hmem : ((b⁻¹ * φ b : ↥Bs) : G) ∈ ⁅Bs, Subgroup.zpowers a⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
      rw [hcommut]
      exact Subgroup.commutator_mem_commutator (Bs.inv_mem b.2) (Subgroup.mem_zpowers a)
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (h.2 hmem)
    rw [← hc, mul_inv_cancel_right]

theorem not_ggTransvection_of_noTransvection {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (h : GGNoTransvection p Bs) :
    ∀ a ∈ Subgroup.normalizer (Bs : Set G), ¬ GGTransvection p Bs a := by
  intro a ha htr
  obtain ⟨φ, hφ, htφ⟩ := ggIsTransvection_of_ggTransvection hp hBs ha htr
  exact h φ hφ htφ

end Transvection

section LemmaNineFour

variable {G : Type} [Group G] [Finite G]

theorem centralizer_eq_bot_of_signalizers {p : ℕ} {G₀ D J : Subgroup G} (hchar : IsCharTwoType G)
    (hp : p.Prime) (hp2 : p ≠ 2) (hJG₀ : J ≤ G₀) (hDJ : D ≤ Subgroup.centralizer (J : Set G))
    (hodd : Odd (Nat.card (Subgroup.centralizer (G₀ : Set G))))
    (hsig : ∀ Q : Subgroup G, D ≤ Subgroup.normalizer (Q : Set G) →
      Nat.Coprime p (Nat.card Q) → Q ≤ Subgroup.normalizer (G₀ : Set G))
    (hJ : 2 ∣ Nat.card J) :
    Subgroup.centralizer (G₀ : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Subgroup.centralizer (G₀ : Set G) with hX
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 J))
  set T' : Subgroup G := (T : Subgroup J).map J.subtype with hT'
  have hT'J : T' ≤ J := Subgroup.map_subtype_le _
  have hT'ne : T' ≠ ⊥ := by
    intro h
    have hT1 : (T : Subgroup J) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ Subtype.coe_injective).mp h
    have := T.not_dvd_index
    rw [hT1, Subgroup.index_bot] at this
    exact this hJ
  have hT'p : IsPGroup 2 T' := T.isPGroup'.map J.subtype
  set Nn := Subgroup.normalizer (T' : Set G) with hNn
  have hcharN := hchar Nn ⟨T', hT'ne, hT'p, rfl⟩
  set Q := pCoreOf 2 Nn with hQ
  have hQp : IsPGroup 2 Q :=
    (Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 Nn).map Nn.subtype
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hcen : ∀ c ∈ Subgroup.centralizer (J : Set G), c ∈ Nn := fun c hc =>
    Subgroup.centralizer_le_normalizer (T' : Set G) (Subgroup.centralizer_le hT'J hc)
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := fun d hd =>
    mem_normalizer_pCoreOf (hcen d (hDJ hd))
  have hcop : Nat.Coprime p (Nat.card Q) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hQM : Q ≤ Subgroup.normalizer (G₀ : Set G) := hsig Q hDQ hcop
  have hXN : X ≤ Nn := fun c hc =>
    Subgroup.centralizer_le_normalizer (T' : Set G)
      (Subgroup.centralizer_le (fun t ht => hJG₀ (hT'J ht)) hc)
  have hXinf : Q ⊓ X = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hXC : X ≤ Subgroup.centralizer (Q : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hw1 : q * c * q⁻¹ * c⁻¹ ∈ Q := by
      have h1 : c * q⁻¹ * c⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pCoreOf (hXN hc)) q⁻¹).mp
          (Q.inv_mem hq)
      have := Q.mul_mem hq h1
      simpa [mul_assoc] using this
    have hw2 : q * c * q⁻¹ * c⁻¹ ∈ X := by
      have h1 : q * c * q⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hQM hq)) c).mp hc
      exact X.mul_mem h1 (X.inv_mem hc)
    have hw : q * c * q⁻¹ * c⁻¹ = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hw1, hw2⟩
      rwa [hXinf, Subgroup.mem_bot] at this
    calc q * c = q * c * q⁻¹ * c⁻¹ * (c * q) := by group
      _ = c * q := by rw [hw, one_mul]
  rw [eq_bot_iff]
  intro c hc
  have hcQ : c ∈ Q := hcharN (Subgroup.mem_inf.mpr ⟨hXN hc, hXC hc⟩)
  have := Subgroup.mem_inf.mpr ⟨hcQ, hc⟩
  rwa [hXinf] at this

end LemmaNineFour

end CFSG.StandardType
