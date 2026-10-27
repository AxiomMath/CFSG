module

public import CFSG.Quasithin.Vol2.Ch12Sec5Beta
public import CFSG.Quasithin.Vol2.Ch12Sec5Hat7
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableW
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32S
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Background.InternalSecRealB
public import CFSG.Quasithin.EmptyFaithful.Der6EMain
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152FinCore
public import CFSG.Quasithin.EmptyFaithful.S152He8Aut
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A5Sit15d
public import CFSG.Quasithin.H13.A6S1372L19c
public import CFSG.Quasithin.H13.A6S1372L74a
public import CFSG.Quasithin.H13.A6S1372L74d
public import CFSG.Quasithin.H13.A6S1372L74f
public import CFSG.Quasithin.H13.A6S1372L76Of3
public import CFSG.Quasithin.H13.A6S1372L76V
public import CFSG.Quasithin.H13.A6S13827a
public import CFSG.Quasithin.H13.A6S138Ia
public import CFSG.Quasithin.H13.A7Nat1238QTabA7
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34Out
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Lie
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.Sporadic.J4.QT2LocProof
public import Certificates.Kernel.J4Count.Prim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125Ir Matrix
open scoped commutatorElement Pointwise

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125BetaJ4

theorem fix_V3 : ∀ x : Fin 10 → ZMod 2, (∀ k : Fin 10, 6 < k.val → x k = 0) →
    (∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat (1 + Matrix.single 2 3 (1 : ZMod 2)) *ᵥ x) k = x k) →
    (∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat (1 + Matrix.single 3 4 (1 : ZMod 2)) *ᵥ x) k = x k) →
    ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 4 → x k = 0 := by
  decide +kernel

theorem wedge_fix_V3 : ∀ x : Fin 10 → ZMod 2, (∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 4 → x k = 0) →
    JonesParshall.wedgeMat (1 + Matrix.single 2 3 (1 : ZMod 2)) *ᵥ x = x ∧
      JonesParshall.wedgeMat (1 + Matrix.single 3 4 (1 : ZMod 2)) *ᵥ x = x := by
  decide +kernel

theorem wedge_t23 : JonesParshall.wedgeMat (1 + Matrix.single 2 3 (1 : ZMod 2)) *ᵥ
    (Pi.single 2 1 : Fin 10 → ZMod 2) = Pi.single 2 1 + Pi.single 1 1 := by
  decide +kernel

@[expose] def g3mat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def g3 : SL5 := ⟨g3mat, by decide +kernel⟩

theorem g3_pow_three : g3 ^ 3 = 1 := Subtype.ext (by decide +kernel)

theorem wedge_g3 : (∀ k : Fin 10, k ≠ 0 →
    (JonesParshall.wedgeMat g3mat *ᵥ (Pi.single 1 1 : Fin 10 → ZMod 2)) k =
      (Pi.single 4 1 : Fin 10 → ZMod 2) k) ∧
    ∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat (g3mat * g3mat) *ᵥ (Pi.single 1 1 : Fin 10 → ZMod 2)) k =
        (Pi.single 1 1 + Pi.single 4 1 : Fin 10 → ZMod 2) k := by
  decide +kernel

theorem g3_mem_q234 : g3 ∈ S125Pm.q234 := by
  rw [S125Pm.mem_q234]
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro i j hj hi
    change g3mat i j = 0
    fin_cases i <;> fin_cases j <;> simp_all <;> rfl

theorem card_V3_filter : (Finset.univ.filter fun x : Fin 10 → ZMod 2 =>
    ∀ k ∉ ({0, 1, 4} : Finset (Fin 10)), x k = 0).card = 8 := by
  decide +kernel

theorem eq_bot_of_perfect {R : Type*} [Group R] [hs : Group.IsSolvable R]
    (h : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊤) : (⊤ : Subgroup R) = ⊥ := by
  obtain ⟨n, hn⟩ := hs.solvable
  have hall : ∀ k, derivedSeries R k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih]; exact h
  rw [← hall n, hn]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

open S125Fin in
theorem almostSpecial (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    AlmostSpecialHyp F.V7 F.V1 L T (Subgroup.normalizer (F.V1 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have h2 := lemma12_5_2_of h1222 G T L V F hH
  have hT2 : IsPGroup 2 ↥T := hyp.sylow.1
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hV₇V : F.V7 ≤ V := Subgroup.map_subtype_le _
  have hV₁V₇ : F.V1 ≤ F.V7 := S125L5a.sub_mono_le F (by decide)
  have hTV₇ : T ≤ Subgroup.normalizer (F.V7 : Set G) :=
    S125Tr2.T_le_normalizer_sub F hf.T_le _ fun u hu =>
      S125W.coordFix_V7_of (S125Tr2.stabGam_of_upperTri hu 2)
  have hV₇e : IsElemAbelian 2 F.V7 := by
    have := hf.comm
    exact ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from
      congrArg (Subtype.val : ↥V → G) (mul_comm' (⟨a, hV₇V a.2⟩ : V) ⟨b, hV₇V b.2⟩))⟩⟩,
      fun x hx => hf.sq x (hV₇V hx)⟩
  have hO2L : L = oTwoUpper L := (hyp.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx).symm
  have hTM₁ : T ≤ mi T L F.V1 := le_inf le_sup_right hTG₁
  have hlOne : lOne L F.V1 ≤ mi T L F.V1 :=
    (oTwoUpper_le _).trans (inf_le_inf_right _ le_sup_left)
  have hM₁le : mi T L F.V1 ≤ lOne L F.V1 ⊔ T := by
    have hTs : QuasithinUnique.IsSylowTwoOf T (mi T L F.V1) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTM₁
    rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow hTs]
    refine sup_le_sup_right ((Subgroup.closure_le _).mpr ?_) T
    rintro x ⟨hxM, hxo⟩
    obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hT2 hyp.normalizes hxM.1
    have hxL : x ∈ L :=
      mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hxo))
        (pow_orderOf_eq_one x) hj
    exact Subgroup.subset_closure ⟨⟨hxL, hxM.2⟩, hxo⟩
  have hirr := h2.1.2.2.2.2.1
  have hX : lOne L F.V1 ⊔ T ≤ mi T L F.V1 := sup_le hlOne hTM₁
  exact
    { elemAbelian := hV₇e
      ne_bot := S125.V1_ne_bot F
      le_V := hV₁V₇
      oTwo_eq := hO2L
      V_le_T := hV₇V.trans hf.le_T
      T_le_normV₁ := hTG₁
      T_le_normV := hTV₇
      T_le_normL := hyp.normalizes
      sylow_LT := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
      H_le := le_rfl
      lOne_sup_le := sup_le (hlOne.trans inf_le_right) hTG₁
      sylow_H := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTG₁
      charTwo := charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTG₁, S125O2P.pCoreOf_G1_ne_bot F⟩
      irred := ⟨hirr.1, hX.trans hirr.2.2.1, hX.trans hirr.2.1,
        fun W h1 h2 h3 => hirr.2.2.2 W h1 h2 (hM₁le.trans h3)⟩ }

theorem conjClosure_le_pCoreOf (h1222 : Stmt12_2_2) (F : Frame125 T L V)
    (hH : Hyp125 G T L V) :
    conjClosure F.V7 (Subgroup.normalizer (F.V1 : Set G)) ≤
      pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) := by
  have h := almostSpecial h1222 F hH
  intro u hu
  have hcc := h.conjClosure_le_N
  have hQ : tmk F.V1 ⟨u, hcc hu⟩ ∈ tildeOf F.V1 (pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G))) :=
    omegaOneCenterOf_le _ ((secImg_le_iff.1 h.G22_one.2) ⟨u, hcc hu⟩ hu)
  exact (secMk_mem_secImg_iff h.V₁_le_pCoreOf).1 hQ

omit [Finite G] in
theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have hle : ∀ {X : Subgroup G} {x : G}, x ∈ Subgroup.normalizer (X : Set G) →
      X.map (MulAut.conj x).toMonoidHom ≤ X := by
    rintro X x hx _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  have hmap : ∀ {x : G}, x ∈ Subgroup.normalizer (H : Set G) →
      x ∈ Subgroup.normalizer (K : Set G) →
      (⁅H, K⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom ≤ ⁅H, K⁆ := by
    intro x h1 h2
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono (hle h1) (hle h2)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hmap hH hK ⟨y, hy, rfl⟩
  · intro hy
    have h := hmap (Subgroup.inv_mem _ hH) (Subgroup.inv_mem _ hK) ⟨_, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using h

omit [Finite G] in
theorem mem_normalizer_centralizerMod {N X U : Subgroup G} {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hgN : g ∈ Subgroup.normalizer (N : Set G)) :
    ∀ x ∈ centralizerMod N X U, g * x * g⁻¹ ∈ centralizerMod N X U := by
  intro x hx
  obtain ⟨hxX, hxN, hxc⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgX x).mp hxX, Subgroup.mul_mem _
    (Subgroup.mul_mem _ hgN hxN) (Subgroup.inv_mem _ hgN), fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) u).mp hu
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp hgN _).mp (hxc _ hu')
  have e : g * (x * (g⁻¹ * u * g) * x⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ * u⁻¹ := by group
  rw [← e]
  exact h1

omit [Finite G] in
theorem comm_mem_V1_iff (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (l : ↥(L ⊔ T)) (w : ↥V) :
    (l : G) * w * (l : G)⁻¹ * (w : G)⁻¹ ∈ F.V1 ↔ ∀ k : Fin 10, k ≠ 0 →
      (JonesParshall.wedgeMat (S125Pm.phi F hLV hTV l : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (F.e w)) k = Multiplicative.toAdd (F.e w) k := by
  have hlV : (l : G) ∈ Subgroup.normalizer (V : Set G) := sup_le hLV hTV l.2
  set w' : ↥V := ⟨l * w * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hlV _).mp w.2⟩ with hw'
  have hc := S125Beta.e_conj F hLV hTV l w w' rfl
  have he : (l : G) * w * (l : G)⁻¹ * (w : G)⁻¹ = ((w' * w⁻¹ : ↥V) : G) := by simp [hw']
  show (l : G) * w * (l : G)⁻¹ * (w : G)⁻¹ ∈ F.sub {0} ↔ _
  rw [he, S125St.mem_sub_iff, map_mul, map_inv, toAdd_mul, toAdd_inv, hc]
  constructor
  · intro h k hk
    have := h k (by simpa using hk)
    rw [Pi.add_apply, Pi.neg_apply] at this
    exact (add_neg_eq_zero.1 this)
  · intro h k hk
    rw [Pi.add_apply, Pi.neg_apply, h k (by simpa using hk), add_neg_cancel]


section Sec

variable {A B X : Subgroup G}

omit [Finite G] in
theorem map_conjK_subgroupOf {x : G} (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) :
    (B.subgroupOf A).map (S125Hat7.conjK A hxA).toMonoidHom = B.subgroupOf A := by
  ext a
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hxB _).mp hb
  · intro ha
    refine ⟨(S125Hat7.conjK A hxA).symm a, ?_, MulEquiv.apply_symm_apply _ _⟩
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxB) _).mp ha
    simpa [S125Hat7.conjK] using h

@[expose] noncomputable def secAct [(B.subgroupOf A).Normal]
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hXB : X ≤ Subgroup.normalizer (B : Set G)) :
    ↥X →* MulAut (↥A ⧸ B.subgroupOf A) where
  toFun x := QuotientGroup.congr (B.subgroupOf A) (B.subgroupOf A) (S125Hat7.conjK A (hXA x.2))
    (map_conjK_subgroupOf (hXA x.2) (hXB x.2))
  map_one' := MulEquiv.ext fun q => QuotientGroup.induction_on q fun a =>
    congrArg (QuotientGroup.mk (s := B.subgroupOf A)) (Subtype.ext (by simp [S125Hat7.conjK]))
  map_mul' x y := MulEquiv.ext fun q => QuotientGroup.induction_on q fun a =>
    congrArg (QuotientGroup.mk (s := B.subgroupOf A))
      (Subtype.ext (by simp [S125Hat7.conjK, mul_assoc]))

omit [Finite G] in
theorem secAct_mk [(B.subgroupOf A).Normal]
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (x : ↥X) (a : ↥A) :
    secAct hXA hXB x (QuotientGroup.mk a) =
      QuotientGroup.mk (S125Hat7.conjK A (hXA x.2) a) := rfl

omit [Finite G] in
theorem secAct_eq_one_iff [(B.subgroupOf A).Normal]
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (x : ↥X) :
    secAct hXA hXB x = 1 ↔ ∀ a ∈ A, a⁻¹ * ((x : G) * a * (x : G)⁻¹) ∈ B := by
  constructor
  · intro h a ha
    have h1 : (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ B.subgroupOf A) =
        QuotientGroup.mk (S125Hat7.conjK A (hXA x.2) ⟨a, ha⟩) := by
      rw [← secAct_mk hXA hXB, h]
      rfl
    have h2 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1)
    simpa [S125Hat7.conjK, mul_assoc] using h2
  · intro h
    refine MulEquiv.ext fun q => QuotientGroup.induction_on q fun a => ?_
    show (QuotientGroup.mk (S125Hat7.conjK A (hXA x.2) a) : ↥A ⧸ B.subgroupOf A) =
      QuotientGroup.mk a
    refine (QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)).symm
    simpa [S125Hat7.conjK, mul_assoc] using h a a.2

end Sec


theorem not_mem_V7_idx :
    ∀ k : Fin 10, 6 < k.val → k ∉ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 10)) := by
  decide

theorem comm_mem_of_irr {V₁ V₇ Q M : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (hQV₁ : Q ≤ Subgroup.normalizer (V₁ : Set G)) (hV₇Q : V₇ ≤ Q)
    (hQV₇ : Q ≤ Subgroup.normalizer (V₇ : Set G)) (hirr : IrrSection M V₁ V₇)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hV₇N : V₇ ≤ Subgroup.normalizer (V₁ : Set G)) :
    ∀ q ∈ Q, ∀ v ∈ V₇, v * q * v⁻¹ * q⁻¹ ∈ V₁ := by
  set W := centralizerMod V₁ V₇ Q with hW
  have h1 : V₁ ≤ W := fun v hv => ⟨hirr.1.le hv, Subgroup.le_normalizer hv, fun q hq => by
    have h := (Subgroup.mem_normalizer_iff.mp (hQV₁ hq) _).mp (V₁.inv_mem hv)
    rw [show v * q * v⁻¹ * q⁻¹ = v * (q * v⁻¹ * q⁻¹) by group]
    exact V₁.mul_mem hv h⟩
  have hWeq : W = V₇ := by
    rcases hirr.2.2.2 W h1 (centralizerMod_le_left _ _ _) (fun m hm =>
      S125St.mem_normalizer_of_conj_le (mem_normalizer_centralizerMod (hirr.2.2.1 hm)
        (hMQ hm) (hirr.2.1 hm))) with h | h
    · exfalso
      obtain ⟨z, hzV₇, hzV₁, hz⟩ := S125Beta.exists_fix_mod hQ2 hQV₁ hV₇Q hQV₇ hirr.1.not_ge
      have hzW : z ∈ W := ⟨hzV₇, hV₇N hzV₇, hz⟩
      rw [h] at hzW
      exact hzV₁ hzW
    · exact h
  intro q hq v hv
  have hvW : v ∈ W := by
    rw [hWeq]
    exact hv
  exact hvW.2.2 q hq

theorem secAct_eq_one_of_perfect {A B C : Subgroup G} [(B.subgroupOf A).Normal]
    (hCA : C ≤ Subgroup.normalizer (A : Set G)) (hCB : C ≤ Subgroup.normalizer (B : Set G))
    (hcard : Nat.card (↥A ⧸ B.subgroupOf A) ≤ 4) {Q' : Type*} [Group Q'] (f : ↥C →* Q')
    (hf : ⁅f.range, f.range⁆ = f.range) (hker : ∀ c, f c = 1 → secAct hCA hCB c = 1) :
    ∀ c, secAct hCA hCB c = 1 := by
  set ρ := secAct hCA hCB with hρ
  have hRperf : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact ρ.range.mul_mem (ρ.range.mul_mem (ρ.range.mul_mem ha hb) (ρ.range.inv_mem ha))
        (ρ.range.inv_mem hb)
    rintro _ ⟨c, rfl⟩
    have h1 : f c ∈ (commutator ↥C).map f := by
      rw [map_commutator_eq, hf]
      exact ⟨c, rfl⟩
    obtain ⟨d, hd, hdc⟩ := h1
    have h3 : ρ c = ρ d := by
      rw [show c = d * (d⁻¹ * c) by group, map_mul,
        hker (d⁻¹ * c) (by rw [map_mul, map_inv, hdc, inv_mul_cancel]), mul_one]
    rw [h3, ← map_commutator_eq]
    exact ⟨d, hd, rfl⟩
  have hRsolv : Group.IsSolvable ↥ρ.range := by
    have := Equiv.Perm.isSolvable (α := ↥A ⧸ B.subgroupOf A) hcard
    exact Group.isSolvable_of_isSolvable_injective
      (f := (MulAut.toPerm (M := ↥A ⧸ B.subgroupOf A)).comp ρ.range.subtype)
      (fun a b h => Subtype.ext (MulEquiv.ext fun x =>
        congrArg (fun σ : Equiv.Perm (↥A ⧸ B.subgroupOf A) => σ x) h))
  have hP : Group.IsPerfect ↥ρ.range := Subgroup.isPerfect_iff.mpr hRperf
  have h0 : commutator ↥ρ.range = ⊤ := Group.IsPerfect.commutator_eq_top
  have h := eq_bot_of_perfect (R := ↥ρ.range) (by rw [← commutator_def]; exact h0)
  intro c
  have h1 : (⟨ρ c, c, rfl⟩ : ↥ρ.range) ∈ (⊤ : Subgroup ↥ρ.range) := Subgroup.mem_top _
  rw [h, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

section Pre

variable {K₁ : Subgroup G}

omit [Finite G] in
theorem mk_mem_img_of_mem_sup {X : Subgroup G} (hXK : X ≤ K₁)
    (hXO : X ≤ Subgroup.normalizer (pCoreOf 2 K₁ : Set G)) {x : G} (hx : x ∈ X ⊔ pCoreOf 2 K₁) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)
      (⟨x, sup_le hXK (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁) hx⟩ : ↥K₁) ∈ S125Cfg.img K₁ X := by
  have hx' : x ∈ ((X : Set G) * (pCoreOf 2 K₁ : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X _ hXO]
    exact hx
  obtain ⟨v, hv, o, ho, rfl⟩ := hx'
  have hoK : o ∈ K₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₁ ho
  have e1 : (⟨v * o, sup_le hXK (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁) hx⟩ : ↥K₁) =
      ⟨v, hXK hv⟩ * ⟨o, hoK⟩ := rfl
  have ho1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) (⟨o, hoK⟩ : ↥K₁) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← A6.A6L74.mem_pCoreOf_iff]
    exact ho
  rw [e1, map_mul, ho1, mul_one]
  exact ⟨⟨v, hXK hv⟩, hv, rfl⟩

theorem mk_mem_normalizer_iff {X : Subgroup G} (hXK : X ≤ K₁)
    (hXO : X ≤ Subgroup.normalizer (pCoreOf 2 K₁ : Set G)) (k : ↥K₁) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) k ∈
        Subgroup.normalizer (S125Cfg.img K₁ X : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ↔
      (k : G) ∈ Subgroup.normalizer ((X ⊔ pCoreOf 2 K₁ : Subgroup G) : Set G) := by
  have hXOK : X ⊔ pCoreOf 2 K₁ ≤ K₁ := sup_le hXK (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁)
  constructor
  · intro hk
    refine S125St.mem_normalizer_of_conj_le fun x hx => ?_
    have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) (k * ⟨x, hXOK hx⟩ * k⁻¹) ∈
        S125Cfg.img K₁ X := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hk _).mp (mk_mem_img_of_mem_sup hXK hXO hx)
    have h1 := S125Cfg.mem_of_mk_mem (A := X ⊔ pCoreOf 2 K₁) le_sup_right
      (k * ⟨x, hXOK hx⟩ * k⁻¹) (S125Cfg.img_mono le_sup_left hk')
    simpa using h1
  · intro hk
    apply S125St.mem_normalizer_of_conj_le
    rintro _ ⟨v, hv, rfl⟩
    have hv' : ((k : G) * v * (k : G)⁻¹) ∈ X ⊔ pCoreOf 2 K₁ :=
      (Subgroup.mem_normalizer_iff.mp hk _).mp (Subgroup.mem_sup_left hv)
    have e2 : k * v * k⁻¹ = (⟨(k : G) * v * (k : G)⁻¹, hXOK hv'⟩ : ↥K₁) := Subtype.ext rfl
    rw [← map_inv, ← map_mul, ← map_mul, e2]
    exact mk_mem_img_of_mem_sup hXK hXO hv'

theorem mem_pCoreOf_of_mk_mem {Nt : Subgroup G} {NE : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)}
    (hNtK : Nt ≤ K₁)
    (hiff : ∀ k : ↥K₁, QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) k ∈ NE ↔ (k : G) ∈ Nt)
    (k : ↥K₁) (hk : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) k ∈ pCoreOf 2 NE) :
    (k : G) ∈ pCoreOf 2 Nt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hπ
  set P₂ : Subgroup G := ((pCoreOf 2 NE).comap π).map K₁.subtype with hP₂
  have hP₂Nt : P₂ ≤ Nt := by
    rintro _ ⟨k', hk', rfl⟩
    exact (hiff k').1 (CFSG.LieType.BorelTits.pCoreOf_le 2 NE hk')
  have hP₂n : Nt ≤ Subgroup.normalizer (P₂ : Set G) := by
    intro n hn
    apply S125St.mem_normalizer_of_conj_le
    rintro _ ⟨k', hk', rfl⟩
    have hnK := hNtK hn
    refine ⟨⟨n, hnK⟩ * k' * ⟨n, hnK⟩⁻¹, ?_, rfl⟩
    show π (⟨n, hnK⟩ * k' * ⟨n, hnK⟩⁻¹) ∈ pCoreOf 2 NE
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 NE ((hiff ⟨n, hnK⟩).2 hn)) _).mp hk'
  have hP₂2 : IsPGroup 2 ↥P₂ := by
    rintro ⟨_, k', hk', rfl⟩
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 NE) ⟨π k', hk'⟩
    have h1 : π (k' ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have h2 : k' ^ 2 ^ a ∈ CFSG.pCore 2 ↥K₁ := by
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K₁)) ⟨_, h2⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((k' : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥K₁) => ((z : ↥K₁) : G)) hb
      simpa using this
    simpa [pow_add, pow_mul] using hb'
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP₂Nt hP₂n hP₂2 ⟨k, hk, rfl⟩

end Pre

omit [Finite G] in
theorem conj_mem_V3 (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {l₁ l₂ : ↥(L ⊔ T)}
    (hφ₁ : (S125Pm.phi F hLV hTV l₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      1 + Matrix.single 2 3 1)
    (hφ₂ : (S125Pm.phi F hLV hTV l₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      1 + Matrix.single 3 4 1)
    {Q : Subgroup G} (hQ : ∀ q ∈ Q, ∀ v ∈ F.V7, v * q * v⁻¹ * q⁻¹ ∈ F.V1) {c : G}
    (hcV₇ : c ∈ Subgroup.normalizer (F.V7 : Set G))
    (hcV₁ : c ∈ Subgroup.normalizer (F.V1 : Set G))
    (hc₁ : c⁻¹ * l₁ * c * (l₁ : G)⁻¹ ∈ Q) (hc₂ : c⁻¹ * l₂ * c * (l₂ : G)⁻¹ ∈ Q) :
    ∀ x ∈ F.V3, c * x * c⁻¹ ∈ F.V3 := by
  have hV₇V : F.V7 ≤ V := Subgroup.map_subtype_le _
  have hV₃V : F.V3 ≤ V := Subgroup.map_subtype_le _
  have hV₃V₇ : F.V3 ≤ F.V7 := S125L5a.sub_mono_le F (by decide)
  intro x hx
  set xv : ↥V := ⟨x, hV₃V hx⟩ with hxv
  have hcx : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 4 → Multiplicative.toAdd (F.e xv) k = 0 := by
    have h := (S125St.mem_sub_iff F {0, 1, 4} xv).1 hx
    intro k h0 h1 h4
    exact h k (by simp [h0, h1, h4])
  obtain ⟨hw1, hw2⟩ := wedge_fix_V3 _ hcx
  have key : ∀ (l : ↥(L ⊔ T)) (M : Matrix (Fin 5) (Fin 5) (ZMod 2)),
      (S125Pm.phi F hLV hTV l : Matrix (Fin 5) (Fin 5) (ZMod 2)) = M →
      JonesParshall.wedgeMat M *ᵥ Multiplicative.toAdd (F.e xv) =
        Multiplicative.toAdd (F.e xv) → (l : G) * x * (l : G)⁻¹ = x := by
    intro l M hM hW
    have hlV : (l : G) ∈ Subgroup.normalizer (V : Set G) := sup_le hLV hTV l.2
    set w : ↥V := ⟨l * x * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hlV _).mp xv.2⟩ with hw
    have hc := S125Beta.e_conj F hLV hTV l xv w rfl
    rw [hM, hW] at hc
    have hwx : w = xv := F.e.injective (Multiplicative.toAdd.injective hc)
    exact congrArg Subtype.val hwx
  have hx1 := key l₁ _ hφ₁ hw1
  have hx2 := key l₂ _ hφ₂ hw2
  have hxV₇ := hV₃V₇ hx
  have hwV₇ : c * x * c⁻¹ ∈ F.V7 := (Subgroup.mem_normalizer_iff.mp hcV₇ x).mp hxV₇
  set w : ↥V := ⟨c * x * c⁻¹, hV₇V hwV₇⟩ with hw
  have hlw : ∀ l : ↥(L ⊔ T), c⁻¹ * l * c * (l : G)⁻¹ ∈ Q → (l : G) * x * (l : G)⁻¹ = x →
      (l : G) * w * (l : G)⁻¹ * (w : G)⁻¹ ∈ F.V1 := by
    intro l hq hlx
    have hlx' : (l : G)⁻¹ * x * l = x := by
      calc (l : G)⁻¹ * x * l = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * l := by rw [hlx]
        _ = x := by group
    have h1 : (c⁻¹ * l * c * (l : G)⁻¹) * x * (c⁻¹ * l * c * (l : G)⁻¹)⁻¹ * x⁻¹ ∈ F.V1 := by
      have h := F.V1.inv_mem (hQ _ hq x hxV₇)
      rwa [show (x * (c⁻¹ * l * c * (l : G)⁻¹) * x⁻¹ * (c⁻¹ * l * c * (l : G)⁻¹)⁻¹)⁻¹ =
        (c⁻¹ * l * c * (l : G)⁻¹) * x * (c⁻¹ * l * c * (l : G)⁻¹)⁻¹ * x⁻¹ by group] at h
    have h2 := (Subgroup.mem_normalizer_iff.mp hcV₁ _).mp h1
    have e : (l : G) * (c * x * c⁻¹) * (l : G)⁻¹ * (c * x * c⁻¹)⁻¹ =
        c * ((c⁻¹ * l * c * (l : G)⁻¹) * x * (c⁻¹ * l * c * (l : G)⁻¹)⁻¹ * x⁻¹) * c⁻¹ := by
      calc (l : G) * (c * x * c⁻¹) * (l : G)⁻¹ * (c * x * c⁻¹)⁻¹
          = (l : G) * c * ((l : G)⁻¹ * x * l) * c⁻¹ * (l : G)⁻¹ * (c * x * c⁻¹)⁻¹ := by
            rw [hlx']
            group
        _ = c * ((c⁻¹ * l * c * (l : G)⁻¹) * x * (c⁻¹ * l * c * (l : G)⁻¹)⁻¹ * x⁻¹) *
            c⁻¹ := by group
    show (l : G) * (c * x * c⁻¹) * (l : G)⁻¹ * (c * x * c⁻¹)⁻¹ ∈ F.V1
    rw [e]
    exact h2
  have hw1' := (comm_mem_V1_iff F hLV hTV l₁ w).1 (hlw l₁ hc₁ hx1)
  have hw2' := (comm_mem_V1_iff F hLV hTV l₂ w).1 (hlw l₂ hc₂ hx2)
  rw [hφ₁] at hw1'
  rw [hφ₂] at hw2'
  have hsupp : ∀ k : Fin 10, 6 < k.val → Multiplicative.toAdd (F.e w) k = 0 := by
    have h := (S125St.mem_sub_iff F {0, 1, 2, 3, 4, 5, 6} w).1 hwV₇
    exact fun k hk => h k (not_mem_V7_idx k hk)
  have h3 := fix_V3 _ hsupp hw1' hw2'
  show (w : G) ∈ F.sub {0, 1, 4}
  rw [S125St.mem_sub_iff]
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact h3 k hk.1 hk.2.1 hk.2.2

theorem exists_mem_oTwoUpper_P (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    ∃ (y : ↥(L ⊔ T)) (a : ℕ), (y : G) ∈ oTwoUpper F.P ∧
      S125Pm.phi F hLV hTV y = g3 ^ 2 ^ a := by
  have hf := S125Ex.Facts125.of h1222 hH
  obtain ⟨p, hp⟩ := S125Pm.phi_surjective F hLV hTV g3
  have hpP : (p : G) ∈ F.P := (S125Pm.mem_P_iff F p).2 (hp ▸ g3_mem_q234)
  have hp3 : ((p ^ 3 : ↥(L ⊔ T)) : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨(p ^ 3).2, (S125Pm.phi_eq_one_iff F hLV hTV (p ^ 3)).1
      (by rw [map_pow, hp, g3_pow_three])⟩
  obtain ⟨a, ha⟩ := S125Tr2.isPGroup_centralizer hH hf ⟨_, hp3⟩
  refine ⟨p ^ 2 ^ a, a, ?_, by rw [map_pow, hp]⟩
  have hy3 : ((p ^ 2 ^ a : ↥(L ⊔ T)) : G) ^ 3 = 1 := by
    have h1 : ((p : G) ^ 3) ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    rw [Subgroup.coe_pow, ← pow_mul, mul_comm (2 ^ a) 3, pow_mul, h1]
  have hyodd : Odd (orderOf ((p ^ 2 ^ a : ↥(L ⊔ T)) : G)) := by
    have hd := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hd with h | h <;> rw [h] <;> decide
  refine mem_oTwoUpper_of_odd ?_ hyodd
  rw [Subgroup.coe_pow]
  exact F.P.pow_mem hpP _

omit [Finite G] in
theorem not_comm_mem_V1 (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {y : ↥(L ⊔ T)} {a : ℕ}
    (hφy : S125Pm.phi F hLV hTV y = g3 ^ 2 ^ a) :
    ¬ (y : G) * (S125Beta.bvec F 1 : ↥V) * (y : G)⁻¹ * ((S125Beta.bvec F 1 : ↥V) : G)⁻¹ ∈
      F.V1 := by
  intro hy1
  rw [comm_mem_V1_iff F hLV hTV y (S125Beta.bvec F 1), hφy] at hy1
  have h4 := hy1 4 (by decide)
  rw [S125Beta.bvec, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h4
  have hmod : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by
    have h3 : ¬ 3 ∣ 2 ^ a := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h
      omega
    omega
  rw [pow_eq_pow_mod (2 ^ a) g3_pow_three] at h4
  rcases hmod with h | h <;> rw [h] at h4
  · rw [pow_one] at h4
    change (JonesParshall.wedgeMat g3mat *ᵥ _) 4 = _ at h4
    rw [wedge_g3.1 4 (by decide)] at h4
    simp at h4
  · rw [Matrix.SpecialLinearGroup.coe_pow, sq] at h4
    change (JonesParshall.wedgeMat (g3mat * g3mat) *ᵥ _) 4 = _ at h4
    rw [wedge_g3.2 4 (by decide)] at h4
    simp at h4

theorem not_comm_le_V1 (hJs : IsSimpleGroup NativeSporadic.J4) (h1222 : Stmt12_2_2)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hLK : li L F.V1 ≤ K₁) (e : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* NativeSporadic.J4)
    {U : Subgroup G} (hV₇U : F.V7 ≤ U)
    (hUn : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hOU : ∀ o ∈ pCoreOf 2 K₁, ∀ u ∈ U, o * u * o⁻¹ * u⁻¹ ∈ F.V1)
    (hV : ¬ V ≤ pCoreOf 2 K₁) : ¬ ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ F.V1 := by
  intro hall
  have hf := S125Ex.Facts125.of h1222 hH
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hVK : V ≤ K₁ := (S125L8.V_le_l1 h1222 F hH).trans hLK
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hπ
  set C := centralizerMod F.V1 K₁ U with hC
  have hVC : V ≤ C := fun v hv => ⟨hVK hv, hKG (hVK hv), fun u hu => by
    have h1 := F.V1.inv_mem (hall u hu v hv)
    rwa [show (u * v * u⁻¹ * v⁻¹)⁻¹ = v * u * v⁻¹ * u⁻¹ by group] at h1⟩
  have hOKC : pCoreOf 2 K₁ ≤ C := fun o ho => ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 K₁ ho,
    hKG (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁ ho), fun u hu => hOU o ho u hu⟩
  have hCK : C ≤ K₁ := centralizerMod_le_left _ _ _
  have hCn : (C.subgroupOf K₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).2 fun k hk =>
      S125Fin.mem_normalizer_centralizerMod hk (hUn (hKG hk)) (hKG hk)
  have hQs : IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := @MulEquiv.isSimpleGroup _ _ _ _ hJs e
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hQs _
    (hCn.map π (QuotientGroup.mk'_surjective _)) with hb | ht
  · apply hV
    intro v hv
    have h1 : π ⟨v, hVK hv⟩ ∈ (C.subgroupOf K₁).map π := ⟨⟨v, hVK hv⟩, hVC hv, rfl⟩
    rw [hb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← A6.A6L74.mem_pCoreOf_iff] at h1
    exact h1
  · obtain ⟨-, hphi⟩ := S125Pm.phi_li_iff h1222 F hH (S125L8.autOn_l1 h1222 F hH)
    obtain ⟨l₁, hl₁, hφ₁⟩ :=
      hphi _ (S125Gen.tv_mem_pR (show (2 : Fin 5) ≠ 3 by decide) (by decide))
    have hl₁C : (l₁ : G) ∈ C := by
      have h1 : π ⟨l₁, hLK hl₁⟩ ∈ (C.subgroupOf K₁).map π := by
        rw [ht]
        exact Subgroup.mem_top _
      exact S125Cfg.mem_of_mk_mem hOKC _ h1
    have hb2 : ((S125Beta.bvec F 2 : ↥V) : G) ∈ F.V7 := by
      show ((S125Beta.bvec F 2 : ↥V) : G) ∈ F.sub {0, 1, 2, 3, 4, 5, 6}
      rw [S125St.mem_sub_iff, S125Beta.bvec, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      intro k hk
      exact Pi.single_eq_of_ne (by rintro rfl; simp at hk) _
    have h1 := hl₁C.2.2 _ (hV₇U hb2)
    rw [comm_mem_V1_iff F hf.normalizes hf.T_le l₁ (S125Beta.bvec F 2), hφ₁] at h1
    have h2 := h1 1 (by decide)
    change (JonesParshall.wedgeMat (1 + Matrix.single 2 3 (1 : ZMod 2)) *ᵥ _) 1 = _ at h2
    rw [S125Beta.bvec, MulEquiv.apply_symm_apply, toAdd_ofAdd, wedge_t23] at h2
    simp at h2

theorem comm_sup_eq (hJs : IsSimpleGroup NativeSporadic.J4) (h1222 : Stmt12_2_2)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁) (e : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* NativeSporadic.J4)
    (hV : ¬ V ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G))) :
    V ⊓ pCoreOf 2 K₁ = F.V7 ∧
      ⁅conjClosure F.V7 (Subgroup.normalizer (F.V1 : Set G)), V ⊔ pCoreOf 2 K₁⁆ ⊔ F.V1 =
        F.V7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have h2 := lemma12_5_2_of h1222 G T L V F hH
  set G₁ := Subgroup.normalizer (F.V1 : Set G) with hG₁
  set O₁ := pCoreOf 2 G₁ with hO₁
  set OK := pCoreOf 2 K₁ with hOK
  set M₁ := mi T L F.V1 with hM₁
  set U₁ := conjClosure F.V7 G₁ with hU₁
  have hKG : K₁ ≤ G₁ := le_of_mem_cComp hK
  have hVK : V ≤ K₁ := (S125L8.V_le_l1 h1222 F hH).trans hLK
  have hV₇V : F.V7 ≤ V := Subgroup.map_subtype_le _
  have hV₁V₇ : F.V1 ≤ F.V7 := S125L5a.sub_mono_le F (by decide)
  have hMV : M₁ ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans (sup_le hf.normalizes hf.T_le)
  have hMG₁ : M₁ ≤ G₁ := inf_le_right
  have hG₁O : G₁ ≤ Subgroup.normalizer (OK : Set G) :=
    hK₁n.trans (S125Fin.normalizer_le_normalizer_pCoreOf K₁)
  have hOKO₁ : OK ≤ O₁ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hKG) hG₁O
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hO₁K : O₁ ⊓ K₁ ≤ OK := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₁ (hKG hk), Subgroup.le_normalizer hk⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁).to_le inf_le_left)
  have hirr17 := h2.1.2.2.2.2.1
  have hirr7 := h2.1.2.2.2.2.2
  have hASH := almostSpecial h1222 F hH
  have hQU : ∀ q ∈ O₁, ∀ u ∈ U₁, q * u * q⁻¹ * u⁻¹ ∈ F.V1 :=
    fun q hq u hu => S125Fin.comm_mem_of_almostSpecial hASH hq hu
  have hUO : U₁ ≤ O₁ := conjClosure_le_pCoreOf h1222 F hH
  have hUT : U₁ ≤ T := hASH.G22_three.1
  have hV₇U : F.V7 ≤ U₁ := le_conjClosure _ _
  have hUn : G₁ ≤ Subgroup.normalizer (U₁ : Set G) := le_normalizer_conjClosure _ _
  have hV₇OK : F.V7 ≤ OK := fun v hv => hO₁K ⟨hUO (hV₇U hv), hVK (hV₇V hv)⟩
  have hsec : ∀ W : Subgroup G, M₁ ≤ Subgroup.normalizer (W : Set G) → F.V7 ≤ W → ¬ V ≤ W →
      V ⊓ W = F.V7 := by
    intro W hW h7 hVW
    rcases hirr7.2.2.2 (V ⊓ W) (le_inf hV₇V h7) inf_le_left
      (fun m hm => Subgroup.inf_normalizer_le_normalizer_inf ⟨hMV hm, hW hm⟩) with h | h
    · exact h
    · exact absurd (show V ≤ W by rw [← h]; exact inf_le_right) hVW
  have hVO₁ : V ⊓ O₁ = F.V7 := hsec O₁
    (fun m hm => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₁ (hMG₁ hm))
    (hV₇U.trans hUO) hV
  have hVOK : V ⊓ OK = F.V7 := hsec OK (fun m hm => hG₁O (hMG₁ hm)) hV₇OK
    (fun h => hV (h.trans hOKO₁))
  refine ⟨hVOK, ?_⟩
  have hA : ∀ u ∈ U₁, ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ F.V7 := by
    intro u hu v hv
    rw [← hVO₁]
    refine ⟨V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hf.T_le (hUT hu)) v).mp hv)
      (V.inv_mem hv), hUO ?_⟩
    have h1 : v * u⁻¹ * v⁻¹ ∈ U₁ :=
      (Subgroup.mem_normalizer_iff.mp (hUn (hKG (hVK hv))) _).mp (U₁.inv_mem hu)
    rw [show u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) by group]
    exact U₁.mul_mem hu h1
  have hB := not_comm_le_V1 hJs h1222 F hH hK hLK e hV₇U hUn
    (fun o ho u hu => hQU o (hOKO₁ ho) u hu) (fun h => hV (h.trans hOKO₁))
  have hC7 : ⁅U₁, V⁆ ⊔ F.V1 = F.V7 := by
    have hle : ⁅U₁, V⁆ ⊔ F.V1 ≤ F.V7 := sup_le (Subgroup.commutator_le.2 fun u hu v hv => by
      rw [commutatorElement_def]
      exact hA u hu v hv) hV₁V₇
    have hMN : M₁ ≤ Subgroup.normalizer ((⁅U₁, V⁆ ⊔ F.V1 : Subgroup G) : Set G) := fun m hm =>
      S125Fin.mem_normalizer_sup
        (fun x hx => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
          (mem_normalizer_commutator (hUn (hMG₁ hm)) (hMV hm)) x).mp hx))
        (fun x hx => Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hMG₁ hm) x).mp hx))
    rcases hirr17.2.2.2 _ le_sup_right hle hMN with h | h
    · refine absurd (fun u hu v hv => ?_) hB
      rw [← h]
      have h1 := Subgroup.commutator_mem_commutator hu hv
      rw [commutatorElement_def] at h1
      exact Subgroup.mem_sup_left h1
    · exact h
  have hVOn : V ≤ Subgroup.normalizer (OK : Set G) :=
    hVK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₁)
  apply le_antisymm
  · refine sup_le (Subgroup.commutator_le.2 fun u hu x hx => ?_) hV₁V₇
    have hx' : x ∈ ((V : Set G) * (OK : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V OK hVOn]
      exact hx
    obtain ⟨v, hv, o, ho, rfl⟩ := hx'
    have h1 := hA u hu v hv
    have h2 : u * o * u⁻¹ * o⁻¹ ∈ F.V1 := by
      have h := F.V1.inv_mem (hQU o (hOKO₁ ho) u hu)
      rwa [show (o * u * o⁻¹ * u⁻¹)⁻¹ = u * o * u⁻¹ * o⁻¹ by group] at h
    have h3 : v * (u * o * u⁻¹ * o⁻¹) * v⁻¹ ∈ F.V1 :=
      (Subgroup.mem_normalizer_iff.mp (hKG (hVK hv)) _).mp h2
    rw [show ⁅u, v * o⁆ = (u * v * u⁻¹ * v⁻¹) * (v * (u * o * u⁻¹ * o⁻¹) * v⁻¹) by
      rw [commutatorElement_def]
      group]
    exact F.V7.mul_mem h1 (hV₁V₇ h3)
  · rw [← hC7]
    exact sup_le_sup_right (Subgroup.commutator_mono le_rfl le_sup_left) _

theorem card_img_eq (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K₁ : Subgroup G} (hVK : V ≤ K₁) (hVOK : V ⊓ pCoreOf 2 K₁ = F.V7) :
    Nat.card (S125Cfg.img K₁ V) = 8 := by
  have hf := S125Ex.Facts125.of h1222 hH
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hπ
  set ρ : ↥V →* ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ := π.comp (Subgroup.inclusion hVK) with hρ
  have hrange : ρ.range = S125Cfg.img K₁ V := by
    rw [hρ, MonoidHom.range_comp, Subgroup.inclusion_range, S125Cfg.img]
  have hkerc : Nat.card ρ.ker = Nat.card ↥(V ⊓ pCoreOf 2 K₁) := by
    refine Nat.card_congr
      ⟨fun x => ⟨(x : ↥V), ⟨(x : ↥V).2, ?_⟩⟩, fun y => ⟨⟨y, y.2.1⟩, ?_⟩, fun _ => rfl,
        fun _ => rfl⟩
    · have hx : π (Subgroup.inclusion hVK (x : ↥V)) = 1 := MonoidHom.mem_ker.1 x.2
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        ← A6.A6L74.mem_pCoreOf_iff] at hx
      exact hx
    · show π (Subgroup.inclusion hVK ⟨y, y.2.1⟩) = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← A6.A6L74.mem_pCoreOf_iff]
      exact y.2.2
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hrange, hkerc, hf.card, hVOK, S125Beta.card_V7] at hcard
  norm_num at hcard
  omega

omit [Finite G] in
theorem card_quot_V3 (F : Frame125 T L V) [(F.V1.subgroupOf F.V3).Normal] :
    Nat.card (↥F.V3 ⧸ F.V1.subgroupOf F.V3) ≤ 4 := by
  have hc8 : Nat.card F.V3 = 8 := by
    rw [← card_V3_filter, ← S125L9a.card_sub F {0, 1, 4}]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv.symm
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (F.V1.subgroupOf F.V3)
  have h1 : Nat.card (F.V1.subgroupOf F.V3) = 2 :=
    (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (S125L5a.sub_mono_le F (by decide))).toEquiv).trans
        (S125L9a.card_V1 F)
  rw [hc8, h1] at h
  omega

omit [Finite G] in
theorem range_comp_inclusion {K₁ : Subgroup G} (X : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)).comp
      (Subgroup.inclusion (Subgroup.map_subtype_le _ :
        (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))).map K₁.subtype ≤ K₁))).range = X := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨k, hk, hkc⟩ := c.2
    have hk' : Subgroup.inclusion (Subgroup.map_subtype_le _ :
        (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))).map K₁.subtype ≤ K₁) c = k :=
      Subtype.ext hkc.symm
    show QuotientGroup.mk' _ (Subgroup.inclusion _ c) ∈ X
    rw [hk']
    exact hk
  · intro hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₁) y
    exact ⟨⟨k, k, hy, rfl⟩, rfl⟩

theorem V_le_pCoreOf_of_j4 (hβ : KG125BetaJ4) (hJs : IsSimpleGroup NativeSporadic.J4)
    (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁) (hPK : oTwoUpper F.P ≤ K₁)
    (e : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* NativeSporadic.J4) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hf.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hf.T_le
  set OK := pCoreOf 2 K₁ with hOK
  set M₁ := mi T L F.V1 with hM₁
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hπ
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hVK : V ≤ K₁ := (S125L8.V_le_l1 h1222 F hH).trans hLK
  have hVM : V ≤ M₁ := hf.le_T.trans (le_inf le_sup_right (S125L2G.T_le_V F hTV).1)
  have hV₇V : F.V7 ≤ V := Subgroup.map_subtype_le _
  have hV₃V : F.V3 ≤ V := Subgroup.map_subtype_le _
  have hV₁V₃ : F.V1 ≤ F.V3 := S125L5a.sub_mono_le F (by decide)
  have hV₃V₇ : F.V3 ≤ F.V7 := S125L5a.sub_mono_le F (by decide)
  have hMV : M₁ ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans (sup_le hLV hTV)
  have hMG₁ : M₁ ≤ Subgroup.normalizer (F.V1 : Set G) := inf_le_right
  have hG₁O : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (OK : Set G) :=
    hK₁n.trans (S125Fin.normalizer_le_normalizer_pCoreOf K₁)
  have hVOn : V ≤ Subgroup.normalizer (OK : Set G) :=
    hVK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₁)
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hf.comm
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : V) ⟨y, hy⟩)
  by_contra hV
  obtain ⟨hVOK, hC7'⟩ := comm_sup_eq hJs h1222 F hH hK hK₁n hLK e hV
  set E := S125Cfg.img K₁ V with hE
  set N := S125Cfg.img K₁ M₁ with hN
  have hNE : N ≤ Subgroup.normalizer (E : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) := by
    rintro _ ⟨m, hm, rfl⟩
    apply S125St.mem_normalizer_of_conj_le
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨m * v * m⁻¹, ?_, by simp⟩
    show ((m : G) * v * (m : G)⁻¹) ∈ V
    exact (Subgroup.mem_normalizer_iff.mp (hMV hm) v).mp hv
  have hEO : E ≤ pCoreOf 2 N := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (S125Cfg.img_mono hVM) hNE
    (((IsPGroup.of_card (n := 10) hf.card).of_equiv
      (Subgroup.subgroupOfEquivOfLe hVK).symm).map π)
  obtain ⟨hβ1, hβ2⟩ := hβ _ ⟨e⟩ _ _ _ E (S125Cfg.isSylow_img h1222 F hH hK₁n hKG)
    (S125Cfg.config63 h1222 F hH hK₁n hKG hLK hPK) hEO hNE (card_img_eq h1222 F hH hVK hVOK)
  set Nt := K₁ ⊓ Subgroup.normalizer ((V ⊔ OK : Subgroup G) : Set G) with hNt
  have hNtK : Nt ≤ K₁ := inf_le_left
  have hiff : ∀ k : ↥K₁, π k ∈ Subgroup.normalizer (E : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ↔
      (k : G) ∈ Nt := fun k =>
    (mk_mem_normalizer_iff hVK hVOn k).trans ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have hNtV₇ : Nt ≤ Subgroup.normalizer (F.V7 : Set G) := by
    intro k hk
    rw [← hC7']
    exact S125Fin.mem_normalizer_sup
      (fun y hy => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator (le_normalizer_conjClosure _ _ (hKG (hNtK hk))) hk.2) y).mp hy))
      (fun y hy => Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hKG (hNtK hk)) y).mp hy))
  set Qt := pCoreOf 2 Nt with hQt
  have hQtNt : Qt ≤ Nt := CFSG.LieType.BorelTits.pCoreOf_le 2 Nt
  have hOKQt : OK ≤ Qt := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (fun o ho => ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 K₁ ho,
      Subgroup.le_normalizer (Subgroup.mem_sup_right ho)⟩)
    (fun k hk => hG₁O (hKG (hNtK hk))) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hMNt : M₁ ≤ Subgroup.normalizer (Nt : Set G) := by
    intro m hm
    have hmVO : m ∈ Subgroup.normalizer ((V ⊔ OK : Subgroup G) : Set G) :=
      S125Fin.mem_normalizer_sup
        (fun v hv => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hMV hm) v).mp hv))
        (fun o ho => Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hG₁O (hMG₁ hm)) o).mp ho))
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hK₁n (hMG₁ hm), Subgroup.le_normalizer hmVO⟩
  have hV₇OK : F.V7 ≤ OK := by
    rw [← hVOK]
    exact inf_le_right
  have hQtriv := comm_mem_of_irr (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Nt)
    (hQtNt.trans (hNtK.trans hKG)) (hV₇OK.trans hOKQt) (hQtNt.trans hNtV₇)
    (lemma12_5_2_of h1222 G T L V F hH).1.2.2.2.2.1
    (fun m hm => S125Fin.normalizer_le_normalizer_pCoreOf Nt (hMNt hm))
    (fun v hv => hKG (hVK (hV₇V hv)))
  set Cs := CFSG.inSubgroup CFSG.perfectResidual
    (Subgroup.centralizer (E : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))) with hCs
  set Ct : Subgroup G := (Cs.comap π).map K₁.subtype with hCt
  have hCtK : Ct ≤ K₁ := Subgroup.map_subtype_le _
  have hCsN : Cs ≤ Subgroup.normalizer (E : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :=
    (Subgroup.map_subtype_le _).trans (Subgroup.centralizer_le_normalizer _)
  have hCtNt : Ct ≤ Nt := by
    rintro _ ⟨k, hk, rfl⟩
    exact (hiff k).1 (hCsN hk)
  have hQEQt := mem_pCoreOf_of_mk_mem hNtK hiff
  have hL₁N : S125Cfg.img K₁ (li L F.V1) ≤ CFSG.inSubgroup CFSG.perfectResidual N := by
    refine CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual ?_
      (S125Cfg.img_mono ((Subgroup.map_subtype_le _).trans (inf_le_inf_right _ le_sup_left)))
    rw [S125Cfg.img, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective K₁.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLK,
      S125K6.commutator_li]
  have hCL : ∀ c ∈ Ct, ∀ l ∈ li L F.V1, c * l * c⁻¹ * l⁻¹ ∈ Qt := by
    rintro _ ⟨c, hc, rfl⟩ l hl
    have h1 : π (c * ⟨l, hLK hl⟩ * c⁻¹ * ⟨l, hLK hl⟩⁻¹) ∈
        pCoreOf 2 (Subgroup.normalizer (E : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def]
      exact hβ1 (Subgroup.commutator_mem_commutator hc (hL₁N ⟨⟨l, hLK hl⟩, hl, rfl⟩))
    simpa using hQEQt _ h1
  obtain ⟨-, hphi⟩ := S125Pm.phi_li_iff h1222 F hH (S125L8.autOn_l1 h1222 F hH)
  obtain ⟨l₁, hl₁, hφ₁⟩ :=
    hphi _ (S125Gen.tv_mem_pR (show (2 : Fin 5) ≠ 3 by decide) (by decide))
  obtain ⟨l₂, hl₂, hφ₂⟩ :=
    hphi _ (S125Gen.tv_mem_pR (show (3 : Fin 5) ≠ 4 by decide) (by decide))
  have hφ₁' : (S125Pm.phi F hLV hTV l₁ : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      1 + Matrix.single 2 3 1 := by
    rw [hφ₁]
    rfl
  have hφ₂' : (S125Pm.phi F hLV hTV l₂ : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      1 + Matrix.single 3 4 1 := by
    rw [hφ₂]
    rfl
  have hCtN3 : Ct ≤ Subgroup.normalizer (F.V3 : Set G) := fun c hc =>
    S125St.mem_normalizer_of_conj_le (conj_mem_V3 F hLV hTV hφ₁' hφ₂' hQtriv
      (hNtV₇ (hCtNt hc)) (hKG (hCtK hc)) (by simpa using hCL c⁻¹ (Ct.inv_mem hc) l₁ hl₁)
      (by simpa using hCL c⁻¹ (Ct.inv_mem hc) l₂ hl₂))
  have hCtN1 : Ct ≤ Subgroup.normalizer (F.V1 : Set G) := hCtK.trans hKG
  have : (F.V1.subgroupOf F.V3).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV₁V₃).2 fun x hx => hKG (hVK (hV₃V hx))
  have hRbot := secAct_eq_one_of_perfect hCtN3 hCtN1 (card_quot_V3 F)
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)).comp (Subgroup.inclusion hCtK))
    (by
      rw [range_comp_inclusion Cs]
      exact CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual _)
    (fun c hc => (secAct_eq_one_iff hCtN3 hCtN1 c).2 fun a ha => by
      have hcO : (c : G) ∈ OK := by
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          ← A6.A6L74.mem_pCoreOf_iff] at hc
        exact hc
      have h := F.V1.inv_mem (hQtriv c (hOKQt hcO) a (hV₃V₇ ha))
      have hca : (c : G) * a * (c : G)⁻¹ ∈ V :=
        hV₃V ((Subgroup.mem_normalizer_iff.mp (hCtN3 c.2) a).mp ha)
      have hcomm := hVab _ (hV₃V ha) _ hca
      have e : a⁻¹ * ((c : G) * a * (c : G)⁻¹) = (a * c * a⁻¹ * (c : G)⁻¹)⁻¹ := by
        calc a⁻¹ * ((c : G) * a * (c : G)⁻¹)
            = a⁻¹ * ((c : G) * a * (c : G)⁻¹ * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * ((c : G) * a * (c : G)⁻¹)) * a⁻¹ := by rw [← hcomm]
          _ = (a * c * a⁻¹ * (c : G)⁻¹)⁻¹ := by group
      rw [e]
      exact h)
  set b₁ := S125Beta.bvec F 1 with hb₁
  have hb₁V₃ : (b₁ : G) ∈ F.V3 := by
    show (b₁ : G) ∈ F.sub {0, 1, 4}
    rw [S125St.mem_sub_iff, hb₁, S125Beta.bvec, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    intro k hk
    exact Pi.single_eq_of_ne (by rintro rfl; simp at hk) _
  obtain ⟨y, a, hyP, hφy⟩ := exists_mem_oTwoUpper_P h1222 F hH hLV hTV
  have hyK : (y : G) ∈ K₁ := hPK hyP
  have hπy : π ⟨y, hyK⟩ ∈ oTwoUpper (S125Cfg.img K₁ F.P) := by
    rw [S125Cfg.oTwoUpper_img F hPK]
    exact ⟨⟨y, hyK⟩, hyP, rfl⟩
  have hπy' := hβ2 hπy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hCsN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))] at hπy'
  obtain ⟨cs, hcs, qs, hqs, hcq⟩ := hπy'
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₁) cs
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₁) qs
  have hcCt : (c : G) ∈ Ct := ⟨c, hcs, rfl⟩
  have ho : ((c * q)⁻¹ * ⟨y, hyK⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ := by
    have h1 : (QuotientGroup.mk (c * q) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁) =
        QuotientGroup.mk ⟨y, hyK⟩ := by
      rw [QuotientGroup.mk_mul]
      exact hcq
    exact QuotientGroup.eq.1 h1
  set r : G := (q : G) * (((c * q)⁻¹ * ⟨y, hyK⟩ : ↥K₁) : G) with hr
  have hrQt : r ∈ Qt :=
    Qt.mul_mem (hQEQt q hqs) (hOKQt ((A6.A6L74.mem_pCoreOf_iff _).2 ho))
  have hyeq : (y : G) = c * r := by
    rw [hr]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  apply not_comm_mem_V1 F hLV hTV hφy
  have h1 : r * b₁ * r⁻¹ * (b₁ : G)⁻¹ ∈ F.V1 := by
    have h := F.V1.inv_mem (hQtriv r hrQt _ (hV₃V₇ hb₁V₃))
    rwa [show ((b₁ : G) * r * (b₁ : G)⁻¹ * r⁻¹)⁻¹ = r * b₁ * r⁻¹ * (b₁ : G)⁻¹ by group] at h
  have h3 : (c : G) * (r * b₁ * r⁻¹ * (b₁ : G)⁻¹) * (c : G)⁻¹ ∈ F.V1 :=
    (Subgroup.mem_normalizer_iff.mp (hKG c.2) _).mp h1
  have h4 : (c : G) * b₁ * (c : G)⁻¹ * (b₁ : G)⁻¹ ∈ F.V1 := by
    have h5 := (secAct_eq_one_iff hCtN3 hCtN1 ⟨c, hcCt⟩).1 (hRbot ⟨c, hcCt⟩) _ hb₁V₃
    have hcb : (c : G) * b₁ * (c : G)⁻¹ ∈ V :=
      hV₃V ((Subgroup.mem_normalizer_iff.mp (hCtN3 hcCt) _).mp hb₁V₃)
    have hcomm := hVab _ (hV₃V hb₁V₃) _ hcb
    have e : (c : G) * b₁ * (c : G)⁻¹ * (b₁ : G)⁻¹ =
        (b₁ : G)⁻¹ * ((c : G) * b₁ * (c : G)⁻¹) := by
      calc (c : G) * b₁ * (c : G)⁻¹ * (b₁ : G)⁻¹
          = (b₁ : G)⁻¹ * ((b₁ : G) * ((c : G) * b₁ * (c : G)⁻¹)) * (b₁ : G)⁻¹ := by group
        _ = (b₁ : G)⁻¹ * (((c : G) * b₁ * (c : G)⁻¹) * b₁) * (b₁ : G)⁻¹ := by rw [hcomm]
        _ = (b₁ : G)⁻¹ * ((c : G) * b₁ * (c : G)⁻¹) := by group
    rw [e]
    exact h5
  rw [hyeq, show (c : G) * r * b₁ * ((c : G) * r)⁻¹ * (b₁ : G)⁻¹ =
    ((c : G) * (r * b₁ * r⁻¹ * (b₁ : G)⁻¹) * (c : G)⁻¹) *
      ((c : G) * b₁ * (c : G)⁻¹ * (b₁ : G)⁻¹) by group]
  exact F.V1.mul_mem h3 h4

end S125BetaJ4

end CFSG.Quasithin.H13
