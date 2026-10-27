module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.MPrime
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.InvariantSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar
public import CFSG.RankThree.GF2n.Tim81.Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Tim81
open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

@[expose] def UnitaryConclusionPin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G) (f : ℕ) (hf : 2 ≤ f) (m : ℕ)
    (hm : 4 ≤ m) (Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* G),
    Hyp M V →
    Nat.card V = 2 ^ f → Φ.range = Subgroup.normalClosure (V : Set G) →
    Φ.ker = Subgroup.center _ →
    (∀ U : Subgroup G, (∃ g : G, U = conjSubgroup g V) ↔
      ∃ x, U = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul (by omega : 1 ≤ f))
        m).rootGroup (unitaryLongRoot m (by omega))) x).map Φ) →
    Nat.card ↥(Pc M V) = Nat.card V ^ (2 * m - 3)

theorem maxAb_bar_Z0_comm {Z0 : Subgroup G}
    (hmax : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hE : Assembly.IsElemAbelian 2
      ((VbarPrime M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup (Hbar M Q Z))) :
    Maximal (fun W : Subgroup (Hbar M Q Z) =>
      W ≤ MbarPrime M Q Z Z0 ∧
      MbarPrime M Q Z Z0 ≤ Subgroup.normalizer (W : Set (Hbar M Q Z)) ∧
      IsMulCommutative W)
      ((VbarPrime M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup (Hbar M Q Z)) := by
  obtain ⟨hZ0K, -, -, hmaximal⟩ := hmax
  let K : Subgroup G := NormH0 M Z Z0
  let H : Subgroup G := H0 M Z
  have hKH : K ≤ H := NormH0_le_H0 M Z Z0
  have hHM : H ≤ M := inf_le_left
  have hKM : K ≤ M := hKH.trans hHM
  let ψ : ↥K →* Hbar M Q Z :=
    { toFun := fun k =>
        ⟨QuotientGroup.mk' (Q.subgroupOf M) (Subgroup.inclusion hKM k),
          Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKM k,
            Subgroup.mem_subgroupOf.mpr (hKH k.2), rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hrange : ψ.range = MbarPrime M Q Z Z0 := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKM k,
          Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
    · intro hx
      have hxK : (x : Mbar M Q) ∈ bar M Q K := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hxK
      refine ⟨⟨y, Subgroup.mem_subgroupOf.mp hyK⟩, ?_⟩
      ext
      change QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q)
      exact hyx
  have hker : ψ.ker = Q.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (ψ k : Mbar M Q) = 1 := by
        simpa using congrArg Subtype.val h
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (Subgroup.inclusion hKM k)).mp h1)
    · intro hk
      ext
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hKM k)).mpr hk
  have hVeq : (Z0.subgroupOf K).map ψ =
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKM z,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz), rfl⟩)
    · intro hx
      have hxZ : (x : Mbar M Q) ∈ bar M Q Z0 := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨y, hyZ, hyx⟩ := Subgroup.mem_map.mp hxZ
      have hyZ0 : (y : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hyZ
      refine ⟨⟨y, hZ0K hyZ0⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hyZ0
      · ext
        change QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q)
        exact hyx
  have hV'leM' : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      MbarPrime M Q Z Z0 := by
    rw [← hVeq]
    exact (Subgroup.map_le_range ψ (Z0.subgroupOf K)).trans_eq hrange
  have hM'NV : MbarPrime M Q Z Z0 ≤
      Subgroup.normalizer ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :
        Set (Hbar M Q Z)) := by
    intro m hm
    rw [← hrange] at hm
    obtain ⟨k, rfl⟩ := hm
    rw [← conjSubgroup_eq_self_iff]
    have hconjK : conjSubgroup k (Z0.subgroupOf K) = Z0.subgroupOf K := by
      have hkN : (k : G) ∈ Subgroup.normalizer (Z0 : Set G) := k.2.2
      have hkinv : (k : G)⁻¹ ∈ Subgroup.normalizer (Z0 : Set G) := Subgroup.inv_mem _ hkN
      ext z
      rw [mem_conjSubgroup]
      constructor
      · intro hz
        have hz' : (k : G)⁻¹ * (z : G) * (k : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hz
        exact Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp hkinv (z : G)).mpr (by simpa using hz'))
      · intro hz
        have hz' : (z : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hz
        have hz'' : (k : G)⁻¹ * (z : G) * (k : G)⁻¹⁻¹ ∈ Z0 :=
          (Subgroup.mem_normalizer_iff.mp hkinv (z : G)).mp (by simpa using hz')
        exact Subgroup.mem_subgroupOf.mpr (by simpa using hz'')
    rw [← hVeq, CFSG.GroupTheory.map_conjSubgroup, hconjK]
  refine ⟨⟨hV'leM', hM'NV, hE.1⟩, ?_⟩
  intro W hW hV'W
  obtain ⟨hWleM', hWN, hWE⟩ := hW
  let A : Subgroup ↥K := W.comap ψ
  have hWrange : W ≤ ψ.range := by rwa [hrange]
  have hA_map : A.map ψ = W := Subgroup.map_comap_eq_self hWrange
  have hZA : Z0.subgroupOf K ≤ A := by
    intro z hz
    have hzV : ψ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
      rw [← hVeq]
      exact ⟨z, hz, rfl⟩
    exact hV'W hzV
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, ((⁅x, y⁆ : ↥K) : G) ∈ Q := by
    intro x hx y hy
    have hψx : ψ x ∈ W := by
      rw [← hA_map]
      exact Subgroup.mem_map_of_mem ψ hx
    have hψy : ψ y ∈ W := by
      rw [← hA_map]
      exact Subgroup.mem_map_of_mem ψ hy
    have hcent : W ≤ Subgroup.centralizer (W : Set (Hbar M Q Z)) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hWE
    have hcomm : ⁅ψ x, ψ y⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp (hcent hψx)) (ψ y) hψy
    have h2 : ψ ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, hcomm]
    have h3 : ⁅x, y⁆ ∈ ψ.ker := MonoidHom.mem_ker.mpr h2
    rw [hker] at h3
    exact Subgroup.mem_subgroupOf.mp h3
  have hAk : ∀ k ∈ K, conjSubgroup k (A.map K.subtype) = A.map K.subtype := by
    intro k hk
    have hψk : ψ ⟨k, hk⟩ ∈ MbarPrime M Q Z Z0 := by
      rw [← hrange]
      exact ⟨⟨k, hk⟩, rfl⟩
    have hNW : conjSubgroup (ψ ⟨k, hk⟩) W = W :=
      conjSubgroup_eq_self_iff.mpr (hWN hψk)
    have hconjA : conjSubgroup (⟨k, hk⟩ : ↥K) A = A := by
      ext x
      rw [mem_conjSubgroup]
      constructor
      · intro hx
        have h2 : (ψ ⟨k, hk⟩)⁻¹ * ψ x * ψ ⟨k, hk⟩ ∈ W := by
          simpa [A, Subgroup.mem_comap] using hx
        have h3 : ψ x ∈ conjSubgroup (ψ ⟨k, hk⟩) W :=
          (mem_conjSubgroup).mpr h2
        rwa [hNW] at h3
      · intro hx
        have h3 : ψ x ∈ conjSubgroup (ψ ⟨k, hk⟩) W := by rwa [hNW]
        have h2 : (ψ ⟨k, hk⟩)⁻¹ * ψ x * ψ ⟨k, hk⟩ ∈ W :=
          (mem_conjSubgroup).mp h3
        show ψ ((⟨k, hk⟩ : ↥K)⁻¹ * x * ⟨k, hk⟩) ∈ W
        simpa using h2
    have hmap := CFSG.GroupTheory.map_conjSubgroup (f := K.subtype) A (⟨k, hk⟩ : ↥K)
    simpa [hconjA] using hmap
  have hZ0AG : Z0 ≤ A.map K.subtype := by
    intro z hz
    exact Subgroup.mem_map.mpr
      ⟨⟨z, hZ0K hz⟩, hZA (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hAGleK : A.map K.subtype ≤ K := Subgroup.map_subtype_le A
  have hAGcomm : ∀ x ∈ A.map K.subtype, ∀ y ∈ A.map K.subtype, ⁅x, y⁆ ∈ Q := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have h := hAcomm x' hx' y' hy'
    rw [← map_commutatorElement]
    exact h
  have hAGeq : A.map K.subtype = Z0 := hmaximal (A.map K.subtype) hZ0AG hAGleK hAk hAGcomm
  intro w hw
  have hwW : w ∈ A.map ψ := by rwa [hA_map]
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hwW
  have haG : (a : G) ∈ Z0 := by
    have hmem : (a : G) ∈ A.map K.subtype := ⟨a, ha, rfl⟩
    rwa [hAGeq] at hmem
  rw [← hVeq]
  exact ⟨a, Subgroup.mem_subgroupOf.mpr haG, rfl⟩

theorem generalizedFitting_MbarPrime_eq_of_fitting {Z0 : Subgroup G} {N : Subgroup G}
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q N).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    generalizedFitting (MbarPrime M Q Z Z0) =
      ((bar M Q N).subgroupOf (bar M Q (H0 M Z))).subgroupOf (MbarPrime M Q Z Z0) := by
  have hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) := MbarPrimeLe M Q Z Z0
  let e : ↥(MbarPrime M Q Z Z0) ≃* ↥(bar M Q (NormH0 M Z Z0)) :=
    Subgroup.subgroupOfEquivOfLe hKH
  have hmapF : (generalizedFitting (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) :=
    CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  have hmapS : (((bar M Q N).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      (bar M Q N).subgroupOf (bar M Q (NormH0 M Z Z0)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨⟨y.1, hKH y.2⟩, y.2⟩, hy, rfl⟩
  exact Subgroup.map_injective e.injective (hmapF.trans (hF.trans hmapS.symm))

theorem isMaximalTwoLocal_of_isMaxTwoLocalSubgroup {M : Subgroup G}
    (h : CFSG.Open.IsMaxTwoLocalSubgroup M) : IsMaximalTwoLocal M :=
  ⟨h.1, fun H hMH hH => hMH.ne (h.2 H hH hMH.le).symm⟩

theorem exists_isHMember_of_fitting (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (h34 : Stroth34Statement) (h712 : Stroth712Statement)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNL : ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0) :
    ∃ H : Subgroup (Hbar M Q Z),
      IsHMember (MbarPrime M Q Z Z0)
        ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) H := by
  have h5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).2.1
  let Hw : Subgroup (Hbar M Q Z) :=
    (bar M Q (NormH0L M Z (LB M Q B))).subgroupOf (bar M Q (H0 M Z))
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  have hCNH0 : hc.CN t ≤ H0 M Z := fun y hy => hc.Rt_le_H0 t (Ctx.mem_CN.mp hy).1
  have hCNN : hc.CN t ≤ Subgroup.normalizer (LB M Q B : Set G) := by
    intro y hy
    have h := hc.CN_normalizes_conj_LB h35 hs.toSec5.mem (h := 1) (Subgroup.one_mem _) hy
    rwa [conjSubgroup_one_sec4] at h
  have hCNL : bar M Q (hc.CN t) ≤ bar M Q (NormH0L M Z (LB M Q B)) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M (fun y hy =>
      Subgroup.mem_inf.mpr ⟨hCNH0 hy, hCNN hy⟩))
  have hPc : Pc (MbarPrime M Q Z Z0) V ≤ Hw := by
    refine (inf_le_left.trans ?_)
    have hpc : pCore 2 (MbarPrime M Q Z Z0) =
        ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
          (MbarPrime M Q Z Z0) := by
      rw [← generalizedFitting_MbarPrime hc hs hZ0 h712]
      exact generalizedFitting_MbarPrime_eq_of_fitting hF
    change (pCore 2 (MbarPrime M Q Z Z0)).map (MbarPrime M Q Z Z0).subtype ≤ Hw
    rw [hpc, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left.trans (Subgroup.subgroupOf_mono _ hCNL)
  have hO2 : inSubgroup (pCore 2) Hw ≠ ⊥ := by
    let L : Subgroup (Hbar M Q Z) :=
      (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z))
    have hLH : L ≤ Hw := by
      apply Subgroup.subgroupOf_mono
      exact Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
        (Subgroup.subgroupOf_mono M (fun y hy => Subgroup.mem_inf.mpr
          ⟨hc.LB_le_H0 hy, Subgroup.le_normalizer hy⟩))
    have hLHbar : bar M Q (LB M Q B) ≤ bar M Q (H0 M Z) :=
      Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
        (Subgroup.subgroupOf_mono M (fun y hy => hc.LB_le_H0 hy))
    have hLnormH : Hw ≤ Subgroup.normalizer (L : Set (Hbar M Q Z)) := by
      have hN := bar_le_normalizer_of_le_normalizer (le_sup_left : Q ≤ LB M Q B)
        hc.LB_le_M
        (fun y hy => (show y ∈ H0 M Z ⊓ Subgroup.normalizer (LB M Q B : Set G)
          from hy).1.1)
        (fun y hy => (show y ∈ H0 M Z ⊓ Subgroup.normalizer (LB M Q B : Set G)
          from hy).2)
      intro x hx
      have hxbar : (x : Mbar M Q) ∈ bar M Q (NormH0L M Z (LB M Q B)) :=
        Subgroup.mem_subgroupOf.mp hx
      rw [← Subgroup.subgroupOf_normalizer_eq hLHbar]
      exact Subgroup.mem_subgroupOf.mpr (hN hxbar)
    have hLnormal : (L.subgroupOf Hw).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hLnormH
    have hLp : IsPGroup 2 (L.subgroupOf Hw) := by
      have hE : Assembly.IsElemAbelian 2 (bar M Q (LB M Q B)) := hc.isElemAbelian_bar_LB
      have hP : IsPGroup 2 (bar M Q (LB M Q B)) := CFSG.Open.IsElemAbelian.isPGroup hE
      have hPL : IsPGroup 2 L :=
        hP.of_equiv (Subgroup.subgroupOfEquivOfLe hLHbar).symm
      exact hPL.of_equiv (Subgroup.subgroupOfEquivOfLe hLH).symm
    have hLne_sub : L.subgroupOf Hw ≠ ⊥ := by
      intro hbot
      have hLbot : L = ⊥ := by
        have := congrArg (Subgroup.map Hw.subtype) hbot
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLH,
          Subgroup.map_bot] at this
      have hcard : 4 ≤ Nat.card L := by
        have hbar := hc.four_le_card_bar_LB h34 h5.width h5.n_gt h5.noA2 h5.gen
        rw [show Nat.card L = Nat.card (bar M Q (LB M Q B)) by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLHbar).toEquiv]
        exact hbar
      rw [hLbot, Subgroup.card_bot] at hcard
      omega
    have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (p := 2)
      hLnormal hLp
    intro hbot
    have hLbot : L.subgroupOf Hw = ⊥ := by
      have hbot' : Subgroup.map Hw.subtype (pCore 2 ↥Hw) = ⊥ := hbot
      have hmap := Subgroup.map_mono (f := Hw.subtype) hle
      rw [hbot'] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective (L.subgroupOf Hw)
        (f := Hw.subtype) Hw.subtype_injective).mp (le_bot_iff.mp hmap)
    exact hLne_sub hLbot
  have hnotle : ¬ Hw ≤ MbarPrime M Q Z Z0 := by
    intro hle
    apply hNL
    intro x hx
    obtain ⟨hxH0, hxNL⟩ := hx
    have hxM : x ∈ M := hxH0.1
    let xM : M := ⟨x, hxM⟩
    let xH : Hbar M Q Z := ⟨QuotientGroup.mk' (Q.subgroupOf M) xM,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxH0)⟩
    have hxHw : xH ∈ Hw := Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hxH0, hxNL⟩))
    have hxM' : xH ∈ MbarPrime M Q Z Z0 := hle hxHw
    have hxbarNorm : (xH : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) :=
      Subgroup.mem_subgroupOf.mp hxM'
    have hQZ0 : Q ≤ Z0 := by
      have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q :=
        fun r hr y hy => (Subgroup.mem_normalizer_iff.mp
          (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
      exact IsCentrePre.Q_le hZ0 (hc.Q_le_Rt hs.toSec5.mem) hnormR
    have hQH : Q ≤ H0 M Z := fun q hq =>
      Subgroup.mem_inf.mpr ⟨hc.hyp.Q_normal.1 hq,
        Subgroup.mem_centralizer_iff.mpr fun z hz => by
          rw [hc.hyp.hZ, cen_eq] at hz
          exact (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm⟩
    have hQN : Q ≤ NormH0 M Z Z0 := fun q hq =>
      Subgroup.mem_inf.mpr ⟨hQH hq, Z0.le_normalizer (hQZ0 hq)⟩
    exact (mk_mem_bar_iff_sec4 hQN xM).mp hxbarNorm
  exact ⟨Hw, hO2, hPc, hnotle⟩

end CFSG.RankThree.GF2n.Stroth80
