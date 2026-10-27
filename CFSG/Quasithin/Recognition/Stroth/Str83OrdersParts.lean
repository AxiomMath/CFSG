module

public import CFSG.Quasithin.Recognition.Stroth.Str83Props
public import CFSG.Quasithin.Recognition.Stroth.BenderSylow
public import CFSG.Quasithin.Recognition.Stroth.BenderBorel
public import CFSG.GH74.Uniqueness.SU.KI8Basic
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Recognition.Stroth.WeissStrothLeaves

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

private noncomputable def actionOnQuot (Li S : Subgroup G)
    (hS : S ≤ Subgroup.normalizer (Li : Set G)) :
    ↥(Li ⊔ S) →* MulAut (oTwoQuot ↥Li) :=
  (oTwoQuotConj Li).comp (Subgroup.inclusion (sup_le Subgroup.le_normalizer hS))

private theorem oTwoQuotConj_of_mem {L : Subgroup G} (x : ↥L) :
    oTwoQuotConj L ⟨(x : G), Subgroup.le_normalizer x.2⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [oTwoQuotConj_mk, MulAut.conj_apply]
    change (QuotientGroup.mk (⟨(x : G) * (y : G) * (x : G)⁻¹, _⟩ : ↥L) : oTwoQuot ↥L) =
      (QuotientGroup.mk x : oTwoQuot ↥L) * (QuotientGroup.mk y : oTwoQuot ↥L) *
        ((QuotientGroup.mk x : oTwoQuot ↥L))⁻¹
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1

private theorem isSylowTwoOf_sup_of_hyp111At {Li Lj S : Subgroup G} (h : Hyp111At Li Lj S) :
    IsSylowTwoOf S (Li ⊔ S) := by
  refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex le_sup_right h.pgroup ?_
  rw [CFSG.Quasithin.F112W.relIndex_sup_eq_relIndex_inf (N := Li) (B := S) h.normalizes]
  have h1 := h.sylow.2.2
  rw [inf_comm] at h1
  rwa [show ((Li ⊓ S).subgroupOf Li).index = (Li ⊓ S).relIndex Li from by
    simpa [Subgroup.subgroupOf_self] using
      Subgroup.relIndex_subgroupOf (H := Li ⊓ S) (K := Li) (L := Li) le_rfl] at h1

private theorem ker_action_inf_eq {Li Lj S : Subgroup G} (h : Hyp111At Li Lj S)
    (hZ : Subgroup.center (oTwoQuot ↥Li) = ⊥) :
    (actionOnQuot Li S h.normalizes).ker ⊓ Li.subgroupOf (Li ⊔ S) =
      (pCoreOf 2 Li).subgroupOf (Li ⊔ S) := by
  classical
  let P : Subgroup G := Li ⊔ S
  let σ := actionOnQuot Li S h.normalizes
  have hLiP : Li ≤ P := le_sup_left
  have hPN : P ≤ Subgroup.normalizer (Li : Set G) :=
    sup_le Subgroup.le_normalizer h.normalizes
  ext y
  constructor
  · rintro ⟨hyK, hyH⟩
    have hyl : (y : G) ∈ Li := Subgroup.mem_subgroupOf.mp hyH
    have hσy : σ y = MulAut.conj
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hyl⟩) := by
      change oTwoQuotConj Li ⟨(y : G), hPN y.2⟩ = _
      exact oTwoQuotConj_of_mem ⟨(y : G), hyl⟩
    have hσ1 : σ y = 1 := MonoidHom.mem_ker.mp hyK
    rw [hσy] at hσ1
    have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hyl⟩ ∈
        Subgroup.center (oTwoQuot ↥Li) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut (oTwoQuot ↥Li) => f g) hσ1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hyl⟩
          = (QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hyl⟩ * g *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hyl⟩)⁻¹) *
              QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hyl⟩ := by rw [h]
        _ = QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hyl⟩ * g := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    have hyQ : (⟨(y : G), hyl⟩ : ↥Li) ∈ CFSG.pCore 2 ↥Li :=
      (QuotientGroup.eq_one_iff (x := (⟨(y : G), hyl⟩ : ↥Li))).mp hcen
    exact Subgroup.mem_subgroupOf.mpr ((CFSG.Quasithin.F1.mem_pCore_iff_coe _).mp hyQ)
  · intro hy
    have hyl : (y : G) ∈ pCoreOf 2 Li := Subgroup.mem_subgroupOf.mp hy
    have hylL : (y : G) ∈ Li := (CFSG.LieType.BorelTits.pCoreOf_le 2 Li) hyl
    refine ⟨?_, Subgroup.mem_subgroupOf.mpr hylL⟩
    change σ y = 1
    have hσy : σ y = MulAut.conj
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hylL⟩) := by
      change oTwoQuotConj Li ⟨(y : G), hPN y.2⟩ = _
      exact oTwoQuotConj_of_mem ⟨(y : G), hylL⟩
    rw [hσy]
    have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥Li) ⟨(y : G), hylL⟩ = 1 :=
      (QuotientGroup.eq_one_iff
        (x := (⟨(y : G), hylL⟩ : ↥Li))).mpr
        ((CFSG.Quasithin.F1.mem_pCore_iff_coe _).mpr hyl)
    rw [hq, map_one]

private theorem ker_action_le_pCoreOf {Li Lj S : Subgroup G} (h : Hyp111At Li Lj S)
    (hZ : Subgroup.center (oTwoQuot ↥Li) = ⊥) :
    (actionOnQuot Li S h.normalizes).ker ≤ pCoreOf 2 (⊤ : Subgroup ↥(Li ⊔ S)) := by
  classical
  let P : Subgroup G := Li ⊔ S
  let σ := actionOnQuot Li S h.normalizes
  let H : Subgroup ↥P := Li.subgroupOf P
  have hLiP : Li ≤ P := le_sup_left
  have hPN : P ≤ Subgroup.normalizer (Li : Set G) :=
    sup_le Subgroup.le_normalizer h.normalizes
  have hHN : H.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLiP).mpr hPN
  have hHidx : ∃ n, H.index = 2 ^ n := by
    have h1 : H.index = Li.relIndex P := by
      rw [show H.index = (Li.subgroupOf P).relIndex (P.subgroupOf P) from by
        rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right]]
      exact Subgroup.relIndex_subgroupOf (H := Li) (K := P) (L := P) le_rfl
    have h2 : Li.relIndex P = (Li ⊓ S).relIndex S := by
      rw [show P = S ⊔ Li from by rw [show P = Li ⊔ S from rfl, sup_comm]]
      rw [CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer (D := Li) (T := S) h.normalizes]
      exact (Subgroup.inf_relIndex_right Li S).symm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := h.pgroup.index ((Li ⊓ S).subgroupOf S)
    refine ⟨n, ?_⟩
    rw [h1, h2, ← hn]
    simpa [Subgroup.subgroupOf_self] using
      (Subgroup.relIndex_subgroupOf (H := Li ⊓ S) (K := S) (L := S) le_rfl).symm
  have hKH : σ.ker ⊓ H = (pCoreOf 2 Li).subgroupOf P := by
    simpa [σ, H] using ker_action_inf_eq h hZ
  have hQ2 : IsPGroup 2 ((pCoreOf 2 Li).subgroupOf P) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Li).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Li).trans hLiP)).symm
  have hK2 : IsPGroup 2 ↥(σ.ker) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨m, hm⟩ := hHidx
    have hxpowH : (x : ↥P) ^ H.index ∈ H := Subgroup.pow_index_mem H (x : ↥P)
    have hxpowK : (x : ↥P) ^ H.index ∈ σ.ker := σ.ker.pow_mem x.2 H.index
    have hxmem : (x : ↥P) ^ H.index ∈ (pCoreOf 2 Li).subgroupOf P := by
      rw [← hKH]
      exact ⟨hxpowK, hxpowH⟩
    obtain ⟨n, hn⟩ := hQ2 ⟨(x : ↥P) ^ H.index, hxmem⟩
    refine ⟨m + n, ?_⟩
    apply Subtype.ext
    show (x : ↥P) ^ 2 ^ (m + n) = 1
    have hn' : ((x : ↥P) ^ H.index) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    rw [show (2 : ℕ) ^ (m + n) = H.index * 2 ^ n by rw [pow_add, ← hm]]
    simpa [pow_mul] using hn'
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 (N := σ.ker) (H := ⊤) le_top
    (by
      haveI : σ.ker.Normal := MonoidHom.normal_ker σ
      exact Subgroup.normal_comap (f := (⊤ : Subgroup ↥P).subtype)) hK2

private theorem exists_mem_inf_of_mem {Li Lj S : Subgroup G} (h : Hyp111At Li Lj S)
    (hZ : Subgroup.center (oTwoQuot ↥Li) = ⊥)
    (hodd : Odd (MulAut.conj : oTwoQuot ↥Li →* MulAut (oTwoQuot ↥Li)).range.index)
    {s : G} (hs : s ∈ S) :
    ∃ l : ↥Li, (l : G) ∈ S ∧
      (actionOnQuot Li S h.normalizes) ⟨s, (le_sup_right : S ≤ Li ⊔ S) hs⟩ =
        (actionOnQuot Li S h.normalizes) ⟨(l : G), (le_sup_left : Li ≤ Li ⊔ S) l.2⟩ := by
  classical
  let P : Subgroup G := Li ⊔ S
  let σ := actionOnQuot Li S h.normalizes
  have hSP : S ≤ P := le_sup_right
  have hLiP : Li ≤ P := le_sup_left
  have hSylP : IsSylowTwoOf S P := isSylowTwoOf_sup_of_hyp111At h
  obtain ⟨k, hk⟩ := h.pgroup ⟨s, hs⟩
  let α : MulAut (oTwoQuot ↥Li) := σ ⟨s, hSP hs⟩
  have hkP : (⟨s, hSP hs⟩ : ↥P) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hαpow : α ^ 2 ^ k = 1 := by
    simp only [α]
    rw [← map_pow, hkP, map_one]
  have hαmem : α ∈ (MulAut.conj : oTwoQuot ↥Li →* MulAut (oTwoQuot ↥Li)).range := by
    haveI : (MulAut.conj : oTwoQuot ↥Li →* MulAut (oTwoQuot ↥Li)).range.Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (oTwoQuot ↥Li)
    have hP2 : IsPGroup 2 (Subgroup.zpowers α) := by
      rw [isPGroup_iff_exists_orderOf_dvd_pow]
      refine ⟨k, fun g => ?_⟩
      simpa [Subgroup.orderOf_coe] using
        (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one hαpow)
    exact Subgroup.zpowers_le.mp
      (CFSG.GH74.Uniqueness.SU.K.KI8.le_of_isPGroup_of_odd_index hodd hP2)
  obtain ⟨l, hl⟩ := hαmem
  obtain ⟨l', hl'⟩ := QuotientGroup.mk_surjective (s := CFSG.pCore 2 ↥Li) l
  have hσl : σ ⟨l', hLiP l'.2⟩ = α := by
    rw [show σ ⟨l', hLiP l'.2⟩ =
        MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Li) l') from
      oTwoQuotConj_of_mem l']
    rw [← hl]
    exact congrArg MulAut.conj hl'
  have hxker : σ ⟨s * (l' : G)⁻¹, P.mul_mem (hSP hs) (P.inv_mem (hLiP l'.2))⟩ = 1 := by
    have h1 : (⟨s * (l' : G)⁻¹, P.mul_mem (hSP hs) (P.inv_mem (hLiP l'.2))⟩ : ↥P) =
        ⟨s, hSP hs⟩ * (⟨l', hLiP l'.2⟩)⁻¹ := by
      apply Subtype.ext
      rfl
    rw [h1, map_mul, map_inv, hσl]
    rw [show σ ⟨s, hSP hs⟩ = α from rfl, mul_inv_cancel]
  have hxO : s * (l' : G)⁻¹ ∈ pCoreOf 2 P := by
    have hx : (⟨s * (l' : G)⁻¹, P.mul_mem (hSP hs) (P.inv_mem (hLiP l'.2))⟩ : ↥P) ∈
        σ.ker := MonoidHom.mem_ker.mpr hxker
    have hle := ker_action_le_pCoreOf h hZ hx
    have hpc : pCoreOf 2 (⊤ : Subgroup ↥P) = CFSG.pCore 2 ↥P :=
      CFSG.Quasithin.pCoreOf_top 2
    rw [hpc] at hle
    change s * (l' : G)⁻¹ ∈ (CFSG.pCore 2 ↥P).map P.subtype
    exact Subgroup.mem_map.mpr ⟨_, hle, rfl⟩
  have hl'S : (l' : G) ∈ S := by
    have hxOS : s * (l' : G)⁻¹ ∈ S :=
      CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hSylP hxO
    have h1 : (s * (l' : G)⁻¹)⁻¹ ∈ S := S.inv_mem hxOS
    have h2 : (s * (l' : G)⁻¹)⁻¹ * s ∈ S := S.mul_mem h1 hs
    convert h2 using 1
    group
  exact ⟨l', hl'S, hσl.symm⟩

theorem borelOf_le_normalizer_of_odd_outer {Li Lj S : Subgroup G}
    (h : Hyp111At Li Lj S) (hZ : Subgroup.center (oTwoQuot ↥Li) = ⊥)
    (hodd : Odd (MulAut.conj : oTwoQuot ↥Li →* MulAut (oTwoQuot ↥Li)).range.index) :
    borelOf Li S ≤ Subgroup.normalizer (S : Set G) := by
  have hSylP : IsSylowTwoOf S (Li ⊔ S) := isSylowTwoOf_sup_of_hyp111At h
  have hEq : S = pCoreOf 2 (Li ⊔ S) ⊔ (S ⊓ Li) := by
    refine le_antisymm ?_ (sup_le (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hSylP)
      inf_le_left)
    intro s hs
    obtain ⟨l, hlS, hsl⟩ := exists_mem_inf_of_mem h hZ hodd hs
    let P : Subgroup G := Li ⊔ S
    have hSP : S ≤ P := le_sup_right
    have hLiP : Li ≤ P := le_sup_left
    let σ := actionOnQuot Li S h.normalizes
    have hxker : σ ⟨s * (l : G)⁻¹, P.mul_mem (hSP hs)
        (P.inv_mem (hLiP l.2))⟩ = 1 := by
      have h1 : (⟨s * (l : G)⁻¹, P.mul_mem (hSP hs)
          (P.inv_mem (hLiP l.2))⟩ : ↥P) =
          ⟨s, hSP hs⟩ * (⟨l, hLiP l.2⟩)⁻¹ := by
        apply Subtype.ext
        rfl
      rw [h1, map_mul, map_inv, hsl]
      rw [mul_inv_cancel]
    have hxO : s * (l : G)⁻¹ ∈ pCoreOf 2 (Li ⊔ S) := by
      have hx : (⟨s * (l : G)⁻¹, P.mul_mem (hSP hs)
          (P.inv_mem (hLiP l.2))⟩ : ↥P) ∈ σ.ker := MonoidHom.mem_ker.mpr hxker
      have hle := ker_action_le_pCoreOf h hZ hx
      have hpc : pCoreOf 2 (⊤ : Subgroup ↥P) = CFSG.pCore 2 ↥P :=
        CFSG.Quasithin.pCoreOf_top 2
      rw [hpc] at hle
      change s * (l : G)⁻¹ ∈ (CFSG.pCore 2 ↥P).map P.subtype
      exact Subgroup.mem_map.mpr ⟨_, hle, rfl⟩
    have hmem : (s * (l : G)⁻¹) * (l : G) ∈ pCoreOf 2 P ⊔ (S ⊓ Li) :=
      Subgroup.mul_mem_sup hxO (Subgroup.mem_inf.mpr ⟨hlS, l.2⟩)
    convert hmem using 1
    rw [mul_assoc, inv_mul_cancel, mul_one]
  exact CFSG.Quasithin.F1.borelOf_le_normalizer_of_eq hEq

theorem str83_bigB_le_normalizer {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)) :
    bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨e1⟩ := hSz
  obtain ⟨e2⟩ := hL2
  have hB1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha
      (e1.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hB2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) e2
  have hodd1 : Odd (MulAut.conj : oTwoQuot ↥L1 →* MulAut (oTwoQuot ↥L1)).range.index :=
    BenderType.lemma_3_1_b_suzuki hB1
  have hodd2 : Odd (MulAut.conj : oTwoQuot ↥L2 →* MulAut (oTwoQuot ↥L2)).range.index := by
    obtain ⟨-, hcard⟩ := BenderType.outer_linear hB2
    have hidx : (MulAut.conj : oTwoQuot ↥L2 →* MulAut (oTwoQuot ↥L2)).range.index =
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (oTwoQuot ↥L2)) :=
      Subgroup.index_eq_card
        (H := (MulAut.conj : oTwoQuot ↥L2 →* MulAut (oTwoQuot ↥L2)).range)
    rw [hidx, hcard]
    exact ⟨a, rfl⟩
  have h1 : borelOf L1 S ≤ Subgroup.normalizer (S : Set G) :=
    borelOf_le_normalizer_of_odd_outer hF.h1 (BenderType.center_eq_bot hB1) hodd1
  have h2 : borelOf L2 S ≤ Subgroup.normalizer (S : Set G) :=
    borelOf_le_normalizer_of_odd_outer hF.h2 (BenderType.center_eq_bot hB2) hodd2
  exact sup_le (sup_le h1 h2) Subgroup.le_normalizer

theorem str83_eq_sup_pCoreOf {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)) :
    S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ∧
      S = (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  have hB := str83_bigB_le_normalizer hF ha hSz hL2
  constructor
  · exact eq_sup_pCoreOf_of_bender_left hF hB (Or.inl ⟨a, ha, hSz⟩)
  · exact eq_sup_pCoreOf_of_bender_right hF hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))

private theorem inf_pCoreOf_vertex_left {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    L1 ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  set P : Subgroup G := L1 ⊔ bigB L1 L2 S with hP
  set Q : Subgroup G := pCoreOf 2 P with hQ
  have hL1P : L1 ≤ P := le_sup_left
  have hL1N : L1 ≤ Subgroup.normalizer (Q : Set G) :=
    hL1P.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (F1.parabolic_le_normalizer hR).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1)
  have hQle : pCoreOf 2 L1 ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans hL1P) hPN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L1)
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L1) hQle)
  have hN : ((L1 ⊓ Q).subgroupOf L1).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro x hx
    exact CFSG.ABGLocalTools.mem_normalizer_inf (Subgroup.le_normalizer hx) (hL1N hx)
  have hQ2 : IsPGroup 2 ↥(L1 ⊓ Q) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).to_le
      (inf_le_right : L1 ⊓ Q ≤ Q)
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hN hQ2

private theorem inf_pCoreOf_vertex_right {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    L2 ⊓ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 := by
  have h := inf_pCoreOf_vertex_left (L1 := L2) (L2 := L1) (S := S) hF.symm
  rwa [bigB_comm] at h

private theorem relIndex_pCoreOf_vertex_left {L1 L2 S : Subgroup G}
    {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hE : S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) :
    (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex S = (2 ^ (2 * a + 1)) ^ 2 := by
  obtain ⟨e⟩ := hSz
  let Q := pCoreOf 2 (L1 ⊔ bigB L1 L2 S)
  let S1 := S ⊓ L1
  have hS1P : S1 ≤ L1 ⊔ bigB L1 L2 S :=
    (inf_le_right : S ⊓ L1 ≤ L1).trans le_sup_left
  have hS1N : S1 ≤ Subgroup.normalizer (Q : Set G) :=
    hS1P.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
  have hrel : Q.relIndex S = Q.relIndex S1 := by
    rw [hE]
    exact CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hS1N
  rw [hrel, ← Subgroup.inf_relIndex_right Q S1]
  have hinf : Q ⊓ S1 = pCoreOf 2 L1 := by
    rw [show Q ⊓ S1 = (Q ⊓ L1) ⊓ S1 from by
      simp [S1, inf_assoc, inf_left_comm, inf_comm]]
    have hQL : Q ⊓ L1 = pCoreOf 2 L1 := by
      rw [inf_comm]
      exact inf_pCoreOf_vertex_left hF
    rw [hQL]
    exact inf_eq_left.mpr (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow)
  rw [hinf]
  exact relIndex_pCoreOf_sylow_sz ha e hF.1.h1.sylow

private theorem relIndex_pCoreOf_sylow_l2
    {L T : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (e : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    (pCoreOf 2 L).relIndex T = 2 ^ f := by
  classical
  obtain ⟨e⟩ := e
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (CFSG.pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  have hmap1 : (pCoreOf 2 L).relIndex T = (CFSG.pCore 2 K1).relIndex T1 := by
    rw [CFSG.Open.pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hT.1]
    exact Subgroup.relIndex_map_map_of_injective (f := L.subtype) (CFSG.pCore 2 K1) T1
      L.subtype_injective
  have hmap2 : (CFSG.pCore 2 K1).relIndex T1 = Nat.card (T1.map π) := by
    have h := Subgroup.relIndex_ker (K := T1) π
    rwa [QuotientGroup.ker_mk'] at h
  have hT1syl : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm, ?_⟩
    rw [show (T1.subgroupOf ⊤).index = T1.index from by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]]
    exact hT.2.2
  have hcard : Nat.card (T1.map π) = 2 ^ f := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P1 : Sylow 2 K1 := hT1syl.2.1.toSylow (by
      have h := hT1syl.2.2
      rwa [show (T1.subgroupOf ⊤).index = T1.index from by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]] at h)
    let P2 : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
    have hcoe : (P2 : Subgroup (oTwoQuot K1)) = T1.map π :=
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
    have hB : BenderType (oTwoQuot K1) f 1 1 := BenderType.linear f hf e
    obtain ⟨t, hc⟩ := hB.exists_benderCore P2
    rw [hcoe] at hc
    simpa using hc.card_eq
  rw [hmap1, hmap2, hcard]

private theorem relIndex_pCoreOf_vertex_right {L1 L2 S : Subgroup G}
    {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hE : S = (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) :
    (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)).relIndex S = 2 ^ (2 * a + 1) := by
  let Q := pCoreOf 2 (L2 ⊔ bigB L1 L2 S)
  let S1 := S ⊓ L2
  have hS1P : S1 ≤ L2 ⊔ bigB L1 L2 S :=
    (inf_le_right : S ⊓ L2 ≤ L2).trans le_sup_left
  have hS1N : S1 ≤ Subgroup.normalizer (Q : Set G) :=
    hS1P.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L2 ⊔ bigB L1 L2 S))
  have hrel : Q.relIndex S = Q.relIndex S1 := by
    rw [hE]
    exact CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hS1N
  rw [hrel, ← Subgroup.inf_relIndex_right Q S1]
  have hinf : Q ⊓ S1 = pCoreOf 2 L2 := by
    rw [show Q ⊓ S1 = (Q ⊓ L2) ⊓ S1 from by
      simp [S1, inf_assoc, inf_left_comm, inf_comm]]
    have hQL : Q ⊓ L2 = pCoreOf 2 L2 := by
      rw [inf_comm]
      exact inf_pCoreOf_vertex_right hF
    rw [hQL]
    exact inf_eq_left.mpr (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow)
  rw [hinf]
  exact relIndex_pCoreOf_sylow_l2 (by omega) hL2 hF.1.h2.sylow

theorem str83Orders_of_parts (hR : Str83RqEq)
    (hQ : Str83Q1Order) : Str83Orders := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  have hL2' : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) :=
    hR G L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨hE1, hE2⟩ := str83_eq_sup_pCoreOf hF.1 ha hSz hL2'
  have hQ1 : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10 :=
    hQ G L1 L2 S a hF ha hSz hL2'
  let Q1 := pCoreOf 2 (L1 ⊔ bigB L1 L2 S)
  let Q2 := pCoreOf 2 (L2 ⊔ bigB L1 L2 S)
  have hQ1le : Q1 ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hQ2le : Q2 ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)
  have hrel1 : Q1.relIndex S = (2 ^ (2 * a + 1)) ^ 2 :=
    relIndex_pCoreOf_vertex_left hF ha hSz hE1
  have hrel2 : Q2.relIndex S = 2 ^ (2 * a + 1) :=
    relIndex_pCoreOf_vertex_right hF ha hL2' hE2
  have hScard : Nat.card S = (2 ^ (2 * a + 1)) ^ 12 := by
    have h := Subgroup.relIndex_mul_card (H := Q1) (K := S)
    rw [inf_eq_left.mpr hQ1le, hrel1, hQ1] at h
    rw [← h, ← pow_add]
  have hQ2card : Nat.card Q2 = (2 ^ (2 * a + 1)) ^ 11 := by
    have h := Subgroup.relIndex_mul_card (H := Q2) (K := S)
    rw [inf_eq_left.mpr hQ2le, hrel2, hScard] at h
    have hqpos : 0 < 2 ^ (2 * a + 1) := pow_pos (by norm_num) _
    refine Nat.eq_of_mul_eq_mul_left hqpos ?_
    calc 2 ^ (2 * a + 1) * Nat.card Q2 = (2 ^ (2 * a + 1)) ^ 12 := h
      _ = 2 ^ (2 * a + 1) * (2 ^ (2 * a + 1)) ^ 11 := by
        rw [show (12 : ℕ) = 11 + 1 by norm_num, pow_succ, mul_comm]
  exact ⟨hL2', hQ1, hQ2card, hScard⟩

end CFSG.Quasithin.Stroth
