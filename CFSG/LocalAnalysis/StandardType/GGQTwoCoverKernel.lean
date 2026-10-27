module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.CharacteristicNormalizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoNormalizerLift
public import CFSG.RankThree.PGroups.CentralCoprimeKernel
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open Subgroup
open scoped Pointwise

theorem pPrimeCore_complement_of_central_quotient
    {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    {N : Subgroup C} [N.Normal] (hNZ : N ≤ center C)
    (hCN : IsPGroup p (C ⧸ N)) (P : Sylow p C) :
    let K : Subgroup C := pPrimeCore p C
    K ≤ N ∧ K.Characteristic ∧ (P : Subgroup C).Characteristic ∧
      K ⊔ (P : Subgroup C) = ⊤ ∧ Disjoint K (P : Subgroup C) ∧
      Nat.Coprime p (Nat.card K) := by
  let K : Subgroup C := pPrimeCore p C
  have hKN : K ≤ N := CFSG.LocalAnalysis.ComponentInitial.pPrimeCore_le_of_isPGroup_quotient hCN
  have hKchar : K.Characteristic := inferInstance
  have hPnormal : (P : Subgroup C).Normal :=
    (CFSG.RankThree.PGroups.sylow_normal_of_le_center_of_isPGroup_quotient
      (Fact.out : p.Prime) hNZ hCN P).1
  have hPchar : (P : Subgroup C).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hNil : Group.IsNilpotent (C ⧸ N) := hCN.isNilpotent
  have hCnil : Group.IsNilpotent C :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N)
      (by simpa [QuotientGroup.ker_mk'] using hNZ)
  have hdec : (⊤ : Subgroup C) ≤ pCore p C ⊔ K :=
    CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (p := p) hCnil
  have hOpP : pCore p C ≤ (P : Subgroup C) :=
    (CFSG.pCore_isPGroup (p := p) (G := C)).le_sylow_of_normal P
  have hsup : K ⊔ (P : Subgroup C) = ⊤ := by
    apply eq_top_iff.mpr
    have hle : K ⊔ (P : Subgroup C) = (P : Subgroup C) ⊔ K := sup_comm K P
    rw [hle]
    exact hdec.trans (sup_le_sup hOpP le_rfl)
  have hdisj : Disjoint K (P : Subgroup C) := by
    obtain ⟨n, hn⟩ := (P.isPGroup' : IsPGroup p (P : Subgroup C)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact ((CFSG.pPrimeCore_coprime_card (p := p) (G := C)).pow_left n).symm
  have hKcop : Nat.Coprime p (Nat.card K) :=
    CFSG.pPrimeCore_coprime_card (p := p) (G := C)
  exact ⟨hKN, hKchar, hPchar, hsup, hdisj, hKcop⟩

end CFSG.StandardType

namespace CFSG.StandardType

theorem central_core_complement_data
    {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {Bs J C : Subgroup Y} (hB : CFSG.Open.IsElemAbelian p Bs)
    (hCnorm : C.Normal) (hJnorm : J.Normal)
    (hNcen : (C ⊓ J).subgroupOf C ≤ Subgroup.center ↥C)
    (hCN : IsPGroup p (C ⧸ (C ⊓ J).subgroupOf C))
    (P : Sylow p C) :
    let K : Subgroup Y := (pPrimeCore p C).map C.subtype
    let Pg : Subgroup Y := (P : Subgroup C).map C.subtype
    let S : Subgroup Y := Bs ⊔ Pg
    let V : Subgroup Y := Bs ⊔ C
    K ≤ J ∧ K ≤ V ∧ S ≤ V ∧ K ⊔ S = V ∧ K ⊓ S = ⊥ ∧
      IsPGroup p S ∧ Nat.Coprime p (Nat.card K) ∧
      Nat.Coprime (Nat.card K) (K.relIndex V) ∧
      (⊤ : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) ∧
      Bs ≤ Subgroup.normalizer (Pg : Set Y) ∧
      (K.subgroupOf C).Characteristic ∧ (Pg.subgroupOf C).Characteristic := by
  let K0 : Subgroup C := pPrimeCore p C
  let K : Subgroup Y := K0.map C.subtype
  let Pg : Subgroup Y := (P : Subgroup C).map C.subtype
  let S : Subgroup Y := Bs ⊔ Pg
  let V : Subgroup Y := Bs ⊔ C
  have hNnormY : (C ⊓ J).Normal := Subgroup.normal_inf_normal C J
  have hNnormC : ((C ⊓ J).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (Subgroup.le_normalizer_of_normal)
  have hNcenC : (C ⊓ J).subgroupOf C ≤ Subgroup.center ↥C := hNcen
  obtain ⟨hKN, hKchar, hPchar, hsup, hdisj, hKcop⟩ :=
    pPrimeCore_complement_of_central_quotient (p := p)
      (N := (C ⊓ J).subgroupOf C) hNcenC hCN P
  have hKsupP : K ⊔ Pg = C := by
    have h := congrArg (fun T : Subgroup C => T.map C.subtype) hsup
    simpa [K, Pg, K0, Subgroup.map_sup, Subgroup.map_top,
      Subgroup.range_subtype] using h
  have hKleC : K ≤ C := Subgroup.map_subtype_le K0
  have hPgleC : Pg ≤ C := Subgroup.map_subtype_le (P : Subgroup C)
  have hKleJ : K ≤ J := by
    have h := Subgroup.map_mono (f := C.subtype) hKN
    have hmap : ((C ⊓ J).subgroupOf C).map C.subtype = C ⊓ J :=
      Subgroup.map_subgroupOf_eq_of_le inf_le_left
    rw [hmap] at h
    exact h.trans inf_le_right
  have hKleV : K ≤ V := hKleC.trans le_sup_right
  have hSleV : S ≤ V := sup_le le_sup_left (hPgleC.trans le_sup_right)
  have hKsub : K.subgroupOf C = K0 := by
    change (K0.map C.subtype).comap C.subtype = K0
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective K0
  have hPsub : Pg.subgroupOf C = (P : Subgroup C) := by
    change ((P : Subgroup C).map C.subtype).comap C.subtype = (P : Subgroup C)
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective (P : Subgroup C)
  have hKcharC : (K.subgroupOf C).Characteristic := by
    simpa [hKsub] using hKchar
  have hPcharC : (Pg.subgroupOf C).Characteristic := by
    simpa [hPsub] using hPchar
  have htopNC : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (C : Set Y) :=
    Subgroup.le_normalizer_of_normal (K := (⊤ : Subgroup Y))
  have hNK : Subgroup.normalizer (C : Set Y) ≤ Subgroup.normalizer (K : Set Y) :=
    CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic hKleC hKcharC
  have hNP : Subgroup.normalizer (C : Set Y) ≤ Subgroup.normalizer (Pg : Set Y) :=
    CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic hPgleC hPcharC
  have hKnorm : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) := htopNC.trans hNK
  have hPnorm : Bs ≤ Subgroup.normalizer (Pg : Set Y) :=
    (le_top : Bs ≤ (⊤ : Subgroup Y)).trans (htopNC.trans hNP)
  have hKcopY : Nat.Coprime p (Nat.card K) := by
    rw [show Nat.card K = Nat.card K0 from Subgroup.card_map_of_injective C.subtype_injective]
    exact hKcop
  have hSp : IsPGroup p S :=
    IsPGroup.to_sup_of_normal_right' (CFSG.Open.IsElemAbelian.isPGroup hB)
      (P.isPGroup'.map C.subtype) hPnorm
  have hKsupS : K ⊔ S = V := by
    calc
      K ⊔ S = K ⊔ (Bs ⊔ Pg) := rfl
      _ = (K ⊔ Bs) ⊔ Pg := by rw [sup_assoc]
      _ = (Bs ⊔ K) ⊔ Pg := by rw [sup_comm K Bs]
      _ = Bs ⊔ (K ⊔ Pg) := by rw [sup_assoc]
      _ = Bs ⊔ C := by rw [hKsupP]
      _ = V := rfl
  have hKSdisj : K ⊓ S = ⊥ := by
    obtain ⟨n, hn⟩ := hSp.exists_card_eq
    exact Subgroup.inf_eq_bot_of_coprime
      (by simpa [hn] using (hKcopY.symm).pow_right n)
  have hKnormalY : K.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hKnorm)
  have hK'normal : (K.subgroupOf V).Normal := hKnormalY.subgroupOf V
  let f : S.subgroupOf V →* (V ⧸ K.subgroupOf V) :=
    (QuotientGroup.mk' (K.subgroupOf V)).comp (S.subgroupOf V).subtype
  have hf : Function.Surjective f := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      have hv : (v : Y) ∈ K ⊔ S := by rw [hKsupS]; exact v.2
      obtain ⟨k, hk, s, hs, hks⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := K) (t := S)).mp hv
      have hsV : s ∈ V := hSleV hs
      have hksKV : s⁻¹ * k * s ∈ V :=
        V.mul_mem (V.mul_mem (V.inv_mem hsV) (hKleV hk)) hsV
      have hksK : s⁻¹ * k * s ∈ K := by
        simpa using hKnormalY.conj_mem k hk (s⁻¹)
      have hsS : (⟨s, hsV⟩ : V) ∈ S.subgroupOf V :=
        Subgroup.mem_subgroupOf.mpr hs
      refine ⟨⟨(⟨s, hsV⟩ : V), hsS⟩, ?_⟩
      change QuotientGroup.mk' (K.subgroupOf V) (⟨s, hsV⟩ : V) =
        QuotientGroup.mk' (K.subgroupOf V) v
      apply QuotientGroup.eq.mpr
      have hv_eq : v = (⟨k * s, V.mul_mem (hKleV hk) hsV⟩ : V) := by
        apply Subtype.ext
        exact hks.symm
      rw [hv_eq]
      have hval : (⟨s, hsV⟩ : V)⁻¹ * (⟨k * s, V.mul_mem (hKleV hk) hsV⟩ : V) =
          (⟨s⁻¹ * k * s, hksKV⟩ : V) := by
        apply Subtype.ext
        simp [mul_assoc]
      rw [hval]
      exact Subgroup.mem_subgroupOf.mpr hksK
  have hSsub : IsPGroup p (S.subgroupOf V) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSleV).symm
  have hquot : IsPGroup p (V ⧸ K.subgroupOf V) :=
    IsPGroup.of_surjective hSsub f hf
  have hrel : K.relIndex V = Nat.card (V ⧸ K.subgroupOf V) := by
    have h1 : K.relIndex V = (K.subgroupOf V).index := by
      simpa using (Subgroup.relIndex_subgroupOf (H := K) (K := V) (L := V) le_rfl).symm
    exact h1.trans (Subgroup.index_eq_card (K.subgroupOf V))
  obtain ⟨n, hn⟩ := hquot.exists_card_eq
  have hcop : Nat.Coprime (Nat.card K) (K.relIndex V) := by
    rw [hrel, hn]
    exact (hKcopY.symm).pow_right n
  exact ⟨hKleJ, hKleV, hSleV, hKsupS, hKSdisj, hSp, hKcopY, hcop, hKnorm, hPnorm,
    hKcharC, hPcharC⟩

end CFSG.StandardType

namespace CFSG.StandardType

theorem normalizes_sup_of_normalizes_image
    {Y R : Type*} [Group Y] [Finite Y] [Group R] {Bs C : Subgroup Y} {n0 : Y}
    (ρ : Y →* MulAut R) (hCker : C = ρ.ker)
    (hn0C : n0 ∈ Subgroup.normalizer (C : Set Y))
    (hA : ρ n0 ∈
      Subgroup.normalizer (((ρ.comp Bs.subtype).range : Subgroup (MulAut R)) : Set (MulAut R))) :
    n0 ∈ Subgroup.normalizer ((Bs ⊔ C : Subgroup Y) : Set Y) := by
  let A : Subgroup (MulAut R) := (ρ.comp Bs.subtype).range
  have hA' : ρ n0 ∈ Subgroup.normalizer (A : Set (MulAut R)) := hA
  have hCmap : C.map (MulAut.conj n0).toMonoidHom = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn0C
  have hBmap : Bs.map (MulAut.conj n0).toMonoidHom ≤ Bs ⊔ C := by
    rintro _ ⟨b, hb, rfl⟩
    have hbA : ρ b ∈ A := ⟨⟨b, hb⟩, rfl⟩
    have hconjA : ρ n0 * ρ b * (ρ n0)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hA' (ρ b)).mp hbA
    obtain ⟨b0, hb0⟩ := MonoidHom.mem_range.mp hconjA
    let c : Y := n0 * b * n0⁻¹ * (b0 : Bs)⁻¹
    have hb0' : ρ (b0 : Bs) = ρ n0 * ρ b * (ρ n0)⁻¹ := by
      simpa using hb0
    have hcC : c ∈ C := by
      rw [hCker, MonoidHom.mem_ker]
      rw [show c = n0 * b * n0⁻¹ * (b0 : Bs)⁻¹ by rfl]
      change ρ (n0 * b * n0⁻¹ * (↑b0)⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [hb0']
      group
    have hbc : c * (b0 : Bs) = n0 * b * n0⁻¹ := by
      calc
        c * (b0 : Bs) = (n0 * b * n0⁻¹) * ((b0 : Bs)⁻¹ * b0) := by
          simp [c, mul_assoc]
        _ = n0 * b * n0⁻¹ := by simp
    change n0 * b * n0⁻¹ ∈ Bs ⊔ C
    rw [← hbc]
    exact (Bs ⊔ C).mul_mem (Subgroup.mem_sup_right hcC)
      (Subgroup.mem_sup_left (b0 : Bs).2)
  have hVmap : (Bs ⊔ C).map (MulAut.conj n0).toMonoidHom ≤ Bs ⊔ C := by
    rw [Subgroup.map_sup]
    exact sup_le hBmap (hCmap.le.trans le_sup_right)
  have hVmap_eq : (Bs ⊔ C).map (MulAut.conj n0).toMonoidHom = Bs ⊔ C :=
    Subgroup.eq_of_le_of_card_ge hVmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj n0).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hVmap_eq

end CFSG.StandardType

namespace CFSG.StandardType

theorem central_quotient_normalizer_lift
    {Y R : Type} [Group Y] [Finite Y] [Group R] {p : ℕ} [Fact p.Prime]
    {Bs J C : Subgroup Y} {n0 : Y} (ρ : Y →* MulAut R)
    (hB : CFSG.Open.IsElemAbelian p Bs)
    (hCnorm : C.Normal) (hJnorm : J.Normal)
    (hNcen : (C ⊓ J).subgroupOf C ≤ Subgroup.center ↥C)
    (hCN : IsPGroup p (C ⧸ (C ⊓ J).subgroupOf C))
    (P : Sylow p C)
    (hCker : C = ρ.ker)
    (hBcharS : (Bs.subgroupOf (Bs ⊔ (P : Subgroup C).map C.subtype)).Characteristic)
    (hn0J : n0 ∈ J)
    (hA : ρ n0 ∈ Subgroup.normalizer
      (((ρ.comp Bs.subtype).range : Subgroup (MulAut R)) : Set (MulAut R))) :
    ∃ n' ∈ J, n' ∈ Subgroup.normalizer (Bs : Set Y) ∧ ρ n' = ρ n0 := by
  let K : Subgroup Y := (pPrimeCore p C).map C.subtype
  let Pg : Subgroup Y := (P : Subgroup C).map C.subtype
  let S : Subgroup Y := Bs ⊔ Pg
  let V : Subgroup Y := Bs ⊔ C
  obtain ⟨hKleJ, hKleV, hSleV, hKsupS, hKSdisj, hSp, hKcopY, hcop,
    hKnorm, hPnorm, hKcharC, hPcharC⟩ :=
    central_core_complement_data (Y := Y) (Bs := Bs) (J := J) (C := C)
      hB hCnorm hJnorm hNcen hCN P
  have hKnormalY : K.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hKnorm)
  have hn0C : n0 ∈ Subgroup.normalizer (C : Set Y) :=
    (Subgroup.le_normalizer_of_normal (K := (⊤ : Subgroup Y)) (H := C))
      (Subgroup.mem_top n0)
  have hn0V : n0 ∈ Subgroup.normalizer (V : Set Y) := by
    simpa only [V] using normalizes_sup_of_normalizes_image (Bs := Bs) (C := C)
      ρ hCker hn0C hA
  have hn0K : n0 ∈ Subgroup.normalizer (K : Set Y) :=
    (Subgroup.le_normalizer_of_normal (K := (⊤ : Subgroup Y)) (H := K))
      (Subgroup.mem_top n0)
  have hKleC : K ≤ C := Subgroup.map_subtype_le (pPrimeCore p C)
  have hρK : ∀ (z : Y) (hz : z ∈ K), ρ z = 1 := by
    intro z hz
    have hzC : z ∈ C := hKleC hz
    have hzker : z ∈ ρ.ker := by simpa [hCker] using hzC
    exact MonoidHom.mem_ker.mp hzker
  have hBS : Bs ≤ S := le_sup_left
  have hKH : K ≤ V := hKleV
  have hKHnorm : V ≤ Subgroup.normalizer (K : Set Y) := le_top.trans hKnorm
  have hKJ : K ≤ J := hKleJ
  have hKY : K ≤ (⊤ : Subgroup Y) := le_top
  let ρtop : ↥(⊤ : Subgroup Y) →* MulAut R :=
    ρ.comp (Subgroup.topEquiv (G := Y)).toMonoidHom
  have hρKtop : ∀ (z : Y) (hz : z ∈ K), ρtop ⟨z, Subgroup.mem_top z⟩ = 1 := by
    intro z hz
    simpa [ρtop] using hρK z hz
  obtain ⟨n', hn'J, hn'B, hn'Y, hn'ρ⟩ :=
    CFSG.StandardType.exists_normalizer_lift_of_isComplement
      (G := Y) (Y := (⊤ : Subgroup Y)) (B := Bs) (J := J) (K := K) (H := V) (S := S)
      (n0 := n0) (Subgroup.mem_top n0) ρtop hBS hBcharS hKH hKHnorm hcop hSleV
      hKSdisj hKsupS hKJ hKY hn0J hρKtop hn0V hn0K
  exact ⟨n', hn'J, hn'B, by simpa [ρtop] using hn'ρ⟩

end CFSG.StandardType
