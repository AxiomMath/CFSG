module

public import CFSG.RankThree.Co2.Hyp
public import Certificates.Certificate16022
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate16000

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster.B.TwoA.Co2Inv

section Conj

variable {G : Type*} [Group G] {z : G}

@[expose] def selfC {K : Type*} [Group K] (x : K) : Subgroup.centralizer ({x} : Set K) :=
  ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem coe_selfC {K : Type*} [Group K] (x : K) : (selfC x : K) = x := rfl

@[expose] def centralC {K : Type*} [Group K] {c : K} (hc : c ∈ Subgroup.center K) (x : K) :
    Subgroup.centralizer ({x} : Set K) :=
  ⟨c, Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 hc x).symm⟩

theorem coe_centralC {K : Type*} [Group K] {c : K} (hc : c ∈ Subgroup.center K) (x : K) :
    (centralC hc x : K) = c := rfl

@[expose] def conjCentralizerEquiv (c : G)
    (t s : Subgroup.centralizer ({z} : Set G)) (ht : (t : G) = c * z * c⁻¹)
    (hs : (s : G) = c⁻¹ * z * c) :
    Subgroup.centralizer ({t} : Set (Subgroup.centralizer ({z} : Set G))) ≃*
      Subgroup.centralizer ({s} : Set (Subgroup.centralizer ({z} : Set G))) where
  toFun x := ⟨⟨c⁻¹ * (x : G) * c, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (x : G) * t = t * x := congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.1 x.2)
      rw [ht] at hx
      calc c⁻¹ * (x : G) * c * z = c⁻¹ * ((x : G) * (c * z * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * z * c⁻¹) * x) * c := by rw [hx]
        _ = z * (c⁻¹ * x * c) := by group⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change c⁻¹ * (x : G) * c * s = s * (c⁻¹ * x * c)
      have hxz : (x : G) * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 x.1.2
      rw [hs]
      calc c⁻¹ * (x : G) * c * (c⁻¹ * z * c) = c⁻¹ * ((x : G) * z) * c := by group
        _ = c⁻¹ * (z * x) * c := by rw [hxz]
        _ = c⁻¹ * z * c * (c⁻¹ * x * c) := by group⟩
  invFun y := ⟨⟨c * (y : G) * c⁻¹, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hy : (y : G) * s = s * y := congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.1 y.2)
      rw [hs] at hy
      calc c * (y : G) * c⁻¹ * z = c * ((y : G) * (c⁻¹ * z * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * z * c) * y) * c⁻¹ := by rw [hy]
        _ = z * (c * y * c⁻¹) := by group⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change c * (y : G) * c⁻¹ * t = t * (c * y * c⁻¹)
      have hyz : (y : G) * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 y.1.2
      rw [ht]
      calc c * (y : G) * c⁻¹ * (c * z * c⁻¹) = c * ((y : G) * z) * c⁻¹ := by group
        _ = c * (z * y) * c⁻¹ := by rw [hyz]
        _ = c * z * c⁻¹ * (c * y * c⁻¹) := by group⟩
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext
    change c * (c⁻¹ * (x : G) * c) * c⁻¹ = x
    group
  right_inv y := by
    apply Subtype.ext; apply Subtype.ext
    change c⁻¹ * (c * (y : G) * c⁻¹) * c = y
    group
  map_mul' x y := by
    apply Subtype.ext; apply Subtype.ext
    change c⁻¹ * ((x : G) * y) * c = c⁻¹ * x * c * (c⁻¹ * y * c)
    group

end Conj

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

@[expose] def partnerIso {t s : h.H} (c : G) (ht : (t : G) = c * h.z * c⁻¹)
    (hs : (s : G) = c⁻¹ * h.z * c) :
    Subgroup.centralizer ({h.φ t} : Set Cr) ≃* Subgroup.centralizer ({h.φ s} : Set Cr) :=
  ((centralizerMulEquiv h.φ t).symm.trans (conjCentralizerEquiv c t s ht hs)).trans
    (centralizerMulEquiv h.φ s)

theorem exists_partner {t : h.H} (ht : IsConj h.z (t : G)) (htz : t ≠ h.zG) :
    ∃ s : h.H, IsConj h.z (s : G) ∧ s ≠ h.zG ∧
      ∃ Ψ : Subgroup.centralizer ({h.φ t} : Set Cr) ≃*
          Subgroup.centralizer ({h.φ s} : Set Cr),
        Ψ (selfC (h.φ t)) = centralC rCr_mem_center (h.φ s) ∧
          Ψ (centralC rCr_mem_center (h.φ t)) = selfC (h.φ s) ∧
          ∃ c : G, c * h.z * c⁻¹ = t ∧ (s : G) = c⁻¹ * h.z * c ∧
            ∀ y, ((h.φ.symm (Ψ y : Cr) : h.H) : G) =
              c⁻¹ * ((h.φ.symm (y : Cr) : h.H) : G) * c := by
  obtain ⟨c, hc⟩ := isConj_iff.1 ht
  have hsH : c⁻¹ * h.z * c ∈ h.H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have htz' : (t : G) * h.z = h.z * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    rw [← hc] at htz'
    calc c⁻¹ * h.z * c * h.z = c⁻¹ * (h.z * (c * h.z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * h.z * c⁻¹) * h.z) * c := by rw [htz']
      _ = h.z * (c⁻¹ * h.z * c) := by group
  set s : h.H := ⟨c⁻¹ * h.z * c, hsH⟩
  have hsz : s ≠ h.zG := by
    intro e
    have e' : c⁻¹ * h.z * c = h.z := congrArg Subtype.val e
    apply htz
    apply Subtype.ext
    change (t : G) = h.z
    rw [← hc]
    calc c * h.z * c⁻¹ = c * (c⁻¹ * h.z * c) * c⁻¹ := by rw [e']
      _ = h.z := by group
  refine ⟨s, isConj_iff.2 ⟨c⁻¹, by simp [s]⟩, hsz, ?_⟩
  have hs0 : (s : G) = c⁻¹ * h.z * c := rfl
  refine ⟨h.partnerIso c hc.symm hs0, ?_, ?_, c, hc, rfl, fun y => ?_⟩
  · apply Subtype.ext
    show h.φ (conjCentralizerEquiv c t s hc.symm hs0
      ((centralizerMulEquiv h.φ t).symm (selfC (h.φ t))) : h.H) = rCr
    refine (congrArg h.φ (?_ : (conjCentralizerEquiv c t s hc.symm hs0
      ((centralizerMulEquiv h.φ t).symm (selfC (h.φ t))) : h.H) = h.zG)).trans h.φ_zG
    apply Subtype.ext
    show c⁻¹ * ((h.φ.symm (h.φ t) : h.H) : G) * c = h.z
    have e3 : ((h.φ.symm (h.φ t) : h.H) : G) = c * h.z * c⁻¹ :=
      (congrArg Subtype.val (h.φ.symm_apply_apply t)).trans hc.symm
    rw [e3]
    group
  · apply Subtype.ext
    show h.φ (conjCentralizerEquiv c t s hc.symm hs0
      ((centralizerMulEquiv h.φ t).symm (centralC rCr_mem_center (h.φ t))) : h.H) = h.φ s
    apply congrArg h.φ
    apply Subtype.ext
    show c⁻¹ * ((h.φ.symm rCr : h.H) : G) * c = c⁻¹ * h.z * c
    exact congrArg (fun x => c⁻¹ * x * c) (congrArg Subtype.val h.φ_symm_rCr)
  · show ((h.φ.symm (h.φ (conjCentralizerEquiv c t s hc.symm hs0
      ((centralizerMulEquiv h.φ t).symm y) : h.H)) : h.H) : G) =
        c⁻¹ * ((h.φ.symm (y : Cr) : h.H) : G) * c
    exact (congrArg Subtype.val (h.φ.symm_apply_apply _)).trans rfl

end Co2CentHyp

end CFSG.RankThree.Co2
