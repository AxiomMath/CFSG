module

public import CFSG.RankThree.PartOne.Q1327T.MSplit
public import CFSG.RankThree.PartOne.Q1327T.GlueDatum
import CFSG.RankThree.PartOne.S12.Sec127
public import CFSG.RankThree.PartOne.Q1327T.Perm3

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327
  CFSG.RankThree.PartOne.K1320 CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.Torsion37
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem weyl_perm3M (H : Hyp G p A c L E f r R s s' zs) {t : MulAut E}
    (hsr : IsAutReflection p E s) (htr : IsAutReflection p E t) (hnc : s * t ≠ t * s)
    (h3 : (s * t) ^ 3 = 1) {a : G} {N P : Subgroup G} (d : PairN p f E R s t a N P) :
    Nonempty (torusImage E N ≃* Equiv.Perm (Fin 3)) := by
  classical
  set a₀ : E := ⟨a, d.a_mem⟩ with ha₀
  have ha1 : a₀ ≠ 1 := fun h1 => d.a_ne (congrArg Subtype.val h1)
  have hWa : ∀ g ∈ torusImage E N, g a₀ = a₀ := by
    intro g hg
    obtain ⟨x, hxN, hx, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hg
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := d.a_cent x hxN
    calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [← this]
      _ = a := by group
  have hss : s * s = 1 := RefFacts.mul_self_eq_one hsr
  have hs1 : s ≠ 1 := fun h1 => by
    have := hsr.1
    rw [h1, orderOf_one] at this
    omega
  have hst1 : s * t ≠ 1 := fun h1 => hnc (by
    have : t = s⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h4 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    rw [this, h4])
  have hρo : orderOf (s * t) = 3 := orderOf_eq_prime h3 hst1
  have hσo : orderOf s = 2 := hsr.1
  have hρW : s * t ∈ torusImage E N := Subgroup.mul_mem _ d.s_mem d.t_mem
  have hc6 := card_eq_six_of_fixes H (Sec127.torusImage_le_torusWeyl E N) ha1 hWa hρW d.s_mem
    hρo hσo
  have : Finite (MulAut ↥E) :=
    Finite.of_injective (fun φ : MulAut ↥E => (φ : ↥E → ↥E)) DFunLike.coe_injective
  have htt : t * t = 1 := RefFacts.mul_self_eq_one htr
  have hrel : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    have h4 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have h5 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [mul_inv_rev, h4, h5, ← mul_assoc, hss, one_mul]
  refine nonempty_mulEquiv_perm_three (⟨s * t, hρW⟩ : ↥(torusImage E N))
    (⟨s, d.s_mem⟩ : ↥(torusImage E N)) ?_ ?_ ?_ ?_ ?_ hc6
  · exact Subtype.ext (by simpa using h3)
  · exact fun h1 => hst1 (congrArg Subtype.val h1)
  · exact Subtype.ext (by simpa using hss)
  · exact fun h1 => hs1 (congrArg Subtype.val h1)
  · exact Subtype.ext (by simpa using hrel)

theorem kf1327S_of_inspectionM
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hSLB : N143.SectionListBound) (hInsp : Row8U3Inspection) :
    KF1327S := by
  intro G _ _ p A c L E f r R s s' zs H
  classical
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  obtain ⟨t, v, ht, hnc, h3, hv1, hsv, htv, hcardP, hvP⟩ := exists_pair hGA H
  obtain ⟨N, P, d⟩ := exists_pairN hS hSLB H ht hv1 hsv htv hnc hcardP hvP
  obtain ⟨hsR, -, -, -⟩ := class_facts H (Or.inl rfl) (mem_clsOf_self p E s)
  obtain ⟨htR, -, -, -⟩ := class_facts H (Or.inl rfl) ht
  have hconc := hInsp (↥N ⧸ aschbacherSolvableCore p ↥N) p f _ trivial d.conf
  have hZ := hconc.1
  have haNot : (v : G) ∉ N := by
    intro haN'
    set θ := aschbacherSolvableCore p ↥N with hθ
    set a' : ↥N := ⟨(v : G), haN'⟩ with ha'
    have hcen : (QuotientGroup.mk' θ a') ∈ Subgroup.center (↥N ⧸ θ) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
      show QuotientGroup.mk' θ n * QuotientGroup.mk' θ a' = QuotientGroup.mk' θ a' *
        QuotientGroup.mk' θ n
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (d.a_cent n n.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    have hθa : a' ∈ θ := (QuotientGroup.eq_one_iff a').1 hcen
    apply not_dvd_card_theta (H := ↥N) hp
    have hord : orderOf (⟨a', hθa⟩ : ↥θ) = p := by
      rw [Subgroup.orderOf_mk]
      have hao : a' ^ p = 1 := Subtype.ext d.a_pow
      have ha1 : a' ≠ 1 := fun h1 => d.a_ne (congrArg Subtype.val h1)
      have : Fact p.Prime := ⟨hp⟩
      exact orderOf_eq_prime hao ha1
    have := orderOf_dvd_natCard (⟨a', hθa⟩ : ↥θ)
    rwa [hord] at this
  obtain ⟨eW⟩ := torusImage_equiv hp d.a_cent d.a_pow d.a_ne haNot d.P_le d.P_elem d.E_eq
  obtain ⟨e3⟩ := weyl_perm3M H hsR.1 htR.1 hnc h3 d
  have hmodel := hconc.2 ⟨eW.symm.trans e3⟩
  obtain ⟨A₀, S, hA₀E, hA₀el, hA₀card, hSp, hS1, hS2, hA₀S, hcomm⟩ :=
    exists_datum hp hp5 H d hZ hmodel
  exact ⟨(v : G), N, A₀, S, d.a_mem, d.a_ne, d.N_le, d.N_mem, d.Ks_le, hmodel, hA₀E, hA₀el,
    hA₀card, hSp, hS1, hS2, hA₀S, hcomm⟩

end CFSG.RankThree.PartOne.Q1327T
