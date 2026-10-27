module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SCK
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SLift
import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSp)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem innerOn148_of_inner {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hg3 : g ^ 3 = 1)
    (hinn : ∀ α : MulAut ↥X, α ^ 3 = 1 → ∃ s : ↥X, α = MulAut.conj s) : InnerOn148 X g := by
  have h3 : (X.normalizerMonoidHom ⟨g, hg⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  obtain ⟨s, hs⟩ := hinn _ h3
  refine ⟨s, s.2, fun y hy => ?_⟩
  have := congrArg (fun α : MulAut ↥X => ((α ⟨y, hy⟩ : ↥X) : G)) hs
  simpa using this

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer1422 {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : X.map (MulAut.conj g).toMonoidHom = X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa [mul_assoc] using this

section KP4


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}
  [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem card_K_bar (h : Cfg A c L R S J) :
    Nat.card (img148 A (Subgroup.normalizer (S : Set G)) (L ⊓ Subgroup.normalizer (R : Set G))) =
      360 := by
  obtain ⟨φ⟩ := h.nonempty_K_equiv
  rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num [Nat.factorial]

theorem not_le_centralizer (h : Cfg A c L R S J)
    (hne : Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J) ≠ 360) :
    ¬ img148 A (Subgroup.normalizer (S : Set G)) J ≤
      Subgroup.centralizer {alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A} := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  intro hle
  obtain ⟨hJq, -⟩ := Main148.img148_isQuasisimple (A := A) (Y := M) h.J_mem h.three_dvd_card_J
  obtain ⟨hKL, hKsub⟩ := h.K_le_centralizer
  have heq : img148 A M J ⊓ Subgroup.centralizer {alpha148 A M c h.pt.mem_A} = img148 A M J :=
    inf_eq_left.mpr hle
  rw [heq] at hKL hKsub
  obtain ⟨φ⟩ := h.nonempty_K_equiv
  have hKq : IsQuasisimple ↥(img148 A M K) := by
    have hsimple6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hnc : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
      have : Nontrivial (alternatingGroup (Fin 6)) := hsimple6.toNontrivial
      exact Main148.exists_ne_comm_of_isPerfect isPerfect_alternatingGroup_six
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hKc : IsComponent ((img148 A M K).subgroupOf (img148 A M J)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm hKq,
      hKsub⟩
  have htop := Sec4.Ronan431.eq_top_of_isComponent hJq hKc
  apply hne
  rw [← h.card_K_bar, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, htop,
    Subgroup.card_top]

theorem center_J_eq_bot (h : Cfg A c L R S J)
    (hne : Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J) ≠ 360) :
    img148 A (Subgroup.normalizer (S : Set G)) A ⊓
        Subgroup.centralizer (img148 A (Subgroup.normalizer (S : Set G)) J :
          Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
            ker148 A (Subgroup.normalizer (S : Set G)))) = ⊥ ∧
      Subgroup.center ↥(img148 A (Subgroup.normalizer (S : Set G)) J) = ⊥ := by
  set M := Subgroup.normalizer (S : Set G) with hM
  have hA : IsE27 A := h.pt.std.isE27
  obtain ⟨-, hJθ⟩ := Main148.img148_isQuasisimple (A := A) (Y := M) h.J_mem h.three_dvd_card_J
  have hAC := Sec4.Ronan431.inf_centralizer_eq_bot (img148_isE27 hA)
    (img148_mono (A := A) (Y := M) h.K_le) h.zpowers_eq_inf_centralizer_K
    (h.not_le_centralizer hne)
  exact ⟨hAC, Sec4.Ronan431.center_eq_bot_of_pRank (h.pRank_le ⊤) (img148_isE27 hA) h.normal_J
    hAC (Sec4.Census.isPGroup_center_of_theta_eq_bot hJθ)⟩

theorem le_J_of_innerOn (h : Cfg A c L R S J)
    (hne : Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J) ≠ 360)
    (hin : InnerOn148 (img148 A (Subgroup.normalizer (S : Set G)) J)
      (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A)) : A ≤ J := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  have hA : IsE27 A := h.pt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAF : A ∈ partTwoF G := h.pt.std.toSec13Data.mem_partTwoF
  have hJMA : J ≤ M ⊔ A := h.J_le_M.trans le_sup_left
  obtain ⟨-, hZ⟩ := h.center_J_eq_bot hne
  obtain ⟨u, hu, huJ, hcu⟩ :=
    exists_mem_inf_of_innerOn148 hAF h.A_le_NM hJMA h.A_le hZ h.pt.mem_A hin
  have ha : c * u⁻¹ ∈ A := A.mul_mem h.pt.mem_A (A.inv_mem hu)
  have huJ' : alpha148 A M u hu ∈ img148 A M J := mem_img148_iff.mpr ⟨u, _, huJ, rfl⟩
  have hcent : alpha148 A M (c * u⁻¹) ha ∈
      Subgroup.centralizer (img148 A M K : Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyJ : y ∈ img148 A M J := img148_mono h.K_le hy
    have hy' : (alpha148 A M u hu)⁻¹ * y * alpha148 A M u hu ∈ img148 A M J :=
      (img148 A M J).mul_mem ((img148 A M J).mul_mem ((img148 A M J).inv_mem huJ') hyJ) huJ'
    have h1 := hcu _ hy'
    rw [alpha148_mul h.pt.mem_A (A.inv_mem hu), alpha148_inv hu]
    set γ := alpha148 A M c h.pt.mem_A
    set υ := alpha148 A M u hu
    have h2 : γ * (υ⁻¹ * y * υ) * γ⁻¹ = y := by rw [h1]; group
    calc y * (γ * υ⁻¹) = γ * (υ⁻¹ * y * υ) * γ⁻¹ * (γ * υ⁻¹) := by rw [h2]
      _ = γ * υ⁻¹ * y := by group
  have hmem : alpha148 A M (c * u⁻¹) ha ∈ Subgroup.zpowers (alpha148 A M c h.pt.mem_A) := by
    rw [h.zpowers_eq_inf_centralizer_K]
    exact ⟨alpha148_mem_img148 ha, hcent⟩
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
  have hn' : alpha148 A M c h.pt.mem_A ^ n = alpha148 A M (c * u⁻¹) ha := hn
  rw [← alpha148_pow h.pt.mem_A n] at hn'
  have hcn : c ^ n = c * u⁻¹ :=
    alpha148_injective hA3 (A.pow_mem h.pt.mem_A n) ha hn'
  have huc : u ∈ Subgroup.zpowers c := by
    have : u = (c ^ n)⁻¹ * c := by rw [hcn]; group
    rw [this]
    exact (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem
      ((Subgroup.zpowers c).pow_mem (Subgroup.mem_zpowers c) n)) (Subgroup.mem_zpowers c)
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply h.not_le_centralizer hne
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hcu y hy
    have h2 : alpha148 A M (1 : G) hu = 1 := by
      rw [alpha148_eq_mk']
      rfl
    rw [h2, one_mul, inv_one, mul_one] at h1
    calc y * alpha148 A M c h.pt.mem_A =
        alpha148 A M c h.pt.mem_A * y * (alpha148 A M c h.pt.mem_A)⁻¹ *
          alpha148 A M c h.pt.mem_A := by rw [h1]
      _ = alpha148 A M c h.pt.mem_A * y := by group
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA3 c h.pt.mem_A) h.c_ne_one
  have hu3 : orderOf u = 3 := orderOf_eq_prime (hA3 u hu) hu1
  have hzeq : Subgroup.zpowers u = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hu3])
  have hcJ : c ∈ J := by
    have : c ∈ Subgroup.zpowers u := hzeq ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr huJ) this
  obtain ⟨-, -, hAR, -⟩ := h.pt.R_facts h.R_mem
  rw [h.pt.eq_sup]
  exact sup_le (Subgroup.zpowers_le.mpr hcJ) ((B_le_K hAR).trans h.K_le)


theorem false_of_A9Sp6 (hKF : KF1422A9Sp6) (h : Cfg A c L R S J)
    (hJ : Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃*
        projSp 3 (GaloisField 2 1))) : False := by
  set M := Subgroup.normalizer (S : Set G) with hM
  set J' := img148 A M J with hJ'
  have hA : IsE27 A := h.pt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hne : Nat.card J' ≠ 360 := by
    rcases hJ with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    · rw [Nat.card_congr φ.toEquiv, CFSG.PGLModel.card_projSp_three_two]
      norm_num
  obtain ⟨hinn, hEx⟩ := hKF ↥J' hJ
  have hcN : alpha148 A M c h.pt.mem_A ∈
      Subgroup.normalizer (J' : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
    img148_le_normalizer h.A_le (alpha148_mem_img148 h.pt.mem_A)
  have hc3 : alpha148 A M c h.pt.mem_A ^ 3 = 1 := by
    rw [← alpha148_pow h.pt.mem_A 3]
    simp only [hA3 c h.pt.mem_A]
    rfl
  have hAJ := h.le_J_of_innerOn hne (innerOn148_of_inner hcN hc3 hinn)
  have hAJ' : img148 A M A ≤ J' := img148_mono hAJ
  obtain ⟨hBe, hB9, -⟩ := h.B_bar_facts
  have hBA : img148 A M (A ⊓ L) ≤ img148 A M A := img148_mono inf_le_left
  have hE := isE27_subgroupOf1422 hAJ' (img148_isE27 hA)
  obtain ⟨n, hn, hnD⟩ := hEx ((img148 A M A).subgroupOf J') hE.1 hE.2
    ((img148 A M (A ⊓ L)).subgroupOf J')
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hBA (Subgroup.mem_subgroupOf.mp hx)))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBA.trans hAJ')).toEquiv, hB9])
  have hn' : (n : ↥(M ⊔ A) ⧸ ker148 A M) ∈
      Subgroup.normalizer (img148 A M A : Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hAJ' hx⟩).mp
        (Subgroup.mem_subgroupOf.mpr hx)
      simpa [Subgroup.mem_subgroupOf] using h1
    · intro hx
      have hxJ : x ∈ J' := by
        have h1 : (n : ↥(M ⊔ A) ⧸ ker148 A M)⁻¹ * ((n : _) * x * (n : _)⁻¹) * (n : _) ∈ J' :=
          J'.mul_mem (J'.mul_mem (J'.inv_mem n.2) (hAJ' hx)) n.2
        simpa [mul_assoc] using h1
      have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hxJ⟩).mpr
        (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa [Subgroup.mem_subgroupOf] using h1
  obtain ⟨w, hw, hwA, hwn⟩ := exists_lift_normalizer148
    (fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩) h.A_le_NM hn'
  have hwB : Subgroup.zpowers w ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (h.pt.wb hwA)
  have hnB : (n : ↥(M ⊔ A) ⧸ ker148 A M) ∈
      Subgroup.normalizer (img148 A M (A ⊓ L) : Set (↥(M ⊔ A) ⧸ ker148 A M)) := by
    rw [← hwn]
    exact img148_le_normalizer hwB (mem_img148_iff.mpr ⟨w, hw, Subgroup.mem_zpowers w, rfl⟩)
  apply hnD
  apply map_conj_eq_of_mem_normalizer1422
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp hnB x

end Cfg

end KP4

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
