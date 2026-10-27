module

public import CFSG.RankThree.PartOne.Q1327T.CLeaf
public import CFSG.RankThree.PartOne.Q1327.Datum
public import CFSG.RankThree.PartOne.Q1327T.CAlg

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.Q1327 CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem zs_mul_ss'_apply (hGA : CFSG.Open.GriessAllModelsStatement)
    (H : Hyp G p A c L E f r R s s' zs) (e : E) : (zs * (s * s')) e = e⁻¹ := by
  classical
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  obtain ⟨a, a', b, g₀, -, -, -, -, -, -, hss, haa', -, -, -, -, hfixu, hfixc, -, -, -, -, -, -⟩ :=
    refData hGA H
  have hu : s * s' = a * a' := by
    rcases hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
      exact haa'.symm
  have hs2 : s * s = 1 := RefFacts.mul_self_eq_one H.hs.1
  have hs'2 : s' * s' = 1 := RefFacts.mul_self_eq_one H.hs'.1
  have hzs2 : zs * zs = 1 := RefFacts.mul_self_eq_one H.hzs.1
  have hu2 : (s * s') * (s * s') = 1 := by
    have hc := H.hcomm
    calc s * s' * (s * s') = s * (s' * s) * s' := by group
      _ = s * (s * s') * s' := by rw [hc]
      _ = (s * s) * (s' * s') := by group
      _ = 1 := by rw [hs2, hs'2, one_mul]
  have hzcomm : zs * (s * s') = (s * s') * zs := by
    have h1 := H.hzc s H.hsL
    have h2 := H.hzc s' H.hs'L
    calc zs * (s * s') = (zs * s) * s' := by group
      _ = (s * zs) * s' := by rw [h1]
      _ = s * (zs * s') := by group
      _ = s * (s' * zs) := by rw [h2]
      _ = (s * s') * zs := by group
  have hcu : (s * s') ⟨c, hcE⟩ = ⟨c, hcE⟩ :=
    hfixc (s * s') ((torusImage E L).mul_mem H.hsL H.hs'L) hcE
  have hczs : zs ⟨c, hcE⟩ = (⟨c, hcE⟩ : E)⁻¹ :=
    RefFacts.t_apply_inv_of_mem_autMoved hd H.hzs.1 (c_mem_autMoved H hcE)
  have hmovx : ∀ x : E, zs x * x⁻¹ ∈ Subgroup.zpowers (⟨c, hcE⟩ : E) := by
    intro x
    have h1 : ((zs x * x⁻¹ : E) : G) ∈ autMovedInG E zs :=
      Subgroup.mem_map.2 ⟨zs x * x⁻¹, Subgroup.subset_closure ⟨x, rfl⟩, rfl⟩
    rw [H.hmov] at h1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  have hfixx : ∀ x : E, (s * s') x = x → x ∈ Subgroup.zpowers (⟨c, hcE⟩ : E) := by
    intro x hx
    rw [hu] at hx
    have h1 : (x : G) ∈ autFixedInG E (a * a') := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    rw [hfixu] at h1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  exact zs_mul_u_eq_inv hd hzs2 hu2 hzcomm hczs hcu hmovx hfixx e

theorem s'_mem_cls (hGA : CFSG.Open.GriessAllModelsStatement)
    (H : Hyp G p A c L E f r R s s' zs) : s' ∈ clsOf p E s := by
  obtain ⟨a, a', b, g₀, -, -, -, -, -, -, hss, -, -, -, ⟨h₁, hh₁X, hh₁⟩, -, -, -, -, -, -, -, -,
    -⟩ := refData hGA H
  rcases hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨h₁, hh₁X, ?_⟩
    rw [h1, h2]
    exact hh₁
  · refine ⟨h₁⁻¹, Subgroup.inv_mem _ hh₁X, ?_⟩
    rw [h1, h2, ← hh₁]
    group

theorem zs_mem_torusImage (hGA : CFSG.Open.GriessAllModelsStatement)
    (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G} (hJ : JcData p E c R s Jc)
    {φ : MulAut E} (hφ : φ ∈ torusImage E Jc) (hneg : ∀ e : E, φ e = e⁻¹) :
    zs ∈ torusImage E Jc := by
  have hu : s * s' ∈ torusImage E Jc :=
    (torusImage E Jc).mul_mem (mem_torusImage_Jc H hJ (mem_clsOf_self p E s))
      (mem_torusImage_Jc H hJ (s'_mem_cls hGA H))
  have h1 : zs * (s * s') = φ :=
    MulEquiv.ext fun e => by rw [zs_mul_ss'_apply hGA H e, hneg e]
  have h2 : zs = φ * (s * s')⁻¹ := eq_mul_inv_of_mul_eq h1
  rw [h2]
  exact (torusImage E Jc).mul_mem hφ ((torusImage E Jc).inv_mem hu)

theorem conj_c_commute (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) {y₁ y₂ : G}
    (h₁ : y₁ ∈ Jc ⊓ Subgroup.centralizer (autFixedInG E zs : Set G))
    (h₂ : y₂ ∈ Jc ⊓ Subgroup.centralizer (autFixedInG E zs : Set G)) :
    Commute (y₁ * c * y₁⁻¹) (y₂ * c * y₂⁻¹) := by
  classical
  have h := H.h12
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨-, hKmodel, -, hKmov, -⟩ := H.hKz
  have hcK : c ∈ kZero p E zs := hKmov (by rw [H.hmov]; exact Subgroup.mem_zpowers c)
  have hR1 : R ≠ ⊥ := by
    intro h0
    have := H.hRcard
    rw [h0, Subgroup.card_bot] at this
    exact H.hr.one_lt.ne this
  obtain ⟨⟨ρ, hρ⟩, hρ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
  have hρ1' : ρ ≠ 1 := fun h1 => hρ1 (Subtype.ext h1)
  have hρK : ρ ∈ kZero p E zs := H.hRz hρ
  have key : ∀ y ∈ Jc ⊓ Subgroup.centralizer (autFixedInG E zs : Set G),
      y * c * y⁻¹ ∈ kZero p E zs ∧ Commute ρ (y * c * y⁻¹) := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (kZero p E zs : Set G) :=
      S15K.kZero_normalized p E zs hy.2
    refine ⟨(Subgroup.mem_normalizer_iff.mp hyN c).mp hcK, ?_⟩
    have hρy : Commute ρ y := Subgroup.mem_centralizer_iff.1 (hJ.le_M hy.1) ρ hρ
    have hρc : Commute ρ c := H.hRE ρ hρ c hcE
    exact (hρy.mul_right hρc).mul_right hρy.inv_right
  obtain ⟨ha, haρ⟩ := key y₁ h₁
  obtain ⟨hb, hbρ⟩ := key y₂ h₂
  have hx1 : (⟨ρ, hρK⟩ : ↥(kZero p E zs)) ≠ 1 := fun h1 => hρ1' (congrArg Subtype.val h1)
  have hab := psl_two_centralizer_comm hKmodel
    (a := ⟨y₁ * c * y₁⁻¹, ha⟩) (b := ⟨y₂ * c * y₂⁻¹, hb⟩) hx1
    (Subtype.ext haρ.symm.eq) (Subtype.ext hbρ.symm.eq)
  exact congrArg Subtype.val hab

end CFSG.RankThree.PartOne.Q1327Z
