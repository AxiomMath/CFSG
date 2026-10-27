module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J K : Subgroup G} {x y : G}

theorem hdRo7CLOKnownAux_p_eq_three
    (hrow : GGResRowAt ggRowCorank2C p J K) : p = 3 := by
  obtain ⟨_, _, _, _, _, _, hp3, _, _, _, _, _⟩ := hrow
  exact hp3

theorem hdRo7CLOKnownAux_exists_d
    (hH : GGResHyp p B Bs x L D J y K) :
    ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
  have hD_eq : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hD_eq]
    exact Subgroup.subset_closure (by simp)
  refine ⟨y, hyD, ?_⟩
  intro hyx
  have hD_eq_x : D = Subgroup.zpowers x := by
    rw [hD_eq]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy
      · rw [hzx]
        exact Subgroup.mem_zpowers x
      · rw [hzy]
        exact hyx
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hcardD : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hcardZ : Nat.card (Subgroup.zpowers x) = p := by
    haveI : Fact (Nat.Prime p) := ⟨hH.1.tableB_facts.1⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)]
  rw [hD_eq_x, hcardZ] at hcardD
  have hp2 : 1 < p := Nat.Prime.one_lt hH.1.tableB_facts.1
  have hcontra : p ^ 2 = p := hcardD.symm
  have h : p * p = p * 1 := by
    simpa [pow_two] using hcontra
  have hp1 : p = 1 := Nat.mul_left_cancel (Nat.zero_lt_of_lt hp2) h
  exact Nat.Prime.ne_one hH.1.tableB_facts.1 hp1

theorem hdRo7CLOKnownAux_d_pow_eq_one
    (hH : GGResHyp p B Bs x L D J y K) {d : G} (hd : d ∈ D) : d ^ p = 1 := by
  exact hH.1.2.2.1.2.1.2 d hd

theorem hdRo7CLOKnownAux_D_eq_closure
    (hH : GGResHyp p B Bs x L D J y K) :
    D = Subgroup.closure ({x, y} : Set G) ∧ y ∉ Subgroup.zpowers x := by
  have hD_eq : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  refine ⟨hD_eq, ?_⟩
  intro hyx
  have hyD : y ∈ D := by
    rw [hD_eq]
    exact Subgroup.subset_closure (by simp)
  have hD_eq_x : D = Subgroup.zpowers x := by
    rw [hD_eq]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy
      · rw [hzx]
        exact Subgroup.mem_zpowers x
      · rw [hzy]
        exact hyx
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hcardD : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hcardZ : Nat.card (Subgroup.zpowers x) = p := by
    haveI : Fact (Nat.Prime p) := ⟨hH.1.tableB_facts.1⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)]
  rw [hD_eq_x, hcardZ] at hcardD
  have hp2 : 1 < p := Nat.Prime.one_lt hH.1.tableB_facts.1
  have hcontra : p ^ 2 = p := hcardD.symm
  have h : p * p = p * 1 := by
    simpa [pow_two] using hcontra
  have hp1 : p = 1 := Nat.mul_left_cancel (Nat.zero_lt_of_lt hp2) h
  exact Nat.Prime.ne_one hH.1.tableB_facts.1 hp1

@[expose] noncomputable def hdRo7CLOKnownAux_e
    (hH : GGResHyp p B Bs x L D J y K) {d : G} (hd : d ∈ D) : MulAut ↥L where
  toFun l := ⟨d⁻¹ * (l : G) * d, by
    have hnorm : Bs ≤ Subgroup.normalizer (L : Set G) :=
      GGInnerDiagOn.le_normalizer hH.2.2.1.1
    have hdBs : d ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hd)
    exact (Subgroup.mem_normalizer_iff''.1 (hnorm hdBs) (l : G)).1 l.2⟩
  invFun l := ⟨d * (l : G) * d⁻¹, by
    have hnorm : Bs ≤ Subgroup.normalizer (L : Set G) :=
      GGInnerDiagOn.le_normalizer hH.2.2.1.1
    have hdBs : d ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hd)
    exact (Subgroup.mem_normalizer_iff.1 (hnorm hdBs) (l : G)).1 l.2⟩
  left_inv l := by
    apply Subtype.ext
    show d * (d⁻¹ * (l : G) * d) * d⁻¹ = (l : G)
    group
  right_inv l := by
    apply Subtype.ext
    show d⁻¹ * (d * (l : G) * d⁻¹) * d = (l : G)
    group
  map_mul' a b := by
    apply Subtype.ext
    show d⁻¹ * ((a : G) * b) * d = d⁻¹ * a * d * (d⁻¹ * b * d)
    group

theorem hdRo7CLOKnownAux_e_ne_one
    (hH : GGResHyp p B Bs x L D J y K) {d : G} (hd : d ∈ D)
    (hdn : d ∉ Subgroup.zpowers x) :
    ∃ l ∈ L, d⁻¹ * l * d ≠ l := by
  by_contra h
  push_neg at h
  have hd_cent : d ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := h l hl
    have h2 : l * d = d * l := by
      calc l * d = d * (d⁻¹ * l * d) := by group
        _ = d * l := by rw [h1]
    exact h2
  have hdBs : d ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hd)
  have hmem : d ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hdBs, hd_cent⟩
  rw [hdRo7CLCoordAux_bstar_centralizer_eq hH] at hmem
  exact hdn hmem

theorem hdRo7CLOKnownAux_e_pow_eq_one
    (hH : GGResHyp p B Bs x L D J y K) {d : G} (hd : d ∈ D)
    (hdn : d ∉ Subgroup.zpowers x) :
    (hdRo7CLOKnownAux_e hH hd) ^ p = 1 := by
  have hd_pow : d ^ p = 1 := hdRo7CLOKnownAux_d_pow_eq_one hH hd
  have key : ∀ (n : ℕ) (l : ↥L),
      (((hdRo7CLOKnownAux_e hH hd) ^ n) l : G) = (d ^ n)⁻¹ * (l : G) * d ^ n := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
        intro l
        rw [pow_succ, MulAut.mul_apply, ih]
        change (d ^ n)⁻¹ * (d⁻¹ * (l : G) * d) * d ^ n =
          (d ^ (n + 1))⁻¹ * (l : G) * d ^ (n + 1)
        group
  ext l
  simp only [MulAut.one_apply]
  rw [key p l, hd_pow]
  simp

theorem hdRo7CLOKnownAux_centralizer_eq
    (hH : GGResHyp p B Bs x L D J y K) {d : G} (hd : d ∈ D)
    (hdn : d ∉ Subgroup.zpowers x) :
    Subgroup.centralizer ({d} : Set G) ⊓ L = Subgroup.centralizer (D : Set G) ⊓ L := by
  have hD_eq : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hx_mem : x ∈ D := by
    rw [hD_eq]
    exact Subgroup.subset_closure (by simp)
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
    hH.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hcardD : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hcardzx : Nat.card (Subgroup.zpowers x) = p := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)]
  set H : Subgroup G := Subgroup.closure ({x, d} : Set G) with hHdef
  have hH_le_D : H ≤ D := by
    rw [hHdef, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx_mem
    · exact hd
  have hzx_le_H : Subgroup.zpowers x ≤ H := by
    rw [hHdef, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hd_mem_H : d ∈ H := by
    rw [hHdef]
    exact Subgroup.subset_closure (by simp)
  have hcardH_dvd : Nat.card H ∣ p ^ 2 := by
    rw [← hcardD]
    exact Subgroup.card_dvd_of_le hH_le_D
  obtain ⟨i, hi_le, hi_eq⟩ := (Nat.dvd_prime_pow hp).1 hcardH_dvd
  have hp_dvd_H : p ∣ Nat.card H := by
    have hdvd := Subgroup.card_dvd_of_le hzx_le_H
    rwa [hcardzx] at hdvd
  have hi_ge : 1 ≤ i := by
    by_contra h
    push_neg at h
    have hi0 : i = 0 := by omega
    rw [hi0, pow_zero] at hi_eq
    have : p ∣ 1 := by rwa [hi_eq] at hp_dvd_H
    exact hp.not_dvd_one this
  have hD_eq_xd : D = H := by
    have hi_cases : i = 1 ∨ i = 2 := by omega
    rcases hi_cases with hi1 | hi2
    · exfalso
      have hcardH : Nat.card H = p := by rw [hi_eq, hi1, pow_one]
      have hHzx : Subgroup.zpowers x = H :=
        Subgroup.eq_of_le_of_card_ge hzx_le_H (by rw [hcardH, hcardzx])
      rw [← hHzx] at hd_mem_H
      exact hdn hd_mem_H
    · have hcardH : Nat.card H = p ^ 2 := by rw [hi_eq, hi2]
      exact (Subgroup.eq_of_le_of_card_ge hH_le_D (by rw [hcardH, hcardD])).symm
  rw [hD_eq_xd, Subgroup.centralizer_closure]
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf] at hg ⊢
    obtain ⟨hgd, hgL⟩ := hg
    refine ⟨?_, hgL⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mp (hLx hgL) _ (by simp)
    · exact Subgroup.mem_centralizer_iff.mp hgd _ (by simp)
  · intro g hg
    rw [Subgroup.mem_inf] at hg ⊢
    obtain ⟨hgxd, hgL⟩ := hg
    refine ⟨?_, hgL⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp hgxd _ (by simp)

theorem hdRo7CLOKnownAux_ggFixSub_eq
    (hH : GGResHyp p B Bs x L D J y K) {d : G} (hd : d ∈ D)
    (hdn : d ∉ Subgroup.zpowers x) :
    ggFixSub (hdRo7CLOKnownAux_e hH hd) =
      (Subgroup.centralizer ({d} : Set G) ⊓ L).subgroupOf L := by
  ext l
  rw [mem_ggFixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hcoe : d⁻¹ * (l : G) * d = (l : G) := by
      simpa [hdRo7CLOKnownAux_e] using congrArg Subtype.val h
    have hrel : (l : G) * d = d * (l : G) := by
      calc (l : G) * d = d * (d⁻¹ * (l : G) * d) := by group
        _ = d * (l : G) := by rw [hcoe]
    exact ⟨hrel, l.2⟩
  · rintro ⟨hrel, -⟩
    apply Subtype.ext
    show d⁻¹ * (l : G) * d = (l : G)
    calc d⁻¹ * (l : G) * d = d⁻¹ * ((l : G) * d) := by group
      _ = d⁻¹ * (d * (l : G)) := by rw [hrel]
      _ = (l : G) := by group

private theorem hdRo7CLOKnownAux_isComponentOf_subgroupOf_of {Γ : Type*} [Group Γ]
    {Q H G : Subgroup Γ} (hQ : CFSG.Assembly.IsComponentOf Q H) (hQG : Q ≤ G) :
    CFSG.Assembly.IsComponentOf (Q.subgroupOf G) (H.subgroupOf G) :=
  ⟨Subgroup.comap_mono hQ.1, hQ.2.1.comap G.subtype,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQG) hQ.2.2⟩

theorem hdRo7CLOKnownAux_component
    (hH : GGResHyp p B Bs x L D J y K) {d : G} (hd : d ∈ D)
    (hdn : d ∉ Subgroup.zpowers x) :
    CFSG.Assembly.IsComponentOf (J.subgroupOf L) (ggFixSub (hdRo7CLOKnownAux_e hH hd)) := by
  have hQ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJ_le_L : J ≤ L := hQ.1.trans inf_le_left
  have hcomp := hdRo7CLOKnownAux_isComponentOf_subgroupOf_of hQ hJ_le_L
  have hDd : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [inf_comm L (Subgroup.centralizer (D : Set G))]
    rw [← hdRo7CLOKnownAux_centralizer_eq hH hd hdn]
    rw [inf_comm (Subgroup.centralizer ({d} : Set G)) L]
  have hgoal : ggFixSub (hdRo7CLOKnownAux_e hH hd) =
      (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L := by
    rw [hdRo7CLOKnownAux_ggFixSub_eq hH hd hdn]
    congr 1
    rw [inf_comm (Subgroup.centralizer ({d} : Set G)) L]
    exact hDd.symm
  rw [hgoal]
  exact hcomp

end CFSG.StandardType.HdRo7C

end
