module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootLocal
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentFusion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.GroupTheory.SwappedFactorsOffenders
public import CFSG.GH74.GLS.SP.GenOrder
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] (D : RootData G)

private lemma card_closure_t_u : Nat.card (closure {D.t, D.u} : Subgroup G) = 4 :=
  card_closure_pair D.orderOf_t D.orderOf_u D.t_commute_u D.u_ne_t

private lemma t_ne_one : D.t ≠ 1 :=
  (orderOf_eq_prime_iff.mp D.orderOf_t).2

private lemma u_ne_one : D.u ≠ 1 :=
  (orderOf_eq_prime_iff.mp D.orderOf_u).2

private lemma isKleinFour_closure_t_u [Finite G] :
    IsKleinFour (closure {D.t, D.u} : Subgroup G) := by
  haveI : Fintype (closure {D.t, D.u} : Subgroup G) := Fintype.ofFinite _
  haveI : Nontrivial (closure {D.t, D.u} : Subgroup G) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, card_closure_t_u D]
    norm_num
  refine IsKleinFour.mk (card_closure_t_u D) ?_
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  refine orderOf_eq_prime ?_ hg
  ext
  refine sq_eq_one_of_mem_closure (s := ({D.t, D.u} : Set G)) ?_ ?_ g.2
  · intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact D.t_commute_u
    · exact D.t_commute_u.symm
    · exact Commute.refl _
  · intro a ha
    rcases ha with rfl | rfl
    · rw [← D.orderOf_t, pow_orderOf_eq_one]
    · rw [← D.orderOf_u, pow_orderOf_eq_one]

private lemma closure_t_u_le_centralizer :
    closure {D.t, D.u} ≤ centralizer (D.D1 : Set G) := by
  have ht : D.t ∈ centralizer (D.D1 : Set G) := by
    rw [D.D1_eq_range, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact (D.d_commute_t (thetaM a.toAdd)).eq
  have hu : D.u ∈ centralizer (D.D1 : Set G) := by
    rw [D.D1_eq_range, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact (D.d_commute_u (thetaM a.toAdd)).eq
  refine (closure_le _).mpr ?_
  rintro g (rfl | rfl)
  exacts [ht, hu]

private lemma D1_le_centralizer_u : D.D1 ≤ centralizer {D.u} := by
  rw [D.D1_eq_range]
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (D.d_commute_u (thetaM a.toAdd)).eq

private lemma isMulCommutative_closure_t_u :
    IsMulCommutative (closure {D.t, D.u} : Subgroup G) := by
  refine Subgroup.isMulCommutative_closure (k := ({D.t, D.u} : Set G)) ?_
  intro a ha b hb _
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Commute.refl _
  · exact D.t_commute_u
  · exact D.t_commute_u.symm
  · exact Commute.refl _

private lemma closure_t_u_le_centralizer_sup :
    closure {D.t, D.u} ≤
      centralizer ((D.D1 ⊔ closure {D.t, D.u} : Subgroup G) : Set G) := by
  rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
  haveI := isMulCommutative_closure_t_u D
  exact le_inf (closure_t_u_le_centralizer D) (Subgroup.le_centralizer (H := closure {D.t, D.u}))

private lemma conj_u_of_mem_normalizer_closure_t_u {g : G}
    (hg : g ∈ normalizer (closure {D.t, D.u} : Set G)) : g * D.u * g⁻¹ = D.u := by
  have hgt : g * D.t * g⁻¹ ∈ closure {D.t, D.u} :=
    (mem_normalizer_iff.mp hg D.t).mp (subset_closure (by simp))
  have hgu : g * D.u * g⁻¹ ∈ closure {D.t, D.u} :=
    (mem_normalizer_iff.mp hg D.u).mp (subset_closure (by simp))
  have hne1 : ∀ x : G, x ≠ 1 → g * x * g⁻¹ ≠ 1 := by
    intro x hx h
    refine hx ?_
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  rcases D.mem_closure_t_u hgt with h | h | h | h
  · exact absurd h (hne1 D.t (t_ne_one D))
  · rcases D.mem_closure_t_u hgu with h' | h' | h' | h'
    · exact absurd h' (hne1 D.u (u_ne_one D))
    · exact absurd (isConj_iff.mpr ⟨g, h'⟩).symm D.not_isConj_t_u
    · exact h'
    · exact absurd (D.isConj_t_tu.trans (isConj_iff.mpr ⟨g, h'⟩).symm) D.not_isConj_t_u
  · exact absurd (isConj_iff.mpr ⟨g, h⟩) D.not_isConj_t_u
  · rcases D.mem_closure_t_u hgu with h' | h' | h' | h'
    · exact absurd h' (hne1 D.u (u_ne_one D))
    · exact absurd (isConj_iff.mpr ⟨g, h'⟩).symm D.not_isConj_t_u
    · exact h'
    · exfalso
      have hEq : D.u = D.t := by
        calc D.u = g⁻¹ * (g * D.u * g⁻¹) * g := by group
          _ = g⁻¹ * (g * D.t * g⁻¹) * g := by rw [h', h]
          _ = D.t := by group
      exact D.u_ne_t hEq

private lemma card_sup_D1_closure_t_u [Finite G] :
    Nat.card (D.D1 ⊔ closure {D.t, D.u} : Subgroup G) = 20 := by
  obtain ⟨-, -, -, -, -, -, -, hD1F, -, -, -, -⟩ := D.diagonal_unipotent_local_data
  have hA : (closure {D.t, D.u} : Subgroup G) ≤ normalizer (D.D1 : Set G) :=
    (closure_t_u_le_centralizer D).trans (Subgroup.centralizer_le_normalizer _)
  rw [CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hA hD1F, D.card_D1, card_closure_t_u D]

private lemma normalizer_closure_t_u_inf_le [Finite G] :
    normalizer (closure {D.t, D.u} : Set G) ⊓ centralizer (D.D1 : Set G) ≤
      D.D1 ⊔ closure {D.t, D.u} := by
  obtain ⟨-, -, -, -, -, -, -, -, hCu, -, -, -⟩ := D.diagonal_unipotent_local_data
  intro g hg
  obtain ⟨hgN, hgC⟩ := mem_inf.mp hg
  have hgu : g * D.u * g⁻¹ = D.u := conj_u_of_mem_normalizer_closure_t_u D hgN
  have hgCu : g ∈ centralizer {D.u} := by
    rw [mem_centralizer_singleton_iff]
    calc g * D.u = g * D.u * g⁻¹ * g := by group
      _ = D.u * g := by rw [hgu]
  rw [← hCu]
  exact mem_inf.mpr ⟨hgC, hgCu⟩

private lemma le_of_inf_normalizer_le {P H : Subgroup G} [Finite G]
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (h : normalizer (H : Set G) ⊓ P ≤ H) : P ≤ H := by
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  by_contra hle
  have hHlt : H.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun htop => hle htop
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt (hnc (H.subgroupOf P) hHlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hHP] at hxN
  exact hxH (Subgroup.mem_subgroupOf.mpr
    (h (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxN, x.2⟩)))

private lemma eq_of_isPGroup_two_of_le {P : Subgroup G} [Finite G]
    (hP : IsPGroup 2 P) (hPC : P ≤ centralizer (D.D1 : Set G))
    (hFP : closure {D.t, D.u} ≤ P) : P = closure {D.t, D.u} := by
  have hPF : P ⊓ (D.D1 ⊔ closure {D.t, D.u} : Subgroup G) = closure {D.t, D.u} := by
    have hP2 : IsPGroup 2 ↥(P ⊓ (D.D1 ⊔ closure {D.t, D.u} : Subgroup G)) := hP.to_inf_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)
      (G := ↥(P ⊓ (D.D1 ⊔ closure {D.t, D.u} : Subgroup G)))).mp hP2
    have hdvd : 2 ^ n ∣ 20 := by
      rw [← hn]
      exact (Subgroup.card_dvd_of_le inf_le_right).trans (by rw [card_sup_D1_closure_t_u D])
    have h4dvd : 4 ∣ 2 ^ n := by
      rw [← hn, ← card_closure_t_u D]
      exact Subgroup.card_dvd_of_le (le_inf hFP le_sup_right)
    have hn2 : 2 ≤ n := by
      have h4le : 2 ^ 2 ≤ 2 ^ n := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at h4dvd
        exact Nat.le_of_dvd (by positivity) h4dvd
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4le
    have hn4 : n ≤ 4 := by
      by_contra h
      have h5 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle : 2 ^ n ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd
      norm_num at h5
      omega
    interval_cases n
    · exact (Subgroup.eq_of_le_of_card_ge
        (le_inf hFP (le_sup_right : _ ≤ D.D1 ⊔ closure {D.t, D.u}))
        (by rw [hn, card_closure_t_u D]; norm_num)).symm
    · norm_num at hdvd
    · norm_num at hdvd
  have h' : normalizer (closure {D.t, D.u} : Set G) ⊓ P ≤ D.D1 ⊔ closure {D.t, D.u} :=
    (inf_le_inf_left _ hPC).trans (normalizer_closure_t_u_inf_le D)
  have h'' : normalizer (closure {D.t, D.u} : Set G) ⊓ P ≤
      P ⊓ (D.D1 ⊔ closure {D.t, D.u}) := le_inf inf_le_right h'
  rw [hPF] at h''
  exact le_antisymm (le_of_inf_normalizer_le hP hFP h'') hFP

private lemma sylow_closure_t_u [Finite G] :
    ∃ S : Sylow 2 ↥(centralizer (D.D1 : Set G)),
      (S : Subgroup ↥(centralizer (D.D1 : Set G))) =
        (closure {D.t, D.u}).subgroupOf (centralizer (D.D1 : Set G)) ∧
      (S : Subgroup ↥(centralizer (D.D1 : Set G))) ≤
        CFSG.centerIn (G := ↥(centralizer (D.D1 : Set G)))
          (normalizer (S : Subgroup ↥(centralizer (D.D1 : Set G)))) := by
  classical
  have hFC : closure {D.t, D.u} ≤ centralizer (D.D1 : Set G) := closure_t_u_le_centralizer D
  have hF2' : IsPGroup 2 ((closure {D.t, D.u}).subgroupOf (centralizer (D.D1 : Set G))) := by
    have h := (IsPGroup.of_card (p := 2) (n := 2)
      (by rw [card_closure_t_u D]; norm_num)).comap_of_injective
      (centralizer (D.D1 : Set G)).subtype (centralizer (D.D1 : Set G)).subtype_injective
    rwa [Subgroup.comap_subtype] at h
  obtain ⟨S, hSge⟩ := hF2'.exists_le_sylow
  have hSeq : (S : Subgroup ↥(centralizer (D.D1 : Set G))) =
      (closure {D.t, D.u}).subgroupOf (centralizer (D.D1 : Set G)) := by
    have hP2 : IsPGroup 2 ((S : Subgroup ↥(centralizer (D.D1 : Set G))).map
        (centralizer (D.D1 : Set G)).subtype) := S.isPGroup'.map _
    have hPC : (S : Subgroup ↥(centralizer (D.D1 : Set G))).map
        (centralizer (D.D1 : Set G)).subtype ≤ centralizer (D.D1 : Set G) :=
      Subgroup.map_subtype_le _
    have hFP : closure {D.t, D.u} ≤ (S : Subgroup ↥(centralizer (D.D1 : Set G))).map
        (centralizer (D.D1 : Set G)).subtype := by
      have h := Subgroup.map_mono hSge (f := (centralizer (D.D1 : Set G)).subtype)
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hFC] at h
    have heq : (S : Subgroup ↥(centralizer (D.D1 : Set G))).map
        (centralizer (D.D1 : Set G)).subtype = closure {D.t, D.u} :=
      eq_of_isPGroup_two_of_le D hP2 hPC hFP
    refine Subgroup.map_subtype_inj.mp ?_
    rw [heq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hFC]
  refine ⟨S, hSeq, ?_⟩
  intro x hx
  refine mem_inf.mpr ⟨Subgroup.le_normalizer hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyN : y ∈ (Subgroup.normalizer (closure {D.t, D.u} : Set G)).subgroupOf
      (centralizer (D.D1 : Set G)) := by
    rw [Subgroup.subgroupOf_normalizer_eq hFC, ← hSeq]
    exact hy
  have hyA : ((y : ↥(centralizer (D.D1 : Set G))) : G) ∈ D.D1 ⊔ closure {D.t, D.u} :=
    normalizer_closure_t_u_inf_le D
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hyN, y.2⟩)
  have hxF : ((x : ↥(centralizer (D.D1 : Set G))) : G) ∈ closure {D.t, D.u} :=
    Subgroup.mem_subgroupOf.mp (hSeq ▸ hx)
  refine Subtype.ext ?_
  simpa using (Subgroup.mem_centralizer_iff.mp (closure_t_u_le_centralizer_sup D hxF) _ hyA)

private lemma card_R [Finite G] : Nat.card D.R = 25 := by
  obtain ⟨-, -, -, -, hRcard, -, -, -, -, -, -, -⟩ := D.diagonal_unipotent_local_data
  exact hRcard

private lemma D1_le_R : D.D1 ≤ D.R := by
  rw [D.D1_eq_range]
  rintro _ ⟨a, rfl⟩
  exact mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨a, rfl⟩)

private lemma isMulCommutative_R : IsMulCommutative D.R := by
  haveI h1 : IsMulCommutative D.P1 := Subgroup.range_isMulCommutative D.q1
  haveI h2 : IsMulCommutative D.P2 := Subgroup.range_isMulCommutative D.q2
  have hR : D.R = D.P1 ⊔ D.P2 := rfl
  rw [hR]
  refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
  rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
  have h12 : D.P1 ≤ centralizer (D.P2 : Set G) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact (D.commute_q1_q2 a b).eq.symm
  have h21 : D.P2 ≤ centralizer (D.P1 : Set G) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact (D.commute_q1_q2 a b).eq
  exact sup_le (le_inf (Subgroup.le_centralizer (H := D.P1)) h12)
    (le_inf h21 (Subgroup.le_centralizer (H := D.P2)))

private lemma R_le_centralizer : D.R ≤ centralizer (D.D1 : Set G) := by
  haveI := isMulCommutative_R D
  exact (Subgroup.le_centralizer (H := D.R)).trans (Subgroup.centralizer_le (D1_le_R D))

private lemma R_le_centralizer_t [Finite G] : D.R ≤ centralizer {D.t} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hCt, -, -⟩ := D.diagonal_unipotent_local_data
  have h : D.R ≤ centralizer (D.D1 : Set G) ⊓ centralizer {D.t} := hCt ▸ le_sup_left
  exact h.trans inf_le_right

private lemma closure_t_u_le_normalizer_R [Finite G] :
    closure {D.t, D.u} ≤ normalizer (D.R : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hNR⟩ := D.diagonal_unipotent_local_data
  have hle : D.R ⊔ D.H ⊔ zpowers D.u ≤ normalizer (D.R : Set G) := hNR ▸ inf_le_left
  refine (closure_le _).mpr ?_
  rintro g (rfl | rfl)
  · refine hle (mem_sup_left (mem_sup_right ?_))
    exact zpowers_le.mpr (subset_closure (by simp)) D.t_mem_zpowers_h1
  · exact hle (mem_sup_right (mem_zpowers D.u))

private lemma card_sup_R_closure_t_u [Finite G] :
    Nat.card (D.R ⊔ closure {D.t, D.u} : Subgroup G) = 100 := by
  obtain ⟨-, -, -, -, hRcard, -, -, -, -, -, -, -⟩ := D.diagonal_unipotent_local_data
  have hinf : D.R ⊓ closure {D.t, D.u} = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hRcard, card_closure_t_u D]
    norm_num
  rw [CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot (closure_t_u_le_normalizer_R D) hinf,
    hRcard, card_closure_t_u D]

private lemma card_map_R [Finite G] :
    Nat.card (D.R.map (MulAut.conj D.y⁻¹).toMonoidHom : Subgroup G) = 25 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj D.y⁻¹).injective, card_R D]

private lemma map_conj_le_centralizer {g : G} (hg : g ∈ normalizer (D.D1 : Set G)) :
    D.R.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (D.D1 : Set G) := by
  intro z hz
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hgd : g * d * g⁻¹ ∈ D.D1 := (Subgroup.mem_normalizer_iff.mp hg d).mp hd
  have hcomm : (g * d * g⁻¹) * r = r * (g * d * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (R_le_centralizer D hr) _ hgd
  show d * (MulAut.conj g⁻¹) r = (MulAut.conj g⁻¹) r * d
  rw [MulAut.conj_apply, inv_inv]
  calc d * (g⁻¹ * r * g) = g⁻¹ * ((g * d * g⁻¹) * r) * g := by group
    _ = g⁻¹ * (r * (g * d * g⁻¹)) * g := by rw [hcomm]
    _ = g⁻¹ * r * g * d := by group

private lemma map_conj_le_centralizer_tu [Finite G] :
    D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤ centralizer {D.t * D.u} := by
  intro z hz
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hz
  have hcomm : r * D.t = D.t * r := by
    have h := R_le_centralizer_t D hr
    rwa [Subgroup.mem_centralizer_singleton_iff] at h
  have hyu : D.y * D.u * D.y⁻¹ = D.u := by
    calc D.y * D.u * D.y⁻¹ = D.u * D.y * D.y⁻¹ := by rw [D.y_commute_u.eq]
      _ = D.u := by group
  have htu' : D.t * D.u = D.y * D.t * D.y⁻¹ := by
    calc D.t * D.u = D.y * (D.y⁻¹ * (D.t * D.u) * D.y) * D.y⁻¹ := by group
      _ = D.y * D.t * D.y⁻¹ :=
          by rw [show D.y⁻¹ * (D.t * D.u) * D.y = D.t from D.outer.y_conj_tu]
  have hy : D.y * (D.t * D.u) * D.y⁻¹ = D.t := by
    calc D.y * (D.t * D.u) * D.y⁻¹
        = (D.y * D.t * D.y⁻¹) * (D.y * D.u * D.y⁻¹) := by group
      _ = (D.t * D.u) * D.u := by rw [htu', hyu]
      _ = D.t := by rw [mul_assoc, D.u_mul_u, mul_one]
  have hconj : D.y⁻¹ * r * D.y * (D.t * D.u) * (D.y⁻¹ * r * D.y)⁻¹ = D.t * D.u := by
    calc D.y⁻¹ * r * D.y * (D.t * D.u) * (D.y⁻¹ * r * D.y)⁻¹
        = D.y⁻¹ * r * (D.y * (D.t * D.u) * D.y⁻¹) * r⁻¹ * D.y := by group
      _ = D.y⁻¹ * r * D.t * r⁻¹ * D.y := by rw [hy]
      _ = D.y⁻¹ * (r * D.t * r⁻¹) * D.y := by group
      _ = D.y⁻¹ * D.t * D.y := by rw [show r * D.t * r⁻¹ = D.t from by rw [hcomm]; group]
      _ = D.t * D.u := D.outer.y_conj_t
  rw [Subgroup.mem_centralizer_singleton_iff]
  show (MulAut.conj D.y⁻¹) r * (D.t * D.u) = (D.t * D.u) * (MulAut.conj D.y⁻¹) r
  rw [MulAut.conj_apply, inv_inv]
  calc D.y⁻¹ * r * D.y * (D.t * D.u)
      = D.y⁻¹ * r * D.y * (D.t * D.u) * (D.y⁻¹ * r * D.y)⁻¹ * (D.y⁻¹ * r * D.y) := by
        group
    _ = (D.t * D.u) * (D.y⁻¹ * r * D.y) := by rw [hconj]

private lemma map_conj_closure_t_u :
    (closure {D.t, D.u} : Subgroup G).map (MulAut.conj D.y⁻¹).toMonoidHom =
      closure {D.t, D.u} := by
  have h1 : (MulAut.conj D.y⁻¹).toMonoidHom D.t = D.t * D.u := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact D.outer.y_conj_t
  have h2 : (MulAut.conj D.y⁻¹).toMonoidHom D.u = D.u := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc D.y⁻¹ * D.u * D.y = D.y⁻¹ * (D.u * D.y) := by group
      _ = D.y⁻¹ * (D.y * D.u) := by rw [D.y_commute_u.eq]
      _ = D.u := by group
  rw [MonoidHom.map_closure, Set.image_pair, h1, h2]
  refine le_antisymm ?_ ?_
  · refine (closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · exact subset_closure (by simp)
  · refine (closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · have hmem : (D.t * D.u) * D.u ∈ closure {D.t * D.u, D.u} :=
        mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      have h : (D.t * D.u) * D.u = D.t := by rw [mul_assoc, D.u_mul_u, mul_one]
      rwa [h] at hmem
    · exact subset_closure (by simp)

private lemma card_sup_map_R_closure_t_u [Finite G] :
    Nat.card
      (D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ⊔ closure {D.t, D.u} : Subgroup G) = 100 := by
  have heq : (D.R ⊔ closure {D.t, D.u} : Subgroup G).map (MulAut.conj D.y⁻¹).toMonoidHom =
      D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ⊔ closure {D.t, D.u} := by
    rw [Subgroup.map_sup, map_conj_closure_t_u D]
  rw [← heq, Subgroup.card_map_of_injective (MulAut.conj D.y⁻¹).injective,
    card_sup_R_closure_t_u D]

private lemma centralizer_closure_t_u :
    centralizer ((closure {D.t, D.u} : Subgroup G) : Set G) =
      centralizer ({D.t} : Set G) ⊓ centralizer ({D.u} : Set G) := by
  have h1 : (closure {D.t, D.u} : Subgroup G) = zpowers D.t ⊔ zpowers D.u := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  rw [h1, CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer,
    Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure, Subgroup.centralizer_closure]

private lemma card_quot_pPrimeCore [Finite G] :
    Nat.card (↥(centralizer (D.D1 : Set G)) ⧸
      CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))) = 4 := by
  classical
  obtain ⟨S, hS, hScenter⟩ := sylow_closure_t_u D
  have hcomp : CFSG.HasNormalPComplement 2 ↥(centralizer (D.D1 : Set G)) :=
    CFSG.hasNormalPComplement_of_sylow_le_center_normalizer 2 S hScenter
  have hmapcard : Nat.card ↥((S : Subgroup ↥(centralizer (D.D1 : Set G))).map
      (centralizer (D.D1 : Set G)).subtype) = 4 := by
    rw [hS, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (closure_t_u_le_centralizer D), card_closure_t_u D]
  have hcardS : Nat.card ↥S = 4 := by
    have h1 := Subgroup.card_map_of_injective (centralizer (D.D1 : Set G)).subtype_injective
      (K := (S : Subgroup ↥(centralizer (D.D1 : Set G))))
    rw [hmapcard] at h1
    exact h1.symm
  let e := CFSG.BenderSuzuki.External.quotientPPrimeCoreEquivSylowOfHasNormalPComplement
    hcomp S
  rw [Nat.card_congr e.toEquiv]
  exact hcardS

private lemma relIndex_pPrimeCore [Finite G] :
    ((CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))).map
        (centralizer (D.D1 : Set G)).subtype).relIndex (centralizer (D.D1 : Set G)) = 4 := by
  have hsub : ((CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))).map
      (centralizer (D.D1 : Set G)).subtype).subgroupOf (centralizer (D.D1 : Set G)) =
      CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G)) := by
    rw [← Subgroup.map_subtype_inj, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (Subgroup.map_subtype_le _)
  show (((CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))).map
    (centralizer (D.D1 : Set G)).subtype).subgroupOf (centralizer (D.D1 : Set G))).index = 4
  rw [hsub, Subgroup.index_eq_card]
  exact card_quot_pPrimeCore D

private lemma pPrimeCore_le_Q [Finite G] :
    (CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))).map
        (centralizer (D.D1 : Set G)).subtype ≤ D.Q :=
  Subgroup.map_mono (f := (centralizer (D.D1 : Set G)).subtype)
    (CFSG.ABGLocalTools.le_oddCore_of_normal CFSG.pPrimeCore_normal
      (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card))

private lemma mem_pPrimeCore_of_odd_order [Finite G]
    {y : ↥(centralizer (D.D1 : Set G))} (hy : Odd (orderOf y)) :
    y ∈ CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G)) := by
  have hq2 : IsPGroup 2 (↥(centralizer (D.D1 : Set G)) ⧸
      CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))) :=
    IsPGroup.of_card (n := 2) (by rw [card_quot_pPrimeCore D]; norm_num)
  by_contra hcon
  have hne : QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))) y ≠ 1 := by
    intro h
    exact hcon ((QuotientGroup.eq_one_iff y).mp h)
  have h2dvd : 2 ∣ orderOf
      (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))) y) :=
    hq2.dvd_orderOf hne
  have hodd : Odd (orderOf
      (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))) y)) :=
    Odd.of_dvd_nat hy (orderOf_map_dvd _ y)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

private lemma odd_orderOf_of_card_odd {H : Subgroup G} (h : Odd (Nat.card H)) {x : G}
    (hx : x ∈ H) : Odd (orderOf x) :=
  Odd.of_dvd_nat h (Subgroup.orderOf_dvd_natCard H hx)

private lemma mem_Q_of_odd_order [Finite G] {x : G}
    (hx : x ∈ centralizer (D.D1 : Set G)) (hxodd : Odd (orderOf x)) : x ∈ D.Q := by
  refine pPrimeCore_le_Q D (Subgroup.mem_map.mpr
    ⟨⟨x, hx⟩, mem_pPrimeCore_of_odd_order D ?_, rfl⟩)
  simpa using hxodd

private lemma R_le_Q [Finite G] : D.R ≤ D.Q := fun x hx =>
  mem_Q_of_odd_order D (R_le_centralizer D hx)
    (odd_orderOf_of_card_odd (by rw [card_R D]; norm_num) hx)

private lemma D1_le_Q [Finite G] : D.D1 ≤ D.Q := fun x hx =>
  mem_Q_of_odd_order D (R_le_centralizer D (D1_le_R D hx))
    (odd_orderOf_of_card_odd (by rw [card_R D]; norm_num) (D1_le_R D hx))

private lemma map_R_le_Q [Finite G] :
    D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤ D.Q := fun x hx =>
  mem_Q_of_odd_order D (map_conj_le_centralizer D D.outer.y_mem_normalizer hx)
    (odd_orderOf_of_card_odd (by rw [card_map_R D]; norm_num) hx)

private lemma odd_dvd_of_dvd_four_mul {n m : ℕ} (hn : Odd n) (h : n ∣ 4 * m) : n ∣ m := by
  have hcop : Nat.Coprime n 4 := by
    have h2 : Nat.Coprime n 2 := (Nat.coprime_two_left.mpr hn).symm
    simpa using h2.pow_right 2
  exact hcop.dvd_mul_left.mp h

private lemma card_inf_centralizer_t [Finite G] :
    Nat.card ↥(D.Q ⊓ centralizer {D.t}) = 25 := by
  have hle : D.Q ⊓ centralizer {D.t} ≤ D.R ⊔ closure {D.t, D.u} := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hCt, -, -⟩ := D.diagonal_unipotent_local_data
    rw [← hCt]
    exact le_inf (inf_le_left.trans D.Q_le_centralizer) inf_le_right
  have hdvd : Nat.card ↥(D.Q ⊓ centralizer {D.t}) ∣ 100 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [card_sup_R_closure_t_u D] at h
  have hodd : Odd (Nat.card ↥(D.Q ⊓ centralizer {D.t})) :=
    Odd.of_dvd_nat D.odd_card_Q (Subgroup.card_dvd_of_le inf_le_left)
  have hdvd25 : Nat.card ↥(D.Q ⊓ centralizer {D.t}) ∣ 25 :=
    odd_dvd_of_dvd_four_mul hodd (by simpa using hdvd)
  have hle25 : Nat.card ↥(D.Q ⊓ centralizer {D.t}) ≤ 25 :=
    Nat.le_of_dvd (by norm_num) hdvd25
  have hge : 25 ≤ Nat.card ↥(D.Q ⊓ centralizer {D.t}) := by
    have h2 : D.R ≤ D.Q ⊓ centralizer {D.t} := le_inf (R_le_Q D) (R_le_centralizer_t D)
    have h3 := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h2)
    rwa [card_R D] at h3
  omega

private lemma card_inf_centralizer_u [Finite G] :
    Nat.card ↥(D.Q ⊓ centralizer {D.u}) = 5 := by
  have hle : D.Q ⊓ centralizer {D.u} ≤ D.D1 ⊔ closure {D.t, D.u} := by
    obtain ⟨-, -, -, -, -, -, -, -, hCu, -, -, -⟩ := D.diagonal_unipotent_local_data
    rw [← hCu]
    exact le_inf (inf_le_left.trans D.Q_le_centralizer) inf_le_right
  have hdvd : Nat.card ↥(D.Q ⊓ centralizer {D.u}) ∣ 20 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [card_sup_D1_closure_t_u D] at h
  have hodd : Odd (Nat.card ↥(D.Q ⊓ centralizer {D.u})) :=
    Odd.of_dvd_nat D.odd_card_Q (Subgroup.card_dvd_of_le inf_le_left)
  have hdvd5 : Nat.card ↥(D.Q ⊓ centralizer {D.u}) ∣ 5 :=
    odd_dvd_of_dvd_four_mul hodd (by simpa using hdvd)
  have hle5 : Nat.card ↥(D.Q ⊓ centralizer {D.u}) ≤ 5 :=
    Nat.le_of_dvd (by norm_num) hdvd5
  have hge : 5 ≤ Nat.card ↥(D.Q ⊓ centralizer {D.u}) := by
    have h2 : D.D1 ≤ D.Q ⊓ centralizer {D.u} := le_inf (D1_le_Q D) (D1_le_centralizer_u D)
    have h3 := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h2)
    rwa [D.card_D1] at h3
  omega

private lemma card_inf_centralizer_tu [Finite G] :
    Nat.card ↥(D.Q ⊓ centralizer {D.t * D.u}) = 25 := by
  have hle : D.Q ⊓ centralizer {D.t * D.u} ≤
      D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ⊔ closure {D.t, D.u} := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hCtu, -⟩ := D.diagonal_unipotent_local_data
    rw [← hCtu]
    exact le_inf (inf_le_left.trans D.Q_le_centralizer) inf_le_right
  have hdvd : Nat.card ↥(D.Q ⊓ centralizer {D.t * D.u}) ∣ 100 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [card_sup_map_R_closure_t_u D] at h
  have hodd : Odd (Nat.card ↥(D.Q ⊓ centralizer {D.t * D.u})) :=
    Odd.of_dvd_nat D.odd_card_Q (Subgroup.card_dvd_of_le inf_le_left)
  have hdvd25 : Nat.card ↥(D.Q ⊓ centralizer {D.t * D.u}) ∣ 25 :=
    odd_dvd_of_dvd_four_mul hodd (by simpa using hdvd)
  have hle25 : Nat.card ↥(D.Q ⊓ centralizer {D.t * D.u}) ≤ 25 :=
    Nat.le_of_dvd (by norm_num) hdvd25
  have hge : 25 ≤ Nat.card ↥(D.Q ⊓ centralizer {D.t * D.u}) := by
    have h2 : D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤ D.Q ⊓ centralizer {D.t * D.u} :=
      le_inf (map_R_le_Q D) (map_conj_le_centralizer_tu D)
    have h3 := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h2)
    rwa [card_map_R D] at h3
  omega

private lemma Q_inf_centralizer_t [Finite G] : D.Q ⊓ centralizer {D.t} = D.R :=
  (Subgroup.eq_of_le_of_card_ge (le_inf (R_le_Q D) (R_le_centralizer_t D))
    (by rw [card_inf_centralizer_t D, card_R D])).symm

private lemma Q_inf_centralizer_u [Finite G] : D.Q ⊓ centralizer {D.u} = D.D1 :=
  (Subgroup.eq_of_le_of_card_ge (le_inf (D1_le_Q D) (D1_le_centralizer_u D))
    (by rw [card_inf_centralizer_u D, D.card_D1])).symm

private lemma Q_inf_centralizer_tu [Finite G] :
    D.Q ⊓ centralizer {D.t * D.u} = D.R.map (MulAut.conj D.y⁻¹).toMonoidHom :=
  (Subgroup.eq_of_le_of_card_ge
    (le_inf (map_R_le_Q D) (map_conj_le_centralizer_tu D))
    (by rw [card_inf_centralizer_tu D, card_map_R D])).symm

private lemma inf_centralizer_closure_t_u [Finite G] :
    D.Q ⊓ centralizer ((closure {D.t, D.u} : Subgroup G) : Set G) = D.D1 := by
  rw [centralizer_closure_t_u D]
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxQ, hxAB⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨-, hxB⟩ := Subgroup.mem_inf.mp hxAB
    have h1 : x ∈ D.Q ⊓ centralizer {D.u} := Subgroup.mem_inf.mpr ⟨hxQ, hxB⟩
    rwa [Q_inf_centralizer_u D] at h1
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨D1_le_Q D hx,
      Subgroup.mem_inf.mpr ⟨R_le_centralizer_t D (D1_le_R D hx), D1_le_centralizer_u D hx⟩⟩

private lemma closure_t_u_le_normalizer_Q :
    closure {D.t, D.u} ≤ normalizer (D.Q : Set G) := by
  have hsub : D.Q.subgroupOf (centralizer (D.D1 : Set G)) =
      CFSG.oddCore ↥(centralizer (D.D1 : Set G)) := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr D.Q_le_centralizer]
    rfl
  have hnormal : (D.Q.subgroupOf (centralizer (D.D1 : Set G))).Normal := by
    rw [hsub]
    exact CFSG.oddCore_normal _
  exact (closure_t_u_le_centralizer D).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer D.Q_le_centralizer).mp hnormal)

private lemma card_Q [Finite G] : Nat.card D.Q = 125 := by
  haveI : IsKleinFour ↥(closure {D.t, D.u}) := isKleinFour_closure_t_u D
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq
    (T := closure {D.t, D.u}) (K := D.Q) D.odd_card_Q (closure_t_u_le_normalizer_Q D)
    (subset_closure (by simp)) (subset_closure (by simp)) (t_ne_one D) (u_ne_one D)
    D.u_ne_t.symm
  rw [inf_centralizer_closure_t_u D, Q_inf_centralizer_t D, Q_inf_centralizer_u D,
    D.card_D1, card_R D, card_inf_centralizer_tu D] at hBW
  norm_num at hBW
  omega

private lemma relIndex_Q [Finite G] : D.Q.relIndex (centralizer (D.D1 : Set G)) = 4 := by
  have hmul := Subgroup.relIndex_mul_relIndex (H := (CFSG.pPrimeCore 2
    ↥(centralizer (D.D1 : Set G))).map (centralizer (D.D1 : Set G)).subtype)
    (K := D.Q) (L := centralizer (D.D1 : Set G)) (pPrimeCore_le_Q D) D.Q_le_centralizer
  have hdvd : D.Q.relIndex (centralizer (D.D1 : Set G)) ∣ 4 := by
    have h : D.Q.relIndex (centralizer (D.D1 : Set G)) ∣
        ((CFSG.pPrimeCore 2 ↥(centralizer (D.D1 : Set G))).map
          (centralizer (D.D1 : Set G)).subtype).relIndex D.Q *
        D.Q.relIndex (centralizer (D.D1 : Set G)) := dvd_mul_left _ _
    rwa [hmul, relIndex_pPrimeCore D] at h
  have hQ_inf_F : D.Q ⊓ closure {D.t, D.u} = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [card_Q D, card_closure_t_u D]
    norm_num
  have hge : 4 ≤ D.Q.relIndex (centralizer (D.D1 : Set G)) := by
    have hcard : Nat.card (D.Q ⊔ closure {D.t, D.u} : Subgroup G) = Nat.card D.Q * 4 := by
      rw [CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot (closure_t_u_le_normalizer_Q D) hQ_inf_F,
        card_closure_t_u D]
    have hle : Nat.card D.Q * 4 ≤ Nat.card (centralizer (D.D1 : Set G)) := by
      rw [← hcard]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le
        (sup_le D.Q_le_centralizer (closure_t_u_le_centralizer D)))
    have h1 : D.Q.relIndex (centralizer (D.D1 : Set G)) * Nat.card D.Q =
        Nat.card (centralizer (D.D1 : Set G)) := by
      have h := Subgroup.relIndex_mul_card D.Q (centralizer (D.D1 : Set G))
      rwa [inf_eq_left.mpr D.Q_le_centralizer] at h
    rw [← h1] at hle
    exact Nat.le_of_mul_le_mul_right (by rw [mul_comm 4]; exact hle) Nat.card_pos
  exact le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hge

private lemma D1_mul_R [Finite G] : (D.D1 : Set G) * (D.R : Set G) = (D.R : Set G) := by
  ext x
  constructor
  · rintro ⟨d, hd, r, hr, rfl⟩
    exact D.R.mul_mem (D1_le_R D hd) hr
  · intro hx
    exact ⟨1, one_mem _, x, hx, one_mul x⟩

private lemma t_mul_u_ne_one [Finite G] : D.t * D.u ≠ 1 := by
  intro h
  have h1 : D.u = D.t := by
    calc D.u = D.t⁻¹ * (D.t * D.u) := by group
      _ = D.t⁻¹ * 1 := by rw [h]
      _ = D.t := by rw [D.t_inv, mul_one]
  exact D.u_ne_t h1

private lemma t_ne_t_mul_u [Finite G] : D.t ≠ D.t * D.u := by
  intro h
  have h1 : (1 : G) = D.u := by
    calc (1 : G) = D.t⁻¹ * D.t := by rw [inv_mul_cancel]
      _ = D.t⁻¹ * (D.t * D.u) := by rw [← h]
      _ = D.u := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  exact u_ne_one D h1.symm

private lemma u_ne_t_mul_u [Finite G] : D.u ≠ D.t * D.u := by
  intro h
  have h1 : D.t = 1 := by
    calc D.t = (D.t * D.u) * D.u⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = D.u * D.u⁻¹ := by rw [← h]
      _ = 1 := by rw [mul_inv_cancel]
  exact t_ne_one D h1

private lemma Q_eq_mul [Finite G] :
    (D.Q : Set G) = (D.R.map (MulAut.conj D.y⁻¹).toMonoidHom : Set G) * (D.R : Set G) := by
  haveI : IsKleinFour ↥(closure {D.t, D.u}) := isKleinFour_closure_t_u D
  have hprod := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers
    (T := closure {D.t, D.u}) (K := D.Q) D.odd_card_Q (closure_t_u_le_normalizer_Q D)
    (a₁ := D.t * D.u) (a₂ := D.u) (a₃ := D.t)
    (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
    (subset_closure (by simp)) (subset_closure (by simp))
    (t_mul_u_ne_one D) (u_ne_one D) (t_ne_one D)
    (u_ne_t_mul_u D).symm (t_ne_t_mul_u D).symm D.u_ne_t
  rw [hprod, Q_inf_centralizer_tu D, Q_inf_centralizer_u D, Q_inf_centralizer_t D]
  rw [mul_assoc, D1_mul_R D]

private lemma normalizer_D1_le_normalizer_Q [Finite G] :
    normalizer (D.D1 : Set G) ≤ normalizer (D.Q : Set G) := by
  intro g hg
  have hginv : g⁻¹ ∈ normalizer (D.D1 : Set G) := (normalizer (D.D1 : Set G)).inv_mem hg
  have key : ∀ h ∈ normalizer (D.D1 : Set G), ∀ y ∈ D.Q, h * y * h⁻¹ ∈ D.Q := by
    intro h hh y hy
    have hmem : h * y * h⁻¹ ∈ centralizer (D.D1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : h⁻¹ * d * h ∈ D.D1 := by
        have := (Subgroup.mem_normalizer_iff.mp ((normalizer (D.D1 : Set G)).inv_mem hh) d).mp hd
        simpa using this
      have hx' : (h⁻¹ * d * h) * y = y * (h⁻¹ * d * h) :=
        Subgroup.mem_centralizer_iff.mp (D.Q_le_centralizer hy) _ hd'
      calc d * (h * y * h⁻¹) = h * ((h⁻¹ * d * h) * y) * h⁻¹ := by group
        _ = h * (y * (h⁻¹ * d * h)) * h⁻¹ := by rw [hx']
        _ = (h * y * h⁻¹) * d := by group
    refine mem_Q_of_odd_order D hmem ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq (MulAut.conj h) y]
    exact odd_orderOf_of_card_odd (by rw [card_Q D]; norm_num) hy
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key g hg x, ?_⟩
  intro hx
  have h1 := key g⁻¹ hginv (g * x * g⁻¹) hx
  have h2 : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [h2] at h1

theorem odd_complement_of_diagonal_centralizer [Finite G] :
    Nat.card D.Q = 125 ∧ D.Q.relIndex (centralizer (D.D1 : Set G)) = 4 ∧
    (D.Q : Set G) = (D.R.map (MulAut.conj D.y⁻¹).toMonoidHom : Set G) * (D.R : Set G) ∧
    D.Q ⊓ centralizer {D.t} = D.R ∧ D.Q ⊓ centralizer {D.u} = D.D1 ∧
    D.Q ⊓ centralizer {D.t * D.u} = D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ∧
    normalizer (D.D1 : Set G) ≤ normalizer (D.Q : Set G) := by
  exact ⟨card_Q D, relIndex_Q D, Q_eq_mul D, Q_inf_centralizer_t D, Q_inf_centralizer_u D,
    Q_inf_centralizer_tu D, normalizer_D1_le_normalizer_Q D⟩

end CFSG.OddTranspositions.PartThree.Wong.RootData
