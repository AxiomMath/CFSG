module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin.A1b Subgroup
open scoped commutatorElement

structure FourFiveNMN {Q : Type} [Group Q] (N : Subgroup Q) : Prop where
  normal : N.Normal
  ne_bot : N ≠ ⊥
  minimal : ∀ M : Subgroup Q, M.Normal → M ≤ N → M = ⊥ ∨ M = N
  nonabelian : ¬ IsMulCommutative N

variable {Q : Type} [Group Q] [Finite Q]

private theorem fourFive_isMulCommutative_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsMulCommutative A) : IsMulCommutative B :=
  IsMulCommutative.of_comm fun a b => by
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, h.is_comm.comm a' b']

private theorem fourFive_open_isQuasisimple_of_simple_nonabelian {A : Type*} [Group A]
    [IsSimpleGroup A] (h : ¬ IsMulCommutative A) : CFSG.Open.IsQuasisimple A :=
  ⟨(TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative h).commutator_eq_top, by
    have hZ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative h
    exact MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot)⟩

private theorem fourFive_open_isQuasisimple_nontrivial {A : Type*} [Group A]
    (h : CFSG.Open.IsQuasisimple A) : Nontrivial A := by
  haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := h.2
  obtain ⟨a, b, hne⟩ := exists_pair_ne (A ⧸ Subgroup.center A)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun hxy => hne (by rw [hxy])⟩

private theorem fourFive_isQuasisimple_of_open {A : Type*} [Group A]
    (h : CFSG.Open.IsQuasisimple A) : CFSG.IsQuasisimple A := by
  refine ⟨Group.isPerfect_def.mpr h.1, h.2, ?_⟩
  by_contra hnab
  push Not at hnab
  have hle : commutator A ≤ Subgroup.center A := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center A)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hnab ((QuotientGroup.mk' (Subgroup.center A)) x), mul_inv_cancel_right, mul_inv_cancel]
  rw [h.1] at hle
  haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := h.2
  haveI : Subsingleton (A ⧸ Subgroup.center A) :=
    QuotientGroup.subsingleton_iff.mpr (top_le_iff.mp hle)
  exact not_subsingleton (A ⧸ Subgroup.center A) inferInstance

private theorem fourFive_map_conj_eq_of_normal {N : Subgroup Q} (hN : N.Normal) (t : Q) :
    N.map (MulAut.conj t).toMonoidHom = N := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hN.conj_mem y hy t
  · intro hx
    refine Subgroup.mem_map.mpr ⟨t⁻¹ * x * t, ?_, ?_⟩
    · simpa using hN.conj_mem x hx t⁻¹
    · change t * (t⁻¹ * x * t) * t⁻¹ = x
      group

private structure FourFiveData (N : Subgroup Q) where
  r : ℕ
  S : Fin r → Subgroup Q
  iSup_eq : (⨆ i, S i) = N
  le : ∀ i, S i ≤ N
  normal : ∀ i, ((S i).subgroupOf N).Normal
  simple : ∀ i, IsSimpleGroup ↥(S i)
  nonabelian : ∀ i, ¬ IsMulCommutative ↥(S i)
  commute : ∀ i j, i ≠ j → ∀ x y : Q, x ∈ S i → y ∈ S j → Commute x y

private theorem fourFive_factors_nonempty {N : Subgroup Q} (hN : FourFiveNMN N) :
    Nonempty (FourFiveData N) := by
  classical
  obtain ⟨r, S, _hr, hSN, hSsimple, hSconj, hSnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hN.normal hN.ne_bot hN.minimal
  have hcomm : Pairwise (fun i j => ∀ x y : Q, x ∈ S i → y ∈ S j → Commute x y) := by
    intro i j hij x y hx hy
    have hx' : (e.toMonoidHom (Pi.mulSingle i ⟨x, hx⟩) : Q) = x := by
      have h := he i (Pi.mulSingle i ⟨x, hx⟩)
        fun k hk => Pi.mulSingle_eq_of_ne (M := fun j => ↥(S j)) hk ⟨x, hx⟩
      simpa using h
    have hy' : (e.toMonoidHom (Pi.mulSingle j ⟨y, hy⟩) : Q) = y := by
      have h := he j (Pi.mulSingle j ⟨y, hy⟩)
        fun k hk => Pi.mulSingle_eq_of_ne (M := fun j => ↥(S j)) hk ⟨y, hy⟩
      simpa using h
    have h1 : Commute (e.toMonoidHom (Pi.mulSingle i ⟨x, hx⟩))
        (e.toMonoidHom (Pi.mulSingle j ⟨y, hy⟩)) :=
      Commute.map (Pi.mulSingle_commute hij ⟨x, hx⟩ ⟨y, hy⟩) e.toMonoidHom
    have h2 := congrArg (fun z : ↥N => (z : Q)) h1
    simp only [Subgroup.coe_mul] at h2
    rwa [hx', hy'] at h2
  have hnonab : ∀ i, ¬ IsMulCommutative ↥(S i) := by
    by_contra h
    push Not at h
    obtain ⟨i₀, hi₀⟩ := h
    have hall : ∀ j, IsMulCommutative ↥(S j) := by
      intro j
      obtain ⟨g, hg⟩ := hSconj i₀ j
      rw [hg]
      exact fourFive_isMulCommutative_of_mulEquiv
        (Subgroup.equivMapOfInjective (S i₀) (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective) hi₀
    exact hN.nonabelian (IsMulCommutative.of_comm fun a b => by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      funext j
      exact (hall j).is_comm.comm (x j) (y j))
  have hiSup : (⨆ i, S i) = N := by
    have hh : Subgroup.noncommPiCoprod hcomm = N.subtype.comp e.toMonoidHom := by
      refine MonoidHom.pi_ext fun i a => ?_
      rw [MonoidHom.comp_apply, Subgroup.noncommPiCoprod_mulSingle]
      simpa using (he i (Pi.mulSingle i a)
        fun k hk => Pi.mulSingle_eq_of_ne (M := fun j => ↥(S j)) hk a).symm
    have hrange : (N.subtype.comp e.toMonoidHom).range = N := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, rfl⟩
        exact (e x).2
      · intro n hn
        exact ⟨e.symm ⟨n, hn⟩, by simp⟩
    rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm), hh, hrange]
  exact ⟨⟨r, S, hiSup, hSN, hSnorm, hSsimple, hnonab, hcomm⟩⟩

private noncomputable def fourFive_factors {N : Subgroup Q} (hN : FourFiveNMN N) :
    FourFiveData N :=
  Classical.choice (fourFive_factors_nonempty hN)

private theorem fourFive_component_eq_factor {N : Subgroup Q} (hN : FourFiveNMN N)
    (D : FourFiveData N) {J : Subgroup Q} (hJ : IsComponentOf J N) : ∃ i, J = D.S i := by
  classical
  have hJ'q : CFSG.Open.IsQuasisimple ↥(J.subgroupOf N) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.2
  have hJ'comp : CFSG.IsComponent (J.subgroupOf N) :=
    ⟨fourFive_isQuasisimple_of_open hJ'q, CFSG.Open.IsSubnormal.subgroupOf hJ.2.1⟩
  have hdich : ∀ i, (J.subgroupOf N) ≤ (D.S i).subgroupOf N ∨
      ⁅J.subgroupOf N, (D.S i).subgroupOf N⁆ = ⊥ :=
    fun i => CFSG.LocalCores.component_normal_subgroup hJ'comp (D.normal i)
  by_cases hcase : ∃ i, (J.subgroupOf N) ≤ (D.S i).subgroupOf N
  · obtain ⟨i, hi⟩ := hcase
    refine ⟨i, ?_⟩
    have hJSi : J ≤ D.S i := CFSG.LocalCores.le_of_subgroupOf_le hJ.1 hi
    have hsub : CFSG.Open.IsSubnormal J (D.S i) := by
      have h := CFSG.Open.IsSubnormal.inf_of_le hJ.2.1 (D.le i)
      rwa [inf_eq_left.mpr hJSi] at h
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub (D.simple i) with h | h
    · exfalso
      haveI : Nontrivial ↥J := fourFive_open_isQuasisimple_nontrivial hJ.2.2
      exact not_subsingleton ↥J (by rw [h]; infer_instance)
    · exact h
  · exfalso
    push Not at hcase
    have hcommJ : ∀ i, ⁅J, D.S i⁆ = ⊥ := by
      intro i
      have h := (hdich i).resolve_left (hcase i)
      have h2 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf (K := J) (H := D.S i)
        (L := N) hJ.1 h
      rwa [inf_eq_left.mpr (D.le i)] at h2
    have hcent : J ≤ Subgroup.centralizer (N : Set Q) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      rw [← D.iSup_eq, Subgroup.iSup_eq_closure] at hn
      induction hn using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommJ i) hj) x hxi
      | one => exact Commute.one_left j
      | mul x y _ _ ihx ihy => exact Commute.mul_left ihx ihy
      | inv x _ ih => exact Commute.inv_left ih
    have hcommJself : IsMulCommutative ↥J :=
      IsMulCommutative.of_comm fun x y => by
        have h := Subgroup.mem_centralizer_iff.mp (hcent x.2) (y : Q) (hJ.1 y.2)
        exact Subtype.ext h.symm
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
    have hcenter : Subgroup.center ↥J = ⊤ := Subgroup.center_eq_top_iff.mpr hcommJself
    haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) :=
      QuotientGroup.subsingleton_iff.mpr hcenter
    exact not_subsingleton (↥J ⧸ Subgroup.center ↥J) inferInstance

theorem fourFive_nmn_component_simple {N J : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) : IsSimpleGroup ↥J ∧ ¬ IsMulCommutative ↥J := by
  let D := fourFive_factors hN
  obtain ⟨i, hi⟩ := fourFive_component_eq_factor hN D hJ
  rw [hi]
  exact ⟨D.simple i, D.nonabelian i⟩

theorem fourFive_nmn_components_sup {N : Subgroup Q} (hN : FourFiveNMN N) :
    (⨆ (J : Subgroup Q) (_ : IsComponentOf J N), J) = N := by
  let D := fourFive_factors hN
  refine le_antisymm (iSup₂_le fun J hJ => hJ.1) ?_
  have hle : (⨆ i, D.S i) ≤ ⨆ (J) (_ : IsComponentOf J N), J := by
    refine iSup_le fun i => ?_
    haveI : IsSimpleGroup ↥(D.S i) := D.simple i
    have hcomp : IsComponentOf (D.S i) N :=
      ⟨D.le i, CFSG.Open.IsSubnormal.step (D.le i) (D.normal i) (CFSG.Open.IsSubnormal.refl N),
        fourFive_open_isQuasisimple_of_simple_nonabelian (D.nonabelian i)⟩
    exact le_iSup₂ (f := fun J (_ : IsComponentOf J N) => J) (D.S i) hcomp
  rwa [D.iSup_eq] at hle

theorem fourFive_nmn_component_conj {N J : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) (t : Q) : IsComponentOf (conjSub t J) N := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_conjSub_iff] at hx
    simpa [mul_assoc] using hN.normal.conj_mem (t⁻¹ * x * t) (hJ.1 hx) t
  · have h := CFSG.Open.IsSubnormal.map (MulAut.conj t).toMonoidHom hJ.2.1
    rw [fourFive_map_conj_eq_of_normal hN.normal t] at h
    simpa [conjSub] using h
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective J (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective).symm hJ.2.2

theorem fourFive_nmn_components_commute {N J J' : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) (hJ' : IsComponentOf J' N) (hne : J ≠ J') : ⁅J, J'⁆ = ⊥ := by
  let D := fourFive_factors hN
  obtain ⟨i, hi⟩ := fourFive_component_eq_factor hN D hJ
  obtain ⟨k, hk⟩ := fourFive_component_eq_factor hN D hJ'
  have hik : i ≠ k := by rintro rfl; exact hne (hi.trans hk.symm)
  rw [hi, hk, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (D.commute i k hik x y hx hy).symm

end CFSG.LocalAnalysis.WeakClosure81
