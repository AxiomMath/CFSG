module

public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEFixedResidual
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

@[expose] noncomputable def thetaSupplementAt (p : ℕ) (L : Subgroup G) (b : G) : Subgroup G :=
  (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G))

theorem map_inSubgroup_perfectResidual_of_injective {G' : Type*} [Group G'] [Finite G]
    [Finite G'] (f : G →* G') (hf : Function.Injective f) (X : Subgroup G) :
    (inSubgroup perfectResidual X).map f = inSubgroup perfectResidual (X.map f) := by
  have h : (perfectResidual X).map (X.equivMapOfInjective f hf).toMonoidHom =
      perfectResidual (X.map f) :=
    RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq _
      (X.equivMapOfInjective f hf).surjective
  rw [inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem normalizer_le_normalizer_inSubgroup_perfectResidual [Finite G] (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual X : Set G) :=
  fun g hg => mem_normalizer_of_map_conj_eq (by
    rw [map_inSubgroup_perfectResidual_of_injective _ (MulAut.conj g).injective,
      map_conj_eq_of_mem_normalizer hg])

theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  mem_normalizer_of_map_conj_eq (by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB])

theorem isSolvable_and_not_dvd_sup [Finite G] {p : ℕ} (hp : p.Prime) {N T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hNs : Group.IsSolvable N)
    (hTs : Group.IsSolvable T) (hNp : ¬ p ∣ Nat.card N) (hTp : ¬ p ∣ Nat.card T) :
    Group.IsSolvable (N ⊔ T : Subgroup G) ∧ ¬ p ∣ Nat.card (N ⊔ T : Subgroup G) := by
  set W := N ⊔ T with hW
  have hNW : N ≤ W := le_sup_left
  have hTW : T ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hTN
  have : (N.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).mpr hWN
  set q := QuotientGroup.mk' (N.subgroupOf W)
  set φ : T →* W ⧸ N.subgroupOf W := q.comp (Subgroup.inclusion hTW)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hw : (w : G) ∈ (N : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N T hTN]
      exact w.2
    obtain ⟨n, hn, t, ht, hnt⟩ := hw
    refine ⟨⟨t, ht⟩, ?_⟩
    change q (Subgroup.inclusion hTW ⟨t, ht⟩) = q w
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change ((Subgroup.inclusion hTW ⟨t, ht⟩)⁻¹ * w : W) ∈ N.subgroupOf W
    rw [Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hTW ⟨t, ht⟩)⁻¹ * w : W).val = t⁻¹ * n * t := by
      change t⁻¹ * (w : G) = _
      rw [← hnt, mul_assoc]
    rw [this]
    exact (Subgroup.mem_normalizer_iff''.mp (hTN ht) n).mp hn
  have hQs : Group.IsSolvable (W ⧸ N.subgroupOf W) := Group.isSolvable_of_surjective hφ
  refine ⟨Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNW) q fun x hx => ?_, ?_⟩
  · rw [QuotientGroup.ker_mk'] at hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro h
    have hcard := Subgroup.card_mul_index (N.subgroupOf W)
    have h1 : Nat.card (N.subgroupOf W) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
    have h2 : (N.subgroupOf W).index ∣ Nat.card T := by
      have := Subgroup.card_map_dvd (⊤ : Subgroup T) φ
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top,
        Subgroup.card_top] at this
      exact this
    rw [← hcard, h1] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · exact hNp h'
    · exact hTp (h'.trans h2)

theorem hyperplane_fixed_residual_common_theta_supplement [Finite G] {p : ℕ} (hp : p.Prime)
    {D L : Subgroup G} (hDp : IsPGroup p D) (hDab : IsMulCommutative D)
    (hDL : D ≤ Subgroup.normalizer (L : Set G))
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hLD : ⁅L, D⁆ ≤ inSubgroup (aschbacherSolvableCore p) L) :
    L = inSubgroup (aschbacherSolvableCore p) L ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) ∧
      ∀ b ∈ D,
        (thetaSupplementAt p L b : Set G) =
            ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) *
              (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) :
                Set G) ∧
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) ≤
            L ⊓ inSubgroup perfectResidual (thetaSupplementAt p L b) ∧
          inSubgroup perfectResidual (thetaSupplementAt p L b) =
            inSubgroup (aschbacherSolvableCore p)
                (inSubgroup perfectResidual (thetaSupplementAt p L b)) ⊔
              inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) ∧
          D ≤ Subgroup.normalizer
            (inSubgroup perfectResidual (thetaSupplementAt p L b) : Set G) ∧
          ⁅inSubgroup perfectResidual (thetaSupplementAt p L b), D⁆ ≤
            inSubgroup (aschbacherSolvableCore p)
              (inSubgroup perfectResidual (thetaSupplementAt p L b)) := by
  set ΘL := inSubgroup (aschbacherSolvableCore p) L with hΘL
  set P := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)) with hP
  have hPX : P ≤ L ⊓ Subgroup.centralizer (D : Set G) := Subgroup.map_subtype_le _
  have hPL : P ≤ L := hPX.trans inf_le_left
  have hPD : P ≤ Subgroup.centralizer (D : Set G) := hPX.trans inf_le_right
  have hPperf : Group.IsPerfect P := by
    set X := L ⊓ Subgroup.centralizer (D : Set G)
    obtain ⟨-, -, hperf, -⟩ := perfect_residual_characterization (G := X)
    have := hperf
    exact Group.IsPerfect.ofSurjective
      (f := ((perfectResidual X).equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom)
      ((perfectResidual X).equivMapOfInjective X.subtype X.subtype_injective).surjective
  obtain ⟨hθLs, -, hθLp, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  have hΘLL : ΘL ≤ L := Subgroup.map_subtype_le _
  have hLΘL : L ≤ Subgroup.normalizer (ΘL : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p L)
  have hΘLs : Group.IsSolvable ΘL := by
    have := hθLs
    exact Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _)
  have hΘLp : ¬ p ∣ Nat.card ΘL := by
    rwa [hΘL, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  have hsupL : L = ΘL ⊔ P := by
    let _ : MulDistribMulAction D L :=
      MulDistribMulAction.compHom L (L.normalizerMonoidHom.comp (Subgroup.inclusion hDL))
    have hsmul : ∀ (d : D) (l : L), ((d • l : L) : G) = d * l * (d : G)⁻¹ := fun _ _ => rfl
    have htriv : ∀ (d : D) (l : L), ((d • l : L) : L ⧸ aschbacherSolvableCore p L) =
        (l : L ⧸ aschbacherSolvableCore p L) := by
      intro d l
      rw [QuotientGroup.eq]
      have h1 : ⁅(d : G), ((l⁻¹ : L) : G)⁆ ∈ ⁅L, D⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator d.2 (l⁻¹).2
      obtain ⟨y, hy, hyeq⟩ := hLD h1
      have hy' : y = (d • l)⁻¹ * l := by
        apply Subtype.ext
        have hyeq' : (y : G) = ⁅(d : G), ((l⁻¹ : L) : G)⁆ := hyeq
        rw [hyeq', commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
        group
      rw [← hy']
      exact hy
    obtain ⟨hsup, -⟩ := theta_component_trivial_quotient_action_fixed_residual hp hLq hDp htriv
    set Cfix := fixedPointSubgroup D L
    have hCfix : Cfix.map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
        have h := congrArg Subtype.val (hl ⟨d, hd⟩)
        rw [hsmul] at h
        calc d * (l : G) = d * l * d⁻¹ * d := by group
          _ = l * d := by rw [h]
      · rintro ⟨hxL, hxC⟩
        refine ⟨⟨x, hxL⟩, fun d => Subtype.ext ?_, rfl⟩
        rw [hsmul]
        have h := Subgroup.mem_centralizer_iff.mp hxC d d.2
        calc (d : G) * x * (d : G)⁻¹ = x * d * (d : G)⁻¹ := by rw [h]
          _ = x := by group
    have h := congrArg (Subgroup.map L.subtype) hsup
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      map_inSubgroup_perfectResidual_of_injective _ L.subtype_injective, hCfix] at h
    exact h.symm
  refine ⟨hsupL, fun b hb => ?_⟩
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set Nb := inSubgroup (aschbacherSolvableCore p) Cb with hNb
  set CLb := L ⊓ Cb with hCLb
  set Ub := thetaSupplementAt p L b with hUb
  set Lb := inSubgroup perfectResidual Ub with hLb
  have hUbdef : Ub = CLb ⊔ Nb := rfl
  have hDCb : D ≤ Cb := fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((IsMulCommutative.is_comm (M := D)).comm ⟨d, hd⟩ ⟨b, hb⟩))
  have hPCb : P ≤ Cb := hPD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hNbCb : Nb ≤ Cb := Subgroup.map_subtype_le _
  have hCbNb : Cb ≤ Subgroup.normalizer (Nb : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p Cb)
  obtain ⟨hθbs, -, hθbp, -⟩ := solvable_prime_complement_core_characterization (H := Cb) hp
  have hNbs : Group.IsSolvable Nb := by
    have := hθbs
    exact Group.isSolvable_of_surjective (Cb.subtype.subgroupMap_surjective _)
  have hNbp : ¬ p ∣ Nat.card Nb := by
    rwa [hNb, inSubgroup, Subgroup.card_map_of_injective Cb.subtype_injective]
  have hUbset : (Ub : Set G) = (CLb : Set G) * (Nb : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right CLb Nb (inf_le_right.trans hCbNb)
  set T := ΘL ⊓ Cb with hT
  have hCLbTP : CLb ≤ T ⊔ P := by
    intro x hx
    have hxL : x ∈ (ΘL : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left ΘL P (hPL.trans hLΘL), ← hsupL]
      exact hx.1
    obtain ⟨t, ht, q, hq, rfl⟩ := hxL
    have htC : t ∈ Cb := by
      have := Cb.mul_mem hx.2 (Cb.inv_mem (hPCb hq))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨ht, htC⟩ hq
  set V := Nb ⊔ T with hV
  have hTNb : T ≤ Subgroup.normalizer (Nb : Set G) := inf_le_right.trans hCbNb
  have hTs : Group.IsSolvable T := by
    have := hΘLs
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hTp : ¬ p ∣ Nat.card T := fun h => hΘLp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨hVs, hVp⟩ := isSolvable_and_not_dvd_sup hp hTNb hNbs hTs hNbp hTp
  have hCLbV : CLb ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_sup (hCbNb hg.2) (mem_normalizer_inf (hLΘL hg.1) (Subgroup.le_normalizer hg.2))
  have hUbV : Ub ≤ Subgroup.normalizer (V : Set G) :=
    sup_le hCLbV ((le_sup_left : Nb ≤ V).trans Subgroup.le_normalizer)
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    hCLbV ⟨hPL hg, hPCb hg⟩
  have hUbVP : Ub ≤ V ⊔ P :=
    sup_le (hCLbTP.trans (sup_le_sup_right le_sup_right P)) (le_sup_left.trans le_sup_left)
  have hPUb : P ≤ Ub := fun x hx => Subgroup.mem_sup_left ⟨hPL hx, hPCb hx⟩
  have hPLb : P ≤ Lb := by
    have hperf : Group.IsPerfect (P.subgroupOf Ub) := by
      have := hPperf
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hPUb).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPUb).symm.surjective
    have h := (perfect_residual_transport (MonoidHom.id Ub)).2.2 _ hperf
    intro x hx
    exact ⟨⟨x, hPUb hx⟩, h hx, rfl⟩
  have hLbUb : Lb ≤ Ub := Subgroup.map_subtype_le _
  have hLbV : Lb ⊓ V ≤ inSubgroup (aschbacherSolvableCore p) Lb := by
    have hmax := (solvable_prime_complement_core_characterization (H := Lb) hp).2.2.2.1
    have hn : ((Lb ⊓ V).subgroupOf Lb).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun g hg =>
        mem_normalizer_inf (Subgroup.le_normalizer hg) (hUbV (hLbUb hg))
    have hs : Group.IsSolvable ((Lb ⊓ V).subgroupOf Lb) := by
      have := hVs
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion (inf_le_right : Lb ⊓ V ≤ V)).comp
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : Lb ⊓ V ≤ Lb)).toMonoidHom)
        ((Subgroup.inclusion_injective (inf_le_right : Lb ⊓ V ≤ V)).comp
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : Lb ⊓ V ≤ Lb)).injective)
    have hpd : ¬ p ∣ Nat.card ((Lb ⊓ V).subgroupOf Lb) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Lb ⊓ V ≤ Lb)).toEquiv]
      exact fun h => hVp (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    have h := hmax _ hn hs hpd
    intro x hx
    exact ⟨⟨x, hx.1⟩, h hx, rfl⟩
  have hLbsup : Lb = inSubgroup (aschbacherSolvableCore p) Lb ⊔ P := by
    apply le_antisymm
    · intro x hx
      have hxVP : x ∈ (V : Set G) * (P : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left V P hPV]
        exact hUbVP (hLbUb hx)
      obtain ⟨v, hv, q, hq, rfl⟩ := hxVP
      have hvLb : v ∈ Lb := by
        have := Lb.mul_mem hx (Lb.inv_mem (hPLb hq))
        simpa using this
      exact Subgroup.mul_mem_sup (hLbV ⟨hvLb, hv⟩) hq
    · exact sup_le (Subgroup.map_subtype_le _) hPLb
  have hDLb : D ≤ Subgroup.normalizer (Lb : Set G) := by
    intro d hd
    have hdCLb : d ∈ Subgroup.normalizer (CLb : Set G) :=
      mem_normalizer_inf (hDL hd) (Subgroup.le_normalizer (hDCb hd))
    have hdNb : d ∈ Subgroup.normalizer (Nb : Set G) := hCbNb (hDCb hd)
    exact normalizer_le_normalizer_inSubgroup_perfectResidual Ub (mem_normalizer_sup hdCLb hdNb)
  have hcomm : ⁅Lb, D⁆ ≤ inSubgroup (aschbacherSolvableCore p) Lb := by
    rw [Subgroup.commutator_le]
    intro x hx d hd
    set ΘLb := inSubgroup (aschbacherSolvableCore p) Lb
    have hdΘ : d ∈ Subgroup.normalizer (ΘLb : Set G) :=
      normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p Lb (hDLb hd)
    have hLbΘ : Lb ≤ Subgroup.normalizer (ΘLb : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p Lb)
    have hxs : x ∈ (ΘLb : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left ΘLb P (hPLb.trans hLbΘ), ← hLbsup]
      exact hx
    obtain ⟨t, ht, q, hq, rfl⟩ := hxs
    have hqd : q * d = d * q := (Subgroup.mem_centralizer_iff.mp (hPD hq) d hd).symm
    have hdt : d * t⁻¹ * d⁻¹ ∈ ΘLb := (Subgroup.mem_normalizer_iff.mp hdΘ t⁻¹).mp (inv_mem ht)
    have heq : ⁅t * q, d⁆ = t * (d * t⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]
      calc t * q * d * (t * q)⁻¹ * d⁻¹ = t * (q * d) * q⁻¹ * t⁻¹ * d⁻¹ := by group
        _ = t * (d * q) * q⁻¹ * t⁻¹ * d⁻¹ := by rw [hqd]
        _ = t * (d * t⁻¹ * d⁻¹) := by group
    rw [heq]
    exact mul_mem ht hdt
  exact ⟨hUbset, le_inf (hPL) hPLb, hLbsup, hDLb, hcomm⟩

end CFSG.RankThree.GroupTheory.SteinbergBY
