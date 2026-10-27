module

public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofSL34
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofLeviMat
import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.PartTwo.Sec21.Item22L2

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item221ResProof.Levi

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree mem_slPi_true diagE blockHom
  thetaQuotMulAut)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

@[expose] noncomputable def phi (e : lBar L ≃* slPi true 3 (2 ^ 2) K) : ↥L →* GL (Fin 3) K :=
  (slPi true 3 (2 ^ 2) K).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))

omit [Finite G] [Finite K] in
theorem phi_apply (e : lBar L ≃* slPi true 3 (2 ^ 2) K) (x : ↥L) :
    phi e x = ((e (x : lBar L) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) := rfl

omit [Finite G] [Finite K] in
theorem phi_eq_one_iff (e : lBar L ≃* slPi true 3 (2 ^ 2) K) (x : ↥L) :
    phi e x = 1 ↔ x ∈ aschbacherSolvableCore 3 ↥L := by
  rw [phi_apply, ← QuotientGroup.eq_one_iff]
  constructor
  · intro h
    have h1 : e (x : lBar L) = 1 := Subtype.ext h
    rwa [MulEquiv.map_eq_one_iff] at h1
  · intro h
    rw [h, map_one]
    rfl

@[expose] noncomputable def tau (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (lBar L) :=
  thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩)

theorem tau_mem {A : Subgroup G} {b : G} (hbA : b ∈ A)
    (hb : b ∈ Subgroup.normalizer (L : Set G)) : tau b hb ∈ Sec4.autThetaQuot A L :=
  Sec4.mem_autThetaQuot_iff.mpr ⟨b, hb, hbA, rfl⟩

theorem tau_mk (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    tau b hb (x : lBar L) = ((L.normalizerMonoidHom ⟨b, hb⟩ x : ↥L) : lBar L) :=
  Sec4.thetaQuotMulAut_mk _ x

variable {e : lBar L ≃* slPi true 3 (2 ^ 2) K} {b : G}
  {hb : b ∈ Subgroup.normalizer (L : Set G)} {y : GL (Fin 3) K}

omit [Finite K] in
theorem phi_conj
    (hy : ∀ z : lBar L, ((e (tau b hb z) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) =
      y * (e z : GL (Fin 3) K) * y⁻¹) (x : ↥L) :
    phi e (L.normalizerMonoidHom ⟨b, hb⟩ x) = y * phi e x * y⁻¹ := by
  rw [phi_apply, phi_apply, ← hy, tau_mk]

omit [Finite K] in
theorem phi_mem_centralizer
    (hy : ∀ z : lBar L, ((e (tau b hb z) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) =
      y * (e z : GL (Fin 3) K) * y⁻¹) {x : ↥L} (hx : (x : G) * b = b * x) :
    phi e x ∈ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
  have hfix : L.normalizerMonoidHom ⟨b, hb⟩ x = x := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change b * x * b⁻¹ = x
    rw [← hx, mul_inv_cancel_right]
  have h := phi_conj hy x
  rw [hfix] at h
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc phi e x * y = y * phi e x * y⁻¹ * y := by rw [← h]
    _ = y * phi e x := by group

omit [Finite K] in
theorem mem_theta_of_commute
    (hy : ∀ z : lBar L, ((e (tau b hb z) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) =
      y * (e z : GL (Fin 3) K) * y⁻¹) {x : ↥L} (hx : phi e x * y = y * phi e x) :
    x⁻¹ * L.normalizerMonoidHom ⟨b, hb⟩ x ∈ aschbacherSolvableCore 3 ↥L := by
  rw [← phi_eq_one_iff e, map_mul, map_inv, phi_conj hy]
  calc (phi e x)⁻¹ * (y * phi e x * y⁻¹) = (phi e x)⁻¹ * (phi e x * y * y⁻¹) := by rw [hx]
    _ = 1 := by group

omit [Finite G] [Finite K] in
theorem commute_of_isPerfect (hT : aschbacherSolvableCore 3 ↥L ≤ Subgroup.center ↥L)
    {H : Subgroup ↥L} (hH : Group.IsPerfect ↥H)
    (hHb : ∀ x ∈ H, x⁻¹ * L.normalizerMonoidHom ⟨b, hb⟩ x ∈ aschbacherSolvableCore 3 ↥L) :
    ∀ x ∈ H, L.normalizerMonoidHom ⟨b, hb⟩ x = x := by
  set T := aschbacherSolvableCore 3 ↥L with hTdef
  set β := L.normalizerMonoidHom ⟨b, hb⟩ with hβ
  have hcen : ∀ t ∈ T, ∀ z : ↥L, t * z = z * t := fun t ht z =>
    (Subgroup.mem_center_iff.mp (hT ht) z).symm
  let f : ↥H →* ↥T :=
    { toFun := fun x => ⟨(x : ↥L)⁻¹ * β x, hHb x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        have hc := hcen _ (hHb x x.2) ((y : ↥L)⁻¹)
        calc (y : ↥L)⁻¹ * (x : ↥L)⁻¹ * (β x * β y) =
            (y : ↥L)⁻¹ * ((x : ↥L)⁻¹ * β x) * β y := by group
          _ = ((x : ↥L)⁻¹ * β x) * (y : ↥L)⁻¹ * β y := by rw [hc]
          _ = (x : ↥L)⁻¹ * β x * ((y : ↥L)⁻¹ * β y) := by group }
  have hTc : ∀ s t : ↥T, s * t = t * s := fun s t =>
    Subtype.ext (hcen _ s.2 t)
  have hrange : Group.IsPerfect f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have hsub := subsingleton_of_isPerfect_of_isSolvable hrange (Group.isSolvable_of_comm
    (fun a b => Subtype.ext (hTc a b)))
  intro x hx
  have h1 : f ⟨x, hx⟩ = 1 := by
    have := Subsingleton.elim (⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : f.range) 1
    exact congrArg Subtype.val this
  have h2 : x⁻¹ * β x = 1 := congrArg Subtype.val h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm

omit [Finite G] [Finite K] in
theorem phi_mem_slPi (x : ↥L) : phi e x ∈ slPi true 3 (2 ^ 2) K := (e (x : lBar L)).2

omit [Finite G] [Finite K] in
theorem exists_phi_eq {h : GL (Fin 3) K} (hh : h ∈ slPi true 3 (2 ^ 2) K) :
    ∃ x : ↥L, phi e x = h := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) (e.symm ⟨h, hh⟩)
  refine ⟨x, ?_⟩
  rw [phi_apply]
  change ((e (QuotientGroup.mk' _ x) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) = h
  rw [hx, MulEquiv.apply_symm_apply]

omit [Finite K] in
theorem le_centralizer_of_forall_commute (hq : IsQuasisimple L)
    (hy : ∀ z : lBar L, ((e (tau b hb z) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) =
      y * (e z : GL (Fin 3) K) * y⁻¹)
    (hyc : ∀ M : GL (Fin 3) K, M * y = y * M) : L ≤ Subgroup.centralizer ({b} : Set G) := by
  have hT := Item221Proof.theta_le_center hq
  have hperf : Group.IsPerfect ↥(⊤ : Subgroup ↥L) := Group.IsPerfect.top_iff.mpr hq.1
  have h := commute_of_isPerfect hT hperf (fun x _ => mem_theta_of_commute hy (hyc _))
  intro x hx
  have h1 := congrArg Subtype.val (h ⟨x, hx⟩ (Subgroup.mem_top _))
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  change b * x * b⁻¹ = x at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * b = b * x * b⁻¹ * b := by rw [h1]
    _ = b * x := by group

omit [Finite K] in
theorem perfectResidual_eq_bot_of_commute
    (hy : ∀ z : lBar L, ((e (tau b hb z) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) =
      y * (e z : GL (Fin 3) K) * y⁻¹)
    (habel : ∀ M ∈ slPi true 3 (2 ^ 2) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)),
      ∀ N ∈ slPi true 3 (2 ^ 2) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)),
        M * N = N * M) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {b}) = ⊥ := by
  set R := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {b}) with hRdef
  have hR : Group.IsPerfect ↥R := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hRC : R ≤ L ⊓ Subgroup.centralizer {b} := Subgroup.map_subtype_le _
  have hRL : R ≤ L := hRC.trans inf_le_left
  set R' := R.subgroupOf L with hR'
  have eR : ↥R' ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRL
  have hR'p : Group.IsPerfect ↥R' :=
    Group.IsPerfect.ofSurjective (f := eR.symm.toMonoidHom) eR.symm.surjective
  set f : ↥R' →* GL (Fin 3) K := (phi e).comp R'.subtype with hf
  have hfC : ∀ x : ↥R', f x ∈ slPi true 3 (2 ^ 2) K ⊓
      Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
    intro x
    refine ⟨phi_mem_slPi _, phi_mem_centralizer hy ?_⟩
    have hx : ((x : ↥L) : G) ∈ Subgroup.centralizer ({b} : Set G) :=
      (hRC (Subgroup.mem_subgroupOf.mp x.2)).2
    exact Subgroup.mem_centralizer_singleton_iff.mp hx
  have hrange : Group.IsPerfect f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have hsub := subsingleton_of_isPerfect_of_isSolvable hrange (Group.isSolvable_of_comm (by
    rintro ⟨_, x, rfl⟩ ⟨_, z, rfl⟩
    exact Subtype.ext (habel _ (hfC x) _ (hfC z))))
  have hker : ∀ x : ↥R', (x : ↥L) ∈ aschbacherSolvableCore 3 ↥L := by
    intro x
    rw [← phi_eq_one_iff e]
    have := Subsingleton.elim (⟨f x, ⟨x, rfl⟩⟩ : f.range) 1
    exact congrArg Subtype.val this
  have hRs : Group.IsSolvable ↥R' := by
    have hTs := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
    have hle : R' ≤ aschbacherSolvableCore 3 ↥L := fun x hx => hker ⟨x, hx⟩
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hsub' := subsingleton_of_isPerfect_of_isSolvable hR'p hRs
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨⟨x, hRL hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩ : ↥R') = 1 := Subsingleton.elim _ _
  exact (Subgroup.mem_bot).mpr (congrArg (fun z : ↥R' => ((z : ↥L) : G)) h1)

theorem perfectResidual_eq (hq : IsQuasisimple L)
    (hy : ∀ z : lBar L, ((e (tau b hb z) : slPi true 3 (2 ^ 2) K) : GL (Fin 3) K) =
      y * (e z : GL (Fin 3) K) * y⁻¹) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {b}) =
      (inSubgroup perfectResidual ((inSubgroup perfectResidual (slPi true 3 (2 ^ 2) K ⊓
        Subgroup.centralizer ({y} : Set (GL (Fin 3) K)))).comap (phi e))).map L.subtype := by
  set N := inSubgroup perfectResidual (slPi true 3 (2 ^ 2) K ⊓
    Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) with hN
  set P := N.comap (phi e) with hP
  have hT := Item221Proof.theta_le_center hq
  have hNle : N ≤ slPi true 3 (2 ^ 2) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) :=
    Subgroup.map_subtype_le _
  rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ L.subtype_injective]
  apply le_antisymm
  ·
    set R := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {b}) with hRdef
    have hR : Group.IsPerfect ↥R := Sec6.isPerfect_inSubgroup_perfectResidual _
    have hRC : R ≤ L ⊓ Subgroup.centralizer {b} := Subgroup.map_subtype_le _
    have hRL : R ≤ L := hRC.trans inf_le_left
    refine Sec6.le_inSubgroup_perfectResidual_of_isPerfect hR ?_
    set R' := R.subgroupOf L with hR'
    have eR : ↥R' ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRL
    have hR'p : Group.IsPerfect ↥R' :=
      Group.IsPerfect.ofSurjective (f := eR.symm.toMonoidHom) eR.symm.surjective
    have himg : R'.map (phi e) ≤ N := by
      refine Sec6.le_inSubgroup_perfectResidual_of_isPerfect
        (Group.IsPerfect.ofSurjective (f := ((phi e).subgroupMap R'))
          ((phi e).subgroupMap_surjective R')) ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨phi_mem_slPi _, phi_mem_centralizer hy ?_⟩
      have hx' : (x : G) ∈ Subgroup.centralizer ({b} : Set G) :=
        (hRC (Subgroup.mem_subgroupOf.mp hx)).2
      exact Subgroup.mem_centralizer_singleton_iff.mp hx'
    intro x hx
    exact ⟨⟨x, hRL hx⟩, himg ⟨⟨x, hRL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  ·
    set Q := inSubgroup perfectResidual P with hQ
    have hQp : Group.IsPerfect ↥Q := Sec6.isPerfect_inSubgroup_perfectResidual _
    have hQP : Q ≤ P := Subgroup.map_subtype_le _
    have hcomm := commute_of_isPerfect hT hQp (fun x hx => mem_theta_of_commute hy
      (Subgroup.mem_centralizer_singleton_iff.mp (hNle (hQP hx)).2))
    have hQC : Q.map L.subtype ≤ L ⊓ Subgroup.centralizer {b} := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have h1 := congrArg Subtype.val (hcomm x hx)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      change b * x * b⁻¹ = x at h1
      show (x : G) ∈ Subgroup.centralizer {b}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : G) * b = b * x * b⁻¹ * b := by rw [h1]
        _ = b * x := by group
    rw [← GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      L.subtype_injective]
    have := hQp
    exact Sec6.le_inSubgroup_perfectResidual_of_isPerfect (Group.IsPerfect.map L.subtype) hQC

omit [Finite G] [Finite K] in
theorem comap_phi_eq_map_conj {N₁ N₂ : Subgroup (GL (Fin 3) K)} {l : ↥L}
    (hN : N₁ = N₂.map (MulAut.conj (phi e l)).toMonoidHom) :
    N₁.comap (phi e) = (N₂.comap (phi e)).map (MulAut.conj l).toMonoidHom := by
  ext x
  rw [hN, Subgroup.mem_comap, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, Subgroup.mem_comap]
  simp only [MulAut.conj_symm_apply, map_mul, map_inv]

omit [Finite K] in
theorem nonempty_perfectResidual_comap_equiv {N₁ N₂ : Subgroup (GL (Fin 3) K)} {l : ↥L}
    (hN : N₁ = N₂.map (MulAut.conj (phi e l)).toMonoidHom) :
    Nonempty (inSubgroup perfectResidual (N₁.comap (phi e)) ≃*
      inSubgroup perfectResidual (N₂.comap (phi e))) := by
  rw [comap_phi_eq_map_conj hN,
    ← GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      (MulAut.conj l).injective]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj l).injective).symm⟩

open scoped IsMulCommutative in
theorem nonempty_perfectResidual_equiv (hq : IsQuasisimple L)
    (hθ : IsPGroup 2 (aschbacherSolvableCore 3 ↥L)) {N : Subgroup (GL (Fin 3) K)}
    (hNS : N ≤ slPi true 3 (2 ^ 2) K) (hNp : Group.IsPerfect ↥N) (hN60 : Nat.card N = 60)
    {V : Subgroup ↥L} (hVP : V ≤ N.comap (phi e)) (hVe : CFSG.Assembly.IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4) (hVT : V ⊓ aschbacherSolvableCore 3 ↥L = ⊥) :
    Nonempty (inSubgroup perfectResidual (N.comap (phi e)) ≃* N) := by
  set T := aschbacherSolvableCore 3 ↥L with hTdef
  have hT := Item221Proof.theta_le_center hq
  have hcen : ∀ t ∈ T, ∀ z : ↥L, t * z = z * t := fun t ht z =>
    (Subgroup.mem_center_iff.mp (hT ht) z).symm
  set P := N.comap (phi e) with hP
  set R := inSubgroup perfectResidual P with hR
  have hRp : Group.IsPerfect ↥R := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hRP : R ≤ P := Subgroup.map_subtype_le _
  have hPN : P.map (phi e) = N := by
    apply le_antisymm (Subgroup.map_comap_le _ _)
    intro n hn
    obtain ⟨x, hx⟩ := exists_phi_eq (e := e) (hNS hn)
    exact ⟨x, show (phi e) x ∈ N by rw [hx]; exact hn, hx⟩
  set f : ↥P →* GL (Fin 3) K := (phi e).comp P.subtype with hf
  have hfr : f.range = N := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hPN]
  have hRN : R.map (phi e) = N := by
    have h1 := (perfect_residual_transport f).1
    have h2 : (perfectResidual ↥P).map f = R.map (phi e) := by
      rw [hR, inSubgroup, Subgroup.map_map]
    have h3 : (perfectResidual ↥f.range).map f.range.subtype = inSubgroup perfectResidual f.range :=
      rfl
    rw [← h2, h1, h3, hfr, CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect hNp]
  set fR : ↥R →* GL (Fin 3) K := (phi e).comp R.subtype with hfR
  have hfRr : fR.range = N := by rw [hfR, MonoidHom.range_comp, Subgroup.range_subtype]; exact hRN
  set W := V.map (phi e) with hW
  have hVinj : Function.Injective ((phi e).comp V.subtype) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hvT : (v : ↥L) ∈ T := (phi_eq_one_iff e _).mp hv
    have h := Subgroup.mem_inf.mpr ⟨v.2, hvT⟩
    rw [hVT, Subgroup.mem_bot] at h
    exact Subtype.ext h
  have hW4 : Nat.card W = 4 := by
    have hWr : W = ((phi e).comp V.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hWr, ← Nat.card_congr (MonoidHom.ofInjective hVinj).toEquiv, hV4]
  have hWN : W ≤ N := by
    rintro _ ⟨v, hv, rfl⟩
    exact hVP hv
  set Q := W.comap fR with hQ
  have hQidx : Q.index = 15 := by
    set gR := fR.rangeRestrict with hgR
    have hQ' : Q = (W.subgroupOf fR.range).comap gR := by
      ext x
      rw [hQ, Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rfl
    rw [hQ', Subgroup.index_comap_of_surjective _ fR.rangeRestrict_surjective]
    have hWr : W ≤ fR.range := by rw [hfRr]; exact hWN
    have hc := (W.subgroupOf fR.range).card_mul_index
    have h1 : Nat.card ↥(W.subgroupOf fR.range) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWr).toEquiv, hW4]
    have h2 : Nat.card ↥fR.range = 60 := by rw [hfRr, hN60]
    rw [h1, h2] at hc
    omega
  have hQc : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x := by
    have hdec : ∀ x ∈ Q, ∃ v ∈ V, ((v : ↥L))⁻¹ * (x : ↥L) ∈ T := by
      intro x hx
      obtain ⟨v, hv, hvx⟩ := hx
      refine ⟨v, hv, (phi_eq_one_iff e _).mp ?_⟩
      rw [map_mul, map_inv, hvx]
      exact inv_mul_cancel _
    intro x hx z hz
    obtain ⟨v, hv, hvx⟩ := hdec x hx
    obtain ⟨w, hw, hwz⟩ := hdec z hz
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    set t := ((v : ↥L))⁻¹ * (x : ↥L) with ht
    set t' := ((w : ↥L))⁻¹ * (z : ↥L) with ht'
    have hxv : (x : ↥L) = v * t := by rw [ht]; group
    have hzw : (z : ↥L) = w * t' := by rw [ht']; group
    have hvw : (v : ↥L) * w = w * v := congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
    rw [hxv, hzw]
    calc (v : ↥L) * t * (w * t') = v * (t * w) * t' := by group
      _ = v * (w * t) * t' := by rw [hcen t hvx w]
      _ = (v * w) * (t * t') := by group
      _ = (w * v) * (t' * t) := by rw [hvw, hcen t hvx t']
      _ = w * (v * t') * t := by group
      _ = w * (t' * v) * t := by rw [hcen t' hwz v]
      _ = w * t' * (v * t) := by group
  have : IsMulCommutative ↥Q := ⟨⟨fun a b => Subtype.ext (hQc a a.2 b b.2)⟩⟩
  have hker : ∀ k : ↥R, fR k = 1 → k = 1 := by
    intro k hk
    have hkT : (k : ↥L) ∈ T := (phi_eq_one_iff e _).mp hk
    have hkC : ∀ z : ↥R, Commute k z := fun z => by
      unfold Commute SemiconjBy
      exact Subtype.ext (hcen _ hkT z)
    have hkQ : k ∈ Q := by
      rw [hQ, Subgroup.mem_comap, hk]
      exact W.one_mem
    have htr := MonoidHom.transfer_eq_pow (MonoidHom.id ↥Q) k (fun j g₀ _ => by
      rw [mul_assoc, (Commute.pow_left (hkC g₀) j).eq, inv_mul_cancel_left])
    have htriv : MonoidHom.transfer (MonoidHom.id ↥Q) k = 1 := by
      set τ := MonoidHom.transfer (MonoidHom.id ↥Q) with hτ
      have hrange : Group.IsPerfect τ.range :=
        Group.IsPerfect.ofSurjective (f := τ.rangeRestrict) τ.rangeRestrict_surjective
      have hsub := subsingleton_of_isPerfect_of_isSolvable hrange
        (Group.isSolvable_of_comm (fun a b => Subtype.ext (mul_comm (a : ↥Q) b)))
      have := Subsingleton.elim (⟨τ k, ⟨k, rfl⟩⟩ : τ.range) 1
      exact congrArg Subtype.val this
    rw [htriv, MonoidHom.id_apply] at htr
    have hk15 : k ^ 15 = 1 := by
      have h : k ^ Q.index = 1 := by
        have h' := congrArg Subtype.val htr.symm
        exact h'
      rwa [hQidx] at h
    obtain ⟨j, hj⟩ := hθ ⟨(k : ↥L), hkT⟩
    have hkj : k ^ 2 ^ j = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun z : ↥T => ((z : ↥L) : G)) hj
      simpa using this
    have h1 : orderOf k ∣ Nat.gcd (2 ^ j) 15 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hkj)
      (orderOf_dvd_of_pow_eq_one hk15)
    have hcop : Nat.gcd (2 ^ j) 15 = 1 :=
      Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 15)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hinj : Function.Injective fR := by
    rw [injective_iff_map_eq_one]
    exact hker
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hfRr)⟩

end CFSG.RankThree.PartTwo.Sec21.Item221ResProof.Levi

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (slPi PiField ModThree)
open Item221ResProof.Levi Item221ResProof.LeviMat
open CFSG.RankThree.PartOne.KFU (permGL)
open CFSG.Assembly.RankThreeEven (projSL)

theorem sl34LeviCover : SL34LeviCover := by
  intro G _ _ A L hAe hAL hq ⟨eB⟩ hC hθ a' ha'A ha'L V hVL hVa' hVe hV4 hVT a haA haL hne
  obtain ⟨π, p, f, K, _, hPi, hmod, e, D, hD, hconj, -⟩ := hC
  obtain ⟨rfl, rfl, rfl⟩ := SL3Lines.params_eq (by norm_num) even_two hPi hmod (eB.symm.trans e)
  have := hPi.finite
  have h2 : (2 : K) = 0 := SL3Lines.two_eq_zero_of_mulEquiv le_rfl
    (fun x hx => (Sec4.mem_slPi_true _).mp hx) (eB.symm.trans e)
  have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
  have hK : Nat.card K = 2 ^ 2 := hPi.card
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  obtain ⟨g, -, hdiag, -⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  set T := aschbacherSolvableCore 3 ↥L with hTdef
  have hcard : ∀ (u : GL (Fin 3) K), Nat.card ↥(levi0.map (MulAut.conj u).toMonoidHom) = 60 := by
    intro u
    rw [Subgroup.card_map_of_injective (MulAut.conj u).injective,
      ← Nat.card_congr (levi0Equiv (K := K)).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  obtain ⟨y, hyD, hy⟩ := hconj _ (tau_mem haA (hAL haA))
  obtain ⟨l, s, t, -, -, hyg⟩ := hdiag y hyD
  have hst : ¬ (s = 1 ∧ t = 1) := by
    rintro ⟨rfl, rfl⟩
    exact haL (le_centralizer_of_forall_commute hq hy (fun M => commute_of_scalar hyg M))
  have hnd : ¬ (s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) := by
    rintro ⟨hs1, ht1, hst'⟩
    exact hne (perfectResidual_eq_bot_of_commute hy
      (fun M hM N hN => commute_of_distinct hyg hs1 ht1 hst' hM hN))
  obtain ⟨σ, l₁, e₁, he₁, hyu⟩ := exists_conj_diagE hyg hst hnd
  obtain ⟨y', hy'D, hy'⟩ := hconj _ (tau_mem ha'A (hAL ha'A))
  obtain ⟨l', s', t', -, -, hyg'⟩ := hdiag y' hy'D
  have hst2 : ¬ (s' = 1 ∧ t' = 1) := by
    rintro ⟨rfl, rfl⟩
    exact ha'L (le_centralizer_of_forall_commute hq hy' (fun M => commute_of_scalar hyg' M))
  set V' := V.subgroupOf L with hV'
  have eV : ↥V' ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVL
  have hV'4 : Nat.card V' = 4 := by rw [Nat.card_congr eV.toEquiv, hV4]
  have hV'e : CFSG.Assembly.IsElemAbelian 2 V' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨((x : ↥L) : G), x.2⟩ ⟨((y : ↥L) : G), y.2⟩)
    · simpa using hVe.2 _ (Subgroup.mem_subgroupOf.mp hx)
  have hV'T : V' ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxT⟩
    have h1 : (x : G) ∈ V ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
      ⟨Subgroup.mem_subgroupOf.mp hxV, ⟨x, hxT, rfl⟩⟩
    rw [hVT, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have hV'c : ∀ v ∈ V', ((v : ↥L) : G) * a' = a' * v := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (hVa' (Subgroup.mem_subgroupOf.mp hv))
  have hV'sq : ∀ v ∈ V', v * v = 1 := fun v hv => by
    have h := hV'e.2 v hv
    rwa [sq] at h
  have hnd2 : ¬ (s' ≠ 1 ∧ t' ≠ 1 ∧ s' ≠ t') := by
    rintro ⟨hs1, ht1, hst'⟩
    have hV1 : V' = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have hvC : phi e v ∈ slPi true 3 (2 ^ 2) K ⊓ Subgroup.centralizer {y'} :=
        ⟨phi_mem_slPi v, phi_mem_centralizer hy' (hV'c v hv)⟩
      have h1 := eq_one_of_distinct_of_mul_self hyg' hs1 ht1 hst' hvC (by
        rw [← map_mul, hV'sq v hv, map_one])
      have hvT : v ∈ T := (phi_eq_one_iff e v).mp h1
      have h3 : v ∈ V' ⊓ T := ⟨hv, hvT⟩
      rwa [hV'T] at h3
    rw [hV1, Subgroup.card_bot] at hV'4
    omega
  obtain ⟨σ', l₂, e₂, he₂, hyu'⟩ := exists_conj_diagE hyg' hst2 hnd2
  set N := inSubgroup perfectResidual (slPi true 3 (2 ^ 2) K ⊓
    Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) with hN
  set N' := inSubgroup perfectResidual (slPi true 3 (2 ^ 2) K ⊓
    Subgroup.centralizer ({y'} : Set (GL (Fin 3) K))) with hN'
  have hNeq : N = levi0.map (MulAut.conj (g * permGL σ)).toMonoidHom := by
    rw [hN, hyu]
    exact perfectResidual_centralizer_conj_eq hPi hK4 he₁ _ _
  have hN'eq : N' = levi0.map (MulAut.conj (g * permGL σ')).toMonoidHom := by
    rw [hN', hyu']
    exact perfectResidual_centralizer_conj_eq hPi hK4 he₂ _ _
  obtain ⟨h, hhS, hhN⟩ := exists_mem_slPi_map_levi0 (K := K) (2 ^ 2) g σ σ'
  obtain ⟨lh, hlh⟩ := exists_phi_eq (e := e) hhS
  have hNN' : N = N'.map (MulAut.conj (phi e lh)).toMonoidHom := by
    rw [hNeq, hN'eq, hlh]
    exact hhN
  obtain ⟨e₃⟩ := nonempty_perfectResidual_comap_equiv (e := e) hNN'
  have hV'P : V' ≤ N'.comap (phi e) := by
    intro v hv
    have hvC : phi e v ∈ slPi true 3 (2 ^ 2) K ⊓ Subgroup.centralizer {y'} :=
      ⟨phi_mem_slPi v, phi_mem_centralizer hy' (hV'c v hv)⟩
    rw [hyu'] at hvC
    have h1 := mem_perfectResidual_of_mul_self hPi hK4 he₂ _ _ hvC (by
      rw [← map_mul, hV'sq v hv, map_one])
    rw [← hyu'] at h1
    exact h1
  have hN'S : N' ≤ slPi true 3 (2 ^ 2) K := (Subgroup.map_subtype_le _).trans inf_le_left
  have hN'p : Group.IsPerfect ↥N' := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hN'60 : Nat.card N' = 60 := by rw [hN'eq]; exact hcard _
  obtain ⟨e₄⟩ := nonempty_perfectResidual_equiv (e := e) hq hθ hN'S hN'p hN'60 hV'P hV'e hV'4
    hV'T
  have e₅ : ↥N' ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (MulEquiv.subgroupCongr hN'eq).trans
      ((Subgroup.equivMapOfInjective _ _ (MulAut.conj (g * permGL σ')).injective).symm.trans
        (levi0Equiv (K := K)).symm)
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 2)
  have hcardK : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 2 (by norm_num)]
  have e₆ : Matrix.SpecialLinearGroup (Fin 2) K ≃* projSL 2 (GaloisField 2 2) :=
    (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcardK)).trans (projSLTwoEquivSL _).symm
  rw [perfectResidual_eq hq hy]
  exact ⟨(Subgroup.equivMapOfInjective _ _ L.subtype_injective).symm.trans
    (e₃.trans (e₄.trans (e₅.trans e₆)))⟩

theorem item221SL34_of_items (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item221SL34 :=
  item221SL34_of h45 h66 sl34LeviCover

end CFSG.RankThree.PartTwo.Sec21
