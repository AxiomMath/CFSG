module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.GroupTheory.SteinbergCECentralQuotientCore
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped commutatorElement Pointwise

theorem commutatorElement_mul_of_mem_center_left {X : Type*} [Group X] (a b : X) {k : X}
    (hk : k ∈ Subgroup.center X) : ⁅a * k, b⁆ = ⁅a, b⁆ := by
  have hkb : k * b = b * k := (Subgroup.mem_center_iff.mp hk b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * k * b * (a * k)⁻¹ * b⁻¹ = a * (k * b) * k⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * k) * k⁻¹ * a⁻¹ * b⁻¹ := by rw [hkb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_of_mem_center_right {X : Type*} [Group X] (a b : X) {k : X}
    (hk : k ∈ Subgroup.center X) : ⁅a, b * k⁆ = ⁅a, b⁆ := by
  have hka : k * a⁻¹ = a⁻¹ * k := (Subgroup.mem_center_iff.mp hk a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * k) * a⁻¹ * (b * k)⁻¹ = a * b * (k * a⁻¹) * k⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * k) * k⁻¹ * b⁻¹ := by rw [hka]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_sup_eq_of_le_center {X : Type*} [Group X] (L K : Subgroup X)
    (hK : K ≤ Subgroup.center X) : ⁅L ⊔ K, L ⊔ K⁆ = ⁅L, L⁆ := by
  have : K.Normal := Subgroup.normal_of_le_center hK
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_left le_sup_left)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ (L : Set X) * (K : Set X) := by rw [← Subgroup.mul_normal]; exact ha
  have hb' : b ∈ (L : Set X) * (K : Set X) := by rw [← Subgroup.mul_normal]; exact hb
  obtain ⟨l, hl, k, hk, rfl⟩ := ha'
  obtain ⟨l', hl', k', hk', rfl⟩ := hb'
  rw [commutatorElement_mul_of_mem_center_left _ _ (hK hk),
    commutatorElement_mul_of_mem_center_right _ _ (hK hk')]
  exact Subgroup.commutator_mem_commutator hl hl'

theorem isQuasisimple_thetaQuotient_iff_of_surjective {L M : Type*} [Group L] [Group M]
    [Finite L] [Finite M] {p : ℕ} (hp : p.Prime) (hL : Group.IsPerfect L) (g : L →* M)
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center L) :
    IsQuasisimple (L ⧸ aschbacherSolvableCore p L) ↔
      IsQuasisimple (M ⧸ aschbacherSolvableCore p M) := by
  have hθ := central_quotient_solvable_prime_complement_core hp g hg hker
  have hle : aschbacherSolvableCore p L ≤ (aschbacherSolvableCore p M).comap g := by
    rw [← hθ]
    exact Subgroup.le_comap_map _ _
  set gbar := QuotientGroup.map _ _ g hle
  have hsurj : Function.Surjective gbar :=
    QuotientGroup.map_surjective_of_surjective _ _ g ((QuotientGroup.mk_surjective).comp hg) hle
  have := hL
  refine LocalCores.isQuasisimple_iff_of_surjective inferInstance gbar hsurj fun x hx => ?_
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, QuotientGroup.map_mk, QuotientGroup.eq_one_iff, ← hθ] at hx
  obtain ⟨t, ht, hgt⟩ := hx
  have hlt : l * t⁻¹ ∈ g.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgt, mul_inv_cancel]
  have heq : (l : L ⧸ aschbacherSolvableCore p L) = ((l * t⁻¹ : L) : L ⧸ _) := by
    rw [QuotientGroup.eq]
    simpa using inv_mem ht
  rw [heq, Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hker hlt) y']

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ}

theorem map_mem_thetaComponents_of_ker_le_center (hp : p.Prime) (f : X →* Y)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X) {L : Subgroup X}
    (hL : L ∈ thetaComponents p X) : L.map f ∈ thetaComponents p Y := by
  set g := f.subgroupMap L
  have hgs : Function.Surjective g := f.subgroupMap_surjective L
  have hgk : g.ker ≤ Subgroup.center L := fun x hx => by
    have hx' : (x : X) ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp (hker hx') y)
  have := hL.1
  exact ⟨Group.IsPerfect.ofSurjective hgs, hL.2.1.map hf,
    (isQuasisimple_thetaQuotient_iff_of_surjective hp hL.1 g hgs hgk).mp hL.2.2⟩

theorem commutator_comap_mem_thetaComponents (hp : p.Prime) (f : X →* Y)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X) {M : Subgroup Y}
    (hM : M ∈ thetaComponents p Y) :
    ⁅M.comap f, M.comap f⁆ ∈ thetaComponents p X ∧ ⁅M.comap f, M.comap f⁆.map f = M := by
  set V := M.comap f with hV
  set fV := f.subgroupComap M
  have hfVs : Function.Surjective fV := f.subgroupComap_surjective M hf
  have hfVk : fV.ker ≤ Subgroup.center V := fun x hx => by
    have hx' : (x : X) ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp (hker hx') y)
  obtain ⟨-, hPerf, hPsurj⟩ :=
    LocalCores.central_extension_derived_of_surjective fV hfVs hfVk hM.1
  have hPeq : (commutator V).map V.subtype = ⁅V, V⁆ := Subgroup.map_subtype_commutator V
  set P := ⁅V, V⁆ with hP
  have hPV : P ≤ V := Subgroup.commutator_le_self V
  have hPM : P.map f = M := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact hPV
    · intro m hm
      obtain ⟨c, hc⟩ := hPsurj ⟨m, hm⟩
      refine ⟨((c : V) : X), ?_, ?_⟩
      · rw [← hPeq]
        exact ⟨c, c.2, rfl⟩
      · exact congrArg Subtype.val hc
  have hPperf : Group.IsPerfect P := by
    have := hPerf
    have h : Group.IsPerfect ((commutator V).map V.subtype) := Group.IsPerfect.ofSurjective
      (f := ((commutator V).equivMapOfInjective V.subtype V.subtype_injective).toMonoidHom)
      ((commutator V).equivMapOfInjective V.subtype V.subtype_injective).surjective
    rwa [hPeq] at h
  have hPsub : P.IsSubnormal := by
    have hPV' : P.subgroupOf V = commutator V := by
      rw [← hPeq, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective V.subtype_injective]
    refine Subgroup.IsSubnormal.step P V hPV (hM.2.1.comap f) ?_
    rw [hPV']
    infer_instance
  set g := f.subgroupMap P
  have hgs : Function.Surjective g := f.subgroupMap_surjective P
  have hgk : g.ker ≤ Subgroup.center P := fun x hx => by
    have hx' : (x : X) ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp (hker hx') y)
  have hq := (isQuasisimple_thetaQuotient_iff_of_surjective hp hPperf g hgs hgk).mpr
  have hq' : IsQuasisimple (P.map f ⧸ aschbacherSolvableCore p (P.map f)) := by
    rw [hPM]
    exact hM.2.2
  exact ⟨⟨hPperf, hPsub, hq hq'⟩, hPM⟩

omit [Finite X] [Finite Y] in
theorem commutator_comap_map_eq_of_mem_thetaComponents (f : X →* Y)
    (hker : f.ker ≤ Subgroup.center X) {L : Subgroup X} (hL : L ∈ thetaComponents p X) :
    ⁅(L.map f).comap f, (L.map f).comap f⁆ = L := by
  rw [Subgroup.comap_map_eq, commutator_sup_eq_of_le_center L f.ker hker]
  exact Subgroup.isPerfect_iff.mp hL.1

theorem central_quotient_theta_component_bijection (hp : p.Prime) (f : X →* Y)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X) :
    Set.BijOn (fun L : Subgroup X => L.map f) (thetaComponents p X) (thetaComponents p Y) ∧
      Set.InvOn (fun M : Subgroup Y => ⁅M.comap f, M.comap f⁆) (fun L : Subgroup X => L.map f)
        (thetaComponents p X) (thetaComponents p Y) ∧
      Set.MapsTo (fun M : Subgroup Y => ⁅M.comap f, M.comap f⁆) (thetaComponents p Y)
        (thetaComponents p X) ∧
      ∀ L ∈ thetaComponents p X, (IsQuasisimple L ↔ IsQuasisimple (L.map f)) := by
  have hinv : Set.InvOn (fun M : Subgroup Y => ⁅M.comap f, M.comap f⁆)
      (fun L : Subgroup X => L.map f) (thetaComponents p X) (thetaComponents p Y) :=
    ⟨fun L hL => commutator_comap_map_eq_of_mem_thetaComponents f hker hL,
      fun M hM => (commutator_comap_mem_thetaComponents hp f hf hker hM).2⟩
  have hmaps : Set.MapsTo (fun M : Subgroup Y => ⁅M.comap f, M.comap f⁆) (thetaComponents p Y)
      (thetaComponents p X) := fun M hM => (commutator_comap_mem_thetaComponents hp f hf hker hM).1
  refine ⟨hinv.bijOn (fun L hL => map_mem_thetaComponents_of_ker_le_center hp f hf hker hL)
    hmaps, hinv, hmaps, fun L hL => ?_⟩
  have hgk : (f.subgroupMap L).ker ≤ Subgroup.center L := fun x hx => by
    have hx' : (x : X) ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp (hker hx') y)
  exact LocalCores.isQuasisimple_iff_of_surjective hL.1 (f.subgroupMap L)
    (f.subgroupMap_surjective L) hgk

end CFSG.RankThree.GroupTheory.SteinbergBY
