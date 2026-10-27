module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalCount
public import CFSG.Timmesfeld.Bridge.RootStructWTIL2

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

theorem eq_one_of_perfect_quotient {R H M : Type*} [Group R] [Group H] [Group M]
    [Group.IsPerfect H] (f : R →* H) (hf : Function.Surjective f) (φ : R →* M)
    (hcomm : ∀ x y, φ x * φ y = φ y * φ x) (hker : f.ker ≤ φ.ker) (r : R) : φ r = 1 := by
  have h1 : commutator R ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, hcomm x y, map_inv,
      map_inv]
    group
  have h2 : (commutator R).map f = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 hf, ← commutator_def, Group.IsPerfect.commutator_eq_top]
  obtain ⟨r', hr', hfr⟩ : f r ∈ (commutator R).map f := by
    rw [h2]
    trivial
  have hk : r'⁻¹ * r ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfr, inv_mul_cancel]
  calc φ r = φ r' * φ (r'⁻¹ * r) := by rw [← map_mul, mul_inv_cancel_left]
    _ = 1 := by rw [h1 hr', hker hk, mul_one]

variable {G : Type*} [Group G] {D : Set G}

theorem conj_mem_lineGroup {a d g r : G} (hg : Commute g a) (hr : r ∈ lineGroup D a d) :
    g * r * g⁻¹ ∈ lineGroup D a d := by
  have hle : lineGroup D a d ≤ (lineGroup D a d).comap (MulAut.conj g).toMonoidHom := by
    refine iSup_le fun g' => ?_
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_comap]
    have hg'' : g * (g' : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_centralizer_singleton_iff.2 hg.eq) g'.2
    refine Subgroup.mem_iSup_of_mem ⟨g * g', hg''⟩ ⟨h, hh, ?_⟩
    simp [mul_assoc]
  exact hle hr

theorem inf_le_lineGroup (D : Set G) (a d : G) :
    nCore D d ⊓ Subgroup.centralizer {a} ≤ lineGroup D a d := fun k hk =>
  Subgroup.mem_iSup_of_mem ⟨1, Subgroup.one_mem _⟩ ⟨k, Subgroup.mem_sup_left hk, by simp⟩

namespace TwoLocalSetting

theorem commute_of_mem_lineGroup {G : Type} [Group G] {D : Set G} (S : TwoLocalSetting G D)
    {a d c r : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hda : d ≠ a)
    (h5 : 5 ≤ (rootLines D a).ncard) (hc : c ∈ Subgroup.centralizer (nCore D a : Set G))
    (hr : r ∈ lineGroup D a d) : Commute r c := by
  have := S.hyp.finite
  have hD := S.root
  have hL := S.lineSetting
  have hadD : a * d ∈ D := S.mul_mem_of_commute ha hd had (Ne.symm hda)
  have hdT : d ∉ rootSet D a := by
    rw [S.sing a ha]
    exact hda
  set R := lineGroup D a d with hRdef
  set M := nCore D a with hMdef
  set Z := M ⊓ Subgroup.centralizer (M : Set G) with hZdef
  obtain ⟨m, -, hk, hMR, hker, ⟨f, hfs, hfk⟩, -⟩ :=
    rootLinesL2Step G D hL a ha d hd had hadD hdT (by omega)
  have hm : 2 ≤ m := by
    by_contra hm
    push Not at hm
    interval_cases m <;> omega
  have hcard : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [GaloisField.card 2 m (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card
    (GaloisField 2 m) hcard
  have hRa : ∀ x ∈ R, Commute x a := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (lineGroup_le_centralizer D a d hx)
  have hcM : ∀ m ∈ M, Commute c m := fun m hm =>
    (Subgroup.mem_centralizer_iff.1 hc m hm).symm
  have hca : Commute c a := hcM a (S.self_mem ha)
  have hkerM : ∀ x : R, x ∈ f.ker → (x : G) ∈ M := by
    intro x hx
    rw [hfk] at hx
    exact Subgroup.mem_subgroupOf.1 hx
  have hRZ : ∀ x ∈ R, ∀ z ∈ Z, Commute x z := by
    intro z₀ hz₀ z hz
    have hval : ∀ x ∈ R, x * z * x⁻¹ * z⁻¹ = 1 ∨ x * z * x⁻¹ * z⁻¹ = a := by
      intro x hx
      rcases S.conj_eq_or_of_mem_center ha hz (hRa x hx) with h | h <;> rw [h]
      · exact Or.inl (mul_inv_cancel z)
      · exact Or.inr (by group)
    let φ : R →* G :=
      { toFun := fun x => (x : G) * z * (x : G)⁻¹ * z⁻¹
        map_one' := by simp
        map_mul' := by
          intro x y
          have hy := hval y y.2
          have hx := hval x x.2
          have e : ((x * y : R) : G) * z * ((x * y : R) : G)⁻¹ * z⁻¹ =
              (x : G) * ((y : G) * z * (y : G)⁻¹ * z⁻¹) * (x : G)⁻¹ *
                ((x : G) * z * (x : G)⁻¹ * z⁻¹) := by
            simp only [Subgroup.coe_mul]
            group
          rw [e]
          rcases hy with hy | hy <;> rcases hx with hx | hx <;> rw [hy, hx] <;>
            simp only [mul_one, one_mul, mul_inv_cancel, (hRa x x.2).eq, mul_inv_cancel_right] }
    have hφ := eq_one_of_perfect_quotient f hfs φ
      (fun x y => by
        rcases hval x x.2 with hx | hx <;> rcases hval y y.2 with hy | hy <;>
          simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, hx, hy, one_mul, mul_one])
      (fun x hx => MonoidHom.mem_ker.2 (by
        have hxM := hkerM x hx
        change (x : G) * z * (x : G)⁻¹ * z⁻¹ = 1
        rw [Subgroup.mem_centralizer_iff.1 hz.2 x hxM, mul_inv_cancel_right,
          mul_inv_cancel]))
      ⟨z₀, hz₀⟩
    change z₀ * z * z₀⁻¹ * z⁻¹ = 1 at hφ
    exact commutatorElement_eq_one_iff_commute.1 hφ
  have hRC : ∀ x ∈ R, x * c * x⁻¹ * c⁻¹ ∈ Z := by
    intro x hx
    have hxa := hRa x hx
    have hxc : ∀ m ∈ M, Commute (x * c * x⁻¹) m := by
      intro m hm
      have hm' : x⁻¹ * m * x⁻¹⁻¹ ∈ M := conj_mem_nCore S.hyp.isClass hxa.inv_left hm
      have h1 := hcM _ hm'
      have e : m = x * (x⁻¹ * m * x⁻¹⁻¹) * x⁻¹ := by group
      rw [e]
      exact (Commute.conj_iff x).2 h1
    have hmemC : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.centralizer (M : Set G) := by
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hc)
      exact Subgroup.mem_centralizer_iff.2 fun m hm => (hxc m hm).symm.eq
    have hmemR : x * c * x⁻¹ * c⁻¹ ∈ R := by
      rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by group]
      exact R.mul_mem hx (conj_mem_lineGroup hca (R.inv_mem hx))
    refine ⟨(hker _ hmemR).1 fun L hL' => ?_, hmemC⟩
    obtain ⟨y, hy, hay, hya, rfl⟩ := (S.mem_rootLines_iff ha).1 hL'
    have hc' : Commute (x * c * x⁻¹ * c⁻¹) a :=
      (Subgroup.mem_centralizer_iff.1 hmemC a (S.self_mem ha)).symm
    have hcy : Commute (x * c * x⁻¹ * c⁻¹) y :=
      (Subgroup.mem_centralizer_iff.1 hmemC y (S.mem_nCore ha hy hay.symm)).symm
    exact (S.map_line_eq_iff ha hy hay hya hc').2 (Or.inl (by rw [hcy.eq, mul_inv_cancel_right]))
  let ψ : R →* G :=
    { toFun := fun x => (x : G) * c * (x : G)⁻¹ * c⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        have e : ((x * y : R) : G) * c * ((x * y : R) : G)⁻¹ * c⁻¹ =
            (x : G) * ((y : G) * c * (y : G)⁻¹ * c⁻¹) * (x : G)⁻¹ *
              ((x : G) * c * (x : G)⁻¹ * c⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [e, (hRZ x x.2 _ (hRC y y.2)).eq, mul_inv_cancel_right]
        exact Subgroup.mem_centralizer_iff.1 (hRC x x.2).2 _ (hRC y y.2).1 }
  have hψ := eq_one_of_perfect_quotient f hfs ψ
    (fun x y => (Subgroup.mem_centralizer_iff.1 (hRC y y.2).2 _ (hRC x x.2).1))
    (fun x hx => MonoidHom.mem_ker.2 (by
      have hxM := hkerM x hx
      change (x : G) * c * (x : G)⁻¹ * c⁻¹ = 1
      rw [← (hcM x hxM).eq, mul_inv_cancel_right, mul_inv_cancel]))
    ⟨r, hr⟩
  change r * c * r⁻¹ * c⁻¹ = 1 at hψ
  exact commutatorElement_eq_one_iff_commute.1 hψ

end TwoLocalSetting

end CFSG.Timmesfeld.Bridge
