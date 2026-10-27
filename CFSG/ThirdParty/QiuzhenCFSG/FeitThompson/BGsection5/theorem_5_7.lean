module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.corollary_4_19

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.7 from BG Section 5 -/

open scoped commutatorElement

private theorem CFSG.chiefFactor_exists_isPFactor
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (cf : ChiefFactor G) :
    ∃ q : ℕ, q.Prime ∧ cf.IsPFactor q := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
  have : Uq.Normal := hmin.1
  have : IsMinimalNormal Uq := {
    minimal := by
      intro K _ hKle
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hmin.2.2 K inferInstance hKle hKbot)
  }
  have : Group.IsSolvable (G ⧸ cf.V) := by infer_instance
  have : Group.IsSolvable Uq := by infer_instance
  obtain ⟨q, hq, hUq_elem⟩ :=
    minimalNormal_solvable_exists_isElementaryAbelian
      (G := G ⧸ cf.V) (M := Uq)
  refine ⟨q, hq, ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  have hUq_p : IsPGroup q Uq := by
    let _ : IsElementaryAbelian q Uq := hUq_elem
    exact IsElementaryAbelian.isPGroup q Uq
  dsimp [ChiefFactor.IsPFactor]
  let _ : (cf.V.subgroupOf cf.U).Normal :=
    Subgroup.Normal.subgroupOf (G := G) (hH := cf.isChief.normal_K) cf.U
  exact hUq_p.of_equiv (quotientSubgroupRangeEquiv cf.U cf.V).symm

private theorem CFSG.derived_conj_image_isPGroup_of_narrow_high_rank
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Subgroup G} [R.Normal]
    (hnarrow : IsNarrowPGroup p R) (hRrank : 3 ≤ groupRank R)
    (hoddG : Odd (Nat.card G)) :
    IsPGroup p ((derivedSubgroup G).map (MulAut.conjNormal (H := R))) := by
  classical
  let φ : G →* MulAut R := MulAut.conjNormal (H := R)
  let A : Subgroup (MulAut R) := φ.range
  have hAodd : Odd (Nat.card A) := by
    exact odd_of_card_dvd hoddG (Subgroup.card_range_dvd φ)
  have hsolvA : Group.IsSolvable A := by
    exact Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hderA : IsPGroup p (derivedSubgroup A) :=
    theorem_5_5_a_high_rank_series_bridge
      (p := p) hpodd (R := R) hnarrow hRrank (A := A) hAodd
  let ψ : G →* A := φ.rangeRestrict
  have hψ_surj : Function.Surjective ψ := φ.rangeRestrict_surjective
  have hmap_eq : (derivedSubgroup G).map ψ = derivedSubgroup A := by
    simpa [derivedSubgroup, derivedSeries_one] using
      map_derivedSeries_eq (f := ψ) hψ_surj 1
  have hmap_p : IsPGroup p ((derivedSubgroup G).map ψ) := by
    rw [hmap_eq]
    exact hderA
  have hmap_subtype_p :
      IsPGroup p (((derivedSubgroup G).map ψ).map A.subtype) := by
    exact IsPGroup.map (p := p) (H := (derivedSubgroup G).map ψ) hmap_p A.subtype
  have hmap_map : ((derivedSubgroup G).map ψ).map A.subtype =
      (derivedSubgroup G).map φ := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨g, hg, rfl⟩
      exact Subgroup.mem_map_of_mem φ hg
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_, rfl⟩
      exact Subgroup.mem_map_of_mem ψ hg
  rw [hmap_map] at hmap_subtype_p
  simpa [φ] using hmap_subtype_p

private theorem CFSG.chiefFactor_derived_conj_image_isPGroup_of_pCore_action
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p : ℕ} [Fact p.Prime] (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p)
    (hcfU : cf.U ≤ fittingSubgroup G)
    (hderR_p : IsPGroup p ((derivedSubgroup G).map (MulAut.conjNormal (H := pCore p G)))) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    let φ : (G ⧸ cf.V) →* MulAut Uq := by
      let hmin :
          Uq.Normal ∧ Uq ≠ ⊥ ∧
            (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
        simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
      letI : Uq.Normal := hmin.1
      exact MulAut.conjNormal (H := Uq)
    IsPGroup p ((derivedSubgroup G).map (φ.comp π)) := by
  classical
  let R : Subgroup G := pCore p G
  let P : Sylow p cf.U := default
  have hUsub_nil : Group.IsNilpotent ↥(cf.U.subgroupOf (fittingSubgroup G)) := by
    infer_instance
  have hUnil : Group.IsNilpotent ↥cf.U := by
    let e :
        ↥(cf.U.subgroupOf (fittingSubgroup G)) ≃* ↥cf.U :=
      Subgroup.subgroupOfEquivOfLe (G := G) (H := cf.U) (K := fittingSubgroup G) hcfU
    exact Group.nilpotent_of_mulEquiv (G := ↥(cf.U.subgroupOf (fittingSubgroup G))) (G' := ↥cf.U) e
  let N : Subgroup G := P.map cf.U.subtype
  have hN_le_R : N ≤ R := by
    simpa [N, R] using
      sylow_map_le_pCore_local (G := G) (N := cf.U) cf.isChief.normal_H hUnil P
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
  have : Uq.Normal := hmin.1
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  have hUq_p : IsPGroup p Uq := by
    let _ : (cf.V.subgroupOf cf.U).Normal :=
      Subgroup.Normal.subgroupOf (G := G) (hH := cf.isChief.normal_K) cf.U
    exact hcf_p.of_equiv (quotientSubgroupRangeEquiv cf.U cf.V)
  let πUq : cf.U →* Uq :=
    ((π.comp cf.U.subtype).codRestrict Uq fun u =>
      Subgroup.mem_map_of_mem π u.2)
  have hπUq_surj : Function.Surjective πUq := by
    intro u
    rcases Subgroup.mem_map.mp u.2 with ⟨x, hxU, hx⟩
    refine ⟨⟨x, hxU⟩, ?_⟩
    exact Subtype.ext hx
  let Nqsub : Subgroup Uq := (P : Subgroup cf.U).map πUq
  have hNqsub_top : Nqsub = ⊤ := by
    let Tmap : Sylow p Uq := P.mapSurjective (f := πUq) hπUq_surj
    have htop_p : IsPGroup p (⊤ : Subgroup Uq) := by
      simpa using hUq_p.to_subgroup (⊤ : Subgroup Uq)
    let Ttop : Sylow p Uq :=
      IsPGroup.toSylow (G := Uq) (p := p) htop_p (by
        simpa using (Fact.out : Nat.Prime p).not_dvd_one)
    have hTtop_normal : (Ttop : Subgroup Uq).Normal := by
      have hTtop_eq : (Ttop : Subgroup Uq) = ⊤ := by
        dsimp [Ttop]
      rw [hTtop_eq]
      infer_instance
    have : Unique (Sylow p Uq) := Sylow.unique_of_normal Ttop hTtop_normal
    have hSylow_eq : Tmap = Ttop := Subsingleton.elim _ _
    change (Tmap : Subgroup Uq) = ⊤
    simpa [Tmap, Ttop, IsPGroup.toSylow_coe] using
      congrArg (fun S : Sylow p Uq => (S : Subgroup Uq)) hSylow_eq
  have hNqsub_map :
      Nqsub.map Uq.subtype = N.map π := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨z, hzP, rfl⟩
      exact Subgroup.mem_map_of_mem π <|
        Subgroup.mem_map_of_mem cf.U.subtype hzP
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyN, rfl⟩
      rcases Subgroup.mem_map.mp hyN with ⟨z, hzP, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      exact ⟨πUq z, Subgroup.mem_map_of_mem πUq hzP, rfl⟩
  have htop_map_Uq : (⊤ : Subgroup Uq).map Uq.subtype = Uq := by
    simpa [MonoidHom.range_eq_map] using
      (Uq.range_subtype : Uq.subtype.range = Uq)
  have hNq_eq_Uq : N.map π = Uq := by
    calc
      N.map π = Nqsub.map Uq.subtype := hNqsub_map.symm
      _ = (⊤ : Subgroup Uq).map Uq.subtype := by rw [hNqsub_top]
      _ = Uq := htop_map_Uq
  let D : Subgroup G := derivedSubgroup G
  let fR : D →* MulAut R := (MulAut.conjNormal (H := R)).comp D.subtype
  let fU : D →* MulAut Uq := ((φ.comp π).comp D.subtype)
  have hfactor : ∀ {x y : D}, fR x = fR y → fU x = fU y := by
    intro x y hxy
    ext u
    have huNq : (u : G ⧸ cf.V) ∈ N.map π := by
      rw [hNq_eq_Uq]
      exact u.2
    rcases Subgroup.mem_map.mp huNq with ⟨n, hnN, hu_eq⟩
    have hnR : n ∈ R := hN_le_R hnN
    have hconjR :
        (fR x) ⟨n, hnR⟩ = (fR y) ⟨n, hnR⟩ := by
      exact congrArg (fun e : MulAut R => e ⟨n, hnR⟩) hxy
    have hconj_eq :
        x.1 * n * x.1⁻¹ = y.1 * n * y.1⁻¹ := by
      simpa [fR, MulAut.conjNormal_apply] using congrArg Subtype.val hconjR
    have hπconj_eq :
        π (x.1 * n * x.1⁻¹) = π (y.1 * n * y.1⁻¹) := by
      simpa [π, map_mul, mul_assoc] using congrArg π hconj_eq
    calc
      (((fU x) u : Uq) : G ⧸ cf.V)
          = (π x.1) * (u : G ⧸ cf.V) * (π x.1)⁻¹ := by
              simp [fU, φ, MulAut.conjNormal_apply]
      _ = (π x.1) * π n * (π x.1)⁻¹ := by rw [hu_eq]
      _ = π (x.1 * n * x.1⁻¹) := by simp [π, map_mul, mul_assoc]
      _ = π (y.1 * n * y.1⁻¹) := hπconj_eq
      _ = (π y.1) * π n * (π y.1)⁻¹ := by simp [π, map_mul, mul_assoc]
      _ = (π y.1) * (u : G ⧸ cf.V) * (π y.1)⁻¹ := by rw [hu_eq]
      _ = (((fU y) u : Uq) : G ⧸ cf.V) := by
              simp [fU, φ, MulAut.conjNormal_apply]
  have hfrange_eq :
      fR.range = (derivedSubgroup G).map (MulAut.conjNormal (H := R)) := by
    calc
      fR.range = (⊤ : Subgroup D).map fR := MonoidHom.range_eq_map fR
      _ = ((⊤ : Subgroup D).map D.subtype).map (MulAut.conjNormal (H := R)) := by
            rw [Subgroup.map_map]
      _ = D.map (MulAut.conjNormal (H := R)) := by
            congr 1
            simpa [MonoidHom.range_eq_map] using
              (D.range_subtype : D.subtype.range = D)
      _ = (derivedSubgroup G).map (MulAut.conjNormal (H := R)) := rfl
  let H : Subgroup (MulAut R) := fR.range
  have hH_p : IsPGroup p H := by
    change IsPGroup p fR.range
    rw [hfrange_eq]
    simpa [R] using hderR_p
  let rep : H → D := fun a => Classical.choose a.2
  have hrep : ∀ a : H, fR (rep a) = a := by
    intro a
    exact Classical.choose_spec a.2
  let ρ : H →* MulAut Uq := {
    toFun := fun a => fU (rep a)
    map_one' := by
      have h1 : fR (rep 1) = fR 1 := by
        calc
          fR (rep 1) = (1 : H) := hrep 1
          _ = fR 1 := by simp [H, fR]
      simpa [fU] using hfactor h1
    map_mul' := by
      intro a b
      have hmul : fR (rep (a * b)) = fR (rep a * rep b) := by
        calc
          fR (rep (a * b)) = a * b := hrep (a * b)
          _ = fR (rep a) * fR (rep b) := by rw [hrep a, hrep b]
          _ = fR (rep a * rep b) := by simp [fR]
      calc
        fU (rep (a * b)) = fU (rep a * rep b) := hfactor hmul
        _ = fU (rep a) * fU (rep b) := by simp [fU]
  }
  have hρrange_eq : ρ.range = fU.range := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨a, rfl⟩
      exact ⟨rep a, rfl⟩
    · intro hx
      rcases hx with ⟨d, rfl⟩
      let a : H := ⟨fR d, ⟨d, rfl⟩⟩
      refine ⟨a, ?_⟩
      change fU (rep a) = fU d
      exact hfactor (by simpa [a] using hrep a)
  have hfurange_eq :
      fU.range = (derivedSubgroup G).map ((MulAut.conjNormal (H := Uq)).comp π) := by
    calc
      fU.range = (⊤ : Subgroup D).map fU := MonoidHom.range_eq_map fU
      _ = ((⊤ : Subgroup D).map D.subtype).map (φ.comp π) := by
            rw [Subgroup.map_map]
      _ = D.map (φ.comp π) := by
            congr 1
            simpa [MonoidHom.range_eq_map] using
              (D.range_subtype : D.subtype.range = D)
      _ = (derivedSubgroup G).map (φ.comp π) := rfl
  have hρrange_p : IsPGroup p ρ.range := by
    have htop_p : IsPGroup p (⊤ : Subgroup H) := by
      simpa using hH_p.to_subgroup (⊤ : Subgroup H)
    have : IsPGroup p ((⊤ : Subgroup H).map ρ) :=
      IsPGroup.map (p := p) (H := (⊤ : Subgroup H)) htop_p ρ
    rw [MonoidHom.range_eq_map]
    exact this
  have hfurange_p : IsPGroup p fU.range := by
    rw [← hρrange_eq]
    exact hρrange_p
  rw [hfurange_eq] at hfurange_p
  exact hfurange_p

private theorem CFSG.chiefFactor_conj_range_pCore_eq_bot
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p : ℕ} [Fact p.Prime] (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    let φ : (G ⧸ cf.V) →* MulAut Uq := by
      let hmin :
          Uq.Normal ∧ Uq ≠ ⊥ ∧
            (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
        simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
      letI : Uq.Normal := hmin.1
      exact MulAut.conjNormal (H := Uq)
    pCore p φ.range = ⊥ := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
  have : Uq.Normal := hmin.1
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  let A : Subgroup (MulAut Uq) := φ.range
  have hUq_p : IsPGroup p Uq := by
    let _ : (cf.V.subgroupOf cf.U).Normal :=
      Subgroup.Normal.subgroupOf (G := G) (hH := cf.isChief.normal_K) cf.U
    exact hcf_p.of_equiv (quotientSubgroupRangeEquiv cf.U cf.V)
  let P : Subgroup A := pCore p A
  have hP_p : IsPGroup p P := by
    dsimp [P]
    exact pCore_isPGroup (G := A) (p := p)
  have hUq_dvd : p ∣ Nat.card Uq := by
    have hUq_nontrivial : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hmin.2.1
    rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Uq) (hG := hUq_p)).1 hUq_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn)
  let F : Subgroup Uq := fixedPointSubgroup P Uq
  have hF_ne_bot : F ≠ ⊥ := by
    have hone_fix : (1 : Uq) ∈ MulAction.fixedPoints P Uq := by
      simp [MulAction.mem_fixedPoints]
    obtain ⟨u, hu_fix, hu_ne_one'⟩ :=
      hP_p.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (α := Uq) hUq_dvd hone_fix
    have hu_ne_one : u ≠ 1 := by
      intro hu
      exact hu_ne_one' hu.symm
    intro hbot
    have hu_mem : u ∈ F := by
      simpa [F, FixedPoints.mem_subgroup] using
        MulAction.mem_fixedPoints.mp hu_fix
    have hu_bot : u ∈ (⊥ : Subgroup Uq) := by
      simpa [hbot] using hu_mem
    exact hu_ne_one (Subgroup.mem_bot.mp hu_bot)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  have hF_inv : IsInvariant A Uq F := by
    refine ⟨?_⟩
    intro a u
    constructor
    · intro hu
      change u ∈ fixedPointSubgroup P Uq at hu
      change a • u ∈ fixedPointSubgroup P Uq
      rw [FixedPoints.mem_subgroup] at hu ⊢
      exact smul_mem_fixedPoints_of_normal (H := P) a hu
    · intro hu
      change a • u ∈ fixedPointSubgroup P Uq at hu
      change u ∈ fixedPointSubgroup P Uq
      rw [FixedPoints.mem_subgroup] at hu ⊢
      have hsmul := smul_mem_fixedPoints_of_normal (H := P) a⁻¹ hu
      simpa [mul_smul] using hsmul
  let Fmap : Subgroup (G ⧸ cf.V) := F.map Uq.subtype
  have hFmap_normal : Fmap.Normal := by
    refine ⟨?_⟩
    intro x hx q
    rcases Subgroup.mem_map.mp hx with ⟨u, huF, rfl⟩
    let aq : A := ⟨φ q, ⟨q, rfl⟩⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨aq • u, (hF_inv.invariant aq u).1 huF, ?_⟩
    change (((φ q) u : Uq) : G ⧸ cf.V) = q * (u : G ⧸ cf.V) * q⁻¹
    simp [φ, MulAut.conjNormal_apply]
  have hFmap_le_Uq : Fmap ≤ Uq := by
    exact Subgroup.map_subtype_le F
  have hFmap_ne_bot : Fmap ≠ ⊥ := by
    intro hbot
    have : F = ⊥ := by
      exact
        (Subgroup.map_eq_bot_iff_of_injective (H := F) (f := Uq.subtype)
          Uq.subtype_injective).1 (by simpa [Fmap] using hbot)
    exact hF_ne_bot this
  have hFmap_eq_Uq : Fmap = Uq :=
    hmin.2.2 Fmap hFmap_normal hFmap_le_Uq hFmap_ne_bot
  have htop_map_Uq : (⊤ : Subgroup Uq).map Uq.subtype = Uq := by
    simpa [MonoidHom.range_eq_map] using
      (Uq.range_subtype : Uq.subtype.range = Uq)
  have hF_top : F = ⊤ := by
    have hinj : Function.Injective (Subgroup.map Uq.subtype) :=
      Subgroup.map_injective (f := Uq.subtype) Uq.subtype_injective
    apply hinj
    simpa [Fmap, htop_map_Uq] using hFmap_eq_Uq
  have htriv : ActsTrivially (A := P) (G := Uq) := by
    intro a u
    have huF : u ∈ F := by
      simp [F, hF_top]
    exact (FixedPoints.mem_subgroup (M := P) (a := u)).mp huF a
  have hsub : Subsingleton P := by
    refine ⟨?_⟩
    intro a b
    apply Subtype.ext
    ext u
    have ha := htriv a u
    have hb := htriv b u
    change ((a : A) : MulAut Uq) u = u at ha
    change ((b : A) : MulAut Uq) u = u at hb
    exact congrArg Subtype.val (ha.trans hb.symm)
  have hcard_one : Nat.card P = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  change P = ⊥
  exact (Subgroup.card_eq_one (H := P)).1 hcard_one

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.theorem_5_7_chief_factor_centralized
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {E : Subgroup G} [IsElementaryAbelian p E] (hE_le : E ≤ fittingSubgroup G)
    (hcent_rank : groupRank (subgroupCentralizerIn (fittingSubgroup G) E) ≤ 2)
    (cf : ChiefFactor G) (hcfU : cf.U ≤ fittingSubgroup G) :
    derivedSubgroup G ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
  classical
  obtain ⟨q, hq, hcf_q⟩ := chiefFactor_exists_isPFactor (G := G) cf
  have : Fact q.Prime := ⟨hq⟩
  let R : Subgroup G := pCore q G
  have hR_normal : R.Normal := by
    dsimp [R]
    infer_instance
  have hR_p : IsPGroup q R := by
    dsimp [R]
    exact pCore_isPGroup (G := G) (p := q)
  have hR_le_fit : R ≤ fittingSubgroup G := by
    simpa [R] using (pCore_le_fitting G q)
  have hRcent_rank : groupRank (subgroupCentralizerIn R E) ≤ 2 := by
    exact
      pCore_centralizer_rank_le_two_of_fitting_centralizer_rank_le_two
        (G := G) (q := q) hE_le hcent_rank
  by_cases hR_rank_le : groupRank R ≤ 2
  · have hprank_fit : primeRank q (fittingSubgroup G) ≤ 2 := by
      exact (primeRank_fitting_le_groupRank_pCore (G := G) (q := q)).trans hR_rank_le
    exact corollary_4_19
      (G := G) (p := q) (inferInstance : Group.IsSolvable G) hodd (fittingSubgroup G) hprank_fit
      cf hcf_q hcfU
  · have hE_le_pCore : E ≤ pCore p G :=
      elementaryAbelian_le_pCore_of_le_fitting (G := G) (p := p) hE_le
    have hq_eq_p : q = p := by
      by_contra hq_ne_p
      have hR_le_centE : R ≤ subgroupCentralizerIn R E := by
        intro x hxR
        refine ⟨hxR, ?_⟩
        intro y hyE
        exact (pCore_commute_of_ne_local (G := G) (p := q) (q := p) hq_ne_p
          x (by simpa [R] using hxR) y (hE_le_pCore hyE)).symm
      have hR_rank_le' : groupRank R ≤ 2 := by
        have hR_le_centRE : R ≤ subgroupCentralizerIn R E := hR_le_centE
        have hrank_mono :
            groupRank R ≤ groupRank (subgroupCentralizerIn R E) :=
          groupRank_le_groupRank_of_subgroup hR_le_centRE
        exact hrank_mono.trans hRcent_rank
      exact hR_rank_le hR_rank_le'
    subst q
    have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat hodd hp_dvd
    have hR_rank : 3 ≤ groupRank R := by omega
    let Z : Subgroup R := Ω₁Z p R
    let S : Subgroup R := E.subgroupOf R
    have hS_elem : IsElementaryAbelian p S :=
      IsElementaryAbelian.subgroupOf (p := p) hE_le_pCore
    let : IsElementaryAbelian p S := hS_elem
    have hZ_elem : IsElementaryAbelian p Z := by
      simpa [Z] using omega1Z_isElementaryAbelian (p := p) (R := R)
    let : IsElementaryAbelian p Z := hZ_elem
    have hS_not_le_Z : ¬ S ≤ Z := by
      intro hSZ
      have hR_le_centE : R ≤ subgroupCentralizerIn R E := by
        intro x hxR
        refine ⟨hxR, ?_⟩
        intro y hyE
        let xR : R := ⟨x, hxR⟩
        let yR : R := ⟨y, hE_le_pCore hyE⟩
        have hyS : yR ∈ S := by
          simpa [S, Subgroup.mem_subgroupOf] using hyE
        have hyZ : yR ∈ Z := hSZ hyS
        simpa [xR, yR] using
          (congrArg Subtype.val <|
            (Subgroup.mem_center_iff.mp ((omega1Z_le_center p R) hyZ)) xR).symm
      have hR_rank_le' : groupRank R ≤ 2 := by
        exact (groupRank_le_groupRank_of_subgroup hR_le_centE).trans hRcent_rank
      exact hR_rank_le hR_rank_le'
    have hEZ_elem : IsElementaryAbelian p (Z ⊔ S : Subgroup R) := by
      have hS_le_centZ : S ≤ Subgroup.centralizer (Z : Set R) := by
        exact (Subgroup.le_centralizer_iff).mp <|
          (omega1Z_le_center p R).trans (Subgroup.center_le_centralizer (S : Set R))
      exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := Z) (C := S) hS_le_centZ
    let : IsElementaryAbelian p (Z ⊔ S : Subgroup R) := hEZ_elem
    let C : Subgroup R := (subgroupCentralizerIn R E).subgroupOf R
    have hZ_le_C : Z ≤ C := by
      intro z hzZ
      show (z : G) ∈ subgroupCentralizerIn R E
      refine ⟨z.2, ?_⟩
      intro e he
      let eR : R := ⟨e, hE_le_pCore he⟩
      simpa [eR] using congrArg Subtype.val <|
        (Subgroup.mem_center_iff.mp ((omega1Z_le_center p R) hzZ)) eR
    have hS_le_C : S ≤ C := by
      intro s hsS
      show (s : G) ∈ subgroupCentralizerIn R E
      refine ⟨s.2, ?_⟩
      intro e he
      let eR : R := ⟨e, hE_le_pCore he⟩
      have heS : eR ∈ S := by
        simpa [S, Subgroup.mem_subgroupOf] using he
      exact congrArg Subtype.val <|
        (setLike_mul_comm (s := S) heS hsS)
    have hEZ_le_C : Z ⊔ S ≤ C := sup_le hZ_le_C hS_le_C
    have hZ_ne_bot : Z ≠ ⊥ := by
      have hR_nontrivial : Nontrivial R := by
        refine not_subsingleton_iff_nontrivial.mp ?_
        intro hsub
        let : Subsingleton R := hsub
        have hcyc : IsCyclic R := inferInstance
        have hRank_le_one : groupRank R ≤ 1 := groupRank_le_one_of_isCyclic R
        exact (by decide : ¬ 3 ≤ (1 : ℕ)) (le_trans hR_rank hRank_le_one)
      let : Nontrivial R := hR_nontrivial
      have hcenter_nontrivial : Nontrivial (Subgroup.center R) := hR_p.center_nontrivial
      have hcenter_p : IsPGroup p (Subgroup.center R) := hR_p.to_subgroup (Subgroup.center R)
      have hpdvd_center : p ∣ Nat.card (Subgroup.center R) := by
        rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Subgroup.center R)
            (hG := hcenter_p)).1 hcenter_nontrivial with
          ⟨n, hn, hcard⟩
        rw [hcard]
        exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn)
      simpa [Z, Ω₁Z] using
        omega₁_map_subtype_ne_bot (M := Subgroup.center R) (p := p) hpdvd_center
    have hEZ_ne_Z : (Z ⊔ S : Subgroup R) ≠ Z := by
      intro hEZ
      exact hS_not_le_Z (by
        intro s hsS
        have hsEZ : s ∈ (Z ⊔ S : Subgroup R) := Subgroup.mem_sup_right hsS
        simpa [hEZ] using hsEZ)
    have hEZ_card : Nat.card (Z ⊔ S : Subgroup R) = p ^ 2 := by
      have hEZ_p : IsPGroup p (Z ⊔ S : Subgroup R) :=
        IsElementaryAbelian.isPGroup p (Z ⊔ S : Subgroup R)
      rcases hEZ_p.exists_card_eq with ⟨k, hk⟩
      have hZsub_ne_bot : (Z.subgroupOf (Z ⊔ S)) ≠ ⊥ := by
        intro hbot
        have hmap_eq : (Z.subgroupOf (Z ⊔ S)).map (Z ⊔ S).subtype = Z := by
          exact
            Subgroup.map_subgroupOf_eq_of_le
              (G := R) (H := Z) (K := Z ⊔ S) le_sup_left
        have : Z = ⊥ := by
          rw [← hmap_eq, hbot, Subgroup.map_bot]
        exact hZ_ne_bot this
      have hk_ne_zero : k ≠ 0 := by
        intro hk0
        have hcard_one : Nat.card (Z ⊔ S : Subgroup R) = 1 := by
          simpa [hk0] using hk
        have hEZ_bot : (Z ⊔ S : Subgroup R) = ⊥ :=
          (Subgroup.card_eq_one (H := Z ⊔ S)).1 hcard_one
        exact hZ_ne_bot <|
          le_bot_iff.mp (by simpa [hEZ_bot] using (le_sup_left : Z ≤ Z ⊔ S))
      have hk_ne_one : k ≠ 1 := by
        intro hk1
        have hcard_p : Nat.card (Z ⊔ S : Subgroup R) = p := by
          simpa [hk1] using hk
        have : Fact (Nat.card (Z ⊔ S : Subgroup R)).Prime := ⟨by
          simpa [hcard_p] using (Fact.out : Nat.Prime p)⟩
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Z.subgroupOf (Z ⊔ S)) with hbot | htop
        · exact hZsub_ne_bot hbot
        · exact hEZ_ne_Z <|
            le_antisymm ((Subgroup.subgroupOf_eq_top).1 htop) le_sup_left
      have hk_lt_three : k < 3 := by
        by_contra hnot
        have hk3 : 3 ≤ k := by omega
        let EZ : Subgroup R := Z ⊔ S
        let : Fact (IsPGroup p EZ) := ⟨hEZ_p⟩
        obtain ⟨D, _hDnorm, hD_le_top, hDcard⟩ :=
          lemma_1_22 (G := EZ) p (⊤ : Subgroup EZ) inferInstance k
            (by simpa [EZ] using hk) 3 hk3
        let DmapR : Subgroup R := D.map EZ.subtype
        have hDmapR_le_C : DmapR ≤ C := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨d, hdD, rfl⟩
          exact hEZ_le_C (show ((d : EZ) : R) ∈ EZ from (d : EZ).2)
        let Dsub : Subgroup C := DmapR.subgroupOf C
        have hDsub_card : Nat.card Dsub = p ^ 3 := by
          rw [natCard_subgroupOf_eq DmapR C hDmapR_le_C]
          calc
            Nat.card DmapR = Nat.card D := by
              symm
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective (f := EZ.subtype) D EZ.subtype_injective).toEquiv
            _ = p ^ 3 := hDcard
        have hDmapR_elem : IsElementaryAbelian p DmapR := by
          have hD_elem : IsElementaryAbelian p D := by
            have htop_elem : IsElementaryAbelian p (⊤ : Subgroup EZ) := by
              exact isElementaryAbelian_top (p := p) (G := EZ)
            let : IsElementaryAbelian p (⊤ : Subgroup EZ) := htop_elem
            exact isElementaryAbelian_of_le (p := p) hD_le_top
          let : IsElementaryAbelian p D := hD_elem
          simpa [DmapR] using
            IsElementaryAbelian.map_subtype (p := p) (K := EZ) (H := D)
        have hDsub_elem : IsElementaryAbelian p Dsub := by
          let : IsElementaryAbelian p DmapR := hDmapR_elem
          exact IsElementaryAbelian.subgroupOf (p := p) hDmapR_le_C
        have hDmapRG_le_cent : DmapR.map R.subtype ≤ subgroupCentralizerIn R E := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨d, hdD, rfl⟩
          exact hDmapR_le_C hdD
        let Dcent : Subgroup (subgroupCentralizerIn R E) :=
          (DmapR.map R.subtype).subgroupOf (subgroupCentralizerIn R E)
        have hDmapRG_card : Nat.card (DmapR.map R.subtype) = p ^ 3 := by
          calc
            Nat.card (DmapR.map R.subtype) = Nat.card DmapR := by
              symm
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective (f := R.subtype) DmapR R.subtype_injective).toEquiv
            _ = p ^ 3 := by
              rw [natCard_subgroupOf_eq DmapR C hDmapR_le_C] at hDsub_card
              exact hDsub_card
        have hDcent_card : Nat.card Dcent = p ^ 3 := by
          rw [natCard_subgroupOf_eq (DmapR.map R.subtype) (subgroupCentralizerIn R E)
            hDmapRG_le_cent]
          exact hDmapRG_card
        have hDcent_elem : IsElementaryAbelian p Dcent := by
          let : IsElementaryAbelian p DmapR := hDmapR_elem
          let : IsElementaryAbelian p (DmapR.map R.subtype) := by
            simpa [DmapR] using
              IsElementaryAbelian.map_subtype (p := p) (K := R) (H := DmapR)
          exact IsElementaryAbelian.subgroupOf (p := p) hDmapRG_le_cent
        let : IsElementaryAbelian p Dcent := hDcent_elem
        have hRcent_rank_ge : 3 ≤ groupRank (subgroupCentralizerIn R E) :=
          groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
            (p := p) (G := subgroupCentralizerIn R E) (B := Dcent) hDcent_card
        exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hRcent_rank_ge hRcent_rank)
      have hk_two : k = 2 := by omega
      simpa [hk_two] using hk
    have hEZ_mem : Z ⊔ S ∈ elementaryAbelianSubgroupsOfRank p 2 R :=
      ⟨hEZ_card, hEZ_elem⟩
    have hEZ_max : Z ⊔ S ∈ maximalElementaryAbelianSubgroups p R := by
      refine ⟨hEZ_elem, ?_⟩
      intro B hEZ_le_B hBelem
      let : IsElementaryAbelian p B := hBelem
      have hB_le_C : B ≤ C := by
        intro b hb
        refine ⟨b.2, ?_⟩
        intro e he
        let eR : R := ⟨e, hE_le_pCore he⟩
        have heS : eR ∈ S := by
          simpa [S, Subgroup.mem_subgroupOf] using he
        have heB : eR ∈ B := hEZ_le_B (Subgroup.mem_sup_right heS)
        exact congrArg Subtype.val <|
          (setLike_mul_comm (s := B) heB hb)
      by_cases hB_eq : B = Z ⊔ S
      · exact hB_eq.symm
      · have hlt_card : Nat.card (Z ⊔ S : Subgroup R) < Nat.card B := by
          have hle_card : Nat.card (Z ⊔ S : Subgroup R) ≤ Nat.card B :=
            Subgroup.card_le_of_le hEZ_le_B
          exact lt_of_le_of_ne hle_card fun hcard_eq =>
            hB_eq <|
              (Subgroup.eq_of_le_of_card_ge hEZ_le_B (le_of_eq hcard_eq.symm)).symm
        rcases (IsElementaryAbelian.isPGroup p B).exists_card_eq with ⟨k, hk⟩
        rw [hEZ_card, hk] at hlt_card
        have hk3 : 3 ≤ k := by
          have hk_gt_two : 2 < k :=
            (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).1 hlt_card
          omega
        let : Fact (IsPGroup p B) := ⟨IsElementaryAbelian.isPGroup p B⟩
        obtain ⟨D, _hDnorm, hD_le_B, hDcard⟩ :=
          lemma_1_22 (G := B) p (⊤ : Subgroup B) inferInstance k
            (by simpa using hk) 3 hk3
        let DmapR : Subgroup R := D.map B.subtype
        have hDmapR_le_C : DmapR ≤ C := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨d, _hdD, rfl⟩
          exact hB_le_C d.2
        let Dsub : Subgroup C := DmapR.subgroupOf C
        have hDsub_card : Nat.card Dsub = p ^ 3 := by
          rw [natCard_subgroupOf_eq DmapR C hDmapR_le_C]
          calc
            Nat.card DmapR = Nat.card D := by
              symm
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective (f := B.subtype) D B.subtype_injective).toEquiv
            _ = p ^ 3 := hDcard
        have hDmapR_elem : IsElementaryAbelian p DmapR := by
          have hD_elem : IsElementaryAbelian p D := by
            have htop_elem : IsElementaryAbelian p (⊤ : Subgroup B) := by
              exact isElementaryAbelian_top (p := p) (G := B)
            let : IsElementaryAbelian p (⊤ : Subgroup B) := htop_elem
            exact isElementaryAbelian_of_le (p := p) hD_le_B
          let : IsElementaryAbelian p D := hD_elem
          simpa [DmapR] using
            IsElementaryAbelian.map_subtype (p := p) (K := B) (H := D)
        have hDsub_elem : IsElementaryAbelian p Dsub := by
          let : IsElementaryAbelian p DmapR := hDmapR_elem
          exact IsElementaryAbelian.subgroupOf (p := p) hDmapR_le_C
        have hDmapRG_le_cent : DmapR.map R.subtype ≤ subgroupCentralizerIn R E := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨d, hdD, rfl⟩
          exact hDmapR_le_C hdD
        let Dcent : Subgroup (subgroupCentralizerIn R E) :=
          (DmapR.map R.subtype).subgroupOf (subgroupCentralizerIn R E)
        have hDmapRG_card : Nat.card (DmapR.map R.subtype) = p ^ 3 := by
          calc
            Nat.card (DmapR.map R.subtype) = Nat.card DmapR := by
              symm
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective (f := R.subtype) DmapR R.subtype_injective).toEquiv
            _ = p ^ 3 := by
              rw [natCard_subgroupOf_eq DmapR C hDmapR_le_C] at hDsub_card
              exact hDsub_card
        have hDcent_card : Nat.card Dcent = p ^ 3 := by
          rw [natCard_subgroupOf_eq (DmapR.map R.subtype) (subgroupCentralizerIn R E)
            hDmapRG_le_cent]
          exact hDmapRG_card
        have hDcent_elem : IsElementaryAbelian p Dcent := by
          let : IsElementaryAbelian p DmapR := hDmapR_elem
          let : IsElementaryAbelian p (DmapR.map R.subtype) := by
            simpa [DmapR] using
              IsElementaryAbelian.map_subtype (p := p) (K := R) (H := DmapR)
          exact IsElementaryAbelian.subgroupOf (p := p) hDmapRG_le_cent
        let : IsElementaryAbelian p Dcent := hDcent_elem
        have hRcent_rank_ge : 3 ≤ groupRank (subgroupCentralizerIn R E) :=
          groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
            (p := p) (G := subgroupCentralizerIn R E) (B := Dcent) hDcent_card
        exact False.elim ((by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hRcent_rank_ge hRcent_rank))
    have hnarrow : IsNarrowPGroup p R := by
      exact (theorem_5_3 (p := p) hpodd (R := R) hR_p hR_rank).mpr
        ⟨Z ⊔ S, hEZ_mem, hEZ_max⟩
    have hderR_p :
        IsPGroup p ((derivedSubgroup G).map (MulAut.conjNormal (H := R))) := by
      simpa [R] using
        derived_conj_image_isPGroup_of_narrow_high_rank
          (G := G) (p := p) hpodd (R := R) hnarrow hR_rank hodd
    have : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    have hUq_min :
        Uq.Normal ∧ Uq ≠ ⊥ ∧
          (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
      simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
    have : Uq.Normal := hUq_min.1
    let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
    let A : Subgroup (MulAut Uq) := φ.range
    let ψ : G →* A :=
      ((φ.comp π).codRestrict A fun g => ⟨π g, rfl⟩)
    have hderUq_p :
        IsPGroup p ((derivedSubgroup G).map ((MulAut.conjNormal (H := Uq)).comp π)) := by
      simpa [φ, Uq, π] using
        chiefFactor_derived_conj_image_isPGroup_of_pCore_action
          (G := G) (p := p) cf hcf_q hcfU hderR_p
    have hApcore_bot : pCore p A = ⊥ := by
      simpa [A, φ, Uq, π] using
        chiefFactor_conj_range_pCore_eq_bot
          (G := G) (p := p) cf hcf_q
    have hψ_surj : Function.Surjective ψ := by
      intro a
      rcases a.2 with ⟨q, hq⟩
      rcases QuotientGroup.mk'_surjective (N := cf.V) q with ⟨g, rfl⟩
      refine ⟨g, ?_⟩
      apply Subtype.ext
      exact hq
    have hmap_eq : (derivedSubgroup G).map ψ = derivedSubgroup A := by
      simpa [derivedSubgroup, derivedSeries_one] using
        map_derivedSeries_eq (f := ψ) hψ_surj 1
    have hmap_subtype_p :
        IsPGroup p (((derivedSubgroup G).map ψ).map A.subtype) := by
      have hmap_map :
          ((derivedSubgroup G).map ψ).map A.subtype =
            (derivedSubgroup G).map ((MulAut.conjNormal (H := Uq)).comp π) := by
        rw [Subgroup.map_map]
        congr 1
      rw [hmap_map]
      exact hderUq_p
    have hderA_p : IsPGroup p (derivedSubgroup A) := by
      rw [← hmap_eq]
      exact hmap_subtype_p.of_equiv
        (Subgroup.equivMapOfInjective (f := A.subtype) ((derivedSubgroup G).map ψ)
          A.subtype_injective).symm
    have hderA_le_pcore : derivedSubgroup A ≤ pCore p A :=
      le_sSup ⟨(inferInstance : (derivedSubgroup A).Normal), hderA_p⟩
    have hderA_bot : derivedSubgroup A = ⊥ := by
      exact le_antisymm (hderA_le_pcore.trans (by simp [hApcore_bot])) bot_le
    have hderψ_bot : (derivedSubgroup G).map ψ = ⊥ := by
      rw [hmap_eq, hderA_bot]
    have hcomm : ⁅derivedSubgroup G, cf.U⁆ ≤ cf.V := by
      rw [Subgroup.commutator_le]
      intro x hxder u huU
      have hxψ_mem : ψ x ∈ (derivedSubgroup G).map ψ := Subgroup.mem_map_of_mem ψ hxder
      have hxψ_bot : ψ x ∈ (⊥ : Subgroup A) := by
        rw [hderψ_bot] at hxψ_mem
        exact hxψ_mem
      have hxψ_eq : ψ x = 1 := Subgroup.mem_bot.mp hxψ_bot
      let uq : Uq := ⟨π u, Subgroup.mem_map_of_mem π huU⟩
      have hfix : (φ (π x)) uq = uq := by
        simpa [ψ, A, φ, π] using congrArg (fun a : A => ((a : MulAut Uq) uq)) hxψ_eq
      have hconj : π x * π u * (π x)⁻¹ = π u := by
        simpa [φ, uq, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
      have hcomm_eq_one : ⁅π x, π u⁆ = 1 := by
        rw [commutatorElement_def]
        calc
          π x * π u * (π x)⁻¹ * (π u)⁻¹ = π u * (π u)⁻¹ := by rw [hconj]
          _ = 1 := by simp
      have : π ⁅x, u⁆ = 1 := by
        simpa [map_commutatorElement] using hcomm_eq_one
      exact (QuotientGroup.eq_one_iff (N := cf.V) ⁅x, u⁆).1 this
    exact
      (le_centralizerOfChiefFactor_iff
        (G := G) (H := (⊤ : Subgroup G)) (N := derivedSubgroup G) (cf := cf)).2
        ⟨by simp, hcomm⟩

private theorem CFSG.derivedSubgroup_le_fitting_of_centralizes_restricted_chiefFactors
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hchief :
      ∀ cf : ChiefFactor G, cf.U ≤ fittingSubgroup G →
        derivedSubgroup G ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf) :
    derivedSubgroup G ≤ fittingSubgroup G := by
  have hder_norm : (derivedSubgroup G).Normal := by infer_instance
  have hder_le_fitOf :
      derivedSubgroup G ≤ fittingSubgroupOf (G := G) (derivedSubgroup G) := by
    exact
      normal_le_fittingSubgroupOf_of_centralizes_restricted_chiefFactors
        (G := G) (H := derivedSubgroup G) hder_norm
      (fun cf hcfU =>
        hchief cf (hcfU.trans
          (fittingSubgroupOf_le_fittingSubgroup
            (G := G) (H := derivedSubgroup G) hder_norm)))
  exact hder_le_fitOf.trans
    (fittingSubgroupOf_le_fittingSubgroup
      (G := G) (H := derivedSubgroup G) hder_norm)

public theorem CFSG.theorem_5_7
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {E : Subgroup G} [IsElementaryAbelian p E] (hE_le : E ≤ fittingSubgroup G)
    (hcent_rank : groupRank (subgroupCentralizerIn (fittingSubgroup G) E) ≤ 2) :
    derivedSubgroup G ≤ fittingSubgroup G := by
  exact derivedSubgroup_le_fitting_of_centralizes_restricted_chiefFactors (G := G)
    (fun cf hcfU =>
      theorem_5_7_chief_factor_centralized
        (G := G) (p := p) hodd hp_dvd hE_le hcent_rank cf hcfU)
