module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Res
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

theorem point_component {J : Type} [Group J] (hJ : J2Facts J) {p : ℕ} (hp : p.Prime)
    (hp7 : ¬ (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7)) {x c d : G} (hxp : x ^ p = 1)
    (hcY : c ∈ Subgroup.centralizer ({x} : Set G)) (hdY : d ∈ Subgroup.centralizer ({x} : Set G))
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* J) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hθ : ¬ p ∣ Nat.card (aschbacherSolvableCore 3 ↥L)) (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) :
    ∃ M : Subgroup ↥(Subgroup.centralizer ({x} : Set G)),
      M ∈ thetaComponentsAt 3 (⟨c, hcY⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∧
      ∃ hdM : (⟨d, hdY⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈ M,
        ∃ φ : ↥M →* J, Function.Surjective φ ∧ φ ⟨_, hdM⟩ ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hJ.finite
  obtain ⟨hLc, hLsub, -⟩ := thetaComponentsAt_facts hL
  set θL := aschbacherSolvableCore 3 ↥L with hθL
  have hθsol : Group.IsSolvable θL :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  let τ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxL⟩
  have hτ : ∀ l : ↥L, ((τ l : ↥L) : G) = x * (l : G) * x⁻¹ := fun l => rfl
  have hτp : τ ^ p = 1 := by
    have h : (⟨x, hxL⟩ : Subgroup.normalizer (L : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [← map_pow, h, map_one]
  have hσ1 : Sec4.thetaQuotMulAut ↥L τ = 1 :=
    hJ.eq_one_of_pow_prime e hp hp7 (by rw [← map_pow, hτp, map_one])
  have hτθ : ∀ n ∈ θL, τ n ∈ θL := fun n hn => by
    have h := Sec4.map_aschbacherSolvableCore τ
    have h' : τ n ∈ (aschbacherSolvableCore 3 ↥L).map (τ : ↥L →* ↥L) :=
      Subgroup.mem_map_of_mem (τ : ↥L →* ↥L) hn
    rw [h] at h'
    exact h'
  have hlτ : ∀ l : ↥L, l⁻¹ * τ l ∈ θL := fun l => by
    have h := congrArg (fun σ : MulAut (↥L ⧸ θL) => σ (l : ↥L ⧸ θL)) hσ1
    simp only [Sec4.thetaQuotMulAut_mk, MulAut.one_apply] at h
    exact QuotientGroup.eq.mp h.symm
  have hcos : ∀ l : ↥L, ∃ n ∈ θL, τ (l * n) = l * n := fun l =>
    exists_mul_fixed (p := p) τ hτp θL hτθ hθ l (hlτ l)
  set Y := Subgroup.centralizer ({x} : Set G) with hYdef
  set X : Subgroup G := L ⊓ Y with hXdef
  have hXL : X ≤ L := inf_le_left
  have hXY : X ≤ Y := inf_le_right
  let ρ : ↥X →* J :=
    e.toMonoidHom.comp ((QuotientGroup.mk' θL).comp (Subgroup.inclusion hXL))
  have hρapp : ∀ y : ↥X, ρ y = e ((⟨(y : G), hXL y.2⟩ : ↥L) : ↥L ⧸ θL) := fun y => rfl
  have hρ : Function.Surjective ρ := by
    intro j
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm j)
    obtain ⟨n, hn, hfix⟩ := hcos l
    have hu : ((l * n : ↥L) : G) ∈ Y := by
      rw [hYdef, Subgroup.mem_centralizer_singleton_iff]
      have h1 : x * ((l * n : ↥L) : G) * x⁻¹ = ((l * n : ↥L) : G) := by
        have := congrArg Subtype.val hfix
        rwa [hτ] at this
      calc ((l * n : ↥L) : G) * x = (x * ((l * n : ↥L) : G) * x⁻¹) * x := by rw [h1]
        _ = x * ((l * n : ↥L) : G) := inv_mul_cancel_right _ _
    refine ⟨⟨((l * n : ↥L) : G), (l * n).2, hu⟩, ?_⟩
    rw [hρapp]
    change e ((l * n : ↥L) : ↥L ⧸ θL) = j
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one, hl]
    exact e.apply_symm_apply j
  have hker : Group.IsSolvable ρ.ker ∧ ¬ 3 ∣ Nat.card ρ.ker := by
    let f : ρ.ker →* θL :=
      ((Subgroup.inclusion hXL).comp ρ.ker.subtype).codRestrict θL (fun y => by
        have h1 : ρ y.1 = 1 := y.2
        rw [hρapp] at h1
        exact (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp h1))
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun z : θL => ((z : ↥L) : G)) hab))
    haveI := hθsol
    exact ⟨Group.isSolvable_of_isSolvable_injective hf, fun h =>
      three_not_dvd_card_aschbacherSolvableCore (G := ↥L)
        (h.trans (Subgroup.card_dvd_of_injective f hf))⟩
  obtain ⟨hRsurj, hRq, hRd⟩ := hJ.residual_component ρ hρ hker.1 hker.2
  obtain ⟨-, hRchar, hRperf, -⟩ := perfect_residual_characterization (G := ↥X)
  set R := perfectResidual ↥X with hRdef
  set M : Subgroup G := R.map X.subtype with hMdef
  have hMX : M ≤ X := Subgroup.map_subtype_le R
  have hMY : M ≤ Y := hMX.trans hXY
  have hMc : M ≤ Subgroup.centralizer ({c} : Set G) := hMX.trans (hXL.trans hLc)
  have hdXmem : d ∈ X := Subgroup.mem_inf.mpr ⟨hdL, hdY⟩
  have hdM : d ∈ M := by
    have h3 : (⟨d, hdXmem⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    exact ⟨⟨d, hdXmem⟩, hRd _ h3, rfl⟩
  set D := Subgroup.centralizer ({(⟨c, hcY⟩ : ↥Y)} : Set ↥Y) with hDdef
  let MY : Subgroup ↥Y := M.subgroupOf Y
  have hMYD : MY ≤ D := fun y hy => by
    have hyM : (y : G) ∈ M := hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hMc hyM)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext h1)
  have hsubMX : SubnormalIn M X := by
    change (M.subgroupOf X).IsSubnormal
    have h : M.subgroupOf X = R := Subgroup.comap_map_eq_self_of_injective X.subtype_injective R
    rw [h]
    haveI := hRchar
    exact Subgroup.Normal.isSubnormal inferInstance
  have hsubXC : SubnormalIn X (Subgroup.centralizer ({c} : Set G) ⊓ Y) :=
    SubnormalIn.inf Y (hLsub : SubnormalIn L (Subgroup.centralizer ({c} : Set G)))
  have hsubMC : SubnormalIn M (Subgroup.centralizer ({c} : Set G) ⊓ Y) :=
    SubnormalIn.trans hMX (le_inf (hXL.trans hLc) hXY) hsubMX hsubXC
  have hsubMY : SubnormalIn MY D := by
    have h := SubnormalIn.subgroupOf Y
      (inf_le_right : Subgroup.centralizer ({c} : Set G) ⊓ Y ≤ Y) hsubMC
    have hD : (Subgroup.centralizer ({c} : Set G) ⊓ Y).subgroupOf Y = D := by
      ext y
      constructor
      · intro hy
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext h1)
      · intro hy
        have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr h1, y.2⟩)
    rw [hD] at h
    exact h
  let N : Subgroup ↥D := MY.subgroupOf D
  have eR : ↥R ≃* ↥N :=
    (R.equivMapOfInjective X.subtype X.subtype_injective).trans
      ((Subgroup.subgroupOfEquivOfLe hMY).symm.trans (Subgroup.subgroupOfEquivOfLe hMYD).symm)
  have hN : N ∈ thetaComponents 3 ↥D := by
    refine ⟨?_, hsubMY, isQuasisimple_thetaQuot_of_mulEquiv eR hRq⟩
    haveI := hRperf
    exact Group.IsPerfect.ofSurjective (f := eR.toMonoidHom) eR.surjective
  have hdMY : (⟨d, hdY⟩ : ↥Y) ∈ MY := hdM
  refine ⟨MY, ⟨N, hN, ?_⟩, hdMY, ?_⟩
  · show (MY.subgroupOf D).map D.subtype = MY
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hMYD
  · let incl : ↥MY →* ↥X := (Y.subtype.comp MY.subtype).codRestrict X (fun m => hMX m.2)
    refine ⟨ρ.comp incl, ?_, ?_⟩
    · intro j
      obtain ⟨r, hr⟩ := hRsurj j
      have hmM : ((R.subtype r : ↥X) : G) ∈ M := ⟨R.subtype r, r.2, rfl⟩
      refine ⟨⟨⟨((R.subtype r : ↥X) : G), hMY hmM⟩, hmM⟩, ?_⟩
      exact hr
    · intro h1
      have h2 : ρ ⟨d, hdXmem⟩ = 1 := h1
      rw [hρapp] at h2
      have h3 : ((⟨d, hdL⟩ : ↥L) : ↥L ⧸ θL) = 1 := e.map_eq_one_iff.mp h2
      have h4 : (⟨d, hdL⟩ : ↥L) ∈ θL := (QuotientGroup.eq_one_iff _).mp h3
      have h5 : (⟨d, hdL⟩ : ↥L) = 1 :=
        eq_one_of_pow_three_of_not_dvd
          (three_not_dvd_card_aschbacherSolvableCore (G := ↥L)) h4
          (Subtype.ext (by simpa using hd3))
      exact hd1 (congrArg Subtype.val h5)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
