module

public import CFSG.Quasithin.EmptyFaithful.R3c2Theta
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.R3c2Base
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top quotPCore_subgroupOf_equiv
  pRank_subgroupOf_eq map_oPrimeResidualOf_top)

variable {G : Type} [Group G]

theorem le_thetaOf_of_surjection [Finite G] {H L : Subgroup G} (hLH : L ≤ H) (hperf : ⁅L, L⁆ = L)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {X : Type*} [Group X] [Finite X] (ψ : ↥L →* X) (hψ : Function.Surjective ψ)
    (hker3 : ∀ x ∈ ψ.ker, orderOf x ≠ 3)
    (hgen : Subgroup.closure {y : X | orderOf y = 3} = ⊤) (hX3 : 3 ∣ Nat.card X) : L ≤ thetaOf H := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup ↥L := Subgroup.closure {x : ↥L | orderOf x = 3} with hD
  have hDn : D.Normal := ⟨fun n hn g => by
    refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ D) ?_ ?_ ?_ ?_ hn
    · intro y hy
      apply Subgroup.subset_closure
      show orderOf (g * y * g⁻¹) = 3
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
      simpa using this.trans hy
    · simp
    · intro x y _ _ hx hy
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact D.mul_mem hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact D.inv_mem hx⟩
  have hDθ : ∀ x ∈ D, (x : G) ∈ thetaOf H := by
    intro x hx
    refine Subgroup.closure_induction (p := fun (x : ↥L) _ => (x : G) ∈ thetaOf H) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Subgroup.subset_closure ⟨hLH y.2, (Subgroup.orderOf_coe y).trans hy⟩
    · exact Subgroup.one_mem _
    · intro x y _ _ hx hy
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      exact Subgroup.inv_mem _ hx
  have hψD : D.map ψ = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro a ha
    obtain ⟨x, hxa, hx3⟩ := exists_orderOf_three_lift ψ hker3 (hψ a) ha
    exact ⟨x, Subgroup.subset_closure hx3, hxa⟩
  have hDK : ∀ l : ↥L, ∃ d ∈ D, d⁻¹ * l ∈ ψ.ker := by
    intro l
    have : ψ l ∈ D.map ψ := hψD ▸ Subgroup.mem_top _
    obtain ⟨d, hd, hdl⟩ := this
    exact ⟨d, hd, by rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, inv_mul_cancel]⟩
  have hnotall : (ψ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ≠ ⊤ := by
    intro htop
    obtain ⟨x3, hx3⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 hX3
    obtain ⟨l, hl⟩ := hψ x3
    have hl' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l ∈ ψ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkl⟩ := hl'
    have ho : k⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq]
      exact hkl
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨k⁻¹ * l, ho⟩
    have hψl : ψ l = ψ (k⁻¹ * l) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
    have h2 : (ψ l) ^ 2 ^ m = 1 := by
      rw [hψl, ← map_pow]
      have : (k⁻¹ * l) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      rw [this, map_one]
    rw [hl] at h2
    have h3 : orderOf x3 ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
    rw [hx3] at h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have : (ψ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hKcen := le_center_of_normal_ne_top hQ hnotall
  set g : ↥ψ.ker →* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp ψ.ker.subtype with hg
  have hgr : ∀ a b : g.range, a * b = b * a := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    have ha : g a ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := hKcen ⟨(a : ↥L), a.2, rfl⟩
    exact (Subgroup.mem_center_iff.1 ha (g b)).symm
  have : Group.IsSolvable ↥g.range := Group.isSolvable_of_comm hgr
  have hker2 : IsPGroup 2 ↥g.ker := by
    intro x
    have hxg : g x.1 = 1 := x.2
    have hmem : ((x.1 : ↥ψ.ker) : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).1 hxg
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
    exact ⟨m, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hm))⟩
  have : Group.IsNilpotent ↥g.ker := hker2.isNilpotent
  have : Group.IsSolvable ↥ψ.ker :=
    Group.isSolvable_of_ker_le_range g.ker.subtype g.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  set q : ↥ψ.ker →* (↥L ⧸ D) := (QuotientGroup.mk' D).comp ψ.ker.subtype with hq
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨d, hd, hk⟩ := hDK l
    refine ⟨⟨d⁻¹ * l, hk⟩, ?_⟩
    show (QuotientGroup.mk (d⁻¹ * l) : ↥L ⧸ D) = QuotientGroup.mk l
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d⁻¹).2 (D.inv_mem hd), one_mul]
  have : Group.IsSolvable (↥L ⧸ D) := Group.isSolvable_of_surjective hqs
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  have hcomm : commutator (↥L ⧸ D) = ⊤ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ (QuotientGroup.mk' D)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective D),
      ← commutator_def, hLperf.commutator_eq_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective D)] at h1
    rw [commutator_def]
    exact h1.symm
  have hsub : Subsingleton (↥L ⧸ D) := by
    by_contra hns
    have : Nontrivial (↥L ⧸ D) := not_subsingleton_iff_nontrivial.1 hns
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥L ⧸ D)).ne hcomm
  intro l hl
  have hlD : (⟨l, hl⟩ : ↥L) ∈ D :=
    (QuotientGroup.eq_one_iff _).1 (Subsingleton.elim _ _)
  exact hDθ _ hlD


theorem eq_thetaOf_of_a318_of_group [Finite G] (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {H L : Subgroup G} (hH : SQTKGroup ↥H) (hL : L ∈ cComp H)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hr : 2 ≤ CFSG.Open.pRank 3 L)
    (hn2 : ¬ A318Case2 (starImage 3 (L.subgroupOf H)))
    (hn3 : A318Case3Group ↥(starImage 3 (L.subgroupOf H)) →
      ¬ A318Case3b (starImage 3 (L.subgroupOf H))) (hθ : L ≤ thetaOf H) :
    L = thetaOf H := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hSQ := SQTKHyp.of_sqtkGroup ↥H hH
  have hLc := subgroupOf_mem_cComp hL
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr' : 1 < CFSG.Open.pRank 3 (L.subgroupOf H) := by
    rw [pRank_subgroupOf_eq hLH Nat.prime_three (by norm_num), ← R3c.pRank_three_eq_pCore_quotient L]
    omega
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' Nat.prime_three (by norm_num) hr'
  have hLmap : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3g, h3⟩
  · have h1' : L = oPrimeResidualOf 3 H := by rw [← map_oPrimeResidualOf_top, ← h1, hLmap]
    exact le_antisymm hθ (h1' ▸ thetaOf_le_oPrimeResidualOf_three H)
  · exact absurd h2 hn2
  · rcases h3 with h | h
    · rw [← hLmap, h, map_thetaOf_top]
    · exact absurd h (hn3 h3g)

end CFSG.Quasithin.R3c2
