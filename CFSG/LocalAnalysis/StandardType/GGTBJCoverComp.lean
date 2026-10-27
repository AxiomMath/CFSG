module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggCover_component {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {g : G} (hBs : IsElemAbelian p Bs) (hgBs : g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {H : Type} [Group H] [Finite H] (ψ : ↥X →* H) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥X) (Λ : H →* MulAut ↥X)
    (hΛc : ∀ x, Λ (ψ x) = MulAut.conj x) (hΛn : ∀ h l, ψ (Λ h l) = h * ψ l * h⁻¹)
    {c : H} (hc : Λ c = ggGamma X hN ⟨g, hgBs⟩)
    (hJX : J ≤ X) (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G))) :
    IsComponentOf ((J.subgroupOf X).map ψ) (Subgroup.centralizer ({c} : Set H)) ∧
      ∀ (b : ↥Bs) (c' : H), Λ c' = ggGamma X hN b →
        c' ∈ Subgroup.centralizer (((J.subgroupOf X).map ψ : Subgroup H) : Set H) →
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  constructor
  · have hcent : ((X ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf X).map ψ =
        Subgroup.centralizer ({c} : Set H) := by
      apply le_antisymm
      · rintro y ⟨x, hx, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hx' : (x : G) ∈ X ⊓ Subgroup.centralizer ({g} : Set G) :=
          Subgroup.mem_subgroupOf.mp hx
        have hxg : (x : G) * g = g * (x : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hx'.2
        have hΛcx : Λ c x = x := by
          apply Subtype.ext
          have h1 : ((Λ c x : ↥X) : G) = g * (x : G) * g⁻¹ := by
            rw [hc]
            exact ggGamma_coe X hN ⟨g, hgBs⟩ x
          rw [h1]
          calc g * (x : G) * g⁻¹ = (x : G) * g * g⁻¹ := by rw [hxg]
            _ = x := by group
        have h1 : ψ x = c * ψ x * c⁻¹ := by
          have h2 := hΛn c x
          rwa [hΛcx] at h2
        calc ψ x * c = (c * ψ x * c⁻¹) * c := by
              conv_lhs => rw [h1]
          _ = c * ψ x := by group
      · intro h hh
        obtain ⟨x, rfl⟩ := hψ h
        have hcomm : c * ψ x = ψ x * c :=
          (Subgroup.mem_centralizer_singleton_iff.mp hh).symm
        let g₀ : ↥Bs := ⟨g, hgBs⟩
        have hg₀p : g₀ ^ p = 1 := by
          apply Subtype.ext
          exact hBs.2 g hgBs
        let A : Subgroup ↥Bs := Subgroup.zpowers g₀
        have hAp : IsPGroup p A := by
          change IsPGroup p (Subgroup.zpowers g₀)
          exact IsPGroup.of_card_dvd_pow (n := 1) (by
            rw [Nat.card_zpowers]
            simpa using orderOf_dvd_of_pow_eq_one hg₀p)
        let α : A →* MulAut ↥X := (ggGamma X hN).comp A.subtype
        have hcop : ¬ p ∣ Nat.card (ψ.ker) := by
          intro hdvd
          obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
          have hzmem : (z : ↥X) ∈ Subgroup.center ↥X := hker z.2
          have hzp : (z : ↥X) ^ p = 1 := by
            have h : (z : ψ.ker) ^ p = 1 := by
              rw [← hz]
              exact pow_orderOf_eq_one z
            simpa using congrArg Subtype.val h
          have hz1val : (z : ↥X) = 1 := hZp _ hzmem hzp
          have hz1 : z = 1 := Subtype.ext hz1val
          rw [hz1] at hz
          have hp1 : p = 1 := by simpa using hz.symm
          exact (Fact.out : p.Prime).ne_one hp1
        have hinv : ∀ a : A, ∀ y : ↥X, x⁻¹ * y ∈ ψ.ker →
            x⁻¹ * α a y ∈ ψ.ker := by
          intro a y hy
          rw [MonoidHom.mem_ker] at hy ⊢
          have hyψ : ψ y = ψ x := by
            have h1 : ψ (x⁻¹ * y) = 1 := hy
            rw [map_mul, map_inv] at h1
            exact (eq_of_inv_mul_eq_one h1).symm
          have hαψ : ψ (α a y) = ψ x := by
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
            have hαeq : α a = Λ (c ^ k) := by
              change ggGamma X hN (a : ↥Bs) = Λ (c ^ k)
              rw [← hk]
              calc ggGamma X hN (g₀ ^ k) = (ggGamma X hN g₀) ^ k := map_zpow (ggGamma X hN) g₀ k
                _ = (Λ c) ^ k := by rw [hc]
                _ = Λ (c ^ k) := (map_zpow Λ c k).symm
            calc ψ (α a y) = ψ (Λ (c ^ k) y) := by rw [hαeq]
              _ = c ^ k * ψ y * (c ^ k)⁻¹ := hΛn (c ^ k) y
              _ = c ^ k * ψ x * (c ^ k)⁻¹ := by rw [hyψ]
              _ = ψ x := by
                have hcomm' : Commute c (ψ x) := hcomm
                calc c ^ k * ψ x * (c ^ k)⁻¹ = ψ x * c ^ k * (c ^ k)⁻¹ := by
                      rw [hcomm'.zpow_left k]
                  _ = ψ x := by group
          rw [map_mul, map_inv, hαψ, inv_mul_cancel]
        obtain ⟨cX, hcN, hcfix⟩ :=
          (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p hAp α (ψ.ker)
            hcop x).2 hinv
        refine ⟨cX, ?_, ?_⟩
        · refine Subgroup.mem_subgroupOf.mpr ⟨cX.2, ?_⟩
          change (cX : G) ∈ Subgroup.centralizer ({g} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hgen : α ⟨g₀, Subgroup.mem_zpowers g₀⟩ cX = cX := hcfix _
          have hgen' : ggGamma X hN g₀ cX = cX := by simpa [α] using hgen
          have hΛ : Λ c cX = cX := by
            rw [hc]
            exact hgen'
          have hconj : ((Λ c cX : ↥X) : G) = g * (cX : G) * g⁻¹ := by
            rw [hc]
            simpa using ggGamma_coe X hN g₀ cX
          have hval : g * (cX : G) * g⁻¹ = (cX : G) := by
            calc g * (cX : G) * g⁻¹ = ((Λ c cX : ↥X) : G) := hconj.symm
              _ = (cX : G) := congrArg Subtype.val hΛ
          calc (cX : G) * g = (g * (cX : G) * g⁻¹) * g := by rw [hval]
            _ = g * (cX : G) := by group
        · have h1 : ψ (x⁻¹ * cX) = 1 := hcN
          rw [map_mul, map_inv] at h1
          exact (eq_of_inv_mul_eq_one h1).symm
    have hsubX : IsSubnormal (J.subgroupOf X)
        ((X ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf X) := by
      have h := hcomp.2.1.comap X.subtype
      rwa [Subgroup.comap_subtype, Subgroup.comap_subtype] at h
    have hsubMap : IsSubnormal ((J.subgroupOf X).map ψ)
        (((X ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf X).map ψ) :=
      hsubX.map ψ
    have hsub : IsSubnormal ((J.subgroupOf X).map ψ)
        (Subgroup.centralizer ({c} : Set H)) := by
      rwa [hcent] at hsubMap
    have hle : (J.subgroupOf X).map ψ ≤ Subgroup.centralizer ({c} : Set H) := by
      rw [← hcent]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hcomp.1 hx)
    have hJq : CFSG.Open.IsQuasisimple J := hcomp.2.2
    have hKq : CFSG.Open.IsQuasisimple (J.subgroupOf X) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJX) hJq
    let φJ : ↥(J.subgroupOf X) →* H := ψ.comp (J.subgroupOf X).subtype
    have hφJker : φJ.ker ≤ Subgroup.center ↥(J.subgroupOf X) := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hzψ : ψ (z : ↥X) = 1 := by
        change ψ ((J.subgroupOf X).subtype z) = 1
        exact hz
      have hzcenter : (z : ↥X) ∈ Subgroup.center ↥X := hker hzψ
      exact Subgroup.mem_center_iff.mp hzcenter (w : ↥X)
    have hquotq : CFSG.Open.IsQuasisimple (↥(J.subgroupOf X) ⧸ φJ.ker) :=
      CFSG.ComponentClassification.Quasisimple.central_quotient hKq φJ.ker hφJker
    have hrangeq : CFSG.Open.IsQuasisimple ↥φJ.range :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (QuotientGroup.quotientKerEquivRange φJ).symm hquotq
    have hrange : φJ.range = (J.subgroupOf X).map ψ := by
      change (ψ.comp (J.subgroupOf X).subtype).range = (J.subgroupOf X).map ψ
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hq : CFSG.Assembly.IsQuasisimple ((J.subgroupOf X).map ψ) := by
      rw [← hrange]
      exact hrangeq
    exact ⟨hle, hsub, hq⟩
  · intro b c' hc' hc'cent
    let zval : ↥J → G := fun j => (j : G)⁻¹ * (b : G) * (j : G) * (b : G)⁻¹
    have hconjX : ∀ j : ↥J, (b : G) * (j : G) * (b : G)⁻¹ ∈ X := by
      intro j
      exact (Subgroup.mem_normalizer_iff.mp (hN b.2) (j : G)).mp (hJX j.2)
    have hzmemX : ∀ j : ↥J, zval j ∈ X := by
      intro j
      have h : zval j = (j : G)⁻¹ * ((b : G) * (j : G) * (b : G)⁻¹) := by
        simp only [zval]
        group
      rw [h]
      exact X.mul_mem (X.inv_mem (hJX j.2)) (hconjX j)
    let zX : ↥J → ↥X := fun j => ⟨zval j, hzmemX j⟩
    have hzψ : ∀ j : ↥J, ψ (zX j) = 1 := by
      intro j
      let jX : ↥X := ⟨(j : G), hJX j.2⟩
      have hzX_eq : zX j = (jX)⁻¹ * ggGamma X hN b jX := by
        apply Subtype.ext
        simp only [zX, zval, jX, Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe]
        group
      rw [hzX_eq, map_mul, map_inv]
      have hΛ := hΛn c' jX
      rw [hc'] at hΛ
      rw [hΛ]
      have hmemj : ψ jX ∈ ((J.subgroupOf X).map ψ : Subgroup H) :=
        Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr j.2)
      have hcommj : c' * ψ jX = ψ jX * c' :=
        (Subgroup.mem_centralizer_iff.mp hc'cent (ψ jX) hmemj).symm
      rw [show c' * ψ jX * c'⁻¹ = ψ jX by rw [hcommj]; group]
      exact inv_mul_cancel _
    have hzcenter : ∀ j : ↥J, zX j ∈ Subgroup.center ↥X :=
      fun j => hker (MonoidHom.mem_ker.mpr (hzψ j))
    have hz_mul : ∀ j k : ↥J, zX (j * k) = zX j * zX k := by
      intro j k
      apply Subtype.ext
      have hcommval : (k : G)⁻¹ * zval j = zval j * (k : G)⁻¹ := by
        have h := Subgroup.mem_center_iff.mp (hzcenter j)
          (⟨(k : G)⁻¹, hJX (J.inv_mem k.2)⟩ : ↥X)
        exact congrArg Subtype.val h
      change zval (j * k) = zval j * zval k
      calc zval (j * k)
          = (k : G)⁻¹ * zval j * ((b : G) * (k : G) * (b : G)⁻¹) := by
            simp only [zval, Subgroup.coe_mul]
            group
        _ = zval j * (k : G)⁻¹ * ((b : G) * (k : G) * (b : G)⁻¹) := by rw [hcommval]
        _ = zval j * zval k := by
            simp only [zval]
            group
    let φ : ↥J →* ↥X := MonoidHom.mk' zX hz_mul
    have hφrange : φ.range ≤ Subgroup.center ↥X := by
      rintro _ ⟨j, rfl⟩
      exact hzcenter j
    haveI : IsMulCommutative ↥φ.range := by
      rw [← Subgroup.le_centralizer_iff_isMulCommutative]
      exact hφrange.trans (Subgroup.center_le_centralizer (φ.range : Set ↥X))
    haveI : Group.IsPerfect ↥J := ⟨hcomp.2.2.1⟩
    haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    have hφone : ∀ j : ↥J, φ j = 1 := by
      intro j
      have h1 : (⟨φ j, ⟨j, rfl⟩⟩ : φ.range) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val h1
    have hzone : ∀ j : ↥J, zX j = 1 := by
      intro j
      simpa [φ] using hφone j
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    let jJ : ↥J := ⟨j, hj⟩
    have h1 : (j : G)⁻¹ * (b : G) * (j : G) * (b : G)⁻¹ = 1 := by
      have h := congrArg Subtype.val (hzone jJ)
      simpa [zX, zval, jJ] using h
    calc j * (b : G) = j * ((j : G)⁻¹ * (b : G) * (j : G) * (b : G)⁻¹) * (b : G) := by
          rw [h1]
          group
      _ = (b : G) * j := by group

end CFSG.StandardType

end
