module

public import CFSG.Quasithin.EmptyFaithful.S151S5A
public import CFSG.Quasithin.EmptyFaithful.S151S4D

public section

namespace CFSG.Quasithin.S151S5

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_of_isSubnormal' {H K : Subgroup G} (h : IsSubnormal H K) :
    pCoreOf 2 H ≤ pCoreOf 2 K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    have hHM : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hle)
      (hHM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem inf_pCoreOf_eq {L X : Subgroup G} (hLX : L ≤ X) (hsub : IsSubnormal L X) :
    L ⊓ pCoreOf 2 X = pCoreOf 2 L := by
  apply le_antisymm
  · have hQN : L ≤ Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) :=
      hLX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    have hN : L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 X : Subgroup G) : Set G) :=
      fun x hx => zb_mem_normalizer_inf (Subgroup.le_normalizer hx) (hQN hx)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right)
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) (pCoreOf_le_of_isSubnormal' hsub)

theorem charTwo_sup_of_simple_comp {L S : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hsub : IsSubnormal L (L ⊔ S)) (hperf : ⁅L, L⁆ = L) (hchar : CharTwo L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hz : ∀ x : ↥L ⧸ CFSG.pCore 2 ↥L, (∀ y, y * x = x * y) → x = 1) : CharTwo (L ⊔ S) := by
  classical
  set X : Subgroup G := L ⊔ S with hXdef
  have hLX : L ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  set Q' : Subgroup ↥X := CFSG.pCore 2 ↥X with hQ'def
  have hQ'n : Q'.Normal := CFSG.pCore_normal
  have hQamb : pCoreOf 2 X = Q'.map X.subtype := by
    unfold pCoreOf
    try with_reducible rfl
  have hmemQ : ∀ x : ↥X, x ∈ Q' ↔ (x : G) ∈ pCoreOf 2 X := by
    intro x
    rw [hQamb]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
  let π : ↥X →* ↥X ⧸ Q' := QuotientGroup.mk' Q'
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q'
  have hO : CFSG.pCore 2 (↥X ⧸ Q') = ⊥ := pCore_two_quotient_eq_bot
  let ψ : ↥L →* ↥X ⧸ Q' := π.comp (Subgroup.inclusion hLX)
  let J : Subgroup (↥X ⧸ Q') := ψ.range
  have hJeq : J = (L.subgroupOf X).map π := by
    show ψ.range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkerψ : ψ.ker = CFSG.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    have h0 : ψ x = 1 ↔ Subgroup.inclusion hLX x ∈ Q' :=
      QuotientGroup.eq_one_iff (N := Q') (Subgroup.inclusion hLX x)
    rw [h0, hmemQ]
    show (x : G) ∈ pCoreOf 2 X ↔ _
    constructor
    · intro hx
      have h1 : (x : G) ∈ L ⊓ pCoreOf 2 X := ⟨x.2, hx⟩
      rw [inf_pCoreOf_eq hLX hsub] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = x := Subtype.ext hyx
      rw [this] at hy
      assumption
    · intro hx
      have h1 : (x : G) ∈ pCoreOf 2 L := ⟨x, by assumption, rfl⟩
      exact pCoreOf_le_of_isSubnormal' hsub h1
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  have hJq : CFSG.IsQuasisimple ↥J := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hJsub : J.IsSubnormal := by
    rw [hJeq]
    exact ((isSubnormal_iff_subgroupOf hLX).mp hsub).map hπs
  have hJcomp : CFSG.IsComponent J := ⟨hJq, hJsub⟩
  have hJz : ∀ x ∈ J, (∀ y ∈ J, y * x = x * y) → x = 1 := by
    intro x hx hxc
    obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
    have ha1 : a = 1 := by
      apply hz a
      intro b
      have h1 := hxc (e b : ↥X ⧸ Q') (e b).2
      apply e.injective
      rw [map_mul, map_mul, ha]
      exact Subtype.ext h1
    rw [ha1, map_one] at ha
    exact congrArg Subtype.val ha.symm
  let Sb : Subgroup (↥X ⧸ Q') := (S.subgroupOf X).map π
  have hSb2 : IsPGroup 2 ↥Sb := (CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le hSX hS2).map π
  have hLS : L.subgroupOf X ⊔ S.subgroupOf X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLX, Subgroup.map_subgroupOf_eq_of_le hSX,
      Subgroup.map_top, Subgroup.range_subtype]
  have hgen : J ⊔ Sb = ⊤ := by
    rw [hJeq, ← Subgroup.map_sup, hLS, Subgroup.map_top_of_surjective π hπs]
  let Nc : Subgroup ↥X := Subgroup.centralizer (Q' : Set ↥X)
  have hNcn : Nc.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q' := by
      have := hQ'n.conj_mem q hq g⁻¹
      simpa using this
    have h1 := hn _ hq'
    calc q * (g * n * g⁻¹) = g * ((g⁻¹ * q * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
      _ = (g * n * g⁻¹) * q := by group
  have hNbn : (Nc.map π).Normal := hNcn.map π hπs
  have hNcQ : Nc ≤ Q' := by
    rcases component_le_or_normal_eq_bot hJcomp hJz hSb2 hgen hO hNbn with hJN | hNb
    · exfalso
      set N : Subgroup G := X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) with hNdef
      set Q : Subgroup G := pCoreOf 2 X with hQdef
      have hQX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
      have hNX : N ≤ X := inf_le_left
      have hQnorm : X ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
      have hconjN : ∀ x ∈ X, ∀ h ∈ N, x * h * x⁻¹ ∈ N := by
        intro x hx h hh
        refine ⟨X.mul_mem (X.mul_mem hx hh.1) (X.inv_mem hx), Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
        have hq' : x⁻¹ * q * x ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (hQnorm (X.inv_mem hx)) q).mp hq
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hh.2 _ hq'
        calc q * (x * h * x⁻¹) = x * ((x⁻¹ * q * x) * h) * x⁻¹ := by group
          _ = x * (h * (x⁻¹ * q * x)) * x⁻¹ := by rw [h1]
          _ = (x * h * x⁻¹) * q := by group
      have hXN : X ≤ Subgroup.normalizer (N : Set G) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro h
        refine ⟨fun hh => hconjN x hx h hh, fun hh => ?_⟩
        have := hconjN x⁻¹ (X.inv_mem hx) _ hh
        simpa [mul_assoc] using this
      have hLNQ : L ≤ N ⊔ Q := by
        intro l hl
        have hmem : π ⟨l, hLX hl⟩ ∈ J := ⟨⟨l, hl⟩, rfl⟩
        obtain ⟨n, hn, hnl⟩ := hJN hmem
        have hqn : n⁻¹ * ⟨l, hLX hl⟩ ∈ Q' := QuotientGroup.eq.mp hnl
        have hl' : l = (n : G) * ((n⁻¹ * ⟨l, hLX hl⟩ : ↥X) : G) := by simp
        rw [hl']
        refine Subgroup.mul_mem_sup ⟨n.2, ?_⟩ ((hmemQ _).mp hqn)
        refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
        have hq' : ((⟨q, hQX hq⟩ : ↥X)) ∈ Q' := (hmemQ _).mpr hq
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hn _ hq')
      have hLN : L ≤ N := by
        calc L = twoResidual L := (S151S4.twoResidual_eq_self_of_perfect hperf).symm
          _ ≤ twoResidual (N ⊔ Q) := E1.twoResidual_mono hLNQ
          _ ≤ N := by
            refine twoResidual_le_of_isTwoQuotient le_sup_left ((sup_le hNX hQX).trans hXN) ?_
            intro y hy
            obtain ⟨n, hn, q, hq, rfl⟩ := mem_mul_of_le_normalizer (hQX.trans hXN) hy
            obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨q, hq⟩
            have hqk : q ^ 2 ^ k = 1 := by
              have := congrArg Subtype.val hk
              simpa using this
            obtain ⟨q', hq', hqe⟩ := mul_pow_mem_of_mem_normalizer (hXN (hQX hq)) hn (2 ^ k)
            exact ⟨k, by rw [hqe, hqk, mul_one]; exact hq'⟩
      have hLC : L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) := fun l hl =>
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (pCoreOf_le_of_isSubnormal' hsub))
          ((hLN hl).2)
      have hLO : L ≤ pCoreOf 2 L := fun l hl => hchar ⟨hl, hLC hl⟩
      have htriv : ∀ x : ↥L ⧸ CFSG.pCore 2 ↥L, x = 1 := by
        intro x
        induction x using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq_one_iff]
          obtain ⟨z, hz', hzy⟩ := hLO y.2
          have : z = y := Subtype.ext hzy
          rw [this] at hz'
          assumption
      have hnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := by
        have : Nontrivial ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
          hq.2.1.toNontrivial
        exact Function.Surjective.nontrivial
          (f := QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
          (QuotientGroup.mk'_surjective _)
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ CFSG.pCore 2 ↥L)
      exact hab (by rw [htriv a, htriv b])
    · intro n hn
      have h1 : π n ∈ Nc.map π := Subgroup.mem_map_of_mem π hn
      rw [hNb, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff n).mp h1
  unfold CharTwo
  intro x hx
  obtain ⟨hxX, hxC⟩ := hx
  have hxNc : (⟨x, hxX⟩ : ↥X) ∈ Nc := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : (q : G) ∈ pCoreOf 2 X := (hmemQ q).mp hq
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (q : G) hq')
  exact (hmemQ _).mp (hNcQ hxNc)

end CFSG.Quasithin.S151S5
