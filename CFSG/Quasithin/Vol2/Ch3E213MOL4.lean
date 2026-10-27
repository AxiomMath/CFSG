module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Vol2.Ch3E213MDefs

public section

namespace CFSG.Quasithin.Ch3E213M.OL

open CFSG.Open CFSG.QuasithinUnique B6 E2P
open scoped commutatorElement

theorem ker_eq_bot_of_section {E Q : Type*} [Group E] [Group Q] (hperf : commutator E = ⊤)
    {π : E →* Q} (hcen : π.ker ≤ Subgroup.center E) {σ : Q →* E} (hσ : ∀ g, π (σ g) = g) :
    π.ker = ⊥ := by
  have hfc : ∀ e : E, e * (σ (π e))⁻¹ ∈ Subgroup.center E := fun e =>
    hcen (by rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel])
  let f : E →* E :=
    { toFun := fun e => e * (σ (π e))⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have h := Subgroup.mem_center_iff.mp (hfc b) (σ (π a))⁻¹
        show a * b * (σ (π (a * b)))⁻¹ = a * (σ (π a))⁻¹ * (b * (σ (π b))⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc a * b * ((σ (π b))⁻¹ * (σ (π a))⁻¹)
            = a * ((b * (σ (π b))⁻¹) * (σ (π a))⁻¹) := by group
          _ = a * ((σ (π a))⁻¹ * (b * (σ (π b))⁻¹)) := by rw [h]
          _ = a * (σ (π a))⁻¹ * (b * (σ (π b))⁻¹) := by group }
  have hker : commutator E ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hfc y) (f x)
  rw [hperf] at hker
  rw [eq_bot_iff]
  intro e he
  have h1 : f e = 1 := hker (Subgroup.mem_top e)
  have h2 : f e = e := by
    show e * (σ (π e))⁻¹ = e
    rw [MonoidHom.mem_ker.mp he, map_one, inv_one, mul_one]
  rw [Subgroup.mem_bot, ← h2, h1]

theorem commutator_eq_top_of_perfect {G : Type*} [Group G] {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    commutator ↥K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, hK]

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem kerIn_le_pCoreOf (hS : Setting H T M V K) (hC2 : Case2 H T M K)
    (hL : IsPSL 3 3 1 ↥(E2.star M H K)) : kerIn M H ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hUJ : pCoreOf 2 H ≤ kerIn M H := hS.hyp.minParabolic.pCoreOf_le_kerIn
  have hUn : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hKJ : ∀ x ∈ K, x ∈ kerIn M H → x ∈ pCoreOf 2 H := by
    intro x hxK hxJ
    set N : Subgroup ↥K := (pCoreOf 2 H).subgroupOf K with hN
    have hNn : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hUn g.2) n).mp hn⟩
    let ψ : ↥K →* ↥(E2.star M H K) :=
      ((starMap M H).comp (Subgroup.inclusion hKH)).codRestrict (E2.star M H K)
        (fun k => by rw [star_def]; exact ⟨_, (Subgroup.mem_subgroupOf).mpr k.2, rfl⟩)
    have hψsurj : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      rw [star_def] at hy
      obtain ⟨h, hh, rfl⟩ := hy
      exact ⟨⟨h, hh⟩, rfl⟩
    have hψ1 : ∀ k : ↥K, ψ k = 1 ↔ (k : G) ∈ kerIn M H := by
      intro k
      constructor
      · intro h
        have h1 : starMap M H (Subgroup.inclusion hKH k) = 1 := congrArg Subtype.val h
        have h2 : Subgroup.inclusion hKH k ∈ (kerIn M H).subgroupOf H := by
          rw [← ker_starMap]
          exact h1
        exact Subgroup.mem_subgroupOf.mp h2
      · intro h
        apply Subtype.ext
        show starMap M H (Subgroup.inclusion hKH k) = 1
        rw [← MonoidHom.mem_ker, ker_starMap]
        exact Subgroup.mem_subgroupOf.mpr h
    have hNker : N ≤ ψ.ker := fun k hk => (hψ1 k).mpr (hUJ (Subgroup.mem_subgroupOf.mp hk))
    let ψ' : ↥K ⧸ N →* ↥(E2.star M H K) := QuotientGroup.lift N ψ hNker
    have hψ'surj : Function.Surjective ψ' := by
      intro y
      obtain ⟨k, rfl⟩ := hψsurj y
      exact ⟨QuotientGroup.mk k, rfl⟩
    have hψ'cen : ψ'.ker ≤ Subgroup.center (↥K ⧸ N) := by
      intro e he
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective e
      have hkJ : (k : G) ∈ kerIn M H := (hψ1 k).mp he
      rw [Subgroup.mem_center_iff]
      intro e'
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective e'
      have hc := ((hC2.2 (k : G)).mp hkJ).2 (y : G) (Subgroup.mem_sup_left y.2)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hg : (((y : G) * k)⁻¹) ∈ K := K.inv_mem (K.mul_mem y.2 k.2)
      have h1 := (Subgroup.mem_normalizer_iff.mp (hUn hg) _).mp hc
      have h2 : (((y * k)⁻¹ * (k * y) : ↥K) : G) =
          ((y : G) * k)⁻¹ * ((k : G) * y * (k : G)⁻¹ * (y : G)⁻¹) * ((y : G) * k)⁻¹⁻¹ := by
        push_cast
        group
      rw [h2]
      exact h1
    have hperfK : commutator ↥K = ⊤ := commutator_eq_top_of_perfect hS.mem_cComp.2.1
    have hperfE : commutator (↥K ⧸ N) = ⊤ := by
      have h := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ (QuotientGroup.mk' N)
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
      rw [_root_.commutator_def, ← h, ← _root_.commutator_def, hperfK,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hL
    have hF3 : Nat.card F = 3 := by rw [hcard, pow_one]
    have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      have h := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3) (by norm_num) F
      have h3 : Nat.gcd 3 (Nat.card F - 1) = 1 := by rw [hF3]; norm_num
      rw [h3] at h
      exact Nat.dvd_one.mp h
    let θ : ↥(E2.star M H K) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
    let π : ↥K ⧸ N →* Matrix.SpecialLinearGroup (Fin 3) F := θ.toMonoidHom.comp ψ'
    have hπsurj : Function.Surjective π := θ.surjective.comp hψ'surj
    have hπker : π.ker = ψ'.ker := by
      ext a
      simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    have hπcen : π.ker ≤ Subgroup.center (↥K ⧸ N) := hπker ▸ hψ'cen
    have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating 2 F :=
      CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card le_rfl (by omega) (by omega)
        (by omega)
    obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
      (m := 2) le_rfl hsep hπsurj hπcen
    have hbot := ker_eq_bot_of_section hperfE hπcen hσ
    have hmem : (QuotientGroup.mk ⟨x, hxK⟩ : ↥K ⧸ N) ∈ π.ker := by
      rw [hπker, MonoidHom.mem_ker]
      exact (hψ1 ⟨x, hxK⟩).mpr hxJ
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  intro x hx
  have hxKU : x ∈ pCoreOf 2 H ⊔ K := by
    rw [sup_comm]
    exact ((hC2.2 x).mp hx).1
  obtain ⟨u, hu, k, hk, rfl⟩ := E2P.exists_mul_of_mem_sup_of_le_normalizer' hUn hxKU
  have hkJ : k ∈ kerIn M H := by
    have := (kerIn M H).mul_mem ((kerIn M H).inv_mem (hUJ hu)) hx
    simpa using this
  exact (pCoreOf 2 H).mul_mem hu (hKJ k hk hkJ)

end CFSG.Quasithin.Ch3E213M.OL
