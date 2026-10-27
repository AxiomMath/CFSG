module

public import CFSG.LieType.Ree.SuzukiBorelStructure
public import CFSG.LieType.Ree.SuzukiOvoidWeyl
import CFSG.RankThree.S4Free.SuzukiEight
import CFSG.RankThree.S4Free.StellmacherL24
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiModule

public section

open CFSG.Blueprint CFSG.LieType.Ree Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.S4Free

namespace Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

private theorem eq_zero_or_eq_one_of_pow_theta (hK : Nat.card K = 2 ^ (2 * a + 1)) {t : K}
    (ht : t ^ 2 ^ (a + 1) = t) : t = 0 ∨ t = 1 := by
  obtain ⟨-, -, hθθ, -⟩ := suzuki_frobenius_exponents a K hK
  have h2 : t ^ 2 = t := by rw [← hθθ t, ht, ht]
  have : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h2, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private theorem exists_ne_zero_ne_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun t _ => by
    by_cases h0 : t = 0
    · exact Or.inl h0
    · exact Or.inr (h t h0)
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, hK, Set.ncard_pair zero_ne_one] at hcard
  have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega


theorem eq_bot_or_eq_suzukiZ0_or_eq_suzukiU (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {W : Subgroup (suzukiGroup a K)} (hWU : W ≤ suzukiU a K)
    (hWB : suzukiB a K ≤ normalizer (W : Set (suzukiGroup a K))) :
    W = ⊥ ∨ W = suzukiZ0 a K ∨ W = suzukiU a K := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hD : ∀ (l : Kˣ) (u v : K), suzukiSElt a K u v ∈ W →
      suzukiSElt a K ((l : K) * u) ((l : K) ^ (2 ^ (a + 1) + 1) * v) ∈ W := by
    intro l u v huv
    rw [← suzukiDElt_conj hK]
    have hl : (suzukiDElt a K l)⁻¹ ∈ normalizer (W : Set (suzukiGroup a K)) :=
      hWB (mem_sup_right (inv_mem (subset_closure ⟨l, rfl⟩)))
    have := (mem_normalizer_iff.mp hl _).mp huv
    rwa [inv_inv] at this
  have hZ : ∀ v₀ : K, v₀ ≠ 0 → suzukiSElt a K 0 v₀ ∈ W → suzukiZ0 a K ≤ W := by
    intro v₀ hv₀ hW0
    rw [suzukiZ0, closure_le]
    rintro _ ⟨v, rfl⟩
    show suzukiSElt a K 0 v ∈ W
    by_cases hv : v = 0
    · rw [hv, suzukiSElt_zero_zero hK]
      exact one_mem W
    · obtain ⟨l, hl⟩ := hbij.2 (Units.mk0 (v / v₀) (div_ne_zero hv hv₀))
      have := hD l 0 v₀ hW0
      have hl' : (l : K) ^ (2 ^ (a + 1) + 1) = v / v₀ := by
        have h1 := congrArg Units.val hl
        simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h1
        rwa [show ((2 : ℤ) ^ (a + 1) + 1) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast] at h1
      rwa [mul_zero, hl', div_mul_cancel₀ v hv₀] at this
  by_cases hWZ : W ≤ suzukiZ0 a K
  ·
    by_cases hW1 : W = ⊥
    · exact Or.inl hW1
    · right; left
      obtain ⟨⟨x, hxW⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
      have hx1 : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      obtain ⟨v₀, rfl⟩ := (mem_suzukiZ0_iff hK).mp (hWZ hxW)
      have hv₀ : v₀ ≠ 0 := fun h => hx1 (by rw [h, suzukiSElt_zero_zero hK])
      exact le_antisymm hWZ (hZ v₀ hv₀ hxW)
  ·
    right; right
    obtain ⟨x, hxW, hxZ⟩ := Set.not_subset.mp hWZ
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).mp (hWU hxW)
    have hu : u ≠ 0 := fun h => hxZ ((mem_suzukiZ0_iff hK).mpr ⟨v, by rw [h]⟩)
    obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one ha hK
    set c := t * u with hc
    have hy : suzukiSElt a K c 0 ∈ normalizer (W : Set (suzukiGroup a K)) :=
      hWB (mem_sup_left ((mem_suzukiU_iff hK).mpr ⟨c, 0, rfl⟩))
    have hconj := (mem_normalizer_iff.mp hy _).mp hxW
    have hcomm := W.mul_mem (W.inv_mem hxW) hconj
    obtain ⟨-, hadd, -⟩ := suzuki_frob_data a hK
    have key : (suzukiSElt a K u v)⁻¹ * (suzukiSElt a K c 0 * suzukiSElt a K u v *
        (suzukiSElt a K c 0)⁻¹) =
        suzukiSElt a K 0 (c ^ 2 ^ (a + 1) * u + u ^ 2 ^ (a + 1) * c) := by
      rw [suzukiSElt_inv hK, suzukiSElt_inv hK, suzukiSElt_mul hK, suzukiSElt_mul hK,
        suzukiSElt_mul hK, suzukiSElt_inj, hadd c u]
      constructor
      · linear_combination (u + c) * h2
      · rw [pow_succ u, pow_succ c]
        linear_combination (v + u ^ 2 ^ (a + 1) * u + c ^ 2 ^ (a + 1) * c +
          u ^ 2 ^ (a + 1) * c) * h2
    rw [key] at hcomm
    have hne : c ^ 2 ^ (a + 1) * u + u ^ 2 ^ (a + 1) * c ≠ 0 := by
      intro h0
      have h1 : (t ^ 2 ^ (a + 1) + t) * (u ^ 2 ^ (a + 1) * u) = 0 := by
        rw [← h0, hc, mul_pow]
        ring
      rcases mul_eq_zero.mp h1 with h3 | h3
      · have h4 : t ^ 2 ^ (a + 1) = t := by
          linear_combination h3 - t * h2
        rcases eq_zero_or_eq_one_of_pow_theta hK h4 with h5 | h5
        · exact ht0 h5
        · exact ht1 h5
      · exact hu (by
          rcases mul_eq_zero.mp h3 with h5 | h5
          · exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h5
          · exact h5)
    have hZW := hZ _ hne hcomm
    refine le_antisymm hWU fun y hy => ?_
    obtain ⟨u', w, rfl⟩ := (mem_suzukiU_iff hK).mp hy
    by_cases hu' : u' = 0
    · rw [hu']
      exact hZW ((mem_suzukiZ0_iff hK).mpr ⟨w, rfl⟩)
    · have h1 := hD (Units.mk0 (u' / u) (div_ne_zero hu' hu)) u v hxW
      rw [Units.val_mk0, div_mul_cancel₀ u' hu] at h1
      set v₁ := (u' / u) ^ (2 ^ (a + 1) + 1) * v
      have h2' := W.mul_mem h1 (hZW ((mem_suzukiZ0_iff hK).mpr ⟨w - v₁, rfl⟩))
      rwa [suzukiSElt_mul hK, mul_zero, add_zero, add_sub_cancel, add_zero] at h2'

variable {X : Type*} [Group X]

theorem exists_mulEquiv_sylow_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    (S : Sylow 2 X) :
    ∃ φ : X ≃* suzukiGroup a K, (S : Subgroup X) = (suzukiU a K).comap φ.toMonoidHom ∧
      normalizer ((S : Subgroup X) : Set X) = (suzukiB a K).comap φ.toMonoidHom := by
  obtain ⟨g, hS⟩ := CFSG.RankThree.S4Free.Suzuki.exists_mem_sylow_iff hK e S
  refine ⟨e.trans (MulAut.conj g⁻¹), ?_, ?_⟩
  · ext x
    rw [hS, mem_comap]
    simp [MulAut.conj_apply]
  · rw [CFSG.RankThree.S4Free.Suzuki.normalizer_eq_map_suzukiB hK e hS]
    ext x
    rw [mem_map_equiv, mem_comap]
    simp [MulAut.conj_apply, MulAut.conj_symm_apply, mul_assoc]

theorem suzukiU_inf_centralizer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiU a K ⊓ centralizer (suzukiU a K : Set (suzukiGroup a K)) = suzukiZ0 a K := by
  have h := CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism.center_suzukiU hK ha
  ext x
  constructor
  · rintro ⟨hxU, hxC⟩
    have : (⟨x, hxU⟩ : suzukiU a K) ∈ center (suzukiU a K) := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext ((mem_centralizer_iff.mp hxC) y y.2)
    rw [h, mem_subgroupOf] at this
    exact this
  · intro hx
    have hxU : x ∈ suzukiU a K := suzukiZ0_le_suzukiU hx
    have : (⟨x, hxU⟩ : suzukiU a K) ∈ center (suzukiU a K) := by
      rw [h, mem_subgroupOf]
      exact hx
    refine ⟨hxU, mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact congrArg Subtype.val ((mem_center_iff.mp this) ⟨y, hy⟩)

theorem inf_centralizer_eq_comap (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : X ≃* suzukiGroup a K) {S : Subgroup X} (hSφ : S = (suzukiU a K).comap φ.toMonoidHom) :
    S ⊓ centralizer (S : Set X) = (suzukiZ0 a K).comap φ.toMonoidHom := by
  rw [← suzukiU_inf_centralizer ha hK, comap_inf, hSφ]
  congr 1
  ext x
  rw [mem_comap, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx u hu
    have h1 := hx (φ.symm u) (show φ (φ.symm u) ∈ suzukiU a K by
      rw [MulEquiv.apply_symm_apply]; exact hu)
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  · intro hx s hs
    have h1 := hx (φ s) hs
    apply φ.injective
    rw [map_mul, map_mul]
    exact h1

theorem sq_mem_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : suzukiGroup a K}
    (hx : x ∈ suzukiU a K) : x ^ 2 ∈ suzukiZ0 a K := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).mp hx
  rw [pow_two, suzukiSElt_mul hK, mem_suzukiZ0_iff hK]
  refine ⟨u ^ 2 ^ (a + 1) * u, ?_⟩
  rw [suzukiSElt_inj]
  constructor
  · linear_combination (-u) * h2
  · linear_combination (-v) * h2

theorem card_sylow_and_center (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) :
    Nat.card S = (2 ^ (2 * a + 1)) ^ 2 ∧
      Nat.card ((S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) : Subgroup X) =
        2 ^ (2 * a + 1) ∧
      (∀ s ∈ (S : Subgroup X), s ^ 2 ∈ (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X)) ∧
      ∀ s ∈ (S : Subgroup X), ∀ t ∈ (S : Subgroup X),
        ⁅s, t⁆ ∈ (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) := by
  obtain ⟨φ, hSφ, -⟩ := exists_mulEquiv_sylow_eq hK e S
  rw [inf_centralizer_eq_comap ha hK φ hSφ]
  refine ⟨?_, ?_, fun s hs => ?_, fun s hs t ht => ?_⟩
  · rw [hSφ, ← (suzuki_unipotent_structure hK).2.1, comap_equiv_eq_map_symm']
    exact Nat.card_congr (MulEquiv.subgroupMap φ.symm (suzukiU a K)).toEquiv.symm
  · rw [← CFSG.ShultStronglyClosedTI.SuzukiModel.card_suzukiZ0 hK, comap_equiv_eq_map_symm']
    exact Nat.card_congr (MulEquiv.subgroupMap φ.symm (suzukiZ0 a K)).toEquiv.symm
  · rw [hSφ] at hs
    rw [mem_comap, MulEquiv.coe_toMonoidHom, map_pow]
    exact sq_mem_suzukiZ0 hK hs
  · rw [hSφ] at hs ht
    rw [mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
    exact commutatorElement_mem_suzukiZ0 hK hs ht

theorem eq_bot_or_eq_center_or_eq_sylow (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) {W : Subgroup X} (hWS : W ≤ S)
    (hWN : normalizer ((S : Subgroup X) : Set X) ≤ normalizer (W : Set X)) :
    W = ⊥ ∨ W = (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) ∨ W = S := by
  obtain ⟨φ, hSφ, hNφ⟩ := exists_mulEquiv_sylow_eq hK e S
  have hWU : W.map φ.toMonoidHom ≤ suzukiU a K := by
    rw [map_le_iff_le_comap, ← hSφ]
    exact hWS
  have hWB : suzukiB a K ≤ normalizer ((W.map φ.toMonoidHom : Subgroup _) : Set _) := by
    intro b hb
    have hn : φ.symm b ∈ normalizer (W : Set X) := hWN (by
      rw [hNφ, mem_comap]
      simpa using hb)
    rw [mem_normalizer_iff] at hn ⊢
    intro y
    rw [mem_map_equiv, mem_map_equiv, map_mul, map_mul, map_inv]
    exact hn (φ.symm y)
  have hW : W = (W.map φ.toMonoidHom).comap φ.toMonoidHom :=
    (comap_map_eq_self_of_injective φ.injective W).symm
  rcases eq_bot_or_eq_suzukiZ0_or_eq_suzukiU ha hK hWU hWB with h | h | h
  · left
    rw [hW, h]
    ext x
    rw [mem_comap, mem_bot, mem_bot, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · right; left
    rw [hW, h, inf_centralizer_eq_comap ha hK φ hSφ]
  · right; right
    rw [hW, h, hSφ]

theorem centralizer_eq_sylow_of_mulEquiv (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) {z : X} (hz : orderOf z = 2)
    (hzS : z ∈ (S : Subgroup X)) : centralizer ({z} : Set X) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  set Q : Sylow 2 (suzukiGroup a K) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup (suzukiGroup a K)) = (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hzQ : e z ∈ (Q : Subgroup (suzukiGroup a K)) := by
    rw [hQ]
    exact mem_map_of_mem e.toMonoidHom hzS
  have hez : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  have h := CFSG.RankThree.centralizer_eq_sylow hK hez Q hzQ
  ext x
  have hx := congrArg (fun T : Subgroup (suzukiGroup a K) => e x ∈ T) h
  simp only [eq_iff_iff, mem_centralizer_singleton_iff, hQ, mem_map_equiv,
    MulEquiv.symm_apply_apply] at hx
  rw [mem_centralizer_singleton_iff, ← hx, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem inf_eq_bot_of_sylow_ne (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    {S S' : Sylow 2 X} (hne : S ≠ S') : (S : Subgroup X) ⊓ S' = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  by_contra hbot
  have h2 : IsPGroup 2 ((S : Subgroup X) ⊓ S' : Subgroup X) := S.isPGroup'.to_inf_left
  have : Nontrivial ((S : Subgroup X) ⊓ S' : Subgroup X) := (nontrivial_iff_ne_bot _).mpr hbot
  obtain ⟨n, hn, hcard⟩ := h2.nontrivial_iff_card.mp inferInstance
  obtain ⟨⟨z, hzSS⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := ((S : Subgroup X) ⊓ S' :
    Subgroup X)) 2 (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  rw [Subgroup.orderOf_mk] at hz
  apply hne
  ext x
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← centralizer_eq_sylow_of_mulEquiv hK e S hz hzSS.1,
    ← centralizer_eq_sylow_of_mulEquiv hK e S' hz hzSS.2]

theorem exists_cyclic_complement (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) :
    ∃ T : Subgroup X, IsCyclic T ∧ Nat.card T = 2 ^ (2 * a + 1) - 1 ∧
      (S : Subgroup X) ⊓ T = ⊥ ∧ (S : Subgroup X) ⊔ T = normalizer ((S : Subgroup X) : Set X) ∧
      ∀ z ∈ (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X),
        ∀ z' ∈ (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X),
          z ≠ 1 → z' ≠ 1 → ∃ t ∈ T, t * z * t⁻¹ = z' := by
  obtain ⟨φ, hSφ, hNφ⟩ := exists_mulEquiv_sylow_eq hK e S
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hB := suzuki_borel_structure hK
  let D : Kˣ →* suzukiGroup a K :=
    { toFun := suzukiDElt a K
      map_one' := suzukiDElt_one
      map_mul' := fun l m => (suzukiDElt_mul l m).symm }
  have hDrange : D.range = suzukiT a K := by
    apply SetLike.coe_injective
    rw [MonoidHom.coe_range, hB.1]
    rfl
  have hTcyc : IsCyclic (suzukiT a K) := by
    rw [← hDrange]
    exact isCyclic_of_surjective D.rangeRestrict D.rangeRestrict_surjective
  refine ⟨(suzukiT a K).comap φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [comap_equiv_eq_map_symm']
    exact isCyclic_of_surjective (MulEquiv.subgroupMap φ.symm (suzukiT a K)).toMonoidHom
      (MulEquiv.surjective _)
  · rw [comap_equiv_eq_map_symm', ← hB.2.2.1]
    exact Nat.card_congr (MulEquiv.subgroupMap φ.symm (suzukiT a K)).toEquiv.symm
  · rw [hSφ, ← comap_inf, hB.2.2.2.2.1]
    ext x
    rw [mem_comap, mem_bot, mem_bot, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · rw [hNφ, hSφ, comap_equiv_eq_map_symm', comap_equiv_eq_map_symm',
      comap_equiv_eq_map_symm', ← Subgroup.map_sup]
    rfl
  · intro z hz z' hz' hz1 hz1'
    rw [inf_centralizer_eq_comap ha hK φ hSφ, mem_comap] at hz hz'
    obtain ⟨v, hv⟩ := (mem_suzukiZ0_iff hK).mp hz
    obtain ⟨v', hv'⟩ := (mem_suzukiZ0_iff hK).mp hz'
    have hv0 : v ≠ 0 := fun h0 => hz1 (by
      apply φ.injective
      rw [map_one, MulEquiv.coe_toMonoidHom] at *
      rw [← hv, h0, suzukiSElt_zero_zero hK])
    have hv0' : v' ≠ 0 := fun h0 => hz1' (by
      apply φ.injective
      rw [map_one, MulEquiv.coe_toMonoidHom] at *
      rw [← hv', h0, suzukiSElt_zero_zero hK])
    obtain ⟨l, hl⟩ := hbij.2 (Units.mk0 (v' / v) (div_ne_zero hv0' hv0))
    have hl' : (l : K) ^ (2 ^ (a + 1) + 1) = v' / v := by
      have h1 := congrArg Units.val hl
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h1
      rwa [show ((2 : ℤ) ^ (a + 1) + 1) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast] at h1
    refine ⟨φ.symm ((suzukiDElt a K l)⁻¹), ?_, ?_⟩
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact inv_mem (subset_closure ⟨l, rfl⟩)
    · apply φ.injective
      simp only [MulEquiv.coe_toMonoidHom] at hv hv'
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
      rw [← hv, ← hv', suzukiDElt_conj hK, mul_zero, hl', div_mul_cancel₀ v' hv0]

private theorem suzukiW_mul_suzukiS (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiW K * suzukiS a (0 : K) 1 = !![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiW, suzukiS, suzukiN, Matrix.mul_apply, Fin.sum_univ_four]

private theorem suzukiW_mul_suzukiS_pow_five (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiW K * suzukiS a (0 : K) 1) ^ 5 = 1 := by
  obtain ⟨hchar, -⟩ := suzuki_frobenius_exponents a K hK
  have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  rw [suzukiW_mul_suzukiS hK]
  set P : Matrix (Fin 4) (Fin 4) K := !![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] with hP
  have hP2 : P ^ 2 = !![1, 1, 1, 1; 1, 0, 0, 1; 1, 0, 1, 0; 1, 1, 0, 1] := by
    rw [sq, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, h2]
  have hP4 : P ^ 4 = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1] := by
    rw [show P ^ 4 = (P ^ 2) ^ 2 by rw [← pow_mul], hP2, sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, h2]
  rw [pow_succ, hP4, hP]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, h2]

theorem orderOf_suzukiWElt_mul_suzukiSElt (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    orderOf (suzukiWElt a K * suzukiSElt a K 0 1) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (suzukiSElt_ext ?_) fun h => ?_
  · rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul,
      coe_suzukiWElt, coe_suzukiSElt, Subgroup.coe_one, Units.val_one]
    exact suzukiW_mul_suzukiS_pow_five hK
  · have h1 := congrArg (fun g : suzukiGroup a K =>
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 1) h
    simp only [Subgroup.coe_mul, Units.val_mul, coe_suzukiWElt, coe_suzukiSElt,
      suzukiW_mul_suzukiS hK, Subgroup.coe_one, Units.val_one] at h1
    simp at h1

theorem exists_orderOf_eq_five_inv (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    {t : X} (ht : orderOf t = 2) : ∃ f : X, orderOf f = 5 ∧ t * f * t⁻¹ = f⁻¹ := by
  set w := suzukiWElt a K
  set u := suzukiSElt a K 0 1
  have hw : w * w = 1 := suzukiWElt_mul_self
  have hu : u * u = 1 := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiSElt_zero_mul_self hK 1
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hw2 : orderOf w = 2 := by
    refine orderOf_eq_prime (by rw [sq, hw]) fun h1 => ?_
    have h2 := congrArg (fun g : suzukiGroup a K =>
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 3) h1
    simp [w, coe_suzukiWElt, suzukiW] at h2
  have hinv : w * (w * u) * w⁻¹ = (w * u)⁻¹ := by
    rw [hwi, mul_inv_rev, hwi, hui, ← mul_assoc, hw, one_mul]
  have het : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (CFSG.QuasithinUnique.Setup.Family.suzuki_involutions_conjugate hK w (e t) hw2 het)
  refine ⟨e.symm (c * (w * u) * c⁻¹), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, show c * (w * u) * c⁻¹ = MulAut.conj c (w * u) from rfl,
      MulEquiv.orderOf_eq, orderOf_suzukiWElt_mul_suzukiSElt hK]
  · apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← hc]
    calc c * w * c⁻¹ * (c * (w * u) * c⁻¹) * (c * w * c⁻¹)⁻¹ =
        c * (w * (w * u) * w⁻¹) * c⁻¹ := by group
      _ = (c * (w * u) * c⁻¹)⁻¹ := by rw [hinv]; group

private theorem two_pow_mod_five (a : ℕ) : 2 ^ (2 * a + 1) % 5 = 2 ∨ 2 ^ (2 * a + 1) % 5 = 3 := by
  induction a with
  | zero => left; norm_num
  | succ a ih =>
    rw [show 2 * (a + 1) + 1 = 2 * a + 1 + 2 by ring, pow_add]
    omega

theorem not_five_dvd_card_normalizer (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) :
    ¬ 5 ∣ Nat.card (normalizer ((S : Subgroup X) : Set X)) := by
  rw [card_normalizer_sylow hK e S]
  intro h5
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h))
    omega
  · have h1 := two_pow_mod_five a
    have h2 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    omega

end Suzuki

namespace Stell

section Helpers

variable {G G' : Type*} [Group G] [Group G']

theorem card_map_eq_relIndex (f : G →* G') (K : Subgroup G) :
    Nat.card (K.map f) = f.ker.relIndex K := by
  rw [← MonoidHom.domRestrict_range]
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.domRestrict K)).toEquiv,
    MonoidHom.ker_domRestrict]
  rfl

theorem card_eq_card_map_mul {N : Subgroup G} [N.Normal] {K : Subgroup G} (hNK : N ≤ K) :
    Nat.card K = Nat.card (K.map (QuotientGroup.mk' N)) * Nat.card N := by
  rw [card_map_eq_relIndex, QuotientGroup.ker_mk', ← relIndex_mul_card N K, inf_of_le_left hNK]

theorem mem_normalizer_sup {A B : Subgroup G} {n : G} (hA : n ∈ normalizer (A : Set G))
    (hB : n ∈ normalizer (B : Set G)) : n ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ m : G, m ∈ normalizer (A : Set G) → m ∈ normalizer (B : Set G) →
      (A ⊔ B).map (MulAut.conj m).toMonoidHom ≤ A ⊔ B := by
    intro m hmA hmB
    rw [Subgroup.map_sup]
    refine sup_le_sup (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, rfl⟩ := hx
      exact (mem_normalizer_iff.mp hmA y).mp hy
    · obtain ⟨y, hy, rfl⟩ := hx
      exact (mem_normalizer_iff.mp hmB y).mp hy
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key n hA hB ⟨x, hx, rfl⟩
  · intro hx
    have := key n⁻¹ (inv_mem hA) (inv_mem hB) ⟨_, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem card_abelianization_eq_pow_of_pow_mem [Finite G] {r : ℕ} [Fact r.Prime]
    (hD : ∀ x : G, x ^ r ∈ commutator G) (hZ : center G = commutator G)
    (hc : Nat.card (center G) = r) : ∃ b : ℕ, Nat.card (Abelianization G) = r ^ (2 * b) := by
  obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hc
  have hkill : ∀ v : Additive (Abelianization G), r • v = 0 := by
    intro v
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
    induction u using QuotientGroup.induction_on with
    | H x =>
      change r • Additive.ofMul (Abelianization.of x) = 0
      rw [← ofMul_pow, ← map_pow]
      have : Abelianization.of (x ^ r) = 1 := by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
        exact hD x
      rw [this]
      rfl
  have := AddCommGroup.zmodModule hkill
  obtain ⟨B, hBa, hBn, -⟩ := CFSG.OddSolvableUnitary.exists_commForm hZ ε
  have : Finite (Additive (Abelianization G)) :=
    Finite.of_surjective (fun x : G => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod r) (Additive (Abelianization G)) := Module.Finite.of_finite
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod r) hBa hBn
  refine ⟨b, ?_⟩
  change Nat.card (Additive (Abelianization G)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod, hb, two_mul]

theorem commutatorElement_mul_central {x y z z' : G} (hz : ∀ g : G, z * g = g * z)
    (hz' : ∀ g : G, z' * g = g * z') : ⁅x * z, y * z'⁆ = ⁅x, y⁆ := by
  have h1 : z * (y * z') * z⁻¹ = y * z' := by rw [hz (y * z'), mul_inv_cancel_right]
  have h2 : z' * x⁻¹ * z'⁻¹ = x⁻¹ := by rw [hz' x⁻¹, mul_inv_cancel_right]
  calc ⁅x * z, y * z'⁆ = x * (z * (y * z') * z⁻¹) * x⁻¹ * (y * z')⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * (z' * x⁻¹ * z'⁻¹) * y⁻¹ := by rw [h1]; group
    _ = ⁅x, y⁆ := by rw [h2, commutatorElement_def]

end Helpers

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem le_or_le_of_mulEquiv_suzukiGroup {H : Type*} [Group H] [Finite H] {Z : Subgroup H}
    [Z.Normal] (hZc : Z ≤ center H) (hZd : Z ≤ commutator H) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : H ⧸ Z ≃* suzukiGroup a K) (S : Sylow 2 H)
    {W : Subgroup H} (hWS : W ≤ S)
    (hWN : normalizer ((S : Subgroup H) : Set H) ≤ normalizer (W : Set H)) : Z ≤ W ∨ W ≤ Z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hZcomm : ∀ z ∈ Z, ∀ g : H, z * g = g * z := fun z hz g =>
    (mem_center_iff.mp (hZc hz) g).symm
  have hcentral : ∀ T : Subgroup H, T ≤ Z → T.Normal := fun T hT =>
    ⟨fun n hn g => by rw [← hZcomm n (hT hn) g, mul_inv_cancel_right]; exact hn⟩
  have hperfQ : commutator (H ⧸ Z) = ⊤ := by
    have h1 := (suzuki_perfect ha hK).1
    have h2 : (commutator (suzukiGroup a K)).map e.symm.toMonoidHom = commutator (H ⧸ Z) := by
      rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
        map_top_of_surjective _ e.symm.surjective]
    rw [← h2, h1, map_top_of_surjective _ e.symm.surjective]
  have hperf : commutator H = ⊤ := by
    have h1 : (commutator H).map π = ⊤ := by
      rw [_root_.commutator_def, map_commutator, map_top_of_surjective _ hπs,
        ← _root_.commutator_def, hperfQ]
    rw [eq_top_iff, ← comap_top π, ← h1, comap_map_eq, hker, sup_of_le_left hZd]
  haveI : Group.IsPerfect H := ⟨hperf⟩
  have hZ2 : IsPGroup 2 Z := by
    obtain ⟨Q⟩ : Nonempty (Sylow 2 Z) := inferInstance
    set P : Subgroup H := (Q : Subgroup Z).map Z.subtype with hPdef
    have hPZ : P ≤ Z := map_subtype_le _
    haveI hPn : P.Normal := hcentral P hPZ
    have hQ2 : IsPGroup 2 P := Q.isPGroup'.map Z.subtype
    set N : Subgroup (H ⧸ P) := Z.map (QuotientGroup.mk' P) with hNdef
    have hNodd : Odd (Nat.card N) := by
      rw [hNdef, card_map_eq_relIndex, QuotientGroup.ker_mk']
      have hPQ : P.subgroupOf Z = Q := comap_map_eq_self_of_injective Z.subtype_injective _
      rw [relIndex, hPQ]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp Q.not_dvd_index)
    have hNc : N ≤ center (H ⧸ P) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P g
      rw [← map_mul, ← map_mul, hZcomm z hz g]
    let ψ : H ⧸ P →* H ⧸ Z := QuotientGroup.map P Z (MonoidHom.id H) (fun x hx => hPZ hx)
    have hψ : ∀ x : H, ψ (x : H ⧸ P) = (x : H ⧸ Z) := fun x => rfl
    obtain ⟨m, hm, ⟨f⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel
        (G := suzukiGroup a K) (p := 2) (f := 2 * a + 1)
        ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
    let χ := (f.toMonoidHom.comp e.toMonoidHom).comp ψ
    have hχs : Function.Surjective χ := by
      intro y
      obtain ⟨x, hx⟩ := hπs (e.symm (f.symm y))
      refine ⟨(x : H ⧸ P), ?_⟩
      change f (e (ψ (x : H ⧸ P))) = y
      rw [hψ]
      change f (e (π x)) = y
      rw [hx, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have hχk : χ.ker = N := by
      ext x
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P x
      rw [MonoidHom.mem_ker]
      change f (e (ψ (x : H ⧸ P))) = 1 ↔ _
      rw [hψ, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have : z⁻¹ * x ∈ P := by
          rw [← QuotientGroup.eq_one_iff (N := P), QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          rw [show ((z : H) : H ⧸ P) = QuotientGroup.mk' P x from hzx]
          exact inv_mul_cancel _
        have := Z.mul_mem hz (hPZ this)
        rwa [mul_inv_cancel_left] at this
    have hbot := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial m (by omega) χ hχs
      (hχk ▸ hNc) (hχk ▸ hNodd)
    have hZP : Z ≤ P := by
      intro z hz
      have : QuotientGroup.mk' P z ∈ χ.ker := by rw [hχk]; exact ⟨z, hz, rfl⟩
      rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    exact hQ2.to_le hZP
  have hZS : Z ≤ S := hZ2.le_sylow_of_normal S
  have hZS' : Z ≤ ⁅(S : Subgroup H), (S : Subgroup H)⁆ := by
    have := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived S Z hZc hZ2
    rwa [map_subtype_commutator] at this
  set Sb : Sylow 2 (H ⧸ Z) := S.mapSurjective hπs with hSbdef
  have hSb : (Sb : Subgroup (H ⧸ Z)) = (S : Subgroup H).map π := Sylow.coe_mapSurjective _ _
  have hcSb : (Sb : Subgroup (H ⧸ Z)).comap π = S := by
    rw [hSb, comap_map_eq, hker, sup_of_le_left hZS]
  have hnorm : ∀ n : H, π n ∈ normalizer ((Sb : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) →
      n ∈ normalizer ((S : Subgroup H) : Set H) := by
    intro n hn
    rw [mem_normalizer_iff] at hn ⊢
    intro h
    rw [← hcSb, mem_comap, mem_comap, map_mul, map_mul, map_inv]
    exact hn (π h)
  have hmapN : ∀ V : Subgroup H, normalizer ((S : Subgroup H) : Set H) ≤ normalizer (V : Set H) →
      normalizer ((Sb : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) ≤
        normalizer ((V.map π : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) := by
    intro V hV nb hnb
    obtain ⟨n, rfl⟩ := hπs nb
    have hn := hV (hnorm n hnb)
    rw [mem_normalizer_iff]
    intro yb
    obtain ⟨y, rfl⟩ := hπs yb
    constructor
    · rintro ⟨v, hv, hvy⟩
      refine ⟨n * v * n⁻¹, (mem_normalizer_iff.mp hn v).mp hv, ?_⟩
      rw [map_mul, map_mul, map_inv, hvy]
    · rintro ⟨v, hv, hvy⟩
      refine ⟨n⁻¹ * v * n, ?_, ?_⟩
      · have := (mem_normalizer_iff.mp (inv_mem hn) v).mp hv
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hvy]
        group
  have hWb : W.map π ≤ Sb := by rw [hSb]; exact map_mono hWS
  obtain ⟨hcardSb, hcardZb, hsqb, hcommb⟩ := Suzuki.card_sylow_and_center ha hK e Sb
  set Zb := (Sb : Subgroup (H ⧸ Z)) ⊓ centralizer ((Sb : Subgroup (H ⧸ Z)) : Set (H ⧸ Z))
    with hZbdef
  have hcommS : ∀ V X : Subgroup H, (S : Subgroup H) ≤ V ⊔ Z →
      (∀ v ∈ V, ∀ v' ∈ V, ⁅v, v'⁆ ∈ X) → ⁅(S : Subgroup H), (S : Subgroup H)⁆ ≤ X := by
    intro V X hSV hVX
    rw [commutator_le]
    intro s hs t ht
    have hs' : s ∈ ((V ⊔ Z : Subgroup H) : Set H) := hSV hs
    have ht' : t ∈ ((V ⊔ Z : Subgroup H) : Set H) := hSV ht
    rw [mul_normal] at hs' ht'
    obtain ⟨v, hv, z, hz, rfl⟩ := hs'
    obtain ⟨v', hv', z', hz', rfl⟩ := ht'
    rw [commutatorElement_mul_central (hZcomm z hz) (hZcomm z' hz')]
    exact hVX v hv v' hv'
  rcases Suzuki.eq_bot_or_eq_center_or_eq_sylow ha hK e Sb hWb (hmapN W hWN) with h | h | h
  ·
    right
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff _).mp h
  ·
    replace h : W.map π = Zb := h
    by_cases hZW : Z ≤ W
    · exact Or.inl hZW
    exfalso
    have hP : W ⊔ Z = Zb.comap π := by rw [← h, comap_map_eq, hker]
    have hne : W.subgroupOf Z ≠ ⊤ := by
      intro htop
      apply hZW
      intro z hz
      have : (⟨z, hz⟩ : Z) ∈ W.subgroupOf Z := by rw [htop]; exact mem_top _
      exact this
    obtain ⟨M₀, hM₀le, hM₀max⟩ :=
      exists_maximal_ge_of_wellFoundedGT (fun T : Subgroup Z => T ≠ ⊤) _ hne
    have hM₀co : IsCoatom M₀ := ⟨hM₀max.1, fun T hT => by
      by_contra hTt
      exact hT.ne (le_antisymm hT.le (hM₀max.2 hTt hT.le))⟩
    haveI : Group.IsNilpotent Z := hZ2.isNilpotent
    have hidx : M₀.index = 2 := hZ2.isCoatom_iff_index_eq_prime.mp hM₀co
    set Z₀ : Subgroup H := M₀.map Z.subtype with hZ₀def
    have hZ₀Z : Z₀ ≤ Z := map_subtype_le M₀
    have hZWZ₀ : Z ⊓ W ≤ Z₀ := fun x hx =>
      ⟨⟨x, hx.1⟩, hM₀le (by rw [mem_subgroupOf]; exact hx.2), rfl⟩
    have hZ₀rel : Z₀.relIndex Z = 2 := by
      have : Z₀.subgroupOf Z = M₀ := comap_map_eq_self_of_injective Z.subtype_injective M₀
      rw [relIndex, this, hidx]
    haveI hZ₀n : Z₀.Normal := hcentral Z₀ hZ₀Z
    set W₁ := W ⊔ Z₀ with hW₁def
    have hW₁S : W₁ ≤ S := sup_le hWS (hZ₀Z.trans hZS)
    have hW₁N : normalizer ((S : Subgroup H) : Set H) ≤ normalizer (W₁ : Set H) := fun n hn =>
      mem_normalizer_sup (hWN hn) (by rw [normalizer_eq_top_iff.mpr hZ₀n]; exact mem_top n)
    have hZW₁ : Z ⊓ W₁ = Z₀ := by
      rw [hW₁def, ← Subgroup.inf_sup_assoc_of_le
        (by rw [normalizer_eq_top_iff.mpr hZ₀n]; exact le_top) hZ₀Z]
      exact sup_of_le_right hZWZ₀
    have hW₁Z : W₁ ⊔ Z = W ⊔ Z := by rw [hW₁def, sup_assoc, sup_of_le_right hZ₀Z]
    have hnot : ¬ ⁅(S : Subgroup H), (S : Subgroup H)⁆ ≤ W₁ := by
      intro hle
      have h1 : Z ≤ Z₀ := hZW₁ ▸ le_inf le_rfl (hZS'.trans hle)
      have h2 : Z₀.relIndex Z = 1 := relIndex_eq_one.mpr h1
      omega
    have hSW₁ : (S : Subgroup H) ≤ normalizer (W₁ : Set H) := le_normalizer.trans hW₁N
    have hSW : (S : Subgroup H) ≤ normalizer (W : Set H) := le_normalizer.trans hWN
    let C : Subgroup H :=
      { carrier := {s | s ∈ (S : Subgroup H) ∧ ∀ t ∈ (S : Subgroup H), ⁅s, t⁆ ∈ W₁}
        mul_mem' := by
          rintro x y ⟨hx, hxt⟩ ⟨hy, hyt⟩
          refine ⟨mul_mem hx hy, fun t ht => ?_⟩
          have e1 : ⁅x * y, t⁆ = x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆ := by
            simp only [commutatorElement_def]; group
          rw [e1]
          exact W₁.mul_mem ((mem_normalizer_iff.mp (hSW₁ hx) _).mp (hyt t ht)) (hxt t ht)
        one_mem' := ⟨one_mem _, fun t _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
        inv_mem' := by
          rintro x ⟨hx, hxt⟩
          refine ⟨inv_mem hx, fun t ht => ?_⟩
          have e1 : ⁅x⁻¹, t⁆ = x⁻¹ * ⁅x, t⁆⁻¹ * x⁻¹⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e1]
          exact (mem_normalizer_iff.mp (hSW₁ (inv_mem hx)) _).mp (W₁.inv_mem (hxt t ht)) }
    have hCS : C ≤ S := fun s hs => hs.1
    have hWC : W ≤ C := fun w hw => ⟨hWS hw, fun t ht => by
      have h1 : t * w⁻¹ * t⁻¹ ∈ W := (mem_normalizer_iff.mp (hSW ht) _).mp (W.inv_mem hw)
      rw [commutatorElement_def, show w * t * w⁻¹ * t⁻¹ = w * (t * w⁻¹ * t⁻¹) by group]
      exact mem_sup_left (W.mul_mem hw h1)⟩
    have hCN : normalizer ((S : Subgroup H) : Set H) ≤ normalizer (C : Set H) := by
      intro n hn
      have key : ∀ m ∈ normalizer ((S : Subgroup H) : Set H), ∀ c ∈ C, m * c * m⁻¹ ∈ C := by
        intro m hm c hc
        refine ⟨(mem_normalizer_iff.mp hm c).mp hc.1, fun t ht => ?_⟩
        have ht' : m⁻¹ * t * m ∈ (S : Subgroup H) := by
          have := (mem_normalizer_iff.mp (inv_mem hm) t).mp ht
          rwa [inv_inv] at this
        have e1 : ⁅m * c * m⁻¹, t⁆ = m * ⁅c, m⁻¹ * t * m⁆ * m⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact (mem_normalizer_iff.mp (hW₁N hm) _).mp (hc.2 _ ht')
      rw [mem_normalizer_iff]
      intro c
      refine ⟨key n hn c, fun hc => ?_⟩
      have := key n⁻¹ (inv_mem hn) _ hc
      rwa [show n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c by group] at this
    have hCb : C.map π ≤ Sb := by rw [hSb]; exact map_mono hCS
    have hZbne : Zb ≠ ⊥ := by
      intro hb
      have h1 := hcardZb
      rw [hb, card_bot] at h1
      have : 2 ^ 1 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases Suzuki.eq_bot_or_eq_center_or_eq_sylow ha hK e Sb hCb (hmapN C hCN) with hC | hC | hC
    · apply hZbne
      rw [← h, eq_bot_iff, ← hC]
      exact map_mono hWC
    · replace hC : C.map π = Zb := hC
      have hCle : C ≤ W₁ ⊔ Z := by
        rw [hW₁Z, hP, ← hC]
        exact le_comap_map π C
      haveI hN₁ : (W₁.subgroupOf S).Normal :=
        (normal_subgroupOf_iff_le_normalizer hW₁S).mpr hSW₁
      set N₁ := W₁.subgroupOf (S : Subgroup H) with hN₁def
      set ρ := QuotientGroup.mk' N₁ with hρdef
      have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective N₁
      have hρker : ρ.ker = N₁ := QuotientGroup.ker_mk' N₁
      set Zh : Subgroup (↥(S : Subgroup H) ⧸ N₁) := (Z.subgroupOf S).map ρ with hZhdef
      have hρmem : ∀ s : (S : Subgroup H), (s : H) ∈ W₁ ⊔ Z → ρ s ∈ Zh := by
        intro s hs
        have hs' : (s : H) ∈ ((W₁ ⊔ Z : Subgroup H) : Set H) := hs
        rw [mul_normal] at hs'
        obtain ⟨w, hw, z, hz, hwz⟩ := hs'
        have hwS : w ∈ (S : Subgroup H) := hW₁S hw
        have hzS : z ∈ (S : Subgroup H) := hZS hz
        have hs1 : s = ⟨w, hwS⟩ * ⟨z, hzS⟩ := Subtype.ext hwz.symm
        have hw1 : ρ ⟨w, hwS⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hρker, mem_subgroupOf]
          exact hw
        rw [hs1, map_mul, hw1, one_mul]
        exact ⟨⟨z, hzS⟩, hz, rfl⟩
      have hmapS : ∀ s : (S : Subgroup H), π s ∈ (Sb : Subgroup (H ⧸ Z)) := fun s => by
        rw [hSb]
        exact mem_map_of_mem π s.2
      have hcenter : center (↥(S : Subgroup H) ⧸ N₁) = Zh := by
        apply le_antisymm
        · intro x hx
          obtain ⟨s, rfl⟩ := hρs x
          refine hρmem s (hCle ⟨s.2, fun t ht => ?_⟩)
          have h1 := mem_center_iff.mp hx (ρ ⟨t, ht⟩)
          have h2 : ρ ⁅s, ⟨t, ht⟩⁆ = 1 := by
            rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
            exact h1.symm
          rw [← MonoidHom.mem_ker, hρker, mem_subgroupOf] at h2
          exact h2
        · rintro _ ⟨z, hz, rfl⟩
          rw [mem_center_iff]
          intro y
          obtain ⟨y, rfl⟩ := hρs y
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hZcomm z (mem_subgroupOf.mp hz) y).symm
      have hcardZh : Nat.card Zh = 2 := by
        rw [hZhdef, card_map_eq_relIndex, hρker, hN₁def, relIndex_subgroupOf hZS,
          ← inf_relIndex_right, inf_comm, hZW₁, hZ₀rel]
      have hcommE : commutator (↥(S : Subgroup H) ⧸ N₁) = Zh := by
        have hle : commutator (↥(S : Subgroup H) ⧸ N₁) ≤ Zh := by
          rw [_root_.commutator_def, commutator_le]
          intro x _ y _
          obtain ⟨s, rfl⟩ := hρs x
          obtain ⟨t, rfl⟩ := hρs y
          rw [← map_commutatorElement]
          refine hρmem _ ?_
          rw [hW₁Z, hP, mem_comap]
          have := hcommb (π s) (hmapS s) (π t) (hmapS t)
          rwa [← map_commutatorElement] at this
        have hne : commutator (↥(S : Subgroup H) ⧸ N₁) ≠ ⊥ := by
          intro hbot
          apply hnot
          rw [commutator_le]
          intro s hs t ht
          have h1 : ⁅ρ ⟨s, hs⟩, ρ ⟨t, ht⟩⁆ ∈ commutator (↥(S : Subgroup H) ⧸ N₁) := by
            rw [_root_.commutator_def]
            exact commutator_mem_commutator (mem_top _) (mem_top _)
          rw [hbot, mem_bot, ← map_commutatorElement, ← MonoidHom.mem_ker, hρker,
            mem_subgroupOf] at h1
          exact h1
        refine eq_of_le_of_card_ge hle ?_
        rw [hcardZh]
        have := (one_lt_card_iff_ne_bot _).mpr hne
        omega
      have hsq : ∀ x : ↥(S : Subgroup H) ⧸ N₁, x ^ 2 ∈ commutator (↥(S : Subgroup H) ⧸ N₁) := by
        intro x
        obtain ⟨s, rfl⟩ := hρs x
        rw [hcommE, ← map_pow]
        refine hρmem _ ?_
        rw [hW₁Z, hP, mem_comap]
        have := hsqb (π s) (hmapS s)
        rwa [← map_pow] at this
      have hZE : center (↥(S : Subgroup H) ⧸ N₁) = commutator (↥(S : Subgroup H) ⧸ N₁) :=
        hcenter.trans hcommE.symm
      have hcE : Nat.card (center (↥(S : Subgroup H) ⧸ N₁)) = 2 := by
        rw [hcenter]
        exact hcardZh
      obtain ⟨b, hb⟩ := card_abelianization_eq_pow_of_pow_mem hsq hZE hcE
      have hcard1 : Nat.card (↥(S : Subgroup H) ⧸ N₁) = 2 ^ (2 * b) * 2 := by
        rw [CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hZE hcE, hb]
      have hcard2 : Nat.card (↥(S : Subgroup H) ⧸ N₁) = 2 * 2 ^ (2 * a + 1) := by
        have hE : Nat.card (↥(S : Subgroup H) ⧸ N₁) * Nat.card W₁ = Nat.card S := by
          have := relIndex_mul_card W₁ S
          rw [inf_of_le_left hW₁S] at this
          exact this
        have hS' : Nat.card S = (2 ^ (2 * a + 1)) ^ 2 * Nat.card Z := by
          rw [card_eq_card_map_mul hZS, ← hSb, hcardSb]
        have hW₁' : 2 * Nat.card W₁ = 2 ^ (2 * a + 1) * Nat.card Z := by
          have h1 : Nat.card (W₁ ⊔ Z : Subgroup H) = 2 ^ (2 * a + 1) * Nat.card Z := by
            rw [card_eq_card_map_mul (le_sup_right : Z ≤ W₁ ⊔ Z), hW₁Z, Subgroup.map_sup, h,
              QuotientGroup.map_mk'_self, sup_bot_eq, hcardZb]
          have h2 := relIndex_mul_card W₁ (W₁ ⊔ Z)
          rw [inf_of_le_left le_sup_left, relIndex_sup_of_normal, ← inf_relIndex_right,
            inf_comm, hZW₁, hZ₀rel] at h2
          rw [← h1, ← h2]
        have hq : 0 < 2 ^ (2 * a + 1) * Nat.card Z := Nat.mul_pos (by positivity) Nat.card_pos
        apply Nat.eq_of_mul_eq_mul_right hq
        calc Nat.card (↥(S : Subgroup H) ⧸ N₁) * (2 ^ (2 * a + 1) * Nat.card Z) =
            Nat.card (↥(S : Subgroup H) ⧸ N₁) * (2 * Nat.card W₁) := by rw [hW₁']
          _ = 2 * (Nat.card (↥(S : Subgroup H) ⧸ N₁) * Nat.card W₁) := by ring
          _ = 2 * ((2 ^ (2 * a + 1)) ^ 2 * Nat.card Z) := by rw [hE, hS']
          _ = 2 * 2 ^ (2 * a + 1) * (2 ^ (2 * a + 1) * Nat.card Z) := by ring
      have h3 : 2 ^ (2 * b + 1) = 2 ^ (2 * a + 2) := by
        rw [pow_succ, ← hcard1, hcard2, pow_succ]
        ring
      have := Nat.pow_right_injective (le_refl 2) h3
      omega
    · apply hnot
      have hSCZ : (S : Subgroup H) ≤ C ⊔ Z := by rw [← hcSb, ← hC, comap_map_eq, hker]
      exact hcommS C W₁ hSCZ fun c hc c' hc' => hc.2 c' hc'.1
  ·
    left
    have hSWZ : (S : Subgroup H) ≤ W ⊔ Z := by
      rw [← hcSb, ← h, comap_map_eq, hker]
    exact hZS'.trans (hcommS W W hSWZ fun v hv v' hv' => by
      rw [commutatorElement_def]
      exact W.mul_mem (W.mul_mem (W.mul_mem hv hv') (W.inv_mem hv)) (W.inv_mem hv'))

end Stell

end CFSG.RankThree.S4Free
