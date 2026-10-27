module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u v

section Generic

variable {G : Type v} [Group G]

theorem centralizer_singleton_map_equiv (e : G ≃* G) (x : G) :
    Subgroup.centralizer ({e x} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  · intro h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h

theorem conjugate_reflection_torus_normalizer (T : Subgroup G) [IsCyclic T] (w : G)
    (hw : w ∈ Subgroup.normalizer (T : Set G)) (hwsq : w * w = 1)
    (hinv : ∀ y : G, y ∈ T → w * y * w⁻¹ = y⁻¹)
    (hnormalizer : ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w)
    (e : G ≃* G) (x : G) (hxT : x ∈ T.map e.toMonoidHom) (hx : x ≠ 1)
    (hxodd : Odd (orderOf x)) :
    Subgroup.centralizer ({x} : Set G) = T.map e.toMonoidHom ∧ e w * e w = 1 ∧
      (∀ y ∈ T.map e.toMonoidHom, e w * y * (e w)⁻¹ = y⁻¹) ∧
      ∀ R : Subgroup G, R ≤ T.map e.toMonoidHom → R ≠ ⊥ →
        Subgroup.normalizer (R : Set G) = T.map e.toMonoidHom ⊔ Subgroup.zpowers (e w) := by
  have hx0T : e.symm x ∈ T := Subgroup.mem_map_equiv.mp hxT
  have hx0ne : e.symm x ≠ 1 := fun h => hx (by
    simpa only [e.apply_symm_apply, e.map_one] using congrArg e h)
  have hx0odd : Odd (orderOf (e.symm x)) :=
    (orderOf_injective e.symm.toMonoidHom e.symm.injective x).symm ▸ hxodd
  have hRne : Subgroup.zpowers (e.symm x) ≠ ⊥ := by
    intro h
    exact hx0ne (Subgroup.zpowers_eq_bot.mp h)
  obtain ⟨hC0, -⟩ := odd_element_centralizer_eq_reflection_torus T w (e.symm x) hw hwsq hinv
    hx0T hx0ne hx0odd (hnormalizer _ (Subgroup.zpowers_le_of_mem hx0T) hRne)
  refine ⟨?_, by rw [← map_mul, hwsq, map_one], ?_, ?_⟩
  · have h := centralizer_singleton_map_equiv e (e.symm x)
    rwa [e.apply_symm_apply, hC0] at h
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    change e w * e t * (e w)⁻¹ = (e t)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hinv t ht, map_inv]
  · intro R hR hR1
    have hR0 : R.map e.symm.toMonoidHom ≤ T := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      have h := hR hz
      rw [Subgroup.mem_map_equiv] at h
      exact h
    have hR01 : R.map e.symm.toMonoidHom ≠ ⊥ := by
      intro h
      exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R e.symm.injective).mp h)
    have hRmap : (R.map e.symm.toMonoidHom).map e.toMonoidHom = R := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id R
      ext y
      simp
    rw [← hRmap, ← Subgroup.map_normalizer_eq_of_bijective _ e.bijective,
      hnormalizer _ hR0 hR01, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl

end Generic

variable {K : Type u} [Field K] [Finite K]

theorem psl2_even_odd_element_torus_normalizer (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (x : PSL2MatrixGroup K) (hx : x ≠ 1) (hxodd : Odd (orderOf x)) :
    ∃ w : PSL2MatrixGroup K, w * w = 1 ∧
      (∀ y ∈ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)), w * y * w⁻¹ = y⁻¹) ∧
      ∀ R : Subgroup (PSL2MatrixGroup K),
        R ≤ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)) → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup K)) =
            Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)) ⊔ Subgroup.zpowers w := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (PSL2MatrixGroup K) := default
  obtain ⟨U, S, _, hUcard, _, hScard, hpart⟩ :=
    huppert_II_8_5_a_psl2_cover (p := 2) (f := f) hcard P
  have hKge : 4 ≤ Nat.card K := by
    rw [hcard]
    exact (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  have hKeven : Even (Nat.card K) := by
    rw [hcard]
    exact even_two.pow_of_ne_zero (by omega)
  have hminusodd : Odd (Nat.card K - 1) := Nat.Even.sub_odd (by omega) hKeven odd_one
  have hplusodd : Odd (Nat.card K + 1) := hKeven.add_odd odd_one
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 1 := hminusodd.coprime_two_right.gcd_eq_one
  rw [hgcd, Nat.div_one] at hUcard hScard
  have hUS : Nat.Coprime (Nat.card U) (Nat.card S) := by
    have h := hsplit_nonsplit_order_coprime (Nat.card K) (by omega)
    simpa only [hgcd, Nat.div_one, hUcard, hScard] using h
  have hcover : ∀ y : PSL2MatrixGroup K, y ≠ 1 →
      ∃ V : Subgroup (PSL2MatrixGroup K), y ∈ V ∧
        ((∃ g, V = (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = S.map (MulAut.conj g).toMonoidHom)) := fun y hy => (hpart y hy).exists
  obtain ⟨U0, wU, hU0cyclic, hU0card, hwUN, -, hwUsq, hwUinv, -, hU0N⟩ :=
    huppert_II_8_3_split_torus_reflection_data (p := 2) (f := f) hcard
  obtain ⟨S0, wS, hS0cyclic, hS0card, hwSN, -, hwSsq, hwSinv, -, hS0N⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data (p := 2) (f := f) hcard
  rw [hgcd, Nat.div_one] at hU0card hS0card
  let : IsCyclic U0 := hU0cyclic
  let : IsCyclic S0 := hS0cyclic
  obtain ⟨gU, hgU⟩ := reference_torus_matches_partition
    (P : Subgroup (PSL2MatrixGroup K)) U S U0 P.isPGroup'
    (hU0card.trans hUcard.symm) (hUcard.symm ▸ hminusodd)
    (by rw [hUcard]; omega) hUS hcover
  have hreverse : ∀ y : PSL2MatrixGroup K, y ≠ 1 →
      ∃ V : Subgroup (PSL2MatrixGroup K), y ∈ V ∧
        ((∃ g, V = (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = S.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = U.map (MulAut.conj g).toMonoidHom)) := by
    intro y hy
    obtain ⟨V, hyV, hVP | hVU | hVS⟩ := hcover y hy
    · exact ⟨V, hyV, Or.inl hVP⟩
    · exact ⟨V, hyV, Or.inr (Or.inr hVU)⟩
    · exact ⟨V, hyV, Or.inr (Or.inl hVS)⟩
  obtain ⟨gS, hgS⟩ := reference_torus_matches_partition
    (P : Subgroup (PSL2MatrixGroup K)) S U S0 P.isPGroup'
    (hS0card.trans hScard.symm) (hScard.symm ▸ hplusodd)
    (by rw [hScard]; omega) hUS.symm hreverse
  obtain ⟨V, hxV, hVP | hVU | hVS⟩ := hcover x hx
  · obtain ⟨g, rfl⟩ := hVP
    have htwo := P.isPGroup'.map (MulAut.conj g).toMonoidHom
    let y : (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom := ⟨x, hxV⟩
    have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hxodd
    have hcop := htwo.orderOf_coprime hyodd.coprime_two_left y
    have hyone : y = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl)
    exact False.elim (hx (congrArg Subtype.val hyone))
  · obtain ⟨g, rfl⟩ := hVU
    let eU : PSL2MatrixGroup K ≃* PSL2MatrixGroup K :=
      (MulAut.conj gU).symm.trans (MulAut.conj g)
    have hUmap : U0.map eU.toMonoidHom = U.map (MulAut.conj g).toMonoidHom := by
      have hU0back : U0.map (MulAut.conj gU).symm.toMonoidHom = U :=
        (Subgroup.map_symm_eq_iff_map_eq (K := U) (e := MulAut.conj gU)).mpr hgU.symm
      change U0.map ((MulAut.conj g).toMonoidHom.comp
        (MulAut.conj gU).symm.toMonoidHom) = _
      rw [← Subgroup.map_map, hU0back]
    have hxU0 : x ∈ U0.map eU.toMonoidHom := hUmap.symm ▸ hxV
    obtain ⟨hC, hsq, hinv, hN⟩ := conjugate_reflection_torus_normalizer U0 wU hwUN hwUsq
      hwUinv hU0N eU x hxU0 hx hxodd
    refine ⟨eU wU, hsq, fun y hy => hinv y (hC ▸ hy), fun R hR hR1 => ?_⟩
    rw [hC] at hR ⊢
    exact hN R hR hR1
  · obtain ⟨g, rfl⟩ := hVS
    let eS : PSL2MatrixGroup K ≃* PSL2MatrixGroup K :=
      (MulAut.conj gS).symm.trans (MulAut.conj g)
    have hSmap : S0.map eS.toMonoidHom = S.map (MulAut.conj g).toMonoidHom := by
      have hS0back : S0.map (MulAut.conj gS).symm.toMonoidHom = S :=
        (Subgroup.map_symm_eq_iff_map_eq (K := S) (e := MulAut.conj gS)).mpr hgS.symm
      change S0.map ((MulAut.conj g).toMonoidHom.comp
        (MulAut.conj gS).symm.toMonoidHom) = _
      rw [← Subgroup.map_map, hS0back]
    have hxS0 : x ∈ S0.map eS.toMonoidHom := hSmap.symm ▸ hxV
    obtain ⟨hC, hsq, hinv, hN⟩ := conjugate_reflection_torus_normalizer S0 wS hwSN hwSsq
      hwSinv hS0N eS x hxS0 hx hxodd
    refine ⟨eS wS, hsq, fun y hy => hinv y (hC ▸ hy), fun R hR hR1 => ?_⟩
    rw [hC] at hR ⊢
    exact hN R hR hR1

theorem psl2_even_odd_torus_normalizer_dichotomy (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f) (x : PSL2MatrixGroup K) (hx : x ≠ 1) (hxodd : Odd (orderOf x))
    (R : Subgroup (PSL2MatrixGroup K))
    (hR : R ≤ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K))) (hR1 : R ≠ ⊥)
    {g : PSL2MatrixGroup K} (hg : g ∈ Subgroup.normalizer (R : Set (PSL2MatrixGroup K))) :
    g ∈ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)) ∨
      ∀ y ∈ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)), g * y * g⁻¹ = y⁻¹ := by
  set D := Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K))
  obtain ⟨hDcyc, -, -⟩ := psl2_even_odd_element_full_centralizer f hf hcard x hx hxodd
  let : IsCyclic D := hDcyc
  obtain ⟨w, hwsq, hwinv, hN⟩ := psl2_even_odd_element_torus_normalizer f hf hcard x hx hxodd
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
  have hwD : w ∈ Subgroup.normalizer (D : Set (PSL2MatrixGroup K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => (hwinv y hy).symm ▸ D.inv_mem hy, fun hy => ?_⟩
    have h := hwinv _ hy
    have hy' : y = (w * y * w⁻¹)⁻¹ := by
      rw [← h, hwi]
      simp only [← mul_assoc]
      rw [hwsq, one_mul, mul_assoc, hwsq, mul_one]
    rw [hy']
    exact D.inv_mem hy
  rw [hN R hR hR1] at hg
  rcases reflection_join_action D w hwD hwsq hwinv g hg with hid | hinv
  · left
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxD : x ∈ D := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have h := hid x hxD
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  · exact Or.inr hinv

omit [Finite K] in
theorem exists_sylow_mem_of_orderOf_eq_two {t : PSL2MatrixGroup K} (ht : orderOf t = 2) :
    ∃ P : Sylow 2 (PSL2MatrixGroup K), t ∈ P := by
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers t)⟩

theorem eq_one_of_odd_of_commute_involution {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    {t x : PSL2MatrixGroup K} (ht : orderOf t = 2) (hxodd : Odd (orderOf x))
    (hxt : x * t = t * x) : x = 1 := by
  obtain ⟨P, htP⟩ := exists_sylow_mem_of_orderOf_eq_two ht
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hxP : x ∈ (P : Subgroup (PSL2MatrixGroup K)) := by
    rw [← sylow_centralizer_eq hcard P htP ht1]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxt
  let y : (P : Subgroup (PSL2MatrixGroup K)) := ⟨x, hxP⟩
  have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hxodd
  have hcop := P.isPGroup'.orderOf_coprime hyodd.coprime_two_left y
  have hy1 : y = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl)
  exact congrArg Subtype.val hy1

theorem orderOf_eq_two_of_even {f : ℕ} (hcard : Nat.card K = 2 ^ f) {x : PSL2MatrixGroup K}
    (hx : Even (orderOf x)) : orderOf x = 2 := by
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have h2 : 2 ∣ orderOf x := even_iff_two_dvd.mp hx
  set t := x ^ (orderOf x / 2)
  have ht : orderOf t = 2 := orderOf_pow_orderOf_div hx0 h2
  obtain ⟨P, htP⟩ := exists_sylow_mem_of_orderOf_eq_two ht
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hxP : x ∈ (P : Subgroup (PSL2MatrixGroup K)) := by
    rw [← sylow_centralizer_eq hcard P htP ht1]
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((Commute.self_pow x _).eq)
  let : IsElementaryAbelian 2 P := (psl2_even_sylow_elementary_card f hcard P).1
  have hsq : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxP
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · rw [h] at hx
    exact absurd hx (by decide)
  · exact h

end CFSG.ShultStronglyClosedTI.LinearModel
