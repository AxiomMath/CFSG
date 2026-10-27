module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFactSpec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2ModelHom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2CentralizerModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2CentralizerShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2ThreeCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2CentralizerFpf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2InvolutionProduct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QCore
public import CFSG.Quasithin.H13.NQTermAmbientQuotient
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.RankThree.S4Free.StellmacherW
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3U3Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact in
theorem k_J2_centralizer_shape_holds :
    K_J2_centralizer_shape := by
  classical
  intro Y _ _ K hKn hK hidx S hS
  obtain ⟨ρ, -, hker2, -, hrange, hC⟩ := exists_j2Model_hom K hKn hK hidx S hS
  obtain ⟨e1⟩ := CFSG.Quasithin.N204.nonempty_oTwoQuot_equiv_of_surjective
    (ρ.subgroupMap (Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y)))
    (ρ.subgroupMap_surjective _)
    (CFSG.Quasithin.H13.NQTerm.isPGroup_ker_subgroupMap ρ _
      (hker2.to_le inf_le_right))
  rcases hrange with h | h
  · left
    obtain ⟨e2⟩ := oTwoQuot_centralizerIn_P
    rw [h] at hC
    exact ⟨e1.trans ((CFSG.Quasithin.F112R.oTwoQuotCongr (MulEquiv.subgroupCongr hC)).trans e2)⟩
  · right
    obtain ⟨e2⟩ := oTwoQuot_centralizerIn_R
    rw [h] at hC
    exact ⟨e1.trans ((CFSG.Quasithin.F112R.oTwoQuotCongr (MulEquiv.subgroupCongr hC)).trans e2)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact in
theorem k_J2_centralizer_fpf_holds :
    K_J2_centralizer_fpf := by
  classical
  intro Y _ _ K hKn hK hidx S hS P' x hP' hxC hodd hxN hfpf
  obtain ⟨ρ, hker, hker2, -, hrange, hC⟩ := exists_j2Model_hom K hKn hK hidx S hS
  have hxK : x ∈ K := by
    obtain ⟨n, hn⟩ := hidx
    have := hKn
    have h1 : orderOf (QuotientGroup.mk x : Y ⧸ K) ∣ orderOf x :=
      orderOf_map_dvd (QuotientGroup.mk' K) x
    have h2 : orderOf (QuotientGroup.mk x : Y ⧸ K) ∣ 2 ^ n := by
      rw [← hn, Subgroup.index]
      exact orderOf_dvd_natCard _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have h3 : orderOf (QuotientGroup.mk x : Y ⧸ K) = 1 := by
      rcases k with _ | k
      · simpa using hk
      · exfalso
        rw [hk] at h1
        exact (Nat.not_even_iff_odd.2 hodd)
          (even_iff_two_dvd.2 (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) h1))
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hPker : ∀ p ∈ P', ρ p = 1 → p = 1 := by
    intro p hp hρp
    have hpk : p ∈ ρ.ker := hρp
    rw [hker, Subgroup.mem_centralizer_iff] at hpk
    exact hfpf p hp (hpk x hxK)
  have hQ8 : CFSG.Quasithin.IsQ8D8 ↥(CFSG.Open.pCoreOf 2
      ((Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y)).map ρ)) := by
    obtain ⟨hPR, h8⟩ := pCoreOf_centralizerIn_permTwoA
    rcases hrange with h | h
    · rw [hC, h, hPR]; exact h8
    · rw [hC, h]; exact h8
  have hPQ : P'.map ρ ≤ CFSG.Open.pCoreOf 2
      ((Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y)).map ρ) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨c, hc, rfl⟩ := hP' hp
    rw [CFSG.Open.pCoreOf, ← CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker
      (ρ.subgroupMap _) (ρ.subgroupMap_surjective _)
      (CFSG.Quasithin.H13.NQTerm.isPGroup_ker_subgroupMap ρ _
        (hker2.to_le inf_le_right))]
    exact ⟨ρ.subgroupMap _ c, ⟨c, hc, rfl⟩, rfl⟩
  have hρP : P'.map ρ = ⊥ := by
    refine eq_bot_of_le_isQ8D8_of_fpf hQ8 hPQ (x := ρ x) ?_ ?_ ?_
    · intro q hq
      have hxmem : ρ x ∈ (Subgroup.centralizer
          (((Subgroup.center S).map S.subtype) : Set Y)).map ρ := ⟨x, hxC, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hxmem) q).1 hq
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨x * p * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN p).1 hp, by
        simp only [map_mul, map_inv]⟩
    · rintro _ ⟨p, hp, rfl⟩ hcomm
      have h1 : ρ (x * p * x⁻¹ * p⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
        group
      have h2 : x * p * x⁻¹ * p⁻¹ ∈ P' :=
        P'.mul_mem ((Subgroup.mem_normalizer_iff.1 hxN p).1 hp) (P'.inv_mem hp)
      have h3 := hPker _ h2 h1
      have h4 : x * p = p * x := by
        calc x * p = (x * p * x⁻¹ * p⁻¹) * p * x := by group
          _ = p * x := by rw [h3, one_mul]
      rw [hfpf p hp h4, map_one]
  rw [eq_bot_iff]
  intro p hp
  have hm : ρ p ∈ P'.map ρ := ⟨p, hp, rfl⟩
  rw [hρP, Subgroup.mem_bot] at hm
  exact (Subgroup.mem_bot).2 (hPker p hp hm)

open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact in
theorem k_J2_threeCentral_holds :
    K_J2_threeCentral := by
  classical
  intro X _ _ hX S hS z hzS hzc hz2 Y hYC hY3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e0⟩ := hX
  let θ : X ≃* ↥P := e0.trans nativeEquivP
  have hS2 : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := ⟨hS.1, hS.2.1, hS.2.2⟩
  have hT2 := CFSG.Quasithin.ModH.isSylowTwoOf_map_equiv θ hS2
  obtain ⟨hp, hidx⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.1 hT2
  let T : Sylow 2 ↥P := hp.toSylow hidx
  have hT : (T : Subgroup ↥P) = S.map θ.toMonoidHom := IsPGroup.toSylow_coe hp hidx
  have hz1 : θ z ≠ 1 := by
    intro h
    have h1 : z = 1 := θ.injective (h.trans (map_one θ).symm)
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_permTwoA T (θ z) (by rw [hT]; exact ⟨z, hzS, rfl⟩)
    (by
      rw [hT]
      rintro _ ⟨w, hw, rfl⟩
      change θ z * θ w = θ w * θ z
      rw [← map_mul, ← map_mul, hzc w hw]) hz1
  let φ : X →* Equiv.Perm (Fin 315) :=
    (MulAut.conj g).toMonoidHom.comp (P.subtype.comp θ.toMonoidHom)
  have hφ : ∀ x, φ x = g * (θ x : Equiv.Perm (Fin 315)) * g⁻¹ := fun x => rfl
  have hφP : ∀ x, φ x ∈ P := fun x => by
    rw [hφ]
    exact P.mul_mem (P.mul_mem hg (θ x).2) (P.inv_mem hg)
  have hφz : φ z = permTwoA := hgz
  have hYC' : Y.map φ ≤ CFSG.Sporadic.Schreier.centralizerIn P permTwoA := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hφP y, ?_⟩
    show φ y ∈ Subgroup.centralizer {permTwoA}
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [← hφz, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_iff.1 (hYC hy)) z (Set.mem_singleton z)]
  have hcardC : Nat.card (CFSG.Sporadic.Schreier.centralizerIn P permTwoA) = 1920 :=
    Kernel.centralizerIn_P_permTwoA.2.1
  obtain ⟨hy0P, hy0c, hy0o⟩ := permY0_facts
  have hy0C : Subgroup.zpowers permY0 ≤ CFSG.Sporadic.Schreier.centralizerIn P permTwoA := by
    rw [Subgroup.zpowers_le]
    refine ⟨hy0P, ?_⟩
    show permY0 ∈ Subgroup.centralizer {permTwoA}
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hy0c.symm
  set C := CFSG.Sporadic.Schreier.centralizerIn P permTwoA with hCdef
  have hφinj : Function.Injective φ :=
    (MulAut.conj g).injective.comp (P.subtype_injective.comp θ.injective)
  have hA3 : Nat.card ((Y.map φ).subgroupOf C) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC').toEquiv,
      Subgroup.card_map_of_injective hφinj, hY3]
  have hB3 : Nat.card ((Subgroup.zpowers permY0).subgroupOf C) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hy0C).toEquiv, Nat.card_zpowers, hy0o]
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartTwo.Sec20.F3U3.exists_map_conj_eq_of_card_eq
    (p := 3) (by rw [hcardC]; norm_num) hA3 hB3
  let ψ : X →* Equiv.Perm (Fin 315) := (MulAut.conj (c : Equiv.Perm (Fin 315))).toMonoidHom.comp φ
  have hψinj : Function.Injective ψ := (MulAut.conj _).injective.comp hφinj
  have hcP : (c : Equiv.Perm (Fin 315)) ∈ P := c.2.1
  have hψY : Y.map ψ = Subgroup.zpowers permY0 := by
    have h1 := congrArg (Subgroup.map C.subtype) hc
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hy0C, Subgroup.map_map] at h1
    have h2 : C.subtype.comp (MulAut.conj c).toMonoidHom =
        ((MulAut.conj (c : Equiv.Perm (Fin 315))).toMonoidHom.comp C.subtype) := by
      ext x
      simp
    have h3 : ((Y.map φ).subgroupOf C).map C.subtype = Y.map φ := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYC']
    rw [h1, h2]
    calc Y.map ψ = (Y.map φ).map (MulAut.conj (c : Equiv.Perm (Fin 315))).toMonoidHom :=
          (Subgroup.map_map _ _ _).symm
      _ = (((Y.map φ).subgroupOf C).map C.subtype).map
            (MulAut.conj (c : Equiv.Perm (Fin 315))).toMonoidHom := by rw [h3]
      _ = _ := Subgroup.map_map _ _ _
  have hψrange : ∀ q ∈ P, ∃ x, ψ x = q := by
    intro q hq
    refine ⟨θ.symm ⟨g⁻¹ * ((c : Equiv.Perm (Fin 315))⁻¹ * q * c) * g, ?_⟩, ?_⟩
    · exact P.mul_mem (P.mul_mem (P.inv_mem hg)
        (P.mul_mem (P.mul_mem (P.inv_mem hcP) hq) hcP)) hg
    · show (c : Equiv.Perm (Fin 315)) * (g * ((θ (θ.symm _) : ↥P) : Equiv.Perm (Fin 315)) * g⁻¹) *
        (c : Equiv.Perm (Fin 315))⁻¹ = q
      rw [MulEquiv.apply_symm_apply]
      group
  obtain ⟨hP3P, hP3c, hP3z⟩ := P3j_facts
  refine ⟨P3j.comap ψ, ?_, ?_⟩
  · have hmap : (P3j.comap ψ).map ψ = P3j := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun q hq => ?_
      obtain ⟨x, hx⟩ := hψrange q (hP3P hq)
      exact ⟨x, by show ψ x ∈ P3j; rw [hx]; exact hq, hx⟩
    have hcard : Nat.card (P3j.comap ψ) = 27 := by
      rw [← Subgroup.card_map_of_injective hψinj, hmap, hP3c]
    have hcardX : Nat.card X = 604800 := (Nat.card_congr θ.toEquiv).trans card_P
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num), ?_⟩
    rw [Subgroup.relIndex_top_right]
    have h := (P3j.comap ψ).card_mul_index
    rw [hcard, hcardX] at h
    have h2 : (P3j.comap ψ).index = 22400 := by omega
    rw [h2]
    norm_num
  · apply Subgroup.map_injective hψinj
    have hmap : (P3j.comap ψ).map ψ = P3j := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun q hq => ?_
      obtain ⟨x, hx⟩ := hψrange q (hP3P hq)
      exact ⟨x, by show ψ x ∈ P3j; rw [hx]; exact hq, hx⟩
    rw [hψY, ← CFSG.RankThree.S4Free.centerOf_map_of_injective hψinj, hmap, hP3z]

open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact in
theorem k_J2_involution_product_holds :
    K_J2_involution_product := by
  classical
  intro Y _ _ K hKn hK a ha2 ⟨k, hk, hak⟩
  have := hKn
  obtain ⟨e0⟩ := hK
  let θ : ↥K ≃* ↥P := e0.trans nativeEquivP
  let ρ : Y →* Equiv.Perm (Fin 315) := j2Cover_autModel.embed K θ
  have hρK : ∀ s : ↥K, ρ s = θ s := fun s => j2Cover_autModel.embed_coe K θ s
  have hρa2 : ρ a * ρ a = 1 := by rw [← map_mul, ha2, map_one]
  have hρa1 : ρ a ≠ 1 := by
    intro h
    have hmem : a ∈ ρ.ker := h
    rw [embed_ker_eq_centralizer] at hmem
    exact hak ((Subgroup.mem_centralizer_iff.1 hmem k hk).symm)
  have hρord : orderOf (ρ a) = 2 := orderOf_eq_prime (by rw [pow_two, hρa2]) hρa1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcls, -⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, c, hc, e⟩ := hcls (ρ a) (j2Cover_autModel.embed_mem K θ a) hρord
  obtain ⟨y₀, hy₀, hord⟩ := exists_conj_orderOf_four r hr
  let w : ↥P := ⟨c * y₀ * c⁻¹, P.mul_mem (P.mul_mem hc hy₀) (P.inv_mem hc)⟩
  let y : Y := (θ.symm w : ↥K)
  have hyK : y ∈ K := (θ.symm w).2
  have hρy : ρ y = c * y₀ * c⁻¹ := by
    show ρ ((θ.symm w : ↥K) : Y) = _
    rw [hρK, MulEquiv.apply_symm_apply]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hgK : a * (y⁻¹ * a * y) ∈ K := by
    have h1 : a * y⁻¹ * a⁻¹ ∈ K := hKn.conj_mem _ (K.inv_mem hyK) a
    rw [hainv] at h1
    have h2 := K.mul_mem h1 hyK
    rwa [show a * y⁻¹ * a * y = a * (y⁻¹ * a * y) by group] at h2
  refine ⟨y, hyK, ?_⟩
  have hρg : ρ (a * (y⁻¹ * a * y)) = c * (r * (y₀⁻¹ * r * y₀)) * c⁻¹ := by
    simp only [map_mul, map_inv, e, hρy]
    group
  have h1 : orderOf (a * (y⁻¹ * a * y)) = orderOf (ρ (a * (y⁻¹ * a * y))) := by
    have h2 : ρ (a * (y⁻¹ * a * y)) = ((θ ⟨_, hgK⟩ : ↥P) : Equiv.Perm (Fin 315)) :=
      hρK ⟨_, hgK⟩
    rw [h2, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  rw [h1, hρg]
  have h3 := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    (r * (y₀⁻¹ * r * y₀))
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h3
  rw [h3, hord]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
