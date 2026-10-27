module

public import CFSG.Quasithin.EmptyFaithful.E22QLift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.Quasithin.EmptyFaithful.E22PTr
import CFSG.Quasithin.EmptyFaithful.E22PL2Psl
import CFSG.Quasithin.EmptyFaithful.E22PL2PglB
import CFSG.Quasithin.EmptyFaithful.E22PL2PglC
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.Quasithin.E22L2
  CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_normal
  pslRange_index_eq_two)

@[expose] def WitnessIn (H : Type) [Group H] : Prop :=
  ∀ (T A : Subgroup H) (z : H), IsSylowIn 2 T ⊤ → orderOf z = 2 → (∀ x ∈ T, z * x = x * z) →
    A ≤ T → IsElemAbelian 2 A → A ≠ ⊥ →
    ∃ K : Subgroup H, IsE 1 ⊤ T A K ∧ ¬ K ≤ Subgroup.centralizer ({z} : Set H)

theorem e22qwit_isPGroup {H : Type*} [Group H] {A : Subgroup H} (hA : IsElemAbelian 2 A) :
    IsPGroup 2 A := CFSG.Open.IsElemAbelian.isPGroup hA

theorem e22qwit_card_two_or_four_le {H : Type} [Group H] [Finite H] {A : Subgroup H}
    (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥) : Nat.card A = 2 ∨ 4 ≤ Nat.card A := by
  obtain ⟨k, hk⟩ := (e22qwit_isPGroup hA).exists_card_eq
  rcases k with _ | _ | k
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hA1
  · left
    simpa using hk
  · right
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem e22qwit_mem_of_commute {H : Type} [Group H] [Finite H] {T : Subgroup H}
    (hT : IsSylowIn 2 T ⊤) {z : H} (hz2 : orderOf z = 2) (hzc : ∀ x ∈ T, z * x = x * z) :
    z ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.not_dvd_relIndex
  let Q : Sylow 2 H := hT.isPGroup.toSylow hindex
  have hQ : (Q : Subgroup H) = T := rfl
  have hZ : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hzN : z ∈ Subgroup.normalizer (Q : Set H) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hzc h (hQ ▸ hh)).symm
  have hZN : Subgroup.zpowers z ≤ Subgroup.normalizer (Q : Set H) :=
    (Subgroup.zpowers_le).mpr hzN
  have h1 := hZ.inf_normalizer_sylow Q
  have h2 : z ∈ Subgroup.zpowers z ⊓ (Q : Subgroup H) := by
    rw [← h1]
    exact ⟨Subgroup.mem_zpowers z, hZN (Subgroup.mem_zpowers z)⟩
  exact hQ ▸ h2.2

theorem e22qwit_central_involution_unique {H : Type} [Group H] {T : Subgroup H} {m : ℕ}
    (hm : 2 ≤ m) (e : T ≃* DihedralGroup (2 ^ m)) {z z' : H} (hzT : z ∈ T) (hz'T : z' ∈ T)
    (hz2 : orderOf z = 2) (hz'2 : orderOf z' = 2) (hzc : ∀ t ∈ T, z * t = t * z)
    (hz'c : ∀ t ∈ T, z' * t = t * z') : z = z' := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ι, hι, rfl⟩ := e22pd1_exists_embedding e
  have key : ∀ x : DihedralGroup (2 ^ (k + 2)), orderOf (ι x) = 2 →
      (∀ t ∈ ι.range, ι x * t = t * ι x) → x = DihedralGroup.r (2 ^ (k + 1)) := by
    intro x hx2 hxc
    have hxo : orderOf x = 2 := by rw [← orderOf_injective ι hι x]; exact hx2
    have hxcen : x ∈ Subgroup.center (DihedralGroup (2 ^ (k + 2))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hι
      rw [map_mul, map_mul]
      exact (hxc (ι g) ⟨g, rfl⟩).symm
    have hxsq : x ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hxo] at h
    have hxne : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxo
      omega
    exact CFSG.GorensteinWalter.unique_central_involution_of_dihedral_two_pow
      (m := k + 2) (by omega) x hxcen hxsq hxne
  obtain ⟨d, rfl⟩ := hzT
  obtain ⟨d', rfl⟩ := hz'T
  rw [key d hz2 hzc, key d' hz'2 hz'c]

theorem e22qwit_card_two {G : Type} [Group G] [Finite G] (L T A : Subgroup G) [L.Normal]
    [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤)
    (hAT : A ≤ T) (hA : Nat.card A = 2) {z : G} (hz1 : z ≠ 1) :
    ∃ K : Subgroup G, IsE 1 ⊤ T A K ∧ ¬ K ≤ Subgroup.centralizer ({z} : Set G) := by
  refine ⟨⊤, isE_one_top_of_almostSimple L T A hnc hC hT hLT hAT hA, fun h => hz1 ?_⟩
  have hzC : z ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top g)) z rfl).symm
  rw [hC, Subgroup.mem_bot] at hzC
  exact hzC

theorem WitnessIn.of_mulEquiv {H H' : Type} [Group H] [Group H'] [Finite H] [Finite H']
    (e : H ≃* H') (h : WitnessIn H') : WitnessIn H := by
  intro T A z hT hz2 hzc hAT hAab hA1
  have htop : (⊤ : Subgroup H).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.surjective
  have hT' : IsSylowIn 2 (T.map e.toMonoidHom) ⊤ := by
    have := (E1.isSylowIn_map_mulEquiv e (P := T) (H := ⊤)).mpr hT
    rwa [htop] at this
  have hz2' : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz2
  have hzc' : ∀ x ∈ T.map e.toMonoidHom, e z * x = x * e z := by
    rintro _ ⟨t, ht, rfl⟩
    show e z * e t = e t * e z
    rw [← map_mul, ← map_mul, hzc t ht]
  have hAab' : IsElemAbelian 2 (A.map e.toMonoidHom) := isElemAbelian_map_hom e.toMonoidHom hAab
  have hA1' : A.map e.toMonoidHom ≠ ⊥ := fun hbot =>
    hA1 ((E1.map_eq_bot_iff_mulEquiv e A).mp hbot)
  obtain ⟨K', hK', hK'z⟩ := h _ _ _ hT' hz2' hzc' (Subgroup.map_mono hAT) hAab' hA1'
  have hmap : (K'.map e.symm.toMonoidHom).map e.toMonoidHom = K' := by
    simpa using CFSG.LocalCores.map_map_symm e.symm K'
  refine ⟨K'.map e.symm.toMonoidHom, ?_, ?_⟩
  · refine (E1.isE_map_mulEquiv e).mp ?_
    rw [htop, hmap]
    exact hK'
  · intro hle
    apply hK'z
    rw [← hmap]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hxz := Subgroup.mem_centralizer_iff.mp (hle hx) z rfl
    show e z * e x = e x * e z
    rw [← map_mul, ← map_mul, hxz]

theorem e22qwit_pgl2
    {K : Type} [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) (hq7 : 7 ≤ Nat.card K) :
    WitnessIn (PGL2 K) := by
  have := e22pl2pgl_finite K
  intro T A z hT hz2 hzc hAT hAab hA1
  have hcard3 : 3 < Nat.card K := by omega
  have : (pslRange K).Normal := pslRange_normal hodd hcard3
  have : IsSimpleGroup ↥(pslRange K) := e22pl2pgl_simple_J hcard3
  have hnc := e22pl2pgl_nonabelian_J hcard3
  have hCJ := e22pl2pgl_centralizer_J hodd hcard3
  have hJT := e22pl2pgl_sup_eq_top hodd hT
  obtain ⟨m, hm3, ⟨e⟩⟩ := e22pl2pgl_sylow_dihedral_q hodd hq8 hT
  have hm2 : 2 ≤ m := by omega
  obtain ⟨z₀, hz₀T, hz₀2, hz₀c, hz₀V, hAV⟩ := dihedral_sylow_data hm2 e
  have hzT : z ∈ T := e22qwit_mem_of_commute hT hz2 hzc
  have hzz : z = z₀ := e22qwit_central_involution_unique hm2 e hzT hz₀T hz2 hz₀2 hzc hz₀c
  have hzV : ∀ V : Subgroup (PGL2 K), V ≤ T → IsKleinFour ↥V → z ∈ V :=
    fun V hV hVK => hzz ▸ hz₀V V hV hVK
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  obtain ⟨t, -, htz⟩ := dihedral_central_involution_sq hm2 e hzT hz2 hzc
  have hzJ : z ∈ pslRange K := by
    rw [← htz]
    have := Subgroup.pow_index_mem (pslRange K) t
    rwa [pslRange_index_eq_two hodd] at this
  have hO2 : pCoreOf 2 (⊤ : Subgroup (PGL2 K)) = ⊥ :=
    pCoreOf_top_eq_bot_of_normal_simple (pslRange K) hnc hCJ
  rcases e22qwit_card_two_or_four_le hAab hA1 with hA2 | hA4
  · exact e22qwit_card_two (pslRange K) T A hnc hCJ hT hJT hAT hA2 hz1
  · obtain ⟨hAcard, hAK⟩ := hAV A hAT hAab hA4
    by_cases hAJ : A ≤ pslRange K
    ·
      obtain ⟨V', hV'T, hV', hne, hV'N, hVN, hN8, hC, hcomm⟩ :=
        dihedral_kleinFour_partner hm2 e hAT hAK
      have hV'J : V' ≤ pslRange K := by
        have hT₀ := dihedral_normalizer_le_of_index_two (T₀ := T ⊓ pslRange K) hm3 e inf_le_left
          (e22pl2pgl_relIndex_inf hodd hcard3 hT) (le_inf hAT hAJ) hAK hV'T hV' hVN hV'N hne hN8
        exact ((le_inf hV'T Subgroup.le_normalizer).trans hT₀).trans inf_le_right
      have hcent : Subgroup.centralizer (V' : Set (PGL2 K)) = V' :=
        pgl2_kleinFour_centralizer_eq_self K hodd V' hV'
      have hsurj := e22pl2pgl_normalizer_surjective_q hodd hq8 hq7 hV'J hV'
      exact ⟨Subgroup.normalizer (V' : Set (PGL2 K)),
        isE_one_normalizer_kleinFour hT hO2 hAK hV' hAT hV'T hne hcent hsurj hN8 hVN hC hcomm,
        not_normalizer_le_centralizer hV' hsurj (hzV V' hV'T hV') hz1⟩
    ·
      exact e22pl2pgl_outer_member hodd hcard3 hT hAT hAab hAcard hO2 (hzV A hAT hAK) hz2 hzJ hAJ

theorem e22qwit_psl2
    {K : Type} [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) (hq7 : 7 ≤ Nat.card K) :
    WitnessIn (PSL2 K) := by
  intro T A z hT hz2 hzc hAT hAab hA1
  have hcard3 : 3 < Nat.card K := by omega
  have hsimple : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hperf : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K hcard3
  obtain ⟨S, m, hST, hm2, ⟨e⟩⟩ := e22pl2psl_sylow_dihedral_q hodd hq8 hT
  subst hST
  obtain ⟨z₀, hz₀T, hz₀2, hz₀c, hz₀V, hAV⟩ := dihedral_sylow_data hm2 e
  have hzT : z ∈ (S : Subgroup (PSL2 K)) := e22qwit_mem_of_commute hT hz2 hzc
  have hzz : z = z₀ := e22qwit_central_involution_unique hm2 e hzT hz₀T hz2 hz₀2 hzc hz₀c
  have hzV : ∀ V : Subgroup (PSL2 K), V ≤ (S : Subgroup (PSL2 K)) → IsKleinFour ↥V → z ∈ V :=
    fun V hV hVK => hzz ▸ hz₀V V hV hVK
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hsimple' : IsSimpleGroup ↥(⊤ : Subgroup (PSL2 K)) := Subgroup.topEquiv.isSimpleGroup
  have hcen : Subgroup.center (PSL2 K) = ⊥ := psl2_center_eq_bot K
  have hnc : ∃ a b : ↥(⊤ : Subgroup (PSL2 K)), a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    obtain ⟨x, hx⟩ := exists_ne (1 : PSL2 K)
    have hxc : x ∈ Subgroup.center (PSL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := hcomm ⟨y, Subgroup.mem_top y⟩ ⟨x, Subgroup.mem_top x⟩
      exact congrArg Subtype.val this
    rw [hcen, Subgroup.mem_bot] at hxc
    exact hx hxc
  have hCtop : Subgroup.centralizer ((⊤ : Subgroup (PSL2 K)) : Set (PSL2 K)) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  rcases e22qwit_card_two_or_four_le hAab hA1 with hA2 | hA4
  · exact e22qwit_card_two ⊤ _ A hnc hCtop hT (top_sup_eq _) hAT hA2 hz1
  · obtain ⟨-, hAK⟩ := hAV A hAT hAab hA4
    obtain ⟨V', hV'T, hV', hne, hV'N, hVN, hN8, hC, hcomm⟩ :=
      dihedral_kleinFour_partner hm2 e hAT hAK
    have hO2 : pCoreOf 2 (⊤ : Subgroup (PSL2 K)) = ⊥ :=
      pCoreOf_top_eq_bot_of_normal_simple ⊤ hnc hCtop
    have hcent : Subgroup.centralizer (V' : Set (PSL2 K)) = V' :=
      psl2_kleinFour_centralizer_eq_self K hodd V' hV'
    have hsurj := perfect_dihedral_fourgroup_normalizer_surjective S hm2 e V' hV'T hV'
    exact ⟨Subgroup.normalizer (V' : Set (PSL2 K)),
      isE_one_normalizer_kleinFour hT hO2 hAK hV' hAT hV'T hne hcent hsurj hN8 hVN hC hcomm,
      not_normalizer_le_centralizer hV' hsurj (hzV V' hV'T hV') hz1⟩

theorem e22qwit_transport {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {J : Subgroup H} [J.Normal] (hJ : IsPSL 2 p 1 ↥J)
    (hC : Subgroup.centralizer (J : Set H) = ⊥) :
    Nonempty (H ≃* PSL2 (ZMod p)) ∨ Nonempty (H ≃* PGL2 (ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hodd : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by simp⟩
  have hcard : 3 < Nat.card (ZMod p) := by
    rw [Nat.card_zmod]
    omega
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hJ
  obtain ⟨ι, hι, hPSL, -⟩ := CFSG.ABGDGroups.exists_embedding_of_normal_psl2 hodd hcard e hC
  have hPGL : ι.range ≤ pGammaL2PGLRange (ZMod p) :=
    le_top.trans_eq (e22ptr_pGammaL2PGLRange_eq_top (ZMod p)).symm
  have eι : H ≃* ι.range := MonoidHom.ofInjective hι
  rcases e22ptr_eq_psl_or_eq_pgl (ZMod p) hodd hPSL hPGL with h | h
  · exact Or.inl ⟨eι.trans ((MulEquiv.subgroupCongr h).trans (pGammaL2PSLRangeEquiv _).symm)⟩
  · exact Or.inr ⟨eι.trans ((MulEquiv.subgroupCongr h).trans (pGammaL2PGLRangeEquiv _).symm)⟩

theorem witnessL2 {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp7 : 7 ≤ p) : WitnessL2 p := by
  have : Fact p.Prime := ⟨hp⟩
  intro H _ _ J T A _ hJ hC hT _ z hz2 hzc hAT hAab hA1
  have hK : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hodd : IsOddPrimePower (Nat.card (ZMod p)) := e22pl2pgl_isOddPrimePower hp7 hK
  have hq8 : Nat.card (ZMod p) % 8 = 1 ∨ Nat.card (ZMod p) % 8 = 7 := by rwa [hK]
  have hq7 : 7 ≤ Nat.card (ZMod p) := by rwa [hK]
  have := e22pl2pgl_finite (ZMod p)
  have hW : WitnessIn H := by
    rcases e22qwit_transport hp7 hJ hC with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact WitnessIn.of_mulEquiv e (e22qwit_psl2 hodd hq8 hq7)
    · exact WitnessIn.of_mulEquiv e (e22qwit_pgl2 hodd hq8 hq7)
  exact hW T A z hT hz2 hzc hAT hAab hA1

end CFSG.Quasithin.E2.E22N
