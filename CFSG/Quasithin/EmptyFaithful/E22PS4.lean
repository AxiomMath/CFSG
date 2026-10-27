module

public import CFSG.Quasithin.H13.NQCoreA6EOneStmt
import CFSG.Quasithin.H13.NQCoreAlt6Lift
import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem e22ps4_perm3_prod_conj (g : Equiv.Perm (Fin 3)) (hg : g ≠ 1) :
    ∃ c : Equiv.Perm (Fin 3), (g * (c * g * c⁻¹)) ^ 3 = 1 ∧ g * (c * g * c⁻¹) ≠ 1 := by
  revert g
  decide +kernel

theorem e22ps4_perm3_normal_pGroup_eq_bot (N : Subgroup (Equiv.Perm (Fin 3))) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  by_contra hg1
  obtain ⟨c, h3, h1⟩ := e22ps4_perm3_prod_conj g hg1
  have hy : g * (c * g * c⁻¹) ∈ N := N.mul_mem hg (Subgroup.Normal.conj_mem ‹N.Normal› g hg c)
  obtain ⟨k, hk⟩ := hN ⟨_, hy⟩
  have hk' : (g * (c * g * c⁻¹)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  apply h1
  have hd3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have h := Nat.dvd_gcd hd3 hd2
  rw [hcop] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

theorem e22ps4_perm3_even_sq (σ : Equiv.Perm (Fin 3)) (h1 : Equiv.Perm.sign σ = 1)
    (h2 : σ ^ 2 = 1) : σ = 1 := by
  revert σ
  decide +kernel

theorem e22ps4_perm3_comm_sq (a σ : Equiv.Perm (Fin 3)) (ha : Equiv.Perm.sign a = 1)
    (hσ : Equiv.Perm.sign σ ≠ 1) : a * (⁅a, σ⁆ ^ 2)⁻¹ = 1 := by
  revert a σ
  decide +kernel

theorem e22ps4_pCore_eq_ker {K : Type*} [Group K] [Finite K] (Φ : K →* Equiv.Perm (Fin 3))
    (hΦ : Function.Surjective Φ) (hker : IsPGroup 2 Φ.ker) :
    CFSG.Open.pCore 2 K = Φ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCore 2 Φ.normal_ker hker)
  have hn : ((CFSG.Open.pCore 2 K).map Φ).Normal :=
    (CFSG.LieType.BorelTits.pCore_normal 2).map Φ hΦ
  have hp : IsPGroup 2 ((CFSG.Open.pCore 2 K).map Φ) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).map Φ
  have hb := e22ps4_perm3_normal_pGroup_eq_bot _ hp
  intro x hx
  rw [MonoidHom.mem_ker]
  have hx' : Φ x ∈ (CFSG.Open.pCore 2 K).map Φ := Subgroup.mem_map_of_mem Φ hx
  rw [hb] at hx'
  simpa using hx'

omit [Finite H] in
theorem e22ps4_exists_phi {V' : Subgroup H} (hV' : IsKleinFour ↥V')
    (hcent : Subgroup.centralizer (V' : Set H) = V')
    (hsurj : Function.Surjective V'.normalizerMonoidHom) :
    ∃ Φ : ↥(Subgroup.normalizer (V' : Set H)) →* Equiv.Perm (Fin 3),
      Function.Surjective Φ ∧ Φ.ker = V'.subgroupOf (Subgroup.normalizer (V' : Set H)) := by
  have := hV'
  refine ⟨(CFSG.GorensteinWalter.kleinFourAutSymmetricThreeEquiv V').toMonoidHom.comp
    V'.normalizerMonoidHom, ?_, ?_⟩
  · exact (CFSG.GorensteinWalter.kleinFourAutSymmetricThreeEquiv V').surjective.comp hsurj
  · ext x
    have h1 : x ∈ V'.normalizerMonoidHom.ker ↔
        x ∈ V'.subgroupOf (Subgroup.normalizer (V' : Set H)) := by
      rw [Subgroup.normalizerMonoidHom_ker, hcent]
    rw [← h1, MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (MulEquiv.injective _)]

omit [Finite H] in
theorem e22ps4_card_normalizer {V' : Subgroup H} (hV' : IsKleinFour ↥V')
    (hcent : Subgroup.centralizer (V' : Set H) = V')
    (hsurj : Function.Surjective V'.normalizerMonoidHom) :
    Nat.card (Subgroup.normalizer (V' : Set H)) = 24 := by
  have := hV'
  have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [CFSG.GorensteinWalter.kleinFourAut_card V'] at h1
  have h2 : Nat.card V'.normalizerMonoidHom.ker = 4 := by
    rw [Subgroup.normalizerMonoidHom_ker, hcent,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := V'))).toEquiv]
    exact IsKleinFour.card_four
  omega

theorem e22ps4_card_inf {K₀ V V' : Subgroup H} (h8 : Nat.card K₀ = 8) (hV : V ≤ K₀)
    (hV' : V' ≤ K₀) (hc : Nat.card V = 4) (hc' : Nat.card V' = 4) (hne : V' ≠ V) :
    Nat.card ↥(V ⊓ V') = 2 := by
  have hr : ∀ W : Subgroup H, W ≤ K₀ → Nat.card W = 4 → W.relIndex K₀ = 2 := by
    intro W hW hcW
    have h := Subgroup.relIndex_mul_card W K₀
    rw [inf_eq_left.mpr hW, hcW, h8] at h
    omega
  have h1 := Subgroup.relIndex_inf_le (H := V) (K := V') (L := K₀)
  rw [hr V hV hc, hr V' hV' hc'] at h1
  have h2 := Subgroup.relIndex_mul_card (V ⊓ V') K₀
  rw [inf_eq_left.mpr (inf_le_left.trans hV), h8] at h2
  have h3 : Nat.card ↥(V ⊓ V') ∣ 4 := hc ▸ Subgroup.card_dvd_of_le inf_le_left
  have h4 : Nat.card ↥(V ⊓ V') ≠ 4 := by
    intro h
    have hVV' : V ⊓ V' = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hle : V ≤ V' := hVV' ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  have h5 : Nat.card ↥(V ⊓ V') ≤ 4 := Nat.le_of_dvd (by norm_num) h3
  have h6 : 0 < Nat.card ↥(V ⊓ V') := Nat.card_pos
  generalize Nat.card ↥(V ⊓ V') = c at *
  interval_cases c <;> omega

theorem e22ps4_exists_ne {V' : Subgroup H} (hV' : IsKleinFour ↥V') (z : ↥V') :
    ∃ w : ↥V', w ≠ 1 ∧ w ≠ z := by
  classical
  have := hV'
  have : Fintype ↥V' := Fintype.ofFinite ↥V'
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset ↥V') ⊆ {1, z} := by
    intro w _
    by_cases hw : w = 1
    · simp [hw]
    · simp [hcon w hw]
  have h1 := Finset.card_le_card hsub
  have h2 : ({1, z} : Finset ↥V').card ≤ 2 := Finset.card_le_two
  have h3 : (Finset.univ : Finset ↥V').card = 4 := by
    rw [Finset.card_univ]
    exact IsKleinFour.card_four'
  omega

theorem e22ps4_comm_gen {K : Type*} [Group K] (Φ : K →* Equiv.Perm (Fin 3)) (W : Subgroup K)
    (hW : ∃ w ∈ W, Φ w ∉ alternatingGroup (Fin 3)) :
    (alternatingGroup (Fin 3)).comap Φ ≤ Φ.ker ⊔ ⁅(alternatingGroup (Fin 3)).comap Φ, W⁆ := by
  obtain ⟨w, hwW, hw⟩ := hW
  intro x hx
  have hc : ⁅x, w⁆ ∈ ⁅(alternatingGroup (Fin 3)).comap Φ, W⁆ :=
    Subgroup.commutator_mem_commutator hx hwW
  have hker : x * (⁅x, w⁆ ^ 2)⁻¹ ∈ Φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, map_pow, map_commutatorElement]
    exact e22ps4_perm3_comm_sq (Φ x) (Φ w) (Equiv.Perm.mem_alternatingGroup.mp hx)
      (fun h => hw (Equiv.Perm.mem_alternatingGroup.mpr h))
  have hx' : x = (x * (⁅x, w⁆ ^ 2)⁻¹) * ⁅x, w⁆ ^ 2 := by group
  rw [hx']
  exact Subgroup.mul_mem_sup hker (Subgroup.pow_mem _ hc 2)

theorem e22ps4_exists_odd {V V' K : Subgroup H} (hV : IsKleinFour ↥V) (hV' : IsKleinFour ↥V')
    (hne : V' ≠ V) (hVK : V ≤ K) (Φ : ↥K →* Equiv.Perm (Fin 3))
    (hΦk : Φ.ker = V'.subgroupOf K) :
    ∃ w ∈ V.subgroupOf K, Φ w ∉ alternatingGroup (Fin 3) := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ V' := by
    intro v hv
    have hw : (⟨v, hVK hv⟩ : K) ∈ V.subgroupOf K := hv
    have h1 := hcon _ hw
    have h2 : (⟨v, hVK hv⟩ : K) ^ 2 = 1 := by
      have h3 : (⟨v, hv⟩ : V) * ⟨v, hv⟩ = 1 := IsKleinFour.mul_self _
      have h4 : v * v = 1 := congrArg Subtype.val h3
      refine Subtype.ext ?_
      simpa [pow_two] using h4
    have h5 : Φ ⟨v, hVK hv⟩ = 1 := e22ps4_perm3_even_sq _
      (Equiv.Perm.mem_alternatingGroup.mp h1) (by rw [← map_pow, h2, map_one])
    have h6 : (⟨v, hVK hv⟩ : K) ∈ Φ.ker := h5
    rw [hΦk] at h6
    exact h6
  have hcV : Nat.card V = 4 := IsKleinFour.card_four
  have hcV' : Nat.card V' = 4 := IsKleinFour.card_four
  exact hne (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem e22ps4_typeOne {T V V' K : Subgroup H} (hT : IsSylowIn 2 T ⊤)
    (hV : IsKleinFour ↥V) (hV' : IsKleinFour ↥V') (hVT : V ≤ T) (hV'T : V' ≤ T)
    (hne : V' ≠ V) (hK24 : Nat.card K = 24) (hVK : V ≤ K) (hV'K : V' ≤ K)
    (Φ : ↥K →* Equiv.Perm (Fin 3)) (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker = V'.subgroupOf K) (hN8 : Nat.card ↥(T ⊓ K) = 8)
    (hC : T ⊓ Subgroup.centralizer (V : Set H) ≤ K) (hcomm : ⁅T ⊓ K, V⁆ ≤ V') :
    CFSG.Quasithin.H13.NQCore.E1TypeOne ⊤ T V K := by
  have hcV : Nat.card V = 4 := IsKleinFour.card_four
  have hcV' : Nat.card V' = 4 := IsKleinFour.card_four
  have hV'p : IsPGroup 2 V' := IsPGroup.of_card (n := 2) (by rw [hcV']; norm_num)
  have hker : IsPGroup 2 Φ.ker := by
    rw [hΦk]
    exact hV'p.of_equiv (Subgroup.subgroupOfEquivOfLe hV'K).symm
  have hcore : pCoreOf 2 K = V' := by
    unfold pCoreOf
    rw [e22ps4_pCore_eq_ker Φ hΦs hker, hΦk]
    exact Subgroup.map_subgroupOf_eq_of_le hV'K
  set PK : Subgroup ↥K := (alternatingGroup (Fin 3)).comap Φ with hPK
  have hPKn : PK.Normal := Subgroup.normal_comap Φ
  have hPK_idx : PK.index = 2 := by
    rw [hPK, Subgroup.index_comap_of_surjective _ hΦs]
    exact alternatingGroup.index_eq_two
  have hPK_card : Nat.card PK = 12 := by
    have h := Subgroup.card_mul_index PK
    rw [hPK_idx, hK24] at h
    omega
  have hPmap : (PK.map K.subtype).subgroupOf K = PK :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective PK
  have hPcard : Nat.card (PK.map K.subtype) = 12 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hPK_card
  have hkerPK : Φ.ker ≤ PK := fun x hx => by
    rw [hPK, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Subgroup.one_mem _
  have hV'P : V' ≤ PK.map K.subtype := by
    have h := Subgroup.map_mono (f := K.subtype) hkerPK
    rwa [hΦk, Subgroup.map_subgroupOf_eq_of_le hV'K] at h
  have hgen : PK.map K.subtype = V' ⊔ ⁅PK.map K.subtype, V⁆ := by
    obtain ⟨w, hw, hwA⟩ := e22ps4_exists_odd hV hV' hne hVK Φ hΦk
    have h1 := e22ps4_comm_gen Φ (V.subgroupOf K) ⟨w, hw, hwA⟩
    have h2 : ⁅PK, V.subgroupOf K⁆ ≤ PK := Subgroup.commutator_le_left _ _
    have h1' := Subgroup.map_mono (f := K.subtype) h1
    have h2' := Subgroup.map_mono (f := K.subtype) h2
    rw [Subgroup.map_sup, Subgroup.map_commutator, hΦk, Subgroup.map_subgroupOf_eq_of_le hV'K,
      Subgroup.map_subgroupOf_eq_of_le hVK] at h1'
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVK] at h2'
    exact le_antisymm h1' (sup_le hV'P h2')
  have hV₀ : V ≤ T ⊓ K := le_inf hVT hVK
  have hV'₀ : V' ≤ T ⊓ K := le_inf hV'T hV'K
  refine ⟨le_top, hVK, hC, ?_, ⟨PK.map K.subtype, 3, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨inf_le_right, hT.isPGroup.to_le inf_le_left, ?_⟩
    have h := Subgroup.relIndex_mul_card (T ⊓ K) K
    rw [inf_eq_left.mpr (inf_le_right : T ⊓ K ≤ K), hN8, hK24] at h
    have hr : (T ⊓ K).relIndex K = 3 := by omega
    rw [hr]
    norm_num
  · rw [hcore]
    exact hV'P
  · exact Subgroup.map_subtype_le _
  · rw [hPmap]
    exact hPKn
  · rw [hcore, hPcard, hcV']
  · exact ⟨1, by rw [hK24, hPcard]; norm_num⟩
  · rw [hcore]
    exact hgen
  · rw [hcore, hcV, e22ps4_card_inf hN8 hV₀ hV'₀ hcV hcV' hne]
  · rw [hcore]
    exact hcomm

theorem isE_one_normalizer_kleinFour {T V V' : Subgroup H} (hT : IsSylowIn 2 T ⊤)
    (hO2 : pCoreOf 2 (⊤ : Subgroup H) = ⊥)
    (hV : IsKleinFour ↥V) (hV' : IsKleinFour ↥V') (hVT : V ≤ T) (hV'T : V' ≤ T) (hne : V' ≠ V)
    (hcent : Subgroup.centralizer (V' : Set H) = V')
    (hsurj : Function.Surjective V'.normalizerMonoidHom)
    (hN8 : Nat.card ↥(T ⊓ Subgroup.normalizer (V' : Set H)) = 8)
    (hVN : V ≤ Subgroup.normalizer (V' : Set H))
    (hC : T ⊓ Subgroup.centralizer (V : Set H) ≤ Subgroup.normalizer (V' : Set H))
    (hcomm : ⁅T ⊓ Subgroup.normalizer (V' : Set H), V⁆ ≤ V') :
    IsE 1 ⊤ T V (Subgroup.normalizer (V' : Set H)) := by
  obtain ⟨Φ, hΦs, hΦk⟩ := e22ps4_exists_phi hV' hcent hsurj
  exact CFSG.Quasithin.H13.NQCore.isE_one_of_typeOne hO2
    (e22ps4_typeOne hT hV hV' hVT hV'T hne (e22ps4_card_normalizer hV' hcent hsurj) hVN
      Subgroup.le_normalizer Φ hΦs hΦk hN8 hC hcomm)

theorem not_normalizer_le_centralizer {V' : Subgroup H} (hV' : IsKleinFour ↥V')
    (hsurj : Function.Surjective V'.normalizerMonoidHom) {z : H} (hz : z ∈ V') (hz1 : z ≠ 1) :
    ¬ Subgroup.normalizer (V' : Set H) ≤ Subgroup.centralizer ({z} : Set H) := by
  classical
  have := hV'
  intro hle
  have hz1' : (⟨z, hz⟩ : ↥V') ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  obtain ⟨w, hw1, hwz⟩ := e22ps4_exists_ne hV' ⟨z, hz⟩
  have he : (Equiv.swap (⟨z, hz⟩ : ↥V') w) 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne hz1'.symm hw1.symm
  obtain ⟨n, hn⟩ := hsurj (IsKleinFour.mulEquiv (Equiv.swap (⟨z, hz⟩ : ↥V') w) he)
  have h1 : V'.normalizerMonoidHom n ⟨z, hz⟩ = w := by
    rw [hn]
    exact Equiv.swap_apply_left _ _
  have h2 : ((V'.normalizerMonoidHom n ⟨z, hz⟩ : ↥V') : H) = (n : H) * z * (n : H)⁻¹ :=
    V'.normalizerMonoidHom_apply_apply_coe n ⟨z, hz⟩
  have h3 : z * (n : H) = (n : H) * z :=
    Subgroup.mem_centralizer_iff.mp (hle n.2) z rfl
  have h4 : (n : H) * z * (n : H)⁻¹ = z := by
    rw [← h3]
    group
  rw [h1, h4] at h2
  exact hwz (Subtype.ext h2)

end CFSG.Quasithin.E22L2
