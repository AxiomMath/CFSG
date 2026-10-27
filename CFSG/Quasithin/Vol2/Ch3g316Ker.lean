module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.Ch3g316

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Ker

theorem transfer_apply_eq_pow_index_of_conj {Γ A : Type*} [Group Γ] [CommGroup A]
    {H : Subgroup Γ} [H.FiniteIndex] (ϕ : H →* A) {z : Γ} (hz : z ∈ H)
    (hconj : ∀ g : Γ, ∃ h : H, (h : Γ) = g⁻¹ * z * g ∧ ϕ h = ϕ ⟨z, hz⟩) :
    MonoidHom.transfer ϕ z = ϕ ⟨z, hz⟩ ^ H.index := by
  have : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers z) (Γ ⧸ H))) :=
    Fintype.ofFinite _
  rw [Subgroup.index_eq_sum_minimalPeriod H z, ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine Finset.prod_congr rfl fun q _ => ?_
  obtain ⟨h, hh, hϕ⟩ := hconj q.out.out
  have hpow : (⟨q.out.out⁻¹ * z ^ Function.minimalPeriod (z • ·) q.out * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem H z q.out⟩ : H) =
      h ^ Function.minimalPeriod (z • ·) q.out := by
    apply Subtype.ext
    have := conj_pow (a := q.out.out⁻¹) (b := z) (i := Function.minimalPeriod (z • ·) q.out)
    simp only [inv_inv] at this
    rw [Subgroup.coe_pow, hh, this]
  rw [hpow, map_pow, hϕ]

theorem exists_hom_units_ker_eq_of_index_eq_two {X : Type*} [Group X] {N : Subgroup X}
    (hN : N.index = 2) : ∃ χ : X →* ℤˣ, χ.ker = N := by
  classical
  refine ⟨{ toFun := fun x => if x ∈ N then 1 else -1
            map_one' := by simp
            map_mul' := fun a b => ?_ }, ?_⟩
  · by_cases ha : a ∈ N <;> by_cases hb : b ∈ N <;>
      simp [ha, hb, Subgroup.mul_mem_iff_of_index_two hN]
  · ext x
    by_cases hx : x ∈ N <;> simp [MonoidHom.mem_ker, hx]

theorem exists_hom_units_of_isPGroup {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    {N : Subgroup X} [N.Normal] (hN : N ≠ ⊤) : ∃ μ : X →* ℤˣ, N ≤ μ.ker ∧ μ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (X ⧸ N) := (hX.to_quotient N).isNilpotent
  obtain ⟨n, hn⟩ := hX.index N
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hN (Subgroup.index_eq_one.mp (by simpa using hn))
  have hdvd : 2 ∣ Nat.card (X ⧸ N) := by
    rw [← Subgroup.index]
    exact hn ▸ dvd_pow_self 2 hn0
  obtain ⟨H₂, hH₂, -⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  obtain ⟨χ, hχ⟩ := exists_hom_units_ker_eq_of_index_eq_two hH₂
  refine ⟨χ.comp (QuotientGroup.mk' N), fun x hx => ?_, fun h => ?_⟩
  · simp [MonoidHom.mem_ker, (QuotientGroup.eq_one_iff x).mpr hx]
  · have hχ1 : χ = 1 := MonoidHom.ext fun y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact congrArg (· x) h
    rw [hχ1, MonoidHom.ker_one] at hχ
    rw [← hχ, Subgroup.index_top] at hH₂
    exact absurd hH₂ (by norm_num)

theorem le_of_forall_hom_units_eq_one {Γ : Type*} [Group Γ] [Finite Γ] {H E Z : Subgroup Γ}
    (hH : IsPGroup 2 H) (hodd : ¬ 2 ∣ H.index) (hEH : E ≤ H)
    (hEn : H ≤ Subgroup.normalizer (E : Set Γ)) (hZH : Z ≤ H) (hZn : Z.Normal)
    (hcomm : ∀ z ∈ Z, ∀ g : Γ, ⁅z, g⁆ ∈ E) (hHEZ : H ≤ E ⊔ Z)
    (hχ : ∀ χ : Γ →* ℤˣ, χ = 1) : H ≤ E := by
  by_contra hne
  have : (E.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEH).mpr hEn
  obtain ⟨μ, hμN, hμ1⟩ := exists_hom_units_of_isPGroup hH
    (fun h => hne (Subgroup.subgroupOf_eq_top.mp h))
  have hEμ : ∀ (e : Γ) (he : e ∈ E), μ ⟨e, hEH he⟩ = 1 := fun e he =>
    hμN (Subgroup.mem_subgroupOf.mpr he)
  obtain ⟨z, hzZ, hμz⟩ : ∃ z : Γ, ∃ hz : z ∈ Z, μ ⟨z, hZH hz⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hμ1
    have hle : H ≤ μ.ker.map H.subtype := by
      refine hHEZ.trans (sup_le (fun e he => ?_) (fun z hz => ?_))
      · exact ⟨⟨e, hEH he⟩, hEμ e he, rfl⟩
      · exact ⟨⟨z, hZH hz⟩, hcon z hz, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hx (by simpa using hy)
  have hz : z ∈ H := hZH hzZ
  have hconj : ∀ g : Γ, ∃ h : H, (h : Γ) = g⁻¹ * z * g ∧ μ h = μ ⟨z, hz⟩ := by
    intro g
    have hgz : g⁻¹ * z * g ∈ H := hZH (by simpa using hZn.conj_mem z hzZ g⁻¹)
    have hc : g⁻¹ * z * g * z⁻¹ ∈ E := by
      have h1 := E.inv_mem (hcomm z hzZ g⁻¹)
      simpa [commutatorElement_def, mul_assoc] using h1
    refine ⟨⟨g⁻¹ * z * g, hgz⟩, rfl, ?_⟩
    have hm : (⟨g⁻¹ * z * g, hgz⟩ : H) =
        ⟨g⁻¹ * z * g * z⁻¹, H.mul_mem hgz (H.inv_mem hz)⟩ * ⟨z, hz⟩ :=
      Subtype.ext (by simp)
    rw [hm, map_mul, hEμ _ hc, one_mul]
  have hV : MonoidHom.transfer μ z = 1 := by
    rw [hχ (MonoidHom.transfer μ)]
    rfl
  have hodd' : Odd H.index := Nat.odd_iff.mpr (by omega)
  have hneg : μ ⟨z, hz⟩ = -1 := (Int.units_eq_one_or _).resolve_left hμz
  rw [transfer_apply_eq_pow_index_of_conj μ hz hconj, hneg, hodd'.neg_one_pow] at hV
  exact neg_units_ne_self 1 hV

theorem hom_units_eq_one_of_twoResidual_eq {G : Type*} [Group G] {K : Subgroup G}
    (hK : twoResidual K = K) (χ : K →* ℤˣ) : χ = 1 := by
  set N : Subgroup G := χ.ker.map K.subtype with hN
  have hNK : N ≤ K := Subgroup.map_subtype_le _
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp ?_
    show ((χ.ker.map K.subtype).comap K.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact MonoidHom.normal_ker χ
  have h2 : ∀ y ∈ K, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
    intro y hy
    refine ⟨1, Subgroup.mem_map.mpr ⟨⟨y, hy⟩ ^ 2, ?_, by simp⟩⟩
    rw [MonoidHom.mem_ker, map_pow, Int.units_sq]
  have hle := twoResidual_le_of_isTwoQuotient hNK hKN h2
  rw [hK] at hle
  ext x
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have hyx' : y = x := Subtype.ext hyx
  rw [hyx'] at hy
  simpa using hy

end Ker

theorem sylow_le_of_central_quotient {G : Type} [Group G] [Finite G] {K P D N₀ : Subgroup G}
    (hP : IsSylowTwoOf P K) (hK : twoResidual K = K) (hDP : D ≤ P)
    (hDn : P ≤ Subgroup.normalizer (D : Set G)) (hN₀K : K ≤ Subgroup.normalizer (N₀ : Set G))
    (hN₀D : N₀ ≤ D) (hQP : pCoreOf 2 K ≤ P) (hcomm : ⁅pCoreOf 2 K, K⁆ ≤ N₀)
    (hPD : P ≤ D ⊔ pCoreOf 2 K) : P ≤ D := by
  have _ := hN₀K
  have hPK : P ≤ K := hP.1
  have hDK : D ≤ K := hDP.trans hPK
  have hQK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hQ : ∀ z : K, z ∈ pCore 2 K → (z : G) ∈ pCoreOf 2 K := fun z hz =>
    Subgroup.mem_map_of_mem K.subtype hz
  have hmain := Ker.le_of_forall_hom_units_eq_one (Γ := K) (H := P.subgroupOf K)
    (E := D.subgroupOf K) (Z := pCore 2 K)
    (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm) hP.2.2
    (fun x hx => hDP hx) ?_ (fun z hz => hQP (hQ z hz)) (pCore_normal 2) ?_ ?_
    (Ker.hom_units_eq_one_of_twoResidual_eq hK)
  · exact fun x hx => hmain (show (⟨x, hPK hx⟩ : K) ∈ P.subgroupOf K from hx)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.mp (hDn (show (g : G) ∈ P from hg)) (x : G)
  · intro z hz g
    have h1 : ⁅(z : G), (g : G)⁆ ∈ ⁅pCoreOf 2 K, K⁆ :=
      Subgroup.commutator_mem_commutator (hQ z hz) g.2
    exact hN₀D (hcomm h1)
  · have hsup : P.subgroupOf K ≤ (D ⊔ pCoreOf 2 K).subgroupOf K := fun x hx => hPD hx
    rw [Subgroup.subgroupOf_sup hDK hQK,
      show (pCoreOf 2 K).subgroupOf K = pCore 2 K from
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _] at hsup
    exact hsup

end CFSG.Quasithin.Ch3g316
