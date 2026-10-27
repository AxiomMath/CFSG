module

public import CFSG.RankThree.PartOne.TAIL.Data
public import CFSG.RankThree.PartOne.S12.InputsEleven

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def innK (K : Type*) [Group K] : Subgroup (MulAut K) :=
  (MulAut.conj : K →* MulAut K).range

instance innK_normal (K : Type*) [Group K] : (innK K).Normal where
  conj_mem := by
    rintro _ ⟨k, rfl⟩ a
    refine ⟨a k, ?_⟩
    ext x
    simp [MulAut.conj_apply]

structure OutData (K : Type*) [Group K] : Prop where
  comm : ∀ a b : MulAut K, a * b * a⁻¹ * b⁻¹ ∈ innK K
  index_dvd : (innK K).index ∣ 42

theorem OutData.of_complement {K : Type*} [Group K] [Finite K] (Φ : Subgroup (MulAut K))
    (hc : ∀ a ∈ Φ, ∀ b ∈ Φ, a * b = b * a) (hd : Nat.card Φ ∣ 42)
    (hgen : ∀ β : MulAut K, ∃ i ∈ innK K, ∃ φ ∈ Φ, β = i * φ) : OutData K := by
  have hπ : ∀ β : MulAut K, ∃ φ ∈ Φ,
      QuotientGroup.mk' (innK K) β = QuotientGroup.mk' (innK K) φ := by
    intro β
    obtain ⟨i, hi, φ, hφ, rfl⟩ := hgen β
    refine ⟨φ, hφ, ?_⟩
    have h1 : QuotientGroup.mk' (innK K) i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    rw [map_mul, h1, one_mul]
  refine ⟨fun a b => ?_, ?_⟩
  · obtain ⟨φ₁, hφ₁, h₁⟩ := hπ a
    obtain ⟨φ₂, hφ₂, h₂⟩ := hπ b
    have key : QuotientGroup.mk' (innK K) (a * b * a⁻¹ * b⁻¹) =
        QuotientGroup.mk' (innK K) (φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹) := by
      simp only [map_mul, map_inv, h₁, h₂]
    have hcomm : φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹ = 1 := by
      rw [hc φ₁ hφ₁ φ₂ hφ₂]
      group
    rw [← QuotientGroup.eq_one_iff (N := innK K)]
    show QuotientGroup.mk' (innK K) (a * b * a⁻¹ * b⁻¹) = 1
    rw [key, hcomm, map_one]
  · let f : Φ →* MulAut K ⧸ innK K := (QuotientGroup.mk' (innK K)).comp Φ.subtype
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨φ, hφ, h⟩ := hπ β
      exact ⟨⟨φ, hφ⟩, h.symm⟩
    exact (Subgroup.card_dvd_of_surjective hf).trans hd

theorem OutData.of_mulEquiv {K X : Type*} [Group K] [Group X] (e : K ≃* X) (h : OutData X) :
    OutData K := by
  have hinn : ∀ k : K, MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
    intro k
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hmem : ∀ a : MulAut K, a ∈ innK K ↔ MulAut.congr e a ∈ innK X := by
    intro a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e k, (hinn k).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨e.symm x, ?_⟩
      apply (MulAut.congr e).injective
      rw [hinn, MulEquiv.apply_symm_apply, hx]
  refine ⟨fun a b => ?_, ?_⟩
  · rw [hmem, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h.comm _ _
  · have hc : innK K = (innK X).comap (MulAut.congr e).toMonoidHom := by
      ext a
      exact hmem a
    rw [hc, Subgroup.index_comap_of_surjective _ (MulAut.congr e).surjective]
    exact h.index_dvd

section Parts

variable {G : Type} [Group G]

theorem mem_sup_centralizer_iff {K : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ K ⊔ Subgroup.centralizer (K : Set G) ↔ K.normalizerMonoidHom ⟨n, hn⟩ ∈ innK ↥K := by
  have hCN : Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G)
  constructor
  · intro h
    rw [sup_comm] at h
    have h' : n ∈ ((Subgroup.centralizer (K : Set G) ⊔ K : Subgroup G) : Set G) := h
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at h'
    obtain ⟨z, hz, k, hk, rfl⟩ := h'
    refine ⟨⟨k, hk⟩, ?_⟩
    ext x
    have hy : k * (x : G) * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk x.2) (K.inv_mem hk)
    have hzy : z * (k * (x : G) * k⁻¹) = (k * (x : G) * k⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.1 hz _ hy).symm
    simp only [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_mul, Subgroup.coe_inv]
    symm
    calc z * k * (x : G) * (z * k)⁻¹ = z * (k * (x : G) * k⁻¹) * z⁻¹ := by group
      _ = k * (x : G) * k⁻¹ := by rw [hzy]; group
  · rintro ⟨⟨k, hk⟩, hkn⟩
    have hkn' : ∀ x : ↥K, (k : G) * x * (k : G)⁻¹ = n * x * n⁻¹ := by
      intro x
      have := congrArg (fun φ : MulAut ↥K => ((φ x : ↥K) : G)) hkn
      simpa [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    have hz : k⁻¹ * n ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hkn' ⟨x, hx⟩
      simp only at h1
      calc x * (k⁻¹ * n) = k⁻¹ * (k * x * k⁻¹) * n := by group
        _ = k⁻¹ * (n * x * n⁻¹) * n := by rw [h1]
        _ = k⁻¹ * n * x := by group
    have : n = k * (k⁻¹ * n) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk hz

theorem seven_dvd_of_zpow_mem {Q : Subgroup G} {c : G} (hcQ : c ∉ Q) (hc7 : c ^ 7 ∈ Q) {k : ℤ}
    (hk : c ^ k ∈ Q) : (7 : ℤ) ∣ k := by
  by_contra h
  have hp : Prime (7 : ℤ) := Int.prime_iff_natAbs_prime.2 (by norm_num)
  have hcop : IsCoprime (7 : ℤ) k := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 h
  obtain ⟨a, b, hab⟩ := hcop
  apply hcQ
  have : c = (c ^ 7) ^ a * (c ^ k) ^ b := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : ((7 : ℕ) : ℤ) * a + k * b = 1 := by push_cast; linarith
    rw [this, zpow_one]
  rw [this]
  exact Q.mul_mem (Q.zpow_mem hc7 a) (Q.zpow_mem hk b)

theorem out_central_of_outData {K : Subgroup G} {c : G} (hO : OutData ↥K) (hc7 : c ^ 7 = 1)
    (hc : InducesFieldAut 7 c K) :
    ∀ n ∈ Subgroup.normalizer (K : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers c →
      n * c * n⁻¹ = c := by
  intro n hn hnc
  obtain ⟨hcN, hcnot, hc7mem, -⟩ := hc
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hnc
  set ρ := K.normalizerMonoidHom with hρ
  set a : MulAut ↥K := ρ ⟨n, hn⟩ with ha
  set b : MulAut ↥K := ρ ⟨c, hcN⟩ with hb
  have h1 : a * b * a⁻¹ = b ^ j := by
    have e : (⟨n, hn⟩ : ↥(Subgroup.normalizer (K : Set G))) * ⟨c, hcN⟩ * ⟨n, hn⟩⁻¹ =
        (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ j := by
      apply Subtype.ext
      simp [hj]
    rw [ha, hb, ← map_inv, ← map_mul, ← map_mul, e, map_zpow]
  have h2 := hO.comm a b
  have h3 : a * b * a⁻¹ * b⁻¹ = b ^ (j - 1) := by
    rw [h1, zpow_sub_one]
  rw [h3] at h2
  have hbk : b ^ (j - 1) = ρ ((⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ (j - 1)) := by
    rw [hb, map_zpow]
  have hcj : c ^ (j - 1) ∈ K ⊔ Subgroup.centralizer (K : Set G) := by
    have hnm : c ^ (j - 1) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.zpow_mem _ hcN _
    rw [mem_sup_centralizer_iff hnm]
    have : (⟨c ^ (j - 1), hnm⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ (j - 1) := by
      apply Subtype.ext
      simp
    rw [this, ← hbk]
    exact h2
  obtain ⟨q, hq⟩ := seven_dvd_of_zpow_mem hcnot hc7mem hcj
  have : c ^ (j - 1) = 1 := by
    rw [hq, zpow_mul]
    have : c ^ (7 : ℤ) = 1 := by exact_mod_cast hc7
    rw [this, one_zpow]
  calc n * c * n⁻¹ = c ^ j := hj.symm
    _ = c ^ (j - 1) * c := by rw [← zpow_add_one]; congr 1; ring
    _ = c := by rw [this, one_mul]

theorem out_index_of_outData [Finite G] {K : Subgroup G} (hO : OutData ↥K) :
    ∀ R : Subgroup G, IsPGroup 7 R → R ≤ Subgroup.normalizer (K : Set G) →
      (R ⊓ (K ⊔ Subgroup.centralizer (K : Set G))).relIndex R ≤ 7 := by
  intro R hR hRN
  have h1 : (R ⊓ (K ⊔ Subgroup.centralizer (K : Set G))).relIndex R =
      (K ⊔ Subgroup.centralizer (K : Set G)).relIndex R := Subgroup.inf_relIndex_left _ _
  have h2 : ((K ⊔ Subgroup.centralizer (K : Set G)).subgroupOf
      (Subgroup.normalizer (K : Set G))).relIndex
      (R.subgroupOf (Subgroup.normalizer (K : Set G))) =
      (K ⊔ Subgroup.centralizer (K : Set G)).relIndex R := Subgroup.relIndex_subgroupOf hRN
  have h3 : (K ⊔ Subgroup.centralizer (K : Set G)).subgroupOf
      (Subgroup.normalizer (K : Set G)) = (innK ↥K).comap K.normalizerMonoidHom := by
    ext ⟨n, hn⟩
    exact mem_sup_centralizer_iff hn
  rw [h1, ← h2, h3, Subgroup.relIndex_comap]
  have hR' : IsPGroup 7 (R.subgroupOf (Subgroup.normalizer (K : Set G))) := hR.comap_subtype
  have hP : IsPGroup 7 ((R.subgroupOf (Subgroup.normalizer (K : Set G))).map
      K.normalizerMonoidHom) := hR'.map _
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
  set P := (R.subgroupOf (Subgroup.normalizer (K : Set G))).map K.normalizerMonoidHom with hPdef
  have hr1 : (innK ↥K).relIndex P ∣ 42 :=
    (Subgroup.relIndex_dvd_index_of_normal _ _).trans hO.index_dvd
  have hr2 : (innK ↥K).relIndex P ∣ 7 ^ m := hm ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, hk, hk7⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hr2
  rw [hk7]
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k ≤ 1 := by omega
    have : 7 ^ k ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h49 : 49 ∣ 42 := by
    have : 7 ^ 2 ∣ 7 ^ k := pow_dvd_pow 7 hk2
    rw [← hk7] at this
    exact (by norm_num : (49 : ℕ) = 7 ^ 2) ▸ this.trans hr1
  omega

theorem rank_one_of_sylow [Finite G] {K : Subgroup G}
    (hS : ∀ R : Subgroup G, R ≤ K → IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49) :
    CFSG.pRank 7 ↥K ≤ 1 := by
  unfold CFSG.pRank
  refine csSup_le' ?_
  rintro r ⟨A, hA, hr⟩
  have hA7 : IsPGroup 7 ↥A := IsElementaryAbelian.isPGroup 7 ↥A
  have hR : IsPGroup 7 (A.map K.subtype) := hA7.map _
  have hcyc : IsCyclic ↥(A.map K.subtype) := (hS _ (Subgroup.map_subtype_le A) hR).1
  have hcyc' : IsCyclic ↥A :=
    (Subgroup.equivMapOfInjective A K.subtype K.subtype_injective).isCyclic.2 hcyc
  have hexp : Monoid.exponent ↥A ∣ 7 := IsElementaryAbelian.exponent_dvd_p 7 ↥A
  rw [IsCyclic.exponent_eq_card] at hexp
  have h7 : Nat.card ↥A ≤ 7 := Nat.le_of_dvd (by norm_num) hexp
  rw [hr] at h7
  by_contra hlt
  have : 7 ^ 2 ≤ 7 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem kData_of_parts [Finite G] {K : Subgroup G} {c : G}
    (hZ : K ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (hS : ∀ R : Subgroup G, R ≤ K → IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49)
    (hO : OutData ↥K) (hc7 : c ^ 7 = 1) (hc : InducesFieldAut 7 c K) : KData G K c :=
  ⟨hZ, rank_one_of_sylow hS, hS, out_index_of_outData hO, out_central_of_outData hO hc7 hc⟩

end Parts


end CFSG.RankThree.PartOne.TAIL
