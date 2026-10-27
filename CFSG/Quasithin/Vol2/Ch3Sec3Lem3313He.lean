module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313Pre

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactAutHeSylow : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) →
    ∀ A S : Subgroup (MulAut Q), (MulAut.conj : Q →* MulAut Q).range ≤ A →
      IsSylowTwoOf S A → Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A ≤ S

namespace Lem3313

variable {G : Type} [Group G] [Finite G] {T H : Subgroup G}

theorem comm_mem_pCoreOf_of_he (hF : FactAutHeSylow) {K X : Subgroup G}
    (he : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))
    (hEN : K ⊔ X ≤ Subgroup.normalizer (K : Set G)) (hTE : IsSylowTwoOf T (K ⊔ X)) {d : G}
    (hdE : d ∈ K ⊔ X) (hdT : d ∈ Subgroup.normalizer (T : Set G)) (hodd : Odd (orderOf d))
    {y : G} (hy : y ∈ K) : d * y * d⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
  set φ := Vol2.Ch10.SecB.conjLBar K X hEN with hφ
  set S : Subgroup (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) := (T.subgroupOf (K ⊔ X)).map φ with hS
  have hSyl : IsSylowTwoOf S φ.range := Vol2.Ch10.SecB.isSylowTwoOf_map_range hTE φ
  have hInn : (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).range ≤
      φ.range := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
    refine ⟨⟨l, Subgroup.mem_sup_left hl⟩, ?_⟩
    ext q'
    obtain ⟨⟨l', hl'⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q'
    rw [Vol2.Ch10.SecB.conjLBar_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have key : ∀ (g : G) (hg : g ∈ K ⊔ X), g ∈ Subgroup.normalizer (T : Set G) →
      ∀ s ∈ S, φ ⟨g, hg⟩ * s * (φ ⟨g, hg⟩)⁻¹ ∈ S := by
    rintro g hg hgT _ ⟨⟨t, htE⟩, htT, rfl⟩
    have htT' : t ∈ T := Subgroup.mem_subgroupOf.mp htT
    have h1 : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hgT t).mp htT'
    refine ⟨⟨g * t * g⁻¹, hTE.1 h1⟩, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    have e : (⟨g * t * g⁻¹, hTE.1 h1⟩ : ↥(K ⊔ X)) = ⟨g, hg⟩ * ⟨t, htE⟩ * (⟨g, hg⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hdi : d⁻¹ ∈ K ⊔ X := (K ⊔ X).inv_mem hdE
  have haN : φ ⟨d, hdE⟩ ∈ Subgroup.normalizer (S : Set (MulAut (↥K ⧸ CFSG.pCore 2 ↥K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨key d hdE hdT s, fun hs => ?_⟩
    have h1 := key d⁻¹ hdi (Subgroup.inv_mem _ hdT) _ hs
    have e : (⟨d⁻¹, hdi⟩ : ↥(K ⊔ X)) = (⟨d, hdE⟩)⁻¹ := rfl
    rw [e, map_inv] at h1
    simpa [mul_assoc] using h1
  have haS : φ ⟨d, hdE⟩ ∈ S := hF _ he _ S hInn hSyl ⟨haN, ⟨d, hdE⟩, rfl⟩
  obtain ⟨j, hj⟩ := hSyl.2.1 ⟨_, haS⟩
  have hj' : φ ⟨d, hdE⟩ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hd1 : φ ⟨d, hdE⟩ ^ orderOf d = 1 := by
    have h1 : (⟨d, hdE⟩ : ↥(K ⊔ X)) ^ orderOf d = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← map_pow, h1, map_one]
  have hcop : Nat.Coprime (2 ^ j) (orderOf d) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  have ha1 : φ ⟨d, hdE⟩ = 1 := by
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hd1)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h1
    exact orderOf_eq_one_iff.mp h1
  have hdy : d * y * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hEN hdE) y).mp hy
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d * y * d⁻¹, hdy⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hy⟩ := by
    calc (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d * y * d⁻¹, hdy⟩ : ↥K ⧸ CFSG.pCore 2 ↥K)
        = φ ⟨d, hdE⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hy⟩) :=
          (Vol2.Ch10.SecB.conjLBar_mk hEN ⟨d, hdE⟩ hy).symm
      _ = QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hy⟩ := by rw [ha1]; rfl
  have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨d * y * d⁻¹, hdy⟩ * (⟨y, hy⟩ : ↥K)⁻¹) :
      ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem le_normalizer_of_he (hHe : FactAutHeSylow) (hT : quasithinIsSylowTwo T)
    (hTsyl : IsSylowTwoOf T H) {D K : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (K : Set G)) (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (hDodd : Odd (Nat.card D))
    (hYK : oTwoUpper H ≤ K)
    (he : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hTsyl.1
  have hEN : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTL
  have hEN' : K ⊔ (T ⊔ D) ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (sup_le hTL hDK)
  have hTE : IsSylowTwoOf T (K ⊔ (T ⊔ D)) := ⟨le_sup_left.trans le_sup_right, hT.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le hT (le_sup_left.trans le_sup_right)⟩
  have hcomm : ∀ d ∈ D, ∀ y ∈ K, d * y * d⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
    intro d hd y hy
    have hodd : Odd (orderOf d) := by
      have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hDodd h1
    exact comm_mem_pCoreOf_of_he hHe he hEN' hTE
      ((le_sup_right.trans le_sup_right : D ≤ K ⊔ (T ⊔ D)) hd) (hDT hd) hodd hy
  have hOK : pCoreOf 2 K ≤ H := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K (K ⊔ T)
        le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hEN)
    have hTKT : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hT.1,
      Vol2.Ch10.SecA.not_two_dvd_index_of_le hT le_sup_right⟩
    exact (h1.trans (pCoreOf_le_of_isSylowTwoOf hTKT)).trans hTH
  intro d hd
  exact mem_normalizer_oTwoUpper_of_comm hOK hYK (hcomm d hd) (hcomm d⁻¹ (D.inv_mem hd))

end Lem3313

end CFSG.Quasithin.H13
