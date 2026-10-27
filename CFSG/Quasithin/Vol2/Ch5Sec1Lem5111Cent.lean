module

public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Cent

variable {A : Type} [Group A] [Finite A]

theorem centralizer_le_of_pCore_eq_bot {Y : Subgroup A} [Y.Normal]
    (hO : CFSG.pCore 2 A = ⊥) (h2 : ∀ a : A, ∃ e : ℕ, a ^ 2 ^ e ∈ Y) :
    Subgroup.centralizer (Y : Set A) ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (Y : Set A) with hCdef
  have hker : (QuotientGroup.mk' (Y.subgroupOf C)).ker ≤ Subgroup.center ↥C := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp z.2 x hx).symm
  have hQ2 : IsPGroup 2 (↥C ⧸ Y.subgroupOf C) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 c
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact he
  have : Group.IsNilpotent (↥C ⧸ Y.subgroupOf C) := hQ2.isNilpotent
  have : Group.IsNilpotent ↥C := Subgroup.isNilpotent_of_ker_le_center _ hker
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hPn : (P : Subgroup ↥C).Normal := inferInstance
  have := Sylow.unique_of_normal P hPn
  have hmemP : ∀ y : ↥C, (∃ e : ℕ, y ^ 2 ^ e = 1) → y ∈ (P : Subgroup ↥C) := by
    rintro y ⟨e, he⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one he)
    have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨Q, hQ⟩ := hy2.exists_le_sylow
    rw [Subsingleton.elim Q P] at hQ
    exact hQ (Subgroup.mem_zpowers y)
  have hP' : (P : Subgroup ↥C).map C.subtype ≤ CFSG.pCore 2 A := by
    refine le_sSup ⟨⟨fun x hx a => ?_⟩, (P.isPGroup').map C.subtype⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have haC : a * (y : A) * a⁻¹ ∈ C :=
      (inferInstance : C.Normal).conj_mem _ y.2 a
    obtain ⟨e, he⟩ := P.isPGroup' ⟨y, hy⟩
    have he' : (y : A) ^ 2 ^ e = 1 := by
      have := congrArg (fun z : ↥(P : Subgroup ↥C) => ((z : ↥C) : A)) he
      simpa using this
    refine ⟨⟨_, haC⟩, hmemP _ ⟨e, Subtype.ext ?_⟩, rfl⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [conj_pow, he', mul_one, mul_inv_cancel]
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at hP'
  have hodd : ¬ 2 ∣ Nat.card ↥C := by
    intro h2C
    have h3 : (Nat.card ↥C).factorization 2 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2C).ne'
    have h4 : 2 ^ (Nat.card ↥C).factorization 2 = 1 := by
      rw [← Sylow.card_eq_multiplicity P, hP', Subgroup.card_bot]
    rcases Nat.pow_eq_one.mp h4 with h | h
    · norm_num at h
    · exact h3 h
  intro c hc
  obtain ⟨e, he⟩ := h2 c
  have hco : Nat.Coprime (2 ^ e) (orderOf (⟨c, hc⟩ : ↥C)) := by
    refine Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    exact fun h => hodd (h.trans (orderOf_dvd_natCard _))
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hco
  have hu' : (c ^ 2 ^ e) ^ u = c := by
    have := congrArg Subtype.val hu
    simpa using this
  rw [← hu']
  exact Y.pow_mem he u

end Cent

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_mem_modO2Image_iff {H K : Subgroup G} (hKH : K ≤ H) (h : ↥H) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) h ∈ modO2Image H K ↔
      (h : G) ∈ K ⊔ pCoreOf 2 H := by
  rw [← Vol2.Ch11.SecS.map_comap_modO2Image hKH]
  constructor
  · intro hh
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h', hh', hh'h⟩
    rw [show h = h' from Subtype.ext hh'h.symm]
    exact hh'

theorem mem_sup_pCoreOf_of_forall_comm {H K T : Subgroup G} (hKH : K ≤ H)
    (hKN : H ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 T) (hTK : T ⊔ K = H)
    {c : G} (hcH : c ∈ H) (hc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    c ∈ K ⊔ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hKb : (modO2Image H K).Normal := by
    have : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)
  have hO : CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ := pCore_two_quotient_pCore_two ↥H
  have hTKn : T ≤ Subgroup.normalizer (K : Set G) := (le_sup_left.trans hTK.le).trans hKN
  have h2 : ∀ a : ↥H ⧸ CFSG.pCore 2 ↥H, ∃ e : ℕ, a ^ 2 ^ e ∈ modO2Image H K := by
    intro a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) a
    have hh : (h : G) ∈ K ⊔ T := by
      rw [sup_comm, hTK]
      exact h.2
    obtain ⟨k, hk, t, ht, hkt⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTKn).mp hh
    obtain ⟨e, he⟩ := hT2 ⟨t, ht⟩
    have he' : t ^ 2 ^ e = 1 := congrArg Subtype.val he
    have hc : t⁻¹ * k * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTKn ht)) k).mp hk
      simpa using this
    obtain ⟨c', hc', hpow⟩ := exists_pow_mul_eq_pow_mul (hTKn ht) hc (2 ^ e)
    have hhe : (h : G) ^ 2 ^ e = c' := by
      rw [show (h : G) = t * (t⁻¹ * k * t) by rw [hkt]; group, hpow, he', one_mul]
    refine ⟨e, ⟨h ^ 2 ^ e, ?_, map_pow _ _ _⟩⟩
    show ((h ^ 2 ^ e : ↥H) : G) ∈ K
    rw [Subgroup.coe_pow, hhe]
    exact hc'
  have hOKH : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (A3.subnormal_of_normal hKH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN))
  have hcC : π ⟨c, hcH⟩ ∈ Subgroup.centralizer
      ((modO2Image H K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h1 : (k : G)⁻¹ * c * k * c⁻¹ ∈ pCoreOf 2 H := by
      have := hc _ (K.inv_mem hk')
      have h3 := hOKH (Subgroup.inv_mem _ this)
      simpa [mul_assoc] using h3
    have h4 : c⁻¹ * ((k : G)⁻¹ * c * k * c⁻¹) * c ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (H.inv_mem hcH)) _).mp h1
      simpa using this
    rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map] at h4
    obtain ⟨z, hz, hzc⟩ := h4
    have hz' : z = (k * ⟨c, hcH⟩)⁻¹ * (⟨c, hcH⟩ * k) := by
      apply Subtype.ext
      have hzc' : (z : G) = c⁻¹ * ((k : G)⁻¹ * c * k * c⁻¹) * c := hzc
      rw [hzc']
      simp [mul_assoc]
    rw [← hz']
    exact hz
  have h5 := centralizer_le_of_pCore_eq_bot hO h2 hcC
  exact (mk_mem_modO2Image_iff hKH ⟨c, hcH⟩).mp h5

end Bar

end CFSG.Quasithin.H13
