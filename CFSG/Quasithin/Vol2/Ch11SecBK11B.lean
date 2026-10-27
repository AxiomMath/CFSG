module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.BK11

open CFSG.Open CFSG.QuasithinUnique

variable {S : Type} [Group S] {B : Subgroup S}

theorem eq_of_pow_two_modEq {n m : ℕ} (hn : n ≤ 3) (hm : m ≤ n) (h : 2 ^ m ≡ 2 ^ n [MOD 5]) :
    m = n := by
  unfold Nat.ModEq at h
  interval_cases n <;> interval_cases m <;> first | rfl | (norm_num at h)

theorem commute_of_pow_five [Finite S] {x : ↥B} (hx : x ^ 5 = 1)
    (hO8 : Nat.card (CFSG.pCore 2 ↥B) ≤ 8) (o : ↥B) (ho : o ∈ CFSG.pCore 2 ↥B) :
    x * o = o * x := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥B with hO
  let f : ↥(Subgroup.zpowers x) →* MulAut ↥O :=
    (MulAut.conjNormal).comp (Subgroup.zpowers x).subtype
  let _ : MulAction ↥(Subgroup.zpowers x) ↥O := MulAction.compHom ↥O f
  have hsmul : ∀ (g : ↥(Subgroup.zpowers x)) (o' : ↥O),
      ((g • o' : ↥O) : ↥B) = (g : ↥B) * o' * (g : ↥B)⁻¹ := fun g o' =>
    MulAut.conjNormal_apply (g : ↥B) o'
  have h5 : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hmod := h5.card_modEq_card_fixedPoints ↥O
  let F : Subgroup ↥O := (Subgroup.centralizer ({x} : Set ↥B)).comap O.subtype
  have hF : MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥O = (F : Set ↥O) := by
    ext o'
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, F, Subgroup.mem_comap,
      Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg Subtype.val (h ⟨x, Subgroup.mem_zpowers x⟩)
      rw [hsmul] at h1
      calc (o' : ↥B) * x = x * o' * x⁻¹ * x := by rw [h1]
        _ = x * o' := by group
    · rintro h ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      apply Subtype.ext
      rw [hsmul]
      have hc : Commute x (o' : ↥B) := h.symm
      change x ^ k * (o' : ↥B) * (x ^ k)⁻¹ = o'
      rw [(hc.zpow_left k).eq, mul_inv_cancel_right]
  have hcF : Nat.card ↑(MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥O) = Nat.card F := by
    rw [hF]
    rfl
  rw [hcF] at hmod
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
  rw [← hO] at hn
  have hdvd : Nat.card F ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card F
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hn3 : n ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hFO : Nat.card F = Nat.card ↥O := by
    rw [hn, hmeq]
    rw [hn, hmeq] at hmod
    rw [eq_of_pow_two_modEq hn3 hm hmod.symm]
  have hFtop : F = ⊤ := (Subgroup.card_eq_iff_eq_top F).mp hFO
  have hoF : (⟨o, ho⟩ : ↥O) ∈ F := hFtop ▸ Subgroup.mem_top _
  exact (Subgroup.mem_centralizer_singleton_iff.mp hoF).symm

theorem card_quot {F : Type} [Field F] [Finite F] (hF4 : Nat.card F = 4)
    (eF : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60 := by
  rw [Nat.card_congr eF.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF4]
  norm_num

theorem nonempty_quot_equiv_a5 {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F = 4)
    (eF : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5)) := by
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2) Nat.prime_two (by norm_num) (by rw [hF4]; norm_num)
  obtain ⟨eA⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inl hF4)
  exact ⟨(eF.trans Vol2Native.A312L.sl2EquivStatedProj).trans eA⟩

theorem isSimpleGroup_quot {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F = 4)
    (eF : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B) := by
  obtain ⟨e⟩ := nonempty_quot_equiv_a5 hF4 eF
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact MulEquiv.isSimpleGroup e

theorem exists_pow_five [Finite S] (h60 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60) :
    ∃ x : ↥B, x ^ 5 = 1 ∧ x ∉ CFSG.pCore 2 ↥B := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [h60]; norm_num)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hy5 : y ^ 5 ∈ CFSG.pCore 2 ↥B := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) ⟨_, hy5⟩
  refine ⟨y ^ 2 ^ m, ?_, fun h => ?_⟩
  · have h1 := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
    rw [← pow_mul, mul_comm, pow_mul, h1]
  · have h1 : ((y : ↥B ⧸ CFSG.pCore 2 ↥B)) ^ 2 ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hq] at h2
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h2))
    omega

theorem commute_pCore [Finite S] (hB : ⁅B, B⁆ = B)
    {F : Type} [Field F] [Finite F] (hF4 : Nat.card F = 4)
    (eF : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hO8 : Nat.card (CFSG.pCore 2 ↥B) ≤ 8) :
    ∀ o ∈ CFSG.pCore 2 ↥B, ∀ y : ↥B, o * y = y * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp := isSimpleGroup_quot hF4 eF
  have h60 := card_quot hF4 eF
  have hBperf : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hB
  set O := CFSG.pCore 2 ↥B with hO
  set Kc : Subgroup ↥B := Subgroup.centralizer (O : Set ↥B) with hKc
  have hmap : Kc.map (QuotientGroup.mk' O) = ⊤ := by
    have : (Kc.map (QuotientGroup.mk' O)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Kc.map (QuotientGroup.mk' O)) with h | h
    · exfalso
      obtain ⟨x, hx5, hxO⟩ := exists_pow_five h60
      have hxK : x ∈ Kc := Subgroup.mem_centralizer_iff.mpr fun o ho =>
        (commute_of_pow_five hx5 hO8 o ho).symm
      have h1 : QuotientGroup.mk' O x ∈ Kc.map (QuotientGroup.mk' O) :=
        Subgroup.mem_map_of_mem _ hxK
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hxO h1
    · exact h
  have hsup : Kc ⊔ O = ⊤ := by
    rw [← QuotientGroup.ker_mk' O, ← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have hKtop : Kc = ⊤ := by
    by_contra hne
    have : Nontrivial (↥B ⧸ Kc) := QuotientGroup.nontrivial_iff.mpr hne
    have : Group.IsPerfect (↥B ⧸ Kc) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Kc) (QuotientGroup.mk'_surjective _)
    have hOmap : O.map (QuotientGroup.mk' Kc) = ⊤ := by
      have h1 : (O.map (QuotientGroup.mk' Kc)).comap (QuotientGroup.mk' Kc) = ⊤ := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm, hsup]
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Kc)
        (O.map (QuotientGroup.mk' Kc)), h1, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Kc)]
    have h2 : IsPGroup 2 (↥B ⧸ Kc) := by
      intro q
      have hq : q ∈ O.map (QuotientGroup.mk' Kc) := hOmap ▸ Subgroup.mem_top q
      obtain ⟨o, ho, rfl⟩ := hq
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) ⟨o, ho⟩
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have h3 : o ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [h3, map_one]
    have := h2.isNilpotent
    exact Group.IsPerfect.not_isSolvable (↥B ⧸ Kc) inferInstance
  intro o ho y
  have hyK : y ∈ Kc := hKtop ▸ Subgroup.mem_top y
  exact Subgroup.mem_centralizer_iff.mp hyK o ho

end CFSG.Quasithin.Vol2.Ch11.SecA.BK11
