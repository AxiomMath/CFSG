module

public import CFSG.Quasithin.Vol2.Ch9Prop927

public section

namespace CFSG.Quasithin.H13.Ch9

namespace KStar

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecB CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

variable {G : Type} [Group G] [Finite G]

theorem le_of_isSylowTwoOf_of_le {Y : Type*} [Group Y] [Finite Y] {K S P : Subgroup Y}
    (hS : IsSylowTwoOf S K) (hP : IsPGroup 2 P) (hSP : S ≤ P) (hPK : P ≤ K) : P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_relIndex S P K hSP hPK
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have h2 : S.relIndex P ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card S P
  have h3 : ¬ 2 ∣ S.relIndex K := hS.2.2
  have h4 : S.relIndex P = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply h3
      rw [← h1, hj, pow_succ]
      exact dvd_mul_of_dvd_left (dvd_mul_left 2 _) _
  exact Subgroup.relIndex_eq_one.mp h4

theorem le_normalizer_inf_of_isBorelIn {H T X K B : Subgroup G} (hXH : X ≤ H) (hTX : T ≤ X)
    (hT : IsSylowTwoOf T H) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn X H))
    (hBor : E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K))) (hBX : B ≤ X ⊓ K) :
    B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSeq⟩ := hBor
  set φ := QuotientGroup.mk' ((kerIn X H).subgroupOf H) with hφ
  have hTK : IsSylowTwoOf (T ⊓ K) K := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hT hKH hHK
  have hTKS : E2.star X H (T ⊓ K) ≤ S := by
    refine le_of_isPGroup_of_le_normalizer hS ?_ (star_mono inf_le_right) ?_
    · exact ((hTK.2.1.comap_of_injective H.subtype H.subtype_injective).map φ)
    · refine (star_mono (inf_le_inf_right K hTX)).trans ?_
      rw [hSeq]
      exact inf_le_right
  set Sh : Subgroup G := (S.comap φ).map H.subtype ⊓ K with hSh
  have hSh2 : IsPGroup 2 Sh := by
    rintro ⟨x, ⟨h, hhS, rfl⟩, hxK⟩
    obtain ⟨a, ha⟩ := hS.2.1 ⟨φ h, hhS⟩
    have ha' : φ (h ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have hker : ((h : G) ^ 2 ^ a) ∈ kerIn X H := by
      have h3 : h ^ 2 ^ a ∈ (kerIn X H).subgroupOf H := by
        rw [← QuotientGroup.ker_mk' ((kerIn X H).subgroupOf H)]
        exact ha'
      rw [Subgroup.mem_subgroupOf] at h3
      simpa using h3
    obtain ⟨c, hc⟩ := hJ ⟨_, hker⟩
    refine ⟨a + c, Subtype.ext ?_⟩
    have hc' : ((h : G) ^ 2 ^ a) ^ 2 ^ c = 1 := by
      simpa using congrArg Subtype.val hc
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_subtype]
    rw [pow_add, pow_mul, hc']
  have hTKSh : T ⊓ K ≤ Sh := by
    intro t ht
    refine ⟨⟨⟨t, hKH ht.2⟩, ?_, rfl⟩, ht.2⟩
    exact hTKS ⟨⟨t, hKH ht.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hShTK : Sh ≤ T ⊓ K := le_of_isSylowTwoOf_of_le hTK hSh2 hTKSh inf_le_right
  intro b hb
  have hbH : b ∈ H := hXH (hBX hb).1
  have hbN : φ ⟨b, hbH⟩ ∈ Subgroup.normalizer (S : Set (E2.StarQuot X H)) := by
    have h1 : φ ⟨b, hbH⟩ ∈ E2.star X H (X ⊓ K) :=
      ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr (hBX hb), rfl⟩
    rw [hSeq] at h1
    exact h1.2
  have hconj : ∀ t ∈ T ⊓ K, b * t * b⁻¹ ∈ T ⊓ K := by
    intro t ht
    have htH : t ∈ H := hKH ht.2
    have hbt : φ (⟨b, hbH⟩ * ⟨t, htH⟩ * ⟨b, hbH⟩⁻¹) ∈ S := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hbN _).mp
        (hTKS ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩)
    have hbK : b * t * b⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHK hbH) t).mp ht.2
    exact hShTK ⟨⟨_, hbt, rfl⟩, hbK⟩
  have hle : (T ⊓ K).map (MulAut.conj b).toMonoidHom ≤ T ⊓ K := by
    rintro _ ⟨t, ht, rfl⟩
    show (MulAut.conj b) t ∈ T ⊓ K
    rw [MulAut.conj_apply]
    exact hconj t ht
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj b).injective).ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

omit [Finite G] in
theorem nonempty_modO2_equiv_alt_five {H X K : Subgroup G}
    (hKH : K ≤ H) (hJ : IsPGroup 2 (kerIn X H)) (hK : IsPSL 2 2 2 ↥(E2.star X H K)) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inl (by rw [hF]; norm_num))
  set φ := QuotientGroup.mk' ((kerIn X H).subgroupOf H) with hφ
  let ρ : ↥K →* ↥(E2.star X H K) :=
    (φ.comp (Subgroup.inclusion hKH)).codRestrict (E2.star X H K)
      (fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
  let g : ↥K →* alternatingGroup (Fin 5) := (e.trans e5).toMonoidHom.comp ρ
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨⟨_, ⟨h, hh, rfl⟩⟩, hz⟩ := (e.trans e5).surjective y
    refine ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, ?_⟩
    rw [← hz]
    rfl
  have hker : IsPGroup 2 g.ker := by
    rintro ⟨k, hk⟩
    have h1 : ρ k = 1 := (e.trans e5).injective (by rw [map_one]; exact hk)
    have h2 : φ (Subgroup.inclusion hKH k) = 1 := congrArg Subtype.val h1
    have h3 : (k : G) ∈ kerIn X H := by
      have h4 : Subgroup.inclusion hKH k ∈ (kerIn X H).subgroupOf H := by
        rw [← QuotientGroup.ker_mk' ((kerIn X H).subgroupOf H)]
        exact h2
      exact Subgroup.mem_subgroupOf.mp h4
    obtain ⟨m, hm⟩ := hJ ⟨k, h3⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hm
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨Vol2Native.A312L.modO2EquivOfHom Vol2Native.A312L.Seven.alt5_nonabelian g hg hker⟩

end KStar

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem exists_comp_of_nParam_eq_two
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h122 : Vol2Native.Lemma122A) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3)
    (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) (h331 : Stmt3_3_1)
    (hF1 : FactBorelOddLarge) (hF2 : FactBenderCartanFrob) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn : E1.nParam H = 2) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      IsPGroup 2 (kerIn (H ⊓ fsuM T L) H) ∧
      (IsPSL 2 2 2 ↥(E2.star (H ⊓ fsuM T L) H K) ∨ IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) ∧
      ∀ B : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
        B ≤ K ∧ Nat.card B = 3 ∧ B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have hn2 := S.eq_two hE22 h4414 hC58 h317 h122 h37c h38c h37 h38 h39 h3228 hE610 h63 hH11 h1
    h331 hF1 hF2
  have hn1 : 1 < E1.nParam H := by rw [hn]; norm_num
  obtain ⟨hmin, hSQ, hns, hTXs⟩ := S.minParabolic_of_isHStar h331 hH hn1
  obtain ⟨B₀, hB₀⟩ := S.exists_hall hE22 h331 hH hn1
  have hcard : ∀ B : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
      Nat.card B = 2 ^ n - 1 := fun B hB =>
    (S.hall_eq_cartan hE22 h4414 hC58 h317 h331 h122 h37c h38c h37 h38 h39 h3228 hE610 h63 hH11
      h1 hH hn1 hB).2.2.1
  have hnH := S.le_nParam_add_one h37 h38 h39 h3228 hE610 h63 hH11 h1 hH
  obtain ⟨K, hKc, hHK, hTK, hJ, hBor, htype⟩ := KStar.exists_comp hE22 hF1 hmin hSQ hns
    inf_le_left hTXs.1 hTXs hn1 S.two_le hnH hB₀ (hcard B₀ hB₀)
  have hT2 : IsPGroup 2 T := hTXs.2.1
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hTH : IsSylowTwoOf T H :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hH.1.1
  refine ⟨K, hKc, hHK, hTK, hJ, ?_, fun B hB => ⟨?_, ?_, ?_⟩⟩
  · rw [hn2] at htype
    rcases htype with h | h | ⟨-, h⟩
    · exact Or.inl h
    · exact absurd h Vol2.Ch10.SecB.C11AmS.not_isSz_two
    · exact Or.inr h
  · exact Vol2.Ch10.SecB.C11AmS.le_of_odd (hB.1.trans inf_le_left) hB.2.1
      (B6.isTwoQuotient_of_sup_eq hT2 hHKn (by rw [hHK, sup_comm]))
  · rw [hcard B hB, hn2]
    norm_num
  · have hBK : B ≤ K := Vol2.Ch10.SecB.C11AmS.le_of_odd (hB.1.trans inf_le_left) hB.2.1
      (B6.isTwoQuotient_of_sup_eq hT2 hHKn (by rw [hHK, sup_comm]))
    exact KStar.le_normalizer_inf_of_isBorelIn inf_le_left hTXs.1 hTH (le_of_mem_cComp hKc)
      hHKn hJ hBor (le_inf hB.1 hBK)

end Setup

end CFSG.Quasithin.H13.Ch9
