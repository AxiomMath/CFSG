module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPJ1
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217JPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelFixed
public import CFSG.CGT.PushingUpLit.SYMB.ProdCard
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2122np_card_le_eight_of_isPGroup_two_isJ1 {A : Type} [Group A] [Finite A]
    (hA : IsJ1 A) {P : Subgroup A} (hP : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  have hA2 : Nat.card A = 175560 := (kJ1_holds A hA).1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : Nat.card P ∣ 175560 := by
    rw [← hA2]
    exact Subgroup.card_subgroup_dvd_card P
  have hk3 : k ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ k := by omega
    have h16 : 16 ∣ 2 ^ k := by
      have h := Nat.pow_dvd_pow 2 h4
      norm_num at h ⊢
      exact h
    have : 16 ∣ 175560 := h16.trans (hk ▸ hdvd)
    norm_num at this
  calc Nat.card P = 2 ^ k := hk
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

theorem uc22s2122np_normalizer_prod_eq_of_isJ1 {A B : Type} [Group A] [Group B]
    {P₁ : Subgroup A} {P₂ : Subgroup B} :
    Subgroup.normalizer ((P₁.prod P₂ : Subgroup (A × B)) : Set (A × B)) =
      (Subgroup.normalizer (P₁ : Set A)).prod (Subgroup.normalizer (P₂ : Set B)) := by
  suffices hgoal : Subgroup.normalizer ((P₁.prod P₂ : Subgroup (A × B)) : Set (A × B)) =
      (Subgroup.normalizer (P₁ : Set A)).prod (Subgroup.normalizer (P₂ : Set B)) from
    Classical.byContradiction (fun h => h hgoal)
  have hfst : Subgroup.map (MonoidHom.fst A B) (P₁.prod P₂) = P₁ := by
    ext a
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.1
    · intro ha
      exact ⟨(a, 1), ⟨ha, P₂.one_mem⟩, rfl⟩
  have hsnd : Subgroup.map (MonoidHom.snd A B) (P₁.prod P₂) = P₂ := by
    ext b
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.2
    · intro hb
      exact ⟨(1, b), ⟨P₁.one_mem, hb⟩, rfl⟩
  apply le_antisymm
  · intro n hn
    rw [Subgroup.mem_prod]
    constructor
    · have h := Subgroup.le_normalizer_map (H := P₁.prod P₂) (MonoidHom.fst A B)
        (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
      rwa [hfst] at h
    · have h := Subgroup.le_normalizer_map (H := P₁.prod P₂) (MonoidHom.snd A B)
        (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
      rwa [hsnd] at h
  · intro n hn
    rw [Subgroup.mem_prod] at hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [Subgroup.mem_prod] at hq ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp hn.1 q.1).mp hq.1,
        (Subgroup.mem_normalizer_iff.mp hn.2 q.2).mp hq.2⟩
    · intro hq
      rw [Subgroup.mem_prod] at hq ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp hn.1 q.1).mpr hq.1,
        (Subgroup.mem_normalizer_iff.mp hn.2 q.2).mpr hq.2⟩

theorem uc22s2122np_card_eq_eight_of_sixty_four_le {A B : Type} [Group A] [Group B]
    {P₁ : Subgroup A} {P₂ : Subgroup B} (hP₁le : Nat.card P₁ ≤ 8) (hP₂le : Nat.card P₂ ≤ 8)
    (h64 : 64 ≤ Nat.card P₁ * Nat.card P₂) :
    Nat.card P₁ = 8 ∧ Nat.card P₂ = 8 := by
  have hP₁eq : Nat.card P₁ = 8 := by
    rcases lt_or_eq_of_le hP₁le with hlt | heq
    · exfalso
      have hle' : Nat.card P₁ * Nat.card P₂ ≤ 7 * 8 :=
        Nat.mul_le_mul (by omega : Nat.card P₁ ≤ 7) (by omega : Nat.card P₂ ≤ 8)
      omega
    · exact heq
  have hP₂eq : Nat.card P₂ = 8 := by
    rcases lt_or_eq_of_le hP₂le with hlt | heq
    · exfalso
      have hle' : Nat.card P₁ * Nat.card P₂ ≤ 8 * 7 :=
        Nat.mul_le_mul (by omega : Nat.card P₁ ≤ 8) (by omega : Nat.card P₂ ≤ 7)
      omega
    · exact heq
  exact ⟨hP₁eq, hP₂eq⟩

theorem uc22s2122np_prod_eq_of_card_sixty_four {A B : Type} [Group A] [Group B] [Finite A]
    [Finite B] {Q : Subgroup (A × B)} (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q = 64)
    (hA : IsJ1 A) (hB : IsJ1 B) :
    Nat.card (Q.map (MonoidHom.fst A B)) = 8 ∧
      Nat.card (Q.map (MonoidHom.snd A B)) = 8 ∧
      Q = (Q.map (MonoidHom.fst A B)).prod (Q.map (MonoidHom.snd A B)) := by
  let P₁ : Subgroup A := Q.map (MonoidHom.fst A B)
  let P₂ : Subgroup B := Q.map (MonoidHom.snd A B)
  have hP₁ : IsPGroup 2 P₁ := hQ.map (MonoidHom.fst A B)
  have hP₂ : IsPGroup 2 P₂ := hQ.map (MonoidHom.snd A B)
  have hP₁le : Nat.card P₁ ≤ 8 := uc22s2122np_card_le_eight_of_isPGroup_two_isJ1 hA hP₁
  have hP₂le : Nat.card P₂ ≤ 8 := uc22s2122np_card_le_eight_of_isPGroup_two_isJ1 hB hP₂
  have hle : Q ≤ P₁.prod P₂ := by
    intro q hq
    rw [Subgroup.mem_prod]
    exact ⟨Subgroup.mem_map.mpr ⟨q, hq, rfl⟩, Subgroup.mem_map.mpr ⟨q, hq, rfl⟩⟩
  have hprod : Nat.card (P₁.prod P₂) = Nat.card P₁ * Nat.card P₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv P₁ P₂).toEquiv, Nat.card_prod]
  have hQle : Nat.card Q ≤ Nat.card (P₁.prod P₂) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
  have h64 : 64 ≤ Nat.card P₁ * Nat.card P₂ := by
    calc 64 = Nat.card Q := hQcard.symm
      _ ≤ Nat.card (P₁.prod P₂) := hQle
      _ = Nat.card P₁ * Nat.card P₂ := hprod
  obtain ⟨hP₁eq, hP₂eq⟩ :=
    uc22s2122np_card_eq_eight_of_sixty_four_le hP₁le hP₂le h64
  have hQeq : Q = P₁.prod P₂ := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hprod, hP₁eq, hP₂eq, hQcard]
  exact ⟨hP₁eq, hP₂eq, hQeq⟩

theorem uc22s2122np_card_normalizer_prod_of_isJ1 {A B : Type} [Group A] [Group B]
    [Finite A] [Finite B]
    {Q : Subgroup (A × B)} (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q = 64)
    (hA : IsJ1 A) (hB : IsJ1 B) :
    Nat.card (Subgroup.normalizer (Q : Set (A × B))) = 168 * 168 := by
  suffices hgoal : Nat.card (Subgroup.normalizer (Q : Set (A × B))) = 168 * 168 from
    Classical.byContradiction (fun h => h hgoal)
  let P₁ : Subgroup A := Q.map (MonoidHom.fst A B)
  let P₂ : Subgroup B := Q.map (MonoidHom.snd A B)
  obtain ⟨hP₁eq, hP₂eq, hQeq⟩ := uc22s2122np_prod_eq_of_card_sixty_four hQ hQcard hA hB
  have hfactA : (Nat.card A).factorization 2 = 3 := by
    rw [(kJ1_holds A hA).1]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (p := 2) (n := 175560) (k := 3)
      Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
  have hfactB : (Nat.card B).factorization 2 = 3 := by
    rw [(kJ1_holds B hB).1]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (p := 2) (n := 175560) (k := 3)
      Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
  let S₁ : Sylow 2 A := Sylow.ofCard P₁ (by rw [hP₁eq, hfactA]; norm_num)
  let S₂ : Sylow 2 B := Sylow.ofCard P₂ (by rw [hP₂eq, hfactB]; norm_num)
  have hN₁ : Nat.card (Subgroup.normalizer (P₁ : Set A)) = 168 := by
    have h := (uc22s2122np_card_normalizer_sylow_of_isJ1 hA S₁).1
    rwa [Sylow.coe_ofCard] at h
  have hN₂ : Nat.card (Subgroup.normalizer (P₂ : Set B)) = 168 := by
    have h := (uc22s2122np_card_normalizer_sylow_of_isJ1 hB S₂).1
    rwa [Sylow.coe_ofCard] at h
  rw [hQeq, uc22s2122np_normalizer_prod_eq_of_isJ1]
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hN₁, hN₂]

theorem uc22s2122np_exists_mulEquiv_prod_of_isComplement {H : Type} [Group H]
    {A B : Subgroup H} (h : B.IsComplement' A)
    (hcomm : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) :
    ∃ Φ : H ≃* ↥B × ↥A, ∀ x, ((Φ x).1 : H) * ((Φ x).2 : H) = x := by
  let f : H →* ↥B × ↥A :=
    { toFun := fun x => ((h.equiv x).1, (h.equiv x).2)
      map_one' := by
        have h1 := h.equiv_one B.one_mem A.one_mem
        exact Prod.ext (congrArg Prod.fst h1) (congrArg Prod.snd h1)
      map_mul' := fun x y => by
        apply h.equiv.symm.injective
        rw [IsComplement.equiv_symm_apply, IsComplement.equiv_symm_apply]
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        rw [h.equiv_fst_mul_equiv_snd (x * y)]
        conv_lhs => rw [← h.equiv_fst_mul_equiv_snd x,
          ← h.equiv_fst_mul_equiv_snd y]
        have hc := hcomm ((h.equiv y).1 : H) (h.equiv y).1.2
          ((h.equiv x).2 : H) (h.equiv x).2.2
        calc ((h.equiv x).1 : H) * ((h.equiv x).2 : H)
              * (((h.equiv y).1 : H) * ((h.equiv y).2 : H))
            = ((h.equiv x).1 : H) * (((h.equiv x).2 : H) * ((h.equiv y).1 : H))
              * ((h.equiv y).2 : H) := by group
          _ = ((h.equiv x).1 : H) * (((h.equiv y).1 : H) * ((h.equiv x).2 : H))
              * ((h.equiv y).2 : H) := by rw [hc]
          _ = ((h.equiv x).1 : H) * ((h.equiv y).1 : H)
              * (((h.equiv x).2 : H) * ((h.equiv y).2 : H)) := by group }
  refine ⟨MulEquiv.ofBijective f ?_, fun x => ?_⟩
  · simpa [f] using h.equiv.bijective
  · simpa [f] using h.equiv_fst_mul_equiv_snd x

theorem uc22s2122np_card_barImage_of_isJ1 {M L : Subgroup G} (hL : L ∈ calC M)
    (hJ : IsJ1 (Bar2 L)) : Nat.card (barImage M L) = 175560 := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (L := M) (K := L) hL
  rw [← Nat.card_congr e.toEquiv]
  exact (kJ1_holds (Bar2 L) hJ).1

theorem uc22s2122np_isJ1_barImage {M L : Subgroup G} (hL : L ∈ calC M)
    (hJ : IsJ1 (Bar2 L)) : IsJ1 (barImage M L) := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (L := M) (K := L) hL
  obtain ⟨φ⟩ := hJ
  exact ⟨e.symm.trans φ⟩

theorem uc22s2122np_barImage_conjClosure_eq_sup {M L L' : Subgroup G}
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hK : conjClosure M L = L ⊔ L') :
    barImage M (conjClosure M L) = barImage M L ⊔ barImage M L' := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hL'M : L' ≤ M := CFSG.Quasithin.A3.subnormal_le hL'.1
  simp only [barImage, hK, Subgroup.subgroupOf_sup hLM hL'M, Subgroup.map_sup]

theorem uc22s2122np_barImage_conjClosure_normal {M L : Subgroup G} (hL : L ∈ calC M) :
    (barImage M (conjClosure M L)).Normal := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hclM : conjClosure M L ≤ M :=
    uc22p22v_conjClosure_le (N := M) (E := L) (F := M) Subgroup.le_normalizer hLM
  have hnorm : M ≤ normalizer (conjClosure M L : Set G) :=
    uc22p22v_le_normalizer_conjClosure M L
  have hsub : ((conjClosure M L).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hclM).2 hnorm
  have hmap := hsub.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    (QuotientGroup.mk'_surjective _)
  simpa [barImage] using hmap

theorem uc22s2122np_card_barImage_conjClosure {M L L' : Subgroup G}
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure M L = L ⊔ L') :
    Nat.card (barImage M (conjClosure M L)) = 175560 * 175560 := by
  rw [uc22s2122np_barImage_conjClosure_eq_sup hL hL' hK]
  have hcomm := uc22p22l_barImage_commute hL hL' hne
  have hdisj : Disjoint (barImage M L) (barImage M L') :=
    disjoint_iff.mpr (uc22s217j_barImage_inf_eq_bot hL hL' hne
      (center_eq_bot_of_isJ1 hJ))
  have hnorm : barImage M L' ≤ normalizer (barImage M L : Set (Bar2 M)) :=
    CFSG.CGT.PushingUpLit.SYMB.le_normalizer_of_commute
      (fun b hb a ha => (hcomm a ha b hb).symm)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    uc22s2122np_card_barImage_of_isJ1 hL hJ,
    uc22s2122np_card_barImage_of_isJ1 hL' hJ']

theorem uc22s2122np_isSylowOf_barImage_T (D : Data G) :
    CFSG.ABGLocalTools.IsSylowOf 2 (barImage D.M D.T) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf D.M) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) D.M]
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr D.sylowM.le]
    exact D.sylowM
  have hmap := CFSG.RankThree.PartTwo.Sec12.IsSylowOf.map hT (uc22p21cPi D.M)
  simpa [barImage, Subgroup.map_top, MonoidHom.range_eq_top.mpr
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D.M))] using hmap

theorem uc22s2122np_isSylowOf_inf_barImage_T (D : Data G) {L L' : Subgroup G}
    (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M) (hK : conjClosure D.M L = L ⊔ L') :
    CFSG.ABGLocalTools.IsSylowOf 2
      (barImage D.M D.T ⊓ barImage D.M (conjClosure D.M L))
      (barImage D.M (conjClosure D.M L)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKbar : (barImage D.M (conjClosure D.M L)).Normal :=
    uc22s2122np_barImage_conjClosure_normal hL
  have hnorm : (⊤ : Subgroup (Bar2 D.M)) ≤
      normalizer (barImage D.M (conjClosure D.M L) : Set (Bar2 D.M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := barImage D.M (conjClosure D.M L)) (K := (⊤ : Subgroup (Bar2 D.M)))
      le_top).mp (Subgroup.Normal.subgroupOf hKbar (⊤ : Subgroup (Bar2 D.M)))
  exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
    (uc22s2122np_isSylowOf_barImage_T D) le_top hnorm

theorem uc22s2122np_card_inf_barImage_T (D : Data G) {L L' : Subgroup G}
    (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M) (hne : L ≠ L')
    (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') :
    Nat.card ↥(barImage D.M D.T ⊓ barImage D.M (conjClosure D.M L)) = 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := uc22s2122np_isSylowOf_inf_barImage_T D hL hL' hK
  have hcardK := uc22s2122np_card_barImage_conjClosure hL hL' hne hJ hJ' hK
  have hfact : (Nat.card (barImage D.M (conjClosure D.M L))).factorization 2 = 6 := by
    rw [hcardK]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (p := 2) (n := 175560 * 175560)
      (k := 6) Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
  rw [hQ.card_eq, hfact]
  norm_num

theorem uc22s2122np_card_normalizer_subgroupOf_prod {H : Type} [Group H] [Finite H]
    {A B K : Subgroup H} (hK : K = A ⊔ B)
    (hcompl : (A.subgroupOf K).IsComplement' (B.subgroupOf K))
    (hcomm : ∀ b ∈ B.subgroupOf K, ∀ a ∈ A.subgroupOf K, b * a = a * b)
    (hA : IsJ1 A) (hB : IsJ1 B)
    {Q : Subgroup K} (hQp : IsPGroup 2 Q) (hQcard : Nat.card Q = 64) :
    Nat.card ↥(Subgroup.normalizer (Q : Set K)) = 168 * 168 := by
  have hAK : A ≤ K := by rw [hK]; exact le_sup_left
  have hBK : B ≤ K := by rw [hK]; exact le_sup_right
  obtain ⟨Φ, -⟩ := uc22s2122np_exists_mulEquiv_prod_of_isComplement
    (A := B.subgroupOf K) (B := A.subgroupOf K) hcompl
    (fun b hb a ha => (hcomm a ha b hb).symm)
  let Qm : Subgroup (↥(A.subgroupOf K) × ↥(B.subgroupOf K)) := Q.map Φ.toMonoidHom
  have hQmp : IsPGroup 2 Qm := hQp.map Φ.toMonoidHom
  have hQmcard : Nat.card Qm = 64 := by
    change Nat.card ↥(Q.map Φ.toMonoidHom) = 64
    rw [Subgroup.card_map_of_injective Φ.injective, hQcard]
  have hJB : IsJ1 ↥(B.subgroupOf K) := by
    obtain ⟨φ⟩ := hB
    exact ⟨(Subgroup.subgroupOfEquivOfLe hBK).trans φ⟩
  have hJA : IsJ1 ↥(A.subgroupOf K) := by
    obtain ⟨φ⟩ := hA
    exact ⟨(Subgroup.subgroupOfEquivOfLe hAK).trans φ⟩
  haveI : Finite ↥(A.subgroupOf K) := Subtype.finite
  haveI : Finite ↥(B.subgroupOf K) := Subtype.finite
  have hprod : Nat.card ↥(Subgroup.normalizer
      (Qm : Set (↥(A.subgroupOf K) × ↥(B.subgroupOf K)))) = 168 * 168 :=
    uc22s2122np_card_normalizer_prod_of_isJ1 hQmp hQmcard hJA hJB
  calc Nat.card ↥(Subgroup.normalizer (Q : Set K))
      = Nat.card ↥((Subgroup.normalizer (Q : Set K)).map Φ.toMonoidHom) :=
        (Subgroup.card_map_of_injective Φ.injective).symm
    _ = Nat.card ↥(Subgroup.normalizer (Qm : Set (↥(A.subgroupOf K) × ↥(B.subgroupOf K)))) := by
        rw [Subgroup.map_equiv_normalizer_eq Q Φ]
    _ = 168 * 168 := hprod

theorem uc22s2122np_sylow_seven_normal_of_card_dvd_441 {H : Type} [Group H] [Finite H]
    (hcard : Nat.card H ∣ 441) (P : Sylow 7 H) : (P : Subgroup H).Normal := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases hP1 : Nat.card P = 1
  · rw [Subgroup.eq_bot_of_card_eq (P : Subgroup H) hP1]
    infer_instance
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · rw [pow_zero] at hk; exact absurd hk hP1
      · exact h
    have h7dvdP : 7 ∣ Nat.card P := by
      rw [hk]; exact dvd_pow_self 7 (by omega)
    have hidx : (P : Subgroup H).index ∣ 63 := by
      obtain ⟨c, hc⟩ := h7dvdP
      have hdvd : Nat.card P * (P : Subgroup H).index ∣ 441 := by
        rw [Subgroup.card_mul_index (P : Subgroup H)]
        exact hcard
      rw [show (441 : ℕ) = 7 * 63 by norm_num, hc, mul_assoc] at hdvd
      have hc' : c * (P : Subgroup H).index ∣ 63 :=
        Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) hdvd
      exact (Dvd.intro_left c rfl).trans hc'
    have hn63 : Nat.card (Sylow 7 H) ∣ 63 := P.card_dvd_index.trans hidx
    obtain ⟨n, hn⟩ : ∃ n, n = Nat.card (Sylow 7 H) := ⟨_, rfl⟩
    have hnpos : 0 < n := by rw [hn]; exact Nat.card_pos
    have hnle : n ≤ 63 := by rw [hn]; exact Nat.le_of_dvd (by norm_num) hn63
    have hn63' : n ∣ 63 := by rwa [hn]
    have hmod : n ≡ 1 [MOD 7] := by rw [hn]; exact card_sylow_modEq_one 7 H
    interval_cases n <;> norm_num at hmod
    all_goals norm_num at hn63'
    have hn1 : Nat.card (Sylow 7 H) = 1 := by omega
    haveI : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.mp hn1).1
    exact P.normal_of_subsingleton

theorem uc22s2122np_isComplement_barImage_pair {M L L' : Subgroup G}
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure M L = L ⊔ L') :
    ((barImage M L).subgroupOf (barImage M (conjClosure M L))).IsComplement'
      ((barImage M L').subgroupOf (barImage M (conjClosure M L))) := by
  have hK_eq : barImage M (conjClosure M L) = barImage M L ⊔ barImage M L' :=
    uc22s2122np_barImage_conjClosure_eq_sup hL hL' hK
  have hAK : barImage M L ≤ barImage M (conjClosure M L) := by
    rw [hK_eq]; exact le_sup_left
  have hBK : barImage M L' ≤ barImage M (conjClosure M L) := by
    rw [hK_eq]; exact le_sup_right
  have hdisj : Disjoint (barImage M L) (barImage M L') :=
    disjoint_iff.mpr (uc22s217j_barImage_inf_eq_bot hL hL' hne
      (center_eq_bot_of_isJ1 hJ))
  have hnorm : barImage M L' ≤ normalizer (barImage M L : Set (Bar2 M)) :=
    CFSG.CGT.PushingUpLit.SYMB.le_normalizer_of_commute
      (fun b hb a ha => (uc22p22l_barImage_commute hL hL' hne a ha b hb).symm)
  have hcardAB : Nat.card (barImage M L) * Nat.card (barImage M L') =
      Nat.card (barImage M (conjClosure M L)) := by
    rw [hK_eq, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      _ _ hnorm hdisj]
  rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
  constructor
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hcardAB]
  · rw [disjoint_iff]
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      have hx : (x : Bar2 M) ∈ barImage M L ⊓ barImage M L' :=
        ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_subgroupOf.mp hxB⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at hx
      exact Subtype.ext hx
    · rintro rfl
      exact ⟨(barImage M L).one_mem, (barImage M L').one_mem⟩

theorem uc22s2122np_card_normalizer_inf_barImage_T {D : Data G} {L L' : Subgroup G}
    (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M) (hne : L ≠ L')
    (hJ : IsJ1 (Bar2 L)) (hJ' : IsJ1 (Bar2 L'))
    (hK : conjClosure D.M L = L ⊔ L') :
    Nat.card ↥(Subgroup.normalizer
      (((barImage D.M D.T ⊓ barImage D.M (conjClosure D.M L)).subgroupOf
        (barImage D.M (conjClosure D.M L))) :
          Set (barImage D.M (conjClosure D.M L)))) = 168 * 168 := by
  let A := barImage D.M L
  let B := barImage D.M L'
  let K := barImage D.M (conjClosure D.M L)
  let Qbar := barImage D.M D.T ⊓ K
  let Q : Subgroup K := Qbar.subgroupOf K
  have hK_eq : K = A ⊔ B :=
    uc22s2122np_barImage_conjClosure_eq_sup hL hL' hK
  have hcompl : (A.subgroupOf K).IsComplement' (B.subgroupOf K) :=
    uc22s2122np_isComplement_barImage_pair hL hL' hne hJ hJ' hK
  have hcomm : ∀ b ∈ B.subgroupOf K, ∀ a ∈ A.subgroupOf K, b * a = a * b := by
    intro b hb a ha
    apply Subtype.ext
    exact (uc22p22l_barImage_commute hL hL' hne (a : Bar2 D.M)
      (Subgroup.mem_subgroupOf.mp ha) (b : Bar2 D.M)
      (Subgroup.mem_subgroupOf.mp hb)).symm
  have hA : IsJ1 A := uc22s2122np_isJ1_barImage hL hJ
  have hB : IsJ1 B := uc22s2122np_isJ1_barImage hL' hJ'
  have hQp : IsPGroup 2 Q :=
    (uc22s2122np_isSylowOf_inf_barImage_T D hL hL' hK).isPGroup.comap_subtype
  have hQcard : Nat.card Q = 64 := by
    rw [show Nat.card Q = Nat.card Qbar from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Qbar ≤ K)).toEquiv]
    exact uc22s2122np_card_inf_barImage_T D hL hL' hne hJ hJ' hK
  have hmain := uc22s2122np_card_normalizer_subgroupOf_prod hK_eq hcompl hcomm hA hB hQp hQcard
  simpa only [Q, Qbar, K, A, B] using hmain

theorem uc22s2122np_card_comap_quotient {N : Type} [Group N] [Finite N]
    {QN : Subgroup N} [QN.Normal] (P : Subgroup (N ⧸ QN)) :
    Nat.card ↥(Subgroup.comap (QuotientGroup.mk' QN) P) = Nat.card P * Nat.card QN := by
  calc Nat.card ↥(Subgroup.comap (QuotientGroup.mk' QN) P)
      = Nat.card ↥(QuotientGroup.mk ⁻¹' (P : Set (N ⧸ QN))) := rfl
    _ = Nat.card (↥QN × ↥P) :=
        Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet QN (P : Set (N ⧸ QN)))
    _ = Nat.card QN * Nat.card P := Nat.card_prod _ _
    _ = Nat.card P * Nat.card QN := Nat.mul_comm _ _

theorem uc22s2122np_mem_comap_of_pow_seven {N : Type} [Group N] [Finite N]
    {QN : Subgroup N} [QN.Normal] (P : Sylow 7 (N ⧸ QN))
    (hPnorm : (P : Subgroup (N ⧸ QN)).Normal) {x : N} (hx : x ^ 7 = 1) :
    x ∈ Subgroup.comap (QuotientGroup.mk' QN) (P : Subgroup (N ⧸ QN)) := by
  rw [Subgroup.mem_comap]
  have hy : (QuotientGroup.mk' QN x) ^ 7 = 1 := by rw [← map_pow, hx, map_one]
  have hdvd : orderOf (QuotientGroup.mk' QN x) ∣ 7 := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (p := 7) (m := 1)
    (i := orderOf ((QuotientGroup.mk' QN) x)) Nat.prime_seven).1 (by simpa using hdvd)
  have hP : IsPGroup 7 (Subgroup.zpowers (QuotientGroup.mk' QN x)) :=
    IsPGroup.of_card (p := 7) (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q', hQ'⟩ := hP.exists_le_sylow
  haveI : Unique (Sylow 7 (N ⧸ QN)) := Sylow.unique_of_normal P hPnorm
  have hQeq : Q' = P := Subsingleton.elim _ _
  rw [← hQeq]
  exact hQ' (Subgroup.mem_zpowers _)

theorem uc22s2122np_card_sylow_seven_of_card_441 {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 441) (P : Sylow 7 H) : Nat.card P = 49 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h441 : (441 : ℕ).factorization 7 = 2 :=
    CFSG.GroupTheory.factorization_eq_of_pow_dvd Nat.prime_seven (by norm_num)
      (by norm_num) (by norm_num)
  rw [Sylow.card_eq_multiplicity, hH, h441]
  norm_num

theorem uc22s2122np_factorization_seven_card_J1 :
    (175560 : ℕ).factorization 7 = 1 :=
  CFSG.GroupTheory.factorization_eq_of_pow_dvd (p := 7) (n := 175560) (k := 1)
    Nat.prime_seven (by norm_num) (by norm_num) (by norm_num)

theorem uc22s2122np_factorization_seven_card_J1_sq :
    (175560 * 175560 : ℕ).factorization 7 = 2 :=
  CFSG.GroupTheory.factorization_eq_of_pow_dvd (p := 7) (n := 175560 * 175560) (k := 2)
    Nat.prime_seven (by norm_num) (by norm_num) (by norm_num)

theorem uc22s2122np_factorization_seven_card_thirtyone_thirtysix :
    (3136 : ℕ).factorization 7 = 2 :=
  CFSG.GroupTheory.factorization_eq_of_pow_dvd (p := 7) (n := 3136) (k := 2)
    Nat.prime_seven (by norm_num) (by norm_num) (by norm_num)

theorem uc22s2122np_isPGroup_zpowers_of_pow_seven {B : Type} [Group B] {b : B}
    (hb : b ^ 7 = 1) : IsPGroup 7 (Subgroup.zpowers b : Subgroup B) := by
  have hdvd : orderOf b ∣ 7 := orderOf_dvd_of_pow_eq_one hb
  have hcard : Nat.card (Subgroup.zpowers b) ∣ 7 := by rwa [Nat.card_zpowers]
  rcases (Nat.dvd_prime Nat.prime_seven).1 hcard with h | h
  · exact IsPGroup.of_card (p := 7) (n := 0) (by rw [h, pow_zero])
  · exact IsPGroup.of_card (p := 7) (n := 1) (by rw [h, pow_one])

theorem uc22s2122np_mem_normalizer_inf {B : Type} [Group B] {A K : Subgroup B} {g : B}
    (hA : g ∈ Subgroup.normalizer A) (hK : g ∈ Subgroup.normalizer K) :
    g ∈ Subgroup.normalizer (A ⊓ K : Subgroup B) := by
  by_contra hgoal
  apply hgoal
  rw [Subgroup.mem_normalizer_iff] at hA hK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(hA x).mp h.1, (hK x).mp h.2⟩,
    fun h => ⟨(hA x).mpr h.1, (hK x).mpr h.2⟩⟩

theorem uc22s2122np_normalizer_le_normalizer_normalizer {B : Type} [Group B]
    {H : Subgroup B} :
    Subgroup.normalizer (H : Set B) ≤
      Subgroup.normalizer (Subgroup.normalizer (H : Set B) : Set B) := by
  by_contra hgoal
  apply hgoal
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  change Subgroup.map (MulAut.conj g).toMonoidHom H = H at hg
  change Subgroup.map (MulAut.conj g).toMonoidHom
    (Subgroup.normalizer (H : Set B)) = Subgroup.normalizer (H : Set B)
  rw [Subgroup.map_equiv_normalizer_eq (H := H) (MulAut.conj g), hg]

theorem uc22s2122np_map_normalizerMonoidHom_subgroupOf_eq {B : Type} [Group B]
    {Q N : Subgroup B} (hQN : Q ≤ N) {t : B}
    (htN : t ∈ Subgroup.normalizer N) (htQ : t ∈ Subgroup.normalizer Q) :
    Subgroup.map (Subgroup.normalizerMonoidHom N ⟨t, htN⟩).toMonoidHom (Q.subgroupOf N) =
      Q.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_map]
  have hcomp : N.subtype.comp (Subgroup.normalizerMonoidHom N ⟨t, htN⟩).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp N.subtype := by
    ext x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe N ⟨t, htN⟩ x
  have htQmap : Subgroup.map (MulAut.conj t).toMonoidHom Q = Q :=
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp htQ)
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hQN, htQmap]

theorem uc22s2122np_map_comap_of_sylow_normal {N : Type} [Group N] [Finite N]
    {Q : Subgroup N} [Q.Normal] (P : Sylow 7 (N ⧸ Q))
    (hPnorm : (P : Subgroup (N ⧸ Q)).Normal) (ψ : MulAut N)
    (hQinv : Subgroup.map ψ.toMonoidHom Q = Q) :
    Subgroup.map ψ.toMonoidHom
        (Subgroup.comap (QuotientGroup.mk' Q) (P : Subgroup (N ⧸ Q))) =
      Subgroup.comap (QuotientGroup.mk' Q) (P : Subgroup (N ⧸ Q)) := by
  haveI : Finite (Sylow 7 (N ⧸ Q)) := inferInstance
  have hPchar : (P : Subgroup (N ⧸ Q)).Characteristic :=
    Sylow.characteristic_of_normal P hPnorm
  let φ : MulAut (N ⧸ Q) := CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism
    ψ Q hQinv
  have hfix : Subgroup.comap φ.toMonoidHom (P : Subgroup (N ⧸ Q)) = P :=
    (Subgroup.characteristic_iff_comap_eq.mp hPchar) φ
  have h1 : ∀ x : N, (QuotientGroup.mk' Q) (ψ x) = φ ((QuotientGroup.mk' Q) x) := by
    intro x
    rw [CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply]
  apply Subgroup.eq_of_le_of_card_ge
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_comap] at hx ⊢
    change (QuotientGroup.mk' Q) (ψ x) ∈ (P : Subgroup (N ⧸ Q))
    rw [h1]
    have hy' : (QuotientGroup.mk' Q) x ∈
        Subgroup.comap φ.toMonoidHom (P : Subgroup (N ⧸ Q)) := by
      rwa [hfix]
    exact (Subgroup.mem_comap (f := φ.toMonoidHom)).mp hy'
  · rw [Subgroup.card_map_of_injective ψ.injective]

theorem uc22s2122np_exists_mul_of_isComplement {H : Type} [Group H] {A B K : Subgroup H}
    (h : (A.subgroupOf K).IsComplement' (B.subgroupOf K)) :
    ∀ k ∈ K, ∃ a ∈ A, ∃ b ∈ B, k = a * b := by
  intro k hk
  let k' : K := ⟨k, hk⟩
  refine ⟨((h.equiv k').1 : K), ?_, ((h.equiv k').2 : K), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp (h.equiv k').1.2
  · exact Subgroup.mem_subgroupOf.mp (h.equiv k').2.2
  · exact (congrArg Subtype.val (h.equiv_fst_mul_equiv_snd k')).symm

theorem uc22s2122np_exists_sylow_preimage {N : Type} [Group N] [Finite N]
    {Q : Subgroup N} [Q.Normal] (hNcard : Nat.card N = 168 * 168)
    (hQcard : Nat.card Q = 64) :
    ∃ (P : Sylow 7 (N ⧸ Q)) (R : Subgroup N),
      (P : Subgroup (N ⧸ Q)).Normal ∧ Nat.card P = 49 ∧ Nat.card R = 49 * 64 ∧
      R = Subgroup.comap (QuotientGroup.mk' Q) (P : Subgroup (N ⧸ Q)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hindex : Q.index = 441 := by
    have h := Subgroup.card_mul_index Q
    rw [hQcard, hNcard] at h
    omega
  have hquot : Nat.card (N ⧸ Q) = 441 := by
    rw [← Subgroup.index_eq_card]
    exact hindex
  let P : Sylow 7 (N ⧸ Q) := Classical.arbitrary _
  have hPcard : Nat.card P = 49 :=
    uc22s2122np_card_sylow_seven_of_card_441 hquot P
  have hPnormal : (P : Subgroup (N ⧸ Q)).Normal :=
    uc22s2122np_sylow_seven_normal_of_card_dvd_441 (by rw [hquot]) P
  refine ⟨P, Subgroup.comap (QuotientGroup.mk' Q) (P : Subgroup (N ⧸ Q)),
    hPnormal, hPcard, ?_, rfl⟩
  rw [uc22s2122np_card_comap_quotient (QN := Q) (P := P), hPcard, hQcard]

end CFSG.LocalAnalysis.UniquenessCase.UC22
