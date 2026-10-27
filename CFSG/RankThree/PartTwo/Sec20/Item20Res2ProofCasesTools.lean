module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSL3
import CFSG.Quasithin.EmptyFaithful.SBc8Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2

variable {G : Type} [Group G] [Finite G]

theorem centralizer_of_transfer {K A P : Subgroup G} {Z : Set G}
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : IsPGroup 2 A) (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (hZA : ∀ z ∈ Z, ∀ a ∈ A, z * a * z⁻¹ = a) (hZP : ∀ z ∈ Z, ∀ p ∈ P, p * z * p⁻¹ * z⁻¹ = 1)
    (hZK : ∀ z ∈ Z, ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ A) {k : G} (hk : k ∈ K)
    (hfix : ∀ m ∈ A, (∀ p ∈ P, p * m * p⁻¹ = m) → k * m * k⁻¹ = m) :
    ∀ z ∈ Z, k * z * k⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ P.relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
  intro z hz
  obtain ⟨m, hmA, hmC⟩ := CFSG.Quasithin.SBc8.exists_mul_centralizer_of_cocycle hKA hAc hA2 hP.le
    hodd (hZA z hz) (hZK z hz) (hZP z hz)
  have hmP : ∀ p ∈ P, p * m * p⁻¹ = m := by
    intro p hp
    have h1 := hmC p (hP.le hp)
    have h2 : p * z * p⁻¹ = z := mul_inv_eq_one.mp (hZP z hz p hp)
    calc p * m * p⁻¹ = (p * (z * m⁻¹) * p⁻¹)⁻¹ * (p * z * p⁻¹) := by group
      _ = (z * m⁻¹)⁻¹ * z := by rw [h1, h2]
      _ = m := by group
  have hkm := hfix m hmA hmP
  calc k * z * k⁻¹ = (k * (z * m⁻¹) * k⁻¹) * (k * m * k⁻¹) := by group
    _ = z * m⁻¹ * m := by rw [hmC k hk, hkm]
    _ = z := by group

theorem exists_coords_fixed {K P : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hα : Function.Surjective α)
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ (x : Fin 3 → F),
      (∀ p : ↥K, (p : G) ∈ P → (α p : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) →
      ∀ k : ↥K, g⁻¹ * α k * g ∈ vstab F → (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_le_sylow (Q.mapSurjective hα)
  refine ⟨g, fun x hx k hk => ?_⟩
  have hU : ∀ u ∈ LinearFlag.unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
    intro u hu
    have h := hg u hu
    rw [Sylow.coe_mapSurjective, hQ] at h
    obtain ⟨p, hp, hpu⟩ := h
    have hfix := hx p (Subgroup.mem_subgroupOf.mp hp)
    have hu' : u = g⁻¹ * α p * g := by rw [hpu]; group
    rw [hu', Res2.mulVec_mul_mul, Res2.mulVec_inv_mulVec, hfix]
  obtain ⟨h1, h2⟩ := coords_eq_zero_of_unitriangular_fixed hU
  have hline := Res2.eq_smul_e0 h1 h2
  have hk' : ((g⁻¹ * α k * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Pi.single 0 1 = Pi.single 0 1 := hk
  have : ((g⁻¹ * α k * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
    rw [hline, mulVec_smul, hk']
  rw [Res2.mulVec_mul_mul, Res2.mulVec_inv_mulVec] at this
  calc (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ x
      = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ ((α k : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) :=
        (Res2.mulVec_inv_mulVec g _).symm
    _ = x := by rw [this, Res2.mulVec_inv_mulVec]

omit [Finite G] in
theorem omegaOneCenterOf_eq_zTwenty (T : Subgroup G) :
    CFSG.Quasithin.omegaOneCenterOf T = zTwenty T := by
  apply le_antisymm
  · rw [CFSG.Quasithin.omegaOneCenterOf, CFSG.Quasithin.omegaOneOf, Subgroup.closure_le]
    rintro z ⟨⟨hzT, hzc⟩, hz2⟩
    refine ⟨⟨z, hzT⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff]
    refine ⟨Subgroup.mem_center_iff.mpr fun t => Subtype.ext ?_, Subtype.ext (by simpa using hz2)⟩
    exact Subgroup.mem_centralizer_iff.mp hzc t t.2
  · intro z hz
    obtain ⟨hzT, hzc⟩ := mem_and_commute_of_mem_zTwenty hz
    have hz2 : z ^ 2 = 1 := by
      obtain ⟨w, hw, rfl⟩ := hz
      rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hw
      have := congrArg Subtype.val hw.2
      simpa using this
    exact Subgroup.subset_closure ⟨⟨hzT, Subgroup.mem_centralizer_iff.mpr fun t ht => hzc t ht⟩,
      hz2⟩

theorem sTwenty_eq_of_vstab {K T M N : Subgroup G}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) (hTN : T ≤ N)
    (h207 : K ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N) (hKN : ¬ K ≤ N)
    (hLQ : K ⊔ CFSG.Open.pCoreOf 2 (K ⊔ T) = K ⊔ T)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hK0 : ∀ k : ↥K, α k ∈ vstab F → (k : G) ∈ Subgroup.centralizer (zTwenty T : Set G)) :
    CFSG.Open.pCoreOf 2 ((K ⊔ T) ⊓ N) =
      CFSG.Open.pCoreOf 2 ((K ⊔ T) ⊓ Subgroup.centralizer (zTwenty T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := zTwenty T with hZ
  set KT := K ⊔ T with hKT
  set Q := CFSG.Open.pCoreOf 2 KT with hQ
  set S := CFSG.Open.pCoreOf 2 (KT ⊓ N) with hS
  set Y1 := KT ⊓ Subgroup.centralizer (Z : Set G) with hY1
  set R := CFSG.Open.pCoreOf 2 Y1 with hR
  have hTM : T ≤ M := hTsyl.le
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTM.trans hMK
  have hKTM : KT ≤ M := sup_le hKM hTM
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowOf (hTsyl.of_le le_sup_right hKTM)
  have hQN : Q ≤ N := hQT.trans hTN
  have hKTQ : KT ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 KT
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 KT
  have hTC : T ≤ Subgroup.centralizer (Z : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => ((mem_and_commute_of_mem_zTwenty hz).2 t ht).symm
  have hKKT : K ≤ KT := le_sup_left
  have hQKN : Q ≤ Subgroup.normalizer (K : Set G) := hQT.trans hTK
  have hKQ : ∀ x ∈ KT, ∃ k ∈ K, ∃ o ∈ Q, x = k * o := by
    intro x hx
    rw [← hLQ, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K Q hQKN] at hx
    obtain ⟨k, hk, o, ho, rfl⟩ := hx
    exact ⟨k, hk, o, ho, rfl⟩
  have hKTs : ∀ x ∈ KT, ∃ k ∈ K, ∃ t ∈ T, x = k * t := by
    intro x hx
    rw [hKT, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hx
    obtain ⟨k, hk, t, ht, rfl⟩ := hx
    exact ⟨k, hk, t, ht, rfl⟩
  have hQKO : ∀ x ∈ Q, x ∈ K → x ∈ CFSG.Open.pCoreOf 2 K := by
    intro x hxQ hxK
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_right : Q ⊓ K ≤ K)
      (fun k hk => mem_normalizer_inf_of_mem (hKTQ (hKKT hk)) (Subgroup.le_normalizer hk))
      (hQ2.to_le inf_le_left) ⟨hxQ, hxK⟩
  have hOKN : CFSG.Open.pCoreOf 2 K ≤ N := by
    refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKKT) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans hQN
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hαeq : ∀ k k' : ↥K, α k = α k' → (k' : G)⁻¹ * k ∈ CFSG.Open.pCoreOf 2 K := by
    intro k k' h
    have := (hαk (k'⁻¹ * k)).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
    simpa using this
  have hY1Y2 : Y1 ≤ KT ⊓ N := by
    rintro y ⟨hyKT, hyC⟩
    refine ⟨hyKT, ?_⟩
    obtain ⟨k, hk, t, ht, rfl⟩ := hKTs y hyKT
    have hkC : k ∈ Subgroup.centralizer (Z : Set G) := by
      have : k = (k * t) * t⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hyC (Subgroup.inv_mem _ (hTC ht))
    exact N.mul_mem (h207 ⟨hk, hkC⟩) (hTN ht)
  set IKN := ((K ⊓ N).subgroupOf K).map α with hIKN
  have hvI : vstab F ≤ IKN := by
    intro h hh
    obtain ⟨k, rfl⟩ := hαs h
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, h207 ⟨k.2, hK0 k hh⟩⟩, rfl⟩
  have hIl : IKN ≤ lstab F := by
    by_contra hnot
    apply hKN
    have htop := eq_top_of_vstab_le hvI hnot
    intro k hk
    have hmem : α ⟨k, hk⟩ ∈ IKN := htop ▸ Subgroup.mem_top _
    obtain ⟨k', hk', hkk'⟩ := hmem
    have h1 := hαeq ⟨k, hk⟩ k' hkk'.symm
    have : k = k' * ((k' : G)⁻¹ * k) := by group
    rw [this]
    exact N.mul_mem (Subgroup.mem_subgroupOf.mp hk').2 (hOKN h1)
  set Ku : Subgroup G := ((urad F).comap α).map K.subtype with hKu
  have hmemKu : ∀ x (hx : x ∈ K), x ∈ Ku ↔ α ⟨x, hx⟩ ∈ urad F := by
    intro x hx
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hKuK : Ku ≤ K := Subgroup.map_subtype_le _
  have hKuN : Ku ≤ N := by
    rintro _ ⟨k, hk, rfl⟩
    exact h207 ⟨k.2, hK0 k (urad_le_vstab hk)⟩
  have hKu2 : IsPGroup 2 Ku := by
    rintro ⟨x, hx⟩
    have hxK := hKuK hx
    have hxu := (hmemKu x hxK).mp hx
    have hsq : α (⟨x, hxK⟩ ^ 2) = 1 := by
      rw [map_pow]
      exact sq_eq_one_of_mem_urad hxu
    have hx2 : x ^ 2 ∈ CFSG.Open.pCoreOf 2 K := by
      have := (hαk _).mp hsq
      simpa using this
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨x ^ 2, hx2⟩
    refine ⟨j + 1, Subtype.ext ?_⟩
    have hj' : (x ^ 2) ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_succ, pow_mul', hj']
  have hKuQ : Ku ≤ Subgroup.normalizer (Q : Set G) := hKuK.trans (hKKT.trans hKTQ)
  have hR''2 : IsPGroup 2 (Ku ⊔ Q : Subgroup G) := hKu2.to_sup_of_normal_right' hQ2 hKuQ
  have hR''Y2 : Ku ⊔ Q ≤ KT ⊓ N :=
    sup_le (le_inf (hKuK.trans hKKT) hKuN) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 KT) hQN)
  have hY2R'' : KT ⊓ N ≤ Subgroup.normalizer ((Ku ⊔ Q : Subgroup G) : Set G) := by
    rintro y ⟨hyKT, hyN⟩
    obtain ⟨k, hk, o, ho, rfl⟩ := hKQ y hyKT
    have hkN : k ∈ N := by
      have : k = (k * o) * o⁻¹ := by group
      rw [this]
      exact N.mul_mem hyN (N.inv_mem (hQN ho))
    have hαkl : α ⟨k, hk⟩ ∈ lstab F := hIl ⟨⟨k, hk⟩, Subgroup.mem_subgroupOf.mpr ⟨hk, hkN⟩, rfl⟩
    have hkKu : k ∈ Subgroup.normalizer (Ku : Set G) := by
      apply Sec20.mem_normalizer_of_map_conj_le
      rintro _ ⟨x, hx, rfl⟩
      have hxK := hKuK hx
      have hkx : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)
      show k * x * k⁻¹ ∈ Ku
      rw [hmemKu _ hkx]
      have he : α ⟨k * x * k⁻¹, hkx⟩ = α ⟨k, hk⟩ * α ⟨x, hxK⟩ * (α ⟨k, hk⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [he]
      exact conj_mem_urad hαkl ((hmemKu x hxK).mp hx)
    have hoKu : o ∈ Subgroup.normalizer (Ku : Set G) := by
      apply Sec20.mem_normalizer_of_map_conj_le
      rintro _ ⟨x, hx, rfl⟩
      have hxK := hKuK hx
      have hox : o * x * o⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hQKN ho) x).mp hxK
      show o * x * o⁻¹ ∈ Ku
      rw [hmemKu _ hox]
      have hcomm : (x : G)⁻¹ * (o * x * o⁻¹) ∈ CFSG.Open.pCoreOf 2 K := by
        refine hQKO _ ?_ (K.mul_mem (K.inv_mem hxK) hox)
        have h1 : x⁻¹ * o * x ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (hKTQ (hKKT (K.inv_mem hxK))) o).mp ho
          simpa using this
        have : (x : G)⁻¹ * (o * x * o⁻¹) = (x⁻¹ * o * x) * o⁻¹ := by group
        rw [this]
        exact Q.mul_mem h1 (Q.inv_mem ho)
      have hαe : α ⟨o * x * o⁻¹, hox⟩ = α ⟨x, hxK⟩ := by
        have h1 := (hαk ((⟨x, hxK⟩ : ↥K)⁻¹ * ⟨o * x * o⁻¹, hox⟩)).mpr (by simpa using hcomm)
        rw [map_mul, map_inv, inv_mul_eq_one] at h1
        exact h1.symm
      rw [hαe]
      exact (hmemKu x hxK).mp hx
    have hyN' := Subgroup.mul_mem _
      (Subgroup.inf_normalizer_le_normalizer_sup Ku Q ⟨hkKu, hKTQ (hKKT hk)⟩)
      (Subgroup.inf_normalizer_le_normalizer_sup Ku Q ⟨hoKu, Subgroup.le_normalizer ho⟩)
    exact hyN'
  have hR''S : Ku ⊔ Q ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR''Y2 hY2R'' hR''2
  have hRY1 : R ≤ Y1 := CFSG.LieType.BorelTits.pCoreOf_le 2 Y1
  have hRle : R ≤ Ku ⊔ Q := by
    intro r hr
    have hrKT : r ∈ KT := (hRY1 hr).1
    obtain ⟨k, hk, o, ho, rfl⟩ := hKQ r hrKT
    set R' := (R ⊔ Q) ⊓ K with hR'
    have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := hRY1.trans (inf_le_left.trans hKTQ)
    have hR'2 : IsPGroup 2 R' :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y1).to_sup_of_normal_right' hQ2 hRQ).to_le
        inf_le_left
    have hkR' : k ∈ R' := by
      refine ⟨?_, hk⟩
      have : k = (k * o) * o⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right (Q.inv_mem ho))
    have hαR' : (R'.subgroupOf K).map α ≤ urad F := by
      refine le_urad_of_isPGroup le_rfl irredModE0_vstab (hR'2.comap_subtype.map _) ?_
      intro h hh
      obtain ⟨k₀, rfl⟩ := hαs h
      have hk₀Y1 : (k₀ : G) ∈ Y1 := ⟨hKKT k₀.2, hK0 k₀ hh⟩
      have hk₀R' : (k₀ : G) ∈ Subgroup.normalizer (R' : Set G) :=
        mem_normalizer_inf_of_mem
          (Subgroup.inf_normalizer_le_normalizer_sup R Q
            ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y1 hk₀Y1, hKTQ (hKKT k₀.2)⟩)
          (Subgroup.le_normalizer k₀.2)
      apply Sec20.mem_normalizer_of_map_conj_le
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨k₀ * x * k₀⁻¹, ?_, by simp⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hk₀R' _).mp (Subgroup.mem_subgroupOf.mp hx)
    have hku : α ⟨k, hk⟩ ∈ urad F := hαR' ⟨⟨k, hk⟩, Subgroup.mem_subgroupOf.mpr hkR', rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hmemKu k hk).mpr hku))
      (Subgroup.mem_sup_right ho)
  have hQS : Q ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 KT) hQN) (inf_le_left.trans hKTQ) hQ2
  have hSY2 : S ≤ KT ⊓ N := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSY1 : S ≤ Y1 := by
    intro s hs
    obtain ⟨k, hk, o, ho, rfl⟩ := hKQ s (hSY2 hs).1
    have hkS : k ∈ S := by
      have : k = (k * o) * o⁻¹ := by group
      rw [this]
      exact S.mul_mem hs (S.inv_mem (hQS ho))
    have hαS : ((S ⊓ K).subgroupOf K).map α ≤ urad F := by
      refine le_urad_of_isPGroup le_rfl irredModE0_vstab
        (((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left).comap_subtype.map _) ?_
      intro h hh
      obtain ⟨k₀, hk₀, rfl⟩ := hvI hh
      have hk₀KN : (k₀ : G) ∈ K ⊓ N := Subgroup.mem_subgroupOf.mp hk₀
      have hk₀S : (k₀ : G) ∈ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) :=
        mem_normalizer_inf_of_mem
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ ⟨hKKT hk₀KN.1, hk₀KN.2⟩)
          (Subgroup.le_normalizer hk₀KN.1)
      apply Sec20.mem_normalizer_of_map_conj_le
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨k₀ * x * k₀⁻¹, ?_, by simp⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hk₀S _).mp (Subgroup.mem_subgroupOf.mp hx)
    have hkv : α ⟨k, hk⟩ ∈ vstab F :=
      urad_le_vstab (hαS ⟨⟨k, hk⟩, Subgroup.mem_subgroupOf.mpr ⟨hkS, hk⟩, rfl⟩)
    exact ⟨(hSY2 hs).1, Subgroup.mul_mem _ (hK0 ⟨k, hk⟩ hkv) (hTC (hQT ho))⟩
  have hSR : S ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSY1
      (hY1Y2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact le_antisymm hSR (hRle.trans hR''S)

theorem false_of_sTwenty_eq_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (hS : CFSG.Open.pCoreOf 2 ((kTwenty M c ⊔ T) ⊓ N) =
      CFSG.Open.pCoreOf 2 ((kTwenty M c ⊔ T) ⊓ Subgroup.centralizer (zTwenty T : Set G)))
    (hcore : CFSG.Quasithin.C134NotCentralizerCore (kTwenty M c ⊔ T) (sTwenty M N c T)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTKT : CFSG.ABGLocalTools.IsSylowOf 2 T (kTwenty M c ⊔ T) :=
    hT.sylow.of_le le_sup_right (sup_le hKM hT.sylow.le)
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf T (kTwenty M c ⊔ T) := by
    obtain ⟨h1, h2, h3⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hTKT
    exact ⟨h1, h2, h3⟩
  have hST : sTwenty M N c T ≤ T :=
    pCoreOf_le_of_isSylowOf (hT.sylow.of_le (le_inf le_sup_right hTN)
      (inf_le_left.trans (sup_le hKM hT.sylow.le)))
  apply hcore T hsyl hST
  rw [omegaOneCenterOf_eq_zTwenty]
  exact hS

end CFSG.RankThree.PartTwo.Sec20
