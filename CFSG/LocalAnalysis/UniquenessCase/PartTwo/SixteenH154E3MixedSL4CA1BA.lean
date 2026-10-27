module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Para
public import CFSG.GroupTheory.AlternatingFive.SylowTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique

structure s16h_SL4TwoFrame {W : Type} [CommGroup W] (X L L' T : Subgroup (MulAut W)) : Prop where
  le_x : L ≤ X
  le_x' : L' ≤ X
  t_le : T ≤ X
  t_two : IsPGroup 2 ↥T
  t_syl : ¬ 2 ∣ T.relIndex X
  comm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  perm : ∀ x ∈ X,
    (L.map (MulAut.conj x).toMonoidHom = L ∧ L'.map (MulAut.conj x).toMonoidHom = L') ∨
    (L.map (MulAut.conj x).toMonoidHom = L' ∧ L'.map (MulAut.conj x).toMonoidHom = L)
  swap : ∃ t ∈ T, L.map (MulAut.conj t).toMonoidHom = L'

private theorem s16h_sl4tf_mem_of_pow_nine {Y : Type} [Group Y]
    {X : Subgroup Y} [hN : X.Normal] (hP : IsPGroup 2 (Y ⧸ X)) {y : Y}
    (hy : y ^ 9 = 1) : y ∈ X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq9 : (QuotientGroup.mk' X y) ^ 9 = 1 := by
    rw [← map_pow, hy, map_one]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) (QuotientGroup.mk' X y)
  have hdvd : orderOf (QuotientGroup.mk' X y) ∣ 9 := orderOf_dvd_of_pow_eq_one hq9
  have h2k : 2 ^ k ∣ 9 := hk ▸ hdvd
  have hcop : Nat.Coprime (2 ^ k) 9 := (by norm_num : Nat.Coprime 2 9).pow_left k
  have h1 : 2 ^ k = 1 := by
    have hg : Nat.gcd (2 ^ k) 9 = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
    rwa [Nat.gcd_eq_left h2k] at hg
  have hq1 : QuotientGroup.mk' X y = 1 := orderOf_eq_one_iff.mp (hk.trans h1)
  exact (QuotientGroup.eq_one_iff y).mp hq1

private theorem s16h_sl4tf_mem_sup_of_commute {G : Type} [Group G] {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, x, hx, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, H.mul_mem ha₁ ha₂, b₁ * b₂, K.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * ((a₂ * b₁) * b₂) := by group
      _ = a₁ * ((b₁ * a₂) * b₂) := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
    rw [hcomm a ha b hb, mul_inv_rev]

private theorem s16h_sl4tf_norm_card {X : Type} [Group X]
    (ψ : X ≃* alternatingGroup (Fin 5)) (T : Subgroup X)
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) :
    Nat.card (Subgroup.normalizer (T : Set X)) = 12 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Subgroup (alternatingGroup (Fin 5)) := T.map ψ.toMonoidHom
  have hT' : IsPGroup 2 T' := hT.map ψ.toMonoidHom
  have hodd' : ¬ 2 ∣ T'.index := by
    rw [Subgroup.index_map_of_bijective ψ.bijective]
    exact hodd
  let P : Sylow 2 (alternatingGroup (Fin 5)) := hT'.toSylow hodd'
  have hP : (P : Subgroup (alternatingGroup (Fin 5))) = T' :=
    IsPGroup.toSylow_coe hT' hodd'
  have h12 : Nat.card (Subgroup.normalizer (T' : Set (alternatingGroup (Fin 5)))) = 12 := by
    rw [← hP]
    exact CFSG.GroupTheory.AlternatingFive.card_normalizer_sylow_two P
  have hmap : (Subgroup.normalizer (T : Set X)).map ψ.toMonoidHom =
      Subgroup.normalizer (T' : Set (alternatingGroup (Fin 5))) := by
    rw [Subgroup.map_normalizer_eq_of_bijective T ψ.bijective]
  have hc := Subgroup.card_map_of_injective (f := ψ.toMonoidHom)
    (K := Subgroup.normalizer (T : Set X)) ψ.injective
  rw [hmap, h12] at hc
  exact hc.symm

private theorem s16h_sl4tf_nx_eq {W : Type} [CommGroup W]
    {X L L' : Subgroup (MulAut W)} (hLL' : L ≠ L')
    (hperm : ∀ x ∈ X,
      (L.map (MulAut.conj x).toMonoidHom = L ∧ L'.map (MulAut.conj x).toMonoidHom = L') ∨
      (L.map (MulAut.conj x).toMonoidHom = L' ∧ L'.map (MulAut.conj x).toMonoidHom = L)) :
    X ⊓ Subgroup.normalizer (L : Set (MulAut W)) =
      X ⊓ Subgroup.normalizer (L' : Set (MulAut W)) := by
  have memN : ∀ {H : Subgroup (MulAut W)} {y : MulAut W},
      y ∈ Subgroup.normalizer (H : Set (MulAut W)) ↔
        H.map (MulAut.conj y).toMonoidHom = H := by
    intro H y
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  ext y
  constructor
  · rintro ⟨hyX, hyN⟩
    refine ⟨hyX, ?_⟩
    rcases hperm y hyX with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact memN.mpr h2
    · exact (hLL' ((memN.mp hyN).symm.trans h1)).elim
  · rintro ⟨hyX, hyN⟩
    refine ⟨hyX, ?_⟩
    rcases hperm y hyX with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact memN.mpr h1
    · exact (hLL' (((memN.mp hyN).symm.trans h2).symm)).elim

private theorem s16h_sl4tf_inf_eq_bot {W : Type} [CommGroup W] [Finite W]
    {L L' : Subgroup (MulAut W)} (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hL : IsAlt ↥L 5) (hLL' : L ≠ L') (hcard : Nat.card ↥L' = Nat.card ↥L) :
    L ⊓ L' = ⊥ := by
  obtain ⟨e⟩ := hL
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hLnorm : L ≤ Subgroup.normalizer ((L ⊓ L') : Set (MulAut W)) := by
    refine (show L ≤ Subgroup.centralizer ((L ⊓ L') : Set (MulAut W)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm a ha y hy.2).symm
  have hnorm : ((L ⊓ L').subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hLnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ L').subgroupOf L) with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff] at hbot
    simpa [inf_of_le_left inf_le_left] using hbot
  · exfalso
    have hle : L ≤ L' := (Subgroup.subgroupOf_eq_top.1 htop).trans inf_le_right
    exact hLL' (Subgroup.eq_of_le_of_card_ge hle hcard.le)

theorem s16h_sl4_a5_parabolic_of_two_frame {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} (F : s16h_SL4TwoFrame X L L' T)
    (hL : IsAlt ↥L 5) (hLL' : L ≠ L') :
    ∃ (J : Subgroup (MulAut W)) (a : ℕ), J ≤ X ∧ T ≤ J ∧ J ≤ L ⊔ L' ⊔ T ∧
      Nat.card ↥J = 2 ^ a * 9 ∧ ∀ x ∈ J, x ^ 9 = 1 → x ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, htL⟩ := F.swap
  have hcardLL' : Nat.card ↥L' = Nat.card ↥L := by
    rw [← htL, Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hperm : ∀ x ∈ X,
      (L.map (MulAut.conj x).toMonoidHom = L ∧ L'.map (MulAut.conj x).toMonoidHom = L') ∨
      (L.map (MulAut.conj x).toMonoidHom = L' ∧ L'.map (MulAut.conj x).toMonoidHom = L) :=
    F.perm
  set X0 : Subgroup (MulAut W) := X ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hX0def
  have hNX : X ⊓ Subgroup.normalizer (L' : Set (MulAut W)) = X0 := by
    rw [hX0def]
    exact (s16h_sl4tf_nx_eq hLL' hperm).symm
  have hX0norm : X ≤ Subgroup.normalizer (X0 : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show X0.map (MulAut.conj x).toMonoidHom = X0
    rw [hX0def, Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      Subgroup.map_normalizer_eq_of_bijective L (MulAut.conj x).bijective]
    have hxX : X.map (MulAut.conj x).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
    rw [hxX]
    rcases hperm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
    · rw [h1]
      simpa only [hX0def] using hNX
  have hTX : IsSylowTwoOf T X := ⟨F.t_le, F.t_two, F.t_syl⟩
  have hT0syl : IsSylowTwoOf (T ⊓ X0) X0 :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hTX inf_le_left hX0norm
  have hLX0 : L ≤ X0 := by rw [hX0def]; exact le_inf F.le_x Subgroup.le_normalizer
  have hX0NL : X0 ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [hX0def]; exact inf_le_right
  have hTLsyl : IsSylowTwoOf (T ⊓ L) L := by
    have h := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hT0syl hLX0 hX0NL
    rwa [inf_assoc, inf_comm X0 L, inf_of_le_left hLX0] at h
  have hAlt := hL
  obtain ⟨ψ⟩ := hAlt
  have hTL'p : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le inf_le_right hTLsyl.2.1
  have hTL'odd : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index := hTLsyl.2.2
  have hA5 := s16h_sl4tf_norm_card ψ ((T ⊓ L).subgroupOf L) hTL'p hTL'odd
  set BL : Subgroup (MulAut W) :=
    Subgroup.normalizer (T ⊓ L : Subgroup (MulAut W)) ⊓ L with hBLdef
  have hBLsub : BL.subgroupOf L =
      Subgroup.normalizer (((T ⊓ L).subgroupOf L) : Set ↥L) := by
    rw [hBLdef, Subgroup.inf_subgroupOf_right]
    exact Subgroup.subgroupOf_normalizer_eq inf_le_right
  have hBLe : BL ≤ L := by rw [hBLdef]; exact inf_le_right
  have hBLcard : Nat.card ↥BL = 12 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBLe).toEquiv]
    rw [hBLsub, hA5]
  set BL' : Subgroup (MulAut W) := BL.map (MulAut.conj t).toMonoidHom with hBL'def
  have hTtmap : T.map (MulAut.conj t).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htT)
  have hBL'eq : BL' = Subgroup.normalizer (T ⊓ L' : Subgroup (MulAut W)) ⊓ L' := by
    rw [hBL'def, hBLdef,
      Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
      Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj t).bijective,
      Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hTtmap, htL]
  have hBL'card : Nat.card ↥BL' = 12 := by
    rw [hBL'def, Subgroup.card_map_of_injective (MulAut.conj t).injective, hBLcard]
  have hBL'le : BL' ≤ L' := by rw [hBL'eq]; exact inf_le_right
  have hBLeq : BL ⊓ BL' = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc BL ⊓ BL' ≤ L ⊓ L' := inf_le_inf hBLe hBL'le
      _ = ⊥ := s16h_sl4tf_inf_eq_bot F.comm hL hLL' hcardLL'
  have hcommBL : ∀ a ∈ BL, ∀ b ∈ BL', a * b = b * a :=
    fun a ha b hb => F.comm a (hBLe ha) b (hBL'le hb)
  have hconjBL : ∀ s ∈ T,
      (BL.map (MulAut.conj s).toMonoidHom = BL ∧
        BL'.map (MulAut.conj s).toMonoidHom = BL') ∨
      (BL.map (MulAut.conj s).toMonoidHom = BL' ∧
        BL'.map (MulAut.conj s).toMonoidHom = BL) := by
    intro s hs
    have hTs : T.map (MulAut.conj s).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs)
    have hconjInf : (Subgroup.normalizer (T ⊓ L : Subgroup (MulAut W)) ⊓ L).map
        (MulAut.conj s).toMonoidHom =
        Subgroup.normalizer (T ⊓ L.map (MulAut.conj s).toMonoidHom :
          Subgroup (MulAut W)) ⊓ L.map (MulAut.conj s).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj s).injective,
        Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj s).bijective,
        Subgroup.map_inf _ _ _ (MulAut.conj s).injective, hTs]
    have hconjInf' : (Subgroup.normalizer (T ⊓ L' : Subgroup (MulAut W)) ⊓ L').map
        (MulAut.conj s).toMonoidHom =
        Subgroup.normalizer (T ⊓ L'.map (MulAut.conj s).toMonoidHom :
          Subgroup (MulAut W)) ⊓ L'.map (MulAut.conj s).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj s).injective,
        Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj s).bijective,
        Subgroup.map_inf _ _ _ (MulAut.conj s).injective, hTs]
    rcases hperm s (F.t_le hs) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hBLdef, hconjInf, h1]
      · rw [hBL'eq, hconjInf', h2]
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hBLdef, hconjInf, h1, hBL'eq]
      · rw [hBL'eq, hconjInf', h2, hBLdef]
  have hTnormB : T ≤ Subgroup.normalizer ((BL ⊔ BL' : Subgroup (MulAut W)) : Set (MulAut W)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases hconjBL s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · change Subgroup.map (MulAut.conj s).toMonoidHom (BL ⊔ BL') = BL ⊔ BL'
      rw [Subgroup.map_sup, h1, h2]
    · change Subgroup.map (MulAut.conj s).toMonoidHom (BL ⊔ BL') = BL ⊔ BL'
      rw [Subgroup.map_sup, h1, h2, sup_comm]
  set B : Subgroup (MulAut W) := BL ⊔ BL' with hBdef
  set J : Subgroup (MulAut W) := B ⊔ T with hJdef
  have hTBnorm : T ≤ Subgroup.normalizer (B : Set (MulAut W)) := by
    rw [hBdef]; exact hTnormB
  have hBL'normBL : BL' ≤ Subgroup.normalizer (BL : Set (MulAut W)) := by
    refine (show BL' ≤ Subgroup.centralizer (BL : Set (MulAut W)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcommBL y hy b hb
  have hBcard : Nat.card ↥B = 144 := by
    have h1 : BL.relIndex (BL' ⊔ BL) = BL.relIndex BL' :=
      CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hBL'normBL
    have h2 : BL.relIndex BL' * Nat.card ↥(BL ⊓ BL') = Nat.card ↥BL' :=
      Subgroup.relIndex_mul_card BL BL'
    have h3 : BL.relIndex (BL' ⊔ BL) * Nat.card ↥(BL ⊓ (BL' ⊔ BL)) = Nat.card ↥(BL' ⊔ BL) :=
      Subgroup.relIndex_mul_card BL (BL' ⊔ BL)
    rw [inf_eq_left.mpr le_sup_right] at h3
    rw [hBLeq, Subgroup.card_bot, mul_one] at h2
    have hrel : BL.relIndex BL' = 12 := h2.trans hBL'card
    rw [hBdef, sup_comm, ← h3, h1, hrel, hBLcard]
  obtain ⟨k, hk⟩ := F.t_two.exists_card_eq
  have hBT2 : IsPGroup 2 (B ⊓ T : Subgroup (MulAut W)) :=
    IsPGroup.to_inf_right (H := B) (K := T) F.t_two
  obtain ⟨j, hj⟩ := hBT2.exists_card_eq
  have hBrelJ : B.relIndex J = B.relIndex T := by
    have h := CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hTBnorm
    rwa [show T ⊔ B = J from by rw [hJdef, sup_comm]] at h
  have hBJnorm : (B.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show B ≤ J from by rw [hJdef]; exact le_sup_left)).mpr
      (by rw [hJdef]; exact sup_le Subgroup.le_normalizer hTBnorm)
  have hquot_dvd : Nat.card (↥J ⧸ B.subgroupOf J) ∣ 2 ^ k := by
    rw [show Nat.card (↥J ⧸ B.subgroupOf J) = B.relIndex J from rfl, hBrelJ]
    refine ⟨2 ^ j, ?_⟩
    have h2 : B.relIndex T * 2 ^ j = 2 ^ k := by
      have h := Subgroup.relIndex_mul_card B T
      rwa [hj, hk] at h
    exact h2.symm
  have hPquot : IsPGroup 2 (↥J ⧸ B.subgroupOf J) := IsPGroup.of_card_dvd_pow hquot_dvd
  have hJ_eq : Nat.card ↥J = B.relIndex T * Nat.card ↥B := by
    have h3 := Subgroup.relIndex_mul_card B (T ⊔ B)
    rw [inf_eq_left.mpr le_sup_right, show T ⊔ B = J from by rw [hJdef, sup_comm], hBrelJ] at h3
    exact h3.symm
  have hJcard_mul : Nat.card ↥J * 2 ^ j = 2 ^ k * 144 := by
    rw [hJ_eq, hBcard]
    have h2 : B.relIndex T * 2 ^ j = 2 ^ k := by
      have h := Subgroup.relIndex_mul_card B T
      rwa [hj, hk] at h
    calc (B.relIndex T * 144) * 2 ^ j = (B.relIndex T * 2 ^ j) * 144 := by ring
      _ = 2 ^ k * 144 := by rw [h2]
  have hjle : j ≤ k := by
    have hdvd : 2 ^ j ∣ 2 ^ k := by
      rw [← hj, ← hk]
      exact Subgroup.card_dvd_of_le (inf_le_right : B ⊓ T ≤ T)
    exact (Nat.pow_le_pow_iff_right (by norm_num : 2 ≤ 2)).mp
      (Nat.le_of_dvd (by positivity) hdvd)
  have hJcard : Nat.card ↥J = 2 ^ (k + 4 - j) * 9 := by
    have h144 : (144 : ℕ) = 2 ^ 4 * 9 := by norm_num
    rw [h144] at hJcard_mul
    have hRHS : 2 ^ k * (2 ^ 4 * 9) = (2 ^ (k + 4 - j) * 9) * 2 ^ j := by
      have hpow : 2 ^ (k + 4 - j) * 2 ^ j = 2 ^ (k + 4) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : j ≤ k + 4)]
      rw [← mul_assoc, ← pow_add, ← hpow]
      ac_rfl
    rw [hRHS] at hJcard_mul
    exact Nat.mul_right_cancel (by positivity : 0 < 2 ^ j) hJcard_mul
  refine ⟨J, k + 4 - j, ?_, ?_, ?_, hJcard, ?_⟩
  · rw [hJdef, hBdef]
    exact sup_le (sup_le (hBLe.trans F.le_x) (hBL'le.trans F.le_x')) F.t_le
  · rw [hJdef]; exact le_sup_right
  · rw [hJdef, hBdef]
    exact sup_le (sup_le (hBLe.trans (le_sup_left.trans le_sup_left))
      (hBL'le.trans (le_sup_right.trans le_sup_left))) le_sup_right
  · intro x hxJ hx9
    have hxJ9 : (⟨x, hxJ⟩ : ↥J) ^ 9 = 1 := Subtype.ext (by simpa using hx9)
    have hxB : x ∈ B := by
      have hxBsub : (⟨x, hxJ⟩ : ↥J) ∈ B.subgroupOf J :=
        s16h_sl4tf_mem_of_pow_nine hPquot hxJ9
      exact Subgroup.mem_subgroupOf.mp hxBsub
    rcases s16h_sl4tf_mem_sup_of_commute hcommBL (by rw [hBdef] at hxB; exact hxB) with
      ⟨a, ha, b, hb, hab⟩
    have ha12 : a ^ 12 = 1 := by
      have hd : orderOf a ∣ 12 := by
        have h := Subgroup.orderOf_dvd_natCard BL ha
        rwa [hBLcard] at h
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hb12 : b ^ 12 = 1 := by
      have hd : orderOf b ∣ 12 := by
        have h := Subgroup.orderOf_dvd_natCard BL' hb
        rwa [hBL'card] at h
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hx12 : x ^ 12 = 1 := by
      rw [← hab]
      have hc : Commute a b := hcommBL a ha b hb
      rw [hc.mul_pow, ha12, hb12, mul_one]
    have hd9 : orderOf x ∣ 9 := orderOf_dvd_of_pow_eq_one hx9
    have hd12 : orderOf x ∣ 12 := orderOf_dvd_of_pow_eq_one hx12
    have hd3 : orderOf x ∣ 3 := by
      have h := Nat.dvd_gcd hd9 hd12
      norm_num at h
      exact h
    exact orderOf_dvd_iff_pow_eq_one.mp hd3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
