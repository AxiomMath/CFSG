module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312KG
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoreA
public import CFSG.Quasithin.Vol2.Ch4Sec2NoSum2

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem mem_pCoreOf_nsb37 {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X :=
  Subgroup.mem_map_iff_mem X.subtype_injective

omit [Finite G] in
private theorem mem_sup_of_le_normalizer_nsb37 {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, (a₂⁻¹ * b₁ * a₂) * b₂, B.mul_mem ?_ hb₂, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha₂)) b₁).1 hb₁
        simpa using this
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA ha) b⁻¹).1 (B.inv_mem hb)
        exact this }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact (_root_.sup_le hAS hBS) hx

private theorem LH_inf_eq_nsb37 {T M L Mm I H K H₁ K₁ : Subgroup G} (c : Conf4212 G T M L I H K)
    (hy : Hyp4_2_3 G T M L Mm I) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hIH₁ : I ≤ H₁) (hKH₁ : K ≤ H₁) (c₁ : Conf4212 G T M L I H₁ K₁) : L ⊓ H₁ = L ⊓ H := by
  have hLHL : perfectCore (L ⊓ H) ≤ L := (perfectCore_le _).trans inf_le_left
  have hLHH : perfectCore (L ⊓ H) ≤ H := (perfectCore_le _).trans inf_le_right
  have hLHH₁ : perfectCore (L ⊓ H) ≤ H₁ := c.LH_le.trans hKH₁
  have hN : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    c.hyp421.sup_le.trans (c.normal.trans (normalizer_le_normalizer_pCoreOf 2 L))
  have hL2 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) hN
      (pCoreOf_isPGroup 2 L)
  have hdec : ∀ x ∈ L, ∃ a ∈ perfectCore (L ⊓ H), ∃ o ∈ pCoreOf 2 L, x = a * o := by
    intro x hx
    exact mem_sup_of_le_normalizer_nsb37 (hLHL.trans (le_normalizer_pCoreOf 2 L)) (c.L_le hx)
  apply le_antisymm
  ·
    rintro x ⟨hxL, hxH₁⟩
    obtain ⟨a, ha, o, ho, rfl⟩ := hdec x hxL
    have hoH₁ : o ∈ H₁ := by
      have h1 := H₁.mul_mem (H₁.inv_mem (hLHH₁ ha)) hxH₁
      rwa [inv_mul_cancel_left] at h1
    have hoRH₁ : o ∈ pCoreOf 2 (L ⊔ T) ⊓ H₁ := ⟨hL2 ho, hoH₁⟩
    have hoR : o ∈ pCoreOf 2 I := c₁.inf_le_pCoreOf_I hy h37 h38 h39 hoRH₁
    have hoH : o ∈ H := (pCoreOf_le 2 I).trans c.inH.1 hoR
    exact ⟨hxL, H.mul_mem (hLHH ha) hoH⟩
  ·
    rintro x ⟨hxL, hxH⟩
    obtain ⟨a, ha, o, ho, rfl⟩ := hdec x hxL
    have hoH : o ∈ H := by
      have h1 := H.mul_mem (H.inv_mem (hLHH ha)) hxH
      rwa [inv_mul_cancel_left] at h1
    have hoRH : o ∈ pCoreOf 2 (L ⊔ T) ⊓ H := ⟨hL2 ho, hoH⟩
    have hoR : o ∈ pCoreOf 2 I := c.inf_le_pCoreOf_I hy h37 h38 h39 hoRH
    have hoH₁ : o ∈ H₁ := (pCoreOf_le 2 I).trans hIH₁ hoR
    exact ⟨hxL, H₁.mul_mem (hLHH₁ ha) hoH₁⟩

private theorem le_sup_coreK_nsb37 {K N : Subgroup G} (hs : IsSimpleGroup (ModO2 K))
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) {x : G} (hxN : x ∈ N)
    (hxK : x ∉ pCoreOf 2 K) : K ≤ pCoreOf 2 K ⊔ N := by
  have hNn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  haveI hMn : ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
  have hxK' : (⟨x, hNK hxN⟩ : ↥K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hxN
  have hne : (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hNK hxN⟩ : ↥K) ∈
        (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
      Subgroup.mem_map_of_mem _ hxK'
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hxK ((mem_pCoreOf_nsb37 _).mpr hmem)
  have htop : (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) = ⊤ :=
    (hs.eq_bot_or_eq_top_of_normal
      ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))).resolve_left hne
  intro k hk
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨k, hk⟩ : ↥K) ∈
      (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨n', hn', hnk⟩ := Subgroup.mem_map.mp hk'
  have hu1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ((⟨k, hk⟩ : ↥K) * n'⁻¹) = 1 := by
    rw [map_mul, map_inv, hnk, mul_inv_cancel]
  have hu : (⟨k, hk⟩ : ↥K) * n'⁻¹ ∈ CFSG.pCore 2 ↥K := by
    rw [QuotientGroup.mk'_apply] at hu1
    exact (QuotientGroup.eq_one_iff _).mp hu1
  have hu' : (((⟨k, hk⟩ : ↥K) * n'⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := (mem_pCoreOf_nsb37 _).mpr hu
  have hn'N : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
  have hkk : k = (((⟨k, hk⟩ : ↥K) * n'⁻¹ : ↥K) : G) * (n' : G) := by simp
  rw [hkk]
  exact Subgroup.mul_mem_sup hu' hn'N

private theorem K_le_K₁_nsb37 {K K₁ H₁ A : Subgroup G} (hKperf : ⁅K, K⁆ = K)
    (hs : IsSimpleGroup (ModO2 K)) (hAK : A ≤ K) (hAperf : ⁅A, A⁆ = A) (hA : A ≠ ⊥)
    (hAK₁ : A ≤ K₁) (hKH₁ : K ≤ H₁) (hH₁K₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G)) :
    K ≤ K₁ := by
  have hN' : K ≤ Subgroup.normalizer ((K ⊓ K₁ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hk, hH₁K₁ (hKH₁ hk)⟩)
  have hnot : ¬ A ≤ pCoreOf 2 K := fun hle =>
    hA (eq_bot_of_perfect_of_isPGroup_two hAperf ((pCoreOf_isPGroup 2 K).to_le hle))
  obtain ⟨x, hxA, hxK⟩ : ∃ x ∈ A, x ∉ pCoreOf 2 K := by
    by_contra hc
    exact hnot fun x hx => Classical.byContradiction fun hx' => hc ⟨x, hx, hx'⟩
  have hxN : x ∈ K ⊓ K₁ := Subgroup.mem_inf.mpr ⟨hAK hxA, hAK₁ hxA⟩
  have hKWN : K ≤ pCoreOf 2 K ⊔ (K ⊓ K₁) :=
    le_sup_coreK_nsb37 hs inf_le_left hN' hxN hxK
  exact (CFSG.Quasithin.H13.Ch4.CentK.le_of_perfect_of_le_sup_coreA hKperf
    ((pCoreOf_le 2 K).trans hN') (CFSG.Quasithin.isSolvable_pCoreOf_two K) hKWN).trans inf_le_right

private theorem pCoreOf_subgroupOf_nsb37 (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  unfold pCoreOf
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

private theorem relIndex_ne_zero_nsb37 (A B : Subgroup G) : A.relIndex B ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

private theorem card_modO2_eq_relIndex_nsb37 (L : Subgroup G) :
    Nat.card (ModO2 L) = (pCoreOf 2 L).relIndex L := by
  rw [Subgroup.relIndex, pCoreOf_subgroupOf_nsb37, Subgroup.index_eq_card]

private theorem K₁_le_K_nsb37 {T M L Mm I H K H₁ K₁ : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I)
    (c : Conf4212 G T M L I H K) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (c₁ : Conf4212 G T M L I H₁ K₁) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hKK₁ : K ≤ K₁) (hH₁K₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G))
    (hcard : Nat.card (ModO2 K₁) ≤ Nat.card (ModO2 K)) : K₁ ≤ K := by
  have hK₁H₁ : K₁ ≤ H₁ := le_of_mem_cComp c₁.K_mem
  have hU₁H₁ : pCoreOf 2 K₁ ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K₁).trans hK₁H₁)
      (hH₁K₁.trans (normalizer_le_normalizer_pCoreOf 2 K₁)) (pCoreOf_isPGroup 2 K₁)
  have h5 := lemma_4_1_4_five (hy.hyp4_1_1 h37 h38 h39) hy.sigma hy.gammaStar c₁.inH c₁.not_le
  have hU₁I : pCoreOf 2 K₁ ≤ pCoreOf 2 I := hU₁H₁.trans (h5.2.2.1.trans h5.2.2.2)
  have hU₁N : pCoreOf 2 K₁ ≤ Subgroup.normalizer (K : Set G) :=
    hU₁I.trans ((pCoreOf_le 2 I).trans (c.inH.1.trans hHK))
  have hK₁N : K₁ ≤ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) := le_normalizer_pCoreOf 2 K₁
  have hKN : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 K₁ : Subgroup G) : Set G) := by
    intro k hk
    have hk₁ := Subgroup.mem_normalizer_iff.mp (hK₁N (hKK₁ hk))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), (hk₁ x).mp hxU⟩
    · intro hx
      obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, (hk₁ x).mpr hxU⟩
      have e : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      have h := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      rwa [e] at h
  have hPG : IsPGroup 2 ↥(K ⊓ pCoreOf 2 K₁) := (pCoreOf_isPGroup 2 K₁).to_le inf_le_right
  have hKUU : K ⊓ pCoreOf 2 K₁ ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hKN hPG
  obtain ⟨Ku, hKu⟩ : ∃ X : Subgroup K₁, X = K.subgroupOf K₁ := ⟨_, rfl⟩
  obtain ⟨Uu, hUu⟩ : ∃ X : Subgroup K₁, X = (pCoreOf 2 K₁).subgroupOf K₁ := ⟨_, rfl⟩
  obtain ⟨Uo, hUo⟩ : ∃ X : Subgroup K₁, X = (pCoreOf 2 K).subgroupOf K₁ := ⟨_, rfl⟩
  have hUuN : Uu.Normal := by
    rw [hUu]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 K₁)).mpr
      (le_normalizer_pCoreOf 2 K₁)
  have hidx₁ : Uu.index = Nat.card (ModO2 K₁) := by
    rw [hUu, pCoreOf_subgroupOf_nsb37, Subgroup.index_eq_card]
  have hidxK : Uo.relIndex Ku = Nat.card (ModO2 K) := by
    rw [hUo, hKu, Subgroup.relIndex_subgroupOf hKK₁, card_modO2_eq_relIndex_nsb37]
  have hYX : Uu ⊓ Ku ≤ Uo ⊓ Ku := by
    intro x hx
    obtain ⟨hxU, hxK⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, hxK⟩
    rw [hUu, Subgroup.mem_subgroupOf] at hxU
    rw [hKu, Subgroup.mem_subgroupOf] at hxK
    rw [hUo, Subgroup.mem_subgroupOf]
    exact hKUU (Subgroup.mem_inf.mpr ⟨hxK, hxU⟩)
  have hle : Uo.relIndex Ku ≤ Uu.relIndex Ku := by
    have h1 : Uu.relIndex Ku = (Uu ⊓ Ku).relIndex Ku :=
      (Subgroup.inf_relIndex_right Uu Ku).symm
    have h2 : (Uu ⊓ Ku).relIndex Ku = (Uu ⊓ Ku).relIndex (Uo ⊓ Ku) * (Uo ⊓ Ku).relIndex Ku :=
      (Subgroup.relIndex_mul_relIndex (Uu ⊓ Ku) (Uo ⊓ Ku) Ku hYX inf_le_right).symm
    have h3 : (Uo ⊓ Ku).relIndex Ku = Uo.relIndex Ku := Subgroup.inf_relIndex_right Uo Ku
    rw [h1, h2, h3]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (relIndex_ne_zero_nsb37 _ _))
  have hsup : Uu.relIndex (Ku ⊔ Uu) = Uu.relIndex Ku := by
    haveI := hUuN
    exact Subgroup.relIndex_sup_right Ku Uu
  have hmul : Uu.relIndex (Ku ⊔ Uu) * (Ku ⊔ Uu).index = Uu.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have hUuidx : Uu.index ≤ Uo.relIndex Ku := by
    rw [hidx₁, hidxK]
    exact hcard
  have hPidx : (Ku ⊔ Uu).index = 1 := by
    have hpos : Uu.relIndex (Ku ⊔ Uu) ≠ 0 := relIndex_ne_zero_nsb37 _ _
    have hp0 : (Ku ⊔ Uu).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hcle : Uu.relIndex (Ku ⊔ Uu) * (Ku ⊔ Uu).index ≤ Uu.relIndex (Ku ⊔ Uu) * 1 := by
      rw [hmul, mul_one, hsup]
      exact hUuidx.trans hle
    have hp1 := Nat.le_of_mul_le_mul_left hcle (Nat.pos_of_ne_zero hpos)
    omega
  have hPtop : Ku ⊔ Uu = ⊤ := Subgroup.index_eq_one.mp hPidx
  have hK₁le : K₁ ≤ K ⊔ pCoreOf 2 K₁ := by
    intro x hx
    have hxP : (⟨x, hx⟩ : ↥K₁) ∈ Ku ⊔ Uu := by
      rw [hPtop]
      exact Subgroup.mem_top _
    have hPQ : Ku ⊔ Uu ≤ (K ⊔ pCoreOf 2 K₁ : Subgroup G).subgroupOf K₁ := by
      refine sup_le ?_ ?_
      · intro y hy
        rw [hKu, Subgroup.mem_subgroupOf] at hy
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hy)
      · intro y hy
        rw [hUu, Subgroup.mem_subgroupOf] at hy
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hy)
    exact Subgroup.mem_subgroupOf.mp (hPQ hxP)
  have hK₁le' : K₁ ≤ pCoreOf 2 K₁ ⊔ K := by
    rw [sup_comm]
    exact hK₁le
  exact CFSG.Quasithin.H13.Ch4.CentK.le_of_perfect_of_le_sup_coreA (perfect_of_mem_cComp c₁.K_mem)
    hU₁N (CFSG.Quasithin.isSolvable_pCoreOf_two K₁) hK₁le'

private theorem transport_eq_nsb37 {X Y : Subgroup G} (P : Subgroup G → Prop) (h : X = Y)
    (hP : P X) : P Y := by
  subst h
  exact hP

private theorem noSumBigData_transport_nsb37 {T M L Mm I H K H₁ K₁ : Subgroup G} {m k : ℕ}
    (hd : NoSumBigData G T M L Mm I H K m k) (hIH₁ : InM I H₁) (c₁ : Conf4212 G T M L I H₁ K₁)
    (hL : perfectCore (L ⊓ H₁) = perfectCore (L ⊓ H)) :
    NoSumBigData G T M L Mm I H₁ K₁ m k := by
  obtain ⟨hy, -, -, hm, hmk, hk4, hPSL, hSum⟩ := hd
  refine ⟨hy, hIH₁, c₁, hm, hmk, hk4, ?_, ?_⟩
  · exact transport_eq_nsb37 (fun A => IsPSL m 2 1 (ModO2 A)) hL.symm hPSL
  · exact transport_eq_nsb37
      (fun A => IsSumOfNaturalModules (A ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
        ((pCoreOf 2 I).subgroupOf (A ⊔ pCoreOf 2 I))
        (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k) hL.symm hSum

theorem lemma37_of (h32 : Lemma32) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h425 : Thm4_2_5)
    (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) : Lemma37 := by
  intro G _ _ T M L Mm I H K m k hch X hIX hKX hX
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  have hy : Hyp4_2_3 G T M L Mm I := hd.1
  have hIH : InM I H := hd.2.1
  have c : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hHK, hK2, n, -, hKn⟩ := h32 G T M L Mm I H K m k hd
  have hKs : IsSimpleGroup (ModO2 K) := CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSL hKn
  obtain ⟨H₁, hH₁⟩ := exists_inM_of_pCoreOf_ne_bot hX
  have hIH₁ : InM I H₁ := ⟨hH₁.1, hIX.trans hH₁.2⟩
  have hKH₁ : K ≤ H₁ := hKX.trans hH₁.2
  have hH₁M : ¬ H₁ ≤ M := fun h => c.K_not_le (hKH₁.trans h)
  have hne : H₁ ≠ M := fun h => hH₁M (h ▸ le_rfl)
  have h425' := h425 G T M L Mm I H₁ hy hIH₁ hne
  obtain ⟨K₁, c₁⟩ := hy.lemma_4_2_12_two h36 h37 h38 h39 (h48 G) (inH_of_inM hIH₁) hH₁M h425'
  have hL₁ : perfectCore (L ⊓ H₁) = perfectCore (L ⊓ H) := by
    rw [LH_inf_eq_nsb37 c hy h37 h38 h39 hIH₁.2 hKH₁ c₁]
  have hd₁ : NoSumBigData G T M L Mm I H₁ K₁ m k := noSumBigData_transport_nsb37 hd hIH₁ c₁ hL₁
  have hH₁K₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G) := (h32 G T M L Mm I H₁ K₁ m k hd₁).1
  have hcard : Nat.card (ModO2 K₁) ≤ Nat.card (ModO2 K) := hch.2 H₁ K₁ hd₁
  have hLK₁ : perfectCore (L ⊓ H) ≤ K₁ := by
    rw [← hL₁]
    exact c₁.LH_le
  have hKK₁ : K ≤ K₁ :=
    K_le_K₁_nsb37 (perfect_of_mem_cComp c.K_mem) hKs c.LH_le
      (perfectCore_perfect _) (ne_bot_of_mem_cComp c.LH_mem) hLK₁ hKH₁ hH₁K₁
  have hK₁K : K₁ ≤ K := K₁_le_K_nsb37 hy c h37 h38 h39 c₁ hHK hKK₁ hH₁K₁ hcard
  have hK₁eq : K₁ = K := le_antisymm hK₁K hKK₁
  rw [hK₁eq] at hH₁K₁
  have hH₁H : H₁ ≤ H := by
    have h1 : H₁ ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      hH₁K₁.trans (normalizer_le_normalizer_pCoreOf 2 K)
    rwa [Conf4212.normalizer_pCoreOf_K_eq hIH hHK hK2] at h1
  exact hH₁.2.trans hH₁H

end CFSG.Quasithin.H13.Ch4.NSB
