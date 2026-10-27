module

public import CFSG.Quasithin.H13.A7FiveFixed
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.Quasithin.H13.A7CentralCoverGen
public import CFSG.Quasithin.H13.A7NaturalLocal
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] noncomputable def autA5Equiv : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective (SteinbergCB.conjPerm 5)
    ⟨SteinbergCB.conjPerm_injective (by norm_num), SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩

theorem autA5Equiv_apply_coe (σ : Perm (Fin 5)) (g : alternatingGroup (Fin 5)) :
    ((autA5Equiv σ g : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ * g * σ⁻¹ :=
  SteinbergCB.conjPerm_apply 5 σ g

section KAct

variable {K : Subgroup G} (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))

@[expose] noncomputable def kAct : normalizer (K : Set G) →* Perm (Fin 5) :=
  autA5Equiv.symm.toMonoidHom.comp ((MulAut.congr eK).toMonoidHom.comp
    (SteinbergBS.conjQuotientHom K (CFSG.pCore 2 K)))

@[expose] noncomputable def kHom : K →* alternatingGroup (Fin 5) :=
  eK.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 K))

@[expose] noncomputable def kBar : K →* Perm (Fin 5) :=
  (alternatingGroup (Fin 5)).subtype.comp (kHom eK)

theorem kBar_apply (k : K) : kBar eK k = (eK (QuotientGroup.mk k) : Perm (Fin 5)) := rfl

theorem kHom_surjective : Function.Surjective (kHom eK) :=
  eK.surjective.comp (QuotientGroup.mk'_surjective _)

theorem kBar_mem (k : K) : kBar eK k ∈ alternatingGroup (Fin 5) := (kHom eK k).2

theorem kBar_eq_one_iff (k : K) : kBar eK k = 1 ↔ k ∈ CFSG.pCore 2 K := by
  rw [kBar_apply, ← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 K)]
  constructor
  · intro h
    apply eK.injective
    rw [map_one]
    exact Subtype.ext h
  · intro h
    rw [h, map_one]
    rfl

theorem kAct_conj {g : G} (hg : g ∈ normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    kBar eK ⟨g * k * g⁻¹, (mem_normalizer_iff.1 hg k).1 hk⟩ =
      kAct eK ⟨g, hg⟩ * kBar eK ⟨k, hk⟩ * (kAct eK ⟨g, hg⟩)⁻¹ := by
  have h : autA5Equiv (kAct eK ⟨g, hg⟩) =
      MulAut.congr eK (SteinbergBS.conjQuotientHom K (CFSG.pCore 2 K) ⟨g, hg⟩) := by
    simp only [kAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have h2 := congrArg (fun φ : MulAut (alternatingGroup (Fin 5)) =>
    ((φ (eK (QuotientGroup.mk ⟨k, hk⟩)) : alternatingGroup (Fin 5)) : Perm (Fin 5))) h
  simp only [autA5Equiv_apply_coe, MulAut.congr_apply] at h2
  rw [kBar_apply, kBar_apply, h2]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem kAct_of_mem {k : G} (hk : k ∈ K) :
    kAct eK ⟨k, le_normalizer hk⟩ = kBar eK ⟨k, hk⟩ := by
  apply SteinbergCB.conjPerm_injective (n := 5) (by norm_num)
  ext x
  obtain ⟨l, rfl⟩ := kHom_surjective eK x
  rw [SteinbergCB.conjPerm_apply, SteinbergCB.conjPerm_apply]
  have h1 := kAct_conj eK (le_normalizer hk) l.2
  have h2 : kBar eK ⟨k * l * k⁻¹, (mem_normalizer_iff.1 (le_normalizer hk) l).1 l.2⟩ =
      kBar eK ⟨k, hk⟩ * kBar eK l * (kBar eK ⟨k, hk⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have h3 : ((kHom eK l : alternatingGroup (Fin 5)) : Perm (Fin 5)) = kBar eK l := rfl
  rw [h3, ← h1, ← h2]

theorem comm_mem_of_kAct_eq_one {g : G} (hg : g ∈ normalizer (K : Set G))
    (h1 : kAct eK ⟨g, hg⟩ = 1) {k : G} (hk : k ∈ K) :
    g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have h := kAct_conj eK hg hk
  rw [h1, one_mul, inv_one, mul_one] at h
  set k' : K := ⟨g * k * g⁻¹, (mem_normalizer_iff.1 hg k).1 hk⟩
  have h2 : kBar eK (k' * (⟨k, hk⟩ : K)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [kBar_eq_one_iff] at h2
  rw [pCoreOf_eq_map_cfsgPCore]
  exact ⟨_, h2, rfl⟩

theorem kAct_eq_one_of_comm {g : G} (hg : g ∈ normalizer (K : Set G))
    (h : ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : kAct eK ⟨g, hg⟩ = 1 := by
  apply SteinbergCB.conjPerm_injective (n := 5) (by norm_num)
  rw [map_one]
  ext x
  obtain ⟨l, rfl⟩ := kHom_surjective eK x
  rw [SteinbergCB.conjPerm_apply, MulAut.one_apply]
  have h1 := kAct_conj eK hg l.2
  have h3 : ((kHom eK l : alternatingGroup (Fin 5)) : Perm (Fin 5)) = kBar eK l := rfl
  rw [h3, ← h1]
  have hmem := h l l.2
  rw [pCoreOf_eq_map_cfsgPCore] at hmem
  obtain ⟨c, hc, hce⟩ := hmem
  have h4 : (⟨g * l * g⁻¹, (mem_normalizer_iff.1 hg l).1 l.2⟩ : K) = c * l := by
    apply Subtype.ext
    show g * l * g⁻¹ = (c : G) * l
    rw [show (c : G) = g * l * g⁻¹ * (l : G)⁻¹ from hce]
    group
  rw [h4, map_mul, (kBar_eq_one_iff eK c).2 hc, one_mul]

theorem mem_pCoreOf_of_kAct_eq_one {k : G} (hk : k ∈ K)
    (h1 : kAct eK ⟨k, le_normalizer hk⟩ = 1) : k ∈ pCoreOf 2 K := by
  rw [kAct_of_mem eK hk, kBar_eq_one_iff] at h1
  rw [pCoreOf_eq_map_cfsgPCore]
  exact ⟨_, h1, rfl⟩

end KAct

section Borel

variable [Finite G]

omit [Finite G] in
theorem pCoreOf_le_of_le_normalizer (T : Sylow 2 G) {K : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) : pCoreOf 2 K ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : IsPGroup 2 (pCoreOf 2 K) := by
    rw [pCoreOf_eq_map_cfsgPCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := K)).map K.subtype
  have hTO : (T : Subgroup G) ≤ normalizer (pCoreOf 2 K : Set G) :=
    hTK.trans normalizer_le_normalizer_pCoreOf_two
  have h := T.3 (hO.to_sup_of_normal_left' T.isPGroup' hTO) le_sup_right
  rw [← h]
  exact le_sup_left

theorem sylow_inf_of_le_normalizer (T : Sylow 2 G) {K : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    IsPGroup 2 ((T ⊓ K : Subgroup G)) ∧ ¬ 2 ∣ (T ⊓ K : Subgroup G).relIndex K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) (K ⊔ T) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, T.isPGroup', fun h => T.not_dvd_index ?_⟩
    exact h.trans (relIndex_dvd_index_of_le le_sup_right)
  have h2 := h1.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTK)
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h2
  exact ⟨h2.2.1, h2.2.2⟩

theorem exists_borel (T : Sylow 2 G) {K : Subgroup G}
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) :
    (∃ k : G, k ∈ K ∧ k ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) ∧ k ^ 3 = 1 ∧
      k ∉ pCoreOf 2 K) ∧ ¬ K ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := T ⊓ K with hSdef
  obtain ⟨hS2, hSodd⟩ := sylow_inf_of_le_normalizer T hTK
  have hOS : pCoreOf 2 K ≤ S := le_inf (pCoreOf_le_of_le_normalizer T hTK)
    (by rw [pCoreOf_eq_map_cfsgPCore]; exact map_subtype_le _)
  have hS1 : IsPGroup 2 (S.subgroupOf K) := hS2.comap_of_injective K.subtype K.subtype_injective
  set P1 : Sylow 2 K := hS1.toSylow hSodd with hP1def
  have hP1 : (P1 : Subgroup K) = S.subgroupOf K := IsPGroup.toSylow_coe hS1 hSodd
  set P2 : Sylow 2 (alternatingGroup (Fin 5)) := P1.mapSurjective (kHom_surjective eK)
  have hP2 : (P2 : Subgroup (alternatingGroup (Fin 5))) = (S.subgroupOf K).map (kHom eK) := by
    rw [Sylow.coe_mapSurjective, hP1]
  have hP2card : Nat.card P2 = 4 :=
    nat_card_sylow_two_of_card_sixty SteinbergCB.nat_card_alternating_five P2
  set Sp : Subgroup (Perm (Fin 5)) := (P2 : Subgroup _).map (alternatingGroup (Fin 5)).subtype
  have hSpA : Sp ≤ alternatingGroup (Fin 5) := map_subtype_le _
  have hSpcard : Nat.card Sp = 4 := by
    rw [Subgroup.card_map_of_injective (subtype_injective _), hP2card]
  have hmemSp : ∀ k : K, kBar eK k ∈ Sp ↔ (k : G) ∈ S := by
    intro k
    constructor
    · rintro ⟨a, ha, hak⟩
      rw [hP2] at ha
      obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 ha
      rw [mem_subgroupOf] at hs
      have h1 : kBar eK (s⁻¹ * k) = 1 := by
        rw [map_mul, map_inv, ← hak]
        show ((kHom eK s : Perm (Fin 5)))⁻¹ * (a : Perm (Fin 5)) = 1
        rw [hsa]
        simp
      rw [kBar_eq_one_iff] at h1
      have h2 : ((s⁻¹ * k : K) : G) ∈ S := hOS (by
        rw [pCoreOf_eq_map_cfsgPCore]
        exact ⟨_, h1, rfl⟩)
      have h3 := mul_mem hs h2
      simpa using h3
    · intro hk
      refine ⟨kHom eK k, ?_, rfl⟩
      rw [hP2]
      exact Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hk)
  obtain ⟨c, -, hc⟩ := exists_conj_kleinV0 hSpA hSpcard
  set κ₀ : Perm (Fin 5) := swap 0 1 * swap 1 2 with hκ₀
  set κ : Perm (Fin 5) := c⁻¹ * κ₀ * c with hκ
  have hκA : κ ∈ alternatingGroup (Fin 5) := by
    rw [mem_alternatingGroup, hκ, map_mul, map_mul, map_inv, hκ₀]
    have : sign (swap (0 : Fin 5) 1 * swap 1 2) = 1 := by decide
    rw [this, mul_one, inv_mul_cancel]
  have hκN : ∀ a ∈ Sp, κ * a * κ⁻¹ ∈ Sp := by
    intro a ha
    rw [hc] at ha ⊢
    have := threeCycle_normalizes_kleinV0 _ ha
    rw [show c * (κ * a * κ⁻¹) * c⁻¹ = κ₀ * (c * a * c⁻¹) * κ₀⁻¹ by rw [hκ]; group]
    exact this
  have hκ₀3 : κ₀ * κ₀ * κ₀ = 1 := by
    rw [hκ₀]
    decide
  have hκ3 : κ ^ 3 = 1 := by
    calc κ ^ 3 = c⁻¹ * (κ₀ * κ₀ * κ₀) * c := by rw [hκ, pow_succ, pow_succ, pow_one]; group
      _ = 1 := by rw [hκ₀3, mul_one, inv_mul_cancel]
  have hκ1 : κ ≠ 1 := by
    intro h
    have : κ₀ = 1 := by
      rw [show κ₀ = c * κ * c⁻¹ by rw [hκ]; group, h, mul_one, mul_inv_cancel]
    exact absurd this (by rw [hκ₀]; decide)
  obtain ⟨k₀, hk₀⟩ := kHom_surjective eK ⟨κ, hκA⟩
  have hk₀κ : kBar eK k₀ = κ := congrArg Subtype.val hk₀
  have hκinv : κ⁻¹ = κ * κ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three]
    exact hκ3
  have hκN' : ∀ a ∈ Sp, κ⁻¹ * a * κ⁻¹⁻¹ ∈ Sp := by
    intro a ha
    have h1 := hκN _ (hκN a ha)
    rw [hκinv]
    convert h1 using 1
    group
  have hconj : ∀ k : K, (∀ a ∈ Sp, kBar eK k * a * (kBar eK k)⁻¹ ∈ Sp) →
      ∀ t ∈ S, (k : G) * t * (k : G)⁻¹ ∈ S := by
    intro k hk t ht
    have htK : t ∈ K := (mem_inf.1 ht).2
    have hkt : (k : G) * t * (k : G)⁻¹ ∈ K := mul_mem (mul_mem k.2 htK) (inv_mem k.2)
    have h1 : kBar eK ⟨(k : G) * t * (k : G)⁻¹, hkt⟩ =
        kBar eK k * kBar eK ⟨t, htK⟩ * (kBar eK k)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have h2 := hk _ ((hmemSp ⟨t, htK⟩).2 ht)
    rw [← h1] at h2
    exact (hmemSp _).1 h2
  obtain ⟨k₀, hk₀⟩ := kHom_surjective eK ⟨κ, hκA⟩
  have hk₀κ : kBar eK k₀ = κ := congrArg Subtype.val hk₀
  have hk₀N : (k₀ : G) ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff]
    intro t
    constructor
    · exact hconj k₀ (by rw [hk₀κ]; exact hκN) t
    · intro ht
      have h1 := hconj k₀⁻¹ (by rw [map_inv, hk₀κ]; exact hκN') _ ht
      rwa [Subgroup.coe_inv, inv_inv, show (k₀ : G)⁻¹ * ((k₀ : G) * t * (k₀ : G)⁻¹) * k₀ = t by
        group] at h1
  have hk3 : kBar eK (k₀ ^ 3) = 1 := by rw [map_pow, hk₀κ, hκ3]
  rw [kBar_eq_one_iff] at hk3
  obtain ⟨r, hr⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨k₀ ^ 3, hk3⟩
  have hr' : (k₀ ^ 3) ^ 2 ^ r = 1 := by
    have := congrArg Subtype.val hr
    simpa using this
  refine ⟨⟨((k₀ ^ 2 ^ r : K) : G), (k₀ ^ 2 ^ r).2, ?_, ?_, ?_⟩, ?_⟩
  · rw [SubgroupClass.coe_pow]
    exact pow_mem hk₀N _
  · rw [← SubgroupClass.coe_pow, ← pow_mul, mul_comm, pow_mul, hr']
    rfl
  · intro h
    rw [pCoreOf_eq_map_cfsgPCore] at h
    obtain ⟨y, hy, hyk⟩ := h
    have hyk' : y = k₀ ^ 2 ^ r := Subtype.ext hyk
    have hy2 : k₀ ^ 2 ^ r ∈ CFSG.pCore 2 K := hyk' ▸ hy
    have hy3 := (kBar_eq_one_iff eK _).2 hy2
    rw [map_pow, hk₀κ] at hy3
    have hord : orderOf κ = 3 := orderOf_eq_prime hκ3 hκ1
    have h3 := orderOf_dvd_of_pow_eq_one hy3
    rw [hord] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · intro hKN
    have hnorm : (S.subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_right).2 hKN
    have hP2n : ((S.subgroupOf K).map (kHom eK)).Normal := hnorm.map _ (kHom_surjective eK)
    have hc4 : Nat.card ((S.subgroupOf K).map (kHom eK)) = 4 := hP2 ▸ hP2card
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have := hP2n
    rcases hsimple.eq_bot_or_eq_top_of_normal ((S.subgroupOf K).map (kHom eK)) with h | h
    · rw [h, card_bot] at hc4
      exact absurd hc4 (by norm_num)
    · rw [h, card_top, SteinbergCB.nat_card_alternating_five] at hc4
      exact absurd hc4 (by norm_num)

theorem normalizer_inf_le_of_hStar (T : Sylow 2 G) {M H K : Subgroup G}
    (hH : IsHStar (T : Subgroup G) M H) (hKH : K ≤ H)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hnot : ¬ K ≤ normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    H ⊓ normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ M := by
  by_contra hc
  have hTN : (T : Subgroup G) ≤ H ⊓ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    le_inf hH.1.1 fun t ht => inf_normalizer_le_normalizer_inf ⟨le_normalizer ht, hTK ht⟩
  have h := hH.2.2 _ (inH_of_le T hTN inf_le_left hH.1) inf_le_left hc
  exact hnot (hKH.trans (h ▸ inf_le_right))

theorem card_quot_of_alternating_seven {Q : Type*} [Group Q] [Finite Q]
    (hA7 : Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 7))) :
    Nat.card Q = 2520 * Nat.card (center Q) := by
  obtain ⟨f⟩ := hA7
  rw [card_eq_card_quotient_mul_card_subgroup (center Q), Nat.card_congr f.toEquiv,
    nat_card_alternating_seven]

theorem mem_of_three_element (h1228 : Stmt12_2_8) {T L V : Subgroup G} (hyp : Hyp1223 G T L V)
    (hA7 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)))
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x ∈ L := by
  have hQ := card_quot_of_alternating_seven hA7
  have hZ : 0 < Nat.card (center (↥L ⧸ CFSG.pCore 2 ↥L)) := Nat.card_pos
  rcases h1228 G T L V hyp with h | h | ⟨-, h⟩
  · rw [← h]
    exact subset_closure ⟨hxM, 1, by rw [pow_one]; exact hx3⟩
  · exfalso
    rcases h with he | h
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, SteinbergCB.nat_card_alternating_five] at hQ
      omega
    · obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 h
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two] at hQ
      omega
  · rw [h]
    exact subset_closure ⟨hxM, orderOf_eq_prime hx3 hx1⟩

theorem borel_centralizes (T : Sylow 2 G) {H K : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hKH : K ≤ H) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hV : IsPrimeReduced 2 ((VZ (T : Subgroup G) H).subgroupOf H))
    (hU : IsA5ModuleSum K ⁅VZ (T : Subgroup G) H, K⁆) {k : G} (hkK : k ∈ K)
    (hkN : k ∈ normalizer ((T ⊓ K : Subgroup G) : Set G)) (hk3 : k ^ 3 = 1)
    {z : G} (hz : z ∈ quasithinOmegaOneCenter (T : Subgroup G)) : k * z * k⁻¹ = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set VH := VZ (T : Subgroup G) H with hVH
  obtain ⟨-, hel, -⟩ := hV
  have hZT : quasithinOmegaOneCenter (T : Subgroup G) ≤ T :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).1
  have hZC : quasithinOmegaOneCenter (T : Subgroup G) ≤ centralizer ((T : Subgroup G) : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hZV : quasithinOmegaOneCenter (T : Subgroup G) ≤ VH := le_conjClosure _ _
  have hVHH : VH ≤ H := conjClosure_le fun h hh z hz =>
    mul_mem (mul_mem hh (hTH (hZT hz))) (inv_mem hh)
  have hHN : H ≤ normalizer (VH : Set G) := le_normalizer_conjClosure _ _
  have hsq : ∀ a ∈ VH, a * a = 1 := by
    intro a ha
    have := hel
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := VH.subgroupOf H)
      (⟨a, hVHH ha⟩ : H) (mem_subgroupOf.2 ha)
    rw [← pow_two]
    simpa using congrArg Subtype.val h
  have hcomm : ∀ a ∈ VH, ∀ b ∈ VH, a * b = b * a := by
    intro a ha b hb
    have h := hel.toIsMulCommutative.is_comm.comm (⟨⟨a, hVHH ha⟩, mem_subgroupOf.2 ha⟩ :
      VH.subgroupOf H) ⟨⟨b, hVHH hb⟩, mem_subgroupOf.2 hb⟩
    exact congrArg (fun x : VH.subgroupOf H => ((x : H) : G)) h
  have hUV : ⁅VH, K⁆ ≤ VH := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have h1 : b * a⁻¹ * b⁻¹ ∈ VH := (mem_normalizer_iff.1 (hHN (hKH hb)) _).1 (inv_mem ha)
    have h2 := mul_mem ha h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  obtain ⟨hS2, hSodd⟩ := sylow_inf_of_le_normalizer T hTK
  set u : G := k * z * k⁻¹ * z⁻¹ with hu
  have hzV := hZV hz
  have huU : u ∈ ⁅VH, K⁆ := by
    have h := commutator_mem_commutator hzV hkK
    rw [commutatorElement_def] at h
    have h' := inv_mem h
    rwa [show (z * k * z⁻¹ * k⁻¹)⁻¹ = u by rw [hu]; group] at h'
  have hcz : ∀ t ∈ (T : Subgroup G), t * z * t⁻¹ = z := by
    intro t ht
    rw [mem_centralizer_iff.1 (hZC hz) t ht, mul_inv_cancel_right]
  have huS : ∀ s ∈ (T ⊓ K : Subgroup G), s * u * s⁻¹ = u := by
    intro s hs
    have ht' : k⁻¹ * s * k * s⁻¹ ∈ (T ⊓ K : Subgroup G) := by
      have h1 : k⁻¹ * s * k⁻¹⁻¹ ∈ (T ⊓ K : Subgroup G) :=
        (mem_normalizer_iff.1 (inv_mem hkN) s).1 hs
      rw [inv_inv] at h1
      exact mul_mem h1 (inv_mem hs)
    have hsk : s * k * s⁻¹ = k * (k⁻¹ * s * k * s⁻¹) := by group
    have h1 := hcz s (mem_inf.1 hs).1
    have h2 := hcz _ (mem_inf.1 ht').1
    calc s * u * s⁻¹ = (s * k * s⁻¹) * (s * z * s⁻¹) * (s * k * s⁻¹)⁻¹ * (s * z * s⁻¹)⁻¹ := by
          rw [hu]; group
      _ = k * ((k⁻¹ * s * k * s⁻¹) * z * (k⁻¹ * s * k * s⁻¹)⁻¹) * k⁻¹ * z⁻¹ := by
          rw [hsk, h1]; group
      _ = u := by rw [h2, hu]
  have hku := IsA5ModuleSum.conj_eq_of_fixed hU
    (fun a ha b hb => hcomm a (hUV ha) b (hUV hb)) inf_le_right hS2 hSodd hkK hkN huU huS
  exact conj_eq_of_cube hsq hk3 hzV (hHN (hKH hkK)) hku

end Borel

end CFSG.Quasithin.H13.A7
