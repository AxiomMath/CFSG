module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUP2
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2
public import CFSG.Quasithin.Vol2.Ch11SecQ9bJ1
public import CFSG.Quasithin.Vol2.Ch11SecSPGL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem exists_outer_point (hFb : Facts12b) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) {V₀ : Subgroup G}
    (hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (V₀ : Set G)))
    (hNK : Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K)
    (hS : IsPSL 2 5 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSLEps3 true 5 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsPSLEps3 true 5 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSLEps3 false 5 1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ t ∈ T ⊓ K, ∀ l ∈ LOf L V₁, ∃ y ∈ LOf L V₁,
      t * y * t⁻¹ * (l * y * l⁻¹)⁻¹ ∉ pCoreOf 2 (LOf L V₁) := by
  have hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTV₀)
      (le_of_mem_cComp hK) hNK
  have hTL₁ : T ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₁)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
  obtain ⟨e₁⟩ := modO2Image_quotEquiv hLK
  obtain ⟨r, hr, hrout⟩ := hFb.outer _ hS (modO2Image K (T ⊓ K)) (modO2Image K (LOf L V₁))
    (isSylowTwoOf_modO2Image hSyl) (modO2Image_le_normalizer (inf_le_left.trans hTL₁))
    (modO2Image_perfect hLK (perfectCore_perfect _))
    ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩
  obtain ⟨t', ht', rfl⟩ := hr
  refine ⟨t', Subgroup.mem_subgroupOf.mp ht', fun l hl => ?_⟩
  obtain ⟨y, hy, hyout⟩ := hrout _ ⟨⟨l, hLK hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hmem => hyout ?_⟩
  apply modO2Image_pCoreOf_le hLK
  refine ⟨t' * y' * t'⁻¹ * (⟨l, hLK hl⟩ * y' * (⟨l, hLK hl⟩ : ↥K)⁻¹)⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
  · simp

theorem false_of_outer_point (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    {V₀ : Subgroup G} (hV₀V : V₀ ≤ fsuV T I)
    (hXC₀ : xOne X (LOf L V₁) ⊓ Subgroup.centralizer (V₀ : Set G) = ⊥)
    (hKC : K ≤ Subgroup.centralizer (V₀ : Set G))
    (hXK : xOne X (LOf L V₁) ≤ Subgroup.normalizer (K : Set G)) {t : G} (ht : t ∈ T ⊓ K)
    (hout : ∀ l ∈ LOf L V₁, ∃ y ∈ LOf L V₁,
      t * y * t⁻¹ * (l * y * l⁻¹)⁻¹ ∉ pCoreOf 2 (LOf L V₁)) : False := by
  have hX1card := card_xOne hC hF hN h1102 h hV₁ hV₂ hX
  obtain ⟨x, hxX, -, hxo⟩ := exists_orderOf_eq_of_dvd Nat.prime_three hX1card (by norm_num)
  obtain ⟨k, hk⟩ := isPGroup_of_outer hFb hN h1102 h hV₁ hX ht.1 hout hxX
  have hxK := hXK hxX
  have hc : t * (x * t⁻¹ * x⁻¹) ∈ K :=
    K.mul_mem ht.2 ((Subgroup.mem_normalizer_iff.mp hxK _).mp (K.inv_mem ht.2))
  have hpow : ∀ m : ℕ, ∃ c' ∈ K, (t * x * t⁻¹ * x) ^ m = c' * x ^ (2 * m) := by
    intro m
    induction m with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨c', hc', he⟩ := ih
      refine ⟨c' * (x ^ (2 * m) * (t * (x * t⁻¹ * x⁻¹)) * (x ^ (2 * m))⁻¹),
        K.mul_mem hc' ((Subgroup.mem_normalizer_iff.mp (pow_mem hxK _) _).mp hc), ?_⟩
      rw [pow_succ, he, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
      group
  obtain ⟨c', hc', he⟩ := hpow (2 ^ k)
  have hxC : x ^ (2 * 2 ^ k) ∈ xOne X (LOf L V₁) ⊓ Subgroup.centralizer (V₀ : Set G) := by
    refine ⟨pow_mem hxX _, ?_⟩
    have h1 : x ^ (2 * 2 ^ k) = c'⁻¹ * (t * x * t⁻¹ * x) ^ 2 ^ k := by rw [he]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC hc'))
      (Subgroup.centralizer_le hV₀V hk)
  rw [hXC₀, Subgroup.mem_bot] at hxC
  have h3 := orderOf_dvd_of_pow_eq_one hxC
  rw [hxo, ← pow_succ'] at h3
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem false_of_outerList_point (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12)
    (hF11 : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2)
    (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    {V₀ : Subgroup G} (hV₀₁ : V₀ ≤ V₁) (hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G))
    (hXV₀ : xOne X (LOf L V₁) ≤ Subgroup.normalizer (V₀ : Set G))
    (hXC₀ : xOne X (LOf L V₁) ⊓ Subgroup.centralizer (V₀ : Set G) = ⊥)
    (hK : K ∈ cComp (Subgroup.normalizer (V₀ : Set G)))
    (hNK : Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K)
    (hS : IsPSL 2 5 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSLEps3 true 5 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsPSLEps3 true 5 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSLEps3 false 5 1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    False := by
  obtain ⟨t, ht, hout⟩ := exists_outer_point hFb hN h1102 h hV₁ hTV₀ hK hNK hLK hS
  exact false_of_outer_point hFb hC hF hN h1102 h hV₁ hV₂ hX
    (hV₀₁.trans (IsVi.le_fsuV hV₁)) hXC₀ (le_centralizer_point hF11 hN h1102 h hV₁ hV₀₁ hK hLK)
    (hXV₀.trans hNK) ht hout

theorem false_of_rank3_point (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12)
    (hF11 : Facts11) (hN : NatFacts) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X) {V₀ : Subgroup G} (hV₀₁ : V₀ ≤ V₁)
    (hV₀ : V₀ ≠ ⊥) (hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G))
    (hXV₀ : xOne X (LOf L V₁) ≤ Subgroup.normalizer (V₀ : Set G))
    (hXC₀ : xOne X (LOf L V₁) ⊓ Subgroup.centralizer (V₀ : Set G) = ⊥)
    (hK : K ∈ cComp (Subgroup.normalizer (V₀ : Set G)))
    (hNK : Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₁ < K)
    (hS : IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 7)) ∨
      IsSporadic .M22 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSporadic .J2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsSporadic .J4 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSporadic .HS (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsSporadic .Ru (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSLEps3 false 5 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsPSLEps3 false 5 1 (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  obtain ⟨hQ, hZ, hrk, hL3⟩ := hFb.list3.1 _ hS
  obtain ⟨s, p, e, hp, he, hP⟩ := isPSLEps3_point hC hF hF11 hN h318 h36 h38 h1102 h hV₁ hV₂ hX
    hV₀₁ hV₀ hXV₀ hXC₀ hK hNK hlt hQ hZ hrk
  obtain ⟨rfl, rfl, rfl⟩ := hL3 s p e hp he hP
  exact false_of_outerList_point hFb hC hF hF11 hN h1102 h hV₁ hV₂ hX hV₀₁ hTV₀ hXV₀ hXC₀ hK hNK
    hlt.le (Or.inr (Or.inr (Or.inr hP)))

theorem le_normalizer_of_J1_T (hFb : Facts12b) (h331 : Stmt3_3_1) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hTN : T ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K) (hJ : IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    K ≤ Subgroup.normalizer (L : Set G) := by
  set H := K ⊔ T with hH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTN)
  have hSn : (modO2Image H K).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := modO2Image_equiv le_sup_left hKn
  obtain ⟨j⟩ := hJ
  have hSJ : IsSporadic .J1 ↥(modO2Image H K) := ⟨e.symm.trans j⟩
  have hTsyl : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hL₁H : LOf L V₁ ≤ H := hLK.trans le_sup_left
  have hJ1 := hFb.j1 _ (modO2Image H K) (modO2Image H T) (modO2Image H (LOf L V₁)) hSn hSJ
    (isSylowTwoOf_modO2Image hTsyl)
    (Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
      (hLK (Subgroup.mem_subgroupOf.mp hy)))
    (modO2Image_ne_bot hL₁H (perfectCore_perfect _) (lOf_ne_bot hN h1102 h hV₁ (Or.inl rfl)))
    (modO2Image_perfect hL₁H (perfectCore_perfect _))
    (modO2Image_le_normalizer (T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₁)))
  set A := Subgroup.normalizer (L : Set G) ⊓ H with hA
  have hL₁M : LOf L V₁ ≤ Subgroup.normalizer (L : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hBA : modO2Image H (LOf L V₁) ≤ modO2Image H A :=
    Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
      ⟨hL₁M (Subgroup.mem_subgroupOf.mp hy), hL₁H (Subgroup.mem_subgroupOf.mp hy)⟩
  have hNA : Subgroup.normalizer (modO2Image H T : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      modO2Image H A := by
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨g, Subgroup.mem_subgroupOf.mpr
      ⟨normalizer_T_le h331 h (mem_normalizer_of_mk_mem_normalizer le_sup_right hOT hq), g.2⟩,
      rfl⟩
  have hSA := hJ1.trans (sup_le hBA hNA)
  intro k hk
  have hkH : k ∈ H := Subgroup.mem_sup_left hk
  have hk' : k ∈ ((modO2Image H A).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
      H.subtype := ⟨⟨k, hkH⟩, hSA ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
  rw [map_comap_modO2Image inf_le_right] at hk'
  exact (sup_le inf_le_left (hOT.trans h.normal)) hk'

theorem false_of_J1_point (hFb : Facts12b) (hF11 : Facts11) (h331 : Stmt3_3_1)
    (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    {V₀ : Subgroup G} (hV₀₁ : V₀ ≤ V₁) (hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G))
    (hLV₀ : L ⊓ Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (V₁ : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (V₀ : Set G)))
    (hNK : Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₁ < K) (hJ : IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K)) : False :=
  not_le_normalizer_point hF11 hN h1102 h hV₁ hV₀₁ hLV₀ hK hlt
    (le_normalizer_of_J1_T hFb h331 hN h1102 h hV₁ (hTV₀.trans hNK) hlt.le hJ)

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
