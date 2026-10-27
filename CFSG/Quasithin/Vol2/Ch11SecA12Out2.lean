module

public import CFSG.Quasithin.Vol2.Ch11SecA12B
public import CFSG.Quasithin.Vol2.Ch11SecA13Line
public import CFSG.Quasithin.Vol2.Ch11SecA15S5
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem fieldAutPoint_data (hFb : Facts12b) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2)
    (hV₁ : IsVi T L I 2 1 V₁) (hX : IsCartanX T L X) :
    FieldAutPoint (autOn L (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (V₁.subgroupOf (fsuV T I))
      (autOn X (fsuV T I)) := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hP := isSylowTwoOf_P h
  have hU₁ : IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) 4 1
      (V₁.subgroupOf (fsuV T I)) := isFlagW_of_isVi h hV₁
  have hD := isHall_autOn_cartan h1102 h hX
  have hZ := autOn_fix_centralizer L (fsuV T I)
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I 2 h
  rcases hk with ⟨K, _, _, hK, e, π, hπ, -⟩ | ⟨K, _, _, hK, e, π, hπ, -⟩ |
      ⟨K, _, _, hK, e, hnat⟩
  · exact hFb.fieldSL3 K (hK.trans (by norm_num)) _ hsq _ _ π hπ hZ _ hP _ hU₁ _ hD
  · exact hFb.fieldSp4 K (hK.trans (by norm_num)) _ hsq _ _ π hπ hZ _ hP _ hU₁ _ hD
  · obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
    exact hFb.fieldG2 K' (hK'.trans (by norm_num)) _ hsq _ _ π hπ hZ _ hP _ hU₁ _ hD

omit [Finite G] in
theorem conjV_pow_eq_one (V : Subgroup G) {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    {k : ℕ} (hk : a ^ 2 ^ k = 1) : conjV V a ha ^ 2 ^ k = 1 := by
  rw [← conjV_pow]
  ext v
  rw [conjV_apply_coe, hk]
  simp

omit [Finite G] in
theorem conjV_out_eq {V : Subgroup G} {a b c : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hb : b ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.normalizer (V : Set G))
    (hw : a * b * a⁻¹ * (c * b * c⁻¹)⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    conjV V a ha * conjV V b hb * (conjV V a ha)⁻¹ *
      (conjV V c hc * conjV V b hb * (conjV V c hc)⁻¹)⁻¹ = conjV V _ hw := by
  simp only [mul_inv_rev, inv_inv, ← conjV_inv]
  ext v
  simp only [MulAut.mul_apply, conjV_apply_coe]
  group

omit [Finite G] in
theorem conjV_mul4_eq {V : Subgroup G} {a b : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hb : b ∈ Subgroup.normalizer (V : Set G))
    (hw : a * b * a⁻¹ * b ∈ Subgroup.normalizer (V : Set G)) :
    conjV V a ha * conjV V b hb * (conjV V a ha)⁻¹ * conjV V b hb = conjV V _ hw := by
  simp only [← conjV_inv]
  ext v
  simp only [MulAut.mul_apply, conjV_apply_coe]
  group

omit [Finite G] in
theorem conjV_conj_mem_autOn {V A : Subgroup G} {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (htA : t ∈ Subgroup.normalizer (A : Set G))
    {g : MulAut ↥V} (hg : g ∈ autOn A V) : conjV V t htV * g * (conjV V t htV)⁻¹ ∈ autOn A V := by
  obtain ⟨a, ha, haV, rfl⟩ := mem_autOn_iff.mp hg
  rw [← conjV_inv, ← conjV_mul, ← conjV_mul]
  exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp htA a).mp ha) _

theorem isPGroup_of_outer (hFb : Facts12b) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hX : IsCartanX T L X) {t : G} (ht : t ∈ T)
    (hout : ∀ l ∈ LOf L V₁, ∃ y ∈ LOf L V₁,
      t * y * t⁻¹ * (l * y * l⁻¹)⁻¹ ∉ pCoreOf 2 (LOf L V₁))
    {x : G} (hx : x ∈ xOne X (LOf L V₁)) :
    ∃ k : ℕ, (t * x * t⁻¹ * x) ^ 2 ^ k ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := L_le_normalizer_fsuV h
  have hU₁ : V₁ ≤ V := IsVi.le_fsuV hV₁
  have hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [centralizer_eq_pCoreOf h1102 h]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  set L₁ := LOf L V₁ with hL₁
  have hL₁L : L₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hL₁V : L₁ ≤ Subgroup.normalizer (V : Set G) := hL₁L.trans hLV
  have hCL₁ : IsPGroup 2 ↥(L₁ ⊓ Subgroup.centralizer (V : Set G)) :=
    hC.to_le (inf_le_inf_right _ hL₁L)
  have htV : t ∈ Subgroup.normalizer (V : Set G) := T_le_normalizer_fsuV T I ht
  have htL₁ : t ∈ Subgroup.normalizer (L₁ : Set G) :=
    T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₁) ht
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := hLV (hX.1 hx.1).1
  have hΓ : gammaW (autOn L V) (V₁.subgroupOf V) = autOn L₁ V := (SecS.autOn_lOf hLV hU₁).symm
  have hO : pCoreOf 2 (autOn L₁ V) = autOn (pCoreOf 2 L₁) V := (autOn_pCoreOf hL₁V hCL₁).symm
  obtain ⟨k₀, hk₀⟩ := h.fsu.sylow.1 ⟨t, ht⟩
  have hk₀' : t ^ 2 ^ k₀ = 1 := by simpa using congrArg Subtype.val hk₀
  have hd : conjV V x hxV ∈ centW (autOn X V) (gammaW (autOn L V) (V₁.subgroupOf V)) := by
    rw [← SecS.autOn_xOne hLV hU₁
      (cartan_le_normalizer_lOf hN h1102 h (Or.inl rfl) hV₁ hX) hC]
    exact conjV_mem_autOn hx hxV
  have hZ : conjV V t htV ∈ stabW ((Subgroup.centralizer (L : Set G)).subgroupOf V) := by
    rw [mem_stabW]
    intro u
    have hc := Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer
      (h.normal ht)) (u : G)
    simpa [Subgroup.mem_subgroupOf, conjV_apply_coe] using hc
  have hU : conjV V t htV ∈ stabW (V₁.subgroupOf V) :=
    (conjV_mem_stabW_iff hU₁ htV).mpr (IsVi.le_normalizer hV₁ ht)
  have hτout : ∀ γ ∈ gammaW (autOn L V) (V₁.subgroupOf V), ∃ g ∈ gammaW (autOn L V)
      (V₁.subgroupOf V), conjV V t htV * g * (conjV V t htV)⁻¹ * (γ * g * γ⁻¹)⁻¹ ∉
        pCoreOf 2 (gammaW (autOn L V) (V₁.subgroupOf V)) := by
    rw [hΓ, hO]
    intro γ hγ
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hγ
    obtain ⟨y, hy, hyo⟩ := hout l hl
    refine ⟨conjV V y (hL₁V hy), conjV_mem_autOn hy _, fun hmem => hyo ?_⟩
    have hw : t * y * t⁻¹ * (l * y * l⁻¹)⁻¹ ∈ L₁ :=
      L₁.mul_mem ((Subgroup.mem_normalizer_iff.mp htL₁ y).mp hy)
        (L₁.inv_mem (L₁.mul_mem (L₁.mul_mem hl hy) (L₁.inv_mem hl)))
    rw [conjV_out_eq htV (hL₁V hy) hlV (hL₁V hw)] at hmem
    obtain ⟨o, ho, hoV, hoe⟩ := mem_autOn_iff.mp hmem
    have hoL : o ∈ L₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 L₁ ho
    have hc : o⁻¹ * (t * y * t⁻¹ * (l * y * l⁻¹)⁻¹) ∈ L₁ ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨L₁.mul_mem (L₁.inv_mem hoL) hw, SecS.inv_mul_mem_centralizer hoe.symm⟩
    have := (pCoreOf 2 L₁).mul_mem ho (SecS.le_pCoreOf_of_centralizer hL₁V hCL₁ hc)
    rwa [mul_inv_cancel_left] at this
  have key := (fieldAutPoint_data hFb h1102 h hV₁ hX) (conjV V t htV)
    (fun g hg => conjV_conj_mem_autOn htV (h.normal ht) hg) hZ hU
    ⟨k₀, conjV_pow_eq_one V htV hk₀'⟩ hτout _ hd
  have hgV : t * x * t⁻¹ * x ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htV hxV) (Subgroup.inv_mem _ htV))
      hxV
  rw [conjV_mul4_eq htV hxV hgV] at key
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨_, key⟩
  refine ⟨k, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hk2 : conjV V (t * x * t⁻¹ * x) hgV ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hk' := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hk2
  simp only [MulAut.one_apply, conjV_pow_apply_coe] at hk'
  calc v * (t * x * t⁻¹ * x) ^ 2 ^ k
      = (t * x * t⁻¹ * x) ^ 2 ^ k * v * ((t * x * t⁻¹ * x) ^ 2 ^ k)⁻¹ *
          (t * x * t⁻¹ * x) ^ 2 ^ k := by rw [hk']
    _ = (t * x * t⁻¹ * x) ^ 2 ^ k * v := by group

theorem false_of_outer (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    (hKC : K ≤ Subgroup.centralizer (V₁ : Set G))
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
  have hxC : x ^ (2 * 2 ^ k) ∈ xOne X (LOf L V₁) ⊓ Subgroup.centralizer (V₁ : Set G) := by
    refine ⟨pow_mem hxX _, ?_⟩
    have h1 : x ^ (2 * 2 ^ k) = c'⁻¹ * (t * x * t⁻¹ * x) ^ 2 ^ k := by rw [he]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC hc'))
      (Subgroup.centralizer_le (IsVi.le_fsuV hV₁) hk)
  rw [xOne_inf_centralizer hC hF hN h1102 h hV₁ hV₂ hX, Subgroup.mem_bot] at hxC
  have h3 := orderOf_dvd_of_pow_eq_one hxC
  rw [hxo, ← pow_succ'] at h3
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecA
