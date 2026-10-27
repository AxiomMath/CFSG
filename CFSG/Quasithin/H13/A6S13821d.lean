module

public import CFSG.Quasithin.H13.L32AC48b
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.A6S13816b

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def IsList13821 (X : Type) [Group X] : Prop :=
  IsPSL 3 2 1 X ∨ IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X ∨ IsAlt 6 X ∨ IsAlt 7 X ∨ IsPSU 3 3 1 X

theorem IsList13821.list47 {X : Type} [Group X] (h : IsList13821 X) : L32A.C.IsList47 X := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl ⟨3, h⟩
  · exact Or.inl ⟨4, h⟩
  · exact Or.inl ⟨5, h⟩
  · exact Or.inr (Or.inl ⟨6, h⟩)
  · exact Or.inr (Or.inl ⟨7, h⟩)
  · exact Or.inr (Or.inr h)

theorem IsList13821.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsList13821 X) : IsList13821 Y := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl (IsPSL.of_mulEquiv e h)
  · exact Or.inr (Or.inl (IsPSL.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (IsPSL.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (IsAlt.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsAlt.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (IsPSU.of_mulEquiv e h)))))

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem oTwoRes_solvRad_le_L1 (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) : oTwoRes (solvRad H) ≤ S.L1 := by
  set M := Subgroup.normalizer (L : Set G) with hM
  set R := solvRad H with hR
  set Y := oTwoRes R with hY
  have hLT : S.L1 ⊔ T ≤ H := hH.1.1
  have hHR : H ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H)
  have hRM : R ≤ M := by
    have hsol : Group.IsSolvable ↥(R ⊔ (S.L1 ⊔ T)) :=
      C126.isSolvable_sup_of_le_normalizer' (hLT.trans hHR) (solvRad_isSolvable H)
        (S.isSolvable_L1T h1334 hS)
    have hle : R ⊔ (S.L1 ⊔ T) ≤ S.G1 := sup_le ((solvRad_le H).trans hH.2.1) (hLT.trans hH.2.1)
    exact le_sup_left.trans (h13 G T L V S hS _ le_sup_right hle hsol)
  have hYR : Y ≤ R := oTwoRes_le _
  have hYH : Y ≤ H := hYR.trans (solvRad_le H)
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer hHR
  have hYY : oTwoRes Y = Y := by
    refine le_antisymm (oTwoRes_le _) ?_
    rw [hY, oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
    rw [S.zv, Subgroup.mem_bot] at h1
    exact S.z_ne_one h1
  have hYz : Y ≤ M ⊓ Subgroup.centralizer ({S.z} : Set G) :=
    le_inf (hYR.trans hRM) (hYH.trans hH.2.1)
  have hInH : InH T H := ⟨le_sup_right.trans hLT, hH.1.2⟩
  rcases h139 G T L V H Y S.z S.h13 S.irr S.a6 hInH hH.2.2 hYY hYH hHY hz hzL hYz with
    h | ⟨-, hA6, hhat⟩
  · rw [h]
    exact bot_le
  · by_cases hh : IsHatA6 L
    · rw [hhat hh]
      exact S.l1plus_le_L1
    · rw [hA6 (S.nonempty_alt6_of_not_hat hh)]
      exact le_rfl

theorem not_isPGroup_two_L1 : ¬ IsPGroup 2 ↥S.L1 := by
  intro hp
  obtain ⟨g, hgL, hg⟩ := S.exists_L1_c012
  obtain ⟨k, hk⟩ := hp ⟨g, hgL⟩
  have hk' : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h1 : (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 6)) ^ 2 ^ k = 1 := by
    rw [← hg, ← map_pow, hk', map_one]
  have h3 : (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 6)) ^ 3 = 1 := by decide
  have hg : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  have h4 := pow_gcd_eq_one.mpr ⟨h1, h3⟩
  rw [hg, pow_one] at h4
  exact absurd h4 (by decide)

theorem eq_of_mem_cComp_of_L1_le (h37 : A37ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ cComp H) (h₂ : K₂ ∈ cComp H) (hL₁ : S.L1 ≤ K₁)
    (hL₂ : S.L1 ≤ K₂) (hZ : Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = ⊥) : K₁ = K₂ := by
  by_contra hne
  obtain ⟨hc, -⟩ := lemma_1_2_1_two S.h13.qtke S.h13.simple S.h13.nonabelian h37 hH.1.2 h₁ h₂ hne
  have hO : S.L1 ≤ pCoreOf 2 K₁ := by
    intro l hl
    have hl1 : l ∈ K₁ := hL₁ hl
    have hcen : (QuotientGroup.mk (⟨l, hl1⟩ : ↥K₁) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∈
        Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hkl : ⁅k, l⁆ ∈ pCoreOf 2 K₁ :=
        (Subgroup.mem_inf.mp (hc (Subgroup.commutator_mem_commutator hk (hL₂ hl)))).1
      have hkl' : ⁅(⟨k, hk⟩ : ↥K₁), (⟨l, hl1⟩ : ↥K₁)⁆ ∈ CFSG.pCore 2 ↥K₁ := by
        rw [← pCoreOf_subgroupOf_eq K₁, Subgroup.mem_subgroupOf]
        exact hkl
      have h1 : (QuotientGroup.mk ⁅(⟨k, hk⟩ : ↥K₁), (⟨l, hl1⟩ : ↥K₁)⁆ :
          ↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = 1 := (QuotientGroup.eq_one_iff _).mpr hkl'
      have h2 : ⁅(QuotientGroup.mk (⟨k, hk⟩ : ↥K₁) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁),
          (QuotientGroup.mk (⟨l, hl1⟩ : ↥K₁) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁)⁆ = 1 := by
        rw [← h1]
        exact (map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)) _ _).symm
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf_eq K₁,
      Subgroup.mem_subgroupOf] at hcen
    exact hcen
  exact S.not_isPGroup_two_L1 ((pCoreOf_isPGroup 2 K₁).to_le hO)

theorem centralizer_modO2_eq_bot (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (huniq : cComp H = {K})
    (hL1K : S.L1 ≤ K) [hKbn : (modO2Image H K).Normal]
    (hZ : Subgroup.center ↥(modO2Image H K) = ⊥) :
    Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := ↥H ⧸ CFSG.pCore 2 ↥H with hQ
  set Kb := modO2Image H K with hKb
  set C := Subgroup.centralizer (Kb : Set Q) with hCdef
  set π : ↥H →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hCK : C ⊓ Kb = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxK⟩
    have hx : (⟨x, hxK⟩ : ↥Kb) ∈ Subgroup.center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hKmem : K ∈ cComp H := by rw [huniq]; exact Set.mem_singleton K
  have hsolv : Group.IsSolvable ↥C := by
    by_contra hns
    have hn : (C.subgroupOf ⊤).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
      rw [Subgroup.normalizer_eq_top_iff.mpr hCn]
    obtain ⟨K', hK', hK'C⟩ := exists_cComp_le_of_not_solvable le_top hn hns
    rw [L32A.C.cComp_top_eq huniq, Set.mem_singleton_iff] at hK'
    rw [hK'] at hK'C
    have hb : Kb = ⊥ := le_bot_iff.mp (hCK ▸ le_inf hK'C le_rfl)
    exact (modO2Image_mem_cComp hKmem).1 hb
  set Ch := C.comap π with hCh
  have hChn : Ch.Normal := hCn.comap π
  have hOC : CFSG.pCore 2 ↥H ≤ Ch := by
    intro x hx
    show π x ∈ C
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact C.one_mem
  have hChs : Group.IsSolvable ↥Ch := by
    have hP : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
      have := IsPGroup.isNilpotent (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
      infer_instance
    let f : ↥(CFSG.pCore 2 ↥H) →* ↥Ch := Subgroup.inclusion hOC
    let g : ↥Ch →* ↥C := (π.comp Ch.subtype).codRestrict C fun x => x.2
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro x hx
    have hx1 : π x = 1 := congrArg Subtype.val hx
    have hx2 : (x : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hx1
    exact ⟨⟨x, hx2⟩, rfl⟩
  have hChR : Ch.map H.subtype ≤ solvRad H := by
    refine le_solvRad (Subgroup.map_subtype_le _) ?_ ?_
    · rw [map_subtype_subgroupOf']
      exact hChn
    · exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective Ch H.subtype
        H.subtype_injective).toMonoidHom) (Subgroup.equivMapOfInjective Ch H.subtype
        H.subtype_injective).surjective
  have hR := S.oTwoRes_solvRad_le_L1 h139 h1334 h13 hS hH
  have hpow : ∀ c ∈ C, ∃ a : ℕ, c ^ 2 ^ a = 1 := by
    intro c hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) c
    have hxC : x ∈ Ch := hc
    obtain ⟨a, n, hn, hxn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    have hy1 : (x ^ 2 ^ a) ^ n = 1 := by
      rw [← pow_mul, ← hxn, pow_orderOf_eq_one]
    have hyG : ((x ^ 2 ^ a : ↥H) : G) ∈ oTwoRes (solvRad H) :=
      mem_oTwoRes_of_odd (hChR ⟨x ^ 2 ^ a, Ch.pow_mem hxC _, rfl⟩) hn
        (by rw [← Subgroup.coe_pow, hy1, Subgroup.coe_one])
    have hyK : x ^ 2 ^ a ∈ K.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hL1K (hR hyG)
    have hyKb : π (x ^ 2 ^ a) ∈ Kb := ⟨_, hyK, rfl⟩
    have hyC : π (x ^ 2 ^ a) ∈ C := Ch.pow_mem hxC _
    have h1 : π (x ^ 2 ^ a) ∈ C ⊓ Kb := ⟨hyC, hyKb⟩
    rw [hCK, Subgroup.mem_bot, map_pow] at h1
    exact h1
  have h2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨a, ha⟩ := hpow c c.2
    exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow, ha, Subgroup.coe_one])⟩
  have hle : C ≤ CFSG.pCore 2 Q := le_sSup ⟨hCn, h2⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
  exact le_bot_iff.mp hle

theorem eq_sup_T_of_index {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
    [hKbn : (modO2Image H K).Normal] {j : ℕ} (hj : (modO2Image H K).index = 2 ^ j) :
    H = K ⊔ T := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  set Q := ↥H ⧸ CFSG.pCore 2 ↥H with hQ
  set f : ↥H →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hOT : CFSG.pCore 2 ↥H ≤ T.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ pCoreOf 2 H := by
      refine ⟨x, ?_, rfl⟩
      assumption
    exact isSylowTwoOf_pCoreOf_le hTsyl hx'
  have hTidx : (modO2Image H T).index = (T.subgroupOf H).index := by
    refine Subgroup.index_map_eq (T.subgroupOf H) hfs ?_
    rw [QuotientGroup.ker_mk']
    exact hOT
  have hsup : modO2Image H K ⊔ modO2Image H T = ⊤ := by
    have h1 : (modO2Image H K ⊔ modO2Image H T).index ∣ 2 ^ j :=
      hj ▸ Subgroup.index_dvd_of_le le_sup_left
    have h2 : (modO2Image H K ⊔ modO2Image H T).index ∣ (T.subgroupOf H).index :=
      hTidx ▸ Subgroup.index_dvd_of_le le_sup_right
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hi0 : i = 0 := by
      by_contra hi0
      apply hTsyl.2.2
      have h3 : 2 ∣ (modO2Image H K ⊔ modO2Image H T).index := by
        rw [hi]
        exact dvd_pow_self 2 hi0
      exact h3.trans h2
    rw [hi0, pow_zero] at hi
    exact Subgroup.index_eq_one.mp hi
  apply le_antisymm _ (sup_le hKH hTH)
  intro x hx
  have hmem : f ⟨x, hx⟩ ∈ modO2Image H K ⊔ modO2Image H T := hsup ▸ Subgroup.mem_top _
  obtain ⟨y, ⟨k, hk, rfl⟩, z, ⟨t, ht, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hfeq : f (k * t) = f ⟨x, hx⟩ := by
    rw [map_mul]
    exact hyz
  have hq : (k * t)⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥H := by
    rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hfeq
    exact hfeq
  have hqT : ((k * t)⁻¹ * ⟨x, hx⟩ : ↥H) ∈ T.subgroupOf H := hOT hq
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk ht
  rw [Subgroup.mem_subgroupOf] at hqT
  have e : x = (k : G) * ((t : G) * (((k * t)⁻¹ * ⟨x, hx⟩ : ↥H) : G)) := by
    simp [mul_assoc]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_right hqT))

end Setting4

end CFSG.Quasithin.H13.A6
