module

public import CFSG.Quasithin.EmptyFaithful.R3c16ReeA
public import CFSG.Quasithin.EmptyFaithful.R3c11L3b

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup.X6

section StepB

variable {G : Type*} [Group G]

theorem centralizes_of_mem_sup_perfect {M U L V : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hV4 : Nat.card V = 4) (hU2 : IsPGroup 2 ↥U)
    (hUM : U ≤ M) (hLM : L ≤ M) (hL : Group.IsPerfect ↥L) {y : G} (hy : y ∈ U ⊔ L) {k : ℕ}
    (hk : y ^ (3 ^ k) = 1) : ∀ v ∈ V, y * v = v * y := by
  classical
  have hVfin : Finite ↥V := Nat.finite_of_card_ne_zero (by omega)
  let ρ : ↥M →* MulAut ↥V := (Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hMV)
  have hρ : ∀ (g : ↥M) (v : ↥V), ((ρ g v : ↥V) : G) = (g : G) * (v : G) * (g : G)⁻¹ :=
    fun g v => Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion hMV g) v
  have hsolv : Group.IsSolvable (MulAut ↥V) := by
    have hP : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hV4.le
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥V)
      (fun a b h => MulEquiv.ext fun x => Equiv.congr_fun h x)
  have hL1 : ∀ l : ↥L, ρ (Subgroup.inclusion hLM l) = 1 := by
    set ρL : ↥L →* MulAut ↥V := ρ.comp (Subgroup.inclusion hLM) with hρL
    have := hL
    have := hsolv
    have hrange : ρL.range = ⊥ := by
      by_contra hne
      have : Nontrivial ↥ρL.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      have : Group.IsPerfect ↥ρL.range := Group.IsPerfect.range ρL
      exact Group.IsPerfect.not_isSolvable ↥ρL.range inferInstance
    intro l
    have : ρL l ∈ ρL.range := ⟨l, rfl⟩
    rw [hrange, Subgroup.mem_bot] at this
    exact this
  have hyM : y ∈ M := (sup_le hUM hLM) hy
  set y' : ↥M := ⟨y, hyM⟩ with hy'
  have hy'mem : y' ∈ (U ⊔ L).subgroupOf M := hy
  rw [Subgroup.subgroupOf_sup hUM hLM] at hy'mem
  have hLker : ∀ x ∈ L.subgroupOf M, ρ x = 1 := fun x hx => hL1 ⟨(x : G), hx⟩
  have hmem : ρ y' ∈ (U.subgroupOf M).map ρ := by
    have h1 : ρ y' ∈ (U.subgroupOf M ⊔ L.subgroupOf M).map ρ := Subgroup.mem_map_of_mem ρ hy'mem
    rw [Subgroup.map_sup] at h1
    have h2 : (L.subgroupOf M).map ρ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [hLker x hx]
      exact Subgroup.one_mem _
    rwa [h2, sup_bot_eq] at h1
  have hU'2 : IsPGroup 2 ↥(U.subgroupOf M) := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM).symm
  have hρU2 : IsPGroup 2 ↥((U.subgroupOf M).map ρ) := hU'2.map ρ
  have hρy3 : (ρ y') ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    have : y' ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hρy1 : ρ y' = 1 := eq_one_of_isPGroup_two_of_threePow hρU2 hmem hρy3
  intro v hv
  have h3 := hρ y' ⟨v, hv⟩
  rw [hρy1, MulAut.one_apply] at h3
  calc y * v = (y * v * y⁻¹) * y := by group
    _ = v * y := by rw [← h3]

end StepB

section StepC

theorem noThreeAct_gamma
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Type} [Group X]
    (φ : X ≃* ↥(F4.reeGamma K a)) {T V : Subgroup X} (hT2 : IsPGroup 2 ↥T)
    (hφ : T.map φ.toMonoidHom =
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
    (hVT : V ≤ T) (hV4 : Nat.card V = 4) (hTV : T ≤ Subgroup.normalizer (V : Set X)) {y : X}
    (hyV : y ∈ Subgroup.normalizer (V : Set X)) {k : ℕ} (hk : y ^ (3 ^ k) = 1) :
    ∀ v ∈ V, y * v = v * y := by
  classical
  by_cases hy1 : y = 1
  · intro v _
    rw [hy1, one_mul, mul_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUΓ : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUN : (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) ≤
      Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
        Set ↥(F4.reeGamma K a)) := by
    rw [← hφ]
    rintro _ ⟨t, ht, rfl⟩
    exact (R3c11.mem_normalizer_map_equiv_iff φ V t).mpr (hTV ht)
  have hyN : φ y ∈ Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
      Set ↥(F4.reeGamma K a)) := (R3c11.mem_normalizer_map_equiv_iff φ V y).mpr hyV
  have hV₁U : V.map φ.toMonoidHom ≤
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) := hφ ▸ Subgroup.map_mono hVT
  have hV₁4 : Nat.card (V.map φ.toMonoidHom) = 4 := by
    rw [← hV4]
    exact (Nat.card_congr (V.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm
  have hU₁2 : IsPGroup 2 ↥((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) :=
    hφ ▸ hT2.map φ.toMonoidHom
  have hN1 : Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
      Set ↥(F4.reeGamma K a)) ≠ ⊤ := by
    intro htop
    have hnorm : (V.map φ.toMonoidHom).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
    obtain ⟨-, ⟨PV, hPV⟩, hUV, -⟩ := large_Ree_Sylow_opposition F4 a K w₀ hw₀
    have hV₁2 : IsPGroup 2 ↥(V.map φ.toMonoidHom) := hU₁2.to_le hV₁U
    have hle : V.map φ.toMonoidHom ≤ (PV : Subgroup ↥(F4.reeGamma K a)) :=
      hV₁2.le_sylow_of_normal PV
    rw [hPV] at hle
    have hbot : V.map φ.toMonoidHom ≤ ⊥ := by
      intro x hx
      have hxU : (x : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a := hV₁U hx
      have hxV : (x : ModGL F4.tag K) ∈ F4.reeFixedNegUnipotent K a := hle hx
      have : (x : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a ⊓ F4.reeFixedNegUnipotent K a :=
        ⟨hxU, hxV⟩
      rw [hUV, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have h1 : Nat.card (V.map φ.toMonoidHom) = 1 := by
      have : V.map φ.toMonoidHom = ⊥ := le_bot_iff.1 hbot
      rw [this]
      exact Subgroup.card_bot
    omega
  have hMΓ : (Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
      Set ↥(F4.reeGamma K a))).map (F4.reeGamma K a).subtype ≤ F4.reeGamma K a :=
    Subgroup.map_subtype_le _
  have hUM : F4.reeFixedPosUnipotent K a ≤
      (Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
        Set ↥(F4.reeGamma K a))).map (F4.reeGamma K a).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hUΓ]
    exact Subgroup.map_mono hUN
  have hMne : (Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
      Set ↥(F4.reeGamma K a))).map (F4.reeGamma K a).subtype ≠ F4.reeGamma K a := by
    intro h
    apply hN1
    apply Subgroup.map_injective (F4.reeGamma K a).subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact h
  have hyM : ((φ y : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ∈
      (Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
        Set ↥(F4.reeGamma K a))).map (F4.reeGamma K a).subtype :=
    Subgroup.mem_map_of_mem (F4.reeGamma K a).subtype hyN
  have hφk : (φ y) ^ (3 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hk' : ((φ y : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ^ (3 ^ k) = 1 := by
    have := congrArg (fun z : ↥(F4.reeGamma K a) => (z : ModGL F4.tag K)) hφk
    simpa using this
  have hy1' : ((φ y : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ≠ 1 := by
    intro h
    apply hy1
    apply φ.injective
    apply Subtype.ext
    simpa using h
  obtain ⟨j, hyj, hjM, hperf⟩ :=
    ree_threeElement_mem_sup_block ha hK hMΓ hUM hMne hyM hk' hy1'
  have hLΓ : F4.reeLocalBlock K a j ≤ F4.reeGamma K a := hjM.trans hMΓ
  have hyUL : φ y ∈ (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) ⊔
      (F4.reeLocalBlock K a j).subgroupOf (F4.reeGamma K a) := by
    rw [← Subgroup.subgroupOf_sup hUΓ hLΓ]
    exact hyj
  have hLN : (F4.reeLocalBlock K a j).subgroupOf (F4.reeGamma K a) ≤
      Subgroup.normalizer ((V.map φ.toMonoidHom : Subgroup ↥(F4.reeGamma K a)) :
        Set ↥(F4.reeGamma K a)) := by
    intro l hl
    have hlM : (l : ModGL F4.tag K) ∈ (Subgroup.normalizer ((V.map φ.toMonoidHom :
        Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a))).map
          (F4.reeGamma K a).subtype := hjM hl
    obtain ⟨n, hn, hnl⟩ := hlM
    have : n = l := Subtype.ext hnl
    rw [← this]
    exact hn
  have hL₁perf : Group.IsPerfect ↥((F4.reeLocalBlock K a j).subgroupOf (F4.reeGamma K a)) := by
    have := hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLΓ).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have key := centralizes_of_mem_sup_perfect (V := V.map φ.toMonoidHom) le_rfl hV₁4
    hU₁2 hUN hLN hL₁perf hyUL hφk
  intro v hv
  apply φ.injective
  rw [map_mul, map_mul]
  exact key (φ v) ⟨v, hv, rfl⟩

theorem noThreeAct_ree
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f)
    {T V : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hVT : V ≤ T) (hV4 : Nat.card V = 4)
    (hTV : T ≤ Subgroup.normalizer (V : Set X)) {y : X}
    (hyV : y ∈ Subgroup.normalizer (V : Set X)) {k : ℕ} (hk : y ^ (3 ^ k) = 1) :
    ∀ v ∈ V, y * v = v * y := by
  obtain ⟨a, K, hKF, hKFin, hcp, φ, ha, hfa, hK, hφ, -, -⟩ :=
    even_rank_two_residual_largeRee hX hT
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  exact noThreeAct_gamma ha hK' φ (K1.isSylowTwoOf_top_iff.mp hT).1 hφ hVT hV4 hTV hyV hk

end StepC

end CFSG.Quasithin.R3c16
