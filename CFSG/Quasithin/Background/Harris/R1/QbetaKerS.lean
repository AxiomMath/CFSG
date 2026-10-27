module

public import CFSG.Quasithin.Background.Harris.R1.Split
public import CFSG.Quasithin.Background.Harris.R1.PermHom
public import CFSG.Quasithin.Recognition.SzR1Prep

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7
  CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem ker_theta_eq (hL24 : IsL2Quot 2 (OTwoQuot K1)) (θ : ↥K1 →* A5)
    (hs : Function.Surjective θ) : θ.ker = CFSG.Open.pCore 2 ↥K1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := hL24
  obtain ⟨e2⟩ := F112J2.nonempty_psl_four_equiv_alt5
  let e : OTwoQuot K1 ≃* A5 := e1.trans e2
  have hNn : (CFSG.Open.pCore 2 ↥K1).Normal := CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := ↥K1)
  have hN2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥K1) := CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥K1)
  have hle : CFSG.Open.pCore 2 ↥K1 ≤ θ.ker := by
    have hmapn : ((CFSG.Open.pCore 2 ↥K1).map θ).Normal := hNn.map θ hs
    have hsimple : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.Open.pCore 2 ↥K1).map θ) with hb | ht
    · intro x hx
      have : θ x ∈ (CFSG.Open.pCore 2 ↥K1).map θ := Subgroup.mem_map_of_mem θ hx
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hp : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥K1).map θ) :=
        hN2.of_surjective (θ.subgroupMap _) (θ.subgroupMap_surjective _)
      rw [ht] at hp
      have hp' : IsPGroup 2 A5 := hp.of_equiv Subgroup.topEquiv
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp'
      rw [A5Model.card_A5] at hn
      have hn6 : n < 6 := by
        by_contra hcon
        have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases n <;> omega
  have hidx1 : (CFSG.Open.pCore 2 ↥K1).index = 60 := by
    rw [Subgroup.index, Nat.card_congr e.toEquiv]
    exact A5Model.card_A5
  have hidx2 : θ.ker.index = 60 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs, Subgroup.card_top]
    exact A5Model.card_A5
  have hpos : 0 < Nat.card ↥K1 := Nat.card_pos
  have h1 := Subgroup.index_mul_card (CFSG.Open.pCore 2 ↥K1)
  have h2 := Subgroup.index_mul_card θ.ker
  rw [hidx1] at h1
  rw [hidx2] at h2
  have hc : Nat.card ↥θ.ker ≤ Nat.card ↥(CFSG.Open.pCore 2 ↥K1) := by omega
  exact (Subgroup.eq_of_le_of_card_ge hle hc).symm

theorem kerM_le_pCore (C : FamCtx K1 L2 S Zs Ω)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1) :
    C.kerM ≤ pCoreOf 2 (K1 ⊔ S) := by
  have hS2 : IsPGroup 2 ↥S := C.amalgamHypV.sylow₁.2.1
  have hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) :=
    sup_le Subgroup.le_normalizer C.hSK
  have hD2 : ∀ g : ↥(K1 ⊔ S), permHom C g = 1 → ∃ n : ℕ, (g : G) ^ 2 ^ n = 1 := by
    intro g hg
    obtain ⟨a, ha⟩ := SplitAux.exists_pow_two_mem hS2 hN g.2
    have hmem : (g : G) ^ 2 ^ a ∈ K1 ⊔ S := (K1 ⊔ S).pow_mem g.2 _
    have hker1 : (⟨(g : G) ^ 2 ^ a, hmem⟩ : ↥(K1 ⊔ S)) ∈ (permHom C).ker := by
      have : (⟨(g : G) ^ 2 ^ a, hmem⟩ : ↥(K1 ⊔ S)) = g ^ 2 ^ a := rfl
      rw [MonoidHom.mem_ker, this, map_pow, hg, one_pow]
    have hk1 : permHom C ⟨(g : G) ^ 2 ^ a, hmem⟩ = 1 := hker1
    have hact : C.D.act ⟨(g : G) ^ 2 ^ a, ha⟩ = 1 := by
      rw [← permHom_K1 C]
      exact hk1
    have hx' : (g : G) ^ 2 ^ a ∈ pCoreOf 2 K1 := hker _ hact
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K1 ⟨(g : G) ^ 2 ^ a, hx'⟩
    have hb' : ((g : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    exact ⟨a + b, by rw [pow_add, pow_mul, hb']⟩
  intro x hx
  have hxH : x ∈ K1 ⊔ S := C.kerM_le_sup hx
  have hφ : permHom C ⟨x, hxH⟩ = 1 := (permHom_eq_one_iff C ⟨x, hxH⟩).2 hx
  exact SplitAux.ker_le_pCore_of (permHom C) hD2 hxH hφ

theorem kerM_le_S (C : FamCtx K1 L2 S Zs Ω)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1) : C.kerM ≤ S :=
  (kerM_le_pCore C hker).trans (isSylowTwoOf_pCoreOf_le C.amalgamHypV.sylow₂)

end CFSG.Quasithin.Background.Harris.R1
