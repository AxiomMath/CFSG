module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvPair
public import CFSG.Quasithin.Vol2.Ch10SecQ34LE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {Kc X : Subgroup G} {Q₁ Q₂ : Type} [Group Q₁]
  [Group Q₂] [Finite Q₁] [Finite Q₂]

theorem inl_mem_map_pCoreOf {φ : ↥Kc →* Q₁ × Q₂} (hφ : Function.Surjective φ)
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) {S : Subgroup G} (hS : IsSylowTwoOf S Kc)
    (hXK : X ≤ Kc) {u : Q₁}
    (hu : u ∈ pCoreOf 2 ((X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) ⊔
        (S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ))) :
    (u, (1 : Q₂)) ∈ ((pCoreOf 2 (X ⊔ S)).subgroupOf Kc).map φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ₁ := (MonoidHom.fst Q₁ Q₂).comp φ with hφ₁
  set Y₁ := (X.subgroupOf Kc).map φ₁ with hY₁
  set S₁ := (S.subgroupOf Kc).map φ₁ with hS₁
  set U := pCoreOf 2 (Y₁ ⊔ S₁) with hU
  obtain ⟨hSyl₁, -, hprod⟩ := map_sylow_eq_prod hφ hS
  have hUS : U ≤ S₁ := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
    (A4.isSylowTwoOf_mono hSyl₁ le_sup_right le_top)
  set V : Subgroup G := (X ⊔ S) ⊓ (((U.prod ⊥).comap φ).map Kc.subtype) with hV
  have hV2 : IsPGroup 2 ↥V := by
    rintro ⟨_, -, ⟨k, hk, rfl⟩⟩
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Y₁ ⊔ S₁)) ⟨(φ k).1, hk.1⟩
    have hk2 : (φ k).2 = 1 := Subgroup.mem_bot.mp hk.2
    have hφa : φ (k ^ 2 ^ a) = 1 := by
      rw [map_pow]
      refine Prod.ext ?_ ?_
      · simpa using congrArg Subtype.val ha
      · simp [hk2]
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kc) ⟨_, hker _ hφa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((k : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    change (k : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact hb'
  have hM : X ⊔ S ≤ ((Y₁ ⊔ S₁).comap φ₁).map Kc.subtype := by
    refine sup_le (fun x hx => ?_) fun x hx => ?_
    · exact ⟨⟨x, hXK hx⟩, Subgroup.mem_sup_left ⟨⟨x, hXK hx⟩, hx, rfl⟩, rfl⟩
    · exact ⟨⟨x, hS.1 hx⟩, Subgroup.mem_sup_right ⟨⟨x, hS.1 hx⟩, hx, rfl⟩, rfl⟩
  have hNV : X ⊔ S ≤ Subgroup.normalizer (V : Set G) := by
    intro g hg
    refine C10P34.mem_normalizer_of_forall_conj_mem fun v hv => ?_
    obtain ⟨hvXS, ⟨k, hk, rfl⟩⟩ := hv
    obtain ⟨g', hg', rfl⟩ := hM hg
    refine ⟨(X ⊔ S).mul_mem ((X ⊔ S).mul_mem hg hvXS) ((X ⊔ S).inv_mem hg),
      ⟨g' * k * g'⁻¹, ?_, rfl⟩⟩
    show φ (g' * k * g'⁻¹) ∈ U.prod ⊥
    rw [map_mul, map_mul, map_inv]
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_mul, Prod.fst_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₁ ⊔ S₁) hg') _).mp hk.1
    · simp only [Prod.snd_mul, Prod.snd_inv]
      rw [Subgroup.mem_bot.mp hk.2, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hVW : V ≤ pCoreOf 2 (X ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hNV hV2
  have hu1 : (u, (1 : Q₂)) ∈ (S.subgroupOf Kc).map φ := by
    rw [hprod]
    exact ⟨hUS hu, Subgroup.one_mem _⟩
  obtain ⟨k, hk, hku⟩ := hu1
  have hkV : (k : G) ∈ V := by
    refine ⟨Subgroup.mem_sup_right hk, ⟨k, ?_, rfl⟩⟩
    show φ k ∈ U.prod ⊥
    rw [hku]
    exact ⟨hu, Subgroup.mem_bot.mpr rfl⟩
  exact ⟨k, hVW hkV, hku⟩

omit [Finite Q₂] in
theorem pCoreOf_map_fst_eq_bot {φ : ↥Kc →* Q₁ × Q₂}
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc)
    (hO : ∀ k : ↥Kc, (k : G) ∈ pCoreOf 2 Kc → φ k = 1) (hXK : X ≤ Kc)
    (hprod : (X.subgroupOf Kc).map φ = ((X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ)).prod
      ((X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)))
    (hbad : pCoreOf 2 X ≤ pCoreOf 2 Kc) :
    pCoreOf 2 ((X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ₁ := (MonoidHom.fst Q₁ Q₂).comp φ with hφ₁
  set Y₁ := (X.subgroupOf Kc).map φ₁ with hY₁
  set U := pCoreOf 2 Y₁ with hU
  set V : Subgroup G := X ⊓ (((U.prod ⊥).comap φ).map Kc.subtype) with hV
  have hV2 : IsPGroup 2 ↥V := by
    rintro ⟨_, -, ⟨k, hk, rfl⟩⟩
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₁) ⟨(φ k).1, hk.1⟩
    have hk2 : (φ k).2 = 1 := Subgroup.mem_bot.mp hk.2
    have hφa : φ (k ^ 2 ^ a) = 1 := by
      rw [map_pow]
      refine Prod.ext ?_ ?_
      · simpa using congrArg Subtype.val ha
      · simp [hk2]
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kc) ⟨_, hker _ hφa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((k : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    change (k : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact hb'
  have hNV : X ≤ Subgroup.normalizer (V : Set G) := by
    intro g hg
    refine C10P34.mem_normalizer_of_forall_conj_mem fun v hv => ?_
    obtain ⟨hvX, ⟨k, hk, rfl⟩⟩ := hv
    have hg' : φ₁ ⟨g, hXK hg⟩ ∈ Y₁ := ⟨⟨g, hXK hg⟩, hg, rfl⟩
    refine ⟨X.mul_mem (X.mul_mem hg hvX) (X.inv_mem hg),
      ⟨⟨g, hXK hg⟩ * k * ⟨g, hXK hg⟩⁻¹, ?_, rfl⟩⟩
    show φ (⟨g, hXK hg⟩ * k * ⟨g, hXK hg⟩⁻¹) ∈ U.prod ⊥
    rw [map_mul, map_mul, map_inv]
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_mul, Prod.fst_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁ hg') _).mp hk.1
    · simp only [Prod.snd_mul, Prod.snd_inv]
      rw [Subgroup.mem_bot.mp hk.2, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hVO : V ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hNV hV2
  refine eq_bot_iff.mpr fun u hu => ?_
  have hu1 : (u, (1 : Q₂)) ∈ (X.subgroupOf Kc).map φ := by
    rw [hprod]
    exact ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 Y₁ hu, Subgroup.one_mem _⟩
  obtain ⟨k, hk, hku⟩ := hu1
  have hkV : (k : G) ∈ V := by
    refine ⟨hk, ⟨k, ?_, rfl⟩⟩
    show φ k ∈ U.prod ⊥
    rw [hku]
    exact ⟨hu, Subgroup.mem_bot.mpr rfl⟩
  have h1 : φ k = 1 := hO k (hbad (hVO hkV))
  rw [hku] at h1
  exact Subgroup.mem_bot.mpr (congrArg Prod.fst h1)

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
