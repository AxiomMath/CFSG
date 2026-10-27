module

public import CFSG.Quasithin.Vol2.Ch10SecE9B
public import CFSG.Quasithin.Vol2.Ch10SecE9C
public import CFSG.Quasithin.Vol2.Ch10SecQ34LK

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

section Snd

variable {G : Type} [Group G] [Finite G] {Kc X : Subgroup G} {Q₁ Q₂ : Type} [Group Q₁]
  [Group Q₂] [Finite Q₁] [Finite Q₂]

omit [Finite Q₁] in
theorem pCoreOf_map_snd_eq_bot {φ : ↥Kc →* Q₁ × Q₂}
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc)
    (hO : ∀ k : ↥Kc, (k : G) ∈ pCoreOf 2 Kc → φ k = 1) (hXK : X ≤ Kc)
    (hprod : (X.subgroupOf Kc).map φ = ((X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ)).prod
      ((X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)))
    (hbad : pCoreOf 2 X ≤ pCoreOf 2 Kc) :
    pCoreOf 2 ((X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ₁ := (MonoidHom.snd Q₁ Q₂).comp φ with hφ₁
  set Y₁ := (X.subgroupOf Kc).map φ₁ with hY₁
  set U := pCoreOf 2 Y₁ with hU
  set V : Subgroup G := X ⊓ ((((⊥ : Subgroup Q₁).prod U).comap φ).map Kc.subtype) with hV
  have hV2 : IsPGroup 2 ↥V := by
    rintro ⟨_, -, ⟨k, hk, rfl⟩⟩
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₁) ⟨(φ k).2, hk.2⟩
    have hk2 : (φ k).1 = 1 := Subgroup.mem_bot.mp hk.1
    have hφa : φ (k ^ 2 ^ a) = 1 := by
      rw [map_pow]
      refine Prod.ext ?_ ?_
      · simp [hk2]
      · simpa using congrArg Subtype.val ha
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
    show φ (⟨g, hXK hg⟩ * k * ⟨g, hXK hg⟩⁻¹) ∈ (⊥ : Subgroup Q₁).prod U
    rw [map_mul, map_mul, map_inv]
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_mul, Prod.fst_inv]
      rw [Subgroup.mem_bot.mp hk.1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · simp only [Prod.snd_mul, Prod.snd_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁ hg') _).mp hk.2
  have hVO : V ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hNV hV2
  refine eq_bot_iff.mpr fun u hu => ?_
  have hu1 : ((1 : Q₁), u) ∈ (X.subgroupOf Kc).map φ := by
    rw [hprod]
    exact ⟨Subgroup.one_mem _, CFSG.LieType.BorelTits.pCoreOf_le 2 Y₁ hu⟩
  obtain ⟨k, hk, hku⟩ := hu1
  have hkV : (k : G) ∈ V := by
    refine ⟨hk, ⟨k, ?_, rfl⟩⟩
    show φ k ∈ (⊥ : Subgroup Q₁).prod U
    rw [hku]
    exact ⟨Subgroup.mem_bot.mpr rfl, hu⟩
  have h1 : φ k = 1 := hO k (hbad (hVO hkV))
  rw [hku] at h1
  exact Subgroup.mem_bot.mpr (congrArg Prod.snd h1)

theorem inr_mem_map_pCoreOf {φ : ↥Kc →* Q₁ × Q₂} (hφ : Function.Surjective φ)
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) {S : Subgroup G} (hS : IsSylowTwoOf S Kc)
    (hXK : X ≤ Kc) {u : Q₂}
    (hu : u ∈ pCoreOf 2 ((X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ) ⊔
        (S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ))) :
    ((1 : Q₁), u) ∈ ((pCoreOf 2 (X ⊔ S)).subgroupOf Kc).map φ := by
  have h := inl_mem_map_pCoreOf (φ := C10P34.swapHom φ)
    ((MulEquiv.prodComm (M := Q₁) (N := Q₂)).surjective.comp hφ) (C10P34.swapHom_ker hker) hS
    hXK (u := u) (by rwa [C10P34.fst_comp_swapHom])
  obtain ⟨w, hw, hwu⟩ := h
  exact ⟨w, hw, Prod.ext (congrArg Prod.snd hwu) (congrArg Prod.fst hwu)⟩

end Snd

variable {G : Type} [Group G] [Finite G] {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}

theorem mem_normalizer_of_inner {X T : Subgroup G}
    (hc : C10P34.PairCtx H K₁ K₂ φ) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (e₁ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (e₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* PSL(2, ZMod p))
    (hXK : X ≤ K₁ ⊔ K₂) (hXO : oTwoUpper X = X) (hX3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hS : IsSylowTwoOf (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    {n : G} (hnK : n ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))
    {a₁ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁} {a₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂}
    (hconj : ∀ (z : G) (hz : z ∈ K₁ ⊔ K₂) (hz' : n * z * n⁻¹ ∈ K₁ ⊔ K₂),
      φ ⟨n * z * n⁻¹, hz'⟩ = (a₁ * (φ ⟨z, hz⟩).1 * a₁⁻¹, a₂ * (φ ⟨z, hz⟩).2 * a₂⁻¹))
    (ha₁Y : a₁ ∈ Subgroup.normalizer
      ((((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) : Subgroup _) : Set _))
    (ha₂Y : a₂ ∈ Subgroup.normalizer
      ((((X.subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) : Subgroup _) : Set _)) :
    n ∈ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) := fun k hk => by
    have h1 : k ∈ φ.ker := hk
    rw [hc.ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hSX : T ⊓ (K₁ ⊔ K₂) ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
  have hON : pCoreOf 2 (K₁ ⊔ K₂) ≤ Subgroup.normalizer (X : Set G) :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS).trans hSX
  have hXprod := C10P34.map_eq_prod hp5 e₁ e₂ hker hXK hXO hX3 hPX hP hP3
  have hgen : ∀ x ∈ X, Odd (orderOf x) → n * x * n⁻¹ ∈ X := by
    intro x hx hxo
    have hxK := hXK hx
    have hx' := conj_mem_of_mem_normalizer hnK hxK
    refine C10P34.mem_of_odd_of_mem_map hker hON hXO hx' ?_ ?_
    · rw [show n * x * n⁻¹ = MulAut.conj n x from rfl, MulEquiv.orderOf_eq]
      exact hxo
    · rw [hconj x hxK hx', hXprod]
      exact ⟨(Subgroup.mem_normalizer_iff.mp ha₁Y _).mp ⟨⟨x, hxK⟩, hx, rfl⟩,
        (Subgroup.mem_normalizer_iff.mp ha₂Y _).mp ⟨⟨x, hxK⟩, hx, rfl⟩⟩
  have hle : X.map (MulAut.conj n).toMonoidHom ≤ X := by
    conv_lhs => rw [← hXO]
    rw [oTwoUpper, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨hx, hxo⟩, rfl⟩
    exact hgen x hx hxo
  exact C10P34.mem_normalizer_of_forall_conj_mem fun x hx => hle ⟨x, hx, rfl⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
