module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LI
public import CFSG.Quasithin.Vol2.Ch10SecB5EvPair

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {Kc X : Subgroup G} {Q₁ Q₂ : Type} [Group Q₁]
  [Group Q₂] [Finite Q₁] [Finite Q₂]

abbrev swapHom (φ : ↥Kc →* Q₁ × Q₂) : ↥Kc →* Q₂ × Q₁ :=
  (MulEquiv.prodComm (M := Q₁) (N := Q₂)).toMonoidHom.comp φ

omit [Finite G] [Finite Q₁] [Finite Q₂] in
theorem fst_comp_swapHom (φ : ↥Kc →* Q₁ × Q₂) :
    (MonoidHom.fst Q₂ Q₁).comp (swapHom φ) = (MonoidHom.snd Q₁ Q₂).comp φ :=
  MonoidHom.ext fun _ => rfl

omit [Finite G] [Finite Q₁] [Finite Q₂] in
theorem swapHom_ker {φ : ↥Kc →* Q₁ × Q₂} (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) :
    ∀ k, swapHom φ k = 1 → (k : G) ∈ pCoreOf 2 Kc := fun k hk =>
  hker k ((MulEquiv.map_eq_one_iff (MulEquiv.prodComm (M := Q₁) (N := Q₂))).mp hk)

variable {p : ℕ} [Fact p.Prime]

theorem map_eq_prod (hp5 : 5 ≤ p) (e₁ : Q₁ ≃* PSL(2, ZMod p)) (e₂ : Q₂ ≃* PSL(2, ZMod p))
    {φ : ↥Kc →* Q₁ × Q₂} (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) (hXK : X ≤ Kc)
    (hX : oTwoUpper X = X) (h3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) {P : Subgroup G} (hPX : P ≤ X)
    (hP : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1) :
    (X.subgroupOf Kc).map φ = ((X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ)).prod
      ((X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)) := by
  have h₁ := fst_le_comap_inl hp5 e₁ e₂ hker hXK hX h3 hPX hP hP3
  have h₂ : (X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ) ≤
      ((X.subgroupOf Kc).map φ).comap (MonoidHom.inr Q₁ Q₂) := by
    have h := fst_le_comap_inl hp5 e₂ e₁ (swapHom_ker hker) hXK hX h3 hPX hP hP3
    rw [fst_comp_swapHom] at h
    intro y hy
    obtain ⟨x', hx', hx'y⟩ := h hy
    exact ⟨x', hx', congrArg Prod.swap hx'y⟩
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · obtain ⟨hz1, hz2⟩ := hz
    have e : z = (z.1, 1) * (1, z.2) := by ext <;> simp
    rw [e]
    exact Subgroup.mul_mem _ (h₁ hz1) (h₂ hz2)

omit [Finite Q₁] in
theorem fst_ne_bot (hp5 : 5 ≤ p) (e₂ : Q₂ ≃* PSL(2, ZMod p)) {φ : ↥Kc →* Q₁ × Q₂}
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) (hXK : X ≤ Kc) (hX : oTwoUpper X = X)
    (h3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) : (X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) ≠ ⊥ := by
  obtain ⟨y, hy3, x, hx, hxy⟩ := exists_inl_mem hp5 e₂ hker hXK hX h3 hPX hP hP3
  intro hb
  have hy : y ∈ (X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) :=
    ⟨x, hx, by rw [MonoidHom.comp_apply, hxy]; rfl⟩
  rw [hb, Subgroup.mem_bot] at hy
  rw [hy, orderOf_one] at hy3
  exact absurd hy3 (by norm_num)

omit [Finite Q₂] in
theorem snd_ne_bot (hp5 : 5 ≤ p) (e₁ : Q₁ ≃* PSL(2, ZMod p)) {φ : ↥Kc →* Q₁ × Q₂}
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) (hXK : X ≤ Kc) (hX : oTwoUpper X = X)
    (h3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) : (X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ) ≠ ⊥ := by
  rw [← fst_comp_swapHom]
  exact fst_ne_bot hp5 e₁ (swapHom_ker hker) hXK hX h3 hPX hP hP3

omit [Fact p.Prime] in
theorem map_pCoreOf_le {Q : Type} [Group Q] [Finite Q] (f : ↥Kc →* Q) (hXK : X ≤ Kc) :
    ((pCoreOf 2 X).subgroupOf Kc).map f ≤ pCoreOf 2 ((X.subgroupOf Kc).map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOX := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hOK : pCoreOf 2 X ≤ Kc := hOX.trans hXK
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono fun k hk => hOX hk)
    (map_le_normalizer_map f (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) hOK)
    ((A4.isPGroup_subgroupOf_of_le hOK (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)).map f)

omit [Fact p.Prime] in
theorem pCoreOf_sup_le_map_fst {φ : ↥Kc →* Q₁ × Q₂} (hφ : Function.Surjective φ)
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) {S : Subgroup G} (hS : IsSylowTwoOf S Kc)
    (hXK : X ≤ Kc) :
    pCoreOf 2 ((X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) ⊔
        (S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ)) ≤
      ((pCoreOf 2 (X ⊔ S)).subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) := by
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
    refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
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
  intro u hu
  have hu1 : (u, (1 : Q₂)) ∈ (S.subgroupOf Kc).map φ := by
    rw [hprod]
    exact ⟨hUS hu, Subgroup.one_mem _⟩
  obtain ⟨k, hk, hku⟩ := hu1
  have hkV : (k : G) ∈ V := by
    refine ⟨Subgroup.mem_sup_right hk, ⟨k, ?_, rfl⟩⟩
    show φ k ∈ U.prod ⊥
    rw [hku]
    exact ⟨hu, Subgroup.mem_bot.mpr rfl⟩
  refine ⟨k, hVW hkV, ?_⟩
  rw [hφ₁, MonoidHom.comp_apply, hku]
  rfl

omit [Fact p.Prime] in
theorem pCoreOf_sup_le_map_snd {φ : ↥Kc →* Q₁ × Q₂} (hφ : Function.Surjective φ)
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) {S : Subgroup G} (hS : IsSylowTwoOf S Kc)
    (hXK : X ≤ Kc) :
    pCoreOf 2 ((X.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ) ⊔
        (S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)) ≤
      ((pCoreOf 2 (X ⊔ S)).subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ) := by
  have h := pCoreOf_sup_le_map_fst (φ := swapHom φ)
    ((MulEquiv.prodComm (M := Q₁) (N := Q₂)).surjective.comp hφ) (swapHom_ker hker) hS hXK
  rwa [fst_comp_swapHom] at h

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
