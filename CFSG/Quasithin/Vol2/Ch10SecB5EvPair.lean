module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvL2Q

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

theorem eq_of_isSylowTwoOf_top_le {Q : Type} [Group Q] [Finite Q] {P R : Subgroup Q}
    (hP : IsSylowTwoOf P ⊤) (hR : IsPGroup 2 R) (hPR : P ≤ R) : P = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm hPR ?_
  have hidx : ¬ 2 ∣ P.index := by
    have h := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right _] at h
  obtain ⟨k, hk⟩ := hR.index (P.subgroupOf R)
  have hdvd : P.relIndex R ∣ P.index := Subgroup.relIndex_dvd_index_of_le hPR
  have h1 : P.relIndex R = 1 := by
    rw [Subgroup.relIndex, hk] at hdvd ⊢
    rcases k with _ | k
    · rfl
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd) hidx
  exact Subgroup.relIndex_eq_one.mp h1

theorem isPGroup_prod {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] {A : Subgroup Q₁}
    {B : Subgroup Q₂} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) : IsPGroup 2 ↥(A.prod B) := by
  rintro ⟨⟨a, b⟩, ha, hb⟩
  obtain ⟨i, hi⟩ := hA ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hB ⟨b, hb⟩
  have hi' : a ^ 2 ^ i = 1 := congrArg Subtype.val hi
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  refine ⟨i + j, Subtype.ext (Prod.ext ?_ ?_)⟩
  · simp [pow_add, pow_mul, hi']
  · simp [pow_add, pow_mul', hj']

theorem mem_normalizer_of_conj_mem {Q : Type} [Group Q] [Finite Q] {U : Subgroup Q} {g : Q}
    (h : ∀ u ∈ U, g * u * g⁻¹ ∈ U) : g ∈ Subgroup.normalizer (U : Set Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    simpa [MulAut.conj_apply] using h u hu
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

end General

variable {G : Type} [Group G] [Finite G] {Kc S X : Subgroup G} {Q₁ Q₂ : Type} [Group Q₁]
  [Group Q₂] [Finite Q₁] [Finite Q₂] {φ : ↥Kc →* Q₁ × Q₂}

omit [Finite G] in
theorem map_sylow_eq_prod (hφ : Function.Surjective φ) (hS : IsSylowTwoOf S Kc) :
    IsSylowTwoOf ((S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ)) ⊤ ∧
      IsSylowTwoOf ((S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)) ⊤ ∧
      (S.subgroupOf Kc).map φ =
        ((S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ)).prod
          ((S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)) := by
  have h1 := SecA.isSylowTwoOf_map_of_surjective hS ((MonoidHom.fst Q₁ Q₂).comp φ)
    (Prod.fst_surjective.comp hφ)
  have h2 := SecA.isSylowTwoOf_map_of_surjective hS ((MonoidHom.snd Q₁ Q₂).comp φ)
    (Prod.snd_surjective.comp hφ)
  refine ⟨h1, h2, eq_of_isSylowTwoOf_top_le (SecA.isSylowTwoOf_map_of_surjective hS φ hφ)
    (isPGroup_prod h1.2.1 h2.2.1) ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨⟨s, hs, rfl⟩, ⟨s, hs, rfl⟩⟩

theorem mem_of_proj_mem (hφ : Function.Surjective φ)
    (hker : φ.ker = (pCoreOf 2 Kc).subgroupOf Kc) (hS : IsSylowTwoOf S Kc) {k : ↥Kc}
    (h1 : (φ k).1 ∈ (S.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ))
    (h2 : (φ k).2 ∈ (S.subgroupOf Kc).map ((MonoidHom.snd Q₁ Q₂).comp φ)) : (k : G) ∈ S := by
  have hO : pCoreOf 2 Kc ≤ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS
  have hmem : φ k ∈ (S.subgroupOf Kc).map φ := by
    rw [(map_sylow_eq_prod hφ hS).2.2]
    exact ⟨h1, h2⟩
  obtain ⟨s, hs, hsk⟩ := hmem
  have hk : s⁻¹ * k ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsk, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have : (k : G) = (s : G) * ((s⁻¹ * k : ↥Kc) : G) := by simp
  rw [this]
  exact S.mul_mem hs (hO hk)

omit [Finite G] [Finite Q₁] [Finite Q₂] in
theorem proj_conj_mem {Q : Type} [Group Q] (π : ↥Kc →* Q) {U : Subgroup Q} {x y : G}
    (hxK : x ∈ Kc) (hyK : y ∈ Kc) (hN : π ⟨x, hxK⟩ ∈ Subgroup.normalizer (U : Set Q))
    (hy : π ⟨y, hyK⟩ ∈ U) (hk : x * y * x⁻¹ ∈ Kc) : π ⟨x * y * x⁻¹, hk⟩ ∈ U := by
  have e : (⟨x * y * x⁻¹, hk⟩ : ↥Kc) = ⟨x, hxK⟩ * ⟨y, hyK⟩ * (⟨x, hxK⟩ : ↥Kc)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp hN _).mp hy

omit [Finite G] [Finite Q₁] [Finite Q₂] in
theorem map_le_normalizer_of_proj
    {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (he : Even n) (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (π : ↥Kc →* Q)
    (hU : IsSylowTwoOf ((S.subgroupOf Kc).map π) ⊤) (hXSK : X ⊔ S ≤ Kc)
    (h5 : ¬ 5 ∣ Nat.card ↥(X ⊔ S)) :
    ((X ⊔ S).subgroupOf Kc).map π ≤
      Subgroup.normalizer (((S.subgroupOf Kc).map π : Subgroup Q) : Set Q) := by
  refine le_normalizer_of_not_five_dvd hn he hF e hU
    (Subgroup.map_mono fun x hx => Subgroup.mem_sup_right hx) fun h => h5 ?_
  refine h.trans ((Subgroup.card_map_dvd _ π).trans ?_)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXSK).toEquiv]

theorem le_normalizer_of_pair
    {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (he₁ : Even n₁) (he₂ : Even n₂)
    (hF₁ : Nat.card F₁ = 2 ^ n₁) (hF₂ : Nat.card F₂ = 2 ^ n₂)
    (e₁ : Q₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : Q₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (hφ : Function.Surjective φ)
    (hker : φ.ker = (pCoreOf 2 Kc).subgroupOf Kc) (hS : IsSylowTwoOf S Kc) (hXK : X ≤ Kc)
    (h5 : ¬ 5 ∣ Nat.card ↥(X ⊔ S)) : X ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨hU₁, hU₂, -⟩ := map_sylow_eq_prod hφ hS
  have hXSK : X ⊔ S ≤ Kc := sup_le hXK hS.1
  have hN₁ := map_le_normalizer_of_proj hn₁ he₁ hF₁ e₁ _ hU₁ hXSK h5
  have hN₂ := map_le_normalizer_of_proj hn₂ he₂ hF₂ e₂ _ hU₂ hXSK h5
  intro x hx
  have hxK := hXK hx
  have hxXS : (⟨x, hxK⟩ : ↥Kc) ∈ (X ⊔ S).subgroupOf Kc := Subgroup.mem_sup_left hx
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have hyK := hS.1 hy
  have hk : x * y * x⁻¹ ∈ Kc := Kc.mul_mem (Kc.mul_mem hxK hyK) (Kc.inv_mem hxK)
  exact mem_of_proj_mem hφ hker hS (k := ⟨x * y * x⁻¹, hk⟩)
    (proj_conj_mem ((MonoidHom.fst Q₁ Q₂).comp φ) hxK hyK (hN₁ ⟨_, hxXS, rfl⟩)
      ⟨⟨y, hyK⟩, hy, rfl⟩ hk)
    (proj_conj_mem ((MonoidHom.snd Q₁ Q₂).comp φ) hxK hyK (hN₂ ⟨_, hxXS, rfl⟩)
      ⟨⟨y, hyK⟩, hy, rfl⟩ hk)

end CFSG.Quasithin.Vol2.Ch10.SecB
