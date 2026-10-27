module

public import CFSG.Quasithin.H13.NQCoreA6EOneConcrete
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Quasithin.SteinbergCCLocalSylowAction
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

section Transport

variable {B G : Type*} [Group B] [Group G] {φ : B →* G}

theorem pCoreOf_map_of_injective (hφ : Function.Injective φ) (K : Subgroup B) :
    pCoreOf 2 (K.map φ) = (pCoreOf 2 K).map φ := by
  unfold CFSG.Open.pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (K.equivMapOfInjective φ hφ),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowIn_of_map (hφ : Function.Injective φ) {p : ℕ} {P Q : Subgroup B}
    (h : IsSylowIn p (P.map φ) (Q.map φ)) : IsSylowIn p P Q := by
  refine ⟨(map_le_map_iff_of_injective hφ).mp h.1,
    h.2.1.of_equiv (P.equivMapOfInjective φ hφ).symm, ?_⟩
  rw [← relIndex_map_map_of_injective P Q hφ]
  exact h.2.2

theorem isSylowIn_map (hφ : Function.Injective φ) {p : ℕ} {P Q : Subgroup B}
    (h : IsSylowIn p P Q) : IsSylowIn p (P.map φ) (Q.map φ) := by
  refine ⟨map_mono h.1, h.2.1.of_equiv (P.equivMapOfInjective φ hφ), ?_⟩
  rw [relIndex_map_map_of_injective P Q hφ]
  exact h.2.2

theorem E1TypeOne.comap (hφ : Function.Injective φ) {T A : Subgroup B} {K' : Subgroup G}
    (h : E1TypeOne φ.range (T.map φ) (A.map φ) K') : E1TypeOne ⊤ T A (K'.comap φ) := by
  set K := K'.comap φ with hKdef
  have hKmap : K.map φ = K' := by
    rw [hKdef, Subgroup.map_comap_eq, inf_of_le_right h.le]
  have hcore : (pCoreOf 2 K).map φ = pCoreOf 2 K' := by
    rw [← pCoreOf_map_of_injective hφ, hKmap]
  obtain ⟨P', p, hp, hQP', hP'K', hP'n, hP'card, ⟨b, hb⟩, hP'eq⟩ := h.core
  set P := P'.comap φ with hPdef
  have hPmap : P.map φ = P' := by
    rw [hPdef, Subgroup.map_comap_eq, inf_of_le_right (hP'K'.trans h.le)]
  refine ⟨le_top, fun a ha => h.A_le (mem_map_of_mem φ ha), fun x hx => ?_, ?_,
    ⟨P, p, hp, ?_, comap_mono hP'K', ?_, ?_, ⟨b, ?_⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
    refine h.centralizer_le (mem_inf.mpr ⟨mem_map_of_mem φ hxT, ?_⟩)
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hxC a ha]
  · apply isSylowIn_of_map hφ
    rw [map_inf_eq _ _ φ hφ, hKmap]
    exact h.sylow
  · rw [← map_le_map_iff_of_injective hφ, hcore, hPmap]
    exact hQP'
  · rw [normal_subgroupOf_iff (comap_mono hP'K')]
    intro x k hx hk
    have h1 := (normal_subgroupOf_iff hP'K').mp hP'n (φ x) (φ k) hx hk
    show φ (k * x * k⁻¹) ∈ P'
    rw [map_mul, map_mul, map_inv]
    exact h1
  · calc Nat.card P = Nat.card P' := by rw [← hPmap, card_map_of_injective hφ]
      _ = Nat.card (pCoreOf 2 K') * p := hP'card
      _ = Nat.card (pCoreOf 2 K) * p := by rw [← hcore, card_map_of_injective hφ]
  · calc Nat.card K = Nat.card K' := by rw [← hKmap, card_map_of_injective hφ]
      _ = Nat.card P' * 2 ^ b := hb
      _ = Nat.card P * 2 ^ b := by rw [← hPmap, card_map_of_injective hφ]
  · apply map_injective hφ
    rw [Subgroup.map_sup, map_commutator, hPmap, hcore]
    exact hP'eq
  · calc Nat.card A = Nat.card (A.map φ) := (card_map_of_injective hφ).symm
      _ = 2 * Nat.card (A.map φ ⊓ pCoreOf 2 K' : Subgroup G) := h.index_two
      _ = 2 * Nat.card (A ⊓ pCoreOf 2 K : Subgroup B) := by
        rw [← hcore, ← map_inf_eq _ _ φ hφ, card_map_of_injective hφ]
  · rw [← map_le_map_iff_of_injective hφ, map_commutator, map_inf_eq _ _ φ hφ, hKmap, hcore]
    exact h.comm_le

theorem weakClosure_map (hφ : Function.Injective φ) (T : Subgroup B) (Ω : Set (Subgroup B)) :
    E1.weakClosure (T.map φ) ((fun A => A.map φ) '' Ω) = (E1.weakClosure T Ω).map φ := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'T => ?_
    obtain ⟨A, hA, rfl⟩ := hA'
    refine map_mono (le_iSup₂_of_le A hA (le_iSup_of_le ?_ le_rfl))
    exact (map_le_map_iff_of_injective hφ).mp hA'T
  · rw [map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    rw [← map_le_iff_le_comap]
    exact le_iSup₂_of_le (A.map φ) ⟨A, hA, rfl⟩ (le_iSup_of_le (map_mono hAT) le_rfl)

theorem map_normalizer_of_injective (hφ : Function.Injective φ) (W : Subgroup B) :
    (normalizer (W : Set B)).map φ = φ.range ⊓ normalizer ((W.map φ : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.mpr ⟨⟨x, rfl⟩, mem_normalizer_iff.mpr fun z => ?_⟩
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨x * w * x⁻¹, (mem_normalizer_iff.mp hx w).mp hw, by simp⟩
    · rintro ⟨w, hw, hwz⟩
      have : z = φ (x⁻¹ * w * x) := by
        rw [map_mul, map_mul, map_inv, hwz]
        group
      rw [this]
      refine mem_map_of_mem φ ?_
      have h1 := (mem_normalizer_iff.mp (inv_mem hx) w).mp hw
      rwa [inv_inv] at h1
  · intro hy
    obtain ⟨⟨x, rfl⟩, hxN⟩ := mem_inf.mp hy
    refine mem_map_of_mem φ (mem_normalizer_iff.mpr fun w => ?_)
    rw [← mem_map_iff_mem hφ (K := W), ← mem_map_iff_mem hφ (K := W), map_mul, map_mul, map_inv]
    exact mem_normalizer_iff.mp hxN (φ w)

theorem isElemAbelian_map_of {B G : Type*} [Group B] [Group G] (f : B →* G) {A : Subgroup B}
    (h : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map h _

theorem conjSub_map {B G : Type*} [Group B] [Group G] (f : B →* G) (b : B) (A : Subgroup B) :
    A1b.conjSub (f b) (A.map f) = (A1b.conjSub b A).map f := by
  unfold A1b.conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

theorem map_conj_eq_of_mem {G : Type*} [Group G] {X : Subgroup G} {x : G} (hx : x ∈ X) :
    X.map (MulAut.conj x).toMonoidHom = X := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
  · intro y hy
    refine ⟨x⁻¹ * y * x, X.mul_mem (X.mul_mem (X.inv_mem hx) hy) hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end Transport

section Embedding

variable {B : Type} [Group B] (S₀ : Subgroup B) [S₀.Normal]

@[expose] noncomputable def conjEquiv : Setup.X3Aut.AutA6 ≃* MulAut ↥A6Models.psl29 :=
  MulEquiv.ofBijective Setup.X3Aut.conjHom
    ⟨DoubleA3.conjAut_injective, DoubleA3.conjAut_surjective⟩

@[expose] noncomputable def toAutA6 (e : ↥S₀ ≃* ↥A6Models.psl29) : B →* P10 :=
  A6Models.autA6.subtype.comp (conjEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal))

theorem toAutA6_apply (e : ↥S₀ ≃* ↥A6Models.psl29) (b : B) :
    toAutA6 S₀ e b = (conjEquiv.symm (MulAut.congr e (MulAut.conjNormal b)) : P10) := rfl

theorem toAutA6_injective (e : ↥S₀ ≃* ↥A6Models.psl29) (hC : centralizer (S₀ : Set B) = ⊥) :
    Function.Injective (toAutA6 S₀ e) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  rw [toAutA6_apply] at hb
  have h1 : conjEquiv.symm (MulAut.congr e (MulAut.conjNormal b)) = 1 := Subtype.ext hb
  have h2 : MulAut.congr e (MulAut.conjNormal (H := S₀) b) = 1 := by
    rw [← conjEquiv.apply_symm_apply (MulAut.congr e _), h1, map_one]
  have h3 : MulAut.conjNormal (H := S₀) b = 1 := by
    rw [← (MulAut.congr e).symm_apply_apply (MulAut.conjNormal b), h2, map_one]
  have hbC : b ∈ centralizer (S₀ : Set B) := by
    rw [mem_centralizer_iff]
    intro s hs
    have h4 := congrArg (fun f : MulAut S₀ => ((f ⟨s, hs⟩ : S₀) : B)) h3
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h4
    calc s * b = b * s * b⁻¹ * b := by rw [h4]
      _ = b * s := by group
  rw [hC, mem_bot] at hbC
  exact hbC

theorem range_toAutA6_le (e : ↥S₀ ≃* ↥A6Models.psl29) :
    (toAutA6 S₀ e).range ≤ A6Models.autA6 := by
  rintro _ ⟨b, rfl⟩
  exact (conjEquiv.symm (MulAut.congr e (MulAut.conjNormal b))).2

theorem psl29_le_range_toAutA6 (e : ↥S₀ ≃* ↥A6Models.psl29) :
    A6Models.psl29 ≤ (toAutA6 S₀ e).range := by
  intro y hy
  refine ⟨((e.symm ⟨y, hy⟩ : S₀) : B), ?_⟩
  have h1 : MulAut.congr e (MulAut.conjNormal ((e.symm ⟨y, hy⟩ : S₀) : B)) =
      conjEquiv ⟨y, psl29_le_autA6 hy⟩ := by
    rw [MulAut.conjNormal_val]
    refine MulEquiv.ext fun z => Subtype.ext ?_
    show ((e ((e.symm ⟨y, hy⟩) * e.symm z * (e.symm ⟨y, hy⟩)⁻¹) : A6Models.psl29) : P10) =
      y * (z : P10) * y⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [toAutA6_apply, h1, MulEquiv.symm_apply_apply]

end Embedding

theorem stmtA6AutEOneWitnessesAll :
    ∀ (B : Type) [Group B] [Finite B] (S₀ : Subgroup B) [S₀.Normal],
      Nonempty (↥S₀ ≃* alternatingGroup (Fin 6)) → centralizer (S₀ : Set B) = ⊥ →
      ∀ T : Subgroup B, IsSylowIn 2 T ⊤ → ∀ Ω : Set (Subgroup B), E1.IsInvColl ⊤ Ω →
        ∃ F : Set (Subgroup B × Subgroup B),
          (∀ AK ∈ F, AK.1 ∈ Ω ∧ AK.1 ≤ T ∧ E1TypeOne ⊤ T AK.1 AK.2) ∧
            (⨆ AK ∈ F, AK.2) ⊔ normalizer (E1.weakClosure T Ω : Set B) = ⊤ := by
  intro B _ _ S₀ _ ⟨e₀⟩ hC T hT Ω hΩ
  classical
  set e : ↥S₀ ≃* ↥A6Models.psl29 := e₀.trans Setup.X3Aut.psiEquiv.symm with hedef
  set φ := toAutA6 S₀ e with hφdef
  have hφ : Function.Injective φ := toAutA6_injective S₀ e hC
  obtain ⟨S, hS, hall⟩ := A6EOne.a6_eOne_concrete (psl29_le_range_toAutA6 S₀ e)
    (range_toAutA6_le S₀ e)
  have hTX : IsSylowIn 2 (T.map φ) φ.range := by
    have h1 := isSylowIn_map hφ hT
    rwa [← MonoidHom.range_eq_map] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxX, hx⟩ := SteinbergCC.exists_conj_eq_of_isSylowOf
    (CFSG.ABGLocalTools.isSylowOf_iff.mpr hTX) (CFSG.ABGLocalTools.isSylowOf_iff.mpr hS)
  set φ' : B →* P10 := (MulAut.conj x).toMonoidHom.comp φ with hφ'def
  have hφ' : Function.Injective φ' := (MulAut.conj x).injective.comp hφ
  have hφ'T : T.map φ' = S := by rw [← hx, Subgroup.map_map]
  have hφ'X : φ'.range = φ.range := by
    rw [hφ'def, MonoidHom.range_comp, map_conj_eq_of_mem hxX]
  set Ω' : Set (Subgroup P10) := (fun A => A.map φ') '' Ω with hΩ'def
  have hΩ' : E1.IsInvColl φ.range Ω' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨A, -, rfl⟩
      rw [← hφ'X]
      exact map_le_range φ' A
    · rintro _ ⟨A, hA, rfl⟩
      exact isElemAbelian_map_of φ' (hΩ.isElemAbelian A hA)
    · rintro _ ⟨A, hA, rfl⟩ h hh
      rw [← hφ'X] at hh
      obtain ⟨b, rfl⟩ := hh
      rw [conjSub_map]
      exact ⟨_, hΩ.conj A hA b (mem_top b), rfl⟩
  obtain ⟨F', hF', hgen⟩ := hall Ω' hΩ'
  set F : Set (Subgroup B × Subgroup B) :=
    (fun AK => (AK.1.comap φ', AK.2.comap φ')) '' F' with hFdef
  refine ⟨F, ?_, ?_⟩
  · rintro _ ⟨⟨A', K'⟩, hAK, rfl⟩
    obtain ⟨hA'Ω, hA'S, hTO⟩ := hF' _ hAK
    obtain ⟨A, hA, rfl⟩ := hA'Ω
    simp only
    rw [comap_map_eq_self_of_injective hφ']
    refine ⟨hA, ?_, ?_⟩
    · rw [← hφ'T] at hA'S
      exact (map_le_map_iff_of_injective hφ').mp hA'S
    · refine E1TypeOne.comap hφ' ?_
      rw [hφ'X, hφ'T]
      exact hTO
  have hsup : (⨆ AK ∈ F, AK.2).map φ' = ⨆ AK ∈ F', AK.2 := by
    apply le_antisymm
    · rw [map_le_iff_le_comap]
      refine iSup₂_le fun AK hAK => ?_
      obtain ⟨⟨A', K'⟩, hAK', rfl⟩ := hAK
      exact comap_mono (le_iSup₂_of_le (A', K') hAK' le_rfl)
    · refine iSup₂_le fun AK hAK => ?_
      have hK'X : AK.2 ≤ φ'.range := by
        rw [hφ'X]
        exact (hF' AK hAK).2.2.le
      calc AK.2 = (AK.2.comap φ').map φ' := by rw [map_comap_eq, inf_of_le_right hK'X]
        _ ≤ _ := map_mono (le_iSup₂_of_le (AK.1.comap φ', AK.2.comap φ') ⟨AK, hAK, rfl⟩ le_rfl)
  apply map_injective hφ'
  rw [Subgroup.map_sup, hsup, map_normalizer_of_injective hφ', ← weakClosure_map hφ', hφ'T,
    ← MonoidHom.range_eq_map, hφ'X]
  exact hgen

theorem stmtA6AutEOneWitnesses :
    ∀ (B : Type) [Group B] [Finite B] (S₀ : Subgroup B) [S₀.Normal],
      Nonempty (↥S₀ ≃* alternatingGroup (Fin 6)) → centralizer (S₀ : Set B) = ⊥ →
      ∀ T : Subgroup B, IsSylowIn 2 T ⊤ → ∀ Ω : Set (Subgroup B), E1.IsInvColl ⊤ Ω →
        (∀ A ∈ Ω, Nat.card A ≠ 2) →
        ∃ F : Set (Subgroup B × Subgroup B),
          (∀ AK ∈ F, AK.1 ∈ Ω ∧ AK.1 ≤ T ∧ E1TypeOne ⊤ T AK.1 AK.2) ∧
            (⨆ AK ∈ F, AK.2) ⊔ normalizer (E1.weakClosure T Ω : Set B) = ⊤ :=
  fun B _ _ S₀ _ he hC T hT Ω hΩ _ => stmtA6AutEOneWitnessesAll B S₀ he hC T hT Ω hΩ

end CFSG.Quasithin.H13.NQCore
