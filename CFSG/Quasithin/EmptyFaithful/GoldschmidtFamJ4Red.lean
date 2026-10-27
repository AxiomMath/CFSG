module

public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Open CFSG.QuasithinUnique

theorem le_pCore_two {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (hK : IsPGroup 2 K) :
    K ≤ CFSG.pCore 2 G :=
  le_sSup ⟨inferInstance, hK⟩

theorem nonempty_modO2_equiv {B S : Type*} [Group B] [Group S] (ψ : B →* S)
    (hψ : Function.Surjective ψ) (hk : IsPGroup 2 ψ.ker) (hS : CFSG.pCore 2 S = ⊥) :
    Nonempty ((B ⧸ CFSG.pCore 2 B) ≃* S) := by
  have hker : CFSG.pCore 2 B = ψ.ker := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker]
      have : ((CFSG.pCore 2 B).map ψ).Normal :=
        Subgroup.Normal.map (CFSG.pCore_normal) ψ hψ
      have h1 : (CFSG.pCore 2 B).map ψ ≤ CFSG.pCore 2 S :=
        le_pCore_two ((CFSG.pCore_isPGroup (p := 2) (G := B)).map ψ)
      have h2 : ψ x ∈ (CFSG.pCore 2 B).map ψ := Subgroup.mem_map_of_mem ψ hx
      have h3 := h1 h2
      rwa [hS, Subgroup.mem_bot] at h3
    · have : ψ.ker.Normal := MonoidHom.normal_ker ψ
      exact le_pCore_two hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem isPGroup_ker_comp {B C S : Type*} [Group B] [Group C] [Group S] (ψ₁ : B →* C)
    (ψ₂ : C →* S) (h₁ : IsPGroup 2 ψ₁.ker) (h₂ : IsPGroup 2 ψ₂.ker) :
    IsPGroup 2 (ψ₂.comp ψ₁).ker := by
  intro x
  have hx : ψ₂ (ψ₁ x) = 1 := x.2
  obtain ⟨k, hk⟩ := h₂ ⟨ψ₁ x, hx⟩
  have hk' : ψ₁ ((x : B) ^ 2 ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := h₁ ⟨(x : B) ^ 2 ^ k, hk'⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have hm' : ((x : B) ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  show (x : B) ^ 2 ^ (k + m) = 1
  rw [pow_add, pow_mul]
  exact hm'

theorem pCore_eq_bot_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : CFSG.pCore 2 S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 S) with h | h
  · exact h
  · exfalso
    have hP : IsPGroup 2 S := by
      intro g
      have := (CFSG.pCore_isPGroup (p := 2) (G := S)) ⟨g, by rw [h]; trivial⟩
      obtain ⟨k, hk⟩ := this
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Group.IsNilpotent S := hP.isNilpotent
    have hs : Group.IsSolvable S := inferInstance
    have := (IsSimpleGroup.comm_iff_isSolvable (G := S)).2 hs
    obtain ⟨a, b, hab⟩ := hna
    exact hab (this a b)

theorem pCore_eq_bot_of_isHat {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hc : Nat.card (Subgroup.center X) = 3) :
    CFSG.pCore 2 X = ⊥ := by
  obtain ⟨-, hsimple, hna⟩ := hX
  have : Finite (X ⧸ Subgroup.center X) := inferInstance
  have hqbot : CFSG.pCore 2 (X ⧸ Subgroup.center X) = ⊥ := pCore_eq_bot_of_simple hna
  set N := CFSG.pCore 2 X with hN
  have hmap : N.map (QuotientGroup.mk' (Subgroup.center X)) ≤
      CFSG.pCore 2 (X ⧸ Subgroup.center X) := by
    have : (N.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal _ (QuotientGroup.mk'_surjective _)
    exact le_pCore_two ((CFSG.pCore_isPGroup (p := 2) (G := X)).map _)
  rw [hqbot] at hmap
  have hNZ : N ≤ Subgroup.center X := by
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center X) x ∈
        N.map (QuotientGroup.mk' (Subgroup.center X)) :=
      Subgroup.mem_map_of_mem _ hx
    have h2 := hmap h1
    rw [Subgroup.mem_bot] at h2
    exact (QuotientGroup.eq_one_iff x).1 h2
  have hZ3 : Nat.card (Subgroup.center X) = 3 := hc
  have hNP : IsPGroup 2 N := CFSG.pCore_isPGroup
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxZ : x ∈ Subgroup.center X := hNZ hx
  let z : Subgroup.center X := ⟨x, hxZ⟩
  obtain ⟨k, hk⟩ := hNP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hz : z ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center X) (x := z)
    rwa [hZ3] at this
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz
    have h3 : orderOf z ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact congrArg Subtype.val hz1

theorem isSylowTwoOf_subgroupOf_of_le {Γ : Type*} [Group Γ] {T M : Subgroup Γ}
    (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M) : IsSylowTwoOf (T.subgroupOf M) ⊤ := by
  refine ⟨le_top, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm, ?_⟩
  rw [show ((T.subgroupOf M).subgroupOf (⊤ : Subgroup ↥M)).index = T.relIndex M from
    Subgroup.relIndex_top_right (T.subgroupOf M)]
  intro h2
  apply hT.2.2
  rw [show (T.subgroupOf (⊤ : Subgroup Γ)).index = T.index from Subgroup.relIndex_top_right T]
  exact h2.trans (Subgroup.relIndex_dvd_index_of_le hTM)

theorem isE2_of_elementary {Γ : Type} [Group Γ] [Finite Γ] (E : Subgroup Γ)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) {n : ℕ}
    (hcard : Nat.card E = 2 ^ n) : IsE2 n ↥E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥E)
    (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun a => Subtype.ext (by rw [pow_two]; exact hsq a a.2)) hcard

theorem inv_conj_mem_of_mem_normalizer {Γ : Type*} [Group Γ] {V : Subgroup Γ} {n : Γ}
    (hn : n ∈ Subgroup.normalizer (V : Set Γ)) {x : Γ} (hx : x ∈ V) : n⁻¹ * x * n ∈ V := by
  have hn' : n⁻¹ ∈ Subgroup.normalizer (V : Set Γ) := (Subgroup.normalizer (V : Set Γ)).inv_mem hn
  have h := (Subgroup.mem_normalizer_iff.mp hn' x).mp hx
  rwa [inv_inv] at h

@[expose] def J4Shape (B : Type) [Group B] : Prop :=
  IsExt B (fun V _ => IsExtraspecial2 6 V)
      (fun Y _ => IsHat Y (CFSG.Blueprint.NativeSporadic.Carrier .M22)) ∨
    IsExt B (fun V _ => IsE2 11 V) (fun Y _ => IsSporadic .M24 Y) ∨
    IsAlt 5 (B ⧸ CFSG.pCore 2 B) ∨ IsHat (B ⧸ CFSG.pCore 2 B) (alternatingGroup (Fin 6)) ∨
    IsPSL 4 2 1 (B ⧸ CFSG.pCore 2 B) ∨ IsPSL 3 2 1 (B ⧸ CFSG.pCore 2 B)

theorem J4Shape.of_alt5 {B : Type} [Group B]
    (e : (B ⧸ CFSG.pCore 2 B) ≃* alternatingGroup (Fin 5)) : J4Shape B :=
  Or.inr (Or.inr (Or.inl ⟨e⟩))

theorem J4Shape.of_psl32 {B S : Type} [Group B] [Group S] (e : (B ⧸ CFSG.pCore 2 B) ≃* S)
    (h : IsPSL 3 2 1 S) : J4Shape B :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (IsPSL.of_mulEquiv e.symm h)))))

theorem J4Shape.of_psl42 {B S : Type} [Group B] [Group S] (e : (B ⧸ CFSG.pCore 2 B) ≃* S)
    (h : IsPSL 4 2 1 S) : J4Shape B :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsPSL.of_mulEquiv e.symm h)))))

theorem J4Shape.of_hat6 {B S : Type} [Group B] [Group S] (e : (B ⧸ CFSG.pCore 2 B) ≃* S)
    (h : IsHat S (alternatingGroup (Fin 6))) : J4Shape B :=
  Or.inr (Or.inr (Or.inr (Or.inl (IsHat.of_mulEquiv e.symm h))))

end CFSG.Quasithin.J4Fam
