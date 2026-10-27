module

public import CFSG.Milestones.ASVolI.F429.Gen

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open CFSG.LieType.BorelTits (pCoreOf_le pCoreOf_isPGroup le_pCoreOf_of_le_normalizer
  normalizer_le_normalizer_pCoreOf le_normalizer_pCoreOf)

section Generic

variable {E : Type} [Group E]

theorem burnsideF429_oPPrime_le (P : Subgroup E) : oPPrime 2 P ≤ P :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem burnsideF429_le_normalizer_oPPrime {P T : Subgroup E}
    (hT : T ≤ Subgroup.normalizer (P : Set E)) :
    T ≤ Subgroup.normalizer ((oPPrime 2 P : Subgroup E) : Set E) := by
  have key : ∀ s : E, s ∈ Subgroup.normalizer (P : Set E) →
      ∀ x ∈ oPPrime 2 P, s * x * s⁻¹ ∈ oPPrime 2 P := by
    intro s hs x hx
    have hmap : (oPPrime 2 P).map (MulAut.conj s).toMonoidHom ≤ oPPrime 2 P := by
      unfold oPPrime
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨hyP, k, hk⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hs y).1 hyP, k, ?_⟩
      rw [← hk]
      exact orderOf_injective (MulAut.conj s).toMonoidHom (MulEquiv.injective _) y
    exact hmap ⟨x, hx, rfl⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t (hT ht) x
  · intro hx
    have := key t⁻¹ (Subgroup.inv_mem _ (hT ht)) _ hx
    simpa [mul_assoc] using this

theorem burnsideF429_relIndex_sup [Finite E] {L T : Subgroup E}
    (hTL : T ≤ Subgroup.normalizer (L : Set E)) :
    T.relIndex (L ⊔ T) = (L ⊓ T).relIndex L := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hTL
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTL
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient T L hTL
  have h1 : L.relIndex T = L.relIndex (T ⊔ L) := by
    unfold Subgroup.relIndex Subgroup.index
    exact Nat.card_congr e.toEquiv
  have hSp : 0 < Nat.card ↥(L ⊓ T) := Nat.card_pos
  have hc1 := Subgroup.relIndex_mul_card L (T ⊔ L)
  have hc2 := Subgroup.relIndex_mul_card L T
  have hc3 := Subgroup.relIndex_mul_card T (T ⊔ L)
  have hc4 := Subgroup.relIndex_mul_card (L ⊓ T) L
  rw [inf_eq_left.2 le_sup_right] at hc1
  rw [inf_eq_left.2 le_sup_left] at hc3
  rw [inf_eq_left.2 inf_le_left] at hc4
  rw [sup_comm]
  have hpos : 0 < L.relIndex T := by
    rcases Nat.eq_zero_or_pos (L.relIndex T) with h | h
    · have : Nat.card T = 0 := by rw [← hc2, h, zero_mul]
      exact absurd this Nat.card_pos.ne'
    · exact h
  have key : T.relIndex (T ⊔ L) * (L.relIndex T * Nat.card ↥(L ⊓ T)) =
      (L ⊓ T).relIndex L * (L.relIndex T * Nat.card ↥(L ⊓ T)) := by
    calc T.relIndex (T ⊔ L) * (L.relIndex T * Nat.card ↥(L ⊓ T))
        = T.relIndex (T ⊔ L) * Nat.card T := by rw [hc2]
      _ = Nat.card ↥(T ⊔ L) := hc3
      _ = L.relIndex (T ⊔ L) * Nat.card L := hc1.symm
      _ = L.relIndex T * ((L ⊓ T).relIndex L * Nat.card ↥(L ⊓ T)) := by rw [h1, hc4]
      _ = (L ⊓ T).relIndex L * (L.relIndex T * Nat.card ↥(L ⊓ T)) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hSp) key

end Generic

section Setting


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_c5_of_key (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {M : Subgroup E}
    (hM : M₁ ⊓ M₂ ≤ M) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂))
    (hkey : ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp) :
    pCoreOf 2 (oPPrime 2 (Gp ⊓ M) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set L := oPPrime 2 (Gp ⊓ M) with hLdef
  have hSyl : ChF.IsSylowOf 2 S (Gp ⊓ M) := burnsideF429_sylowBar_inf hyp hM
  have hSL : S ≤ L := burnsideF429_sbar_le_oPPrime hSyl.1
  have hLP : L ≤ Gp ⊓ M := burnsideF429_oPPrime_le _
  have hSylL : ChF.IsSylowOf 2 S L := burnsideF429_isSylowOf_of_le hSyl hSL hLP
  have hTP : T ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have htM : t ∈ M := hM (hT.1 ht)
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG t,
        M.mul_mem (M.mul_mem htM hxM) (M.inv_mem htM)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG t⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem htM) hxM) htM
        simpa [mul_assoc] using this
  have hTL : T ≤ Subgroup.normalizer ((L : Subgroup E) : Set E) :=
    burnsideF429_le_normalizer_oPPrime hTP
  have hTinf : T ⊓ Gp = S := burnsideF429_T_inf_Gp hyp hT
  have hST : S ≤ T := burnsideF429_sbar_le hT
  have hLT : L ⊓ T = S := by
    refine le_antisymm (fun x hx => ?_) (le_inf hSL hST)
    rw [← hTinf]
    exact ⟨hx.2, (hLP hx.1).1⟩
  have hTsyl : ChF.IsSylowOf 2 T (L ⊔ T) := by
    refine ⟨le_sup_right, hT.2.1, ?_⟩
    rw [burnsideF429_relIndex_sup hTL, hLT]
    exact hSylL.2.2
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hQT : Q ≤ T := F7.isSylowTwoOf_pCoreOf_le hTsyl
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have hQnorm : L ⊔ T ≤ Subgroup.normalizer ((Q : Subgroup E) : Set E) :=
    le_normalizer_pCoreOf 2 _
  have hOL : pCoreOf 2 L ≤ S := F7.isSylowTwoOf_pCoreOf_le hSylL
  have hQL : Q ⊓ L ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQ2.to_le inf_le_left)
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hQnorm (Subgroup.mem_sup_left hl)) x
    constructor
    · rintro ⟨hxQ, hxL⟩
      exact ⟨h1.1 hxQ, L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)⟩
    · rintro ⟨hxQ, hxL⟩
      refine ⟨h1.2 hxQ, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hl) hxL) hl
      simpa [mul_assoc] using this
  apply le_antisymm
  · intro u hu
    have huT := hQT hu
    obtain ⟨k, hk⟩ := hT.2.1 ⟨u, huT⟩
    have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcomm : ∀ b ∈ L ⊓ (M₁ ⊓ M₂), u * b * u⁻¹ * b⁻¹ ∈ S := by
      intro b hb
      have h1 : u * b * u⁻¹ * b⁻¹ ∈ Q := by
        have hb' : b * u⁻¹ * b⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.1 (hQnorm (Subgroup.mem_sup_left hb.1)) _).1
            (Q.inv_mem hu)
        have := Q.mul_mem hu hb'
        simpa [mul_assoc] using this
      have h2 : u * b * u⁻¹ * b⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTL huT) b).1 hb.1) (L.inv_mem hb.1)
      exact hOL (hQL ⟨h1, h2⟩)
    have huG : u ∈ Gp := hkey u (hT.1 huT) k hk' hcomm
    have huS : u ∈ S := by
      rw [← hTinf]
      exact ⟨huT, huG⟩
    exact hQL ⟨hu, hSL huS⟩
  · refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 _)
    exact sup_le (le_normalizer_pCoreOf 2 _) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 _))

theorem burnsideF429_c5i_of_keys (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂))
    (hkey₁ : ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₁) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp)
    (hkey₂ : ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp) :
    burnsideF429_C5 κ Gp M₁ M₂ hyp T :=
  Or.inl ⟨burnsideF429_c5_of_key hyp inf_le_left hT hkey₁,
    burnsideF429_c5_of_key hyp inf_le_right hT hkey₂⟩

end Setting

end CFSG.ASVolI
