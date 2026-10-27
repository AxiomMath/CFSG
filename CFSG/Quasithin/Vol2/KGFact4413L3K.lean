module

public import CFSG.Quasithin.Vol2.KGFact4413Q
public import CFSG.Quasithin.Vol2.KGFact4413L3X

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {Γ : Type} [Group Γ]

theorem star_normal {M' H K : Subgroup Γ} (hKH : K ≤ H)
    (hHN : H ≤ Subgroup.normalizer (K : Set Γ)) : (E2.star M' H K).Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN).map _
    (QuotientGroup.mk'_surjective _)

theorem conjNormal_starRes {M' H K : Subgroup Γ} (hKH : K ≤ H) [(E2.star M' H K).Normal]
    (t : ↥H) (k : ↥K) (hk : (t : Γ) * k * (t : Γ)⁻¹ ∈ K) :
    MulAut.conjNormal (starPi M' H t) (starRes M' H K hKH k) = starRes M' H K hKH ⟨_, hk⟩ := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  show starPi M' H t * starPi M' H (Subgroup.inclusion hKH k) * (starPi M' H t)⁻¹ =
    starPi M' H (Subgroup.inclusion hKH ⟨_, hk⟩)
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext rfl)

theorem map_subtype_starRes {M' H K Y : Subgroup Γ} (hKH : K ≤ H) (hYK : Y ≤ K) :
    ((Y.subgroupOf K).map (starRes M' H K hKH)).map (E2.star M' H K).subtype =
      E2.star M' H Y := by
  ext y
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact mem_star510_iff.mpr ⟨Subgroup.inclusion hKH k, hk, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
    exact ⟨starRes M' H K hKH ⟨x, hYK hx⟩, ⟨⟨x, hYK hx⟩, hx, rfl⟩, rfl⟩

variable [Finite Γ]

theorem map_conjNormal_starRes {M' H K Y : Subgroup Γ} (hKH : K ≤ H) [(E2.star M' H K).Normal]
    {t : ↥H} (htK : (t : Γ) ∈ Subgroup.normalizer (K : Set Γ))
    (htY : (t : Γ) ∈ Subgroup.normalizer (Y : Set Γ)) :
    ((Y.subgroupOf K).map (starRes M' H K hKH)).map
        (MulAut.conjNormal (starPi M' H t)).toMonoidHom =
      (Y.subgroupOf K).map (starRes M' H K hKH) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hk' : (t : Γ) * k * (t : Γ)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htK k).mp k.2
    refine ⟨⟨_, hk'⟩, ?_, (conjNormal_starRes hKH t k hk').symm⟩
    exact (Subgroup.mem_normalizer_iff.mp htY k).mp hk
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conjNormal (starPi M' H t)).toMonoidHom)
      (MulAut.conjNormal (starPi M' H t)).injective]

omit [Finite Γ] in
theorem exists_conj_eq_mul {A S K : Subgroup Γ}
    (hAS : (A : Set Γ) * (S : Set Γ) = (S : Set Γ) * (A : Set Γ)) (hAK : A ≤ K)
    (hSK : S ≤ Subgroup.normalizer (K : Set Γ)) {t a : Γ} (ht : t ∈ S) (ha : a ∈ A) :
    ∃ a' ∈ A, ∃ s ∈ S ⊓ K, t * a * t⁻¹ = a' * s := by
  have h1 : a * t⁻¹ ∈ (A : Set Γ) * (S : Set Γ) := Set.mul_mem_mul ha (S.inv_mem ht)
  rw [hAS] at h1
  obtain ⟨s₁, hs₁, a₁, ha₁, he₁⟩ := h1
  have h2 : t * s₁ * a₁ ∈ (S : Set Γ) * (A : Set Γ) := Set.mul_mem_mul (S.mul_mem ht hs₁) ha₁
  rw [← hAS] at h2
  obtain ⟨a₂, ha₂, s₂, hs₂, he₂⟩ := h2
  dsimp only at he₁ he₂
  have he : t * a * t⁻¹ = a₂ * s₂ := by
    rw [he₂, mul_assoc t s₁ a₁, he₁]
    group
  have hK1 : t * a * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hSK ht) a).mp (hAK ha)
  refine ⟨a₂, ha₂, s₂, ⟨hs₂, ?_⟩, he⟩
  have : s₂ = a₂⁻¹ * (t * a * t⁻¹) := by
    rw [he]
    group
  rw [this]
  exact K.mul_mem (K.inv_mem (hAK ha₂)) hK1

omit [Finite Γ] in
theorem conjNormal_starRes_mem {M' H K A S : Subgroup Γ} (hKH : K ≤ H)
    [(E2.star M' H K).Normal] (hAK : A ≤ K) (hSK : S ≤ Subgroup.normalizer (K : Set Γ))
    (hAS : (A : Set Γ) * (S : Set Γ) = (S : Set Γ) * (A : Set Γ)) {t : ↥H} (ht : (t : Γ) ∈ S)
    {y : ↥(E2.star M' H K)} (hy : y ∈ (A.subgroupOf K).map (starRes M' H K hKH)) :
    MulAut.conjNormal (starPi M' H t) y ∈ (A.subgroupOf K).map (starRes M' H K hKH) ⊔
      ((S ⊓ K).subgroupOf K).map (starRes M' H K hKH) := by
  obtain ⟨k, hk, rfl⟩ := hy
  have hk' : (t : Γ) * k * (t : Γ)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hSK ht) k).mp k.2
  rw [conjNormal_starRes hKH t k hk']
  obtain ⟨a', ha', s, hs, he⟩ := exists_conj_eq_mul hAS hAK hSK ht (Subgroup.mem_subgroupOf.mp hk)
  have he' : (⟨_, hk'⟩ : ↥K) = ⟨a', hAK ha'⟩ * ⟨s, hs.2⟩ := Subtype.ext he
  rw [he', map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, ha', rfl⟩)
    (Subgroup.mem_sup_right ⟨_, hs, rfl⟩)

omit [Finite Γ] in
theorem isMaxParabolic2_of_isCoatom {Y : Type} [Group Y] {L U : Subgroup Y}
    (hU : IsSylowTwoOf U L) {P : Subgroup ↥L} (hP : IsCoatom P)
    (hNP : L ⊓ Subgroup.normalizer (U : Set Y) ≤ P.map L.subtype) :
    IsMaxParabolic2 L (P.map L.subtype) := by
  refine ⟨⟨Subgroup.map_subtype_le P, U, hU, hNP⟩, fun h => hP.1 ?_, fun Q hQ hQL hPQ => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : (x : Y) ∈ P.map L.subtype := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  · have hQ0 : P ≤ Q.subgroupOf L := fun x hx => hPQ ⟨x, hx, rfl⟩
    rcases hP.le_iff.mp hQ0 with h | h
    · exfalso
      apply hQL
      refine le_antisymm hQ.1 fun x hx => ?_
      have : (⟨x, hx⟩ : ↥L) ∈ Q.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
    · rw [← h, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ.1]

theorem exists_conjNormal_map_ne {M' H K S : Subgroup Γ} (hKH : K ≤ H)
    [(E2.star M' H K).Normal]
    (hsyl : IsSylowTwoOf (E2.star M' H (S ⊓ K)) (E2.star M' H K))
    (hD : E2.IsDiagramNontrivial (E2.star M' H S) (E2.star M' H K) (E2.star M' H (S ⊓ K)))
    {P : Subgroup ↥(E2.star M' H K)} (hP : IsCoatom P)
    (hNP : Subgroup.normalizer ((((S ⊓ K).subgroupOf K).map (starRes M' H K hKH) :
      Subgroup ↥(E2.star M' H K)) : Set ↥(E2.star M' H K)) ≤ P) :
    ∃ α ∈ MulAut.conjNormal '' ((E2.star M' H S : Subgroup (E2.StarQuot M' H)) :
      Set (E2.StarQuot M' H)), P.map (α : MulAut ↥(E2.star M' H K)).toMonoidHom ≠ P := by
  have : Finite (E2.StarQuot M' H) := Finite.of_surjective _ (starPi_surjective M' H)
  have hUeq : ((S ⊓ K).subgroupOf K).map (starRes M' H K hKH) =
      (E2.star M' H (S ⊓ K)).subgroupOf (E2.star M' H K) := by
    rw [← map_subtype_starRes (M' := M') hKH inf_le_right]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm
  have hNP' : E2.star M' H K ⊓
      Subgroup.normalizer ((E2.star M' H (S ⊓ K) : Subgroup (E2.StarQuot M' H)) :
        Set (E2.StarQuot M' H)) ≤ P.map (E2.star M' H K).subtype := by
    rintro y ⟨hyL, hyN⟩
    refine ⟨⟨y, hyL⟩, hNP ?_, rfl⟩
    rw [hUeq]
    exact (E2.BorelLift.mem_normalizer_subgroupOf_iff hsyl.1 ⟨y, hyL⟩).mpr hyN
  have hnot := hD _ (isMaxParabolic2_of_isCoatom hsyl hP hNP') hNP'
  rw [IsConcreteLE.not_le_iff_exists] at hnot
  obtain ⟨g, hgS, hgN⟩ := hnot
  refine ⟨MulAut.conjNormal g, ⟨g, hgS, rfl⟩, fun hPg => hgN ?_⟩
  refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' : MulAut.conjNormal g z ∈ P := by
    rw [← hPg]
    exact ⟨z, hz, rfl⟩
  exact ⟨_, hz', by simp [MulAut.conjNormal_apply]⟩

theorem not_le_of_case_psl3 {H S MH K B A R : Subgroup Γ} {n p : ℕ}
    (hmin : MinParabolic H S MH) (hK : K ∈ cComp H) (hHK : H = K ⊔ S)
    (hTK : S ≤ Subgroup.normalizer (K : Set Γ))
    (hJ : ∀ x : Γ, x ∈ kerIn MH H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star MH H K) (E2.star MH H (MH ⊓ K)))
    (hY : IsPSL 3 2 n ↥(E2.star MH H K))
    (hD : E2.IsDiagramNontrivial (E2.star MH H S) (E2.star MH H K) (E2.star MH H (S ⊓ K)))
    (hRS : R ≤ S) (hMR : MH ≤ Subgroup.normalizer (R : Set Γ)) (hBM : B ≤ MH)
    (hBo : Odd (Nat.card B)) (hBR : MH ⊓ oTwoUpper H ≤ B ⊔ R) (hBab : IsMulCommutative ↥B)
    (hp : p.Prime) (hp3 : 3 < p) (hAB : A ≤ B) (hA : ∀ a ∈ A, a ^ p = 1)
    (hAS : (A : Set Γ) * (S : Set Γ) = (S : Set Γ) * (A : Set Γ)) :
    ¬ H ⊓ Subgroup.normalizer (A : Set Γ) ≤ MH := by
  have hT : IsSylowTwoOf S H := hmin.isSylow
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHN : H ≤ Subgroup.normalizer (K : Set Γ) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hAK : A ≤ K := hAB.trans (le_of_case_two hmin hK hHK hTK hBM hBo)
  have : (E2.star MH H K).Normal := star_normal hKH hHN
  have hsyl : IsSylowTwoOf (E2.star MH H (S ⊓ K)) (E2.star MH H K) :=
    E2.BorelLift.sylow_star hT hK
  refine not_le_of_case_two_of hmin hK hHK hTK hJ hB hRS hMR hBM hBo hBR hBab hAB hA ?_
  intro X _ _ φ hφ hker hodd hperf S' D' A' hS' hD'N hND' hD'S hD'ab hA'D hA'p hSφ hAφ
  refine exists_mem_normalizer_of_cover_psl3 hY hperf φ hφ hker hodd hS' hD'N hND' hD'S hD'ab
    hp hp3 hA'D hA'p (MulAut.conjNormal '' ((E2.star MH H S : Subgroup (E2.StarQuot MH H)) :
      Set (E2.StarQuot MH H))) ?_ ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨t, htS, rfl⟩ := mem_star510_iff.mp hg
    have htN : (t : Γ) ∈ Subgroup.normalizer ((S ⊓ K : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf,
        Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer htS) y,
        Subgroup.mem_normalizer_iff.mp (hTK htS) y]
    rw [hSφ]
    exact map_conjNormal_starRes hKH (hTK htS) htN
  · intro P hP hNP
    rw [hSφ] at hNP
    exact exists_conjNormal_map_ne hKH hsyl hD hP hNP
  · rintro _ ⟨g, hg, rfl⟩ a ha
    obtain ⟨t, htS, rfl⟩ := mem_star510_iff.mp hg
    rw [hAφ] at ha
    rw [hAφ, hSφ]
    exact conjNormal_starRes_mem hKH hAK hTK hAS htS ha

end CFSG.Quasithin.H13.KG4413
