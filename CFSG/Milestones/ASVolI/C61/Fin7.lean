module

public import CFSG.Milestones.ASVolI.C61.Fin6
public import CFSG.Milestones.ASVolI.C61.Fin3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G G' : Type} [Group G] [Group G'] {H Λ : Subgroup G} {ι : ↥H →* G'} {κ : ↥Λ →* G'}

theorem burnsideC56_fin_c6 (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l) (hsyl : IsSylowTwoOf (Λ ⊓ H) H)
    (c6 : ((((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι).relIndex
          ((⊤ : Subgroup ↥Λ).map κ) = 2 ∧
        thompsonJ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) =
          thompsonJ ((⊤ : Subgroup ↥Λ).map κ) ∧
        ((IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) ∧
            IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 3) →
          Nonempty (↥((⊤ : Subgroup ↥H).map ι) ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
      (IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) ∧
        IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 3 ∧
        Nonempty (↥((⊤ : Subgroup ↥H).map ι) ≃* Equiv.Perm (Fin 4)) ∧
        IsDihedralOrSemidihedral ((⊤ : Subgroup ↥Λ).map κ)) ∨
      (((IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) ∧
            IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 5) ∨
          IsA3Product ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) 2) ∧
        thompsonJ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) =
          thompsonJ ((⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
            (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι : Subgroup G') : Set G')) ∧
        QuotHas ((⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
            (((⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
              (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι : Subgroup G') : Set G') :
                Subgroup G') : Set G'))
          (thompsonJ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι))
          (fun Y _ => Nonempty (Y ≃* DihedralGroup 4)) ∧
        ∀ x ∈ (⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
            (((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι : Subgroup G') : Set G'),
          x ∉ (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι →
          ∀ (A₁ : Subgroup G') (r : G'),
            r ∈ (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι →
            r ∉ thompsonJ ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) →
            (A₁ ⊓ pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)).relIndex A₁ = 2 →
            AFam ((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι) =
              {pCoreOf 2 ((⊤ : Subgroup ↥H).map ι),
                ChC.rconj x (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)), A₁, ChC.rconj r A₁} →
            Nat.card ↥((⊤ : Subgroup ↥Λ).map κ ⊓ Subgroup.normalizer
              ((A₁ ⊔ pCoreOf 2 ((⊤ : Subgroup ↥H).map ι) : Subgroup G') : Set G')) ≥
              Nat.card ↥((⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι)))) :
    ((Λ ⊓ H).relIndex Λ = 2 ∧ thompsonJ (Λ ⊓ H) = thompsonJ Λ ∧
      ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3) →
        Nonempty (↥H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
    (IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3 ∧
      Nonempty (↥H ≃* Equiv.Perm (Fin 4)) ∧ IsDihedralOrSemidihedral Λ) ∨
    (((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) ∧
      thompsonJ (Λ ⊓ H) = thompsonJ (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) ∧
      QuotHas (Λ ⊓ Subgroup.normalizer ((Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G) :
          Subgroup G) : Set G)) (thompsonJ (Λ ⊓ H))
        (fun Y _ => Nonempty (Y ≃* DihedralGroup 4)) ∧
      ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        ∀ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H → r ∉ thompsonJ (Λ ⊓ H) →
          (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 →
          AFam (Λ ⊓ H) = {pCoreOf 2 H, ChC.rconj x (pCoreOf 2 H), A₁, ChC.rconj r A₁} →
          Nat.card ↥(Λ ⊓ Subgroup.normalizer ((A₁ ⊔ pCoreOf 2 H : Subgroup G) : Set G)) ≥
            Nat.card ↥(Λ ⊓ H)) := by
  have hsΛ := Λ.subtype_injective
  have hQ : pCoreOf 2 H ≤ Λ ⊓ H := hsyl.pCoreOf_le
  set CL := (Λ ⊓ H).subgroupOf Λ with hCLdef
  set QL := (pCoreOf 2 H).subgroupOf Λ with hQLdef
  have hC := burnsideC56_finL_C hag hmeet
  have hC' : CL.map Λ.subtype = Λ ⊓ H := burnsideC56_finL_C'
  have hQ' := burnsideC56_finL_Q hι hag hQ
  have hQ'' : QL.map Λ.subtype = pCoreOf 2 H := burnsideC56_finL_Q' hQ
  have hΛt : (⊤ : Subgroup ↥Λ).map Λ.subtype = Λ := burnsideC56_fin_top Λ
  rcases c6 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    rw [hC, burnsideC56_tr_relIndex hκ] at h1
    rw [hC, burnsideC56_tr_thompsonJ hκ, burnsideC56_tr_thompsonJ hκ] at h2
    refine ⟨?_, ?_, fun hcond => ?_⟩
    · have := (burnsideC56_tr_relIndex hsΛ CL ⊤).trans h1
      rwa [hC', hΛt] at this
    · have e : thompsonJ CL = thompsonJ (⊤ : Subgroup ↥Λ) := Subgroup.map_injective hκ h2
      have := congrArg (Subgroup.map Λ.subtype) e
      rw [← burnsideC56_tr_thompsonJ hsΛ, ← burnsideC56_tr_thompsonJ hsΛ, hC', hΛt] at this
      exact this
    · rw [burnsideC56_finH_mulEquiv hι]
      exact h3 ⟨(burnsideC56_finH_isBlock2 hι).mp hcond.1,
        (burnsideC56_finH_isAltType hι 3).mp hcond.2⟩
  · right; left
    refine ⟨(burnsideC56_finH_isBlock2 hι).mpr h1, (burnsideC56_finH_isAltType hι 3).mpr h2,
      (burnsideC56_finH_mulEquiv hι _).mpr h3, ?_⟩
    have := (burnsideC56_tr_isDihedralOrSemidihedral hsΛ (⊤ : Subgroup ↥Λ)).mpr
      ((burnsideC56_tr_isDihedralOrSemidihedral hκ _).mp h4)
    rwa [hΛt] at this
  · right; right
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [← burnsideC56_finH_isBlock2 hι, ← burnsideC56_finH_isAltType hι,
        ← burnsideC56_finH_isA3Product hι] at h1
      exact h1
    · rw [hC, burnsideC56_finL_N hκ, burnsideC56_tr_thompsonJ hκ, burnsideC56_tr_thompsonJ hκ] at h2
      rw [← hC', burnsideC56_finL_N', burnsideC56_tr_thompsonJ hsΛ, burnsideC56_tr_thompsonJ hsΛ,
        Subgroup.map_injective hκ h2]
    · rw [hC, burnsideC56_finL_N hκ, burnsideC56_finL_N hκ, burnsideC56_tr_thompsonJ hκ,
        burnsideC56_tr_quotHas hκ] at h3
      rw [← hC', burnsideC56_finL_N', burnsideC56_finL_N', burnsideC56_tr_thompsonJ hsΛ,
        burnsideC56_tr_quotHas hsΛ]
      exact h3
    · intro x hx hxC A₁ r hr hrJ hidx hAF
      rw [← hC', burnsideC56_finL_N'] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      have hx₀C : x₀ ∉ CL := fun h => hxC (hC' ▸ Subgroup.mem_map_of_mem _ h)
      have hA₁mem : A₁ ∈ AFam (Λ ⊓ H) := by rw [hAF]; simp
      have hA₁le : A₁ ≤ Λ := hA₁mem.1.trans inf_le_left
      set A₁₀ := A₁.subgroupOf Λ with hA₁₀def
      have hA₁ : A₁₀.map Λ.subtype = A₁ := burnsideC56_fin_sub hA₁le
      rw [← hC'] at hr hrJ
      obtain ⟨r₀, hr₀, rfl⟩ := hr
      rw [burnsideC56_tr_thompsonJ hsΛ] at hrJ
      rw [← hA₁, ← hQ'', burnsideC56_fin_relIndex_inf hsΛ] at hidx
      rw [← hC', ← hA₁, ← hQ'', show (Λ.subtype x₀ : G) = Λ.subtype x₀ from rfl,
        burnsideC56_tr_rconj hsΛ, burnsideC56_tr_rconj hsΛ, ← burnsideC56_fin_image_four,
        burnsideC56_fin_AFam_eq hsΛ] at hAF
      have h5 := h4 (κ x₀) (by rw [hC, burnsideC56_finL_N hκ]; exact Subgroup.mem_map_of_mem κ hx₀)
        (by rw [hC]; exact fun h => hx₀C ((Subgroup.mem_map_iff_mem hκ).mp h))
        (A₁₀.map κ) (κ r₀) (by rw [hC]; exact Subgroup.mem_map_of_mem κ hr₀)
        (by
          rw [hC, burnsideC56_tr_thompsonJ hκ]
          exact fun h => hrJ (Subgroup.mem_map_of_mem _ ((Subgroup.mem_map_iff_mem hκ).mp h)))
        (by rw [hQ', burnsideC56_fin_relIndex_inf hκ]; exact hidx)
        (by
          rw [hC, hQ', burnsideC56_tr_rconj hκ, burnsideC56_tr_rconj hκ,
            ← burnsideC56_fin_image_four, burnsideC56_fin_AFam_eq hκ]
          exact hAF)
      rw [hQ', ← Subgroup.map_sup, burnsideC56_finL_N hκ, burnsideC56_tr_card hκ, hC,
        burnsideC56_tr_card hκ] at h5
      rw [← hA₁, ← hQ'', ← Subgroup.map_sup, burnsideC56_finL_N', burnsideC56_tr_card hsΛ, ← hC',
        burnsideC56_tr_card hsΛ]
      exact h5

theorem burnsideC56_C61_of_fin
    (hfin : ∀ (G : Type) [Group G] [Finite G] (H Λ : Subgroup G) [Finite H] [Finite Λ],
      CharTwo H →
      ((∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2))) →
      IsPGroup 2 Λ → IsSylowTwoOf (Λ ⊓ H) H →
      Λ ⊓ H < Λ →
      (∀ T₀ : Subgroup G, T₀ ≠ ⊥ → T₀ ≤ Λ ⊓ H → H ≤ Subgroup.normalizer (T₀ : Set G) →
        Λ ⊓ Subgroup.normalizer (T₀ : Set G) = Λ ⊓ H) →
      ((Λ ⊓ H).relIndex (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) = 2 ∧
        thompsonJ (Λ ⊓ H) = baum (Λ ⊓ H) ∧
        ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
          (baum (Λ ⊓ H) : Set G) = (pCoreOf 2 H : Set G) * (rconj x (pCoreOf 2 H) : Set G)) ∧
      ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
          IsAltType (oTwoUpper H) 5)) ∨
        IsA3Product H (oTwoUpper H) 1 ∨ IsA3Product H (oTwoUpper H) 2) ∧
      (∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
            IsAltType (oTwoUpper H) 3)) →
          AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H)}) ∧
        (∀ n : ℕ, 1 < n → IsBlock2 H (oTwoUpper H) → IsLin2Type (oTwoUpper H) n →
          ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
            IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n) ∧
        (IsBlock2 H (oTwoUpper H) → IsAltType (oTwoUpper H) 3 →
          ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
            IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ 1)) ∧
      (∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) →
        ∃ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H ∧ r ∉ thompsonJ (Λ ⊓ H) ∧
          (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
          AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H), A₁, rconj r A₁}) ∧
      ((pCoreOf 2 H : Set G) =
        (((Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) *
          (pCoreOf 2 (oTwoUpper H) : Set G)) ∧
      (((Λ ⊓ H).relIndex Λ = 2 ∧ thompsonJ (Λ ⊓ H) = thompsonJ Λ ∧
        ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3) →
          Nonempty (↥H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
      (IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3 ∧
        Nonempty (↥H ≃* Equiv.Perm (Fin 4)) ∧ IsDihedralOrSemidihedral Λ) ∨
      (((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) ∧
        thompsonJ (Λ ⊓ H) = thompsonJ (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) ∧
        QuotHas (Λ ⊓ Subgroup.normalizer ((Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G) :
            Subgroup G) : Set G)) (thompsonJ (Λ ⊓ H))
          (fun Y _ => Nonempty (Y ≃* DihedralGroup 4)) ∧
        ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
          ∀ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H → r ∉ thompsonJ (Λ ⊓ H) →
            (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 →
            AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H), A₁, rconj r A₁} →
            Nat.card ↥(Λ ⊓ Subgroup.normalizer ((A₁ ⊔ pCoreOf 2 H : Subgroup G) : Set G)) ≥
              Nat.card ↥(Λ ⊓ H)))) :
    C_6_1 := by
  intro G _ H Λ _ _ hc hi hΛ2 hsyl hlt hiv
  haveI : Finite ↥(Λ ⊓ H) := Finite.of_injective (fun x : ↥(Λ ⊓ H) => (⟨x, x.2.2⟩ : ↥H))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hι := burnsideC56_iota_injective H Λ
  have hκ := burnsideC56_kappa_injective H Λ
  have hag := burnsideC56_iota_eq_kappa H Λ
  have hmeet := burnsideC56_iota_eq_kappa_iff H Λ
  obtain ⟨hc', hi', hΛ2', hsyl', hlt', hiv'⟩ :=
    burnsideC56_fin_hyps hι hκ hag hmeet hc hi hΛ2 hsyl hlt hiv
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hfin (Equiv.Perm (burnsideC56_Om H Λ))
    ((⊤ : Subgroup ↥H).map (burnsideC56_iota H Λ)) ((⊤ : Subgroup ↥Λ).map (burnsideC56_kappa H Λ))
    hc' hi' hΛ2' hsyl' hlt' hiv'
  exact ⟨burnsideC56_fin_c1 hι hκ hag hmeet hsyl c1, burnsideC56_fin_c2 hι c2,
    burnsideC56_fin_c3 hι hκ hag hmeet hsyl c3, burnsideC56_fin_c4 hι hκ hag hmeet hsyl c4,
    burnsideC56_fin_c5 hι hag hmeet c5, burnsideC56_fin_c6 hι hκ hag hmeet hsyl c6⟩

end CFSG.ASVolI
