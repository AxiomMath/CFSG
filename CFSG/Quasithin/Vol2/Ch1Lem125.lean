module

public import CFSG.Quasithin.Vol2.Ch1Proj
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Vol2.Ch1Local

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem commutator_sSup_le {H N A : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (h𝒞 : ∀ K ∈ 𝒞, K ≤ H)
    (hc : ∀ K ∈ 𝒞, ⁅A, K⁆ ≤ N) : ⁅A, sSup 𝒞⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro a ha x hx
  rw [sSup_eq_iSup'] at hx
  refine (Subgroup.iSup_induction (fun K : 𝒞 => (K : Subgroup G))
    (C := fun x => ⁅a, x⁆ ∈ N ∧ x ∈ H) hx ?_ ?_ ?_).1
  · intro K x hx
    exact ⟨hc K K.2 (Subgroup.commutator_mem_commutator ha hx), h𝒞 K K.2 hx⟩
  · exact ⟨by simp, H.one_mem⟩
  · rintro x y ⟨hx1, hxH⟩ ⟨hy1, hyH⟩
    have h1 : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    exact ⟨by rw [h1]; exact N.mul_mem hx1 ((Subgroup.mem_normalizer_iff.mp (hN hxH) _).mp hy1),
      H.mul_mem hxH hyH⟩

theorem conj_mem_sSup {E : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h : ∀ K ∈ 𝒞, K ≤ E ∧ (K.subgroupOf E).Normal) {e x : G} (he : e ∈ E) (hx : x ∈ sSup 𝒞) :
    e * x * e⁻¹ ∈ sSup 𝒞 := by
  rw [sSup_eq_iSup'] at hx ⊢
  refine Subgroup.iSup_induction (fun K : 𝒞 => (K : Subgroup G))
    (C := fun x => e * x * e⁻¹ ∈ ⨆ K : 𝒞, (K : Subgroup G)) hx ?_ ?_ ?_
  · intro K x hxK
    have h1 : e * x * e⁻¹ ∈ (K : Subgroup G) :=
      (Subgroup.normal_subgroupOf_iff (h K K.2).1).mp (h K K.2).2 x e hxK he
    exact Subgroup.mem_iSup_of_mem K h1
  · simp
  · intro x y hx hy
    simpa [mul_assoc] using Subgroup.mul_mem _ hx hy

theorem TwoCosets.subgroupOf' {A B : Subgroup G} (h : TwoCosets A B) (C : Subgroup G) :
    TwoCosets (A.subgroupOf C) (B.subgroupOf C) := by
  intro a ha b hb c hc
  rcases h a ha b hb c hc with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem commutator_subgroupOf {A B E : Subgroup G} (hA : A ≤ E) (hB : B ≤ E) :
    ⁅A.subgroupOf E, B.subgroupOf E⁆ = (⁅A, B⁆).subgroupOf E := by
  have h1 : ⁅A, B⁆ ≤ E := (Subgroup.commutator_mono hA hB).trans (A3.commutator_self_le E)
  apply Subgroup.map_injective E.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le h1]

end Generic

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_subgroupOf_of_le {S H E : Subgroup G} (hS : IsSylowTwoOf S H) (hHE : H ≤ E) :
    IsSylowTwoOf (S.subgroupOf E) (H.subgroupOf E) := by
  rw [A4.isSylowTwoOf_iff_maximal] at hS ⊢
  obtain ⟨hSH, hS2, hmax⟩ := hS
  refine ⟨fun x hx => hSH hx, A4.isPGroup_subgroupOf_of_le (hSH.trans hHE) hS2,
    fun P hPH hP hSP => ?_⟩
  have hPH' : P.map E.subtype ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPH hx
  have hSP' : S ≤ P.map E.subtype := fun s hs =>
    ⟨⟨s, hHE (hSH hs)⟩, hSP (show (⟨s, hHE (hSH hs)⟩ : ↥E) ∈ S.subgroupOf E from hs), rfl⟩
  have := hmax _ hPH' (hP.map E.subtype) hSP'
  intro x hx
  exact this ⟨x, hx, rfl⟩

theorem lemma_1_2_5_exists_of_a3_sq {H S R L : Subgroup G} (hS : IsSylowTwoOf S H) (hRS : R ≤ S)
    (hidx : R.relIndex S ≤ 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H)
    (h37H : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H))
    (h37M : A37Statement (↥(L ⊔ R) ⧸ CFSG.pCore 2 ↥(L ⊔ R)))
    (hEcore : cCompSpan H = perfectCore H) : ∃ K ∈ cComp H, L ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : L ∈ cComp (L ⊔ R) := cComp_of_isLocal hL
  have hRsyl : IsSylowTwoOf R (L ⊔ R) := ⟨le_sup_right, hL.1, hL.2.2.1⟩
  have hLE : L ≤ cCompSpan H := by
    rw [hEcore]; exact le_perfectCore_of_perfect hLH (perfect_of_mem_cComp hLc)
  have hEH : cCompSpan H ≤ H := by rw [hEcore]; exact perfectCore_le H
  have hEnorm : H ≤ Subgroup.normalizer (cCompSpan H : Set G) := by
    rw [hEcore]; exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore H)
  have hO2n : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hpick : ∃ K ∈ cComp H, ¬ L ≤ sSup (cComp H \ {K}) := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ K ∈ cComp H, ⁅L, K⁆ ≤ pCoreOf 2 H := by
      intro K hK
      have h1 : ⁅sSup (cComp H \ {K}), K⁆ ≤ pCoreOf 2 H := by
        rw [Subgroup.commutator_comm]
        refine commutator_sSup_le hO2n (fun K' hK' => le_of_mem_cComp hK'.1) (fun K' hK' => ?_)
        exact commutator_le_pCoreOf_of_ne h37H hK hK'.1 (fun h => hK'.2 h.symm)
      exact (Subgroup.commutator_mono (hcon K hK) le_rfl).trans h1
    have h2 : ⁅L, cCompSpan H⁆ ≤ pCoreOf 2 H :=
      commutator_sSup_le hO2n (fun K hK => le_of_mem_cComp hK) hcomm
    have h3 : L ≤ pCoreOf 2 H :=
      calc L = ⁅L, L⁆ := (perfect_of_mem_cComp hLc).symm
        _ ≤ ⁅L, cCompSpan H⁆ := Subgroup.commutator_mono le_rfl hLE
        _ ≤ pCoreOf 2 H := h2
    have : Group.IsNilpotent ↥L :=
      (((pCoreOf_isPGroup 2 H).to_le h3)).isNilpotent
    exact not_isSolvable_of_mem_cComp hLc inferInstance
  obtain ⟨K, hK, hLK'⟩ := hpick
  set K' := sSup (cComp H \ {K}) with hK'def
  obtain ⟨hKE, hKn⟩ := cComp_normal_span_of_le hK
  have hK'E : K' ≤ cCompSpan H := sSup_le_sSup Set.sdiff_subset
  have hKK'sup : K ⊔ K' = cCompSpan H := by
    have h1 : insert K (cComp H \ {K}) = cComp H := by
      rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hK]
    calc K ⊔ K' = sSup (insert K (cComp H \ {K})) := sSup_insert.symm
      _ = cCompSpan H := by rw [h1]; rfl
  have hEK' : cCompSpan H ≤ Subgroup.normalizer (K' : Set G) := by
    have key : ∀ e ∈ cCompSpan H, ∀ x ∈ K', e * x * e⁻¹ ∈ K' := fun e he x hx =>
      conj_mem_sSup (fun K'' hK'' => cComp_normal_span_of_le hK''.1) he hx
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key e he x hx, fun hx => ?_⟩
    have := key e⁻¹ (Subgroup.inv_mem _ he) _ hx
    simpa [mul_assoc] using this
  have hLcL : L ∈ cComp L := by
    rw [cComp_self_eq_singleton hLc]; exact Set.mem_singleton L
  have hTwo : TwoCosets R S := twoCosets_of_relIndex_le_two hidx
  have hD : IsSylowTwoOf (R ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hLc) hRsyl
  have hS₁ : IsSylowTwoOf ((S ⊓ cCompSpan H).subgroupOf (cCompSpan H)) ⊤ :=
    isSylowTwoOf_top_subgroupOf (A4.isSylowTwoOf_inf_normal hS hEH hEnorm)
  have hΛ : L.subgroupOf (cCompSpan H) ∈ cComp (L.subgroupOf (cCompSpan H)) :=
    subgroupOf_mem_cComp_of_le hLE hLcL
  have hΛK' : ¬ L.subgroupOf (cCompSpan H) ≤ K'.subgroupOf (cCompSpan H) := fun h =>
    hLK' fun l hl => h (show (⟨l, hLE hl⟩ : ↥(cCompSpan H)) ∈ L.subgroupOf (cCompSpan H) from hl)
  have hR₁ : (R ⊓ cCompSpan H).subgroupOf (cCompSpan H) ≤
      (S ⊓ cCompSpan H).subgroupOf (cCompSpan H) := fun x hx => by
    have hx' : (x : G) ∈ R ⊓ cCompSpan H := hx
    exact (⟨hRS hx'.1, hx'.2⟩ : (x : G) ∈ S ⊓ cCompSpan H)
  have h2 : TwoCosets ((R ⊓ cCompSpan H).subgroupOf (cCompSpan H))
      ((S ⊓ cCompSpan H).subgroupOf (cCompSpan H)) := (hTwo.inf (cCompSpan H)).subgroupOf' _
  have hD' : IsSylowTwoOf ((R ⊓ cCompSpan H).subgroupOf (cCompSpan H) ⊓
      L.subgroupOf (cCompSpan H)) (L.subgroupOf (cCompSpan H)) := by
    have e : (R ⊓ cCompSpan H).subgroupOf (cCompSpan H) ⊓ L.subgroupOf (cCompSpan H) =
        (R ⊓ L).subgroupOf (cCompSpan H) := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, x.2⟩, h.2⟩⟩
    rw [e]
    exact isSylowTwoOf_subgroupOf_of_le hD hLE
  have hZ : IsPGroup 2 ((pCoreOf 2 (L ⊔ R) ⊓ cCompSpan H).subgroupOf (cCompSpan H)) :=
    A4.isPGroup_subgroupOf_of_le inf_le_right (pCoreOf_isPGroup 2 (L ⊔ R)).to_inf_left
  have hKL : ∀ r ∈ (R ⊓ cCompSpan H).subgroupOf (cCompSpan H),
      (L.subgroupOf (cCompSpan H)).map (MulAut.conj r).toMonoidHom = L.subgroupOf (cCompSpan H) ∨
        ⁅L.subgroupOf (cCompSpan H), (L.subgroupOf (cCompSpan H)).map (MulAut.conj r).toMonoidHom⁆ ≤
          (pCoreOf 2 (L ⊔ R) ⊓ cCompSpan H).subgroupOf (cCompSpan H) := by
    intro r hr
    have hr' : (r : G) ∈ R ⊓ cCompSpan H := hr
    have hr'M : (r : G) ∈ L ⊔ R := (le_sup_right : R ≤ L ⊔ R) hr'.1
    have hLr : L.map (MulAut.conj (r : G)).toMonoidHom ∈ cComp (L ⊔ R) :=
      map_conj_mem_cComp hLc hr'M
    have hconj : (L.subgroupOf (cCompSpan H)).map (MulAut.conj r).toMonoidHom =
        (L.map (MulAut.conj (r : G)).toMonoidHom).subgroupOf (cCompSpan H) := by
      ext y
      rw [A38.mem_map_conj, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, A38.mem_map_conj]
      rfl
    have hLrE : L.map (MulAut.conj (r : G)).toMonoidHom ≤ cCompSpan H := by
      rintro _ ⟨x, hx, rfl⟩
      exact (cCompSpan H).mul_mem ((cCompSpan H).mul_mem hr'.2 (hLE hx))
        ((cCompSpan H).inv_mem hr'.2)
    by_cases hne : L.map (MulAut.conj (r : G)).toMonoidHom = L
    · left
      rw [hconj, hne]
    · right
      rw [hconj, commutator_subgroupOf hLE hLrE]
      have h1 := commutator_le_pCoreOf_of_ne h37M hLc hLr (Ne.symm hne)
      intro x hx
      exact ⟨h1 hx, x.2⟩
  have hProj := le_of_projection (X := ↥(cCompSpan H))
    (K := K.subgroupOf (cCompSpan H)) (K' := K'.subgroupOf (cCompSpan H))
    (Λ := L.subgroupOf (cCompSpan H))
    (S₁ := (S ⊓ cCompSpan H).subgroupOf (cCompSpan H))
    (R₁ := (R ⊓ cCompSpan H).subgroupOf (cCompSpan H))
    (Z := (pCoreOf 2 (L ⊔ R) ⊓ cCompSpan H).subgroupOf (cCompSpan H))
    hKn ((Subgroup.normal_subgroupOf_iff_le_normalizer hK'E).mpr hEK')
    (by rw [← Subgroup.subgroupOf_sup hKE hK'E, hKK'sup, Subgroup.subgroupOf_self])
    hΛ hΛK' hS₁ hR₁ h2 hD' hZ hKL
  exact ⟨K, hK, fun l hl =>
    hProj (show (⟨l, hLE hl⟩ : ↥(cCompSpan H)) ∈ L.subgroupOf (cCompSpan H) from hl)⟩

theorem lemma_1_2_5_exists (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    {H S R L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hRS : R ≤ S)
    (hidx : R.relIndex S ≤ 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H) :
    ∃ K ∈ cComp H, L ≤ K :=
  lemma_1_2_5_exists_of_a3_sq hS hRS hidx hL hLH
    (h37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hH))
    (h37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hL.2.2.2))
    (lemma_1_2_1_one hQ hs hnab h39 hH)

theorem lemma_1_2_5 (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    {H S R L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hRS : R ≤ S)
    (hidx : R.relIndex S ≤ 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H) :
    ∃! K, K ∈ cComp H ∧ L ≤ K := by
  obtain ⟨K, hK, hLK⟩ := lemma_1_2_5_exists hQ hs hnab h37 h39 hH hS hRS hidx hL hLH
  have hQH := sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hH
  refine ⟨K, ⟨hK, hLK⟩, fun K' hK' => ?_⟩
  exact lemma_1_2_4_unique (h37 _ hQH) (mem_lFamily_of_isLocal hL) hK'.1 hK hK'.2 hLK

theorem lemma_1_2_5_of_relIndex_eq_two (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    {H S R L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hRS : R ≤ S)
    (hidx : R.relIndex S = 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H) :
    ∃! K, K ∈ cComp H ∧ L ≤ K :=
  lemma_1_2_5 hQ hs hnab h37 h39 hH hS hRS hidx.le hL hLH

end Ambient

end CFSG.Quasithin
