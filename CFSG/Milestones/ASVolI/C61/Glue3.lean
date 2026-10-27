module

public import CFSG.Milestones.ASVolI.C61.Glue2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCExcl
public import CFSG.Milestones.ASVolI.C61.CS
public import CFSG.Milestones.ASVolI.C61.Tr3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H Λ K₁ : Subgroup G}

@[expose] def burnsideC56_glue_Case (H S K₁ : Subgroup G) : Prop :=
  (conjJoin S K₁ = K₁ ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 5) ∧
      ¬ IsA3Product H (oTwoUpper H) 1 ∧ ¬ IsA3Product H (oTwoUpper H) 2) ∨
    (conjJoin S K₁ = K₁ ∧ IsAltType K₁ 3 ∧ ¬ IsA3Product H (oTwoUpper H) 2) ∨
    (conjJoin S K₁ ≠ K₁ ∧ IsAltType K₁ 3 ∧ ¬ IsBlock2 H (oTwoUpper H))

theorem burnsideC56_glue_map_conj_self {t : G} (ht : t ∈ H) :
    H.map (MulAut.conj t).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact H.mul_mem (H.mul_mem ht hh) (H.inv_mem ht)
  · intro hx
    refine ⟨t⁻¹ * x * t, H.mul_mem (H.mul_mem (H.inv_mem ht) hx) ht, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem burnsideC56_glue_A3Product (hcs : burnsideC56_CS G Λ ⊤ H (Λ ⊓ H) K₁)
    (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H) (h3 : IsAltType K₁ 3)
    (hne : conjJoin (Λ ⊓ H) K₁ ≠ K₁) : IsA3Product H (oTwoUpper H) 2 := by
  rcases hcs.blocks with hj | ⟨t, ht, hK, hjoin2, hcomm⟩
  · exact absurd hj hne
  have hf : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have htH : t ∈ H := ht.2
  refine ⟨K₁, hcs.block.1, h3, Or.inr ⟨rfl, K₁.map (MulAut.conj t).toMonoidHom, hK,
    ?_, (burnsideC56_tr_isAltType hf K₁ 3).mpr h3,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm, by rw [← hjoin, hjoin2]⟩⟩
  have := (burnsideC56_tr_isBlock2 hf H K₁).mpr hcs.block.1
  rwa [burnsideC56_glue_map_conj_self htH] at this

theorem burnsideC56_glue_c2 (hcs : burnsideC56_CS G Λ ⊤ H (Λ ⊓ H) K₁)
    (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H) (hcase : burnsideC56_glue_Case H (Λ ⊓ H) K₁) :
    (IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
        IsAltType (oTwoUpper H) 5)) ∨
      IsA3Product H (oTwoUpper H) 1 ∨ IsA3Product H (oTwoUpper H) 2 := by
  rcases hcase with ⟨hj, hL, -, -⟩ | ⟨hj, h3, -⟩ | ⟨hne, h3, -⟩
  · rw [burnsideC56_glue_L_eq hjoin hj]
    exact Or.inl ⟨hcs.block.1, hL⟩
  · rw [burnsideC56_glue_L_eq hjoin hj]
    exact Or.inr (Or.inl ⟨K₁, hcs.block.1, h3, Or.inl ⟨rfl, rfl⟩⟩)
  · exact Or.inr (Or.inr (burnsideC56_glue_A3Product hcs hjoin h3 hne))

theorem burnsideC56_glue_c3 (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H)
    (hcase : burnsideC56_glue_Case H (Λ ⊓ H) K₁) (hC : C61Concl Λ H (Λ ⊓ H) K₁) :
    ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
      ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
          IsAltType (oTwoUpper H) 3)) →
        AFam (Λ ⊓ H) = {pCoreOf 2 H, ChC.rconj x (pCoreOf 2 H)}) ∧
      (∀ n : ℕ, 1 < n → IsBlock2 H (oTwoUpper H) → IsLin2Type (oTwoUpper H) n →
        ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
          IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n) ∧
      (IsBlock2 H (oTwoUpper H) → IsAltType (oTwoUpper H) 3 →
        ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
          IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ 1) := by
  intro x hx hxS
  obtain ⟨-, h2, -⟩ := hC
  rcases hcase with ⟨hj, -, -, -⟩ | ⟨hj, -, -⟩ | ⟨-, -, hnb⟩
  · have hL := burnsideC56_glue_L_eq hjoin hj
    rw [hL]
    refine ⟨fun hc' => ?_, fun n hn _ hlin B hB _ => ?_, fun _ h3 B hB _ => ?_⟩
    · have hA := (h2 hj hc'.2).1 x hx hxS
      ext A
      exact hA A
    · have hb := (h2 hj (Or.inl ⟨n, hn, hlin⟩)).2.2 n hn hlin
      rw [← hL, ← burnsideC56_glue_blockD hjoin] at hB
      exact (Subgroup.card_le_of_le hB).trans hb
    · have hb := (h2 hj (Or.inr h3)).2.1 h3
      rw [← hL, ← burnsideC56_glue_blockD hjoin] at hB
      exact (Subgroup.card_le_of_le hB).trans hb
  · have hL := burnsideC56_glue_L_eq hjoin hj
    rw [hL]
    refine ⟨fun hc' => ?_, fun n hn _ hlin B hB _ => ?_, fun _ h3 B hB _ => ?_⟩
    · have hA := (h2 hj hc'.2).1 x hx hxS
      ext A
      exact hA A
    · have hb := (h2 hj (Or.inl ⟨n, hn, hlin⟩)).2.2 n hn hlin
      rw [← hL, ← burnsideC56_glue_blockD hjoin] at hB
      exact (Subgroup.card_le_of_le hB).trans hb
    · have hb := (h2 hj (Or.inr h3)).2.1 h3
      rw [← hL, ← burnsideC56_glue_blockD hjoin] at hB
      exact (Subgroup.card_le_of_le hB).trans hb
  · exact ⟨fun h => absurd h.1 hnb, fun _ _ h => absurd h hnb, fun h => absurd h hnb⟩

theorem burnsideC56_glue_c4 (hcs : burnsideC56_CS G Λ ⊤ H (Λ ⊓ H) K₁)
    (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H)
    (hcase : burnsideC56_glue_Case H (Λ ⊓ H) K₁) (hC : C61Concl Λ H (Λ ⊓ H) K₁)
    (hr : ((IsAltType K₁ 5 ∧ conjJoin (Λ ⊓ H) K₁ = K₁) ∨
        (IsAltType K₁ 3 ∧ conjJoin (Λ ⊓ H) K₁ ≠ K₁)) →
      ∃ r ∈ Λ ⊓ H, r ∉ baum (Λ ⊓ H)) :
    ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
      ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) →
      ∃ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H ∧ r ∉ thompsonJ (Λ ⊓ H) ∧
        (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
        AFam (Λ ⊓ H) = {pCoreOf 2 H, ChC.rconj x (pCoreOf 2 H), A₁, ChC.rconj r A₁} := by
  intro x hx hxS hcond
  have hJ := (burnsideC56_glue_c1 hC).2.1
  have key : ∀ hβ : (IsAltType K₁ 5 ∧ conjJoin (Λ ⊓ H) K₁ = K₁) ∨
      (IsAltType K₁ 3 ∧ conjJoin (Λ ⊓ H) K₁ ≠ K₁),
      ∃ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H ∧ r ∉ thompsonJ (Λ ⊓ H) ∧
        (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
        AFam (Λ ⊓ H) = {pCoreOf 2 H, ChC.rconj x (pCoreOf 2 H), A₁, ChC.rconj r A₁} := by
    intro hβ
    obtain ⟨r, hrS, hrB⟩ := hr hβ
    have hrJ : r ∉ thompsonJ (Λ ⊓ H) := by rw [hJ]; exact hrB
    obtain ⟨A₁, hidx, hiff⟩ := hC.2.2.1 hβ x hx hxS r hrS hrJ
    refine ⟨A₁, r, hrS, hrJ, hidx, ?_⟩
    ext A
    exact hiff A
  rcases hcase with ⟨hj, hL, -, hn2⟩ | ⟨hj, h3, hn2⟩ | ⟨hne, h3, -⟩
  · rcases hcond with ⟨-, h5⟩ | h2
    · rw [burnsideC56_glue_L_eq hjoin hj] at h5
      exact key (Or.inl ⟨h5, hj⟩)
    · exact absurd h2 hn2
  · rcases hcond with ⟨-, h5⟩ | h2
    · rw [burnsideC56_glue_L_eq hjoin hj] at h5
      exact absurd h3 (CFSG.QuasithinUnique.AppC.not_alt3_of_alt5 h5)
    · exact absurd h2 hn2
  · exact key (Or.inr ⟨h3, hne⟩)

theorem burnsideC56_glue_c6 (hcs : burnsideC56_CS G Λ ⊤ H (Λ ⊓ H) K₁)
    (hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H)
    (hcase : burnsideC56_glue_Case H (Λ ⊓ H) K₁) (hC : C61Concl Λ H (Λ ⊓ H) K₁) :
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
  have h1 := hC.1.2
  obtain ⟨-, -, -, -, h6⟩ := hC
  have hblk : IsBlock2 H (oTwoUpper H) → conjJoin (Λ ⊓ H) K₁ = K₁ := by
    intro hb
    rcases hcase with ⟨hj, -⟩ | ⟨hj, -⟩ | ⟨-, -, hnb⟩
    · exact hj
    · exact hj
    · exact absurd hb hnb
  rcases h6 with ⟨ha, hb, hc⟩ | ⟨h3, hj, hiso, hdih⟩ | ⟨hcond, hJ, ⟨f, hf, hker⟩, hcard⟩
  · refine Or.inl ⟨ha, hb, fun hh => ?_⟩
    have hj := hblk hh.1
    have h3 := hh.2
    rw [burnsideC56_glue_L_eq hjoin hj] at h3
    exact hc h3 hj
  · have hL := burnsideC56_glue_L_eq hjoin hj
    refine Or.inr (Or.inl ⟨?_, ?_, hiso, hdih⟩)
    · rw [hL]; exact hcs.block.1
    · rw [hL]; exact h3
  · refine Or.inr (Or.inr ⟨?_, hJ, ⟨DihedralGroup 4, inferInstance, f, hf, hker,
      ⟨MulEquiv.refl _⟩⟩, ?_⟩)
    · rcases hcond with ⟨h5, hj⟩ | ⟨h3, hne⟩
      · left
        rw [burnsideC56_glue_L_eq hjoin hj]
        exact ⟨hcs.block.1, h5⟩
      · exact Or.inr (burnsideC56_glue_A3Product hcs hjoin h3 hne)
    · intro x hx hxS A₁ r hr hrJ hidx hAF
      have hmax : IsMaxElemAbelian (Λ ⊓ H) A₁ := by
        have : A₁ ∈ AFam (Λ ⊓ H) := by rw [hAF]; simp
        exact this
      have hAQ : A₁ ≠ pCoreOf 2 H := by
        intro h
        rw [h, inf_idem, Subgroup.relIndex_self] at hidx
        omega
      by_cases hAx : ∃ x' ∈ normT Λ (Λ ⊓ H), x' ∉ Λ ⊓ H ∧ A₁ = conjR (pCoreOf 2 H) x'
      · obtain ⟨x', hx', hx'S, rfl⟩ := hAx
        have hb := (h1 x' hx' hx'S).2
        rw [sup_comm, ← hb]
        refine Subgroup.card_le_of_le (le_inf inf_le_left fun s hs => ?_)
        exact normalizer_le_normalizer_baum (Λ ⊓ H) (Subgroup.le_normalizer hs)
      · push Not at hAx
        exact hcard A₁ hmax hAQ fun x' hx' hx'S h => hAx x' hx' hx'S h

end CFSG.ASVolI
