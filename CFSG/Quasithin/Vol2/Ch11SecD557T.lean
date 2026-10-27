module

public import CFSG.Quasithin.Vol2.Ch11SecD557S
public import CFSG.Quasithin.Vol2.Ch11SecD556C
public import CFSG.Quasithin.Vol2.Ch11SecD557M

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem stmt11_5_5_normalizer_three (h1110 : Stmt11_1_0) (h1154 : Stmt11_5_4)
    (h1155 : Stmt11_5_5) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hSL3 : KindSL3 L (fsuV T I) n) (hK : KOf L V₁ V₁ = LOf L V₁) :
    ∃ (s : ℕ) (W : Fin s → Subgroup G) (F : Type) (_ : Field F) (_ : Fintype F),
      Fintype.card F = 2 ^ n ∧
      (∀ i, V₁ ≤ W i ∧ W i ≤ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ∧
      (V₁ ⊔ ⨆ i, W i) = conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ∧
      ∀ i, IsNaturalSection (KOf L V₁ V₁) (W i) V₁ (CFSG.pCore 2 ↥(KOf L V₁ V₁))
        (StatedSL 2 F) := by
  have hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hV₁O : V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))
  have hO2ne : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := fun hb =>
    SecA.IsVi.ne_bot h hV₁ le_rfl (le_bot_iff.mp (hb ▸ hV₁O))
  have hH₁ : InH (LOf L V₁ ⊔ T) (Subgroup.normalizer (V₁ : Set G)) :=
    ⟨sup_le (lOf_le_normalizer L V₁) hTG₁, hO2ne⟩
  have hH₁M : ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := fun hle =>
    (h1154 G T L I n V₁ h hV₁).1 ((Subgroup.centralizer_le_normalizer _).trans hle)
  obtain ⟨V₃, hV₃, -⟩ := (h1110 G T L I n h).1 3 (by norm_num) le_rfl
  have hV₃eq : V₃ = fsuV T I := ((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).1 hSL3
  obtain ⟨-, -, -, h5four⟩ := h1155 G T L I n V₁ V₃ _ h hV₁ hV₃ hH₁ hH₁M le_rfl
  subst hV₃eq
  obtain ⟨s, W, F, hF, hFt, hcard, hW, -, hsup, hnat⟩ := h5four hK
  exact ⟨s, W, F, hF, hFt, hcard, hW, hsup, hnat⟩

theorem inf_centralizer_eq_bot_of_kOf_eq (hG2 : SecA.FactG2DerivedOrder) (hNat : NatV3Fact)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h1154 : Stmt11_5_4)
    (h1155 : Stmt11_5_5) {V₁ : Subgroup G} {x y : G}
    (hconf : Config11_5_7SL3 G T L I n V₁ x y) (hK : KOf L V₁ V₁ = LOf L V₁) :
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨h, hV₁, hSL3, hU, -, -, -, -, -, -, -, -, -, -⟩ := hconf
  have hyp := almostSpecialL3Hyp_of_kindSL3 hG2 hNat h1102 h1110 h1141 h hV₁ hSL3 hU
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := ⟨hyp, D⟩
  obtain ⟨s, W, F, _, _, hF, hW, hsup, hnat⟩ :=
    stmt11_5_5_normalizer_three h1110 h1154 h1155 h hV₁ hSL3 hK
  obtain ⟨h5one, h5two, -⟩ := stmt11_5_5_normalizer h1110 h1154 h1155 h hV₁ hSL3
  have hn0 : n ≠ 0 := by have := h.one_lt; omega
  have h2F : (2 : F) = 0 := two_eq_zero_of_card hn0 (by rw [Nat.card_eq_fintype_card, hF])
  have hK3 : 3 ∣ Nat.card ↥(KOf L V₁ V₁) := by
    obtain ⟨F', _, _, hF', ⟨e⟩⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
    have h3 := three_dvd_card_SL2 (two_eq_zero_of_card hn0 hF')
    rw [← Nat.card_congr e.toEquiv] at h3
    rw [hK]
    exact h3.trans (Subgroup.index_dvd_card _)
  have hUG₁ := h5one.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hKG₁ : KOf L V₁ V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    kOf_le_normalizer (lOf_le_normalizer L V₁)
  rw [eq_bot_iff]
  rintro c ⟨hcU, hcL⟩
  have hcV₁ : c ∈ V₁ := mem_of_forall_conj_eq_of_natural W h2F (fun i => (hW i).2)
    (St.hyp.base.le_V.trans (le_conjClosure _ _)) hsup hnat
    (fun a ha b hb => h5two (Subgroup.commutator_mem_commutator ha (h5one hb))) hUG₁
    (hKG₁.trans (le_normalizer_conjClosure _ _)) hKG₁ hK3 hcU fun k hk => by
      have hkL : k ∈ L := by
        rw [hK] at hk
        exact ((perfectCore_le _).trans inf_le_left) hk
      rw [Subgroup.mem_centralizer_iff.mp hcL k hkL, mul_inv_cancel_right]
  have h1 : c ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨St.hyp.base.le_V hcV₁, hcL⟩
  rwa [inf_centralizer_eq_bot_of_natData St.D] at h1

end CFSG.Quasithin.Vol2.Ch11.SecD
