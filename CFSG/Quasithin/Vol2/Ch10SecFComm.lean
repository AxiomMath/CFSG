module

public import CFSG.Quasithin.Vol2.Ch10SecFX
public import CFSG.Quasithin.Vol2.Ch10SecEE3V

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem alternatingGroup_five_center : ∀ g : alternatingGroup (Fin 5),
    (∀ h : alternatingGroup (Fin 5), g * h = h * g) → g = 1 := by
  decide +kernel

theorem card_evenWeight_five : Nat.card (evenWeight 5) = 16 := by
  classical
  have hmem : ∀ x : Fin 5 → ZMod 2, x ∈ evenWeight 5 ↔ ∑ i, x i = 0 := fun _ => Iff.rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem fsuUL_inf_centralizer_eq_bot (h2 : Ch10.Case10_1_1Two T L I) :
    fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨huU, huL⟩
  obtain ⟨-, hcU, hA⟩ := h2
  have h1 : (⟨u, huU⟩ : ↥(fsuUL T L I)) = 1 := by
    refine SecE.eq_one_of_alternatingNatural_five hA fun φ hφ => ?_
    obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := Subgroup.mem_map.mp hφ
    apply Subtype.ext
    show g * u * g⁻¹ = u
    rw [Subgroup.mem_centralizer_iff.mp huL g (Subgroup.mem_subgroupOf.mp hgL)]
    simp
  exact congrArg Subtype.val h1

theorem card_center_le_two (h113 : ASInputs.AS_C_1_13) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5) :
    Nat.card (Subgroup.center ↥L) ≤ 2 := by
  obtain ⟨-, -, -, -, h5, -⟩ := (h113 G L (Ch10.T1 T L) (SecE.isSylowTwoOf_T1_sup hyp)
    inf_le_right hb.1).2.1 5 (Or.inr rfl) hb.2
  obtain ⟨hUn, he | ⟨-, hc⟩⟩ := h5 rfl
  · obtain ⟨e⟩ := he
    have hU := (SecE.blockU_eq_fsuUL h113 hyp h2 hb).1
    have hbot : Subgroup.center ↥L = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : e (QuotientGroup.mk z) = 1 := by
        refine alternatingGroup_five_center _ fun h => ?_
        obtain ⟨y, rfl⟩ := e.surjective h
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
        rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          Subgroup.mem_center_iff.mp hz y]
      have h2' : z ∈ (blockU L).subgroupOf L := by
        rw [← QuotientGroup.eq_one_iff]
        exact e.injective (h1.trans e.map_one.symm)
      have h3 : (z : G) ∈ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨hU ▸ Subgroup.mem_subgroupOf.mp h2', Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro l hl
        have := Subgroup.mem_center_iff.mp hz ⟨l, hl⟩
        exact congrArg Subtype.val this
      rw [fsuUL_inf_centralizer_eq_bot h2] at h3
      exact Subtype.ext h3
    rw [hbot, Subgroup.card_bot]
    norm_num
  · omega

omit [Finite G] in
theorem le_normalizer_inf_of_le {A B C : Subgroup G} (hA : C ≤ Subgroup.normalizer (A : Set G))
    (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hg) x,
    Subgroup.mem_normalizer_iff.mp (hB hg) x]

theorem le_normalizer_conjugate (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) :
    L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
  (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_conjugate hyp.fsu.maximal.1
    (SecA.le_fsuM T L ht))

theorem fsuUL_inf_conjugate_L_eq_bot (h113 : ASInputs.AS_C_1_13) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ⊓ CFSG.conjugate L t = ⊥ := by
  have hU := (SecE.blockU_eq_fsuUL h113 hyp h2 hb).1
  have hZ : blockZ L = ⊥ := by
    rw [blockZ, hU]
    exact fsuUL_inf_centralizer_eq_bot h2
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator ((SecA.le_fsuL0 T L).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I)) Subgroup.le_normalizer
  have hLW := le_normalizer_inf_of_le hLU (le_normalizer_conjugate hyp ht)
  rcases hb.1.2.2.2.2.2 _ (hZ ▸ bot_le) (hU ▸ inf_le_left) hLW with h | h
  · rwa [hZ] at h
  · exfalso
    have hVL : fsuUL T L I ≤ CFSG.conjugate L t := inf_eq_left.mp (h.trans hU)
    obtain ⟨_, -, -, ha, -⟩ := hyp.three
    have hVC : fsuUL T L I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) :=
      (ha t ht htn).2.2
    have hmapC : ∀ v ∈ fsuUL T L I, ∀ l ∈ L, l * (t * v * t⁻¹) = t * v * t⁻¹ * l := by
      intro v hv l hl
      have hl' : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
        rw [mem_conjugate_iff']
        simpa [mul_assoc] using hl
      have hc := Subgroup.mem_centralizer_iff.mp (hVC hv) _ hl'
      calc l * (t * v * t⁻¹) = t * ((t⁻¹ * l * t) * v) * t⁻¹ := by group
        _ = t * (v * (t⁻¹ * l * t)) * t⁻¹ := by rw [hc]
        _ = t * v * t⁻¹ * l := by group
    let f : ↥(fsuUL T L I) → ↥(Subgroup.center ↥L) := fun v =>
      ⟨⟨t * v * t⁻¹, mem_conjugate_iff'.mp (hVL v.2)⟩,
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hmapC v v.2 g g.2)⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : G)) hab
      simp only [f] at h1
      exact Subtype.ext (by simpa using h1)
    have hcard := Nat.card_le_card_of_injective f hf
    have h16 : 16 ≤ Nat.card ↥(fsuUL T L I) := by
      obtain ⟨-, -, -, β, hβ, -⟩ := hb.2
      have := Nat.card_le_card_of_surjective β hβ
      rw [Nat.card_congr Multiplicative.toAdd, card_evenWeight_five, hU] at this
      exact this
    have := card_center_le_two h113 hyp h2 hb
    omega

theorem commutator_conjugate_eq_bot (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅L, CFSG.conjugate L t⁆ = ⊥ := by
  set D := pCoreOf 2 L ⊓ pCoreOf 2 (CFSG.conjugate L t) with hD
  have hLD : L ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_inf_of_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      ((le_normalizer_conjugate hyp ht).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hU := (SecE.blockU_eq_fsuUL h113 hyp h2 hb).1
  have hDL : ⁅D, L⁆ = ⊥ := by
    refine le_bot_iff.mp ((le_inf ?_ ?_).trans
      (fsuUL_inf_conjugate_L_eq_bot h113 hyp h2 hb ht htn).le)
    · rw [← hU]
      exact Subgroup.commutator_mono inf_le_left le_rfl
    · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hLD).trans
        (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
  have h1 : ⁅⁅L, CFSG.conjugate L t⁆, L⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono (SecA.commutator_conjugate_le h37 hyp ht htn)
      le_rfl).trans hDL.le)
  have h2' : ⁅⁅CFSG.conjugate L t, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (CFSG.conjugate L t) L]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2'
  rwa [perfect_of_mem_cComp (SecE.mem_cComp_L0T hyp)] at h3

end CFSG.Quasithin.Vol2.Ch10.SecF
