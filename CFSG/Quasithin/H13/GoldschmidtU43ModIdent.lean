module

public import CFSG.Quasithin.H13.GoldschmidtU43ModRel
public import CFSG.Quasithin.H13.GoldschmidtU43ModSimple
public import Certificates.Certificate6104

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.CosetTable CFSG.Sporadic.Recognition.JankoWong
open CFSG.LieType.Multipliers.U43 (X₀ card_X₀)

abbrev jwPres5 : Type := PG (subsetOf 6 [0, 1, 2, 3, 4]).length (jwRels5 false)

theorem finite_card_jwPres5_le :
    Finite jwPres5 ∧ Nat.card jwPres5 ≤ 3265920 :=
  (Certificates.certificate6104 false).2.1

theorem lift_mk_evalG {K : Type*} [Group K] (g : ℕ → K) {M : ℕ} (w : List (Fin M × Bool)) :
    FreeGroup.lift (fun i : Fin M => g i.val) (FreeGroup.mk w) =
      evalG g (w.map fun l => (l.1.val, l.2)) := by
  rw [FreeGroup.lift_mk, evalG, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp, letterVal]
  cases l.2 <;> rfl

noncomputable def jwHom5 {G : Type} [Group G] {a s u v φ : G} (h : JW20 a s u v φ) :
    jwPres5 →* G :=
  PresentedGroup.toGroup
    (f := fun i : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length => gen5 a s u v φ i.val) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk_evalG (gen5 a s u v φ)]
    exact h.eval_rels _ (List.mem_map_of_mem hw)

theorem jwHom5_of {G : Type} [Group G] {a s u v φ : G} (h : JW20 a s u v φ)
    (i : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) :
    jwHom5 h (PresentedGroup.of i) = gen5 a s u v φ i.val :=
  PresentedGroup.toGroup.of _

theorem range_jwHom5 {G : Type} [Group G] {a s u v φ : G} (h : JW20 a s u v φ) :
    (jwHom5 h).range = Subgroup.closure ({a, s, u, v, φ} : Set G) := by
  have hM : (subsetOf 6 [0, 1, 2, 3, 4]).length = 5 := by decide
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp, jwHom5_of, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    have hj5 : j < 5 := hM ▸ hj
    interval_cases j <;> simp [gen5]
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨⟨0, by omega⟩, rfl⟩
    · exact ⟨⟨1, by omega⟩, rfl⟩
    · exact ⟨⟨2, by omega⟩, rfl⟩
    · exact ⟨⟨3, by omega⟩, rfl⟩
    · exact ⟨⟨4, by omega⟩, rfl⟩

theorem exists_mulEquiv_X0_of_jw20 (hmodel : U43Model)
    {G : Type} [Group G] {a s u v φ : G} (h : JW20 a s u v φ)
    (hK : Subgroup.closure ({a, s, u, v, φ} : Set G) ≠ ⊥) :
    Nonempty (↥(Subgroup.closure ({a, s, u, v, φ} : Set G)) ≃* X₀) := by
  obtain ⟨a₀, s₀, u₀, v₀, φ₀, hJ, hgen⟩ := hmodel
  obtain ⟨hfin, hcard⟩ := finite_card_jwPres5_le
  have hsurj : Function.Surjective (jwHom5 hJ) := by
    rw [← MonoidHom.range_eq_top, range_jwHom5, hgen]
  have hbij : Function.Bijective (jwHom5 hJ) := by
    have := hfin
    refine hsurj.bijective_of_nat_card_le ?_
    rw [card_X₀]
    exact hcard
  have hsimple : IsSimpleGroup jwPres5 :=
    haveI := isSimpleGroup_X₀
    (MulEquiv.ofBijective (jwHom5 hJ) hbij).isSimpleGroup
  have hker : (jwHom5 h).ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (jwHom5 h).ker with h0 | h0
    · exact h0
    · exfalso
      apply hK
      rw [← range_jwHom5 h, MonoidHom.range_eq_bot_iff]
      exact MonoidHom.ker_eq_top_iff.1 h0
  have hinj : Function.Injective (jwHom5 h) := (MonoidHom.ker_eq_bot_iff _).1 hker
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (range_jwHom5 h))).symm.trans
    (MulEquiv.ofBijective (jwHom5 hJ) hbij)⟩

end CFSG.Quasithin.H13.U43
