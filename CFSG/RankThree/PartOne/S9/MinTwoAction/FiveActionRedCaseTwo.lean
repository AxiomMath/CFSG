module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedAbstract
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedRealize

public section

namespace CFSG.RankThree.PartOne.FiveAction.Red

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Quotient36
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]

theorem false_of_nontrivial_atom (hSB : FiveAction.ScalarBound) (hq2 : q ≠ 2)
    (hq5 : q % 5 = 2 ∨ q % 5 = 3) {A D R : Subgroup G} [hDq : Fact (IsPGroup q ↥D)]
    (hset : MinTwoActionSetting 5 q A D R)
    (hrk : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3)
    (U : Subrepresentation (FRep q hset.D_inv)) (hU : IsAtom U) (b : ↥A)
    (hbR : (b : G) ∈ Subgroup.centralizer (R : Set G))
    (hb : ∃ u ∈ U, FRep q hset.D_inv (Subgroup.inclusion (le_sup_right : A ≤ R ⊔ A) b) u ≠ u)
    (hR : ∃ r : ↥(R ⊔ A), (r : G) ∈ R ∧ ∃ u ∈ U, FRep q hset.D_inv r u ≠ u) : False := by
  classical
  have hLD := hset.D_inv
  have hq : q.Prime := hset.prime_q
  have hAord : ¬ q ∣ Nat.card A := by
    rw [hset.A_card]
    intro h
    exact hset.p_ne_q ((Nat.prime_dvd_prime_iff_eq hq hset.prime_p).mp
      (hq.dvd_of_dvd_pow h)).symm
  obtain ⟨Y, hYD, hLY, hYfr, hYimg, hYC⟩ :=
    exists_realization_of_atom hq2 hset.R_two hAord hset.R_inv hLD U hU
  obtain ⟨r, hrR, u, hu, hru⟩ := hR
  have hrY : (r : G) ∉ Subgroup.centralizer (Y : Set G) := fun h => hru (hYC r h u hu)
  have hRY : ⁅R, Y⁆ ≠ ⊥ := fun h =>
    hrY ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hrR)
  have hsetY : MinTwoActionSetting 5 q A Y R :=
    { prime_p := hset.prime_p
      prime_q := hset.prime_q
      three_lt_p := hset.three_lt_p
      q_ne_two := hset.q_ne_two
      p_ne_q := hset.p_ne_q
      A_elem := hset.A_elem
      A_card := hset.A_card
      D_inv := hLY
      D_pgroup := isPGroup_of_le hYD hDq.out
      D_exp := fun x hx => hset.D_exp x (hYD hx)
      D_class := by
        have h1 : ⁅⁅Y, Y⁆, Y⁆ ≤ ⁅⁅D, D⁆, D⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_mono hYD hYD) hYD
        exact le_bot_iff.mp (hset.D_class ▸ h1)
      R_two := hset.R_two
      R_inv := hset.R_inv
      R_comm := hset.R_comm
      R_ne := hset.R_ne
      R_act := hRY
      R_min := fun U' hlt hAU' hcomm g hg =>
        Subgroup.centralizer_le (fun x hx => hYD hx) (hset.R_min U' hlt hAU' hcomm hg) }
  have hrkY : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(Y ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3 :=
    fun r hr hr1 => (pRank_mono_subgroup hq.one_lt (inf_le_inf_right _ hYD)).trans (hrk r hr hr1)
  obtain ⟨X₁, hX₁Y, hX₁fr, hd₁⟩ := exists_sfdata hsetY hrkY
  have hX₁D : X₁ ≤ D := hX₁Y.trans hYD
  have hX₁q : IsPGroup q ↥X₁ := isPGroup_of_le hX₁D hDq.out
  have : Fact (IsPGroup q ↥X₁) := ⟨hX₁q⟩
  have hX₁fr' : X₁ ⊓ inSubgroup frattini D = inSubgroup frattini X₁ := by
    calc X₁ ⊓ inSubgroup frattini D = (X₁ ⊓ Y) ⊓ inSubgroup frattini D := by
          rw [inf_of_le_left hX₁Y]
      _ = X₁ ⊓ (Y ⊓ inSubgroup frattini D) := inf_assoc _ _ _
      _ = X₁ ⊓ inSubgroup frattini Y := by rw [hYfr]
      _ = inSubgroup frattini X₁ := hX₁fr
  have hLX₁ := hd₁.irr.1
  have hV₁U : imageSub (q := q) hLD hLX₁ ≤ U := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := (mem_imageSub hLD hLX₁ w).mp hw
    exact hYimg y (hX₁Y hy)
  have hV₁ne : imageSub (q := q) hLD hLX₁ ≠ ⊥ := by
    intro h
    obtain ⟨x, hx, hxΦ⟩ := IsConcreteLE.exists_of_lt hd₁.irr.2.1
    have h1 : Additive.ofMul ((⟨x, hX₁D hx⟩ : ↥D) : ↥D ⧸ frattini ↥D) ∈
        imageSub (q := q) hLD hLX₁ := (mem_imageSub hLD hLX₁ _).mpr ⟨⟨x, hX₁D hx⟩, hx, rfl⟩
    rw [h] at h1
    have h2 : ((⟨x, hX₁D hx⟩ : ↥D) : ↥D ⧸ frattini ↥D) = 1 :=
      Additive.ofMul.injective (Submodule.mem_bot _ |>.mp h1)
    have h3 := (mk_eq_one_iff hX₁D hX₁fr' ⟨x, hx⟩).mpr h2
    exact hxΦ ((mem_inSubgroup_frattini_iff (⟨x, hx⟩ : ↥X₁)).mpr
      ((QuotientGroup.eq_one_iff _).mp h3))
  have hV₁eq : imageSub (q := q) hLD hLX₁ = U := (hU.le_iff.mp hV₁U).resolve_left hV₁ne
  obtain ⟨u', hu'U, hbu⟩ := hb
  rw [← hV₁eq] at hu'U
  obtain ⟨y, hy, rfl⟩ := (mem_imageSub hLD hLX₁ u').mp hu'U
  have hbnt : ∃ x : ↥X₁, ((conjHom (le_trans le_sup_right hLX₁) b x : ↥X₁) : ↥X₁ ⧸ frattini ↥X₁) ≠
      (x : ↥X₁ ⧸ frattini ↥X₁) := by
    refine ⟨⟨y, hy⟩, fun h => hbu ?_⟩
    have h1 := (mk_eq_iff hX₁D hX₁fr' _ _).mp h
    rw [FRep_apply_mk]
    exact congrArg Additive.ofMul h1
  exact false_of_nontrivial_central hSB hq2 hq5 hset.R_two hset.A_card hset.A_elem hset.R_inv
    hX₁D hset.D_exp hset.D_class hrk hd₁ b hbR hbnt

end CFSG.RankThree.PartOne.FiveAction.Red
