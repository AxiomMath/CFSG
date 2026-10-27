module

public import CFSG.Quasithin.EmptyFaithful.S146zWD
public import CFSG.Quasithin.EmptyFaithful.S146zWA

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C2Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev wC (J J' R : Subgroup G) : Subgroup G :=
  wY J J' R ⊓ Subgroup.centralizer (wV J J' R : Set G)

omit [Finite G] in
theorem wAut_sup_wC (J J' R : Subgroup G) {S : Subgroup G} (hS : S ≤ wY J J' R)
    (hCN : wC J J' R ≤ Subgroup.normalizer (S : Set G)) :
    wAut J J' R (S ⊔ wC J J' R) = wAut J J' R S := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI _).1 hφ
    have hg' : (g : G) ∈ (↑(S ⊔ wC J J' R) : Set G) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN] at hg'
    obtain ⟨s, hs, c, hc, hgsc⟩ := hg'
    have hsN : s ∈ Subgroup.normalizer (wV J J' R : Set G) := Y_le_normalizer_V (hS hs)
    have hcN : c ∈ Subgroup.normalizer (wV J J' R : Set G) := Y_le_normalizer_V hc.1
    have hgeq : g = ⟨s, hsN⟩ * ⟨c, hcN⟩ := Subtype.ext hgsc.symm
    have hc1 : convI (isElemAbelian_wV J J' R) ⟨c, hcN⟩ = 1 :=
      (convI_eq_one_iff _ _).2 hc.2
    rw [hgeq, map_mul, hc1, mul_one]
    exact convI_mem_autI _ hs hsN
  · exact autI_mono _ le_sup_left


omit [Finite G] in
theorem wAut_inf_sup_wC (J J' R : Subgroup G) (hJY : J ≤ wY J J' R) (hRY : R ≤ wY J J' R)
    (hCN : wC J J' R ≤ Subgroup.normalizer (J : Set G)) :
    wAut J J' R (R ⊓ (J ⊔ wC J J' R)) = wAut J J' R R ⊓ wAut J J' R J := by
  apply le_antisymm
  · refine le_inf (autI_mono _ inf_le_left) ?_
    rw [← wAut_sup_wC J J' R hJY hCN]
    exact autI_mono _ inf_le_right
  · intro φ hφ
    obtain ⟨r, hr, hrφ⟩ := (mem_autI _).1 hφ.1
    obtain ⟨j, hj, hjφ⟩ := (mem_autI _).1 hφ.2
    have hjN : (j : G) ∈ Subgroup.normalizer (wV J J' R : Set G) := j.2
    have hrN : (r : G) ∈ Subgroup.normalizer (wV J J' R : Set G) := r.2
    have hinv : (j : G)⁻¹ * r ∈ Subgroup.normalizer (wV J J' R : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hjN) hrN
    have h1 : convI (isElemAbelian_wV J J' R) ⟨(j : G)⁻¹ * r, hinv⟩ = 1 := by
      have e : (⟨(j : G)⁻¹ * r, hinv⟩ : Subgroup.normalizer (wV J J' R : Set G)) = j⁻¹ * r :=
        rfl
      rw [e, map_mul, map_inv, hjφ, hrφ, inv_mul_cancel]
    have hcC : (j : G)⁻¹ * r ∈ Subgroup.centralizer (wV J J' R : Set G) :=
      (convI_eq_one_iff _ _).1 h1
    have hcY : (j : G)⁻¹ * r ∈ wY J J' R :=
      (wY J J' R).mul_mem ((wY J J' R).inv_mem (hJY hj)) (hRY hr)
    have hrJC : (r : G) ∈ J ⊔ wC J J' R := by
      have e : (r : G) = (j : G) * ((j : G)⁻¹ * r) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hj (show (j : G)⁻¹ * r ∈ wC J J' R from ⟨hcY, hcC⟩)
    rw [← hrφ]
    exact convI_mem_autI _ (show (r : G) ∈ R ⊓ (J ⊔ wC J J' R) from ⟨hr, hrJC⟩) hrN

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem isSylowTwoOf_inf_of_sylow {S : Subgroup (MulAut (VMod J J' R))}
    (hS : IsSylowTwoOf S (wAut J J' R J)) (hSR : S ≤ wAut J J' R R) :
    IsSylowTwoOf (R ⊓ J) J := by
  have hV := isElemAbelian_wV J J' R
  have hJY : J ≤ wY J J' R := J_le_wY J J' R
  have hRY : R ≤ wY J J' R := le_sup_right
  have hCY : wC J J' R ≤ wY J J' R := inf_le_left
  have hCN : wC J J' R ≤ Subgroup.normalizer (J : Set G) := d.C_le_normalizer_J
  have hJC_Y : J ⊔ wC J J' R ≤ wY J J' R := sup_le hJY hCY
  have hJC_N : J ⊔ wC J J' R ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer hCN
  have hJC_V : J ⊔ wC J J' R ≤ Subgroup.normalizer (wV J J' R : Set G) :=
    hJC_Y.trans Y_le_normalizer_V
  have hRJ_V : R ⊓ (J ⊔ wC J J' R) ≤ Subgroup.normalizer (wV J J' R : Set G) :=
    inf_le_left.trans (hRY.trans Y_le_normalizer_V)
  have hJ_V : J ≤ Subgroup.normalizer (wV J J' R : Set G) := hJY.trans Y_le_normalizer_V
  have hodd : ¬ 2 ∣ (wAut J J' R R ⊓ wAut J J' R J).relIndex (wAut J J' R J) :=
    (exists_isSylowTwoOf_le_iff_relIndex_odd
      (inf_le_right : wAut J J' R R ⊓ wAut J J' R J ≤ wAut J J' R J)).1
      ⟨S, hS, le_inf hSR hS.1⟩
  have hJCk : (J ⊔ wC J J' R) ⊓ Subgroup.centralizer (wV J J' R : Set G) = wC J J' R := by
    apply le_antisymm
    · intro x hx
      exact ⟨hJC_Y hx.1, hx.2⟩
    · exact le_inf le_sup_right inf_le_right
  have hRk : (R ⊓ (J ⊔ wC J J' R)) ⊓ Subgroup.centralizer (wV J J' R : Set G) =
      pCoreOf 2 (wY J J' R) := by
    apply le_antisymm
    · intro x hx
      exact d.R_inf_C_le ⟨hx.1.1, hRY hx.1.1, hx.2⟩
    · intro x hx
      have hxC : x ∈ wC J J' R := pCoreOf_Y_le_C hx
      exact ⟨⟨d.pCoreOf_Y_le hx, Subgroup.mem_sup_right hxC⟩, hxC.2⟩
  set JC : Subgroup G := J ⊔ wC J J' R with hJC
  set RJ : Subgroup G := R ⊓ JC with hRJ
  set Q : Subgroup G := pCoreOf 2 (wY J J' R) with hQ
  have c1 : Nat.card (wAut J J' R JC) * Nat.card ↥(wC J J' R) = Nat.card ↥JC := by
    have := card_autI_mul_card_inf hV hJC_V
    rwa [hJCk] at this
  have c2 : Nat.card (wAut J J' R RJ) * Nat.card ↥Q = Nat.card ↥RJ := by
    have := card_autI_mul_card_inf hV hRJ_V
    rwa [hRk] at this
  rw [hJC, wAut_sup_wC J J' R hJY hCN] at c1
  rw [hRJ, hJC, wAut_inf_sup_wC J J' R hJY hRY hCN] at c2
  have hQC : IsSylowTwoOf Q (wC J J' R) := d.isSylowTwoOf_pCoreOf_C
  have hm : Q.relIndex (wC J J' R) * Nat.card ↥Q = Nat.card ↥(wC J J' R) := by
    have := Subgroup.relIndex_mul_card Q (wC J J' R)
    rwa [inf_of_le_left hQC.1] at this
  have hn : (wAut J J' R R ⊓ wAut J J' R J).relIndex (wAut J J' R J) *
      Nat.card ↥(wAut J J' R R ⊓ wAut J J' R J) = Nat.card ↥(wAut J J' R J) := by
    have := Subgroup.relIndex_mul_card (wAut J J' R R ⊓ wAut J J' R J) (wAut J J' R J)
    rwa [inf_of_le_left inf_le_right] at this
  have hcardJC : Nat.card ↥JC = Nat.card ↥RJ *
      ((wAut J J' R R ⊓ wAut J J' R J).relIndex (wAut J J' R J) *
        Q.relIndex (wC J J' R)) := by
    rw [← c1, ← c2, ← hn, ← hm]
    ring
  have hRJJC : RJ ≤ JC := inf_le_right
  have hidx : RJ.relIndex JC = (wAut J J' R R ⊓ wAut J J' R J).relIndex (wAut J J' R J) *
      Q.relIndex (wC J J' R) := by
    have h1 := Subgroup.relIndex_mul_card RJ JC
    rw [inf_of_le_left hRJJC, hcardJC] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card ↥RJ) (by rw [h1, mul_comm])
  have hSyl : IsSylowTwoOf RJ JC := by
    refine ⟨hRJJC, d.cfg.radical.isPGroup.to_le inf_le_left, ?_⟩
    change ¬ 2 ∣ RJ.relIndex JC
    rw [hidx]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact hodd h
    · exact hQC.2.2 h
  have hfin := A4.isSylowTwoOf_inf_normal hSyl (le_sup_left : J ≤ JC) hJC_N
  have heq : RJ ⊓ J = R ⊓ J := by
    ext x
    simp only [hRJ, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.mem_sup_left h.2⟩, h.2⟩⟩
  rw [heq] at hfin
  exact hfin

end WreathData

end CFSG.Quasithin.S146zW
