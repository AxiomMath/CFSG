module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenP1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_inf_centralizer {R W : Subgroup G}
    (hR : R ≤ normalizer (W : Set G)) :
    R ≤ normalizer ((R ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ r ∈ R, ∀ x ∈ R ⊓ centralizer (W : Set G),
      r * x * r⁻¹ ∈ R ⊓ centralizer (W : Set G) := by
    intro r hr x hx
    refine Subgroup.mem_inf.2 ⟨R.mul_mem (R.mul_mem hr (Subgroup.mem_inf.1 hx).1)
      (R.inv_mem hr), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : r⁻¹ * w * r ∈ W := by
      simpa using (Subgroup.mem_normalizer_iff.1 (hR (R.inv_mem hr)) w).1 hw
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 _ hw'
    calc w * (r * x * r⁻¹) = r * ((r⁻¹ * w * r) * x) * r⁻¹ := by group
      _ = r * (x * (r⁻¹ * w * r)) * r⁻¹ := by rw [hc]
      _ = r * x * r⁻¹ * w := by group
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key r hr x, fun hx => ?_⟩
  simpa [mul_assoc] using key r⁻¹ (R.inv_mem hr) _ hx

namespace Cfg1511

variable {M V₀ V U S H P Q₀ R : Subgroup G} {p : ℕ}

theorem S_le_cTilde (c : Cfg1511 M V₀ V U S H P Q₀ p) : S ≤ F11.CTilde M V₀ V :=
  c.cex.sylow.le.trans c.cex.centralizer_le_cTilde

theorem S_le_of_le (c : Cfg1511 M V₀ V U S H P Q₀ p) (hPR : P ⊓ F11.CTilde M V₀ V ≤ R) :
    S ≤ R :=
  (le_inf c.hyp.S_le c.S_le_cTilde).trans hPR

theorem inf_centralizer_eq (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) (hPR : P ⊓ F11.CTilde M V₀ V ≤ R) :
    R ⊓ centralizer (U : Set G) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSR : S ≤ R := c.S_le_of_le hPR
  have hSC : S ≤ centralizer (U : Set G) := c.cex.S_le_centralizer
  have hSA : S ≤ R ⊓ centralizer (U : Set G) := le_inf hSR hSC
  have hAMC : R ⊓ centralizer (U : Set G) ≤ M ⊓ centralizer (U : Set G) :=
    le_inf (inf_le_left.trans (hR.le.trans (cTilde_le_M M V₀ V))) inf_le_right
  have hA2 : IsPGroup 2 ↥(R ⊓ centralizer (U : Set G)) := hR.isPGroup.to_le inf_le_left
  have hrel : S.relIndex (R ⊓ centralizer (U : Set G)) *
      (R ⊓ centralizer (U : Set G)).relIndex (M ⊓ centralizer (U : Set G)) =
      S.relIndex (M ⊓ centralizer (U : Set G)) :=
    Subgroup.relIndex_mul_relIndex S _ _ hSA hAMC
  have hdvd : S.relIndex (R ⊓ centralizer (U : Set G)) ∣
      Nat.card ↥(R ⊓ centralizer (U : Set G)) := Subgroup.index_dvd_card _
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hnot2 : ¬ 2 ∣ S.relIndex (M ⊓ centralizer (U : Set G)) := c.cex.sylow.not_dvd_relIndex
  have hj0 : j = 0 := by
    by_contra hjn
    exact hnot2 (hrel ▸ dvd_mul_of_dvd_left (hj ▸ dvd_pow_self 2 hjn) _)
  rw [hj0, pow_zero] at hj
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hj) hSA

theorem R_le_normalizer_sup
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) :
    R ≤ normalizer ((U ⊔ v1Sub15 V₀ U : Subgroup G) : Set G) := by
  have key : ∀ r ∈ R, ∀ w ∈ U ⊔ v1Sub15 V₀ U, r * w * r⁻¹ ∈ U ⊔ v1Sub15 V₀ U := by
    intro r hr w hw
    have hwV : w ∈ V :=
      (sup_le c.cex.le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le)) hw
    have h1 : ⁅r, w⁆ ∈ v1Sub15 V₀ U :=
      Cex15.commutator_cTilde_le_v1Sub15 c.inputs c.std c.cex
        (Subgroup.commutator_mem_commutator (hR.le hr) hwV)
    have h2 : r * w * r⁻¹ = ⁅r, w⁆ * w := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact (U ⊔ v1Sub15 V₀ U).mul_mem (Subgroup.mem_sup_right h1) hw
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key r hr w, fun hw => ?_⟩
  simpa [mul_assoc] using key r⁻¹ (R.inv_mem hr) _ hw

theorem tSub15_eq_inf_centralizer_sup (c : Cfg1511 M V₀ V U S H S Q₀ p)
    (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) (hPR : S ⊓ F11.CTilde M V₀ V ≤ R) :
    tSub15 M V₀ V U S = R ⊓ centralizer ((U ⊔ v1Sub15 V₀ U : Subgroup G) : Set G) := by
  have hRU := c.inf_centralizer_eq hR hPR
  ext x
  rw [mem_tSub15_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxS, -, hx1⟩
    have hxU : x ∈ centralizer (U : Set G) := c.cex.S_le_centralizer hxS
    refine ⟨c.S_le_of_le hPR hxS, ?_⟩
    have hle : U ⊔ v1Sub15 V₀ U ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (Subgroup.mem_centralizer_iff.1 hxU w hw).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (Subgroup.mem_centralizer_iff.1 hx1 w hw).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := Subgroup.mem_centralizer_iff.1 (hle hw) x (Set.mem_singleton x)
    exact this.symm
  · rintro ⟨hxR, hxc⟩
    have hxU : x ∈ centralizer (U : Set G) :=
      Subgroup.centralizer_le (le_sup_left : U ≤ U ⊔ v1Sub15 V₀ U) hxc
    have hxS : x ∈ S := by
      rw [← hRU]
      exact ⟨hxR, hxU⟩
    exact ⟨hxS, c.S_le_cTilde hxS,
      Subgroup.centralizer_le (le_sup_right : v1Sub15 V₀ U ≤ U ⊔ v1Sub15 V₀ U) hxc⟩

theorem R_le_normalizer_tSub15
    (c : Cfg1511 M V₀ V U S H S Q₀ p) (hR : IsSylowIn 2 R (F11.CTilde M V₀ V))
    (hPR : S ⊓ F11.CTilde M V₀ V ≤ R) :
    R ≤ normalizer (tSub15 M V₀ V U S : Set G) := by
  rw [c.tSub15_eq_inf_centralizer_sup hR hPR]
  exact normalizer_inf_centralizer (c.R_le_normalizer_sup hR)

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
