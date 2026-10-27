module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentC
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Perf

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem V_le_cent_xv : V K ≤ Subgroup.centralizer ({xv 1} : Set (C K)) := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨s, rfl⟩ := mem_Xb_iff.1 hg
    exact Subgroup.mem_centralizer_singleton_iff.2 (cc_vb 1 s).eq.symm
  · obtain ⟨s, rfl⟩ := mem_Xc_iff.1 hg
    exact Subgroup.mem_centralizer_singleton_iff.2 (cc_vc 1 s).eq.symm

theorem V_comm {a b : C K} (ha : a ∈ V K) (hb : b ∈ V K) : a * b = b * a := by
  obtain ⟨β, γ, rfl⟩ := mem_V_iff.1 ha
  obtain ⟨b', e, rfl⟩ := mem_V_iff.1 hb
  rw [nf_mul_V, nf_mul_V, add_comm β, add_comm γ]

theorem V_sq {a : C K} (ha : a ∈ V K) : a ^ 2 = 1 := by
  obtain ⟨β, γ, rfl⟩ := mem_V_iff.1 ha
  rw [pow_two, nf_mul_V, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
  exact nf_one

theorem V_ne_bot : V K ≠ ⊥ := by
  intro h
  have h1 : xb (1 : K) ∈ V K := xb_mem_V 1
  rw [h, Subgroup.mem_bot, xb_eq_one_iff] at h1
  exact one_ne_zero h1

theorem V_normalized {x v : C K} (hx : x ∈ Subgroup.centralizer ({xv 1} : Set (C K)))
    (hv : v ∈ V K) : x * v * x⁻¹ ∈ V K :=
  (Subgroup.mem_normalizer_iff.1 (Pa_le_normalizer_V (ct hx)) v).1 hv

theorem torusElt_mem_adjointGroup (i : Fin Tag.G2.rank) (u : Kˣ) :
    torusElt Tag.G2 K i u ∈ adjointGroup Tag.G2 K :=
  parabolicSubgroup_le_adjointGroup Tag.G2 K {i}
    (torusGroup_le_parabolicSubgroup {i} (torusElt_mem_torusGroup i u))

theorem cartan_c : ∑ j, Tag.G2.cartan i0 j * rC j = 1 := by decide

theorem cartan_v : ∑ j, Tag.G2.cartan i0 j * rV j = 0 := by decide

theorem cartan_b : ∑ j, Tag.G2.cartan i0 j * rB j = -1 := by decide

theorem torus_conj_c (u : Kˣ) (s : K) :
    torusElt Tag.G2 K i0 u * gX rC s * (torusElt Tag.G2 K i0 u)⁻¹ = gX rC ((u : K) * s) := by
  have hrC : IsRoot Tag.G2 rC := (pos_TC rC (Set.mem_singleton _)).1
  rw [CFSG.Quasithin.H13.Sec53F.G2.conj_torus i0 hrC u s, cartan_c, zpow_one]

theorem torus_conj_v (u : Kˣ) (s : K) :
    torusElt Tag.G2 K i0 u * gX rV s * (torusElt Tag.G2 K i0 u)⁻¹ = gX rV s := by
  have hrV : IsRoot Tag.G2 rV := (pos_TVBC rV (Or.inl rfl)).1
  rw [CFSG.Quasithin.H13.Sec53F.G2.conj_torus i0 hrV u s, cartan_v, zpow_zero, Units.val_one,
    one_mul]

theorem torus_conj_b (u : Kˣ) (s : K) :
    torusElt Tag.G2 K i0 u * gX rB s * (torusElt Tag.G2 K i0 u)⁻¹ =
      gX rB (((u⁻¹ : Kˣ) : K) * s) := by
  have hrB : IsRoot Tag.G2 rB := (pos_TVBC rB (Or.inr (Or.inl rfl))).1
  rw [CFSG.Quasithin.H13.Sec53F.G2.conj_torus i0 hrB u s, cartan_b, zpow_neg_one]

theorem V_conj_z {v : C K} (hv : v ∈ V K) (hv1 : v ≠ 1) :
    ∃ x ∈ Subgroup.centralizer ({xv 1} : Set (C K)), v = x * xc 1 * x⁻¹ := by
  obtain ⟨β, γ, rfl⟩ := mem_V_iff.1 hv
  have hrC : IsRoot Tag.G2 rC := (pos_TC rC (Set.mem_singleton _)).1
  by_cases hβ : β = 0
  · subst hβ
    have hγ : γ ≠ 0 := by
      rintro rfl
      exact hv1 nf_one
    refine ⟨⟨torusElt Tag.G2 K i0 (Units.mk0 γ hγ),
      torusElt_mem_adjointGroup i0 (Units.mk0 γ hγ)⟩, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
      exact mul_inv_eq_iff_eq_mul.1 (torus_conj_v (Units.mk0 γ hγ) 1)
    · refine Subtype.ext ?_
      rw [← xc_eq_nf]
      show gX rC γ = torusElt Tag.G2 K i0 (Units.mk0 γ hγ) * gX rC 1 *
        (torusElt Tag.G2 K i0 (Units.mk0 γ hγ))⁻¹
      rw [torus_conj_c, Units.val_mk0, mul_one]
  · have hu : β⁻¹ ≠ 0 := inv_ne_zero hβ
    set d : ModGL Tag.G2 K := torusElt Tag.G2 K i0 (Units.mk0 β⁻¹ hu) with hd
    set n : ModGL Tag.G2 K := weylElt Tag.G2 K i0 1 with hn
    refine ⟨xa (γ / β) * ⟨d, torusElt_mem_adjointGroup i0 _⟩ *
      ⟨n, weylElt_mem_adjointGroup i0 1⟩, ?_, ?_⟩
    · refine mul_mem (mul_mem ?_ ?_) nA_mem_centralizer_xv
      · exact Subgroup.mem_centralizer_singleton_iff.2 (cc_av (γ / β) 1).eq
      · refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
        exact mul_inv_eq_iff_eq_mul.1 (torus_conj_v (Units.mk0 β⁻¹ hu) 1)
    · refine Subtype.ext ?_
      rw [coe_nf_V]
      have h1 : n * gX rC (1 : K) * n⁻¹ = gX rB 1 := by
        rw [hn, weylElt_conj_gX i0 hrC 1, reflect_a_c']
      have h2 : d * gX rB (1 : K) * d⁻¹ = gX rB β := by
        rw [hd, torus_conj_b, mul_one]
        simp
      have h3 : gX rA (γ / β) * gX rB β * (gX rA (γ / β))⁻¹ = gX rB β * gX rC γ := by
        have e : gX rA (γ / β) * gX rB β * (gX rA (γ / β))⁻¹ =
            ⁅gX rA (γ / β), gX rB β⁆ * gX rB β := by
          simp only [commutatorElement_def]
          group
        rw [e, rel_ab, show γ / β * β = γ by field_simp]
        exact (comm_bc β γ).eq.symm
      show gX rB β * gX rC γ = (gX rA (γ / β) * d * n) * gX rC 1 * (gX rA (γ / β) * d * n)⁻¹
      calc gX rB β * gX rC γ = gX rA (γ / β) * gX rB β * (gX rA (γ / β))⁻¹ := h3.symm
        _ = gX rA (γ / β) * (d * gX rB (1 : K) * d⁻¹) * (gX rA (γ / β))⁻¹ := by rw [h2]
        _ = gX rA (γ / β) * (d * (n * gX rC (1 : K) * n⁻¹) * d⁻¹) * (gX rA (γ / β))⁻¹ := by
            rw [h1]
        _ = _ := by group

end CFSG.Quasithin.H13.F431.G2.Cent
