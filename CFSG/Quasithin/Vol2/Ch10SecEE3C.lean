module

public import CFSG.Quasithin.Vol2.Ch10SecEE3V
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
    have h2 := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * s := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have h1 := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using h1

theorem exists_involution_of_ne_bot' {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ b ∈ P, b ≠ 1 ∧ b ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨x, x.2, fun h1 => ?_, ?_⟩
  · have h3 : orderOf (x : G) = 1 := by rw [h1]; exact orderOf_one
    rw [Subgroup.orderOf_coe, hx] at h3
    omega
  · have h3 : (x : G) ^ orderOf (x : G) = 1 := pow_orderOf_eq_one _
    rwa [Subgroup.orderOf_coe, hx] at h3

theorem eq_bot_of_omegaOneCenter_inf {T N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hZ : quasithinOmegaOneCenter T ⊓ N = ⊥) :
    N = ⊥ := by
  by_contra hne
  obtain ⟨z, hzN, hz1, hzC⟩ := Lin2.exists_mem_inf_center_of_normal hT hNT hTN hne
  have hP : IsPGroup 2 ↥(N ⊓ Subgroup.centralizer (T : Set G)) := hT.to_le (inf_le_left.trans hNT)
  have hPne : N ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ := fun h =>
    hz1 (by
      have h1 : z ∈ N ⊓ Subgroup.centralizer (T : Set G) := ⟨hzN, hzC⟩
      rw [h] at h1
      exact h1)
  obtain ⟨b, ⟨hbN, hbC⟩, hb1, hb2⟩ := exists_involution_of_ne_bot' hP hPne
  have hbZ : b ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hNT hbN, hbC⟩, hb2⟩
  have h1 : b ∈ quasithinOmegaOneCenter T ⊓ N := ⟨hbZ, hbN⟩
  rw [hZ] at h1
  exact hb1 h1

variable {T L I : Subgroup G}

theorem inf_centralizer_fsuL0_eq_bot (hyp : Hyp10 G T L I)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) :
    T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
  refine eq_bot_of_omegaOneCenter_inf hyp.fsu.sylow.1 inf_le_left ?_ ?_
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxC := normalizer_le_normalizer_centralizer' (fsuL0 T L) (SecA.le_fsuM T L hx)
    constructor
    · intro hy
      exact ⟨T.mul_mem (T.mul_mem hx hy.1) (T.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp hxC y).mp hy.2⟩
    · intro hy
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hxC y).mpr hy.2⟩
      have h1 := T.mul_mem (T.mul_mem (T.inv_mem hx) hy.1) hx
      simpa [mul_assoc] using h1
  · refine le_bot_iff.mp ?_
    rw [← hCZ]
    exact inf_le_inf_left _ inf_le_right

theorem exists_mul_of_mem_pCoreOf (h113 : ASInputs.AS_C_1_13) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5) {x : G}
    (hx : x ∈ pCoreOf 2 (L ⊔ Ch10.T1 T L)) :
    ∃ u ∈ fsuUL T L I, ∃ c ∈ Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G), x = u * c := by
  obtain ⟨hU, hO, -⟩ := blockU_eq_fsuUL h113 hyp h2 hb
  rw [hO] at hx
  have hN : Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer (fsuUL T L I : Set G) := hU ▸ inf_le_left.trans T1_le_normalizer_blockU
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (fsuUL T L I) _ hN
  have hx' : x ∈ ((fsuUL T L I : Set G) *
      ((Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) := by
    rw [← hcoe]
    exact hx
  obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨u, hu, c, hc, rfl⟩

theorem centralizer_le_fsuVM_case2
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hb : IsShort2 L ∧ IsAltType L 5)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) :
    T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hO : pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [(h3228 G T L I hyp.fsu).2.2, SecA.fsuV_eq_of_cases12 h37 h38 hyp (Or.inr h2)]
  have hC0 := inf_centralizer_fsuL0_eq_bot hyp hCZ
  have hab := (SecA.isElemAbelian_fsuVM hyp).1
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  obtain ⟨-, -, hst⟩ := SecA.stmt10_1_1_structure h37 h38 h322 hyp
  obtain ⟨-, hV₁, -, -⟩ := hst t ht htn
  have hdec : ∀ x ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G), ∃ u ∈ fsuUL T L I,
      ∃ c ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G), c ∈ Subgroup.centralizer (L : Set G) ∧
        x = u * c := by
    intro x hx
    have hx' : x ∈ pCoreOf 2 (L ⊔ Ch10.T1 T L) := pCoreOf_L0T_le_pCoreOf hyp (hO ▸ hx)
    obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_pCoreOf h113 hyp h2 hb hx'
    refine ⟨u, hu, c, ⟨hc.1.1, ?_⟩, hc.2, rfl⟩
    have huC : u⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        setLike_mul_comm hv ((fsuVM T L I).inv_mem (hUV hu))
    have h1 := Subgroup.mul_mem _ huC hx.2
    simpa using h1
  intro x hx
  obtain ⟨u, hu, c, hc, hcL, rfl⟩ := hdec x hx
  have hc' : t⁻¹ * c * t ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hc.1) ht, ?_⟩
    have hN := normalizer_le_normalizer_centralizer' (fsuVM T L I)
      (SecA.le_normalizer_fsuVM T L I (T.inv_mem ht))
    have h1 := (Subgroup.mem_normalizer_iff.mp hN c).mp hc.2
    simpa using h1
  obtain ⟨u', hu', d, hd, hdL, hcd⟩ := hdec _ hc'
  have hdLt : d ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := by
    have e : d = u'⁻¹ * (t⁻¹ * c * t) := by rw [hcd]; group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (hV₁ hu')) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : t * y * t⁻¹ ∈ L := SecA.mem_conjugate_iff.mp hy
    have h1 := Subgroup.mem_centralizer_iff.mp hcL _ hy'
    calc y * (t⁻¹ * c * t) = t⁻¹ * ((t * y * t⁻¹) * c) * t := by group
      _ = t⁻¹ * (c * (t * y * t⁻¹)) * t := by rw [h1]
      _ = t⁻¹ * c * t * y := by group
  have hdL0 : d ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    have hle : L ⊔ CFSG.conjugate L t ≤ Subgroup.centralizer ({d} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hdL y hy
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hdLt y hy
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hd1 : d = 1 := by
    have h1 : d ∈ T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := ⟨hd.1, hdL0⟩
    rw [hC0] at h1
    exact h1
  rw [hd1, mul_one] at hcd
  have hcV : c = t * u' * t⁻¹ := by rw [← hcd]; group
  rw [hcV]
  exact (fsuVM T L I).mul_mem (hUV hu)
    ((Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_fsuVM T L I ht) u').mp (hUV hu'))

end CFSG.Quasithin.Vol2.Ch10.SecE
