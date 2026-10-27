module

public import CFSG.Quasithin.Vol2.Ch11SecJY
public import CFSG.Quasithin.Vol2.Ch11SecJFacts
public import CFSG.Quasithin.Vol2.Ch11SecDObl557C
public import CFSG.Quasithin.Vol2.Ch11SecJBeta
public import CFSG.Quasithin.Vol2.Ch11SecJW

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

namespace Core

variable (C : Core G T L I n V₁)

include C in
theorem Ygrp_le_normalizer_V_of_facts (hEnd : FactNatPairEnd) (hDick : FactDicksonGL2)
    (h1110 : Stmt11_1_0) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) :
    Ygrp L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  obtain ⟨W, hV₁W, hWU, hWV, hWVU, hKW⟩ := C.exists_complement h1110 h1154 h1155
  obtain ⟨h5one, h5two, h5three⟩ :=
    SecD.stmt11_5_5_normalizer h1110 h1154 h1155 C.h C.hV₁ C.hSL3
  set U := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hU
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁ := fun a ha b hb =>
    h5two (Subgroup.commutator_mem_commutator ha (h5one hb))
  have hUsq : ∀ a ∈ U, a ^ 2 ∈ V₁ := fun a ha =>
    h5three (SecD.sq_mem_frattini C.St.isPGroup_U ha)
  have hKU : LOf L V₁ ≤ Subgroup.normalizer (U : Set G) :=
    lOf_le_G₁.trans (le_normalizer_conjClosure _ _)
  have hKV : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := lOf_le_L.trans C.St.D.hnorm
  obtain ⟨Ψ, hΨker, hΨx⟩ := hEnd G U (fsuV T I) V₁ W (LOf L V₁) (Cgrp T L I V₁)
    (GaloisField 2 n) C.alpha C.betaV C.betaU C.St.hyp.base.le_V (le_conjClosure _ _) hV₁W hWU
    hWV hWVU hUcomm hUsq hKU hKV lOf_le_G₁ hKW C.alpha_surjective C.betaV_surjective
    C.betaV_ker C.betaU_surjective C.betaU_ker C.betaV_conj C.betaU_conj
    (fun _ hc => hc.2.2.1) (fun _ hc => hc.1) (fun _ hc k hk => hc.2.2.2 k hk)
  obtain ⟨x, c, hc0, hc1, hx⟩ := C.exists_x
  have hxC := C.x_mem_Cgrp hx
  obtain ⟨h10, h00, h11⟩ := hΨx ⟨x, hxC⟩ c (c ^ 3)⁻¹ (C.St.D.hnorm x.2)
    (C.betaV_conj_dg x hc0 hx) (C.betaU_conj_dg x hc0 hx)
  set Yh : Subgroup (GL (Fin 2) (GaloisField 2 n)) :=
    ((Ygrp L V₁).subgroupOf (Cgrp T L I V₁)).map Ψ with hYh
  have hn0 : n ≠ 0 := by have := C.h.one_lt; omega
  have hY2 : IsPGroup 2 Yh := by
    refine hDick (GaloisField 2 n) Yh (Ψ ⟨x, hxC⟩) h10
      (by rw [h00, h11]; exact ne_inv_pow_three hc0 hc1) ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨⟨x, hxC⟩ * y * ⟨x, hxC⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
      have hxN := SecD.normalizer_le_normalizer_Y L V₁ (x_mem_G₁ hx)
      simpa using (Subgroup.mem_normalizer_iff.mp hxN _).mp hy
    · have hdvd : Nat.card Yh ∣ Nat.card ↥(Ygrp L V₁) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.Ygrp_le_Cgrp).toEquiv]
        exact Subgroup.card_map_dvd _ _
      rw [GaloisField.card 2 n hn0]
      exact Nat.Coprime.coprime_dvd_left hdvd (C.coprime_card_Ygrp h1154 h1156)
  refine C.Ygrp_le_normalizer_V fun y hy => ?_
  have hyC := C.Ygrp_le_Cgrp hy
  obtain ⟨k, hk⟩ := hY2 ⟨Ψ ⟨y, hyC⟩, ⟨y, hyC⟩, hy, rfl⟩
  refine ⟨k, ?_⟩
  have h1 : Ψ (⟨y, hyC⟩ ^ (2 ^ k)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  simpa using (hΨker _).1 h1

end Core

theorem obl11_5_7SL3BigCore_of (hEnd : FactNatPairEnd) (hDick : FactDicksonGL2)
    (hG2 : SecA.FactG2DerivedOrder) (hNat : SecD.NatV3Fact) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3)
    (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) :
    SecD.Obl11_5_7SL3BigCore := by
  intro G _ _ T L I n V₁ x y hconf hK hUL _ hcard hO2L
  obtain ⟨h, hV₁, hSL3, hU, -, -, -, -, -, -, -, -, -, -⟩ := hconf
  have hyp := SecD.almostSpecialL3Hyp_of_kindSL3 hG2 hNat h1102 h1110 h1141 h hV₁ hSL3 hU
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let C : Core G T L I n V₁ := ⟨⟨hyp, D⟩, h, hV₁, hSL3, hK, hUL, hO2L, hcard⟩
  have hY := C.Ygrp_le_normalizer_V_of_facts hEnd hDick h1110 h1154 h1155 h1156
  obtain ⟨z, hzV₁, hz1, hzT⟩ := SecD.exists_z h hV₁
  have hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨SecA.IsVi.le_fsuV hV₁ hzV₁, hzT⟩
  have hdec := (h1143 G T L I n V₁ h hV₁ z hz hz1).2.2
  apply (h1154 G T L I n V₁ h hV₁).1
  intro g hg
  have hgN : g ∈ (Subgroup.normalizer (V₁ : Set G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hg
  rw [hdec] at hgN
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, m, hm, rfl⟩ := hgN
  have haK : a ∈ LOf L V₁ := hK ▸ ha
  have haL : a ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer (lOf_le_L haK)
  have hbL : b ∈ Subgroup.normalizer (L : Set G) :=
    SecA.normalizer_fsuV_le h331 h (hY ⟨hb.1.2, hb.2⟩)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haL hbL) hm.1

end CFSG.Quasithin.Vol2.Ch11.SecJ
