module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.CharacteristicNormalizer
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.StandardType.FS81.N6AllMat
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvCube
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvSylow
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Defs
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Coxeter
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Local
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Mat
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import CFSG.Mathlib.GroupTheory.CoxeterCentralLift

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylow_centralizer_eq_subgroupOf {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hsyl : ∀ y ∈ Subgroup.centralizer (E : Set G), ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ E) :
    ∃ P : Sylow 3 ↥(Subgroup.centralizer (E : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer (E : Set G))) =
        E.subgroupOf (Subgroup.centralizer (E : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer (E : Set G)
  have hEC : E ≤ C := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hE.comm he hx).symm
  have hEC3 : IsPGroup 3 (E.subgroupOf C) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hE.2 ((x : C) : G) (Subgroup.mem_subgroupOf.mp x.2)))⟩
  obtain ⟨P, hEP⟩ := hEC3.exists_le_sylow
  have hPE : (P : Subgroup C) ≤ E.subgroupOf C := by
    intro p hp
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    exact Subgroup.mem_subgroupOf.mpr (hsyl (p : G) p.2 k (by
      simpa using congrArg (fun z : ↥P => ((z : C) : G)) hk))
  exact ⟨P, le_antisymm hPE hEP⟩

omit [Finite G] in
theorem normal_subgroupOf_normalizer_of_characteristic_centralizer {E R : Subgroup G}
    (hRC : R ≤ Subgroup.centralizer (E : Set G))
    (hR : (R.subgroupOf (Subgroup.centralizer (E : Set G))).Characteristic) :
    (R.subgroupOf (Subgroup.normalizer (E : Set G))).Normal := by
  have hRleN : R ≤ Subgroup.normalizer (E : Set G) :=
    hRC.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRleN]
  have hCN : Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (E : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G))
  exact hCN.trans
    (CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic hRC hR)

theorem exists_centralizer_eq_sup_twD5 {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E)
    (hnorm : ¬ (Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) :
    ∃ R : Subgroup G, ¬ 3 ∣ Nat.card R ∧ R ≤ Subgroup.centralizer (E : Set G) ∧
      (R.subgroupOf (Subgroup.normalizer (E : Set G))).Normal ∧
      Subgroup.centralizer (E : Set G) = E ⊔ R := by
  classical
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -, hEmax, -, -, -⟩ := hhyp
  obtain ⟨-, hsup, -, -, hself⟩ := hcanon
  have hOut : ¬ 3 ∣ Nat.card (Outer K) := not_three_dvd_card_outer_of_isTwD5 hKmark hKz
  have hsyl : ∀ y ∈ Subgroup.centralizer (E : Set G), ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ E :=
    fun y hy k hk => fs81_three_elem_mem_E hb₀ hKC hKn hOut hA2 hsup hself hEmax.2.1 hnorm hy hk
  set C : Subgroup G := Subgroup.centralizer (E : Set G)
  have hEC : E ≤ C := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hEmax.2.1.comm he hx).symm
  obtain ⟨P, hPeq⟩ := exists_sylow_centralizer_eq_subgroupOf hEmax.2.1 hsyl
  have hPcent : Subgroup.normalizer (P : Set C) ≤ Subgroup.centralizer (P : Set C) := by
    intro c _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpE : (p : G) ∈ E := Subgroup.mem_subgroupOf.mp (hPeq ▸ hp)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 (p : G) hpE)
  obtain ⟨K', -, hK3, -, -, hKchar, -, hKsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hPcent
  have hRchar : ((K'.map C.subtype).subgroupOf C).Characteristic := by
    rw [← Subgroup.comap_subtype (K'.map C.subtype) C,
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective K']
    exact hKchar
  refine ⟨K'.map C.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective C.subtype_injective]
  · exact normal_subgroupOf_normalizer_of_characteristic_centralizer
      (Subgroup.map_subtype_le K') hRchar
  · have h := congrArg (Subgroup.map C.subtype) hKsup
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype, hPeq,
      Subgroup.map_subgroupOf_eq_of_le hEC] at h
    rw [sup_comm]
    exact h.symm

theorem evenFix0_mulVec_zero {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ evenFix0 n) (v : Coords (n + 1)) : (A *ᵥ v) 0 = v 0 := by
  obtain ⟨σ, s, -, ⟨hσ, hs0, -⟩, rfl⟩ := hA
  have hσ' : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ]
  rw [spMat_mulVec]
  simp [hσ', hs0]

theorem rE6_mulVec_zero (ε : ZMod 3) (v : Coords 6) : (rE6 ε *ᵥ v) 0 = v 0 := by
  rw [rE6, Matrix.add_mulVec, Matrix.one_mulVec]
  simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct]

def fixesZeroCoord (B : GL (Fin 6) (ZMod 3)) : Prop :=
  ∀ v : Coords 6, ((B : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 0 = v 0

theorem wE6_mulVec_zero (ε : ZMod 3) {A : GL (Fin 6) (ZMod 3)} (hA : A ∈ wE6 ε)
    (v : Coords 6) : ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 0 = v 0 := by
  have hP : ∀ B ∈ wE6 ε, fixesZeroCoord B := by
    intro B hB
    refine Subgroup.closure_induction (p := fun B _ => fixesZeroCoord B) ?_ ?_ ?_ ?_ hB
    · intro C hC
      rcases hC with hC | hC
      · exact fun w => evenFix0_mulVec_zero hC w
      · intro w
        rw [hC]
        exact rE6_mulVec_zero ε w
    · intro w
      exact congrFun (Matrix.one_mulVec w) 0
    · intro B C _ _ hB hC w
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hB ((C : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w)).trans (hC w)
    · intro B _ hB w
      have h2 : ((B : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
          (((B⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w)) = w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have h3 := hB ((((B⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w))
      rw [h2] at h3
      exact h3.symm
  exact hP A hA v

omit [Finite G] in
theorem conj_mul_inv_mem_inf_of_mem_normalizer {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) {g x : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) (hx : x ∈ E) :
    g * x * g⁻¹ * x⁻¹ ∈ E ⊓ K := by
  classical
  have hgS : g ∈ Subgroup.normalizer (B.span : Set G) := by rwa [hB.1]
  have hxS : x ∈ B.span := by rwa [hB.1]
  set φ : MulAut ↥B.span := B.span.normalizerMonoidHom ⟨g, hgS⟩
  have hφg : ∀ y : ↥B.span, ((φ y : ↥B.span) : G) = g * y * g⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hφmem : φ ∈ ggAutomizer ⊤ B.span := by
    rw [CFSG.StandardType.mem_ggAutomizer_iff]
    exact ⟨g, Subgroup.mem_top g, hgS, hφg⟩
  have hgl : B.glHom φ ∈ wE6 ε := by
    have hmap : B.glHom φ ∈ (ggAutomizer ⊤ B.span).map B.glHom := ⟨φ, hφmem, rfl⟩
    rwa [hX] at hmap
  set e : Coords 6 := B.coords ⟨x, hxS⟩
  have hrow : (B.matOf φ *ᵥ e) 0 = e 0 := by
    have h := wE6_mulVec_zero ε hgl e
    rwa [B.coe_glHom] at h
  have hxvec : B.vec e = x := B.vec_coords ⟨x, hxS⟩
  have hzero : (B.matOf φ *ᵥ e - e) 0 = 0 := by
    simp [Pi.sub_apply, hrow]
  have hcomm : g * x * g⁻¹ * x⁻¹ = B.vec (B.matOf φ *ᵥ e - e) := by
    rw [← hxvec, B.acts_vec' hgS (B.acts_matOf hφg) e, ← B.vec_neg', ← B.vec_add]
    congr 1
    abel
  rw [hcomm]
  exact ⟨by rw [← hB.1]; exact B.vec_mem_span _, B.vec_mem_of_zero hB.2.2 hzero⟩


theorem rE6_mulVec_single_one (ε : ZMod 3) :
    (rE6 ε *ᵥ (Pi.single 0 1 : Coords 6)) 1 = 1 := by
  simp [rE6, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.sum_univ_six]

theorem rE6Unit_mem_wE6 (ε : ZMod 3) (hε : ε ≠ 0) : rE6Unit ε hε ∈ wE6 ε :=
  Subgroup.subset_closure (Or.inr (by rw [coe_rE6Unit]))

omit [Finite G] in
theorem not_normalizer_le_normalizer_zpowers_of_wE6 {B : Basis3 G (5 + 1)} {b₀ : G}
    {K E : Subgroup G} (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) (hε : ε ≠ 0) :
    ¬ (Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
  intro hle
  have hmem : rE6Unit ε hε ∈ (ggAutomizer ⊤ B.span).map B.glHom := by
    rw [hX]
    exact rE6Unit_mem_wE6 ε hε
  obtain ⟨φ, hφmem, hφeq⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g, -, hgS, hφg⟩ := CFSG.StandardType.mem_ggAutomizer_iff.mp hφmem
  have hgN : g ∈ Subgroup.normalizer (E : Set G) := by rwa [hB.1] at hgS
  have hb0vec : B.vec (Pi.single 0 1 : Coords 6) = b₀ := by
    rw [B.vec_single, hB.2.1]
  have hmemz : g * b₀ * g⁻¹ ∈ Subgroup.zpowers b₀ :=
    (Subgroup.mem_normalizer_iff.mp (hle hgN) b₀).mp (Subgroup.mem_zpowers b₀)
  have hM : B.matOf φ = rE6 ε := by
    rw [← B.coe_glHom, hφeq, coe_rE6Unit]
  have hconj : g * b₀ * g⁻¹ =
      B.vec (B.matOf φ *ᵥ (Pi.single 0 1 : Coords 6)) := by
    rw [← hb0vec, B.acts_vec' hgS (B.acts_matOf hφg) (Pi.single 0 1)]
  rw [hconj, ← hb0vec] at hmemz
  have hne : B.matOf φ *ᵥ (Pi.single 0 1 : Coords 6) ≠ 0 := by
    rw [hM]
    intro h0
    have h1 := congrFun h0 1
    rw [rE6_mulVec_single_one] at h1
    exact one_ne_zero h1
  obtain h | h := B.eq_or_eq_neg_of_vec_mem_zpowers hne hmemz
  · have hc := congrFun h 1
    rw [hM, rE6_mulVec_single_one] at hc
    exact one_ne_zero hc
  · have hc := congrFun h 1
    rw [hM, rE6_mulVec_single_one] at hc
    simp at hc


theorem normalizerMonoidHom_range_eq_ggAutomizer {G : Type} [Group G] (B : Subgroup G) :
    B.normalizerMonoidHom.range = ggAutomizer (⊤ : Subgroup G) B := by
  rw [ggAutomizer_eq]
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, Subgroup.mem_top g, g.2,
      fun b => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _⟩
  · rintro ⟨g, -, hg, hφ⟩
    refine ⟨⟨g, hg⟩, MulEquiv.ext fun b => Subtype.ext ?_⟩
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (hφ b).symm

theorem inf_eq_bot_of_pow_three_eq_one_of_not_dvd_card {G : Type} [Group G] {E R : Subgroup G}
    (hE : ∀ x ∈ E, x ^ 3 = 1) (hR : ¬ 3 ∣ Nat.card R) : E ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hE x hx.1)
  have hR' : orderOf x ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hx.2
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h)
  · exact absurd (h ▸ hR') hR

theorem normal_subgroupOf_inf_of_wE6 {G : Type} [Group G] {B : Basis3 G (5 + 1)} {b₀ : G}
    {K E : Subgroup G} (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) :
    ((E ⊓ K).subgroupOf (Subgroup.normalizer (E : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  change (g : G) * (n : G) * (g : G)⁻¹ ∈ E ⊓ K
  have hconj := conj_mul_inv_mem_inf_of_mem_normalizer hB hX g.2 hn.1
  have heq : (g : G) * (n : G) * (g : G)⁻¹ =
      ((g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹) * (n : G) := by group
  rw [heq]
  exact (E ⊓ K).mul_mem hconj hn

theorem card_wE6_eq_51840 {G : Type} [Group G] {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε)
    (hgt : 2 ^ 6 * Nat.factorial 6 < Nat.card (ggAutomizer ⊤ E))
    (hdvd : Nat.card (wE6 ε) ∣ 51840) : Nat.card (wE6 ε) = 51840 := by
  have hcard : Nat.card (wE6 ε) = Nat.card (ggAutomizer ⊤ B.span) := by
    rw [← hX, Subgroup.card_map_of_injective B.glHom_injective]
  have hgt' : 2 ^ 6 * Nat.factorial 6 < Nat.card (wE6 ε) := by
    rw [hcard, hB.1]
    exact hgt
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, mul_zero] at hk
      omega
    by_contra hne
    have h2 : 2 ≤ k := by omega
    have hle : Nat.card (wE6 ε) * 2 ≤ 51840 := by
      calc Nat.card (wE6 ε) * 2 ≤ Nat.card (wE6 ε) * k := Nat.mul_le_mul_left _ h2
        _ = 51840 := hk.symm
    have hgt2 : 51840 < Nat.card (wE6 ε) * 2 := by
      calc 51840 < (2 ^ 6 * Nat.factorial 6) * 2 := by norm_num
        _ < Nat.card (wE6 ε) * 2 := Nat.mul_lt_mul_of_pos_right hgt' (by norm_num)
    omega
  rw [hk1, mul_one] at hk
  exact hk.symm

theorem map_subgroupOf_eq_of_eq_sup {G : Type} [Group G] {N C E R Q : Subgroup G}
    (hEN : E ≤ N) (hRN : R ≤ N) [hRn : (R.subgroupOf N).Normal] (hRQ : R ≤ Q)
    [hQn : (Q.subgroupOf N).Normal] (hC : C = E ⊔ R) :
    (C.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) =
      (E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) := by
  refine le_antisymm ?_
    (Subgroup.map_mono (Subgroup.subgroupOf_mono N (by rw [hC]; exact le_sup_left)))
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
  have hcmem : c ∈ E.subgroupOf N ⊔ R.subgroupOf N := by
    rw [← Subgroup.subgroupOf_sup hEN hRN, ← hC]
    exact hc
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hcmem
  refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
  rw [← hyz, map_mul]
  have hzQ : QuotientGroup.mk' (Q.subgroupOf N) z = 1 := by
    change (z : ↥N ⧸ Q.subgroupOf N) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (hRQ (Subgroup.mem_subgroupOf.mp hz))
  rw [hzQ, mul_one]

theorem map_subgroupOf_le_center_quotient_of_conj_mem {G : Type} [Group G]
    {N E A Q : Subgroup G} (hAQ : A ≤ Q) [hQn : (Q.subgroupOf N).Normal]
    (hconj : ∀ g ∈ N, ∀ x ∈ E, g * x * g⁻¹ * x⁻¹ ∈ A) :
    (E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) ≤
      Subgroup.center (↥N ⧸ Q.subgroupOf N) := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf N) y
  rw [← map_mul, ← map_mul]
  change ((h * e : ↥N) : ↥N ⧸ Q.subgroupOf N) = ((e * h : ↥N) : ↥N ⧸ Q.subgroupOf N)
  rw [QuotientGroup.eq_iff_div_mem]
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hc := hconj h.1 h.2 e.1 (Subgroup.mem_subgroupOf.mp he)
  have hval : (((h * e) / (e * h) : ↥N) : G) = h.1 * e.1 * h.1⁻¹ * e.1⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, mul_inv_rev]
    group
  rw [hval]
  exact hAQ hc

theorem not_mem_sup_of_disjoint {G : Type} [Group G] {N A E R : Subgroup G} {b₀ : G}
    (hAE : A ≤ E) (hEN : E ≤ N) (hAN : A ≤ N) (hRN : R ≤ N)
    [hRn : (R.subgroupOf N).Normal] (hb : b₀ ∈ E) (hord : orderOf b₀ = 3)
    (hdisj : Disjoint (Subgroup.zpowers b₀) A) (hER : E ⊓ R = ⊥) : b₀ ∉ A ⊔ R := by
  intro hb0
  have hb0A : b₀ ∉ A := by
    intro hA
    have hmem : b₀ ∈ Subgroup.zpowers b₀ ⊓ A := ⟨Subgroup.mem_zpowers b₀, hA⟩
    have h1 : b₀ = 1 := Subgroup.mem_bot.mp (disjoint_iff_inf_le.mp hdisj hmem)
    rw [h1, orderOf_one] at hord
    omega
  have hb0N : b₀ ∈ N := hEN hb
  have hb0QN : (⟨b₀, hb0N⟩ : ↥N) ∈ (A ⊔ R).subgroupOf N := hb0
  rw [Subgroup.subgroupOf_sup hAN hRN] at hb0QN
  obtain ⟨a, ha, r, hr, har⟩ := Subgroup.mem_sup_of_normal_right.mp hb0QN
  have har' : (a : G) * (r : G) = b₀ := congrArg Subtype.val har
  have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hr' : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hrE : (r : G) ∈ E := by
    have h1 : (r : G) = (a : G)⁻¹ * b₀ := by rw [← har']; group
    rw [h1]
    exact E.mul_mem (E.inv_mem (hAE ha')) hb
  have hr1 : (r : G) = 1 := by
    have hmem : (r : G) ∈ E ⊓ R := ⟨hrE, hr'⟩
    rw [hER] at hmem
    exact Subgroup.mem_bot.mp hmem
  apply hb0A
  have h1 : b₀ = (a : G) := by rw [← har', hr1, mul_one]
  rw [h1]
  exact ha'


theorem normal_subgroupOf_sup_of_normal {G : Type} [Group G] {N A R : Subgroup G}
    (hAN : A ≤ N) (hRN : R ≤ N) [hAn : (A.subgroupOf N).Normal]
    [hRn : (R.subgroupOf N).Normal] : ((A ⊔ R).subgroupOf N).Normal := by
  rw [Subgroup.subgroupOf_sup hAN hRN]
  infer_instance

theorem exists_liftable_generators_wE6 {ε : ZMod 3} {s : Fin 6 → GL (Fin 6) (ZMod 3)}
    (hs : CoxeterMatrix.E₆.IsLiftable s)
    (hgen : Subgroup.closure (Set.range s) = wE6 ε) :
    ∃ s' : Fin 6 → ↥(wE6 ε), CoxeterMatrix.E₆.IsLiftable s' ∧
      Subgroup.closure (Set.range s') = ⊤ := by
  classical
  let s' : Fin 6 → ↥(wE6 ε) := fun i =>
    ⟨s i, by rw [← hgen]; exact Subgroup.subset_closure ⟨i, rfl⟩⟩
  refine ⟨s', ?_, ?_⟩
  · intro i j
    apply Subtype.ext
    simpa using hs i j
  · rw [eq_top_iff]
    intro x _
    have hto : ∀ {y : GL (Fin 6) (ZMod 3)},
        y ∈ Subgroup.closure (Set.range s) → y ∈ wE6 ε := by
      intro y hy
      rwa [hgen] at hy
    have hx' : (x : GL (Fin 6) (ZMod 3)) ∈ Subgroup.closure (Set.range s) := by
      rw [hgen]
      exact x.2
    let xE : ↥(wE6 ε) := ⟨(x : GL (Fin 6) (ZMod 3)), hto hx'⟩
    have hcl : xE ∈ Subgroup.closure (Set.range s') := by
      refine Subgroup.closure_induction (p := fun y hy =>
        (⟨y, hto hy⟩ : ↥(wE6 ε)) ∈ Subgroup.closure (Set.range s')) ?_ ?_ ?_ ?_ hx'
      · rintro y ⟨i, rfl⟩
        exact Subgroup.subset_closure ⟨i, rfl⟩
      · exact Subgroup.one_mem _
      · intro y z hy hz ihy ihz
        exact Subgroup.mul_mem _ ihy ihz
      · intro y hy ihy
        exact Subgroup.inv_mem _ ihy
    have heq : xE = x := Subtype.ext rfl
    rwa [heq] at hcl

theorem exists_action_hom_of_wE6 {G : Type} [Group G] {B : Basis3 G (5 + 1)} {b₀ : G}
    {K E : Subgroup G} (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε) :
    ∃ f : ↥(Subgroup.normalizer (E : Set G)) →* ↥(wE6 ε),
      Function.Surjective f ∧
        f.ker = (Subgroup.centralizer (E : Set G)).subgroupOf
          (Subgroup.normalizer (E : Set G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (E : Set G)
  let τ : ↥N →* ↥(Subgroup.normalizer (B.span : Set G)) :=
    { toFun := fun x => ⟨x.1, hB.1.symm ▸ x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hτ : Function.Surjective τ := fun y =>
    ⟨⟨y.1, hB.1 ▸ y.2⟩, Subtype.ext rfl⟩
  let g : ↥N →* GL (Fin 6) (ZMod 3) := B.glHom.comp (B.span.normalizerMonoidHom.comp τ)
  have hgrange : g.range = wE6 ε := by
    show (B.glHom.comp (B.span.normalizerMonoidHom.comp τ)).range = wE6 ε
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hτ,
      Subgroup.map_top, normalizerMonoidHom_range_eq_ggAutomizer, hX]
  have hfmem : ∀ x : ↥N, g x ∈ wE6 ε := fun x => by
    have hx : g x ∈ g.range := ⟨x, rfl⟩
    rwa [hgrange] at hx
  let f : ↥N →* ↥(wE6 ε) := g.codRestrict (wE6 ε) hfmem
  have hfker : f.ker = (Subgroup.centralizer (E : Set G)).subgroupOf N := by
    show (g.codRestrict (wE6 ε) hfmem).ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf N
    rw [MonoidHom.ker_codRestrict]
    change (B.glHom.comp (B.span.normalizerMonoidHom.comp τ)).ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf N
    rw [MonoidHom.ker_comp_of_injective _ _ B.glHom_injective]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker]
    simp [τ, Subgroup.mem_subgroupOf, hB.1]
  refine ⟨f, fun y => ?_, hfker⟩
  have hy : (y : GL (Fin 6) (ZMod 3)) ∈ g.range := by
    rw [hgrange]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem exists_quotient_action_of_action_hom {G : Type} [Group G] [Finite G]
    {N C E Q : Subgroup G} {X : Type} [Group X] [Finite X]
    [hQn : (Q.subgroupOf N).Normal]
    (f : ↥N →* X) (hf : Function.Surjective f) (hfker : f.ker = C.subgroupOf N)
    (hQle : Q.subgroupOf N ≤ f.ker)
    (himg : (C.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) =
      (E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)))
    (hEN : E ≤ N) (hEcard : Nat.card E = 3 ^ 6)
    (hcenter : (E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) ≤
      Subgroup.center (↥N ⧸ Q.subgroupOf N)) :
    ∃ π : ↥N ⧸ Q.subgroupOf N →* X,
      Function.Surjective π ∧ π.ker = (E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) ∧
      π.ker ≤ Subgroup.center (↥N ⧸ Q.subgroupOf N) ∧ Odd (Nat.card π.ker) := by
  classical
  let π : ↥N ⧸ Q.subgroupOf N →* X := QuotientGroup.lift (Q.subgroupOf N) f hQle
  have hπ : Function.Surjective π :=
    QuotientGroup.lift_surjective_of_surjective (Q.subgroupOf N) f hf hQle
  have hπker : π.ker = (E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) := by
    show (QuotientGroup.lift (Q.subgroupOf N) f hQle).ker = _
    rw [QuotientGroup.ker_lift, hfker, himg]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hπker]
    refine Odd.of_dvd_nat (n := 3 ^ 6) (by norm_num) ?_
    calc Nat.card ((E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)))
        ∣ Nat.card (E.subgroupOf N) :=
          Subgroup.card_map_dvd (E.subgroupOf N) (QuotientGroup.mk' (Q.subgroupOf N))
      _ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
      _ = 3 ^ 6 := hEcard
  rw [← hπker] at hcenter
  exact ⟨π, hπ, hπker, hcenter, hodd⟩

theorem not_mem_commutator_of_quotient_action {G : Type} [Group G] [Finite G]
    {N Q : Subgroup G} {X : Type} [Group X] [Finite X]
    [hQn : (Q.subgroupOf N).Normal]
    (π : ↥N ⧸ Q.subgroupOf N →* X) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center (↥N ⧸ Q.subgroupOf N)) (hodd : Odd (Nat.card π.ker))
    (s : Fin 6 → X) (hs : CoxeterMatrix.E₆.IsLiftable s)
    (hgen : Subgroup.closure (Set.range s) = ⊤)
    (hcard : Nat.card CoxeterMatrix.E₆.Group = Nat.card X)
    {b₀ : G} (hb0N : b₀ ∈ N) (hb0Q : b₀ ∉ Q)
    (hker : QuotientGroup.mk' (Q.subgroupOf N) (⟨b₀, hb0N⟩ : ↥N) ∈ π.ker) :
    (⟨b₀, hb0N⟩ : ↥N) ∉ commutator ↥N := by
  have hdisj : Disjoint π.ker (commutator (↥N ⧸ Q.subgroupOf N)) :=
    disjoint_ker_commutator_of_coxeter CoxeterMatrix.E₆ π hπ hZ hodd s hs hgen hcard
  intro hmem
  have hc : QuotientGroup.mk' (Q.subgroupOf N) (⟨b₀, hb0N⟩ : ↥N) ∈
      commutator (↥N ⧸ Q.subgroupOf N) := by
    have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf N)) hmem
    rw [commutator_def] at h
    rwa [Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h
  have h1 : QuotientGroup.mk' (Q.subgroupOf N) (⟨b₀, hb0N⟩ : ↥N) = 1 :=
    Subgroup.mem_bot.mp (disjoint_iff_inf_le.mp hdisj ⟨hker, hc⟩)
  exact hb0Q (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))

theorem not_mem_commutator_normalizer_of_wE6
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) {ε : ZMod 3}
    (hε : ε = 1 ∨ ε = -1) (hX : (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε)
    (s : Fin 6 → GL (Fin 6) (ZMod 3))
    (hs : CoxeterMatrix.E₆.IsLiftable s) (hgen : Subgroup.closure (Set.range s) = wE6 ε)
    (hdvd : Nat.card (wE6 ε) ∣ 51840) (hb : b₀ ∈ E) :
    (⟨b₀, Subgroup.le_normalizer hb⟩ : ↥(Subgroup.normalizer (E : Set G))) ∉
      commutator ↥(Subgroup.normalizer (E : Set G)) := by
  classical
  have hnorm := not_normalizer_le_normalizer_zpowers_of_wE6 hB hX (by
    rcases hε with rfl | rfl <;> decide)
  obtain ⟨R, hR3, hRC, hRn, hCeq⟩ := exists_centralizer_eq_sup_twD5 hstd hnorm
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hord, -, -, -, -, -, -, -, hEmax, -, hEcard, hAut⟩ := hhyp
  obtain ⟨hdisj0, -, -, -, -⟩ := hcanon
  let N : Subgroup G := Subgroup.normalizer (E : Set G)
  let C : Subgroup G := Subgroup.centralizer (E : Set G)
  let A : Subgroup G := E ⊓ K; let Q : Subgroup G := A ⊔ R
  have hEN : E ≤ N := Subgroup.le_normalizer
  have hRN : R ≤ N := hRC.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  have hALN : A ≤ N := inf_le_left.trans hEN
  have hEC : E ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hEmax.2.1.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hER : E ⊓ R = ⊥ :=
    inf_eq_bot_of_pow_three_eq_one_of_not_dvd_card (fun x hx => hEmax.2.1.2 x hx) hR3
  have hb0notQ : b₀ ∉ Q :=
    not_mem_sup_of_disjoint inf_le_left hEN hALN hRN hb hord hdisj0 hER (hRn := hRn)
  have hQn : (Q.subgroupOf N).Normal :=
    normal_subgroupOf_sup_of_normal hALN hRN (hAn := normal_subgroupOf_inf_of_wE6 hB hX)
      (hRn := hRn)
  obtain ⟨f, hfsurj, hfker⟩ := exists_action_hom_of_wE6 hB hX
  have hQle : Q.subgroupOf N ≤ f.ker := by
    rw [hfker]
    exact Subgroup.subgroupOf_mono N (sup_le (fun x hx => hEC hx.1) hRC)
  have himg : (C.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) =
      (E.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) :=
    map_subgroupOf_eq_of_eq_sup hEN hRN le_sup_right hCeq (hRn := hRn) (hQn := hQn)
  have hcenter := map_subgroupOf_le_center_quotient_of_conj_mem le_sup_left
    (fun g hg x hx => conj_mul_inv_mem_inf_of_mem_normalizer hB hX hg hx) (hQn := hQn)
  obtain ⟨π, hπ, hπker, hπZ, hπodd⟩ :=
    exists_quotient_action_of_action_hom f hfsurj hfker hQle himg hEN hEcard hcenter
      (hQn := hQn)
  obtain ⟨s', hs', hgen'⟩ := exists_liftable_generators_wE6 hs hgen
  have hW : Nat.card CoxeterMatrix.E₆.Group = Nat.card ↥(wE6 ε) := by
    rw [card_coxeterE6_group, show Nat.card ↥(wE6 ε) = Nat.card (wE6 ε) from rfl,
      card_wE6_eq_51840 hB hX hAut hdvd]
  have hb0N : b₀ ∈ N := hEN hb
  have hkerb : QuotientGroup.mk' (Q.subgroupOf N) ⟨b₀, hb0N⟩ ∈ π.ker := by
    rw [hπker]
    exact Subgroup.mem_map.mpr ⟨⟨b₀, hb0N⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  exact not_mem_commutator_of_quotient_action π hπ hπZ hπodd s' hs' hgen' hW hb0N hb0notQ
    hkerb (hQn := hQn)

end CFSG.StandardType.FrameRoute.FS81

end
