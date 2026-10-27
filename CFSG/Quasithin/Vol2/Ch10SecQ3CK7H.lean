module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H60
public import CFSG.Quasithin.Vol2.Ch10SecD33B
public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecQ9H59

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS.K7

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem quot_A7 {T L I H K M₁ J : Subgroup G} {n m : ℕ} (cfg : B0KConfig G T L I H K M₁ J n m)
    (hc : B0KTypeC M₁ K J) :
    IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨ IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := modO2_mulEquiv cfg.hJ
  rcases hc.2 with hA | h
  · obtain ⟨f⟩ := hA
    exact Or.inl ⟨e.trans f⟩
  · exact Or.inr (IsHat.of_mulEquiv e.symm h)

theorem not_thompsonJ_le (h1022 : Stmt10_2_2) {T L I H K M₁ J : Subgroup G} {n m : ℕ}
    (cfg : B0KConfig G T L I H K M₁ J n m) (hJn : T ≤ Subgroup.normalizer (J : Set G)) :
    ¬ thompsonJ T ≤
      Subgroup.centralizer ((⁅quasithinOmegaOneCenter T, J⁆ : Subgroup G) : Set G) := by
  intro hle
  have hJW : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) :=
    ((h1022 G T L I cfg.hyp H cfg.hH cfg.hZH).2 (Or.inl ⟨n, cfg.case1⟩)).1.2.1
  have hTH : IsSylowTwoOf T H :=
    ⟨cfg.hH.1.1, cfg.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le cfg.hyp.fsu.sylow cfg.hH.1.1⟩
  have hHJT : H ≤ J ⊔ T := by
    rw [← SecD.oTwoUpper_sup_eq hTH, cfg.hHK]
    refine sup_le_sup_right ?_ T
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨t, ht, k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hJn ht) k).mp (cfg.hKJ hk)
  have hVZ : VZ T H ≤ quasithinOmegaOneCenter T ⊔ ⁅quasithinOmegaOneCenter T, J⁆ := by
    rw [VZ, conjClosure, Subgroup.closure_le]
    rintro _ ⟨h, hh, z, hz, rfl⟩
    have hh' : h ∈ ((J ⊔ T : Subgroup G) : Set G) := hHJT hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left J T hJn] at hh'
    obtain ⟨j, hj, t, ht, rfl⟩ := Set.mem_mul.mp hh'
    have htz : t * z * t⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp (E3.omegaOneCenter_le_inf_centralizer T hz).2 t ht,
        mul_inv_cancel_right]
    have e : j * t * z * (j * t)⁻¹ = ⁅j, z⁆ * z := by
      rw [commutatorElement_def]
      calc j * t * z * (j * t)⁻¹ = j * (t * z * t⁻¹) * j⁻¹ := by group
        _ = j * z * j⁻¹ * z⁻¹ * z := by rw [htz]; group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hz)
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hj hz
  have hZc : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (thompsonJ T : Set G) :=
    (E3.omegaOneCenter_le_inf_centralizer T).trans
      (inf_le_right.trans (Subgroup.centralizer_le (B6.thompsonJ_le T)))
  exact hJW (Subgroup.le_centralizer_iff.mp
    (hVZ.trans (sup_le hZc (Subgroup.le_centralizer_iff.mp hle))))

theorem four_le_card_image
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) {T L I H K M₁ J : Subgroup G} {n m : ℕ}
    (cfg : B0KConfig G T L I H K M₁ J n m) (hc : B0KTypeC M₁ K J) :
    4 ≤ Nat.card ↥(modO2Image M₁ (baum T ⊓ J)) := by
  have hSK := isSylowTwoOf_baum_inf hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS cfg
  have hJM : J ≤ M₁ := le_of_mem_cComp cfg.hJ
  have hKM : K ≤ M₁ := cfg.hKJ.trans hJM
  set ψ := toModO2 M₁ K K le_rfl hKM with hψ
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, hψ, range_toModO2, Subgroup.subgroupOf_self]
  have hS' : IsSylowTwoOf ((baum T ⊓ K).subgroupOf K) ⊤ := by
    refine ⟨le_top, hSK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSK.1).symm, ?_⟩
    show ¬ 2 ∣ ((baum T ⊓ K).subgroupOf K).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hSK.2.2
  set P := ((baum T ⊓ K).subgroupOf K).map ψ with hP
  have hPs : IsSylowTwoOf P ⊤ := A312.isSylowTwoOf_top_map ψ hsurj hS'
  have hK : Nat.card ↥(modO2Image M₁ K) = 60 ∨ Nat.card ↥(modO2Image M₁ K) = 168 := by
    rcases hc.1 with h5 | h3
    · exact Or.inl (Ch1Four.card_alt5 h5)
    · exact Or.inr (Ch1Four.card_of_isPSL_three_two h3)
  have h4P : 4 ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hPs.2.1
    have hidx : ¬ 2 ∣ P.index := by
      have := hPs.2.2
      rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at this
    have hmul := Subgroup.card_mul_index P
    rw [hk] at hmul ⊢
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> rcases hK with h | h <;> rw [h] at hmul <;> norm_num at hmul <;>
        omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hle : P.map (modO2Image M₁ K).subtype ≤ modO2Image M₁ (baum T ⊓ J) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨x, hKM x.2⟩, Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp hx).1, cfg.hKJ x.2⟩, ?_⟩
    rw [hψ, Subgroup.coe_subtype, toModO2_coe]
  calc 4 ≤ Nat.card P := h4P
    _ = Nat.card ↥(P.map (modO2Image M₁ K).subtype) :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

omit [Finite G] in
theorem mem_normalizer_centralizer {S : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (S : Set G)) :
    y ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ x ∈ Subgroup.centralizer (S : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
      simpa using this
    have h := hx _ hs'
    calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hx
  simpa [mul_assoc] using this

end C11AmS.K7

end CFSG.Quasithin.Vol2.Ch10.SecB
