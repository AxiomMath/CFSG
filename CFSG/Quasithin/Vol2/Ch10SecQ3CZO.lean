module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZN
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Quasithin.Vol2.Ch10SecQ3CG
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique SecA

theorem card_eq_card_map_mul {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    {A : Subgroup X} (hA : f.ker ≤ A) : Nat.card A = Nat.card (A.map f) * Nat.card f.ker := by
  set g := f.comp A.subtype with hg
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hg, MonoidHom.range_comp,
    Subgroup.range_subtype] at h1
  have h2 : (f.comp A.subtype).ker = f.ker.subgroupOf A := rfl
  rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at h1
  exact h1

variable {G : Type} [Group G] [Finite G]

theorem card_normalizer_sylow_le {X S : Subgroup G} {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥X) (hS : IsSylowTwoOf S X) :
    Nat.card ↥(X ⊓ Subgroup.normalizer (S : Set G)) ≤ Nat.card S * (2 ^ n - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' := S.subgroupOf X with hS'
  have hS'2 : IsPGroup 2 S' := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hS'i : ¬ 2 ∣ S'.index := hS.2.2
  have hkS : α.ker ≤ S' := by
    rw [hker]
    have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).le_sylow_of_normal (hS'2.toSylow hS'i)
    simpa using h
  set P := S'.map α with hP
  have hP2 : IsPGroup 2 P := hS'2.map α
  have hPi : ¬ 2 ∣ P.index := by rw [hP, Subgroup.index_map_eq S' hα hkS]; exact hS'i
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨g, hg1, hg2⟩ := exists_conj_unip hF' hP2 hPi
  have hPc := card_eq_of_conj_unip hg1 hg2
  have hNc := card_normalizer_le hg1 hg2
  set N' := (X ⊓ Subgroup.normalizer (S : Set G)).subgroupOf X with hN'
  have hN'N : N' ≤ Subgroup.normalizer (S' : Set ↥X) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hS', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (Subgroup.mem_subgroupOf.mp hx).2 (h : G)
  have hS'N' : S' ≤ N' := fun x hx =>
    ⟨x.2, Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hx)⟩
  have hkN : α.ker ≤ N' := hkS.trans hS'N'
  have hNP : N'.map α ≤ Subgroup.normalizer (P : Set _) :=
    (Subgroup.map_mono hN'N).trans (Subgroup.le_normalizer_map α)
  have e1 := card_eq_card_map_mul α hkN
  have e2 := card_eq_card_map_mul α hkS
  have e3 : Nat.card ↥(X ⊓ Subgroup.normalizer (S : Set G)) = Nat.card N' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  have e4 : Nat.card S = Nat.card S' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv).symm
  have h5 : Nat.card ↥(N'.map α) ≤ Fintype.card F * (Fintype.card F - 1) :=
    (Subgroup.card_le_of_le hNP).trans hNc
  rw [e3, e1, e4, e2, ← hP, hPc, ← hF]
  calc Nat.card ↥(N'.map α) * Nat.card α.ker
      ≤ Fintype.card F * (Fintype.card F - 1) * Nat.card α.ker := Nat.mul_le_mul_right _ h5
    _ = Fintype.card F * Nat.card α.ker * (Fintype.card F - 1) := by ring

theorem inf_normalizer_eq_sup {X S : Subgroup G} {n : ℕ} (hX : IsLin2Type X n)
    (hS : IsSylowTwoOf S X) {b : G} (hbX : b ∈ X) (hbN : b ∈ Subgroup.normalizer (S : Set G))
    (hbo : orderOf b = 2 ^ n - 1) :
    X ⊓ Subgroup.normalizer (S : Set G) = S ⊔ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := hX
  have hle : S ⊔ Subgroup.zpowers b ≤ X ⊓ Subgroup.normalizer (S : Set G) :=
    sup_le (le_inf hS.1 Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr ⟨hbX, hbN⟩)
  have hbS : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set G) := Subgroup.zpowers_le.mpr hbN
  have hinf : Subgroup.zpowers b ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Nat.sub_self] at hbo
      exact (orderOf_pos b).ne' hbo
    have hodd : Odd (orderOf b) := by
      rw [hbo]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hn⟩) odd_one
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.1
    have hdvd : orderOf (b ^ m) ∣ orderOf b := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow]
    exact eq_one_of_mem_of_odd hS.2.1 hx.2 (hodd.of_dvd_nat hdvd)
  have hc := C5.card_sup_mul_card_inf_of_le_normalizer hbS
  rw [hinf, Subgroup.card_bot, mul_one, sup_comm, Nat.card_zpowers, hbo] at hc
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hc, mul_comm]
  exact card_normalizer_sylow_le hF α hαs hαk hS

theorem open_isQuasisimple_of_sl3 {X : Type} [Group X] {n : ℕ}
    (h : IsPSL 3 2 n X ∨ IsSL3 (2 ^ n) X) (hna : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple X := by
  have hq : CFSG.IsQuasisimple X := by
    rcases h with h | h
    · have := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 n h).2
      exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1
    · obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
      have h1 : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) K) :=
        CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).symm h1
  exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

omit [Finite G] in
theorem commutator_self_of_quasisimple {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hq.1
  rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

omit [Finite G] in
theorem commutator_eq_bot_of_quasisimple {L B : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hne : ¬ L ≤ B) : ⁅B, L⁆ = ⊥ := by
  have hc : ⁅B, L⁆ ≤ B ⊓ L := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hLB hy) x⁻¹).mp (B.inv_mem hx)
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact B.mul_mem hx h1
    · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBL hx) y).mp hy) (L.inv_mem hy)
  have hRn : ((B ⊓ L).subgroupOf L).Normal := ⟨fun r hr l => by
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hLB l.2) r).mp hr.1,
      L.mul_mem (L.mul_mem l.2 hr.2) (L.inv_mem l.2)⟩⟩
  rcases normal_eq_top_or_le_center hq hRn with h | h
  · exfalso
    apply hne
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ (B ⊓ L).subgroupOf L := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  · have hZ : ⁅B, L⁆ ≤ Subgroup.centralizer (L : Set G) := by
      intro x hx
      have hx' := hc hx
      have hmem : (⟨x, hx'.2⟩ : ↥L) ∈ Subgroup.center ↥L := h (Subgroup.mem_subgroupOf.mpr hx')
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨l, hl⟩)
    have h1 : ⁅⁅B, L⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZ
    have h2 : ⁅⁅L, B⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L B]; exact h1
    have h3 : ⁅⁅L, L⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    rw [commutator_self_of_quasisimple hq] at h3
    rw [Subgroup.commutator_comm]
    exact h3

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
