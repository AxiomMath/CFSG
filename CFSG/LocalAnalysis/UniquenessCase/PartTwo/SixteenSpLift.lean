module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeSmall
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.AGLEmbedding.BlockCyc

namespace SpLift

section Abstract

theorem exists_conj_le_of_not_dvd_index {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    {S K : Subgroup C} (hS : IsPGroup p S) (hK : ¬ p ∣ K.index) :
    ∃ g : C, ∀ s ∈ S, g⁻¹ * s * g ∈ K := by
  obtain ⟨q, hq⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (C ⧸ K) hK
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, fun s hs => ?_⟩
  have h1 : ((s * g : C) : C ⧸ K) = (g : C ⧸ K) := MulAction.mem_fixedPoints.1 hq ⟨s, hs⟩
  have h2 := K.inv_mem (QuotientGroup.eq.1 h1)
  have e : ((s * g)⁻¹ * g)⁻¹ = g⁻¹ * s * g := by group
  rwa [e] at h2

theorem not_isCyclic_map {A B : Type*} [Group A] [Group B] {S : Subgroup A} (f : A →* B)
    (hf : Function.Injective f) (h : ¬ IsCyclic S) : ¬ IsCyclic (S.map f) :=
  fun hc => h ((MulEquiv.isCyclic (S.equivMapOfInjective f hf)).2 hc)

theorem exists_noncyclic_pSubgroup_le {C P : Type*} [Group C] [Finite C] [Group P] (g : C →* P)
    (hg : Function.Surjective g) {p : ℕ} [Fact p.Prime] {K : Subgroup C} (hK : ¬ p ∣ K.index)
    {E : Subgroup P} (hEp : IsPGroup p E) (hEc : ¬ IsCyclic E) :
    ∃ X : Subgroup C, X ≤ K ∧ IsPGroup p X ∧ ¬ IsCyclic X := by
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  have hQc : ¬ IsCyclic (Q : Subgroup P) := fun hc => hEc (Subgroup.isCyclic_of_le hEQ)
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hg p Q
  have hSQ : (S : Subgroup C).map g = (Q : Subgroup P) := by
    rw [← hS]
    rfl
  have hSc : ¬ IsCyclic (S : Subgroup C) := by
    intro hc
    apply hQc
    rw [← hSQ]
    exact isCyclic_of_surjective (g.subgroupMap (S : Subgroup C))
      (g.subgroupMap_surjective (S : Subgroup C))
  obtain ⟨c, hc⟩ := exists_conj_le_of_not_dvd_index S.2 hK
  refine ⟨(S : Subgroup C).map (MulAut.conj c⁻¹).toMonoidHom, ?_, S.2.map _,
    not_isCyclic_map _ (MulEquiv.injective _) hSc⟩
  rintro _ ⟨s, hs, rfl⟩
  have := hc s hs
  simpa [MulAut.conj_apply] using this

end Abstract

end SpLift

section Lift

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_noncyclic_bar (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) (hp : p ∈ D.sig) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hP : PairFacts D.M V₀ V) (hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V) (h4 : Nat.card V₀ ≤ 4)
    (x : IntMod V hV) (hx0 : x.val ∉ V₀) {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hE : E ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)) (hEp : IsPGroup p E)
    (hEc : ¬ IsCyclic E) : centralizer ({x.val} : Set G) ≤ D.M := by
  classical
  haveI : Fact p.Prime := ⟨hpp⟩
  have h113 : ∃ n ≤ 2, (D.M ⊓ centralizer ({x.val} : Set G)).relIndex
      (F11.CElt D.M V₀ x.val) = 2 ^ n := by
    rcases hcase with rfl | h
    · exact ⟨0, by norm_num, by simpa using ElevenThree.relIndex_cElt_bot D.M x.val⟩
    · exact ElevenThree.relIndex_cElt_eq_pow_two h h4 x.val_mem hx0
  have hidx : ¬ p ∣ ((D.M ⊓ centralizer ({x.val} : Set G)).subgroupOf
      (F11.CElt D.M V₀ x.val)).index := by
    obtain ⟨n, -, hn⟩ := h113
    intro hd
    have hd' : p ∣ 2 ^ n := by
      rw [← hn]
      exact hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hd'))
  have hCs : F11.CElt D.M V₀ x.val ≤ stabTil V₀ V := fun c hc => ⟨hP.le_normalizer hc.1, hc.2.1⟩
  let f : ↥(F11.CElt D.M V₀ x.val) →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hCs)
  have hfmem : ∀ c : ↥(F11.CElt D.M V₀ x.val),
      f c ∈ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    intro c
    refine Subgroup.mem_inf.2 ⟨actTil_mem_barSub V₀ V hV c.2.1 (hCs c.2), ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    show actTil V₀ V hV ⟨c, hCs c.2⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    exact c.2.2.2
  let g : ↥(F11.CElt D.M V₀ x.val) →* ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)) :=
    f.codRestrict _ hfmem
  have hg : Function.Surjective g := by
    rintro ⟨φ, hφ⟩
    obtain ⟨hφM, hφst⟩ := Subgroup.mem_inf.1 hφ
    obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφM
    have hfix : actTil V₀ V hV m (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
      MulAction.mem_stabilizer_iff.1 hφst
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
    exact ⟨⟨(m : G), hmM, stabTil_le_normalizer₀ V₀ V m.2, hfix⟩, Subtype.ext rfl⟩
  have hE' : IsPGroup p (E.subgroupOf (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  have hEc' : ¬ IsCyclic (E.subgroupOf (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) :=
    fun hc => hEc ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hE)).1 hc)
  obtain ⟨X, hXK, hXp, hXc⟩ := SpLift.exists_noncyclic_pSubgroup_le g hg hidx hE' hEc'
  have hX'K : X.map (F11.CElt D.M V₀ x.val).subtype ≤ D.M ⊓ centralizer ({x.val} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hXK hc)
  have hx1 : x.val ≠ 1 := fun h => hx0 (h ▸ V₀.one_mem)
  have hx2 : ∃ n : ℕ, x.val ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 x.val x.val_mem⟩
  exact centralizer_le_of_noncyclic D h61 hp (fun y hy => (Subgroup.mem_inf.1 (hX'K hy)).1)
    (hXp.map _) (SpLift.not_isCyclic_map _ (Subgroup.subtype_injective _) hXc) hx1 hx2
    (fun y hy => (Subgroup.mem_inf.1 (hX'K hy)).2)

theorem centralizer_le_of_isG2Two (D : Data G) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hP : PairFacts D.M V₀ V)
    (hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V) (h4 : Nat.card V₀ ≤ 4) (x : IntMod V hV)
    (hx0 : x.val ∉ V₀)
    (hG : IsG2Two ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) :
    centralizer ({x.val} : Set G) ≤ D.M := by
  obtain ⟨-, -, D', -, -, hD'⟩ := hG
  obtain ⟨E₀, hE₀, hE₀c⟩ := hasE9_of_model_psu_three_three hD'
  have hE₀p : IsPGroup 3 E₀ := fun e => ⟨1, Subtype.ext (by simpa using hE₀.2 (e : D') e.2)⟩
  have hE₀nc : ¬ IsCyclic E₀ := not_isCyclic_of_isElemAbelian_sq hE₀ hE₀c
  let Z : Subgroup (MulAut (Vtil V₀ V hV)) := ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)
  have hZ : ((E₀.map D'.subtype).map Z.subtype) ≤ Z := by
    rintro _ ⟨_, _, rfl⟩
    exact Subtype.mem _
  exact centralizer_le_of_noncyclic_bar D h61 Nat.prime_three (by norm_num) h3 hV hP hcase h4 x hx0
    hZ ((hE₀p.map D'.subtype).map Z.subtype)
    (SpLift.not_isCyclic_map _ (Subgroup.subtype_injective _)
      (SpLift.not_isCyclic_map _ (Subgroup.subtype_injective _) hE₀nc))

end Lift

section Result

variable {G : Type} [Group G] [Finite G]

private theorem quadF2_one {W : Type*} [CommGroup W] {Q : W → ZMod 2} (hQ : IsQuadF2 Q) :
    Q 1 = 0 := by
  have h := hQ.1 1 1 1
  simp only [polarQ, mul_one] at h
  generalize Q 1 = a at h ⊢
  revert a
  decide

@[expose] def R16_26_fin (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L →
      (∃ Q : Vtil V₀ V hV → ZMod 2, IsPlusQuadF2 Q ∧ QuadInvariant Q (lBar V₀ V hV L)) ∧
      ∀ Q : Vtil V₀ V hV → ZMod 2, IsPlusQuadF2 Q → QuadInvariant Q (lBar V₀ V hV L) →
        (∀ w : Vtil V₀ V hV, w ≠ 1 → Q w = 0 → IsE64L3 ↥(ptCent (Mbar D.M V₀ V hV) w)) ∧
        ∀ w : Vtil V₀ V hV, Q w ≠ 0 → CFSG.Quasithin.IsG2Two ↥(ptCent (Mbar D.M V₀ V hV) w)

theorem R16_26_of_fin (D : Data G) (h61 : UC6.R6_1 D) (h : R16_26_fin D) : R16_26 D := by
  intro V₀ V L hV hS h8
  obtain ⟨hex, hall⟩ := h V₀ V L hV hS h8
  refine ⟨hex, fun Q hQ hQinv => ?_⟩
  obtain ⟨hE, hG⟩ := hall Q hQ hQinv
  refine ⟨hE, fun w hw => ⟨hG w hw, fun x hx => ?_⟩⟩
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M V₀ V := hH125.pairFacts
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases hH125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have h4 : Nat.card V₀ ≤ 4 := by
    have hV₀2 : IsPGroup 2 V₀ := fun g =>
      ⟨1, Subtype.ext (by simpa using hP.elemAbelian₀.2 (g : G) g.2)⟩
    rw [card_eq_two_pow_mSub hV₀2]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS.setting.hyp16.small
      _ = 4 := by norm_num
  have h3 : 3 ∈ D.sig := by
    rw [h8.2.2.1]
    exact Set.mem_singleton 3
  have hx0 : x.val ∉ V₀ := by
    intro h0
    have h1 : mkTil V₀ V hV x = 1 := (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 h0
    apply hw
    rw [← hx, h1]
    exact quadF2_one hQ.1.1
  exact centralizer_le_of_isG2Two D h61 h3 hV hP hcase h4 x hx0 (hx ▸ hG w hw)

end Result

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
