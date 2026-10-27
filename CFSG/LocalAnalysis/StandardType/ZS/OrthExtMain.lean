module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtCorank
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtFrame
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSevenCases
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem finite_subgroup [Module.Finite (ZMod p) U]
    (X : Subgroup (U ≃ₗ[ZMod p] U)) : Finite X := by
  have hU : Finite U := Module.finite_of_finite (ZMod p)
  have hFun : Finite (U → U) := inferInstance
  have hEq : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) LinearEquiv.coe_injective
  exact Finite.of_injective (Subtype.val : X → U ≃ₗ[ZMod p] U) Subtype.val_injective

private theorem ofEq_conj_mem_movedGroup {H X : Subgroup (U ≃ₗ[ZMod p] U)} (hHX : H ≤ X)
    (hV : HardMathSupport.Kantor79.commutatorSpace H =
      HardMathSupport.Kantor79.commutatorSpace X)
    {g : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H} (hg : g ∈ movedGroup H) :
    (LinearEquiv.ofEq _ _ hV).symm.trans (g.trans (LinearEquiv.ofEq _ _ hV)) ∈
      movedGroup X := by
  obtain ⟨h, hgh⟩ := MonoidHom.mem_range.mp hg
  rw [← hgh]
  refine MonoidHom.mem_range.mpr ⟨⟨h.1, hHX h.2⟩, ?_⟩
  ext w
  simp [LinearEquiv.trans_apply, restrictHom_apply]

private theorem not_isImprimitiveOnV_of_le_of_commutatorSpace_eq
    {H X : Subgroup (U ≃ₗ[ZMod p] U)} (hHX : H ≤ X)
    (hV : HardMathSupport.Kantor79.commutatorSpace H =
      HardMathSupport.Kantor79.commutatorSpace X)
    (h : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup H)) :
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) := by
  intro himp
  apply h
  obtain ⟨r, W, hr, hne, hind, hsup, hperm⟩ := himp
  let e : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X := LinearEquiv.ofEq _ _ hV
  refine ⟨r, fun i => (W i).map (e.symm : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
    HardMathSupport.Kantor79.commutatorSpace H), hr, ?_, ?_, ?_, ?_⟩
  · intro i hbot
    exact hne i ((Submodule.map_eq_bot_iff).mp hbot)
  · exact LinearMap.iSupIndep_map (e.symm : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H) e.symm.injective hind
  · have hsup' : (⨆ i, (W i).map (e.symm : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace H))
        = (⨆ i, W i).map (e.symm : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H) := by
      rw [Submodule.map_iSup]
    rw [hsup', hsup, Submodule.map_top, LinearMap.range_eq_top.mpr e.symm.surjective]
  · intro g hg i
    obtain ⟨j, hj⟩ := hperm _ (ofEq_conj_mem_movedGroup hHX hV hg) i
    refine ⟨j, ?_⟩
    have hcomp : ((g : HardMathSupport.Kantor79.commutatorSpace H →ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H).comp
          (e.symm : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
            HardMathSupport.Kantor79.commutatorSpace H))
        = (e.symm : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
            HardMathSupport.Kantor79.commutatorSpace H).comp
          ((e.symm.trans (g.trans e) : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
            HardMathSupport.Kantor79.commutatorSpace X) : HardMathSupport.Kantor79.commutatorSpace X
              →ₗ[ZMod p] HardMathSupport.Kantor79.commutatorSpace X) := by
      ext x
      simp [LinearEquiv.trans_apply]
    rw [← Submodule.map_comp, hcomp, Submodule.map_comp, hj]

theorem eq_of_le_of_splitSupport [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) (hT1 : TFOrthOvergroup p (Module.finrank (ZMod p) U - 1))
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hXG : X ≤ G) (hHX : H ≤ X) (hX : ReflGen p X)
    (hXs : SplitSupport X (Module.finrank (ZMod p) U - 1)) : X = H := by
  have hH := hS.sub
  have hV : HardMathSupport.Kantor79.commutatorSpace H =
      HardMathSupport.Kantor79.commutatorSpace X :=
    Submodule.eq_of_le_of_finrank_eq (HardMathSupport.Kantor79.commutatorSpace_mono hHX)
      (by rw [hH.2.1.2.1, hXs.2.1])
  have hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) :=
    not_isImprimitiveOnV_of_le_of_commutatorSpace_eq hHX hV hH.2.2.1
  have hdX : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hx', hy', hxy⟩ := hH.2.2.2.2
    exact ⟨x, hHX hx, y, hHX hy, hx', hy', hxy⟩
  have horth : IsOrthType p (movedGroup X) :=
    hT1 U X H hHX hX (fun g hg => hS.rGroup.2 g (hXG hg)) hXs hH.1 hH.2.1 hH.2.2.2.1
      hH.2.2.1 hH.2.2.2.2
  have hcard : Nat.card X ≤ Nat.card H :=
    hS.maxCard X hXG ⟨hX, hXs, hprim, horth, hdX⟩
  have hfinX : Finite X := finite_subgroup X
  exact (Subgroup.eq_of_le_of_card_ge hHX hcard).symm

theorem mem_of_movedSpace_le_commutatorSpace (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hT1 : TFOrthOvergroup p (Module.finrank (ZMod p) U - 1)) {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G)
    (hb' : IsRefl p b)
    (hbH : HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H) :
    b ∈ H :=
  mem_of_movedSpace_le_of_maximal hp hS.four_le htab hS.rGroup.2 hS.le hS.sub.1 hS.sub.2.1
    hS.sub.2.2.2.2
    (fun K hKG hHK hK hKs => eq_of_le_of_splitSupport (X := K) hS hT1 hKG hHK hK hKs)
    hb hb' hbH

theorem exists_lemmaTwoSevenData (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hT1 : TFOrthOvergroup p (Module.finrank (ZMod p) U - 1)) :
    ∃ (B : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U), LemmaTwoSevenData p G H B h := by
  have hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H →
      b ∈ H := fun b hb hb' hbH => mem_of_movedSpace_le_commutatorSpace hp hS htab hT1 hb hb' hbH
  have hirr : ∀ b ∈ G, IsRefl p b →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H →
      IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤ :=
    fun b hb hb' hbH hbH' =>
      irredOnSection_closure_insert_of_not_le hp hS.four_le htab hS.rGroup.2 hS.le hS.sub.1
        hS.sub.2.1 hS.sub.2.2.2.2 hb hb' hbH hbH'
  obtain ⟨z, hF, hCD⟩ := exists_lemmaTwoThreeFrame_of_isOrthType hp hS.four_le
    hS.five_le_of_eq_three hS.le hS.rGroup.2 hS.sub.1 hS.sub.2.1 hS.sub.2.2.2.1 hmem hirr
  have hCD' : (∃ τ ∈ (Set.univ : Set (U ≃ₗ[ZMod p] U)), IsCaseCRefl p H z τ) ∨
      ∃ τ h', IsCaseDPair p H z τ h' := by
    rcases hCD with ⟨τ, hτ⟩ | hD
    · exact Or.inl ⟨τ, Set.mem_univ τ, hτ⟩
    · exact Or.inr hD
  obtain ⟨h, hh, hh', B, hB⟩ :=
    exists_isCentralizingSplit hp hF hCD' hS.rGroup.1 hS.irred (fun h hh hh' => by
      have h4 := hS.four_le
      have h3 : 3 ≤ Module.finrank (ZMod p) U - 1 := by omega
      have hstep := (tfOrthStabilizer (p := p) hp (m := Module.finrank (ZMod p) U - 1)) h3
      have hdimU : Module.finrank (ZMod p) U = (Module.finrank (ZMod p) U - 1) + 1 := by omega
      have hstab := hstep U hdimU H hS.sub.1 hS.sub.2.1 hS.sub.2.2.2.1 hS.sub.2.2.1
        hS.sub.2.2.2.2 h hh hh'
      rcases hstab with ⟨hdim, hirr, _⟩ | ⟨hm, _, r, e, s, hr, hT⟩
      · exact Or.inl ⟨by omega, hirr⟩
      · exact Or.inr ⟨by omega, r, e, s, hr, hT⟩)
  exact ⟨B, h, ⟨hS, hmem, hh, hh', hB⟩⟩

private theorem centralizerSpace_eq_span_of_splitSupport [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {e : U} (he : e ∈ centralizerSpace H) (he0 : e ≠ 0) :
    centralizerSpace H = Submodule.span (ZMod p) {e} := by
  refine eq_span_singleton_of_mem_of_finrank_eq_one ?_ he he0
  rw [hs.finrank_centralizerSpace]
  omega

private theorem exists_eq_add_smul_of_splitSupport [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {e : U}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hspan : centralizerSpace H = Submodule.span (ZMod p) {e}) (x : U) :
    ∃ y ∈ HardMathSupport.Kantor79.commutatorSpace H, ∃ c : ZMod p, x = y + c • e := by
  have hx : x ∈ HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H := by
    rw [hs.1.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [hspan] at hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨y, hy, c, by rw [hc]⟩

private theorem Q_ne_zero_of_mem_centralizerSpace [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hiso : ∀ g ∈ H, IsIsom p Q g)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {e : U} (he : e ∈ centralizerSpace H) (he0 : e ≠ 0) :
    Q e ≠ 0 := by
  intro hQe
  refine he0 (CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hQ fun x => ?_)
  obtain ⟨y, hy, c, rfl⟩ :=
    exists_eq_add_smul_of_splitSupport hs (centralizerSpace_eq_span_of_splitSupport hs h4 he he0) x
  rw [QuadraticMap.polar_add_right, polar_eq_zero_of_mem_centralizerSpace hiso he hy,
    QuadraticMap.polar_smul_right]
  simp [hQe]

private theorem ker_polarBilin_le_commutatorSpace [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hiso : ∀ g ∈ H, IsIsom p Q g)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {e : U} (he : e ∈ centralizerSpace H)
    (hQe : Q e ≠ 0) :
    LinearMap.ker (QuadraticMap.polarBilin Q e) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact QuadraticMap.map_zero Q)
  intro x hx
  refine (mem_commutatorSpace_iff_forall_polar_eq_zero hQ hiso hs.1).mpr fun u hu => ?_
  rw [centralizerSpace_eq_span_of_splitSupport hs h4 he he0] at hu
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  rw [← hc, QuadraticMap.polar_smul_left, smul_eq_mul,
    show QuadraticMap.polar Q e x = 0 from by simpa using LinearMap.mem_ker.mp hx, mul_zero]

private theorem exists_mem_inv_apply_mem_of_polar_eq_zero [Module.Finite (ZMod p) U]
    (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hK : (∀ g, g ∈ K ↔ IsIsom p Q g) ∨ ((p = 3 → 5 ≤ Module.finrank (ZMod p) U) ∧
      ∃ c : ZMod p, c ≠ 0 ∧ K = Subgroup.closure (ClassRefl p Q c)))
    (hiso : ∀ k ∈ K, IsIsom p Q k) {H : Subgroup (U ≃ₗ[ZMod p] U)} {e u v : U}
    (he : Q e ≠ 0) (hu : Q u = Q e) (huv : QuadraticMap.polar Q u v = 0)
    (hker : LinearMap.ker (QuadraticMap.polarBilin Q e) ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    ∃ k ∈ K, k⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  obtain ⟨k, hk, hke⟩ := exists_mem_apply_eq_of_isIsom hp (by omega) hQ hK he hu
  refine ⟨k, hk, hker ?_⟩
  have hpolar : QuadraticMap.polar Q e (k⁻¹ v) = QuadraticMap.polar Q u v := by
    rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hiso k hk)) e (k⁻¹ v), hke]
    simp
  rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply, hpolar, huv]

theorem exists_map_eq_polar_eq_zero_of_anisotropic [Module.Finite (ZMod p) U]
    (h2 : (2 : ZMod p) ≠ 0) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {v : U} (hQv : Q v ≠ 0) (c : ZMod p) :
    ∃ u : U, Q u = c ∧ QuadraticMap.polar Q u v = 0 := by
  have hS : ClassicalGroups.Orthogonal.PolarNondegOn Q
      ((⊤ : Submodule (ZMod p) U) ⊓ LinearMap.ker (QuadraticMap.polarBilin Q v)) :=
    (CFSG.ClassicalGroups.Orthogonal.polarNondegOn_top hQ).inf_ker h2 Submodule.mem_top hQv
  have hdim : 2 ≤ Module.finrank (ZMod p) ↥((⊤ : Submodule (ZMod p) U) ⊓
      LinearMap.ker (QuadraticMap.polarBilin Q v)) := by
    have hA := CFSG.ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one (Q := Q) h2
      (S := (⊤ : Submodule (ZMod p) U)) (u := v) Submodule.mem_top hQv
    rw [finrank_top] at hA
    omega
  obtain ⟨u, hu, hQu⟩ := hS.exists_map_eq h2 hdim c
  exact ⟨u, hQu, by
    rw [QuadraticMap.polar_comm]
    simpa using LinearMap.mem_ker.mp hu.2⟩

private theorem exists_hyperbolic_pair_of_singular
    (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {v : U} (hv : v ≠ 0) (hQv : Q v = 0) :
    ∃ a₁ a₂ : U, Q a₁ = 1 ∧ Q a₂ ≠ 0 ∧ QuadraticMap.polar Q a₁ a₂ = 0 ∧
      v = a₂ + (2 : ZMod p)⁻¹ • a₁ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨w, hw⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hQ hv
  obtain ⟨w', hpw⟩ : ∃ w' : U, QuadraticMap.polar Q v w' = 1 := by
    refine ⟨(QuadraticMap.polar Q v w)⁻¹ • w, ?_⟩
    rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw]
  have hpw' : QuadraticMap.polar Q w' v = 1 := by
    rw [QuadraticMap.polar_comm]
    exact hpw
  obtain ⟨a₁, ha₁, hQa1⟩ : ∃ a₁ : U, a₁ = w' + (1 - Q w') • v ∧ Q a₁ = 1 := by
    refine ⟨w' + (1 - Q w') • v, rfl, ?_⟩
    rw [QuadraticMap.map_add Q, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      QuadraticMap.polar_smul_right, smul_eq_mul, hQv, mul_zero, add_zero, hpw', mul_one]
    ring
  have hva : QuadraticMap.polar Q v a₁ = 1 := by
    rw [ha₁, QuadraticMap.polar_add_right, hpw, QuadraticMap.polar_smul_right, smul_eq_mul,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hQv, mul_zero, mul_zero, add_zero]
  have hva' : QuadraticMap.polar Q a₁ v = 1 := by
    rw [QuadraticMap.polar_comm]
    exact hva
  have h4ne : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hQa1ne : Q a₁ ≠ 0 := by rw [hQa1]; exact one_ne_zero
  obtain ⟨a₂, ha₂, hQa2⟩ :
      ∃ a₂ : U, a₂ = v - (2 : ZMod p)⁻¹ • a₁ ∧ Q a₂ = -((4 : ZMod p)⁻¹) := by
    refine ⟨v - (2 : ZMod p)⁻¹ • a₁, rfl, ?_⟩
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hQa1, QuadraticMap.polar_smul_right,
      smul_eq_mul, hva, mul_one, hQv, zero_add]
    field_simp
    ring
  have hQa2ne : Q a₂ ≠ 0 := by
    rw [hQa2]
    exact neg_ne_zero.mpr (inv_ne_zero h4ne)
  have hpa : QuadraticMap.polar Q a₁ a₂ = 0 := by
    rw [ha₂, sub_eq_add_neg, ← neg_smul, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, smul_eq_mul, hva',
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hQa1, mul_one]
    field_simp
    ring
  exact ⟨a₁, a₂, hQa1, hQa2ne, hpa, by rw [ha₂, sub_add_cancel]⟩

private theorem exists_map_eq_polar_eq_zero_of_singular [Module.Finite (ZMod p) U]
    (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {v : U} (hv : v ≠ 0) (hQv : Q v = 0) (c : ZMod p) :
    ∃ u : U, Q u = c ∧ QuadraticMap.polar Q u v = 0 := by
  obtain ⟨a₁, a₂, hQa1, hQa2ne, hpa, hv'⟩ := exists_hyperbolic_pair_of_singular hp hQ hv hQv
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hQa1ne : Q a₁ ≠ 0 := by rw [hQa1]; exact one_ne_zero
  have hS₁ : ClassicalGroups.Orthogonal.PolarNondegOn Q
      ((⊤ : Submodule (ZMod p) U) ⊓ LinearMap.ker (QuadraticMap.polarBilin Q a₁)) :=
    (CFSG.ClassicalGroups.Orthogonal.polarNondegOn_top hQ).inf_ker h2 Submodule.mem_top hQa1ne
  have ha₂S₁ : a₂ ∈ (⊤ : Submodule (ZMod p) U) ⊓
      LinearMap.ker (QuadraticMap.polarBilin Q a₁) :=
    ⟨Submodule.mem_top, by simpa [QuadraticMap.polarBilin_apply_apply] using hpa⟩
  have hS : ClassicalGroups.Orthogonal.PolarNondegOn Q
      (((⊤ : Submodule (ZMod p) U) ⊓ LinearMap.ker (QuadraticMap.polarBilin Q a₁)) ⊓
        LinearMap.ker (QuadraticMap.polarBilin Q a₂)) :=
    hS₁.inf_ker h2 ha₂S₁ hQa2ne
  have hdim : 2 ≤ Module.finrank (ZMod p) ↥(((⊤ : Submodule (ZMod p) U) ⊓
      LinearMap.ker (QuadraticMap.polarBilin Q a₁)) ⊓
        LinearMap.ker (QuadraticMap.polarBilin Q a₂)) := by
    have hA := CFSG.ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one (Q := Q) h2
      (S := (⊤ : Submodule (ZMod p) U)) (u := a₁) Submodule.mem_top hQa1ne
    have hB := CFSG.ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one (Q := Q) h2
      (S := (⊤ : Submodule (ZMod p) U) ⊓ LinearMap.ker (QuadraticMap.polarBilin Q a₁))
      (u := a₂) ha₂S₁ hQa2ne
    rw [finrank_top] at hA
    omega
  obtain ⟨u, hu, hQu⟩ := hS.exists_map_eq h2 hdim c
  have hpa₁ : QuadraticMap.polar Q u a₁ = 0 := by
    rw [QuadraticMap.polar_comm]
    simpa using LinearMap.mem_ker.mp hu.1.2
  have hpa₂ : QuadraticMap.polar Q u a₂ = 0 := by
    rw [QuadraticMap.polar_comm]
    simpa using LinearMap.mem_ker.mp hu.2
  refine ⟨u, hQu, ?_⟩
  rw [hv', QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, smul_eq_mul, hpa₂,
    hpa₁, mul_zero, zero_add]

theorem exists_mem_inv_apply_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hK : (∀ g, g ∈ K ↔ IsIsom p Q g) ∨ ((p = 3 → 5 ≤ Module.finrank (ZMod p) U) ∧
      ∃ c : ZMod p, c ≠ 0 ∧ K = Subgroup.closure (ClassRefl p Q c)))
    (hHK : H ≤ K) (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) (v : U) :
    ∃ k ∈ K, k⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  obtain ⟨e, he, he0⟩ :=
    hs.exists_mem_centralizerSpace_ne_zero (l := Module.finrank (ZMod p) U - 1) (by omega)
  have hisoK : ∀ k ∈ K, IsIsom p Q k := by
    intro k hk
    rcases hK with hfull | ⟨_, c, hc, hKc⟩
    · exact (hfull k).mp hk
    · exact isIsom_of_mem_closure_classRefl (by rwa [hKc] at hk)
  have hisoH : ∀ g ∈ H, IsIsom p Q g := fun g hg => hisoK g (hHK hg)
  have hQe : Q e ≠ 0 := Q_ne_zero_of_mem_centralizerSpace hQ hisoH hs h4 he he0
  have hker := ker_polarBilin_le_commutatorSpace hQ hisoH hs h4 he hQe
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨1, K.one_mem, by simp⟩
  rcases eq_or_ne (Q v) 0 with hQv | hQv
  · obtain ⟨u, hQu, huv⟩ := exists_map_eq_polar_eq_zero_of_singular hp hQ h4 hv hQv (Q e)
    exact exists_mem_inv_apply_mem_of_polar_eq_zero hp h4 hQ hK hisoK hQe hQu huv hker
  · obtain ⟨u, hQu, huv⟩ :=
      exists_map_eq_polar_eq_zero_of_anisotropic h2 hQ (by omega) hQv (Q e)
    exact exists_mem_inv_apply_mem_of_polar_eq_zero hp h4 hQ hK hisoK hQe hQu huv hker

theorem eq_of_isOrthOvergroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (hG : ReflGen p G) (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H)
    {K : Subgroup (U ≃ₗ[ZMod p] U)} (hK : IsOrthOvergroup p G H K)
    (h43 : (p = 3 → 5 ≤ Module.finrank (ZMod p) U) ∨ ∃ Q : QuadraticForm (ZMod p) U,
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ ∀ g, g ∈ K ↔ IsIsom p Q g) : G = K := by
  have hKG : K ≤ G := hK.1
  have hHK : H ≤ K := hK.2.1
  obtain ⟨Q, hQ, hK'⟩ : ∃ Q : QuadraticForm (ZMod p) U,
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      ((∀ g, g ∈ K ↔ IsIsom p Q g) ∨ ((p = 3 → 5 ≤ Module.finrank (ZMod p) U) ∧
        ∃ c : ZMod p, c ≠ 0 ∧ K = Subgroup.closure (ClassRefl p Q c))) := by
    rcases h43 with h43' | ⟨Q', hQ', hKQ'⟩
    · obtain ⟨Q, hQ, hKQ⟩ := hK.2.2.2.2
      rcases hKQ with hfull | ⟨c, hc, hKc⟩
      · exact ⟨Q, hQ, Or.inl hfull⟩
      · exact ⟨Q, hQ, Or.inr ⟨h43', c, hc, hKc⟩⟩
    · exact ⟨Q', hQ', Or.inl hKQ'⟩
  refine le_antisymm ?_ hKG
  rw [hG]
  refine (Subgroup.closure_le _).mpr ?_
  rintro a ⟨haG, ha⟩
  have hne : HardMathSupport.Kantor79.movedSpace a ≠ ⊥ := by
    intro hbot
    have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace a) = 1 := ha.2
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : HardMathSupport.Kantor79.movedSpace a = Submodule.span (ZMod p) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one ha.2 hvV hv0
  obtain ⟨k, hkK, hkv⟩ := exists_mem_inv_apply_mem hp h4 hQ hK' hHK hs v
  have hkG : k ∈ G := hKG hkK
  have hconjG : k⁻¹ * a * k ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hkG) haG) hkG
  have hconjRefl : IsRefl p (k⁻¹ * a * k) := by
    simpa using IsRefl.conj ha k⁻¹
  have hmoved : HardMathSupport.Kantor79.movedSpace (k⁻¹ * a * k) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [show k⁻¹ * a * k = k⁻¹ * a * (k⁻¹)⁻¹ by simp, movedSpace_conj]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hy :
      y ∈ Submodule.span (ZMod p) {v})
    rw [← hc, map_smul]
    exact Submodule.smul_mem _ c hkv
  have hconjH : k⁻¹ * a * k ∈ H := hmem _ hconjG hconjRefl hmoved
  rw [show a = k * (k⁻¹ * a * k) * k⁻¹ by group]
  exact K.mul_mem (K.mul_mem hkK (hHK hconjH)) (K.inv_mem hkK)

theorem isOrthType_of_orthExtSetting (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hT1 : TFOrthOvergroup p (Module.finrank (ZMod p) U - 1))
    (hT4 : TFOrthCorankOne p (Module.finrank (ZMod p) U - 1)) (hT5 : TFDegThree p) :
    IsOrthType p G := by
  obtain ⟨B, h, hD⟩ := exists_lemmaTwoSevenData hp hS htab hT1
  obtain ⟨K, hK⟩ := exists_isOrthOvergroup hp hD hT4 hT5
  have hGK : G = K :=
    eq_of_isOrthOvergroup hp hS.four_le hS.rGroup.1 hS.sub.2.1 hD.mem_of_le hK
      (Or.inl hS.five_le_of_eq_three)
  rw [hGK]
  exact hK.2.2.2.2

theorem isOrthType_of_orthType_subgroup (hp : p ≠ 2) [Module.Finite (ZMod p) U] {n : ℕ}
    (hn : Module.finrank (ZMod p) U = n) (h4 : 4 ≤ n) (hG : IsRGroup p G) (hirr : AbsIrred p G)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) (hHG : H ≤ G) (hH : IsPrimOrthSub p H)
    (hmax : ∀ X : Subgroup (U ≃ₗ[ZMod p] U), X ≤ G → IsPrimOrthSub p X →
      Nat.card X ≤ Nat.card H)
    (htab : TFNegOrGen p (n - 1)) (hT1 : TFOrthOvergroup p (n - 1))
    (hT4 : TFOrthCorankOne p (n - 1)) (hT5 : TFDegThree p) : IsOrthType p G := by
  subst n
  have h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U := by
    intro hp3
    by_contra h5
    have hfin : Module.finrank (ZMod p) U = 4 := by omega
    have hs3 : SplitSupport H 3 := by simpa [hfin] using hH.2.1
    exact hH.2.2.1 (tfOrthThreeThree hp3 U H hs3 hH.2.2.2.1)
  have hirred : IrredOnSection G ⊥ ⊤ := fun X _ _ hX => hirr.1 X hX
  exact isOrthType_of_orthExtSetting hp
    ⟨h4, h43, hG, hirred, hprim, hHG, hH, hmax⟩ htab hT1 hT4 hT5

end CFSG.StandardType.ZS

end
