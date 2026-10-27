module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndLift
import CFSG.RankThree.SubgroupLists.SymplecticReducible
public import Certificates.Certificate43
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Subgroup CFSG.RankThree.SubgroupLists
open scoped Matrix

theorem glLeTwoRep_normal_two_odd {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {G : Type*} [Group G]
    [Finite G] [Group.IsPerfect G] {k : ℕ} (hk : k ≤ 2) (ρ : G →* GL (Fin k) (ZMod p))
    {N : Subgroup G} (hN : N.Normal) :
    (IsPGroup 2 N → ∀ n ∈ N, ∀ g, ρ (g * n) = ρ (n * g)) ∧
      (Odd (Nat.card N) → ∀ n ∈ N, ρ n = 1) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact ⟨fun _ _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  · have : Group.IsSolvable (GL (Fin 1) (ZMod p)) := Group.isSolvable_of_comm gl_fin_one_comm
    have h1 : ∀ g, ρ g = 1 := map_eq_one_of_isPerfect ρ
    exact ⟨fun _ n _ g => by rw [h1, h1], fun _ n _ => h1 n⟩
  · exact gl2Rep_normal_two_odd hp5 ρ hN

theorem normal_of_le_two_reps {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {G : Type*} [Group G]
    [Finite G] [Group.IsPerfect G] {ι : Type*} {k : ι → ℕ} (hk : ∀ i, k i ≤ 2)
    (ρ : ∀ i, G →* GL (Fin (k i)) (ZMod p)) (hjoint : ∀ g, (∀ i, ρ i g = 1) → g = 1) :
    (∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ center G) ∧
      (∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) := by
  refine ⟨fun N hN h2N n hn => mem_center_iff.mpr fun g => ?_, fun N hN hodd => ?_⟩
  · refine mul_inv_eq_one.mp (hjoint _ fun i => ?_)
    rw [map_mul, map_inv, (glLeTwoRep_normal_two_odd hp5 (hk i) (ρ i) hN).1 h2N n hn g,
      mul_inv_cancel]
  · refine eq_bot_iff.mpr fun n hn => mem_bot.mpr ?_
    exact hjoint n fun i => (glLeTwoRep_normal_two_odd hp5 (hk i) (ρ i) hN).2 hodd n hn

@[expose] def sgn {R : Type*} [Ring R] : Fin 2 → R := ![1, -1]

theorem normal_of_commute_klein {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {d : ℕ}
    {H : Subgroup (GL (Fin d) (ZMod p))} (hH : Group.IsPerfect H)
    {T₁ T₂ : GL (Fin d) (ZMod p)} (h₁ : T₁ * T₁ = 1) (h₂ : T₂ * T₂ = 1) (h₁₂ : T₁ * T₂ = T₂ * T₁)
    (hf₁ : Module.finrank (ZMod p)
      (Module.End.eigenspace (Matrix.toLin' (T₁ : Matrix (Fin d) (Fin d) (ZMod p))) 1) ≤ 2)
    (hf₂ : Module.finrank (ZMod p)
      (Module.End.eigenspace (Matrix.toLin' (T₂ : Matrix (Fin d) (Fin d) (ZMod p))) 1) ≤ 2)
    (hf₁₂ : Module.finrank (ZMod p) (Module.End.eigenspace
      (Matrix.toLin' ((T₁ * T₂ : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p))) 1) ≤ 2)
    (hT₁ : ∀ g ∈ H, g * T₁ = T₁ * g) (hT₂ : ∀ g ∈ H, g * T₂ = T₂ * g) :
    (∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N ≤ center H) ∧
      (∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N = ⊥) := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h := (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    exact_mod_cast h
  set a₁ : Module.End (ZMod p) (Fin d → ZMod p) :=
    Matrix.toLin' (T₁ : Matrix (Fin d) (Fin d) (ZMod p)) with ha₁
  set a₂ : Module.End (ZMod p) (Fin d → ZMod p) :=
    Matrix.toLin' (T₂ : Matrix (Fin d) (Fin d) (ZMod p)) with ha₂
  have hmat : ∀ {A B : GL (Fin d) (ZMod p)}, A * B = 1 →
      ∀ v, Matrix.toLin' (A : Matrix (Fin d) (Fin d) (ZMod p))
        (Matrix.toLin' (B : Matrix (Fin d) (Fin d) (ZMod p)) v) = v := by
    intro A B hAB v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hAB,
      Units.val_one, Matrix.one_mulVec]
  have ha₁a₁ : ∀ v, a₁ (a₁ v) = v := hmat h₁
  have ha₂a₂ : ∀ v, a₂ (a₂ v) = v := hmat h₂
  have ha₁₂ : ∀ v, a₁ (a₂ v) = a₂ (a₁ v) := by
    intro v
    rw [ha₁, ha₂, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
      ← Units.val_mul, h₁₂]
  let W : Fin 2 × Fin 2 → Submodule (ZMod p) (Fin d → ZMod p) := fun i =>
    Module.End.eigenspace a₁ (sgn i.1) ⊓ Module.End.eigenspace a₂ (sgn i.2)
  have hW : ∀ i, SubgroupLists.IsInvariant H (W i) := by
    rintro i g hg v ⟨hv₁, hv₂⟩
    have hc : ∀ {T : GL (Fin d) (ZMod p)}, g * T = T * g → ∀ μ : ZMod p,
        v ∈ Module.End.eigenspace (Matrix.toLin' (T : Matrix (Fin d) (Fin d) (ZMod p))) μ →
        (g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ v ∈
          Module.End.eigenspace (Matrix.toLin' (T : Matrix (Fin d) (Fin d) (ZMod p))) μ := by
      intro T hgT μ hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      have hgT' : (g : Matrix (Fin d) (Fin d) (ZMod p)) * T = T * g := by
        rw [← Units.val_mul, ← Units.val_mul, hgT]
      rw [Matrix.mulVec_mulVec, ← hgT', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
    exact ⟨hc (hT₁ g hg) _ hv₁, hc (hT₂ g hg) _ hv₂⟩
  have hdim : ∀ i, Module.finrank (ZMod p) (W i) ≤ 2 := by
    rintro ⟨j, k⟩
    fin_cases j <;> fin_cases k
    · exact (Submodule.finrank_mono inf_le_left).trans hf₁
    · exact (Submodule.finrank_mono inf_le_left).trans hf₁
    · exact (Submodule.finrank_mono inf_le_right).trans hf₂
    · refine (Submodule.finrank_mono ?_).trans hf₁₂
      rintro v ⟨hv₁, hv₂⟩
      have e₁ : a₁ v = (-1 : ZMod p) • v := Module.End.mem_eigenspace_iff.mp hv₁
      have e₂ : a₂ v = (-1 : ZMod p) • v := Module.End.mem_eigenspace_iff.mp hv₂
      rw [Module.End.mem_eigenspace_iff, Units.val_mul, Matrix.toLin'_mul,
        LinearMap.comp_apply, ← ha₂, e₂, map_smul, ← ha₁, e₁, smul_smul]
      norm_num
  have hspan : ∀ v, v ∈ ⨆ i, W i := by
    intro v
    have hdec : ∀ (T : Module.End (ZMod p) (Fin d → ZMod p)), (∀ v, T (T v) = v) →
        ∀ v, ∃ vp ∈ Module.End.eigenspace T 1, ∃ vm ∈ Module.End.eigenspace T (-1),
          v = vp + vm := by
      intro T hT v
      refine ⟨(2 : ZMod p)⁻¹ • (v + T v), ?_, (2 : ZMod p)⁻¹ • (v - T v), ?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, hT, one_smul, add_comm]
      · rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, hT, neg_one_smul, ← smul_neg,
          neg_sub]
      · rw [← smul_add, show v + T v + (v - T v) = (2 : ZMod p) • v by
          rw [two_smul]; abel, smul_smul, inv_mul_cancel₀ h2, one_smul]
    obtain ⟨u, hu, u', hu', rfl⟩ := hdec a₁ ha₁a₁ v
    have hpres : ∀ μ : ZMod p, ∀ x ∈ Module.End.eigenspace a₁ μ,
        a₂ x ∈ Module.End.eigenspace a₁ μ := by
      intro μ x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [ha₁₂, hx, map_smul]
    have hpart : ∀ (j : Fin 2) (x : Fin d → ZMod p), x ∈ Module.End.eigenspace a₁ (sgn j) →
        x ∈ ⨆ i, W i := by
      intro j x hx
      obtain ⟨xp, hxp, xm, hxm, rfl⟩ := hdec a₂ ha₂a₂ x
      have hxp' : xp ∈ Module.End.eigenspace a₁ (sgn j) := by
        have : xp = (2 : ZMod p)⁻¹ • ((xp + xm) + a₂ (xp + xm)) := by
          rw [Module.End.mem_eigenspace_iff] at hxp hxm
          rw [map_add, hxp, hxm, one_smul, neg_one_smul, show xp + xm + (xp + -xm) =
            (2 : ZMod p) • xp by rw [two_smul]; abel, smul_smul, inv_mul_cancel₀ h2, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (add_mem hx (hpres _ _ hx))
      have hxm' : xm ∈ Module.End.eigenspace a₁ (sgn j) := by
        have : xm = (2 : ZMod p)⁻¹ • ((xp + xm) - a₂ (xp + xm)) := by
          rw [Module.End.mem_eigenspace_iff] at hxp hxm
          rw [map_add, hxp, hxm, one_smul, neg_one_smul, show xp + xm - (xp + -xm) =
            (2 : ZMod p) • xm by rw [two_smul]; abel, smul_smul, inv_mul_cancel₀ h2, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (sub_mem hx (hpres _ _ hx))
      refine add_mem (Submodule.mem_iSup_of_mem (j, 0) ⟨hxp', ?_⟩)
        (Submodule.mem_iSup_of_mem (j, 1) ⟨hxm', ?_⟩)
      · simpa [sgn] using hxp
      · simpa [sgn] using hxm
    exact add_mem (hpart 0 u (by simpa [sgn] using hu)) (hpart 1 u' (by simpa [sgn] using hu'))
  let b : ∀ i, Module.Basis (Fin (Module.finrank (ZMod p) (W i))) (ZMod p)
      ((W i) ⧸ (⊥ : Submodule (ZMod p) (Fin d → ZMod p)).comap (W i).subtype) := fun i =>
    Module.finBasisOfFinrankEq (ZMod p) _ (finrank_section_bot (W i))
  have hρ := fun i => sectionRep_bot_eq_one_iff H (hW i) (b i)
  refine normal_of_le_two_reps hp5 hdim (fun i => sectionRep H (isInvariant_bot H) (hW i) (b i))
    fun g hg => ?_
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hv := hspan v
  rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
  refine Submodule.iSup_induction W (motive := fun v =>
    (((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ v = v)) hv ?_ ?_ ?_
  · intro i w hw
    exact (hρ i g).mp (hg i) w hw
  · exact Matrix.mulVec_zero _
  · intro x y hx hy
    rw [Matrix.mulVec_add, hx, hy]

variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G] {p : ℕ} [Fact p.Prime]

theorem normal_two_le_center_of_central_four (hp5 : 5 ≤ p) {d : ℕ}
    {ρ : G →* GL (Fin d) (ZMod p)} (hρ : ∀ y, ρ y = 1 → y ∈ oddCore G)
    (hfix : ∀ t : G, orderOf t = 2 → Module.finrank (ZMod p) (Module.End.eigenspace
      (Matrix.toLin' (ρ t : Matrix (Fin d) (Fin d) (ZMod p))) 1) ≤ 2)
    {z₁ z₂ : G ⧸ oddCore G} (hz₁ : z₁ ∈ center (G ⧸ oddCore G))
    (hz₂ : z₂ ∈ center (G ⧸ oddCore G)) (hz₁1 : z₁ ≠ 1) (hz₂1 : z₂ ≠ 1) (h12 : z₁ ≠ z₂)
    (hz₁2 : z₁ * z₁ = 1) (hz₂2 : z₂ * z₂ = 1) (N : Subgroup (G ⧸ oddCore G)) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N ≤ center (G ⧸ oddCore G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (oddCore G) with hπ
  set Q := zpowers z₁ ⊔ zpowers z₂ with hQ
  have hQc : Q ≤ center (G ⧸ oddCore G) := sup_le (zpowers_le.mpr hz₁) (zpowers_le.mpr hz₂)
  have hQn : Q.Normal := normal_of_le_center hQc
  have hsq : ∀ {z : G ⧸ oddCore G}, z * z = 1 → ∀ x ∈ zpowers z, x * x = 1 := by
    intro z hz x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz, one_zpow]
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨x, hx⟩
    have : (zpowers z₂).Normal := normal_of_le_center (zpowers_le.mpr hz₂)
    obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    have hac : a * c = c * a := (mem_center_iff.mp (zpowers_le.mpr hz₂ hc) a)
    simp only [pow_one, OneMemClass.coe_one, sq]
    calc a * c * (a * c) = a * a * (c * c) := by
          rw [mul_assoc, ← mul_assoc c a c, ← hac]; group
      _ = 1 := by rw [hsq hz₁2 a ha, hsq hz₂2 c hc, one_mul]
  obtain ⟨R, hRQ, hRinj, -, hRN⟩ := exists_lift_two Q hQ2
  have hRN' := hRN hQn
  obtain ⟨w₁, hw₁, hπ₁⟩ : z₁ ∈ R.map π := by rw [hRQ]; exact mem_sup_left (mem_zpowers z₁)
  obtain ⟨w₂, hw₂, hπ₂⟩ : z₂ ∈ R.map π := by rw [hRQ]; exact mem_sup_right (mem_zpowers z₂)
  have hlift_eq : ∀ r ∈ R, ∀ r' ∈ R, π r = π r' → r = r' := fun r hr r' hr' h =>
    eq_of_mk_eq hRinj hr hr' h
  have hww₁ : w₁ * w₁ = 1 := hlift_eq _ (mul_mem hw₁ hw₁) _ (one_mem R) (by
    rw [map_mul, hπ₁, hz₁2, map_one])
  have hww₂ : w₂ * w₂ = 1 := hlift_eq _ (mul_mem hw₂ hw₂) _ (one_mem R) (by
    rw [map_mul, hπ₂, hz₂2, map_one])
  have hw₁₂ : w₁ * w₂ = w₂ * w₁ := hlift_eq _ (mul_mem hw₁ hw₂) _ (mul_mem hw₂ hw₁) (by
    rw [map_mul, map_mul, hπ₁, hπ₂, mem_center_iff.mp hz₂ z₁])
  have hord : ∀ {w : G} {z : G ⧸ oddCore G}, w * w = 1 → π w = z → z ≠ 1 → orderOf w = 2 :=
    fun hww hπw hz1 => orderOf_eq_prime (by rw [sq, hww])
      (fun h => hz1 (by rw [← hπw, h, map_one]))
  have hz12 : z₁ * z₂ ≠ 1 := by
    intro h
    apply h12
    calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, hz₂2, mul_one]
      _ = z₂ := by rw [h, one_mul]
  have hw12 : (w₁ * w₂) * (w₁ * w₂) = 1 := by
    calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * w₁ * (w₂ * w₂) := by rw [← hw₁₂]; group
      _ = 1 := by rw [hww₁, hww₂, one_mul]
  have hf₁ := hfix w₁ (hord hww₁ hπ₁ hz₁1)
  have hf₂ := hfix w₂ (hord hww₂ hπ₂ hz₂1)
  have hf₁₂ := hfix (w₁ * w₂) (hord hw12 (by rw [map_mul, hπ₁, hπ₂]) hz12)
  rw [map_mul] at hf₁₂
  have hcomm : ∀ {w : G}, w ∈ R → ∀ n ∈ normalizer (R : Set G), n * w = w * n := by
    intro w hw n hn
    have hmem : n * w * n⁻¹ ∈ R := (mem_normalizer_iff.mp hn w).mp hw
    have hcen : π w ∈ center (G ⧸ oddCore G) := hQc (hRQ ▸ mem_map_of_mem π hw)
    have h1 : n * w * n⁻¹ = w := hlift_eq _ hmem _ hw (by
      rw [map_mul, map_mul, map_inv, mem_center_iff.mp hcen (π n), mul_inv_cancel_right])
    calc n * w = n * w * n⁻¹ * n := by group
      _ = w * n := by rw [h1]
  set M := CFSG.Quasithin.perfectCore (normalizer (R : Set G)) with hMdef
  have hMp : Group.IsPerfect M :=
    Subgroup.isPerfect_iff.mpr (CFSG.Quasithin.perfectCore_perfect _)
  have hMmap : M.map π = ⊤ := by
    rw [hMdef, CFSG.Quasithin.map_perfectCore, hRN']
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect Subgroup.commutator_eq_self
  have hMle : M ≤ normalizer (R : Set G) := CFSG.Quasithin.perfectCore_le _
  have hHp : Group.IsPerfect (M.map ρ) := Group.IsPerfect.map ρ
  obtain ⟨h2, hodd⟩ := normal_of_commute_klein hp5 hHp
    (by rw [← map_mul, hww₁, map_one]) (by rw [← map_mul, hww₂, map_one])
    (by rw [← map_mul, ← map_mul, hw₁₂]) hf₁ hf₂ hf₁₂
    (by
      rintro _ ⟨m, hm, rfl⟩
      rw [← map_mul, ← map_mul, hcomm hw₁ m (hMle hm)])
    (by
      rintro _ ⟨m, hm, rfl⟩
      rw [← map_mul, ← map_mul, hcomm hw₂ m (hMle hm)])
  exact le_center_of_perfect_lift hρ hMmap h2 hodd N hN hN2

end CFSG.RankThree.PartTwo.Sec4.Census
