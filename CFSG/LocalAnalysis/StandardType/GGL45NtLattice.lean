module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Weyl
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.F4Regular
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.HardMathSupport.C14Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise

section Lattice

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private theorem lattice_exists_zpow_form {τ : Tag} {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) :
    ∃ (g : Kˣ) (f₀ : (Fin τ.rank → ℤ) →+ ℤ), g ^ p = 1 ∧ ∀ v, rootChar a v = g ^ f₀ v := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity p K)
  have hc : ∀ i, ∃ c : ℤ, (g : Kˣ) ^ c = a i := fun i => by
    obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨a i, (mem_rootsOfUnity p (a i)).2 (ha i)⟩)
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  choose c hc using hc
  refine ⟨g, AddMonoidHom.mk' (fun v => ∑ i, c i * v i) fun x y => by
      simp [mul_add, Finset.sum_add_distrib], (mem_rootsOfUnity p (g : Kˣ)).1 g.2, fun v => ?_⟩
  simp only [rootChar, AddMonoidHom.mk'_apply, ← hc, ← zpow_mul, prod_zpow_eq_zpow_sum]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private theorem lattice_exists_invariant_form_of_coprime {τ : Tag} {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) {w : WeylGroup τ} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hcop : Nat.Coprime (orderOf w) p) :
    ∃ f : (Fin τ.rank → ℤ) →+ ℤ, (∀ v, f (w • v) = f v) ∧ ∀ v, f v = 0 → rootChar a v = 1 := by
  obtain ⟨g, f₀, hgp, hχ⟩ := lattice_exists_zpow_form (K := K) hp ha
  set r := orderOf w
  set q := orderOf g
  have hqp : q ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hcop' : Nat.Coprime r q := Nat.Coprime.coprime_dvd_right hqp hcop
  obtain ⟨u, s, hus⟩ : IsCoprime (r : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop'
  refine ⟨AddMonoidHom.mk' (fun v => u * ∑ j ∈ Finset.range r, f₀ ((w ^ j) • v)) fun x y => by
      simp [smul_add, Finset.sum_add_distrib, mul_add], ?_, ?_⟩
  · intro v
    simp only [AddMonoidHom.mk'_apply]
    congr 1
    have e : ∀ j : ℕ, f₀ (w ^ j • w • v) = f₀ (w ^ (j + 1) • v) := fun j => by
      rw [← mul_smul, ← pow_succ]
    simp only [e]
    have h1 := Finset.sum_range_succ (fun j => f₀ (w ^ j • v)) r
    have h2 := Finset.sum_range_succ' (fun j => f₀ (w ^ j • v)) r
    have h3 : w ^ r = 1 := pow_orderOf_eq_one w
    simp only [h3, one_smul, pow_zero] at h1 h2
    linarith
  · intro v hv
    simp only [AddMonoidHom.mk'_apply] at hv
    have hwv : ∀ (j : ℕ) (x : Fin τ.rank → ℤ), rootChar a ((w ^ j) • x) = rootChar a x :=
      fun j x => (Subgroup.pow_mem _ hw j : w ^ j ∈ rootCharStabilizerSubgroup a) x
    have hdvd : ∀ j : ℕ, (q : ℤ) ∣ f₀ v - f₀ ((w ^ j) • v) := fun j => by
      have h := hwv j v
      rw [hχ, hχ] at h
      exact Int.modEq_iff_dvd.1 (zpow_eq_zpow_iff_modEq.1 h)
    set S := ∑ j ∈ Finset.range r, f₀ ((w ^ j) • v)
    have hD : (q : ℤ) ∣ (r : ℤ) * f₀ v - S := by
      have h : (q : ℤ) ∣ ∑ j ∈ Finset.range r, (f₀ v - f₀ ((w ^ j) • v)) :=
        Finset.dvd_sum fun j _ => hdvd j
      rwa [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hdv : (q : ℤ) ∣ f₀ v := by
      have e : f₀ v = u * ((r : ℤ) * f₀ v - S) + (q : ℤ) * (s * f₀ v) := by
        linear_combination (-(f₀ v)) * hus + hv
      rw [e]
      exact dvd_add (Dvd.dvd.mul_left hD u) (dvd_mul_right _ _)
    rw [hχ]
    exact orderOf_dvd_iff_zpow_eq_one.1 hdv


theorem eq_zero_of_fin_sum_digits (B : ℤ) (hB : 0 ≤ B) :
    ∀ (n : ℕ) (c : Fin n → ℤ), (∀ k, |c k| ≤ B) →
      ∑ k : Fin n, (2 * B + 1) ^ (k : ℕ) * c k = 0 → ∀ k, c k = 0 := by
  intro n
  induction n with
  | zero => intro c _ _ k; exact k.elim0
  | succ n ih =>
    intro c hc hsum
    rw [Fin.sum_univ_succ] at hsum
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ] at hsum
    set T := ∑ k : Fin n, (2 * B + 1) ^ (k : ℕ) * c k.succ with hT
    have hrest : ∑ k : Fin n, (2 * B + 1) ^ (k : ℕ) * (2 * B + 1) * c k.succ =
        (2 * B + 1) * T := by
      rw [hT, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hrest] at hsum
    have hdvd : (2 * B + 1) ∣ c 0 := ⟨-T, by linarith⟩
    have h0 : c 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (by linarith [hc 0])
    have hT0 : T = 0 := by
      rw [h0, zero_add] at hsum
      rcases mul_eq_zero.1 hsum with h | h
      · linarith
      · exact h
    have hs := ih (fun k => c k.succ) (fun k => hc _) hT0
    intro k
    refine Fin.cases h0 (fun k => hs k) k

def familyReflectionGroup {τ : Tag} {K : Type} [Field K] {ι : Type}
    (a : ι → Fin τ.rank → Kˣ) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {r | ∃ (w : WeylGroup τ) (i : Fin τ.rank),
    w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ familyKernel a ∧ r = w * simple τ i * w⁻¹}

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem mem_familyReflectionGroup_of_coprime {τ : Tag} {K : Type} [Field K] {ι : Type}
    [Finite ι] {p : ℕ} (hp : p.Prime)
    {a : ι → Fin τ.rank → Kˣ} (ha : ∀ i j, a i j ^ p = 1) {w : WeylGroup τ}
    (hw : w ∈ familyStabilizerSubgroup a) (hcop : Nat.Coprime (orderOf w) p) :
    w ∈ familyReflectionGroup a := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hwj : ∀ j, w ∈ rootCharStabilizerSubgroup (a j) := fun j =>
    (Subgroup.mem_iInf.1 hw) j
  choose f hfw hfker using fun j => lattice_exists_invariant_form_of_coprime hp (ha j) (hwj j) hcop
  haveI : Finite (WeylGroup τ) := (exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.1
  have hfin : {β : Fin τ.rank → ℤ | IsRoot τ β}.Finite :=
    (Set.finite_range (fun x : WeylGroup τ × Fin τ.rank =>
      x.1 • (Pi.single x.2 1 : Fin τ.rank → ℤ))).subset fun β hβ => by
        obtain ⟨u, i, hu⟩ := isRoot_iff_exists_smul_single.1 hβ
        exact ⟨(u, i), hu⟩
  set B : ℤ := ∑ β ∈ hfin.toFinset, ∑ j, |f j β| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB : ∀ β, IsRoot τ β → ∀ j, |f j β| ≤ B := fun β hβ j =>
    (Finset.single_le_sum (f := fun j => |f j β|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun β => ∑ j, |f j β|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        ((Set.Finite.mem_toFinset hfin).2 hβ))
  set e := Fintype.equivFin ι
  let F : (Fin τ.rank → ℤ) →+ ℤ := ∑ j, (2 * B + 1) ^ (e j : ℕ) • f j
  have hFapp : ∀ v, F v = ∑ j, (2 * B + 1) ^ (e j : ℕ) * f j v := fun v => by
    simp [F, AddMonoidHom.finset_sum_apply]
  have hF : ∀ v, F (w • v) = F v := fun v => by simp only [hFapp, hfw]
  refine (Subgroup.closure_le (familyReflectionGroup a)).2 ?_ (mem_stab_closure_of_invariant F hF)
  rintro _ ⟨u, i, hui, rfl⟩
  have hroot : IsRoot τ (u • (Pi.single i 1 : Fin τ.rank → ℤ)) := IsRoot.smul (isRoot_single τ i) u
  refine Subgroup.subset_closure ⟨u, i, ⟨hroot, fun j => hfker j _ ?_⟩, rfl⟩
  set β := u • (Pi.single i 1 : Fin τ.rank → ℤ)
  have hsum : ∑ k : Fin (Fintype.card ι), (2 * B + 1) ^ (k : ℕ) * f (e.symm k) β = 0 := by
    rw [← hui, hFapp]
    exact (Fintype.sum_equiv e _ _ fun j => by simp).symm
  have := eq_zero_of_fin_sum_digits B hB0 _ (fun k => f (e.symm k) β) (fun k => hB β hroot _) hsum (e j)
  simpa using this


def fixReflectionGroup {τ : Tag} (p : ℕ) (w : WeylGroup τ) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {r | ∃ (u : WeylGroup τ) (i : Fin τ.rank),
    (∀ f : (Fin τ.rank → ℤ) →+ ZMod p, (∀ v, f (w • v) = f v) →
      f (u • (Pi.single i 1 : Fin τ.rank → ℤ)) = 0) ∧ r = u * simple τ i * u⁻¹}

def SylowCert (τ : Tag) (p : ℕ) : Prop :=
  ¬ p ^ 2 ∣ Nat.card (WeylGroup τ) ∧
    ∃ w₀ : WeylGroup τ, orderOf w₀ = p ∧ w₀ ∈ fixReflectionGroup p w₀

theorem invariant_zpow {τ : Tag} {M : Type*} [AddCommMonoid M] (f : (Fin τ.rank → ℤ) →+ M)
    {y : WeylGroup τ} (hy : ∀ v, f (y • v) = f v) (n : ℤ) (v : Fin τ.rank → ℤ) :
    f ((y ^ n) • v) = f v := by
  induction n using Int.induction_on generalizing v with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, ih, hy]
  | pred n ih =>
    rw [zpow_sub_one, mul_smul, ih]
    have := hy (y⁻¹ • v)
    rw [smul_inv_smul] at this
    exact this.symm

theorem conj_mem_fixReflectionGroup {τ : Tag} {p : ℕ} {x x' : WeylGroup τ} (g : WeylGroup τ)
    (hx' : x' ∈ fixReflectionGroup p x) :
    g * x' * g⁻¹ ∈ fixReflectionGroup p (g * x * g⁻¹) := by
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨u, i, hu, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨g * u, i, fun f hf => ?_, by group⟩
    let f' : (Fin τ.rank → ℤ) →+ ZMod p :=
      AddMonoidHom.mk' (fun v => f (g • v)) fun v₁ v₂ => by rw [smul_add, map_add]
    have hf' : ∀ v, f' (x • v) = f' v := fun v => by
      simp only [f', AddMonoidHom.mk'_apply]
      have := hf (g • v)
      rwa [← mul_smul, show g * x * g⁻¹ * g = g * x by group, mul_smul] at this
    have := hu f' hf'
    simpa [f', mul_smul] using this
  | one => simpa using one_mem _
  | mul y z _ _ hy hz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]; exact mul_mem hy hz
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hy

theorem fixReflectionGroup_mono {τ : Tag} {p : ℕ} {x y : WeylGroup τ} (hxy : x ∈ Subgroup.zpowers y) :
    fixReflectionGroup p x ≤ fixReflectionGroup p y := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨u, i, hu, rfl⟩
  refine ⟨u, i, fun f hf => hu f fun v => ?_, rfl⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxy
  exact invariant_zpow f hf n v

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem fixReflectionGroup_le_family {τ : Tag} {K : Type} [Field K] {ι : Type}
    {p : ℕ} (hp : p.Prime) {a : ι → Fin τ.rank → Kˣ}
    (ha : ∀ i j, a i j ^ p = 1) {z : WeylGroup τ} (hz : z ∈ familyStabilizerSubgroup a) :
    fixReflectionGroup p z ≤ familyReflectionGroup a := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨u, i, hu, rfl⟩
  refine ⟨u, i, ⟨IsRoot.smul (isRoot_single τ i) u, fun j => ?_⟩, rfl⟩
  obtain ⟨g, f₀, hgp, hχ⟩ := lattice_exists_zpow_form (K := K) hp (ha j)
  have hzj : z ∈ rootCharStabilizerSubgroup (a j) := (Subgroup.mem_iInf.1 hz) j
  have hdvd : ∀ v, (orderOf g : ℤ) ∣ f₀ (z • v) - f₀ v := fun v => by
    have h := hzj v
    rw [hχ, hχ] at h
    exact Int.modEq_iff_dvd.1 (zpow_eq_zpow_iff_modEq.1 h).symm
  have hord : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rcases (Nat.dvd_prime hp).1 hord with h1 | hpord
  · rw [hχ, orderOf_eq_one_iff.1 h1, one_zpow]
  · let f : (Fin τ.rank → ℤ) →+ ZMod p := (Int.castAddHom (ZMod p)).comp f₀
    have hf : ∀ v, f (z • v) = f v := fun v => by
      simp only [f, AddMonoidHom.comp_apply, Int.coe_castAddHom]
      rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hpord ▸ hdvd v
    have h0 := hu f hf
    simp only [f, AddMonoidHom.comp_apply, Int.coe_castAddHom,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    rw [hχ]
    exact orderOf_dvd_iff_zpow_eq_one.1 (hpord ▸ h0)

theorem familyStabilizer_le_reflection_of_prime_power
    {τ : Tag} {K : Type} [Field K] {ι : Type} [Finite ι]
    {p : ℕ} (hp : p.Prime) {a : ι → Fin τ.rank → Kˣ}
    (ha : ∀ i j, a i j ^ p = 1)
    (hP : ∀ z ∈ familyStabilizerSubgroup a, ∀ e : ℕ,
      orderOf z = p ^ e → z ∈ familyReflectionGroup a) :
    familyStabilizerSubgroup a ≤ familyReflectionGroup a := by
  have := Fact.mk hp
  have : Finite (WeylGroup τ) := (exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.1
  intro w hw
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' p hp.ne_one
  have hcopm : Nat.Coprime (p ^ e) m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  obtain ⟨x, y, hxy⟩ : IsCoprime ((p ^ e : ℕ) : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hcopm
  have hsplit : w = w ^ (x * (p ^ e : ℕ)) * w ^ (y * m) := by
    rw [← zpow_add, show x * ((p ^ e : ℕ) : ℤ) + y * m = 1 from hxy, zpow_one]
  have hpow : w ^ (orderOf w) = 1 := pow_orderOf_eq_one w
  have hA : w ^ (x * (p ^ e : ℕ)) ∈ familyReflectionGroup a := by
    refine mem_familyReflectionGroup_of_coprime hp ha (zpow_mem hw _) ?_
    have : (w ^ (x * (p ^ e : ℕ))) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show x * ((p ^ e : ℕ) : ℤ) * (m : ℤ) =
        (orderOf w : ℤ) * x by rw [hord]; push_cast; ring, zpow_mul, zpow_natCast, hpow, one_zpow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one this)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm |>.symm |> fun h => h.symm
  set z := w ^ (y * m) with hzdef
  have hzS : z ∈ familyStabilizerSubgroup a := zpow_mem hw _
  have hzpe : z ^ (p ^ e) = 1 := by
    rw [hzdef, ← zpow_natCast, ← zpow_mul, show y * (m : ℤ) * ((p ^ e : ℕ) : ℤ) =
      (orderOf w : ℤ) * y by rw [hord]; push_cast; ring, zpow_mul, zpow_natCast, hpow, one_zpow]
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).mp
    (orderOf_dvd_of_pow_eq_one hzpe)
  have hB : z ∈ familyReflectionGroup a := hP z hzS f hf
  rw [hsplit]
  exact mul_mem hA hB

theorem familyStabilizer_le_reflection {τ : Tag} {K : Type} [Field K] {ι : Type}
    [Finite ι] {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ) ∨ SylowCert τ p)
    {a : ι → Fin τ.rank → Kˣ} (ha : ∀ i j, a i j ^ p = 1) :
    familyStabilizerSubgroup a ≤ familyReflectionGroup a := by
  have := Fact.mk hp
  have : Finite (WeylGroup τ) :=
    (exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.1
  refine familyStabilizer_le_reflection_of_prime_power hp ha ?_
  intro z hzS e hze
  by_cases hz1 : z = 1
  · rw [hz1]; exact one_mem _
  have hdvdW : orderOf z ∣ Nat.card (WeylGroup τ) := orderOf_dvd_natCard z
  rcases hW with hW | ⟨hW2, w₀, hw₀, hw₀mem⟩
  · have he : e = 0 := by
      by_contra he
      exact hW (dvd_trans (dvd_pow_self p he) (hze ▸ hdvdW))
    have hzo : orderOf z = 1 := by rw [hze, he, pow_zero]
    exact absurd (orderOf_eq_one_iff.mp hzo) hz1
  · have he1 : e ≤ 1 := by
      by_contra he
      exact hW2 (dvd_trans (pow_dvd_pow p (by omega)) (hze ▸ hdvdW))
    have he0 : e ≠ 0 := fun h => hz1 (orderOf_eq_one_iff.mp (by rw [hze, h, pow_zero]))
    have hzp : orderOf z = p := by rw [hze, show e = 1 by omega, pow_one]
    have hidx : ∀ t : WeylGroup τ, orderOf t = p → ¬ p ∣ (Subgroup.zpowers t).index := by
      intro t ht hdiv
      have hc := Subgroup.card_mul_index (Subgroup.zpowers t)
      rw [Nat.card_zpowers, ht] at hc
      exact hW2 (by rw [← hc, pow_two]; exact Nat.mul_dvd_mul_left p hdiv)
    have hPz : IsPGroup p (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
    have hP0 : IsPGroup p (Subgroup.zpowers w₀) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw₀, pow_one])
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup τ) (hP0.toSylow (hidx w₀ hw₀))
      (hPz.toSylow (hidx z hzp))
    have hzmem : z ∈ (g • hP0.toSylow (hidx w₀ hw₀) : Sylow p (WeylGroup τ)) := by
      rw [hg]; exact (IsPGroup.mem_toSylow _ _).2 (Subgroup.mem_zpowers z)
    have hzmem2 : z ∈ (MulAut.conj g • ((hP0.toSylow (hidx w₀ hw₀) : Sylow p (WeylGroup τ)) :
        Subgroup (WeylGroup τ))) := by
      rw [← Sylow.coe_subgroup_smul]; exact hzmem
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzmem2
    replace hzmem := hzmem2
    have hz' : g⁻¹ * z * g ∈ Subgroup.zpowers w₀ := by
      have := (IsPGroup.mem_toSylow _ _).1 hzmem
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
    have hw₀z : w₀ ∈ Subgroup.zpowers (g⁻¹ * z * g) := by
      have hle : Subgroup.zpowers (g⁻¹ * z * g) ≤ Subgroup.zpowers w₀ :=
        (Subgroup.zpowers_le).2 hz'
      have hcard : Nat.card (Subgroup.zpowers (g⁻¹ * z * g)) = Nat.card (Subgroup.zpowers w₀) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hw₀, ← hzp]
        simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
      have := Subgroup.eq_of_le_of_card_ge hle hcard.ge
      rw [this]; exact Subgroup.mem_zpowers w₀
    have h1 : w₀ ∈ fixReflectionGroup p (g⁻¹ * z * g) := fixReflectionGroup_mono hw₀z hw₀mem
    have h2 : g⁻¹ * z * g ∈ fixReflectionGroup p (g⁻¹ * z * g) := by
      have hzz : g⁻¹ * z * g ∈ Subgroup.zpowers w₀ := hz'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hzz
      have := zpow_mem h1 n
      rwa [hn] at this
    have h3 := conj_mem_fixReflectionGroup g h2
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h3
    exact fixReflectionGroup_le_family hp ha hzS h3

theorem conj_simple_mem_fixReflectionGroup {τ : Tag} {p : ℕ} {w₀ u : WeylGroup τ} {i : Fin τ.rank}
    (y z : Fin τ.rank → ℤ)
    (h : u • (Pi.single i 1 : Fin τ.rank → ℤ) = w₀ • y - y + (p : ℤ) • z) :
    u * simple τ i * u⁻¹ ∈ fixReflectionGroup p w₀ := by
  refine Subgroup.subset_closure ⟨u, i, fun f hf => ?_, rfl⟩
  rw [h, map_add, map_sub, hf, sub_self, zero_add, map_zsmul, zsmul_eq_mul]
  simp

theorem lattice_list_prod_simple_smul {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (l.map (simple τ)).prod • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.prod_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem sylowCert_of_chain {τ : Tag} {p : ℕ} (hp : p.Prime) (hW2 : ¬ p ^ 2 ∣ Nat.card (WeylGroup τ))
    (l : List (Fin τ.rank)) (y z : Fin τ.rank → Fin τ.rank → ℤ)
    (hpow : ∀ i : Fin τ.rank, (fun v => l.foldr (reflect τ) v)^[p] (Pi.single i 1) = Pi.single i 1)
    (hne : ∃ i : Fin τ.rank, l.foldr (reflect τ) (Pi.single i 1) ≠ Pi.single i 1)
    (hwit : ∀ i ∈ l, (Pi.single i 1 : Fin τ.rank → ℤ) =
      l.foldr (reflect τ) (y i) - y i + (p : ℤ) • z i) :
    SylowCert τ p := by
  haveI := Fact.mk hp
  set w₀ := (l.map (simple τ)).prod
  refine ⟨hW2, w₀, orderOf_eq_prime ?_ ?_, ?_⟩
  · refine ext_single fun i => ?_
    rw [one_smul, ← congrFun (smul_iterate w₀ p) (Pi.single i 1)]
    have : (fun v => w₀ • v) = fun v => l.foldr (reflect τ) v := funext (lattice_list_prod_simple_smul l)
    rw [this]; exact hpow i
  · intro h1
    obtain ⟨i, hi⟩ := hne
    apply hi
    rw [← lattice_list_prod_simple_smul]
    change w₀ • _ = _
    rw [h1, one_smul]
  · refine (fixReflectionGroup p w₀).list_prod_mem fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have := conj_simple_mem_fixReflectionGroup (p := p) (w₀ := w₀) (u := 1) (i := i) (y i) (z i)
      (by rw [one_smul, lattice_list_prod_simple_smul]; exact hwit i hi)
    simpa using this


end Lattice

section Group

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem canonicalRep_conj_simple_mem_familyGroup
    {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ} {i : Fin τ.rank}
    (hα : w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ familyKernel a) :
    canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹) ∈ familyGroup (K := K) a := by
  set n := canonicalRep (coxeterSystem τ) K w
  set α : Fin τ.rank → ℤ := w • (Pi.single i 1 : Fin τ.rank → ℤ)
  have hnegα : -α ∈ familyKernel a := by
    refine ⟨IsRoot.neg hα.1, fun j => ?_⟩
    rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2 j, inv_one, mul_one]
  have hmapx := (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ i)
  have hmapy := (canonical_weyl_root_transport τ K).2.1 w _ (IsRoot.neg (isRoot_single τ i))
  rw [smul_neg] at hmapy
  have hU : ∀ β ∈ familyKernel a, rootSubgroup τ K β ≤ familyGroup (K := K) a := fun β hβ =>
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ familyKernel a) => rootSubgroup τ K γ) β hβ
      le_rfl).trans le_sup_right
  have hx : ∀ c : K, n * xUnit τ K i c * n⁻¹ ∈ familyGroup (K := K) a := fun c => by
    refine hU α hα ?_
    rw [← hmapx]
    exact ⟨_, xUnit_mem_rootSubgroup i c, rfl⟩
  have hy : ∀ c : K, n * yUnit τ K i c * n⁻¹ ∈ familyGroup (K := K) a := fun c => by
    refine hU (-α) hnegα ?_
    rw [← hmapy]
    exact ⟨_, yUnit_mem_rootSubgroup i c, rfl⟩
  have hm : n * weylElt τ K i 1 * n⁻¹ ∈ familyGroup (K := K) a := by
    rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
    have e : n * (xUnit τ K i ((1 : Kˣ) : K) * yUnit τ K i (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) *
        xUnit τ K i ((1 : Kˣ) : K)) * n⁻¹ = (n * xUnit τ K i ((1 : Kˣ) : K) * n⁻¹) *
          (n * yUnit τ K i (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * n⁻¹) *
            (n * xUnit τ K i ((1 : Kˣ) : K) * n⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  have hN : (canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ K i 1 * n⁻¹) ∈ monomialSubgroup τ K :=
    mul_mem (inv_mem (canonicalRep_mem_monomialSubgroup K _))
      (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K w) (weylElt_mem_monomialSubgroup i))
        (inv_mem (canonicalRep_mem_monomialSubgroup K w)))
  have hmaps : MapsRootLines ((canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ K i 1 * n⁻¹)) 1 := by
    have := (mapsRootLines_canonicalRep (R := K) (w * simple τ i * w⁻¹)).inv.mul
      (((mapsRootLines_canonicalRep (R := K) w).mul (mapsRootLines_weylElt i)).mul
        (mapsRootLines_canonicalRep (R := K) w).inv)
    rwa [inv_mul_cancel] at this
  have hT := mem_torusGroup_of_mapsRootLines_one hN hmaps
  have e : canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹) =
      (n * weylElt τ K i 1 * n⁻¹) *
        ((canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
          (n * weylElt τ K i 1 * n⁻¹))⁻¹ := by group
  rw [e]
  exact mul_mem hm (inv_mem (le_sup_left (a := torusGroup τ K) hT))

theorem canonicalRep_mem_familyGroup {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ familyReflectionGroup a) :
    canonicalRep (coxeterSystem τ) K w ∈ familyGroup (K := K) a := by
  have hTM : torusGroup τ K ≤ familyGroup (K := K) a := le_sup_left
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, i, hα, rfl⟩ := hx
    exact canonicalRep_conj_simple_mem_familyGroup hα
  | one => rw [canonicalRep_one]; exact one_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk, hkxy⟩ := canonicalRep_mul_mem (R := K) x y
    have e : canonicalRep (coxeterSystem τ) K (x * y) =
        k⁻¹ * (canonicalRep (coxeterSystem τ) K x * canonicalRep (coxeterSystem τ) K y) := by
      rw [hkxy]; group
    rw [e]
    exact mul_mem (inv_mem (hTM hk)) (mul_mem hx hy)
  | inv x _ hx =>
    obtain ⟨k, hk, hkx⟩ := canonicalRep_mul_mem (R := K) x x⁻¹
    rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkx
    have e : canonicalRep (coxeterSystem τ) K x⁻¹ = (canonicalRep (coxeterSystem τ) K x)⁻¹ * k := by
      rw [← hkx]; group
    rw [e]
    exact mul_mem (inv_mem hx) (hTM hk)

theorem familyCentralizer_eq_familyGroup {τ : Tag} {K : Type} [Field K] {ι : Type}
    (a : ι → Fin τ.rank → Kˣ)
    (h : familyStabilizerSubgroup a ≤ familyReflectionGroup a) :
    familyCentralizer τ K a = familyGroup (K := K) a := by
  refine le_antisymm (fun g hg => ?_) (familyGroup_le_familyCentralizer a)
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ K a hg
  exact mul_mem hm (canonicalRep_mem_familyGroup (h (mem_familyStabilizerSubgroup.2 hw)))


theorem sylowCert_D4_3 : SylowCert .D4 3 :=
  sylowCert_of_chain (by norm_num) (by have h := CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.not_nine_dvd_card_weylGroup_D4; norm_num at h ⊢; exact h) [(⟨0, by decide⟩ : Fin Tag.D4.rank), (⟨2, by decide⟩ : Fin Tag.D4.rank)]
    (fun i => if i.val = 0 then ![1, 2, 0, 0] else if i.val = 2 then ![2, 2, 0, 0] else 0) (fun i => if i.val = 0 then ![0, 0, -1, 0] else if i.val = 2 then ![0, 0, -1, 0] else 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sylowCert_E6_5 : SylowCert .E6 5 :=
  sylowCert_of_chain (by norm_num) (by rw [CFSG.StandardType.NoOffExc.card_weyl_E6]; norm_num) [(⟨0, by decide⟩ : Fin Tag.E6.rank), (⟨2, by decide⟩ : Fin Tag.E6.rank), (⟨3, by decide⟩ : Fin Tag.E6.rank), (⟨4, by decide⟩ : Fin Tag.E6.rank)]
    (fun i => if i.val = 0 then ![1, 2, 3, 0, 0, 0] else if i.val = 2 then ![2, 2, 3, 0, 0, 0] else if i.val = 3 then ![2, 2, 4, 0, 0, 0] else if i.val = 4 then ![2, 2, 4, 1, 0, 0] else 0) (fun i => if i.val = 0 then ![0, 0, 0, -1, 0, 0] else if i.val = 2 then ![0, 0, 0, -1, 0, 0] else if i.val = 3 then ![0, 0, 0, -1, 0, 0] else if i.val = 4 then ![0, 0, 0, -1, 0, 0] else 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sylowCert_E7_5 : SylowCert .E7 5 :=
  sylowCert_of_chain (by norm_num) (by rw [CFSG.StandardType.NoOffExc.card_weyl_E7]; norm_num) [(⟨0, by decide⟩ : Fin Tag.E7.rank), (⟨2, by decide⟩ : Fin Tag.E7.rank), (⟨3, by decide⟩ : Fin Tag.E7.rank), (⟨4, by decide⟩ : Fin Tag.E7.rank)]
    (fun i => if i.val = 0 then ![1, 2, 3, 0, 0, 0, 0] else if i.val = 2 then ![2, 2, 3, 0, 0, 0, 0] else if i.val = 3 then ![2, 2, 4, 0, 0, 0, 0] else if i.val = 4 then ![2, 2, 4, 1, 0, 0, 0] else 0) (fun i => if i.val = 0 then ![0, 0, 0, -1, 0, 0, 0] else if i.val = 2 then ![0, 0, 0, -1, 0, 0, 0] else if i.val = 3 then ![0, 0, 0, -1, 0, 0, 0] else if i.val = 4 then ![0, 0, 0, -1, 0, 0, 0] else 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sylowCert_E7_7 : SylowCert .E7 7 :=
  sylowCert_of_chain (by norm_num) (by rw [CFSG.StandardType.NoOffExc.card_weyl_E7]; norm_num) [(⟨0, by decide⟩ : Fin Tag.E7.rank), (⟨2, by decide⟩ : Fin Tag.E7.rank), (⟨3, by decide⟩ : Fin Tag.E7.rank), (⟨4, by decide⟩ : Fin Tag.E7.rank), (⟨5, by decide⟩ : Fin Tag.E7.rank), (⟨6, by decide⟩ : Fin Tag.E7.rank)]
    (fun i => if i.val = 0 then ![4, 5, 2, 0, 0, 0, 0] else if i.val = 2 then ![5, 5, 2, 0, 0, 0, 0] else if i.val = 3 then ![5, 5, 3, 0, 0, 0, 0] else if i.val = 4 then ![5, 5, 3, 1, 0, 0, 0] else if i.val = 5 then ![5, 5, 3, 1, 1, 0, 0] else if i.val = 6 then ![5, 5, 3, 1, 1, 1, 0] else 0) (fun i => if i.val = 0 then ![0, 0, -1, -1, 0, 0, 0] else if i.val = 2 then ![0, 0, -1, -1, 0, 0, 0] else if i.val = 3 then ![0, 0, -1, -1, 0, 0, 0] else if i.val = 4 then ![0, 0, -1, -1, 0, 0, 0] else if i.val = 5 then ![0, 0, -1, -1, 0, 0, 0] else if i.val = 6 then ![0, 0, -1, -1, 0, 0, 0] else 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sylowCert_E8_7 : SylowCert .E8 7 :=
  sylowCert_of_chain (by norm_num) (by rw [CFSG.StandardType.NoOffExc.card_weyl_E8]; norm_num) [(⟨0, by decide⟩ : Fin Tag.E8.rank), (⟨2, by decide⟩ : Fin Tag.E8.rank), (⟨3, by decide⟩ : Fin Tag.E8.rank), (⟨4, by decide⟩ : Fin Tag.E8.rank), (⟨5, by decide⟩ : Fin Tag.E8.rank), (⟨6, by decide⟩ : Fin Tag.E8.rank)]
    (fun i => if i.val = 0 then ![4, 5, 2, 0, 0, 0, 0, 0] else if i.val = 2 then ![5, 5, 2, 0, 0, 0, 0, 0] else if i.val = 3 then ![5, 5, 3, 0, 0, 0, 0, 0] else if i.val = 4 then ![5, 5, 3, 1, 0, 0, 0, 0] else if i.val = 5 then ![5, 5, 3, 1, 1, 0, 0, 0] else if i.val = 6 then ![5, 5, 3, 1, 1, 1, 0, 0] else 0) (fun i => if i.val = 0 then ![0, 0, -1, -1, 0, 0, 0, 0] else if i.val = 2 then ![0, 0, -1, -1, 0, 0, 0, 0] else if i.val = 3 then ![0, 0, -1, -1, 0, 0, 0, 0] else if i.val = 4 then ![0, 0, -1, -1, 0, 0, 0, 0] else if i.val = 5 then ![0, 0, -1, -1, 0, 0, 0, 0] else if i.val = 6 then ![0, 0, -1, -1, 0, 0, 0, 0] else 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sylowCert_G2_3 : SylowCert .G2 3 := by
  haveI := Fact.mk Nat.prime_three
  set i0 : Fin Tag.G2.rank := ⟨0, by decide⟩
  set i1 : Fin Tag.G2.rank := ⟨1, by decide⟩
  set l : List (Fin Tag.G2.rank) := [i0, i1, i0, i1]
  set w₀ : WeylGroup .G2 := (l.map (simple .G2)).prod with hw₀
  have hinv : (simple .G2 i1)⁻¹ = simple .G2 i1 := (coxeterSystem .G2).inv_simple i1
  have hw₀' : w₀ = simple .G2 i0 * (simple .G2 i1 * simple .G2 i0 * (simple .G2 i1)⁻¹) := by
    rw [hinv, hw₀]; simp [l, mul_assoc]
  have hact : ∀ v, w₀ • v = l.foldr (reflect .G2) v := lattice_list_prod_simple_smul l
  refine ⟨by rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]; norm_num, w₀,
    orderOf_eq_prime ?_ ?_, ?_⟩
  · refine ext_single fun i => ?_
    rw [one_smul, ← congrFun (smul_iterate w₀ 3) (Pi.single i 1)]
    have : (fun v => w₀ • v) = fun v => l.foldr (reflect .G2) v := funext hact
    rw [this]; revert i; decide +kernel
  · intro h1
    have := hact (Pi.single i0 1)
    rw [h1, one_smul] at this
    revert this; decide +kernel
  · have hA : simple .G2 i0 ∈ fixReflectionGroup 3 w₀ := by
      have := conj_simple_mem_fixReflectionGroup (τ := .G2) (p := 3) (w₀ := w₀) (u := 1) (i := i0)
        (fun j : Fin Tag.G2.rank => (![0, 2] : Fin 2 → ℤ) j) (fun j : Fin Tag.G2.rank => (![1, 2] : Fin 2 → ℤ) j)
        (by rw [one_smul, hact]; decide +kernel)
      simpa using this
    have hB : simple .G2 i1 * simple .G2 i0 * (simple .G2 i1)⁻¹ ∈ fixReflectionGroup 3 w₀ :=
      conj_simple_mem_fixReflectionGroup (τ := .G2) (p := 3) (w₀ := w₀)
        (fun j : Fin Tag.G2.rank => (![0, 2] : Fin 2 → ℤ) j) (fun j : Fin Tag.G2.rank => (![1, 3] : Fin 2 → ℤ) j)
        (by rw [simple_smul, hact]; decide +kernel)
    have hmem := mul_mem hA hB
    rwa [← hw₀'] at hmem


theorem prime_cases_three_five_seven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ 7 < p := by
  rcases Nat.lt_or_ge 7 p with h | h
  · exact Or.inr (Or.inr (Or.inr h))
  have h2 := hp.two_le
  have : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · simp
  · exact absurd hp (by norm_num)
  · simp
  · exact absurd hp (by norm_num)
  · simp

theorem not_dvd_or_sylowCert (τ : Tag) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5) :
    ¬ p ∣ Nat.card (WeylGroup τ) ∨ SylowCert τ p := by
  rcases prime_cases_three_five_seven hp hp2 with rfl | rfl | rfl | hp7
  · cases τ
    · exact Or.inr sylowCert_G2_3
    · exact absurd rfl (h3 (Or.inl rfl))
    · exact Or.inr sylowCert_D4_3
    · exact absurd rfl (h3 (Or.inr (Or.inl rfl)))
    · exact absurd rfl (h3 (Or.inr (Or.inr (Or.inl rfl))))
    · exact absurd rfl (h3 (Or.inr (Or.inr (Or.inr rfl))))
  · cases τ
    · left; rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]; norm_num
    · exact Or.inl (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 (by norm_num) (by norm_num))
    · exact Or.inl (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 (by norm_num) (by norm_num))
    · exact Or.inr sylowCert_E6_5
    · exact Or.inr sylowCert_E7_5
    · exact absurd rfl (h5 rfl)
  · cases τ
    · left; rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]; norm_num
    · exact Or.inl (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 (by norm_num) (by norm_num))
    · exact Or.inl (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 (by norm_num) (by norm_num))
    · left; rw [CFSG.StandardType.NoOffExc.card_weyl_E6]; norm_num
    · exact Or.inr sylowCert_E7_7
    · exact Or.inr sylowCert_E8_7
  · left
    cases τ
    · rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      have : p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> revert h hp <;> norm_num
    · exact CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by omega)
    · exact CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by omega)
    · exact CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp hp7 (Or.inl rfl)
    · exact CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inl rfl))
    · exact CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))

theorem familyCentralizer_eq_familyGroup_of_nonTorsion {τ : Tag} {K : Type} [Field K] {ι : Type}
    [Finite ι] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5)
    (a : ι → Fin τ.rank → Kˣ) (ha : ∀ i j, a i j ^ p = 1) :
    familyCentralizer τ K a = familyGroup (K := K) a :=
  familyCentralizer_eq_familyGroup a
    (familyStabilizer_le_reflection hp (not_dvd_or_sylowCert τ hp hp2 h3 h5) ha)

end Group

end CFSG.HardMathSupport.C14Lattice
