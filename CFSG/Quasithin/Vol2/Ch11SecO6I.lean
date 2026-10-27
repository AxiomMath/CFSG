module

public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Quasithin
open scoped commutatorElement

variable {X : Type} [Group X]

theorem commute_of_pCore_ne {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hrp : r ≠ p) {d e : X}
    (hd : d ∈ CFSG.pCore r X) (he : e ∈ CFSG.pCore p X) : d * e = e * d :=
  (Subgroup.commute_of_normal_of_disjoint _ _ CFSG.pCore_normal CFSG.pCore_normal
    (IsPGroup.disjoint_of_ne r p hrp _ _ CFSG.pCore_isPGroup CFSG.pCore_isPGroup) d e hd he).eq

theorem map_mem_pCore (r : ℕ) (β : MulAut X) {d : X} (hd : d ∈ CFSG.pCore r X) :
    β d ∈ CFSG.pCore r X := by
  rw [← CFSG.pCore_map_iso r β]
  exact Subgroup.mem_map_of_mem _ hd

theorem exists_conj_fitting [Finite X] (β : MulAut X)
    (h : ∀ r : ℕ, r.Prime → ∃ f ∈ CFSG.pCore r X, ∀ d ∈ CFSG.pCore r X, β d = f * d * f⁻¹) :
    ∃ f ∈ CFSG.fittingSubgroup X, ∀ d ∈ CFSG.fittingSubgroup X, β d = f * d * f⁻¹ := by
  classical
  have key : ∀ T : Finset ℕ, (∀ r ∈ T, r.Prime) → ∃ f ∈ CFSG.fittingSubgroup X,
      (∀ r ∈ T, ∀ d ∈ CFSG.pCore r X, β d = f * d * f⁻¹) ∧
      (∀ r : ℕ, r.Prime → r ∉ T → ∀ d ∈ CFSG.pCore r X, f * d = d * f) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, one_mem _, by simp, fun r _ _ d _ => by simp⟩
    | insert a T haT ih =>
      intro hT
      obtain ⟨f, hfF, hf1, hf2⟩ := ih fun r hr => hT r (Finset.mem_insert_of_mem hr)
      have ha : a.Prime := hT a (Finset.mem_insert_self a T)
      have : Fact a.Prime := ⟨ha⟩
      obtain ⟨g, hg, hg1⟩ := h a ha
      refine ⟨f * g, Subgroup.mul_mem _ hfF (CFSG.pCore_le_fitting X a hg),
        fun r hr d hd => ?_, fun r hr hrT d hd => ?_⟩
      · rcases Finset.mem_insert.mp hr with rfl | hrT
        · calc β d = f * β d * f⁻¹ := by
                rw [hf2 r ha haT (β d) (map_mem_pCore r β hd), mul_inv_cancel_right]
            _ = f * (g * d * g⁻¹) * f⁻¹ := by rw [hg1 d hd]
            _ = f * g * d * (f * g)⁻¹ := by group
        · have : Fact r.Prime := ⟨hT r hr⟩
          have hra : r ≠ a := fun h => haT (h ▸ hrT)
          have hgd : g * d = d * g := commute_of_pCore_ne (Ne.symm hra) hg hd
          calc β d = f * d * f⁻¹ := hf1 r hrT d hd
            _ = f * (g * d * g⁻¹) * f⁻¹ := by rw [hgd, mul_inv_cancel_right]
            _ = f * g * d * (f * g)⁻¹ := by group
      · have hra : r ≠ a := fun h => hrT (h ▸ Finset.mem_insert_self a T)
        have hrT' : r ∉ T := fun h' => hrT (Finset.mem_insert_of_mem h')
        have : Fact r.Prime := ⟨hr⟩
        have hgd : g * d = d * g := commute_of_pCore_ne (Ne.symm hra) hg hd
        calc f * g * d = f * (d * g) := by rw [mul_assoc, hgd]
          _ = d * (f * g) := by rw [← mul_assoc, hf2 r hr hrT' d hd, mul_assoc]
  obtain ⟨f, hfF, hf1, -⟩ := key (Nat.card X).primeFactors
    fun r hr => Nat.prime_of_mem_primeFactors hr
  refine ⟨f, hfF, fun d hd => ?_⟩
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at hd
  have hle : (⨆ p : (Nat.card X).primeFactors, CFSG.pCore (p : ℕ) X) ≤
      MonoidHom.eqLocus β.toMonoidHom (MulAut.conj f).toMonoidHom :=
    iSup_le fun p e he => by
      change β e = MulAut.conj f e
      rw [MulAut.conj_apply]
      exact hf1 p p.2 e he
  have := hle hd
  change β d = MulAut.conj f d at this
  rwa [MulAut.conj_apply] at this

theorem frattiniIn_central [Finite X] {r : ℕ} [Fact r.Prime]
    (hE : IsPOnePlusTwo r ↥(CFSG.pCore r X)) {x : X} (hx : x ∈ frattiniIn (CFSG.pCore r X))
    {e : X} (he : e ∈ CFSG.pCore r X) : x * e = e * x := by
  obtain ⟨hex, -, hexp⟩ := hE
  set E := CFSG.pCore r X
  have : Fact (IsPGroup r ↥E) := ⟨CFSG.pCore_isPGroup⟩
  have hcomm : commutator ↥E ≤ Subgroup.center ↥E := by
    have : IsMulCommutative (↥E ⧸ Subgroup.center ↥E) :=
      (IsExtraspecial.quotient_elementary_abelian r ↥E).toIsMulCommutative
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center ↥E)).1 this
  obtain ⟨u, hu, rfl⟩ := hx
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := r)] at hu
  have hle : Subgroup.closure (((commutator ↥E : Subgroup ↥E) : Set ↥E) ∪
      Set.range (fun x : ↥E => x ^ r)) ≤ Subgroup.center ↥E := by
    rw [Subgroup.closure_le]
    rintro y (hy | ⟨w, rfl⟩)
    · exact hcomm hy
    · change w ^ r ∈ Subgroup.center ↥E
      rw [hexp w]
      exact one_mem _
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp (hle hu) ⟨e, he⟩)).symm

theorem mul_comm_of_card_dvd_sq {r : ℕ} [Fact r.Prime] (H : Subgroup X) {k : ℕ}
    (hk : Nat.card H = r ^ k) (hk2 : k ≤ 2) {a b : X} (ha : a ∈ H) (hb : b ∈ H) :
    a * b = b * a := by
  have key : (⟨a, ha⟩ : H) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    interval_cases k
    · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
      exact Subsingleton.elim _ _
    · have : IsCyclic H := isCyclic_of_prime_card (by rw [hk, pow_one])
      exact (inferInstance : IsMulCommutative H).is_comm.comm _ _
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk).is_comm.comm _ _
  exact congrArg Subtype.val key

theorem exists_conj_of_pOnePlusTwo [Finite X] {r : ℕ} [Fact r.Prime]
    (hE : IsPOnePlusTwo r ↥(CFSG.pCore r X)) (β : MulAut X)
    (hβ : ∀ d ∈ CFSG.pCore r X, d⁻¹ * β d ∈ frattiniIn (CFSG.pCore r X)) :
    ∃ f ∈ CFSG.pCore r X, ∀ d ∈ CFSG.pCore r X, β d = f * d * f⁻¹ := by
  set E := CFSG.pCore r X with hEdef
  have : Fact (IsPGroup r ↥E) := ⟨CFSG.pCore_isPGroup⟩
  have hcen : ∀ x ∈ frattiniIn E, ∀ e ∈ E, x * e = e * x := fun x hx e he =>
    frattiniIn_central hE hx he
  obtain ⟨hex, hcard, -⟩ := hE
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a := by
    have hnt := IsExtraspecial.quotient_nontrivial r ↥E
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥E ⧸ Subgroup.center ↥E)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∉ Subgroup.center ↥E := fun h => hq ((QuotientGroup.eq_one_iff x).mpr h)
    rw [Subgroup.mem_center_iff] at hx
    push Not at hx
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, g.2, x, x.2, fun h => hg (Subtype.ext h)⟩
  set z := a * b * a⁻¹ * b⁻¹ with hzdef
  have hzE : z ∈ E := by
    rw [hzdef]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hzΦ : z ∈ frattiniIn E := by
    refine ⟨⁅(⟨a, ha⟩ : ↥E), ⟨b, hb⟩⁆, CFSG.commutator_le_frattini_of_isPGroup (p := r)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)), ?_⟩
    simp only [commutatorElement_def, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, z]
  have hzc : ∀ e ∈ E, z * e = e * z := hcen z hzΦ
  have hz1 : z ≠ 1 := by
    intro h
    apply hab
    rw [hzdef] at h
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  have hZ : ∀ w ∈ E, (∀ e ∈ E, w * e = e * w) → ∃ i : ℕ, w = z ^ i := by
    intro w hw hwc
    have hcardC : Nat.card (Subgroup.center ↥E) = r := IsExtraspecial.center_order_p r ↥E
    let zz : Subgroup.center ↥E := ⟨⟨z, hzE⟩, Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (hzc g g.2).symm⟩
    let ww : Subgroup.center ↥E := ⟨⟨w, hw⟩, Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (hwc g g.2).symm⟩
    have hzz : zz ≠ 1 := fun h => hz1 (congrArg (fun u : Subgroup.center ↥E => ((u : ↥E) : X)) h)
    have htop := zpowers_eq_top_of_prime_card hcardC hzz
    have hmem : ww ∈ (Submonoid.powers zz : Set (Subgroup.center ↥E)) := by
      rw [powers_eq_zpowers, htop]
      exact Subgroup.mem_top _
    obtain ⟨i, hi⟩ := Submonoid.mem_powers_iff _ _ |>.mp hmem
    exact ⟨i, (congrArg (fun u : Subgroup.center ↥E => ((u : ↥E) : X)) hi).symm⟩
  have hβa : a⁻¹ * β a ∈ E := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) (map_mem_pCore r β ha)
  have hβb : b⁻¹ * β b ∈ E := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) (map_mem_pCore r β hb)
  obtain ⟨i, hi⟩ := hZ _ hβa (hcen _ (hβ a ha))
  obtain ⟨j, hj⟩ := hZ _ hβb (hcen _ (hβ b hb))
  have hβa' : β a = a * z ^ i := by rw [← hi, mul_inv_cancel_left]
  have hβb' : β b = b * z ^ j := by rw [← hj, mul_inv_cancel_left]
  have hza : Commute z a := hzc a ha
  have hzb : Commute z b := hzc b hb
  have hab' : a * b = z * b * a := by rw [hzdef]; group
  have h1 : b⁻¹ * a * b = a * z :=
    calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
      _ = b⁻¹ * (z * b) * a := by rw [hab']; group
      _ = b⁻¹ * (b * z) * a := by rw [hzb.eq]
      _ = z * a := by group
      _ = a * z := hza.eq
  have h2 : a * b * a⁻¹ = b * z :=
    calc a * b * a⁻¹ = z * b := by rw [hab']; group
      _ = b * z := hzb.eq
  have hpa : ∀ n : ℕ, b⁻¹ ^ n * a * (b⁻¹ ^ n)⁻¹ = a * z ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : z ^ n * b = b * z ^ n := (hzb.pow_left n).eq
      calc b⁻¹ ^ (n + 1) * a * (b⁻¹ ^ (n + 1))⁻¹ = b⁻¹ * (b⁻¹ ^ n * a * (b⁻¹ ^ n)⁻¹) * b := by
            rw [pow_succ']
            group
        _ = b⁻¹ * a * (z ^ n * b) := by rw [ih]; group
        _ = b⁻¹ * a * b * z ^ n := by rw [hc]; group
        _ = a * z ^ (n + 1) := by rw [h1, pow_succ']; group
  have hpb : ∀ n : ℕ, a ^ n * b * (a ^ n)⁻¹ = b * z ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : a * z ^ n = z ^ n * a := (hza.pow_left n).eq.symm
      calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
        _ = a * b * a⁻¹ * (a * z ^ n * a⁻¹) := by rw [ih]; group
        _ = b * z ^ (n + 1) := by rw [h2, hc, pow_succ']; group
  set f := a ^ j * b⁻¹ ^ i with hfdef
  have hfE : f ∈ E := Subgroup.mul_mem _ (Subgroup.pow_mem _ ha j)
    (Subgroup.pow_mem _ (Subgroup.inv_mem _ hb) i)
  have hfa : β a = f * a * f⁻¹ := by
    have e1 : a ^ j * a = a * a ^ j := ((Commute.refl a).pow_left j).eq
    have e2 : a ^ j * z ^ i = z ^ i * a ^ j := ((hza.pow_left i).pow_right j).eq.symm
    calc β a = a * z ^ i := hβa'
      _ = a * (z ^ i * a ^ j) * (a ^ j)⁻¹ := by group
      _ = a * (a ^ j * z ^ i) * (a ^ j)⁻¹ := by rw [e2]
      _ = a ^ j * a * z ^ i * (a ^ j)⁻¹ := by rw [e1]; group
      _ = a ^ j * (b⁻¹ ^ i * a * (b⁻¹ ^ i)⁻¹) * (a ^ j)⁻¹ := by rw [hpa]; group
      _ = f * a * f⁻¹ := by rw [hfdef]; group
  have hfb : β b = f * b * f⁻¹ := by
    have e1 : b⁻¹ ^ i * b = b * b⁻¹ ^ i := ((Commute.refl b).inv_left.pow_left i).eq
    calc β b = a ^ j * b * (a ^ j)⁻¹ := by rw [hβb', hpb]
      _ = a ^ j * (b⁻¹ ^ i * b * (b⁻¹ ^ i)⁻¹) * (a ^ j)⁻¹ := by rw [e1]; group
      _ = f * b * f⁻¹ := by rw [hfdef]; group
  set H := Subgroup.closure ({a, b} : Set X) with hHdef
  have hHE : H ≤ E := by
    rw [hHdef, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have haH : a ∈ H := Subgroup.subset_closure (Set.mem_insert a _)
  have hbH : b ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hEH : E ≤ H := by
    have hdvd : Nat.card H ∣ r ^ 3 := hcard ▸ Subgroup.card_dvd_of_le hHE
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).mp hdvd
    by_cases hk2 : k ≤ 2
    · exact absurd (mul_comm_of_card_dvd_sq H hk hk2 haH hbH) hab
    · have hk' : k = 3 := by omega
      exact (Subgroup.eq_of_le_of_card_ge hHE (by rw [hcard, hk, hk'])).symm.le
  refine ⟨f, hfE, fun d hd => ?_⟩
  have hle : H ≤ MonoidHom.eqLocus β.toMonoidHom (MulAut.conj f).toMonoidHom := by
    rw [hHdef, Subgroup.closure_le]
    intro x hx
    change β x = MulAut.conj f x
    rw [MulAut.conj_apply]
    rcases hx with rfl | rfl
    · exact hfa
    · exact hfb
  have := hle (hEH hd)
  change β d = MulAut.conj f d at this
  rwa [MulAut.conj_apply] at this

theorem conj_eq_of_mem_center {r : ℕ} [Fact r.Prime]
    (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) (hE : IsPOnePlusTwo r ↥(CFSG.pCore r X))
    {w : X} (hw : w ∈ CFSG.pCore r X) (hwc : ∀ e ∈ CFSG.pCore r X, w * e = e * w) (y : X) :
    y * w * y⁻¹ = w := by
  obtain ⟨hex, -, -⟩ := hE
  set E := CFSG.pCore r X
  set Z : Subgroup X := (Subgroup.center ↥E).map E.subtype with hZ
  have hZmem : ∀ v, v ∈ Z ↔ v ∈ E ∧ ∀ e ∈ E, v * e = e * v := by
    intro v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, fun e he => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hu ⟨e, he⟩)).symm⟩
    · rintro ⟨hv, hvc⟩
      exact ⟨⟨v, hv⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hvc g g.2).symm, rfl⟩
  have hZn : Z.Normal := ⟨fun v hv g => by
    rw [hZmem] at hv ⊢
    obtain ⟨hvE, hvc⟩ := hv
    refine ⟨Subgroup.Normal.conj_mem CFSG.pCore_normal v hvE g, fun e he => ?_⟩
    have he' : g⁻¹ * e * g ∈ E := by
      have := Subgroup.Normal.conj_mem CFSG.pCore_normal e he g⁻¹
      rwa [inv_inv] at this
    have h1 := hvc _ he'
    calc g * v * g⁻¹ * e = g * (v * (g⁻¹ * e * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * e * g) * v) * g⁻¹ := by rw [h1]
      _ = e * (g * v * g⁻¹) := by group⟩
  have hcardZ : Nat.card Z = r := by
    rw [hZ, Subgroup.card_map_of_injective E.subtype_injective]
    exact IsExtraspecial.center_order_p r ↥E
  have : IsCyclic Z := isCyclic_of_prime_card hcardZ
  let ρ : X →* (ZMod (Nat.card Z))ˣ :=
    (IsCyclic.mulAutMulEquiv Z).toMonoidHom.comp (MulAut.conjNormal (H := Z))
  have hy : y ∈ commutator X := by
    rw [commutator_def, hX]
    exact Subgroup.mem_top y
  have hρ : ρ y = 1 := Abelianization.commutator_subset_ker ρ hy
  have h1 : MulAut.conjNormal (H := Z) y = 1 := by
    apply (IsCyclic.mulAutMulEquiv Z).injective
    rw [map_one]
    exact hρ
  have h2 := congrArg (fun α : MulAut Z => ((α ⟨w, (hZmem w).mpr ⟨hw, hwc⟩⟩ : Z) : X)) h1
  simpa [MulAut.conjNormal_apply] using h2

end CFSG.Quasithin.Vol2.Ch11.O6
