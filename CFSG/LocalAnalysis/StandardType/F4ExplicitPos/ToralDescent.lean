module

public import CFSG.HardMathSupport.Timmesfeld.Torality.DescentCongruence
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedTorus
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FiniteCountsPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.ToralDescent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RootBaseChange

variable {τ : Tag} {R S : Type} [Field R] [Field S]

theorem bcGL_mem_monomialSubgroup
    (f : R →+* S) {g : ModGL τ R}
    (hg : g ∈ monomialSubgroup τ R) : bcGL f g ∈ monomialSubgroup τ S := by
  have hle : monomialSubgroup τ R ≤ (monomialSubgroup τ S).comap (bcGL f) := by
    rw [monomialSubgroup, sup_le_iff, torusGroup, Subgroup.closure_le, Subgroup.closure_le]
    constructor
    · rintro _ ⟨⟨i, t⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, FixedTorus.bcGL_torusElt]
      exact torusElt_mem_monomialSubgroup i _
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, bcGL_weylElt]
      simpa using weylElt_mem_monomialSubgroup (τ := τ) (R := S) i
  exact hle hg

theorem exists_finset_descent
    {τ : Tag} {k : Type} [Field k] {x : ModGL τ k}
    (hx : x ∈ adjointGroup τ k) :
    ∃ E : Finset k, ∀ K : Subfield k, (E : Set k) ⊆ K →
      ∃ y ∈ adjointGroup τ K, bcGL K.subtype y = x := by
  classical
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, c, hc | hc⟩ := hg
    · refine ⟨{c}, fun K hK =>
        ⟨xUnit τ K i ⟨c, hK (Finset.mem_coe.2 (Finset.mem_singleton_self c))⟩,
          xUnit_mem_adjointGroup i _, ?_⟩⟩
      rw [bcGL_xUnit]
      exact Units.ext hc.symm
    · refine ⟨{c}, fun K hK =>
        ⟨yUnit τ K i ⟨c, hK (Finset.mem_coe.2 (Finset.mem_singleton_self c))⟩,
          yUnit_mem_adjointGroup i _, ?_⟩⟩
      rw [bcGL_yUnit]
      exact Units.ext hc.symm
  | one => exact ⟨∅, fun K _ => ⟨1, one_mem _, map_one _⟩⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨E₁, h₁⟩ := ihg
    obtain ⟨E₂, h₂⟩ := ihh
    refine ⟨E₁ ∪ E₂, fun K hK => ?_⟩
    rw [Finset.coe_union, Set.union_subset_iff] at hK
    obtain ⟨y₁, hy₁, e₁⟩ := h₁ K hK.1
    obtain ⟨y₂, hy₂, e₂⟩ := h₂ K hK.2
    exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, by rw [map_mul, e₁, e₂]⟩
  | inv g _ ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨E, fun K hK => ?_⟩
    obtain ⟨y, hy, e⟩ := hE K hK
    exact ⟨y⁻¹, inv_mem hy, by rw [map_inv, e]⟩

theorem comap_le_adjointGroup {K₁ L : Type} [Field K₁] [Field L] (ι : K₁ →+* L)
    (hι : Function.Injective ι) {B : Subgroup (ModGL τ L)}
    (hdesc : ∀ x ∈ B, ∃ y ∈ adjointGroup τ K₁, bcGL ι y = x) :
    B.comap (bcGL ι) ≤ adjointGroup τ K₁ := by
  intro y hy
  obtain ⟨y', hy', e⟩ := hdesc _ hy
  rw [← bcGL_injective ι hι e]
  exact hy'

theorem isPGroup_comap {K₁ L : Type} [Field K₁] [Field L] (ι : K₁ →+* L)
    (hι : Function.Injective ι) {p : ℕ} {B : Subgroup (ModGL τ L)}
    (hexp : ∀ x ∈ B, x ^ p = 1) : IsPGroup p (B.comap (bcGL ι)) := by
  rintro ⟨y, hy⟩
  refine ⟨1, Subtype.ext ?_⟩
  apply bcGL_injective ι hι
  rw [pow_one]
  simpa using hexp _ hy

theorem not_dvd_of_modEq_pow {p q M : ℕ} (hp : p.Prime) (hM : 1 ≤ M) (hq : q ≡ 1 [MOD p ^ M]) :
    ¬ p ∣ q := by
  intro h
  have h1 : q % p = 1 % p := Nat.ModEq.of_dvd (dvd_pow_self p (by omega)) hq
  rw [Nat.mod_eq_zero_of_dvd h, Nat.mod_eq_of_lt hp.one_lt] at h1
  exact zero_ne_one h1

theorem exists_descent_subgroup
    {L : Type} [Field L] [IsAlgClosed L] {ℓ r : ℕ} [Fact ℓ.Prime]
    [Fact r.Prime] (hℓr : ℓ ≠ r) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {B : Subgroup (ModGL τ L)} (hB : B ≤ adjointGroup τ L) (hBfin : (B : Set (ModGL τ L)).Finite)
    (E₀ : Finset L) {M : ℕ} (hM : 1 ≤ M) :
    ∃ K₁ : Subfield L, Finite K₁ ∧ (E₀ : Set L) ⊆ K₁ ∧ Nat.card K₁ ≡ 1 [MOD r ^ M] ∧
      ∀ x ∈ B, ∃ y ∈ adjointGroup τ K₁, bcGL K₁.subtype y = x := by
  classical
  let F : ModGL τ L → Finset L := fun x =>
    if hx : x ∈ adjointGroup τ L then (exists_finset_descent hx).choose else ∅
  have hF : ∀ x ∈ B, ∀ K₁ : Subfield L, (F x : Set L) ⊆ K₁ →
      ∃ y ∈ adjointGroup τ K₁, bcGL K₁.subtype y = x := by
    intro x hx K₁ hK₁
    have hxC := hB hx
    have := (exists_finset_descent hxC).choose_spec K₁
    simp only [F, hxC, ↓reduceDIte] at hK₁
    exact this hK₁
  set E : Finset L := E₀ ∪ hBfin.toFinset.biUnion F with hE
  obtain ⟨K₁, hK₁fin, hEK, hK₁q⟩ := exists_finite_subfield_congruence_prime hℓr E
    (fun z _ => halg.isAlgebraic z) hM
  refine ⟨K₁, hK₁fin, fun z hz => hEK (Finset.mem_coe.2 (Finset.mem_union_left _ hz)), hK₁q,
    fun x hx => hF x hx K₁ fun z hz => hEK (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨x, hBfin.mem_toFinset.2 hx, hz⟩)))⟩

theorem units_map_prod_zpow {n : ℕ} (φ : R →+* S) (a : Fin n → Rˣ)
    (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    Units.map φ.toMonoidHom (∏ j, a j ^ B j i) =
      ∏ j, (Units.map φ.toMonoidHom (a j)) ^ B j i := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => map_zpow _ _ _

theorem bcGL_rootDiagUnit_F4
    (φ : R →+* S) (a : Fin Tag.F4.rank → Rˣ) :
    bcGL φ (rootDiagUnit Tag.F4 a) =
      rootDiagUnit Tag.F4 (fun i => Units.map φ.toMonoidHom (a i)) := by
  have hB : cartanInvF4 * Tag.F4.cartan = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [rootDiagUnit_eq_list_prod_torusElt (τ := Tag.F4) (K := R) (B := cartanInvF4) hB a,
    rootDiagUnit_eq_list_prod_torusElt (τ := Tag.F4) (K := S) (B := cartanInvF4) hB
      (fun i => Units.map φ.toMonoidHom (a i)),
    map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  rw [Function.comp_apply, CFSG.StandardType.F4ExplicitPos.FixedTorus.bcGL_torusElt,
    units_map_prod_zpow φ a cartanInvF4 i]

section F4

theorem exists_conj_le_monomial_bar
    {L : Type} [Field L] [IsAlgClosed L] {ℓ p : ℕ}
    [Fact ℓ.Prime] [hp : Fact p.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {B : Subgroup (ModGL Tag.F4 L)} (hB : B ≤ adjointGroup Tag.F4 L)
    (hBfin : (B : Set (ModGL Tag.F4 L)).Finite) (hexp : ∀ x ∈ B, x ^ p = 1) :
    ∃ c ∈ adjointGroup Tag.F4 L, ∀ x ∈ B, c * x * c⁻¹ ∈ monomialSubgroup Tag.F4 L := by
  classical
  set M := (Nat.card (WeylGroup Tag.F4)).factorization p + 1 with hM
  have hWM : ¬ p ^ M ∣ Nat.card (WeylGroup Tag.F4) :=
    Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp.out
  obtain ⟨K₁, hK₁, -, hq, hdesc⟩ :=
    exists_descent_subgroup (τ := Tag.F4) hℓ halg hB hBfin ∅ (by omega : 1 ≤ M)
  have : Finite K₁ := hK₁
  have hιinj : Function.Injective K₁.subtype := fun x y h => Subtype.ext h
  have hqp : ¬ p ∣ Nat.card K₁ := not_dvd_of_modEq_pow hp.out (by omega) hq
  obtain ⟨u, hu, hun⟩ :=
    CFSG.StandardType.F4ExplicitPos.FiniteCounts.f4_exists_conj_le_monomial_of_isPGroup
      (K := K₁) hqp hq hWM (comap_le_adjointGroup K₁.subtype hιinj hdesc)
      (isPGroup_comap K₁.subtype hιinj hexp)
  refine ⟨bcGL K₁.subtype u, bcGL_mem_adjointGroup K₁.subtype hu, fun x hx => ?_⟩
  obtain ⟨y, -, rfl⟩ := hdesc x hx
  have h := bcGL_mem_monomialSubgroup K₁.subtype (hun y (by
    change bcGL K₁.subtype y ∈ B
    exact hx))
  rwa [map_mul, map_mul, map_inv] at h

theorem exists_conj_le_monomial_centralizer_bar
    {L : Type} [Field L] [IsAlgClosed L] {ℓ p : ℕ}
    [Fact ℓ.Prime] [hp : Fact p.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) (a : Fin Tag.F4.rank → Lˣ)
    {B : Subgroup (ModGL Tag.F4 L)} (hB : B ≤ adjointGroup Tag.F4 L)
    (hBfin : (B : Set (ModGL Tag.F4 L)).Finite)
    (hBa : ∀ x ∈ B, rootDiagUnit Tag.F4 a * x = x * rootDiagUnit Tag.F4 a)
    (hexp : ∀ x ∈ B, x ^ p = 1) :
    ∃ z ∈ adjointGroup Tag.F4 L, rootDiagUnit Tag.F4 a * z = z * rootDiagUnit Tag.F4 a ∧
      ∀ x ∈ B, z * x * z⁻¹ ∈ monomialSubgroup Tag.F4 L := by
  classical
  set M := (Nat.card (WeylGroup Tag.F4)).factorization p + 1 with hM
  have hWM : ¬ p ^ M ∣ Nat.card (WeylGroup Tag.F4) :=
    Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp.out
  set E₀ : Finset L := Finset.univ.image (fun i => (a i : L)) ∪
    Finset.univ.image (fun i => ((a i)⁻¹ : Lˣ) : Fin Tag.F4.rank → L) with hE₀
  obtain ⟨K₁, hK₁, hE₀K, hq, hdesc⟩ :=
    exists_descent_subgroup (τ := Tag.F4) hℓ halg hB hBfin E₀
      (by omega : 1 ≤ M)
  have : Finite K₁ := hK₁
  have hq3 : ¬ p ∣ Nat.card K₁ := not_dvd_of_modEq_pow hp.out (by omega) hq
  set ι := K₁.subtype with hι
  have hιinj : Function.Injective ι := fun x y h => Subtype.ext h
  have ha1 : ∀ i, (a i : L) ∈ K₁ := fun i =>
    hE₀K (Finset.mem_coe.2 (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  have ha2 : ∀ i, (((a i)⁻¹ : Lˣ) : L) ∈ K₁ := fun i =>
    hE₀K (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun i => ((a i)⁻¹ : Lˣ) : Fin Tag.F4.rank → L)
        (Finset.mem_univ i))))
  let a' : Fin Tag.F4.rank → K₁ˣ := fun i =>
    ⟨⟨a i, ha1 i⟩, ⟨((a i)⁻¹ : Lˣ), ha2 i⟩, Subtype.ext (Units.mul_inv (a i)),
      Subtype.ext (Units.inv_mul (a i))⟩
  have ha' : (fun i => Units.map ι.toMonoidHom (a' i)) = a := by
    funext i
    exact Units.ext rfl
  have hda : bcGL ι (rootDiagUnit Tag.F4 a') = rootDiagUnit Tag.F4 a := by
    rw [bcGL_rootDiagUnit_F4, ha']
  set B' := B.comap (bcGL ι) with hB'
  have hB'C : B' ≤ familyCentralizer Tag.F4 K₁ (fun _ : Unit => a') := by
    intro y hy
    refine mem_familyCentralizer.2 ⟨comap_le_adjointGroup ι hιinj hdesc hy, fun _ => ?_⟩
    apply bcGL_injective ι hιinj
    have h := hBa _ hy
    rw [map_mul, map_mul, map_inv, hda, h, mul_inv_cancel_right]
  obtain ⟨u, hu, hun⟩ :=
    CFSG.StandardType.F4ExplicitPos.FiniteCounts.f4_exists_conj_le_monomial_of_isPGroup_family
      (K := K₁) (a := fun _ : Unit => a') hq3 hq hWM hB'C
      (isPGroup_comap ι hιinj hexp)
  obtain ⟨huC, hud⟩ := mem_familyCentralizer.1 hu
  refine ⟨bcGL ι u, bcGL_mem_adjointGroup ι huC, ?_, fun x hx => ?_⟩
  · have h := congrArg (bcGL ι) (hud ())
    rw [map_mul, map_mul, map_inv, hda] at h
    calc rootDiagUnit Tag.F4 a * bcGL ι u =
          (rootDiagUnit Tag.F4 a * bcGL ι u * (rootDiagUnit Tag.F4 a)⁻¹) *
            rootDiagUnit Tag.F4 a := by group
      _ = bcGL ι u * rootDiagUnit Tag.F4 a := by rw [h]
  · obtain ⟨y, -, rfl⟩ := hdesc x hx
    have h := bcGL_mem_monomialSubgroup ι (Subgroup.mem_inf.1 (hun y (by
      change bcGL ι y ∈ B
      exact hx))).2
    rwa [map_mul, map_mul, map_inv] at h

theorem exists_conj_le_monomial_bar_zmod2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {B : Subgroup (ModGL Tag.F4 L)}
    (hB : B ≤ adjointGroup Tag.F4 L) (hBfin : (B : Set (ModGL Tag.F4 L)).Finite)
    (hexp : ∀ x ∈ B, x ^ p = 1) :
    ∃ c ∈ adjointGroup Tag.F4 L, ∀ x ∈ B, c * x * c⁻¹ ∈ monomialSubgroup Tag.F4 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_conj_le_monomial_bar (ℓ := 2) hp2.symm halg hB hBfin hexp

theorem exists_conj_le_monomial_centralizer_bar_zmod2
    {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (a : Fin Tag.F4.rank → Lˣ) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {B : Subgroup (ModGL Tag.F4 L)} (hB : B ≤ adjointGroup Tag.F4 L)
    (hBfin : (B : Set (ModGL Tag.F4 L)).Finite)
    (hBa : ∀ x ∈ B, rootDiagUnit Tag.F4 a * x = x * rootDiagUnit Tag.F4 a)
    (hexp : ∀ x ∈ B, x ^ p = 1) :
    ∃ z ∈ adjointGroup Tag.F4 L, rootDiagUnit Tag.F4 a * z = z * rootDiagUnit Tag.F4 a ∧
      ∀ x ∈ B, z * x * z⁻¹ ∈ monomialSubgroup Tag.F4 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_conj_le_monomial_centralizer_bar (ℓ := 2) hp2.symm halg a hB hBfin hBa hexp

end F4

end CFSG.StandardType.F4ExplicitPos.ToralDescent

end

end
