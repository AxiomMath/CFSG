module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.GroupTheory.CentralCoverTorus
public import CFSG.LinearAlgebra.CubeRootBlockSymmetric
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open scoped MatrixGroups

theorem factorization_card_statedSp_three {F : Type} [Field F] [Finite F] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : 5 ≤ r) (hdvd : r ∣ Nat.card F - 1) :
    (Nat.card (StatedSp 3 F)).factorization r = 3 * (Nat.card F - 1).factorization r := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqne : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have hq1 : Nat.card F - 1 ≠ 0 := by omega
  have hnq : ¬ r ∣ Nat.card F := by
    intro h
    have h1 : r ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub h hdvd
    rw [Nat.sub_sub_self hq.le] at h1
    exact hr.not_dvd_one h1
  have hnr2 : ¬ r ∣ 2 := by
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  have hn4 : ¬ r ∣ 4 := fun h => hnr2 (hr.dvd_of_dvd_pow (n := 2) (by simpa using h))
  have hn6 : ¬ r ∣ 6 := by
    intro h
    rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
    rcases (hr.dvd_mul.mp h) with h2 | h3
    · exact hnr2 h2
    · exact (by omega : r ≠ 3) ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h3)
  have h2 : (Nat.card F ^ 2 - 1).factorization r = (Nat.card F - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq hdvd
      (by norm_num : 2 ≠ 0), Nat.factorization_eq_zero_of_not_dvd hnr2, add_zero]
  have h4 : (Nat.card F ^ 4 - 1).factorization r = (Nat.card F - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq hdvd
      (by norm_num : 4 ≠ 0), Nat.factorization_eq_zero_of_not_dvd hn4, add_zero]
  have h6 : (Nat.card F ^ 6 - 1).factorization r = (Nat.card F - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq hdvd
      (by norm_num : 6 ≠ 0), Nat.factorization_eq_zero_of_not_dvd hn6, add_zero]
  have h9 : (Nat.card F ^ 9).factorization r = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hnq, mul_zero]
  have hne2 : Nat.card F ^ 2 - 1 ≠ 0 := by
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (a := Nat.card F) (n := 2) (by omega) hq
    omega
  have hne4 : Nat.card F ^ 4 - 1 ≠ 0 := by
    have : 1 < Nat.card F ^ 4 := Nat.one_lt_pow (a := Nat.card F) (n := 4) (by omega) hq
    omega
  have hne6 : Nat.card F ^ 6 - 1 ≠ 0 := by
    have : 1 < Nat.card F ^ 6 := Nat.one_lt_pow (a := Nat.card F) (n := 6) (by omega) hq
    omega
  rw [card_statedSp]
  have hIcc : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num, show 2 * 1 = 2 by norm_num,
    show 2 * 2 = 4 by norm_num, show 2 * 3 = 6 by norm_num]
  rw [Nat.factorization_mul (pow_ne_zero _ hqne)
    (mul_ne_zero hne2 (mul_ne_zero hne4 hne6)), Finsupp.add_apply]
  rw [Nat.factorization_mul hne2 (mul_ne_zero hne4 hne6), Finsupp.add_apply,
    Nat.factorization_mul hne4 hne6, Finsupp.add_apply]
  rw [h9, h2, h4, h6]
  ring

theorem exists_cover_sp6 {K : Type} [Group K] {f : ℕ}
    (hK : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp 3 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
      ∃ φ : K →* StatedSp 3 F, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center K := by
  obtain ⟨F, hF, hFin, hChar, hFcard, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel
      (L := K ⧸ Subgroup.center K) hK
  letI := hF
  letI := hFin
  letI := hChar
  let ψ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let φ : K →* StatedSp 3 F := e.toMonoidHom.comp ψ
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact ⟨F, hF, hFin, hChar, hFcard, φ, hφ, hker⟩

private theorem exists_sylow_closure_sp6 {F : Type} [Field F] [Finite F] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : 5 ≤ r) (hrd : r ∣ Nat.card F - 1) :
    ∃ (S : Set (StatedSp 3 F)) (D : Sylow r (StatedSp 3 F)),
      (D : Subgroup (StatedSp 3 F)) = Subgroup.closure S ∧
      (∀ s ∈ S, ∀ t ∈ S, Commute s t) ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        (∃ c : StatedSp 3 F, c * s * c⁻¹ = s⁻¹ ∧ c * t * c⁻¹ = t) ∨
          (∃ c : StatedSp 3 F, c * t * c⁻¹ = t⁻¹ ∧ c * s * c⁻¹ = s)) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  set a : ℕ := (Nat.card F - 1).factorization r with ha
  have hra : r ^ a ∣ Nat.card F - 1 := by
    rw [ha]
    exact (hr.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  let ζ : Fˣ := g ^ (orderOf g / r ^ a)
  have hζ : orderOf ζ = r ^ a :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' (by rw [hgord]; exact hra)
  let S : Set (StatedSp 3 F) := Set.range fun i : Fin 3 => lam i (sl2Diag ζ)
  have hS_comm : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩
    by_cases hij : i = j
    · subst hij; exact Commute.refl _
    · exact commute_lam_lam hij (sl2Diag ζ) (sl2Diag ζ)
  have hS_odd : ∀ s ∈ S, Odd (orderOf s) := by
    rintro s ⟨i, rfl⟩
    rw [orderOf_lam_sl2Diag, hζ]
    exact (hr.odd_of_ne_two hr2).pow
  have hinv : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (∃ c : StatedSp 3 F, c * s * c⁻¹ = s⁻¹ ∧ c * t * c⁻¹ = t) ∨
        (∃ c : StatedSp 3 F, c * t * c⁻¹ = t⁻¹ ∧ c * s * c⁻¹ = s) := by
    rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ hst
    have hij : i ≠ j := by
      rintro rfl
      exact hst rfl
    have hc : Commute (lam i (sl2W : SpecialLinearGroup (Fin 2) F)) (lam j (sl2Diag ζ)) :=
      commute_lam_lam hij _ _
    refine Or.inl ⟨lam i sl2W, lam_sl2W_conj_lam_sl2Diag i ζ, ?_⟩
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hS_eq : S = Set.range fun i : Fin 3 =>
      torusHom (r := 3) (k := F) (Pi.mulSingle i ζ) := by
    simp only [S, lam_sl2Diag]
  have hcardD : Nat.card (Subgroup.closure S) = (r ^ a) ^ 3 := by
    rw [hS_eq, ← hζ]
    exact card_closure_single_torusHom 3 ζ
  have hcardD' : Nat.card (Subgroup.closure S) = r ^ (3 * a) := by
    rw [hcardD, ← pow_mul, Nat.mul_comm]
  have hDpg : IsPGroup r (Subgroup.closure S) := IsPGroup.of_card (n := 3 * a) hcardD'
  have hrpow : (r ^ a).factorization r = a := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hr.factorization_self, mul_one]
  have hDfac : (Nat.card (Subgroup.closure S)).factorization r = 3 * a := by
    rw [hcardD, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hrpow]
  have hfac : (Nat.card (StatedSp 3 F)).factorization r =
      (Nat.card (Subgroup.closure S)).factorization r := by
    rw [factorization_card_statedSp_three hr hr2 hr5 hrd, hDfac]
  haveI : Fact r.Prime := ⟨hr⟩
  have hidx : ¬ r ∣ (Subgroup.closure S).index :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.not_dvd_index_of_card_eq hr _ hfac
  let D : Sylow r (StatedSp 3 F) := hDpg.toSylow hidx
  have hDcoe : (D : Subgroup (StatedSp 3 F)) = Subgroup.closure S :=
    IsPGroup.toSylow_coe hDpg hidx
  exact ⟨S, D, hDcoe, hS_comm, hS_odd, hinv⟩

theorem k_CartanSylowAbelian_sp6 :
    ∀ (K : Type) [Group K] [Finite K] (f r : ℕ),
      CFSG.Open.StatedLieAdmissible .PSp 3 2 f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp 3 2 f → CFSG.Open.IsQuasisimple K →
          Odd (Nat.card (Subgroup.center K)) → r.Prime → 5 ≤ r → r ∣ 2 ^ f - 1 →
            ∀ P : Sylow r K, IsMulCommutative (P : Subgroup K) := by
  intro K _ _ f r hAdm hK hQ hOddC hr hr5 hrdvd P
  obtain ⟨F, hF, hFin, hChar, hFcard, φ, hφ, hker⟩ := exists_cover_sp6 hK
  letI := hF
  letI := hFin
  have hq : Nat.card F = 2 ^ f := hFcard
  have hr2 : r ≠ 2 := by omega
  haveI : Fact r.Prime := ⟨hr⟩
  have hrdvd' : r ∣ Nat.card F - 1 := by rw [hq]; exact hrdvd
  obtain ⟨S, D, hDcoe, hS_comm, hS_odd, hinv⟩ :=
    exists_sylow_closure_sp6 (F := F) hr hr2 hr5 hrdvd'
  have hcomm := CFSG.GroupTheory.comap_closure_comm_of_inverters (φ := φ) hφ hker
    hS_comm hS_odd hinv
  have hDcomm : ∀ a ∈ (D : Subgroup (StatedSp 3 F)).comap φ,
      ∀ b ∈ (D : Subgroup (StatedSp 3 F)).comap φ, a * b = b * a := by
    rw [hDcoe]
    exact hcomm
  exact CFSG.GroupTheory.isMulCommutative_sylow_of_comap_comm hφ D hDcomm P

private theorem closure_lam_diag_eq_map_sp6 {F : Type} [Field F] {ζ : Fˣ} :
    Subgroup.closure
        ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} : Set (StatedSp 3 F)) =
      (Subgroup.pi Set.univ (fun i : Fin 3 =>
        (if i ∈ ({0, 1} : Finset (Fin 3)) then Subgroup.zpowers ζ else ⊥ :
          Subgroup Fˣ))).map (torusHom (r := 3) (k := F)) := by
  have hset : (torusHom (r := 3) (k := F)) ''
      Set.range (fun i : {i : Fin 3 // i ∈ ({0, 1} : Finset (Fin 3))} =>
        (Pi.mulSingle (M := fun _ : Fin 3 => Fˣ) (i : Fin 3) ζ)) =
      ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} : Set (StatedSp 3 F)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      have hi : (i : Fin 3) = 0 ∨ (i : Fin 3) = 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using i.2
      rcases hi with h | h
      · change torusHom (r := 3) (k := F) (Pi.mulSingle (i : Fin 3) ζ) ∈
          ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} : Set (StatedSp 3 F))
        rw [h]
        exact Or.inl (lam_sl2Diag 0 ζ).symm
      · change torusHom (r := 3) (k := F) (Pi.mulSingle (i : Fin 3) ζ) ∈
          ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} : Set (StatedSp 3 F))
        rw [h]
        exact Or.inr (lam_sl2Diag 1 ζ).symm
    · rintro (rfl | rfl)
      · exact ⟨_, ⟨⟨0, by decide⟩, rfl⟩, (lam_sl2Diag 0 ζ).symm⟩
      · exact ⟨_, ⟨⟨1, by decide⟩, rfl⟩, (lam_sl2Diag 1 ζ).symm⟩
  rw [pi_ite_zpowers_eq_closure, MonoidHom.map_closure, hset]

private theorem card_pow_closure_lam_diag_sp6 {F : Type} [Field F] [Finite F] {r : ℕ}
    {ζ : Fˣ} (hζ : orderOf ζ = r) :
    Nat.card (Subgroup.closure
        ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} : Set (StatedSp 3 F))) = r ^ 2 ∧
      ∀ y ∈ Subgroup.closure
        ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} : Set (StatedSp 3 F)), y ^ r = 1 := by
  rw [closure_lam_diag_eq_map_sp6]
  constructor
  · rw [Subgroup.card_map_of_injective torusHom_injective, card_pi_ite_zpowers, hζ,
      show ({0, 1} : Finset (Fin 3)).card = 2 by decide]
  · intro y hy
    exact pow_eq_one_of_mem_map_pi_ite_zpowers hζ hy

private theorem card_pow_zpowers_lam_two_sp6 {F : Type} [Field F] {p : ℕ}
    {g : SpecialLinearGroup (Fin 2) F} (hg : orderOf g = p) :
    Nat.card (Subgroup.zpowers (lam 2 g : StatedSp 3 F)) = p ∧
      ∀ y ∈ Subgroup.zpowers (lam 2 g : StatedSp 3 F), y ^ p = 1 := by
  constructor
  · rw [Nat.card_zpowers, orderOf_lam, hg]
  · intro y hy
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hy).trans
      (by rw [orderOf_lam, hg]))

private theorem odd_orderOf_lam_sl2Diag_sp6 {F : Type} [Field F] {r : ℕ}
    {ζ : Fˣ} (hr : r.Prime) (hr2 : r ≠ 2) (hζ : orderOf ζ = r) :
    Odd (orderOf (lam 0 (sl2Diag ζ) : StatedSp 3 F)) ∧
      Odd (orderOf (lam 1 (sl2Diag ζ) : StatedSp 3 F)) := by
  have h : Odd r := hr.odd_of_ne_two hr2
  constructor <;> rw [orderOf_lam_sl2Diag, hζ] <;> exact h

private theorem commute_odd_insert_sp6 {F : Type} [Field F] {p r : ℕ}
    {ζ : Fˣ} {g : SpecialLinearGroup (Fin 2) F}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hζ : orderOf ζ = r) (hg : orderOf g = p) :
    (∀ a ∈ ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ), lam 2 g} : Set (StatedSp 3 F)),
      ∀ b ∈ ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ), lam 2 g} : Set (StatedSp 3 F)),
        Commute a b) ∧
      ∀ a ∈ ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ), lam 2 g} : Set (StatedSp 3 F)),
        Odd (orderOf a) := by
  have hcomm01 : Commute (lam 0 (sl2Diag ζ) : StatedSp 3 F) (lam 1 (sl2Diag ζ)) :=
    commute_lam_lam (by decide : (0 : Fin 3) ≠ 1) _ _
  have hcomm0x : Commute (lam 0 (sl2Diag ζ) : StatedSp 3 F) (lam 2 g) :=
    commute_lam_lam (by decide : (0 : Fin 3) ≠ 2) _ _
  have hcomm1x : Commute (lam 1 (sl2Diag ζ) : StatedSp 3 F) (lam 2 g) :=
    commute_lam_lam (by decide : (1 : Fin 3) ≠ 2) _ _
  have hodd := odd_orderOf_lam_sl2Diag_sp6 hr hr2 hζ
  have hoddx : Odd (orderOf (lam 2 g : StatedSp 3 F)) := by
    rw [orderOf_lam, hg]
    exact hp.odd_of_ne_two hp2
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact Commute.refl _
    · exact hcomm01
    · exact hcomm0x
    · exact hcomm01.symm
    · exact Commute.refl _
    · exact hcomm1x
    · exact hcomm0x.symm
    · exact hcomm1x.symm
    · exact Commute.refl _
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hodd.1
    · exact hodd.2
    · exact hoddx

private theorem inverter_insert_sp6 {F : Type} [Field F] {ζ : Fˣ}
    {g : SpecialLinearGroup (Fin 2) F}
    (hgsym : (g : Matrix (Fin 2) (Fin 2) F)ᵀ = (g : Matrix (Fin 2) (Fin 2) F)) :
    ∀ a ∈ ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ), lam 2 g} : Set (StatedSp 3 F)),
      ∀ b ∈ ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ), lam 2 g} : Set (StatedSp 3 F)),
        a ≠ b →
        (∃ c : StatedSp 3 F, c * a * c⁻¹ = a⁻¹ ∧ c * b * c⁻¹ = b) ∨
          (∃ c : StatedSp 3 F, c * b * c⁻¹ = b⁻¹ ∧ c * a * c⁻¹ = a) := by
  have hcentral : ∀ (i j : Fin 3) (hij : i ≠ j) (u : SpecialLinearGroup (Fin 2) F),
      lam i (sl2W : SpecialLinearGroup (Fin 2) F) * lam j u *
        (lam i (sl2W : SpecialLinearGroup (Fin 2) F))⁻¹ = lam j u := by
    intro i j hij u
    have hc : Commute (lam i (sl2W : SpecialLinearGroup (Fin 2) F)) (lam j u) :=
      commute_lam_lam hij _ _
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hinvx : (lam 2 (sl2W : SpecialLinearGroup (Fin 2) F) : StatedSp 3 F) * lam 2 g *
      (lam 2 (sl2W : SpecialLinearGroup (Fin 2) F))⁻¹ = (lam 2 g)⁻¹ :=
    lam_sl2W_conj_eq_inv_of_transpose 2 hgsym
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · refine Or.inl ⟨lam 0 sl2W, lam_sl2W_conj_lam_sl2Diag 0 ζ,
      hcentral 0 1 (by decide) (sl2Diag ζ)⟩
  · refine Or.inl ⟨lam 0 sl2W, lam_sl2W_conj_lam_sl2Diag 0 ζ,
      hcentral 0 2 (by decide) g⟩
  · refine Or.inl ⟨lam 1 sl2W, lam_sl2W_conj_lam_sl2Diag 1 ζ,
      hcentral 1 0 (by decide) (sl2Diag ζ)⟩
  · exact absurd rfl hab
  · refine Or.inl ⟨lam 1 sl2W, lam_sl2W_conj_lam_sl2Diag 1 ζ,
      hcentral 1 2 (by decide) g⟩
  · exact Or.inl ⟨lam 2 sl2W, hinvx, hcentral 2 0 (by decide) (sl2Diag ζ)⟩
  · exact Or.inl ⟨lam 2 sl2W, hinvx, hcentral 2 1 (by decide) (sl2Diag ζ)⟩
  · exact absurd rfl hab

private theorem sup_le_closure_sp6 {F : Type} [Field F] {ζ : Fˣ}
    {g : SpecialLinearGroup (Fin 2) F} :
    Subgroup.closure ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} : Set (StatedSp 3 F)) ⊔
        Subgroup.zpowers (lam 2 g : StatedSp 3 F) ≤
      Subgroup.closure ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ), lam 2 g} :
        Set (StatedSp 3 F)) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)

theorem k_RankThreeCentTorus_sp6 :
    ∀ (K : Type) [Group K] [Finite K] (f p r : ℕ),
      CFSG.Open.StatedLieAdmissible .PSp 3 2 f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp 3 2 f → CFSG.Open.IsQuasisimple K →
          Odd (Nat.card (Subgroup.center K)) → Odd f →
            p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 → r.Prime → 5 ≤ r → r ∣ 2 ^ f - 1 →
              ∃ E : Subgroup K, CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
                1 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Subgroup.centralizer (E : Set K))) := by
  intro K _ _ f p r hAdm hK hQ hOddC hf hp hp2 hpdvd hr hr5 hrdvd
  obtain ⟨F, hF, hFin, hChar, hFcard, φ, hφ, hker⟩ := exists_cover_sp6 hK
  letI := hF
  letI := hFin
  letI := hChar
  have hq : Nat.card F = 2 ^ f := hFcard
  have hr2 : r ≠ 2 := by omega
  have hrdvd' : r ∣ Nat.card F - 1 := by rw [hq]; exact hrdvd
  have hpdvd' : p ∣ Nat.card F + 1 := by rw [hq]; exact hpdvd
  have hmod : Nat.card F % 3 = 2 := by rw [hq]; exact CFSG.two_pow_mod_three_of_odd hf
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rwa [Nat.card_units])
  obtain ⟨g, hgsym, hgord⟩ :=
    CFSG.LinearAlgebra.exists_symmetric_sl2_orderOf_eq hp hp2 hpdvd' hmod
  have hD := card_pow_closure_lam_diag_sp6 (F := F) hζ
  have hE := card_pow_zpowers_lam_two_sp6 (g := g) hgord
  have hS := commute_odd_insert_sp6 hp hp2 hr hr2 hζ hgord
  have hinv := inverter_insert_sp6 (ζ := ζ) hgsym
  have hcommS := CFSG.GroupTheory.comap_closure_comm_of_inverters (φ := φ) hφ hker
    hS.1 hS.2 hinv
  have hDEle : Subgroup.closure ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} :
      Set (StatedSp 3 F)) ⊔ Subgroup.zpowers (lam 2 g : StatedSp 3 F) ≤
      Subgroup.closure ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ), lam 2 g} :
        Set (StatedSp 3 F)) := sup_le_closure_sp6
  have hc : ∀ a ∈ (Subgroup.closure ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} :
        Set (StatedSp 3 F)) ⊔ Subgroup.zpowers (lam 2 g : StatedSp 3 F)).comap φ,
      ∀ b ∈ (Subgroup.closure ({lam 0 (sl2Diag ζ), lam 1 (sl2Diag ζ)} :
        Set (StatedSp 3 F)) ⊔ Subgroup.zpowers (lam 2 g : StatedSp 3 F)).comap φ,
        a * b = b * a := by
    intro a ha b hb
    exact hcommS a (Subgroup.comap_mono hDEle ha) b (Subgroup.comap_mono hDEle hb)
  exact CFSG.GroupTheory.exists_elemAbelian_le_pRank_centralizer_of_comap_comm
    (φ := φ) hφ hker hr hr2 hp hp2 hD.2 hE.2 hc
    (a := 2) (b := 1) (by rw [hD.1]) (by rw [hE.1, pow_one])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
