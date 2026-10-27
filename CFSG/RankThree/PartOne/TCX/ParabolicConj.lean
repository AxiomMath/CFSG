module

public import CFSG.RankThree.PartOne.TCX.ComplementSylow
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


theorem exists_conj_mem_parabolicLevi_of_normalizes {τ : Tag} {K : Type} [Field K] [Finite K]
    {r p : ℕ} [Fact r.Prime] [CharP K r] (hp : p.Prime) (hpr : p ≠ r)
    {x : adjointGroup τ K} (hx : orderOf x = p) {S : Subgroup (adjointGroup τ K)} (hS : S ≠ ⊥)
    (hSr : IsPGroup r S) (hxS : x ∈ Subgroup.normalizer (S : Set (adjointGroup τ K))) :
    ∃ (J : Set (Fin τ.rank)) (g : adjointGroup τ K), J ≠ Set.univ ∧
      ((g * x * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ parabolicLevi τ K J := by
  classical
  have hfin : Finite (ModGL τ K) := finite_modGL
  obtain ⟨S₂, P, hPtop, hNS, -, -, hS₂⟩ := holds_adjointGroup_tag τ K r S hS hSr
  have hUsyl := isPGroup_and_not_dvd_index r (posUnipotent_le_adjointGroup (τ := τ) (K := K))
    (card_posUnipotent (τ := τ) (K := K))
  set SU : Sylow r (adjointGroup τ K) := hUsyl.1.toSylow hUsyl.2 with hSU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup τ K) SU S₂
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  have hmem : ∀ z : adjointGroup τ K, z ∈ (S₂ : Subgroup (adjointGroup τ K)) ↔
      g⁻¹ * z * g ∈ (SU : Subgroup (adjointGroup τ K)) := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_symm_apply]
  have hSUmem : ∀ z : adjointGroup τ K, z ∈ (SU : Subgroup (adjointGroup τ K)) ↔
      (z : ModGL τ K) ∈ posUnipotent τ K := fun z => Iff.rfl
  have hBP : ∀ b : adjointGroup τ K, (b : ModGL τ K) ∈ borelGroup τ K → g * b * g⁻¹ ∈ P := by
    intro b hb
    apply hS₂
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    have e : g⁻¹ * (g * b * g⁻¹ * y * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * y * g) * b⁻¹ := by
      group
    rw [e, hSUmem, hSUmem]
    have := Subgroup.mem_normalizer_iff.1 (hBN hb) ((g⁻¹ * y * g : adjointGroup τ K) : ModGL τ K)
    simpa using this
  set P' : Subgroup (adjointGroup τ K) := P.comap (MulAut.conj g).toMonoidHom with hP'
  have hP'mem : ∀ y, y ∈ P' ↔ g * y * g⁻¹ ∈ P := fun y => by
    simp [hP', MulAut.conj_apply]
  have hP'top : P' ≠ ⊤ := by
    intro h
    apply hPtop
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : g⁻¹ * y * g ∈ P' := h ▸ Subgroup.mem_top _
    rw [hP'mem] at h1
    simpa [mul_assoc] using h1
  set A : Subgroup (ModGL τ K) := P'.map (adjointGroup τ K).subtype with hA
  have hBA : borelGroup τ K ≤ A := fun b hb =>
    ⟨⟨b, borelGroup_le_adjointGroup' hb⟩, (hP'mem _).2 (hBP _ hb), rfl⟩
  have hAC : A ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  have hAJ := (borel_overgroup_classification τ K).1 A hBA hAC
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ A} with hJ
  have hJne : J ≠ Set.univ := by
    intro hJu
    apply hP'top
    have hAeq : A = adjointGroup τ K := by
      rw [hAJ, hJu]
      refine le_antisymm (parabolicSubgroup_le_adjointGroup τ K _) ?_
      rw [(borel_weyl_generation τ K).1]
      unfold parabolicSubgroup
      refine sup_le_sup_left (Subgroup.closure_mono ?_) _
      rintro _ ⟨i, rfl⟩
      exact ⟨i, Set.mem_univ i, rfl⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (y : ModGL τ K) ∈ A := by
      rw [hAeq]
      exact y.2
    obtain ⟨y', hy', hyy'⟩ := h1
    have h2 : y' = y := Subtype.ext hyy'
    rwa [← h2]
  have hx'P' : g⁻¹ * x * g ∈ P' := by
    rw [hP'mem]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hNS hxS
  have hx'A : ((g⁻¹ * x * g : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J := by
    rw [← hAJ]
    exact ⟨_, hx'P', rfl⟩
  obtain ⟨hQP, hQnorm, -, hMP, hQM, -, hfact, -, -, -, -, -, hpg⟩ :=
    parabolic_root_radical_Levi_factors τ K J
  obtain ⟨hQcard, hQr, -⟩ := hpg r
  set G : Type := ↥(parabolicSubgroup τ K J) with hG
  set N : Subgroup G := (parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J) with hNdef
  set M' : Subgroup G := (parabolicLevi τ K J).subgroupOf (parabolicSubgroup τ K J) with hMdef
  have hNnormal : N.Normal := hQnorm
  have hdisj : N ⊓ M' = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨hyN, hyM⟩ := Subgroup.mem_inf.1 hy
    have h1 : (y : ModGL τ K) ∈ parabolicRadical τ K J ⊓ parabolicLevi τ K J :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyN, Subgroup.mem_subgroupOf.1 hyM⟩
    rw [hQM, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hprod : ∀ g' : G, ∃ n ∈ N, ∃ m ∈ M', g' = n * m := by
    intro g'
    obtain ⟨⟨q, m⟩, ⟨hq, hm, hqm⟩, -⟩ := hfact g' g'.2
    exact ⟨⟨q, hQP hq⟩, Subgroup.mem_subgroupOf.2 hq, ⟨m, hMP hm⟩, Subgroup.mem_subgroupOf.2 hm,
      Subtype.ext hqm⟩
  have hNp : ¬ p ∣ Nat.card N := by
    intro hdvd
    have hNQ : Nat.card N = Nat.card (parabolicRadical τ K J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    obtain ⟨k, hk⟩ := hQr.exists_card_eq
    rw [hNQ, hk] at hdvd
    exact hpr (Nat.prime_dvd_prime_iff_eq hp Fact.out |>.1 (hp.dvd_of_dvd_pow hdvd))
  set x₀ : adjointGroup τ K := g⁻¹ * x * g with hx₀
  set x'' : G := ⟨(x₀ : ModGL τ K), hx'A⟩ with hx''
  have hx''ord : orderOf x'' = p := by
    have h1 : orderOf x₀ = p := by
      rw [← hx]
      have := (MulAut.conj g⁻¹).orderOf_eq x
      simpa [MulAut.conj_apply, hx₀] using this
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, h1]
  obtain ⟨y, hy⟩ := exists_conj_mem_of_complement (G := G) (N := N) (M := M') hdisj hprod hp hNp
    hx''ord
  have hyM : ((y * x'' * y⁻¹ : G) : ModGL τ K) ∈ parabolicLevi τ K J :=
    Subgroup.mem_subgroupOf.1 hy
  let y' : adjointGroup τ K := ⟨(y : ModGL τ K), parabolicSubgroup_le_adjointGroup τ K J y.2⟩
  refine ⟨J, y' * g⁻¹, hJne, ?_⟩
  have e : ((y' * g⁻¹ * x * (y' * g⁻¹)⁻¹ : adjointGroup τ K) : ModGL τ K) =
      ((y * x'' * y⁻¹ : G) : ModGL τ K) := by
    have e1 : y' * g⁻¹ * x * (y' * g⁻¹)⁻¹ = y' * x₀ * y'⁻¹ := by
      simp only [hx₀]
      group
    rw [e1]
    rfl
  rw [e]
  exact hyM

theorem rootDiagUnit_commute_parabolicLevi {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) {J : Set (Fin τ.rank)} (ha : ∀ j ∈ J, a j = 1) {m : ModGL τ K}
    (hm : m ∈ parabolicLevi τ K J) : m * rootDiagUnit τ a = rootDiagUnit τ a * m := by
  have hle : parabolicLevi τ K J ≤ Subgroup.centralizer ({rootDiagUnit τ a} : Set (ModGL τ K)) := by
    refine sup_le (fun h hh => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (rootDiagUnit_mul_comm_of_mem_torusGroup a hh).symm
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        obtain ⟨hx, -, -⟩ := root_diagonal_conjugation τ K a
        have h1 := hx j c
        rw [ha j hj, Units.val_one, one_mul] at h1
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        obtain ⟨-, hy, -⟩ := root_diagonal_conjugation τ K a
        have h1 := hy j c
        rw [ha j hj, inv_one, Units.val_one, one_mul] at h1
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hm)

theorem exists_centralizer_elt_orderOf_of_normalizes {τ : Tag} {K : Type} [Field K] [Finite K]
    {r p : ℕ} [Fact r.Prime] [CharP K r]
    (hT : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ adjointGroup τ K) (hp : p.Prime)
    (hpr : p ≠ r) {x : adjointGroup τ K} (hx : orderOf x = p) {S : Subgroup (adjointGroup τ K)}
    (hS : S ≠ ⊥) (hSr : IsPGroup r S)
    (hxS : x ∈ Subgroup.normalizer (S : Set (adjointGroup τ K))) :
    ∃ z ∈ Subgroup.centralizer ({x} : Set (adjointGroup τ K)), orderOf z = Nat.card K - 1 := by
  classical
  obtain ⟨J, g, hJ, hm⟩ := exists_conj_mem_parabolicLevi_of_normalizes hp hpr hx hS hSr hxS
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  set a : Fin τ.rank → Kˣ := Pi.mulSingle i u with ha
  have haJ : ∀ j ∈ J, a j = 1 := fun j hj => by
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [ha, Pi.mulSingle_eq_of_ne hji]
  set d : adjointGroup τ K := ⟨rootDiagUnit τ a, hT a⟩ with hd
  refine ⟨g⁻¹ * d * g, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 := rootDiagUnit_commute_parabolicLevi a haJ hm
    apply Subtype.ext
    have h2 : ((g * x * g⁻¹ : adjointGroup τ K) : ModGL τ K) * rootDiagUnit τ a =
        rootDiagUnit τ a * ((g * x * g⁻¹ : adjointGroup τ K) : ModGL τ K) := h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
    have h3 : (g : ModGL τ K) * (x : ModGL τ K) * (g : ModGL τ K)⁻¹ * rootDiagUnit τ a =
        rootDiagUnit τ a * ((g : ModGL τ K) * (x : ModGL τ K) * (g : ModGL τ K)⁻¹) := h2
    have h4 : (x : ModGL τ K) * ((g : ModGL τ K)⁻¹ * rootDiagUnit τ a * (g : ModGL τ K)) =
        ((g : ModGL τ K)⁻¹ * rootDiagUnit τ a * (g : ModGL τ K)) * (x : ModGL τ K) := by
      have := congrArg (fun m => (g : ModGL τ K)⁻¹ * m * (g : ModGL τ K)) h3
      simp only [mul_assoc, inv_mul_cancel_left] at this ⊢
      simpa [mul_assoc] using this
    simpa [hd, mul_assoc] using h4.symm
  · have h1 : orderOf (g⁻¹ * d * g) = orderOf d := by
      have := (MulAut.conj g⁻¹).orderOf_eq d
      simpa [MulAut.conj_apply] using this
    have h3 : orderOf (rootDiagUnit τ a) = orderOf a :=
      orderOf_injective (rootDiagUnitHom τ K) rootDiagUnit_injective a
    rw [h1, hd, Subgroup.orderOf_mk, h3]
    have h2 : orderOf a = orderOf u := by
      have := orderOf_injective (MonoidHom.mulSingle (fun _ : Fin τ.rank => Kˣ) i)
        (Pi.mulSingle_injective (M := fun _ : Fin τ.rank => Kˣ) i) u
      simpa [ha] using this
    rw [h2, hu, Nat.card_units]

end CFSG.RankThree.PartOne.TCX
