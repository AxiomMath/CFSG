module

public import CFSG.Timmesfeld.ARS.CaseENodeLemma
public import CFSG.Timmesfeld.ARS.SimplyLacedConfigA

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem frame_of_surjective {Δ' : Set (Subgroup G)}
    (hinv : ∀ X ∈ Δ', ∀ v ∈ gen Δ', conjSub X v ∈ Δ') {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅) {adj : Fin D.rank → Fin D.rank → Prop}
    {P Q : Fin D.rank → Subgroup G} (hX : IsConfig R adj P Q) (hPQ : ∀ k, P k ∈ Δ' ∧ Q k ∈ Δ')
    (Ψ₀ : K →* ↥(gen Δ'))
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ₀ = (P k).subgroupOf (gen Δ'))
    (hQ : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ₀ = (Q k).subgroupOf (gen Δ'))
    (hsurj : Function.Surjective Ψ₀) :
    (∀ k, (D.rootGroup (Pi.single k 1)).map ((gen Δ').subtype.comp Ψ₀) = P k) ∧
      (∀ k, (D.rootGroup (-Pi.single k 1)).map ((gen Δ').subtype.comp Ψ₀) = Q k) ∧
      (∀ γ ∈ D.roots, (D.rootGroup γ).map ((gen Δ').subtype.comp Ψ₀) ∈ Δ') ∧
      (∀ g, (gen Δ').subtype.comp Ψ₀ g ∈ gen Δ') ∧
      (∀ v ∈ gen Δ', ∃ g, (gen Δ').subtype.comp Ψ₀ g = v) ∧
      (∀ k, Opposite ((D.rootGroup (Pi.single k 1)).map ((gen Δ').subtype.comp Ψ₀))
        ((D.rootGroup (-Pi.single k 1)).map ((gen Δ').subtype.comp Ψ₀))) := by
  set Ψ := (gen Δ').subtype.comp Ψ₀ with hΨ
  have hP' : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ = P k := fun k => by
    rw [hΨ, ← Subgroup.map_map, hP k, Subgroup.map_subgroupOf_eq_of_le (le_gen (hPQ k).1)]
  have hQ' : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ = Q k := fun k => by
    rw [hΨ, ← Subgroup.map_map, hQ k, Subgroup.map_subgroupOf_eq_of_le (le_gen (hPQ k).2)]
  have hrange : ∀ g, Ψ g ∈ gen Δ' := fun g => (Ψ₀ g).2
  refine ⟨hP', hQ', fun γ hγ => ?_, hrange, fun v hv => ?_, fun k => ?_⟩
  · obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single hdiv hγ
    rw [← actsAs_nrep hct w _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i),
      ← map_conjSub_eq, hP' i]
    exact hinv _ (hPQ i).1 _ (hrange _)
  · obtain ⟨g, hg⟩ := hsurj ⟨v, hv⟩
    exact ⟨g, by simp [Ψ, hg]⟩
  · rw [hP' k, hQ' k]
    exact hX.opp k

theorem leviFrame_of_surjective (hR : IsRootClass R) {A A₀ : Subgroup G} {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅) {adj : Fin D.rank → Fin D.rank → Prop}
    {P Q : Fin D.rank → Subgroup G} (hX : IsConfig R adj P Q)
    (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀) (Ψ₀ : K →* ↥(levi R A A₀))
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ₀ = (P k).subgroupOf (levi R A A₀))
    (hQ : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ₀ = (Q k).subgroupOf (levi R A A₀))
    (hsurj : Function.Surjective Ψ₀) :
    LeviFrame R A A₀ D n H ((levi R A A₀).subtype.comp Ψ₀) ∧
      (∀ k, (D.rootGroup (Pi.single k 1)).map ((levi R A A₀).subtype.comp Ψ₀) = P k) ∧
      (∀ k, (D.rootGroup (-Pi.single k 1)).map ((levi R A A₀).subtype.comp Ψ₀) = Q k) := by
  obtain ⟨hP', hQ', hmem, hrange, hsurj', hopp⟩ := frame_of_surjective (Δ' := leviSet R A A₀)
    (fun X hX v hv => Levi.conjSub_mem_leviSet_of_mem_levi hR hX hv) hct hdiv hX hPQ Ψ₀ hP hQ
    hsurj
  refine ⟨⟨⟨hct, hext, hdiv, hmem, hrange, fun v hv => ?_, hopp⟩, hsurj'⟩, hP', hQ'⟩
  obtain ⟨g, hg⟩ := hsurj' v hv
  exact ⟨g, 1, fun y => Commute.one_left _, by rw [mul_one]; exact hg.symm⟩


namespace CaseE

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.Timmesfeld

theorem adj_A {m : ℕ} (a b : Fin m) (h : CartanMatrix.A m a b = -1) :
    edgeA m a b ∨ edgeA m b a := by
  simp only [CartanMatrix.A, Matrix.of_apply] at h
  show b.val = a.val + 1 ∨ a.val = b.val + 1
  split_ifs at h
  omega

theorem adj_D {n : ℕ} (a b : Fin n) (h : Spin.cartanD n a b = -1) :
    edgeD n a b ∨ edgeD n b a := by
  rw [LevisSpin.cartanD_apply] at h
  unfold edgeD
  split_ifs at h
  omega

theorem adj_E6 (a b : Fin 6) (h : Tag.cartan .E6 a b = -1) :
    edgeE 6 a b ∨ edgeE 6 b a := by
  fin_cases a <;> fin_cases b <;>
    first | (left; decide) | (right; decide) | (exfalso; revert h; decide)

theorem adj_E7 (a b : Fin 7) (h : Tag.cartan .E7 a b = -1) :
    edgeE 7 a b ∨ edgeE 7 b a := by
  fin_cases a <;> fin_cases b <;>
    first | (left; decide) | (right; decide) | (exfalso; revert h; decide)

theorem adj_E8 (a b : Fin 8) (h : Tag.cartan .E8 a b = -1) :
    edgeE 8 a b ∨ edgeE 8 b a := by
  fin_cases a <;> fin_cases b <;>
    first | (left; decide) | (right; decide) | (exfalso; revert h; decide)

theorem posDef_D (n : ℕ) : ((Spin.cartanD n).map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [Spin.cartanD_eq]
  exact TauCeti.posDef_map_intCast_cartanMatrix_D n

theorem posDef_E8 : ((Tag.cartan .E8).map (Int.cast : ℤ → ℚ)).PosDef := by
  have e : Tag.cartan .E8 = CartanMatrix.E 8 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [e]
  exact TauCeti.posDef_map_intCast_cartanMatrix_E8

theorem highest_mem_A {m : ℕ} (hm : 1 ≤ m) (F : Type) [Field F] :
    (fun _ => 1 : Fin m → ℤ) ∈ (SpecialLinear.rootDatum m F).roots := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : 0 < m := by omega
  have e := SpecialLinear.roots_eq m
  refine (Set.ext_iff.1 e _).2 ⟨0, Fin.last m, fun e => ?_, funext fun a => ?_⟩
  · have := congrArg Fin.val e
    simp at this
    omega
  · simp only [SpecialLinear.toStd, Pi.sub_apply, Pi.single_apply]
    rcases Nat.eq_zero_or_pos a.val with h0 | h0
    · have ha : a = 0 := Fin.ext h0
      simp [ha, hm0, hm1]
    · have h0' : a ≠ 0 := fun e => by
        rw [e] at h0
        simp at h0
      by_cases hl : a.val = m
      · have ha : a = Fin.last m := Fin.ext hl
        simp [ha, hm0, hm1]
      · have hl' : a ≠ Fin.last m := fun e => hl (by rw [e]; simp)
        have hlt : a.val < m := by omega
        simp [h0', hl', hlt, h0]

@[expose] def highestD (n : ℕ) (k : Fin n) : ℤ :=
  if k.val = 0 ∨ k.val + 2 = n ∨ k.val + 1 = n then 1 else 2

theorem one_le_highestD {n : ℕ} (k : Fin n) : 1 ≤ highestD n k := by
  unfold highestD
  split_ifs <;> omega

theorem highestD_mem {n : ℕ} (hn : 4 ≤ n) (F : Type) [Field F] (hn3 : 3 ≤ n) :
    highestD n ∈ (Spin.plusDatum n F hn3).roots := by
  have e := Spin.rootsD_eq (n := n) (by omega)
  refine (Set.ext_iff.1 e _).2 ⟨⟨0, by omega⟩, ⟨1, by omega⟩, 1, 1,
    fun e => by simpa using congrArg Fin.val e, Or.inl rfl, Or.inl rfl, funext fun a => ?_⟩
  simp only [Spin.toStdD, highestD, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem highest_mem_E6 (F : Type) [Field F] :
    (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) ∈ (Minuscule.e6Datum F).roots := by
  have e := Minuscule.roots_eq Minuscule.isFiniteType_cartan_E6
  refine (Set.ext_iff.1 e _).2 ((RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2
    ⟨70, by rw [Tag.rootCertificate_length]; decide, ?_⟩)
  show Tag.E6.rootCertificate.root 70 = (![1, 2, 2, 3, 2, 1] : Fin (Tag.rank .E6) → ℤ)
  funext i
  fin_cases i <;> rfl

theorem highest_mem_E7 (F : Type) [Field F] :
    (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ) ∈ (Minuscule.e7Datum F).roots := by
  have e := Minuscule.roots_eq Minuscule.isFiniteType_cartan_E7
  refine (Set.ext_iff.1 e _).2 ((RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2
    ⟨124, by rw [Tag.rootCertificate_length]; decide, ?_⟩)
  show Tag.E7.rootCertificate.root 124 = (![2, 2, 3, 4, 3, 2, 1] : Fin (Tag.rank .E7) → ℤ)
  funext i
  fin_cases i <;> rfl

theorem highest_mem_E8 (F : Type) [Field F] :
    (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) ∈ (Adjoint.e8Datum F).roots := by
  have e := Adjoint.roots_eq_setOf_isRoot (τ := .E8) (Adjoint.e8Datum F).isFiniteType
  refine (Set.ext_iff.1 e _).2 ((RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2
    ⟨238, by rw [Tag.rootCertificate_length]; decide, ?_⟩)
  show Tag.E8.rootCertificate.root 238 = (![2, 3, 4, 6, 5, 4, 3, 2] : Fin (Tag.rank .E8) → ℤ)
  funext i
  fin_cases i <;> rfl

theorem one_le_highest_E6 : ∀ i : Fin 6, 1 ≤ (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) i := by decide

theorem one_le_highest_E7 : ∀ i : Fin 7, 1 ≤ (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ) i := by
  decide

theorem one_le_highest_E8 : ∀ i : Fin 8, 1 ≤ (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) i := by
  decide

theorem eq_of_highest_E6 (j : Fin 6) (h : (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) j = 1) :
    j.val = 0 ∨ j.val = 5 := by
  revert j
  decide

theorem eq_of_highest_E7 (j : Fin 7) (h : (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ) j = 1) :
    j.val = 6 := by
  revert j
  decide

theorem ne_one_highest_E8 (j : Fin 8) (h : (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) j = 1) :
    False := by
  revert j
  decide

end CaseE

section Node

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem exists_caseENode_of_leviFrame (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}
    (hF : LeviFrame R A A₀ D n H Ψ) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {θ : Fin D.rank → ℤ}
    (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i) :
    ∃ j, θ j = 1 ∧ ∃ E F, CaseENode R A A₀ (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ) E F j := by
  obtain ⟨E, hE, hEU⟩ := exists_mem_lambdaStar_commuting_negUnipotent h hA hAne hA₀ hF.hext
    hF.hdiv Ψ hF.mem
  obtain ⟨j, hθj, hj⟩ := exists_eq_of_highest h hA hAne hmax hA₀ hF.toCompFrame hpd hE hEU hX
    hadj hθ hθ1 hF.surj
  obtain ⟨F, hN⟩ := exists_caseENode h hA hAne hmax hA₀ hF hpd hX hadj hE hEU hj
  exact ⟨j, hθj, E, F, hN⟩

theorem Sec13.exists_caseENode_of_surjective {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
    {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {adj : Fin D.rank → Fin D.rank → Prop}
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {θ : Fin D.rank → ℤ}
    (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i) {P Q : Fin D.rank → Subgroup G}
    (hX : IsConfig R adj P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    (Ψ₀ : K →* ↥(levi R A A₀))
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ₀ = (P k).subgroupOf (levi R A A₀))
    (hQ : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ₀ = (Q k).subgroupOf (levi R A A₀))
    (hsurj : Function.Surjective Ψ₀) :
    ∃ j, θ j = 1 ∧ ∃ E F, CaseENode R A A₀ P Q E F j := by
  obtain ⟨hF, hP', hQ'⟩ := leviFrame_of_surjective hS.hyp.root hct hext hdiv hX hPQ Ψ₀ hP hQ hsurj
  have eP : (fun k => (D.rootGroup (Pi.single k 1)).map ((levi R A A₀).subtype.comp Ψ₀)) = P :=
    funext hP'
  have eQ : (fun k => (D.rootGroup (-Pi.single k 1)).map ((levi R A A₀).subtype.comp Ψ₀)) = Q :=
    funext hQ'
  have hX' := hX
  rw [← eP, ← eQ] at hX'
  obtain ⟨j, hθj, E, F, hN⟩ := exists_caseENode_of_leviFrame hS.hyp hS.mem hS.sec8.2 hS.max
    hS.opp hF hpd hX' hadj hθ hθ1
  rw [eP, eQ] at hN
  exact ⟨j, hθj, E, F, hN⟩

end Node

end CFSG.Timmesfeld.ARS
