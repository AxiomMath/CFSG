module

public import CFSG.Timmesfeld.Exceptional.DeepContra
public import CFSG.Timmesfeld.Exceptional.DeepH

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Certificates

variable {G : Type*} [Group G] {D : Set G}

theorem exists_two_near (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D) {c p : G}
    (hc : c ∈ D) (hp : p ∈ D) (hp4 : p ∈ nbhd D c 4) (hp3 : p ∉ nbhd D c 3) :
    ∃ x : Fin 2 → G, (∀ i, x i ∈ collinearSet D p) ∧ (∀ i, x i ∈ nbhd D c 3) ∧
      x 1 ≠ x 0 ∧ x 1 ≠ p * x 0 := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  obtain ⟨-, y, hy3, hpy⟩ := (mem_nbhd_succ_iff hc).1 hp4
  have hyD := nbhd_subset hc 3 hy3
  have hy2 : y ∉ nbhd D c 2 := fun h => hp3 (mem_nbhd_succ_of_commute hp h hpy)
  have hyp : y ≠ p := fun e => hp3 (e ▸ hy3)
  have hpyD : p * y ∈ D := hNP p hp y hyD hpy (Ne.symm hyp)
  have hTO := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hp).2 hp3
  obtain ⟨-, hodd⟩ := hTO.opposite_self hp
  obtain ⟨e, he, hep, -⟩ := exists_reflection hD hconj hp hc hodd
  obtain ⟨s, hs, hys, -, hsc⟩ := exists_special_of_mem_nbhd_three hD hNL hNP hc hy3 hy2
  obtain ⟨hv, hv3, -, hvy, hvpy⟩ := FarLine.reflect hclass hD hNL hNP hPl hP1 hc hp hp3 he hep
    hyD hpy hs hys hsc rfl rfl
  refine ⟨![y, e * (s * c) ^ 2 * e], fun i => ?_, fun i => ?_, hvy, hvpy⟩
  · fin_cases i
    · exact ⟨hyD, hpy, hpyD⟩
    · exact hv
  · fin_cases i
    · exact hy3
    · exact hv3

theorem lineConfig_of_two_near (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    (hP1 : ExcP1 D) {c p : G} (hc : c ∈ D) (hp : p ∈ D) (hp4 : p ∈ nbhd D c 4)
    (hp3 : p ∉ nbhd D c 3) {x : Fin 2 → G} (hx : ∀ i, x i ∈ collinearSet D p)
    (hx3 : ∀ i, x i ∈ nbhd D c 3) (h10 : x 1 ≠ x 0) (h10' : x 1 ≠ p * x 0) :
    LineConfig p c x := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have hTO := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hp).2 hp3
  have hx2 : ∀ i, x i ∉ nbhd D c 2 := fun i h => hp3 (mem_nbhd_succ_of_commute hp h (hx i).2.1)
  have hsq : (x 0 * x 1) ^ 2 = p := by
    rcases NoLevi.centralizer_cases hD hconj hNL hNP hPl hp (hx 0).1 (hx 1).1 (hx 0).2.1
        (hx 1).2.1 (ne_of_mem_collinearSet hD hp (hx 0))
        (ne_of_mem_collinearSet hD hp (hx 1)) with h | h | ⟨-, h⟩
    · exact absurd h h10
    · exact absurd h h10'
    · exact h
  have hcfg := lineConfig_of_totallyOpposite hD hTO hp hc (hx 0).1 (hx 1).1 (hx 0).2.1 (hx 1).2.1
    (hx 0).2.2 (hx 1).2.2 hsq (orderOf_eq_five_of_mem_nbhd_four hclass hD hNL hNP hPl hP1 hp hc hp4
      hp3) (orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc (hx3 0) (hx2 0))
    (orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc (hx3 1) (hx2 1))
  have e : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [e]
  exact hcfg

theorem exists_conj_fixed [Finite G] {S : Set G} {g : G} (hg : g ^ 3 = 1)
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) (h3 : ¬ 3 ∣ S.ncard) : ∃ s ∈ S, g * s * g⁻¹ = s := by
  classical
  have hg' : g * (g * g) = 1 := by rw [← pow_three]; exact hg
  have hginv : g⁻¹ = g * g := inv_eq_of_mul_eq_one_right hg'
  have hS' : ∀ s ∈ S, g⁻¹ * s * g ∈ S := fun s hs => by
    have h := hS _ (hS s hs)
    have e : g * (g * s * g⁻¹) * g⁻¹ = g⁻¹ * s * g := by
      calc g * (g * s * g⁻¹) * g⁻¹ = (g * g) * s * (g * g)⁻¹ := by group
        _ = g⁻¹ * s * (g⁻¹)⁻¹ := by rw [hginv]
        _ = g⁻¹ * s * g := by rw [inv_inv]
    rwa [e] at h
  let σ : Equiv.Perm S :=
    { toFun := fun s => ⟨g * s * g⁻¹, hS s s.2⟩
      invFun := fun s => ⟨g⁻¹ * s * g, hS' s s.2⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc]) }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun s => Subtype.ext ?_
    rw [pow_one, show (3 : ℕ) = 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_one]
    show g * (g * (g * (s : G) * g⁻¹) * g⁻¹) * g⁻¹ = s
    have e : g * (g * (g * (s : G) * g⁻¹) * g⁻¹) * g⁻¹ = g ^ 3 * s * (g ^ 3)⁻¹ := by
      simp only [pow_three, mul_inv_rev, mul_assoc]
    rw [e, hg, one_mul, inv_one, mul_one]
  have : Fintype S := Fintype.ofFinite S
  have hcard : ¬ 3 ∣ Fintype.card S := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

@[expose] def offLines (D : Set G) (p : G) (x : Fin 2 → G) : Set G :=
  {r | r ∈ collinearSet D p ∧ ∀ i, r ≠ x i ∧ r ≠ p * x i}

theorem ncard_offLines [Finite G] (hD : IsRootInvolutionSet D) {p : G} (hp : p ∈ D)
    {x : Fin 2 → G} (hx : ∀ i, x i ∈ collinearSet D p) (h10 : x 1 ≠ x 0) (h10' : x 1 ≠ p * x 0) :
    (offLines D p x).ncard + 4 = (collinearSet D p).ncard := by
  set T : Set G := {x 0, p * x 0, x 1, p * x 1} with hT
  have hTsub : T ⊆ collinearSet D p := by
    intro r hr
    simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hx 0
    · exact mul_mem_collinearSet hD hp (hx 0)
    · exact hx 1
    · exact mul_mem_collinearSet hD hp (hx 1)
  have hoff : offLines D p x = collinearSet D p \ T := by
    ext r
    simp only [offLines, hT, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Fin.forall_fin_two]
    tauto
  have hp2 := hD.mul_self_eq_one hp
  have hpp : ∀ g : G, p * (p * g) = g := fun g => by rw [← mul_assoc, hp2, one_mul]
  have hne : ∀ g : G, g ≠ p * g := fun g e => hD.ne_one hp (by
    have := congrArg (· * g⁻¹) e
    simpa using this.symm)
  have hcard : T.ncard = 4 := by
    rw [hT, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
    · exact hne (x 1)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun e => h10' e.symm, fun e => h10 (mul_left_cancel e).symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne (x 0), fun e => h10 e.symm, fun e => h10' (by rw [e, hpp])⟩
  rw [hoff, Set.ncard_sdiff hTsub, hcard]
  have := Set.ncard_le_ncard hTsub (Set.toFinite _)
  omega

theorem false_of_mem_nbhd_four [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D)
    (hW1 : ∀ c ∈ D, ∀ p ∈ D, p ∉ nbhd D c 3 → ¬ ThreeNear D c p) {c p : G} (hc : c ∈ D)
    (hp : p ∈ D) (hp4 : p ∈ nbhd D c 4) (hp3 : p ∉ nbhd D c 3)
    (h3 : (collinearSet D p).ncard % 3 ≠ 1) : False := by
  obtain ⟨x, hx, hx3, h10, h10'⟩ := exists_two_near hclass hD hNL hNP hPl hP1 hc hp hp4 hp3
  have hcfg := lineConfig_of_two_near hclass hD hNL hNP hPl hP1 hc hp hp4 hp3 hx hx3 h10 h10'
  obtain ⟨hzp, -, hzx, hz3⟩ := zEl_facts hcfg
  set z := zEl p c x with hz_def
  have hfix : ∀ g, Commute z g → z⁻¹ * g * z = g := fun g hg => by
    rw [mul_assoc, ← hg.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hS : ∀ s ∈ offLines D p x, z * s * z⁻¹ ∈ offLines D p x := by
    rintro s ⟨⟨hsD, hps, hpsD⟩, hsx⟩
    refine ⟨⟨conj_mem_of_isClass hclass z hsD, ?_, ?_⟩, fun i => ⟨fun e => (hsx i).1 ?_,
      fun e => (hsx i).2 ?_⟩⟩
    · have := (Commute.conj_iff z).2 hps
      rwa [show z * p * z⁻¹ = p by rw [hzp.eq, mul_inv_cancel_right]] at this
    · rw [show p * (z * s * z⁻¹) = z * (p * s) * z⁻¹ by
        rw [← mul_assoc, ← mul_assoc, ← hzp.eq]; group]
      exact conj_mem_of_isClass hclass z hpsD
    · rw [show s = z⁻¹ * (z * s * z⁻¹) * z by group, e, hfix _ (hzx i)]
    · rw [show s = z⁻¹ * (z * s * z⁻¹) * z by group, e, hfix _ (hzp.mul_right (hzx i))]
  have hcard := ncard_offLines hD hp hx h10 h10'
  obtain ⟨q, ⟨hq, hqx⟩, hzq⟩ := exists_conj_fixed hz3 hS (by omega)
  have hzq' : Commute z q := mul_inv_eq_iff_eq_mul.1 hzq
  have hq3 : q ∉ nbhd D c 3 := by
    intro hq3
    refine hW1 c hc p hp hp3 ⟨![x 0, x 1, q], fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i
      exacts [hx 0, hx 1, hq]
    · fin_cases i
      exacts [hx3 0, hx3 1, hq3]
    · have hp2 := hD.mul_self_eq_one hp
      have hpp : ∀ g : G, p * (p * g) = g := fun g => by rw [← mul_assoc, hp2, one_mul]
      fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
      · exact ⟨h10, h10'⟩
      · exact hqx 0
      · exact ⟨Ne.symm h10, fun (e : x 0 = p * x 1) => h10' (by rw [e, hpp])⟩
      · exact hqx 1
      · exact ⟨fun (e : x 0 = q) => (hqx 0).1 e.symm,
          fun (e : x 0 = p * q) => (hqx 0).2 (by rw [e, hpp])⟩
      · exact ⟨fun (e : x 1 = q) => (hqx 1).1 e.symm,
          fun (e : x 1 = p * q) => (hqx 1).2 (by rw [e, hpp])⟩
  have hTO := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hq.1).2 hq3
  obtain ⟨-, hodd⟩ := hTO.opposite_self hq.1
  have hW1' : ∀ i, ¬ ThreeNear D (zPt p c x i) (yPt p c x (farZ i)) := fun i =>
    hW1 _ (zPt_mem hclass hp i) _ (yPt_mem hD hp hx (farZ i)).1
      (zPt_facts hclass hD hNL hNP hP1 hcfg hp hx i).2.2.2
  obtain ⟨hY, hW, hZ⟩ := deep_relations hclass hD hsing hQ hNL hNP hPl hP1 hcfg hp hx hq
    (fun i => hqx i) hW1'
  exact hD.ne_one hq.1 (eq_one_of_relations hcfg hzq' (hD.mul_self_eq_one hq.1) hq.2.1 hY hW hZ
    hodd)

theorem excDiam4_of_noThreeNear [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x}) (hQ : CommLambda D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D)
    (hconn : Closure.CommConnected D)
    (hW1 : ∀ c ∈ D, ∀ p ∈ D, p ∉ nbhd D c 3 → ¬ ThreeNear D c p)
    (h3 : ∀ d ∈ D, (collinearSet D d).ncard % 3 ≠ 1) : ExcDiam4 D := by
  intro p hp c hc _
  have key : ∀ k, nbhd D c k ⊆ nbhd D c 3 := by
    intro k
    induction k with
    | zero => exact nbhd_mono (by norm_num)
    | succ k ih =>
      intro d hd
      obtain ⟨hdD, e, he, hde⟩ := (mem_nbhd_succ_iff hc).1 hd
      have hd4 : d ∈ nbhd D c 4 := mem_nbhd_succ_of_commute hdD (ih he) hde
      by_contra hd3
      exact false_of_mem_nbhd_four hclass hD hsing hQ hNL hNP hPl hP1 hW1 hc hdD hd4 hd3
        (h3 d hdD)
  obtain ⟨k, hk⟩ := exists_mem_nbhd hconn hc hp
  exact nbhd_mono (by norm_num) (key k hk)

end CFSG.Timmesfeld.Moufang.Deep
