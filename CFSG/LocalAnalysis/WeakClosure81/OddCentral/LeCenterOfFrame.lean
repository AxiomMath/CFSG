module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Lifts
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.FrameY
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.LocalAnalysis.WeakClosure81.OddCentral
open CFSG.LocalAnalysis.WeakClosure81.OddCentral CFSG.Timmesfeld.Bridge.Asc72

section
variable {Y : Type} [Group Y]

theorem moves_conj {P Z : Subgroup Y} [hP : P.Normal] [hZ : Z.Normal] {a x : Y} (hx : x ∈ P)
    (h : a * x * a⁻¹ * x⁻¹ ∉ Z) (k : Y) :
    ∃ y ∈ P, (k * a * k⁻¹) * y * (k * a * k⁻¹)⁻¹ * y⁻¹ ∉ Z := by
  refine ⟨k * x * k⁻¹, hP.conj_mem x hx k, fun hm => h ?_⟩
  have := hZ.conj_mem _ hm k⁻¹
  convert this using 1
  group

end

section

theorem le_center_of_frame (G : Type) [Group G] [Finite G] {V H E : Subgroup G}
    (h : Hyp711 V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {Y : Type} [Group Y] [Finite Y] {ι : Y →* X}
    (hι : Function.Injective ι) {s d₁ d₂ d₃ t : Y} (hsV : ι s ∈ barSub (kSub V H E) φ V)
    (hs1 : s ≠ 1) (hs : normalClosure ({s} : Set Y) = ⊤)
    (_hL : IsL2OrSz (Y ⧸ fusionZStar Y) 2) (hF : OddCentral.IsFrame s d₁ d₂ d₃ t)
    (hPS : ∀ A B : Subgroup Y, A.Normal → B.Normal → B < A → A ≤ fusionOddCore Y →
      (∀ N : Subgroup Y, N.Normal → B ≤ N → N ≤ A → N = B ∨ N = A) →
      (∃ a ∈ A, d₁ * a * d₁⁻¹ * a⁻¹ ∉ B) →
      ∀ d ∈ ({d₁, d₂, d₃} : Set Y), ∀ r ∈ fusionOddCore Y, ∀ a ∈ A,
        (d * r * d⁻¹ * r⁻¹) * a * (d * r * d⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B) :
    fusionOddCore Y ≤ center Y := by
  classical
  have hD := OddCentral.isOddTransp_of_embedding G h hφ hS hι hsV hs1
  obtain ⟨h1, h2, h3, c12, c23, c13, hcZ, h12Z, t1, t2, t3⟩ := hF
  have hDc : ∀ x ∈ {x : Y | IsConj s x}, ∀ g : Y, g * x * g⁻¹ ∈ {x : Y | IsConj s x} :=
    fun x hx g => hx.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hsq : ∀ x ∈ {x : Y | IsConj s x}, x * x = 1 := fun x hx => by
    have := pow_orderOf_eq_one x; rw [hD.1 _ hx, pow_two] at this; exact this
  have h23Z : d₂ * d₃ ∉ fusionZStar Y := fun h => h12Z (by
    have := (fusionZStar_normal Y).conj_mem _ h t⁻¹
    rwa [show t⁻¹ * (d₂ * d₃) * t⁻¹⁻¹ = d₁ * d₂ by
      calc t⁻¹ * (d₂ * d₃) * t⁻¹⁻¹ = t⁻¹ * ((t * d₁ * t⁻¹) * (t * d₂ * t⁻¹)) * t⁻¹⁻¹ := by
            rw [t1, t2]
        _ = d₁ * d₂ := by group] at this)
  have h31Z : d₃ * d₁ ∉ fusionZStar Y := fun h => h23Z (by
    have := (fusionZStar_normal Y).conj_mem _ h t⁻¹
    rwa [show t⁻¹ * (d₃ * d₁) * t⁻¹⁻¹ = d₂ * d₃ by
      calc t⁻¹ * (d₃ * d₁) * t⁻¹⁻¹ = t⁻¹ * ((t * d₂ * t⁻¹) * (t * d₃ * t⁻¹)) * t⁻¹⁻¹ := by
            rw [t2, t3]
        _ = d₂ * d₃ := by group] at this)
  have hne : ∀ x y : Y, x ∈ {x : Y | IsConj s x} → x * y ∉ fusionZStar Y → x ≠ y :=
    fun x y hx hxy h => hxy (by rw [← h, hsq x hx]; exact one_mem _)
  have n12 := hne _ _ h1 h12Z
  have n23 := hne _ _ h2 h23Z
  have n31 := hne _ _ h3 h31Z
  let d : Fin 3 → Y := ![d₁, d₂, d₃]
  have hdD : ∀ i, d i ∈ {x : Y | IsConj s x} := by
    intro i; fin_cases i
    · exact h1
    · exact h2
    · exact h3
  have hdc : ∀ i j, d i * d j = d j * d i := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact c12.eq
    · exact c13.eq
    · exact c12.symm.eq
    · rfl
    · exact c23.eq
    · exact c13.symm.eq
    · exact c23.symm.eq
    · rfl
  have hdn : ∀ i j, i ≠ j → d i ≠ d j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact n12
    · exact n31.symm
    · exact n12.symm
    · exact absurd rfl hij
    · exact n23
    · exact n31
    · exact n23.symm
    · exact absurd rfl hij
  have ht : ∀ i, t * d i * t⁻¹ = d (i + 1) := by
    intro i; fin_cases i
    · exact t1
    · exact t2
    · exact t3
  have hcO : ∀ g : Y, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ fusionOddCore Y := by
    intro g
    have hc := mem_center_iff.mp (mem_comap.mp hcZ) (QuotientGroup.mk' (fusionOddCore Y) g)
    rw [← QuotientGroup.ker_mk' (fusionOddCore Y), MonoidHom.mem_ker]
    show QuotientGroup.mk' (fusionOddCore Y) ((d₁ * d₂ * d₃)⁻¹ * (g * (d₁ * d₂ * d₃) * g⁻¹)) = 1
    generalize d₁ * d₂ * d₃ = c at hc ⊢
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have hgen : normalClosure ({d 0} : Set Y) = ⊤ := by
    obtain ⟨g, hg⟩ := isConj_iff.mp h1
    rw [eq_top_iff, ← hs]
    refine normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    have := (normalClosure_normal (s := ({d 0} : Set Y))).conj_mem _
      (subset_normalClosure (Set.mem_singleton _)) g⁻¹
    rwa [show g⁻¹ * d 0 * g⁻¹⁻¹ = s by
      show g⁻¹ * d₁ * g⁻¹⁻¹ = s
      rw [← hg]; group] at this
  have hd : ∀ i, d i * d i = 1 := fun i => hsq _ (hdD i)
  have hRodd := OddCentral.odd_card_fusionOddCore Y
  by_contra hcen
  have hP : ∃ i, ∃ f ∈ fusionOddCore Y, d i * f ≠ f * d i := by
    by_contra hall
    push Not at hall
    exact hcen (le_center_of_comm hgen (fun x hx => hall 0 x hx))
  obtain ⟨P, hPn, hPR, hPm, hmin⟩ := exists_min_moved hP
  haveI := hPn
  haveI hZn : (P ⊓ center Y).Normal := Subgroup.normal_inf_normal _ _
  have hZc : P ⊓ center Y ≤ center Y := inf_le_right
  have hZP : P ⊓ center Y ≤ P := inf_le_left
  have hPodd : Odd (Nat.card P) := Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le hPR)
  have hmax := max_of_min hgen hmin
  have hmv : ∃ i, ∃ x ∈ P, d i * x * (d i)⁻¹ * x⁻¹ ∉ P ⊓ center Y := by
    obtain ⟨i, x, hx, hne⟩ := hPm
    exact ⟨i, x, hx, fun hm => hne (commute_of_comm_mem hZc hZP hPodd (hd i) hm)⟩
  have hZ0P : P ⊓ center Y < P := by
    refine lt_of_le_of_ne hZP fun heq => ?_
    obtain ⟨i, x, hx, hne⟩ := hmv
    exact hne (by rw [heq]; exact P.mul_mem (hPn.conj_mem x hx (d i)) (P.inv_mem hx))
  have hP' := comm_of_chief_odd hZ0P hPodd hmax
  have step : ∀ i : Fin 3, (∃ x ∈ P, d i * x * (d i)⁻¹ * x⁻¹ ∉ P ⊓ center Y) →
      ∃ x ∈ P, d (i + 1) * x * (d (i + 1))⁻¹ * x⁻¹ ∉ P ⊓ center Y := by
    rintro i ⟨x, hx, hne⟩
    rw [← ht i]; exact moves_conj hx hne t
  have hmove0 : ∃ x ∈ P, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ P ⊓ center Y := by
    obtain ⟨i, hi⟩ := hmv
    fin_cases i
    · exact hi
    · exact step 2 (step 1 hi)
    · exact step 2 hi
  have hLA : ∀ i j, i ≠ j → ∀ x ∈ P, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ P ⊓ center Y →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ P ⊓ center Y :=
    fun i j hij x hx hm => la_section hD hDc (hdD i) (hdD j) (hdn i j hij) (hdc i j) hPodd
      (fun y hy => hPn.conj_mem y hy (d i)) hZP hx hm
  have hPSa := hPS P (P ⊓ center Y) hPn hZn hZ0P hPR hmax hmove0
  have hSi : ∀ i, ∀ r ∈ fusionOddCore Y, ∀ a ∈ P,
      (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ P ⊓ center Y := by
    intro i; fin_cases i
    · exact hPSa d₁ (by simp)
    · exact hPSa d₂ (by simp)
    · exact hPSa d₃ (by simp)
  have hRc := comm_c_of_comm (R := fusionOddCore Y) hSi
  have hc := (s3_prime hZP hPodd hP' hmax hRodd hd hdc hcO hRc hLA hmove0).1
  have hc2 : (d 0 * d 1 * d 2) * (d 0 * d 1 * d 2) = 1 :=
    mul_sq_eq_one (mul_sq_eq_one (hd 0) (hd 1) (hdc 0 1)) (hd 2)
      (by rw [mul_assoc, hdc 1 2, ← mul_assoc, hdc 0 2, mul_assoc])
  have hYR := exists_mul_centralizer hRodd hc2 hcO
  have hnt := invSet_nontrivial hZc hP' hPodd hd hdc ht hc hLA hmove0
  have hmoveAll : ∀ e, IsConj s e → ∃ p ∈ P, e * p * e⁻¹ * p⁻¹ ≠ 1 := by
    intro e hse
    obtain ⟨x, hx, hne⟩ := hmove0
    obtain ⟨k, rfl⟩ := isConj_iff.mp ((hdD 0).symm.trans hse)
    obtain ⟨y, hy, hy'⟩ := moves_conj hx hne k
    exact ⟨y, hy, fun h1 => hy' (by rw [h1]; exact one_mem _)⟩
  exact false_of_frame_G h hφ hι hS hsV hs1 hZc hZP hP' hPodd hd hdc hdn ht hc hLA (hSi 0) hYR
    hgen hmax hnt hdD hmoveAll
end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
