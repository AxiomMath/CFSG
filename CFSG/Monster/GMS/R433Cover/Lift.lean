module

public import CFSG.Monster.GMS.R433Cover.Relators

public section

namespace CFSG.Monster.GMS.R433Cover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)
open CFSG.YGroups (yRels spiderWord R433 U433 F433 yGen)
open scoped commutatorElement

variable {E G : Type*} [Group E] [Group G]

structure CentralKernel (π : E →* G) (z : E) : Prop where
  central : ∀ x : E, x * z = z * x
  mul_self : z * z = 1
  map_eq_one : π z = 1
  ker_sub : ∀ x, π x = 1 → IsZ z x

theorem exists_edge_lifts {π : E →* G} {z : E} (hz : CentralKernel π z) {l : ℕ → E} {g : ℕ → G}
    (hl : ∀ c < 11, π (l c) = g c)
    (hedge : ∀ c, 0 < c → c < 11 → (g (parent c) * g c) ^ 3 = 1) :
    ∀ n ≤ 11, ∃ gh : ℕ → E, (∀ c < n, π (gh c) = g c) ∧
      ∀ c, 0 < c → c < n → (gh (parent c) * gh c) ^ 3 = 1 := by
  obtain ⟨hzc, hz2, hπz, hker⟩ := hz
  intro n
  induction n with
  | zero => intro _; exact ⟨l, by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨gh, h1, h2⟩ := ih (by omega)
    by_cases h0 : n = 0
    · subst h0
      refine ⟨l, ?_, ?_⟩
      · intro c hc; exact hl c (by omega)
      · intro c hc hc'; omega
    · have hpn : parent n < n := parent_lt n (Nat.pos_of_ne_zero h0)
      have hπ : π ((gh (parent n) * l n) ^ 3) = 1 := by
        rw [map_pow, map_mul, h1 _ hpn, hl n (by omega)]
        exact hedge n (Nat.pos_of_ne_zero h0) (by omega)
      by_cases hc : (gh (parent n) * l n) ^ 3 = 1
      · refine ⟨Function.update gh n (l n), ?_, ?_⟩
        · intro c hc'
          by_cases hcn : c = n
          · subst hcn; simpa using hl c (by omega)
          · rw [Function.update_of_ne hcn]; exact h1 c (by omega)
        · intro c hc0 hc'
          by_cases hcn : c = n
          · subst hcn
            rw [Function.update_of_ne (by omega), Function.update_self]; exact hc
          · have hpc : parent c < c := parent_lt c hc0
            rw [Function.update_of_ne hcn, Function.update_of_ne (by omega)]
            exact h2 c hc0 (by omega)
      · have hz : (gh (parent n) * l n) ^ 3 = z := (hker _ hπ).resolve_left hc
        refine ⟨Function.update gh n (l n * z), ?_, ?_⟩
        · intro c hc'
          by_cases hcn : c = n
          · subst hcn; simp [map_mul, hπz, hl c (by omega)]
          · rw [Function.update_of_ne hcn]; exact h1 c (by omega)
        · intro c hc0 hc'
          by_cases hcn : c = n
          · subst hcn
            rw [Function.update_of_ne (by omega), Function.update_self]
            have hcomm : Commute (gh (parent c) * l c) z := hzc _
            calc (gh (parent c) * (l c * z)) ^ 3 = ((gh (parent c) * l c) * z) ^ 3 := by
                  rw [mul_assoc]
              _ = (gh (parent c) * l c) ^ 3 * z ^ 3 := hcomm.mul_pow 3
              _ = 1 := by rw [hz, pow_three', hz2, one_mul, hz2]
          · have hpc : parent c < c := parent_lt c hc0
            rw [Function.update_of_ne hcn, Function.update_of_ne (by omega)]
            exact h2 c hc0 (by omega)

theorem lift_family {π : E →* G} {z : E} (hz : CentralKernel π z) (hπ : Function.Surjective π)
    {g : ℕ → G} (hrel : ∀ w ∈ yRels 4 3 3, evalWord g w = 1)
    (hF : (evalWord g [0, 5, 6, 7, 1, 2, 8]) ^ 9 = 1)
    {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < 11) (hY : ConjIdentity g Y) (h1 : SpiderIdentity g) :
    ∃ g' : ℕ → E, (∀ c < 11, π (g' c) = g c) ∧ (∀ w ∈ yRels 4 3 3, evalWord g' w = 1) ∧
      (evalWord g' [0, 5, 6, 7, 1, 2, 8]) ^ 9 = 1 := by
  classical
  have hz' := hz
  obtain ⟨hzc, hz2, hπz, hker⟩ := hz'
  have hY' : (evalWord g Y)⁻¹ * (g 0 * g 4 * g 6) * evalWord g Y = g 2 * g 5 * g 7 * g 9 := hY
  have h1' : ((evalWord g (spiderWord 4 3)) ^ 5 * g 0) ^ 3 = 1 := h1
  choose l hl using fun c => hπ (g c)
  have hedgeG : ∀ c, 0 < c → c < 11 → (g (parent c) * g c) ^ 3 = 1 := by
    intro c hc0 hc
    have h := fam_pair hrel (parent_lt c hc0) hc
    rwa [pair_exp_three c hc hc0] at h
  obtain ⟨gh, hgh1, hgh2⟩ := exists_edge_lifts hz (l := l) (g := g) (fun c _ => hl c) hedgeG 11
    le_rfl
  have hedge : ∀ p ∈ edges, (gh p.1 * gh p.2) ^ 3 = 1 := by
    intro p hp
    obtain ⟨h0, h11, hpar⟩ := edges_parent p hp
    have := hgh2 p.2 h0 h11
    rwa [hpar] at this
  have hsq : ∀ s < 11, IsZ z (gh s * gh s) := by
    intro s hs
    apply hker
    rw [map_mul, hgh1 s hs]
    exact fam_sq hrel hs
  have hcm : ∀ s t, nonadj s t = true → IsZ z (cm (gh s) (gh t)) := by
    intro s t hst
    obtain ⟨hs, ht⟩ := nonadj_lt hst
    apply hker
    have hc := fam_comm hrel hst
    simp only [cm, map_mul, map_inv, hgh1 s hs, hgh1 t ht]
    calc g s * g t * (g s)⁻¹ * (g t)⁻¹ = (g t * g s) * (g s)⁻¹ * (g t)⁻¹ := by rw [hc]
      _ = 1 := by group
  have hlt_ev : ∀ w : List ℕ, (∀ c ∈ w, c < 11) → π (evalWord gh w) = evalWord g w := by
    intro w hw
    exact map_evalWord_of_forall π gh g w (fun c hc => hgh1 c (hw c hc))
  have hF' : IsZ z ((evalWord gh [0, 5, 6, 7, 1, 2, 8]) ^ 9) := by
    apply hker
    rw [map_pow, hlt_ev _ (by decide)]
    exact hF
  have hsp_ev : (evalWord g (spiderWord 4 3)) ^ 10 = 1 := by
    have := hrel (List.replicate 10 (spiderWord 4 3)).flatten (by
      simp only [yRels, List.mem_append]
      refine Or.inr ?_
      simp)
    rwa [CFSG.YGroups.Y443.evalWord_replicate_flatten] at this
  have hsp : IsZ z ((evalWord gh (spiderWord 4 3)) ^ 10) := by
    apply hker
    rw [map_pow, hlt_ev _ (by decide)]
    exact hsp_ev
  have hI1 : IsZ z (((evalWord gh (spiderWord 4 3)) ^ 5 * gh 0) ^ 3) := by
    apply hker
    rw [map_pow, map_mul, map_pow, hlt_ev _ (by decide), hgh1 0 (by norm_num)]
    exact h1'
  have hI2 : IsZ z ((evalWord gh Y)⁻¹ * (gh 0 * gh 4 * gh 6) * evalWord gh Y *
      (gh 2 * gh 5 * gh 7 * gh 9)⁻¹) := by
    apply hker
    simp only [map_mul, map_inv, hlt_ev Y hYlt, hgh1 0 (by norm_num), hgh1 2 (by norm_num),
      hgh1 4 (by norm_num), hgh1 5 (by norm_num), hgh1 6 (by norm_num), hgh1 7 (by norm_num),
      hgh1 9 (by norm_num)]
    rw [hY']; group
  obtain ⟨hsq1, hcomm, hsp1⟩ := flags_vanish hzc hz2 hedge hsq hcm hF'
    (by simpa [spiderWord] using hsp) (by simpa [spiderWord] using hI1) hI2
  have hrelgh := rels_of_flags hsq1 hcomm hedge hsp1
  rcases hF' with hF1 | hFz
  · exact ⟨gh, hgh1, hrelgh, hF1⟩
  · refine ⟨fun c => gh c * z, ?_, ?_, ?_⟩
    · intro c hc; rw [map_mul, hπz, mul_one]; exact hgh1 c hc
    · intro w hw
      rw [evalWord_mul_central hzc, hrelgh w hw, one_mul]
      have := length_even_of_mem_yRels w hw
      obtain ⟨m, hm⟩ : ∃ m, w.length = 2 * m := ⟨w.length / 2, by omega⟩
      rw [hm, pow_mul, sq, hz2, one_pow]
    · rw [evalWord_mul_central hzc]
      have hcomm : Commute (evalWord gh [0, 5, 6, 7, 1, 2, 8])
          (z ^ ([0, 5, 6, 7, 1, 2, 8] : List ℕ).length) :=
        Commute.pow_right (hzc _) _
      rw [hcomm.mul_pow, hFz]
      have : z ^ (([0, 5, 6, 7, 1, 2, 8] : List ℕ).length * 9) = z := by
        have h63 : ([0, 5, 6, 7, 1, 2, 8] : List ℕ).length * 9 = 2 * 31 + 1 := by simp
        rw [h63, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
      rw [← pow_mul, this, hz2]

theorem exists_hom_R433 {π : E →* G} {z : E} (hz : CentralKernel π z) (hπ : Function.Surjective π)
    (ρ : R433 →* G) {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < 11) (hY : ConjIdentity (marked ρ) Y)
    (h1 : SpiderIdentity (marked ρ)) : ∃ θ : R433 →* E, π.comp θ = ρ := by
  obtain ⟨g', hg1, hg2, hg3⟩ :=
    lift_family hz hπ (marked_rels ρ) (marked_F ρ) hYlt hY h1
  let ψ : U433 →* E := CFSG.YGroups.yModelHom g' hg2
  have hψ : ∀ c < 11, ψ (yGen 4 3 3 c) = g' c := fun c hc =>
    CFSG.YGroups.yModelHom_yGen (by simpa [CFSG.YGroups.ngen] using hc)
  have hFψ : ψ (F433 2 1 3) = 1 := by
    rw [F433_213_eq, map_pow, CFSG.YGroups.Relabel.map_evalWord]
    have : evalWord (fun c => ψ (yGen 4 3 3 c)) [0, 5, 6, 7, 1, 2, 8] =
        evalWord g' [0, 5, 6, 7, 1, 2, 8] := by
      apply CFSG.YGroups.evalWord_congr
      intro c hc
      exact hψ c (by simp at hc; omega)
    rw [this]; exact hg3
  have hle : Subgroup.normalClosure {F433 2 1 3} ≤ ψ.ker :=
    Subgroup.normalClosure_le_normal (by simpa [MonoidHom.mem_ker] using hFψ)
  let θ : R433 →* E := QuotientGroup.lift (Subgroup.normalClosure {F433 2 1 3}) ψ hle
  refine ⟨θ, ?_⟩
  refine (MonoidHom.cancel_right R433.π_surjective).1 ?_
  refine PresentedGroup.ext fun c => ?_
  have hc : (c : ℕ) < 11 := c.2
  simp only [MonoidHom.comp_apply]
  have e1 : (PresentedGroup.of c : U433) = yGen 4 3 3 c := (CFSG.YGroups.yGen_of_lt c.2).symm
  rw [e1]
  show π (ψ (yGen 4 3 3 c)) = ρ (R433.π (yGen 4 3 3 c))
  rw [hψ c hc, hg1 c hc]
  rfl

theorem commutatorElement_mul_central {x y k : E} (hk : ∀ g : E, g * k = k * g) :
    ⁅x * k, y⁆ = ⁅x, y⁆ ∧ ⁅x, y * k⁆ = ⁅x, y⁆ := by
  constructor
  · calc ⁅x * k, y⁆ = x * (k * y) * (k⁻¹ * x⁻¹) * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * (y * k) * (k⁻¹ * x⁻¹) * y⁻¹ := by rw [← hk y]
      _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group
  · calc ⁅x, y * k⁆ = x * y * (k * x⁻¹) * k⁻¹ * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * y * (x⁻¹ * k) * k⁻¹ * y⁻¹ := by rw [← hk x⁻¹]
      _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem surj_of_perfect {π : E →* G} {z : E} (hz : CentralKernel π z) {ρ : R433 →* G}
    {θ : R433 →* E} (hπθ : π.comp θ = ρ) (hρ : Function.Surjective ρ)
    (hperf : commutator E = ⊤) : Function.Surjective θ := by
  obtain ⟨hzc, hz2, -, hker⟩ := hz
  have hdecomp : ∀ e : E, ∃ s : E, s ∈ θ.range ∧ ∃ k, IsZ z k ∧ e = s * k := by
    intro e
    obtain ⟨r, hr⟩ := hρ (π e)
    have hπr : π (θ r) = π e := by
      have := congrArg (fun f => f r) hπθ
      simpa [hr] using this
    have h1 : π ((θ r)⁻¹ * e) = 1 := by
      rw [map_mul, map_inv, hπr, inv_mul_cancel]
    exact ⟨θ r, ⟨r, rfl⟩, (θ r)⁻¹ * e, hker _ h1, by group⟩
  have hcomm : commutator E ≤ θ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨s₁, hs₁, k₁, hk₁, rfl⟩ := hdecomp a
    obtain ⟨s₂, hs₂, k₂, hk₂, rfl⟩ := hdecomp b
    have c₁ := IsZ.comm hzc hz2 hk₁
    have c₂ := IsZ.comm hzc hz2 hk₂
    rw [(commutatorElement_mul_central c₁).1, (commutatorElement_mul_central c₂).2,
      commutatorElement_def]
    exact θ.range.mul_mem (θ.range.mul_mem (θ.range.mul_mem hs₁ hs₂) (θ.range.inv_mem hs₁))
      (θ.range.inv_mem hs₂)
  intro e
  have h := hcomm
  rw [hperf] at h
  exact h (Subgroup.mem_top e)

theorem nonempty_mulEquiv_of_cover [Finite R433] {π : E →* G} {z : E} (hz : CentralKernel π z)
    (hπ : Function.Surjective π) {ρ : R433 →* G} (hρ : Function.Surjective ρ) {Y : List ℕ}
    (hYlt : ∀ c ∈ Y, c < 11) (hY : ConjIdentity (marked ρ) Y) (h1 : SpiderIdentity (marked ρ))
    (hperf : commutator E = ⊤) (hcard : Nat.card R433 ≤ Nat.card E) :
    Nonempty (E ≃* R433) := by
  obtain ⟨θ, hθ⟩ := exists_hom_R433 hz hπ ρ hYlt hY h1
  have hsurj := surj_of_perfect hz hθ hρ hperf
  have hbij := hsurj.bijective_of_nat_card_le hcard
  exact ⟨(MulEquiv.ofBijective θ hbij).symm⟩

end CFSG.Monster.GMS.R433Cover
