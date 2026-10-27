module

public import CFSG.Sporadic.Recognition.YCoverFlags
public import CFSG.YGroups.Exact.Model

public section

namespace CFSG.Sporadic.Recognition.YCover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)
open CFSG.Monster.GMS.R433Cover (IsZ cm evalWord_mul_central map_evalWord_of_forall
  commute_of_sq evalWord_reverse_inv)
open CFSG.YGroups (yRels yEdges ngen spiderWord pairExp pairWord yGen YGroup yModelHom
  yModelHom_yGen)
open scoped commutatorElement

variable {p q r : ℕ} {E G : Type*} [Group E] [Group G]

structure CentralKernel (π : E →* G) (z : E) : Prop where
  central : ∀ x : E, x * z = z * x
  mul_self : z * z = 1
  map_eq_one : π z = 1
  ker_sub : ∀ x, π x = 1 → IsZ z x

theorem evalWord_replicate_flatten' (g : ℕ → G) (w : List ℕ) (n : ℕ) :
    evalWord g (List.replicate n w).flatten = (evalWord g w) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, evalWord_append, ih, pow_succ']

theorem evalWord_pair' (g : ℕ → G) (s t m : ℕ) :
    evalWord g (List.replicate m [s, t]).flatten = (g s * g t) ^ m := by
  rw [evalWord_replicate_flatten', evalWord_cons, evalWord_cons, evalWord_nil, mul_one]

theorem map_evalWord' {H : Type*} [Group H] (φ : E →* H) (g : ℕ → E) (w : List ℕ) :
    φ (evalWord g w) = evalWord (fun c => φ (g c)) w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]

theorem nonadjB_symm {s t : ℕ} (h : nonadjB p q r s t = true) : nonadjB p q r t s = true := by
  unfold nonadjB adjB at h ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not, ne_eq] at h ⊢
  exact ⟨⟨⟨h.1.1.2, h.1.1.1⟩, fun e => h.1.2 e.symm⟩, h.2.2, h.2.1⟩

theorem pairExp_nonadj {s t : ℕ} (h : nonadjB p q r s t = true) :
    pairExp p q r s t = 2 := by
  unfold nonadjB adjB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not] at h
  simp [pairExp, h.2.1]

theorem rels_of_flags (D : FlagData p q r) {gh : ℕ → E}
    (hsq1 : ∀ s < ngen p q r, gh s * gh s = 1)
    (hcomm : ∀ s t, nonadjB p q r s t = true → gh s * gh t = gh t * gh s)
    (hedge : ∀ e ∈ yEdges p q r, (gh e.1 * gh e.2) ^ 3 = 1)
    (hsp : (evalWord gh (spiderWord p q)) ^ 10 = 1) :
    ∀ w ∈ yRels p q r, evalWord gh w = 1 := by
  intro w hw
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, hst⟩, rfl⟩) | hspw
  · have := hsq1 s hs
    simpa [evalWord] using this
  · have hlt : s < t := by simpa using hst
    unfold pairWord
    rw [evalWord_pair']
    by_cases he : (s, t) ∈ yEdges p q r
    · have h3 : pairExp p q r s t = 3 := by simp [pairExp, he]
      rw [h3]
      exact hedge (s, t) he
    · have h2 : pairExp p q r s t = 2 := by simp [pairExp, he]
      rw [h2]
      have hna : nonadjB p q r s t = true := by
        unfold nonadjB adjB
        have hte : (t, s) ∉ yEdges p q r := fun h' => by
          have := D.edges_lt h'
          simp only at this
          omega
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
          decide_eq_true_eq, decide_eq_false_iff_not, ne_eq]
        exact ⟨⟨⟨hs, ht⟩, by omega⟩, he, hte⟩
      have hc := hcomm s t hna
      have hs1 := hsq1 s hs
      have ht1 := hsq1 t ht
      calc (gh s * gh t) ^ 2 = gh s * gh t * (gh s * gh t) := sq _
        _ = gh s * (gh t * gh s) * gh t := by group
        _ = gh s * (gh s * gh t) * gh t := by rw [← hc]
        _ = (gh s * gh s) * (gh t * gh t) := by group
        _ = 1 := by rw [hs1, ht1, one_mul]
  · split_ifs at hspw with hc
    · simp only [List.mem_singleton] at hspw
      subst hspw
      rw [evalWord_replicate_flatten']
      exact hsp
    · simp at hspw

theorem fam_sq {g : ℕ → G} (hrel : ∀ w ∈ yRels p q r, evalWord g w = 1) {s : ℕ}
    (hs : s < ngen p q r) : g s * g s = 1 := by
  have := hrel [s, s] (CFSG.YGroups.square_mem_yRels hs)
  simpa [evalWord] using this

theorem fam_pair {g : ℕ → G} (hrel : ∀ w ∈ yRels p q r, evalWord g w = 1) {s t : ℕ}
    (hst : s < t) (ht : t < ngen p q r) : (g s * g t) ^ pairExp p q r s t = 1 := by
  have := hrel (pairWord p q r s t) (by
    simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
      List.mem_filter]
    exact Or.inl (Or.inr ⟨s, by omega, t, ⟨ht, by simpa using hst⟩, rfl⟩))
  rwa [pairWord, evalWord_pair'] at this

theorem fam_comm {g : ℕ → G} (hrel : ∀ w ∈ yRels p q r, evalWord g w = 1) {s t : ℕ}
    (h : nonadjB p q r s t = true) : g s * g t = g t * g s := by
  obtain ⟨hs, ht⟩ := nonadjB_lt h
  rcases Nat.lt_or_gt_of_ne (nonadjB_ne h) with hlt | hlt
  · have h2 := fam_pair hrel hlt ht
    rw [pairExp_nonadj h] at h2
    exact commute_of_sq (fam_sq hrel hs) (fam_sq hrel ht) h2
  · have h' := nonadjB_symm h
    have h2 := fam_pair hrel hlt hs
    rw [pairExp_nonadj h'] at h2
    exact (commute_of_sq (fam_sq hrel ht) (fam_sq hrel hs) h2).symm

@[expose] def ConjIdentity (D : FlagData p q r) (g : ℕ → G) (Y : List ℕ) : Prop :=
  (evalWord g Y)⁻¹ * (g D.t₁ * g D.t₂ * g D.t₃) * evalWord g Y = g D.q₁ * g D.q₂ * g D.q₃ * g D.q₄

@[expose] def SpiderIdentity (p q : ℕ) (g : ℕ → G) : Prop :=
  ((evalWord g (spiderWord p q)) ^ 5 * g 0) ^ 3 = 1

theorem exists_edge_lifts (D : FlagData p q r) {π : E →* G} {z : E} (hz : CentralKernel π z)
    {l : ℕ → E} {g : ℕ → G} (hl : ∀ c < ngen p q r, π (l c) = g c)
    (hedge : ∀ c, 0 < c → c < ngen p q r → (g (parentY p q c) * g c) ^ 3 = 1) :
    ∀ n ≤ ngen p q r, ∃ gh : ℕ → E, (∀ c < n, π (gh c) = g c) ∧
      ∀ c, 0 < c → c < n → (gh (parentY p q c) * gh c) ^ 3 = 1 := by
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
    · have hpn : parentY p q n < n := (D.parent_edge n (by omega) (Nat.pos_of_ne_zero h0)).1
      have hπ : π ((gh (parentY p q n) * l n) ^ 3) = 1 := by
        rw [map_pow, map_mul, h1 _ hpn, hl n (by omega)]
        exact hedge n (Nat.pos_of_ne_zero h0) (by omega)
      by_cases hc : (gh (parentY p q n) * l n) ^ 3 = 1
      · refine ⟨Function.update gh n (l n), ?_, ?_⟩
        · intro c hc'
          by_cases hcn : c = n
          · subst hcn; simpa using hl c (by omega)
          · rw [Function.update_of_ne hcn]; exact h1 c (by omega)
        · intro c hc0 hc'
          by_cases hcn : c = n
          · subst hcn
            rw [Function.update_of_ne (by omega), Function.update_self]; exact hc
          · have hpc : parentY p q c < c :=
              (D.parent_edge c (by omega) hc0).1
            rw [Function.update_of_ne hcn, Function.update_of_ne (by omega)]
            exact h2 c hc0 (by omega)
      · have hz : (gh (parentY p q n) * l n) ^ 3 = z := (hker _ hπ).resolve_left hc
        refine ⟨Function.update gh n (l n * z), ?_, ?_⟩
        · intro c hc'
          by_cases hcn : c = n
          · subst hcn; simp [map_mul, hπz, hl c (by omega)]
          · rw [Function.update_of_ne hcn]; exact h1 c (by omega)
        · intro c hc0 hc'
          by_cases hcn : c = n
          · subst hcn
            rw [Function.update_of_ne (by omega), Function.update_self]
            have hcomm : Commute (gh (parentY p q c) * l c) z := hzc _
            calc (gh (parentY p q c) * (l c * z)) ^ 3
                = ((gh (parentY p q c) * l c) * z) ^ 3 := by rw [mul_assoc]
              _ = (gh (parentY p q c) * l c) ^ 3 * z ^ 3 := hcomm.mul_pow 3
              _ = 1 := by rw [hz, pow_three', hz2, one_mul, hz2]
          · have hpc : parentY p q c < c := (D.parent_edge c (by omega) hc0).1
            rw [Function.update_of_ne hcn, Function.update_of_ne (by omega)]
            exact h2 c hc0 (by omega)


theorem lift_family (D : FlagData p q r) {π : E →* G} {z : E} (hz : CentralKernel π z)
    (hπ : Function.Surjective π) {g : ℕ → G} (hrel : ∀ w ∈ yRels p q r, evalWord g w = 1)
    (hF : (evalWord g D.Fw) ^ 9 = 1) {Y : List ℕ} (hYlt : ∀ c ∈ Y, c < ngen p q r)
    (hY : ConjIdentity D g Y) (h1 : SpiderIdentity p q g) :
    ∃ g' : ℕ → E, (∀ c < ngen p q r, π (g' c) = g c) ∧ (∀ w ∈ yRels p q r, evalWord g' w = 1) ∧
      (evalWord g' D.Fw) ^ 9 = 1 := by
  classical
  have hz' := hz
  obtain ⟨hzc, hz2, hπz, hker⟩ := hz'
  have h0 : 0 < ngen p q r := by unfold ngen; omega
  choose l hl using fun c => hπ (g c)
  have hedgeG : ∀ c, 0 < c → c < ngen p q r → (g (parentY p q c) * g c) ^ 3 = 1 := by
    intro c hc0 hc
    obtain ⟨hlt, he⟩ := D.parent_edge c hc hc0
    have h := fam_pair hrel hlt hc
    have h3 : pairExp p q r (parentY p q c) c = 3 := by simp [pairExp, he]
    rwa [h3] at h
  obtain ⟨gh, hgh1, hgh2⟩ := exists_edge_lifts D hz (l := l) (g := g) (fun c _ => hl c) hedgeG
    (ngen p q r) le_rfl
  have hedge : ∀ e ∈ yEdges p q r, (gh e.1 * gh e.2) ^ 3 = 1 := by
    intro e he
    obtain ⟨hpos, hn, hpar⟩ := D.edges_parent e he
    have := hgh2 e.2 hpos hn
    rwa [hpar] at this
  have hsq : ∀ s < ngen p q r, IsZ z (gh s * gh s) := by
    intro s hs
    apply hker
    rw [map_mul, hgh1 s hs]
    exact fam_sq hrel hs
  have hcm : ∀ s t, nonadjB p q r s t = true → IsZ z (cm (gh s) (gh t)) := by
    intro s t hst
    obtain ⟨hs, ht⟩ := nonadjB_lt hst
    apply hker
    have hc := fam_comm hrel hst
    simp only [cm, map_mul, map_inv, hgh1 s hs, hgh1 t ht]
    calc g s * g t * (g s)⁻¹ * (g t)⁻¹ = (g t * g s) * (g s)⁻¹ * (g t)⁻¹ := by rw [hc]
      _ = 1 := by group
  have hlt_ev : ∀ w : List ℕ, (∀ c ∈ w, c < ngen p q r) → π (evalWord gh w) = evalWord g w := by
    intro w hw
    exact map_evalWord_of_forall π gh g w (fun c hc => hgh1 c (hw c hc))
  have hF' : IsZ z ((evalWord gh D.Fw) ^ 9) := by
    apply hker
    rw [map_pow, hlt_ev _ D.Fw_lt]
    exact hF
  have hsp_ev : (evalWord g (spiderWord p q)) ^ 10 = 1 := by
    have := hrel _ D.spider_mem
    rwa [evalWord_replicate_flatten'] at this
  have hsp : IsZ z ((evalWord gh (spiderWord p q)) ^ 10) := by
    apply hker
    rw [map_pow, hlt_ev _ D.spider_lt]
    exact hsp_ev
  have hI1 : IsZ z (((evalWord gh (spiderWord p q)) ^ 5 * gh 0) ^ 3) := by
    apply hker
    rw [map_pow, map_mul, map_pow, hlt_ev _ D.spider_lt, hgh1 0 h0]
    exact h1
  obtain ⟨ht12, ht13, ht23⟩ := D.triple
  obtain ⟨hq12, hq13, hq14, hq23, hq24, hq34⟩ := D.quad
  have hI2 : IsZ z ((evalWord gh Y)⁻¹ * (gh D.t₁ * gh D.t₂ * gh D.t₃) * evalWord gh Y *
      (gh D.q₁ * gh D.q₂ * gh D.q₃ * gh D.q₄)⁻¹) := by
    apply hker
    simp only [map_mul, map_inv, hlt_ev Y hYlt, hgh1 _ (nonadjB_lt ht12).1,
      hgh1 _ (nonadjB_lt ht12).2, hgh1 _ (nonadjB_lt ht13).2, hgh1 _ (nonadjB_lt hq12).1,
      hgh1 _ (nonadjB_lt hq12).2, hgh1 _ (nonadjB_lt hq13).2, hgh1 _ (nonadjB_lt hq14).2]
    have hY' := hY
    unfold ConjIdentity at hY'
    rw [hY']; group
  obtain ⟨hsq1, hcomm, hsp1⟩ := flags_vanish D hzc hz2 hedge hsq hcm hF' hsp hI1 hI2
  have hrelgh := rels_of_flags D hsq1 hcomm hedge hsp1
  rcases hF' with hF1 | hFz
  · exact ⟨gh, hgh1, hrelgh, hF1⟩
  · refine ⟨fun c => gh c * z, ?_, ?_, ?_⟩
    · intro c hc; rw [map_mul, hπz, mul_one]; exact hgh1 c hc
    · intro w hw
      rw [evalWord_mul_central hzc, hrelgh w hw, one_mul]
      have := D.even_rels w hw
      obtain ⟨m, hm⟩ : ∃ m, w.length = 2 * m := ⟨w.length / 2, by omega⟩
      rw [hm, pow_mul, sq, hz2, one_pow]
    · rw [evalWord_mul_central hzc]
      have hcomm : Commute (evalWord gh D.Fw) (z ^ D.Fw.length) :=
        Commute.pow_right (hzc _) _
      rw [hcomm.mul_pow, hFz]
      have hodd : z ^ (D.Fw.length * 9) = z := by
        obtain ⟨m, hm⟩ : ∃ m, D.Fw.length * 9 = 2 * m + 1 := ⟨D.Fw.length * 9 / 2, by
          have := D.Fw_odd; omega⟩
        rw [hm, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
      rw [← pow_mul, hodd, hz2]

abbrev QuotY (p q r : ℕ) (F : YGroup p q r) : Type := YGroup p q r ⧸ Subgroup.normalClosure {F}

@[expose] noncomputable def quotMk (F : YGroup p q r) : YGroup p q r →* QuotY p q r F :=
  QuotientGroup.mk' (Subgroup.normalClosure {F})

theorem quotMk_surjective (F : YGroup p q r) : Function.Surjective (quotMk F) :=
  QuotientGroup.mk'_surjective _

theorem quotMk_self (F : YGroup p q r) : quotMk F F = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure rfl)

@[expose] noncomputable def marked (F : YGroup p q r) (ρ : QuotY p q r F →* G) (c : ℕ) : G :=
  ρ (quotMk F (yGen p q r c))

theorem marked_evalWord (F : YGroup p q r) (ρ : QuotY p q r F →* G) (w : List ℕ) :
    evalWord (marked F ρ) w = (ρ.comp (quotMk F)) (evalWord (yGen p q r) w) :=
  (map_evalWord' (ρ.comp (quotMk F)) (yGen p q r) w).symm

theorem marked_rels (F : YGroup p q r) (ρ : QuotY p q r F →* G) :
    ∀ w ∈ yRels p q r, evalWord (marked F ρ) w = 1 := by
  intro w hw
  rw [marked_evalWord, CFSG.YGroups.evalWord_yGen_of_mem hw, map_one]

theorem marked_mul_self (F : YGroup p q r) (ρ : QuotY p q r F →* G) (c : ℕ) :
    marked F ρ c * marked F ρ c = 1 := by
  show ρ (quotMk F (yGen p q r c)) * ρ (quotMk F (yGen p q r c)) = 1
  rw [← map_mul, ← map_mul, CFSG.YGroups.yGen_mul_self, map_one, map_one]

theorem marked_F {F : YGroup p q r} {Fw : List ℕ} (hF : F = evalWord (yGen p q r) Fw ^ 9)
    (ρ : QuotY p q r F →* G) : (evalWord (marked F ρ) Fw) ^ 9 = 1 := by
  rw [marked_evalWord, ← map_pow, ← hF]
  simp [quotMk_self]

theorem conjIdentity_of_eq (D : FlagData p q r) {g : ℕ → G} (hinv : ∀ c, g c * g c = 1)
    (Y : List ℕ)
    (h : evalWord g (Y.reverse ++ [D.t₁, D.t₂, D.t₃] ++ Y) =
      evalWord g [D.q₁, D.q₂, D.q₃, D.q₄]) : ConjIdentity D g Y := by
  rw [evalWord_append, evalWord_append, evalWord_reverse_inv hinv] at h
  simpa [ConjIdentity, evalWord, mul_assoc] using h

theorem spiderIdentity_of_eq {g : ℕ → G}
    (h : evalWord g
      (List.replicate 3 ((List.replicate 5 (spiderWord p q)).flatten ++ [0])).flatten = 1) :
    SpiderIdentity p q g := by
  rw [evalWord_replicate_flatten', evalWord_append, evalWord_replicate_flatten'] at h
  simpa [SpiderIdentity, evalWord] using h

theorem exists_hom_quot (D : FlagData p q r) {F : YGroup p q r}
    (hFdef : F = evalWord (yGen p q r) D.Fw ^ 9) {π : E →* G} {z : E} (hz : CentralKernel π z)
    (hπ : Function.Surjective π) (ρ : QuotY p q r F →* G) {Y : List ℕ}
    (hYlt : ∀ c ∈ Y, c < ngen p q r) (hY : ConjIdentity D (marked F ρ) Y)
    (h1 : SpiderIdentity p q (marked F ρ)) : ∃ θ : QuotY p q r F →* E, π.comp θ = ρ := by
  obtain ⟨g', hg1, hg2, hg3⟩ :=
    lift_family D hz hπ (marked_rels F ρ) (marked_F hFdef ρ) hYlt hY h1
  let ψ : YGroup p q r →* E := yModelHom g' hg2
  have hψ : ∀ c < ngen p q r, ψ (yGen p q r c) = g' c := fun c hc => yModelHom_yGen hc
  have hFψ : ψ F = 1 := by
    rw [hFdef, map_pow, map_evalWord']
    have : evalWord (fun c => ψ (yGen p q r c)) D.Fw = evalWord g' D.Fw := by
      apply CFSG.YGroups.evalWord_congr
      intro c hc
      exact hψ c (D.Fw_lt c hc)
    rw [this]; exact hg3
  have hle : Subgroup.normalClosure {F} ≤ ψ.ker :=
    Subgroup.normalClosure_le_normal (by simpa [MonoidHom.mem_ker] using hFψ)
  refine ⟨QuotientGroup.lift (Subgroup.normalClosure {F}) ψ hle, ?_⟩
  refine (MonoidHom.cancel_right (quotMk_surjective F)).1 ?_
  refine PresentedGroup.ext fun c => ?_
  have hc : (c : ℕ) < ngen p q r := c.2
  simp only [MonoidHom.comp_apply]
  have e1 : (PresentedGroup.of c : YGroup p q r) = yGen p q r c :=
    (CFSG.YGroups.yGen_of_lt c.2).symm
  rw [e1]
  show π (ψ (yGen p q r c)) = ρ (quotMk F (yGen p q r c))
  rw [hψ c hc, hg1 c hc]
  rfl

end CFSG.Sporadic.Recognition.YCover
