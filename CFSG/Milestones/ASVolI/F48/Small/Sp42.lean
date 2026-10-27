module

public import CFSG.Milestones.ASVolI.F48.Small.Rel
public import CFSG.Milestones.ASVolI.F48.Small.Pres
public import Certificates.Certificate7530
public import Certificates.Certificate7531
public import CFSG.Quasithin.Recognition.GoldschmidtF112SSSp42
public import CFSG.Milestones.ASVolI.F48.Id
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.CosetTable CFSG.Quasithin.F6.GoldAmS Equiv

theorem burnsideF48s_sp42_sup : S6G1 ⊔ S6G2 = ⊤ := by
  rcases lattice_S6 (S6G1 ⊔ S6G2) (inf_le_left.trans le_sup_left) with h | h | h | h
  · exact absurd (h ▸ le_sup_left : S6G1 ≤ S6G1 ⊓ S6G2) (not_le_of_gt T_lt_G1)
  · exact absurd (h ▸ le_sup_right : S6G2 ≤ S6G1) S6G2_not_le_G1
  · exact absurd (h ▸ le_sup_left : S6G1 ≤ S6G2) S6G1_not_le_G2
  · exact h

theorem burnsideF48s_sp42_isLieParabolics :
    IsLieParabolics 2 (⊤ : Subgroup S6) (S6G1 ⊓ S6G2) S6G1 S6G2 := by
  have hcardS6 : Nat.card S6 = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have hidx : (S6G1 ⊓ S6G2).index = 45 := by
    have h := Subgroup.card_mul_index (S6G1 ⊓ S6G2)
    rw [card_S6T, hcardS6] at h
    omega
  refine ⟨⟨S6G1 ⊓ S6G2, ⟨le_top, IsPGroup.of_card (p := 2) (n := 4) card_S6T, ?_⟩, ?_⟩, ?_, rfl,
    fun Q => ?_⟩
  · rw [Subgroup.relIndex_top_right, hidx]; decide
  · rw [top_inf_eq]
    exact le_antisymm Subgroup.le_normalizer normalizer_S6T_le
  · intro h
    exact S6G1_not_le_G2 h.le
  · have hmax1 : ∀ R : Subgroup S6, S6G1 < R → R = ⊤ := by
      intro R hR
      rcases lattice_S6 R (inf_le_left.trans hR.le) with h | h | h | h
      · exact absurd (h ▸ hR.le) (not_le_of_gt T_lt_G1)
      · exact absurd h hR.ne'
      · exact absurd (h ▸ hR.le) S6G1_not_le_G2
      · exact h
    have hmax2 : ∀ R : Subgroup S6, S6G2 < R → R = ⊤ := by
      intro R hR
      rcases lattice_S6 R (inf_le_right.trans hR.le) with h | h | h | h
      · exact absurd (h ▸ hR.le) (not_le_of_gt T_lt_G2)
      · exact absurd (h ▸ hR.le) S6G2_not_le_G1
      · exact absurd h hR.ne'
      · exact h
    have hne1 : S6G1 ≠ ⊤ := fun h => S6G2_not_le_G1 (h ▸ le_top)
    have hne2 : S6G2 ≠ ⊤ := fun h => S6G1_not_le_G2 (h ▸ le_top)
    constructor
    · rintro ⟨hTQ, -, hQne, hQmax⟩
      rcases lattice_S6 Q hTQ with h | h | h | h
      · exfalso
        subst h
        have := hQmax S6G1 T_lt_G1 le_top
        exact hne1 this
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hQne
    · rintro (rfl | rfl)
      · exact ⟨inf_le_left, le_top, hne1, fun R hR _ => hmax1 R hR⟩
      · exact ⟨inf_le_right, le_top, hne2, fun R hR _ => hmax2 R hR⟩

section Facts

theorem burnsideF48s_sp42_facts : burnsideF48s_sp42PermFacts := Certificates.certificate7531

theorem burnsideF48s_sp42_closure_UV :
    Subgroup.closure ({burnsideF48s_sp42UV 1, burnsideF48s_sp42UV 0} : Set S6) = ⊤ := by
  have hc : (burnsideF48s_sp42UV 1).IsCycle :=
    List.isCycle_formPerm (by decide) (by decide)
  have hs : (burnsideF48s_sp42UV 1).support = Finset.univ := by decide
  have h := Equiv.Perm.closure_cycle_adjacent_swap hc hs 1
  have e : swap 1 (burnsideF48s_sp42UV 1 1) = burnsideF48s_sp42UV 0 := by decide
  rwa [e] at h

theorem burnsideF48s_sp42_aut_inner (ψ : S6 ≃* S6) (h1 : ∀ x, ψ x ∈ S6G1 ↔ x ∈ S6G1)
    (h2 : ∀ x, ψ x ∈ S6G2 ↔ x ∈ S6G2) : ∃ g : S6, ∀ x, ψ x = g * x * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hrUV, hw1, hw2, haut⟩ := burnsideF48s_sp42_facts
  have hUVψ : ∀ s : String, burnsideF48s_sp42EvUV ![ψ (burnsideF48s_sp42UV 0),
      ψ (burnsideF48s_sp42UV 1)] s = ψ (burnsideF48s_sp42EvUV burnsideF48s_sp42UV s) := by
    intro s
    unfold burnsideF48s_sp42EvUV
    refine (burnsideF48s_ev_congr _ fun l _ => ?_).trans
      (burnsideF48s_ev_map ψ.toMonoidHom burnsideF48s_sp42UV _)
    obtain ⟨i, b⟩ := l
    fin_cases i <;> rfl
  have hu1 : burnsideF48s_sp42UV 0 ∈ S6G1 := mem_S6G1.2 (by decide)
  have hv2 : burnsideF48s_sp42UV 1 ∈ S6G2 := mem_S6G2.2 (by decide)
  have huv : burnsideF48s_sp42UV 0 ≠ burnsideF48s_sp42UV 1 := by decide
  have hcond : burnsideF48s_sp42AutCond (ψ (burnsideF48s_sp42UV 0)) (ψ (burnsideF48s_sp42UV 1)) =
      true := by
    unfold burnsideF48s_sp42AutCond
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact mem_S6G1.1 ((h1 _).2 hu1)
    · exact mem_S6G2.1 ((h2 _).2 hv2)
    · exact fun h => huv (ψ.injective h)
    · intro s hs
      rw [hUVψ, hrUV s hs, map_one]
    · intro s hs
      rw [hUVψ]
      exact mem_S6G1.1 ((h1 _).2 (mem_S6G1.2 (hw1 s hs)))
    · intro s hs
      rw [hUVψ]
      exact mem_S6G2.1 ((h2 _).2 (mem_S6G2.2 (hw2 s hs)))
  obtain ⟨g, hgu, hgv⟩ := haut _ _ hcond
  refine ⟨g, fun x => ?_⟩
  have hle : Subgroup.closure ({burnsideF48s_sp42UV 1, burnsideF48s_sp42UV 0} : Set S6) ≤
      MonoidHom.eqLocus ψ.toMonoidHom (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · show ψ _ = g * _ * g⁻¹
      rw [hgv]
    · show ψ _ = g * _ * g⁻¹
      rw [hgu]
  rw [burnsideF48s_sp42_closure_UV] at hle
  exact hle (Subgroup.mem_top x)

theorem burnsideF48s_sp42_Gp_top {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 1 Gp M₁ M₂)
    (hP : IsLieParabolics 2 Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) : Gp = ⊤ := by
  haveI : Gp.Normal := hyp.normal
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, K, hK, hKf, hc, he⟩ := hyp.model
  obtain ⟨ε₀⟩ := nonempty_mulEquiv_S6_of_isSp42 (W := ↥Gp) ⟨K, hK, hKf, by simpa using hc, he⟩
  obtain ⟨ε, -, hε⟩ := burnsideF48_identify ε₀.symm burnsideF48s_sp42_isLieParabolics hP
  have hconj : ∀ {M : Subgroup E} {e : E}, e ∈ M → ∀ y : E, e * y * e⁻¹ ∈ M ↔ y ∈ M := by
    intro M e he y
    constructor
    · intro h
      have := M.mul_mem (M.mul_mem (M.inv_mem he) h) he
      simpa [mul_assoc] using this
    · intro h
      exact M.mul_mem (M.mul_mem he h) (M.inv_mem he)
  have key : ∀ e ∈ M₁ ⊓ M₂, e ∈ Gp := by
    intro e he
    let c : ↥Gp ≃* ↥Gp := MulAut.conjNormal e
    have hc : ∀ y : ↥Gp, ((c y : ↥Gp) : E) = e * y * e⁻¹ := fun y => MulAut.conjNormal_apply e y
    let ψ : S6 ≃* S6 := ε.trans (c.trans ε.symm)
    have hψ : ∀ x, ε (ψ x) = c (ε x) := fun x => ε.apply_symm_apply _
    have hmemImg : ∀ (Q : Subgroup S6) (x : S6), ((ε x : ↥Gp) : E) ∈ burnsideF48_img ε Q ↔ x ∈ Q :=
      fun Q x => burnsideF48_mem_img ε Q x
    have hpres : ∀ (Q : Subgroup S6) (M : Subgroup E), burnsideF48_img ε Q = Gp ⊓ M → e ∈ M →
        ∀ x, ψ x ∈ Q ↔ x ∈ Q := by
      intro Q M hQ heM x
      rw [← hmemImg, ← hmemImg, hψ, hQ, hc]
      simp only [Subgroup.mem_inf]
      rw [hconj heM]
      exact ⟨fun h => ⟨(ε x).2, h.2⟩,
        fun h => ⟨(inferInstance : Gp.Normal).conj_mem _ (ε x).2 e, h.2⟩⟩
    have h1 : ∀ x, ψ x ∈ S6G1 ↔ x ∈ S6G1 := by
      rcases hε with ⟨hA, -⟩ | ⟨hA, -⟩
      · exact hpres S6G1 M₁ hA he.1
      · exact hpres S6G1 M₂ hA he.2
    have h2 : ∀ x, ψ x ∈ S6G2 ↔ x ∈ S6G2 := by
      rcases hε with ⟨-, hB⟩ | ⟨-, hB⟩
      · exact hpres S6G2 M₂ hB he.2
      · exact hpres S6G2 M₁ hB he.1
    obtain ⟨g, hg⟩ := burnsideF48s_sp42_aut_inner ψ h1 h2
    set t : E := ((ε g : ↥Gp) : E) with htdef
    have hcy : ∀ y : ↥Gp, e * y * e⁻¹ = t * y * t⁻¹ := by
      intro y
      have h := congrArg ε (hg (ε.symm y))
      rw [hψ, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h
      have h' := congrArg Subtype.val h
      rw [hc] at h'
      simpa [htdef] using h'
    have hcent : t⁻¹ * e ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h' := hcy ⟨y, hy⟩
      simp only at h'
      calc y * (t⁻¹ * e) = t⁻¹ * (t * y * t⁻¹) * e := by group
        _ = t⁻¹ * (e * y * e⁻¹) * e := by rw [h']
        _ = t⁻¹ * e * y := by group
    rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcent
    have he' : e = t := by
      calc e = t * (t⁻¹ * e) := by group
        _ = t := by rw [hcent, mul_one]
    rw [he']
    exact (ε g).2
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, k, hk, rfl⟩ := hyp.split x
  exact Gp.mul_mem hn (key k hk)

end Facts

section Core

theorem burnsideF48s_sp42_card_S6 : Nat.card S6 = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl

theorem burnsideF48s_sp42_card_PG (j : ℕ) (hj : j < 4) :
    Finite (PG 5 (burnsideF48s_sp42Ws j)) ∧
      Nat.card (PG 5 (burnsideF48s_sp42Ws j)) ≤ if j = 1 then 720 else 48 := by
  exact Certificates.certificate7530 j hj

theorem burnsideF48s_sp42_core {Y : Type} [Group Y] (f₁ : ↥S6G1 →* Y) (f₂ : ↥S6G2 →* Y)
    (h12 : ∀ (t : S6) (h : t ∈ S6G1 ⊓ S6G2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hcard : 720 ≤ Nat.card Y)
    {x y : S6} (hx : x ∈ S6G1) (hxT : x ∉ S6G2) (hx2 : x * x = 1)
    (hy : y ∈ S6G2) (hyT : y ∉ S6G1) (hy2 : y * y = 1)
    (hrel : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ 4 = 1) :
    ∃ φ : Y ≃* S6, (∀ z : ↥S6G1, φ (f₁ z) = z) ∧ (∀ z : ↥S6G2, φ (f₂ z) = z) := by
  obtain ⟨hL1, hL2, hrels, hcovA, hcovB, hlA, hlB, hcand, hext1, -, -, -, -⟩ :=
    burnsideF48s_sp42_facts
  have hL1' : ∀ i : Fin 5, i ≠ 4 → burnsideF48s_sp42L i ∈ S6G1 :=
    fun i hi => mem_S6G1.2 (hL1 i hi)
  have hL2' : ∀ i : Fin 5, i ≠ 3 → burnsideF48s_sp42L i ∈ S6G2 :=
    fun i hi => mem_S6G2.2 (hL2 i hi)
  let LA : Fin 5 → ↥S6G1 := fun i => if h : i = 4 then 1 else ⟨burnsideF48s_sp42L i, hL1' i h⟩
  let LB : Fin 5 → ↥S6G2 := fun i => if h : i = 3 then 1 else ⟨burnsideF48s_sp42L i, hL2' i h⟩
  let yL : Fin 5 → Y := fun i => if i = 4 then f₂ (LB i) else f₁ (LA i)
  have hevA : ∀ w : List (Fin 5 × Bool), (∀ l ∈ w, l.1 ≠ 4) →
      ((burnsideF48s_ev LA w : ↥S6G1) : S6) = burnsideF48s_ev burnsideF48s_sp42L w ∧
        burnsideF48s_ev yL w = f₁ (burnsideF48s_ev LA w) := by
    intro w hw
    refine ⟨(burnsideF48s_ev_map S6G1.subtype LA w).symm.trans
      (burnsideF48s_ev_congr w fun l hl => ?_), (burnsideF48s_ev_congr w fun l hl => ?_).trans
      (burnsideF48s_ev_map f₁ LA w)⟩
    · simp [LA, hw l hl]
    · simp [yL, hw l hl]
  have hevB : ∀ w : List (Fin 5 × Bool), (∀ l ∈ w, l.1 ≠ 3) →
      ((burnsideF48s_ev LB w : ↥S6G2) : S6) = burnsideF48s_ev burnsideF48s_sp42L w ∧
        burnsideF48s_ev yL w = f₂ (burnsideF48s_ev LB w) := by
    intro w hw
    refine ⟨(burnsideF48s_ev_map S6G2.subtype LB w).symm.trans
      (burnsideF48s_ev_congr w fun l hl => ?_), (burnsideF48s_ev_congr w fun l hl => ?_).trans
      (burnsideF48s_ev_map f₂ LB w)⟩
    · simp [LB, hw l hl]
    · have h3 := hw l hl
      by_cases h4 : l.1 = 4
      · simp [yL, h4, LB]
      · have hT : burnsideF48s_sp42L l.1 ∈ S6G1 ⊓ S6G2 := ⟨hL1' _ h4, hL2' _ h3⟩
        have := h12 _ hT
        simp only [yL, LA, LB, h4, h3, if_false, dif_neg, not_false_eq_true]
        exact this
  have hrelY : ∀ s ∈ burnsideF48s_sp42RelA ++ burnsideF48s_sp42RelB,
      burnsideF48s_ev yL (burnsideF48s_sp42Word s) = 1 := by
    intro s hs
    rcases List.mem_append.1 hs with hsA | hsB
    · have hl : ∀ l ∈ burnsideF48s_sp42Word s, l.1 ≠ 4 :=
        hlA s (List.mem_append_right _ hsA)
      obtain ⟨e1, e2⟩ := hevA _ hl
      rw [e2]
      have : burnsideF48s_ev LA (burnsideF48s_sp42Word s) = 1 :=
        Subtype.ext (e1.trans (hrels s hs))
      rw [this, map_one]
    · have hl : ∀ l ∈ burnsideF48s_sp42Word s, l.1 ≠ 3 :=
        hlB s (List.mem_append_right _ hsB)
      obtain ⟨e1, e2⟩ := hevB _ hl
      rw [e2]
      have : burnsideF48s_ev LB (burnsideF48s_sp42Word s) = 1 :=
        Subtype.ext (e1.trans (hrels s hs))
      rw [this, map_one]
  obtain ⟨g, hg1, hg2, j, hj, hgx, hgy⟩ := hcand x (mem_S6G1.1 hx) (fun h => hxT (mem_S6G2.2 h))
    hx2 y (mem_S6G2.1 hy) (fun h => hyT (mem_S6G1.2 h)) hy2
  have hg1' : g ∈ S6G1 := mem_S6G1.2 hg1
  have hg2' : g ∈ S6G2 := mem_S6G2.2 hg2
  have hextY : burnsideF48s_ev yL (burnsideF48s_sp42Ext j) = 1 := by
    have hlA' : ∀ l ∈ burnsideF48s_sp42Word (burnsideF48s_sp42CandA.getD j ""), l.1 ≠ 4 := by
      refine hlA _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp [burnsideF48s_sp42CandA]
    have hlB' : ∀ l ∈ burnsideF48s_sp42Word (burnsideF48s_sp42CandB.getD j ""), l.1 ≠ 3 := by
      refine hlB _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp [burnsideF48s_sp42CandB]
    obtain ⟨a1, a2⟩ := hevA _ hlA'
    obtain ⟨b1, b2⟩ := hevB _ hlB'
    unfold burnsideF48s_sp42Ext
    rw [burnsideF48s_ev_replicate, burnsideF48s_ev_append, a2, b2]
    have ea : burnsideF48s_ev LA (burnsideF48s_sp42Word (burnsideF48s_sp42CandA.getD j "")) =
        ⟨g, hg1'⟩ * ⟨x, hx⟩ * ⟨g, hg1'⟩⁻¹ := by
      apply Subtype.ext
      rw [a1]
      exact hgx.symm
    have eb : burnsideF48s_ev LB (burnsideF48s_sp42Word (burnsideF48s_sp42CandB.getD j "")) =
        ⟨g, hg2'⟩ * ⟨y, hy⟩ * ⟨g, hg2'⟩⁻¹ := by
      apply Subtype.ext
      rw [b1]
      exact hgy.symm
    rw [ea, eb, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← h12 g ⟨hg1', hg2'⟩]
    set G := f₁ ⟨g, hg1'⟩
    have : G * f₁ ⟨x, hx⟩ * G⁻¹ * (G * f₂ ⟨y, hy⟩ * G⁻¹) = G * (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) * G⁻¹ := by
      group
    rw [this, ← MulAut.conj_apply, ← map_pow, hrel, map_one]
  have hws : ∀ w ∈ burnsideF48s_sp42Ws j, burnsideF48s_ev yL w = 1 := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      exact hrelY s hs
    · rw [List.mem_singleton] at h
      rw [h]
      exact hextY
  have hcovA' : ∀ z : ↥S6G1, ∃ w : List (Fin 5 × Bool), (∀ l ∈ w, l.1 ≠ 4) ∧
      burnsideF48s_ev LA w = z := by
    intro z
    obtain ⟨s, hs, hsz⟩ := hcovA z (mem_S6G1.1 z.2)
    have hl := hlA s (List.mem_append_left _ (List.mem_append_left _ hs))
    exact ⟨_, hl, Subtype.ext ((hevA _ hl).1.trans hsz)⟩
  have hcovB' : ∀ z : ↥S6G2, ∃ w : List (Fin 5 × Bool), (∀ l ∈ w, l.1 ≠ 3) ∧
      burnsideF48s_ev LB w = z := by
    intro z
    obtain ⟨s, hs, hsz⟩ := hcovB z (mem_S6G2.1 z.2)
    have hl := hlB s (List.mem_append_left _ (List.mem_append_left _ hs))
    exact ⟨_, hl, Subtype.ext ((hevB _ hl).1.trans hsz)⟩
  have hgenY : Subgroup.closure (Set.range yL) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    have hmem : ∀ w : List (Fin 5 × Bool), burnsideF48s_ev yL w ∈ Subgroup.closure (Set.range yL) :=
      fun w => burnsideF48s_ev_mem yL w fun l _ => Subgroup.subset_closure ⟨l.1, rfl⟩
    refine sup_le ?_ ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, hl, rfl⟩ := hcovA' z
      rw [← (hevA w hl).2]
      exact hmem w
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, hl, rfl⟩ := hcovB' z
      rw [← (hevB w hl).2]
      exact hmem w
  obtain ⟨hfin, hcardP⟩ := burnsideF48s_sp42_card_PG j hj
  have hY := burnsideF48s_card_le_of_pres hws hgenY
  by_cases hj1 : j = 1
  swap
  · exfalso
    rw [if_neg hj1] at hcardP
    omega
  subst hj1
  rw [if_pos rfl] at hcardP
  have hdS : ∀ w ∈ burnsideF48s_sp42Ws 1, burnsideF48s_ev burnsideF48s_sp42L w = 1 := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      exact hrels s hs
    · rw [List.mem_singleton] at h
      rw [h]
      exact hext1
  have hgenS : Subgroup.closure (Set.range burnsideF48s_sp42L) = ⊤ := by
    rw [eq_top_iff, ← burnsideF48s_sp42_sup]
    have hmem : ∀ w : List (Fin 5 × Bool), burnsideF48s_ev burnsideF48s_sp42L w ∈
        Subgroup.closure (Set.range burnsideF48s_sp42L) :=
      fun w => burnsideF48s_ev_mem _ w fun l _ => Subgroup.subset_closure ⟨l.1, rfl⟩
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨w, hl, hw⟩ := hcovA' ⟨z, hz⟩
      have := (hevA w hl).1
      rw [hw] at this
      rw [show z = burnsideF48s_ev burnsideF48s_sp42L w from this]
      exact hmem w
    · obtain ⟨w, hl, hw⟩ := hcovB' ⟨z, hz⟩
      have := (hevB w hl).1
      rw [hw] at this
      rw [show z = burnsideF48s_ev burnsideF48s_sp42L w from this]
      exact hmem w
  obtain ⟨φ, hφ⟩ := burnsideF48s_equiv_of_pres hws hdS hgenY hgenS
    (by rw [burnsideF48s_sp42_card_S6]; exact hcardP) (by rw [burnsideF48s_sp42_card_S6]; exact hcard)
  have hφw : ∀ w : List (Fin 5 × Bool), φ (burnsideF48s_ev yL w) =
      burnsideF48s_ev burnsideF48s_sp42L w := by
    intro w
    exact (burnsideF48s_ev_map φ.toMonoidHom yL w).symm.trans
      (burnsideF48s_ev_congr w fun l _ => hφ l.1)
  refine ⟨φ, fun z => ?_, fun z => ?_⟩
  · obtain ⟨w, hl, rfl⟩ := hcovA' z
    rw [← (hevA w hl).2, hφw, (hevA w hl).1]
  · obtain ⟨w, hl, rfl⟩ := hcovB' z
    rw [← (hevB w hl).2, hφw, (hevB w hl).1]

end Core

theorem burnsideF48s_range_comp_mulEquiv {A B C : Type*} [Group A] [Group B] [Group C] (g : B →* C)
    (e : A ≃* B) : (g.comp e.toMonoidHom).range = g.range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨e.symm b, by simp⟩

@[expose] noncomputable def burnsideF48s_restrictTo {D E : Type} [Group D] [Group E] (θ : D ≃* E)
    {A : Subgroup D} {M : Subgroup E} (hM : M = A.map θ.toMonoidHom) : ↥A ≃* ↥M :=
  (θ.subgroupMap A).trans (MulEquiv.subgroupCongr hM.symm)

theorem burnsideF48s_pCoreOf_eq_self {E : Type} [Group E] {B : Subgroup E} (hp : IsPGroup 2 ↥B) :
    pCoreOf 2 B = B := by
  apply le_antisymm (burnsideF48s_pCoreOf_le 2 B)
  intro b hb
  have htop : (⊤ : Subgroup ↥B) ≤ CFSG.pCore 2 ↥B := by
    refine le_sSup ⟨⟨fun x hx g => ?_⟩, hp.of_equiv Subgroup.topEquiv.symm⟩
    exact Subgroup.mem_top _
  exact ⟨⟨b, hb⟩, htop (Subgroup.mem_top _), rfl⟩

section Final

theorem burnsideF48s_sp42_qe {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : S6 ≃* E)
    {A₁ A₂ : Subgroup S6} (hA : (A₁ = S6G1 ∧ A₂ = S6G2) ∨ (A₁ = S6G2 ∧ A₂ = S6G1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hcard : 720 ≤ Nat.card Y)
    {a : ↥M₁} {b : ↥M₂} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hrel : (β.φ1 a * β.φ2 b) ^ 4 = 1) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  let eG : ↥(M₁ ⊔ M₂) ≃* E := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have heG : ∀ z : ↥(M₁ ⊔ M₂), eG z = z := fun _ => rfl
  have h12β : ∀ (t : E) (h1 : t ∈ M₁) (h2 : t ∈ M₂), β.φ1 ⟨t, h1⟩ = β.φ2 ⟨t, h2⟩ :=
    fun t h1 h2 => (β.comm1 ⟨t, ⟨h1, h2⟩⟩).trans (β.comm2 ⟨t, ⟨h1, h2⟩⟩).symm
  have hmemθ : ∀ {A : Subgroup S6} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ z : S6, θ z ∈ M ↔ z ∈ A := by
    intro A M hM z
    rw [hM]
    exact Subgroup.mem_map_iff_mem θ.injective
  have hpre : ∀ {A : Subgroup S6} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ u : ↥M, ∃ z : S6, z ∈ A ∧ θ z = u := by
    intro A M hM u
    obtain ⟨z, hz, hzu⟩ : (u : E) ∈ A.map θ.toMonoidHom := by rw [← hM]; exact u.2
    exact ⟨z, hz, hzu⟩
  rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    let r₁ := burnsideF48s_restrictTo θ hM1
    let r₂ := burnsideF48s_restrictTo θ hM2
    let f₁ : ↥S6G1 →* Y := β.φ1.comp r₁.toMonoidHom
    let f₂ : ↥S6G2 →* Y := β.φ2.comp r₂.toMonoidHom
    have hf12 : ∀ (t : S6) (h : t ∈ S6G1 ⊓ S6G2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ :=
      fun t h => h12β (θ t) _ _
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ1.range from burnsideF48s_range_comp_mulEquiv _ _,
        show f₂.range = β.φ2.range from burnsideF48s_range_comp_mulEquiv _ _]
      exact β.gen
    obtain ⟨x, hx, hxa⟩ := hpre hM1 a
    obtain ⟨y, hy, hyb⟩ := hpre hM2 b
    have hxT : x ∉ S6G2 := fun h => haM (hxa ▸ (hmemθ hM2 x).2 h)
    have hyT : y ∉ S6G1 := fun h => hbM (hyb ▸ (hmemθ hM1 y).2 h)
    have hx2 : x * x = 1 := θ.injective (by rw [map_mul, hxa, map_one]; exact congrArg Subtype.val ha2)
    have hy2 : y * y = 1 := θ.injective (by rw [map_mul, hyb, map_one]; exact congrArg Subtype.val hb2)
    have hra : r₁ ⟨x, hx⟩ = a := Subtype.ext hxa
    have hrb : r₂ ⟨y, hy⟩ = b := Subtype.ext hyb
    have hrel' : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ 4 = 1 := by
      show (β.φ1 (r₁ ⟨x, hx⟩) * β.φ2 (r₂ ⟨y, hy⟩)) ^ 4 = 1
      rw [hra, hrb]; exact hrel
    obtain ⟨φ, hφ1, hφ2⟩ :=
      burnsideF48s_sp42_core f₁ f₂ hf12 hfgen hcard hx hxT hx2 hy hyT hy2 hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM2 z).2 hz
  ·
    let r₁ := burnsideF48s_restrictTo θ hM2
    let r₂ := burnsideF48s_restrictTo θ hM1
    let f₁ : ↥S6G1 →* Y := β.φ2.comp r₁.toMonoidHom
    let f₂ : ↥S6G2 →* Y := β.φ1.comp r₂.toMonoidHom
    have hf12 : ∀ (t : S6) (h : t ∈ S6G1 ⊓ S6G2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ :=
      fun t h => (h12β (θ t) _ _).symm
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ2.range from burnsideF48s_range_comp_mulEquiv _ _,
        show f₂.range = β.φ1.range from burnsideF48s_range_comp_mulEquiv _ _, sup_comm]
      exact β.gen
    obtain ⟨x, hx, hxb⟩ := hpre hM2 b
    obtain ⟨y, hy, hya⟩ := hpre hM1 a
    have hxT : x ∉ S6G2 := fun h => hbM (hxb ▸ (hmemθ hM1 x).2 h)
    have hyT : y ∉ S6G1 := fun h => haM (hya ▸ (hmemθ hM2 y).2 h)
    have hx2 : x * x = 1 := θ.injective (by rw [map_mul, hxb, map_one]; exact congrArg Subtype.val hb2)
    have hy2 : y * y = 1 := θ.injective (by rw [map_mul, hya, map_one]; exact congrArg Subtype.val ha2)
    have hrb : r₁ ⟨x, hx⟩ = b := Subtype.ext hxb
    have hra : r₂ ⟨y, hy⟩ = a := Subtype.ext hya
    have hrel' : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ 4 = 1 := by
      show (β.φ2 (r₁ ⟨x, hx⟩) * β.φ1 (r₂ ⟨y, hy⟩)) ^ 4 = 1
      rw [hra, hrb]
      have e : (β.φ2 b * β.φ1 a) ^ 4 = (β.φ1 a)⁻¹ * (β.φ1 a * β.φ2 b) ^ 4 * β.φ1 a := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [e, hrel, mul_one, inv_mul_cancel]
    obtain ⟨φ, hφ1, hφ2⟩ :=
      burnsideF48s_sp42_core f₁ f₂ hf12 hfgen hcard hx hxT hx2 hy hyT hy2 hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM2 z).2 hz

end Final

section Main

theorem burnsideF48s_small_Sp4_two (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .Sp4 2 1 Gp M₁ M₂) : F48Concl .Sp4 2 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hGp := burnsideF48s_sp42_Gp_top hyp hP
  subst hGp
  obtain ⟨-, -, K, hK, hKf, hc, he⟩ := hyp.model
  obtain ⟨ε₀⟩ := nonempty_mulEquiv_S6_of_isSp42 (W := ↥(⊤ : Subgroup E))
    ⟨K, hK, hKf, by simpa using hc, he⟩
  obtain ⟨ε, hεT, hε⟩ := burnsideF48_identify ε₀.symm burnsideF48s_sp42_isLieParabolics hP
  let θ : S6 ≃* E := ε.trans Subgroup.topEquiv
  have himg : ∀ Q : Subgroup S6, burnsideF48_img ε Q = Q.map θ.toMonoidHom := by
    intro Q
    unfold burnsideF48_img
    rw [Subgroup.map_map]
    rfl
  have hT : M₁ ⊓ M₂ = (S6G1 ⊓ S6G2).map θ.toMonoidHom := by
    rw [← himg, hεT, top_inf_eq]
  have h2grp : IsPGroup 2 ↥(M₁ ⊓ M₂) := by
    rw [hT]
    exact IsPGroup.of_card (n := 4)
      (by rw [Subgroup.card_map_of_injective θ.injective]; exact card_S6T)
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .Sp4 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  obtain ⟨a, b, K', haM, hbM, hK', -, -, ha2, hb2, hrel⟩ :=
    burnsideF48s_rel h45 h46 hyp ⟨by decide, by decide⟩ β hβ hs
  have hcore : pCoreOf 2 ((⊤ : Subgroup E) ⊓ (M₁ ⊓ M₂)) = M₁ ⊓ M₂ := by
    rw [top_inf_eq]
    exact burnsideF48s_pCoreOf_eq_self h2grp
  rw [hcore] at hK'
  have hKbot : K' = ⊥ := by
    have h1 : (M₁ ⊓ M₂) ⊓ K' = ⊥ := hK'.2.2.1
    rwa [inf_eq_right.2 hK'.2.1] at h1
  subst hKbot
  have ha2' : a * a = 1 := Subtype.ext (by simpa using ha2)
  have hb2' : b * b = 1 := Subtype.ext (by simpa using hb2)
  obtain ⟨c, hcK, hrel'⟩ := hrel a b (by simp) (by simp)
  have hc1 : c = 1 := Subtype.ext (by simpa using hcK)
  have hc1' : β.φ12 c = 1 := (congrArg β.φ12 hc1).trans (map_one β.φ12)
  rw [hc1'] at hrel'
  have hcard : 720 ≤ Nat.card Y := by
    have h13 := (burnside_as_F_4_13_of h45 h46 .Sp4 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
    rw [card_G0] at h13
    rw [h13, ← Nat.card_congr θ.toEquiv, burnsideF48s_sp42_card_S6]
  rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48s_sp42_qe θ (Or.inl ⟨rfl, rfl⟩) (by rw [← himg, h1, top_inf_eq])
      (by rw [← himg, h2, top_inf_eq]) hyp.gen β hβ hcard haM hbM ha2' hb2' hrel'
  · exact burnsideF48s_sp42_qe θ (Or.inr ⟨rfl, rfl⟩) (by rw [← himg, h2, top_inf_eq])
      (by rw [← himg, h1, top_inf_eq]) hyp.gen β hβ hcard haM hbM ha2' hb2' hrel'

end Main

end CFSG.ASVolI
