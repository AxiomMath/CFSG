module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAux4

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem not_mem_sup_zpowers {E B : Subgroup G} (hEB : E ⊓ B = ⊥) {f₁ f₂ : G} (hf₁ : f₁ ∈ B)
    (hf₂ : f₂ ∈ B) (hne : f₂ ∉ Subgroup.zpowers f₁)
    (hcomm : ∀ x ∈ E, ∀ y ∈ B, Commute x y) : f₂ ∉ E ⊔ Subgroup.zpowers f₁ := by
  intro hmem
  have hz : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers f₁, Commute x y := fun x hx y hy =>
    hcomm x hx y (by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact zpow_mem hf₁ k)
  obtain ⟨e, he, c, hc, hec⟩ := (mem_sup_iff_of_commute hz).mp hmem
  have hcB : c ∈ B := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact zpow_mem hf₁ k
  have heB : e ∈ B := by
    have : e = f₂ * c⁻¹ := by rw [← hec]; group
    rw [this]
    exact mul_mem hf₂ (inv_mem hcB)
  have he1 : e = 1 := by
    have : e ∈ E ⊓ B := ⟨he, heB⟩
    rw [hEB] at this
    exact Subgroup.mem_bot.mp this
  rw [he1, one_mul] at hec
  exact hne (hec ▸ hc)

theorem key_pair
    (h : Counterexample p A θ) {E B : Subgroup G} (D : Data h E)
    (T71 : ∀ {B' : Subgroup G}, B' ∈ signalizerFunctorEk p 2 A → E ≤ B' →
      ∃ W : Fin p → Subgroup G, Concl71 p A θ E B' W)
    (hBA : B ≤ A) (hEB : E ⊓ B = ⊥) {b b' : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) (hb' : b' ∈ B) (hb'ne : b' ∉ Subgroup.zpowers b) :
    wsub p A θ ⊓ Subgroup.centralizer ({b} : Set G) ≤ θ b ∧
      Nat.Coprime p (Nat.card ↥(wsub p A θ)) ∧ signalizerNearPSolvable p ↥(wsub p A θ) := by
  have hθ := h.hyp.nearFunctor
  have hp := h.hyp.prime
  have hA := hθ.elemAbelian
  have hE := D.hE
  have hcomm : ∀ x ∈ E, ∀ y ∈ B, Commute x y := fun x hx y hy =>
    commute_of_mem hA.1 (hE.1 hx) (hBA hy)
  have hb'1 : b' ≠ 1 := fun e => hb'ne (e ▸ one_mem _)
  have hbE : b ∉ E := fun hbE => hb1 (by
    have : b ∈ E ⊓ B := ⟨hbE, hb⟩
    rw [hEB] at this
    exact Subgroup.mem_bot.mp this)
  have hb'E : b' ∉ E := fun hbE' => hb'1 (by
    have : b' ∈ E ⊓ B := ⟨hbE', hb'⟩
    rw [hEB] at this
    exact Subgroup.mem_bot.mp this)
  have hbA : b ∈ A := hBA hb
  have hb'A : b' ∈ A := hBA hb'
  have hbp : b ^ p = 1 := hA.2 b hbA
  have hb'p : b' ^ p = 1 := hA.2 b' hb'A
  have hmk : ∀ {c : G}, c ∈ A → c ≠ 1 → c ∉ E →
      E ⊔ Subgroup.zpowers c ∈ signalizerFunctorEk p 2 A :=
    fun {c} hcA hc1 hcE => by
      have hz := zpowers_mem_signalizerFunctorEk_one hp hA hcA hc1
      have hdisj : E ⊓ Subgroup.zpowers c = ⊥ :=
        CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le hp (by rw [hz.2, pow_one])
          (fun hle => hcE (hle (Subgroup.mem_zpowers c)))
      simpa using CFSG.SignalizerFunctorTheorem.sup_mem_Ek_succ hA hE hz hdisj
  have hB₁ := hmk hb'A hb'1 hb'E
  have hB₂ := hmk hbA hb1 hbE
  obtain ⟨W, hC⟩ := T71 hB₁ le_sup_left
  have hbnot : b ∉ Subgroup.zpowers b' := fun hmem =>
    hb'ne (Sec6Gen.mem_zpowers_of_mem_zpowers hp hbp hb'p hb1 hmem)
  exact key_lemma h D ⟨hE, hB₁, le_sup_left⟩ ⟨hE, hB₂, le_sup_left⟩ hC
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers b')) hb'E
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) hbE
    (not_mem_sup_zpowers hEB hb' hb hbnot hcomm)
    (not_mem_sup_zpowers hEB hb hb' hb'ne hcomm)

theorem false_of_thm71
    (h : Counterexample p A θ) {E : Subgroup G} (D : Data h E)
    (T71 : ∀ {B' : Subgroup G}, B' ∈ signalizerFunctorEk p 2 A → E ≤ B' →
      ∃ W : Fin p → Subgroup G, Concl71 p A θ E B' W) : False := by
  have hθ := h.hyp.nearFunctor
  have hp := h.hyp.prime
  have hA := hθ.elemAbelian
  have hE := D.hE
  obtain ⟨B, hBA, -, hEB, hEBsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
    hp hA hE.1 (bot_le : (⊥ : Subgroup G) ≤ A) (inf_bot_eq E)
  have hBel : IsElemAbelian p B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hBA
  have hBc : Nat.card B = p ^ 2 := by
    have := CFSG.SignalizerFunctorTheorem.card_mul_card_complement hA hE.1 hBA hEB hEBsup
    rw [hE.2, h.hyp.card, pow_one] at this
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [this]; ring)
  have hex : ∀ b ∈ B, ∃ b' ∈ B, b' ∉ Subgroup.zpowers b := by
    intro b hb
    by_contra hcon
    push Not at hcon
    have hle : B ≤ Subgroup.zpowers b := fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    have hb1 : b ≠ 1 ∨ b = 1 := by tauto
    have hcz : Nat.card (Subgroup.zpowers b) ≤ p := by
      rcases hb1 with hb1 | hb1
      · exact (Sec6Gen.card_zpowers_of_pow_eq_one hp (hA.2 b (hBA hb)) hb1).le
      · rw [hb1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]
        exact hp.one_lt.le
    rw [hBc] at h1
    have h2 : p ^ 2 ≤ p := h1.trans hcz
    have h3 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h3
    omega
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ ⊥ := fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    have := Subgroup.card_le_of_le hle
    rw [hBc, Subgroup.card_bot] at this
    have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨b₀', hb₀', hb₀'n⟩ := hex b₀ hb₀
  obtain ⟨-, hcop, hnear⟩ := key_pair h D T71 hBA hEB hb₀ hb₀1 hb₀' hb₀'n
  have hW : ∀ b ∈ B, b ≠ 1 → wsub p A θ ⊓ Subgroup.centralizer ({b} : Set G) ≤ θ b := by
    intro b hb hb1
    obtain ⟨b', hb', hn⟩ := hex b hb
    exact (key_pair h D T71 hBA hEB hb hb1 hb' hn).1
  have hM3 : ∀ a ∈ A, a ≠ 1 → wsub p A θ ⊓ Subgroup.centralizer ({a} : Set G) ≤ θ a := by
    intro a ha ha1
    have hBa : B ≤ Subgroup.centralizer ({a} : Set G) := fun β hβ =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hA.1 (hBA hβ) ha).eq
    have hXA : Admits B (wsub p A θ ⊓ Subgroup.centralizer ({a} : Set G)) :=
      ((Thm51d.admits_wsub (p := p) (θ := θ)).mono_left hBA).inf (admits_centralizer_singleton hBa)
    have hcopX : Nat.Coprime p (Nat.card ↥(wsub p A θ ⊓ Subgroup.centralizer ({a} : Set G))) :=
      hcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    have hgen := iSup_centralizer_nonidentity hp hBel (by rw [hBc]) hXA hcopX
    rw [← hgen]
    refine iSup₂_le fun b hb => iSup_le fun hb1 x hx => ?_
    obtain ⟨⟨hxW, hxa⟩, hxb⟩ := hx
    exact hθ.isFunctor.balance b (hBA hb) hb1 a ha ha1
      ⟨hW b hb hb1 ⟨hxW, hxb⟩, hxa⟩
  obtain ⟨a₁, ha₁, ha₁1⟩ := exists_mem_ne_one hθ
  have hsol : Group.IsSolvable ↥(wsub p A θ ⊓ Subgroup.centralizer (A : Set G)) := by
    have hle : wsub p A θ ⊓ Subgroup.centralizer (A : Set G) ≤
        θ a₁ ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
      ⟨hM3 a₁ ha₁ ha₁1 ⟨hx.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha₁) hx.2⟩,
        hx.2⟩
    have := (hθ.near a₁ ha₁ ha₁1).2
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hmem : wsub p A θ ∈ assoc p A θ :=
    ⟨Thm51d.admits_wsub, hcop, hM3, hnear, hsol⟩
  exact h.notComplete ⟨wsub p A θ, hmem, fun X hX => le_sSup hX⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
