module

public import CFSG.Quasithin.Background.G10FourPartner
public import CFSG.Quasithin.Background.G10FourBig

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}

theorem g10Four_irr_of_dual (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)} (hHΓ : H ≤ Γ)
    {U U' : Submodule (ZMod 2) V} (hUH : Invariant H U)
    (hirrU : ∀ J : Submodule (ZMod 2) V, Invariant H J → J ≤ U → J = ⊥ ∨ J = U)
    (hperp : B.orthogonal U = U) (hcompl : IsCompl U U')
    (hdim : 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V) :
    ∀ J : Submodule (ZMod 2) V, Invariant H J → J ≤ U' → J = ⊥ ∨ J = U' := by
  intro J hJ hJle
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  right
  have hMinv : Invariant H (U ⊓ B.orthogonal J) := by
    intro h hh m hm
    refine ⟨hUH h hh m hm.1, ?_⟩
    show h m ∈ B.orthogonal J
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro j hj
    have hinv : (h⁻¹ : GLV V) ∈ H := H.inv_mem hh
    have h1 := hyp.isometry h (hHΓ hh) ((h⁻¹ : GLV V) j) m
    have h2 : h ((h⁻¹ : GLV V) j) = j := by simp
    rw [h2] at h1
    rw [h1]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hm.2) _ (hJ _ hinv j hj)
  rcases hirrU _ hMinv inf_le_left with hM | hM
  ·
    have hd1 := LinearMap.BilinForm.finrank_orthogonal hyp.nondegenerate' J
    have hd2 := Submodule.finrank_sup_add_finrank_inf_eq U (B.orthogonal J)
    rw [hM, finrank_bot] at hd2
    have hd3 := Submodule.finrank_le (U ⊔ B.orthogonal J)
    have hd4 := Submodule.finrank_add_eq_of_isCompl hcompl
    have hJd : Module.finrank (ZMod 2) J ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le J
    apply Submodule.eq_of_le_of_finrank_le hJle
    omega
  · exfalso
    apply hJ0
    have hUJ : U ≤ B.orthogonal J := by
      rw [← hM]
      exact inf_le_right
    have hJU : J ≤ B.orthogonal U := by
      intro j hj
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      rw [hyp.B_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.1 (hUJ hu)) j hj
    rw [hperp] at hJU
    rw [eq_bot_iff, ← hcompl.inf_eq_bot]
    exact le_inf hJU hJle

theorem g10Four_simple_sub (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)} (hXH : X ≤ H)
    {U U' : Submodule (ZMod 2) V} (hUH : Invariant H U) (hU'H : Invariant H U')
    (hirrU : ∀ J : Submodule (ZMod 2) V, Invariant H J → J ≤ U → J = ⊥ ∨ J = U)
    (hcompl : IsCompl U U') (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0)
    (hn3 : 3 ≤ Module.finrank (ZMod 2) U) {S : Submodule (ZMod 2) V} (hSH : Invariant H S)
    (hS0 : S ≠ ⊥) : S ⊓ U ≠ ⊥ ∨ S ⊓ U' ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hSU, hSU'⟩ := hcon
  have hUX : Invariant X U := fun x hx u hu => hUH x (hXH hx) u hu
  have hU'X : Invariant X U' := fun x hx u hu => hU'H x (hXH hx) u hu
  have hSX : Invariant X S := fun x hx u hu => hSH x (hXH hx) u hu
  obtain ⟨-, -, -, -, hker⟩ := hyp.counting U hUX h1 h2
  have hfull := (hyp.counting U hUX h1 h2).2.2.2.1
  obtain ⟨c', hc', hc0, hcommon⟩ := hyp.exists_common_center hUX h1 h2 hU'X hcompl
  have hdec : ∀ v : V, ∃ a ∈ U, ∃ b ∈ U', v = a + b := by
    intro v
    have : v ∈ U ⊔ U' := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨a, ha, b, hb, hv⟩ := Submodule.mem_sup.1 this
    exact ⟨a, ha, b, hb, hv.symm⟩
  let J : Submodule (ZMod 2) V := (S ⊔ U') ⊓ U
  have hJinv : Invariant H J := by
    intro h hh j hj
    refine ⟨?_, hUH h hh j hj.2⟩
    obtain ⟨s, hs, b, hb, hsb⟩ := Submodule.mem_sup.1 hj.1
    rw [← hsb, map_add]
    exact Submodule.add_mem_sup (hSH h hh s hs) (hU'H h hh b hb)
  rcases hirrU J hJinv inf_le_right with hJ0 | hJU
  · apply hS0
    obtain ⟨s, hs, hs0⟩ : ∃ s ∈ S, s ≠ 0 := by
      by_contra hcon'
      push Not at hcon'
      exact hS0 (eq_bot_iff.2 fun s hs => (Submodule.mem_bot _).2 (hcon' s hs))
    exfalso
    obtain ⟨a, ha, b, hb, hsab⟩ := hdec s
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hs0
      have : s ∈ S ⊓ U' := ⟨hs, by rw [hsab, ha0, zero_add]; exact hb⟩
      rw [hSU', Submodule.mem_bot] at this
      exact this
    have haJ : a ∈ J := by
      refine ⟨?_, ha⟩
      have e1 : a = s - b := by rw [hsab]; abel
      rw [e1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hb)
    rw [hJ0, Submodule.mem_bot] at haJ
    exact ha0 haJ
  · exfalso
    obtain ⟨u₀, hu₀, hB₀⟩ := G101Hyp.exists_one U h2
    have hu₀J : u₀ ∈ J := by
      rw [hJU]
      exact hu₀
    obtain ⟨s₀, hs₀, b₀, hb₀, hsb₀⟩ := Submodule.mem_sup.1 hu₀J.1
    have key : ∀ e : U, B v₁ (e : V) = 0 → (e : V) ≠ 0 → (e : V) + c' ∈ S := by
      intro e he he0
      obtain ⟨x, hx, hxe⟩ := hfull e he
      obtain ⟨l, hl⟩ := hcommon x hx b₀ hb₀
      have hmove := hxe ⟨u₀, hu₀⟩
      simp only [hB₀, one_smul] at hmove
      have hxs : x s₀ - s₀ ∈ S := Submodule.sub_mem _ (hSX x hx s₀ hs₀) hs₀
      have e1 : x s₀ - s₀ = (e : V) - l • c' := by
        have h3 : x s₀ = x u₀ - x b₀ := by
          rw [← hsb₀, map_add]
          abel
        have h4 : s₀ = u₀ - b₀ := by
          rw [← hsb₀]
          abel
        rw [h3, h4, hmove]
        have h5 : x b₀ = b₀ + l • c' := by
          rw [← hl]
          abel
        rw [h5]
        abel
      rw [e1] at hxs
      rcases g10Four_zmod_two_cases l with rfl | rfl
      · exfalso
        apply he0
        have : (e : V) ∈ S ⊓ U := ⟨by simpa using hxs, e.2⟩
        rw [hSU, Submodule.mem_bot] at this
        exact this
      · have e2 : (e : V) - (1 : ZMod 2) • c' = (e : V) + c' := by
          rw [one_smul, sub_eq_add_neg, neg_eq_of_add_eq_zero_right (g10Four_add_self c')]
        rwa [e2] at hxs
    have hk2 : 2 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker ((B v₁).domRestrict U)) := by omega
    obtain ⟨a, ha, a', ha', ha0, ha'0, haa'⟩ := g10Four_exists_two_ne_zero (V := ↥U) _ hk2
    have haB : B v₁ (a : V) = 0 := by simpa using ha
    have ha'B : B v₁ (a' : V) = 0 := by simpa using ha'
    have hS1 := key a haB (fun h => ha0 (Subtype.ext h))
    have hS2 := key a' ha'B (fun h => ha'0 (Subtype.ext h))
    have hsum : (a : V) + a' ∈ S ⊓ U := by
      refine ⟨?_, U.add_mem a.2 a'.2⟩
      have := S.add_mem hS1 hS2
      have e3 : (a : V) + c' + ((a' : V) + c') = (a : V) + a' := by
        have h6 := g10Four_add_self c'
        calc (a : V) + c' + ((a' : V) + c') = (a : V) + a' + (c' + c') := by abel
          _ = (a : V) + a' := by rw [h6, add_zero]
      rwa [e3] at this
    rw [hSU, Submodule.mem_bot] at hsum
    apply haa'
    apply Subtype.ext
    exact (eq_neg_of_add_eq_zero_left hsum).trans
      (neg_eq_of_add_eq_zero_right (g10Four_add_self (a' : V)))

omit [Finite V] in
theorem g10Four_mem_conjSub {γ : GLV V} {U : Submodule (ZMod 2) V} {w : V} :
    w ∈ conjSub γ U ↔ ∃ u ∈ U, γ u = w := by
  unfold conjSub
  rw [Submodule.mem_map]
  rfl

omit [Finite V] in
theorem g10Four_conjSub_inv {γ : GLV V} {U : Submodule (ZMod 2) V} {w : V}
    (hw : w ∈ conjSub γ U) : (γ⁻¹ : GLV V) w ∈ U := by
  obtain ⟨u, hu, rfl⟩ := g10Four_mem_conjSub.1 hw
  simpa using hu

omit [Finite V] in
theorem g10Four_invariant_conjSub {H Γ : Subgroup (GLV V)}
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) {U : Submodule (ZMod 2) V} (hU : Invariant H U)
    {γ : GLV V} (hγ : γ ∈ Γ) : Invariant H (conjSub γ U) := by
  intro h hh w hw
  obtain ⟨u, hu, rfl⟩ := g10Four_mem_conjSub.1 hw
  refine g10Four_mem_conjSub.2 ⟨(γ⁻¹ * h * γ) u, ?_, ?_⟩
  · have hinv : γ⁻¹ * h * γ⁻¹⁻¹ ∈ H := hHn γ⁻¹ (Γ.inv_mem hγ) h hh
    simpa using hU _ hinv u hu
  · simp [mul_assoc]

omit [Finite V] in
theorem g10Four_conj_irr {H Γ : Subgroup (GLV V)}
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) {U' : Submodule (ZMod 2) V}
    (hirr : ∀ J : Submodule (ZMod 2) V, Invariant H J → J ≤ U' → J = ⊥ ∨ J = U')
    {γ : GLV V} (hγ : γ ∈ Γ) {J : Submodule (ZMod 2) V} (hJ : Invariant H J)
    (hJle : J ≤ conjSub γ U') : J = ⊥ ∨ J = conjSub γ U' := by
  let J' : Submodule (ZMod 2) V := Submodule.comap (γ : V →ₗ[ZMod 2] V) J
  have hJ'inv : Invariant H J' := by
    intro h hh v hv
    show γ (h v) ∈ J
    have : γ (h v) = (γ * h * γ⁻¹) (γ v) := by simp
    rw [this]
    exact hJ _ (hHn γ hγ h hh) _ hv
  have hJ'le : J' ≤ U' := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := g10Four_mem_conjSub.1 (hJle hv)
    have : u = v := γ.injective huv
    rw [← this]
    exact hu
  rcases hirr J' hJ'inv hJ'le with h0 | h1
  · left
    rw [eq_bot_iff]
    intro j hj
    have hmem : (γ⁻¹ : GLV V) j ∈ J' := by
      show γ ((γ⁻¹ : GLV V) j) ∈ J
      simpa using hj
    rw [h0, Submodule.mem_bot] at hmem
    have : j = γ ((γ⁻¹ : GLV V) j) := by simp
    rw [this, hmem, map_zero]
    exact Submodule.zero_mem _
  · right
    apply le_antisymm hJle
    intro w hw
    obtain ⟨u, hu, rfl⟩ := g10Four_mem_conjSub.1 hw
    have : u ∈ J' := by
      rw [h1]
      exact hu
    exact this

theorem g10Four_conj_eq (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)} (hHΓ : H ≤ Γ)
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hXH : X ≤ H)
    {U U' : Submodule (ZMod 2) V} (hUH : Invariant H U) (hU'H : Invariant H U')
    (hirrU : ∀ J : Submodule (ZMod 2) V, Invariant H J → J ≤ U → J = ⊥ ∨ J = U)
    (hperp : B.orthogonal U = U) (hcompl : IsCompl U U') (h1 : v₁ ∉ U)
    (h2 : ∃ u ∈ U, B v₁ u ≠ 0) (hn3 : 3 ≤ Module.finrank (ZMod 2) U)
    (hdim : 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V) {γ : GLV V}
    (hγ : γ ∈ Γ) : conjSub γ U' = U ∨ conjSub γ U' = U' := by
  have hirrU' := g10Four_irr_of_dual hyp hHΓ hUH hirrU hperp hcompl hdim
  have hU'dim : Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) U := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  have hSdim : Module.finrank (ZMod 2) (conjSub γ U') = Module.finrank (ZMod 2) U' :=
    LinearEquiv.finrank_map_eq γ U'
  have hSinv := g10Four_invariant_conjSub hHn hU'H hγ
  have hS0 : conjSub γ U' ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hSdim
    omega
  rcases g10Four_simple_sub hyp hXH hUH hU'H hirrU hcompl h1 h2 hn3 hSinv hS0 with hne | hne
  · left
    have hJinv : Invariant H (conjSub γ U' ⊓ U) := fun h hh x hx => ⟨hSinv h hh x hx.1, hUH h hh x hx.2⟩
    rcases g10Four_conj_irr hHn hirrU' hγ hJinv inf_le_left with hJ | hJ
    · exact absurd hJ hne
    · have hSU : conjSub γ U' ≤ U := inf_eq_left.1 hJ
      exact Submodule.eq_of_le_of_finrank_eq hSU (by omega)
  · right
    have hJinv : Invariant H (conjSub γ U' ⊓ U') :=
      fun h hh x hx => ⟨hSinv h hh x hx.1, hU'H h hh x hx.2⟩
    rcases g10Four_conj_irr hHn hirrU' hγ hJinv inf_le_left with hJ | hJ
    · exact absurd hJ hne
    · have hSU : conjSub γ U' ≤ U' := inf_eq_left.1 hJ
      exact Submodule.eq_of_le_of_finrank_eq hSU (by omega)

theorem g10Four_notMem_complement (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hHΓ : H ≤ Γ) (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hXH : X ≤ H)
    {U U' : Submodule (ZMod 2) V} (hUH : Invariant H U) (hU'H : Invariant H U')
    (hirrU : ∀ J : Submodule (ZMod 2) V, Invariant H J → J ≤ U → J = ⊥ ∨ J = U)
    (hperp : B.orthogonal U = U) (hcompl : IsCompl U U') (h1 : v₁ ∉ U)
    (h2 : ∃ u ∈ U, B v₁ u ≠ 0) (hn3 : 3 ≤ Module.finrank (ZMod 2) U)
    (hdim : 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V) : v₁ ∉ U' := by
  intro hv
  have hclaim : ∀ γ ∈ Γ, conjSub γ U' = U ∨ conjSub γ U' = U' := fun γ hγ =>
    g10Four_conj_eq hyp hHΓ hHn hXH hUH hU'H hirrU hperp hcompl h1 h2 hn3 hdim hγ
  let K : Subgroup (GLV V) := stabilizerOf Γ U'
  let C : Subgroup (GLV V) := Γ ⊓ MulAction.stabilizer (GLV V) v₁
  have hCK : C ≤ K := by
    intro c hc
    refine ⟨hc.1, ?_⟩
    rcases hclaim c hc.1 with h | h
    · exfalso
      apply h1
      have hcv : c v₁ = v₁ := hc.2
      have : c v₁ ∈ conjSub c U' := g10Four_mem_conjSub.2 ⟨v₁, hv, rfl⟩
      rw [hcv, h] at this
      exact this
    · exact h
  have hodd : Odd (C.relIndex Γ) := by
    have := hyp.odd_index
    rwa [G101Hyp.stabilizer_eq_subgroupOf] at this
  have hdvd1 : K.relIndex Γ ∣ C.relIndex Γ := Subgroup.relIndex_dvd_of_le_left Γ hCK
  have hdvd2 : K.relIndex Γ ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff']
    by_cases hall : ∀ b ∈ Γ, b ∈ K
    · exact ⟨1, Γ.one_mem, fun b hb => Or.inr (hall b hb)⟩
    · push Not at hall
      obtain ⟨g₀, hg₀, hg₀K⟩ := hall
      have hg₀U : conjSub g₀ U' = U := by
        rcases hclaim g₀ hg₀ with h | h
        · exact h
        · exact absurd ⟨hg₀, h⟩ hg₀K
      refine ⟨g₀⁻¹, Γ.inv_mem hg₀, fun b hb => ?_⟩
      by_cases hbK : b ∈ K
      · exact Or.inr hbK
      · left
        have hbU : conjSub b U' = U := by
          rcases hclaim b hb with h | h
          · exact h
          · exact absurd ⟨hb, h⟩ hbK
        refine ⟨Γ.mul_mem (Γ.inv_mem hg₀) hb, ?_⟩
        apply le_antisymm
        · intro w hw
          obtain ⟨u, hu, rfl⟩ := g10Four_mem_conjSub.1 hw
          have : b u ∈ U := by
            rw [← hbU]
            exact g10Four_mem_conjSub.2 ⟨u, hu, rfl⟩
          rw [← hg₀U] at this
          have h3 := g10Four_conjSub_inv this
          simpa using h3
        · intro u' hu'
          have h4 : g₀ u' ∈ U := by
            rw [← hg₀U]
            exact g10Four_mem_conjSub.2 ⟨u', hu', rfl⟩
          have h5 : g₀ u' ∈ conjSub b U' := by
            rw [hbU]
            exact h4
          have h6 := g10Four_conjSub_inv h5
          refine g10Four_mem_conjSub.2 ⟨(b⁻¹ : GLV V) (g₀ u'), h6, ?_⟩
          simp
  have hodd2 : Odd (K.relIndex Γ) := Odd.of_dvd_nat hodd hdvd1
  have hK1 : K.relIndex Γ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h | h
    · exact h
    · rw [h] at hodd2
      exact absurd hodd2 (by decide)
  have hΓK : Γ ≤ K := Subgroup.relIndex_eq_one.1 hK1
  have hinvΓ : Invariant Γ U' := by
    intro γ hγ u hu
    have := (hΓK hγ).2
    rw [← this]
    exact g10Four_mem_conjSub.2 ⟨u, hu, rfl⟩
  have hne : U' ≠ ⊤ := by
    intro htop
    have hUb : U = ⊥ := by
      have := hcompl.inf_eq_bot
      rwa [htop, inf_top_eq] at this
    rw [hUb] at hn3
    simp at hn3
  exact hyp.notMem_of_invariant hinvΓ hne hv

end CFSG.Quasithin
