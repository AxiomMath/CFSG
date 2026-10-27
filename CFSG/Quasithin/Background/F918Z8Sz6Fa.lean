module

public import CFSG.Quasithin.EmptyFaithful.S153ZM

public section

namespace CFSG.Quasithin.SzTorus

open scoped Pointwise

section Red

variable {Y : Type} [CommGroup Y]

@[expose] def FixGood (m : ℕ) (P : Subgroup (MulAut Y)) (t : MulAut Y) (U : Subgroup Y) : Prop :=
  Nat.card ↥U = Nat.card ↥(U ⊓ fixV P) ^ 4 ∧
    ∀ k : ℕ, ¬ (m ∣ k) → U ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥

theorem fixGood_bot (m : ℕ) (P : Subgroup (MulAut Y)) (t : MulAut Y) :
    FixGood m P t (⊥ : Subgroup Y) := by
  refine ⟨?_, fun k _ => ?_⟩
  · simp
  · simp

theorem isInv_iff {Λ : Subgroup (MulAut Y)} {U : Subgroup Y} :
    XMod.IsInv ↥Λ U ↔ ∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U :=
  ⟨fun h l hl u hu => h ⟨l, hl⟩ u hu, fun h a u hu => h a a.2 u hu⟩

theorem exists_iso_fix {Λ : Subgroup (MulAut Y)} {N M : Subgroup Y} (h : XMod.Iso ↥Λ N M) :
    ∃ φ : ↥N ≃* ↥M, ∀ Q : Subgroup (MulAut Y), Q ≤ Λ → ∀ n : ↥N, (n : Y) ∈ fixV Q →
      ((φ n : ↥M) : Y) ∈ fixV Q := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, fun Q hQ n hn x hx => ?_⟩
  exact hφ ⟨x, hQ hx⟩ n n (hn x hx)

theorem FixGood.of_iso [Finite Y] {m : ℕ} {P : Subgroup (MulAut Y)} {t : MulAut Y}
    {Λ : Subgroup (MulAut Y)} (hP : P ≤ Λ) (ht : t ∈ Λ) {N M : Subgroup Y} (hN : XMod.IsInv ↥Λ N)
    (h : XMod.Iso ↥Λ N M) (hM : FixGood m P t M) : FixGood m P t N := by
  obtain ⟨φ, hφ⟩ := exists_iso_fix h
  obtain ⟨ψ, hψ⟩ := exists_iso_fix (XMod.Iso.symm hN h)
  have hcard : Nat.card ↥(N ⊓ fixV P) = Nat.card ↥(M ⊓ fixV P) := by
    refine le_antisymm ?_ ?_
    · refine Nat.card_le_card_of_injective
        (fun x : ↥(N ⊓ fixV P) => (⟨((φ ⟨x, x.2.1⟩ : ↥M) : Y), (φ ⟨x, x.2.1⟩).2,
          hφ P hP ⟨x, x.2.1⟩ x.2.2⟩ : ↥(M ⊓ fixV P))) ?_
      intro x y hxy
      have h0 := congrArg (fun z : ↥(M ⊓ fixV P) => (z : Y)) hxy
      have h1 : φ ⟨x, x.2.1⟩ = φ ⟨y, y.2.1⟩ := Subtype.ext h0
      have h2 := φ.injective h1
      exact Subtype.ext (congrArg (fun z : ↥N => (z : Y)) h2)
    · refine Nat.card_le_card_of_injective
        (fun x : ↥(M ⊓ fixV P) => (⟨((ψ ⟨x, x.2.1⟩ : ↥N) : Y), (ψ ⟨x, x.2.1⟩).2,
          hψ P hP ⟨x, x.2.1⟩ x.2.2⟩ : ↥(N ⊓ fixV P))) ?_
      intro x y hxy
      have h0 := congrArg (fun z : ↥(N ⊓ fixV P) => (z : Y)) hxy
      have h1 : ψ ⟨x, x.2.1⟩ = ψ ⟨y, y.2.1⟩ := Subtype.ext h0
      have h2 := ψ.injective h1
      exact Subtype.ext (congrArg (fun z : ↥M => (z : Y)) h2)
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hcard, ← hM.1]
    exact Nat.card_congr φ.toEquiv
  · refine (Subgroup.eq_bot_iff_forall _).2 fun n hn => ?_
    have hZ : Subgroup.zpowers (t ^ k) ≤ Λ := Subgroup.zpowers_le.2 (pow_mem ht k)
    obtain ⟨⟨hnN, hnP⟩, hnZ⟩ := hn
    have hmem : ((φ ⟨n, hnN⟩ : ↥M) : Y) ∈ M ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) :=
      ⟨⟨(φ ⟨n, hnN⟩).2, hφ P hP ⟨n, hnN⟩ hnP⟩, hφ _ hZ ⟨n, hnN⟩ hnZ⟩
    rw [hM.2 k hk, Subgroup.mem_bot] at hmem
    have h1 : φ ⟨n, hnN⟩ = 1 := Subtype.ext hmem
    have h2 : (⟨n, hnN⟩ : ↥N) = 1 := φ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2

theorem fix_components {q : MulAut Y} {U₁ U₂ : Subgroup Y} (h₁ : ∀ u ∈ U₁, q u ∈ U₁)
    (h₂ : ∀ u ∈ U₂, q u ∈ U₂) (hd : U₁ ⊓ U₂ = ⊥) {u₁ u₂ : Y} (hu₁ : u₁ ∈ U₁) (hu₂ : u₂ ∈ U₂)
    (hfix : q (u₁ * u₂) = u₁ * u₂) : q u₁ = u₁ ∧ q u₂ = u₂ := by
  rw [map_mul] at hfix
  have ha : q u₁ * u₁⁻¹ ∈ U₁ := U₁.mul_mem (h₁ u₁ hu₁) (U₁.inv_mem hu₁)
  have hb : q u₁ * u₁⁻¹ ∈ U₂ := by
    have e : q u₁ * u₁⁻¹ = u₂ * (q u₂)⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, hfix, mul_comm]
    rw [e]
    exact U₂.mul_mem hu₂ (U₂.inv_mem (h₂ u₂ hu₂))
  have h0 : q u₁ * u₁⁻¹ ∈ U₁ ⊓ U₂ := ⟨ha, hb⟩
  rw [hd, Subgroup.mem_bot, mul_inv_eq_one] at h0
  refine ⟨h0, ?_⟩
  rw [h0] at hfix
  exact mul_left_cancel hfix

theorem card_sup_of_inf_eq_bot {U₁ U₂ : Subgroup Y} (hd : U₁ ⊓ U₂ = ⊥) :
    Nat.card ↥(U₁ ⊔ U₂) = Nat.card ↥U₁ * Nat.card ↥U₂ := by
  let f : ↥U₁ × ↥U₂ → ↥(U₁ ⊔ U₂) := fun p =>
    ⟨(p.1 : Y) * (p.2 : Y), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have e : (a : Y) * b = a' * b' := congrArg Subtype.val hab
      have h0 : (a' : Y)⁻¹ * a ∈ U₁ ⊓ U₂ := by
        refine ⟨U₁.mul_mem (U₁.inv_mem a'.2) a.2, ?_⟩
        have : (a' : Y)⁻¹ * a = b' * (b : Y)⁻¹ := by
          calc (a' : Y)⁻¹ * a = (a' : Y)⁻¹ * (a * b) * (b : Y)⁻¹ := by group
            _ = (a' : Y)⁻¹ * (a' * b') * (b : Y)⁻¹ := by rw [e]
            _ = b' * (b : Y)⁻¹ := by group
        rw [this]
        exact U₂.mul_mem b'.2 (U₂.inv_mem b.2)
      rw [hd, Subgroup.mem_bot, inv_mul_eq_one] at h0
      have ha : a = a' := Subtype.ext h0.symm
      subst ha
      have : (b : Y) = b' := mul_left_cancel e
      exact Prod.ext rfl (Subtype.ext this)
    · rintro ⟨y, hy⟩
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hy
      exact ⟨(⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem FixGood.sup {m : ℕ} {P : Subgroup (MulAut Y)} {t : MulAut Y} {Λ : Subgroup (MulAut Y)}
    (hP : P ≤ Λ) (ht : t ∈ Λ) {U₁ U₂ : Subgroup Y} (h₁ : ∀ l ∈ Λ, ∀ u ∈ U₁, l u ∈ U₁)
    (h₂ : ∀ l ∈ Λ, ∀ u ∈ U₂, l u ∈ U₂) (hd : U₁ ⊓ U₂ = ⊥) (g₁ : FixGood m P t U₁)
    (g₂ : FixGood m P t U₂) : FixGood m P t (U₁ ⊔ U₂) := by
  have key : ∀ Q : Subgroup (MulAut Y), Q ≤ Λ → ∀ u₁ ∈ U₁, ∀ u₂ ∈ U₂, ∀ q ∈ Q,
      q (u₁ * u₂) = u₁ * u₂ → q u₁ = u₁ ∧ q u₂ = u₂ := fun Q hQ u₁ hu₁ u₂ hu₂ q hq hfix =>
    fix_components (fun u hu => h₁ q (hQ hq) u hu) (fun u hu => h₂ q (hQ hq) u hu) hd hu₁ hu₂ hfix
  have hsupfix : (U₁ ⊔ U₂) ⊓ fixV P = (U₁ ⊓ fixV P) ⊔ (U₂ ⊓ fixV P) := by
    refine le_antisymm ?_
      (sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right))
    rintro y ⟨hy, hyf⟩
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hy
    have hc : ∀ q ∈ P, q u₁ = u₁ ∧ q u₂ = u₂ := fun q hq => key P hP u₁ hu₁ u₂ hu₂ q hq (hyf q hq)
    exact Subgroup.mul_mem_sup ⟨hu₁, fun q hq => (hc q hq).1⟩ ⟨hu₂, fun q hq => (hc q hq).2⟩
  have hdisj : (U₁ ⊓ fixV P) ⊓ (U₂ ⊓ fixV P) = ⊥ := by
    refine eq_bot_iff.2 ?_
    rw [← hd]
    exact inf_le_inf inf_le_left inf_le_left
  refine ⟨?_, fun k hk => ?_⟩
  · rw [card_sup_of_inf_eq_bot hd, hsupfix, card_sup_of_inf_eq_bot hdisj, mul_pow, g₁.1, g₂.1]
  · refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    obtain ⟨⟨hyU, hyP⟩, hyZ⟩ := hy
    have hZ : Subgroup.zpowers (t ^ k) ≤ Λ := Subgroup.zpowers_le.2 (pow_mem ht k)
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hyU
    have hcP : ∀ q ∈ P, q u₁ = u₁ ∧ q u₂ = u₂ := fun q hq =>
      key P hP u₁ hu₁ u₂ hu₂ q hq (hyP q hq)
    have hcZ : ∀ q ∈ Subgroup.zpowers (t ^ k), q u₁ = u₁ ∧ q u₂ = u₂ := fun q hq =>
      key _ hZ u₁ hu₁ u₂ hu₂ q hq (hyZ q hq)
    have e₁ : u₁ ∈ U₁ ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) :=
      ⟨⟨hu₁, fun q hq => (hcP q hq).1⟩, fun q hq => (hcZ q hq).1⟩
    have e₂ : u₂ ∈ U₂ ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) :=
      ⟨⟨hu₂, fun q hq => (hcP q hq).2⟩, fun q hq => (hcZ q hq).2⟩
    rw [g₁.2 k hk, Subgroup.mem_bot] at e₁
    rw [g₂.2 k hk, Subgroup.mem_bot] at e₂
    rw [e₁, e₂, mul_one]

end Red

section Gen

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ : Subgroup (MulAut Y)} {V : Subgroup Y}

omit [Finite Y] in
theorem smul_eq_map (t : ↥Γ) (V : Subgroup Y) : t • V = V.map (t : MulAut Y).toMonoidHom :=
  Subgroup.ext fun _ => Iff.rfl

omit [Finite Y] in
theorem iSup_smul_eq_top (hgen : (⨆ g ∈ Γ, V.map g.toMonoidHom) = ⊤) :
    (⨆ t : ↥Γ, t • V) = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun g hg => ?_
  refine le_iSup_of_le ⟨g, hg⟩ ?_
  exact (smul_eq_map ⟨g, hg⟩ V).ge

omit [Finite Y] in
theorem isSemisimple_of_gen (hΓ : ∀ g ∈ Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hirr : XMod.IsIrr ↥Λ V)
    (hgen : (⨆ g ∈ Γ, V.map g.toMonoidHom) = ⊤) :
    IsSemisimpleModule ↥(XMod.opRing ↥Λ Y) (Additive Y) := by
  have hN : XMod.Normalizes ↥Λ ↥Γ Y := Z391.normalizes_of_conj Λ Γ hΓ
  have hinv : ∀ t : ↥Γ, XMod.IsInv ↥Λ (t • V) := fun t =>
    XMod.isInv_smul_of_normalizes hN t hirr.1
  have hsum := iSup_smul_eq_top hgen
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun t : ↥Γ => XMod.toSubmod (hinv t)) (fun t => ?_) ?_
  · have : IsSimpleModule ↥(XMod.opRing ↥Λ Y) ↥(XMod.toSubmod (hinv t)) :=
      (XMod.isIrr_iff (hinv t)).1 (Z391.isIrr_smul hN t hirr)
    infer_instance
  · rw [← XMod.toSubmod_iSup hinv, eq_top_iff]
    intro p _
    show Additive.toMul p ∈ ⨆ t : ↥Γ, t • V
    rw [hsum]
    trivial

omit [Finite Y] in
theorem exists_compl_of_gen (hΓ : ∀ g ∈ Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hirr : XMod.IsIrr ↥Λ V)
    (hgen : (⨆ g ∈ Γ, V.map g.toMonoidHom) = ⊤) {N : Subgroup Y}
    (hN : ∀ l ∈ Λ, ∀ u ∈ N, l u ∈ N) :
    ∃ C : Subgroup Y, (∀ l ∈ Λ, ∀ u ∈ C, l u ∈ C) ∧ N ⊓ C = ⊥ ∧ N ⊔ C = ⊤ := by
  have := isSemisimple_of_gen hΓ hirr hgen
  have hN' : XMod.IsInv ↥Λ N := isInv_iff.2 hN
  obtain ⟨C', hC'⟩ := exists_isCompl (XMod.toSubmod hN')
  refine ⟨XMod.ofSubmod C', isInv_iff.1 (XMod.isInv_ofSubmod C'), ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h1 : Additive.ofMul x ∈ XMod.toSubmod hN' ⊓ C' := ⟨hx.1, hx.2⟩
    rw [hC'.inf_eq_bot, Submodule.mem_bot] at h1
    exact h1
  · rw [eq_top_iff]
    intro y _
    have h1 : Additive.ofMul y ∈ XMod.toSubmod hN' ⊔ C' := by
      rw [hC'.sup_eq_top]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    have : y = Additive.toMul a * Additive.toMul b := by
      have := congrArg Additive.toMul hab
      simpa using this.symm
    rw [this]
    exact Subgroup.mul_mem_sup ha hb

theorem fixGood_of_gen {m : ℕ} {P : Subgroup (MulAut Y)} {t : MulAut Y} (hP : P ≤ Λ) (ht : t ∈ Λ)
    (hΓ : ∀ g ∈ Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hirr : XMod.IsIrr ↥Λ V)
    (hgen : (⨆ g ∈ Γ, V.map g.toMonoidHom) = ⊤)
    (hgood : ∀ g ∈ Γ, FixGood m P t (V.map g.toMonoidHom)) {U : Subgroup Y}
    (hU : ∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) : FixGood m P t U := by
  have hN : XMod.Normalizes ↥Λ ↥Γ Y := Z391.normalizes_of_conj Λ Γ hΓ
  have hsum := iSup_smul_eq_top hgen
  have hirrGood : ∀ N : Subgroup Y, XMod.IsIrr ↥Λ N → FixGood m P t N := by
    intro N hNirr
    obtain ⟨g, hg⟩ := Z391.exists_iso_of_le_iSup_smul hN hirr hNirr (le_top.trans hsum.symm.le)
    refine FixGood.of_iso hP ht hNirr.1 hg ?_
    have h := hgood g g.2
    rwa [← smul_eq_map] at h
  revert hU
  induction U using WellFoundedLT.induction with
  | _ U ih =>
    intro hU
    by_cases hbot : U = ⊥
    · rw [hbot]
      exact fixGood_bot m P t
    obtain ⟨N, ⟨hNU, hNinv, hNne⟩, hNmin⟩ := wellFounded_lt.has_min
      {J : Subgroup Y | J ≤ U ∧ XMod.IsInv ↥Λ J ∧ J ≠ ⊥} ⟨U, le_rfl, isInv_iff.2 hU, hbot⟩
    have hNirr : XMod.IsIrr ↥Λ N := by
      refine ⟨hNinv, bot_lt_iff_ne_bot.2 hNne, fun J hJ _ hJN => ?_⟩
      by_cases hJ0 : J = ⊥
      · exact Or.inl hJ0
      · right
        by_contra hne
        exact hNmin J ⟨hJN.trans hNU, hJ, hJ0⟩ (lt_of_le_of_ne hJN hne)
    obtain ⟨C₀, hC₀, hdisj, hsup⟩ := exists_compl_of_gen hΓ hirr hgen (isInv_iff.1 hNinv)
    have hCU : C₀ ⊓ U < U := by
      refine lt_of_le_of_ne inf_le_right fun h => hNne ?_
      have : N ≤ C₀ ⊓ U := by rw [h]; exact hNU
      exact (inf_eq_left.2 (this.trans inf_le_left)).symm.trans hdisj
    have hCinv : ∀ l ∈ Λ, ∀ u ∈ C₀ ⊓ U, l u ∈ C₀ ⊓ U := fun l hl u hu =>
      ⟨hC₀ l hl u hu.1, hU l hl u hu.2⟩
    have hNC : N ⊓ (C₀ ⊓ U) = ⊥ := by
      refine eq_bot_iff.2 ?_
      rw [← hdisj]
      exact inf_le_inf le_rfl inf_le_left
    have hNCU : N ⊔ (C₀ ⊓ U) = U := by
      refine le_antisymm (sup_le hNU inf_le_right) fun y hy => ?_
      have hy' : y ∈ N ⊔ C₀ := by rw [hsup]; trivial
      obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup.1 hy'
      have : c ∈ U := by
        have := U.mul_mem (U.inv_mem (hNU hn)) hy
        simpa using this
      exact Subgroup.mul_mem_sup hn ⟨hc, this⟩
    have := FixGood.sup hP ht (isInv_iff.1 hNinv) hCinv hNC (hirrGood N hNirr)
      (ih _ hCU hCinv)
    rwa [hNCU] at this

end Gen

end CFSG.Quasithin.SzTorus
