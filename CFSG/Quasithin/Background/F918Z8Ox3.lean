module

public import CFSG.Quasithin.Background.F918Z8Ox1
public import CFSG.Quasithin.Background.F918J1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

theorem opx3_exists_noncomm {S : Type} [Group S] [Finite S] {C : Subgroup S}
    (hC : C ∈ cComp (⊤ : Subgroup S)) : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have h1 : ⁅C, C⁆ ≤ ⊥ := Subgroup.commutator_le.2 fun a ha b hb =>
    Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hcon a ha b hb))
  exact ne_bot_of_mem_cComp hC ((perfect_of_mem_cComp hC).symm.trans (le_bot_iff.1 h1))

theorem opx3_center_trivial {S : Type} [Group S] [Finite S] {C : Subgroup S}
    (hC : C ∈ cComp (⊤ : Subgroup S)) (hs : IsSimpleGroup ↥C) :
    ∀ x ∈ C, (∀ y ∈ C, x * y = y * x) → x = 1 := by
  intro x hx hxc
  have hZ : Subgroup.center ↥C = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥C) with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := opx3_exists_noncomm hC
      apply hab
      have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top (⟨b, hb⟩ : ↥C)) ⟨a, ha⟩
      exact congrArg Subtype.val this
  have hxZ : (⟨x, hx⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hxc k k.2).symm
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

theorem opx3_image_noncomm {S Q : Type} [Group S] [Finite S] [Group Q] (φ : S →* Q)
    {C : Subgroup S} (hC : C ∈ cComp (⊤ : Subgroup S))
    (hinj : ∀ x ∈ C, ∀ y ∈ C, φ x = φ y → x = y) :
    ∃ x ∈ C.map φ, ∃ y ∈ C.map φ, x * y ≠ y * x := by
  obtain ⟨a, ha, b, hb, hab⟩ := opx3_exists_noncomm hC
  refine ⟨φ a, Subgroup.mem_map_of_mem φ ha, φ b, Subgroup.mem_map_of_mem φ hb, fun h => hab ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact hinj _ (C.mul_mem ha hb) _ (C.mul_mem hb ha) h

theorem opx_unique {S Q : Type} [Group S] [Finite S] [Group Q] (φ : S →* Q)
    {C₁ C₂ : Subgroup S} (h₁ : C₁ ∈ cComp (⊤ : Subgroup S)) (h₂ : C₂ ∈ cComp (⊤ : Subgroup S))
    (hs₁ : IsSimpleGroup ↥C₁) (hs₂ : IsSimpleGroup ↥C₂) (himg : C₁.map φ = C₂.map φ)
    (hnc : ∃ x ∈ C₁.map φ, ∃ y ∈ C₁.map φ, x * y ≠ y * x) : C₁ = C₂ := by
  rcases cComp_eq_or_commutator_eq_bot_of_isSimpleGroup h₁ h₂ hs₁ hs₂ with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have hy' : y ∈ C₂.map φ := himg ▸ hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy'
    have hab : a * b = b * a := by
      have h1 : ⁅a, b⁆ ∈ ⁅C₁, C₂⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    exact hxy (by rw [← map_mul, ← map_mul, hab])

theorem opx3_map_conj_eq {Q : Type} [Group Q] [Finite Q] {D : Subgroup Q} {x : Q}
    (h : ∀ y ∈ D, x * y * x⁻¹ ∈ D) : D.map (MulAut.conj x).toMonoidHom = D := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · exact (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge

theorem opx3_map_conj_map {S Q : Type} [Group S] [Group Q] (φ : S →* Q) (K : Subgroup S) (s : S) :
    (K.map (MulAut.conj s).toMonoidHom).map φ =
      (K.map φ).map (MulAut.conj (φ s)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem opx3_exists_equiv {S Q : Type} [Group S] [Group Q] (φ : S →* Q) {C : Subgroup S}
    {D : Subgroup Q} (hinj : ∀ x ∈ C, ∀ y ∈ C, φ x = φ y → x = y) (hD : C.map φ = D) :
    Nonempty (↥C ≃* ↥D) := by
  have hi : Function.Injective (φ.domRestrict C) := fun x y h =>
    Subtype.ext (hinj x x.2 y y.2 h)
  exact ⟨(MonoidHom.ofInjective hi).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.domRestrict_range, hD]))⟩

theorem opx3_conj_inj {S Q : Type} [Group S] [Group Q] (φ : S →* Q) {C : Subgroup S}
    (hinj : ∀ x ∈ C, ∀ y ∈ C, φ x = φ y → x = y) (s : S) :
    ∀ x ∈ C.map (MulAut.conj s).toMonoidHom, ∀ y ∈ C.map (MulAut.conj s).toMonoidHom,
      φ x = φ y → x = y := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
  have h' : φ x = φ y := by simpa [MulAut.conj_apply] using h
  rw [hinj x hx y hy h']

theorem opx3_normalizes {S Q : Type} [Group S] [Finite S] [Group Q] [Finite Q] (φ : S →* Q)
    {C : Subgroup S} (hC : C ∈ cComp (⊤ : Subgroup S)) (hs : IsSimpleGroup ↥C)
    (hinj : ∀ x ∈ C, ∀ y ∈ C, φ x = φ y → x = y) {s : S}
    (h : ∀ y ∈ C.map φ, φ s * y * (φ s)⁻¹ ∈ C.map φ) : ∀ x ∈ C, s * x * s⁻¹ ∈ C := by
  have himg : (C.map (MulAut.conj s).toMonoidHom).map φ = C.map φ := by
    rw [opx3_map_conj_map]
    exact opx3_map_conj_eq h
  have hCs : C.map (MulAut.conj s).toMonoidHom = C := by
    refine opx_unique φ (A38.cComp_conj hC) hC (A38.conjEquiv s C).symm.isSimpleGroup hs himg ?_
    rw [himg]
    exact opx3_image_noncomm φ hC hinj
  intro x hx
  have hmem : s * x * s⁻¹ ∈ C.map (MulAut.conj s).toMonoidHom :=
    ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rwa [hCs] at hmem

theorem opx3_pow_cent {Q : Type} [Group Q] {D : Subgroup Q} {g : Q}
    (h : ∀ x ∈ D, g * x * g⁻¹ = x) (n : ℕ) : ∀ x ∈ D, g ^ n * x * (g ^ n)⁻¹ = x := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    calc g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
          rw [pow_succ']; group
      _ = x := by rw [ih x hx]; exact h x hx

theorem opx3_pow_norm {Q : Type} [Group Q] {D : Subgroup Q} {g : Q}
    (h : ∀ x ∈ D, g * x * g⁻¹ ∈ D) (n : ℕ) : ∀ x ∈ D, g ^ n * x * (g ^ n)⁻¹ ∈ D := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    have e : g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    exact h _ (ih x hx)

theorem opx3_pow_lift {S Q : Type} [Group S] [Finite S] [Group Q] (φ : S →* Q)
    (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime) (g : Q) :
    ∃ (s : S) (m : ℕ), ¬ p ∣ m ∧ φ s = g ^ m ∧ ∃ a : ℕ, s ^ (p ^ a) = 1 := by
  obtain ⟨g₀, rfl⟩ := hφ g
  obtain ⟨a, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g₀).ne' p hp.ne_one
  refine ⟨g₀ ^ m, m, hm, by rw [map_pow], a, ?_⟩
  rw [← pow_mul, mul_comm, ← hord]
  exact pow_orderOf_eq_one g₀

theorem opx3_mem_of_pow_mem {Q : Type} [Group Q] {D : Subgroup Q} {p : ℕ} (hp : p.Prime)
    {g : Q} {m : ℕ} (hm : ¬ p ∣ m) {k : ℕ} (hk : g ^ (p ^ k) = 1) (h : g ^ m ∈ D) : g ∈ D := by
  have hcop : Nat.Coprime m (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk) hcop)
  rw [← hr]
  exact D.pow_mem h r

theorem opx3_lifted {S Q : Type} [Group S] [Finite S] [Group Q] [Finite Q] (φ : S →* Q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrank : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2)
    {Lh Lh' : Subgroup S} (hLh : Lh ∈ cComp (⊤ : Subgroup S))
    (hLh' : Lh' ∈ cComp (⊤ : Subgroup S)) (hs : IsSimpleGroup ↥Lh) (hs' : IsSimpleGroup ↥Lh')
    (hinj : ∀ x ∈ Lh, ∀ y ∈ Lh, φ x = φ y → x = y)
    (hinj' : ∀ x ∈ Lh', ∀ y ∈ Lh', φ x = φ y → x = y) (hne : Lh ≠ Lh')
    {L L' : Subgroup Q} (hL : Lh.map φ = L) (hL' : Lh'.map φ = L')
    (hAut : Nat.card (MulAut ↥L') ≤ 2 * Nat.card ↥L') (hpL : p ∣ Nat.card ↥L)
    (hcard : Nat.card ↥L' = Nat.card ↥L) {s : S} (hsp : ∃ k : ℕ, s ^ (p ^ k) = 1)
    (hsL : ∀ x ∈ L, φ s * x * (φ s)⁻¹ = x) (hsL' : ∀ x ∈ L', φ s * x * (φ s)⁻¹ ∈ L') :
    s ∈ Lh' := by
  have hcomm : ∀ a ∈ Lh, ∀ b ∈ Lh', a * b = b * a := by
    intro a ha b hb
    have h := (cComp_eq_or_commutator_eq_bot_of_isSimpleGroup hLh hLh' hs hs').resolve_left hne
    have h1 : ⁅a, b⁆ ∈ ⁅Lh, Lh'⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  obtain ⟨e⟩ := opx3_exists_equiv φ hinj hL
  obtain ⟨e'⟩ := opx3_exists_equiv φ hinj' hL'
  have hcardL : Nat.card ↥Lh = Nat.card ↥L := Nat.card_congr e.toEquiv
  have hcardL' : Nat.card ↥Lh' = Nat.card ↥L' := Nat.card_congr e'.toEquiv
  have hnL : ∀ x ∈ Lh, s * x * s⁻¹ ∈ Lh := by
    refine opx3_normalizes φ hLh hs hinj fun y hy => ?_
    rw [hL] at hy ⊢
    rw [hsL y hy]
    exact hy
  refine opx_core hp hp2 hrank hcomm (opx3_center_trivial hLh hs) (opx3_center_trivial hLh' hs')
    (hcardL ▸ hpL) (by rw [hcardL', hcard]; exact hpL) ?_ hsp (fun x hx => ?_)
    (opx3_normalizes φ hLh' hs' hinj' fun y hy => ?_)
  · rw [Nat.card_congr (MulAut.congr e').toEquiv, hcardL']
    exact hAut
  · refine hinj _ (hnL x hx) _ hx ?_
    rw [map_mul, map_mul, map_inv]
    exact hsL _ (hL ▸ Subgroup.mem_map_of_mem φ hx)
  · rw [hL'] at hy ⊢
    exact hsL' y hy

theorem opx_cover {Q : Type} [Group Q] [Finite Q] {S : Type} [Group S] [Finite S]
    (φ : S →* Q) (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2)
    {Lh : Subgroup S} (hLh : Lh ∈ cComp (⊤ : Subgroup S)) (hs : IsSimpleGroup ↥Lh)
    (hinj : ∀ x ∈ Lh, ∀ y ∈ Lh, φ x = φ y → x = y)
    {L L' : Subgroup Q} (hL : Lh.map φ = L) {t : Q}
    (hL' : L' = L.map (MulAut.conj t).toMonoidHom) (hne : L ≠ L')
    (hAut : Nat.card (MulAut ↥L') ≤ 2 * Nat.card ↥L') (hpL : p ∣ Nat.card ↥L)
    {g : Q} (hgp : ∃ k : ℕ, g ^ (p ^ k) = 1)
    (hgL : ∀ x ∈ L, g * x * g⁻¹ = x) (hgL' : ∀ x ∈ L', g * x * g⁻¹ ∈ L') : g ∈ L' := by
  obtain ⟨th, rfl⟩ := hφ t
  have himg' : (Lh.map (MulAut.conj th).toMonoidHom).map φ = L' := by
    rw [hL', ← hL, opx3_map_conj_map]
  have hne' : Lh ≠ Lh.map (MulAut.conj th).toMonoidHom := fun h =>
    hne (hL.symm.trans ((congrArg (Subgroup.map φ) h).trans himg'))
  have hcard : Nat.card ↥L' = Nat.card ↥L := by
    rw [hL']
    exact Subgroup.card_map_of_injective (MulAut.conj (φ th)).injective
  obtain ⟨k, hk⟩ := hgp
  obtain ⟨s, m, hm, hsφ, hsp⟩ := opx3_pow_lift φ hφ hp g
  have hs1 : s ∈ Lh.map (MulAut.conj th).toMonoidHom :=
    opx3_lifted φ hp hp2 hrank hLh (A38.cComp_conj hLh) hs
      (A38.conjEquiv th Lh).symm.isSimpleGroup hinj (opx3_conj_inj φ hinj th) hne' hL himg'
      hAut hpL hcard hsp (hsφ ▸ opx3_pow_cent hgL m) (hsφ ▸ opx3_pow_norm hgL' m)
  have h1 : g ^ m ∈ L' := by
    rw [← himg', ← hsφ]
    exact Subgroup.mem_map_of_mem φ hs1
  exact opx3_mem_of_pow_mem hp hm hk h1

end CFSG.Quasithin
