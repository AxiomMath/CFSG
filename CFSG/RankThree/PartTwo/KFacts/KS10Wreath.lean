module

public import CFSG.RankThree.PartTwo.KFacts.K73Recognition
public import CFSG.RankThree.PartTwo.KFacts.KS10L27

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem cube_identity_add {M : Type*} [AddCommGroup M] (α : M →+ M) (v : M) :
    α (α (α v - v) - (α v - v)) - (α (α v - v) - (α v - v)) =
      α (α (α v)) - 3 • α (α v) + 3 • α v - v := by
  simp only [map_sub]
  abel

@[expose] def commMap {M : Type*} [Group M] (α : M →* M) (y : M) : M := α y * y⁻¹

theorem cube_identity_mul {M : Type*} [CommGroup M] (α : M →* M) (x : M) :
    commMap α (commMap α (commMap α x)) = α (α (α x)) * (α (α x))⁻¹ ^ 3 * (α x) ^ 3 * x⁻¹ := by
  simp only [commMap, map_mul, map_inv]
  have := cube_identity_add (MonoidHom.toAdditive α) (Additive.ofMul x)
  simp only [MonoidHom.toAdditive_apply_apply, toMul_ofMul] at this
  apply Additive.ofMul.injective
  simpa [ofMul_mul, ofMul_inv, ofMul_pow, sub_eq_add_neg] using this

theorem prime_mul_card_le_of_le_of_ne {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    (hM : IsPGroup p M) {H K : Subgroup M} (hHK : H ≤ K) (hne : H ≠ K) :
    p * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hM.to_subgroup K)
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.mp (hM.to_subgroup H)
  have hp := (Fact.out : p.Prime)
  have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK
  rw [hm, hl] at hdvd
  have hlm : l ≤ m := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hlm' : l ≠ m := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hHK (by rw [hm, hl]))
  rw [hm, hl, ← pow_succ']
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem mem_zpowers_of_mem_zpowers_of_ne_one' {M : Type*} [Group M] {p : ℕ} [Fact p.Prime]
    {d x : M} (hd : orderOf d = p) (hx : x ∈ Subgroup.zpowers d) (hx1 : x ≠ 1) :
    d ∈ Subgroup.zpowers x := by
  have hp := (Fact.out : p.Prime)
  have hfin : (Subgroup.zpowers d : Set M).Finite := by
    have : IsOfFinOrder d := orderOf_pos_iff.mp (hd ▸ hp.pos)
    exact this.finite_zpowers
  have : Finite (Subgroup.zpowers d) := hfin.to_subtype
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hx
  have hcx : Nat.card (Subgroup.zpowers x) ∣ p := by
    rw [← hd, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hcx1 : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    rw [Nat.card_zpowers]
    intro h1
    exact hx1 (orderOf_eq_one_iff.mp h1)
  have hcx' : Nat.card (Subgroup.zpowers x) = p := by
    rcases (Nat.dvd_prime hp).mp hcx with h | h
    · exact absurd h hcx1
    · exact h
  have heq : Subgroup.zpowers x = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcx', Nat.card_zpowers, hd])
  rw [heq]
  exact Subgroup.mem_zpowers d

theorem exists_eBase_eq {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {a : G} (ha3 : a ^ 3 = 1)
    (haN : a ∈ Subgroup.normalizer (E : Set G)) {d : G} (hdE : d ∈ E) (hd1 : d ≠ 1)
    (hda : a * d * a⁻¹ = d) (hC : ∀ x ∈ E, a * x * a⁻¹ = x → x ∈ Subgroup.zpowers d) :
    ∃ e ∈ E, eBase e a = E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun x y => hE.1.is_comm.comm x y }
  set α : E →* E := (E.normalizerMonoidHom ⟨a, haN⟩).toMonoidHom with hαdef
  have hα : ∀ x : E, ((α x : E) : G) = a * x * a⁻¹ := fun x => rfl
  let f : E →* E :=
    { toFun := commMap α
      map_one' := by simp [commMap]
      map_mul' := fun x y => by
        simp only [commMap, map_mul, mul_inv_rev]
        rw [mul_comm y⁻¹ x⁻¹, mul_mul_mul_comm] }
  have hf : ∀ x, f x = α x * x⁻¹ := fun _ => rfl
  have hexp : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hα3 : ∀ x : E, α (α (α x)) = x := by
    intro x
    apply Subtype.ext
    rw [hα, hα, hα]
    have ha3' : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
    calc a * (a * (a * (x : G) * a⁻¹) * a⁻¹) * a⁻¹ = a * (a * a) * x * (a * (a * a))⁻¹ := by
          group
      _ = x := by rw [ha3', one_mul, inv_one, mul_one]
  have hf3 : ∀ x, f (f (f x)) = 1 := by
    intro x
    change commMap α (commMap α (commMap α x)) = 1
    rw [cube_identity_mul, hα3, inv_pow, hexp, inv_one, mul_one, hexp, mul_one, mul_inv_cancel]
  set dd : E := ⟨d, hdE⟩ with hdd
  have hdd1 : dd ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hdd3 : orderOf dd = 3 := orderOf_eq_prime (hexp dd) hdd1
  have hfdd : f dd = 1 := by
    rw [hf, mul_inv_eq_one]
    exact Subtype.ext hda
  have hker : f.ker = Subgroup.zpowers dd := by
    apply le_antisymm
    · intro x hx
      have hx' : α x = x := mul_inv_eq_one.mp hx
      have h1 := hC x x.2 (congrArg Subtype.val hx')
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [← hk]; simp [hdd])⟩
    · rw [Subgroup.zpowers_le]
      exact hfdd
  have hkercard : Nat.card f.ker = 3 := by rw [hker, Nat.card_zpowers, hdd3]
  have hEcard : Nat.card E = 27 := hE27
  have hrange : Nat.card f.range = 9 := by
    have h1 := card_eq_card_ker_mul_card_range f
    rw [hEcard, hkercard] at h1
    omega
  have hE3 : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  have hdI : dd ∈ f.range := by
    by_contra hdI
    have hinj : ∀ x ∈ f.range, f x = 1 → x = 1 := by
      intro x hx hx1
      by_contra hne
      exact hdI (Subgroup.zpowers_le.mpr hx (mem_zpowers_of_mem_zpowers_of_ne_one' hdd3
        (hker ▸ hx1) hne))
    set f' : f.range →* E := f.comp f.range.subtype with hf'
    have hf'inj : Function.Injective f' := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro x hx
      exact Subtype.ext (hinj x x.2 hx)
    have hle : f'.range ≤ f.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    have heq : f'.range = f.range := Subgroup.eq_of_le_of_card_ge hle (by
      rw [← Nat.card_congr (MonoidHom.ofInjective hf'inj).toEquiv])
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ f.range, y ≠ 1 := by
      by_contra hall
      push Not at hall
      have : f.range = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
      rw [this, Subgroup.card_bot] at hrange
      norm_num at hrange
    rw [← heq] at hy
    obtain ⟨⟨y1, hy1r⟩, rfl⟩ := hy
    rw [← heq] at hy1r
    obtain ⟨⟨y2, hy2r⟩, rfl⟩ := hy1r
    obtain ⟨y3, rfl⟩ := hy2r
    exact hy1 (hf3 y3)
  have hkerI : f.ker ≤ f.range := by rw [hker, Subgroup.zpowers_le]; exact hdI
  have hfI : f.range.map f = f.ker := by
    have hle : f.range.map f ≤ f.ker := by
      rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      exact hf3 z
    apply Subgroup.eq_of_le_of_card_ge hle
    set f'' : f.range →* E := f.comp f.range.subtype
    have hk'' : Nat.card f''.ker = 3 := by
      have : f''.ker.map f.range.subtype = f.ker := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hkerI hx⟩, hx, rfl⟩
      rw [← hkercard, ← this, Subgroup.card_map_of_injective f.range.subtype_injective]
    have h1 := card_eq_card_ker_mul_card_range f''
    rw [hrange, hk''] at h1
    have hr'' : f''.range = f.range.map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hkercard, ← hr'']
    omega
  obtain ⟨e0, he0⟩ : ∃ e0 : E, e0 ∉ f.range := by
    by_contra hall
    push Not at hall
    have : f.range = ⊤ := (Subgroup.eq_top_iff' _).mpr hall
    rw [this, Subgroup.card_top, hEcard] at hrange
    norm_num at hrange
  refine ⟨e0, e0.2, ?_⟩
  set B := eBase (e0 : G) a with hB
  have hconjE : ∀ i : ℕ, eConj (e0 : G) a i ∈ E := by
    intro i
    induction i with
    | zero => rw [eConj_zero]; exact e0.2
    | succ i ih =>
      rw [← conj_eConj]
      exact (Subgroup.mem_normalizer_iff.mp haN _).mp ih
  have hBE : B ≤ E := by
    rw [hB, eBase, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact hconjE 0
    · exact hconjE 1
    · exact hconjE 2
  have hBa : ∀ x ∈ B, a * x * a⁻¹ ∈ B := by
    have hle : B.map (MulAut.conj a).toMonoidHom ≤ B := by
      rw [hB, eBase, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl | rfl
      · change a * eConj (e0 : G) a 0 * a⁻¹ ∈ eBase (e0 : G) a
        rw [conj_eConj]
        exact eConj_mem_eBase (Or.inr (Or.inl rfl))
      · change a * eConj (e0 : G) a 1 * a⁻¹ ∈ eBase (e0 : G) a
        rw [conj_eConj]
        exact eConj_mem_eBase (Or.inr (Or.inr rfl))
      · have h3 : eConj (e0 : G) a (2 + 1) = eConj (e0 : G) a 0 := by
          rw [show (2 + 1 : ℕ) = 0 + 3 from rfl, eConj_add_three ha3]
        change a * eConj (e0 : G) a 2 * a⁻¹ ∈ eBase (e0 : G) a
        rw [conj_eConj, h3]
        exact eConj_mem_eBase (Or.inl rfl)
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  set B' := B.subgroupOf E with hB'
  have hfB : ∀ x ∈ B', f x ∈ B' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hf]
    exact B.mul_mem (hBa _ hx) (B.inv_mem hx)
  have he0B : e0 ∈ B' := by
    rw [Subgroup.mem_subgroupOf, hB]
    have h0 : eConj (e0 : G) a 0 ∈ eBase (e0 : G) a := eConj_mem_eBase (Or.inl rfl)
    rwa [eConj_zero] at h0
  have hfe0 : f e0 ∉ f.ker := by
    intro hfe
    rw [← hfI] at hfe
    obtain ⟨i, hi, hie⟩ := hfe
    have h1 : e0 * i⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hie, mul_inv_cancel]
    apply he0
    have := f.range.mul_mem (hkerI h1) hi
    simpa using this
  have hffe0 : f (f e0) ≠ 1 := fun h => hfe0 h
  have hffe0K : f (f e0) ∈ f.ker := by
    rw [← hfI]
    exact ⟨f e0, ⟨e0, rfl⟩, rfl⟩
  have hkerB : f.ker ≤ B' := by
    rw [hker, Subgroup.zpowers_le]
    have h1 := mem_zpowers_of_mem_zpowers_of_ne_one' hdd3 (hker ▸ hffe0K) hffe0
    exact Subgroup.zpowers_le.mpr (hfB _ (hfB _ he0B)) h1
  have hIB : f.range ≤ B' := by
    have hle : f.ker ≤ B' ⊓ f.range := le_inf hkerB hkerI
    have hne : f.ker ≠ B' ⊓ f.range := fun h =>
      hfe0 (h ▸ ⟨hfB _ he0B, ⟨e0, rfl⟩⟩)
    have h1 := prime_mul_card_le_of_le_of_ne hE3 hle hne
    rw [hkercard] at h1
    have h2 : B' ⊓ f.range = f.range := Subgroup.eq_of_le_of_card_ge inf_le_right (by
      rw [hrange]; omega)
    rw [← h2]
    exact inf_le_left
  have hBtop : B' = ⊤ := by
    have hne : f.range ≠ B' := fun h => he0 (h ▸ he0B)
    have h1 := prime_mul_card_le_of_le_of_ne hE3 hIB hne
    rw [hrange] at h1
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hEcard]
    omega
  apply le_antisymm hBE
  intro x hx
  have : (⟨x, hx⟩ : E) ∈ B' := hBtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_commMap_mem_zpowers {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {a : G} (ha3 : a ^ 3 = 1)
    (haN : a ∈ Subgroup.normalizer (E : Set G)) {d : G} (hdE : d ∈ E) (hd1 : d ≠ 1)
    (hda : a * d * a⁻¹ = d) (hC : ∀ x ∈ E, a * x * a⁻¹ = x → x ∈ Subgroup.zpowers d) :
    ∃ x ∈ E, a * x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers d ∧ a * x * a⁻¹ * x⁻¹ ≠ 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun x y => hE.1.is_comm.comm x y }
  set α : E →* E := (E.normalizerMonoidHom ⟨a, haN⟩).toMonoidHom with hαdef
  have hα : ∀ x : E, ((α x : E) : G) = a * x * a⁻¹ := fun x => rfl
  let f : E →* E :=
    { toFun := commMap α
      map_one' := by simp [commMap]
      map_mul' := fun x y => by
        simp only [commMap, map_mul, mul_inv_rev]
        rw [mul_comm y⁻¹ x⁻¹, mul_mul_mul_comm] }
  have hf : ∀ x, f x = α x * x⁻¹ := fun _ => rfl
  have hexp : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hα3 : ∀ x : E, α (α (α x)) = x := by
    intro x
    apply Subtype.ext
    rw [hα, hα, hα]
    have ha3' : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
    calc a * (a * (a * (x : G) * a⁻¹) * a⁻¹) * a⁻¹ = a * (a * a) * x * (a * (a * a))⁻¹ := by
          group
      _ = x := by rw [ha3', one_mul, inv_one, mul_one]
  have hf3 : ∀ x, f (f (f x)) = 1 := by
    intro x
    change commMap α (commMap α (commMap α x)) = 1
    rw [cube_identity_mul, hα3, inv_pow, hexp, inv_one, mul_one, hexp, mul_one, mul_inv_cancel]
  set dd : E := ⟨d, hdE⟩ with hdd
  have hdd1 : dd ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hdd3 : orderOf dd = 3 := orderOf_eq_prime (hexp dd) hdd1
  have hfdd : f dd = 1 := by
    rw [hf, mul_inv_eq_one]
    exact Subtype.ext hda
  have hker : f.ker = Subgroup.zpowers dd := by
    apply le_antisymm
    · intro x hx
      have hx' : α x = x := mul_inv_eq_one.mp hx
      have h1 := hC x x.2 (congrArg Subtype.val hx')
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [← hk]; simp [hdd])⟩
    · rw [Subgroup.zpowers_le]
      exact hfdd
  have hkercard : Nat.card f.ker = 3 := by rw [hker, Nat.card_zpowers, hdd3]
  have hEcard : Nat.card E = 27 := hE27
  have hrange : Nat.card f.range = 9 := by
    have h1 := card_eq_card_ker_mul_card_range f
    rw [hEcard, hkercard] at h1
    omega
  have hE3 : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  have hdI : dd ∈ f.range := by
    by_contra hdI
    have hinj : ∀ x ∈ f.range, f x = 1 → x = 1 := by
      intro x hx hx1
      by_contra hne
      exact hdI (Subgroup.zpowers_le.mpr hx (mem_zpowers_of_mem_zpowers_of_ne_one' hdd3
        (hker ▸ hx1) hne))
    set f' : f.range →* E := f.comp f.range.subtype with hf'
    have hf'inj : Function.Injective f' := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro x hx
      exact Subtype.ext (hinj x x.2 hx)
    have hle : f'.range ≤ f.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    have heq : f'.range = f.range := Subgroup.eq_of_le_of_card_ge hle (by
      rw [← Nat.card_congr (MonoidHom.ofInjective hf'inj).toEquiv])
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ f.range, y ≠ 1 := by
      by_contra hall
      push Not at hall
      have : f.range = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
      rw [this, Subgroup.card_bot] at hrange
      norm_num at hrange
    rw [← heq] at hy
    obtain ⟨⟨y1, hy1r⟩, rfl⟩ := hy
    rw [← heq] at hy1r
    obtain ⟨⟨y2, hy2r⟩, rfl⟩ := hy1r
    obtain ⟨y3, rfl⟩ := hy2r
    exact hy1 (hf3 y3)
  have hkerI : f.ker ≤ f.range := by rw [hker, Subgroup.zpowers_le]; exact hdI
  have hfI : f.range.map f = f.ker := by
    have hle : f.range.map f ≤ f.ker := by
      rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      exact hf3 z
    apply Subgroup.eq_of_le_of_card_ge hle
    set f'' : f.range →* E := f.comp f.range.subtype
    have hk'' : Nat.card f''.ker = 3 := by
      have : f''.ker.map f.range.subtype = f.ker := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hkerI hx⟩, hx, rfl⟩
      rw [← hkercard, ← this, Subgroup.card_map_of_injective f.range.subtype_injective]
    have h1 := card_eq_card_ker_mul_card_range f''
    rw [hrange, hk''] at h1
    have hr'' : f''.range = f.range.map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hkercard, ← hr'']
    omega
  obtain ⟨x, hxI, hxK⟩ : ∃ x ∈ f.range, x ∉ f.ker := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le hall
    rw [hrange, hkercard] at h1
    norm_num at h1
  have hfx : f x ∈ f.ker := by
    rw [← hfI]
    exact ⟨x, hxI, rfl⟩
  refine ⟨x, x.2, ?_, ?_⟩
  · rw [hker] at hfx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfx
    have hk' : ((f x : E) : G) = d ^ k := by rw [← hk]; simp [hdd]
    rw [show a * (x : G) * a⁻¹ * (x : G)⁻¹ = ((f x : E) : G) from rfl, hk']
    exact Subgroup.zpow_mem_zpowers d k
  · intro h1
    apply hxK
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h1

end CFSG.RankThree.PartTwo.KFacts
