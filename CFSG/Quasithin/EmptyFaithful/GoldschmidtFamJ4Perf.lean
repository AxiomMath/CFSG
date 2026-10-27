module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Red
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem isSolvable_of_ne_top_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] {b : ℕ}
    (hb : ∀ i : ℕ, Nat.card S ∣ i.factorial → b ≤ i)
    (hord : ∀ m : ℕ, m ∣ Nat.card S → m * b ≤ Nat.card S →
      ∃ p q a c : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ m = p ^ a * q ^ c)
    {H : Subgroup S} (hH : H ≠ ⊤) : Group.IsSolvable H := by
  classical
  let π : S →* Equiv.Perm (S ⧸ H) := MulAction.toPermHom S (S ⧸ H)
  have hkerH : π.ker ≤ H := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : π g ((1 : S) : S ⧸ H) = ((1 : S) : S ⧸ H) := by rw [hg]; rfl
    have h2 : π g ((1 : S) : S ⧸ H) = ((g * 1 : S) : S ⧸ H) := by
      show g • ((1 : S) : S ⧸ H) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    rw [h2] at h1
    have := QuotientGroup.eq.1 h1
    simpa using H.inv_mem this
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      apply hH
      rw [h] at hkerH
      exact top_le_iff.1 hkerH
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  have hdvd : Nat.card S ∣ H.index.factorial := by
    have h1 := Subgroup.card_dvd_of_injective π hinj
    rwa [Nat.card_perm] at h1
  have hbi : b ≤ H.index := hb _ hdvd
  have hcard := H.card_mul_index
  have hHdvd : Nat.card H ∣ Nat.card S := Subgroup.card_subgroup_dvd_card H
  have hle : Nat.card H * b ≤ Nat.card S := by
    calc Nat.card H * b ≤ Nat.card H * H.index := Nat.mul_le_mul_left _ hbi
      _ = Nat.card S := hcard
  obtain ⟨p, q, a, c, hp, hq, hpq, hm⟩ := hord _ hHdvd hle
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact hm)

theorem eq_bot_or_top_of_isPerfect {S : Type*} [Group S]
    (hsolv : ∀ H : Subgroup S, H ≠ ⊤ → Group.IsSolvable H) {R : Subgroup S}
    (hR : Group.IsPerfect R) : R = ⊥ ∨ R = ⊤ := by
  by_cases h : R = ⊤
  · exact Or.inr h
  · left
    have hs := hsolv R h
    by_contra hbot
    have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hbot
    have : Group.IsPerfect R := hR
    exact Group.IsPerfect.not_isSolvable R hs

theorem ord60 : ∀ m : ℕ, m ∣ 60 → m * 5 ≤ 60 →
    ∃ p q a c : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ m = p ^ a * q ^ c := by
  intro m hm hle
  have key : ∀ m < 13, m ∣ 60 →
      m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 10 ∨ m = 12 := by
    decide
  rcases key m (by omega) hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 3, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 5, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 5, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem ord168 : ∀ m : ℕ, m ∣ 168 → m * 7 ≤ 168 →
    ∃ p q a c : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ m = p ^ a * q ^ c := by
  intro m hm hle
  have key : ∀ m < 25, m ∣ 168 → m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨
      m = 12 ∨ m = 14 ∨ m = 21 ∨ m = 24 := by
    decide
  rcases key m (by omega) hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 3, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 7, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 3, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 7, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 7, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem solvable_of_ne_top_card60 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Nat.card S = 60) {H : Subgroup S} (hH : H ≠ ⊤) : Group.IsSolvable H := by
  refine isSolvable_of_ne_top_of_simple (b := 5) ?_ (by rw [hS]; exact ord60) hH
  intro i hi
  rw [hS] at hi
  by_contra hlt
  push Not at hlt
  interval_cases i <;> simp [Nat.factorial] at hi

theorem solvable_of_ne_top_card168 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Nat.card S = 168) {H : Subgroup S} (hH : H ≠ ⊤) : Group.IsSolvable H := by
  refine isSolvable_of_ne_top_of_simple (b := 7) ?_ (by rw [hS]; exact ord168) hH
  intro i hi
  rw [hS] at hi
  by_contra hlt
  push Not at hlt
  interval_cases i <;> simp [Nat.factorial] at hi

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem isPerfect_perm_five {R : Subgroup (Equiv.Perm (Fin 5))} (hR : Group.IsPerfect R) :
    R = ⊥ ∨ R = alternatingGroup (Fin 5) := by
  have hle : R ≤ alternatingGroup (Fin 5) := by
    intro x hx
    rw [Equiv.Perm.mem_alternatingGroup]
    let f : R →* ℤˣ := (Equiv.Perm.sign : Equiv.Perm (Fin 5) →* ℤˣ).comp R.subtype
    have h1 : commutator R ≤ f.ker := Abelianization.commutator_subset_ker f
    have h2 : commutator R = ⊤ := Group.isPerfect_def.1 hR
    rw [h2] at h1
    have h3 : (⟨x, hx⟩ : R) ∈ f.ker := h1 trivial
    exact h3
  have := alt5_simple
  have hperf : Group.IsPerfect (R.subgroupOf (alternatingGroup (Fin 5))) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  rcases eq_bot_or_top_of_isPerfect (fun H hH => solvable_of_ne_top_card60 card_alt5 hH) hperf with
    h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxA := hle hx
    have : (⟨x, hxA⟩ : alternatingGroup (Fin 5)) ∈ R.subgroupOf (alternatingGroup (Fin 5)) :=
      Subgroup.mem_subgroupOf.2 hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · right
    refine le_antisymm hle ?_
    intro x hx
    have : (⟨x, hx⟩ : alternatingGroup (Fin 5)) ∈ R.subgroupOf (alternatingGroup (Fin 5)) := by
      rw [h]; trivial
    exact Subgroup.mem_subgroupOf.1 this

theorem nonabelian_of_card168 {Q : Type} [Group Q] [IsSimpleGroup Q] (hQ : Nat.card Q = 168) :
    ∃ a b : Q, a * b ≠ b * a :=
  nonabelian_of_card_not_prime (S := Q) (by rw [hQ]; norm_num)

theorem modO2_of_two_actions {B : Type} [Group B] [Finite B] (hperf : Group.IsPerfect B)
    (hnsolv : ¬ Group.IsSolvable B)
    (hnorm : ∀ P : Subgroup B, P.Normal → P = ⊤ ∨ Group.IsSolvable P)
    {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q] (hQ : Nat.card Q = 168)
    (ρ : B →* Equiv.Perm (Fin 5)) (α : B →* Q) (hK : IsPGroup 2 (ρ.ker ⊓ α.ker : Subgroup B)) :
    Nonempty ((B ⧸ CFSG.pCore 2 B) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((B ⧸ CFSG.pCore 2 B) ≃* Q) := by
  have hQna := nonabelian_of_card168 hQ
  have hQsolv : ¬ Group.IsSolvable Q := fun hs =>
    hQna.elim fun a ⟨b, hab⟩ => hab (((IsSimpleGroup.comm_iff_isSolvable (G := Q)).2 hs) a b)
  have := hperf
  have hRρ : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hRα : Group.IsPerfect α.range := Group.IsPerfect.range α
  rcases isPerfect_perm_five hRρ with hρ | hρ <;>
    rcases eq_bot_or_top_of_isPerfect (fun H hH => solvable_of_ne_top_card168 hQ hH) hRα with
      hα | hα
  ·
    exfalso
    have hρ1 : ρ.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : ρ x ∈ ρ.range := ⟨x, rfl⟩
      rw [hρ, Subgroup.mem_bot] at this
      exact this
    have hα1 : α.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : α x ∈ α.range := ⟨x, rfl⟩
      rw [hα, Subgroup.mem_bot] at this
      exact this
    rw [hρ1, hα1, top_inf_eq] at hK
    have hP : IsPGroup 2 B := by
      intro g
      obtain ⟨k, hk⟩ := hK ⟨g, trivial⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Group.IsNilpotent B := hP.isNilpotent
    exact hnsolv inferInstance
  ·
    right
    have hρ1 : ρ.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : ρ x ∈ ρ.range := ⟨x, rfl⟩
      rw [hρ, Subgroup.mem_bot] at this
      exact this
    rw [hρ1, top_inf_eq] at hK
    exact nonempty_modO2_equiv α (MonoidHom.range_eq_top.1 hα) hK
      (pCore_eq_bot_of_simple hQna)
  ·
    left
    have hα1 : α.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : α x ∈ α.range := ⟨x, rfl⟩
      rw [hα, Subgroup.mem_bot] at this
      exact this
    rw [hα1, inf_top_eq] at hK
    have hmem : ∀ x, ρ x ∈ alternatingGroup (Fin 5) := fun x => by
      rw [← hρ]; exact ⟨x, rfl⟩
    let ρ' : B →* alternatingGroup (Fin 5) := ρ.codRestrict _ hmem
    have hρ's : Function.Surjective ρ' := by
      intro y
      have : (y : Equiv.Perm (Fin 5)) ∈ ρ.range := by rw [hρ]; exact y.2
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩
    have hker : ρ'.ker = ρ.ker := by
      ext x
      simp only [MonoidHom.mem_ker, ρ']
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    have := alt5_simple
    exact nonempty_modO2_equiv ρ' hρ's (by rw [hker]; exact hK)
      (pCore_eq_bot_of_simple alt5_nonabelian)
  ·
    exfalso
    have hαs : Function.Surjective α := MonoidHom.range_eq_top.1 hα
    have hN1 : α.ker ≠ ⊤ := by
      intro h
      apply hQsolv
      have : Subsingleton Q := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hαs a
        obtain ⟨y, rfl⟩ := hαs b
        have hx : α x = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
        have hy : α y = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
        rw [hx, hy]
      infer_instance
    have hN2 : ρ.ker ≠ ⊤ := by
      intro h
      have : ρ.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, rfl⟩
        have : x ∈ ρ.ker := by rw [h]; trivial
        rw [MonoidHom.mem_ker] at this
        rw [this]
        exact Subgroup.one_mem _
      rw [hρ] at this
      have h60 := card_alt5
      have h1 : Nat.card (alternatingGroup (Fin 5)) = 1 := by
        rw [this]
        simp
      omega
    have hN2s : Group.IsSolvable ρ.ker := (hnorm _ inferInstance).resolve_left hN2
    have hmax : α.ker ⊔ ρ.ker = α.ker ∨ α.ker ⊔ ρ.ker = ⊤ := by
      by_cases h : α.ker ⊔ ρ.ker = α.ker
      · exact Or.inl h
      · right
        have hnormQ : (( α.ker ⊔ ρ.ker).map α).Normal := Subgroup.Normal.map inferInstance α hαs
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((α.ker ⊔ ρ.ker).map α) with h1 | h1
        · exfalso
          apply h
          apply le_antisymm
          · intro x hx
            have : α x ∈ (α.ker ⊔ ρ.ker).map α := Subgroup.mem_map_of_mem α hx
            rw [h1, Subgroup.mem_bot] at this
            exact this
          · exact le_sup_left
        ·
          rw [eq_top_iff]
          intro x _
          have hx' : α x ∈ (α.ker ⊔ ρ.ker).map α := by rw [h1]; trivial
          obtain ⟨y, hy, hyx⟩ := hx'
          have hz : y⁻¹ * x ∈ α.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
          have hxy : x = y * (y⁻¹ * x) := by group
          rw [hxy]
          exact Subgroup.mul_mem _ hy ((le_sup_left : α.ker ≤ α.ker ⊔ ρ.ker) hz)
    rcases hmax with h | h
    ·
      have hle : ρ.ker ≤ α.ker := by rw [← h]; exact le_sup_right
      have hdvd : α.ker.index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hle
      have e1 : α.ker.index = 168 := by
        rw [Subgroup.index_ker, hα, Subgroup.card_top, hQ]
      have e2 : ρ.ker.index = 60 := by
        rw [Subgroup.index_ker, hρ, card_alt5]
      rw [e1, e2] at hdvd
      omega
    ·
      have h1 : (α.ker ⊔ ρ.ker).map α = ρ.ker.map α := by
        rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 le_rfl, bot_sup_eq]
      have h2 : ρ.ker.map α = ⊤ := by
        rw [← h1, h, Subgroup.map_top_of_surjective α hαs]
      have hf : Function.Surjective (α.comp ρ.ker.subtype) := by
        intro q
        have : q ∈ ρ.ker.map α := by rw [h2]; trivial
        obtain ⟨y, hy, rfl⟩ := this
        exact ⟨⟨y, hy⟩, rfl⟩
      have := hN2s
      exact hQsolv (Group.isSolvable_of_surjective (f := α.comp ρ.ker.subtype) hf)

end CFSG.Quasithin.J4Fam
