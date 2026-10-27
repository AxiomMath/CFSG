module

public import CFSG.Quasithin.H13.A7Nat1238QTabA314

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

abbrev altFix (S : Finset (Fin 7)) : Subgroup (Perm (Fin 7)) :=
  (alternatingGroup ↥S).map (Perm.ofSubtype : Perm ↥S →* Perm (Fin 7))

theorem card_altFix {S : Finset (Fin 7)} (hS : S.card = 5) : Nat.card (altFix S) = 60 := by
  rw [Subgroup.card_map_of_injective Perm.ofSubtype_injective]
  have : Nontrivial ↥S := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe, hS]
    norm_num
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe, hS]
  decide

theorem altFix_apply_of_not_mem {S : Finset (Fin 7)} {σ : Perm (Fin 7)} (hσ : σ ∈ altFix S)
    {x : Fin 7} (hx : x ∉ S) : σ x = x := by
  obtain ⟨τ, -, rfl⟩ := hσ
  exact Perm.ofSubtype_apply_of_not_mem τ hx

theorem mem_altFix_of {S : Finset (Fin 7)} {σ : Perm (Fin 7)}
    (hA : σ ∈ alternatingGroup (Fin 7)) (hF : ∀ x, x ∉ S → σ x = x) : σ ∈ altFix S := by
  rw [altFix, alternatingGroup.map_ofSubtype]
  refine ⟨?_, hA⟩
  have hp : ∀ x, σ x ∈ S ↔ x ∈ S := fun x => by
    by_cases hx : x ∈ S
    · simp only [hx, iff_true]
      by_contra h
      have h2 : σ x = x := σ.injective (hF _ h)
      exact h (by rw [h2]; exact hx)
    · simp only [hx, iff_false]
      rw [hF x hx]
      exact hx
  exact ⟨σ.subtypePerm hp, Perm.ofSubtype_subtypePerm hp fun x hx => by
    by_contra h
    exact hx (hF x h)⟩

theorem exists_altFix_apply {S : Finset (Fin 7)} (hS : S.card = 5) {x y : Fin 7} (hx : x ∈ S)
    (hy : y ∈ S) : ∃ σ ∈ altFix S, σ x = y := by
  classical
  by_cases hxy : x = y
  · exact ⟨1, one_mem _, by rw [hxy, Perm.one_apply]⟩
  obtain ⟨c, hc⟩ : ((S.erase x).erase y).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxy, hy⟩),
      Finset.card_erase_of_mem hx, hS]
    norm_num
  obtain ⟨hcy, hc'⟩ := Finset.mem_erase.1 hc
  obtain ⟨hcx, hcS⟩ := Finset.mem_erase.1 hc'
  refine ⟨swap x c * swap x y, mem_altFix_of ?_ fun z hz => ?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (Ne.symm hcx), sign_swap hxy]
    decide
  · have hzx : z ≠ x := fun h => hz (h ▸ hx)
    have hzy : z ≠ y := fun h => hz (h ▸ hy)
    have hzc : z ≠ c := fun h => hz (h ▸ hcS)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hzx hzc]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hxy) hcy.symm]

theorem exists_compl_pair {S : Finset (Fin 7)} (hS : S.card = 5) :
    ∃ a b : Fin 7, a ≠ b ∧ a ∉ S ∧ b ∉ S ∧ ∀ x, x ∉ S → x = a ∨ x = b := by
  classical
  have h2 : Sᶜ.card = 2 := by rw [Finset.card_compl, hS]; rfl
  obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.1 h2
  refine ⟨a, b, hab, ?_, ?_, fun x hx => ?_⟩
  · have : a ∈ Sᶜ := by rw [hSab]; simp
    exact Finset.mem_compl.1 this
  · have : b ∈ Sᶜ := by rw [hSab]; simp
    exact Finset.mem_compl.1 this
  · have : x ∈ Sᶜ := Finset.mem_compl.2 hx
    rw [hSab] at this
    simpa using this

theorem not_mem_of_stab {S : Finset (Fin 7)} {σ : Perm (Fin 7)} (hσ : ∀ x ∈ S, σ x ∈ S)
    {x : Fin 7} (hx : x ∉ S) : σ x ∉ S := by
  classical
  intro h
  have hsurj : ∀ y ∈ S, ∃ z ∈ S, σ z = y := by
    have hinj : Set.InjOn σ S := fun u _ v _ huv => σ.injective huv
    have himage : S.image σ = S :=
      Finset.eq_of_subset_of_card_le (fun y hy => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
        exact hσ z hz) (by rw [Finset.card_image_of_injOn hinj])
    intro y hy
    rw [← himage] at hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨z, hz, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hsurj _ h
  exact hx (σ.injective hzx ▸ hz)

theorem fix_or_swap_inv {σ : Perm (Fin 7)} {a b : Fin 7}
    (h : (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a)) :
    (σ a = a ∧ σ b = b ∧ σ⁻¹ a = a ∧ σ⁻¹ b = b) ∨
      (σ a = b ∧ σ b = a ∧ σ⁻¹ a = b ∧ σ⁻¹ b = a) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, Perm.inv_eq_iff_eq.2 h1.symm, Perm.inv_eq_iff_eq.2 h2.symm⟩
  · exact Or.inr ⟨h1, h2, Perm.inv_eq_iff_eq.2 h2.symm, Perm.inv_eq_iff_eq.2 h1.symm⟩

theorem fix_compl_of_perfect {S : Finset (Fin 7)} (hS : S.card = 5) {Y : Subgroup (Perm (Fin 7))}
    (hY : ⁅Y, Y⁆ = Y) (hYS : ∀ y ∈ Y, ∀ x ∈ S, y x ∈ S) : ∀ y ∈ Y, ∀ x, x ∉ S → y x = x := by
  obtain ⟨a, b, hab, haS, hbS, hab'⟩ := exists_compl_pair hS
  have hsw : ∀ y ∈ Y, (y a = a ∧ y b = b) ∨ (y a = b ∧ y b = a) := by
    intro y hy
    rcases hab' _ (not_mem_of_stab (hYS y hy) haS) with h1 | h1 <;>
      rcases hab' _ (not_mem_of_stab (hYS y hy) hbS) with h2 | h2
    · exact absurd (y.injective (h1.trans h2.symm)) hab
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (y.injective (h1.trans h2.symm)) hab
  have hF : ⁅Y, Y⁆ ≤ fixingSubgroup (Perm (Fin 7)) ({a, b} : Set (Fin 7)) := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    rw [mem_fixingSubgroup_iff]
    rcases fix_or_swap_inv (hsw y₁ hy₁) with ⟨h1, h2, i1, i2⟩ | ⟨h1, h2, i1, i2⟩ <;>
      rcases fix_or_swap_inv (hsw y₂ hy₂) with ⟨h3, h4, i3, i4⟩ | ⟨h3, h4, i3, i4⟩ <;>
      · rintro x (rfl | rfl) <;>
          simp [commutatorElement_def, Perm.smul_def, Perm.mul_apply, h1, h2, h3, h4, i1, i2,
            i3, i4]
  intro y hy x hx
  rw [← hY] at hy
  have := ((mem_fixingSubgroup_iff (Perm (Fin 7))).1 (hF hy)) x
  rcases hab' x hx with rfl | rfl
  · exact this (by simp)
  · exact this (by simp)

theorem eq_alt_of_card_ge {X : Subgroup (Perm (Fin 7))} (hX : X ≤ alternatingGroup (Fin 7))
    (hc : 420 ≤ Nat.card X) : X = alternatingGroup (Fin 7) := by
  classical
  set A := alternatingGroup (Fin 7) with hAdef
  set Y := X.subgroupOf A with hYdef
  have hA : Nat.card A = 2520 := by
    rw [card_alternating_fin 7 (by norm_num)]
    decide
  have hY : Nat.card Y = Nat.card X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hidx : Nat.card Y * Y.index = 2520 := by rw [Subgroup.card_mul_index, hA]
  have hidx6 : Y.index ≤ 6 := by
    rw [hY] at hidx
    by_contra h
    push Not at h
    have : 420 * 7 ≤ Nat.card X * Y.index := Nat.mul_le_mul hc h
    omega
  have : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  set φ := MulAction.toPermHom A (A ⧸ Y) with hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, hA] at h1
    have h2 : (Nat.card (A ⧸ Y)).factorial ≤ 720 :=
      (Nat.factorial_le hidx6).trans (by decide)
    omega
  · have hcore : Y.normalCore = ⊤ := by rw [Subgroup.normalCore_eq_ker]; exact h
    have hYtop : Y = ⊤ := top_le_iff.1 (hcore ▸ Y.normalCore_le)
    apply le_antisymm hX
    intro a ha
    have h1 : (⟨a, ha⟩ : A) ∈ Y := hYtop ▸ mem_top _
    exact Subgroup.mem_subgroupOf.1 h1

theorem alt7_overgroup_cases {S : Finset (Fin 7)} (hS : S.card = 5)
    {X : Subgroup (Perm (Fin 7))} (hXA : X ≤ alternatingGroup (Fin 7)) (hFX : altFix S ≤ X)
    (hXp : ⁅X, X⁆ = X) {τ : Perm (Fin 7)} (hτX : τ ∈ normalizer (X : Set (Perm (Fin 7))))
    (hτS : ∀ x ∈ S, τ x ∈ S) (hτ : ∃ x, x ∉ S ∧ τ x ≠ x) :
    X = altFix S ∨ X = alternatingGroup (Fin 7) := by
  classical
  by_cases hstab : ∀ g ∈ X, ∀ x ∈ S, g x ∈ S
  · left
    refine le_antisymm (fun g hg => ?_) hFX
    exact mem_altFix_of (hXA hg) (fix_compl_of_perfect hS hXp hstab g hg)
  right
  push Not at hstab
  obtain ⟨g, hg, s, hs, hgs⟩ := hstab
  obtain ⟨a, b, hab, haS, hbS, hab'⟩ := exists_compl_pair hS
  have hτab : τ a = b ∧ τ b = a := by
    obtain ⟨x, hx, hτx⟩ := hτ
    rcases hab' _ (not_mem_of_stab hτS haS) with h1 | h1 <;>
      rcases hab' _ (not_mem_of_stab hτS hbS) with h2 | h2
    · exact absurd (τ.injective (h1.trans h2.symm)) hab
    · exfalso
      rcases hab' x hx with rfl | rfl
      · exact hτx h1
      · exact hτx h2
    · exact ⟨h1, h2⟩
    · exact absurd (τ.injective (h1.trans h2.symm)) hab
  have hconj : ∀ h ∈ X, τ * h * τ⁻¹ ∈ X := fun h hh => (mem_normalizer_iff.1 hτX h).1 hh
  have hreach : ∀ u : Fin 7, u ∉ S → ∃ h ∈ X, ∃ t ∈ S, h t = u := by
    have hgs' := hab' _ hgs
    have hτg : τ * g * τ⁻¹ ∈ X := hconj g hg
    have hτs : τ s ∈ S := hτS s hs
    have hτgs : (τ * g * τ⁻¹) (τ s) = τ (g s) := by
      simp [Perm.mul_apply]
    intro u hu
    rcases hab' u hu with rfl | rfl <;> rcases hgs' with hga | hga
    · exact ⟨g, hg, s, hs, hga⟩
    · exact ⟨τ * g * τ⁻¹, hτg, τ s, hτs, by rw [hτgs, hga, hτab.2]⟩
    · exact ⟨τ * g * τ⁻¹, hτg, τ s, hτs, by rw [hτgs, hga, hτab.1]⟩
    · exact ⟨g, hg, s, hs, hga⟩
  obtain ⟨h₁, hh₁, s₁, hs₁, h₁s₁⟩ := hreach a haS
  have horb : ∀ u : Fin 7, ∃ h ∈ X, h a = u := by
    have hs₁a : h₁⁻¹ a = s₁ := Perm.inv_eq_iff_eq.2 h₁s₁.symm
    have hS' : ∀ u ∈ S, ∃ h ∈ X, h a = u := fun u hu => by
      obtain ⟨σ, hσ, hσu⟩ := exists_altFix_apply hS hs₁ hu
      exact ⟨σ * h₁⁻¹, X.mul_mem (hFX hσ) (X.inv_mem hh₁), by
        rw [Perm.mul_apply, hs₁a, hσu]⟩
    intro u
    by_cases hu : u ∈ S
    · exact hS' u hu
    · obtain ⟨h₂, hh₂, t, ht, h₂t⟩ := hreach u hu
      obtain ⟨k, hk, hka⟩ := hS' t ht
      exact ⟨h₂ * k, X.mul_mem hh₂ hk, by rw [Perm.mul_apply, hka, h₂t]⟩
  have horbit : MulAction.orbit ↥X a = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    obtain ⟨h, hh, hu⟩ := horb u
    exact ⟨⟨h, hh⟩, hu⟩
  have hidx : (MulAction.stabilizer ↥X a).index = 7 := by
    rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_fin]
  have hstab : (altFix S).subgroupOf X ≤ MulAction.stabilizer ↥X a := by
    intro h hh
    rw [MulAction.mem_stabilizer_iff]
    exact altFix_apply_of_not_mem (Subgroup.mem_subgroupOf.1 hh) haS
  have h60 : 60 ≤ Nat.card (MulAction.stabilizer ↥X a) := by
    have h1 := Subgroup.card_le_of_le hstab
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFX).toEquiv, card_altFix hS] at h1
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥X a)
  rw [hidx] at hcard
  exact eq_alt_of_card_ge hXA (by omega)

theorem le_of_le_sup_center_of_perfect {G : Type*} [Group G] {A A' C : Subgroup G}
    (hC : C ≤ center G) (hA' : ⁅A', A'⁆ = A') (h : A' ≤ A ⊔ C) : A' ≤ A := by
  have hCN : C ≤ normalizer (A : Set G) := by
    intro z hz
    rw [mem_normalizer_iff]
    intro b
    rw [← Subgroup.mem_center_iff.1 (hC hz) b, mul_inv_cancel_right]
  rw [← hA', Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨b, hb, z, hz, rfl⟩ :=
    CFSG.QuasithinUnique.Setup.Family.mem_sup_of_le_normalizer hCN (h hx)
  obtain ⟨b', hb', z', hz', rfl⟩ :=
    CFSG.QuasithinUnique.Setup.Family.mem_sup_of_le_normalizer hCN (h hy)
  rw [commutatorElement_mul_center (hC hz) (hC hz')]
  exact A.mul_mem (A.mul_mem (A.mul_mem hb hb') (A.inv_mem hb)) (A.inv_mem hb')

theorem card_map_of_injOn {G N : Type*} [Group G] [Group N] {f : G →* N} {H : Subgroup G}
    (h : Function.Injective (f.comp H.subtype)) : Nat.card (H.map f) = Nat.card H := by
  have : H.map f = (f.comp H.subtype).range := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [this]
  exact (Nat.card_congr (MonoidHom.ofInjective h).toEquiv).symm

theorem eq_top_of_alt7_overgroup {Λ : Type} [Group Λ] [Finite Λ]
    (hΛ : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤) (hZ : Odd (Nat.card (center Λ)))
    {f : Λ →* Perm (Fin 7)}
    (hfr : f.range = alternatingGroup (Fin 7)) (hfk : f.ker ≤ center Λ) {S : Finset (Fin 7)}
    (hS : S.card = 5) {B K P : Subgroup Λ} (hB : IsAlt 5 ↥B) (hBK : B < K) (hK : ⁅K, K⁆ = K)
    (hBS : ∀ b ∈ B, ∀ x ∈ S, f b x ∈ S) (hP : QuasithinUnique.IsSylowTwoOf P ⊤)
    (hPS : ∀ t ∈ P, ∀ x ∈ S, f t x ∈ S) (hPK : P ≤ normalizer (K : Set Λ)) : K = ⊤ := by
  classical
  obtain ⟨eB⟩ := hB
  have hBinj : Function.Injective (f.comp B.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hb
    have hbZ : (b : Λ) ∈ center Λ := hfk hb
    have hc : eB b ∈ center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨c, rfl⟩ := eB.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.1 hbZ c)
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    rw [Subgroup.mem_bot]
    exact eB.injective (hc.trans (map_one eB).symm)
  have hfB : Nat.card (B.map f) = 60 := by
    rw [card_map_of_injOn hBinj, Nat.card_congr eB.toEquiv, card_alternating_fin 5 (by norm_num)]
    decide
  have hBp : ⁅B, B⁆ = B := by
    have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    have : Group.IsPerfect ↥B :=
      Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
    exact Subgroup.isPerfect_iff.1 this
  have hfBp : ⁅B.map f, B.map f⁆ = B.map f := by rw [← Subgroup.map_commutator, hBp]
  have hfBA : B.map f ≤ alternatingGroup (Fin 7) := hfr ▸ Subgroup.map_le_range f B
  have hfBS : ∀ y ∈ B.map f, ∀ x ∈ S, y x ∈ S := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBS b hb
  have hfBF : B.map f = altFix S := by
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [hfB, card_altFix hS])
    exact mem_altFix_of (hfBA hy) (fix_compl_of_perfect hS hfBp hfBS y hy)
  have hXA : K.map f ≤ alternatingGroup (Fin 7) := hfr ▸ Subgroup.map_le_range f K
  have hFX : altFix S ≤ K.map f := hfBF ▸ Subgroup.map_mono hBK.le
  have hXp : ⁅K.map f, K.map f⁆ = K.map f := by rw [← Subgroup.map_commutator, hK]
  have hcardΛ := Subgroup.card_ker_mul_card_range f
  rw [hfr, card_alternating_fin 7 (by norm_num)] at hcardΛ
  have hkodd : Odd (Nat.card f.ker) := Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hfk)
  obtain ⟨-, hP2, hPodd⟩ := hP
  have hPidx : ¬ 2 ∣ P.index := by
    have : (P.subgroupOf ⊤).index = P.index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    rwa [this] at hPodd
  have h8 : 8 ∣ Nat.card P := by
    have h1 : 8 ∣ Nat.card P * P.index := by
      rw [Subgroup.card_mul_index, ← hcardΛ]
      exact dvd_mul_of_dvd_right (by decide) _
    have hcop : Nat.Coprime 8 P.index :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hPidx)
    exact hcop.dvd_of_dvd_mul_right h1
  have hPinj : Function.Injective (f.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ht
    obtain ⟨k, hk⟩ := hP2 t
    have h1 : orderOf (⟨(t : Λ), ht⟩ : f.ker) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf (⟨(t : Λ), ht⟩ : f.ker) ∣ Nat.card f.ker := orderOf_dvd_natCard _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have h3 : orderOf (⟨(t : Λ), ht⟩ : f.ker) = 1 := by
      rcases j with _ | j
      · simpa using hj
      · exfalso
        rw [hj, pow_succ] at h2
        exact (Nat.not_even_iff_odd.2 hkodd) (even_iff_two_dvd.2 (dvd_of_mul_left_dvd h2))
    rw [orderOf_eq_one_iff] at h3
    have h4 : (t : Λ) = 1 := congrArg Subtype.val h3
    rw [Subgroup.mem_bot]
    exact Subtype.ext h4
  obtain ⟨t, ht, hτ⟩ : ∃ t ∈ P, f t ∉ altFix S := by
    by_contra hall
    push Not at hall
    have hle : P.map f ≤ altFix S := by
      rintro _ ⟨t, ht, rfl⟩
      exact hall t ht
    have h1 := Subgroup.card_dvd_of_le hle
    rw [card_map_of_injOn hPinj, card_altFix hS] at h1
    have := h8.trans h1
    norm_num at this
  have hτmove : ∃ x, x ∉ S ∧ f t x ≠ x := by
    by_contra hall
    push Not at hall
    exact hτ (mem_altFix_of (hfr ▸ MonoidHom.mem_range.2 ⟨t, rfl⟩) hall)
  have hτN : f t ∈ normalizer ((K.map f : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) :=
    Subgroup.le_normalizer_map f ⟨t, hPK ht, rfl⟩
  rcases alt7_overgroup_cases hS hXA hFX hXp hτN (hPS t ht) hτmove with h | h
  ·
    exfalso
    have hKB : K ≤ B ⊔ f.ker := by
      rw [← Subgroup.comap_map_eq]
      intro k hk
      have : f k ∈ K.map f := ⟨k, hk, rfl⟩
      rw [h, ← hfBF] at this
      exact this
    exact hBK.not_ge (le_of_le_sup_center_of_perfect hfk hK hKB)
  ·
    have hK' : (⊤ : Subgroup Λ) ≤ K ⊔ f.ker := by
      rw [← Subgroup.comap_map_eq]
      intro x _
      have : f x ∈ K.map f := by
        rw [h, ← hfr]
        exact MonoidHom.mem_range.2 ⟨x, rfl⟩
      exact this
    exact top_le_iff.1 (le_of_le_sup_center_of_perfect hfk hΛ hK')

end CFSG.Quasithin.H13.A7
