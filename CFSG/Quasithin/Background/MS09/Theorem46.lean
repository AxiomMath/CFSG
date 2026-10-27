module

public import CFSG.Quasithin.Background.MS09.LLemma
public import CFSG.Quasithin.Background.MS09.Module45

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B6 CFSG.Quasithin.MS09.Mod

variable {P : Type} [Group P] {V : Type} [CommGroup V] {ρ : P →* MulAut V}

namespace Th46

theorem exists_fix_ne_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {N : Subgroup P}
    (hN : IsPGroup 2 N) (hV1 : (⊤ : Subgroup V) ≠ ⊥) : fixIn ρ N ⊤ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥N V := MulAction.compHom V (ρ.comp N.subtype)
  have hcong := hN.card_modEq_card_fixedPoints V
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by simpa using hV v⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hV2
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hV1
    rw [pow_zero] at hn
    have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hn).1
    exact Subsingleton.elim _ _
  have heven : 2 ∣ Nat.card (MulAction.fixedPoints ↥N V) := by
    have h2 : 2 ∣ Nat.card V := by rw [hn]; exact dvd_pow_self 2 hn0
    exact (Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr h2)))
  have hfix : ∀ v : V, v ∈ MulAction.fixedPoints ↥N V ↔ v ∈ fixIn ρ N ⊤ := fun v => by
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact ⟨Subgroup.mem_top v, fun g hg => h ⟨g, hg⟩⟩
    · intro h n
      exact h.2 n n.2
  intro hbot
  have hsub : MulAction.fixedPoints ↥N V = {1} := by
    ext v
    rw [hfix, hbot, Subgroup.mem_bot, Set.mem_singleton_iff]
  rw [hsub, Nat.card_unique] at heven
  exact absurd heven (by decide)

theorem normal_le_cenIn [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hirr : ∀ W : Subgroup V, (⊤ : Subgroup P) ≤ stabIn ρ W → W = ⊥ ∨ W = ⊤)
    (hV1 : (⊤ : Subgroup V) ≠ ⊥) {N : Subgroup P} (hN : IsPGroup 2 N) (hNn : N.Normal) :
    N ≤ cenIn ρ ⊤ := by
  have hstab : (⊤ : Subgroup P) ≤ stabIn ρ (fixIn ρ N ⊤) := fun g _ =>
    mem_stabIn_of fun w hw => ⟨Subgroup.mem_top _, fun n hn => by
      have h1 := hw.2 (g⁻¹ * n * g) (by simpa using hNn.conj_mem n hn g⁻¹)
      have e : n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      rw [e, apply_conj', h1]⟩
  rcases hirr _ hstab with h | h
  · exact absurd h (exists_fix_ne_one hV hN hV1)
  · intro n hn v _
    have hv : v ∈ fixIn ρ N ⊤ := by rw [h]; exact Subgroup.mem_top v
    exact hv.2 n hn

@[expose] def lClosure (ρ : P →* MulAut V) (L : Subgroup P) (C : Subgroup V) : Subgroup V :=
  ⨆ (l : P) (_ : l ∈ L), C.map (ρ l).toMonoidHom

theorem le_lClosure (L : Subgroup P) (C : Subgroup V) : C ≤ lClosure ρ L C := by
  intro v hv
  refine le_iSup₂_of_le (f := fun (l : P) (_ : l ∈ L) => C.map (ρ l).toMonoidHom) 1 L.one_mem
    le_rfl ⟨v, hv, ?_⟩
  simp

theorem lClosure_le {L : Subgroup P} {C W : Subgroup V} (hW : L ≤ stabIn ρ W) (hC : C ≤ W) :
    lClosure ρ L C ≤ W :=
  iSup₂_le fun l hl => by
    rintro _ ⟨c, hc, rfl⟩
    exact mem_of_mem_stabIn (hW hl) (hC hc)

theorem le_stabIn_lClosure [Finite V] (L : Subgroup P) (C : Subgroup V) :
    L ≤ stabIn ρ (lClosure ρ L C) := by
  intro l' hl'
  refine mem_stabIn_of fun u hu => ?_
  have hle : (lClosure ρ L C).map (ρ l').toMonoidHom ≤ lClosure ρ L C := by
    rw [lClosure, Subgroup.map_iSup]
    refine iSup_le fun l => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hl => ?_
    rw [Subgroup.map_map]
    refine le_iSup₂_of_le (f := fun (l : P) (_ : l ∈ L) => C.map (ρ l).toMonoidHom) (l' * l)
      (L.mul_mem hl' hl) (le_of_eq ?_)
    congr 1
    ext v
    simp [map_mul, MulAut.mul_apply]
  exact hle ⟨u, hu, rfl⟩

theorem le_cenIn_lClosure {L Q O : Subgroup P} (hOQ : O ≤ Q)
    (hLO : L ≤ Subgroup.normalizer (O : Set P)) :
    O ≤ cenIn ρ (lClosure ρ L (fixIn ρ Q ⊤)) := by
  intro o ho
  have hle : lClosure ρ L (fixIn ρ Q ⊤) ≤ fixIn ρ O ⊤ := by
    refine iSup₂_le fun l hl => ?_
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨Subgroup.mem_top _, fun o' ho' => ?_⟩
    have hmem : l⁻¹ * o' * l ∈ O := by
      have := (Subgroup.mem_normalizer_iff''.mp (hLO hl) o').mp ho'
      simpa [mul_assoc] using this
    have e : o' = l * (l⁻¹ * o' * l) * l⁻¹ := by group
    show ρ o' (ρ l v) = ρ l v
    rw [e, apply_conj', hv.2 _ (hOQ hmem)]
  exact fun u hu => (hle hu).2 o ho

section MinPar

variable [Finite P] [Finite V] {S M : Subgroup P} (hmp : MinParabolic (⊤ : Subgroup P) S M)
  (hV : ∀ v : V, v ^ 2 = 1)
  (hirr : ∀ W : Subgroup V, (⊤ : Subgroup P) ≤ stabIn ρ W → W = ⊥ ∨ W = ⊤)
  (hnt : ¬ (⊤ : Subgroup P) ≤ cenIn ρ ⊤)

include hnt in
theorem top_ne_bot : (⊤ : Subgroup V) ≠ ⊥ := by
  intro h
  apply hnt
  intro g _ v hv
  have : v ∈ (⊥ : Subgroup V) := h ▸ hv
  rw [Subgroup.mem_bot] at this
  rw [this, map_one]

omit [Finite V] in
theorem conjSub_top (g : P) : B6.conjSub g (⊤ : Subgroup P) = ⊤ :=
  conjSub_eq_self (Subgroup.le_normalizer (Subgroup.mem_top g))

omit [Finite P] [Finite V] in
theorem cenIn_top_normal : (cenIn ρ (⊤ : Subgroup V)).Normal :=
  ⟨fun k hk g v _ => by
    have e : ρ (g * k * g⁻¹) v = ρ g (ρ k ((ρ g)⁻¹ v)) := by
      simp [map_mul, map_inv, MulAut.mul_apply]
    rw [e, hk _ (Subgroup.mem_top _)]
    simp⟩

include hmp hV hirr hnt in
theorem fixIn_ne_top {Q : Subgroup P} (hQ : IsSylowTwoOf Q ⊤) : fixIn ρ Q ⊤ ≠ ⊤ := by
  intro htop
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, -, rfl⟩ := isSylowTwoOf_exists_conj hmp.isSylow hQ
  have hM := (MS09.MinParabolic.isUniqueMaxSub hmp).conjSub h
  rw [conjSub_top] at hM
  have hQK : B6.conjSub h S ≤ cenIn ρ ⊤ := fun q hq v _ => by
    have : v ∈ fixIn ρ (B6.conjSub h S) ⊤ := by rw [htop]; exact Subgroup.mem_top v
    exact this.2 q hq
  have hKn : (⊤ : Subgroup P) ≤ Subgroup.normalizer (cenIn ρ ⊤ : Set P) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr cenIn_top_normal]
  rcases hM.dichotomy hQ le_rfl le_top hKn with h1 | h1
  · rw [sup_eq_right.mpr hQK] at h1
    exact hnt h1.ge
  · rw [inf_eq_left.mpr hQK] at h1
    have hOS : pCoreOf 2 (⊤ : Subgroup P) ≤ S := pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
    have hSO : S = pCoreOf 2 ⊤ := (Subgroup.eq_of_le_of_card_ge hOS (by
      rw [← card_conjSub S h]
      exact Subgroup.card_le_of_le h1)).symm
    apply hmp.not_normal
    rw [hSO]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤

include hmp hV hirr hnt in
theorem stabIn_fixIn_le {h : P} : stabIn ρ (fixIn ρ (B6.conjSub h S) ⊤) ≤ B6.conjSub h M := by
  have hQ : IsSylowTwoOf (B6.conjSub h S) ⊤ := by
    have := isSylowTwoOf_conjSub hmp.isSylow h
    rwa [conjSub_top] at this
  have hM := (MS09.MinParabolic.isUniqueMaxSub hmp).conjSub h
  rw [conjSub_top] at hM
  refine hM.le_of_lt (fun q hq => mem_stabIn_of fun v hv => ?_) (lt_of_le_of_ne le_top ?_)
  · rw [hv.2 q hq]
    exact hv
  · intro hstab
    rcases hirr _ hstab.ge with h1 | h1
    · exact exists_fix_ne_one hV hQ.2.1 (top_ne_bot hnt) h1
    · exact fixIn_ne_top hmp hV hirr hnt hQ h1

include hmp hV hirr hnt in
theorem exists_step {A : Subgroup P} (hA : IsPGroup 2 A)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ u : V, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹)
    (hAc : ¬ A ≤ cenIn ρ ⊤) :
    ∃ D : Subgroup P, D < A ∧ A ⊓ cenIn ρ ⊤ ≤ D ∧
      D.relIndex A * Nat.card (fixIn ρ A ⊤) ≤ Nat.card (fixIn ρ D ⊤) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1 := top_ne_bot hnt
  have hO2n : (pCoreOf 2 (⊤ : Subgroup P)).Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup P)))
  have hO2 := normal_le_cenIn hV hirr hV1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤) hO2n
  have hAO : ¬ A ≤ pCoreOf 2 ⊤ := fun h => hAc (h.trans hO2)
  obtain ⟨S', hS', hAS'⟩ := exists_isSylowTwoOf_ge hA (le_top : A ≤ ⊤)
  obtain ⟨g, -, rfl⟩ := isSylowTwoOf_exists_conj hmp.isSylow hS'
  have hM' := (MS09.MinParabolic.isUniqueMaxSub hmp).conjSub g
  rw [conjSub_top] at hM'
  obtain ⟨L, L₀, -, hAL, hmax, hgenL, hnotM⟩ := LLemma.lLemma hS' hM' hAS' hAO
  have hAO2 : IsPGroup 2 ↥(A ⊔ pCoreOf 2 L) := IsPGroup.to_sup_of_normal_right' hA
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    (hAL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
  obtain ⟨SL, hSL, hASL⟩ := exists_isSylowTwoOf_ge hAO2
    (sup_le hAL (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
  obtain ⟨Q, hQ, hSLQ⟩ := exists_isSylowTwoOf_ge hSL.2.1 (le_top : SL ≤ ⊤)
  obtain ⟨h, -, rfl⟩ := isSylowTwoOf_exists_conj hmp.isSylow hQ
  have hAQ : A ≤ B6.conjSub h S := (le_sup_left.trans hASL).trans hSLQ
  have hOQ : pCoreOf 2 L ≤ B6.conjSub h S := (le_sup_right.trans hASL).trans hSLQ
  set C := fixIn ρ (B6.conjSub h S) ⊤ with hC
  set U := lClosure ρ L C with hU
  have hCU : C ≤ U := le_lClosure L C
  have hLU : L ≤ stabIn ρ U := le_stabIn_lClosure L C
  have hOU : pCoreOf 2 L ≤ cenIn ρ U :=
    le_cenIn_lClosure hOQ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hquadU : ∀ a ∈ A, ∀ b ∈ A, ∀ u ∈ U, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹ :=
    fun a ha b hb u _ => hquad a ha b hb u
  have hCX : C ≤ fixIn ρ A U := fun v hv => ⟨hCU hv, fun a ha => hv.2 a (hAQ ha)⟩
  have hgenU : ∀ W : Subgroup V, W ≤ U → L ≤ stabIn ρ W → fixIn ρ A U ≤ W → W = U :=
    fun W hWU hLW hXW => le_antisymm hWU (lClosure_le hLW (hCX.trans hXW))
  have hntU : ¬ A ≤ cenIn ρ U := by
    intro hAU
    obtain ⟨x, hxL, hxL₀⟩ := SetLike.exists_of_lt hmax.lt
    have hxA : B6.conjSub x A ≤ cenIn ρ U := by
      intro a' ha' u hu
      have hu' : (ρ x)⁻¹ u ∈ U := by
        rw [← map_inv]
        exact mem_of_mem_stabIn ((stabIn ρ U).inv_mem (hLU hxL)) hu
      have e : a' = x * (x⁻¹ * a' * x) * x⁻¹ := by group
      have e2 : u = ρ x ((ρ x)⁻¹ u) := by simp
      rw [e, e2, apply_conj', hAU (mem_conjSub.mp ha') _ hu']
    have hLc : L ≤ cenIn ρ U := by
      rw [← hgenL x hxL hxL₀]
      exact sup_le (sup_le hAU hxA) hOU
    have hLC : L ≤ stabIn ρ C := fun l hl =>
      mem_stabIn_of fun v hv => by rw [hLc hl v (hCU hv)]; exact hv
    have hle := hLC.trans (stabIn_fixIn_le hmp hV hirr hnt (h := h))
    apply hnotM (h * g⁻¹) (Subgroup.mem_top _)
    rw [← conjSub_mul, inv_mul_cancel_right]
    exact hle
  have hmod := Mod.relIndex_mul_card_fixIn_le hSL hASL hmax hLU hOU hquadU hgenU hntU
  refine ⟨A ⊓ cenIn ρ U, lt_of_le_of_ne inf_le_left fun he => hntU (he ▸ inf_le_right),
    inf_le_inf_left _ fun k hk u _ => hk u (Subgroup.mem_top u), ?_⟩
  have hUF : U ⊓ fixIn ρ A ⊤ = fixIn ρ A U :=
    le_antisymm (fun v hv => ⟨hv.1, hv.2.2⟩) (fun v hv => ⟨hv.1, Subgroup.mem_top v, hv.2⟩)
  have hUD : U ⊔ fixIn ρ A ⊤ ≤ fixIn ρ (A ⊓ cenIn ρ U) ⊤ :=
    sup_le (fun v hv => ⟨Subgroup.mem_top v, fun d hd => hd.2 v hv⟩)
      (fixIn_anti inf_le_left ⊤)
  have hprod := card_sup_mul_card_inf U (fixIn ρ A ⊤)
  rw [hUF] at hprod
  have h1 : Nat.card U * Nat.card (fixIn ρ A ⊤) ≤
      Nat.card (fixIn ρ (A ⊓ cenIn ρ U) ⊤) * Nat.card (fixIn ρ A U) := by
    rw [← hprod]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hUD)
  have hXpos : 0 < Nat.card (fixIn ρ A U) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hXpos
  calc Nat.card (fixIn ρ A U) * ((A ⊓ cenIn ρ U).relIndex A * Nat.card (fixIn ρ A ⊤))
      = ((A ⊓ cenIn ρ U).relIndex A * Nat.card (fixIn ρ A U)) * Nat.card (fixIn ρ A ⊤) := by
        ring
    _ ≤ Nat.card U * Nat.card (fixIn ρ A ⊤) := Nat.mul_le_mul_right _ hmod
    _ ≤ Nat.card (fixIn ρ (A ⊓ cenIn ρ U) ⊤) * Nat.card (fixIn ρ A U) := h1
    _ = Nat.card (fixIn ρ A U) * Nat.card (fixIn ρ (A ⊓ cenIn ρ U) ⊤) := mul_comm _ _

include hmp hV hirr hnt in
theorem relIndex_mul_card_fixIn_le_of_minParabolic {A : Subgroup P} (hA : IsPGroup 2 A)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ u : V, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹) :
    (A ⊓ cenIn ρ ⊤).relIndex A * Nat.card (fixIn ρ A ⊤) ≤ Nat.card V := by
  suffices key : ∀ n, ∀ A : Subgroup P, Nat.card A = n → IsPGroup 2 A →
      (∀ a ∈ A, ∀ b ∈ A, ∀ u : V, ρ a (ρ b u * u⁻¹) = ρ b u * u⁻¹) →
      (A ⊓ cenIn ρ ⊤).relIndex A * Nat.card (fixIn ρ A ⊤) ≤ Nat.card V from
    key _ A rfl hA hquad
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hA hquad
    by_cases hAc : A ≤ cenIn ρ ⊤
    · rw [inf_eq_left.mpr hAc, Subgroup.relIndex_self, one_mul]
      have htop : fixIn ρ A ⊤ = ⊤ := eq_top_iff.mpr fun v _ =>
        ⟨Subgroup.mem_top v, fun a ha => hAc ha v (Subgroup.mem_top v)⟩
      rw [htop, Subgroup.card_top]
    · obtain ⟨D, hDA, hcD, hstep⟩ := exists_step hmp hV hirr hnt hA hquad hAc
      have hcard : Nat.card D < n := by
        rw [← hn]
        exact lt_of_le_of_ne (Subgroup.card_le_of_le hDA.le)
          fun he => hDA.ne (Subgroup.eq_of_le_of_card_ge hDA.le he.ge)
      have hIH := ih _ hcard D rfl (hA.to_le hDA.le)
        fun a ha b hb u => hquad a (hDA.le ha) b (hDA.le hb) u
      have hDcen : D ⊓ cenIn ρ ⊤ = A ⊓ cenIn ρ ⊤ :=
        le_antisymm (inf_le_inf_right _ hDA.le) (le_inf hcD inf_le_right)
      rw [← Subgroup.relIndex_mul_relIndex (A ⊓ cenIn ρ ⊤) D A hcD hDA.le, ← hDcen]
      calc (D ⊓ cenIn ρ ⊤).relIndex D * D.relIndex A * Nat.card (fixIn ρ A ⊤)
          = (D ⊓ cenIn ρ ⊤).relIndex D * (D.relIndex A * Nat.card (fixIn ρ A ⊤)) := by ring
        _ ≤ (D ⊓ cenIn ρ ⊤).relIndex D * Nat.card (fixIn ρ D ⊤) := Nat.mul_le_mul_left _ hstep
        _ ≤ Nat.card V := hIH

end MinPar

end Th46

end CFSG.Quasithin.MS09

end
