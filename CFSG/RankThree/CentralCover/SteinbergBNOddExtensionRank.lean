module

public import CFSG.RankThree.CentralCover.SteinbergBNOddExtensionCore

public section

namespace CFSG.RankThree.CentralCover

open scoped commutatorElement

section IsotropicSubgroups

theorem exists_mem_not_mem_of_card_lt {G : Type*} [Group G] [Finite G] {U V : Subgroup G}
    (h : Nat.card U < Nat.card V) : ∃ x ∈ V, x ∉ U := by
  by_contra! h'
  exact absurd (Subgroup.card_le_of_le h') (not_le.2 h)

variable {P : Type*} [Group P] [Finite P] {A : Subgroup P} [A.Normal]
  (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A) {p : ℕ} (hp : p.Prime)
  (hpow : ∀ x : P, x ^ p ∈ A)

omit [Finite P] in
include hcomm in
theorem quotient_mul_comm_of_commutator_mem (u v : P ⧸ A) : u * v = v * u := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
  have h : ⁅(x : P ⧸ A), (y : P ⧸ A)⁆ = 1 := by
    rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← map_commutatorElement,
      QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 (hcomm x y)
  exact commutatorElement_eq_one_iff_mul_comm.1 h

omit [Finite P] in
include hpow in
theorem quotient_pow_eq_one_of_pow_mem (u : P ⧸ A) : u ^ p = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 (hpow x)

include hp hpow in
theorem exists_card_eq_pow_of_quotient (U : Subgroup (P ⧸ A)) : ∃ k, Nat.card U = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hW : IsPGroup p (P ⧸ A) := fun u =>
    ⟨1, by rw [pow_one]; exact quotient_pow_eq_one_of_pow_mem hpow u⟩
  exact (hW.to_subgroup U).exists_card_eq

omit [Finite P] in
include hp hpow in
theorem card_zpowers_of_ne_one {w : P ⧸ A} (hw : w ≠ 1) : Nat.card (Subgroup.zpowers w) = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (quotient_pow_eq_one_of_pow_mem hpow w) hw]

include hA hcomm hp hpow

theorem exists_isotropic_plane_of_mem (M : Subgroup P) [M.Normal] {T : Subgroup P}
    {V : Subgroup (P ⧸ A)} {x : P} (hxV : (x : P ⧸ A) ∈ V) (hx1 : (x : P ⧸ A) ≠ 1)
    (hT : ∀ y : P, (y : P ⧸ A) ∈ V → ⁅x, y⁆ ∈ T)
    (hTc : Nat.card (T.map (QuotientGroup.mk' M)) = p) (hV : p ^ 3 ≤ Nat.card V) :
    ∃ U ≤ V, U ≤ orthMod hA hcomm M U ∧ Nat.card U = p ^ 2 := by
  have hWc := quotient_mul_comm_of_commutator_mem hcomm
  have hWp := quotient_pow_eq_one_of_pow_mem hpow
  set H := V ⊓ orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A))
  have hH := card_le_card_inf_orthMod_mul hA hcomm M (T := T) (x := x) (V := V) hT
  rw [hTc] at hH
  have hHc : p ^ 2 ≤ Nat.card H := by
    have := hV.trans hH
    rw [pow_succ] at this
    exact Nat.le_of_mul_le_mul_right this hp.pos
  obtain ⟨y, hyH, hyx⟩ := exists_mem_not_mem_of_card_lt (U := Subgroup.zpowers (x : P ⧸ A))
    (V := H) (by
      rw [card_zpowers_of_ne_one hp hpow hx1]
      exact lt_of_lt_of_le (by
        rw [pow_two]
        exact lt_mul_of_one_lt_left hp.pos hp.one_lt) hHc)
  refine ⟨Subgroup.zpowers (x : P ⧸ A) ⊔ Subgroup.zpowers y, sup_le
    (Subgroup.zpowers_le.2 hxV) (Subgroup.zpowers_le.2 hyH.1), ?_, ?_⟩
  · exact sup_zpowers_le_orthMod hA hcomm M (zpowers_le_orthMod hA hcomm M _) hyH.2
  · rw [card_sup_zpowers_of_not_mem hp hWc hWp hyx, card_zpowers_of_ne_one hp hpow hx1,
      pow_two]

theorem exists_isotropic_plane (M : Subgroup P) [M.Normal] {T : Subgroup P}
    (hT : ∀ x y : P, ⁅x, y⁆ ∈ T) (hTc : Nat.card (T.map (QuotientGroup.mk' M)) = p)
    {V : Subgroup (P ⧸ A)} (hV : p ^ 3 ≤ Nat.card V) :
    ∃ U ≤ V, U ≤ orthMod hA hcomm M U ∧ Nat.card U = p ^ 2 := by
  obtain ⟨w, hwV, hw1⟩ := exists_mem_not_mem_of_card_lt (U := ⊥) (V := V) (by
    rw [Subgroup.card_bot]
    exact lt_of_lt_of_le (Nat.one_lt_pow (by norm_num) hp.one_lt) hV)
  rw [Subgroup.mem_bot] at hw1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  exact exists_isotropic_plane_of_mem hA hcomm hp hpow M hwV hw1 (fun y _ => hT x y) hTc hV

theorem exists_radical_of_card_eq_pow_three (M : Subgroup P) [M.Normal] {T : Subgroup P}
    (hT : ∀ x y : P, ⁅x, y⁆ ∈ T) (hTc : Nat.card (T.map (QuotientGroup.mk' M)) = p)
    {V : Subgroup (P ⧸ A)} (hV : Nat.card V = p ^ 3) :
    ∃ r ∈ V, r ≠ 1 ∧ V ≤ orthMod hA hcomm M (Subgroup.zpowers r) := by
  have hWc := quotient_mul_comm_of_commutator_mem hcomm
  have hWp := quotient_pow_eq_one_of_pow_mem hpow
  have hp1 := hp.one_lt
  obtain ⟨w, hwV, hw1⟩ := exists_mem_not_mem_of_card_lt (U := ⊥) (V := V) (by
    rw [Subgroup.card_bot, hV]
    exact Nat.one_lt_pow (by norm_num) hp1)
  rw [Subgroup.mem_bot] at hw1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  by_cases hVx : V ≤ orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A))
  · exact ⟨x, hwV, hw1, hVx⟩
  set H := V ⊓ orthMod hA hcomm M (Subgroup.zpowers (x : P ⧸ A)) with hHdef
  have hHV : H ≤ V := inf_le_left
  have hH := card_le_card_inf_orthMod_mul hA hcomm M (T := T) (x := x) (V := V)
    (fun y _ => hT x y)
  rw [hTc, hV] at hH
  have hHlt : Nat.card H < Nat.card V := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hHV) fun h => hVx ?_
    rw [← Subgroup.eq_of_le_of_card_ge hHV h.ge]
    exact inf_le_right
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_quotient hp hpow H
  rw [hk, hV] at hHlt
  rw [hk, pow_succ] at hH
  have hk2 : k = 2 := by
    have h1 := (Nat.pow_lt_pow_iff_right hp1).1 hHlt
    have h2 : p ^ 2 ≤ p ^ k := Nat.le_of_mul_le_mul_right hH hp.pos
    have h3 := (Nat.pow_le_pow_iff_right hp1).1 h2
    omega
  subst hk2
  have hxH : (x : P ⧸ A) ∈ H := ⟨hwV, mk_mem_orthMod_zpowers_self hA hcomm M x⟩
  have hpx := card_zpowers_of_ne_one hp hpow hw1
  obtain ⟨y, hyH, hyx⟩ := exists_mem_not_mem_of_card_lt (U := Subgroup.zpowers (x : P ⧸ A))
    (V := H) (by rw [hpx, hk, pow_two]; exact lt_mul_of_one_lt_left hp.pos hp1)
  have hHeq : Subgroup.zpowers (x : P ⧸ A) ⊔ Subgroup.zpowers y = H := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 hxH)
      (Subgroup.zpowers_le.2 hyH)) ?_
    rw [card_sup_zpowers_of_not_mem hp hWc hWp hyx, hpx, hk, pow_two]
  have hHiso : H ≤ orthMod hA hcomm M H := by
    rw [← hHeq]
    exact sup_zpowers_le_orthMod hA hcomm M (zpowers_le_orthMod hA hcomm M _) hyH.2
  obtain ⟨t, htV, htH⟩ := exists_mem_not_mem_of_card_lt (U := H) (V := V)
    (by rw [hk, hV]; exact hHlt)
  have hVeq : H ⊔ Subgroup.zpowers t = V := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hHV (Subgroup.zpowers_le.2 htV)) ?_
    rw [card_sup_zpowers_of_not_mem hp hWc hWp htH, hk, hV]
    ring_nf
    exact le_rfl
  obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective t
  have hH' := card_le_card_inf_orthMod_mul hA hcomm M (T := T) (x := t') (V := H)
    (fun y _ => hT t' y)
  rw [hTc, hk] at hH'
  obtain ⟨u, huH', hu1⟩ := exists_mem_not_mem_of_card_lt (U := ⊥)
    (V := H ⊓ orthMod hA hcomm M (Subgroup.zpowers (t' : P ⧸ A))) (by
      rw [Subgroup.card_bot]
      by_contra hle
      have h1 : Nat.card (H ⊓ orthMod hA hcomm M (Subgroup.zpowers (t' : P ⧸ A)) :
          Subgroup (P ⧸ A)) ≤ 1 := not_lt.1 hle
      have h2 := hH'.trans (Nat.mul_le_mul_right p h1)
      rw [one_mul, pow_two] at h2
      have := Nat.le_of_mul_le_mul_right (h2.trans (le_of_eq (one_mul p).symm)) hp.pos
      omega)
  rw [Subgroup.mem_bot] at hu1
  refine ⟨u, hHV huH'.1, hu1, ?_⟩
  rw [← hVeq]
  refine sup_le (hHiso.trans (orthMod_anti hA hcomm M (Subgroup.zpowers_le.2 huH'.1))) ?_
  rw [Subgroup.zpowers_le]
  have h1 : Subgroup.zpowers u ≤ orthMod hA hcomm M (Subgroup.zpowers (t' : P ⧸ A)) :=
    Subgroup.zpowers_le.2 huH'.2
  exact (le_orthMod_comm hA hcomm M).1 h1 (Subgroup.mem_zpowers _)

theorem exists_isotropic_solid {T : Subgroup P} (hT : ∀ x y : P, ⁅x, y⁆ ∈ T)
    (hTc : Nat.card (T.map (QuotientGroup.mk' (⊥ : Subgroup P))) = p)
    (hW4 : Nat.card (P ⧸ A) = p ^ 4) {x : P} (hx : x ∉ A) (hrad : ∀ y : P, ⁅x, y⁆ = 1) :
    ∃ U : Subgroup (P ⧸ A), U ≤ orthMod hA hcomm ⊥ U ∧ Nat.card U = p ^ 3 := by
  have hWc := quotient_mul_comm_of_commutator_mem hcomm
  have hWp := quotient_pow_eq_one_of_pow_mem hpow
  have hp1 := hp.one_lt
  have hx1 : (x : P ⧸ A) ≠ 1 := fun h => hx ((QuotientGroup.eq_one_iff x).1 h)
  have hr : ⊤ ≤ orthMod hA hcomm ⊥ (Subgroup.zpowers (x : P ⧸ A)) := by
    intro w _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [mk_mem_orthMod_zpowers, hrad y]
    exact Subgroup.one_mem _
  have hpx := card_zpowers_of_ne_one hp hpow hx1
  obtain ⟨w, -, hwx⟩ := exists_mem_not_mem_of_card_lt (U := Subgroup.zpowers (x : P ⧸ A))
    (V := ⊤) (by
      rw [hpx, Subgroup.card_top, hW4]
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 4 := Nat.pow_lt_pow_right hp1 (by norm_num))
  obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
  set U₁ := Subgroup.zpowers (x : P ⧸ A) ⊔ Subgroup.zpowers (w' : P ⧸ A)
  have hU₁ : Nat.card U₁ = p ^ 2 := by
    rw [card_sup_zpowers_of_not_mem hp hWc hWp hwx, hpx, pow_two]
  have hU₁iso : U₁ ≤ orthMod hA hcomm ⊥ U₁ :=
    sup_zpowers_le_orthMod hA hcomm ⊥ (zpowers_le_orthMod hA hcomm ⊥ _) (hr (Subgroup.mem_top _))
  have hU₁w : U₁ ≤ orthMod hA hcomm ⊥ (Subgroup.zpowers (w' : P ⧸ A)) := by
    refine sup_le ?_ (zpowers_le_orthMod hA hcomm ⊥ _)
    exact (le_orthMod_comm hA hcomm ⊥).1 (le_top.trans hr)
  have hH := card_le_card_inf_orthMod_mul hA hcomm ⊥ (T := T) (x := w')
    (V := (⊤ : Subgroup (P ⧸ A))) (fun y _ => hT w' y)
  rw [hTc, Subgroup.card_top, hW4] at hH
  obtain ⟨t, htH, htU⟩ := exists_mem_not_mem_of_card_lt (U := U₁)
    (V := ⊤ ⊓ orthMod hA hcomm ⊥ (Subgroup.zpowers (w' : P ⧸ A))) (by
      rw [hU₁]
      have h1 : p ^ 3 ≤ Nat.card (⊤ ⊓ orthMod hA hcomm ⊥ (Subgroup.zpowers (w' : P ⧸ A)) :
          Subgroup (P ⧸ A)) := by
        rw [pow_succ] at hH
        exact Nat.le_of_mul_le_mul_right hH hp.pos
      exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp1 (by norm_num)) h1)
  refine ⟨U₁ ⊔ Subgroup.zpowers t, ?_, ?_⟩
  · refine sup_zpowers_le_orthMod hA hcomm ⊥ hU₁iso ?_
    rw [orthMod_sup]
    exact ⟨hr (Subgroup.mem_top t), htH.2⟩
  · rw [card_sup_zpowers_of_not_mem hp hWc hWp htU, hU₁]
    ring

theorem card_le_of_le_orthMod_of_orthMod_top_eq_bot {T : Subgroup P}
    (hT : ∀ x y : P, ⁅x, y⁆ ∈ T)
    (hTc : Nat.card (T.map (QuotientGroup.mk' (⊥ : Subgroup P))) = p)
    (hW4 : Nat.card (P ⧸ A) = p ^ 4) (hnd : orthMod hA hcomm ⊥ ⊤ = ⊥)
    {U : Subgroup (P ⧸ A)} (hU : U ≤ orthMod hA hcomm ⊥ U) : Nat.card U ≤ p ^ 2 := by
  have hWc := quotient_mul_comm_of_commutator_mem hcomm
  have hWp := quotient_pow_eq_one_of_pow_mem hpow
  have hp1 := hp.one_lt
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_quotient hp hpow U
  have hk4 : k ≤ 4 := by
    have h := Subgroup.card_le_card_group U
    rw [hk, hW4] at h
    exact (Nat.pow_le_pow_iff_right hp1).1 h
  rw [hk]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hk2
  rcases (show k = 3 ∨ k = 4 by omega) with rfl | rfl
  ·
    obtain ⟨w, -, hwU⟩ := exists_mem_not_mem_of_card_lt (U := U) (V := ⊤) (by
      rw [hk, Subgroup.card_top, hW4]
      exact Nat.pow_lt_pow_right hp1 (by norm_num))
    have htop : U ⊔ Subgroup.zpowers w = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [card_sup_zpowers_of_not_mem hp hWc hWp hwU, hk, hW4]
      ring)
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
    have hH := card_le_card_inf_orthMod_mul hA hcomm ⊥ (T := T) (x := w') (V := U)
      (fun y _ => hT w' y)
    rw [hTc, hk] at hH
    obtain ⟨u, huH, hu1⟩ := exists_mem_not_mem_of_card_lt (U := ⊥)
      (V := U ⊓ orthMod hA hcomm ⊥ (Subgroup.zpowers (w' : P ⧸ A))) (by
        rw [Subgroup.card_bot]
        by_contra hle
        have h2 := hH.trans (Nat.mul_le_mul_right p (not_lt.1 hle))
        rw [one_mul] at h2
        have := (Nat.pow_le_pow_iff_right hp1).1 (h2.trans (pow_one p).symm.le)
        omega)
    rw [Subgroup.mem_bot] at hu1
    have hall : ⊤ ≤ orthMod hA hcomm ⊥ (Subgroup.zpowers u) := by
      rw [← htop]
      refine sup_le (hU.trans (orthMod_anti hA hcomm ⊥ (Subgroup.zpowers_le.2 huH.1))) ?_
      exact (le_orthMod_comm hA hcomm ⊥).1 (Subgroup.zpowers_le.2 huH.2)
    have hu : Subgroup.zpowers u ≤ orthMod hA hcomm ⊥ ⊤ := (le_orthMod_comm hA hcomm ⊥).1 hall
    rw [hnd] at hu
    exact hu1 (Subgroup.mem_bot.1 (hu (Subgroup.mem_zpowers u)))
  ·
    have htop : U = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hk, hW4])
    rw [htop, hnd] at hU
    have h := Subgroup.card_le_of_le hU
    rw [Subgroup.card_top, hW4, Subgroup.card_bot] at h
    exact absurd h (not_le.2 (Nat.one_lt_pow (by norm_num) hp1))

theorem exists_isotropic_plane_of_card_sq {T : Subgroup P} (hT : ∀ x y : P, ⁅x, y⁆ ∈ T)
    (hTA : T ≤ A) (hTp : ∀ t ∈ T, t ^ p = 1) (hTc : Nat.card T = p ^ 2)
    {V : Subgroup (P ⧸ A)} (hV : Nat.card V = p ^ 3) :
    ∃ U ≤ V, U ≤ orthMod hA hcomm ⊥ U ∧ Nat.card U = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  obtain ⟨c, hcT, hc1⟩ := exists_mem_not_mem_of_card_lt (U := ⊥) (V := T) (by
    rw [Subgroup.card_bot, hTc]
    exact Nat.one_lt_pow (by norm_num) hp1)
  rw [Subgroup.mem_bot] at hc1
  set C := Subgroup.zpowers c
  have hC : C.Normal := ⟨fun n hn g => by
    rw [← mul_comm_of_mem_le_center hA (hTA (Subgroup.zpowers_le.2 hcT hn)) g,
      mul_inv_cancel_right]
    exact hn⟩
  have hCc : Nat.card C = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hTp c hcT) hc1]
  have hCT : C ≤ T := Subgroup.zpowers_le.2 hcT
  have hTC : Nat.card (T.map (QuotientGroup.mk' C)) = p := by
    have h := card_inf_ker_mul_card_map (QuotientGroup.mk' C) T
    rw [QuotientGroup.ker_mk', inf_eq_right.2 hCT, hCc, hTc, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  obtain ⟨r, hrV, hr1, hVr⟩ := exists_radical_of_card_eq_pow_three hA hcomm hp hpow C hT hTC hV
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
  have hxC : ∀ y : P, (y : P ⧸ A) ∈ V → ⁅x, y⁆ ∈ C := fun y hy =>
    (mk_mem_orthMod_zpowers hA hcomm C).1 (hVr hy)
  have hCbot : Nat.card (C.map (QuotientGroup.mk' (⊥ : Subgroup P))) = p := by
    have h := card_inf_ker_mul_card_map (QuotientGroup.mk' (⊥ : Subgroup P)) C
    rw [QuotientGroup.ker_mk', inf_bot_eq, Subgroup.card_bot, one_mul, hCc] at h
    exact h
  exact exists_isotropic_plane_of_mem hA hcomm hp hpow ⊥ hrV hr1 hxC hCbot hV.ge

end IsotropicSubgroups

section PowerKernel

variable {P : Type*} [Group P] {A : Subgroup P} {p : ℕ}
  (hA : A ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A) (hpow : ∀ x : P, x ^ p ∈ A)
  (hp : p.Prime) (hp2 : p ≠ 2)

@[expose] def powKerSubgroup : Subgroup P :=
  (A.map (centralPowHom hA hcomm hpow hp hp2)).comap (centralPowHom hA hcomm hpow hp hp2)

theorem mem_powKerSubgroup {x : P} :
    x ∈ powKerSubgroup hA hcomm hpow hp hp2 ↔ ∃ a ∈ A, x ^ p = a ^ p := by
  simp only [powKerSubgroup, Subgroup.mem_comap, Subgroup.mem_map, centralPowHom_apply]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩⟩

theorem le_powKerSubgroup : A ≤ powKerSubgroup hA hcomm hpow hp hp2 := fun a ha =>
  (mem_powKerSubgroup hA hcomm hpow hp hp2).2 ⟨a, ha, rfl⟩

variable [A.Normal]

theorem mk_mem_map_powKerSubgroup {x : P} :
    (x : P ⧸ A) ∈ (powKerSubgroup hA hcomm hpow hp hp2).map (QuotientGroup.mk' A) ↔
      x ∈ powKerSubgroup hA hcomm hpow hp hp2 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    have h := mul_mem hy (le_powKerSubgroup hA hcomm hpow hp hp2 hyx)
    rwa [mul_inv_cancel_left] at h
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem card_quotient_le_card_powKer_mul [Finite P] :
    Nat.card (P ⧸ A) ≤ Nat.card ((powKerSubgroup hA hcomm hpow hp hp2).map
        (QuotientGroup.mk' A)) * Nat.card {a : P // a ∈ A ∧ a ^ p = 1} ∧
      (Nat.card (P ⧸ A) = Nat.card ((powKerSubgroup hA hcomm hpow hp hp2).map
        (QuotientGroup.mk' A)) * Nat.card {a : P // a ∈ A ∧ a ^ p = 1} →
        ∀ a ∈ A, ∃ x : P, x ^ p = a) := by
  set π := centralPowHom hA hcomm hpow hp hp2
  set K := powKerSubgroup hA hcomm hpow hp hp2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
  have h2 := card_inf_ker_mul_card_map (QuotientGroup.mk' A) K
  rw [QuotientGroup.ker_mk', inf_eq_right.2 (le_powKerSubgroup hA hcomm hpow hp hp2)] at h2
  have h3 := Subgroup.card_ker_mul_card_range π
  have hker : π.ker ≤ K := fun x hx => (mem_powKerSubgroup hA hcomm hpow hp hp2).2
    ⟨1, A.one_mem, by rw [← centralPowHom_apply hA hcomm hpow hp hp2, MonoidHom.mem_ker.1 hx,
      one_pow]⟩
  have hmapK : K.map π = A.map π := le_antisymm (Subgroup.map_le_iff_le_comap.2 le_rfl)
    (Subgroup.map_mono (le_powKerSubgroup hA hcomm hpow hp hp2))
  have h4 := card_inf_ker_mul_card_map π K
  rw [inf_eq_right.2 hker, hmapK] at h4
  have h5 : Nat.card A = Nat.card (A.map π) * Nat.card {a : P // a ∈ A ∧ a ^ p = 1} := by
    have hset : ((A.map π : Subgroup P) : Set P) = Set.range fun a : A => (a : P) ^ p := by
      ext y
      simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map, centralPowHom_apply, π]
      exact ⟨fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩, fun ⟨a, ha⟩ => ⟨a, a.2, ha⟩⟩
    rw [card_eq_card_pow_range_mul hA p, ← hset]
    rfl
  have hrange : π.range ≤ A := by
    rintro _ ⟨x, rfl⟩
    exact hpow x
  have h6 : Nat.card π.range ≤ Nat.card A := Subgroup.card_le_of_le hrange
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hkpos : 0 < Nat.card π.ker := Nat.card_pos
  have key : Nat.card (P ⧸ A) * Nat.card A ≤
      Nat.card (K.map (QuotientGroup.mk' A)) * Nat.card {a : P // a ∈ A ∧ a ^ p = 1} *
        Nat.card A := by
    calc Nat.card (P ⧸ A) * Nat.card A = Nat.card π.ker * Nat.card π.range := by rw [← h1, h3]
      _ ≤ Nat.card π.ker * Nat.card A := Nat.mul_le_mul_left _ h6
      _ = Nat.card K * Nat.card {a : P // a ∈ A ∧ a ^ p = 1} := by rw [h5, ← h4, mul_assoc]
      _ = _ := by rw [← h2]; ring
  refine ⟨Nat.le_of_mul_le_mul_right key hApos, fun heq a ha => ?_⟩
  have hr : Nat.card A ≤ Nat.card π.range := by
    have e : Nat.card π.ker * Nat.card A = Nat.card π.ker * Nat.card π.range := by
      calc Nat.card π.ker * Nat.card A = Nat.card K * Nat.card {a : P // a ∈ A ∧ a ^ p = 1} := by
            rw [h5, ← h4, mul_assoc]
        _ = Nat.card (P ⧸ A) * Nat.card A := by rw [← h2, heq]; ring
        _ = Nat.card π.ker * Nat.card π.range := by rw [← h1, h3]
    exact Nat.le_of_mul_le_mul_left e.le hkpos
  have := Subgroup.eq_of_le_of_card_ge hrange hr
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (this ▸ ha)
  exact ⟨x, hx⟩

end PowerKernel

section Statement

variable {P : Type*} [Group P] (A : Subgroup P) [A.Normal] (p : ℕ)

@[expose] def powKerSet : Set P := {x | ∃ a ∈ A, x ^ p = a ^ p}

@[expose] def CentralOddExtensionCaseOne (d : ℕ) : Prop :=
  d = 1 ∧ (∀ x : P, ∃ a ∈ A, x ^ p = a ^ p) ∧ ∀ x : P, (∀ y : P, ⁅x, y⁆ = 1) → x ∈ A

@[expose] def CentralOddExtensionCaseTwo (d : ℕ) : Prop :=
  d = 1 ∧ Nat.card (P ⧸ A) = p * Nat.card ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) ∧
    Nat.card ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) =
      p ^ 2 * Nat.card ((QuotientGroup.mk : P → P ⧸ A) ''
        {x | x ∈ powKerSet A p ∧ ∀ y ∈ powKerSet A p, ⁅x, y⁆ = 1})

@[expose] def CentralOddExtensionCaseThree (d : ℕ) : Prop :=
  d = 2 ∧ (∀ a ∈ A, ∃ x : P, ∃ c ∈ A, a = x ^ p * c ^ p) ∧
    Nat.card ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) = p ^ 2 ∧
    ∃ x ∈ powKerSet A p, ∃ y ∈ powKerSet A p, ⁅x, y⁆ ≠ 1

end Statement

theorem central_odd_prime_extension_exact_elementary_rank {P : Type*} [Group P] [Finite P]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hP : IsPGroup p P) (A : Subgroup P) [A.Normal]
    (hA : A ≤ Subgroup.center P) (hW : IsElementaryAbelian p (P ⧸ A)) {d : ℕ}
    (hd : Nat.card {a : P // a ∈ A ∧ a ^ p = 1} = p ^ d) :
    ((∀ x y : P, ⁅x, y⁆ ∈ A ∧ ⁅x, y⁆ ^ p = 1) ∧
      (∀ x y a c : P, a ∈ A → c ∈ A → ⁅x * a, y * c⁆ = ⁅x, y⁆) ∧
      (∀ x y z : P, ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ ∧ ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆) ∧
      ∀ x : P, ⁅x, x⁆ = 1) ∧
    ((∀ x : P, x ^ p ∈ A) ∧ ∀ x y : P, (x * y) ^ p = x ^ p * y ^ p) ∧
    Nat.card A = Nat.card (Set.range fun a : A => (a : P) ^ p) * p ^ d ∧
    (∃ r : ℕ, IsGreatest {k | ∃ U : Subgroup (P ⧸ A), IsIsotropicPowKer A p U ∧
      Nat.card U = p ^ k} r ∧ CFSG.pRank p P = d + r) ∧
    (∀ U : Subgroup (P ⧸ A), IsIsotropicPowKer A p U → ∃ E : Subgroup P,
      IsElementaryAbelian p E ∧ (∀ x : P, x ∈ E ∧ x ∈ A ↔ x ∈ A ∧ x ^ p = 1) ∧
      E.map (QuotientGroup.mk' A) = U) ∧
    (Nat.card (P ⧸ A) = p ^ 4 →
      (CFSG.pRank p P ≤ 3 → CFSG.pRank p P = 3 ∧
        (CentralOddExtensionCaseOne A p d ∨ CentralOddExtensionCaseTwo A p d ∨
          CentralOddExtensionCaseThree A p d) ∧
        ¬ (CentralOddExtensionCaseOne A p d ∧ CentralOddExtensionCaseTwo A p d) ∧
        ¬ (CentralOddExtensionCaseOne A p d ∧ CentralOddExtensionCaseThree A p d) ∧
        ¬ (CentralOddExtensionCaseTwo A p d ∧ CentralOddExtensionCaseThree A p d)) ∧
      (CentralOddExtensionCaseOne A p d ∨ CentralOddExtensionCaseTwo A p d ∨
          CentralOddExtensionCaseThree A p d → CFSG.pRank p P = 3)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hcomm : ∀ x y : P, ⁅x, y⁆ ∈ A := fun x y => by
    have h : ⁅(x : P ⧸ A), (y : P ⧸ A)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (mul_comm' (x : P ⧸ A) y)
    rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← map_commutatorElement,
      QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  have hpow : ∀ x : P, x ^ p ∈ A := fun x => by
    have h : (x : P ⧸ A) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hW.exponent_dvd_p _
    rw [← QuotientGroup.mk_pow] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  have hcp := commutatorElement_pow_eq_one hA hcomm hpow
  obtain ⟨r, hrS, hrank⟩ := pRank_eq_add_of_isIsotropicPowKer hA hcomm hpow hp hp2 hP hd
  refine ⟨⟨fun x y => ⟨hcomm x y, hcp x y⟩, fun x y a c ha hc => by
      rw [commutatorElement_mul_central_left hA ha, commutatorElement_mul_central_right hA hc],
      fun x y z => ⟨commutatorElement_mul_left_of_central hA hcomm x y z,
        commutatorElement_mul_right_of_central hA hcomm x y z⟩, commutatorElement_self⟩,
    ⟨hpow, mul_pow_prime_of_central hA hcomm hpow hp hp2⟩,
    by rw [card_eq_card_pow_range_mul hA p, hd], ⟨r, hrS, hrank⟩, fun U hU => ?_,
    fun hW4 => ?_⟩
  · obtain ⟨E, hE, hEA, hEU, -⟩ := exists_lift_of_isIsotropicPowKer hA hcomm hpow hp hp2 hU
    exact ⟨E, hE, hEA, hEU⟩
  set π := centralPowHom hA hcomm hpow hp hp2
  set K := powKerSubgroup hA hcomm hpow hp hp2
  set Kb := K.map (QuotientGroup.mk' A) with hKb
  set Ω := A ⊓ π.ker with hΩ
  have hΩmem : ∀ x : P, x ∈ Ω ↔ x ∈ A ∧ x ^ p = 1 := fun x => by
    rw [hΩ, Subgroup.mem_inf, MonoidHom.mem_ker, centralPowHom_apply]
  have hΩcard : Nat.card Ω = p ^ d := by
    rw [← hd]
    exact Nat.card_congr (Equiv.subtypeEquivRight hΩmem)
  have hTΩ : ∀ x y : P, ⁅x, y⁆ ∈ Ω := fun x y => (hΩmem _).2 ⟨hcomm x y, hcp x y⟩
  have hΩbot : Nat.card (Ω.map (QuotientGroup.mk' (⊥ : Subgroup P))) = p ^ d := by
    have h := card_inf_ker_mul_card_map (QuotientGroup.mk' (⊥ : Subgroup P)) Ω
    rw [QuotientGroup.ker_mk', inf_bot_eq, Subgroup.card_bot, one_mul, hΩcard] at h
    exact h
  have hmemKb : ∀ x : P, (x : P ⧸ A) ∈ Kb ↔ ∃ a ∈ A, x ^ p = a ^ p := fun x =>
    (mk_mem_map_powKerSubgroup hA hcomm hpow hp hp2).trans
      (mem_powKerSubgroup hA hcomm hpow hp hp2)
  have hIsoK : ∀ U : Subgroup (P ⧸ A),
      IsIsotropicPowKer A p U ↔ U ≤ Kb ∧ U ≤ orthMod hA hcomm ⊥ U := by
    intro U
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun w hw => ?_, (le_orthMod_iff hA hcomm ⊥).2 fun x y hx hy =>
        Subgroup.mem_bot.2 (h2 x y hx hy)⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      exact (hmemKb x).2 (h1 x hw)
    · rintro ⟨h1, h2⟩
      exact ⟨fun x hx => (hmemKb x).1 (h1 hx), fun x y hx hy =>
        Subgroup.mem_bot.1 ((le_orthMod_iff hA hcomm ⊥).1 h2 x y hx hy)⟩
  have hrle : ∀ U : Subgroup (P ⧸ A), U ≤ Kb → U ≤ orthMod hA hcomm ⊥ U →
      ∀ k, Nat.card U = p ^ k → k ≤ r :=
    fun U h1 h2 k hk => hrS.2 ⟨U, (hIsoK U).2 ⟨h1, h2⟩, hk⟩
  obtain ⟨Ur, hUr, hUrc⟩ := hrS.1
  rw [hIsoK] at hUr
  have hKset : ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) = (Kb : Set (P ⧸ A)) := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmemKb x).2 hx
    · intro hw
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      exact ⟨x, (hmemKb x).1 hw, rfl⟩
  have hKcard : Nat.card ((QuotientGroup.mk : P → P ⧸ A) '' powKerSet A p) = Nat.card Kb := by
    rw [hKset]
    rfl
  set R := Kb ⊓ orthMod hA hcomm ⊥ Kb with hR
  have hRset : ((QuotientGroup.mk : P → P ⧸ A) ''
      {x | x ∈ powKerSet A p ∧ ∀ y ∈ powKerSet A p, ⁅x, y⁆ = 1}) = (R : Set (P ⧸ A)) := by
    ext w
    constructor
    · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
      refine ⟨(hmemKb x).2 hx, (mk_mem_orthMod hA hcomm ⊥).2 fun y hy => ?_⟩
      rw [commutatorElement_mem_swap, hxy y ((hmemKb y).1 hy)]
      exact Subgroup.one_mem _
    · intro hw
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      refine ⟨x, ⟨(hmemKb x).1 hw.1, fun y hy => ?_⟩, rfl⟩
      have h := (mk_mem_orthMod hA hcomm ⊥).1 hw.2 y ((hmemKb y).2 hy)
      rw [commutatorElement_mem_swap, Subgroup.mem_bot] at h
      exact h
  have hRcard : Nat.card ((QuotientGroup.mk : P → P ⧸ A) ''
      {x | x ∈ powKerSet A p ∧ ∀ y ∈ powKerSet A p, ⁅x, y⁆ = 1}) = Nat.card R := by
    rw [hRset]
    rfl
  have hW4' : Nat.card (⊤ : Subgroup (P ⧸ A)) = p ^ 4 := by rw [Subgroup.card_top, hW4]
  have hcase1 : CentralOddExtensionCaseOne A p d → CFSG.pRank p P = 3 := by
    rintro ⟨rfl, hκ, hnd⟩
    have hKtop : Kb = ⊤ := eq_top_iff.2 fun w _ => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      exact (hmemKb x).2 (hκ x)
    have hnd' : orthMod hA hcomm ⊥ ⊤ = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
      refine hnd x fun y => ?_
      have h := (mk_mem_orthMod hA hcomm ⊥).1 hw y (Subgroup.mem_top _)
      rw [commutatorElement_mem_swap, Subgroup.mem_bot] at h
      exact h
    rw [pow_one] at hΩbot
    have hr2 : 2 ≤ r := by
      obtain ⟨U, -, hU, hUc⟩ := exists_isotropic_plane hA hcomm hp hpow ⊥ hTΩ hΩbot
        (V := ⊤) (by rw [hW4']; exact Nat.pow_le_pow_right hp.pos (by norm_num))
      exact hrle U (hKtop ▸ le_top) hU 2 hUc
    have hr2' : r ≤ 2 := by
      have h := card_le_of_le_orthMod_of_orthMod_top_eq_bot hA hcomm hp hpow hTΩ hΩbot hW4
        hnd' hUr.2
      rw [hUrc] at h
      exact (Nat.pow_le_pow_iff_right hp1).1 h
    rw [hrank]
    omega
  have hcase2 : CentralOddExtensionCaseTwo A p d → CFSG.pRank p P = 3 := by
    rintro ⟨rfl, hκ1, hrk⟩
    rw [hKcard] at hκ1 hrk
    rw [hRcard] at hrk
    have hKb3 : Nat.card Kb = p ^ 3 := by
      rw [hW4, show p ^ 4 = p * p ^ 3 by ring] at hκ1
      exact (Nat.eq_of_mul_eq_mul_left hp.pos hκ1).symm
    have hRc : Nat.card R = p := by
      rw [hKb3, show p ^ 3 = p ^ 2 * p by ring] at hrk
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hrk).symm
    rw [pow_one] at hΩbot
    have hr2 : 2 ≤ r := by
      obtain ⟨U, hUK, hU, hUc⟩ := exists_isotropic_plane hA hcomm hp hpow ⊥ hTΩ hΩbot
        (V := Kb) hKb3.ge
      exact hrle U hUK hU 2 hUc
    have hr2' : r ≤ 2 := by
      by_contra h
      have h1 := Subgroup.card_le_of_le hUr.1
      rw [hUrc, hKb3] at h1
      have hr3 : r = 3 := by
        have := (Nat.pow_le_pow_iff_right hp1).1 h1
        omega
      have hUK : Ur = Kb := Subgroup.eq_of_le_of_card_ge hUr.1 (by rw [hUrc, hKb3, hr3])
      have hRK : R = Kb := inf_eq_left.2 (hUK ▸ hUr.2)
      rw [hRK, hKb3] at hRc
      have := Nat.pow_right_injective hp.two_le (hRc.trans (pow_one p).symm)
      omega
    rw [hrank]
    omega
  have hcase3 : CentralOddExtensionCaseThree A p d → CFSG.pRank p P = 3 := by
    rintro ⟨rfl, -, hK2, x, hx, y, hy, hxy⟩
    rw [hKcard] at hK2
    have hr1 : 1 ≤ r := by
      obtain ⟨w, hwK, hw1⟩ := exists_mem_not_mem_of_card_lt (U := ⊥) (V := Kb) (by
        rw [Subgroup.card_bot, hK2]
        exact Nat.one_lt_pow (by norm_num) hp1)
      rw [Subgroup.mem_bot] at hw1
      exact hrle _ (Subgroup.zpowers_le.2 hwK) (zpowers_le_orthMod hA hcomm ⊥ w) 1
        (by rw [card_zpowers_of_ne_one hp hpow hw1, pow_one])
    have hr1' : r ≤ 1 := by
      by_contra h
      have h1 := Subgroup.card_le_of_le hUr.1
      rw [hUrc, hK2] at h1
      have hr2 : r = 2 := by
        have := (Nat.pow_le_pow_iff_right hp1).1 h1
        omega
      have hUK : Ur = Kb := Subgroup.eq_of_le_of_card_ge hUr.1 (by rw [hUrc, hK2, hr2])
      have hiso : Kb ≤ orthMod hA hcomm ⊥ Kb := hUK ▸ hUr.2
      exact hxy (Subgroup.mem_bot.1 ((le_orthMod_iff hA hcomm ⊥).1 hiso x y
        ((hmemKb x).2 hx) ((hmemKb y).2 hy)))
    rw [hrank]
    omega
  refine ⟨fun hle => ?_, fun h => h.elim hcase1 fun h => h.elim hcase2 hcase3⟩
  have hdr : d + r ≤ 3 := hrank ▸ hle
  obtain ⟨hK1, hK1eq⟩ := card_quotient_le_card_powKer_mul hA hcomm hpow hp hp2
  rw [hd, hW4] at hK1
  rw [hd] at hK1eq
  have hKbk : ∃ k, Nat.card Kb = p ^ k := exists_card_eq_pow_of_quotient hp hpow Kb
  obtain ⟨k, hk⟩ := hKbk
  have hk4 : k ≤ 4 := by
    have h := Subgroup.card_le_card_group Kb
    rw [hk, hW4] at h
    exact (Nat.pow_le_pow_iff_right hp1).1 h
  rw [hk, ← pow_add] at hK1
  have hkd : 4 ≤ k + d := (Nat.pow_le_pow_iff_right hp1).1 hK1
  have hcases : CentralOddExtensionCaseOne A p d ∨ CentralOddExtensionCaseTwo A p d ∨
      CentralOddExtensionCaseThree A p d := by
    have hd3 : d ≤ 3 := by omega
    interval_cases d
    ·
      exfalso
      have hΩbot' : Ω = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hΩcard, pow_zero])
      have hKtop : Kb = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hk, hW4]; congr 1; omega)
      have hiso : (⊤ : Subgroup (P ⧸ A)) ≤ orthMod hA hcomm ⊥ ⊤ :=
        (le_orthMod_iff hA hcomm ⊥).2 fun x y _ _ => by
          have h := hTΩ x y
          rw [hΩbot'] at h
          exact h
      have := hrle ⊤ hKtop.ge hiso 4 hW4'
      omega
    ·
      rw [pow_one] at hΩbot
      have hk34 : k = 3 ∨ k = 4 := by omega
      rcases hk34 with rfl | rfl
      ·
        right; left
        have hnotiso : ¬ Kb ≤ orthMod hA hcomm ⊥ Kb := fun h => by
          have := hrle Kb le_rfl h 3 hk
          omega
        have hRK : R ≤ Kb := inf_le_left
        have hRorth : R ≤ orthMod hA hcomm ⊥ Kb := inf_le_right
        obtain ⟨j, hj⟩ := exists_card_eq_pow_of_quotient hp hpow R
        have hj3 : j ≤ 3 := by
          have h := Subgroup.card_le_of_le hRK
          rw [hj, hk] at h
          exact (Nat.pow_le_pow_iff_right hp1).1 h
        have hj0 : j ≠ 0 := by
          rintro rfl
          obtain ⟨r₀, hr₀K, hr₀1, hKr₀⟩ := exists_radical_of_card_eq_pow_three hA hcomm hp hpow
            ⊥ hTΩ hΩbot hk
          have hr₀R : r₀ ∈ R := ⟨hr₀K, (le_orthMod_comm hA hcomm ⊥).1 hKr₀
            (Subgroup.mem_zpowers r₀)⟩
          have hRbot : R = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])
          rw [hRbot, Subgroup.mem_bot] at hr₀R
          exact hr₀1 hr₀R
        have hj2 : j ≠ 2 := by
          rintro rfl
          obtain ⟨t, htK, htR⟩ := exists_mem_not_mem_of_card_lt (U := R) (V := Kb) (by
            rw [hj, hk]
            exact Nat.pow_lt_pow_right hp1 (by norm_num))
          have hKeq : R ⊔ Subgroup.zpowers t = Kb := by
            refine Subgroup.eq_of_le_of_card_ge (sup_le hRK (Subgroup.zpowers_le.2 htK)) ?_
            rw [card_sup_zpowers_of_not_mem hp (quotient_mul_comm_of_commutator_mem hcomm)
              (quotient_pow_eq_one_of_pow_mem hpow) htR, hj, hk]
            ring_nf
            exact le_rfl
          have hRiso : R ≤ orthMod hA hcomm ⊥ R := hRorth.trans (orthMod_anti hA hcomm ⊥ hRK)
          have hKR : Kb ≤ orthMod hA hcomm ⊥ R := (le_orthMod_comm hA hcomm ⊥).1 hRorth
          apply hnotiso
          rw [← hKeq]
          exact sup_zpowers_le_orthMod hA hcomm ⊥ hRiso (hKR htK)
        have hj3' : j ≠ 3 := by
          rintro rfl
          apply hnotiso
          rw [← Subgroup.eq_of_le_of_card_ge hRK (by rw [hj, hk])]
          exact hRorth.trans (orthMod_anti hA hcomm ⊥ hRK)
        have hj1 : j = 1 := by omega
        subst hj1
        refine ⟨rfl, ?_, ?_⟩
        · rw [hKcard, hk, hW4]
          ring
        · rw [hKcard, hRcard, hk, hj]
          ring
      ·
        left
        have hKtop : Kb = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hk, hW4])
        refine ⟨rfl, fun x => (hmemKb x).1 (hKtop ▸ Subgroup.mem_top _), fun x hx => ?_⟩
        by_contra hxA
        obtain ⟨U, hU, hUc⟩ := exists_isotropic_solid hA hcomm hp hpow hTΩ hΩbot hW4 hxA hx
        have := hrle U (hKtop ▸ le_top) hU 3 hUc
        omega
    ·
      right; right
      have hk2 : k = 2 := by
        by_contra hk2
        have hk3 : 3 ≤ k := by omega
        obtain ⟨V', hV'⟩ := Sylow.exists_subgroup_card_pow_prime (G := Kb) p (n := 3) (by
          rw [hk]
          exact Nat.pow_dvd_pow p hk3)
        set V := V'.map Kb.subtype
        have hV : Nat.card V = p ^ 3 := by
          rw [Subgroup.card_map_of_injective Kb.subtype_injective, hV']
        obtain ⟨U, hUV, hU, hUc⟩ := exists_isotropic_plane_of_card_sq hA hcomm hp hpow hTΩ
          inf_le_left (fun t ht => ((hΩmem t).1 ht).2) hΩcard hV
        have := hrle U (hUV.trans (Subgroup.map_subtype_le V')) hU 2 hUc
        omega
      subst hk2
      refine ⟨rfl, fun a ha => ?_, by rw [hKcard, hk], ?_⟩
      · obtain ⟨x, hx⟩ := hK1eq (by rw [hW4, hk]; ring) a ha
        exact ⟨x, 1, A.one_mem, by rw [one_pow, mul_one, hx]⟩
      · by_contra hall
        push Not at hall
        have hiso : Kb ≤ orthMod hA hcomm ⊥ Kb := (le_orthMod_iff hA hcomm ⊥).2
          fun x y hx hy => Subgroup.mem_bot.2 (hall x ((hmemKb x).1 hx) y ((hmemKb y).1 hy))
        have := hrle Kb le_rfl hiso 2 hk
        omega
    ·
      exfalso
      obtain ⟨w, hwK, hw1⟩ := exists_mem_not_mem_of_card_lt (U := ⊥) (V := Kb) (by
        rw [Subgroup.card_bot, hk]
        exact Nat.one_lt_pow (by omega) hp1)
      rw [Subgroup.mem_bot] at hw1
      have := hrle _ (Subgroup.zpowers_le.2 hwK) (zpowers_le_orthMod hA hcomm ⊥ w) 1
        (by rw [card_zpowers_of_ne_one hp hpow hw1, pow_one])
      omega
  refine ⟨hcases.elim hcase1 fun h => h.elim hcase2 hcase3, hcases, ?_, ?_, ?_⟩
  · rintro ⟨⟨-, hκ, -⟩, ⟨-, hκ1, -⟩⟩
    have hKtop : Kb = ⊤ := eq_top_iff.2 fun w _ => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      exact (hmemKb x).2 (hκ x)
    rw [hKcard, hKtop, Subgroup.card_top, hW4] at hκ1
    have : p ^ 4 * 1 = p ^ 4 * p := by rw [mul_one]; nth_rewrite 1 [hκ1]; ring
    have := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 4) this
    omega
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    omega
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    omega


end CFSG.RankThree.CentralCover
