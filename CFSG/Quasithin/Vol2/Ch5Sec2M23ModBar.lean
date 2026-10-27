module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Mod
public import CFSG.Quasithin.Recognition.M23FactsHeptad
public import Certificates.Certificate7098
public import CFSG.Quasithin.Recognition.UniquenessSystemDefs
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction CFSG.A7Fano CFSG.M23Heptad CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.L246.C123 (A7)
open CFSG.Quasithin.Asc94 (heptad₀)
open scoped Pointwise

@[expose] def ιinv : Fin 23 → Fin 7 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 0, 5, 6]

theorem ιbar_mem (i : Fin 7) : ιbar i ∈ heptad₀ := by
  revert i
  decide

theorem ιinv_ιbar (i : Fin 7) : ιinv (ιbar i) = i := by
  revert i
  decide

theorem ιbar_ιinv {x : Fin 23} (hx : x ∈ heptad₀) : ιbar (ιinv x) = x := by
  revert x
  decide

theorem ιbar_injective : Function.Injective ιbar := fun i j h => by
  rw [← ιinv_ιbar i, ← ιinv_ιbar j, h]

@[expose] def ιEquiv : {x // x ∈ heptad₀} ≃ Fin 7 where
  toFun x := ιinv x.1
  invFun i := ⟨ιbar i, ιbar_mem i⟩
  left_inv x := Subtype.ext (ιbar_ιinv x.2)
  right_inv i := ιinv_ιbar i

abbrev M2bar : Subgroup ↥NativeSporadic.M23 := stabilizer ↥NativeSporadic.M23 heptad₀

@[expose] def πbar : ↥M2bar →* Perm (Fin 7) :=
  (Equiv.permCongrHom ιEquiv).toMonoidHom.comp (blockRestr heptad₀)

theorem πbar_apply (k : ↥M2bar) (i : Fin 7) :
    ιbar (πbar k i) = ((k : ↥NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) := by
  have hk : ((k : ↥NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) ∈ heptad₀ :=
    (stab_mem_iff.1 k.2 (ιbar i)).2 (ιbar_mem i)
  change ιbar (ιinv (((k : ↥NativeSporadic.M23) : Perm (Fin 23)) (ιbar i))) = _
  exact ιbar_ιinv hk

theorem πbar_eq_iff {k : ↥M2bar} {σ : Perm (Fin 7)} :
    πbar k = σ ↔ ∀ i, ((k : ↥NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) = ιbar (σ i) := by
  constructor
  · rintro rfl i
    rw [πbar_apply]
  · intro h
    ext i
    apply congrArg Fin.val
    apply ιbar_injective
    rw [πbar_apply, h]

theorem mem_ker_πbar {k : ↥M2bar} :
    k ∈ πbar.ker ↔ ∀ x ∈ heptad₀, (k : ↥NativeSporadic.M23) • x = x := by
  rw [MonoidHom.mem_ker, ← blockRestr_eq_one_iff]
  change (Equiv.permCongrHom ιEquiv) (blockRestr heptad₀ k) = 1 ↔ _
  exact map_eq_one_iff _ (Equiv.permCongrHom ιEquiv).injective

theorem card_M2bar :
    Nat.card M2bar = 40320 := by
  classical
  have horb := orbit_eq_of_reach_closed Asc94.m23Insp_hgens M23Insp.chk_H_reach
    M23Insp.chk_H_closed
  have hidx : (stabilizer ↥NativeSporadic.M23 heptad₀).index = 253 := by
    rw [MulAction.index_stabilizer]
    have e : MulAction.orbit ↥NativeSporadic.M23 heptad₀ =
        ((M23Insp.data.H.toFinset : Finset (Finset (Fin 23))) : Set (Finset (Fin 23))) := by
      ext B
      rw [Finset.mem_coe, List.mem_toFinset]
      exact horb B
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup M23Insp.chk_H_nodup,
      M23Insp.chk_H_len]
  have h : Nat.card M2bar * 253 = 40320 * 253 := by
    have h' := Subgroup.card_mul_index M2bar
    rw [hidx, CFSG.Sporadic.Schreier.m23_card] at h'
    rw [h']
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem ks_mem_M2bar :
    ∀ g ∈ M23Insp.ks, g ∈ M2bar := fun g hg => mem_stabilizer_iff.2 (M23Insp.chk_ks_fix g hg)

theorem card_ker_πbar_le :
    Nat.card πbar.ker ≤ 16 := by
  classical
  have hle : πbar.ker ≤ stabilizer ↥M2bar M23Insp.data.t₀ := by
    intro k hk
    rw [mem_ker_πbar] at hk
    rw [mem_stabilizer_iff]
    funext i
    exact hk (M23Insp.data.t₀ i) (M23Insp.valid.t₀_mem i)
  have h1 := Subgroup.card_le_of_le hle
  have h2 := card_orbit_mul_card_stabilizer (Γ := ↥M2bar) M23Insp.data.t₀
  rw [card_M2bar] at h2
  have horb : 2520 ≤ Nat.card (orbit ↥M2bar M23Insp.data.t₀) := by
    have := le_card_orbit M2bar ks_mem_M2bar M23Insp.valid.T_reach M23Insp.valid.T_nodup
    rwa [M23Insp.chk_T_len'] at this
  have h3 : 2520 * Nat.card (stabilizer ↥M2bar M23Insp.data.t₀) ≤ 2520 * 16 := by
    calc 2520 * Nat.card (stabilizer ↥M2bar M23Insp.data.t₀)
        ≤ Nat.card (orbit ↥M2bar M23Insp.data.t₀) *
            Nat.card (stabilizer ↥M2bar M23Insp.data.t₀) := Nat.mul_le_mul_right _ horb
      _ = 2520 * 16 := by rw [h2]
  exact h1.trans (Nat.le_of_mul_le_mul_left h3 (by norm_num))

theorem es_mem_M2bar :
    ∀ e ∈ M23Insp.data.Es, e ∈ M2bar := fun e he => stab_of_fix (M23Insp.valid.Es_fix e he)

theorem ker_πbar_eq :
    ((fun x : ↥M2bar => (x : ↥NativeSporadic.M23)) ⁻¹' {e | e ∈ M23Insp.data.Es}) =
      (πbar.ker : Set ↥M2bar) := by
  classical
  have hSsub : ((fun x : ↥M2bar => (x : ↥NativeSporadic.M23)) ⁻¹' {e | e ∈ M23Insp.data.Es}) ⊆
      (πbar.ker : Set ↥M2bar) := fun x hx => mem_ker_πbar.mpr (M23Insp.valid.Es_fix _ hx)
  have hSc : ((fun x : ↥M2bar => (x : ↥NativeSporadic.M23)) ⁻¹'
      {e | e ∈ M23Insp.data.Es}).ncard = 16 := by
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · have e : {e | e ∈ M23Insp.data.Es} =
          ((M23Insp.data.Es.toFinset : Finset ↥NativeSporadic.M23) : Set ↥NativeSporadic.M23) := by
        ext x
        simp
      rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup M23Insp.valid.Es_nodup,
        M23Insp.valid.Es_len]
    · intro e he
      exact ⟨⟨e, es_mem_M2bar e he⟩, rfl⟩
  have hK : (πbar.ker : Set ↥M2bar).ncard ≤ 16 := by
    rw [← Nat.card_coe_set_eq]
    exact card_ker_πbar_le
  exact Set.eq_of_subset_of_ncard_le hSsub (by rw [hSc]; exact hK) (Set.toFinite _)

theorem mem_ker_πbar_iff
    (k : ↥M2bar) : k ∈ πbar.ker ↔ (k : ↥NativeSporadic.M23) ∈ M23Insp.data.Es := by
  have := Set.ext_iff.mp ker_πbar_eq.symm k
  exact this

theorem card_ker_πbar :
    Nat.card πbar.ker = 16 := by
  classical
  have h := congrArg Set.ncard ker_πbar_eq
  rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective] at h
  · have e : {e | e ∈ M23Insp.data.Es} =
        ((M23Insp.data.Es.toFinset : Finset ↥NativeSporadic.M23) : Set ↥NativeSporadic.M23) := by
      ext x
      simp
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup M23Insp.valid.Es_nodup,
      M23Insp.valid.Es_len] at h
    exact (Nat.card_coe_set_eq (πbar.ker : Set ↥M2bar)).trans h.symm
  · intro e he
    exact ⟨⟨e, es_mem_M2bar e he⟩, rfl⟩

theorem range_πbar :
    πbar.range = alternatingGroup (Fin 7) := by
  have hrange : Nat.card πbar.range = 2520 := by
    have h := Subgroup.card_ker_mul_card_range πbar
    rw [card_ker_πbar, card_M2bar] at h
    omega
  have hindex : πbar.range.index = 2 := by
    have h := Subgroup.card_mul_index πbar.range
    have hperm : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [hperm, hrange] at h
    omega
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex

@[expose] def Abar : Subgroup ↥M2bar := stabilizer ↥M2bar (0 : Fin 23)

theorem injOn_Abar
    {k : ↥M2bar} (hk : k ∈ Abar) (h1 : πbar k = 1) : k = 1 := by
  have hker : (k : ↥NativeSporadic.M23) ∈ M23Insp.data.Es := (mem_ker_πbar_iff k).mp h1
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hker
  have hi16 : i < 16 := by rw [← M23Insp.valid.Es_len]; exact hi
  have hget : M23Insp.es.getD i 1 = (k : ↥NativeSporadic.M23) := by
    show M23Insp.data.Es.getD i 1 = _
    rw [List.getD_eq_getElem _ _ hi]
    exact hik
  have h0 : ((M23Insp.es.getD i 1 : ↥NativeSporadic.M23) : Perm (Fin 23)) 0 = 0 := by
    rw [hget]
    exact hk
  have := Certificates.certificate7098.2.2.2.2.2.2.2.2.1 ⟨i, hi16⟩ h0
  change M23Insp.es.getD i 1 = 1 at this
  rw [hget] at this
  exact Subtype.ext this

theorem card_orbit_zero_le :
    Nat.card (orbit ↥M2bar (0 : Fin 23)) ≤ 16 := by
  classical
  have hsub : orbit ↥M2bar (0 : Fin 23) ⊆ ((heptad₀ᶜ : Finset (Fin 23)) : Set (Fin 23)) := by
    rintro _ ⟨k, rfl⟩
    rw [Finset.mem_coe, Finset.mem_compl]
    intro h
    have h0 : (0 : Fin 23) ∉ heptad₀ := by decide
    exact h0 ((stab_mem_iff.1 k.2 0).1 h)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hc : heptad₀.card = 7 := M23Insp.chk_card
  rw [Set.ncard_coe_finset, Finset.card_compl, hc, Fintype.card_fin] at h1
  rw [Nat.card_coe_set_eq]
  exact h1

theorem πbar_mem_alt (k : ↥M2bar) :
    πbar k ∈ alternatingGroup (Fin 7) := by
  rw [← range_πbar]
  exact ⟨k, rfl⟩

@[expose] def πA : ↥Abar →* A7 :=
  (πbar.comp Abar.subtype).codRestrict (alternatingGroup (Fin 7)) fun k => πbar_mem_alt k

theorem πA_injective :
    Function.Injective (πA : ↥Abar →* A7) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  have h1 : πbar (k : ↥M2bar) = 1 := congrArg Subtype.val hk
  exact Subtype.ext (injOn_Abar k.2 h1)

theorem card_Abar :
    Nat.card Abar = 2520 := by
  have hle : Nat.card Abar ≤ 2520 := by
    have := Nat.card_le_card_of_injective _ πA_injective
    rwa [CFSG.QuasithinUnique.L246.C123.card_A7] at this
  have h := card_orbit_mul_card_stabilizer (Γ := ↥M2bar) (0 : Fin 23)
  rw [card_M2bar] at h
  have hb := card_orbit_zero_le
  change Nat.card (orbit ↥M2bar (0 : Fin 23)) * Nat.card Abar = 40320 at h
  nlinarith

@[expose] noncomputable def AbarEquiv :
    ↥Abar ≃* A7 :=
  MulEquiv.ofBijective πA (πA_injective.bijective_of_nat_card_le (by
    rw [card_Abar, CFSG.QuasithinUnique.L246.C123.card_A7]))

@[expose] noncomputable def sbar :
    A7 →* ↥M2bar :=
  Abar.subtype.comp AbarEquiv.symm.toMonoidHom

theorem πbar_sbar
    (σ : A7) : πbar (sbar σ) = σ := by
  have h := AbarEquiv.apply_symm_apply σ
  have h' := congrArg Subtype.val h
  exact h'

abbrev Ubar : Subgroup ↥M2bar := πbar.ker

theorem Ubar_comm
    (a b : ↥Ubar) : a * b = b * a := by
  have ha := (mem_ker_πbar_iff (a : ↥M2bar)).mp a.2
  have hb := (mem_ker_πbar_iff (b : ↥M2bar)).mp b.2
  exact Subtype.ext (Subtype.ext (M23Insp.valid.Es_comm _ ha _ hb))

theorem Ubar_sq (a : ↥Ubar) :
    a * a = 1 := by
  have ha := (mem_ker_πbar_iff (a : ↥M2bar)).mp a.2
  exact Subtype.ext (Subtype.ext (M23Insp.valid.Es_sq _ ha))

@[expose] noncomputable def ρbar :
    A7 →* MulAut ↥Ubar :=
  (MulAut.conjNormal (H := Ubar)).comp sbar

theorem ρbar_apply_of_πbar
    {k : ↥M2bar} {σ : A7} (hk : πbar k = σ) (u : ↥Ubar) :
    ((ρbar σ u : ↥Ubar) : ↥M2bar) = k * u * k⁻¹ := by
  change ((MulAut.conjNormal (sbar σ) u : ↥Ubar) : ↥M2bar) = _
  rw [MulAut.conjNormal_apply]
  have hw : (sbar σ)⁻¹ * k ∈ Ubar := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, πbar_sbar, hk, inv_mul_cancel]
  have hwu : (sbar σ)⁻¹ * k * u = u * ((sbar σ)⁻¹ * k) :=
    congrArg Subtype.val (Ubar_comm ⟨_, hw⟩ u)
  calc sbar σ * u * (sbar σ)⁻¹
      = sbar σ * (((sbar σ)⁻¹ * k) * u * ((sbar σ)⁻¹ * k)⁻¹) * (sbar σ)⁻¹ := by
        rw [hwu, mul_inv_cancel_right]
    _ = k * u * k⁻¹ := by group

theorem evalN_mem_M2bar (w : List ℤ) :
    CFSG.QuasithinUnique.Setup.X1.evalN NativeSporadic.M23 M23Insp.ks w ∈ M2bar := by
  rw [CFSG.QuasithinUnique.Setup.X1.evalN, CFSG.QuasithinUnique.Setup.X1.normH_eq]
  induction w with
  | nil => exact M2bar.one_mem
  | cons z w ih =>
    simp only [CFSG.QuasithinUnique.Setup.X1.evalG]
    have hget : ∀ j, M23Insp.ks.getD j 1 ∈ M2bar := by
      intro j
      by_cases hj : j < M23Insp.ks.length
      · rw [List.getD_eq_getElem _ _ hj]
        exact ks_mem_M2bar _ (List.getElem_mem hj)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact M2bar.one_mem
    split
    · exact M2bar.mul_mem (hget _) ih
    · exact M2bar.mul_mem (M2bar.inv_mem (hget _)) ih

@[expose] noncomputable def ubar0U :
    ↥Ubar :=
  ⟨⟨ubar0, es_mem_M2bar _ (by
      show M23Insp.data.Es.getD 10 1 ∈ M23Insp.data.Es
      rw [List.getD_eq_getElem _ _ (by rw [M23Insp.valid.Es_len]; norm_num)]
      exact List.getElem_mem _)⟩,
    (mem_ker_πbar_iff _).mpr (by
      show M23Insp.data.Es.getD 10 1 ∈ M23Insp.data.Es
      rw [List.getD_eq_getElem _ _ (by rw [M23Insp.valid.Es_len]; norm_num)]
      exact List.getElem_mem _)⟩

theorem ubar0U_ne_one :
    ubar0U ≠ 1 := fun h =>
  Certificates.certificate7098.2.2.2.2.2.2.1 (congrArg (fun x : ↥Ubar =>
    ((x : ↥M2bar) : ↥NativeSporadic.M23)) h)

theorem exists_A7_of_mem
    (k : ↥M2bar) : ∃ σ : A7, πbar k = σ := ⟨⟨πbar k, πbar_mem_alt k⟩, rfl⟩

theorem transitive_ρbar :
    ∀ u : ↥Ubar, u ≠ 1 → ∃ σ : A7, ρbar σ ubar0U = u := by
  intro u hu
  have hker := (mem_ker_πbar_iff (u : ↥M2bar)).mp u.2
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hker
  have hi16 : i < 16 := by rw [← M23Insp.valid.Es_len]; exact hi
  have hget : M23Insp.es.getD i 1 = ((u : ↥M2bar) : ↥NativeSporadic.M23) := by
    show M23Insp.data.Es.getD i 1 = _
    rw [List.getD_eq_getElem _ _ hi]
    exact hiu
  have hne : M23Insp.es.getD i 1 ≠ 1 := by
    rw [hget]
    intro h
    exact hu (Subtype.ext (Subtype.ext h))
  have hc := Certificates.certificate7098.2.2.2.2.2.2.2.1 ⟨i, hi16⟩ hne
  change conjElt i * ubar0 * (conjElt i)⁻¹ = M23Insp.es.getD i 1 at hc
  rw [hget] at hc
  let k : ↥M2bar := ⟨conjElt i, evalN_mem_M2bar _⟩
  obtain ⟨σ, hσ⟩ := exists_A7_of_mem k
  refine ⟨σ, Subtype.ext (Subtype.ext ?_)⟩
  rw [ρbar_apply_of_πbar hσ]
  exact hc

@[expose] def g1A : A7 := ⟨g1perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem vecStab_ρbar :
    vecStab ρbar ubar0U = fanoStab fano1 := by
  have hU : Nat.card ↥Ubar = 16 := card_ker_πbar
  let kc : ↥M2bar := ⟨liftCyc, evalN_mem_M2bar _⟩
  let kd : ↥M2bar := ⟨liftDbl, evalN_mem_M2bar _⟩
  let kg : ↥M2bar := ⟨liftG1, evalN_mem_M2bar _⟩
  have hkc : πbar kc = cyc7A := πbar_eq_iff.mpr Certificates.certificate7098.1
  have hkd : πbar kd = dbl7A := πbar_eq_iff.mpr Certificates.certificate7098.2.1
  have hkg : πbar kg = g1A := πbar_eq_iff.mpr Certificates.certificate7098.2.2.1
  have hfix : ∀ {k : ↥M2bar} {σ : A7}, πbar k = σ →
      (k : ↥NativeSporadic.M23) * ubar0 * (k : ↥NativeSporadic.M23)⁻¹ = ubar0 →
      ρbar σ ubar0U = ubar0U := by
    intro k σ hk h
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val (ρbar_apply_of_πbar hk ubar0U)
    exact this.trans h
  have hc := hfix hkc Certificates.certificate7098.2.2.2.1
  have hd := hfix hkd Certificates.certificate7098.2.2.2.2.1
  have hg := hfix hkg Certificates.certificate7098.2.2.2.2.2.1
  rcases vecStab_eq_fanoStab ρbar hU ubar0U_ne_one hc hd transitive_ρbar with h | h
  · exact h
  · exfalso
    have hmem : g1A ∈ vecStab ρbar ubar0U := hg
    rw [h, mem_fanoStab] at hmem
    exact absurd hmem (by decide)

theorem fixed_Ubar :
    ∀ v w : ↥Ubar, v ≠ 1 → w ≠ 1 → v ≠ w → ∀ x : ↥Ubar, x ≠ 1 →
      (∀ g : A7, ρbar g v = v → ρbar g w = w → ρbar g x = x) → x = v ∨ x = w ∨ x = v * w :=
  mem_of_fixed_of_stab_eq ρbar card_ker_πbar Ubar_sq ubar0U_ne_one transitive_ρbar
    reps1_facts.1 (by decide) reps1_facts.2.1 reps1_facts.2.2
    (fun g => by rw [← mem_vecStab, vecStab_ρbar, mem_fanoStab])

end CFSG.Quasithin.H13
