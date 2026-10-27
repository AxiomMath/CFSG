module

public import CFSG.Quasithin.Background.HMathieuMask
public meta import CFSG.Quasithin.Background.HMathieuMask
public meta import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuCentInputs
public import Certificates.Certificate7060

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective

theorem normalizer_eq_of_card {G : Type*} [Group G] [Finite G] {R R' : Subgroup G}
    (hC : Subgroup.centralizer (R : Set G) = ⊥) (hle : R' ≤ Subgroup.normalizer (R : Set G))
    (hcard : Nat.card (MulAut R) ≤ Nat.card R') : Subgroup.normalizer (R : Set G) = R' := by
  set N := Subgroup.normalizer (R : Set G) with hN
  have : (R.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have := finite_mulAut ↥(R.subgroupOf N)
  let f : ↥N →* MulAut ↥(R.subgroupOf N) := MulAut.conjNormal
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hc : (n : G) ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hrN : r ∈ N := Subgroup.le_normalizer hr
      have h1 := congrArg (fun φ : MulAut ↥(R.subgroupOf N) =>
        ((φ ⟨⟨r, hrN⟩, hr⟩ : ↥(R.subgroupOf N)) : ↥N)) hn
      simp only [MulAut.one_apply] at h1
      change ((MulAut.conjNormal n ⟨⟨r, hrN⟩, hr⟩ : ↥(R.subgroupOf N)) : ↥N) = ⟨r, hrN⟩ at h1
      rw [MulAut.conjNormal_apply] at h1
      have h3 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      calc r * (n : G) = (n : G) * r * (n : G)⁻¹ * (n : G) := by rw [h3]
        _ = (n : G) * r := by group
    rw [hC, Subgroup.mem_bot] at hc
    exact Subtype.ext hc
  have h1 : Nat.card N ≤ Nat.card (MulAut ↥(R.subgroupOf N)) := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (MulAut ↥(R.subgroupOf N)) = Nat.card (MulAut R) :=
    Nat.card_congr (MulAut.congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer)).toEquiv
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem centralizer_eq_bot_of_masks {n : ℕ} {X : Subgroup (MulAut (Wn n))}
    (actA : Array ℕ → ℕ → ℕ) (H0 S : List (Array ℕ))
    (hreal : ∀ a ∈ H0 ++ S, ∃ x ∈ X, ∀ m < 2 ^ n, x (toW n m) = toW n (actA a m))
    (hlt : ∀ a m, actA a m < 2 ^ n) {v0 : ℕ} (hv0 : v0 < 2 ^ n) (hv0ne : v0 ≠ 0)
    (hfix0 : ∀ a ∈ H0, actA a v0 = v0)
    (hfix : ∀ m < 2 ^ n, (∀ a ∈ H0, actA a m = m) → m = 0 ∨ m = v0)
    (hspan : ∀ m < 2 ^ n, m ∈ combos (S.map fun a => actA a v0)) :
    Subgroup.centralizer (X : Set (MulAut (Wn n))) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc
  have hcv0 : c (toW n v0) = toW n v0 := by
    obtain ⟨m, hm, hmw⟩ := toW_surj n (c (toW n v0))
    have hmfix : ∀ a ∈ H0, actA a m = m := by
      intro a ha
      obtain ⟨x, hx, hxa⟩ := hreal a (List.mem_append_left S ha)
      have h1 : x (c (toW n v0)) = c (x (toW n v0)) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, hc x hx]
      rw [hxa v0 hv0, hfix0 a ha, ← hmw, hxa m hm] at h1
      exact toW_inj (hlt a m) hm h1
    rcases hfix m hm hmfix with rfl | rfl
    · exfalso
      rw [toW_zero] at hmw
      have : toW n v0 = 1 := by
        have := congrArg c.symm hmw
        simpa using this.symm
      exact hv0ne (toW_inj hv0 (Nat.two_pow_pos n) (this.trans (toW_zero n).symm))
    · exact hmw.symm
  let U : Subgroup (Wn n) :=
    { carrier := {w | c w = w}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := map_one c
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha]
        rfl }
  have hS : ∀ v ∈ S.map fun a => actA a v0, (MaskCoords.std n).vm v ∈ U := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    obtain ⟨x, hx, hxa⟩ := hreal a (List.mem_append_right H0 ha)
    change c (toW n (actA a v0)) = toW n (actA a v0)
    rw [← hxa v0 hv0, ← MulAut.mul_apply, ← hc x hx, MulAut.mul_apply, hcv0]
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj n w
  rw [MulAut.one_apply]
  exact (MaskCoords.std n).vm_mem_of_combos U hS m (hspan m hm)

theorem exists_of_inAutOK {a : Array ℕ} (h : inAutOK a = true) :
    ∃ σ : Equiv.Perm (Fin 24), σ ∈ AutPerm ∧ HasArr σ a := by
  simp only [inAutOK, Bool.and_eq_true] at h
  exact ⟨permOfArr 24 a (invArr a) h.1, mem_AutPerm_of_arr h.1 h.2, hasArr_permOfArr h.1⟩

theorem HasArr.apply_eq {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (h : HasArr σ a) (i : Fin 24)
    {j : Fin 24} (hj : a[(i : ℕ)]! = j) : σ i = j :=
  Fin.ext ((h i).trans hj)

theorem cert22_mem :
    ∀ a ∈ cent22H ++ cent22S, inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1 :=
  Certificates.certificate7060.1

theorem cert22_fix0 : ∀ a ∈ cent22H, act10 a 48 = 48 :=
  Certificates.certificate7060.2.1

theorem cert22_fix :
    ∀ m < 1024, (∀ a ∈ cent22H, act10 a m = m) → m = 0 ∨ m = 48 :=
  Certificates.certificate7060.2.2.1

theorem cert22_span :
    ∀ m < 1024, m ∈ combos (cent22S.map fun a => act10 a 48) :=
  Certificates.certificate7060.2.2.2.1

theorem o2Masks22_nodup : o2Masks22.Nodup :=
  Certificates.certificate7060.2.2.2.2.1

theorem swap01_syndM :
    ∃ i < 12, syndM (permM swap01Arr (Bmask i)) ≠ 0 :=
  Certificates.certificate7060.2.2.2.2.2.1

theorem mem_mog22_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : σ ∈ AutPerm)
    (ha : HasArr σ a) (h0 : a[0]! = 0) (h1 : a[1]! = 1) : σ ∈ mog22 :=
  ⟨⟨hσ, (mem_stab_iff 0 σ).2 (ha.apply_eq 0 h0)⟩, (mem_stab_iff 1 σ).2 (ha.apply_eq 1 h1)⟩

theorem centralizer_rho10_mog22 :
    Subgroup.centralizer ((rho10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) = ⊥ := by
  refine centralizer_eq_bot_of_masks (n := 10) act10 cent22H cent22S (fun a ha => ?_)
    act10_lt (v0 := 48) (by norm_num) (by norm_num) cert22_fix0 cert22_fix cert22_span
  obtain ⟨hok, ha0, ha1⟩ := cert22_mem a ha
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK hok
  refine ⟨rho10 mog22 mog22_le_mog22plus ⟨σ, mem_mog22_of_arr hσ hσa ha0 ha1⟩,
    ⟨_, rfl⟩, fun m _ => ?_⟩
  exact rho10_toW mog22 mog22_le_mog22plus ⟨σ, _⟩ hσa m

theorem cc10_pairVec_mask (j : Fin 24) (hj : j ≠ 0) :
    cocode22Coords.κ (pairVec 0 j) = toW 10 (actM cc10Cols (pairMask 0 j)) := by
  change Multiplicative.ofAdd (cc10 (Multiplicative.toAdd (pairVec 0 j))) = _
  rw [toAdd_pairVec 0 j hj.symm, cc10_bvec]
  rfl

theorem unitVec_sq (x : Fin 24) : unitVec x * unitVec x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem kappa22_pairVec_zero_one : cocode22Coords.κ (pairVec 0 1) = 1 :=
  (cocode22Coords.ker_iff _ (pairVec_mem_coreMod 0 1)).2
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem rho10_pairVec (σ : ↥mog22plus) (j : Fin 24) :
    rho10 mog22plus le_rfl σ (cocode22Coords.κ (pairVec 0 j)) =
      cocode22Coords.κ (pairVec 0 ((σ : Equiv.Perm (Fin 24)) j)) := by
  have h := SecCoords.κ_permAct_rho cocode22Coords mog22plus
    (fun _ hσ => preserves_cocode22 hσ) σ (pairVec_mem_coreMod 0 j)
  rw [permAct_pairVec] at h
  refine h.symm.trans ?_
  rcases σ.2.2 with ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [h0]
  · rw [h0]
    have : pairVec 1 ((σ : Equiv.Perm (Fin 24)) j) =
        pairVec 0 1 * pairVec 0 ((σ : Equiv.Perm (Fin 24)) j) := by
      simp only [pairVec]
      rw [mul_comm (unitVec 0) (unitVec 1), mul_assoc, ← mul_assoc (unitVec 0) (unitVec 0)]
      rw [unitVec_sq, one_mul]
    rw [this, map_mul, kappa22_pairVec_zero_one, one_mul]

theorem kappa22_pairVec_inj {j k : Fin 24} (hj0 : j ≠ 0)
    (hj1 : j ≠ 1) (hk0 : k ≠ 0)
    (hk1 : k ≠ 1) (h : cocode22Coords.κ (pairVec 0 j) = cocode22Coords.κ (pairVec 0 k)) :
    j = k := by
  rw [cc10_pairVec_mask j hj0, cc10_pairVec_mask k hk0] at h
  have h' := toW_inj (actM_lt cc10Cols_lt _) (actM_lt cc10Cols_lt _) h
  have hj2 : 2 ≤ (j : ℕ) := by
    by_contra hc
    interval_cases hjv : (j : ℕ)
    · exact hj0 (Fin.ext hjv)
    · exact hj1 (Fin.ext hjv)
  have hk2 : 2 ≤ (k : ℕ) := by
    by_contra hc
    interval_cases hkv : (k : ℕ)
    · exact hk0 (Fin.ext hkv)
    · exact hk1 (Fin.ext hkv)
  refine Fin.ext (List.inj_on_of_nodup_map o2Masks22_nodup ?_ ?_ h')
  · simp [List.mem_filter, j.2, hj2]
  · simp [List.mem_filter, k.2, hk2]

theorem swap_not_mem_autPerm {σ : Equiv.Perm (Fin 24)}
    (hσ : HasArr σ swap01Arr) :
    σ ∉ AutPerm := by
  intro hmem
  obtain ⟨i, hi, hne⟩ := swap01_syndM
  apply hne
  have h1 := permWord_mem_of_mem_AutPerm hmem (B_mem_C ⟨i, hi⟩)
  rw [B_eq_bvec, permWord_bvec hσ, bvec_mem_C_iff] at h1
  exact h1

theorem swap01Arr_spec : ∀ i : Fin 24, i ≠ 0 → i ≠ 1 → swap01Arr[(i : ℕ)]! = i := by decide

theorem rho10_mog22plus_injective :
    Function.Injective (rho10 mog22plus le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hpair : ∀ i : Fin 24, i ≠ 0 → i ≠ 1 →
      (σ : Equiv.Perm (Fin 24)) i ≠ 0 ∧ (σ : Equiv.Perm (Fin 24)) i ≠ 1 := by
    intro i hi0 hi1
    have hinj := (σ : Equiv.Perm (Fin 24)).injective
    rcases σ.2.2 with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · exact ⟨fun h => hi0 (hinj (h.trans e0.symm)), fun h => hi1 (hinj (h.trans e1.symm))⟩
    · exact ⟨fun h => hi1 (hinj (h.trans e1.symm)), fun h => hi0 (hinj (h.trans e0.symm))⟩
  have hfix : ∀ j : Fin 24, j ≠ 0 → j ≠ 1 → (σ : Equiv.Perm (Fin 24)) j = j := by
    intro j hj0 hj1
    have h := rho10_pairVec σ j
    rw [hσ, MulAut.one_apply] at h
    exact (kappa22_pairVec_inj hj0 hj1 (hpair j hj0 hj1).1 (hpair j hj0 hj1).2 h).symm
  rcases σ.2.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · apply Subtype.ext
    refine Equiv.ext fun i => ?_
    rw [Subgroup.coe_one, Equiv.Perm.one_apply]
    by_cases hi0 : i = 0
    · rw [hi0, h0]
    by_cases hi1 : i = 1
    · rw [hi1, h1]
    exact hfix i hi0 hi1
  · exfalso
    refine swap_not_mem_autPerm (σ := (σ : Equiv.Perm (Fin 24))) (fun i => ?_) σ.2.1
    by_cases hi0 : i = 0
    · rw [hi0, h0]
      rfl
    by_cases hi1 : i = 1
    · rw [hi1, h1]
      rfl
    rw [hfix i hi0 hi1, swap01Arr_spec i hi0 hi1]

theorem cert11_mem :
    ∀ a ∈ cent11H ++ cent11S, inAutOK a = true ∧ a[0]! = 0 :=
  Certificates.certificate7060.2.2.2.2.2.2.1

theorem cert11_fix0 : ∀ a ∈ cent11H, act11 a 95 = 95 :=
  Certificates.certificate7060.2.2.2.2.2.2.2.1

theorem cert11_fix :
    ∀ m < 2048, (∀ a ∈ cent11H, act11 a m = m) → m = 0 ∨ m = 95 :=
  Certificates.certificate7060.2.2.2.2.2.2.2.2.1

theorem cert11_span :
    ∀ m < 2048, m ∈ combos (cent11S.map fun a => act11 a 95) :=
  Certificates.certificate7060.2.2.2.2.2.2.2.2.2.1

theorem mem_mog23_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : σ ∈ AutPerm)
    (ha : HasArr σ a) (h0 : a[0]! = 0) : σ ∈ mog23 :=
  ⟨hσ, (mem_stab_iff 0 σ).2 (ha.apply_eq 0 h0)⟩

theorem centralizer_rho11_mog23 :
    Subgroup.centralizer ((rho11 mog23 inf_le_left).range : Set (MulAut W11)) = ⊥ := by
  refine centralizer_eq_bot_of_masks (n := 11) act11 cent11H cent11S (fun a ha => ?_)
    act11_lt (v0 := 95) (by norm_num) (by norm_num) cert11_fix0 cert11_fix cert11_span
  obtain ⟨hok, ha0⟩ := cert11_mem a ha
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK hok
  exact ⟨rho11 mog23 inf_le_left ⟨σ, mem_mog23_of_arr hσ hσa ha0⟩, ⟨_, rfl⟩,
    fun m _ => rho11_toW mog23 inf_le_left ⟨σ, _⟩ hσa m⟩

theorem centralizer_rho11_autPerm :
    Subgroup.centralizer ((rho11 AutPerm le_rfl).range : Set (MulAut W11)) = ⊥ := by
  refine centralizer_eq_bot_of_masks (n := 11) act11 cent11H cent11S (fun a ha => ?_)
    act11_lt (v0 := 95) (by norm_num) (by norm_num) cert11_fix0 cert11_fix cert11_span
  obtain ⟨hok, -⟩ := cert11_mem a ha
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK hok
  exact ⟨rho11 AutPerm le_rfl ⟨σ, hσ⟩, ⟨_, rfl⟩, fun m _ => rho11_toW AutPerm le_rfl ⟨σ, _⟩ hσa m⟩

theorem pairImg11_inj : ∀ i j k l : Fin 24, i ≠ j → k ≠ l →
    pairImg11 i j = pairImg11 k l → (i = k ∧ j = l) ∨ (i = l ∧ j = k) :=
  Certificates.certificate7060.2.2.2.2.2.2.2.2.2.2

theorem kappa11_pairVec_mask (i j : Fin 24) (hij : i ≠ j) :
    cocodeCoords.κ (pairVec i j) = toW 11 (pairImg11 i j) := by
  change Multiplicative.ofAdd (ccE (Multiplicative.toAdd (pairVec i j))) = _
  rw [toAdd_pairVec i j hij, ccE_bvec]
  rfl

theorem rho11_pairVec (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) (σ : ↥Γ)
    (i j : Fin 24) :
    rho11 Γ hΓ σ (cocodeCoords.κ (pairVec i j)) =
      cocodeCoords.κ (pairVec ((σ : Equiv.Perm (Fin 24)) i) ((σ : Equiv.Perm (Fin 24)) j)) := by
  have h := SecCoords.κ_permAct_rho cocodeCoords Γ (fun _ hσ => preserves_cocode (hΓ hσ)) σ
    (pairVec_mem_coreMod i j)
  rw [permAct_pairVec] at h
  exact h.symm

theorem kappa11_pairVec_inj {i j k l : Fin 24} (hij : i ≠ j)
    (hkl : k ≠ l)
    (h : cocodeCoords.κ (pairVec i j) = cocodeCoords.κ (pairVec k l)) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  rw [kappa11_pairVec_mask i j hij, kappa11_pairVec_mask k l hkl] at h
  exact pairImg11_inj i j k l hij hkl (toW_inj (actM_lt ccECols_lt _) (actM_lt ccECols_lt _) h)

theorem rho11_injective (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : Γ ≤ AutPerm) :
    Function.Injective (rho11 Γ hΓ) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hpair : ∀ i j : Fin 24, i ≠ j →
      ((σ : Equiv.Perm (Fin 24)) i = i ∧ (σ : Equiv.Perm (Fin 24)) j = j) ∨
        ((σ : Equiv.Perm (Fin 24)) i = j ∧ (σ : Equiv.Perm (Fin 24)) j = i) := by
    intro i j hij
    have h := rho11_pairVec Γ hΓ σ i j
    rw [hσ, MulAut.one_apply] at h
    exact kappa11_pairVec_inj ((σ : Equiv.Perm (Fin 24)).injective.ne hij) hij h.symm
  apply Subtype.ext
  refine Equiv.ext fun i => ?_
  rw [Subgroup.coe_one, Equiv.Perm.one_apply]
  obtain ⟨j, hj⟩ : ∃ j : Fin 24, j ≠ i := ⟨i + 1, by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_add] at this
    omega⟩
  obtain ⟨k, hk, hkj⟩ : ∃ k : Fin 24, k ≠ i ∧ k ≠ j := by
    by_contra hc
    push Not at hc
    have h1 := hc (i + 2)
    have h2 := hc (i + 3)
    have e1 : i + 2 ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_add] at this
      omega
    have e2 : i + 3 ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_add] at this
      omega
    have e3 : i + 2 ≠ i + 3 := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_add] at this
      omega
    exact e3 ((h1 e1).trans (h2 e2).symm)
  rcases hpair i j (Ne.symm hj) with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  rcases hpair i k (Ne.symm hk) with ⟨h3, -⟩ | ⟨h3, -⟩
  · exact h3
  · exact absurd (h1.symm.trans h3) (Ne.symm hkj)

end CFSG.Quasithin.H.Mathieu
