module

public import CFSG.Quasithin.Background.HMathieuM21
public meta import CFSG.Quasithin.Background.HMathieuCent
public meta import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuO2CertInputs
public import Certificates.Certificate7066

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

@[expose] def commV {V : Type*} [CommGroup V] (Y : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {w | ∃ y ∈ Y, ∃ u : V, w = y u * u⁻¹}

variable {n : ℕ} {V : Type*} [CommGroup V]

theorem mem_zpowers_of_mul_self {G : Type*} [Group G] {p : G} (hp : p * p = 1) (m : G) :
    m ∈ Subgroup.zpowers p ↔ m = 1 ∨ m = p := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : p ^ (2 : ℤ) = 1 := by rw [zpow_two, hp]
    change p ^ k = 1 ∨ p ^ k = p
    rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem MaskCoords.vm_inv (c : MaskCoords V n) (m : ℕ) : (c.vm m)⁻¹ = c.vm m :=
  inv_eq_of_mul_eq_one_right (by rw [← c.vm_xor, Nat.xor_self, c.vm_zero])

theorem MaskCoords.mul_self_eq_one (c : MaskCoords V n) (v : V) : v * v = 1 := by
  obtain ⟨m, -, rfl⟩ := c.vm_surj v
  rw [← c.vm_xor, Nat.xor_self, c.vm_zero]

theorem commV_eq_top_of_masks (c : MaskCoords V n) {X : Subgroup (MulAut V)}
    (actA : Array ℕ → ℕ → ℕ) (C : List (Array ℕ × ℕ))
    (hreal : ∀ p ∈ C, ∃ x ∈ X, x (c.vm p.2) = c.vm (actA p.1 p.2))
    (hspan : ∀ m < 2 ^ n, m ∈ combos (C.map fun p => actA p.1 p.2 ^^^ p.2)) :
    commV X = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨m, hm, rfl⟩ := c.vm_surj v
  refine c.vm_mem_of_combos (commV X) (l := C.map fun p => actA p.1 p.2 ^^^ p.2) ?_ m
    (hspan m hm)
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  obtain ⟨x, hx, hxp⟩ := hreal p hp
  refine Subgroup.subset_closure ⟨x, hx, c.vm p.2, ?_⟩
  rw [c.vm_xor, ← hxp, c.vm_inv]

theorem centralizer_eq_bot_of_masks_fix (c : MaskCoords V n) {X : Subgroup (MulAut V)}
    (actA : Array ℕ → ℕ → ℕ) (H0 H1 S : List (Array ℕ))
    (hreal : ∀ a ∈ H0 ++ H1 ++ S, ∃ x ∈ X, ∀ m < 2 ^ n, x (c.vm m) = c.vm (actA a m))
    (hlt : ∀ a m, actA a m < 2 ^ n) {x0 v1 : ℕ} (hx0 : x0 < 2 ^ n) (hx0ne : x0 ≠ 0)
    (hv1 : v1 < 2 ^ n) (hv1ne : v1 ≠ 0) (hv1x0 : v1 ≠ x0)
    (hX0 : ∀ x ∈ X, x (c.vm x0) = c.vm x0)
    (hfix0 : ∀ m < 2 ^ n, (∀ a ∈ H0, actA a m = m) → m = 0 ∨ m = x0)
    (h1 : ∀ a ∈ H1, actA a v1 = v1 ∨ actA a v1 = v1 ^^^ x0)
    (hfix1 : ∀ m < 2 ^ n, (∀ a ∈ H1, actA a m = m ∨ actA a m = m ^^^ x0) →
      m = 0 ∨ m = x0 ∨ m = v1 ∨ m = v1 ^^^ x0)
    (hspan : ∀ m < 2 ^ n, m ∈ combos (x0 :: S.map fun a => actA a v1))
    (hcomm : commV X = ⊤) :
    Subgroup.centralizer (X : Set (MulAut V)) = ⊥ := by
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_centralizer_iff] at hd
  have hcx : ∀ x ∈ X, ∀ w, x (d w) = d (x w) := fun x hx w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hd x hx]
  have hreal0 : ∀ a ∈ H0, ∃ x ∈ X, ∀ m < 2 ^ n, x (c.vm m) = c.vm (actA a m) :=
    fun a ha => hreal a (List.mem_append_left _ (List.mem_append_left _ ha))
  have hreal1 : ∀ a ∈ H1, ∃ x ∈ X, ∀ m < 2 ^ n, x (c.vm m) = c.vm (actA a m) :=
    fun a ha => hreal a (List.mem_append_left _ (List.mem_append_right _ ha))
  have hrealS : ∀ a ∈ S, ∃ x ∈ X, ∀ m < 2 ^ n, x (c.vm m) = c.vm (actA a m) :=
    fun a ha => hreal a (List.mem_append_right _ ha)
  have hne1 : ∀ m < 2 ^ n, m ≠ 0 → c.vm m ≠ 1 := fun m hm hm0 h =>
    hm0 (c.vm_inj m 0 hm (Nat.two_pow_pos n) (h.trans c.vm_zero.symm))
  have hcz : d (c.vm x0) = c.vm x0 := by
    obtain ⟨m, hm, hmw⟩ := c.vm_surj (d (c.vm x0))
    have hmfix : ∀ a ∈ H0, actA a m = m := by
      intro a ha
      obtain ⟨x, hx, hxa⟩ := hreal0 a ha
      have e1 : x (d (c.vm x0)) = d (c.vm x0) := by rw [hcx x hx, hX0 x hx]
      rw [← hmw, hxa m hm] at e1
      exact c.vm_inj _ _ (hlt a m) hm e1
    rcases hfix0 m hm hmfix with rfl | rfl
    · exfalso
      rw [c.vm_zero] at hmw
      exact hne1 x0 hx0 hx0ne ((map_eq_one_iff d d.injective).1 hmw.symm)
    · exact hmw.symm
  have hcv : d (c.vm v1) = c.vm v1 ∨ d (c.vm v1) = c.vm v1 * c.vm x0 := by
    obtain ⟨m, hm, hmw⟩ := c.vm_surj (d (c.vm v1))
    have hmfix : ∀ a ∈ H1, actA a m = m ∨ actA a m = m ^^^ x0 := by
      intro a ha
      obtain ⟨x, hx, hxa⟩ := hreal1 a ha
      have e1 : x (d (c.vm v1)) = d (x (c.vm v1)) := hcx x hx _
      rw [hxa v1 hv1] at e1
      rcases h1 a ha with h | h
      · rw [h, ← hmw, hxa m hm] at e1
        exact Or.inl (c.vm_inj _ _ (hlt a m) hm e1)
      · rw [h, c.vm_xor, map_mul, hcz, ← hmw, hxa m hm, ← c.vm_xor] at e1
        exact Or.inr (c.vm_inj _ _ (hlt a m) (Nat.xor_lt_two_pow hm hx0) e1)
    rcases hfix1 m hm hmfix with rfl | rfl | rfl | rfl
    · exfalso
      rw [c.vm_zero] at hmw
      exact hne1 v1 hv1 hv1ne ((map_eq_one_iff d d.injective).1 hmw.symm)
    · exfalso
      rw [← hcz] at hmw
      exact hv1x0 (c.vm_inj _ _ hv1 hx0 (d.injective hmw.symm))
    · exact Or.inl hmw.symm
    · right
      rw [← hmw, c.vm_xor]
  let δ : V →* V :=
    { toFun := fun w => d w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hδ : ∀ w, δ w = d w * w⁻¹ := fun _ => rfl
  have hzz : c.vm x0 * c.vm x0 = 1 := c.mul_self_eq_one _
  let D : Subgroup V := (Subgroup.zpowers (c.vm x0)).comap δ
  have hD : D = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨m, hm, rfl⟩ := c.vm_surj v
    refine c.vm_mem_of_combos D (l := x0 :: S.map fun a => actA a v1) ?_ m (hspan m hm)
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · change δ (c.vm a) ∈ Subgroup.zpowers (c.vm a)
      rw [hδ, hcz, mul_inv_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      obtain ⟨x, hx, hxb⟩ := hrealS b hb
      change δ (c.vm (actA b v1)) ∈ Subgroup.zpowers (c.vm x0)
      rw [← hxb v1 hv1, hδ, ← hcx x hx, ← map_inv, ← map_mul]
      rcases hcv with h | h
      · rw [h, mul_inv_cancel, map_one]
        exact Subgroup.one_mem _
      · rw [h, mul_right_comm, mul_inv_cancel, one_mul, hX0 x hx]
        exact Subgroup.mem_zpowers _
  have hδz : ∀ w, δ w = 1 ∨ δ w = c.vm x0 := fun w =>
    (mem_zpowers_of_mul_self hzz (δ w)).1 (show w ∈ D by rw [hD]; exact Subgroup.mem_top w)
  have hker : commV X ≤ δ.ker := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨y, hy, u, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hδ (y u), ← hcx y hy, ← map_inv,
      ← map_mul, ← hδ]
    rcases hδz u with h | h
    · rw [h, map_one, one_mul, inv_one]
    · rw [h, hX0 y hy, mul_inv_cancel]
  rw [hcomm] at hker
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun w => ?_
  have h := hker (Subgroup.mem_top w)
  rw [MonoidHom.mem_ker, hδ, mul_inv_eq_one] at h
  exact h

@[expose] noncomputable def img10 (Γ : Subgroup (Equiv.Perm (Fin 24))) : Subgroup (MulAut W10) :=
  (Γ.subgroupOf mog22plus).map (rho10 mog22plus le_rfl)

@[expose] noncomputable def img11 (Γ : Subgroup (Equiv.Perm (Fin 24))) : Subgroup (MulAut W11) :=
  (Γ.subgroupOf AutPerm).map (rho11 AutPerm le_rfl)

theorem range_rho10_eq_img10 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) :
    (rho10 Γ hΓ).range = img10 Γ := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨⟨σ, hΓ σ.2⟩, by simp [Subgroup.mem_subgroupOf], MulEquiv.ext fun w => rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, (Subgroup.mem_subgroupOf).1 hσ⟩, MulEquiv.ext fun w => rfl⟩

theorem range_rho11_eq_img11 (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) :
    (rho11 Γ hΓ).range = img11 Γ := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨⟨σ, hΓ σ.2⟩, by simp [Subgroup.mem_subgroupOf], MulEquiv.ext fun w => rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, (Subgroup.mem_subgroupOf).1 hσ⟩, MulEquiv.ext fun w => rfl⟩

theorem exists_img10_mog21 {a : Array ℕ} (h : inAutOK a = true) (h0 : a[0]! = 0)
    (h1 : a[1]! = 1) (h2 : a[2]! = 2) :
    ∃ x ∈ img10 mog21, ∀ m, x (toW 10 m) = toW 10 (act10 a m) := by
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK h
  have hσ21 : σ ∈ mog21 := mem_mog21_of_hasArr hσa h h0 h1 h2
  refine ⟨rho10 mog22plus le_rfl ⟨σ, mog21_le_mog22plus hσ21⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hσ21), fun m => ?_⟩
  exact rho10_toW mog22plus le_rfl ⟨σ, _⟩ hσa m

theorem exists_img11_mog22 {a : Array ℕ} (h : inAutOK a = true) (h0 : a[0]! = 0)
    (h1 : a[1]! = 1) :
    ∃ x ∈ img11 mog22, ∀ m, x (toW 11 m) = toW 11 (act11 a m) := by
  obtain ⟨σ, hσ, hσa⟩ := exists_of_inAutOK h
  have hσ22 : σ ∈ mog22 := mem_mog22_of_arr hσ hσa h0 h1
  refine ⟨rho11 AutPerm le_rfl ⟨σ, hσ⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hσ22), fun m => ?_⟩
  exact rho11_toW AutPerm le_rfl ⟨σ, _⟩ hσa m

theorem o2cert10_mem :
    ∀ a ∈ o2H0_10 ++ o2H1_10 ++ o2S_10 ++ o2C_10.map Prod.fst,
    inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1 ∧ a[2]! = 2 :=
  Certificates.certificate7066.1

theorem o2cert10_fix0 :
    ∀ m < 2 ^ 10, (∀ a ∈ o2H0_10, act10 a m = m) → m = 0 ∨ m = 48 :=
  Certificates.certificate7066.2.1

theorem o2cert10_h1 :
    ∀ a ∈ o2H1_10, act10 a 16 = 16 ∨ act10 a 16 = 16 ^^^ 48 :=
  Certificates.certificate7066.2.2.1

theorem o2cert10_fix1 :
    ∀ m < 2 ^ 10, (∀ a ∈ o2H1_10, act10 a m = m ∨ act10 a m = m ^^^ 48) →
    m = 0 ∨ m = 48 ∨ m = 16 ∨ m = 16 ^^^ 48 :=
  Certificates.certificate7066.2.2.2.1

theorem o2cert10_span :
    ∀ m < 2 ^ 10, m ∈ combos (48 :: o2S_10.map fun a => act10 a 16) :=
  Certificates.certificate7066.2.2.2.2.1

theorem o2cert10_comm :
    ∀ m < 2 ^ 10, m ∈ combos (o2C_10.map fun p => act10 p.1 p.2 ^^^ p.2) :=
  Certificates.certificate7066.2.2.2.2.2.1

theorem pairMask_cc10_zero_two :
    actM cc10Cols (pairMask 0 ((2 : Fin 24) : ℕ)) = 48 :=
  Certificates.certificate7066.2.2.2.2.2.2.1

theorem o2cert11_mem :
    ∀ a ∈ o2H0_11 ++ o2H1_11 ++ o2S_11 ++ o2C_11.map Prod.fst,
    inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1 :=
  Certificates.certificate7066.2.2.2.2.2.2.2.1

theorem o2cert11_fix0 :
    ∀ m < 2 ^ 11, (∀ a ∈ o2H0_11, act11 a m = m) → m = 0 ∨ m = 95 :=
  Certificates.certificate7066.2.2.2.2.2.2.2.2.1

theorem o2cert11_h1 :
    ∀ a ∈ o2H1_11, act11 a 63 = 63 ∨ act11 a 63 = 63 ^^^ 95 :=
  Certificates.certificate7066.2.2.2.2.2.2.2.2.2.1

theorem o2cert11_fix1 :
    ∀ m < 2 ^ 11, (∀ a ∈ o2H1_11, act11 a m = m ∨ act11 a m = m ^^^ 95) →
    m = 0 ∨ m = 95 ∨ m = 63 ∨ m = 63 ^^^ 95 :=
  Certificates.certificate7066.2.2.2.2.2.2.2.2.2.2.1

theorem o2cert11_span :
    ∀ m < 2 ^ 11, m ∈ combos (95 :: o2S_11.map fun a => act11 a 63) :=
  Certificates.certificate7066.2.2.2.2.2.2.2.2.2.2.2.1

theorem o2cert11_comm :
    ∀ m < 2 ^ 11, m ∈ combos (o2C_11.map fun p => act11 p.1 p.2 ^^^ p.2) :=
  Certificates.certificate7066.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pairImg11_zero_one :
    pairImg11 ((0 : Fin 24) : ℕ) ((1 : Fin 24) : ℕ) = 95 :=
  Certificates.certificate7066.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem kappa22_pairVec_zero_two :
    cocode22Coords.κ (pairVec 0 2) = toW 10 48 := by
  rw [cc10_pairVec_mask 2 (by decide), pairMask_cc10_zero_two]

theorem img10_mog21_fix :
    ∀ x ∈ img10 mog21, x (toW 10 48) = toW 10 48 := by
  rintro _ ⟨σ, hσ, rfl⟩
  rw [← kappa22_pairVec_zero_two, rho10_pairVec,
    (mem_stab_iff 2 _).1 (Subgroup.mem_subgroupOf.1 hσ).2]

theorem commV_img10_mog21 : commV (img10 mog21) = ⊤ := by
  refine commV_eq_top_of_masks (MaskCoords.std 10) act10 o2C_10 (fun p hp => ?_) o2cert10_comm
  have hmem := o2cert10_mem p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  obtain ⟨x, hx, hxa⟩ := exists_img10_mog21 hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
  exact ⟨x, hx, hxa p.2⟩

theorem centralizer_img10_mog21 :
    Subgroup.centralizer (img10 mog21 : Set (MulAut W10)) = ⊥ := by
  refine centralizer_eq_bot_of_masks_fix (MaskCoords.std 10) act10 o2H0_10 o2H1_10 o2S_10
    (fun a ha => ?_)
    act10_lt (x0 := 48) (v1 := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) img10_mog21_fix o2cert10_fix0 o2cert10_h1 o2cert10_fix1 o2cert10_span
    commV_img10_mog21
  have hmem := o2cert10_mem a (List.mem_append_left _ ha)
  obtain ⟨x, hx, hxa⟩ := exists_img10_mog21 hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
  exact ⟨x, hx, fun m _ => hxa m⟩

theorem kappa11_pairVec_zero_one :
    cocodeCoords.κ (pairVec 0 1) = toW 11 95 := by
  rw [kappa11_pairVec_mask 0 1 (by decide), pairImg11_zero_one]

theorem img11_mog22_fix :
    ∀ x ∈ img11 mog22, x (toW 11 95) = toW 11 95 := by
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' := Subgroup.mem_subgroupOf.1 hσ
  rw [← kappa11_pairVec_zero_one, rho11_pairVec, (mem_stab_iff 0 _).1 hσ'.1.2,
    (mem_stab_iff 1 _).1 hσ'.2]

theorem commV_img11_mog22 : commV (img11 mog22) = ⊤ := by
  refine commV_eq_top_of_masks (MaskCoords.std 11) act11 o2C_11 (fun p hp => ?_) o2cert11_comm
  have hmem := o2cert11_mem p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  obtain ⟨x, hx, hxa⟩ := exists_img11_mog22 hmem.1 hmem.2.1 hmem.2.2
  exact ⟨x, hx, hxa p.2⟩

theorem centralizer_img11_mog22 :
    Subgroup.centralizer (img11 mog22 : Set (MulAut W11)) = ⊥ := by
  refine centralizer_eq_bot_of_masks_fix (MaskCoords.std 11) act11 o2H0_11 o2H1_11 o2S_11
    (fun a ha => ?_)
    act11_lt (x0 := 95) (v1 := 63) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) img11_mog22_fix o2cert11_fix0 o2cert11_h1 o2cert11_fix1 o2cert11_span
    commV_img11_mog22
  have hmem := o2cert11_mem a (List.mem_append_left _ ha)
  obtain ⟨x, hx, hxa⟩ := exists_img11_mog22 hmem.1 hmem.2.1 hmem.2.2
  exact ⟨x, hx, fun m _ => hxa m⟩

end CFSG.Quasithin.H.Mathieu
