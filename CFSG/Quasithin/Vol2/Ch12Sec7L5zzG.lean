module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzF
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10B

public section

namespace CFSG.Quasithin.H13.S127

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped Pointwise

section Count

variable {G : Type} [Group G]

@[reducible] def conjAH (H : Subgroup G) : MulAction ↥H G :=
  MulAction.compHom G ((MulAut.conj).comp H.subtype)

@[reducible] def conjAHS (H : Subgroup G) : MulAction ↥H (Subgroup G) :=
  MulAction.compHom (Subgroup G) ((MulAut.conj).comp H.subtype)

theorem ncard_conj_orbit (H : Subgroup G) (x : G) :
    {y : G | ∃ h ∈ H, y = h * x * h⁻¹}.ncard =
      ((Subgroup.centralizer ({x} : Set G)).subgroupOf H).index := by
  let _ := conjAH H
  have hsm : ∀ (h : ↥H) (y : G), h • y = (h : G) * y * (h : G)⁻¹ := fun h y => by
    rw [MulAction.compHom_smul_def, MulAut.smul_def, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulAut.conj_apply]
  have e : {y : G | ∃ h ∈ H, y = h * x * h⁻¹} = MulAction.orbit ↥H x := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsm _ _⟩
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨h, hh, hsm _ _⟩
  have hs : MulAction.stabilizer ↥H x = (Subgroup.centralizer ({x} : Set G)).subgroupOf H := by
    ext ⟨h, hh⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, hsm]
    show h * x * h⁻¹ = x ↔ h * x = x * h
    constructor
    · intro e1
      calc h * x = h * x * h⁻¹ * h := by group
        _ = x * h := by rw [e1]
    · intro e1
      rw [e1, mul_inv_cancel_right]
  rw [e, ← MulAction.index_stabilizer, hs]

theorem ncard_conj_orbit_sub [Finite G] (H W : Subgroup G) :
    {Y : Subgroup G | ∃ h ∈ H, Y = W.map (MulAut.conj h).toMonoidHom}.ncard =
      ((Subgroup.normalizer (W : Set G)).subgroupOf H).index := by
  let _ := conjAHS H
  have hsm : ∀ (h : ↥H) (Y : Subgroup G), h • Y = Y.map (MulAut.conj (h : G)).toMonoidHom :=
    fun h Y => by
      rw [MulAction.compHom_smul_def, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.pointwise_smul_def]
      rfl
  have e : {Y : Subgroup G | ∃ h ∈ H, Y = W.map (MulAut.conj h).toMonoidHom} =
      MulAction.orbit ↥H W := by
    ext Y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsm _ _⟩
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨h, hh, hsm _ _⟩
  have hs : MulAction.stabilizer ↥H W = (Subgroup.normalizer (W : Set G)).subgroupOf H := by
    ext ⟨h, hh⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsm]
    show W.map (MulAut.conj h).toMonoidHom = W ↔ h ∈ Subgroup.normalizer (W : Set G)
    constructor
    · intro e1
      refine Subgroup.mem_normalizer_fintype fun w hw => ?_
      have : (MulAut.conj h).toMonoidHom w ∈ W.map (MulAut.conj h).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hw
      rw [e1] at this
      simpa using this
    · intro hN
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨w, hw, rfl⟩
        simpa using (Subgroup.mem_normalizer_iff.mp hN w).mp hw
      · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
  rw [e, ← MulAction.index_stabilizer, hs]

theorem card_sup_zpowers_le [Finite G] {X : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (X : Set G)) (hw2 : w * w = 1) :
    Nat.card ↥(X ⊔ Subgroup.zpowers w) ≤ 2 * Nat.card X := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hconj : ∀ x ∈ X, w * x * w⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.mp hw x).mp hx
  have hconj' : ∀ x ∈ X, w⁻¹ * x * w ∈ X := fun x hx => by
    have := hconj x hx
    rw [hwi] at this ⊢
    exact this
  let S : Subgroup G :=
    { carrier := {x | x ∈ X ∨ w⁻¹ * x ∈ X}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (X.mul_mem ha hb)
        · right
          have e : w⁻¹ * (a * b) = (w⁻¹ * a * w) * (w⁻¹ * b) := by group
          rw [e]
          exact X.mul_mem (hconj' a ha) hb
        · right
          have e : w⁻¹ * (a * b) = (w⁻¹ * a) * b := by group
          rw [e]
          exact X.mul_mem ha hb
        · left
          have e : a * b = (w⁻¹ * (w⁻¹ * a) * w) * (w⁻¹ * b) := by
            calc a * b = (w * w) * (w⁻¹ * (w⁻¹ * a) * w) * (w⁻¹ * b) := by group
              _ = _ := by rw [hw2, one_mul]
          rw [e]
          exact X.mul_mem (hconj' _ ha) hb
      one_mem' := Or.inl X.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (X.inv_mem ha)
        · right
          have e : w⁻¹ * a⁻¹ = w⁻¹ * (w⁻¹ * a)⁻¹ * w := by
            rw [hwi]
            group
          rw [e]
          exact hconj' _ (X.inv_mem ha) }
  have hle : X ⊔ Subgroup.zpowers w ≤ S := by
    refine sup_le (fun x hx => Or.inl hx) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [inv_mul_cancel]; exact X.one_mem)
  have hS : (S : Set G) = (X : Set G) ∪ (fun x => w * x) '' (X : Set G) := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨w⁻¹ * x, hx, by group⟩
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact Or.inl hx
      · exact Or.inr (by rw [← mul_assoc, inv_mul_cancel, one_mul]; exact hy)
  calc Nat.card ↥(X ⊔ Subgroup.zpowers w) ≤ Nat.card ↥S := Subgroup.card_le_of_le hle
    _ = (S : Set G).ncard := (Nat.card_coe_set_eq _)
    _ ≤ (X : Set G).ncard + ((fun x => w * x) '' (X : Set G)).ncard := by
        rw [hS]
        exact Set.ncard_union_le _ _
    _ ≤ (X : Set G).ncard + (X : Set G).ncard := Nat.add_le_add_left (Set.ncard_image_le) _
    _ = 2 * Nat.card X := by rw [← Nat.card_coe_set_eq (X : Set G), two_mul]; rfl

end Count

end CFSG.Quasithin.H13.S127

namespace CFSG.Quasithin.H13.S127.Mod

theorem p1c_other : ∀ c ∈ p1c, c ≠ 0 → ∃ d ∈ p1c, d ≠ 0 ∧ d ≠ c := by decide

theorem p1c_four : ∀ a ∈ p1c, ∀ b ∈ p1c, a ≠ 0 → b ≠ 0 → a ≠ b →
    ∀ c ∈ p1c, c = 0 ∨ c = a ∨ c = b ∨ c = a ^^^ b := by decide

theorem one_mem_oVecL' : (1 : ℕ) ∈ oVecL := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem card_T_eq
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hCV : Subgroup.centralizer (V : Set G) = V) :
    Nat.card T = 2 ^ 10 := by
  have h := s.setting.hyp
  have hVT : V ≤ T := S127.L713.V_le_T h1222 h
  rw [SmithC27.card_eq_card_autOn_mul (S127.Mod.T_le_normalizer h1222 h),
    card_autOn_T_of_ne h1222 h hC.1 hne, hCV, inf_eq_right.mpr hVT,
    (S127.card_eq_of_1222 h1222 h).2.1]
  norm_num

theorem card_H_eq_index
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hCV : Subgroup.centralizer (V : Set G) = V) :
    Nat.card ↥(H714 T L V z) = 2 ^ 10 * (T.subgroupOf (H714 T L V z)).index := by
  have h1 := Subgroup.card_mul_index (T.subgroupOf (H714 T L V z))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le_H).toEquiv,
    s.card_T_eq h1222 hC hne hCV] at h1
  exact h1.symm

theorem card_centralizer_t_le
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hCV : Subgroup.centralizer (V : Set G) = V)
    (hM : Subgroup.normalizer (L : Set G) = L ⊔ T) :
    Nat.card ↥(H714 T L V z ⊓ Subgroup.centralizer ({(C.dc 1 : G)} : Set G)) ≤ 2 ^ 9 := by
  classical
  have h := s.setting.hyp
  set t' : G := (C.dc 1 : G) with ht'
  have hLTV := s.LT_le_normalizer_V h1222
  have hLTM : L ⊔ T ≤ h.hyp.MV := sup_le (S127.Mod.L_le_MV h) (S127.Mod.T_le_MV h1222 h)
  have hzV : z ∈ V := s.z_mem_V
  set cz := C.cd ⟨z, hzV⟩ with hcz
  have hczp : cz ∈ p1c := by
    have := s.mem
    rw [V1_eq h hC] at this
    exact (C.mem_subG ⟨z, hzV⟩).1 this
  have hcz0 : cz ≠ 0 := fun e => s.ne_one (congrArg Subtype.val (C.cd_eq_zero.1 e))
  set K := (L ⊔ T) ⊓ (Subgroup.centralizer ({z} : Set G) ⊓
    Subgroup.centralizer ({t'} : Set G)) with hK
  have hct := cd_t_mem_oVecL h1222 h hC s.setting.t_mem s.setting.orbit_t
  have hle : H714 T L V z ⊓ Subgroup.centralizer ({t'} : Set G) ≤ K := by
    intro x hx
    have hxM : x ∈ Subgroup.normalizer (L : Set G) :=
      centralizer_le_of_oVecL s.setting hC.1 hct (v := C.dc 1)
        (by rw [C.cd_dc 1 (by norm_num)]; exact one_mem_oVecL') hx.2
    rw [hM] at hxM
    exact ⟨hxM, s.H_le_Gz h1222 hx.1, hx.2⟩
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hLTV
  have hcard := SmithC27.card_eq_card_autOn_mul hKN
  have hC1 : Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) ≤ 64 := by
    rw [hCV]
    have h64 : Nat.card ↥V = 64 := by rw [(S127.card_eq_of_1222 h1222 h).2.1]; norm_num
    rw [← h64]
    exact Subgroup.card_le_of_le inf_le_right
  have hA : Nat.card ↥(autOn K V) ≤ 8 := by
    have hmem : ∀ a ∈ autOn K V, C.cB a ∈ stabC1 cz := by
      intro a ha
      obtain ⟨k, hkN, hkK, rfl⟩ := mem_autOn'.1 ha
      have hnm := (MVbar_code h hC.1 (conjAct_mem_autOn (hLTM hkK.1) hkN)).1
      have hkz : k * z * k⁻¹ = z := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hkK.2.1, mul_inv_cancel_right]
      have hkt : k * t' * k⁻¹ = t' := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hkK.2.2, mul_inv_cancel_right]
      have h1 := cd_conj C hkN ⟨z, hzV⟩
      have h2 := cd_conj C hkN (C.dc 1)
      have e1 : (⟨k * z * k⁻¹, (Subgroup.mem_normalizer_iff.1 hkN z).1 hzV⟩ : ↥V) = ⟨z, hzV⟩ :=
        Subtype.ext hkz
      have e2 : (⟨k * (C.dc 1 : G) * k⁻¹, (Subgroup.mem_normalizer_iff.1 hkN (C.dc 1)).1
          (C.dc 1).2⟩ : ↥V) = C.dc 1 := Subtype.ext hkt
      rw [e1] at h1
      rw [e2, C.cd_dc 1 (by norm_num)] at h2
      refine List.mem_filter.2 ⟨hnm, ?_⟩
      rw [← hcz] at h1
      simp [← h1, ← h2]
    have hinj : Function.Injective (fun a : ↥(autOn K V) =>
        (⟨C.cB a, List.mem_toFinset.2 (hmem a a.2)⟩ : ↥(stabC1 cz).toFinset)) := fun a b hab =>
      Subtype.ext (C.cB_injective (congrArg Subtype.val hab))
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_eq_finsetCard]
    exact (List.toFinset_card_le _).trans (cert55_stab cz hczp hcz0)
  calc Nat.card ↥(H714 T L V z ⊓ Subgroup.centralizer ({t'} : Set G)) ≤ Nat.card K :=
        Subgroup.card_le_of_le hle
    _ = Nat.card ↥(autOn K V) * Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) := hcard
    _ ≤ 8 * 64 := Nat.mul_le_mul hA hC1
    _ = 2 ^ 9 := by norm_num

theorem two_mul_le_orbit_t
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hCV : Subgroup.centralizer (V : Set G) = V)
    (hM : Subgroup.normalizer (L : Set G) = L ⊔ T) :
    2 * (T.subgroupOf (H714 T L V z)).index ≤
      {y : G | ∃ h ∈ H714 T L V z, y = h * (C.dc 1 : G) * h⁻¹}.ncard := by
  rw [ncard_conj_orbit]
  set K := (Subgroup.centralizer ({(C.dc 1 : G)} : Set G)).subgroupOf (H714 T L V z) with hK
  have h1 := Subgroup.card_mul_index K
  have hcard : Nat.card ↥K ≤ 2 ^ 9 := by
    rw [hK, ← Subgroup.card_map_of_injective (H714 T L V z).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
    exact s.card_centralizer_t_le h1222 hC hCV hM
  rw [s.card_H_eq_index h1222 hC hne hCV] at h1
  have h2 : 2 ^ 10 * (T.subgroupOf (H714 T L V z)).index ≤ 2 ^ 9 * K.index := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ hcard
  omega

theorem V1_cases [IsMulCommutative ↥V] {C : Coding ↥V}
    (hC : Std C T L) {cv : ℕ} (hcv : cv ∈ p1c) (hcv0 : cv ≠ 0)
    (hcvz : cv ≠ C.cd ⟨z, s.z_mem_V⟩) {x : G} (hx : x ∈ V1 T L V) :
    x = 1 ∨ x = z ∨ x = (C.dc cv : G) ∨ x = z * C.dc cv := by
  have h := s.setting.hyp
  have hzV := s.z_mem_V
  have hxV : x ∈ V := (inf_le_left : V1 T L V ≤ V) hx
  have hcode : ∀ y ∈ V1 T L V, ∀ hy : y ∈ V, C.cd ⟨y, hy⟩ ∈ p1c := fun y hy hyV => by
    rw [V1_eq h hC] at hy
    exact (C.mem_subG ⟨y, hyV⟩).1 hy
  have hcz := hcode z s.mem hzV
  have hcz0 : C.cd ⟨z, hzV⟩ ≠ 0 := fun e => s.ne_one (congrArg Subtype.val (C.cd_eq_zero.1 e))
  rcases p1c_four _ hcz _ hcv hcz0 hcv0 (Ne.symm hcvz) _ (hcode x hx hxV) with e | e | e | e
  · left
    exact congrArg Subtype.val (C.cd_eq_zero.1 e)
  · right; left
    exact congrArg Subtype.val (C.cd_injective e)
  · right; right; left
    have e' : C.cd ⟨x, hxV⟩ = C.cd (C.dc cv) := by rw [C.cd_dc cv (p1c_lt cv hcv)]; exact e
    exact congrArg Subtype.val (C.cd_injective e')
  · right; right; right
    have : (⟨x, hxV⟩ : ↥V) = ⟨z, hzV⟩ * C.dc cv := C.cd_injective (by
      rw [e, C.cd_mul, C.cd_dc cv (p1c_lt cv hcv)])
    exact congrArg Subtype.val this

theorem card_U_le_pow
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) :
    Nat.card ↥(U714 T L V z) ≤ 2 ^ ({Y : Subgroup G | ∃ h ∈ H714 T L V z,
      Y = (V1 T L V).map (MulAut.conj h).toMonoidHom}.ncard + 1) := by
  classical
  have h := s.setting.hyp
  set O := {Y : Subgroup G | ∃ h ∈ H714 T L V z,
    Y = (V1 T L V).map (MulAut.conj h).toMonoidHom} with hO
  have hOfin : O.Finite := Set.toFinite O
  have hzV := s.z_mem_V
  have hcz : C.cd ⟨z, hzV⟩ ∈ p1c := by
    have := s.mem
    rw [V1_eq h hC] at this
    exact (C.mem_subG ⟨z, hzV⟩).1 this
  have hcz0 : C.cd ⟨z, hzV⟩ ≠ 0 := fun e => s.ne_one (congrArg Subtype.val (C.cd_eq_zero.1 e))
  obtain ⟨cv, hcv, hcv0, hcvz⟩ := p1c_other _ hcz hcz0
  set v : G := (C.dc cv : G) with hv
  have hvV1 : v ∈ V1 T L V := by
    rw [V1_eq h hC, C.mem_subG, C.cd_dc cv (p1c_lt cv hcv)]
    exact hcv
  have hV1le : V1 T L V ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers v := by
    intro x hx
    rcases s.V1_cases hC hcv hcv0 hcvz hx with e | e | e | e <;> rw [e]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hUH := s.H_le_normalizer_U h1222
  have hV1U : V1 T L V ≤ U714 T L V z := le_conjClosure _ _
  have hOU : ∀ W ∈ O, W ≤ U714 T L V z := by
    rintro W ⟨g, hg, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hUH hg) x).mp (hV1U hx)
  have hW : ∀ W ∈ O, ∃ w ∈ U714 T L V z, w * w = 1 ∧
      W ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers w := by
    rintro W ⟨g, hg, rfl⟩
    have hgz : (MulAut.conj g) z = z := by
      rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 hg),
        mul_inv_cancel_right]
    refine ⟨g * v * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hUH hg) v).mp (hV1U hvV1), ?_, ?_⟩
    · have hv2 : v * v = 1 := by
        rw [← pow_two]
        exact S127.sq_eq_one_of_mem h.hyp ((inf_le_left : V1 T L V ≤ V) hvV1)
      calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [hv2, mul_one, mul_inv_cancel]
    · refine (Subgroup.map_mono hV1le).trans ?_
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      show Subgroup.zpowers ((MulAut.conj g) z) ⊔ Subgroup.zpowers ((MulAut.conj g) v) ≤ _
      rw [hgz, MulAut.conj_apply]
  have key : ∀ S : Finset (Subgroup G), (↑S ⊆ O) →
      Nat.card ↥(Subgroup.zpowers z ⊔ ⨆ W ∈ S, W) ≤ 2 ^ S.card * 2 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq, Finset.card_empty,
        pow_zero, one_mul]
      rw [Nat.card_zpowers, s.orderOf_z]
    | insert W S hWS ih =>
      intro hsub
      have hWO : W ∈ O := hsub (Finset.mem_insert_self W S)
      have ih' := ih fun x hx => hsub (Finset.mem_insert_of_mem hx)
      obtain ⟨w, hwU, hw2, hWle⟩ := hW W hWO
      set Y := Subgroup.zpowers z ⊔ ⨆ W' ∈ S, W' with hY
      have hYU : Y ≤ U714 T L V z :=
        sup_le (Subgroup.zpowers_le_of_mem s.z_mem_U) (iSup₂_le fun W' hW' =>
          hOU W' (hsub (Finset.mem_insert_of_mem hW')))
      have hwN : w ∈ Subgroup.normalizer (Y : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun y hy => ?_
        have hc := s.comm_mem_U h1222 hwU (hYU hy)
        have e : w * y * w⁻¹ = (w * y * w⁻¹ * y⁻¹) * y := by group
        rw [e]
        exact Y.mul_mem (Subgroup.mem_sup_left hc) hy
      have hsup : Subgroup.zpowers z ⊔ ⨆ W' ∈ insert W S, W' ≤ Y ⊔ Subgroup.zpowers w := by
        rw [Finset.iSup_insert]
        refine sup_le (le_sup_left.trans le_sup_left) (sup_le ?_ (le_sup_right.trans le_sup_left))
        exact hWle.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      calc Nat.card ↥(Subgroup.zpowers z ⊔ ⨆ W' ∈ insert W S, W')
          ≤ Nat.card ↥(Y ⊔ Subgroup.zpowers w) := Subgroup.card_le_of_le hsup
        _ ≤ 2 * Nat.card Y := card_sup_zpowers_le hwN hw2
        _ ≤ 2 * (2 ^ S.card * 2) := Nat.mul_le_mul_left _ ih'
        _ = 2 ^ (insert W S).card * 2 := by
          rw [Finset.card_insert_of_notMem hWS, pow_succ]
          ring
  have hU : U714 T L V z ≤ Subgroup.zpowers z ⊔ ⨆ W ∈ hOfin.toFinset, W := by
    rw [← s.conjClosure_eq h1222]
    refine conjClosure_le fun g hg x hx => Subgroup.mem_sup_right ?_
    have hWO : (V1 T L V).map (MulAut.conj g).toMonoidHom ∈ hOfin.toFinset :=
      hOfin.mem_toFinset.2 ⟨g, hg, rfl⟩
    refine le_iSup₂ (f := fun W (_ : W ∈ hOfin.toFinset) => W) _ hWO ?_
    exact ⟨x, hx, by simp⟩
  calc Nat.card ↥(U714 T L V z) ≤ Nat.card ↥(Subgroup.zpowers z ⊔ ⨆ W ∈ hOfin.toFinset, W) :=
        Subgroup.card_le_of_le hU
    _ ≤ 2 ^ hOfin.toFinset.card * 2 := key _ (by simp)
    _ = 2 ^ (O.ncard + 1) := by rw [Set.ncard_eq_toFinset_card O hOfin, pow_succ]

theorem index_eq_mul
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hCV : Subgroup.centralizer (V : Set G) = V) :
    ∃ r, (T.subgroupOf (H714 T L V z)).index = {Y : Subgroup G | ∃ h ∈ H714 T L V z,
      Y = (V1 T L V).map (MulAut.conj h).toMonoidHom}.ncard * r ∧ 3 ∣ r := by
  rw [ncard_conj_orbit_sub]
  set N₁ := (Subgroup.normalizer (V1 T L V : Set G)).subgroupOf (H714 T L V z) with hN₁
  have hTN : T.subgroupOf (H714 T L V z) ≤ N₁ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (s.T_le_normalizer_V1 h1222 (Subgroup.mem_subgroupOf.1 hx))
  refine ⟨(T.subgroupOf (H714 T L V z)).relIndex N₁, by
    rw [← Subgroup.relIndex_mul_index hTN, mul_comm], ?_⟩
  have hc := Subgroup.relIndex_mul_card (H := T.subgroupOf (H714 T L V z)) (K := N₁)
  rw [inf_eq_left.mpr hTN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le_H).toEquiv,
    s.card_T_eq h1222 hC hne hCV] at hc
  obtain ⟨y, hyL1, hy3⟩ := S127.Mod.idx3_exists (s.relIndex_L1 h1222)
  have hyH : y ∈ H714 T L V z := (le_sup_left.trans le_sup_right : L1 T L V ≤ _) hyL1
  have hyN : (⟨y, hyH⟩ : ↥(H714 T L V z)) ∈ N₁ :=
    Subgroup.mem_subgroupOf.2 ((s.L1T_le_normalizer_V1 h1222) (Subgroup.mem_sup_left hyL1))
  have h3 : 3 ∣ Nat.card ↥N₁ := by
    have := orderOf_dvd_natCard (⟨⟨y, hyH⟩, hyN⟩ : ↥N₁)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hy3] at this
  rw [← hc] at h3
  exact (Nat.Coprime.pow_right 10 (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3

theorem centralizer_le_normalizer_V1 [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) {cv : ℕ} (hcv : cv ∈ p1c)
    (hcv0 : cv ≠ 0) (hcvz : cv ≠ C.cd ⟨z, s.z_mem_V⟩) {h : G} (hh : h ∈ H714 T L V z)
    (hhv : h * C.dc cv = C.dc cv * h) : h ∈ Subgroup.normalizer (V1 T L V : Set G) := by
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 hh)
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hvV1 : (C.dc cv : G) ∈ V1 T L V := by
    rw [V1_eq s.setting.hyp hC, C.mem_subG, C.cd_dc cv (p1c_lt cv hcv)]
    exact hcv
  rcases s.V1_cases hC hcv hcv0 hcvz hx with e | e | e | e <;> rw [e]
  · rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [hhz, mul_inv_cancel_right]
    exact s.mem
  · rw [hhv, mul_inv_cancel_right]
    exact hvV1
  · have hz' : h * z * h⁻¹ = z := by rw [hhz, mul_inv_cancel_right]
    have hv' : h * (C.dc cv : G) * h⁻¹ = C.dc cv := by rw [hhv, mul_inv_cancel_right]
    have e2 : h * (z * C.dc cv) * h⁻¹ = z * C.dc cv := by
      calc h * (z * C.dc cv) * h⁻¹ = (h * z * h⁻¹) * (h * (C.dc cv : G) * h⁻¹) := by group
        _ = z * C.dc cv := by rw [hz', hv']
    rw [e2]
    exact Subgroup.mul_mem _ s.mem hvV1

theorem comm_mul_z_iff (h1222 : Stmt12_2_2) {h v : G} (hh : h ∈ H714 T L V z) :
    h * (z * v) = z * v * h ↔ h * v = v * h := by
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 hh)
  constructor
  · intro e
    have e2 : z * (h * v) = z * (v * h) := by
      rw [← mul_assoc, ← hhz, mul_assoc, e, mul_assoc]
    exact mul_left_cancel e2
  · intro e
    rw [← mul_assoc, hhz, mul_assoc, e, mul_assoc]

omit [Finite G] s in
theorem conj_orbit_eq {H : Subgroup G} {x x' g : G} (hg : g ∈ H) (hx : x' = g * x * g⁻¹) :
    {y : G | ∃ h ∈ H, y = h * x' * h⁻¹} = {y : G | ∃ h ∈ H, y = h * x * h⁻¹} := by
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, H.mul_mem hh hg, by rw [hx]; group⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g⁻¹, H.mul_mem hh (H.inv_mem hg), by rw [hx]; group⟩

omit [Finite G] s in
theorem card_subgroupOf (K H : Subgroup G) : Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm]

theorem two_mul_add_le
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8)
    (hCV : Subgroup.centralizer (V : Set G) = V)
    (hM : Subgroup.normalizer (L : Set G) = L ⊔ T) :
    2 * (T.subgroupOf (H714 T L V z)).index + 2 * {Y : Subgroup G | ∃ h ∈ H714 T L V z,
      Y = (V1 T L V).map (MulAut.conj h).toMonoidHom}.ncard ≤ 70 := by
  classical
  have h := s.setting.hyp
  have hzV := s.z_mem_V
  have hcz : C.cd ⟨z, hzV⟩ ∈ p1c := by
    have := s.mem
    rw [V1_eq h hC] at this
    exact (C.mem_subG ⟨z, hzV⟩).1 this
  have hcz0 : C.cd ⟨z, hzV⟩ ≠ 0 := fun e => s.ne_one (congrArg Subtype.val (C.cd_eq_zero.1 e))
  obtain ⟨cv, hcv, hcv0, hcvz⟩ := p1c_other _ hcz hcz0
  set v : G := (C.dc cv : G) with hv
  have hvV1 : v ∈ V1 T L V := by
    rw [V1_eq h hC, C.mem_subG, C.cd_dc cv (p1c_lt cv hcv)]
    exact hcv
  have hvV : v ∈ V := (inf_le_left : V1 T L V ≤ V) hvV1
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => by
    rw [← pow_two]; exact S127.sq_eq_one_of_mem h.hyp hx
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((S127.card_eq_of_1222 h1222 h).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hv1 : v ≠ 1 := fun e => hcv0 (by
    rw [← C.cd_dc cv (p1c_lt cv hcv)]
    exact C.cd_eq_zero.2 (Subtype.ext e))
  have hvz : v ≠ z := fun e => hcvz (by
    rw [← C.cd_dc cv (p1c_lt cv hcv)]
    exact congrArg C.cd (Subtype.ext e))
  have hzvV : z * v ∈ V := V.mul_mem hzV hvV
  have hzv1 : z * v ≠ 1 := fun e => hvz (by
    have := eq_inv_of_mul_eq_one_right e
    rw [this, inv_eq_of_mul_eq_one_right (hV2 z hzV)])
  have hzvz : z * v ≠ z := fun e => hv1 (mul_left_cancel (e.trans (mul_one z).symm))
  set t' : G := (C.dc 1 : G) with ht'
  have ht'V : t' ∈ V := (C.dc 1).2
  have ht'U : t' ∈ U714 T L V z := (s.mem_U_iff h1222 hC hne hT hbig (C.dc 1)).2
    (by rw [C.cd_dc 1 (by norm_num)]; decide)
  have ht'1 : t' ≠ 1 := fun e => by
    have := C.cd_eq_zero.2 (Subtype.ext e : C.dc 1 = 1)
    rw [C.cd_dc 1 (by norm_num)] at this
    exact absurd this (by norm_num)
  have ht'z : t' ≠ z := fun e => by
    have h1 : C.cd (C.dc 1) = C.cd ⟨z, hzV⟩ := congrArg C.cd (Subtype.ext e)
    rw [C.cd_dc 1 (by norm_num)] at h1
    exact p1c_ne_one _ hcz h1.symm
  have hUH := s.H_le_normalizer_U h1222
  have hV1U : V1 T L V ≤ U714 T L V z := le_conjClosure _ _
  set I := {u : G | u ∈ U714 T L V z ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z} with hI
  have hIle := s.ncard_inv_le h1222 hC hne hT hbig hCV
  have hconjI : ∀ x ∈ U714 T L V z, x * x = 1 → x ≠ 1 → x ≠ z →
      ∀ g ∈ H714 T L V z, g * x * g⁻¹ ∈ I := by
    intro x hxU hx2 hx1 hxz g hg
    have hgz : g * z * g⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 hg), mul_inv_cancel_right]
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hUH hg) x).mp hxU, ?_, ?_, ?_⟩
    · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
    · intro e
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    · intro e
      apply hxz
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [e, hgz]
        _ = z := by group
  set X := {y : G | ∃ g ∈ H714 T L V z, y = g * t' * g⁻¹} with hX
  set A := {y : G | ∃ g ∈ H714 T L V z, y = g * v * g⁻¹} with hA
  set B := {y : G | ∃ g ∈ H714 T L V z, y = g * (z * v) * g⁻¹} with hB
  have hXI : X ⊆ I := by
    rintro _ ⟨g, hg, rfl⟩
    exact hconjI t' ht'U (hV2 t' ht'V) ht'1 ht'z g hg
  have hAI : A ⊆ I := by
    rintro _ ⟨g, hg, rfl⟩
    exact hconjI v (hV1U hvV1) (hV2 v hvV) hv1 hvz g hg
  have hBI : B ⊆ I := by
    rintro _ ⟨g, hg, rfl⟩
    exact hconjI (z * v) (Subgroup.mul_mem _ s.z_mem_U (hV1U hvV1)) (hV2 _ hzvV) hzv1 hzvz g hg
  have hCzv : (Subgroup.centralizer ({z * v} : Set G)).subgroupOf (H714 T L V z) =
      (Subgroup.centralizer ({v} : Set G)).subgroupOf (H714 T L V z) := by
    ext ⟨g, hg⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    show g * (z * v) = z * v * g ↔ g * v = v * g
    exact s.comm_mul_z_iff h1222 hg
  have hAB : B.ncard = A.ncard := by rw [hA, hB, ncard_conj_orbit, ncard_conj_orbit, hCzv]
  have hcardH := s.card_H_eq_index h1222 hC hne hCV
  have hcardT := s.card_T_eq h1222 hC hne hCV
  have hCv : 2 ^ 10 ≤ Nat.card ↥(H714 T L V z ⊓ Subgroup.centralizer ({v} : Set G)) := by
    have horb : {y : G | ∃ g ∈ T, y = g * v * g⁻¹}.ncard ≤ 2 := by
      have hsub : {y : G | ∃ g ∈ T, y = g * v * g⁻¹} ⊆ {v, z * v} := by
        rintro _ ⟨g, hg, rfl⟩
        have hgH : g ∈ H714 T L V z := T_le_H hg
        have hmem : g * v * g⁻¹ ∈ V1 T L V :=
          (Subgroup.mem_normalizer_iff.mp (s.T_le_normalizer_V1 h1222 hg) v).mp hvV1
        have hI' := hconjI v (hV1U hvV1) (hV2 v hvV) hv1 hvz g hgH
        rcases s.V1_cases hC hcv hcv0 hcvz hmem with e | e | e | e
        · exact absurd e hI'.2.2.1
        · exact absurd e hI'.2.2.2
        · exact Or.inl e
        · exact Or.inr e
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    rw [ncard_conj_orbit] at horb
    have h1 := Subgroup.card_mul_index ((Subgroup.centralizer ({v} : Set G)).subgroupOf T)
    rw [card_subgroupOf, hcardT] at h1
    have hCT : 2 ^ 9 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({v} : Set G)) := by
      have h2 : 2 ^ 10 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({v} : Set G)) * 2 := by
        rw [← h1]
        exact Nat.mul_le_mul_left _ horb
      omega
    obtain ⟨y, hyL1, hy3⟩ := S127.Mod.idx3_exists (s.relIndex_L1 h1222)
    have hyH : y ∈ H714 T L V z := (le_sup_left.trans le_sup_right : L1 T L V ≤ _) hyL1
    have hyv : y ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (((oTwoUpper_le _).trans inf_le_right) hyL1) v
        hvV1).symm
    have hyT : y ∉ T := by
      intro hyT
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.hyp.sylow.1) ⟨y, hyT⟩
      have hk' : orderOf y = 2 ^ k := by
        rw [← hk, ← Subgroup.orderOf_coe]
      rw [hy3] at hk'
      have h3 : 3 ∣ 2 ^ k := ⟨1, by rw [mul_one, hk']⟩
      have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    set K := H714 T L V z ⊓ Subgroup.centralizer ({v} : Set G) with hK
    have hle : T ⊓ Subgroup.centralizer ({v} : Set G) ≤ K := inf_le_inf_right _ T_le_H
    have h3 := Subgroup.card_mul_index ((T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h3
    have hidx : 2 ≤ ((T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf K).index := by
      have hne1 : ((T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf K).index ≠ 1 := by
        rw [Ne, Subgroup.index_eq_one]
        intro htop
        have : (⟨y, hyH, hyv⟩ : ↥K) ∈ (T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf K :=
          htop ▸ Subgroup.mem_top _
        exact hyT (Subgroup.mem_subgroupOf.1 this).1
      have hne0 := Subgroup.index_ne_zero_of_finite
        (H := (T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf K)
      omega
    calc 2 ^ 10 = 2 ^ 9 * 2 := by norm_num
      _ ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({v} : Set G)) *
          ((T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf K).index :=
        Nat.mul_le_mul hCT hidx
      _ = Nat.card K := h3
  have hCt : Nat.card ↥(H714 T L V z ⊓ Subgroup.centralizer ({t'} : Set G)) ≤ 2 ^ 9 :=
    s.card_centralizer_t_le h1222 hC hCV hM
  have hnot : ∀ x, x = v ∨ x = z * v → ∀ g ∈ H714 T L V z, t' ≠ g * x * g⁻¹ := by
    intro x hx g hg he
    have horb := conj_orbit_eq hg he
    have hidx : ((Subgroup.centralizer ({t'} : Set G)).subgroupOf (H714 T L V z)).index =
        ((Subgroup.centralizer ({v} : Set G)).subgroupOf (H714 T L V z)).index := by
      rw [← ncard_conj_orbit, ← ncard_conj_orbit, horb]
      rcases hx with rfl | rfl
      · rfl
      · rw [ncard_conj_orbit, ncard_conj_orbit, hCzv]
    have h1 := Subgroup.card_mul_index
      ((Subgroup.centralizer ({t'} : Set G)).subgroupOf (H714 T L V z))
    have h2 := Subgroup.card_mul_index
      ((Subgroup.centralizer ({v} : Set G)).subgroupOf (H714 T L V z))
    rw [card_subgroupOf] at h1 h2
    rw [hidx] at h1
    have hpos := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := (Subgroup.centralizer ({v} : Set G)).subgroupOf (H714 T L V z)))
    have heq : Nat.card ↥(H714 T L V z ⊓ Subgroup.centralizer ({t'} : Set G)) =
        Nat.card ↥(H714 T L V z ⊓ Subgroup.centralizer ({v} : Set G)) :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    omega
  have hXA : Disjoint X (A ∪ B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨g, hg, rfl⟩ (⟨g', hg', he⟩ | ⟨g', hg', he⟩)
    · exact hnot v (Or.inl rfl) (g⁻¹ * g') (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hg')
        (by
          calc t' = g⁻¹ * (g * t' * g⁻¹) * g := by group
            _ = g⁻¹ * (g' * v * g'⁻¹) * g := by rw [he]
            _ = g⁻¹ * g' * v * (g⁻¹ * g')⁻¹ := by group)
    · exact hnot (z * v) (Or.inr rfl) (g⁻¹ * g') (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hg')
        (by
          calc t' = g⁻¹ * (g * t' * g⁻¹) * g := by group
            _ = g⁻¹ * (g' * (z * v) * g'⁻¹) * g := by rw [he]
            _ = g⁻¹ * g' * (z * v) * (g⁻¹ * g')⁻¹ := by group)
  set N₁ := (Subgroup.normalizer (V1 T L V : Set G)).subgroupOf (H714 T L V z) with hN₁
  set Cv := (Subgroup.centralizer ({v} : Set G)).subgroupOf (H714 T L V z) with hCvdef
  have hCN : Cv ≤ N₁ := by
    rintro ⟨g, hg⟩ hgc
    rw [hCvdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hgc
    exact Subgroup.mem_subgroupOf.2
      (s.centralizer_le_normalizer_V1 h1222 hC hcv hcv0 hcvz hg hgc)
  have hAO : {Y : Subgroup G | ∃ h ∈ H714 T L V z,
      Y = (V1 T L V).map (MulAut.conj h).toMonoidHom}.ncard ≤ A.ncard := by
    rw [ncard_conj_orbit_sub, hA, ncard_conj_orbit]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hCN)
  have hAB2 : 2 * {Y : Subgroup G | ∃ h ∈ H714 T L V z,
      Y = (V1 T L V).map (MulAut.conj h).toMonoidHom}.ncard ≤ (A ∪ B).ncard := by
    by_cases hd : Disjoint A B
    · rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _), hAB]
      omega
    · rw [Set.not_disjoint_iff] at hd
      obtain ⟨_, ⟨g, hg, rfl⟩, ⟨g', hg', he⟩⟩ := hd
      set n := g'⁻¹ * g with hn
      have hnH : n ∈ H714 T L V z := Subgroup.mul_mem _ (Subgroup.inv_mem _ hg') hg
      have hnv : n * v * n⁻¹ = z * v := by
        calc n * v * n⁻¹ = g'⁻¹ * (g * v * g⁻¹) * g' := by rw [hn]; group
          _ = g'⁻¹ * (g' * (z * v) * g'⁻¹) * g' := by rw [he]
          _ = z * v := by group
      have hnN : (⟨n, hnH⟩ : ↥(H714 T L V z)) ∈ N₁ := by
        refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_normalizer_fintype fun x hx => ?_)
        have hnz : n * z * n⁻¹ = z := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 hnH),
            mul_inv_cancel_right]
        rcases s.V1_cases hC hcv hcv0 hcvz hx with e | e | e | e <;> rw [e]
        · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
        · rw [hnz]; exact s.mem
        · rw [hnv]; exact Subgroup.mul_mem _ s.mem hvV1
        · have e2 : n * (z * v) * n⁻¹ = (n * z * n⁻¹) * (n * v * n⁻¹) := by group
          rw [e2, hnz, hnv, ← mul_assoc, ← pow_two, S127.sq_eq_one_of_mem h.hyp hzV, one_mul]
          exact hvV1
      have hnC : (⟨n, hnH⟩ : ↥(H714 T L V z)) ∉ Cv := by
        intro hc
        rw [hCvdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hc
        apply s.ne_one
        have h1 : n * v * n⁻¹ = v := by
          have hc' : n * v = v * n := hc
          rw [hc', mul_inv_cancel_right]
        have h2 : z * v = v := hnv.symm.trans h1
        calc z = z * v * v⁻¹ := by group
          _ = 1 := by rw [h2, mul_inv_cancel]
      have hrel : 2 ≤ Cv.relIndex N₁ := by
        have hne1 : Cv.relIndex N₁ ≠ 1 := by
          rw [Ne, Subgroup.relIndex_eq_one]
          exact fun hle => hnC (hle hnN)
        have hne0 : Cv.relIndex N₁ ≠ 0 :=
          Subgroup.index_ne_zero_of_finite (H := Cv.subgroupOf N₁)
        omega
      have hidx := Subgroup.relIndex_mul_index hCN
      have hAidx : A.ncard = Cv.index := by rw [hA, ncard_conj_orbit]
      calc 2 * {Y : Subgroup G | ∃ h ∈ H714 T L V z,
            Y = (V1 T L V).map (MulAut.conj h).toMonoidHom}.ncard = 2 * N₁.index := by
            rw [ncard_conj_orbit_sub]
        _ ≤ Cv.relIndex N₁ * N₁.index := Nat.mul_le_mul_right _ hrel
        _ = A.ncard := by rw [hidx, hAidx]
        _ ≤ (A ∪ B).ncard := Set.ncard_le_ncard Set.subset_union_left (Set.toFinite _)
  have hXt : 2 * (T.subgroupOf (H714 T L V z)).index ≤ X.ncard :=
    s.two_mul_le_orbit_t h1222 hC hne hCV hM
  have hunion : (X ∪ (A ∪ B)).ncard = X.ncard + (A ∪ B).ncard :=
    Set.ncard_union_eq hXA (Set.toFinite _) (Set.toFinite _)
  have hsub : X ∪ (A ∪ B) ⊆ I := Set.union_subset hXI (Set.union_subset hAI hBI)
  have h70 : (X ∪ (A ∪ B)).ncard ≤ 70 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hIle
  omega

theorem card_O_eq_seven
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8)
    (hCV : Subgroup.centralizer (V : Set G) = V)
    (hM : Subgroup.normalizer (L : Set G) = L ⊔ T) :
    ((Subgroup.normalizer (V1 T L V : Set G)).subgroupOf (H714 T L V z)).index = 7 ∧
      (T.subgroupOf (H714 T L V z)).index = 21 := by
  have hO := ncard_conj_orbit_sub (H714 T L V z) (V1 T L V)
  obtain ⟨r, hr, h3r⟩ := s.index_eq_mul h1222 hC hne hCV
  have hsum := s.two_mul_add_le h1222 hC hne hT hbig hCV hM
  have hodd := s.odd_index_T
  have hU := s.card_U_le_pow h1222 hC
  rw [s.card_U_eq h1222 hC hne hT hbig hCV] at hU
  rw [hO] at hr hsum hU
  set o := ((Subgroup.normalizer (V1 T L V : Set G)).subgroupOf (H714 T L V z)).index with ho
  have h6 : 6 ≤ o := by
    by_contra hlt
    have : 2 ^ (o + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨r', rfl⟩ := h3r
  rw [hr] at hsum hodd
  have hr1 : r' = 1 := by
    have hr0 : r' ≠ 0 := by
      rintro rfl
      simp at hodd
    by_contra hr2
    have : 6 * 6 ≤ o * (3 * r') := Nat.mul_le_mul h6 (by omega)
    omega
  subst hr1
  have ho7 : o ≤ 8 := by omega
  have hoodd : Odd o := (Nat.odd_mul.mp hodd).1
  have ho : o = 7 := by
    obtain ⟨k, hk⟩ := hoodd
    omega
  exact ⟨ho, by rw [hr, ho]⟩

theorem exists_seven
    [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8)
    (hCV : Subgroup.centralizer (V : Set G) = V)
    (hM : Subgroup.normalizer (L : Set G) = L ⊔ T) :
    ∃ h ∈ H714 T L V z, h ^ 7 = 1 ∧
      (∀ k : ℕ, 0 < k → k < 7 → h ^ k ∉ Subgroup.normalizer (V1 T L V : Set G)) ∧
      ∀ g ∈ H714 T L V z, ∃ k : ℕ, k < 7 ∧
        (h ^ k)⁻¹ * g ∈ Subgroup.normalizer (V1 T L V : Set G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hO7, hm21⟩ := s.card_O_eq_seven h1222 hC hne hT hbig hCV hM
  set N₁ := (Subgroup.normalizer (V1 T L V : Set G)).subgroupOf (H714 T L V z) with hN₁
  have hH := s.card_H_eq_index h1222 hC hne hCV
  rw [hm21] at hH
  have hN : Nat.card ↥N₁ = 3 * 2 ^ 10 := by
    have := Subgroup.card_mul_index N₁
    rw [hO7, hH] at this
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H714 T L V z)) 7
    (by rw [hH]; norm_num)
  have hcop : ∀ m, 0 < m → m < 7 → (orderOf x).Coprime m := fun m h0 h7 => by
    rw [hx]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (Nat.not_dvd_of_pos_of_lt h0 h7)
  have hnot : ∀ m, 0 < m → m < 7 → x ^ m ∉ N₁ := by
    intro m h0 h7 hmem
    have hdvd := orderOf_dvd_natCard (⟨x ^ m, hmem⟩ : ↥N₁)
    rw [Subgroup.orderOf_mk, Nat.Coprime.orderOf_pow (hcop m h0 h7), hx, hN] at hdvd
    norm_num at hdvd
  refine ⟨x, x.2, ?_, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  · intro k hk0 hk7 hkN
    exact hnot k hk0 hk7 (Subgroup.mem_subgroupOf.2 (by simpa using hkN))
  · intro g hg
    let f : Fin 7 → ↥(H714 T L V z) ⧸ N₁ := fun k => ((x ^ (k : ℕ) : ↥(H714 T L V z)) : _)
    have hinj : Function.Injective f := by
      intro j k hjk
      have hk : ∀ a b : Fin 7, a < b → f a ≠ f b := by
        intro a b hab hfab
        have h1 : (x ^ (a : ℕ))⁻¹ * x ^ (b : ℕ) ∈ N₁ := QuotientGroup.eq.mp hfab
        have h2 : (x ^ (a : ℕ))⁻¹ * x ^ (b : ℕ) = x ^ ((b : ℕ) - a) := by
          rw [← pow_sub_mul_pow x (le_of_lt hab), pow_mul_comm, inv_mul_cancel_left]
        rw [h2] at h1
        exact hnot _ (by omega) (by omega) h1
      rcases lt_trichotomy j k with h | h | h
      · exact absurd hjk (hk j k h)
      · exact h
      · exact absurd hjk.symm (hk k j h)
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [Nat.card_fin, ← Subgroup.index, hO7])
    obtain ⟨k, hk⟩ := hbij.2 ((⟨g, hg⟩ : ↥(H714 T L V z)) : ↥(H714 T L V z) ⧸ N₁)
    refine ⟨k, k.2, ?_⟩
    have := QuotientGroup.eq.mp hk
    simpa using Subgroup.mem_subgroupOf.1 this

end CFSG.Quasithin.H13.S127.L715.Set714
