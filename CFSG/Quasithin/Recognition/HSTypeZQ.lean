module

public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Recognition.HSTypeSetting

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_of_le_normalizer {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) =
      Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem card_modEq_card_inf_centralizer_prime [Finite G] {A : Subgroup G} {y : G} {p : ℕ}
    (hp : p.Prime) (hy : y ^ p = 1) (hyA : y ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card A ≡ Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) [MOD p] := by
  classical
  have := Fintype.ofFinite ↥A
  have : Fact p.Prime := ⟨hp⟩
  let f : Function.End ↥A := fun a => ⟨y * a * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyA a).mp a.2⟩
  have hf : ∀ (k : ℕ) (a : ↥A), ((f ^ k) a : G) = y ^ k * a * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp; rfl
    | succ k ih =>
      intro a
      rw [pow_succ']
      show y * ((f ^ k) a : G) * y⁻¹ = _
      rw [ih, pow_succ']
      group
  have hfp : f ^ p ^ 1 = 1 := by
    funext a
    apply Subtype.ext
    show ((f ^ p ^ 1) a : G) = (a : G)
    rw [pow_one, hf, hy, one_mul, inv_one, mul_one]
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hfp
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  have e : Function.fixedPoints f ≃ ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) :=
    { toFun := fun a => ⟨a.1.1, a.1.2, Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := congrArg Subtype.val a.2
        change y * (a.1 : G) * y⁻¹ = a.1 at this
        calc (a.1 : G) * y = y * a.1 * y⁻¹ * y := by rw [this]
          _ = y * a.1 := by group)⟩
      invFun := fun b => ⟨⟨b.1, b.2.1⟩, Subtype.ext (by
        show y * b.1 * y⁻¹ = b.1
        have := Subgroup.mem_centralizer_singleton_iff.mp b.2.2
        rw [← this, mul_inv_cancel_right])⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  rwa [Nat.card_congr e] at h

theorem card_modEq_card_inf_centralizer [Finite G] {A : Subgroup G} {y : G} (hy : y ^ 3 = 1)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card A ≡ Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) [MOD 3] :=
  card_modEq_card_inf_centralizer_prime Nat.prime_three hy hyA

abbrev hsZQ (z : G) : Subgroup G := hsQ z ⊓ Subgroup.centralizer (hsQ z : Set G)

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem ZQ_subgroupOf_eq_center (z : G) :
    (hsZQ z).subgroupOf (hsQ z) = Subgroup.center ↥(hsQ z) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hx⟩ g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g g.2)
  · intro hx
    exact ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      congrArg Subtype.val (hx ⟨g, hg⟩)⟩

theorem card_ZQ (h : HSSetting z V) : Nat.card (hsZQ z) = 4 := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : hsZQ z ≤ hsQ z)).toEquiv,
    ZQ_subgroupOf_eq_center, card_center_of_isZ4Q8Q8 h.one.fstar]

theorem z_mem_ZQ [Finite G] (h : HSSetting z V) : z ∈ hsZQ z :=
  ⟨h.mem_Q, Subgroup.mem_centralizer_iff.mpr fun _ hq => h.comm_z_of_mem_Q hq⟩

theorem eq_z_of_mem_ZQ [Finite G] (h : HSSetting z V) {x : G} (hx : x ∈ hsZQ z)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = z := by
  have hc : ∀ (u : G) (hu : u ∈ hsZQ z), ∀ w : ↥(hsQ z),
      (⟨u, hu.1⟩ : ↥(hsQ z)) * w = w * ⟨u, hu.1⟩ :=
    fun u hu w => Subtype.ext ((Subgroup.mem_centralizer_iff.mp hu.2 w w.2).symm)
  have := eq_of_central_of_isZ4Q8Q8 h.one.fstar (hc x hx) (Subtype.ext hx2)
    (fun h1 => hx1 (congrArg Subtype.val h1)) (hc z h.z_mem_ZQ)
    (Subtype.ext (by rw [← sq]; exact h.sq_z)) (fun h1 => h.z_ne_one (congrArg Subtype.val h1))
  exact congrArg Subtype.val this

theorem _root_.CFSG.Quasithin.HSType.hsH_le_normalizer_hsZQ (z : G) :
    hsH z ≤ Subgroup.normalizer (hsZQ z : Set G) := by
  have hQ := le_normalizer_quasithinGenFitting (hsH z)
  have key : ∀ g ∈ hsH z, ∀ x ∈ hsZQ z, g * x * g⁻¹ ∈ hsZQ z := by
    intro g hg x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hQ hg) x).mp hx.1,
      Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ hsQ z := by
      have := (Subgroup.mem_normalizer_iff.mp (hQ ((hsH z).inv_mem hg)) q).mp hq
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hq'
    calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * q := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ ((hsH z).inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem H_le_normalizer_ZQ (_h : HSSetting z V) :
    hsH z ≤ Subgroup.normalizer (hsZQ z : Set G) :=
  hsH_le_normalizer_hsZQ z

theorem z_eq_or_sq_of_mem_ZQ [Finite G] (h : HSSetting z V) {x : G} (hx : x ∈ hsZQ z)
    (hx1 : x ≠ 1) : z = x ∨ z = x * x := by
  have h4 : x * x * (x * x) = 1 := by
    have := pow_card_eq_one' (G := ↥(hsZQ z)) (x := ⟨x, hx⟩)
    rw [h.card_ZQ] at this
    have h' := congrArg Subtype.val this
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h'
    rw [← h']
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  by_cases hxx : x * x = 1
  · exact Or.inl (h.eq_z_of_mem_ZQ hx hxx hx1).symm
  · exact Or.inr (h.eq_z_of_mem_ZQ ((hsZQ z).mul_mem hx hx) h4 hxx).symm

theorem mem_conjugate_iff' {K : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate K g ↔ g * x * g⁻¹ ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem conjugate_ZQ_eq_of_ne_bot [Finite G] (h : HSSetting z V) {g : G}
    (hg : hsZQ z ⊓ CFSG.conjugate (hsZQ z) g ≠ ⊥) : CFSG.conjugate (hsZQ z) g = hsZQ z := by
  obtain ⟨⟨x, hxZ, hxZg⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hgx : g * x * g⁻¹ ∈ hsZQ z := mem_conjugate_iff'.mp hxZg
  have hgx1 : g * x * g⁻¹ ≠ 1 := by
    intro h1
    apply hx1'
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
  have hgz : g * z * g⁻¹ = z := by
    have hsq : (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    have hne : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply h.z_ne_one
      have hz : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [hz, h1]
      group
    rcases h.z_eq_or_sq_of_mem_ZQ hxZ hx1' with h1 | h1 <;>
      rcases h.z_eq_or_sq_of_mem_ZQ hgx hgx1 with h2 | h2
    · calc g * z * g⁻¹ = g * x * g⁻¹ := by rw [← h1]
        _ = z := h2.symm
    · exfalso
      apply h.z_ne_one
      calc z = g * (x * x) * g⁻¹ := by rw [h2, hsq]
        _ = 1 := by rw [← h1, hzz, mul_one, mul_inv_cancel]
    · exfalso
      apply hne
      calc g * z * g⁻¹ = g * (x * x) * g⁻¹ := by rw [h1]
        _ = z * z := by rw [← hsq, ← h2]
        _ = 1 := hzz
    · calc g * z * g⁻¹ = g * (x * x) * g⁻¹ := by rw [h1]
        _ = z := by rw [← hsq, ← h2]
  have hgH : g ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hgz])
  ext x
  rw [mem_conjugate_iff']
  exact ((Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_ZQ hgH) x)).symm

theorem ZQ_le_centralizer_of_three [Finite G] (h : HSSetting z V) {y : G} (hyH : y ∈ hsH z)
    (hy : y ^ 3 = 1) : hsZQ z ≤ Subgroup.centralizer ({y} : Set G) := by
  have hmod := card_modEq_card_inf_centralizer hy (h.H_le_normalizer_ZQ hyH)
  rw [h.card_ZQ] at hmod
  set C := hsZQ z ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hzC : Subgroup.zpowers z ≤ C := (Subgroup.zpowers_le).mpr
    ⟨h.z_mem_ZQ, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hyH).symm⟩
  have h2 : 2 ≤ Nat.card C := by
    have := Subgroup.card_le_of_le hzC
    rwa [Nat.card_zpowers, h.orderOf_z] at this
  have hdvd : Nat.card C ∣ 4 := h.card_ZQ ▸ Subgroup.card_dvd_of_le inf_le_left
  have h4 : Nat.card C = 4 := by
    have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card C
    · simp [Nat.ModEq] at hmod
    · simp at hdvd
    · rfl
  have hCZ : C = hsZQ z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, h.card_ZQ])
  rw [← hCZ]
  exact inf_le_right

theorem inf_centralizer_V_eq_of_three [Finite G] (h : HSSetting z V) {y : G} (hyH : y ∈ hsH z)
    (hyM : y ∈ hsM V) (hy : orderOf y = 3) :
    V ⊓ Subgroup.centralizer ({y} : Set G) = Subgroup.zpowers z := by
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hmod := card_modEq_card_inf_centralizer hy3 hyM
  rw [h.card_V] at hmod
  set C := V ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hzC : Subgroup.zpowers z ≤ C := (Subgroup.zpowers_le).mpr
    ⟨h.mem_V, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hyH).symm⟩
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, h.orderOf_z]
  have h2 : 2 ≤ Nat.card C := hz2 ▸ Subgroup.card_le_of_le hzC
  have hdvd : Nat.card C ∣ 8 := h.card_V ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne8 : Nat.card C ≠ 8 := by
    intro h8
    have hCV : C = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.card_V])
    have hyP : y ∈ hsP V := by
      rw [← h.centralizer_V_eq]
      refine ⟨hyM, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have : v ∈ C := hCV ▸ hv
      exact Subgroup.mem_centralizer_singleton_iff.mp this.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (h.isPGroup_P ⟨y, hyP⟩)
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have := orderOf_dvd_of_pow_eq_one hyk
    rw [hy] at this
    have h3 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
    norm_num at h3
  have h2' : Nat.card C = 2 := by
    have hle : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card C <;> simp_all [Nat.ModEq]
  exact (Subgroup.eq_of_le_of_card_ge hzC (by rw [h2', hz2])).symm

theorem centralizer_Q_eq_ZQ_of_three [Finite G] (h : HSSetting z V) {y : G} (hyH : y ∈ hsH z)
    (hyM : y ∈ hsM V) (hy : orderOf y = 3) :
    hsQ z ⊓ Subgroup.centralizer ({y} : Set G) = hsZQ z := by
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hyQ : y ∈ Subgroup.normalizer (hsQ z : Set G) := le_normalizer_quasithinGenFitting _ hyH
  have hmod := card_modEq_card_inf_centralizer hy3 hyQ
  rw [h.card_Q] at hmod
  set C := hsQ z ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hZC : hsZQ z ≤ C := le_inf inf_le_left (h.ZQ_le_centralizer_of_three hyH hy3)
  have h4 : 4 ≤ Nat.card C := h.card_ZQ ▸ Subgroup.card_le_of_le hZC
  have hdvd : Nat.card C ∣ 64 := h.card_Q ▸ Subgroup.card_dvd_of_le inf_le_left
  have hcV := h.inf_centralizer_V_eq_of_three hyH hyM hy
  have hne64 : Nat.card C ≠ 64 := by
    intro h64
    have hCQ : C = hsQ z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h64, h.card_Q])
    have hyQ' : y ∈ hsQ z := by
      refine centralizer_quasithinGenFitting_le (hsH z) ⟨hyH, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hCQ ▸ hq : q ∈ C).2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 (hsQ z) := IsPGroup.of_card (n := 6) (by rw [h.card_Q]; norm_num)
    obtain ⟨k, hk⟩ := hQp ⟨y, hyQ'⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have := orderOf_dvd_of_pow_eq_one hyk
    rw [hy] at this
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    norm_num at h3
  have hne16 : Nat.card C ≠ 16 := by
    intro h16
    have hCV : C ⊓ V = Subgroup.zpowers z := by
      rw [← hcV]
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨h.two.le hx.1, hx.2⟩, hx.1⟩⟩
    have hCN : C ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans h.Q_le_M
    have hprod := card_sup_mul_card_inf_of_le_normalizer hCN
    rw [hCV, Nat.card_zpowers, h.orderOf_z, h16, h.card_V] at hprod
    have hsupQ : C ⊔ V = hsQ z := Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left h.two.le)
      (by rw [h.card_Q]; omega)
    have hcomm : ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ hsZQ z := by
      intro v hv
      have hyvV : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyM v).mp hv
      have hwV : y * v * y⁻¹ * v⁻¹ ∈ V := V.mul_mem hyvV (V.inv_mem hv)
      have hwQ : y * v * y⁻¹ * v⁻¹ ∈ hsQ z := h.two.le hwV
      refine ⟨hwQ, ?_⟩
      have hle : C ⊔ V ≤ Subgroup.centralizer ({y * v * y⁻¹ * v⁻¹} : Set G) := by
        refine sup_le (fun c hc => ?_) (fun u hu => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hcy : Commute c y := Subgroup.mem_centralizer_singleton_iff.mp hc.2
          have hzc : c * z = z * c := h.comm_z_of_mem_Q hc.1
          have hyz : Commute y z := Subgroup.mem_centralizer_singleton_iff.mp hyH
          rcases h.mul_comm_or_mul_z hc.1 (h.two.le hv) with hcv | hcv
          ·
            have hcv' : Commute c v := hcv
            exact ((hcy.mul_right hcv').mul_right hcy.inv_right).mul_right hcv'.inv_right
          ·
            have hcv' : c * v * c⁻¹ = v * z := by
              rw [hcv]
              calc v * c * z * c⁻¹ = v * (c * z * c⁻¹) := by group
                _ = v * z := by rw [hzc, mul_inv_cancel_right]
            have hcy' : c * y * c⁻¹ = y := by rw [hcy.eq, mul_inv_cancel_right]
            have hyzi : z * y⁻¹ = y⁻¹ * z := hyz.inv_left.eq.symm
            have key : c * (y * v * y⁻¹ * v⁻¹) * c⁻¹ = y * v * y⁻¹ * v⁻¹ := by
              calc c * (y * v * y⁻¹ * v⁻¹) * c⁻¹
                  = (c * y * c⁻¹) * (c * v * c⁻¹) * (c * y * c⁻¹)⁻¹ * (c * v * c⁻¹)⁻¹ := by
                    group
                _ = y * (v * z) * y⁻¹ * (v * z)⁻¹ := by rw [hcy', hcv']
                _ = y * v * (z * y⁻¹) * z⁻¹ * v⁻¹ := by group
                _ = y * v * (y⁻¹ * z) * z⁻¹ * v⁻¹ := by rw [hyzi]
                _ = y * v * y⁻¹ * v⁻¹ := by group
            calc c * (y * v * y⁻¹ * v⁻¹) = c * (y * v * y⁻¹ * v⁻¹) * c⁻¹ * c := by group
              _ = y * v * y⁻¹ * v⁻¹ * c := by rw [key]
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (h.elem.1.is_comm.comm ⟨u, hu⟩ ⟨_, hwV⟩)
      refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
      have hq' : q ∈ C ⊔ V := hsupQ ▸ hq
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hq')
    have hyV : ∀ v ∈ V, y * v * y⁻¹ = v := by
      intro v hv
      have hz : ∀ u ∈ V, y * u * y⁻¹ = u ∨ y * u * y⁻¹ = u * z := by
        intro u hu
        have hw := hcomm u hu
        have hwV : y * u * y⁻¹ * u⁻¹ ∈ V :=
          V.mul_mem ((Subgroup.mem_normalizer_iff.mp hyM u).mp hu) (V.inv_mem hu)
        by_cases hw1 : y * u * y⁻¹ * u⁻¹ = 1
        · left
          rw [mul_inv_eq_one] at hw1
          exact hw1
        · right
          have hw2 : y * u * y⁻¹ * u⁻¹ * (y * u * y⁻¹ * u⁻¹) = 1 := by
            have := h.elem.2 _ hwV
            rwa [sq] at this
          have := h.eq_z_of_mem_ZQ hw hw2 hw1
          rw [← this]
          have hcomm' : u * z = z * u := by
            have := h.comm_z_of_mem_Q (h.two.le hu)
            exact this
          calc y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u := by group
            _ = u * (y * u * y⁻¹ * u⁻¹) := by
              rw [this, hcomm']
      rcases hz v hv with h1 | h1
      · exact h1
      · exfalso
        have hyz : y * z * y⁻¹ = z := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hyH, mul_inv_cancel_right]
        have h2 : (y * y) * v * (y * y)⁻¹ = v * z * z := by
          calc (y * y) * v * (y * y)⁻¹ = y * (y * v * y⁻¹) * y⁻¹ := by group
            _ = y * (v * z) * y⁻¹ := by rw [h1]
            _ = (y * v * y⁻¹) * (y * z * y⁻¹) := by group
            _ = v * z * z := by rw [h1, hyz]
        have h3 : (y * y * y) * v * (y * y * y)⁻¹ = v * z * z * z := by
          calc (y * y * y) * v * (y * y * y)⁻¹ = y * ((y * y) * v * (y * y)⁻¹) * y⁻¹ := by
                group
            _ = y * (v * z * z) * y⁻¹ := by rw [h2]
            _ = (y * v * y⁻¹) * (y * z * y⁻¹) * (y * z * y⁻¹) := by group
            _ = v * z * z * z := by rw [h1, hyz]
        have hyyy : y * y * y = 1 := by rw [← hy3, pow_succ, pow_succ, pow_one]
        rw [hyyy, one_mul, inv_one, mul_one] at h3
        have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
        rw [mul_assoc, mul_assoc, hzz, mul_one] at h3
        apply h.z_ne_one
        have := congrArg (v⁻¹ * ·) h3
        simpa using this.symm
    have hVC : V ≤ V ⊓ Subgroup.centralizer ({y} : Set G) := fun v hv =>
      ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := hyV v hv
        calc v * y = y * v * y⁻¹ * y := by rw [this]
          _ = y * v := by group)⟩
    rw [hcV] at hVC
    have := Subgroup.card_le_of_le hVC
    rw [h.card_V, Nat.card_zpowers, h.orderOf_z] at this
    omega
  have h4' : Nat.card C = 4 := by
    have hle : Nat.card C ≤ 64 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : Nat.card C = 4 ∨ Nat.card C = 8 ∨ Nat.card C = 16 ∨ Nat.card C = 32 ∨
        Nat.card C = 64 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp
        (show Nat.card C ∣ 2 ^ 6 by simpa using hdvd)
      rw [hk] at h4 ⊢
      have hk6 : k ≤ 6 := by
        by_contra hk6
        have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ k ≤ 64 := hk ▸ hle
        omega
      interval_cases k <;> simp_all
    rcases hcases with h | h | h | h | h
    · exact h
    · rw [h] at hmod; simp [Nat.ModEq] at hmod
    · exact absurd h hne16
    · rw [h] at hmod; simp [Nat.ModEq] at hmod
    · exact absurd h hne64
  exact (Subgroup.eq_of_le_of_card_ge hZC (by rw [h4', h.card_ZQ])).symm

end HSSetting

end CFSG.Quasithin.HSType
