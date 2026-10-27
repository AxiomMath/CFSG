module

public import CFSG.Walter.ReeOrder.JT.PSL2
public import CFSG.GroupTheory.FourGroupOddOrderIdentity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.Walter.ReeOrder.JT.Defs

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem exists_normal_index_eq_of_commute_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : IsMulCommutative (P : Subgroup G)) {z : G} (hzP : z ∈ P)
    (hz1 : z ≠ 1) (hz : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n * z = z * n) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = p := by
  classical
  let φ : G →* P := MonoidHom.transfer (MonoidHom.id P)
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ hk
    obtain ⟨n, hn, heq⟩ := Sylow.conj_eq_normalizer_conj_of_mem P (z ^ k) g₀
      ((P : Subgroup G).pow_mem hzP k) hk
    rw [heq]
    have hc : Commute n (z ^ k) := Commute.pow_right (hz n hn) k
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hφz : φ z = ⟨z ^ (P : Subgroup G).index, _⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id P) z key
  have hφ1 : φ z ≠ 1 := by
    intro h
    rw [hφz] at h
    have h1 : z ^ (P : Subgroup G).index = 1 := congrArg Subtype.val h
    have h2 : orderOf z ∣ Nat.card (P : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hzP
    exact hz1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h2 P.card_coprime_index) (orderOf_dvd_of_pow_eq_one h1)))
  set A := φ.range
  have hAp : IsPGroup p A := P.isPGroup'.to_subgroup A
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    have h : φ z ∈ A := ⟨z, rfl⟩
    rw [hn] at h
    exact hφ1 (Subgroup.mem_bot.mp h)
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := n - 1)
    (hn ▸ pow_dvd_pow p (Nat.sub_le n 1))
  have hBidx : B.index = p := by
    have h := B.card_mul_index
    rw [hB, hn] at h
    have hp0 : 0 < p ^ (n - 1) := pow_pos (Fact.out : p.Prime).pos _
    have : p ^ n = p ^ (n - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_left hp0 h
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (mul_comm (a : P) b)⟩⟩
  refine ⟨B.comap φ.rangeRestrict, (Subgroup.normal_of_isMulCommutative B).comap _, ?_⟩
  rw [Subgroup.index_comap_of_surjective B φ.rangeRestrict_surjective, hBidx]

theorem inv_of_inf_centralizer_eq_bot [Finite G] {u : G} (hu : u * u = 1) {K : Subgroup G}
    (huK : u ∈ Subgroup.normalizer (K : Set G))
    (hfix : K ⊓ Subgroup.centralizer ({u} : Set G) = ⊥) :
    ∀ x ∈ K, u * x * u⁻¹ = x⁻¹ := by
  classical
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hconjK : ∀ x ∈ K, u * x * u⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp huK x).mp hx
  let φ : K → K := fun k => ⟨k⁻¹ * (u * k * u⁻¹), K.mul_mem (K.inv_mem k.2) (hconjK _ k.2)⟩
  have hφ : Function.Injective φ := by
    intro k l hkl
    have h : (k : G)⁻¹ * (u * k * u⁻¹) = (l : G)⁻¹ * (u * l * u⁻¹) := congrArg Subtype.val hkl
    have hm : (l : G) * (k : G)⁻¹ ∈ K ⊓ Subgroup.centralizer ({u} : Set G) := by
      refine ⟨K.mul_mem l.2 (K.inv_mem k.2), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h' : u * ((l : G) * (k : G)⁻¹) * u⁻¹ = (l : G) * (k : G)⁻¹ := by
        calc u * ((l : G) * (k : G)⁻¹) * u⁻¹ = (u * l * u⁻¹) * (u * k * u⁻¹)⁻¹ := by group
          _ = (l : G) * (k : G)⁻¹ := by
            have : u * (l : G) * u⁻¹ = l * ((k : G)⁻¹ * (u * k * u⁻¹)) := by
              rw [h]; group
            rw [this]; group
      calc ((l : G) * (k : G)⁻¹) * u = u * ((l : G) * (k : G)⁻¹) * u⁻¹ * u := by rw [h']
        _ = u * ((l : G) * (k : G)⁻¹) := by group
    rw [hfix, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact Subtype.ext hm.symm
  have hφs : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ
  intro x hx
  obtain ⟨k, hk⟩ := hφs ⟨x, hx⟩
  have hk' : (k : G)⁻¹ * (u * k * u⁻¹) = x := congrArg Subtype.val hk
  rw [← hk']
  rw [huinv, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, huinv]
  simp only [mul_assoc, hu, mul_one]

theorem le_centralizer_of_inv {u : G} {K : Subgroup G}
    (hinv : ∀ x ∈ K, u * x * u⁻¹ = x⁻¹) : K ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hinv _ (K.mul_mem hx hy)
  rw [show u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) by group, hinv x hx,
    hinv y hy, mul_inv_rev] at h1
  have := congrArg (·⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at this
  exact this

section BrauerWielandt

@[expose, reducible] def conjAct (V K : Subgroup G)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) : MulDistribMulAction V K where
  smul v k := ⟨v * k * (v : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hVK v.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by
    change ((1 : V) : G) * k * ((1 : V) : G)⁻¹ = k
    simp)
  mul_smul a b k := Subtype.ext (by
    change ((a : G) * b) * k * ((a : G) * b)⁻¹ = a * (b * k * (b : G)⁻¹) * (a : G)⁻¹
    group)
  smul_mul a x y := Subtype.ext (by
    change (a : G) * (x * y) * (a : G)⁻¹ = (a * x * (a : G)⁻¹) * (a * y * (a : G)⁻¹)
    group)
  smul_one a := Subtype.ext (by
    change (a : G) * 1 * (a : G)⁻¹ = 1
    group)

theorem inf_centralizer_zpowers (K : Subgroup G) (x : G) :
    K ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      K ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, h x (Subgroup.mem_zpowers x)⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left h k).eq)

theorem card_fixedPointSubgroup_conjAct (V K : Subgroup G)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (S : Subgroup V) :
    letI := conjAct V K hVK
    Nat.card (fixedPointSubgroup S K) =
      Nat.card (K ⊓ Subgroup.centralizer ((S.map V.subtype : Subgroup G) : Set G) :
        Subgroup G) := by
  let := conjAct V K hVK
  have key : (fixedPointSubgroup S K).map K.subtype =
      K ⊓ Subgroup.centralizer ((S.map V.subtype : Subgroup G) : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe, Subgroup.coe_subtype]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have h := congrArg Subtype.val (hk ⟨s, hs⟩)
      change (s : G) * k * (s : G)⁻¹ = k at h
      calc (s : G) * k = ((s : G) * k * (s : G)⁻¹) * s := by group
        _ = k * s := by rw [h]
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rintro ⟨s, hs⟩
      apply Subtype.ext
      change (s : G) * x * (s : G)⁻¹ = x
      rw [h _ ⟨s, hs, rfl⟩, mul_inv_cancel_right]
  rw [← key, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_fixedPointSubgroup_conjAct_top (V K : Subgroup G)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) :
    letI := conjAct V K hVK
    Nat.card (fixedPointSubgroup V K) =
      Nat.card (K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  let := conjAct V K hVK
  have key : (fixedPointSubgroup V K).map K.subtype =
      K ⊓ Subgroup.centralizer (V : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe, Subgroup.coe_subtype]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, fun s hs => ?_⟩
      have h := congrArg Subtype.val (hk ⟨s, hs⟩)
      change (s : G) * k * (s : G)⁻¹ = k at h
      calc (s : G) * k = ((s : G) * k * (s : G)⁻¹) * s := by group
        _ = k * s := by rw [h]
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rintro ⟨s, hs⟩
      apply Subtype.ext
      change (s : G) * x * (s : G)⁻¹ = x
      rw [h _ hs, mul_inv_cancel_right]
  rw [← key, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_mul_card_sq_eq_mul [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : Commute a b) (K : Subgroup G)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hK : Odd (Nat.card K)) :
    Nat.card K * Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) ⊓
        Subgroup.centralizer ({b} : Set G) : Subgroup G) ^ 2 =
      Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) *
        Nat.card (K ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) *
        Nat.card (K ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) := by
  classical
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hc
  have hV : IsKleinFour V :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hab hc
  have hmemV : ∀ x : G, x ∈ V ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := fun x => by
    change x ∈ ({a * b, a, b, 1} : Set G) ↔ _
    simp
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    rw [← mul_one a, ← h, ← mul_assoc, ha, one_mul]
  have haab : a ≠ a * b := by
    intro h
    apply hb1
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm
  have hbab : b ≠ a * b := by
    intro h
    apply ha1
    have := congrArg (· * b⁻¹) h
    simpa using this.symm
  have hVK : V ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rcases (hmemV x).mp hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ haK hbK
    · exact haK
    · exact hbK
    · exact Subgroup.one_mem _
  let := conjAct V K hVK
  let : Fintype V := Fintype.ofFinite V
  have h := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
    (A := V) (X := K) hK).1
  rw [card_fixedPointSubgroup_conjAct_top] at h
  set a' : V := ⟨a, (hmemV a).mpr (Or.inr (Or.inl rfl))⟩
  set b' : V := ⟨b, (hmemV b).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
  set c' : V := ⟨a * b, (hmemV _).mpr (Or.inl rfl)⟩
  have herase : Finset.univ.erase (1 : V) = {a', b', c'} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      rcases (hmemV x).mp x.2 with h1 | h1 | h1 | h1
      · exact Or.inr (Or.inr (Subtype.ext h1))
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Or.inl (Subtype.ext h1))
      · exact absurd (Subtype.ext h1) hx
    · rintro (rfl | rfl | rfl) h1
      · exact ha1 (congrArg Subtype.val h1)
      · exact hb1 (congrArg Subtype.val h1)
      · exact hab1 (congrArg Subtype.val h1)
  have hne1 : a' ≠ b' := fun h1 => hab (congrArg Subtype.val h1)
  have hne2 : a' ≠ c' := fun h1 => haab (congrArg Subtype.val h1)
  have hne3 : b' ≠ c' := fun h1 => hbab (congrArg Subtype.val h1)
  rw [herase, Finset.prod_insert (by simp [hne1, hne2]), Finset.prod_insert (by simp [hne3]),
    Finset.prod_singleton] at h
  have hcz : ∀ x : V, Nat.card (fixedPointSubgroup (Subgroup.zpowers x) K) =
      Nat.card (K ⊓ Subgroup.centralizer ({(x : G)} : Set G) : Subgroup G) := by
    intro x
    rw [card_fixedPointSubgroup_conjAct, MonoidHom.map_zpowers, inf_centralizer_zpowers]
    rfl
  rw [hcz, hcz, hcz] at h
  have hcV : K ⊓ Subgroup.centralizer (V : Set G) =
      K ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨hx, h1⟩
      exact ⟨⟨hx, h1 a ((hmemV a).mpr (Or.inr (Or.inl rfl)))⟩,
        h1 b ((hmemV b).mpr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · rintro ⟨⟨hx, h1⟩, h2⟩
      refine ⟨hx, fun y hy => ?_⟩
      rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
      · rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
      · exact h1
      · exact h2
      · simp
  rw [hcV] at h
  rw [h]
  ring

end BrauerWielandt

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G)

theorem q_eq : h.q = h.p ^ h.f := rfl

theorem t_mul_t : h.t * h.t = 1 := by
  rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]

theorem t_inv : h.t⁻¹ = h.t := inv_eq_of_mul_eq_one_right h.t_mul_t

theorem t_ne_one : h.t ≠ 1 := by
  intro h1
  have := h.orderOf_t
  rw [h1, orderOf_one] at this
  omega

theorem t_mem_centralizer : h.t ∈ Subgroup.centralizer ({h.t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem commute_of_mem {x : G} (hx : x ∈ Subgroup.centralizer ({h.t} : Set G)) :
    x * h.t = h.t * x :=
  Subgroup.mem_centralizer_singleton_iff.mp hx

theorem commute_of_mem_F {x : G} (hx : x ∈ h.F) : x * h.t = h.t * x :=
  h.commute_of_mem (h.le_centralizer hx)

theorem mem_centralizer_t {x : G} :
    x ∈ Subgroup.centralizer ({h.t} : Set G) ↔ x ∈ h.F ∨ h.t * x ∈ h.F := by
  constructor
  · intro hx
    let H : Subgroup G :=
      { carrier := {y | y ∈ h.F ∨ h.t * y ∈ h.F}
        one_mem' := Or.inl h.F.one_mem
        mul_mem' := by
          intro a b ha hb
          have hta : ∀ y ∈ h.F, h.t * y = y * h.t := fun y hy => (h.commute_of_mem_F hy).symm
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (h.F.mul_mem ha hb)
          · right
            have : h.t * (a * b) = a * (h.t * b) := by
              rw [← mul_assoc, hta a ha, mul_assoc]
            rw [this]
            exact h.F.mul_mem ha hb
          · right
            rw [← mul_assoc]
            exact h.F.mul_mem ha hb
          · left
            have hta' : h.t * a = a * h.t := by
              have := hta _ ha
              calc h.t * a = h.t * (h.t * (h.t * a)) := by
                    rw [← mul_assoc, h.t_mul_t, one_mul]
                _ = h.t * ((h.t * a) * h.t) := by rw [this]
                _ = a * h.t := by rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
            have : a * b = (h.t * a) * (h.t * b) := by
              rw [← mul_assoc, hta', mul_assoc a, h.t_mul_t, mul_one]
            rw [this]
            exact h.F.mul_mem ha hb
        inv_mem' := by
          intro a ha
          rcases ha with ha | ha
          · exact Or.inl (h.F.inv_mem ha)
          · right
            have hc : h.t * a = a * h.t := by
              have := (h.commute_of_mem_F ha)
              calc h.t * a = h.t * (h.t * (h.t * a)) := by
                    rw [← mul_assoc, h.t_mul_t, one_mul]
                _ = h.t * ((h.t * a) * h.t) := by rw [this]
                _ = a * h.t := by rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
            have : h.t * a⁻¹ = (h.t * a)⁻¹ := by
              rw [mul_inv_rev, h.t_inv]
              calc h.t * a⁻¹ = a⁻¹ * (a * h.t) * a⁻¹ := by group
                _ = a⁻¹ * (h.t * a) * a⁻¹ := by rw [hc]
                _ = a⁻¹ * h.t := by group
            rw [this]
            exact h.F.inv_mem ha }
    have hle : Subgroup.zpowers h.t ⊔ h.F ≤ H := by
      refine sup_le ?_ (fun y hy => Or.inl hy)
      rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [h.t_mul_t]; exact h.F.one_mem)
    rw [h.centralizer_eq] at hx
    exact hle hx
  · rintro (hx | hx)
    · exact h.le_centralizer hx
    · have : x = h.t * (h.t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ h.t_mem_centralizer (h.le_centralizer hx)

theorem mem_F_of_odd {x : G} (hx : x ∈ Subgroup.centralizer ({h.t} : Set G))
    (hodd : Odd (orderOf x)) : x ∈ h.F := by
  rcases h.mem_centralizer_t.mp hx with hx | hx
  · exact hx
  · exfalso
    set y := h.t * x
    have hxy : x = h.t * y := by rw [← mul_assoc, h.t_mul_t, one_mul]
    have hc : Commute h.t y := (h.commute_of_mem_F hx).symm
    obtain ⟨k, hk⟩ := hodd
    have h2 : h.t ^ 2 = 1 := by rw [← h.orderOf_t, pow_orderOf_eq_one]
    have h1 : (h.t * y) ^ (2 * k + 1) = 1 := by
      rw [← hk, ← hxy]
      exact pow_orderOf_eq_one x
    rw [hc.mul_pow, pow_succ h.t, pow_mul, h2, one_pow, one_mul] at h1
    apply h.t_not_mem
    have : h.t = (y ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact h.F.inv_mem (h.F.pow_mem hx _)

theorem le_F_of_odd {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({h.t} : Set G))
    (hodd : Odd (Nat.card K)) : K ≤ h.F := fun _ hx =>
  h.mem_F_of_odd (hK hx) (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K hx))

theorem facts
    (hp : h.p ≠ 2) : PSL2Facts h.F h.p h.f := psl2Facts h.F h.iso hp h.five_lt

theorem sylow_le_centralizer (S : Sylow 2 G) (htS : h.t ∈ S) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({h.t} : Set G) := by
  intro x hx
  have := h.abelian_sylow S
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨h.t, htS⟩))

@[expose] noncomputable def conj (g : G) : JTHyp G where
  p := h.p
  f := h.f
  five_lt := h.five_lt
  abelian_sylow := h.abelian_sylow
  index_ne_two := h.index_ne_two
  t := g * h.t * g⁻¹
  orderOf_t := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_t]
  F := h.F.map (MulAut.conj g).toMonoidHom
  le_centralizer := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g * x * g⁻¹ * (g * h.t * g⁻¹) = g * h.t * g⁻¹ * (g * x * g⁻¹)
    have := h.commute_of_mem_F hx
    calc g * x * g⁻¹ * (g * h.t * g⁻¹) = g * (x * h.t) * g⁻¹ := by group
      _ = g * (h.t * x) * g⁻¹ := by rw [this]
      _ = g * h.t * g⁻¹ * (g * x * g⁻¹) := by group
  t_not_mem := by
    rintro ⟨x, hx, hxt⟩
    apply h.t_not_mem
    have : x = h.t := by
      have := congrArg (fun y => g⁻¹ * y * g) hxt
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]
  centralizer_eq := by
    have := centralizer_singleton_map (MulAut.conj g) h.t
    rw [MulAut.conj_apply] at this
    rw [← this, h.centralizer_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  iso := (Subgroup.equivMapOfInjective h.F (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans h.iso

@[simp] theorem conj_t (g : G) : (h.conj g).t = g * h.t * g⁻¹ := rfl

@[simp] theorem conj_p (g : G) : (h.conj g).p = h.p := rfl

@[simp] theorem conj_f (g : G) : (h.conj g).f = h.f := rfl

@[simp] theorem conj_q (g : G) : (h.conj g).q = h.q := rfl

@[simp] theorem conj_eps (g : G) : (h.conj g).eps = h.eps := rfl

theorem conj_F (g : G) : (h.conj g).F = h.F.map (MulAut.conj g).toMonoidHom := rfl

end JTHyp

end CFSG.Walter.JT
