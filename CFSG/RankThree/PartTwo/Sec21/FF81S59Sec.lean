module

public import CFSG.RankThree.PartTwo.Sec21.FF81S59Twist
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.GroupTheory.CoprimeSectionStability

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59

open CFSG.RankThree.PartTwo.Sec21.FF79

section Basic

variable {G : Type} [Group G]

theorem mem_nor_inf_cenS {T : Subgroup G} {n : G} (hn : n ∈ Nor T) : n ∈ Nor (T ⊓ CenS T) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ m ∈ Nor T, ∀ x ∈ T ⊓ CenS T, m * x * m⁻¹ ∈ T ⊓ CenS T := by
    intro m hm x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hm x).mp hx.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    have ht' : m⁻¹ * t * m ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) t).mp ht
      rwa [inv_inv] at this
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ ht'
    calc t * (m * x * m⁻¹) = m * ((m⁻¹ * t * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * t * m)) * m⁻¹ := by rw [h1]
      _ = m * x * m⁻¹ * t := by group
  constructor
  · intro hx
    exact key n hn x hx
  · intro hx
    have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
    rwa [inv_inv, show n⁻¹ * (n * x * n⁻¹) * n = x by group] at this

theorem centralizer_zpowers_eq (γ : G) :
    Subgroup.centralizer ((Subgroup.zpowers γ : Subgroup G) : Set G) =
      Subgroup.centralizer ({γ} : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · intro h
    exact h γ (Subgroup.mem_zpowers γ)
  · intro h d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact (Commute.zpow_left (show Commute γ x from h) k).eq

theorem comm_zpowers_iff {Z : Subgroup G} {γ u : G} (hγ : γ ∈ Nor Z) :
    (∀ d ∈ Subgroup.zpowers γ, d * u * d⁻¹ * u⁻¹ ∈ Z) ↔ γ * u * γ⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h
    exact h γ (Subgroup.mem_zpowers γ)
  · intro h
    let S : Subgroup G :=
      { carrier := {d | d ∈ Nor Z ∧ d * u * d⁻¹ * u⁻¹ ∈ Z}
        mul_mem' := by
          rintro d e ⟨hd, hdz⟩ ⟨he, hez⟩
          refine ⟨Subgroup.mul_mem _ hd he, ?_⟩
          have h1 : d * (e * u * e⁻¹ * u⁻¹) * d⁻¹ ∈ Z :=
            (Subgroup.mem_normalizer_iff.mp hd _).mp hez
          have := Z.mul_mem h1 hdz
          rwa [show d * (e * u * e⁻¹ * u⁻¹) * d⁻¹ * (d * u * d⁻¹ * u⁻¹) =
            d * e * u * (d * e)⁻¹ * u⁻¹ by group] at this
        one_mem' := ⟨Subgroup.one_mem _, by simpa using Z.one_mem⟩
        inv_mem' := by
          rintro d ⟨hd, hdz⟩
          refine ⟨Subgroup.inv_mem _ hd, ?_⟩
          have h1 : d⁻¹ * (d * u * d⁻¹ * u⁻¹)⁻¹ * d⁻¹⁻¹ ∈ Z :=
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) _).mp (Z.inv_mem hdz)
          rwa [show d⁻¹ * (d * u * d⁻¹ * u⁻¹)⁻¹ * d⁻¹⁻¹ = d⁻¹ * u * d⁻¹⁻¹ * u⁻¹ by group] at h1 }
    have hle : Subgroup.zpowers γ ≤ S := Subgroup.zpowers_le.mpr ⟨hγ, h⟩
    intro d hd
    exact (hle hd).2

end Basic

section Setup

variable {G : Type} [Group G] [Finite G]

structure TSetup (T : Subgroup G) (γ h₁ h₂ : G) : Prop where
  card_T : Nat.card T = 2 ^ 15
  card_Z : Nat.card ↥(T ⊓ CenS T) = 2 ^ 7
  sq_Z : ∀ z ∈ T ⊓ CenS T, z ^ 2 = 1
  sq_mem : ∀ u ∈ T, u ^ 2 ∈ T ⊓ CenS T
  comm_mem : ∀ u ∈ T, ∀ v ∈ T, u * v * u⁻¹ * v⁻¹ ∈ T ⊓ CenS T
  γT : γ ∈ Nor T
  h₁T : h₁ ∈ Nor T
  h₂T : h₂ ∈ Nor T
  γ7 : γ ^ 7 = 1
  hh₁ : h₁ * γ * h₁⁻¹ = γ ^ 3
  hh₂ : h₂ * γ * h₂⁻¹ = γ ^ 5
  nt1 : ∃ z ∈ T ⊓ CenS T, γ * z ≠ z * γ
  nt2 : ∃ u ∈ T, γ * u * γ⁻¹ * u⁻¹ ∉ T ⊓ CenS T

variable {T : Subgroup G} {γ h₁ h₂ : G}

theorem TSetup.isPGroup (h : TSetup T γ h₁ h₂) : IsPGroup 2 T :=
  IsPGroup.of_card (n := 15) h.card_T

theorem TSetup.orderOf_γ (h : TSetup T γ h₁ h₂) : orderOf γ = 7 := by
  have hd : orderOf γ ∣ 7 := orderOf_dvd_of_pow_eq_one h.γ7
  rcases (Nat.dvd_prime (by norm_num)).mp hd with h1 | h7
  · exfalso
    obtain ⟨z, -, hz⟩ := h.nt1
    apply hz
    rw [orderOf_eq_one_iff.mp h1, one_mul, mul_one]
  · exact h7

theorem le_nor_inf_cenS : T ≤ Nor (T ⊓ CenS T) := fun t ht =>
  mem_nor_inf_cenS (Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => by
    have := T.mul_mem (T.mul_mem ht hx) (T.inv_mem ht)
    exact this, fun hx => by
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) hx) ht
    simpa [mul_assoc] using this⟩)

theorem mem_Cbar (h : TSetup T γ h₁ h₂) {n : G} :
    n ∈ (T ⊓ Cen γ) ⊔ (T ⊓ CenS T) ↔ n ∈ T ∧ γ * n * γ⁻¹ * n⁻¹ ∈ T ⊓ CenS T := by
  have hZT : T ⊓ CenS T ≤ T := inf_le_left
  have hle : (T ⊓ Cen γ) ⊔ (T ⊓ CenS T) ≤ T := sup_le inf_le_left hZT
  have hγZ : γ ∈ Nor (T ⊓ CenS T) := mem_nor_inf_cenS h.γT
  have hord : Nat.card (Subgroup.zpowers γ) = 7 := by rw [Nat.card_zpowers, h.orderOf_γ]
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers γ)) (Nat.card T) := by
    rw [hord, h.card_T]
    exact Nat.Coprime.pow_right _ (by norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable ↥T := by
    haveI : Group.IsNilpotent ↥T := h.isPGroup.isNilpotent
    infer_instance
  have hDN : Subgroup.zpowers γ ≤ Nor T := Subgroup.zpowers_le.mpr h.γT
  have hDM : Subgroup.zpowers γ ≤ Nor (T ⊓ CenS T) := Subgroup.zpowers_le.mpr hγZ
  constructor
  · intro hn
    have hnT : n ∈ T := hle hn
    refine ⟨hnT, ?_⟩
    have := (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff hZT le_nor_inf_cenS hDN hDM
      hcop hsolv hnT).mpr (by rw [centralizer_zpowers_eq, ← Cen]; exact hn)
    exact (comm_zpowers_iff hγZ).mp this
  · rintro ⟨hnT, hn⟩
    have := (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff hZT le_nor_inf_cenS hDN hDM
      hcop hsolv hnT).mp ((comm_zpowers_iff hγZ).mpr hn)
    rwa [centralizer_zpowers_eq, ← Cen] at this

end Setup

section Inn

variable {G : Type} [Group G] [Finite G] {T : Subgroup G} {γ h₁ h₂ : G}

theorem center_eq : Subgroup.center ↥T = (T ⊓ CenS T).subgroupOf T := by
  ext x
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨x.2, fun y hy => ?_⟩
    exact congrArg Subtype.val (h ⟨y, hy⟩)
  · rintro ⟨-, h⟩ y
    exact Subtype.ext (h y y.2)

theorem mem_center_iff' {x : ↥T} : x ∈ Subgroup.center ↥T ↔ (x : G) ∈ T ⊓ CenS T := by
  rw [center_eq, Subgroup.mem_subgroupOf]

theorem relIndex_Cbar (h : TSetup T γ h₁ h₂) :
    ((T ⊓ Cen γ) ⊔ (T ⊓ CenS T)).relIndex T = 64 := by
  haveI : Finite (MulAut ↥T) :=
    Finite.of_injective (fun f : MulAut ↥T => (f : ↥T → ↥T)) DFunLike.coe_injective
  set π : ↥T →* MulAut ↥T := MulAut.conj with hπ
  set E : Subgroup (MulAut ↥T) := π.range with hE
  have hker : π.ker = Subgroup.center ↥T := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      have := congrArg (fun α : MulAut ↥T => α y) hx
      simp only [hπ, MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · intro hx
      refine MulEquiv.ext fun y => ?_
      simp only [hπ, MulAut.conj_apply, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (hx y).symm
  have hcardZ : Nat.card (Subgroup.center ↥T) = 2 ^ 7 := by
    rw [center_eq, ← h.card_Z]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardE : Nat.card E = 2 ^ 8 := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [hker, hcardZ, h.card_T] at h1
    have h2 : 2 ^ 7 * Nat.card E = 2 ^ 7 * 2 ^ 8 := by rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hconj : ∀ (α : MulAut ↥T) (u : ↥T), α * π u * α⁻¹ = π (α u) := by
    intro α u
    refine MulEquiv.ext fun x => ?_
    simp [hπ, MulAut.conj_apply]
  have hnor : ∀ α : MulAut ↥T, α ∈ Subgroup.normalizer (E : Set (MulAut ↥T)) := by
    intro α
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨α u, (hconj α u).symm⟩
    · rintro ⟨v, hv⟩
      refine ⟨α⁻¹ v, ?_⟩
      have h1 := hconj α⁻¹ v
      rw [hv] at h1
      calc π (α⁻¹ v) = α⁻¹ * (α * x * α⁻¹) * α⁻¹⁻¹ := h1.symm
        _ = x := by group
  have hsqZ : ∀ u : ↥T, u ^ 2 ∈ Subgroup.center ↥T := fun u =>
    mem_center_iff'.mpr (h.sq_mem (u : G) u.2)
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (hker ▸ hsqZ u)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have hc : u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center ↥T :=
      mem_center_iff'.mpr (h.comm_mem (u : G) u.2 (v : G) v.2)
    have h1 : π (u * v * u⁻¹ * v⁻¹) = 1 := MonoidHom.mem_ker.mp (hker ▸ hc)
    have h2 : π u * π v * (π u)⁻¹ * (π v)⁻¹ = 1 := by simpa [map_mul, map_inv] using h1
    calc π u * π v = (π u * π v * (π u)⁻¹ * (π v)⁻¹) * (π v * π u) := by group
      _ = π v * π u := by rw [h2, one_mul]
  let gh : MulAut ↥T := T.normalizerMonoidHom ⟨γ, h.γT⟩
  let hh₁ : MulAut ↥T := T.normalizerMonoidHom ⟨h₁, h.h₁T⟩
  let hh₂ : MulAut ↥T := T.normalizerMonoidHom ⟨h₂, h.h₂T⟩
  have hgh7 : gh ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨γ, h.γT⟩ : ↥(Subgroup.normalizer (T : Set G))) ^ 7 = 1 :=
      Subtype.ext (by simpa using h.γ7)
    rw [this, map_one]
  have hhh₁ : hh₁ * gh * hh₁⁻¹ = gh ^ 3 := by
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using h.hh₁)
  have hhh₂ : hh₂ * gh * hh₂⁻¹ = gh ^ 5 := by
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using h.hh₂)
  obtain ⟨j, hj⟩ := twist_sub E hE2 hEc (hnor gh) (hnor hh₁) (hnor hh₂) hgh7 hhh₁ hhh₂
  have hghu : ∀ u : ↥T, ((gh u : ↥T) : G) = γ * (u : G) * γ⁻¹ := fun u => rfl
  have hfix : ∀ u : ↥T, π u ∈ Subgroup.centralizer ({gh} : Set (MulAut ↥T)) ↔
      γ * (u : G) * γ⁻¹ * (u : G)⁻¹ ∈ T ⊓ CenS T := by
    intro u
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hconj gh u
    have h2 : π (gh u) = π u ↔ π (gh u * u⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
    have h3 : π (gh u * u⁻¹) = 1 ↔ γ * (u : G) * γ⁻¹ * (u : G)⁻¹ ∈ T ⊓ CenS T := by
      rw [← MonoidHom.mem_ker, hker, mem_center_iff']
      rfl
    rw [← h3, ← h2, ← h1]
    constructor
    · intro hc
      rw [← hc, mul_inv_cancel_right]
    · intro hc
      calc π u * gh = (gh * π u * gh⁻¹) * gh := by rw [hc]
        _ = gh * π u := by group
  have hcardc : Nat.card ↥(E ⊓ Subgroup.centralizer ({gh} : Set (MulAut ↥T))) = 4 := by
    obtain ⟨u, huT, hu⟩ := h.nt2
    have hne : π ⟨u, huT⟩ ∉ Subgroup.centralizer ({gh} : Set (MulAut ↥T)) := fun hmem =>
      hu ((hfix ⟨u, huT⟩).mp hmem)
    have hpos : 0 < Nat.card ↥(E ⊓ Subgroup.centralizer ({gh} : Set (MulAut ↥T))) :=
      Nat.card_pos
    rw [hcardE] at hj
    rcases j with _ | _ | j
    · exfalso
      rw [pow_zero, mul_one] at hj
      have hle : E ⊓ Subgroup.centralizer ({gh} : Set (MulAut ↥T)) ≤ E := inf_le_left
      have heq : E ⊓ Subgroup.centralizer ({gh} : Set (MulAut ↥T)) = E :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcardE]; exact hj.le)
      apply hne
      have : π ⟨u, huT⟩ ∈ E := ⟨⟨u, huT⟩, rfl⟩
      rw [← heq] at this
      exact this.2
    · rw [zero_add, pow_one] at hj
      omega
    · exfalso
      have h64 : 64 ^ (j + 1 + 1) ≥ 4096 := by
        calc 64 ^ (j + 1 + 1) ≥ 64 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4096 := by norm_num
      have h4 : Nat.card ↥(E ⊓ Subgroup.centralizer ({gh} : Set (MulAut ↥T))) *
          64 ^ (j + 1 + 1) ≥ 1 * 4096 := Nat.mul_le_mul hpos h64
      have h5 : (2 : ℕ) ^ 8 = 256 := by norm_num
      rw [h5] at hj
      omega
  have hCb : ((T ⊓ Cen γ) ⊔ (T ⊓ CenS T)).subgroupOf T =
      (Subgroup.centralizer ({gh} : Set (MulAut ↥T))).comap π := by
    ext u
    rw [Subgroup.mem_subgroupOf, mem_Cbar h, Subgroup.mem_comap, hfix]
    exact ⟨fun hh => hh.2, fun hh => ⟨u.2, hh⟩⟩
  have hmap : Subgroup.map π ⊤ = E := by rw [← MonoidHom.range_eq_map]
  have hidx := Subgroup.relIndex_mul_card (Subgroup.centralizer ({gh} : Set (MulAut ↥T))) E
  rw [inf_comm, hcardc, hcardE] at hidx
  rw [Subgroup.relIndex, hCb, ← Subgroup.relIndex_top_right, Subgroup.relIndex_comap, hmap]
  omega

end Inn

section Final

variable {G : Type} [Group G] [Finite G] {T : Subgroup G} {γ h₁ h₂ : G}

theorem card_Z_cen (h : TSetup T γ h₁ h₂) :
    Nat.card ↥((T ⊓ CenS T) ⊓ Cen γ) = 2 := by
  have hEc : ∀ x ∈ T ⊓ CenS T, ∀ y ∈ T ⊓ CenS T, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  obtain ⟨j, hj⟩ := twist_sub (T ⊓ CenS T) h.sq_Z hEc (mem_nor_inf_cenS h.γT)
    (mem_nor_inf_cenS h.h₁T) (mem_nor_inf_cenS h.h₂T) h.γ7 h.hh₁ h.hh₂
  obtain ⟨z, hzZ, hz⟩ := h.nt1
  have hne : z ∉ Cen γ := fun hmem =>
    hz (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
  have hpos : 0 < Nat.card ↥((T ⊓ CenS T) ⊓ Cen γ) := Nat.card_pos
  change Nat.card ↥(T ⊓ CenS T) = Nat.card ↥((T ⊓ CenS T) ⊓ Cen γ) * 64 ^ j at hj
  rw [h.card_Z] at hj
  rcases j with _ | _ | j
  · exfalso
    rw [pow_zero, mul_one] at hj
    have hle : (T ⊓ CenS T) ⊓ Cen γ ≤ T ⊓ CenS T := inf_le_left
    have heq : (T ⊓ CenS T) ⊓ Cen γ = T ⊓ CenS T :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_Z]; exact hj.le)
    apply hne
    rw [← heq] at hzZ
    exact hzZ.2
  · rw [zero_add, pow_one] at hj
    omega
  · exfalso
    have h64 : 64 ^ (j + 1 + 1) ≥ 4096 := by
      calc 64 ^ (j + 1 + 1) ≥ 64 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4096 := by norm_num
    have h4 : Nat.card ↥((T ⊓ CenS T) ⊓ Cen γ) * 64 ^ (j + 1 + 1) ≥ 1 * 4096 :=
      Nat.mul_le_mul hpos h64
    have h5 : (2 : ℕ) ^ 7 = 128 := by norm_num
    rw [h5] at hj
    omega

theorem card_T_cen (h : TSetup T γ h₁ h₂) : Nat.card ↥(T ⊓ Cen γ) = 8 := by
  have hZT : T ⊓ CenS T ≤ T := inf_le_left
  have hZ := card_Z_cen h
  have hZidx : ((T ⊓ CenS T) ⊓ Cen γ).relIndex (T ⊓ CenS T) = 64 := by
    have := Subgroup.relIndex_mul_card ((T ⊓ CenS T) ⊓ Cen γ) (T ⊓ CenS T)
    rw [inf_of_le_left (inf_le_left : (T ⊓ CenS T) ⊓ Cen γ ≤ T ⊓ CenS T), hZ, h.card_Z] at this
    omega
  have hCb := relIndex_Cbar h
  have hmul := CFSG.GroupTheory.CoprimeSection.index_centralizer_mul
    (D := Subgroup.zpowers γ) (N := T) (M := T ⊓ CenS T) hZT le_nor_inf_cenS
  rw [centralizer_zpowers_eq] at hmul
  have hTidx : (T ⊓ Cen γ).relIndex T = 64 * 64 := by
    rw [hmul, hZidx, hCb]
  have h1 := Subgroup.relIndex_mul_card (T ⊓ Cen γ) T
  rw [inf_of_le_left (inf_le_left : T ⊓ Cen γ ≤ T), hTidx, h.card_T] at h1
  have h2 : 4096 * Nat.card ↥(T ⊓ Cen γ) = 4096 * 8 := by
    have : (2 : ℕ) ^ 15 = 4096 * 8 := by norm_num
    rw [← this, ← h1]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

end Final

end CFSG.RankThree.PartTwo.Sec21.FF81.S59
