module

public import CFSG.Walter.J1.Basic

public section

namespace CFSG.Walter.J1

open scoped Pointwise

open scoped IsMulCommutative in
theorem eq_one_of_mem_sylow_of_commute_normalizer {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    [IsMulCommutative (S : Subgroup G)] {z : G} (hzS : z ∈ S)
    (hz : ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * z = z * n) : z = 1 := by
  classical
  let φ : G →* S := MonoidHom.transfer (MonoidHom.id S)
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ hk
    obtain ⟨n, hn, heq⟩ := Sylow.conj_eq_normalizer_conj_of_mem S (z ^ k) g₀
      (S.toSubgroup.pow_mem hzS k) hk
    rw [heq]
    have hc : Commute n (z ^ k) := Commute.pow_right (hz n hn) k
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hφz : φ z = ⟨z ^ (S : Subgroup G).index, _⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id S) z key
  have hker : φ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      apply (MonoidHom.ker_eq_bot_iff φ).mp h
      rw [map_mul, map_mul, mul_comm]
    · exact h
  have h1 : z ^ (S : Subgroup G).index = 1 := by
    have h : φ z = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top z)
    rw [hφz] at h
    exact congrArg Subtype.val h
  have h2 : orderOf z ∣ Nat.card (S : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hzS
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h2 S.card_coprime_index) (orderOf_dvd_of_pow_eq_one h1))

theorem disjoint_orbit_of_not_mem {A X : Type*} [Group A] [MulAction A X] {x y : X}
    (hy : y ∉ MulAction.orbit A x) : Disjoint (MulAction.orbit A x) (MulAction.orbit A y) := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  have h1 : MulAction.orbit A w = MulAction.orbit A x := MulAction.orbit_eq_iff.mpr hwx
  have h2 : MulAction.orbit A w = MulAction.orbit A y := MulAction.orbit_eq_iff.mpr hwy
  exact hy (MulAction.orbit_eq_iff.mp (h2.symm.trans h1))

theorem orbit_eq_of_ncard_eq_seven {A X : Type*} [Group A] [MulAction A X] [Finite X]
    (T : Set X) (hT : T.ncard = 7) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hodd : ∀ x ∈ T, Odd (MulAction.orbit A x).ncard ∧ (MulAction.orbit A x).ncard ≠ 1) :
    ∀ x ∈ T, MulAction.orbit A x = T := by
  have hsub : ∀ x ∈ T, MulAction.orbit A x ⊆ T := by
    rintro x hx _ ⟨a, rfl⟩
    exact hTinv a x hx
  have hge : ∀ x ∈ T, 3 ≤ (MulAction.orbit A x).ncard := by
    intro x hx
    obtain ⟨⟨k, hk⟩, h1⟩ := hodd x hx
    omega
  intro x hx
  by_contra hne
  have hlt : (MulAction.orbit A x).ncard < 7 :=
    hT ▸ Set.ncard_lt_ncard (LE.le.ssubset_of_ne (hsub x hx) hne)
  obtain ⟨y, hyT, hyx⟩ : ∃ y ∈ T, y ∉ MulAction.orbit A x := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm (hsub x hx) h)
  have hxy : (MulAction.orbit A x ∪ MulAction.orbit A y).ncard =
      (MulAction.orbit A x).ncard + (MulAction.orbit A y).ncard :=
    Set.ncard_union_eq (disjoint_orbit_of_not_mem hyx)
  have hxyle : (MulAction.orbit A x ∪ MulAction.orbit A y).ncard ≤ 7 :=
    hT ▸ Set.ncard_le_ncard (Set.union_subset (hsub x hx) (hsub y hyT))
  have hx3 : (MulAction.orbit A x).ncard = 3 := by
    obtain ⟨⟨k, hk⟩, _⟩ := hodd x hx
    have := hge y hyT
    omega
  have hy3 : (MulAction.orbit A y).ncard = 3 := by
    obtain ⟨⟨k, hk⟩, _⟩ := hodd y hyT
    have := hge x hx
    omega
  obtain ⟨z, hzT, hzxy⟩ : ∃ z ∈ T, z ∉ MulAction.orbit A x ∪ MulAction.orbit A y := by
    by_contra h
    push Not at h
    have := Set.ncard_le_ncard h
    omega
  have hdz : Disjoint (MulAction.orbit A x ∪ MulAction.orbit A y) (MulAction.orbit A z) :=
    Disjoint.union_left (disjoint_orbit_of_not_mem fun h => hzxy (Or.inl h))
      (disjoint_orbit_of_not_mem fun h => hzxy (Or.inr h))
  have hall := Set.ncard_union_eq hdz
  have hallle : (MulAction.orbit A x ∪ MulAction.orbit A y ∪ MulAction.orbit A z).ncard ≤ 7 :=
    hT ▸ Set.ncard_le_ncard (Set.union_subset (Set.union_subset (hsub x hx) (hsub y hyT))
      (hsub z hzT))
  have := hge z hzT
  omega

theorem sylow_two_card_eight_transitive {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) (hS : IsMulCommutative (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 8) :
    ∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  classical
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set φ : N →* MulAut Sg := Sg.normalizerMonoidHom with hφ
  set A : Subgroup (MulAut Sg) := φ.range with hA
  have hcommS : ∀ a b : Sg, a * b = b * a := fun a b => hS.is_comm.comm a b
  have hAodd : Odd (Nat.card A) := by
    have hSN : Sg ≤ N := Subgroup.le_normalizer
    have hker : Sg.subgroupOf N ≤ φ.ker := by
      rw [hφ, Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcommS ⟨y, hy⟩ ⟨x, hx⟩)
    have h1 : φ.ker.index = Nat.card A := Subgroup.index_ker φ
    have h2 : φ.ker.index ∣ (Sg.subgroupOf N).index := Subgroup.index_dvd_of_le hker
    have h3 : (Sg.subgroupOf N).index ∣ Sg.index := Subgroup.relIndex_dvd_index_of_le hSN
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    rw [← h1] at h
    exact S.not_dvd_index (h.trans (h2.trans h3))
  have hfix : ∀ x : Sg, (∀ a : A, a • x = x) → x = 1 := by
    intro x hx
    apply Subtype.ext
    have : IsMulCommutative (S : Subgroup G) := hS
    refine eq_one_of_mem_sylow_of_commute_normalizer hnonab S x.2 ?_
    intro n hn
    have h := congrArg Subtype.val (hx ⟨φ ⟨n, hn⟩, ⟨n, hn⟩, rfl⟩)
    change (n : G) * x * n⁻¹ = x at h
    calc n * (x : G) = (n * x * n⁻¹) * n := by group
      _ = x * n := by rw [h]
  set T : Set Sg := {x | x ≠ 1} with hT
  have hTcard : T.ncard = 7 := by
    have : T = (Set.univ : Set Sg) \ {1} := by ext; simp [hT]
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcard]
  have hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T := by
    intro a x hx h
    apply hx
    have h' : (a : MulAut Sg) x = (a : MulAut Sg) 1 := by rw [map_one]; exact h
    exact (a : MulAut Sg).injective h'
  have horbit : ∀ x ∈ T, MulAction.orbit A x = T := by
    apply orbit_eq_of_ncard_eq_seven T hTcard hTinv
    intro x hx
    have hdvd : (MulAction.orbit A x).ncard ∣ Nat.card A := by
      rw [← MulAction.index_stabilizer]
      exact Subgroup.index_dvd_card _
    refine ⟨Odd.of_dvd_nat hAodd hdvd, fun h1 => hx (hfix x ?_)⟩
    intro a
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h1
    have hxo : x ∈ MulAction.orbit A x := MulAction.mem_orbit_self x
    have hao : a • x ∈ MulAction.orbit A x := MulAction.mem_orbit x a
    rw [hy] at hxo hao
    rw [Set.mem_singleton_iff] at hxo hao
    rw [hao, hxo]
  intro x hx hx1 y hy hy1
  have hxT : (⟨x, hx⟩ : Sg) ∈ T := fun h => hx1 (congrArg Subtype.val h)
  have hyT : (⟨y, hy⟩ : Sg) ∈ T := fun h => hy1 (congrArg Subtype.val h)
  rw [← horbit _ hxT] at hyT
  obtain ⟨⟨a, n, rfl⟩, ha⟩ := hyT
  exact ⟨n, n.2, congrArg Subtype.val ha⟩

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

theorem relIndex_inf_F (S : Sylow 2 G) (htS : h.t ∈ S) :
    ((S : Subgroup G) ⊓ h.F).relIndex S = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨h.t, htS⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  have hbS : (b : G) ∈ (S : Subgroup G) := b.2
  have hbC := h.sylow_le_centralizer S htS hbS
  by_cases hb : (b : G) ∈ h.F
  · refine Or.inr ⟨⟨hbS, hb⟩, fun ⟨_, hbt⟩ => h.t_not_mem ?_⟩
    have : h.t = (b : G)⁻¹ * (b * h.t) := by group
    rw [this]
    exact h.F.mul_mem (h.F.inv_mem hb) hbt
  · refine Or.inl ⟨⟨(S : Subgroup G).mul_mem hbS htS, ?_⟩, fun ⟨_, hb'⟩ => hb hb'⟩
    rcases h.mem_centralizer_t.mp hbC with hb' | hb'
    · exact absurd hb' hb
    · rw [h.commute_of_mem hbC]
      exact hb'

theorem card_sylow_and (S : Sylow 2 G) (htS : h.t ∈ S) :
    Nat.card (S : Subgroup G) = 8 ∧ Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) = 4 := by
  have h1 := Subgroup.relIndex_mul_card ((S : Subgroup G) ⊓ h.F) S
  rw [h.relIndex_inf_F S htS, inf_assoc, inf_comm h.F, ← inf_assoc, inf_idem] at h1
  have hV4 : Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) ∣ 4 :=
    A5Sub.card_dvd_four_of_isPGroup h.iso inf_le_right (S.isPGroup'.to_le inf_le_left)
  have h8 : 8 ∣ Nat.card (S : Subgroup G) := by
    have : 2 ^ 3 ∣ Nat.card G := by
      have := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({h.t} : Set G))
      rw [h.card_centralizer] at this
      exact (by norm_num : 2 ^ 3 ∣ 120).trans this
    exact S.pow_dvd_card_of_pow_dvd_card this
  have hle : Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) ≤ 4 := Nat.le_of_dvd (by norm_num) hV4
  have hpos : 0 < Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) := Nat.card_pos
  refine ⟨by omega, by omega⟩

theorem card_sylow (S : Sylow 2 G) (htS : h.t ∈ S) : Nat.card (S : Subgroup G) = 8 :=
  (h.card_sylow_and S htS).1

theorem card_inf_F (S : Sylow 2 G) (htS : h.t ∈ S) :
    Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) = 4 :=
  (h.card_sylow_and S htS).2

theorem mul_self_of_mem_inf_F {S : Sylow 2 G} {x : G} (hx : x ∈ (S : Subgroup G) ⊓ h.F) :
    x * x = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx.1⟩
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at hk'
  rw [← pow_two]
  exact A5Sub.sq_eq_one_of_pow h.iso hx.2 hk'

theorem mul_self_of_mem_sylow (S : Sylow 2 G) (htS : h.t ∈ S) {x : G}
    (hx : x ∈ S) : x * x = 1 := by
  rcases h.mem_centralizer_t.mp (h.sylow_le_centralizer S htS hx) with hxF | hxF
  · exact h.mul_self_of_mem_inf_F ⟨hx, hxF⟩
  · have hy := h.mul_self_of_mem_inf_F (S := S) ⟨(S : Subgroup G).mul_mem htS hx, hxF⟩
    have hc : h.t * x = x * h.t := (h.commute_of_mem (h.sylow_le_centralizer S htS hx)).symm
    calc x * x = (h.t * h.t) * (x * x) := by rw [h.t_mul_t, one_mul]
      _ = h.t * (h.t * x) * x := by group
      _ = h.t * (x * h.t) * x := by rw [hc]
      _ = (h.t * x) * (h.t * x) := by group
      _ = 1 := hy

theorem centralizer_sylow (S : Sylow 2 G) (htS : h.t ∈ S) :
    Subgroup.centralizer ((S : Subgroup G) : Set G) = S := by
  have hab := h.abelian_sylow S
  have hCV := A5Sub.inf_centralizer_eq h.iso (inf_le_right : (S : Subgroup G) ⊓ h.F ≤ h.F)
    (h.card_inf_F S htS)
  apply le_antisymm
  · intro x hx
    have hxt : x ∈ Subgroup.centralizer ({h.t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx h.t htS).symm)
    have hcV : ∀ y, y ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) →
        y ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
      fun y hy => Subgroup.centralizer_le (fun z hz => hz.1) hy
    rcases h.mem_centralizer_t.mp hxt with hxF | hxF
    · have : x ∈ h.F ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
        ⟨hxF, hcV x hx⟩
      rw [hCV] at this
      exact this.1
    · have htC : h.t ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨h.t, htS⟩)
      have : h.t * x ∈ h.F ⊓
          Subgroup.centralizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
        ⟨hxF, hcV _ (Subgroup.mul_mem _ htC hx)⟩
      rw [hCV] at this
      have hx' : x = h.t * (h.t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [hx']
      exact (S : Subgroup G).mul_mem htS this.1
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem exists_conj_of_mem_sylow (S : Sylow 2 G) (htS : h.t ∈ S) {x y : G}
    (hx : x ∈ S) (hx1 : x ≠ 1) (hy : y ∈ S) (hy1 : y ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  have := h.isSimpleGroup
  exact sylow_two_card_eight_transitive h.nonabelian S (h.abelian_sylow S) (h.card_sylow S htS)
    x hx hx1 y hy hy1

theorem exists_conj_eq_t {x : G} (hx : orderOf x = 2) : ∃ g : G, g * x * g⁻¹ = h.t := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  obtain ⟨S', hS'⟩ := hx2.exists_le_sylow
  obtain ⟨S, hS⟩ := ht2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have htS : h.t ∈ S := hS (Subgroup.mem_zpowers _)
  have hgx : g * x * g⁻¹ ∈ S := by
    rw [← hg]
    change g * x * g⁻¹ ∈ MulAut.conj g • (S' : Subgroup G)
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S' : Subgroup G)
      (hS' (Subgroup.mem_zpowers x))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hgx1 : g * x * g⁻¹ ≠ 1 := by
    intro h1
    have := congrArg (fun w => g⁻¹ * w * g) h1
    simp only [mul_one, inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at this
    rw [this, orderOf_one] at hx
    omega
  obtain ⟨n, -, hn⟩ := h.exists_conj_of_mem_sylow S htS hgx hgx1 htS h.t_ne_one
  exact ⟨n * g, by rw [← hn]; group⟩

include h in
theorem isConj_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hx
  obtain ⟨k, hk⟩ := h.exists_conj_eq_t hy
  refine isConj_iff.mpr ⟨k⁻¹ * g, ?_⟩
  rw [show k⁻¹ * g * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k by group, hg, ← hk]
  group

theorem exists_sylow_mem_t : ∃ S : Sylow 2 G, h.t ∈ S := by
  have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  obtain ⟨S, hS⟩ := ht2.exists_le_sylow
  exact ⟨S, hS (Subgroup.mem_zpowers _)⟩

include h in
theorem card_sylow' (S : Sylow 2 G) : Nat.card (S : Subgroup G) = 8 := by
  obtain ⟨T, hT⟩ := h.exists_sylow_mem_t
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity T, h.card_sylow T hT]

end JankoHyp

end CFSG.Walter.J1
