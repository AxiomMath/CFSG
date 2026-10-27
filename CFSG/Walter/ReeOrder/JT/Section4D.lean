module

public import CFSG.Walter.ReeOrder.JT.Section4C

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise

section General

variable {X : Type*} [Group X] [Finite X]

theorem normalizer_le_normalizer_of_le_isCyclic {Q R : Subgroup X} (hQ : IsCyclic Q)
    (hRQ : R ≤ Q) : Subgroup.normalizer (Q : Set X) ≤ Subgroup.normalizer (R : Set X) := by
  intro g hg
  refine mem_normalizer_of_conj_mem ?_
  set R' := R.map (MulAut.conj g).toMonoidHom
  have hR'Q : R' ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hRQ hx)
  have hcard : Nat.card (R'.subgroupOf Q) = Nat.card (R.subgroupOf Q) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'Q).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRQ).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq : R'.subgroupOf Q = R.subgroupOf Q := IsCyclic.subgroup_eq_iff_card_eq.mpr hcard
  intro x hx
  have h1 : (⟨g * x * g⁻¹, hR'Q ⟨x, hx, rfl⟩⟩ : Q) ∈ R'.subgroupOf Q := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x, hx, rfl⟩
  rw [heq, Subgroup.mem_subgroupOf] at h1
  exact h1

omit [Finite X] in
theorem eq_one_of_conj_eq_of_pow_three_mem {V : Subgroup X} (hV : IsKleinFour V) {m : X}
    (hmN : m ∈ Subgroup.normalizer (V : Set X)) (hm3 : m ^ 3 ∈ Subgroup.centralizer (V : Set X))
    (hmC : m ∉ Subgroup.centralizer (V : Set X)) {v : X} (hv : v ∈ V) (hmv : m * v * m⁻¹ = v) :
    v = 1 := by
  by_contra hv1
  have hconj : ∀ x ∈ V, m * x * m⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmN x).mp hx
  obtain ⟨u, huV, hmu⟩ : ∃ u ∈ V, m * u * m⁻¹ ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hmC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * m = m * (m⁻¹ * x * m) := by group
      _ = m * x := by
        congr 1
        have := hcon x hx
        calc m⁻¹ * x * m = m⁻¹ * (m * x * m⁻¹) * m := by rw [this]
          _ = x := by group
  set w := m * u * m⁻¹
  have hwV : w ∈ V := hconj u huV
  have hu1 : u ≠ 1 := fun h1 => hmu (by simp [w, h1])
  have huv : u ≠ v := by
    rintro rfl
    exact hmu hmv
  have hw1 : w ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg (fun y => m⁻¹ * y * m) h1
    simpa [w, mul_assoc] using this
  have hwv : w ≠ v := by
    intro h1
    apply huv
    have := congrArg (fun y => m⁻¹ * y * m) h1
    have h2 : m⁻¹ * v * m = v := by
      calc m⁻¹ * v * m = m⁻¹ * (m * v * m⁻¹) * m := by rw [hmv]
        _ = v := by group
    simpa [w, mul_assoc, h2] using this
  have hwvu : w = v * u := by
    have := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨v, hv⟩) (y := ⟨u, huV⟩)
      (z := ⟨w, hwV⟩) (fun h1 => hv1 (congrArg Subtype.val h1))
      (fun h1 => hu1 (congrArg Subtype.val h1))
      (fun h1 => huv (congrArg Subtype.val h1).symm)
      (fun h1 => hw1 (congrArg Subtype.val h1))
      (fun h1 => hwv (congrArg Subtype.val h1))
      (fun h1 => hmu (congrArg Subtype.val h1))
    exact congrArg Subtype.val this
  have hvv : v * v = 1 := mul_self_of_isKleinFour' hV hv
  have hmw : m * w * m⁻¹ = u := by
    rw [hwvu, show m * (v * u) * m⁻¹ = (m * v * m⁻¹) * (m * u * m⁻¹) by group, hmv]
    change v * w = u
    rw [hwvu, ← mul_assoc, hvv, one_mul]
  have h3u : m ^ 3 * u * (m ^ 3)⁻¹ = u := by
    rw [(Subgroup.mem_centralizer_iff.mp hm3 u huV).symm, mul_inv_cancel_right]
  apply hmu
  calc m * u * m⁻¹ = m * (m * w * m⁻¹) * m⁻¹ := by rw [hmw]
    _ = m ^ 3 * u * (m ^ 3)⁻¹ := by simp only [w]; rw [pow_three]; group
    _ = u := h3u

omit [Finite X] in
theorem exists_pow_conj_of_pow_three_mem {V : Subgroup X} (hV : IsKleinFour V) {m : X}
    (hmN : m ∈ Subgroup.normalizer (V : Set X)) (hm3 : m ^ 3 ∈ Subgroup.centralizer (V : Set X))
    (hmC : m ∉ Subgroup.centralizer (V : Set X)) {u v : X} (hu : u ∈ V) (hu1 : u ≠ 1)
    (hv : v ∈ V) (hv1 : v ≠ 1) : ∃ k : ℕ, m ^ k * u * (m ^ k)⁻¹ = v := by
  have hconj : ∀ x ∈ V, m * x * m⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmN x).mp hx
  set u₁ := m * u * m⁻¹
  set u₂ := m * u₁ * m⁻¹
  have hu₁V : u₁ ∈ V := hconj u hu
  have hu₂V : u₂ ∈ V := hconj u₁ hu₁V
  have hu₁1 : u₁ ≠ 1 := fun h1 => hu1 (by
    have := congrArg (fun y => m⁻¹ * y * m) h1
    simpa [u₁, mul_assoc] using this)
  have hu₂1 : u₂ ≠ 1 := fun h1 => hu₁1 (by
    have := congrArg (fun y => m⁻¹ * y * m) h1
    simpa [u₂, mul_assoc] using this)
  have huu₁ : u ≠ u₁ := fun h1 =>
    hu1 (eq_one_of_conj_eq_of_pow_three_mem hV hmN hm3 hmC hu h1.symm)
  have hu₁u₂ : u₁ ≠ u₂ := fun h1 =>
    hu₁1 (eq_one_of_conj_eq_of_pow_three_mem hV hmN hm3 hmC hu₁V h1.symm)
  have huu₂ : u ≠ u₂ := by
    intro h1
    have h3 : m ^ 3 * u * (m ^ 3)⁻¹ = u := by
      rw [(Subgroup.mem_centralizer_iff.mp hm3 u hu).symm, mul_inv_cancel_right]
    have : m * u₂ * m⁻¹ = u := by
      rw [← h3]
      simp only [u₂, u₁]
      rw [pow_three]
      group
    rw [← h1] at this
    exact huu₁ this.symm
  by_cases hvu : v = u
  · exact ⟨0, by simp [hvu]⟩
  by_cases hvu₁ : v = u₁
  · exact ⟨1, by simp [hvu₁, u₁]⟩
  by_cases hvu₂ : v = u₂
  · exact ⟨2, by rw [hvu₂, pow_two]; simp only [u₂, u₁]; group⟩
  exfalso
  have h1 := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨u, hu⟩) (y := ⟨u₁, hu₁V⟩)
    (z := ⟨u₂, hu₂V⟩) (fun h0 => hu1 (congrArg Subtype.val h0))
    (fun h0 => hu₁1 (congrArg Subtype.val h0)) (fun h0 => huu₁ (congrArg Subtype.val h0))
    (fun h0 => hu₂1 (congrArg Subtype.val h0)) (fun h0 => huu₂ (congrArg Subtype.val h0).symm)
    (fun h0 => hu₁u₂ (congrArg Subtype.val h0).symm)
  have h2 := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨u, hu⟩) (y := ⟨u₁, hu₁V⟩)
    (z := ⟨v, hv⟩) (fun h0 => hu1 (congrArg Subtype.val h0))
    (fun h0 => hu₁1 (congrArg Subtype.val h0)) (fun h0 => huu₁ (congrArg Subtype.val h0))
    (fun h0 => hv1 (congrArg Subtype.val h0)) (fun h0 => hvu (congrArg Subtype.val h0))
    (fun h0 => hvu₁ (congrArg Subtype.val h0))
  exact hvu₂ (congrArg Subtype.val (h2.trans h1.symm))

end General

structure Config {G : Type} [Group G] [Finite G] (h : JTHyp G) extends Setup h where
  μ : G
  t₁ : G
  μ_mem_NS : μ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)
  μ_mem_NT : μ ∈ Subgroup.normalizer (T : Set G)
  orderOf_μ : orderOf μ = 3
  t₁_mem : t₁ ∈ S
  orderOf_t₁ : orderOf t₁ = 2
  comm : μ * t₁ = t₁ * μ
  μ_fpf : ∀ x ∈ T, μ * x * μ⁻¹ = x → x = 1
  normalizer_T_eq : Subgroup.normalizer (T : Set G) =
    Subgroup.zpowers μ ⊔ Subgroup.centralizer (T : Set G)
  t₁_fpf : ∀ x ∈ GorensteinWalter.oddCoreOf (Subgroup.centralizer (T : Set G)),
    t₁ * x * t₁⁻¹ = x → x = 1

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G}

theorem exists_config
    (s : Setup h) (hp : h.p ≠ 2) : ∃ c : Config h, c.toSetup = s := by
  obtain ⟨μ, t₁, hμS, hμT, hμ3, ht₁S, ht₁2, hc, hfixT, hNT, hfixQ, -⟩ := s.lemma_4_2_c hp
  exact ⟨⟨s, μ, t₁, hμS, hμT, hμ3, ht₁S, ht₁2, hc, hfixT, hNT, hfixQ⟩, rfl⟩

theorem conj_mem_centralizer_T (s : Setup h) {g : G} (hg : g ∈ Subgroup.normalizer (s.T : Set G))
    {y : G} (hy : y ∈ Subgroup.centralizer (s.T : Set G)) :
    g * y * g⁻¹ ∈ Subgroup.centralizer (s.T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro z hz
  have hz' : g⁻¹ * z * g ∈ s.T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) z).mp hz
    simpa using this
  have := hy _ hz'
  calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
    _ = g * y * g⁻¹ * z := by group

end Setup

namespace Config

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (c : Config h) (hp : h.p ≠ 2)
include hp

omit hp in
theorem t₁_fpf_Q : ∀ x ∈ c.Q, c.t₁ * x * c.t₁⁻¹ = x → x = 1 := c.t₁_fpf

omit hp in
theorem t₁_not_mem_T : c.t₁ ∉ c.T := fun hT => by
  have := c.μ_fpf _ hT (by rw [c.comm, mul_inv_cancel_right])
  have h2 := c.orderOf_t₁
  rw [this, orderOf_one] at h2
  omega

theorem normalizer_S_inf_normalizer_T_le :
    Subgroup.normalizer ((c.S : Subgroup G) : Set G) ⊓ Subgroup.normalizer (c.T : Set G) ≤
      (c.S : Subgroup G) ⊔ Subgroup.zpowers c.μ := by
  intro x hx
  have hxS : x ∈ Subgroup.normalizer ((c.S : Subgroup G) : Set G) := hx.1
  have hxT : x ∈ Subgroup.normalizer (c.T : Set G) := hx.2
  have hle : Subgroup.zpowers c.μ ≤
      Subgroup.normalizer ((Subgroup.centralizer (c.T : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj_mem fun y hy => c.toSetup.conj_mem_centralizer_T c.μ_mem_NT hy
  rw [c.normalizer_T_eq, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    at hxT
  obtain ⟨a, ha, b, hb, rfl⟩ := hxT
  have hbS : b ∈ Subgroup.normalizer ((c.S : Subgroup G) : Set G) := by
    have : b = a⁻¹ * (a * b) := by group
    rw [this]
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) hxS
    exact (Subgroup.zpowers_le.mpr c.μ_mem_NS) ha
  have hbS' : b ∈ (c.S : Subgroup G) := by
    rw [← c.toSetup.normalizer_S_inf_centralizer_T hp]
    exact ⟨hbS, hb⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hbS')

theorem commute_t₁ {x : G}
    (hx : x ∈ Subgroup.normalizer ((c.S : Subgroup G) : Set G) ⊓
      Subgroup.normalizer (c.T : Set G)) : x * c.t₁ = c.t₁ * x := by
  have hab := h.abelian_sylow c.S
  have hx' := c.normalizer_S_inf_normalizer_T_le hp hx
  have hle : (c.S : Subgroup G) ⊔ Subgroup.zpowers c.μ ≤ Subgroup.centralizer ({c.t₁} : Set G) := by
    refine sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨c.t₁, c.t₁_mem⟩))) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr c.comm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx')

variable {R : Subgroup G} (hRQ : R ≤ c.Q) (hR : R ≠ ⊥)
include hRQ hR

theorem S_inf_centralizer_R :
    (c.S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G) = c.T := by
  apply le_antisymm
  · rintro x ⟨hxS, hxR⟩
    by_contra hxT
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
    have hyQ : (y : G) ∈ c.Q := hRQ y.2
    have hinv := c.toSetup.conj_eq_inv_of_mem_S hp hxS hxT hyQ
    have hc := (Subgroup.mem_centralizer_iff.mp hxR) y y.2
    rw [hc.symm, mul_inv_cancel_right] at hinv
    have hyy : (y : G) * y = 1 := by
      calc (y : G) * y = y * (y : G)⁻¹ := by rw [← hinv]
        _ = 1 := mul_inv_cancel _
    have hodd := ((c.toSetup.mem_Q_iff hp).mp hyQ).2
    have h2 : orderOf (y : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hyy)
    apply hy1
    apply Subtype.ext
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  · intro x hx
    exact ⟨c.le_S hx, Subgroup.centralizer_le hRQ (c.toSetup.T_le_centralizer_Q hx)⟩

theorem normalizer_S_inf_normalizer_R_le :
    Subgroup.normalizer ((c.S : Subgroup G) : Set G) ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (c.T : Set G) := by
  intro x hx
  have hxS : x ∈ Subgroup.normalizer ((c.S : Subgroup G) : Set G) := hx.1
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := hx.2
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  rw [← c.S_inf_centralizer_R hp hRQ hR] at hy ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hxS y).mp hy.1, ?_⟩
  show x * y * x⁻¹ ∈ Subgroup.centralizer (R : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : x⁻¹ * z * x ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxR) z).mp hz
    simpa using this
  have := (Subgroup.mem_centralizer_iff.mp hy.2) _ hz'
  calc z * (x * y * x⁻¹) = x * ((x⁻¹ * z * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * z * x)) * x⁻¹ := by rw [this]
    _ = x * y * x⁻¹ * z := by group

omit hR in
theorem normalizer_T_le_normalizer_R :
    Subgroup.normalizer (c.T : Set G) ≤ Subgroup.normalizer (R : Set G) :=
  (c.toSetup.normalizer_T_le_normalizer_Q hp).trans
    (normalizer_le_normalizer_of_le_isCyclic (c.toSetup.isCyclic_Q hp) hRQ)

theorem exists_index_two :
    ∃ M : Subgroup G, M ≤ Subgroup.normalizer (R : Set G) ∧
      (M.subgroupOf (Subgroup.normalizer (R : Set G))).Normal ∧
      (M.subgroupOf (Subgroup.normalizer (R : Set G))).index = 2 := by
  set N := Subgroup.normalizer (R : Set G)
  have hSN : (c.S : Subgroup G) ≤ N := c.toSetup.S_le_centralizer_T.trans
    (c.toSetup.centralizer_T_le_normalizer_T.trans (c.normalizer_T_le_normalizer_R hp hRQ))
  let S' : Sylow 2 N := c.S.subtype hSN
  have hab := h.abelian_sylow c.S
  have hS'ab : IsMulCommutative (S' : Subgroup N) := by
    refine ⟨⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.ext (Subtype.ext ?_)⟩⟩
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at ha hb
    have := congrArg Subtype.val (hab.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    exact this
  have ht₁S' : (⟨c.t₁, hSN c.t₁_mem⟩ : N) ∈ (S' : Subgroup N) := by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact c.t₁_mem
  have ht₁1 : (⟨c.t₁, hSN c.t₁_mem⟩ : N) ≠ 1 := by
    intro h1
    have := congrArg Subtype.val h1
    have h2 := c.orderOf_t₁
    change c.t₁ = 1 at this
    rw [this, orderOf_one] at h2
    omega
  have hcomm : ∀ n ∈ Subgroup.normalizer ((S' : Subgroup N) : Set N),
      n * ⟨c.t₁, hSN c.t₁_mem⟩ = ⟨c.t₁, hSN c.t₁_mem⟩ * n := by
    intro n hn
    apply Subtype.ext
    change (n : G) * c.t₁ = c.t₁ * n
    have hnS : (n : G) ∈ Subgroup.normalizer ((c.S : Subgroup G) : Set G) := by
      refine mem_normalizer_of_conj_mem fun y hy => ?_
      have := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hSN hy⟩).mp (by
        rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]; exact hy)
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at this
      exact this
    exact c.commute_t₁ hp ⟨hnS, c.normalizer_S_inf_normalizer_R_le hp hRQ hR ⟨hnS, n.2⟩⟩
  obtain ⟨M', hM'n, hM'idx⟩ := exists_normal_index_eq_of_commute_normalizer S' hS'ab ht₁S'
    ht₁1 hcomm
  have hEq : (M'.map N.subtype).subgroupOf N = M' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective M'
  refine ⟨M'.map N.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [hEq]; exact hM'n
  · rw [hEq]; exact hM'idx

end Config

end CFSG.Walter.JT
