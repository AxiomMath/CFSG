module

public import CFSG.Walter.W67.Section5.Prop56A2a

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

structure K3Data (R V : Subgroup G) : Prop where
  rdata : f5.RData R
  comm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a
  card_R : Nat.card R = s.q ^ 2
  isPGroup : IsPGroup 3 V
  le : R ≤ V
  ne : R ≠ V
  card_V : Nat.card V = s.q ^ 3
  J_le : s.J ∈ Subgroup.normalizer (V : Set G)
  B_le : f5.B ≤ Subgroup.normalizer (V : Set G)
  E_le : s.fr.E ≤ Subgroup.normalizer (V : Set G)
  max : ∀ Q : Subgroup G, IsPGroup 3 Q → V ≤ Q → s.J ∈ Subgroup.normalizer (Q : Set G) →
    f5.B ≤ Subgroup.normalizer (Q : Set G) → s.fr.E ≤ Subgroup.normalizer (Q : Set G) → Q = V

variable {f5}

namespace K3Data

variable {R V : Subgroup G} (hK : f5.K3Data R V)
include hK

theorem P₁_le : f5.P₁ ≤ V := hK.rdata.P₁_le.trans hK.le

theorem JBE_le : f5.JBE ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (sup_le (Subgroup.zpowers_le.mpr hK.J_le) hK.B_le) hK.E_le

theorem fpf
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ V, b * y = y * b → y = 1 :=
  f5.fpf_of_isPGroup h22 h26i hp hK.isPGroup hK.B_le hK.E_le

theorem inf_H
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    V ⊓ s.H = f5.P₁ :=
  f5.inf_H_eq_P₁ hp hK.isPGroup hK.P₁_le hK.B_le (hK.fpf h22 h26i hp)

theorem inf_centralizer_P₁ : V ⊓ Subgroup.centralizer (f5.P₁ : Set G) = R :=
  (Subgroup.eq_of_le_of_card_ge (le_inf hK.le hK.rdata.le_centralizer)
    (hK.rdata.max _ (hK.isPGroup.to_le inf_le_left) inf_le_right)).symm

theorem not_le_centralizer : ¬ V ≤ Subgroup.centralizer (f5.P₁ : Set G) := fun h =>
  hK.ne (le_antisymm hK.le (by
    rw [← hK.inf_centralizer_P₁]
    exact le_inf le_rfl h))

omit hK in
theorem mem_normalizer_center {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  Sec54.mem_normalizer_inf hg (Sec54.mem_normalizer_centralizer hg)

theorem center_le : V ⊓ Subgroup.centralizer (V : Set G) ≤ R := by
  rw [← hK.inf_centralizer_P₁]
  intro z hz
  obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
  exact Subgroup.mem_inf.mpr ⟨hzV, Subgroup.mem_centralizer_iff.mpr fun u hu =>
    (Subgroup.mem_centralizer_iff.mp hzC u (hK.P₁_le hu))⟩

theorem center_ne_bot : V ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV1 : V ≠ ⊥ := fun h => hK.ne (le_antisymm hK.le (by rw [h]; exact bot_le))
  have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV1
  have := hK.isPGroup.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center V)
  intro h
  apply hz1
  have hzG : ((z : V) : G) ∈ V ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(z : V).2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨v, hv⟩)
  rw [h, Subgroup.mem_bot] at hzG
  exact Subtype.ext (Subtype.ext hzG)

theorem not_le_center : ¬ R ≤ V ⊓ Subgroup.centralizer (V : Set G) := by
  intro h
  apply hK.not_le_centralizer
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h (hK.rdata.P₁_le hu))).2 v
    hv).symm

theorem card_center
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    Nat.card (V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) = s.q := by
  obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp (hK.isPGroup.to_le inf_le_left)
    (fun b hb => mem_normalizer_center (hK.B_le hb))
    (fun b hb hb1 y hy => hK.fpf h22 h26i hp b hb hb1 y (Subgroup.mem_inf.mp hy).1)
  have hlt : V ⊓ Subgroup.centralizer (V : Set G) < R :=
    lt_of_le_of_ne hK.center_le fun h => hK.not_le_center (le_of_eq h.symm)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [hk, hK.card_R] at h1
  have hq := s.one_lt_q
  have hk2 : k < 2 := (Nat.pow_lt_pow_iff_right hq).mp h1
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hK.center_ne_bot (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
  rw [hk, show k = 1 by omega, pow_one]

theorem center_inf_P₁ : (V ⊓ Subgroup.centralizer (V : Set G)) ⊓ f5.P₁ = ⊥ := by
  rcases f5.irred_JBE _ inf_le_right (fun g hg => Sec54.mem_normalizer_inf
    (mem_normalizer_center (hK.JBE_le hg)) (f5.JBE_le_normalizer_P₁ hg)) with h | h
  · exact h
  · exfalso
    apply hK.not_le_centralizer
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ (V ⊓ Subgroup.centralizer (V : Set G)) ⊓ f5.P₁ := by rw [h]; exact hu
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hu').1).2 v
      hv).symm

theorem center_eq
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    V ⊓ Subgroup.centralizer (V : Set G) = Sec56.invSub s.J R hK.comm := by
  have hle : V ⊓ Subgroup.centralizer (V : Set G) ≤ Sec56.invSub s.J R hK.comm := by
    intro y hy
    refine ⟨hK.center_le hy, ?_⟩
    have hJy : s.J * y * s.J⁻¹ ∈ V ⊓ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_center hK.J_le) y).mp hy
    set z := y * (s.J * y * s.J⁻¹) with hz
    have hzN : z ∈ V ⊓ Subgroup.centralizer (V : Set G) := Subgroup.mul_mem _ hy hJy
    have hcomm : y * (s.J * y * s.J⁻¹) = (s.J * y * s.J⁻¹) * y :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 _
        (Subgroup.mem_inf.mp hJy).1).symm
    have h1 : s.J * z * s.J⁻¹ = z := by
      calc s.J * z * s.J⁻¹ = (s.J * y * s.J⁻¹) * ((s.J * s.J) * y * (s.J * s.J)⁻¹) := by
            rw [hz]; group
        _ = (s.J * y * s.J⁻¹) * y := by rw [s.J_mul_J]; group
        _ = z := by rw [hz, hcomm]
    have hzH : z ∈ s.H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * s.J = s.J * z * s.J⁻¹ * s.J := by rw [h1]
        _ = s.J * z := by group
    have hzP : z ∈ f5.P₁ := by
      rw [← hK.inf_H h22 h26i hp]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hzN).1, hzH⟩
    have hz1 : z = 1 := by
      have : z ∈ (V ⊓ Subgroup.centralizer (V : Set G)) ⊓ f5.P₁ := Subgroup.mem_inf.mpr ⟨hzN, hzP⟩
      rwa [hK.center_inf_P₁, Subgroup.mem_bot] at this
    calc s.J * y * s.J⁻¹ = y⁻¹ * z := by rw [hz]; group
      _ = y⁻¹ := by rw [hz1, mul_one]
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [(hK.rdata.card_P₂ hK.comm h22 h26i hp hK.card_R).1, hK.card_center h22 h26i hp]

theorem sup_center
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    f5.P₁ ⊔ (V ⊓ Subgroup.centralizer (V : Set G)) = R := by
  rw [hK.center_eq h22 h26i hp]
  exact (hK.rdata.card_P₂ hK.comm h22 h26i hp hK.card_R).2

theorem pow_three
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {r : G}
    (hr : r ∈ R) : r ^ 3 = 1 :=
  hK.rdata.pow_three_eq_one hK.comm h22 h26i hp hK.card_R r hr

theorem le_normalizer
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    V ≤ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := V ⊓ Subgroup.normalizer (R : Set G) with hMdef
  have hRM : R ≤ M := le_inf hK.le Subgroup.le_normalizer
  have hRlt : R < M := by
    have : Group.IsNilpotent V := hK.isPGroup.isNilpotent
    have hlt : R.subgroupOf V < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hK.ne (le_antisymm hK.le ?_)
      intro v hv
      have : (⟨v, hv⟩ : V) ∈ R.subgroupOf V := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨w, hwN, hwR⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    refine lt_of_le_of_ne hRM fun h => hwR ?_
    have hwM : (w : G) ∈ M := by
      refine Subgroup.mem_inf.mpr ⟨w.2, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        have := (Subgroup.mem_normalizer_iff.mp hwN ⟨r, hK.le hr⟩).mp
          (Subgroup.mem_subgroupOf.mpr hr)
        exact Subgroup.mem_subgroupOf.mp this
      · intro hr
        have hrV : r ∈ V := by
          have h1 : (w : G) * r * (w : G)⁻¹ ∈ V := hK.le hr
          have : r = (w : G)⁻¹ * ((w : G) * r * (w : G)⁻¹) * w := by group
          rw [this]
          exact V.mul_mem (V.mul_mem (V.inv_mem w.2) h1) w.2
        have := (Subgroup.mem_normalizer_iff.mp hwN ⟨r, hrV⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hr)
        exact Subgroup.mem_subgroupOf.mp this
    rw [← h] at hwM
    exact Subgroup.mem_subgroupOf.mpr hwM
  obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp (hK.isPGroup.to_le inf_le_left)
    (fun b hb => Sec54.mem_normalizer_inf (hK.B_le hb)
      (Subgroup.le_normalizer (hK.rdata.B_le hb)))
    (fun b hb hb1 y hy => hK.fpf h22 h26i hp b hb hb1 y (Subgroup.mem_inf.mp hy).1)
  have h1 := Subgroup.card_lt_of_lt hRlt
  have h2 := Subgroup.card_le_of_le (inf_le_left : M ≤ V)
  rw [hk, hK.card_R] at h1
  rw [hk, hK.card_V] at h2
  have hq := s.one_lt_q
  have hk1 : 2 < k := (Nat.pow_lt_pow_iff_right hq).mp h1
  have hk2 : k ≤ 3 := (Nat.pow_le_pow_iff_right hq).mp h2
  have hMV : M = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by
    rw [hk, hK.card_V, show k = 3 by omega])
  rw [← hMV]
  exact inf_le_right

theorem commutator_mem
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {r v : G}
    (hr : r ∈ R) (hv : v ∈ V) :
    r * v * r⁻¹ * v⁻¹ ∈ V ⊓ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₁ := V ⊓ Subgroup.centralizer (V : Set G) with hN₁def
  have hcen : ∀ c ∈ N₁, ∀ g ∈ V, c * g = g * c := fun c hc g hg =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 g hg).symm
  let C : Subgroup G :=
    { carrier := {r | r ∈ R ∧ ∀ v ∈ V, r * v * r⁻¹ * v⁻¹ ∈ N₁}
      mul_mem' := fun {a b} ha hb => ⟨R.mul_mem ha.1 hb.1, fun v hv => by
        have h1 := hb.2 v hv
        have h2 := ha.2 v hv
        have h3 : a * b * v * (a * b)⁻¹ * v⁻¹ =
            (b * v * b⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) := by
          calc a * b * v * (a * b)⁻¹ * v⁻¹ = a * (b * v * b⁻¹ * v⁻¹) * (v * a⁻¹ * v⁻¹) := by
                group
            _ = (b * v * b⁻¹ * v⁻¹) * a * (v * a⁻¹ * v⁻¹) := by
                rw [← hcen _ h1 a (hK.le ha.1)]
            _ = (b * v * b⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
        rw [h3]
        exact N₁.mul_mem h1 h2⟩
      one_mem' := ⟨R.one_mem, fun v _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact N₁.one_mem⟩
      inv_mem' := fun {a} ha => ⟨R.inv_mem ha.1, fun v hv => by
        have h1 := ha.2 v hv
        have h2 : a⁻¹ * v * a⁻¹⁻¹ * v⁻¹ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by
          calc a⁻¹ * v * a⁻¹⁻¹ * v⁻¹ = a⁻¹ * (a * v * a⁻¹ * v⁻¹)⁻¹ * a := by group
            _ = (a * v * a⁻¹ * v⁻¹)⁻¹ * a⁻¹ * a := by
                rw [← hcen _ (N₁.inv_mem h1) a⁻¹ (V.inv_mem (hK.le ha.1))]
            _ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
        rw [h2]
        exact N₁.inv_mem h1⟩ }
  have hCR : C ≤ R := fun _ hc => hc.1
  have hN₁C : N₁ ≤ C := fun c hc => ⟨hK.center_le hc, fun v hv => by
    rw [hcen c hc v hv, mul_inv_cancel_right, mul_inv_cancel]
    exact N₁.one_mem⟩
  have hex : ∃ r₀ ∈ C, r₀ ∉ N₁ := by
    have hRn : (R.subgroupOf V).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK.le).mpr (hK.le_normalizer h22 h26i hp)
    set Z := Subgroup.center V with hZdef
    have hQ3 : IsPGroup 3 (V ⧸ Z) := hK.isPGroup.to_quotient Z
    have : Group.IsNilpotent (V ⧸ Z) := hQ3.isNilpotent
    set Rq := (R.subgroupOf V).map (QuotientGroup.mk' Z) with hRqdef
    have : Rq.Normal := hRn.map _ (QuotientGroup.mk'_surjective Z)
    have hRq1 : Rq ≠ ⊥ := by
      intro h
      apply hK.not_le_center
      intro u hu
      have : QuotientGroup.mk' Z (⟨u, hK.le hu⟩ : V) ∈ Rq :=
        ⟨⟨u, hK.le hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact Subgroup.mem_inf.mpr ⟨hK.le hu, Subgroup.mem_centralizer_iff.mpr fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp this ⟨g, hg⟩)⟩
    obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hRq1)
    obtain ⟨hwR, hwZ⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.mp hwR
    refine ⟨r₀, ⟨Subgroup.mem_subgroupOf.mp hr₀, fun v hv => ?_⟩, fun hr₀N => hw1 ?_⟩
    · have h1 := Subgroup.mem_center_iff.mp hwZ (QuotientGroup.mk' Z ⟨v, hv⟩)
      have h2 : QuotientGroup.mk' Z (r₀ * ⟨v, hv⟩ * r₀⁻¹ * (⟨v, hv⟩ : V)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact Subgroup.mem_inf.mpr ⟨(r₀ * ⟨v, hv⟩ * r₀⁻¹ * (⟨v, hv⟩ : V)⁻¹ : V).2,
        Subgroup.mem_centralizer_iff.mpr fun g hg =>
          congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨g, hg⟩)⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr₀N).2 g g.2)
  obtain ⟨r₀, hr₀C, hr₀N⟩ := hex
  have hBC : f5.B ≤ Subgroup.normalizer (C : Set G) := by
    intro b hb
    apply Sec53.mem_normalizer_of_conj_le
    intro a ha
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hK.rdata.B_le hb) a).mp ha.1, fun v hv => ?_⟩
    have hv' : b⁻¹ * v * b ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hK.B_le hb)) v).mp hv
      simpa using this
    have h1 := ha.2 _ hv'
    have h2 : b * a * b⁻¹ * v * (b * a * b⁻¹)⁻¹ * v⁻¹ =
        b * (a * (b⁻¹ * v * b) * a⁻¹ * (b⁻¹ * v * b)⁻¹) * b⁻¹ := by group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_center (hK.B_le hb)) _).mp h1
  obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp (hK.rdata.isPGroup.to_le hCR) hBC
    (fun b hb hb1 y hy => hK.fpf h22 h26i hp b hb hb1 y (hK.le (hCR hy)))
  have hlt : N₁ < C := lt_of_le_of_ne hN₁C fun h => hr₀N (h ▸ hr₀C)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := Subgroup.card_le_of_le hCR
  rw [hk, hK.card_center h22 h26i hp] at h1
  rw [hk, hK.card_R] at h2
  have hq := s.one_lt_q
  have hk1 : 1 < k := by
    have := (Nat.pow_lt_pow_iff_right hq).mp (by rwa [pow_one] : s.q ^ 1 < s.q ^ k)
    exact this
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hq).mp h2
  have hCeq : C = R := Subgroup.eq_of_le_of_card_ge hCR (by
    rw [hk, hK.card_R, show k = 2 by omega])
  have hrC : r ∈ C := hCeq ▸ hr
  exact hrC.2 v hv

theorem mul_pow_three
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {Y r : G}
    (hY : Y ∈ V) (hr : r ∈ R) : (Y * r) ^ 3 = Y ^ 3 := by
  have hc := hK.commutator_mem h22 h26i hp (R.inv_mem hr) (V.inv_mem hY)
  rw [inv_inv, inv_inv] at hc
  set c := r⁻¹ * Y⁻¹ * r * Y with hcdef
  have hcR : c ∈ R := hK.center_le hc
  have hYc : Y⁻¹ * c * Y = c := by
    rw [(Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 Y⁻¹ (V.inv_mem hY))]
    group
  have h1 : Y⁻¹ * r * Y = r * c := by rw [hcdef]; group
  have h2 : (Y⁻¹ * Y⁻¹) * r * (Y * Y) = r * c * c := by
    calc (Y⁻¹ * Y⁻¹) * r * (Y * Y) = Y⁻¹ * (Y⁻¹ * r * Y) * Y := by group
      _ = Y⁻¹ * (r * c) * Y := by rw [h1]
      _ = (Y⁻¹ * r * Y) * (Y⁻¹ * c * Y) := by group
      _ = r * c * c := by rw [h1, hYc]
  have hrc : r * c = c * r := hK.comm r hr c hcR
  have h3 : r * c * c * (r * c) * r = (r * c) ^ 3 := by
    calc r * c * c * (r * c) * r = (r * c) * (c * r) * (c * r) := by group
      _ = (r * c) ^ 3 := by rw [← hrc, pow_three']
  calc (Y * r) ^ 3 = Y ^ 3 * ((Y⁻¹ * Y⁻¹) * r * (Y * Y)) * (Y⁻¹ * r * Y) * r := by
        rw [pow_three' (Y * r)]; group
    _ = Y ^ 3 * (r * c * c * (r * c) * r) := by rw [h2, h1]; group
    _ = Y ^ 3 := by
        rw [h3, hK.pow_three h22 h26i hp (R.mul_mem hr hcR), mul_one]

end K3Data

end Frame5

end CFSG.Walter.W67
