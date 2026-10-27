module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

theorem mem_normalizer_of_conjSub_le' {g : G} {S : Subgroup G} (h : conjSub g S ≤ S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  have heq : conjSub g S = S := Subgroup.eq_of_le_of_card_ge h (by rw [card_conjSub'])
  refine B6.mem_normalizer_of_conjSub_le h ?_
  have := congrArg (conjSub g⁻¹) heq
  rw [conjSub_conjSub_inv] at this
  exact this.symm.le

theorem mem_normalizer_of_forall_conj_mem_of_le {g : G} {S : Subgroup G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  refine mem_normalizer_of_conjSub_le' fun x hx => ?_
  have := h _ (mem_conjSub.mp hx)
  simpa [mul_assoc] using this

theorem le_sup_pCoreOf_of_central {X Z₁ R : Subgroup G} (hZX : Z₁ ≤ X) (hRX : R ≤ X)
    (hRN : X ≤ Subgroup.normalizer (R : Set G))
    (hc : ∀ k ∈ Z₁, ∀ x ∈ X, k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 X)
    (h2 : ∀ r ∈ R, ∃ m : ℕ, r ^ 2 ^ m ∈ Z₁) : R ≤ Z₁ ⊔ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXA : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hA2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hQN : X ≤ Subgroup.normalizer ((Z₁ ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    intro x hx
    refine mem_normalizer_of_conjSub_le' ?_
    unfold conjSub
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro w ⟨k, hk, rfl⟩
      have e : (MulAut.conj x).toMonoidHom k = (x * k * x⁻¹ * k⁻¹) * k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hk)
      have := Subgroup.inv_mem _ (hc k hk x hx)
      have e' : (k * x * k⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * k⁻¹ := by group
      rwa [e'] at this
    · have := (conjSub_eq_of_mem_normalizer' (hXA hx)).le
      exact this.trans le_sup_right
  obtain ⟨S, hS, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ R) IsPGroup.of_bot
  have hSR : S ≤ R := hS.1
  have hRQS : R ≤ (R ⊓ (Z₁ ⊔ pCoreOf 2 X)) ⊔ S := by
    refine F7.isSylowTwoOf_le_sup_of_two_power hS ?_ fun r hr => ?_
    · intro r hr
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hr, hQN (hRX hr)⟩
    · obtain ⟨m, hm⟩ := h2 r hr
      exact ⟨m, R.pow_mem hr _, Subgroup.mem_sup_left hm⟩
  have hconjS : ∀ g ∈ X, (∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ pCoreOf 2 X) →
      g ∈ Subgroup.normalizer ((S ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    intro g hg hgs
    refine mem_normalizer_of_conjSub_le' ?_
    unfold conjSub
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro w ⟨s, hs, rfl⟩
      have e : (MulAut.conj g).toMonoidHom s = (g * s * g⁻¹ * s⁻¹) * s := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hgs s hs)) (Subgroup.mem_sup_left hs)
    · exact (conjSub_eq_of_mem_normalizer' (hXA hg)).le.trans le_sup_right
  have hZ₁N : Z₁ ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    intro k hk
    exact hconjS k (hZX hk) fun s hs => hc k hk s (hRX (hSR hs))
  have hAN : pCoreOf 2 X ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    intro a ha
    refine hconjS a (hAX ha) fun s hs => ?_
    have hs' : s * a⁻¹ * s⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp (hXA (hRX (hSR hs))) _).mp (Subgroup.inv_mem _ ha)
    have e : a * s * a⁻¹ * s⁻¹ = a * (s * a⁻¹ * s⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hs'
  have hSN : S ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    intro s hs
    refine mem_normalizer_of_conjSub_le' ?_
    unfold conjSub
    rw [Subgroup.map_sup]
    exact sup_le ((conjSub_eq_of_mem_normalizer' (Subgroup.le_normalizer hs)).le.trans le_sup_left)
      ((conjSub_eq_of_mem_normalizer' (hXA (hRX (hSR hs)))).le.trans le_sup_right)
  have hRN' : R ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 X : Subgroup G) : Set G) :=
    hRQS.trans (sup_le (inf_le_right.trans (sup_le hZ₁N hAN)) hSN)
  have hXN : X ≤ Subgroup.normalizer ((S ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    intro x hx
    have hxS : conjSub x S ≤ R := by
      have := conjSub_mono x hSR
      rwa [conjSub_eq_of_mem_normalizer' (hRN hx)] at this
    obtain ⟨r, hr, hle⟩ := F7.isSylowTwoOf_exists_conj_le hS hxS (hS.2.1.map _)
    refine mem_normalizer_of_conjSub_le' ?_
    calc conjSub x (S ⊔ pCoreOf 2 X) = conjSub x S ⊔ conjSub x (pCoreOf 2 X) := by
          unfold conjSub; rw [Subgroup.map_sup]
      _ ≤ conjSub r S ⊔ pCoreOf 2 X :=
          sup_le_sup hle (conjSub_eq_of_mem_normalizer' (hXA hx)).le
      _ ≤ conjSub r (S ⊔ pCoreOf 2 X) :=
          sup_le (conjSub_mono r le_sup_left)
            ((conjSub_eq_of_mem_normalizer' (hXA (hRX hr))).ge.trans (conjSub_mono r le_sup_right))
      _ = S ⊔ pCoreOf 2 X := conjSub_eq_of_mem_normalizer' (hRN' hr)
  have hSA2 : IsPGroup 2 (S ⊔ pCoreOf 2 X : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hS.2.1 hA2 ((hSR.trans hRX).trans hXA)
  have hSAle : S ⊔ pCoreOf 2 X ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (sup_le (hSR.trans hRX) hAX) hXN hSA2
  calc R ≤ (R ⊓ (Z₁ ⊔ pCoreOf 2 X)) ⊔ S := hRQS
    _ ≤ Z₁ ⊔ pCoreOf 2 X := sup_le inf_le_right ((le_sup_left.trans hSAle).trans le_sup_right)

omit [Finite G] in
theorem centralizer_ZS_le_normalizer_W {z : G} (hz : z ∈ ch6ZS T L V) :
    Subgroup.centralizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer
      ((conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)) : Subgroup G) : Set G) := by
  intro i hi
  have hiz : i ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hi z hz).symm
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_conjClosure V _ hi, le_normalizer_conjClosure (ch6ZS T L V) _ hiz⟩

omit [Finite G] in
theorem pCoreOf_conjSub' (g : G) (X : Subgroup G) :
    pCoreOf 2 (conjSub g X) = conjSub g (pCoreOf 2 X) := by
  unfold conjSub
  exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) X

namespace Cfg619

variable (h : Hyp6116 G T M L V n) (c : Cfg619 T L V H n y)
include h c

theorem ZE_le_W {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z) :
    conjSub y (ch6ZS T L V) ≤
      conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hZQ⟩ := c.qz h hz1 hzZ
  refine le_inf ?_ hZQ
  have hVBN : V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)) ≤
      Subgroup.normalizer (conjSub y V : Set G) ⊓
        Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G) :=
    le_inf (inf_le_right.trans inf_le_right)
      ((inf_le_right.trans inf_le_left).trans c.conjClosure_le)
  have hVB2 : IsPGroup 2 ↥(V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G))) :=
    (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le inf_le_left
  have hne : ⁅conjSub y V, V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G))⁆ ≠
      ⊥ := by
    intro h0
    apply hz1
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have h2 : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
        conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp (inf_le_left.trans h1))
    rw [hVBF] at h2
    have := Subgroup.mem_zpowers z
    rw [h2, Subgroup.mem_bot] at this
    exact this
  have hEB := h.toHyp611Nat.commutator_eq_conjSub y hVBN hVB2 hne
  rw [← hEB, Subgroup.commutator_comm]
  have hEI : conjSub y V ≤ Subgroup.normalizer
      ((conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) : Subgroup G) : Set G) :=
    c.le_centralizer.trans (le_normalizer_conjClosure V _)
  exact (Subgroup.commutator_mono (inf_le_left.trans (le_conjClosure V _)) le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hEI)

theorem commutator_W_E (h6110 : Stmt6_1_10)
    (hab : IsMulCommutative ↥(conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))))
    {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z) :
    ⁅conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)), conjSub y V⁆ ≤
      conjSub y (ch6ZS T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hQE, -⟩ := c.qz h hz1 hzZ
  have hzmem : z ∈ ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) := hzZ ▸ Subgroup.mem_zpowers z
  have hzS : z ∈ ch6ZS T L V := hzmem.1
  have hZEW := c.ZE_le_W h hz1 hzZ hVBF
  have hW0ab : ∀ a ∈ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)),
      ∀ b ∈ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVW0 : V ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) := le_conjClosure V _
  have hle1 : ⁅conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
      conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)), conjSub y V⁆ ≤
      (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) ⊓ conjSub y V := by
    refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (c.le_centralizer.trans (centralizer_ZS_le_normalizer_W hzS))
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hQE)
  refine hle1.trans ?_
  by_contra hne
  have hlt : conjSub y (ch6ZS T L V) <
      (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) ⊓ conjSub y V :=
    lt_of_le_not_ge (le_inf hZEW (conjSub_mono y inf_le_left)) hne
  have hEcard : Nat.card (conjSub y V) = 16 := by
    rw [card_conjSub', h.toHyp611Nat.natural.card_eq, c.n_eq]; norm_num
  have hZEcard : Nat.card (conjSub y (ch6ZS T L V)) = 4 := by
    rw [card_conjSub', h.toHyp611Nat.card_ZS, c.n_eq]; norm_num
  set WE := (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
    conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) ⊓ conjSub y V with hWE
  have hcardWE : 4 < Nat.card WE := by
    have h1 := Subgroup.card_le_of_le hlt.le
    have h2 : Nat.card WE ≠ 4 := by
      intro h4
      exact hne (Subgroup.eq_of_le_of_card_ge hlt.le (by rw [h4, hZEcard])).ge
    omega
  have hidx : WE.relIndex (conjSub y V) ≤ 2 := by
    have h1 := card_mul_relIndex_of_le (inf_le_right : WE ≤ conjSub y V)
    rw [hEcard] at h1
    have hdvd : Nat.card WE ∣ 16 := hEcard ▸ Subgroup.card_dvd_of_le inf_le_right
    have h8 : 8 ≤ Nat.card WE := by
      have h16 : Nat.card WE ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hk : Nat.card WE <;> omega
    by_contra h3
    push Not at h3
    have : Nat.card WE * 3 ≤ 16 := by
      calc Nat.card WE * 3 ≤ Nat.card WE * WE.relIndex (conjSub y V) :=
            Nat.mul_le_mul_left _ h3
        _ = 16 := h1
    omega
  have hE2 : IsPGroup 2 (conjSub y V) :=
    (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).map _
  have hm := mQuot_le_one_of_relIndex_le_two hE2 hidx
  have hcomm : ∀ a ∈ WE, ∀ v ∈ V, a * v = v * a :=
    fun a ha v hv => hW0ab a ha.1.1 v (hVW0 hv)
  have hVC : conjSub 1 V ≤ Subgroup.centralizer (WE : Set G) := by
    rw [conjSub_one]
    intro v hv
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha v hv
  have hWN : WE ≤ Subgroup.normalizer (conjSub 1 V : Set G) := by
    rw [conjSub_one]
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm a ha v hv).symm
  have hVE := h.toHyp611Nat.le_centralizer_conjSub_of_le h6110 (x := y) (y := 1) (B := WE)
    inf_le_right hWN hm hVC
  rw [conjSub_one] at hVE
  apply hz1
  have h0 : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_left.trans (hVE.trans (Subgroup.centralizer_le inf_le_left)))
  rw [hVBF] at h0
  have := Subgroup.mem_zpowers z
  rw [h0, Subgroup.mem_bot] at this
  exact this

theorem K1_le_normalizer_ZE {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z) :
    centralizerMod (Subgroup.zpowers z) (Subgroup.centralizer (ch6ZS T L V : Set G))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) ≤
      Subgroup.normalizer (conjSub y (ch6ZS T L V) : Set G) := by
  intro k hk
  refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
  have h1 := hk.2.2 x (c.ZE_le_W h hz1 hzZ hVBF hx)
  have h2 : Subgroup.zpowers z ≤ conjSub y (ch6ZS T L V) := hzZ ▸ inf_le_right
  have e : k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact Subgroup.mul_mem _ (h2 h1) hx

theorem pCoreOf_inf_K1_le {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z) :
    pCoreOf 2 (Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G)) ⊓
        centralizerMod (Subgroup.zpowers z) (Subgroup.centralizer (ch6ZS T L V : Set G))
          (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
            conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) ≤
      pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem : z ∈ ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) := hzZ ▸ Subgroup.mem_zpowers z
  have hK1N := (c.K1_le_normalizer_ZE h hz1 hzZ hVBF).trans
    ((F7.normalizer_le_normalizer_centralizer _).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hIz : Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    intro i hi
    have hiz : i ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hi z hzmem.1).symm
    exact Subgroup.centralizer_le_normalizer _ hiz
  have hIK1 := le_normalizer_centralizerMod hIz (Subgroup.le_normalizer)
    (centralizer_ZS_le_normalizer_W hzmem.1)
  have h1 : pCoreOf 2 (Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G)) ⊓
      centralizerMod (Subgroup.zpowers z) (Subgroup.centralizer (ch6ZS T L V : Set G))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) ≤
      pCoreOf 2 (centralizerMod (Subgroup.zpowers z) (Subgroup.centralizer (ch6ZS T L V : Set G))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)))) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hK1N hk, Subgroup.le_normalizer hk⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact h1.trans (F7.pCoreOf_mono_of_le_normalizer (centralizerMod_le_left _ _ _) hIK1)

omit c in
theorem E_le_pCoreOf :
    conjSub y V ≤ pCoreOf 2 (Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G)) := by
  have h1 := conjSub_mono y h.toHyp611Nat.V_le_pCoreOf_centralizer
  rwa [← pCoreOf_conjSub', conjSub_centralizer'] at h1

theorem not_le_K1 {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z) :
    ¬ conjSub y V ≤ centralizerMod (Subgroup.zpowers z)
      (Subgroup.centralizer (ch6ZS T L V : Set G))
      (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) := by
  intro hle
  apply c.not_le_pCoreOf
  have h1 : conjSub y V ≤ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
    (le_inf (E_le_pCoreOf h) hle).trans (c.pCoreOf_inf_K1_le h hz1 hzZ hVBF)
  exact (le_inf h1 (le_inf c.le_H c.le_centralizer)).trans (F7.pCoreOf_inf_le inf_le_right)

theorem not_le_K2 (h6110 : Stmt6_1_10)
    (hab : IsMulCommutative ↥(conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))))
    {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z) :
    ¬ conjSub y V ≤ centralizerMod (ch6ZS T L V) (Subgroup.centralizer (ch6ZS T L V : Set G))
      (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))) := by
  intro hle
  apply c.not_le_K1 h hz1 hzZ hVBF
  have hzmem : z ∈ ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) := hzZ ▸ Subgroup.mem_zpowers z
  have hWE := c.commutator_W_E h h6110 hab hz1 hzZ hVBF
  intro e he
  have heI := c.le_centralizer he
  have hez : e ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    have hiz : e ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp heI z hzmem.1).symm
    exact Subgroup.centralizer_le_normalizer _ hiz
  refine ⟨heI, hez, fun w hw => ?_⟩
  have h1 : e * w * e⁻¹ * w⁻¹ ∈ ch6ZS T L V := (hle he).2.2 w hw
  have h2 : e * w * e⁻¹ * w⁻¹ ∈ conjSub y (ch6ZS T L V) := by
    have := Subgroup.commutator_mem_commutator he hw
    rw [Subgroup.commutator_comm, commutatorElement_def] at this
    exact hWE this
  rw [hzZ]
  exact ⟨h1, h2⟩

theorem not_le_M (h432 : Stmt4_3_2) :
    ¬ conjClosure (conjSub y V) (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ M := by
  intro hle
  have hEM : conjSub y V ≤ M := (le_conjClosure _ _).trans hle
  have hEN : conjSub y V ≤ M ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    le_inf hEM (c.le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
  have h617 := (stmt6_1_7 h432 G T M L V n h.toHyp611Nat).1.2 (ch6ZS T L V)
    h.toHyp611Nat.ZS_ne_bot inf_le_left
  have hEV : conjSub y V ≤ Subgroup.normalizer (V : Set G) :=
    (hEN.trans h617).trans inf_le_right
  have := c.relIndex_F
  rw [inf_eq_left.mpr hEV, Subgroup.relIndex_self] at this
  norm_num at this

end Cfg619

end CFSG.Quasithin.H13
