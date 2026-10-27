module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19W

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

abbrev ch619I (T L V : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (ch6ZS T L V : Set G)

abbrev ch619W (T L V : Subgroup G) (z : G) : Subgroup G :=
  conjClosure V (ch619I T L V) ⊓ conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G))

abbrev ch619K1 (T L V : Subgroup G) (z : G) : Subgroup G :=
  centralizerMod (Subgroup.zpowers z) (ch619I T L V) (ch619W T L V z)

abbrev ch619K2 (T L V : Subgroup G) (z : G) : Subgroup G :=
  centralizerMod (ch6ZS T L V) (ch619I T L V) (ch619W T L V z)

namespace L619

theorem mem_normalizer_conjClosure {g : G} {Z X : Subgroup G}
    (hZ : g ∈ Subgroup.normalizer (Z : Set G)) (hX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure Z X : Set G) := by
  refine mem_normalizer_of_forall_conj_mem_of_le fun w hw => ?_
  have key : conjClosure Z X ≤ (conjClosure Z X).comap (MulAut.conj g).toMonoidHom := by
    refine CFSG.Quasithin.conjClosure_le fun x hx u hu => ?_
    show g * (x * u * x⁻¹) * g⁻¹ ∈ conjClosure Z X
    have e : g * (x * u * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * u * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact CFSG.Quasithin.mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hX x).mp hx)
      ((Subgroup.mem_normalizer_iff.mp hZ u).mp hu)
  exact key hw

omit [Finite G] in
theorem le_normalizer_zpowers {Y : Subgroup G} {z : G}
    (hY : Y ≤ Subgroup.centralizer ({z} : Set G)) :
    Y ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  intro g hg
  have hgz : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]
    exact hY hg
  exact Subgroup.centralizer_le_normalizer _ hgz

omit [Finite G] in
theorem centralizer_le_centralizer_singleton {Z : Subgroup G} {z : G} (hz : z ∈ Z) :
    Subgroup.centralizer (Z : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro i hi
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hi z hz).symm

omit [Finite G] in
theorem isElemAbelian_conjClosure {Z X : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hab : IsMulCommutative ↥(conjClosure Z X)) : IsElemAbelian 2 (conjClosure Z X) := by
  refine ⟨hab, fun x hx => ?_⟩
  have hcomm : ∀ a ∈ conjClosure Z X, ∀ b ∈ conjClosure Z X, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, -, u, hu, rfl⟩ := hx
    have hu2 : u ^ 2 = 1 := hZ.2 u hu
    rw [pow_two] at hu2 ⊢
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
    rw [pow_two] at iha ihb ⊢
    have hba : b * a = a * b := (hcomm a ha b hb).symm
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end L619

namespace L619

omit [Finite G] in
theorem normalizer_I_of {Y : Subgroup G}
    (hYZ : Y ≤ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    Y ≤ Subgroup.normalizer (ch619I T L V : Set G) :=
  hYZ.trans (F7.normalizer_le_normalizer_centralizer _)

theorem normalizer_W_of {Y : Subgroup G} {z : G}
    (hYV : Y ≤ Subgroup.normalizer (conjClosure V (ch619I T L V) : Set G))
    (hYZ : Y ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hYz : Y ≤ Subgroup.centralizer ({z} : Set G)) :
    Y ≤ Subgroup.normalizer (ch619W T L V z : Set G) := by
  intro g hg
  refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
  · exact hYV hg
  · exact mem_normalizer_conjClosure (hYZ hg) (Subgroup.le_normalizer (hYz hg))

theorem normalizer_K1_of {Y : Subgroup G} {z : G}
    (hYV : Y ≤ Subgroup.normalizer (conjClosure V (ch619I T L V) : Set G))
    (hYZ : Y ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hYz : Y ≤ Subgroup.centralizer ({z} : Set G)) :
    Y ≤ Subgroup.normalizer (ch619K1 T L V z : Set G) :=
  le_normalizer_centralizerMod (le_normalizer_zpowers hYz) (normalizer_I_of hYZ)
    (normalizer_W_of hYV hYZ hYz)

end L619

namespace Cfg619

variable (h : Hyp6116 G T M L V n)
include h

theorem pCoreOf_I_le_K2 (h432 : Stmt4_3_2) (z : G) :
    pCoreOf 2 (ch619I T L V) ≤ ch619K2 T L V z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_trans ?_ (centralizerMod_anti_right _ inf_le_left)
  have hIN : Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.normalizer (ch6ZS T L V : Set G) := Subgroup.centralizer_le_normalizer _
  have hTI : T ≤ Subgroup.normalizer
      ((Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) :=
    h.toHyp611Nat.T_le_normalizer_ZS.trans (F7.normalizer_le_normalizer_centralizer _)
  have hZO : ch6ZS T L V ≤ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((inf_le_left.trans h.toHyp611.le_T).trans le_sup_right)
      (sup_le hIN h.toHyp611Nat.T_le_normalizer_ZS)
      ((B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le inf_le_left)
  have hIT : IsInHS T M L V (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) := by
    refine ⟨⟨le_sup_right, fun h0 => h.toHyp611Nat.ZS_ne_bot ?_⟩,
      fun hle => h.not_le (le_sup_left.trans hle), ?_⟩
    · rw [← le_bot_iff, ← h0]; exact hZO
    · exact oTwoUpper_le_of_pow_mem fun x hx => exists_pow_mem_of_le_normalizer h.sylow.1 hTI hx
  have h17 := (stmt6_1_17 h432 G T M L V n h _ hIT).2.1.2.2
  rw [inf_eq_right.mpr le_sup_left] at h17
  intro x hx
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx,
    hIN (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx), fun u hu => ?_⟩
  have hu' : u ∈ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) :=
    conjClosure_mono le_rfl le_sup_left hu
  have h2 := Subgroup.commutator_mem_commutator hx hu'
  rw [Subgroup.commutator_comm, commutatorElement_def] at h2
  exact h17 h2

variable {H : Subgroup G} (c : Cfg619 T L V H n y)
include c

theorem commutator_E_K1_mem {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z) :
    ∀ e ∈ conjSub y V, ∀ k ∈ ch619K1 T L V z, e * k * e⁻¹ * k⁻¹ ∈ pCoreOf 2 (ch619I T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem : z ∈ ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) := hzZ ▸ Subgroup.mem_zpowers z
  have hIz : ch619I T L V ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    L619.le_normalizer_zpowers (L619.centralizer_le_centralizer_singleton hzmem.1)
  have hIK1 : ch619I T L V ≤ Subgroup.normalizer (ch619K1 T L V z : Set G) :=
    le_normalizer_centralizerMod hIz Subgroup.le_normalizer (centralizer_ZS_le_normalizer_W hzmem.1)
  have hK1N := (c.K1_le_normalizer_ZE h hz1 hzZ hVBF).trans
    ((F7.normalizer_le_normalizer_centralizer _).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  intro e he k hk
  have hEO := E_le_pCoreOf (y := y) h
  have h1 : e * k * e⁻¹ * k⁻¹ ∈
      pCoreOf 2 (Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G)) := by
    have hk' : k * e⁻¹ * k⁻¹ ∈
        pCoreOf 2 (Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G)) :=
      (Subgroup.mem_normalizer_iff.mp (hK1N hk) _).mp (Subgroup.inv_mem _ (hEO he))
    have e1 : e * k * e⁻¹ * k⁻¹ = e * (k * e⁻¹ * k⁻¹) := by group
    rw [e1]
    exact Subgroup.mul_mem _ (hEO he) hk'
  have h2 : e * k * e⁻¹ * k⁻¹ ∈ ch619K1 T L V z :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hIK1 (c.le_centralizer he)) k).mp hk)
      (Subgroup.inv_mem _ hk)
  exact c.pCoreOf_inf_K1_le h hz1 hzZ hVBF ⟨h1, h2⟩

theorem commutator_conjClosure_K1_mem {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z)
    {Y : Subgroup G} (hYI : Y ≤ Subgroup.normalizer (ch619I T L V : Set G))
    (hYK1 : Y ≤ Subgroup.normalizer (ch619K1 T L V z : Set G)) :
    ∀ x ∈ conjClosure (conjSub y V) Y, ∀ k ∈ ch619K1 T L V z,
      x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (ch619I T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEK1 := c.commutator_E_K1_mem h hz1 hzZ hVBF
  have hYO : Y ≤ Subgroup.normalizer (pCoreOf 2 (ch619I T L V) : Set G) :=
    hYI.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  let C : Subgroup G := centralizerMod (pCoreOf 2 (ch619I T L V)) ⊤ (ch619K1 T L V z)
  have hle : conjClosure (conjSub y V) Y ≤ C := by
    refine CFSG.Quasithin.conjClosure_le fun g hg e he => ?_
    have heO : e ∈ Subgroup.normalizer (pCoreOf 2 (ch619I T L V) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (c.le_centralizer he)
    refine ⟨trivial, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hYO hg) heO)
      (Subgroup.inv_mem _ (hYO hg)), fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g ∈ ch619K1 T L V z := by
      have := (Subgroup.mem_normalizer_iff.mp (hYK1 (Subgroup.inv_mem _ hg)) k).mp hk
      simpa using this
    have h1 := hEK1 e he _ hk'
    have e1 : g * e * g⁻¹ * k * (g * e * g⁻¹)⁻¹ * k⁻¹ =
        g * (e * (g⁻¹ * k * g) * e⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (hYO hg) _).mp h1
  intro x hx k hk
  exact (hle hx).2.2 k hk

end Cfg619

namespace Cfg619

variable (h : Hyp6116 G T M L V n)
include h

theorem le_K2_of_normal_of (h432 : Stmt4_3_2) {z : G} (hzS : z ∈ ch6ZS T L V)
    {X R : Subgroup G} (hXI : X ≤ ch619I T L V)
    (hIX : ch619I T L V ≤ Subgroup.normalizer (X : Set G))
    (hXK1 : ∀ x ∈ X, ∀ k ∈ ch619K1 T L V z, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (ch619I T L V))
    (hRX : R ≤ X) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (h2 : ∀ r ∈ R, ∃ m : ℕ, r ^ 2 ^ m ∈ ch619K2 T L V z) : R ≤ ch619K2 T L V z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := ch619I T L V with hI
  set K1 := ch619K1 T L V z with hK1
  set K2 := ch619K2 T L V z with hK2
  have hIN : I ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := Subgroup.centralizer_le_normalizer _
  have hIz : I ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    L619.le_normalizer_zpowers (L619.centralizer_le_centralizer_singleton hzS)
  have hzZ' : Subgroup.zpowers z ≤ ch6ZS T L V := Subgroup.zpowers_le.mpr hzS
  have hK1K2 : K1 ≤ K2 := fun k hk => ⟨hk.1, hIN hk.1, fun w hw => hzZ' (hk.2.2 w hw)⟩
  have hc : ∀ k ∈ X ⊓ K1, ∀ p ∈ X, k * p * k⁻¹ * p⁻¹ ∈ pCoreOf 2 X := by
    intro k hk p hp
    have h1 := hXK1 p hp k hk.2
    have h3 : k * p * k⁻¹ * p⁻¹ ∈ pCoreOf 2 I := by
      have := Subgroup.inv_mem _ h1
      have e1 : (p * k * p⁻¹ * k⁻¹)⁻¹ = k * p * k⁻¹ * p⁻¹ := by group
      rwa [e1] at this
    have h4 : k * p * k⁻¹ * p⁻¹ ∈ X :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.1 hp) (Subgroup.inv_mem _ hk.1))
        (Subgroup.inv_mem _ hp)
    exact F7.pCoreOf_inf_le hXI ⟨h3, h4⟩
  have hsq : ∀ k ∈ K2, k ^ 2 ∈ K1 := by
    intro k hk
    refine ⟨I.pow_mem hk.1 2, hIz (I.pow_mem hk.1 2), fun w hw => ?_⟩
    have ha := hk.2.2 w hw
    have hka : k * (k * w * k⁻¹ * w⁻¹) * k⁻¹ = k * w * k⁻¹ * w⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hk.1 _ ha
      calc k * (k * w * k⁻¹ * w⁻¹) * k⁻¹ = (k * w * k⁻¹ * w⁻¹) * k * k⁻¹ := by rw [this]
        _ = k * w * k⁻¹ * w⁻¹ := by group
    have ha2 : (k * w * k⁻¹ * w⁻¹) * (k * w * k⁻¹ * w⁻¹) = 1 := by
      rw [← pow_two]; exact h.toHyp611.isElemAbelian.2 _ ha.1
    have e1 : k ^ 2 * w * (k ^ 2)⁻¹ * w⁻¹ =
        (k * (k * w * k⁻¹ * w⁻¹) * k⁻¹) * (k * w * k⁻¹ * w⁻¹) := by
      rw [pow_two]; group
    rw [e1, hka, ha2]
    exact Subgroup.one_mem _
  have h2' : ∀ r ∈ R, ∃ m : ℕ, r ^ 2 ^ m ∈ X ⊓ K1 := by
    intro r hr
    obtain ⟨m, hm⟩ := h2 r hr
    refine ⟨m + 1, X.pow_mem (hRX hr) _, ?_⟩
    have := hsq _ hm
    rwa [← pow_mul, ← pow_succ] at this
  have hle := le_sup_pCoreOf_of_central inf_le_left hRX hXR hc h2'
  have hO : pCoreOf 2 X ≤ K2 :=
    (F7.pCoreOf_mono_of_le_normalizer hXI hIX).trans (pCoreOf_I_le_K2 h h432 z)
  exact hle.trans (sup_le (inf_le_right.trans hK1K2) hO)

omit h in
theorem commutator_inf_K1_mem {z : G} {X : Subgroup G} (hXI : X ≤ ch619I T L V)
    (hXK1 : ∀ x ∈ X, ∀ k ∈ ch619K1 T L V z, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (ch619I T L V)) :
    ∀ k ∈ X ⊓ ch619K1 T L V z, ∀ p ∈ X, k * p * k⁻¹ * p⁻¹ ∈ pCoreOf 2 X := by
  intro k hk p hp
  have h1 := hXK1 p hp k hk.2
  have h3 : k * p * k⁻¹ * p⁻¹ ∈ pCoreOf 2 (ch619I T L V) := by
    have := Subgroup.inv_mem _ h1
    have e1 : (p * k * p⁻¹ * k⁻¹)⁻¹ = k * p * k⁻¹ * p⁻¹ := by group
    rwa [e1] at this
  have h4 : k * p * k⁻¹ * p⁻¹ ∈ X :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.1 hp) (Subgroup.inv_mem _ hk.1))
      (Subgroup.inv_mem _ hp)
  exact F7.pCoreOf_inf_le hXI ⟨h3, h4⟩

theorem sq_mem_K1 {z : G} (hzS : z ∈ ch6ZS T L V) :
    ∀ k ∈ ch619K2 T L V z, k ^ 2 ∈ ch619K1 T L V z := by
  have hIz : ch619I T L V ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    L619.le_normalizer_zpowers (L619.centralizer_le_centralizer_singleton hzS)
  intro k hk
  refine ⟨(ch619I T L V).pow_mem hk.1 2, hIz ((ch619I T L V).pow_mem hk.1 2), fun w hw => ?_⟩
  have ha := hk.2.2 w hw
  have hka : k * (k * w * k⁻¹ * w⁻¹) * k⁻¹ = k * w * k⁻¹ * w⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hk.1 _ ha
    calc k * (k * w * k⁻¹ * w⁻¹) * k⁻¹ = (k * w * k⁻¹ * w⁻¹) * k * k⁻¹ := by rw [this]
      _ = k * w * k⁻¹ * w⁻¹ := by group
  have ha2 : (k * w * k⁻¹ * w⁻¹) * (k * w * k⁻¹ * w⁻¹) = 1 := by
    rw [← pow_two]; exact h.toHyp611.isElemAbelian.2 _ ha.1
  have e1 : k ^ 2 * w * (k ^ 2)⁻¹ * w⁻¹ =
      (k * (k * w * k⁻¹ * w⁻¹) * k⁻¹) * (k * w * k⁻¹ * w⁻¹) := by
    rw [pow_two]; group
  rw [e1, hka, ha2]
  exact Subgroup.one_mem _

theorem inf_K2_le_sup {z : G} (hzS : z ∈ ch6ZS T L V) {X : Subgroup G}
    (hXI : X ≤ ch619I T L V)
    (hXK1 : ∀ x ∈ X, ∀ k ∈ ch619K1 T L V z, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (ch619I T L V)) :
    X ⊓ ch619K2 T L V z ≤ (X ⊓ ch619K1 T L V z) ⊔ pCoreOf 2 X := by
  have hIN : ch619I T L V ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hIK2 : ch619I T L V ≤ Subgroup.normalizer (ch619K2 T L V z : Set G) :=
    le_normalizer_centralizerMod hIN Subgroup.le_normalizer (centralizer_ZS_le_normalizer_W hzS)
  have hXN : X ≤ Subgroup.normalizer ((X ⊓ ch619K2 T L V z : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hIK2 (hXI hx)⟩
  refine le_sup_pCoreOf_of_central inf_le_left inf_le_left hXN
    (commutator_inf_K1_mem hXI hXK1) fun r hr => ⟨1, X.pow_mem hr.1 _, ?_⟩
  simpa using sq_mem_K1 h hzS r hr.2

variable {H : Subgroup G} (c : Cfg619 T L V H n y)
include c

theorem commutator_W_conj_mem (h6110 : Stmt6_1_10)
    (hab : IsMulCommutative ↥(conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))))
    {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z)
    {g : G} (hg : g ∈ Subgroup.normalizer (ch619W T L V z : Set G))
    {e : G} (he : e ∈ conjSub y V) {w : G} (hw : w ∈ ch619W T L V z) :
    g * e * g⁻¹ * w * (g * e * g⁻¹)⁻¹ * w⁻¹ ∈ conjSub g (conjSub y (ch6ZS T L V)) := by
  have hWE := c.commutator_W_E h h6110 hab hz1 hzZ hVBF
  have hw' : g⁻¹ * w * g ∈ ch619W T L V z := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
    simpa using this
  have h1 : e * (g⁻¹ * w * g) * e⁻¹ * (g⁻¹ * w * g)⁻¹ ∈ conjSub y (ch6ZS T L V) := by
    have := Subgroup.commutator_mem_commutator hw' he
    rw [commutatorElement_def] at this
    have h2 := Subgroup.inv_mem _ (hWE this)
    have e1 : (g⁻¹ * w * g * e * (g⁻¹ * w * g)⁻¹ * e⁻¹)⁻¹ =
        e * (g⁻¹ * w * g) * e⁻¹ * (g⁻¹ * w * g)⁻¹ := by group
    rwa [e1] at h2
  refine mem_conjSub.mpr ?_
  have e2 : g⁻¹ * (g * e * g⁻¹ * w * (g * e * g⁻¹)⁻¹ * w⁻¹) * g =
      e * (g⁻¹ * w * g) * e⁻¹ * (g⁻¹ * w * g)⁻¹ := by group
  rw [e2]
  exact h1

theorem conj_ZE_le_W {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V))
    (hVBF : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z)
    {g : G} (hg : g ∈ Subgroup.normalizer (ch619W T L V z : Set G)) :
    conjSub g (conjSub y (ch6ZS T L V)) ≤ ch619W T L V z := by
  have := conjSub_mono g (c.ZE_le_W h hz1 hzZ hVBF)
  rwa [conjSub_eq_of_mem_normalizer' hg] at this

end Cfg619

omit [Finite G] in
theorem conj_ZE_inf_ZS {Z : Subgroup G} {y z g : G}
    (hzZ : Subgroup.zpowers z = Z ⊓ conjSub y Z)
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (hgz : g ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub g (conjSub y Z) ⊓ Z = Subgroup.zpowers z := by
  have h1 : conjSub g (Z ⊓ conjSub y Z) = Z ⊓ conjSub g (conjSub y Z) := by
    rw [conjSub_inf, conjSub_eq_of_mem_normalizer' hgZ]
  have h2 : conjSub g (Subgroup.zpowers z) = Subgroup.zpowers z := by
    apply conjSub_eq_of_mem_normalizer'
    exact L619.le_normalizer_zpowers le_rfl hgz
  rw [← hzZ, h2] at h1
  rw [inf_comm]
  exact h1.symm

end CFSG.Quasithin.H13
