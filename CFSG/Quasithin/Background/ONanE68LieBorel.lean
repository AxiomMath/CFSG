module

public import CFSG.Quasithin.Background.ONanE68LieMod
public import CFSG.Quasithin.Background.ONanE68LieBlock

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Defs

variable {G : Type} [Group G]

@[expose] def pgOf (T V L : Subgroup G) : Subgroup G :=
  (T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L

@[expose] def borOf (T V L : Subgroup G) : Subgroup G :=
  L ⊓ Subgroup.normalizer ((pgOf T V L : Subgroup G) : Set G)

variable {T V L : Subgroup G}

theorem pgOf_le_left : pgOf T V L ≤ L := inf_le_right

theorem pgOf_le_borOf : pgOf T V L ≤ borOf T V L := le_inf pgOf_le_left Subgroup.le_normalizer

theorem borOf_le_left : borOf T V L ≤ L := inf_le_left

theorem borOf_le_normalizer : borOf T V L ≤ Subgroup.normalizer (pgOf T V L : Set G) := inf_le_right

end Defs

section Pre

variable {G : Type} [Group G] {T V L : Subgroup G}

theorem sylowBar_eq : sylowBar T V L = ((pgOf T V L).subgroupOf L).map (piBar L) := rfl

theorem pre_sylowBar (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L) :
    Fin257.pre (piBar L) (sylowBar T V L) = pgOf T V L :=
  pre_img_eq pgOf_le_left hZ

theorem pre_borel (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L) :
    Fin257.pre (piBar L) (Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L))) =
      borOf T V L := by
  rw [Fin257.pre_normalizer piBar_surjective, pre_sylowBar hZ]
  rfl

theorem mem_borOf_iff (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L) {y : G} :
    y ∈ borOf T V L ↔
      ∃ hy : y ∈ L, piBar L ⟨y, hy⟩ ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)) := by
  rw [← pre_borel hZ, Fin257.mem_pre]

theorem exists_mem_borOf_of_mem_normalizer (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    {x : Bar.Qbar L} (hx : x ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L))) :
    ∃ y : G, y ∈ borOf T V L ∧ piG L y = x := by
  obtain ⟨l, rfl⟩ := piBar_surjective (L := L) x
  have hl : (l : G) ∈ borOf T V L := (mem_borOf_iff hZ).2 ⟨l.2, hx⟩
  exact ⟨l, hl, by rw [piG_of_mem l.2]⟩

theorem piG_mem_normalizer_of_mem_borOf (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    {y : G} (hy : y ∈ borOf T V L) :
    piG L y ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)) := by
  obtain ⟨hyL, hyN⟩ := (mem_borOf_iff hZ).1 hy
  rw [piG_of_mem hyL]
  exact hyN

end Pre

section Solvable

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_comm_le_pGroup {A N : Subgroup G} (hNA : N ≤ A) (hN : IsPGroup 2 N)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ N) : Group.IsSolvable ↥A := by
  have hN' : IsPGroup 2 (N.subgroupOf A) := hN.of_equiv (Subgroup.subgroupOfEquivOfLe hNA).symm
  have : Group.IsNilpotent (N.subgroupOf A) := hN'.isNilpotent
  have hker : (Abelianization.of : ↥A →* Abelianization ↥A).ker ≤
      (N.subgroupOf A).subtype.range := by
    rw [Abelianization.ker_of, Subgroup.range_subtype, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact Subgroup.mem_subgroupOf.2 (hc x x.2 y y.2)
  exact Group.isSolvable_of_ker_le_range _ _ hker

variable {T V L : Subgroup G}

omit [Finite G] in
theorem comm_mem_pgOf (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L) {x y : G} (hx : x ∈ borOf T V L)
    (hy : y ∈ borOf T V L) : x * y * x⁻¹ * y⁻¹ ∈ pgOf T V L := by
  obtain ⟨hxL, hxN⟩ := (mem_borOf_iff hZ).1 hx
  obtain ⟨hyL, hyN⟩ := (mem_borOf_iff hZ).1 hy
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ Fin257.pre (piBar L) (sylowBar T V L) := by
    have hL : x * y * x⁻¹ * y⁻¹ ∈ L := L.mul_mem (L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL))
      (L.inv_mem hyL)
    refine Fin257.mem_pre.2 ⟨hL, ?_⟩
    have e : (⟨x * y * x⁻¹ * y⁻¹, hL⟩ : ↥L) = ⟨x, hxL⟩ * ⟨y, hyL⟩ * ⟨x, hxL⟩⁻¹ * ⟨y, hyL⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hquot _ hxN _ hyN
  rwa [pre_sylowBar hZ] at hmem

theorem isSolvable_borOf (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    (hP2 : IsPGroup 2 (pgOf T V L))
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L) : Group.IsSolvable ↥(borOf T V L) :=
  isSolvable_of_comm_le_pGroup pgOf_le_borOf hP2 fun _ hx _ hy => comm_mem_pgOf hZ hquot hx hy

omit [Finite G] in
theorem charTwo_borOf_of_centralizer_le (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    (hP2 : IsPGroup 2 (pgOf T V L))
    (hcent : ∀ y : Bar.Qbar L, (∀ p ∈ sylowBar T V L, y * p = p * y) → y ∈ sylowBar T V L) :
    CharTwo (borOf T V L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : pgOf T V L ≤ pCoreOf 2 (borOf T V L) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 pgOf_le_borOf borOf_le_normalizer hP2
  intro y hy
  obtain ⟨hyB, hyC⟩ := hy
  obtain ⟨hyL, -⟩ := (mem_borOf_iff hZ).1 hyB
  have hyP : piBar L ⟨y, hyL⟩ ∈ sylowBar T V L := by
    apply hcent
    rintro _ ⟨p, hp, rfl⟩
    have hpP : (p : G) ∈ pgOf T V L := Subgroup.mem_subgroupOf.1 hp
    have hcomm : (y : G) * p = p * y :=
      (Subgroup.mem_centralizer_iff.1 hyC p (hPN hpP)).symm
    have e : (⟨y, hyL⟩ : ↥L) * p = p * ⟨y, hyL⟩ := Subtype.ext hcomm
    rw [← map_mul, ← map_mul, e]
  have hy' : y ∈ Fin257.pre (piBar L) (sylowBar T V L) := Fin257.mem_pre.2 ⟨hyL, hyP⟩
  rw [pre_sylowBar hZ] at hy'
  exact hPN hy'

theorem pCoreOf_borOf (hP : IsSylowTwoOf (pgOf T V L) L) :
    pCoreOf 2 (borOf T V L) = pgOf T V L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf (A4.isSylowTwoOf_mono hP pgOf_le_borOf
      borOf_le_left)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 pgOf_le_borOf borOf_le_normalizer
      hP.2.1

theorem charTwo_borOf_iff (hP : IsSylowTwoOf (pgOf T V L) L) :
    CharTwo (borOf T V L) ↔ ∀ y ∈ borOf T V L, (∀ p ∈ pgOf T V L, y * p = p * y) →
      y ∈ pgOf T V L := by
  unfold CharTwo
  rw [pCoreOf_borOf hP]
  constructor
  · intro h y hy hc
    exact h ⟨hy, Subgroup.mem_centralizer_iff.2 fun p hp => (hc p hp).symm⟩
  · rintro h y ⟨hy, hc⟩
    exact h y hy fun p hp => (Subgroup.mem_centralizer_iff.1 hc p hp).symm

end Solvable

section Normalizer

variable {G : Type} [Group G]

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) :
      Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact and_congr (hA x) (hB x)

theorem mem_normalizer_normalizer {A : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.normalizer (A : Set G) : Subgroup G) : Set G) := by
  have hA' := Subgroup.mem_normalizer_iff.1 hA
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ y, y ∈ A ↔ g⁻¹ * y * g ∈ A := fun y => by
    have := hA' (g⁻¹ * y * g)
    rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
    exact this.symm
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    have e1 : g⁻¹ * (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ := by group
    have h2 := key (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹)
    rw [e1] at h2
    exact ((key y).trans (hx _)).trans h2.symm
  · intro hx y
    have e1 : g * (x * y * x⁻¹) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
    have h2 := hA' (x * y * x⁻¹)
    rw [e1] at h2
    exact ((hA' y).trans (hx _)).trans h2.symm

theorem mem_normalizer_inf_le {Q L : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (L : Set G)) :
    Q ≤ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) :=
  fun _ hq => mem_normalizer_inf (Subgroup.le_normalizer hq) (hQN hq)

variable {T V L : Subgroup G}

theorem le_normalizer_borOf (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤
    Subgroup.normalizer (L : Set G)) :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (borOf T V L : Set G) := by
  intro q hq
  have hL := hQN hq
  have hP : q ∈ Subgroup.normalizer (pgOf T V L : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hq) hL
  exact mem_normalizer_inf hL (mem_normalizer_normalizer hP)

end Normalizer

section Lift

variable {G : Type} [Group G] [Finite G] {T V L : Subgroup G}

theorem relIndex_le_of_comm_count {c : G} (hcL : c ∈ L) {W₀ : Subgroup G} {k : ℕ}
    (hW : Nat.card W₀ ≤ k) (hcomm : ∀ d ∈ pgOf T V L, d * c * d⁻¹ * c⁻¹ ∈ W₀) :
    (sylowBar T V L ⊓ Subgroup.centralizer ({piBar L ⟨c, hcL⟩} : Set (Bar.Qbar L))).relIndex
      (sylowBar T V L) ≤ k := by
  set Wbar : Subgroup (Bar.Qbar L) := (W₀.subgroupOf L).map (piBar L) with hWbar
  have h0 : Nat.card (W₀.subgroupOf L) ≤ Nat.card W₀ :=
    Nat.card_le_card_of_injective
      (fun x : W₀.subgroupOf L => (⟨(x.1 : G), Subgroup.mem_subgroupOf.1 x.2⟩ : W₀))
      (fun x y hxy => by
        have := congrArg (fun z : W₀ => (z : G)) hxy
        exact Subtype.ext (Subtype.ext this))
  have h1 : Nat.card Wbar ≤ Nat.card (W₀.subgroupOf L) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (W₀.subgroupOf L) (piBar L))
  have h2 := relIndex_centralizer_le_card (D := sylowBar T V L) (W := Wbar)
    (c := piBar L ⟨c, hcL⟩) (by
      rintro _ ⟨p, hp, rfl⟩
      have hpP : (p : G) ∈ pgOf T V L := Subgroup.mem_subgroupOf.1 hp
      refine ⟨⟨(p : G) * c * (p : G)⁻¹ * c⁻¹, L.mul_mem (L.mul_mem (L.mul_mem p.2 hcL)
        (L.inv_mem p.2)) (L.inv_mem hcL)⟩, Subgroup.mem_subgroupOf.2 (hcomm _ hpP), ?_⟩
      show piBar L (p * ⟨c, hcL⟩ * p⁻¹ * ⟨c, hcL⟩⁻¹) = _
      rw [map_mul, map_mul, map_mul, map_inv, map_inv])
  exact h2.trans (h1.trans (h0.trans hW))

omit [Finite G] in
theorem orderOf_piG_eq_three (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) {c : G} (hcL : c ∈ L)
    (hc3 : orderOf c = 3) : orderOf (piG L c) = 3 := by
  rw [piG_of_mem hcL]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c' : ↥L := ⟨c, hcL⟩ with hc'
  have hc'3 : orderOf c' = 3 := by rw [← hc3]; exact (Subgroup.orderOf_coe c').symm
  have hpow : piBar L c' ^ 3 = 1 := by
    rw [← map_pow, ← hc'3, pow_orderOf_eq_one, map_one]
  refine orderOf_eq_prime hpow fun h1 => ?_
  have hmem : c' ∈ Subgroup.center ↥L := by
    rw [← ker_piBar, MonoidHom.mem_ker]
    exact h1
  obtain ⟨k, hk⟩ := hZ2 ⟨c', hmem⟩
  have h2 : c' ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := hc'3 ▸ orderOf_dvd_of_pow_eq_one h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem exceptional_of_comm_count (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hord : ∀ c ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), orderOf c = 3 →
      4 < (sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L))).relIndex
        (sylowBar T V L) ∨
      (Nat.card (sylowBar T V L) = 4 ∧
        sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L)) = ⊥))
    (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    {c : G} (hc : c ∈ borOf T V L) (hc3 : orderOf c = 3) {W₀ : Subgroup G}
    (hW : Nat.card W₀ ≤ 4) (hcomm : ∀ d ∈ pgOf T V L, d * c * d⁻¹ * c⁻¹ ∈ W₀) :
    Nat.card (sylowBar T V L) = 4 ∧
      sylowBar T V L ⊓ Subgroup.centralizer ({piG L c} : Set (Bar.Qbar L)) = ⊥ := by
  have hcL : c ∈ L := borOf_le_left hc
  have hcN := piG_mem_normalizer_of_mem_borOf hZ hc
  have h3 := orderOf_piG_eq_three hZ2 hcL hc3
  have hle := relIndex_le_of_comm_count (T := T) (V := V) hcL hW hcomm
  rw [← piG_of_mem hcL] at hle
  rcases hord _ hcN h3 with h4 | h4
  · exact absurd hle (not_le.2 h4)
  · exact h4

end Lift

section Main

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem comm_le_centralizer_of_exceptional (hInn : Ch1.EvenLieAutInner)
    (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L)) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hord : ∀ c ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), orderOf c = 3 →
      4 < (sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L))).relIndex
        (sylowBar T V L) ∨
      (Nat.card (sylowBar T V L) = 4 ∧
        sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L)) = ⊥))
    {c : G} (hc : c ∈ borOf T V L) (hc3 : orderOf c = 3) {W₀ : Subgroup G}
    (hW : Nat.card W₀ ≤ 4) (hcomm : ∀ d ∈ pgOf T V L, d * c * d⁻¹ * c⁻¹ ∈ W₀) :
    (Nat.card (sylowBar T V L) = 4 ∧
      sylowBar T V L ⊓ Subgroup.centralizer ({piG L c} : Set (Bar.Qbar L)) = ⊥) ∧
    ∀ a ∈ V, c * a = a * c → a ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L := center_le_sylow h hU hL hZ2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hcL : c ∈ L := borOf_le_left hc
  obtain ⟨θ, hθ, hθZ⟩ := exists_theta hInn hmod h hU hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  have hexc := exceptional_of_comm_count hZ2 hord hZ hc hc3 hW hcomm
  refine ⟨hexc, fun a haV hac => ?_⟩
  have h1 := theta_comm_of_comm hVN θ hθ ⟨c, hcL⟩ ⟨a, haV⟩ hac
  have hmem : θ ⟨a, haV⟩ ∈ sylowBar T V L := (mem_omegaCenter.1 (hθZ ⟨a, haV⟩)).1
  have hcen : θ ⟨a, haV⟩ ∈ Subgroup.centralizer ({piG L c} : Set (Bar.Qbar L)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, piG_of_mem hcL]
    exact h1.symm
  have h0 : θ ⟨a, haV⟩ ∈ sylowBar T V L ⊓ Subgroup.centralizer ({piG L c} : Set (Bar.Qbar L)) :=
    ⟨hmem, hcen⟩
  rw [hexc.2, Subgroup.mem_bot] at h0
  exact (theta_eq_one_iff hVN θ hθ hZ0 hperf ⟨a, haV⟩).1 h0

theorem borel_le_M_or_small (hInn : Ch1.EvenLieAutInner)
    (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L)) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) (hCh : CharTwo (borOf T V L))
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L)
    (hord : ∀ c ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), orderOf c = 3 →
      4 < (sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L))).relIndex
        (sylowBar T V L) ∨
      (Nat.card (sylowBar T V L) = 4 ∧
        sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L)) = ⊥)) :
    borOf T V L ≤ M ∨
      ((∃ c ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), orderOf c = 3 ∧
          Nat.card (sylowBar T V L) = 4 ∧
          sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L)) = ⊥) ∧
        (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2) := by
  classical
  have hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L := center_le_sylow h hU hL hZ2
  have hPg2 : IsPGroup 2 (pgOf T V L) := h.isPGroup_Q.to_le inf_le_left
  have hsolv := isSolvable_borOf hZ hPg2 hquot
  have hQN' := le_normalizer_borOf (V := V) hQN
  have hKH : borOf T V L ≤ Subgroup.centralizer (U : Set G) := borOf_le_left.trans hL.1
  have hQP : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (pgOf T V L : Set G) :=
    mem_normalizer_inf_le hQN
  have hDn : borOf T V L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) ≤
      Subgroup.normalizer (pgOf T V L : Set G) := sup_le borOf_le_normalizer hQP
  have hDK : pgOf T V L ≤ borOf T V L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) :=
    inf_le_left.trans le_sup_right
  rcases borel_le_M_or_alt3 h hU hKH hQN' hCh hsolv hPg2 hDn hDK with hle | ⟨B', c, hcK, hc3,
    hU4, hcomm, hrel, hLeq⟩
  · exact Or.inl hle
  · right
    have hcL : c ∈ L := borOf_le_left hcK
    obtain ⟨hexc, hcent⟩ := comm_le_centralizer_of_exceptional hInn hmod h hU hL hZ2 hord hcK hc3
      (W₀ := blockU B') (by rw [hU4]) hcomm
    have hcB' : c ∈ B' := by
      rw [hLeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    have hsub : V ⊓ Subgroup.centralizer (B' : Set G) ≤ V ⊓ Subgroup.centralizer (L : Set G) :=
      fun a ⟨haV, haC⟩ => ⟨haV, hcent a haV (Subgroup.mem_centralizer_iff.1 haC c hcB')⟩
    have hdvd := Subgroup.relIndex_dvd_of_le_left V hsub
    have hne : (V ⊓ Subgroup.centralizer (B' : Set G)).relIndex V ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    exact ⟨⟨piG L c, piG_mem_normalizer_of_mem_borOf hZ hcK, orderOf_piG_eq_three hZ2 hcL hc3,
      hexc⟩, (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hrel⟩

theorem borel_le_M_of_strict (hInn : Ch1.EvenLieAutInner)
    (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L)) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) (hCh : CharTwo (borOf T V L))
    (hquot : ∀ a ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        a * b * a⁻¹ * b⁻¹ ∈ sylowBar T V L)
    (hord : ∀ c ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), orderOf c = 3 →
      4 < (sylowBar T V L ⊓ Subgroup.centralizer ({c} : Set (Bar.Qbar L))).relIndex
        (sylowBar T V L)) : borOf T V L ≤ M := by
  rcases borel_le_M_or_small hInn hmod h hU hL hQN hZ2 hCh hquot
      (fun c hc h3 => Or.inl (hord c hc h3)) with hle | ⟨⟨c, hc, hc3, hcard, hbot⟩, -⟩
  · exact hle
  · exfalso
    have h4 := hord c hc hc3
    rw [hbot, Subgroup.relIndex_bot_left, hcard] at h4
    exact lt_irrefl _ h4

end Main

end E68Proof

end E6

end CFSG.Quasithin
