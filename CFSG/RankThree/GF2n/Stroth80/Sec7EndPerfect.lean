module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndInf
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Perf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section EndLemmaP

variable {X : Type} [Group X] [Finite X]

noncomputable def endgConjAut (L : Subgroup X) (k : X)
    (hk : ∀ l ∈ L, k * l * k⁻¹ ∈ L) (hk' : ∀ l ∈ L, k⁻¹ * l * k ∈ L) : MulAut ↥L where
  toFun l := ⟨k * l * k⁻¹, hk l l.2⟩
  invFun l := ⟨k⁻¹ * l * k, hk' l l.2⟩
  left_inv l := by ext; simp [mul_assoc]
  right_inv l := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem endg_perfect_odd {G : Type} [Group G] [Finite G] (hperf : commutator G = ⊤)
    (hcyc : ∀ P : Subgroup G, IsPGroup 2 P → IsCyclic ↥P) : ¬ 2 ∣ Nat.card G := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h2
  have hpg : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht]; norm_num
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have htP : t ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers t)
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  exact CFSG.GH74.GLS.Stage2.Final.Thm6.L20.not_cyclic_sylow_of_perfect hperf P
    (hcyc _ P.isPGroup') ht1 htP ht2

noncomputable def endgOuterHom (L Kp : Subgroup X)
    (hn : ∀ k ∈ Kp, ∀ l ∈ L, k * l * k⁻¹ ∈ L) : ↥Kp →* Outer ↥L where
  toFun k := QuotientGroup.mk (endgConjAut L (k : X) (hn k k.2)
    (fun l hl => by simpa using hn (k : X)⁻¹ (Kp.inv_mem k.2) l hl))
  map_one' := by
    refine (QuotientGroup.eq_one_iff _).mpr ⟨1, ?_⟩
    ext l; simp [endgConjAut]
  map_mul' a b := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    ext l; simp [endgConjAut, mul_assoc]

theorem endg_outerHom_eq_one_iff (L Kp : Subgroup X)
    (hn : ∀ k ∈ Kp, ∀ l ∈ L, k * l * k⁻¹ ∈ L) (k : ↥Kp) :
    endgOuterHom L Kp hn k = 1 ↔ ∃ l ∈ L, ∀ y ∈ L, (k : X) * y * (k : X)⁻¹ = l * y * l⁻¹ := by
  show QuotientGroup.mk _ = (1 : Outer ↥L) ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l, l.2, fun y hy => ?_⟩
    have := congrArg (fun a : MulAut ↥L => ((a ⟨y, hy⟩ : ↥L) : X)) hl
    simpa [endgConjAut] using this.symm
  · rintro ⟨l, hlL, hl⟩
    refine ⟨⟨l, hlL⟩, ?_⟩
    ext y
    simpa [endgConjAut] using (hl y y.2).symm

theorem endg_inner_action (L Kp : Subgroup X)
    (hn : ∀ k ∈ Kp, ∀ l ∈ L, k * l * k⁻¹ ∈ L) (hout : OutCyc ↥L) (hKp : ⁅Kp, Kp⁆ = Kp)
    (hPQ : ∀ J : Subgroup X, J ≤ Kp → (J.subgroupOf Kp).Normal → J ≠ Kp →
      16 ∣ (J.subgroupOf Kp).index) :
    ∀ k ∈ Kp, ∃ l ∈ L, ∀ y ∈ L, k * y * k⁻¹ = l * y * l⁻¹ := by
  set Φ := endgOuterHom L Kp hn with hΦ
  have hker : Φ.ker = ⊤ := by
    by_contra hne
    set J : Subgroup X := Φ.ker.map Kp.subtype with hJ
    have hJK : J ≤ Kp := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hJsub : J.subgroupOf Kp = Φ.ker := by
      rw [hJ]
      exact Subgroup.comap_map_eq_self_of_injective Kp.subtype_injective Φ.ker
    have hJne : J ≠ Kp := by
      intro h
      apply hne
      rw [← hJsub, h]
      exact Subgroup.subgroupOf_self Kp
    have h16 := hPQ J hJK (by rw [hJsub]; infer_instance) hJne
    rw [hJsub, Subgroup.index_ker] at h16
    haveI : Group.IsPerfect ↥Kp := Subgroup.isPerfect_iff.mpr hKp
    haveI : Group.IsPerfect ↥Φ.range := Group.IsPerfect.range Φ
    have hperf : commutator ↥Φ.range = ⊤ := Group.isPerfect_def.mp inferInstance
    refine endg_perfect_odd hperf (fun P hP => ?_) (dvd_trans (by norm_num) h16)
    have hc : IsCyclic ↥(P.map Φ.range.subtype) := hout _ (hP.map Φ.range.subtype)
    exact (Subgroup.equivMapOfInjective P Φ.range.subtype Φ.range.subtype_injective).isCyclic.mpr hc
  intro k hk
  have h1 : Φ ⟨k, hk⟩ = 1 := by
    have : (⟨k, hk⟩ : ↥Kp) ∈ Φ.ker := by rw [hker]; exact Subgroup.mem_top _
    exact this
  exact (endg_outerHom_eq_one_iff L Kp hn ⟨k, hk⟩).mp h1

theorem endg_split_hom {L C Kp : Subgroup X} (hC : ∀ c ∈ C, ∀ l ∈ L, c * l = l * c)
    (hLC : L ⊓ C = ⊥) (hK : ∀ k ∈ Kp, ∃ l ∈ L, ∃ c ∈ C, k = l * c) :
    ∃ φ : ↥Kp →* ↥L, (∀ k : ↥Kp, ∃ c ∈ C, (k : X) = (φ k : X) * c) ∧
      ∀ k : ↥Kp, φ k = 1 ↔ (k : X) ∈ C := by
  have huniq : ∀ {l l' c c' : X}, l ∈ L → l' ∈ L → c ∈ C → c' ∈ C → l * c = l' * c' → l = l' := by
    intro l l' c c' hl hl' hc hc' h
    have h1 : l'⁻¹ * l ∈ L ⊓ C := by
      refine ⟨L.mul_mem (L.inv_mem hl') hl, ?_⟩
      have : l'⁻¹ * l = c' * c⁻¹ := by
        have h2 : l = l' * c' * c⁻¹ := by rw [← h]; group
        rw [h2]; group
      rw [this]
      exact C.mul_mem hc' (C.inv_mem hc)
    rw [hLC, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1).symm
  choose l hl c hc hk using fun k : ↥Kp => hK (k : X) k.2
  have hmul : ∀ a b : ↥Kp, l (a * b) = l a * l b := by
    intro a b
    refine huniq (l := l (a * b)) (l' := l a * l b) (c := c (a * b)) (c' := c a * c b)
      (hl _) (L.mul_mem (hl a) (hl b)) (hc _) (C.mul_mem (hc a) (hc b)) ?_
    have e1 : ((a * b : ↥Kp) : X) = l (a * b) * c (a * b) := hk (a * b)
    have e2 : ((a * b : ↥Kp) : X) = (a : X) * (b : X) := rfl
    have e3 : (a : X) * (b : X) = l a * c a * (l b * c b) := by rw [← hk a, ← hk b]
    have e4 : l a * c a * (l b * c b) = l a * l b * (c a * c b) := by
      have := hC (c a) (hc a) (l b) (hl b)
      calc l a * c a * (l b * c b) = l a * (c a * l b) * c b := by group
        _ = l a * (l b * c a) * c b := by rw [this]
        _ = l a * l b * (c a * c b) := by group
    rw [← e1, e2, e3, e4]
  have hone : l 1 = 1 := by
    refine huniq (l := l 1) (l' := 1) (c := c 1) (c' := 1) (hl _) L.one_mem (hc _) C.one_mem ?_
    have := hk 1
    simpa using this.symm
  refine ⟨{ toFun := fun k => ⟨l k, hl k⟩
            map_one' := Subtype.ext hone
            map_mul' := fun a b => Subtype.ext (hmul a b) }, fun k => ⟨c k, hc k, hk k⟩, ?_⟩
  intro k
  constructor
  · intro h1
    have : (l k) = 1 := congrArg Subtype.val h1
    rw [hk k, this, one_mul]
    exact hc k
  · intro hkC
    apply Subtype.ext
    show l k = 1
    refine huniq (l := l k) (l' := 1) (c := c k) (c' := (k : X)) (hl _) L.one_mem (hc _) hkC ?_
    rw [one_mul]
    exact (hk k).symm

theorem endg_lemmaP {L Kp : Subgroup X} {z : X} (hLs : IsSimpleGroup ↥L)
    (hLnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (hout : OutCyc ↥L)
    (hdich : (∀ w : ↥L, orderOf w = 2 → Group.IsSolvable ↥(Subgroup.centralizer ({w} : Set ↥L))) ∨
      ∀ T : Sylow 2 ↥L, Nat.card (T : Subgroup ↥L) ≤ 8)
    (hKp : ⁅Kp, Kp⁆ = Kp) (hn : ∀ k ∈ Kp, ∀ l ∈ L, k * l * k⁻¹ ∈ L)
    (hz : z ∈ L) (hz1 : z ≠ 1) (hz2 : z * z = 1) (hKz : ∀ k ∈ Kp, k * z = z * k)
    (hact : ∃ k ∈ Kp, ∃ l ∈ L, k * l ≠ l * k)
    (hPQ : ∀ J : Subgroup X, J ≤ Kp → (J.subgroupOf Kp).Normal → J ≠ Kp →
      16 ∣ (J.subgroupOf Kp).index) : False := by
  set C : Subgroup X := Subgroup.centralizer (L : Set X) with hCdef
  have hC : ∀ c ∈ C, ∀ l ∈ L, c * l = l * c := fun c hc l hl =>
    (Subgroup.mem_centralizer_iff.mp hc l hl).symm
  have hLC : L ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxC⟩
    have hxz : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rcases (Subgroup.center ↥L).normal_of_characteristic.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.mem_bot] at hxz
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxz)
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hLnc
      apply hab
      have hmem : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L := by rw [ht]; exact Subgroup.mem_top _
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨b, hb⟩).symm
  have hinner := endg_inner_action L Kp hn hout hKp hPQ
  have hK : ∀ k ∈ Kp, ∃ l ∈ L, ∃ c ∈ C, k = l * c := by
    intro k hk
    obtain ⟨l, hl, hly⟩ := hinner k hk
    refine ⟨l, hl, l⁻¹ * k, ?_, by group⟩
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hly y hy
    have : l⁻¹ * k * y = y * (l⁻¹ * k) := by
      calc l⁻¹ * k * y = l⁻¹ * (k * y * k⁻¹) * k := by group
        _ = l⁻¹ * (l * y * l⁻¹) * k := by rw [h1]
        _ = y * (l⁻¹ * k) := by group
    exact this.symm
  obtain ⟨φ, hφ1, hφ2⟩ := endg_split_hom hC hLC hK
  set J : Subgroup X := Kp ⊓ C with hJ
  have hJK : J ≤ Kp := inf_le_left
  have hJsub : J.subgroupOf Kp = φ.ker := by
    ext k
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hφ2]
    exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩
  have hJne : J ≠ Kp := by
    intro h
    obtain ⟨k, hk, l, hl, hkl⟩ := hact
    have : k ∈ J := by rw [h]; exact hk
    exact hkl (hC k this.2 l hl)
  have h16 := hPQ J hJK (by rw [hJsub]; infer_instance) hJne
  rw [hJsub, Subgroup.index_ker] at h16
  haveI : Group.IsPerfect ↥Kp := Subgroup.isPerfect_iff.mpr hKp
  haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  set zL : ↥L := ⟨z, hz⟩ with hzL
  have hzL2 : orderOf zL = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · ext; simp [hzL, pow_two, hz2]
    · intro h; apply hz1; exact congrArg Subtype.val h
  have hle : φ.range ≤ Subgroup.centralizer ({zL} : Set ↥L) := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨c, hc, hkc⟩ := hφ1 k
    apply Subtype.ext
    show (φ k : X) * z = z * (φ k : X)
    have hφk : (φ k : X) = (k : X) * c⁻¹ := by rw [hkc]; group
    have hcz : c * z = z * c := hC c hc z hz
    have hcz' : c⁻¹ * z = z * c⁻¹ := by
      calc c⁻¹ * z = c⁻¹ * (z * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * z) * c⁻¹ := by rw [hcz]
        _ = z * c⁻¹ := by group
    rw [hφk]
    calc (k : X) * c⁻¹ * z = (k : X) * (c⁻¹ * z) := by group
      _ = (k : X) * (z * c⁻¹) := by rw [hcz']
      _ = ((k : X) * z) * c⁻¹ := by group
      _ = (z * (k : X)) * c⁻¹ := by rw [hKz k k.2]
      _ = z * ((k : X) * c⁻¹) := by group
  have hnt : Nontrivial ↥φ.range := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h0 : 0 < Nat.card ↥φ.range := Nat.card_pos
    have := Nat.le_of_dvd h0 (dvd_trans (show (2 : ℕ) ∣ 16 by norm_num) h16)
    omega
  rcases hdich with hsolv | hsyl
  · haveI := hsolv zL hzL2
    haveI : Group.IsSolvable ↥φ.range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hd : 2 ^ 4 ∣ Nat.card ↥L := by
      have := (Subgroup.card_subgroup_dvd_card φ.range)
      exact dvd_trans (by norm_num [show (2 : ℕ) ^ 4 = 16 by norm_num]) (dvd_trans h16 this)
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd
    have hHp : IsPGroup 2 H := IsPGroup.of_card hH
    obtain ⟨T, hT⟩ := hHp.exists_le_sylow
    have := Subgroup.card_le_of_le hT
    have h8 := hsyl T
    rw [hH] at this
    norm_num at this
    omega

end EndLemmaP

section AbelPieces

variable {X : Type} [Group X] [Finite X]

theorem endg_perfect_fixes_small_set {Kp : Subgroup X} (hKperf : ⁅Kp, Kp⁆ = Kp)
    (𝒦 : Set (Subgroup X)) [Finite ↥𝒦] (hcard : Nat.card ↥𝒦 ≤ 4)
    (hS : ∀ C ∈ 𝒦, ∀ k : X, conjSubgroup k C ∈ 𝒦) :
    ∀ k ∈ Kp, ∀ C ∈ 𝒦, conjSubgroup k C = C := by
  classical
  let perm : X → Equiv.Perm ↥𝒦 := fun k =>
    { toFun := fun C => ⟨conjSubgroup k C, hS C C.2 k⟩
      invFun := fun C => ⟨conjSubgroup k⁻¹ C, hS C C.2 k⁻¹⟩
      left_inv := fun C => Subtype.ext (by
        show conjSubgroup k⁻¹ (conjSubgroup k C) = C
        rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one])
      right_inv := fun C => Subtype.ext (by
        show conjSubgroup k (conjSubgroup k⁻¹ C) = C
        rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]) }
  let act : X →* Equiv.Perm ↥𝒦 :=
    { toFun := perm
      map_one' := Equiv.ext fun C => Subtype.ext (by
        show conjSubgroup 1 (C : Subgroup X) = C
        exact conjSubgroup_one _)
      map_mul' := fun a b => Equiv.ext fun C => Subtype.ext (by
        show conjSubgroup (a * b) (C : Subgroup X) = conjSubgroup a (conjSubgroup b C)
        exact conjSubgroup_mul a b _) }
  haveI : Group.IsSolvable (Equiv.Perm ↥𝒦) := Equiv.Perm.isSolvable hcard
  intro k hk C hC
  have h1 := endg_perfect_hom_trivial hKperf (act.comp Kp.subtype) ⟨k, hk⟩
  have h2 := congrArg (fun f : Equiv.Perm ↥𝒦 => (f ⟨C, hC⟩ : ↥𝒦).1) h1
  simpa [act, perm] using h2

theorem endg_mem_sup_of_commute {Y N : Subgroup X} (hc : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y)
    {x : X} (hx : x ∈ Y ⊔ N) : ∃ y ∈ Y, ∃ n ∈ N, x = y * n := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, N.one_mem, (mul_one x).symm⟩
    · exact ⟨1, Y.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, Y.one_mem, 1, N.one_mem, (mul_one 1).symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨y, hy, n, hn, rfl⟩ := ha
    obtain ⟨y', hy', n', hn', rfl⟩ := hb
    refine ⟨y * y', Y.mul_mem hy hy', n * n', N.mul_mem hn hn', ?_⟩
    have := hc y' hy' n hn
    calc y * n * (y' * n') = y * (n * y') * n' := by group
      _ = y * (y' * n) * n' := by rw [this]
      _ = y * y' * (n * n') := by group
  | inv a _ ha =>
    obtain ⟨y, hy, n, hn, rfl⟩ := ha
    refine ⟨y⁻¹, Y.inv_mem hy, n⁻¹, N.inv_mem hn, ?_⟩
    have := hc y hy n hn
    calc (y * n)⁻¹ = n⁻¹ * y⁻¹ := by group
      _ = y⁻¹ * n⁻¹ := by
        have h2 : y⁻¹ * n = n * y⁻¹ := by
          calc y⁻¹ * n = y⁻¹ * (n * y) * y⁻¹ := by group
            _ = y⁻¹ * (y * n) * y⁻¹ := by rw [this]
            _ = n * y⁻¹ := by group
        calc n⁻¹ * y⁻¹ = n⁻¹ * (y⁻¹ * n) * n⁻¹ := by group
          _ = n⁻¹ * (n * y⁻¹) * n⁻¹ := by rw [h2]
          _ = y⁻¹ * n⁻¹ := by group

theorem endg_split_elem {Cj D Kp : Subgroup X} {z : X}
    (hCD : ∀ c ∈ Cj, ∀ d ∈ D, c * d = d * c) (hbot : Cj ⊓ D = ⊥)
    (hZ : ∀ a ∈ Cj, (∀ c ∈ Cj, c * a = a * c) → a = 1) (hz : z ∈ Cj ⊔ D)
    (hz2 : z * z = 1) (hKz : ∀ k ∈ Kp, k * z = z * k)
    (hKC : ∀ k ∈ Kp, ∀ c ∈ Cj, k * c * k⁻¹ ∈ Cj)
    (hKD : ∀ k ∈ Kp, ∀ d ∈ D, k * d * k⁻¹ ∈ D) :
    ∃ a ∈ Cj, a * a = 1 ∧ (∀ k ∈ Kp, k * a = a * k) ∧
      ((∀ c ∈ Cj, c * z = z * c) ↔ a = 1) := by
  obtain ⟨a, ha, d, hd, rfl⟩ := endg_mem_sup_of_commute hCD hz
  have huniq : ∀ {a' a'' d' d'' : X}, a' ∈ Cj → a'' ∈ Cj → d' ∈ D → d'' ∈ D →
      a' * d' = a'' * d'' → a' = a'' := by
    intro a' a'' d' d'' ha' ha'' hd' hd'' h
    have h1 : a''⁻¹ * a' ∈ Cj ⊓ D := by
      refine ⟨Cj.mul_mem (Cj.inv_mem ha'') ha', ?_⟩
      have : a''⁻¹ * a' = d'' * d'⁻¹ := by
        have h2 : a' = a'' * d'' * d'⁻¹ := by rw [← h]; group
        rw [h2]; group
      rw [this]
      exact D.mul_mem hd'' (D.inv_mem hd')
    rw [hbot, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1).symm
  have hcomm : ∀ c ∈ Cj, ∀ d' ∈ D, d' * c = c * d' := fun c hc d' hd' => (hCD c hc d' hd').symm
  have ha2 : a * a = 1 := by
    have h1 : a * a * (d * d) = 1 := by
      calc a * a * (d * d) = a * (a * d) * d := by group
        _ = a * (d * a) * d := by rw [hCD a ha d hd]
        _ = (a * d) * (a * d) := by group
        _ = 1 := hz2
    have h2 : a * a * (d * d) = 1 * 1 := by rw [h1]; group
    exact huniq (Cj.mul_mem ha ha) Cj.one_mem (D.mul_mem hd hd) D.one_mem
      (by simpa using h1)
  refine ⟨a, ha, ha2, fun k hk => ?_, ?_⟩
  · have h0 : k * (a * d) * k⁻¹ = a * d := by
      rw [hKz k hk]; group
    have h1 : (k * a * k⁻¹) * (k * d * k⁻¹) = a * d := by
      calc (k * a * k⁻¹) * (k * d * k⁻¹) = k * (a * d) * k⁻¹ := by group
        _ = a * d := h0
    have := huniq (hKC k hk a ha) ha (hKD k hk d hd) hd h1
    calc k * a = (k * a * k⁻¹) * k := by group
      _ = a * k := by rw [this]
  · constructor
    · intro hall
      apply hZ a ha
      intro c hc
      have h1 := hall c hc
      have h2 : c * a * d = a * c * d := by
        calc c * a * d = c * (a * d) := by group
          _ = (a * d) * c := h1
          _ = a * (d * c) := by group
          _ = a * (c * d) := by rw [hcomm c hc d hd]
          _ = a * c * d := by group
      exact mul_right_cancel h2
    · rintro rfl c hc
      calc c * (1 * d) = c * d := by group
        _ = d * c := hCD c hc d hd
        _ = 1 * d * c := by group

theorem endg_mem_sup_of_normalizer {N K : Subgroup X}
    (hK : K ≤ Subgroup.normalizer (N : Set X)) {x : X} (hx : x ∈ N ⊔ K) :
    ∃ n ∈ N, ∃ k ∈ K, x = n * k := by
  have hx' : x ∈ ((N ⊔ K : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N K hK] at hx'
  obtain ⟨n, hn, k, hk, rfl⟩ := hx'
  exact ⟨n, hn, k, hk, rfl⟩

end AbelPieces

section CaseEight

variable {X : Type} [Group X] [Finite X] {A R N H : Subgroup X} {t : X}

private lemma endgG_conj_mem {Y : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (Y : Set X))
    {y : X} (hy : y ∈ Y) : g * y * g⁻¹ ∈ Y :=
  (Subgroup.mem_normalizer_iff.mp hg y).mp hy

private lemma endgG_normal_subgroupOf {Y Z : Subgroup X}
    (hZ : ∀ z ∈ Z, ∀ y ∈ Y, z * y * z⁻¹ ∈ Y) : (Y.subgroupOf Z).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hZ g g.2 x hx⟩

private lemma endgG_sup_split {Y M : Subgroup X}
    (hY : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M) :
    ∀ x ∈ Y ⊔ M, ∃ y ∈ Y, ∃ m ∈ M, y * m = x := by
  let T : Subgroup X :=
    { carrier := {x | ∃ y ∈ Y, ∃ m ∈ M, y * m = x}
      one_mem' := ⟨1, Y.one_mem, 1, M.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, m₁, hm₁, rfl⟩ ⟨y₂, hy₂, m₂, hm₂, rfl⟩
        refine ⟨y₁ * y₂, Y.mul_mem hy₁ hy₂, y₂⁻¹ * m₁ * y₂ * m₂, M.mul_mem ?_ hm₂, ?_⟩
        · simpa using hY y₂⁻¹ (Y.inv_mem hy₂) m₁ hm₁
        · group
      inv_mem' := by
        rintro _ ⟨y, hy, m, hm, rfl⟩
        exact ⟨y⁻¹, Y.inv_mem hy, y * m⁻¹ * y⁻¹, hY y hy m⁻¹ (M.inv_mem hm), by group⟩ }
  have hle : Y ⊔ M ≤ T :=
    sup_le (fun y hy => ⟨y, hy, 1, M.one_mem, mul_one y⟩)
      (fun m hm => ⟨1, Y.one_mem, m, hm, one_mul m⟩)
  intro x hx
  exact hle hx

theorem endg_case_eight (h : EndgameHyp X A R N H t) {Kp Cj : Subgroup X}
    (hKR : Kp ≤ R) (hKperf : ⁅Kp, Kp⁆ = Kp) (hRK : R ≤ Kp ⊔ N)
    (hKnorm : ∀ g : X, g ∈ Subgroup.normalizer (R : Set X) →
      g ∈ Subgroup.normalizer (Kp : Set X))
    (hCs : IsSimpleGroup ↥Cj) (hCnc : ∃ a ∈ Cj, ∃ b ∈ Cj, a * b ≠ b * a)
    (hKC : ∀ k ∈ Kp, k ∈ Subgroup.normalizer (Cj : Set X))
    (hCt : ∀ c ∈ Cj, c * t = t * c)
    (hact : ∃ k ∈ Kp, ∃ c ∈ Cj, k * c ≠ c * k) : False := by
  have hCK : ∀ c ∈ Cj, c ∈ Subgroup.normalizer (Kp : Set X) := fun c hc =>
    hKnorm c (h.F0 c (hCt c hc)).1
  have hCN : ∀ c ∈ Cj, c ∈ Subgroup.normalizer (N : Set X) := fun c hc =>
    (h.F0 c (hCt c hc)).2
  have hNK : ∀ n ∈ N, n ∈ Subgroup.normalizer (Kp : Set X) := fun n hn =>
    hKnorm n (Subgroup.le_normalizer (h.N_le hn))
  have hKN : ∀ k ∈ Kp, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k hk n hn
    exact Subgroup.mem_subgroupOf.mp
      (h.N_normal.conj_mem ⟨n, h.N_le hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨k, hKR hk⟩)
  obtain ⟨k₀, hk₀, c₀, hc₀, hne₀⟩ := hact
  have hwC : k₀ * c₀ * k₀⁻¹ * c₀⁻¹ ∈ Cj :=
    Cj.mul_mem (endgG_conj_mem (hKC k₀ hk₀) hc₀) (Cj.inv_mem hc₀)
  have hwK : k₀ * c₀ * k₀⁻¹ * c₀⁻¹ ∈ Kp := by
    have := Kp.mul_mem hk₀ (endgG_conj_mem (hCK c₀ hc₀) (Kp.inv_mem hk₀))
    simpa only [mul_assoc] using this
  have hw1 : k₀ * c₀ * k₀⁻¹ * c₀⁻¹ ≠ 1 := by
    intro hw
    apply hne₀
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hw)
  have hCjKp : Cj ≤ Kp := by
    have hKCj : ∀ z ∈ Cj, ∀ y ∈ Kp ⊓ Cj, z * y * z⁻¹ ∈ Kp ⊓ Cj := by
      intro z hz y hy
      obtain ⟨hyK, hyC⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_inf.mpr ⟨endgG_conj_mem (hCK z hz) hyK,
        Cj.mul_mem (Cj.mul_mem hz hyC) (Cj.inv_mem hz)⟩
    haveI := endgG_normal_subgroupOf hKCj
    rcases hCs.eq_bot_or_eq_top_of_normal ((Kp ⊓ Cj).subgroupOf Cj) with hbot | htop
    · exfalso
      have hmem : (⟨_, hwC⟩ : ↥Cj) ∈ (Kp ⊓ Cj).subgroupOf Cj :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hwK, hwC⟩)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hw1 (congrArg Subtype.val hmem)
    · intro c hc
      have hmem : (⟨c, hc⟩ : ↥Cj) ∈ (Kp ⊓ Cj).subgroupOf Cj := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
  have hCapN : Cj ⊓ N = ⊥ := by
    have hCNj : ∀ z ∈ Cj, ∀ y ∈ Cj ⊓ N, z * y * z⁻¹ ∈ Cj ⊓ N := by
      intro z hz y hy
      obtain ⟨hyC, hyN⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_inf.mpr ⟨Cj.mul_mem (Cj.mul_mem hz hyC) (Cj.inv_mem hz),
        endgG_conj_mem (hCN z hz) hyN⟩
    haveI := endgG_normal_subgroupOf hCNj
    rcases hCs.eq_bot_or_eq_top_of_normal ((Cj ⊓ N).subgroupOf Cj) with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have hmem : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥Cj) ∈ (Cj ⊓ N).subgroupOf Cj :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
    · exfalso
      have hCN' : Cj ≤ N := by
        intro c hc
        have hmem : (⟨c, hc⟩ : ↥Cj) ∈ (Cj ⊓ N).subgroupOf Cj := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
      have hp2 : IsPGroup 2 ↥Cj :=
        h.N_pgroup.of_injective (Subgroup.inclusion hCN') (Subgroup.inclusion_injective hCN')
      haveI : Nontrivial ↥Cj := hCs.toNontrivial
      have hbotC := hp2.bot_lt_center
      obtain ⟨a, ha, b, hb, hab⟩ := hCnc
      rcases hCs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Cj) with hcb | hct
      · exact absurd hcb hbotC.ne'
      · apply hab
        have hcen : (⟨a, ha⟩ : ↥Cj) ∈ Subgroup.center ↥Cj := by
          rw [hct]
          exact Subgroup.mem_top _
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨b, hb⟩)).symm
  obtain ⟨S, hSg, ρ, hρs, hρk, hSs, -⟩ := h.quot
  obtain ⟨ρK, hρK⟩ : ∃ f : ↥Kp →* S, ∀ k : ↥Kp, f k = ρ ⟨(k : X), hKR k.2⟩ :=
    ⟨ρ.comp (Subgroup.inclusion hKR), fun k => rfl⟩
  have hρKker : ∀ k : ↥Kp, ρK k = 1 ↔ (k : X) ∈ N := fun k => by
    rw [hρK]
    exact hρk _
  have hsurj : Function.Surjective ρK := by
    intro s
    obtain ⟨r, rfl⟩ := hρs s
    obtain ⟨k, hk, n, hn, hkn⟩ := endgG_sup_split hKN (r : X) (hRK r.2)
    refine ⟨⟨k, hk⟩, ?_⟩
    have hr : r = ⟨k, hKR hk⟩ * ⟨n, h.N_le hn⟩ := Subtype.ext hkn.symm
    have hnρ : ρ ⟨n, h.N_le hn⟩ = 1 := (hρk _).mpr hn
    rw [hρK, hr, map_mul, hnρ, mul_one]
  have hCjKN : (Cj.subgroupOf Kp).Normal :=
    endgG_normal_subgroupOf (fun z hz y hy => endgG_conj_mem (hKC z hz) hy)
  haveI hmapN : ((Cj.subgroupOf Kp).map ρK).Normal := Subgroup.Normal.map hCjKN ρK hsurj
  have hKleCj : Kp ≤ Cj := by
    rcases hSs.eq_bot_or_eq_top_of_normal ((Cj.subgroupOf Kp).map ρK) with hmb | hmt
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hCnc
      have key : ∀ c ∈ Cj, c = 1 := by
        intro c hc
        have hmem : ρK ⟨c, hCjKp hc⟩ ∈ (Cj.subgroupOf Kp).map ρK :=
          Subgroup.mem_map_of_mem ρK (Subgroup.mem_subgroupOf.mpr hc)
        rw [hmb, Subgroup.mem_bot] at hmem
        have hcCN : c ∈ Cj ⊓ N :=
          Subgroup.mem_inf.mpr ⟨hc, (hρKker ⟨c, hCjKp hc⟩).mp hmem⟩
        rw [hCapN, Subgroup.mem_bot] at hcCN
        exact hcCN
      exact hab (by rw [key a ha, key b hb])
    · have hdec : ∀ k : ↥Kp, ∃ m : ↥Kp, (m : X) ∈ N ∧
          QuotientGroup.mk' (Cj.subgroupOf Kp) m = QuotientGroup.mk' (Cj.subgroupOf Kp) k := by
        intro k
        have hmem : ρK k ∈ (Cj.subgroupOf Kp).map ρK := by
          rw [hmt]
          exact Subgroup.mem_top _
        obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hmem
        refine ⟨x⁻¹ * k, (hρKker _).mp ?_, ?_⟩
        · rw [map_mul, map_inv, hxk, inv_mul_cancel]
        · have hx1 : QuotientGroup.mk' (Cj.subgroupOf Kp) x = 1 :=
            (QuotientGroup.eq_one_iff x).mpr hx
          rw [map_mul, map_inv, hx1, inv_one, one_mul]
      have hPQ : IsPGroup 2 (↥Kp ⧸ Cj.subgroupOf Kp) := by
        intro q
        obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective q
        have hk' : QuotientGroup.mk' (Cj.subgroupOf Kp) k = q := hk
        subst hk'
        obtain ⟨m, hmN, hmk⟩ := hdec k
        obtain ⟨j, hj⟩ := h.N_pgroup ⟨(m : X), hmN⟩
        refine ⟨j, ?_⟩
        have hmj : m ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
        have hpow : QuotientGroup.mk' (Cj.subgroupOf Kp) (m ^ 2 ^ j) = 1 := by
          rw [hmj, map_one]
        rw [map_pow] at hpow
        rw [hmk.symm]
        exact hpow
      haveI : Group.IsSolvable (↥Kp ⧸ Cj.subgroupOf Kp) := by
        haveI := hPQ.isNilpotent
        infer_instance
      intro x hx
      have hk1 := endg_perfect_hom_trivial hKperf (QuotientGroup.mk' (Cj.subgroupOf Kp))
        (⟨x, hx⟩ : ↥Kp)
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨x, hx⟩ : ↥Kp)).mp hk1)
  have hKN0 : Kp ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxC : x ∈ Cj ⊓ N := Subgroup.mem_inf.mpr ⟨hKleCj hxK, hxN⟩
    rw [hCapN, Subgroup.mem_bot] at hxC
    exact Subgroup.mem_bot.mpr hxC
  have hcomm : ∀ k ∈ Kp, ∀ n ∈ N, k * n = n * k := by
    intro k hk n hn
    have hc1 : k * n * k⁻¹ * n⁻¹ ∈ Kp ⊓ N := by
      refine Subgroup.mem_inf.mpr ⟨?_, N.mul_mem (hKN k hk n hn) (N.inv_mem hn)⟩
      have := Kp.mul_mem hk (endgG_conj_mem (hNK n hn) (Kp.inv_mem hk))
      simpa only [mul_assoc] using this
    rw [hKN0, Subgroup.mem_bot] at hc1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)
  exact endg_false_of_split h hKR hcomm hRK

end CaseEight

end CFSG.RankThree.GF2n.Stroth80
