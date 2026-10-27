module

public import CFSG.RankThree.GF2n.Tim78NaturalModule
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.RankThree.GF2n.Tim78S31Count

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_map_mk_mul {X H N : Subgroup G} [(N.subgroupOf X).Normal] (hH : H ≤ X) :
    Nat.card ((H.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) * Nat.card ↥(H ⊓ N) =
      Nat.card H := by
  set φ := (QuotientGroup.mk' (N.subgroupOf X)).comp (H.subgroupOf X).subtype with hφ
  have hrange : φ.range = (H.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hφ1 : ∀ y : ↥(H.subgroupOf X), φ y = 1 ↔ ((y : ↥X) : G) ∈ N := fun y => by
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl
  have hker : Nat.card φ.ker = Nat.card ↥(H ⊓ N) :=
    Nat.card_congr
      { toFun := fun y => ⟨(((y : ↥(H.subgroupOf X)) : ↥X) : G), Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_subgroupOf.mp (y : ↥(H.subgroupOf X)).2, (hφ1 _).mp y.2⟩⟩
        invFun := fun z => ⟨⟨⟨(z : G), hH (Subgroup.mem_inf.mp z.2).1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp z.2).1⟩,
          (hφ1 _).mpr (Subgroup.mem_inf.mp z.2).2⟩
        left_inv := fun y => rfl
        right_inv := fun z => rfl }
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv] at h1
  rw [mul_comm]
  exact h1

namespace Data31

variable {U : Subgroup G} {g α x : G} (D : Data31 U g α x) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include D hCen hU

theorem le_normalizer : U ⊔ conjSubgroup x U ≤ Subgroup.normalizer
    ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) : Subgroup G) : Set G) := by
  rw [← D.sup_eq hCen hU D.mem D.ne_one, ← D.N_eq hCen hU D.mem D.ne_one]
  exact D.pair.le_normalizer hCen hU

theorem comm_N {m n : G} (hm : m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U))
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) :
    m * n = n * m := by
  rw [← D.N_eq hCen hU D.mem D.ne_one] at hm hn
  exact D.pair.comm_N hCen hU hm hn

theorem sq_N {n : G} (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) :
    n * n = 1 := by
  rw [← D.N_eq hCen hU D.mem D.ne_one] at hn
  exact D.pair.sq_N hCen hU hn

theorem conj_mem_N {z n : G} (hz : z ∈ U ⊔ conjSubgroup x U)
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) :
    z * n * z⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) :=
  (Subgroup.mem_normalizer_iff.mp (D.le_normalizer hCen hU hz) n).mp hn

theorem inf_AC : conjSubgroup g U ⊓ conjSubgroup x U = ⊥ :=
  (D.pairAC hCen hU).setup.inf_eq_bot (D.pairAC hCen hU).ne

omit hCen hU in
theorem inf_UC : U ⊓ conjSubgroup x U = ⊥ :=
  inf_conjSubgroup_eq_bot_of_isTI D.core.ti fun h => D.ne_C h.symm

theorem inf_N : conjSubgroup x U ⊓ (PartTwo.omegaOneSub U ⊔
    PartTwo.omegaOneSub (conjSubgroup x U)) = PartTwo.omegaOneSub (conjSubgroup x U) := by
  refine le_antisymm (fun c hc => ?_) (le_inf (PartTwo.omegaOneSub_le _) le_sup_right)
  obtain ⟨hcC, hcN⟩ := Subgroup.mem_inf.mp hc
  have hxX : x⁻¹ ∈ U ⊔ conjSubgroup x U := by
    rw [← D.sup_eq hCen hU D.mem D.ne_one]
    exact (U ⊔ conjSubgroup α U).inv_mem D.memX
  have h1 := D.conj_mem_N hCen hU hxX hcN
  rw [inv_inv] at h1
  rw [← D.N_eq hCen hU D.mem D.ne_one] at h1
  have h2 := D.pair.mem_U₀_of_mem_N hCen hU (mem_conjSubgroup.mp hcC) h1
  rw [omegaOneSub_conj D.core.comm, mem_conjSubgroup]
  exact h2

theorem comm_N_A₀ {a n : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) :
    n * a * n⁻¹ * a⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  obtain ⟨c, hc, hca, -⟩ := D.act hCen hU ha
  have hn' : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U) := by
    rw [D.N_eq hCen hU D.mem D.ne_one]
    exact hn
  have h1 := D.pair.comm_mem_conj hCen hU D.memX hc hn'
  have h2 := hca n⁻¹ (Subgroup.inv_mem _ hn)
  have e : n * a * n⁻¹ * a⁻¹ = (c * n * c⁻¹ * n⁻¹)⁻¹ := by
    calc n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
      _ = n * (c * n⁻¹ * c⁻¹) := by rw [h2]
      _ = (c * n * c⁻¹ * n⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ h1

theorem comm_C_A₀ {a c : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (hc : c ∈ conjSubgroup x U) : c * a * c⁻¹ * a⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  have := (PartTwo.omegaOneSub (conjSubgroup x U)).inv_mem (D.comm_mem_C₀' hCen hU ha hc)
  rwa [show (a * c * a⁻¹ * c⁻¹)⁻¹ = c * a * c⁻¹ * a⁻¹ by group] at this

theorem comm_S_A₀ {a s : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (hs : s ∈ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) ⊔
      conjSubgroup x U) : s * a * s⁻¹ * a⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup
    (le_trans le_sup_right (D.le_normalizer hCen hU)) hs
  have hk₁ := D.comm_C_A₀ hCen hU ha hc
  have hk₂ := D.comm_N_A₀ hCen hU ha hn
  have hcomm := D.comm_N hCen hU hn (Subgroup.mem_sup_right hk₁)
  have e : n * c * a * (n * c)⁻¹ * a⁻¹ =
      (c * a * c⁻¹ * a⁻¹) * (n * a * n⁻¹ * a⁻¹) := by
    calc n * c * a * (n * c)⁻¹ * a⁻¹ =
        (n * (c * a * c⁻¹ * a⁻¹)) * n⁻¹ * (n * a * n⁻¹ * a⁻¹) := by group
      _ = (c * a * c⁻¹ * a⁻¹) * (n * a * n⁻¹ * a⁻¹) := by rw [hcomm, mul_inv_cancel_right]
  rw [e]
  exact Subgroup.mul_mem _ hk₁ hk₂

theorem comm_C₀_A₀ {a z : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (hz : z ∈ PartTwo.omegaOneSub (conjSubgroup x U)) : a * z = z * a := by
  obtain ⟨c, hc, hca, -⟩ := D.act hCen hU ha
  have h1 := hca z (Subgroup.mem_sup_right hz)
  have h2 : c * z = z * c := D.core.comm_conj' x c hc z (PartTwo.omegaOneSub_le _ hz)
  calc a * z = (a * z * a⁻¹) * a := by group
    _ = (c * z * c⁻¹) * a := by rw [h1]
    _ = z * a := by rw [h2, mul_inv_cancel_right]

theorem mem_C₀_of_comm {a c : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1)
    (hc : c ∈ conjSubgroup x U) (hca : c * a = a * c) :
    c ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  by_contra hcC
  have h := (D.pairAC hCen hU).symm.cent hCen hU hc hcC (Subgroup.mem_sup_right ha) hca
  have : a ∈ conjSubgroup g U ⊓ conjSubgroup x U :=
    Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le _ ha, PartTwo.omegaOneSub_le _ h⟩
  rw [D.inf_AC hCen hU, Subgroup.mem_bot] at this
  exact ha1 this

theorem mem_C₀_of_mem_N {n : G}
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U))
    (hna : ∀ a ∈ PartTwo.omegaOneSub (conjSubgroup g U), a * n = n * a) :
    n ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  rw [← D.N_eq hCen hU D.mem D.ne_one] at hn
  exact D.cent_α hCen hU hn (hna α D.mem)

theorem exists_comm_eq {a z : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1)
    (hz : z ∈ PartTwo.omegaOneSub (conjSubgroup x U)) :
    ∃ c ∈ conjSubgroup x U, c * a * c⁻¹ * a⁻¹ = z := by
  have K := D.core
  have hCc := K.comm_conj' x
  have hk : ∀ c ∈ conjSubgroup x U, c * a * c⁻¹ * a⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) :=
    fun c hc => D.comm_C_A₀ hCen hU ha hc
  let θ : ↥(conjSubgroup x U) →* ↥(PartTwo.omegaOneSub (conjSubgroup x U)) :=
    { toFun := fun c => ⟨(c : G) * a * (c : G)⁻¹ * a⁻¹, hk c c.2⟩
      map_one' := Subtype.ext (by
        show ((1 : ↥(conjSubgroup x U)) : G) * a * ((1 : ↥(conjSubgroup x U)) : G)⁻¹ * a⁻¹ = 1
        simp)
      map_mul' := fun c c' => Subtype.ext (by
        show ((c * c' : ↥(conjSubgroup x U)) : G) * a * ((c * c' : ↥(conjSubgroup x U)) : G)⁻¹ *
          a⁻¹ = ((c : G) * a * (c : G)⁻¹ * a⁻¹) * ((c' : G) * a * (c' : G)⁻¹ * a⁻¹)
        have h1 : (c : G) * ((c' : G) * a * (c' : G)⁻¹ * a⁻¹) =
            ((c' : G) * a * (c' : G)⁻¹ * a⁻¹) * c :=
          hCc _ c.2 _ (PartTwo.omegaOneSub_le _ (hk c' c'.2))
        have h2 : ((c : G) * a * (c : G)⁻¹ * a⁻¹) * ((c' : G) * a * (c' : G)⁻¹ * a⁻¹) =
            ((c' : G) * a * (c' : G)⁻¹ * a⁻¹) * ((c : G) * a * (c : G)⁻¹ * a⁻¹) :=
          hCc _ (PartTwo.omegaOneSub_le _ (hk c c.2)) _ (PartTwo.omegaOneSub_le _ (hk c' c'.2))
        rw [Subgroup.coe_mul, h2]
        calc (c : G) * c' * a * ((c : G) * c')⁻¹ * a⁻¹ =
            (c : G) * ((c' : G) * a * (c' : G)⁻¹ * a⁻¹) * a * (c : G)⁻¹ * a⁻¹ := by group
          _ = ((c' : G) * a * (c' : G)⁻¹ * a⁻¹) * c * a * (c : G)⁻¹ * a⁻¹ := by rw [h1]
          _ = ((c' : G) * a * (c' : G)⁻¹ * a⁻¹) * ((c : G) * a * (c : G)⁻¹ * a⁻¹) := by
              group) }
  have hker : θ.ker = (PartTwo.omegaOneSub (conjSubgroup x U)).subgroupOf (conjSubgroup x U) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (c : G) * a * (c : G)⁻¹ * a⁻¹ = 1 := congrArg Subtype.val h
      refine D.mem_C₀_of_comm hCen hU ha ha1 c.2 ?_
      calc (c : G) * a = ((c : G) * a * (c : G)⁻¹ * a⁻¹) * (a * c) := by group
        _ = a * c := by rw [h', one_mul]
    · intro hc
      apply Subtype.ext
      show (c : G) * a * (c : G)⁻¹ * a⁻¹ = 1
      rw [← D.comm_C₀_A₀ hCen hU ha hc]
      group
  have hrange : θ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Subgroup.index_ker, hker, ← Subgroup.relIndex, D.relIndex_C, ← D.card_eq hCen hU,
      omegaOneSub_conj K.comm x, card_conjSubgroup]
  obtain ⟨c, hc⟩ : (⟨z, hz⟩ : ↥(PartTwo.omegaOneSub (conjSubgroup x U))) ∈ θ.range := by
    rw [hrange]
    trivial
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem exists_conj_mem_S₁ {n : G}
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) :
    ∃ c ∈ conjSubgroup x U, c⁻¹ * n ∈ ((PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup x U)) ⊔ conjSubgroup x U) ⊓
        Subgroup.centralizer (PartTwo.omegaOneSub (conjSubgroup g U) : Set G) := by
  have K := D.core
  obtain ⟨a₀, ha₀, ha₀1⟩ := K.exists_ne_one_omega g
  obtain ⟨c, hc, hca⟩ := D.exists_comm_eq hCen hU ha₀ ha₀1 (D.comm_N_A₀ hCen hU ha₀ hn)
  have h2 : c * a₀ * c⁻¹ = n * a₀ * n⁻¹ := by
    calc c * a₀ * c⁻¹ = (c * a₀ * c⁻¹ * a₀⁻¹) * a₀ := by group
      _ = (n * a₀ * n⁻¹ * a₀⁻¹) * a₀ := by rw [hca]
      _ = n * a₀ * n⁻¹ := by group
  have h1 : (c⁻¹ * n) * a₀ = a₀ * (c⁻¹ * n) := by
    calc c⁻¹ * n * a₀ = c⁻¹ * (n * a₀ * n⁻¹) * n := by group
      _ = c⁻¹ * (c * a₀ * c⁻¹) * n := by rw [h2]
      _ = a₀ * (c⁻¹ * n) := by group
  have hnorm := Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup K.ti g)
    (PartTwo.omegaOneSub_le _ ha₀) ha₀1 h1
  have hsS : c⁻¹ * n ∈ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) ⊔
      conjSubgroup x U :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right ((conjSubgroup x U).inv_mem hc))
      (Subgroup.mem_sup_left hn)
  refine ⟨c, hc, Subgroup.mem_inf.mpr ⟨hsS, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩⟩
  have hw : (c⁻¹ * n) * a * (c⁻¹ * n)⁻¹ ∈ conjSubgroup g U :=
    (Subgroup.mem_normalizer_iff.mp hnorm a).mp (PartTwo.omegaOneSub_le _ ha)
  have hk := D.comm_S_A₀ hCen hU ha hsS
  have hk' : (c⁻¹ * n) * a * (c⁻¹ * n)⁻¹ * a⁻¹ ∈ conjSubgroup g U ⊓ conjSubgroup x U :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hw (Subgroup.inv_mem _
      (PartTwo.omegaOneSub_le _ ha)), PartTwo.omegaOneSub_le _ hk⟩
  rw [D.inf_AC hCen hU, Subgroup.mem_bot] at hk'
  calc a * (c⁻¹ * n) = ((c⁻¹ * n) * a * (c⁻¹ * n)⁻¹ * a⁻¹)⁻¹ * ((c⁻¹ * n) * a) := by group
    _ = c⁻¹ * n * a := by rw [hk', inv_one, one_mul]

theorem exists_mul_mem_S₁ {c : G} (hc : c ∈ conjSubgroup x U) :
    ∃ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
      c * n ∈ ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) ⊔
        conjSubgroup x U) ⊓
          Subgroup.centralizer (PartTwo.omegaOneSub (conjSubgroup g U) : Set G) := by
  classical
  have K := D.core
  have P := D.pair
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) with hNdef
  set C := conjSubgroup x U with hCdef
  set C₀ := PartTwo.omegaOneSub (conjSubgroup x U) with hC₀def
  set A₀ := PartTwo.omegaOneSub (conjSubgroup g U) with hA₀def
  have hCc := K.comm_conj' x
  have hC₀c : ∀ y ∈ C₀, ∀ z ∈ C₀, y * z = z * y := fun y hy z hz =>
    hCc y (PartTwo.omegaOneSub_le _ hy) z (PartTwo.omegaOneSub_le _ hz)
  have hkN : ∀ n ∈ N, ∀ a ∈ A₀, n * a * n⁻¹ * a⁻¹ ∈ C₀ := fun n hn a ha =>
    D.comm_N_A₀ hCen hU ha hn
  have hkC : ∀ c ∈ C, ∀ a ∈ A₀, c * a * c⁻¹ * a⁻¹ ∈ C₀ := fun c hc a ha =>
    D.comm_C_A₀ hCen hU ha hc
  let ψN : ↥N →* (↥A₀ → ↥C₀) :=
    { toFun := fun n a => ⟨(n : G) * a * (n : G)⁻¹ * (a : G)⁻¹, hkN n n.2 a a.2⟩
      map_one' := funext fun a => Subtype.ext (by
        show ((1 : ↥N) : G) * a * ((1 : ↥N) : G)⁻¹ * (a : G)⁻¹ = 1
        simp)
      map_mul' := fun n n' => funext fun a => Subtype.ext (by
        show ((n * n' : ↥N) : G) * a * ((n * n' : ↥N) : G)⁻¹ * (a : G)⁻¹ =
          ((n : G) * a * (n : G)⁻¹ * (a : G)⁻¹) * ((n' : G) * a * (n' : G)⁻¹ * (a : G)⁻¹)
        have hk' := hkN n' n'.2 a a.2
        have h1 : (n : G) * ((n' : G) * a * (n' : G)⁻¹ * (a : G)⁻¹) =
            ((n' : G) * a * (n' : G)⁻¹ * (a : G)⁻¹) * n :=
          D.comm_N hCen hU n.2 (Subgroup.mem_sup_right hk')
        have h2 := hC₀c _ (hkN n n.2 a a.2) _ hk'
        rw [Subgroup.coe_mul, h2]
        calc (n : G) * n' * a * ((n : G) * n')⁻¹ * (a : G)⁻¹ =
            (n : G) * ((n' : G) * a * (n' : G)⁻¹ * (a : G)⁻¹) * a * (n : G)⁻¹ * (a : G)⁻¹ := by
              group
          _ = ((n' : G) * a * (n' : G)⁻¹ * (a : G)⁻¹) * n * a * (n : G)⁻¹ * (a : G)⁻¹ := by
              rw [h1]
          _ = ((n' : G) * a * (n' : G)⁻¹ * (a : G)⁻¹) * ((n : G) * a * (n : G)⁻¹ * (a : G)⁻¹) :=
              by group) }
  let ψC : ↥C →* (↥A₀ → ↥C₀) :=
    { toFun := fun c a => ⟨(c : G) * a * (c : G)⁻¹ * (a : G)⁻¹, hkC c c.2 a a.2⟩
      map_one' := funext fun a => Subtype.ext (by
        show ((1 : ↥C) : G) * a * ((1 : ↥C) : G)⁻¹ * (a : G)⁻¹ = 1
        simp)
      map_mul' := fun c c' => funext fun a => Subtype.ext (by
        show ((c * c' : ↥C) : G) * a * ((c * c' : ↥C) : G)⁻¹ * (a : G)⁻¹ =
          ((c : G) * a * (c : G)⁻¹ * (a : G)⁻¹) * ((c' : G) * a * (c' : G)⁻¹ * (a : G)⁻¹)
        have hk' := hkC c' c'.2 a a.2
        have h1 : (c : G) * ((c' : G) * a * (c' : G)⁻¹ * (a : G)⁻¹) =
            ((c' : G) * a * (c' : G)⁻¹ * (a : G)⁻¹) * c :=
          hCc _ c.2 _ (PartTwo.omegaOneSub_le _ hk')
        have h2 := hC₀c _ (hkC c c.2 a a.2) _ hk'
        rw [Subgroup.coe_mul, h2]
        calc (c : G) * c' * a * ((c : G) * c')⁻¹ * (a : G)⁻¹ =
            (c : G) * ((c' : G) * a * (c' : G)⁻¹ * (a : G)⁻¹) * a * (c : G)⁻¹ * (a : G)⁻¹ := by
              group
          _ = ((c' : G) * a * (c' : G)⁻¹ * (a : G)⁻¹) * c * a * (c : G)⁻¹ * (a : G)⁻¹ := by
              rw [h1]
          _ = ((c' : G) * a * (c' : G)⁻¹ * (a : G)⁻¹) * ((c : G) * a * (c : G)⁻¹ * (a : G)⁻¹) :=
              by group) }
  have hcomm_of : ∀ y : G, (∀ a ∈ A₀, y * a * y⁻¹ * a⁻¹ = 1) → ∀ a ∈ A₀, a * y = y * a :=
    fun y hy a ha => by
      calc a * y = (y * a * y⁻¹ * a⁻¹)⁻¹ * (y * a) := by group
        _ = y * a := by rw [hy a ha, inv_one, one_mul]
  have hkerN : ψN.ker = C₀.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine D.mem_C₀_of_mem_N hCen hU n.2 (hcomm_of _ fun a ha => ?_)
      exact congrArg Subtype.val (congrFun h ⟨a, ha⟩)
    · intro hn
      refine funext fun a => Subtype.ext ?_
      show (n : G) * a * (n : G)⁻¹ * (a : G)⁻¹ = 1
      rw [← D.comm_C₀_A₀ hCen hU a.2 hn]
      group
  have hkerC : ψC.ker = C₀.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hca := hcomm_of _ (fun a ha => congrArg Subtype.val (congrFun h ⟨a, ha⟩)) α D.mem
      exact D.mem_C₀_of_comm hCen hU D.mem D.ne_one c.2 hca.symm
    · intro hc
      refine funext fun a => Subtype.ext ?_
      show (c : G) * a * (c : G)⁻¹ * (a : G)⁻¹ = 1
      rw [← D.comm_C₀_A₀ hCen hU a.2 hc]
      group
  have hC₀N : C₀ ≤ N := le_sup_right
  have hcardN : Nat.card N = Nat.card ↥(PartTwo.omegaOneSub U) *
      Nat.card ↥(PartTwo.omegaOneSub U) := by
    rw [hNdef, ← D.N_eq hCen hU D.mem D.ne_one, P.card_N hCen hU, K.card_omega_conj α]
  have hcardC : Nat.card C = Nat.card ↥(PartTwo.omegaOneSub U) *
      Nat.card ↥(PartTwo.omegaOneSub U) := by
    have h1 := Subgroup.relIndex_mul_card (PartTwo.omegaOneSub U) U
    rw [inf_of_le_left (PartTwo.omegaOneSub_le U), ← D.card_eq hCen hU] at h1
    rw [hCdef, card_conjSubgroup, ← h1]
  have hrel : C₀.relIndex N = C₀.relIndex C := by
    have h1 := Subgroup.relIndex_mul_card C₀ N
    have h2 := Subgroup.relIndex_mul_card C₀ C
    rw [inf_of_le_left hC₀N, hcardN] at h1
    rw [inf_of_le_left (PartTwo.omegaOneSub_le _), hcardC] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  have hle : ψN.range ≤ ψC.range := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨c', hc', hmem⟩ := D.exists_conj_mem_S₁ hCen hU n.2
    refine ⟨⟨c', hc'⟩, funext fun a => Subtype.ext ?_⟩
    have hca := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2) a a.2
    show c' * a * c'⁻¹ * (a : G)⁻¹ = (n : G) * a * (n : G)⁻¹ * (a : G)⁻¹
    calc c' * a * c'⁻¹ * (a : G)⁻¹ = c' * ((a : G) * (c'⁻¹ * n)) * (c'⁻¹ * n)⁻¹ * c'⁻¹ *
        (a : G)⁻¹ := by group
      _ = c' * ((c'⁻¹ * n) * a) * (c'⁻¹ * n)⁻¹ * c'⁻¹ * (a : G)⁻¹ := by rw [hca]
      _ = (n : G) * a * (n : G)⁻¹ * (a : G)⁻¹ := by group
  have heq : ψN.range = ψC.range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Subgroup.index_ker, ← Subgroup.index_ker, hkerN, hkerC, ← Subgroup.relIndex,
      ← Subgroup.relIndex, hrel]
  obtain ⟨n, hn⟩ : ψC ⟨c⁻¹, C.inv_mem hc⟩ ∈ ψN.range := by
    rw [heq]
    exact ⟨_, rfl⟩
  refine ⟨n, n.2, Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
    (Subgroup.mem_sup_left n.2), Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩⟩
  have h1 : (n : G) * a * (n : G)⁻¹ * a⁻¹ = c⁻¹ * a * c⁻¹⁻¹ * a⁻¹ :=
    congrArg Subtype.val (congrFun hn ⟨a, ha⟩)
  have h2 : (n : G) * a * (n : G)⁻¹ = c⁻¹ * a * c := by
    calc (n : G) * a * (n : G)⁻¹ = ((n : G) * a * (n : G)⁻¹ * a⁻¹) * a := by group
      _ = (c⁻¹ * a * c⁻¹⁻¹ * a⁻¹) * a := by rw [h1]
      _ = c⁻¹ * a * c := by group
  calc a * (c * n) = c * (c⁻¹ * a * c) * n := by group
    _ = c * ((n : G) * a * (n : G)⁻¹) * n := by rw [h2]
    _ = c * n * a := by group

theorem exists_eq_mul {s : G}
    (hs : s ∈ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) ⊔
      conjSubgroup x U) :
    ∃ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
      ∃ s₁ ∈ ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) ⊔
        conjSubgroup x U) ⊓
          Subgroup.centralizer (PartTwo.omegaOneSub (conjSubgroup g U) : Set G), s = n * s₁ := by
  obtain ⟨n', hn', c, hc, rfl⟩ := exists_mul_of_mem_sup
    (le_trans le_sup_right (D.le_normalizer hCen hU)) hs
  obtain ⟨n, hn, hcn⟩ := D.exists_mul_mem_S₁ hCen hU hc
  have hcnX : c * n ∈ U ⊔ conjSubgroup x U :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
      ((sup_le_sup (PartTwo.omegaOneSub_le U) (PartTwo.omegaOneSub_le _)) hn)
  refine ⟨n' * ((c * n) * n⁻¹ * (c * n)⁻¹), Subgroup.mul_mem _ hn'
    (D.conj_mem_N hCen hU hcnX (Subgroup.inv_mem _ hn)), c * n, hcn, by group⟩

theorem sq_eq_one_of_mem_S₁ {s : G}
    (hs : s ∈ ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U)) ⊔
      conjSubgroup x U) ⊓
        Subgroup.centralizer (PartTwo.omegaOneSub (conjSubgroup g U) : Set G)) : s * s = 1 := by
  have K := D.core
  have P := D.pair
  obtain ⟨hsS, hsA⟩ := Subgroup.mem_inf.mp hs
  rw [Subgroup.mem_centralizer_iff] at hsA
  obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup
    (le_trans le_sup_right (D.le_normalizer hCen hU)) hsS
  obtain ⟨a, ha, c', hc', hcc', hn', hz'⟩ := D.exists_a hCen hU ((conjSubgroup x U).inv_mem hc)
  have hNX : PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) ≤
      U ⊔ conjSubgroup x U := sup_le_sup (PartTwo.omegaOneSub_le U) (PartTwo.omegaOneSub_le _)
  have hw : n * c * c' ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by
    have h1 : c * c' ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by simpa using hcc'
    rw [mul_assoc]
    exact Subgroup.mul_mem _ hn (Subgroup.mem_sup_right h1)
  have hyN : ∀ m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
      n * c * a * m * (n * c * a)⁻¹ = m := by
    intro m hm
    have h1 := hn' m hm
    calc n * c * a * m * (n * c * a)⁻¹ = (n * c) * (a * m * a⁻¹) * (n * c)⁻¹ := by group
      _ = (n * c) * (c' * m * c'⁻¹) * (n * c)⁻¹ := by rw [h1]
      _ = (n * c * c') * m * (n * c * c')⁻¹ := by group
      _ = m := by rw [D.comm_N hCen hU hw hm, mul_inv_cancel_right]
  have hyX : ∀ z ∈ U ⊔ conjSubgroup x U, n * c * a * z * (n * c * a)⁻¹ * z⁻¹ ∈
      PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by
    intro z hz
    have hm₁ := hz' z hz
    have hsX : n * c ∈ U ⊔ conjSubgroup x U :=
      Subgroup.mul_mem _ (hNX hn) (Subgroup.mem_sup_right hc)
    have e : n * c * a * z * (n * c * a)⁻¹ * z⁻¹ =
        ((n * c * c') * (z * (n * c * c')⁻¹ * z⁻¹)) *
          (z * ((n * c) * ((c' * z * c'⁻¹)⁻¹ * (a * z * a⁻¹)) * (n * c)⁻¹) * z⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (D.conj_mem_N hCen hU hz
      (Subgroup.inv_mem _ hw))) (D.conj_mem_N hCen hU hz (D.conj_mem_N hCen hU hsX hm₁))
  have hyy : n * c * a * (n * c * a) = (n * c) * (n * c) := by
    have haa : a * a = 1 := K.sq_omega ha
    have hca : a * (n * c) = (n * c) * a := hsA a ha
    calc n * c * a * (n * c * a) = (n * c) * (a * (n * c)) * a := by group
      _ = (n * c) * ((n * c) * a) * a := by rw [hca]
      _ = (n * c) * (n * c) * (a * a) := by group
      _ = (n * c) * (n * c) := by rw [haa, mul_one]
  have hc2 : c * c ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
    refine (mem_omegaOneSub_iff (K.comm_conj' x)).mpr ⟨(conjSubgroup x U).mul_mem hc hc, ?_⟩
    calc c * c * (c * c) = c ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := K.exp_conj x c hc
  have hssN : (n * c) * (n * c) ∈ PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup x U) := by
    rw [show (n * c) * (n * c) = n * (c * n * c⁻¹) * (c * c) by group]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn (D.conj_mem_N hCen hU
      (Subgroup.mem_sup_right hc) hn)) (Subgroup.mem_sup_right hc2)
  have hssC₀ : (n * c) * (n * c) ∈ PartTwo.omegaOneSub (conjSubgroup x U) :=
    D.mem_C₀_of_mem_N hCen hU hssN fun b hb => by
      calc b * ((n * c) * (n * c)) = (b * (n * c)) * (n * c) := by group
        _ = ((n * c) * b) * (n * c) := by rw [hsA b hb]
        _ = (n * c) * (b * (n * c)) := by group
        _ = (n * c) * ((n * c) * b) := by rw [hsA b hb]
        _ = (n * c) * (n * c) * b := by group
  have hsU : ∀ u ∈ U, u * ((n * c) * (n * c)) = ((n * c) * (n * c)) * u := by
    intro u hu
    have huX : u ∈ U ⊔ conjSubgroup x U := Subgroup.mem_sup_left hu
    have hm : u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹ ∈ PartTwo.omegaOneSub U ⊔
        PartTwo.omegaOneSub (conjSubgroup x U) := by
      have h2 := D.conj_mem_N hCen hU huX (hyX u⁻¹ ((U ⊔ conjSubgroup x U).inv_mem huX))
      rwa [show u * (n * c * a * u⁻¹ * (n * c * a)⁻¹ * u⁻¹⁻¹) * u⁻¹ =
        u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹ by group] at h2
    have hm2 := D.sq_N hCen hU hm
    have hym := hyN _ hm
    rw [← hyy]
    calc u * (n * c * a * (n * c * a)) =
        (u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹) * (n * c * a) *
          ((u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹) * (n * c * a)) * u := by group
      _ = (u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹) * ((n * c * a) *
          (u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹) * (n * c * a)⁻¹) *
            ((n * c * a) * (n * c * a)) * u := by group
      _ = (u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹) * (u * (n * c * a) * u⁻¹ * (n * c * a)⁻¹) *
            ((n * c * a) * (n * c * a)) * u := by rw [hym]
      _ = n * c * a * (n * c * a) * u := by rw [hm2, one_mul]
  have hssU₀ : (n * c) * (n * c) ∈ PartTwo.omegaOneSub U := by
    have h1 : (n * c) * (n * c) ∈ PartTwo.omegaOneSub U ⊔
        PartTwo.omegaOneSub (conjSubgroup α U) := by
      rw [D.N_eq hCen hU D.mem D.ne_one]
      exact hssN
    have h2 := P.centN_conj hCen hU (U ⊔ conjSubgroup α U).one_mem h1 (fun d hd => by
      rw [conjSubgroup_one] at hd
      exact hsU d hd)
    rwa [conjSubgroup_one] at h2
  have hmem : (n * c) * (n * c) ∈ U ⊓ conjSubgroup x U :=
    Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le _ hssU₀, PartTwo.omegaOneSub_le _ hssC₀⟩
  rwa [D.inf_UC, Subgroup.mem_bot] at hmem

theorem false_of_linear {f : ℕ} (hf : 3 ≤ f) (hrel : (PartTwo.omegaOneSub U).relIndex U = 2 ^ f)
    [((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
      (U ⊔ conjSubgroup α U)).Normal]
    (e : ↥(U ⊔ conjSubgroup α U) ⧸
      (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
        (U ⊔ conjSubgroup α U) ≃* PSL(2, GaloisField 2 f)) : False := by
  classical
  have K := D.core
  have P := D.pair
  have hXe := D.sup_eq hCen hU D.mem D.ne_one
  have hNe := D.N_eq hCen hU D.mem D.ne_one
  have hce := D.card_eq hCen hU
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) with hNdef
  set S := N ⊔ conjSubgroup x U with hSdef
  set S₁ := S ⊓ Subgroup.centralizer (PartTwo.omegaOneSub (conjSubgroup g U) : Set G)
    with hS₁def
  have hS₁sq : ∀ s ∈ S₁, s * s = 1 := fun s hs => D.sq_eq_one_of_mem_S₁ hCen hU hs
  have hS₁e : Assembly.IsElemAbelian 2 S₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => by rw [sq]; exact hS₁sq z hz⟩
    have hab := hS₁sq _ (S₁.mul_mem a.2 b.2)
    have ha := hS₁sq _ a.2
    have hb := hS₁sq _ b.2
    show (a : G) * b = b * a
    calc (a : G) * b = ((a : G) * b) * ((a : G) * ((b : G) * b) * a) := by
          rw [hb, mul_one, ha, mul_one]
      _ = (((a : G) * b) * ((a : G) * b)) * ((b : G) * a) := by group
      _ = b * a := by rw [hab, one_mul]
  have hC₀S₁ : PartTwo.omegaOneSub (conjSubgroup x U) ≤ S₁ := fun z hz =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right hz),
      Subgroup.mem_centralizer_iff.mpr fun a ha => D.comm_C₀_A₀ hCen hU ha hz⟩
  obtain ⟨K₁, hK₁S₁, hK₁C₀, hK₁sup⟩ := exists_compl_of_isElemAbelian hS₁e hC₀S₁
  have hNK : N ⊓ K₁ = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨hkN, hkK⟩ := Subgroup.mem_inf.mp hk
    have hkC₀ := D.mem_C₀_of_mem_N hCen hU hkN fun a ha =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hK₁S₁ hkK)).2 a ha
    have : k ∈ K₁ ⊓ PartTwo.omegaOneSub (conjSubgroup x U) := Subgroup.mem_inf.mpr ⟨hkK, hkC₀⟩
    rwa [hK₁C₀] at this
  have hNKS : N ⊔ K₁ = S := by
    apply le_antisymm
    · exact sup_le le_sup_left (le_trans hK₁S₁ inf_le_left)
    · intro s hs
      obtain ⟨n, hn, s₁, hs₁, rfl⟩ := D.exists_eq_mul hCen hU hs
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) ?_
      have : s₁ ∈ K₁ ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by rw [hK₁sup]; exact hs₁
      exact (sup_le le_sup_right (le_trans (le_sup_right : PartTwo.omegaOneSub (conjSubgroup x U)
        ≤ N) le_sup_left)) this
  have hNX : PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U) ≤
      U ⊔ conjSubgroup α U := sup_le_sup (PartTwo.omegaOneSub_le U) (PartTwo.omegaOneSub_le _)
  have hSX : S ≤ U ⊔ conjSubgroup α U := by
    rw [hXe]
    exact sup_le (sup_le_sup (PartTwo.omegaOneSub_le U) (PartTwo.omegaOneSub_le _)) le_sup_right
  have hK₁X : K₁ ≤ U ⊔ conjSubgroup α U := le_trans (le_trans hK₁S₁ inf_le_left) hSX
  have hCX : conjSubgroup x U ≤ U ⊔ conjSubgroup α U := by
    rw [hXe]
    exact le_sup_right
  have : IsMulCommutative ↥((PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U)) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (P.comm_N hCen hU (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hNK' : (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
      (U ⊔ conjSubgroup α U) ⊓ K₁.subgroupOf (U ⊔ conjSubgroup α U) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have hz1' : (z : G) ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U) :=
      Subgroup.mem_subgroupOf.mp hz1
    rw [hNe] at hz1'
    have hz : (z : G) ∈ N ⊓ K₁ := Subgroup.mem_inf.mpr ⟨hz1', Subgroup.mem_subgroupOf.mp hz2⟩
    rw [hNK, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.mpr (Subtype.ext hz)
  have hsup' : (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
      (U ⊔ conjSubgroup α U) ⊔ K₁.subgroupOf (U ⊔ conjSubgroup α U) =
        S.subgroupOf (U ⊔ conjSubgroup α U) := by
    rw [← Subgroup.subgroupOf_sup hNX hK₁X, hNe, hNKS]
  have hπ : Function.Surjective (QuotientGroup.mk' ((PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' ((PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))).ker ≤
        S.subgroupOf (U ⊔ conjSubgroup α U) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    have h1 : (z : G) ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U) :=
      Subgroup.mem_subgroupOf.mp hz
    rw [hNe] at h1
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left h1)
  have hidx := Subgroup.index_map_eq (S.subgroupOf (U ⊔ conjSubgroup α U)) hπ hker
  have hCS : ((conjSubgroup x U).subgroupOf (U ⊔ conjSubgroup α U)).map
      (QuotientGroup.mk' ((PartTwo.omegaOneSub U ⊔
        PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))) ≤
          (S.subgroupOf (U ⊔ conjSubgroup α U)).map (QuotientGroup.mk' ((PartTwo.omegaOneSub U ⊔
            PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))) :=
    Subgroup.map_mono fun z hz =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hz))
  have hdvd := Subgroup.index_dvd_of_le hCS
  have hcard1 := card_map_mk_mul
    (N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)) hCX
  have hinf : conjSubgroup x U ⊓ (PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup α U)) = PartTwo.omegaOneSub (conjSubgroup x U) := by
    rw [hNe]
    exact D.inf_N hCen hU
  rw [hinf] at hcard1
  have hC₀card : Nat.card ↥(PartTwo.omegaOneSub (conjSubgroup x U)) = 2 ^ f := by
    rw [omegaOneSub_conj K.comm x, card_conjSubgroup, hce, hrel]
  have hCcard : Nat.card ↥(conjSubgroup x U) = 2 ^ f * 2 ^ f := by
    have h1 := Subgroup.relIndex_mul_card (PartTwo.omegaOneSub U) U
    rw [inf_of_le_left (PartTwo.omegaOneSub_le U), hrel, hce, hrel] at h1
    rw [card_conjSubgroup, ← h1]
  rw [hC₀card, hCcard] at hcard1
  have hCbar := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ f) hcard1
  have hXbar : Nat.card (↥(U ⊔ conjSubgroup α U) ⧸ (PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U)) =
        2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr (e.trans pslMulEquivSL).toEquiv, card_SL_two_galoisField (by omega)]
  have hCidx : (((conjSubgroup x U).subgroupOf (U ⊔ conjSubgroup α U)).map
      (QuotientGroup.mk' ((PartTwo.omegaOneSub U ⊔
        PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U)))).index =
          (2 ^ f) ^ 2 - 1 := by
    have h1 := Subgroup.card_mul_index (((conjSubgroup x U).subgroupOf (U ⊔ conjSubgroup α U)).map
      (QuotientGroup.mk' ((PartTwo.omegaOneSub U ⊔
        PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))))
    rw [hCbar, hXbar] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
    have h4 : Even ((2 ^ f) ^ 2) :=
      Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, two_ne_zero⟩
    have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    obtain ⟨k, hk⟩ := h4
    exact ⟨k - 1, by omega⟩
  have hoddS : Odd (S.subgroupOf (U ⊔ conjSubgroup α U)).index := by
    rw [← hidx]
    rw [hCidx] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  have hNcard : Nat.card ↥((PartTwo.omegaOneSub U ⊔
      PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U)) =
        2 ^ (f + f) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, P.card_N hCen hU,
      K.card_omega_conj α, hce, hrel, ← pow_add]
  have hcop : Nat.Coprime (S.subgroupOf (U ⊔ conjSubgroup α U)).index
      (Nat.card ↥((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
        (U ⊔ conjSubgroup α U))) := by
    rw [hNcard]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hoddS)
  obtain ⟨Dc, hDc, -, -⟩ := CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting
    ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
      (U ⊔ conjSubgroup α U)) (S.subgroupOf (U ⊔ conjSubgroup α U))
    (K₁.subgroupOf (U ⊔ conjSubgroup α U)) hcop hNK' hsup'
  exact tim78_2_10_d hCen hU P.setup P.exp hf e Dc hDc

end Data31

end CFSG.RankThree.GF2n.Tim78
