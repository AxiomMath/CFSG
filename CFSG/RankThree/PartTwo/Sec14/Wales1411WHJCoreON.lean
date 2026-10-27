module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
public import CFSG.RankThree.Native.ONTripleRed
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA6A6
import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenCores
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.LargeExtraspecial.S8DimB
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenGroups

public section

namespace CFSG.RankThree.PartTwo.Sec14

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.Native.ONTriple
open scoped commutatorElement

namespace Wales1411W.HJON

section Model


theorem comm_mem_center {X : Type} [Group X] [Finite X] (ψ : X ≃* GM) (P : Sylow 3 X) {p q : X}
    (hp : p ∈ (P : Subgroup X)) (hq : q ∈ (P : Subgroup X)) : ⁅p, q⁆ ∈ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ((P : Subgroup X).map ψ.toMonoidHom) =
      3 ^ (Nat.card GM).factorization 3 := by
    rw [Subgroup.card_map_of_injective ψ.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr ψ.toEquiv]
  obtain ⟨g, hg⟩ := sylow_eq_threeQ (Sylow.ofCard _ hcard)
  have hr := relG_conj g
  have hp' : ψ p ∈ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := by
    rw [← hg]
    exact ⟨p, hp, rfl⟩
  have hq' : ψ q ∈ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := by
    rw [← hg]
    exact ⟨q, hq, rfl⟩
  have h := hr.comm_mem hp' hq'
  have hz : MulAut.conj g zG = zG := conj_zG g
  rw [hz] at h
  rw [Sec13.ON134.mem_center_iff_model ψ, map_commutatorElement]
  exact h

end Model

@[expose] def commHom {X : Type*} [Group X] (x : X) (P : Subgroup X)
    (hc : ∀ p ∈ P, ⁅x, p⁆ ∈ Subgroup.center X) : ↥P →* X where
  toFun p := ⁅x, (p : X)⁆
  map_one' := by simp [commutatorElement_def]
  map_mul' p q := by
    have h := (Subgroup.mem_center_iff.mp (hc q q.2)) (p : X)
    simp only [Subgroup.coe_mul, commutatorElement_def] at h ⊢
    calc x * (↑p * ↑q) * x⁻¹ * (↑p * ↑q)⁻¹ =
        x * ↑p * x⁻¹ * (↑p)⁻¹ * (↑p * (x * ↑q * x⁻¹ * (↑q)⁻¹)) * (↑p)⁻¹ := by group
      _ = x * ↑p * x⁻¹ * (↑p)⁻¹ * ((x * ↑q * x⁻¹ * (↑q)⁻¹) * ↑p) * (↑p)⁻¹ := by rw [h]
      _ = x * ↑p * x⁻¹ * (↑p)⁻¹ * (x * ↑q * x⁻¹ * (↑q)⁻¹) := by group

variable {G : Type} [Group G] [Finite G] {Ybar Abar Xbar Rbar : Subgroup G} {abar : G}

theorem center_map_eq (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) [Xbar.Normal]
    (hZ3 : Nat.card (Subgroup.center ↥Xbar) = 3) :
    (Subgroup.center ↥Xbar).map Xbar.subtype = Subgroup.zpowers abar := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Zh := (Subgroup.center ↥Xbar).map Xbar.subtype with hZh
  have hZh3 : Nat.card Zh = 3 := by
    rw [hZh, Subgroup.card_map_of_injective Xbar.subtype_injective, hZ3]
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  have hZA : ∀ z ∈ Zh, ∀ e ∈ Abar, e * z = z * e := by
    intro z hz e he
    have hσ3 : (MulAut.conj e) ^ 3 = 1 := by rw [← map_pow, hA3 e he, map_one]
    have hσZ : ∀ y ∈ Zh, MulAut.conj e y ∈ Zh := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨MulAut.conjNormal e y, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hy ⊢
        intro g
        obtain ⟨g', rfl⟩ := (MulAut.conjNormal e).surjective g
        rw [← map_mul, ← map_mul, hy g']
      · simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    have h := HJA6A6.fixed_of_card_three hZh3 hσ3 hσZ hz
    rw [MulAut.conj_apply] at h
    calc e * z = e * z * e⁻¹ * e := by group
      _ = z * e := by rw [h]
  have hZA' : Zh ≤ Abar := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact one_mem _
    refine hset.mem_A_of_three z ?_ ?_ ?_
    · obtain ⟨y, -, rfl⟩ := hz
      exact hset.le_Y y.2
    · rw [Subgroup.mem_centralizer_iff]
      exact fun e he => hZA z hz e he
    · have h := Subgroup.orderOf_dvd_natCard Zh hz
      rw [hZh3] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
  have hle : Zh ≤ Subgroup.zpowers abar := by
    intro z hz
    refine hset.mem_zpowers z (hZA' hz) (HJInner.le_centralizer_Y_of_X hset (hZA' hz) ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨y, hy, rfl⟩ := hz
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hy) ⟨x, hx⟩)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hZh3, Nat.card_zpowers, orderOf_eq_prime (hA3 abar hset.mem_A) hset.ne_one]

theorem commute_abar (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) (m : G) :
    m * abar = abar * m := by
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({abar} : Set G) := by
    rw [← hset.sup_eq_top]
    refine sup_le hset.le_centralizer_a fun e he => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨e, he⟩ ⟨abar, hset.mem_A⟩)
  exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top m))

theorem exists_inner
    (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) [Xbar.Normal] (ψ : ↥Xbar ≃* GM)
    (hcen : (Subgroup.center ↥Xbar).map Xbar.subtype = Subgroup.zpowers abar) (m : G) :
    ∃ x : ↥Xbar, ∀ y : ↥Xbar, MulAut.conjNormal m y = x * y * x⁻¹ := by
  refine Sec13.ON134.aut_inner ψ (MulAut.conjNormal m) fun z hz => ?_
  have hz' : (z : G) ∈ Subgroup.zpowers abar := hcen ▸ ⟨z, hz, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, ← hk, (Commute.zpow_right (commute_abar hset m) k).eq,
    mul_inv_cancel_right]

theorem exists_gens (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) :
    ∃ e₁ ∈ Abar, ∃ e₂ ∈ Abar,
      Abar = Subgroup.zpowers abar ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  have hAc : ∀ g ∈ Abar, ∀ h ∈ Abar, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hcard : ∀ B : Subgroup G, B ≤ Abar → ∀ h ∈ Abar, h ≠ 1 → h ∉ B →
      Nat.card (B ⊔ Subgroup.zpowers h : Subgroup G) = 3 * Nat.card B := by
    intro B hB h hh hh1 hhB
    have hh3 : Nat.card (Subgroup.zpowers h) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hA3 h hh) hh1
    have hN : Subgroup.zpowers h ≤ Subgroup.normalizer (B : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      rw [hAc h hh z (hB hz), mul_inv_cancel_right]
      exact hz
    have hinf : B ⊓ Subgroup.zpowers h = ⊥ := by
      rcases (Nat.dvd_prime Nat.prime_three).mp
          (hh3 ▸ Subgroup.card_dvd_of_le (inf_le_right : B ⊓ Subgroup.zpowers h ≤ _)) with
        h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have heq : B ⊓ Subgroup.zpowers h = Subgroup.zpowers h :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hh3])
        exact hhB (Subgroup.mem_inf.mp (heq.symm ▸ Subgroup.mem_zpowers h)).1
    have hc := CFSG.LargeExtraspecial.S8.card_sup_mul_card_inf_of_le_normalizer' hN
    rw [hinf, Subgroup.card_bot, mul_one, hh3] at hc
    rw [hc, mul_comm]
  have ha3 : Nat.card (Subgroup.zpowers abar) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA3 abar hset.mem_A) hset.ne_one
  have hnle1 : ¬ Abar ≤ Subgroup.zpowers abar := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hset.card_A, ha3] at this
    norm_num at this
  obtain ⟨e₁, he₁A, he₁⟩ := SetLike.not_le_iff_exists.mp hnle1
  have he₁1 : e₁ ≠ 1 := fun h => he₁ (h ▸ one_mem _)
  have hB₁A : Subgroup.zpowers abar ⊔ Subgroup.zpowers e₁ ≤ Abar :=
    sup_le (Subgroup.zpowers_le.mpr hset.mem_A) (Subgroup.zpowers_le.mpr he₁A)
  have hB₁9 : Nat.card (Subgroup.zpowers abar ⊔ Subgroup.zpowers e₁ : Subgroup G) = 9 := by
    rw [hcard _ (Subgroup.zpowers_le.mpr hset.mem_A) e₁ he₁A he₁1 he₁, ha3]
  have hnle2 : ¬ Abar ≤ Subgroup.zpowers abar ⊔ Subgroup.zpowers e₁ := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hset.card_A, hB₁9] at this
    norm_num at this
  obtain ⟨e₂, he₂A, he₂⟩ := SetLike.not_le_iff_exists.mp hnle2
  have he₂1 : e₂ ≠ 1 := fun h => he₂ (h ▸ one_mem _)
  refine ⟨e₁, he₁A, e₂, he₂A,
    (Subgroup.eq_of_le_of_card_ge (sup_le hB₁A (Subgroup.zpowers_le.mpr he₂A)) ?_).symm⟩
  rw [hcard _ hB₁A e₂ he₂A he₂1 he₂, hB₁9, hset.card_A]

theorem le_X
    (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) [Xbar.Normal] (ψ : ↥Xbar ≃* GM)
    (hZ3 : Nat.card (Subgroup.center ↥Xbar) = 3)
    (hinn : ∀ m : G, ∃ x : ↥Xbar, ∀ y : ↥Xbar, MulAut.conjNormal m y = x * y * x⁻¹) :
    Abar ≤ Xbar := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  have hAp : IsPGroup 3 Abar := IsPGroup.of_card (n := 3) (by rw [hset.card_A]; norm_num)
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal Q (N := Xbar)
  have hmemP : ∀ x : ↥Xbar, x ∈ (P : Subgroup ↥Xbar) ↔ (x : G) ∈ (Q : Subgroup G) := by
    intro x
    rw [hP, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hexp : ∀ p ∈ (P : Subgroup ↥Xbar), p ^ 3 = 1 := fun p hp => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    exact Sec13.ON134.pow_three_eq_one ψ (k := k) (by simpa using congrArg Subtype.val hk)
  have hcomm : ∀ p ∈ (P : Subgroup ↥Xbar), ∀ q ∈ (P : Subgroup ↥Xbar),
      ⁅p, q⁆ ∈ Subgroup.center ↥Xbar := fun p hp q hq => comm_mem_center ψ P hp hq
  have hAP : ∀ e ∈ Abar, ∀ p ∈ (P : Subgroup ↥Xbar),
      MulAut.conjNormal e p ∈ (P : Subgroup ↥Xbar) := by
    intro e he p hp
    rw [hmemP] at hp ⊢
    rw [MulAut.conjNormal_apply]
    exact mul_mem (mul_mem (hAQ he) hp) (inv_mem (hAQ he))
  have hxe : ∀ e ∈ Abar, ∃ x ∈ (P : Subgroup ↥Xbar),
      ∀ y : ↥Xbar, MulAut.conjNormal e y = x * y * x⁻¹ := by
    intro e he
    obtain ⟨x, hx⟩ := hinn e
    refine ⟨x, ?_, hx⟩
    have hx3c : x ^ 3 ∈ Subgroup.center ↥Xbar := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : (MulAut.conjNormal e ^ 3) y = y := by
        rw [← map_pow, hA3 e he, map_one, MulAut.one_apply]
      rw [Sec13.ON134.pow_apply_of_conj hx 3 y] at h1
      calc y * x ^ 3 = x ^ 3 * y * (x ^ 3)⁻¹ * x ^ 3 := by rw [h1]
        _ = x ^ 3 * y := by group
    have hx9 : x ^ 3 ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center ↥Xbar) (x := ⟨x ^ 3, hx3c⟩)
      rw [hZ3] at h
      have h' : (x ^ 3) ^ 3 = 1 := by simpa using congrArg Subtype.val h
      rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
      exact h'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx9)
    have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hN : Subgroup.zpowers x ≤ Subgroup.normalizer ((P : Subgroup ↥Xbar) : Set ↥Xbar) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      rw [← hx y]
      exact hAP e he y hy
    have hsup := hxp.to_sup_of_normal_right' P.isPGroup' hN
    rw [← P.is_maximal' hsup le_sup_right]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hind : ∀ e ∈ Abar, ∃ C : Subgroup ↥(P : Subgroup ↥Xbar), C.index ≤ 3 ∧
      ∀ c ∈ C, e * ((c : ↥Xbar) : G) = ((c : ↥Xbar) : G) * e := by
    intro e he
    obtain ⟨x, hxP, hx⟩ := hxe e he
    set χ := commHom x (P : Subgroup ↥Xbar) (fun p hp => hcomm x hxP p hp) with hχ
    refine ⟨χ.ker, ?_, fun c hc => ?_⟩
    · rw [Subgroup.index_ker]
      have hle : χ.range ≤ Subgroup.center ↥Xbar := by
        rintro _ ⟨p, rfl⟩
        exact hcomm x hxP p p.2
      have := Subgroup.card_le_of_le hle
      rwa [hZ3] at this
    · have h1 : ⁅x, (c : ↥Xbar)⁆ = 1 := MonoidHom.mem_ker.mp hc
      have h2 : x * (c : ↥Xbar) * x⁻¹ = c := by
        rw [commutatorElement_def] at h1
        calc x * ↑c * x⁻¹ = x * ↑c * x⁻¹ * (↑c)⁻¹ * ↑c := by group
          _ = ↑c := by rw [h1, one_mul]
      have h3 := congrArg Subtype.val ((hx c).trans h2)
      rw [MulAut.conjNormal_apply] at h3
      calc e * ((c : ↥Xbar) : G) = e * ((c : ↥Xbar) : G) * e⁻¹ * e := by group
        _ = ((c : ↥Xbar) : G) * e := by rw [h3]
  obtain ⟨e₁, he₁, e₂, he₂, hgens⟩ := exists_gens hset
  obtain ⟨C₁, hC₁, hC₁c⟩ := hind e₁ he₁
  obtain ⟨C₂, hC₂, hC₂c⟩ := hind e₂ he₂
  have hcardP : Nat.card ↥(P : Subgroup ↥Xbar) = 243 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr ψ.toEquiv, factorization_card_GM]
    norm_num
  have hC27 : 27 ≤ Nat.card ↥(C₁ ⊓ C₂) := by
    have h := (C₁ ⊓ C₂).card_mul_index
    rw [hcardP] at h
    have hi : (C₁ ⊓ C₂).index ≤ 9 := Subgroup.index_inf_le.trans (Nat.mul_le_mul hC₁ hC₂)
    have : 243 ≤ Nat.card ↥(C₁ ⊓ C₂) * 9 := h ▸ Nat.mul_le_mul_left _ hi
    omega
  set Cm : Subgroup G := ((C₁ ⊓ C₂).map (P : Subgroup ↥Xbar).subtype).map Xbar.subtype with hCm
  have hCmcard : Nat.card Cm = Nat.card ↥(C₁ ⊓ C₂) := by
    rw [hCm, Subgroup.card_map_of_injective Xbar.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hCmA : Cm ≤ Abar := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    show (((c : ↥(P : Subgroup ↥Xbar)) : ↥Xbar) : G) ∈ Abar
    set y : G := (((c : ↥(P : Subgroup ↥Xbar)) : ↥Xbar) : G) with hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    have hyY : y ∈ Ybar := hset.le_Y (c : ↥Xbar).2
    refine hset.mem_A_of_three y hyY ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hle : Subgroup.zpowers abar ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ ≤
          Subgroup.centralizer ({y} : Set G) := by
        refine sup_le (sup_le ?_ ?_) ?_ <;>
          rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        · exact (Subgroup.mem_centralizer_singleton_iff.mp (hset.le_centralizer_a hyY)).symm
        · exact hC₁c c (Subgroup.mem_inf.mp hc).1
        · exact hC₂c c (Subgroup.mem_inf.mp hc).2
      rw [hgens] at ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    · refine orderOf_eq_prime ?_ hy1
      have h := hexp _ (c : ↥(P : Subgroup ↥Xbar)).2
      simpa [hy] using congrArg Subtype.val h
  have hCmeq := Subgroup.eq_of_le_of_card_ge hCmA (by rw [hset.card_A, hCmcard]; exact hC27)
  rw [← hCmeq]
  exact Subgroup.map_subtype_le _

theorem Y_eq_X (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) [hXn : Xbar.Normal]
    (hcen : (Subgroup.center ↥Xbar).map Xbar.subtype = Subgroup.zpowers abar)
    (hinn : ∀ m : G, ∃ x : ↥Xbar, ∀ y : ↥Xbar, MulAut.conjNormal m y = x * y * x⁻¹) :
    Ybar = Xbar := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRY : Rbar ≤ Ybar := hset.eq_sup ▸ le_sup_right
  have haX : abar ∈ Xbar := by
    have h : abar ∈ (Subgroup.center ↥Xbar).map Xbar.subtype := hcen ▸ Subgroup.mem_zpowers abar
    obtain ⟨y, -, hy⟩ := h
    exact hy ▸ y.2
  have hao : orderOf abar = 3 :=
    orderOf_eq_prime (hset.isElemAbelian.2 abar hset.mem_A) hset.ne_one
  set C : Subgroup G := Ybar ⊓ Subgroup.centralizer (Xbar : Set G) with hCdef
  have hYXC : Ybar ≤ Xbar ⊔ C := by
    have hR : Rbar ≤ Xbar ⊔ C := by
      intro r hr
      obtain ⟨x, hx⟩ := hinn r
      have hc : (x : G)⁻¹ * r ∈ C := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hset.le_Y x.2)) (hRY hr), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h := congrArg Subtype.val (hx ⟨y, hy⟩)
        simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
        calc y * ((x : G)⁻¹ * r) = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * r := by group
          _ = (x : G)⁻¹ * (r * y * r⁻¹) * r := by rw [← h]
          _ = (x : G)⁻¹ * r * y := by group
      have e : r = (x : G) * ((x : G)⁻¹ * r) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right hc)
    intro y hy
    have hy' : y ∈ Xbar ⊔ Rbar := hset.eq_sup ▸ hy
    exact (sup_le le_sup_left hR) hy'
  have hCX : ∀ c ∈ C, c ∈ Xbar → c ∈ Subgroup.zpowers abar := by
    intro c hc hcX
    rw [← hcen]
    refine ⟨⟨c, hcX⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) y y.2)
  have h3X : ∀ c ∈ Ybar, ∀ k : ℕ, c ^ 3 ^ k = 1 → c ∈ Xbar := by
    intro c hc k hck
    have hπ : (QuotientGroup.mk' Xbar) c ∈ Rbar.map (QuotientGroup.mk' Xbar) := by
      have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' Xbar) hc
      rwa [hset.eq_sup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h
    obtain ⟨r, hr, hrc⟩ := hπ
    have h1 : orderOf ((QuotientGroup.mk' Xbar) c) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hck, map_one])
    have h2 : orderOf ((QuotientGroup.mk' Xbar) c) ∣ Nat.card Rbar := by
      rw [← hrc]
      exact (orderOf_map_dvd _ r).trans (Subgroup.orderOf_dvd_natCard Rbar hr)
    have hcop : Nat.Coprime (3 ^ k) (Nat.card Rbar) := Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hset.not_three_dvd_R)
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h3
    exact h3
  have haC : abar ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨hset.le_Y haX, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    exact fun x _ => commute_abar hset x
  set N : Subgroup ↥C := (Subgroup.zpowers abar).subgroupOf C with hN
  have hNc : ∀ n ∈ N, ∀ y : ↥C, n * y = y * n := by
    intro n hn y
    apply Subtype.ext
    rw [hN, Subgroup.mem_subgroupOf] at hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (Commute.zpow_left (commute_abar hset (y : G)).symm k).eq
  haveI hNn : N.Normal := ⟨fun n hn g => by
    have h := hNc n hn g
    have e : g * n * g⁻¹ = n := by rw [← h]; group
    rw [e]
    exact hn⟩
  have hN3 : Nat.card N = 3 := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr haC)).toEquiv,
      Nat.card_zpowers, hao]
  have hidx : ¬ 3 ∣ N.index := by
    intro h3
    have h9 : 3 ^ 2 ∣ Nat.card ↥C := by
      rw [← N.card_mul_index, hN3, pow_two]
      exact Nat.mul_dvd_mul_left 3 h3
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
    have hHN : H ≤ N := by
      intro h hh
      have h9' : h ^ 3 ^ 2 = 1 := by
        have := pow_card_eq_one' (G := H) (x := ⟨h, hh⟩)
        rw [hH] at this
        simpa using congrArg Subtype.val this
      rw [hN, Subgroup.mem_subgroupOf]
      exact hCX h h.2 (h3X h (Subgroup.mem_inf.mp h.2).1 2
        (by simpa using congrArg Subtype.val h9'))
    have := Subgroup.card_le_of_le hHN
    rw [hH, hN3] at this
    norm_num at this
  have hcop3 : Nat.Coprime 3 N.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx
  have hcop : Nat.Coprime (Nat.card N) N.index := by rw [hN3]; exact hcop3
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card K = N.index := by
    have h1 := hK.card_mul_card
    have h2 := N.card_mul_index
    rw [hN3] at h1 h2
    omega
  have hpowK : ∀ k ∈ K, k ^ N.index = 1 := fun k hk => by
    have := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
    rw [hKcard] at this
    simpa using congrArg Subtype.val this
  have hKiff : ∀ c : ↥C, c ∈ K ↔ c ^ N.index = 1 := by
    intro c
    refine ⟨hpowK c, fun hc => ?_⟩
    obtain ⟨⟨⟨n, hn⟩, ⟨k, hk⟩⟩, hnk, -⟩ := (Subgroup.isComplement'_def.mp hK).existsUnique c
    simp only at hnk
    have hnm : n ^ N.index = 1 := by
      have e : c ^ N.index = n ^ N.index * k ^ N.index := by
        rw [← hnk]
        exact Commute.mul_pow (hNc n hn k) _
      rw [hpowK k hk, mul_one, hc] at e
      exact e.symm
    have hn3 : n ^ 3 = 1 := by
      have := pow_card_eq_one' (G := N) (x := ⟨n, hn⟩)
      rw [hN3] at this
      simpa using congrArg Subtype.val this
    have hn1 : n = 1 := by
      have h : n ^ Nat.gcd 3 N.index = 1 := pow_gcd_eq_one.mpr ⟨hn3, hnm⟩
      rwa [hcop3.gcd_eq_one, pow_one] at h
    rw [← hnk, hn1, one_mul]
    exact hk
  set K' : Subgroup G := K.map C.subtype with hK'
  have hK'Y : K' ≤ Ybar := (Subgroup.map_subtype_le K).trans inf_le_left
  have hYK' : Ybar ≤ Subgroup.normalizer (K' : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    obtain ⟨hk₀Y, hk₀C⟩ := Subgroup.mem_inf.mp k₀.2
    have hyk : y * (k₀ : G) * y⁻¹ ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hy hk₀Y) (inv_mem hy), ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hk₀C ⊢
      intro x hx
      have hx' : y⁻¹ * x * y ∈ Xbar := by
        have := hXn.conj_mem x hx y⁻¹
        simpa using this
      have h := hk₀C _ hx'
      calc x * (y * ↑k₀ * y⁻¹) = y * ((y⁻¹ * x * y) * ↑k₀) * y⁻¹ := by group
        _ = y * (↑k₀ * (y⁻¹ * x * y)) * y⁻¹ := by rw [h]
        _ = y * ↑k₀ * y⁻¹ * x := by group
    refine ⟨⟨_, hyk⟩, (hKiff _).mpr ?_, rfl⟩
    apply Subtype.ext
    have hk0m : (k₀ : G) ^ N.index = 1 := by
      simpa using congrArg Subtype.val (hpowK k₀ hk₀)
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [conj_pow, hk0m, mul_one, mul_inv_cancel]
  have hK'3 : ¬ 3 ∣ Nat.card K' := by
    rw [hK', Subgroup.card_map_of_injective C.subtype_injective, hKcard]
    exact hidx
  have hK'bot := hset.eq_bot_of_three K' hK'Y hYK' hK'3
  have hidx1 : N.index = 1 := by
    rw [← hKcard, ← Subgroup.card_map_of_injective C.subtype_injective, ← hK', hK'bot,
      Subgroup.card_bot]
  have hNtop : N = ⊤ := Subgroup.index_eq_one.mp hidx1
  have hCX' : C ≤ Xbar := by
    intro c hc
    have h : (⟨c, hc⟩ : ↥C) ∈ N := hNtop ▸ Subgroup.mem_top _
    rw [hN, Subgroup.mem_subgroupOf] at h
    exact (Subgroup.zpowers_le.mpr haX) h
  exact le_antisymm (hYXC.trans (sup_le le_rfl hCX')) hset.le_Y

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary in
theorem XG_sup_ne_top
    {j l₁ m₁ l₂ m₂ : ℕ} (hj : j < 2) (hl₁ : l₁ < 4)
    (hm₁ : m₁ < 3) (hl₂ : l₂ < 4) (hm₂ : m₂ < 3) :
    XG j l₁ m₁ hj hm₁ ⊔ XG j l₂ m₂ hj hm₂ ≠ ⊤ := by
  have hGM := card_GM
  have htwo : ∀ {a b c d : ℕ} (ha : a < 4) (hb : b < 3) (hc : c < 4) (hd : d < 3), a < c →
      XG j a b hj hb ⊔ XG j c d hj hd ≠ ⊤ := by
    intro a b c d ha hb hc hd hac htop
    set Lp := Subgroup.closure (Set.range (L3Seven.pairY j a b c d)) with hLp
    have hLp_ne : Lp ≠ ⊥ := by
      intro h
      have hx : L3Seven.xE j a b 0 ∈ Lp := Subgroup.subset_closure ⟨0, rfl⟩
      rw [h, Subgroup.mem_bot] at hx
      exact L3Seven.xE_ne_one hj hb (i := 0) (by norm_num) hx
    obtain ⟨y, hy, hcl⟩ := L3Seven.exists_rels_pair hj ha hc hac b d hb hd
    have hLp_card : Nat.card Lp = 1876896 := L3Seven.card_closure_eq y hy hcl hLp_ne
    have hle : XG j a b hj hb ⊔ XG j c d hj hd ≤ Lp := by
      rw [L3Seven.XG_eq_closure hj hb, L3Seven.XG_eq_closure hj hd, ← Subgroup.closure_union,
        Subgroup.closure_le]
      rintro x ((rfl | rfl) | (rfl | rfl))
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨1, rfl⟩
      · exact Subgroup.subset_closure ⟨2, rfl⟩
      · exact Subgroup.subset_closure ⟨3, rfl⟩
    rw [htop, top_le_iff] at hle
    rw [hle, Subgroup.card_top, hGM] at hLp_card
    norm_num at hLp_card
  rcases lt_trichotomy l₁ l₂ with h | rfl | h
  · exact htwo hl₁ hm₁ hl₂ hm₂ h
  ·
    intro htop
    have hle : XG j l₁ m₁ hj hm₁ ⊔ XG j l₁ m₂ hj hm₂ ≤ KL j l₁ :=
      sup_le (XG_le_K hj hm₁) (XG_le_K hj hm₂)
    rw [htop, top_le_iff] at hle
    have hcard : Nat.card (KL j l₁) = 1080 := by
      rw [KL, Subgroup.card_map_of_injective (MulAut.conj _).injective, centralizer_x0_eq.2]
    rw [hle, Subgroup.card_top, hGM] at hcard
    norm_num at hcard
  · rw [sup_comm]
    exact htwo hl₂ hm₂ hl₁ hm₁ h

end Wales1411W.HJON

open Wales1411W Wales1411W.HJON in
theorem ks1411HJCoreON :
    KS1411HJCoreON := by
  intro G _ _ Ybar Abar Xbar Rbar abar hset hX S T hS hT hST _
  exfalso
  haveI := HJInner.normal_X hset
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hset.perfect hX
  have hcen := center_map_eq hset hX.1
  have hinn := exists_inner hset ψ hcen
  have hAX := le_X hset ψ hX.1 hinn
  have hYX := Y_eq_X hset hcen hinn
  set A₀ : Subgroup ↥Xbar := Abar.subgroupOf Xbar with hA₀
  have hA₀e : Late.IsE27 A₀ := by
    refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
    · have h := congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm
        ⟨_, Subgroup.mem_subgroupOf.mp u.2⟩ ⟨_, Subgroup.mem_subgroupOf.mp v.2⟩)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    · apply Subtype.ext
      simpa using hset.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp ha)
    · rw [hA₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, hset.card_A]
  obtain ⟨h, j, hj, hAj⟩ :=
    exists_conj_AG (Sec13.ON134.isE27_map hA₀e ψ.toMonoidHom ψ.injective)
  set φ : ↥Xbar ≃* GM := ψ.trans (MulAut.conj h) with hφ
  have hφA : A₀.map φ.toMonoidHom = AG j := by
    rw [← hAj, Subgroup.map_map]
    rfl
  have h2 : ∀ U : Subgroup G, InvTwo Abar Ybar U →
      IsPGroup 2 ((U.subgroupOf Xbar).map φ.toMonoidHom) := by
    rintro U ⟨hUY, -, hU2⟩
    exact (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe (hYX ▸ hUY)).symm).map φ.toMonoidHom
  have himg : ∀ U : Subgroup G, InvTwo Abar Ybar U →
      (U.subgroupOf Xbar).map φ.toMonoidHom = ⊥ ∨ ∃ l < 4, ∃ (m : ℕ) (hm : m < 3),
        (U.subgroupOf Xbar).map φ.toMonoidHom = XG j l m hj hm := by
    intro U hU
    have hAU := hU.2.1
    refine inv_two_subgroups hj _ ((isPiSubgroup_piOf_iff Nat.prime_two _).mpr (h2 U hU)) ?_
    intro a ha
    rw [← hφA] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    change φ a₀ ∈ Subgroup.normalizer (((U.subgroupOf Xbar).map φ.toMonoidHom : Subgroup GM) :
      Set GM)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨y₀, rfl⟩ := φ.surjective y
    have h1 : φ y₀ ∈ (U.subgroupOf Xbar).map φ.toMonoidHom ↔ y₀ ∈ U.subgroupOf Xbar := by
      rw [Subgroup.mem_map_equiv]
      simp
    have h3 : φ a₀ * φ y₀ * (φ a₀)⁻¹ ∈ (U.subgroupOf Xbar).map φ.toMonoidHom ↔
        a₀ * y₀ * a₀⁻¹ ∈ U.subgroupOf Xbar := by
      rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_equiv]
      simp
    rw [h1, h3, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hAU (Subgroup.mem_subgroupOf.mp ha₀)) y₀
  have hSX : S ≤ Xbar := hYX ▸ hS.prop.1
  have hTX : T ≤ Xbar := hYX ▸ hT.prop.1
  have hsup : (S.subgroupOf Xbar).map φ.toMonoidHom ⊔ (T.subgroupOf Xbar).map φ.toMonoidHom =
      ⊤ := by
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hSX hTX, hST, hYX, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ φ.surjective]
  have hne : ∀ U : Subgroup G, InvTwo Abar Ybar U →
      (U.subgroupOf Xbar).map φ.toMonoidHom ≠ ⊤ := by
    intro U hU htop
    have hp := h2 U hU
    rw [htop] at hp
    obtain ⟨n, hn⟩ := hp ⟨zG, Subgroup.mem_top _⟩
    have hzn : zG ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd := orderOf_dvd_of_pow_eq_one hzn
    rw [relG.orderOf_x] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    norm_num at this
  rcases himg S hS.prop with hS' | ⟨l₁, hl₁, m₁, hm₁, hS'⟩
  · rw [hS', bot_sup_eq] at hsup
    exact hne T hT.prop hsup
  rcases himg T hT.prop with hT' | ⟨l₂, hl₂, m₂, hm₂, hT'⟩
  · rw [hT', sup_bot_eq] at hsup
    exact hne S hS.prop hsup
  rw [hS', hT'] at hsup
  exact XG_sup_ne_top hj hl₁ hm₁ hl₂ hm₂ hsup

end CFSG.RankThree.PartTwo.Sec14
