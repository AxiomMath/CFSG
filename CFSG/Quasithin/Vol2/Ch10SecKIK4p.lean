module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4o
public import CFSG.Quasithin.Vol2.Ch10SecKIK4j
public import CFSG.Quasithin.Vol2.Ch10SecKIK4n

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem mem_centralizer_of_conjAct_eq_one {V : Subgroup G} {g : Subgroup.normalizer (V : Set G)}
    (h : conjAct V g = 1) : (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h
  simp only [MulAut.one_apply] at h1
  rw [InternalSec.coe_conjAct_apply] at h1
  calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * g := by rw [h1]
    _ = g * v := by group

variable [Finite G]

theorem case_b2 {R J V L : Subgroup G} [IsMulCommutative ↥V] {F : Subgroup (MulAut ↥V)}
    (π : Equiv.Perm (Fin 7) →* ↥F) (hR : (FFModel.symDn 7).RealizesVia F ⊤ ⊥ π)
    (hinj : Function.Injective π) (hJF : autOn J V ≤ F) (hX : Nat.card ↥(autOn J V) = 2520)
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hSJ : IsSylowTwoOf (R ⊓ J) J) (hLJ : L ≤ J)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (h60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60) :
    (∀ v ∈ V, ∃ l ∈ L, orderOf l = 3 ∧ l * v = v * l) ∧
      ∀ y ∈ J ⊓ Subgroup.normalizer (L : Set G), orderOf y = 3 →
        y ∈ L ⊔ (J ⊓ Subgroup.centralizer (V : Set G)) := by
  have hbij : Function.Bijective π := ⟨hinj, hR.1⟩
  have hLF : autOn L V ≤ F := (A4.autOn_mono hLJ).trans hJF
  have hQF : autOn (R ⊓ J) V ≤ F := (A4.autOn_mono inf_le_right).trans hJF
  have hA : ((autOn J V).subgroupOf F).comap π = alternatingGroup (Fin 7) :=
    comap_eq_alternatingGroup hbij (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJF).toEquiv]
      exact hX)
  have hleA : ∀ X : Subgroup G, X ≤ J →
      ((autOn X V).subgroupOf F).comap π ≤ alternatingGroup (Fin 7) := by
    intro X hXJ x hx
    rw [← hA]
    exact Subgroup.mem_subgroupOf.2 (A4.autOn_mono hXJ (Subgroup.mem_subgroupOf.1 hx))
  set K := ((autOn L V).subgroupOf F).comap π with hK
  have hKc : Nat.card ↥K = Nat.card ↥(autOn L V) := by
    rw [hK, card_comap_of_bijective hbij]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLF).toEquiv
  obtain ⟨k, hk⟩ := card_autOn_eq (hLJ.trans hJN) hperf hsimple hLV
  rw [h60] at hk
  have hdvd : Nat.card ↥(autOn L V) ∣ 2520 := hX ▸ Subgroup.card_dvd_of_le (A4.autOn_mono hLJ)
  have hk1 : k ≤ 1 := le_one_of_dvd (hk ▸ hdvd)
  have hK60 : 60 ∣ Nat.card ↥K := by rw [hKc, hk]; exact Dvd.intro _ rfl
  have hK7 : ¬ 7 ∣ Nat.card ↥K := by
    rw [hKc, hk]
    interval_cases k <;> norm_num
  have hK9 : ¬ 9 ∣ Nat.card ↥K := by
    rw [hKc, hk]
    interval_cases k <;> norm_num
  have hperfK := perfect_comap hbij hLF (hLJ.trans hJN) hperf
  set P := ((autOn (R ⊓ J) V).subgroupOf F).comap π with hP
  have hPc : Nat.card ↥P = 8 := by
    rw [hP, card_comap_of_bijective hbij,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQF).toEquiv]
    exact card_autOn_sylow hJN hSJ hX
  have hPN : P ≤ Subgroup.normalizer (K : Set (Equiv.Perm (Fin 7))) := by
    intro p hp
    have hp' : ((π p : ↥F) : MulAut ↥V) ∈ autOn (R ⊓ J) V := Subgroup.mem_subgroupOf.1 hp
    obtain ⟨g, hg, hgp⟩ := Setup.mem_autOn_iff.1 hp'
    exact mem_normalizer_comap (hRL hg.1) hgp.symm
  obtain ⟨a, b, hab, hfix⟩ := fix_pair_of_perfect (hleA L hLJ) hperfK hK60 hK7 hK9
    (hleA _ inf_le_right) hPc hPN
  have hmem := mem_iff_of_fix (hleA L hLJ) hK60 hab hfix
  have hsurj := hR.1
  obtain ⟨-, -, -, -, -, -, -, β, -, hβk, hβe⟩ := hR
  refine ⟨fun v hv => ?_, fun y hy hy3 => ?_⟩
  ·
    obtain ⟨w, hw⟩ : ∃ w : ↥V, (w : G) = v := ⟨⟨v, hv⟩, rfl⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
    obtain ⟨mv, hmv⟩ : ∃ mv : G6.PermMod 7, (m : (FFModel.symDn 7).Amb) = mv := ⟨_, rfl⟩
    obtain ⟨c, hc3, hca, hcb, hcx⟩ := exists_threeCycle_fix hab (Multiplicative.toAdd mv)
    have hcK : c ∈ K := (hmem c).2 ⟨hc3.mem_alternatingGroup, hca, hcb⟩
    have hact : G6.permAct 7 c mv = mv := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [G6.permAct_apply]
      exact hcx i
    have hmem' : (FFModel.symDn 7).act c (m : (FFModel.symDn 7).Amb) ∈ (FFModel.symDn 7).sec := by
      show G6.permAct 7 c (m : (FFModel.symDn 7).Amb) ∈ G6.coreMod 7
      rw [hmv, hact, ← hmv]
      exact m.2
    have h1 : β ⟨((π c : ↥F) : MulAut ↥V) w, trivial⟩ = QuotientGroup.mk
        ⟨(FFModel.symDn 7).act c (m : (FFModel.symDn 7).Amb), hmem'⟩ :=
      hβe c ⟨w, trivial⟩ m trivial hmem' hm.symm
    have h2 : β ⟨((π c : ↥F) : MulAut ↥V) w, trivial⟩ = β ⟨w, trivial⟩ := by
      rw [h1, ← hm]
      congr 1
      apply Subtype.ext
      show G6.permAct 7 c (m : (FFModel.symDn 7).Amb) = (m : (FFModel.symDn 7).Amb)
      rw [hmv, hact]
    have hfw : ((π c : ↥F) : MulAut ↥V) w = w := by
      have h3 : β (⟨((π c : ↥F) : MulAut ↥V) w, trivial⟩ * (⟨w, trivial⟩ : ↥(⊤ : Subgroup ↥V))⁻¹)
          = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      have h4 := (hβk _).1 h3
      rw [Subgroup.mem_bot] at h4
      have h5 : ((π c : ↥F) : MulAut ↥V) w * w⁻¹ = 1 := h4
      exact mul_inv_eq_one.1 h5
    obtain ⟨l, hlL, hl⟩ := Setup.mem_autOn_iff.1 (Subgroup.mem_subgroupOf.1 hcK)
    have hcomm : (l : G) * v = v * l := by
      have h6 : conjAct V l w = w := by rw [hl]; exact hfw
      have h7 := congrArg Subtype.val h6
      rw [InternalSec.coe_conjAct_apply, hw] at h7
      calc (l : G) * v = (l : G) * v * (l : G)⁻¹ * l := by group
        _ = v * l := by rw [h7]
    have hord : orderOf (conjAct V l) = 3 := by
      rw [hl, Subgroup.orderOf_coe, orderOf_injective π hinj c, hc3.orderOf]
    have h3 : 3 ∣ orderOf (l : G) := by
      rw [Subgroup.orderOf_coe, ← hord]
      exact orderOf_map_dvd _ _
    refine ⟨(l : G) ^ (orderOf (l : G) / 3), L.pow_mem hlL _,
      orderOf_pow_orderOf_div (orderOf_pos _).ne' h3, ?_⟩
    exact ((Commute.pow_left hcomm _ : Commute _ v)).eq
  ·
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hJN hy.1
    have hyJ : conjAct V ⟨y, hyN⟩ ∈ autOn J V := InternalSec.conjAct_mem_autOn hJN hy.1
    obtain ⟨γ, hγ⟩ : ∃ γ : Equiv.Perm (Fin 7), π γ = ⟨conjAct V ⟨y, hyN⟩, hJF hyJ⟩ := hsurj _
    have hγv : ((π γ : ↥F) : MulAut ↥V) = conjAct V ⟨y, hyN⟩ := congrArg Subtype.val hγ
    have hγA : γ ∈ alternatingGroup (Fin 7) := by
      rw [← hA]
      show π γ ∈ (autOn J V).subgroupOf F
      rw [Subgroup.mem_subgroupOf, hγv]
      exact hyJ
    have hγ3 : γ ^ 3 = 1 := by
      apply hinj
      have hp : π (γ ^ 3) = (π γ) ^ 3 := map_pow π γ 3
      rw [hp, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, hγv, ← map_pow]
      have : (⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) ^ 3 = 1 := by
        apply Subtype.ext
        have := pow_orderOf_eq_one y
        rw [hy3] at this
        simpa using this
      rw [this, map_one, Subgroup.coe_one]
    have hγK := mem_of_normalizes (hleA L hLJ) hK60 hab hfix hγA hγ3
      (mem_normalizer_comap hy.2 hγv)
    have hyL : conjAct V ⟨y, hyN⟩ ∈ autOn L V := by
      rw [← hγv]
      exact Subgroup.mem_subgroupOf.1 hγK
    obtain ⟨l, hlL, hl⟩ := Setup.mem_autOn_iff.1 hyL
    have hc : ((l⁻¹ * ⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) : G) ∈
        Subgroup.centralizer (V : Set G) := by
      apply mem_centralizer_of_conjAct_eq_one
      rw [map_mul, map_inv, hl, inv_mul_cancel]
    have hlJ : (l : G) ∈ J := hLJ hlL
    have e : y = (l : G) * ((l⁻¹ * ⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) : G) := by
      simp
    rw [e]
    refine Subgroup.mul_mem_sup hlL ⟨?_, hc⟩
    simpa using J.mul_mem (J.inv_mem hlJ) hy.1

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
