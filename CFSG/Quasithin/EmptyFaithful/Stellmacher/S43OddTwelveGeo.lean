module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveSec
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCore4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Twelve

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

structure Data (α α' ν β l : Geo H M) : Prop where
  crit : IsCritPair₁ α α'
  hν : ν ∈ nbrs α'
  dν : dist α ν + 1 = bMin H M
  hβ : β ∈ nbrs α
  dβ : dist β ν + 2 = bMin H M
  hl : l ∈ nbrs α'
  lν : l ≠ ν

variable {α' ν β l : Geo H M}

omit [Finite G] in
theorem comm_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem Data.vtypes (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (d : Data α α' ν β l) : vtype α' = true ∧ vtype l = false ∧ vtype ν = false :=
  ⟨Core.vtype_crit hA hs ho d.crit, Core.vtype_nu hA hs ho d.crit d.hl,
    Core.vtype_nu hA hs ho d.crit d.hν⟩

theorem Data.dist_beta (hA : F53Amalgam H M S) (d : Data α α' ν β l) :
    dist β α' + 1 = bMin H M :=
  Core.dist_beta_crit hA d.crit d.hν d.hβ d.dβ

omit [Finite G] in
theorem Data.exists_z (d : Data α α' ν β l) : ∃ z ∈ Zv α, z ∉ Qv α' := by
  by_contra hcon
  push Not at hcon
  exact d.crit.1 fun x hx => hcon x hx

theorem Data.smul_ne (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) {z : G} (hz : z ∈ Zv α) (hzQ : z ∉ Qv α') :
    ∃ hz' : z ∈ stab α', (⟨z, stab_le α' hz'⟩ : ↥(H ⊔ M)) • l ≠ l := by
  obtain ⟨l₁, l₂, h29⟩ := Core.exists_sit29_nu hA h26 hs ho d.crit d.hν
  obtain ⟨hz', h1, h2⟩ := Core.smul_swap_of_crit hA hs h29 d.dν hz hzQ
  refine ⟨Core.Zv_le_stab_crit hA hs d.crit hz, ?_⟩
  rcases h29.nbrs_eq l d.hl with h | h | h
  · exact absurd h d.lν
  · subst h
    rw [h1]
    exact h29.ne₂₃.symm
  · subst h
    rw [h2]
    exact h29.ne₂₃

theorem Data.le_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) {U : Subgroup G} (hU : U ≤ Zv l) {z : G}
    (hz : z ∈ Zv α) (hzQ : z ∉ Qv α') (hzU : ∀ x ∈ U, z * x = x * z) : U ≤ Yv α' := by
  obtain ⟨hz', hmov⟩ := d.smul_ne hA h26 hs ho hz hzQ
  exact hs.le_Yv_of_normalizes hA h26 (d.vtypes hA hs ho).1 d.hl hU hz' hmov
    (conjSub_eq_of_commute hzU)

theorem Data.Zv_inf_Qv_le_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) : Zv l ⊓ Qv α ≤ Yv α' := by
  obtain ⟨z, hz, hzQ⟩ := d.exists_z
  refine d.le_Yv hA h26 hs ho inf_le_left hz hzQ fun x hx => ?_
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 x hx.2).symm

theorem Data.Yv_le_Zv_inf_Qv (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (d : Data α α' ν β l) : Yv α' ≤ Zv l ⊓ Qv α :=
  le_inf (Yv_le_Zv d.hl) (Core.Yv_le_Qv hA hs ho d.crit d.hν d.dν)

theorem Data.Yv_le_Qv_beta (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (d : Data α α' ν β l) : Yv α' ≤ Qv β :=
  (Yv_le_Zv d.hν).trans (Core.Zv_nu_le_Qv_beta hA hs ho d.crit d.hν d.dβ)

theorem Data.inf_inf_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) : Zv l ⊓ Qv β ⊓ Qv α = Yv α' := by
  apply le_antisymm
  · exact le_trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (d.Zv_inf_Qv_le_Yv hA h26 hs ho)
  · have h1 := d.Yv_le_Zv_inf_Qv hA hs ho
    exact le_inf (le_inf (h1.trans inf_le_left) (d.Yv_le_Qv_beta hA hs ho)) (h1.trans inf_le_right)

theorem Data.Qv_beta_le (hA : F53Amalgam H M S) (d : Data α α' ν β l) : Qv β ≤ stab α :=
  Qv_le_stab_of_mem_nbrs hA (nbrs_symm d.hβ)

theorem Data.card_le_eight (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l) :
    Nat.card (Zv l ⊓ Qv β : Subgroup G) ≤ 8 := by
  have h4a := crit4a hA h26 hs ho hb d.crit d.hν d.dν d.hβ d.dβ d.hl d.lν
  have h16 : Nat.card (Zv l) = 16 := hs.card_Zv_false (d.vtypes hA hs ho).2.1
  have hdvd : Nat.card (Zv l ⊓ Qv β : Subgroup G) ∣ 16 :=
    h16 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (Zv l ⊓ Qv β : Subgroup G) ≠ 16 := fun h =>
    h4a ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h16])).ge.trans inf_le_right)
  have h2 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h2] at hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k <;> simp_all

theorem Data.inv_mul_mem_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l) {u v : G}
    (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α) (hv : v ∈ Zv l ⊓ Qv β) (hvQ : v ∉ Qv α) :
    u⁻¹ * v ∈ Yv α' := by
  set K : Subgroup G := Zv l ⊓ Qv β with hK
  have hN : K ⊓ Qv α = Yv α' := d.inf_inf_eq hA h26 hs ho
  have h8 := d.card_le_eight hA h26 hs ho hb
  have h4 : Nat.card (Yv α') = 4 := hs.card_Yv hA h26 (d.vtypes hA hs ho).1
  have hYK : Yv α' ≤ K := hN ▸ inf_le_left
  have hmul := Subgroup.relIndex_mul_card (Yv α') K
  rw [inf_of_le_left hYK, h4] at hmul
  have hne : (Yv α').relIndex K ≠ 1 := fun h1 => by
    have := Subgroup.relIndex_eq_one.mp h1 hu
    rw [← hN] at this
    exact huQ this.2
  have h2 : (Yv α').relIndex K = 2 := by
    rw [← hK] at h8
    have hpos : 0 < (Yv α').relIndex K := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rcases Nat.lt_or_ge ((Yv α').relIndex K) 3 with h | h
    · interval_cases hk : (Yv α').relIndex K
      · exact absurd rfl hne
      · rfl
    · omega
  refine inv_mul_mem_of_relIndex_two h2 hu hv ?_ ?_
  · intro h; rw [← hN] at h; exact huQ h.2
  · intro h; rw [← hN] at h; exact hvQ h.2

theorem Data.exists_gamma (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hb : 4 ≤ bMin H M) (d : Data α α' ν β l) :
    ∃ γ ∈ nbrs β, vtype γ = false ∧ Zv l ≤ Qv γ := by
  obtain ⟨γ, hγ, hdγ⟩ := Core.exists_nbr_dist hA (x := ν) (y := β) (n := bMin H M - 3)
    (by rw [CosetGeom.dist_comm]; have := d.dβ; omega)
  have hγv : vtype γ = false := Sit43.vtype_false_of_adj (Core.vtype_beta hs d.hβ) hγ
  refine ⟨γ, hγ, hγv, ?_⟩
  have h1 := Core.dist_le_of_mem_nbrs hA (x := γ) (y := α') (z := l) d.hl
  have h2 := Core.dist_le_of_mem_nbrs hA (x := γ) (y := ν) (z := α') (nbrs_symm d.hν)
  rw [CosetGeom.dist_comm γ ν] at h2
  exact hs.Zv_le_Qv_of_dist_lt_false (d.vtypes hA hs ho).2.1
    (by rw [CosetGeom.dist_comm]; omega)

theorem Data.relIndex_le_two (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hb : 4 ≤ bMin H M) (d : Data α α' ν β l) :
    (Zv l ⊓ Qv β).relIndex (Zv l) ≤ 2 := by
  obtain ⟨γ, hγ, hγv, hle⟩ := d.exists_gamma hA hs ho hb
  have hβγ : β ∈ nbrs γ := nbrs_symm hγ
  have hE : Zv l ≤ stab γ ⊓ stab β :=
    le_inf (hle.trans (pCoreOf_le 2 _)) (hle.trans (Qv_le_stab_of_mem_nbrs hA hβγ))
  rw [inf_comm, Subgroup.inf_relIndex_right]
  calc (Qv β).relIndex (Zv l) ≤ (Qv β).relIndex (stab γ ⊓ stab β) :=
        Subgroup.relIndex_le_of_le_right hE Subgroup.index_ne_zero_of_finite
    _ = 2 := Sit43.relIndex_Qv_edge hA hγv hβγ

theorem Data.Zv_le_centralizer_Yv (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hb : 4 ≤ bMin H M) (d : Data α α' ν β l) :
    Zv l ≤ Subgroup.centralizer (Yv β : Set G) := by
  obtain ⟨γ, hγ, -, hle⟩ := d.exists_gamma hA hs ho hb
  exact (hle.trans (Qv_le_centralizer_Zv hA γ)).trans (Subgroup.centralizer_le (Yv_le_Zv hγ))

end Twelve

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
