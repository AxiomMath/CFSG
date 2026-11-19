
module

public import CFSG.Sporadic.Schreier.J4SThreeDataBase
public import CFSG.Sporadic.Schreier.J4SOuterBase
public import CFSG.Sporadic.Schreier.J4SInvolutionBase
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFiveBase
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCentBase
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.ComponentInitial CFSG.GroupActions MulAction

def q3gen (i : ℕ) : J := signedWord x y q3Words[i]! ^ q3Exps[i]!

def Q3 : Subgroup J := Subgroup.closure (Set.range fun i : Fin 2 => q3gen i)

theorem q3gen_mem_K (i : ℕ) : q3gen i ∈ K := K.pow_mem (signedWord_mem_K _) _

theorem q3gen_mem (i : Fin 2) : q3gen i ∈ Q3 := Subgroup.subset_closure ⟨i, rfl⟩

theorem Q3_le_K : Q3 ≤ K := by
  rw [Q3, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact q3gen_mem_K i

section Generic

variable {G : Type*} [Group G]

theorem card_centralizer_inf_conj {N : Subgroup G} {g : G} (h1 : ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, g⁻¹ * n * g ∈ N) (q : G) :
    Nat.card (Subgroup.centralizer {g * q * g⁻¹} ⊓ N : Subgroup G) =
      Nat.card (Subgroup.centralizer {q} ⊓ N : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun n => ⟨g⁻¹ * n * g, Subgroup.mem_inf.2 ⟨?_, h2 _ (Subgroup.mem_inf.1 n.2).2⟩⟩
      invFun := fun n => ⟨g * n * g⁻¹, Subgroup.mem_inf.2 ⟨?_, h1 _ (Subgroup.mem_inf.1 n.2).2⟩⟩
      left_inv := fun n => Subtype.ext (by dsimp only; group)
      right_inv := fun n => Subtype.ext (by dsimp only; group) }
  · have hc : (n : G) * (g * q * g⁻¹) = g * q * g⁻¹ * n :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 n.2).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * n * g * q = g⁻¹ * (n * (g * q * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * q * g⁻¹ * n) * g := by rw [hc]
      _ = q * (g⁻¹ * n * g) := by group
  · have hc : (n : G) * q = q * n :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 n.2).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * n * g⁻¹ * (g * q * g⁻¹) = g * (n * q) * g⁻¹ := by group
      _ = g * (q * n) * g⁻¹ := by rw [hc]
      _ = g * q * g⁻¹ * (g * n * g⁻¹) := by group

theorem card_centralizer_le_of_sylow [Finite G] {H Q N : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p)
    (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {b : ℕ}
    (hb : ∀ q ∈ Q, q ≠ 1 → Nat.card (Subgroup.centralizer {q} ⊓ N : Subgroup G) ≤ b)
    {h : G} (hh : h ∈ H) (ho : orderOf h = p) :
    Nat.card (Subgroup.centralizer {h} ⊓ N : Subgroup G) ≤ b := by
  have hQ' : Nat.card (Q.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [← hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  let P : Sylow p H := Sylow.ofCard (Q.subgroupOf H) hQ'
  have hP : IsPGroup p (Subgroup.zpowers (⟨h, hh⟩ : H)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ho, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow P hP
  rw [Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hg
  set q := (g : G) * h * (g : G)⁻¹ with hqdef
  have hq : q ∈ Q := hg
  have hq1 : q ≠ 1 := by
    intro h1
    have : h = 1 := by
      have e : h = (g : G)⁻¹ * q * g := by rw [hqdef]; group
      rw [e, h1]; group
    rw [this, orderOf_one] at ho
    exact hp.out.one_lt.ne ho
  have e : h = (g : G)⁻¹ * q * (g : G)⁻¹⁻¹ := by rw [hqdef]; group
  rw [e, card_centralizer_inf_conj (fun n hn => hnorm _ (H.inv_mem g.2) n hn)
    (fun n hn => by rw [inv_inv]; exact hnorm _ g.2 n hn)]
  exact hb q hq hq1

end Generic

section Kernel

variable {G : Type*} [Group G] [Finite G] {X : Type*} [MulAction G X] [Finite X]
  [IsPretransitive G X] {H N : Subgroup G} {r : X}

theorem pointwise_kernel_no_three (hstab : stabilizer G r = H) (hcoatom : IsCoatom H)
    (hNH : N ≤ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hcardN : Nat.card N = 2048)
    (hcardH : Nat.card H = 501397585920)
    (horb : ∃ x₀ : X, (orbit H x₀).ncard = 28336 ∧
      ∀ x : X, (orbit H x).ncard = 28336 → orbit H x = orbit H x₀)
    (h3 : ∀ h ∈ H, orderOf h = 3 → Nat.card (Subgroup.centralizer {h} ⊓ N : Subgroup G) ≤ 32)
    {α : MulAut G} (hα : α ∈ pointwiseFixingAut H) (hα3 : α ^ 3 = 1) : α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hα1
  obtain ⟨x₀, hx₀, hu⟩ := horb
  obtain ⟨g, h, hh, ho, hc, hcard⟩ := exists_centralizing_element hstab hcoatom hα hα1 hα3
    (fun x hx => hu x (hx.trans hx₀)) (by rw [hx₀]; norm_num) (by rw [hx₀]; norm_num)
  rw [hx₀, hcardH] at hcard
  have h1 := card_mul_card_dvd hNH (Dg_le g) hnorm
  rw [hcardN, hcardH, ← hcard] at h1
  have hpos : 0 < Nat.card (Dg H g) := Nat.card_pos
  have h2 : 2048 ∣ Nat.card (N ⊓ Dg H g : Subgroup G) * 28336 := by
    refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
    rw [show Nat.card (Dg H g) * (Nat.card (N ⊓ Dg H g : Subgroup G) * 28336) =
      Nat.card (N ⊓ Dg H g : Subgroup G) * (Nat.card (Dg H g) * 28336) by ring,
      mul_comm (Nat.card (Dg H g)) 2048]
    exact h1
  have h3' : Nat.card (N ⊓ Dg H g : Subgroup G) ∣ 2048 := by
    rw [← hcardN]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : (N ⊓ Dg H g : Subgroup G) ≤ Subgroup.centralizer {h} ⊓ N := by
    intro m hm
    rw [Subgroup.mem_inf] at hm
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hc m hm.2).eq.symm, hm.1⟩
  have hcm := (Subgroup.card_le_of_le hle).trans (h3 h hh ho)
  revert h2 h3'
  generalize Nat.card (N ⊓ Dg H g : Subgroup G) = c at hcm ⊢
  interval_cases c <;> decide

end Kernel

section Core

variable {G : Type*} [Group G] [Finite G]

theorem isPGroup_pointwise_of_core {N H : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hNH : N ≤ H) (hN : Subgroup.normalizer (N : Set G) = H)
    (hC : Subgroup.centralizer (N : Set G) ⊓ H ≤ N) (hNp : IsPGroup p N)
    (hH : IsPGroup p (pointwiseFixingAut H)) : IsPGroup p (pointwiseFixingAut N) := by
  classical
  have : Finite (MulAut G) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut G))
  have hstab : ∀ α ∈ pointwiseFixingAut N, α ∈ subgroupStabAut H := by
    intro α hα
    have hαN : N.map α.toMonoidHom = N := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hα y hy]
        exact hy
      · intro hx
        exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, hα x hx]⟩
    change H.map α.toMonoidHom = H
    rw [← hN, Subgroup.map_equiv_normalizer_eq, hαN]
  let ι : pointwiseFixingAut N →* subgroupStabAut H :=
    { toFun := fun α => ⟨α, hstab α α.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ρ : pointwiseFixingAut N →* MulAut H := (subgroupStabRestrict H).comp ι
  set V := N.subgroupOf H with hV
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 (hN ▸ le_rfl)
  have hVc : Subgroup.centralizer (V : Set H) ≤ V := by
    intro x hx
    have hxG : (x : G) ∈ Subgroup.centralizer (N : Set G) ⊓ H := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun v hv => ?_, x.2⟩
      have := Subgroup.mem_centralizer_iff.1 hx ⟨v, hNH hv⟩ hv
      exact congrArg Subtype.val this
    exact hC hxG
  have hVp : IsPGroup p V := hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hT := (Tits_self_centralizing_core_automorphism_kernel hVc p hVp).2.2.1
  have hrange : ρ.range ≤ pointwiseFixingAut V := by
    rintro _ ⟨α, rfl⟩
    intro v hv
    apply Subtype.ext
    show (α : MulAut G) (v : G) = v
    exact α.2 v (Subgroup.mem_subgroupOf.1 hv)
  have hker : IsPGroup p ρ.ker := by
    have hle : ρ.ker.map (pointwiseFixingAut N).subtype ≤ pointwiseFixingAut H := by
      rintro _ ⟨α, hα, rfl⟩
      intro h hh
      have := congrArg (fun φ : MulAut H => ((φ ⟨h, hh⟩ : H) : G)) ((MonoidHom.mem_ker).1 hα)
      exact this
    exact (hH.to_le hle).of_equiv (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).symm
  have hran : IsPGroup p ρ.range := (hT.to_le hrange)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hker
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hran
  refine IsPGroup.of_card (n := a + b) ?_
  rw [← card_ker_mul_card_range ρ, ha, hb, pow_add]

end Core

end CFSG.Sporadic.J4Schreier
