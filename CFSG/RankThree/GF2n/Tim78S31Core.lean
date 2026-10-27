module

public import CFSG.RankThree.GF2n.Tim78P214
public import CFSG.RankThree.GF2n.Tim78S3Pair

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_of_orderOf_eq_four {α β : G} (hα : α * α = 1) (hβ : β * β = 1)
    (h4 : (α * β) ^ 4 = 1) : β * (α * β * α⁻¹) = (α * β * α⁻¹) * β := by
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
  have hz : (α * β * α * β) * (α * β * α * β) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hz' : α * β * α * β = β * α * β * α := by
    have := eq_inv_of_mul_eq_one_left hz
    rw [this]
    simp only [mul_inv_rev, hαi, hβi, mul_assoc]
  rw [hαi]
  calc β * (α * β * α) = β * α * β * α := by group
    _ = α * β * α * β := hz'.symm
    _ = α * β * α * β := rfl

omit [Finite G] in
theorem iSup_comm_pGroup {ι : Type*} (S : ι → Subgroup G) (hS : ∀ i, IsPGroup 2 (S i))
    (hc : ∀ i j, ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a) :
    (∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, x * y = y * x) ∧ IsPGroup 2 ↥(⨆ i, S i) := by
  have h1 : ∀ i, (⨆ j, S j) ≤ Subgroup.centralizer (S i : Set G) := fun i =>
    iSup_le fun j y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc i j x hx y hy
  have h2 : (⨆ j, S j) ≤ Subgroup.centralizer ((⨆ j, S j : Subgroup G) : Set G) :=
    iSup_le fun i x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (h1 i hy) x hx).symm
  have hab : ∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (h2 hy) x hx
  refine ⟨hab, ?_⟩
  let E : Subgroup G :=
    { carrier := {z | z ∈ ⨆ i, S i ∧ ∃ k : ℕ, z ^ 2 ^ k = 1}
      one_mem' := ⟨Subgroup.one_mem _, 0, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        obtain ⟨k, hk⟩ := ha.2
        obtain ⟨l, hl⟩ := hb.2
        refine ⟨k + l, ?_⟩
        rw [Commute.mul_pow (hab a ha.1 b hb.1), pow_add, pow_mul, hk, one_pow, one_mul,
          mul_comm (2 ^ k), pow_mul, hl, one_pow]⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
        obtain ⟨k, hk⟩ := ha.2
        exact ⟨k, by rw [inv_pow, hk, inv_one]⟩⟩ }
  have hE : (⨆ i, S i) ≤ E := iSup_le fun i z hz => ⟨Subgroup.mem_iSup_of_mem i hz, by
    obtain ⟨k, hk⟩ := hS i ⟨z, hz⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩⟩
  intro z
  obtain ⟨k, hk⟩ := (hE z.2).2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

structure Core31 (U : Subgroup G) (g : G) : Prop where
  comm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x
  two : IsPGroup 2 U
  ti : IsTI U
  exp : ∀ x ∈ U, x ^ 4 = 1
  exp_ne : ∃ x ∈ U, x ^ 2 ≠ 1
  card4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub U)
  ord : ∀ α ∈ PartTwo.omegaOneSub (conjSubgroup g U), α ≠ 1 →
    ∀ β ∈ PartTwo.omegaOneSub U, β ≠ 1 → orderOf (α * β) = 4

namespace Core31

variable {U : Subgroup G} {g : G} (K : Core31 U g)
include K

omit [Finite G] in
theorem sq_omega {h a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup h U)) : a * a = 1 :=
  ((mem_omegaOneSub_iff (Tim78.comm_conj K.comm h)).mp ha).2

omit [Finite G] in
theorem omega_conj (h : G) :
    PartTwo.omegaOneSub (conjSubgroup h U) = conjSubgroup h (PartTwo.omegaOneSub U) :=
  omegaOneSub_conj K.comm h

omit [Finite G] in
theorem setup (h : G) (hne : U ⊓ Subgroup.normalizer (conjSubgroup h U : Set G) ≠ ⊥) :
    Setup210 U (conjSubgroup h U) :=
  { comm := K.comm
    two := K.two
    exp_ne := K.exp_ne
    ti := K.ti
    conj := ⟨h, rfl⟩
    ne_bot := hne }

omit [Finite G] in
theorem card_omega_conj (h : G) :
    Nat.card ↥(PartTwo.omegaOneSub (conjSubgroup h U)) =
      Nat.card ↥(PartTwo.omegaOneSub U) := by
  rw [K.omega_conj h, card_conjSubgroup]

omit [Finite G] in
theorem exists_ne_one_omega (h : G) : ∃ a ∈ PartTwo.omegaOneSub (conjSubgroup h U), a ≠ 1 := by
  have hne : PartTwo.omegaOneSub (conjSubgroup h U) ≠ ⊥ := by
    intro hbot
    have := K.card_omega_conj h
    rw [hbot, Subgroup.card_bot] at this
    have := K.card4
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨a, ha, fun h' => ha1 (Subtype.ext h')⟩

theorem ne_bot_nrm {α : G} (hα : α ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (hα1 : α ≠ 1) :
    U ⊓ Subgroup.normalizer (conjSubgroup α U : Set G) ≠ ⊥ := by
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have h4 := K.ord α hα hα1 β hβ hβ1
  have hc := comm_of_orderOf_eq_four (K.sq_omega hα) (K.sq_omega (h := 1)
    (by rw [conjSubgroup_one]; exact hβ)) (by rw [← h4]; exact pow_orderOf_eq_one _)
  intro hbot
  have hβU := PartTwo.omegaOneSub_le U hβ
  have hmem : α * β * α⁻¹ ∈ conjSubgroup α U := by
    rw [mem_conjSubgroup, show α⁻¹ * (α * β * α⁻¹) * α = β by group]
    exact hβU
  have hne : α * β * α⁻¹ ≠ 1 := fun h' => hβ1 (by
    calc β = α⁻¹ * (α * β * α⁻¹) * α := by group
      _ = 1 := by rw [h']; group)
  have hN := Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup K.ti α) hmem hne hc
  have : β ∈ U ⊓ Subgroup.normalizer (conjSubgroup α U : Set G) := Subgroup.mem_inf.mpr ⟨hβU, hN⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hβ1 this

theorem exists_noncomm (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∃ α ∈ PartTwo.omegaOneSub (conjSubgroup g U),
      ¬ ∀ a ∈ U, ∀ b ∈ conjSubgroup α U, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  set A₀ := PartTwo.omegaOneSub (conjSubgroup g U) with hA₀
  have hA₀c : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x := fun x hx y hy =>
    Tim78.comm_conj K.comm g x (PartTwo.omegaOneSub_le _ hx) y (PartTwo.omegaOneSub_le _ hy)
  have hpair : ∀ i j : ↥A₀, ∀ a ∈ conjSubgroup (i : G) U, ∀ b ∈ conjSubgroup (j : G) U,
      a * b = b * a := by
    intro i j a ha b hb
    have hij : (i : G)⁻¹ * j ∈ A₀ := A₀.mul_mem (A₀.inv_mem i.2) j.2
    have h := hcon _ hij ((i : G)⁻¹ * a * i) (mem_conjSubgroup.mp ha) ((i : G)⁻¹ * b * i) (by
      rw [mem_conjSubgroup, show ((i : G)⁻¹ * j)⁻¹ * ((i : G)⁻¹ * b * i) * ((i : G)⁻¹ * j) =
        (j : G)⁻¹ * b * j by group]
      exact mem_conjSubgroup.mp hb)
    calc a * b = (i : G) * (((i : G)⁻¹ * a * i) * ((i : G)⁻¹ * b * i)) * (i : G)⁻¹ := by group
      _ = (i : G) * (((i : G)⁻¹ * b * i) * ((i : G)⁻¹ * a * i)) * (i : G)⁻¹ := by rw [h]
      _ = b * a := by group
  obtain ⟨hWc, hW2⟩ := iSup_comm_pGroup (fun i : ↥A₀ => conjSubgroup (i : G) U)
    (fun i => K.two.map (MulAut.conj (i : G)).toMonoidHom) hpair
  set W := ⨆ i : ↥A₀, conjSubgroup (i : G) U with hW
  have hA₀W : A₀ ≤ Subgroup.normalizer (W : Set G) := by
    intro a ha
    rw [← conjSubgroup_eq_self_iff]
    have hle : ∀ b ∈ A₀, conjSubgroup b W ≤ W := by
      intro b hb
      rw [conjSubgroup, Subgroup.map_le_iff_le_comap]
      refine iSup_le fun i => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      show conjSubgroup b (conjSubgroup (i : G) U) ≤ W
      rw [← conjSubgroup_mul]
      exact le_iSup (fun i : ↥A₀ => conjSubgroup (i : G) U) ⟨b * i, A₀.mul_mem hb i.2⟩
    refine le_antisymm (hle a ha) ?_
    have h' := hle a⁻¹ (A₀.inv_mem ha)
    intro w hw
    have : a⁻¹ * w * a ∈ W := h' (by
      rw [mem_conjSubgroup, inv_inv, show a * (a⁻¹ * w * a) * a⁻¹ = w by group]
      exact hw)
    rw [mem_conjSubgroup]
    exact this
  have hS : IsPGroup 2 ↥(A₀ ⊔ W) := IsPGroup.to_sup_of_normal_right'
    (K.two.map (MulAut.conj g).toMonoidHom |>.to_le (PartTwo.omegaOneSub_le _)) hW2 hA₀W
  have hUS : U ≤ A₀ ⊔ W := by
    intro u hu
    refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem ⟨1, A₀.one_mem⟩ ?_)
    rw [conjSubgroup_one]
    exact hu
  have h4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub (conjSubgroup g U) ⊓ (A₀ ⊔ W)) := by
    rw [inf_of_le_left le_sup_left, K.card_omega_conj g]
    exact K.card4
  have hcomm := tim78_2_14_b hCen hU K.comm K.two K.ti (fun h => by
    obtain ⟨x, hx, hx2⟩ := K.exp_ne
    have hx' : x ∈ PartTwo.omegaOneSub U := by rw [h]; exact hx
    exact hx2 (by rw [sq]; exact ((mem_omegaOneSub_iff K.comm).mp hx').2)) hS hUS g h4
  obtain ⟨α, hα, hα1⟩ := K.exists_ne_one_omega g
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have hab := hcomm β hβ α hα
  have h4' := K.ord α hα hα1 β hβ hβ1
  have hsq : (α * β) ^ 2 = 1 := by
    have e : (α * β) ^ 2 = (α * α) * (β * β) := by
      rw [sq, show α * β * (α * β) = α * (β * α) * β by group, hab]
      group
    rw [e, K.sq_omega hα, K.sq_omega (h := 1) (by rw [conjSubgroup_one]; exact hβ), one_mul]
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [h4'] at this
  exact absurd this (by norm_num)

theorem ncpair {α : G} (hα : α ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (hα1 : α ≠ 1)
    (hnc : ¬ ∀ a ∈ U, ∀ b ∈ conjSubgroup α U, a * b = b * a) : NCPair U (conjSubgroup α U) :=
  ⟨K.setup α (K.ne_bot_nrm hα hα1), K.exp, hnc⟩

end Core31

end CFSG.RankThree.GF2n.Tim78
