module

public import CFSG.RankThree.GF2n.Tim78S31Core
public import CFSG.RankThree.GF2n.Tim78S3Swap

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup_of_swap {y : G} (hy2 : y * y = 1) (W : Subgroup G) :
    y ∈ Subgroup.normalizer ((W ⊔ conjSubgroup y W : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_self_iff, conjSubgroup, Subgroup.map_sup]
  change conjSubgroup y W ⊔ conjSubgroup y (conjSubgroup y W) = W ⊔ conjSubgroup y W
  rw [← conjSubgroup_mul, hy2, conjSubgroup_one, sup_comm]

namespace Core31

variable {U : Subgroup G} {g : G} (K : Core31 U g)
include K

omit [Finite G] in
theorem comm_conj' (h : G) : ∀ x ∈ conjSubgroup h U, ∀ y ∈ conjSubgroup h U, x * y = y * x :=
  Tim78.comm_conj K.comm h

omit [Finite G] in
theorem two_conj (h : G) : IsPGroup 2 (conjSubgroup h U) :=
  K.two.map (MulAut.conj h).toMonoidHom

omit [Finite G] in
theorem omega_ne_conj (h : G) : PartTwo.omegaOneSub (conjSubgroup h U) ≠ conjSubgroup h U := by
  intro he
  obtain ⟨u, hu, hu2⟩ := K.exp_ne
  have hmem : h * u * h⁻¹ ∈ conjSubgroup h U := by
    rw [mem_conjSubgroup, show h⁻¹ * (h * u * h⁻¹) * h = u by group]
    exact hu
  rw [← he] at hmem
  have := K.sq_omega hmem
  apply hu2
  rw [sq]
  calc u * u = h⁻¹ * ((h * u * h⁻¹) * (h * u * h⁻¹)) * h := by group
    _ = 1 := by rw [this]; group

omit [Finite G] in
theorem not_comm {α β : G} (hα : α ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (hα1 : α ≠ 1)
    (hβ : β ∈ PartTwo.omegaOneSub U) (hβ1 : β ≠ 1) : α * β ≠ β * α := by
  intro hab
  have h4 := K.ord α hα hα1 β hβ hβ1
  have hsq : (α * β) ^ 2 = 1 := by
    have e : (α * β) ^ 2 = (α * α) * (β * β) := by
      rw [sq, show α * β * (α * β) = α * (β * α) * β by group, ← hab]
      group
    rw [e, K.sq_omega hα, K.sq_omega (h := 1) (by rw [conjSubgroup_one]; exact hβ), one_mul]
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [h4] at this
  exact absurd this (by norm_num)

omit [Finite G] in
theorem ord' {α β : G} (hα : α ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (hα1 : α ≠ 1)
    (hβ : β ∈ PartTwo.omegaOneSub U) (hβ1 : β ≠ 1) : orderOf (β * α) = 4 := by
  rw [orderOf_mul_comm']
  exact K.ord α hα hα1 β hβ hβ1

theorem exists_data31 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∃ α ∈ PartTwo.omegaOneSub (conjSubgroup g U), α ≠ 1 ∧
      (¬ ∀ a ∈ U, ∀ b ∈ conjSubgroup α U, a * b = b * a) ∧
      ∃ x ∈ U ⊔ conjSubgroup α U, conjSubgroup α (conjSubgroup x U) = conjSubgroup x U := by
  obtain ⟨α, hα, hnc⟩ := K.exists_noncomm hCen hU
  have hα1 : α ≠ 1 := fun h => hnc (by
    rw [h, conjSubgroup_one]
    exact K.comm)
  have P := K.ncpair hα hα1 hnc
  have hαα := K.sq_omega hα
  have hX : α ∈ Subgroup.normalizer ((U ⊔ conjSubgroup α U : Subgroup G) : Set G) := by
    rw [← conjSubgroup_eq_self_iff, conjSubgroup, Subgroup.map_sup]
    change conjSubgroup α U ⊔ conjSubgroup α (conjSubgroup α U) = U ⊔ conjSubgroup α U
    rw [← conjSubgroup_mul, hαα, conjSubgroup_one, sup_comm]
  obtain ⟨x₀, hx₀, he⟩ := P.exists_conj hCen hU
  obtain ⟨x, hx, hxC⟩ := P.exists_fixed hCen hU hαα hX ⟨x₀, hx₀, he⟩
  exact ⟨α, hα, hα1, hnc, x, hx, hxC⟩

omit [Finite G] in
theorem exp_ne_conj (h : G) : ∃ y ∈ conjSubgroup h U, y ^ 2 ≠ 1 := by
  obtain ⟨u, hu, hu2⟩ := K.exp_ne
  refine ⟨h * u * h⁻¹, ?_, fun h' => hu2 ?_⟩
  · rw [mem_conjSubgroup, show h⁻¹ * (h * u * h⁻¹) * h = u by group]
    exact hu
  · rw [conj_pow] at h'
    calc u ^ 2 = h⁻¹ * (h * u ^ 2 * h⁻¹) * h := by group
      _ = 1 := by rw [h']; group

omit [Finite G] in
theorem exp_conj (h : G) : ∀ y ∈ conjSubgroup h U, y ^ 4 = 1 := by
  intro y hy
  have h4 := K.exp _ (mem_conjSubgroup.mp hy)
  rw [show (h⁻¹ * y * h) ^ 4 = h⁻¹ * y ^ 4 * h by
    simpa using conj_pow (a := h⁻¹) (b := y) (i := 4)] at h4
  calc y ^ 4 = h * (h⁻¹ * y ^ 4 * h) * h⁻¹ := by group
    _ = 1 := by rw [h4]; group

end Core31

omit [Finite G] in
theorem le_normalizer_iSup {N A : Subgroup G} :
    N ≤ Subgroup.normalizer ((⨆ i : ↥N, conjSubgroup (i : G) A : Subgroup G) : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff]
  have hle : ∀ b ∈ N, conjSubgroup b (⨆ i : ↥N, conjSubgroup (i : G) A) ≤
      ⨆ i : ↥N, conjSubgroup (i : G) A := by
    intro b hb
    rw [conjSubgroup, Subgroup.map_le_iff_le_comap]
    refine iSup_le fun i => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    show conjSubgroup b (conjSubgroup (i : G) A) ≤ _
    rw [← conjSubgroup_mul]
    exact le_iSup (fun i : ↥N => conjSubgroup (i : G) A) ⟨b * i, N.mul_mem hb i.2⟩
  refine le_antisymm (hle m hm) ?_
  have h' := hle m⁻¹ (N.inv_mem hm)
  intro w hw
  have : m⁻¹ * w * m ∈ ⨆ i : ↥N, conjSubgroup (i : G) A := h' (by
    rw [mem_conjSubgroup, inv_inv, show m * (m⁻¹ * w * m) * m⁻¹ = w by group]
    exact hw)
  rw [mem_conjSubgroup]
  exact this

structure Data31 (U : Subgroup G) (g α x : G) : Prop where
  core : Core31 U g
  mem : α ∈ PartTwo.omegaOneSub (conjSubgroup g U)
  ne_one : α ≠ 1
  ncomm : ¬ ∀ a ∈ U, ∀ b ∈ conjSubgroup α U, a * b = b * a
  memX : x ∈ U ⊔ conjSubgroup α U
  fix : conjSubgroup α (conjSubgroup x U) = conjSubgroup x U

namespace Data31

variable {U : Subgroup G} {g α x : G} (D : Data31 U g α x)
include D

theorem pair : NCPair U (conjSubgroup α U) := D.core.ncpair D.mem D.ne_one D.ncomm

omit [Finite G] in
theorem sq_α : α * α = 1 := D.core.sq_omega D.mem

variable (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
include hCen hU

theorem cent_α {n : G}
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U))
    (hc : α * n = n * α) : n ∈ PartTwo.omegaOneSub (conjSubgroup x U) :=
  D.pair.mem_omega_of_swap hCen hU D.sq_α D.ne_one rfl D.mem D.memX D.fix hn hc

theorem comm_N_α {n : G}
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)) :
    α * n * α⁻¹ * n⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) :=
  D.pair.commutator_mem_omega_of_swap hCen hU D.sq_α D.ne_one rfl D.mem D.memX D.fix hn

theorem comm_α_β {β : G} (hβ : β ∈ PartTwo.omegaOneSub U) :
    α * β * α⁻¹ * β⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) :=
  D.comm_N_α hCen hU (Subgroup.mem_sup_left hβ)

theorem not_comm_CA :
    ¬ ∀ c ∈ conjSubgroup x U, ∀ a ∈ conjSubgroup g U, c * a = a * c := by
  intro hCA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have K := D.core
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U) with hN
  set A := conjSubgroup g U with hA
  have hAc := K.comm_conj' g
  have hαA : α ∈ A := PartTwo.omegaOneSub_le _ D.mem
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right D.sq_α
  have hATI : IsTI A := isTI_conjSubgroup K.ti g
  have hAn : ∀ n ∈ N, ∀ b ∈ conjSubgroup n A, ∀ a ∈ A, b * a = a * b := by
    intro n hn
    have hc := D.comm_N_α hCen hU hn
    have hnα : n * α * n⁻¹ = α * (α * n * α⁻¹ * n⁻¹) := by
      calc n * α * n⁻¹ = (α * α) * n * α * n⁻¹ := by rw [D.sq_α, one_mul]
        _ = α * (α * n * α⁻¹ * n⁻¹) := by rw [hαi]; group
    have hmem : n * α * n⁻¹ ∈ conjSubgroup n A := by
      rw [mem_conjSubgroup, show n⁻¹ * (n * α * n⁻¹) * n = α by group]
      exact hαA
    have hne : n * α * n⁻¹ ≠ 1 := fun h => D.ne_one (by
      calc α = n⁻¹ * (n * α * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
    have hcomm : ∀ a ∈ A, a * (n * α * n⁻¹) = (n * α * n⁻¹) * a := by
      intro a ha
      rw [hnα]
      have h1 := hAc a ha α hαA
      have h2 := (hCA _ (PartTwo.omegaOneSub_le _ hc) a ha).symm
      calc a * (α * (α * n * α⁻¹ * n⁻¹)) = (a * α) * (α * n * α⁻¹ * n⁻¹) := by group
        _ = (α * a) * (α * n * α⁻¹ * n⁻¹) := by rw [h1]
        _ = α * (a * (α * n * α⁻¹ * n⁻¹)) := by group
        _ = α * ((α * n * α⁻¹ * n⁻¹) * a) := by rw [h2]
        _ = α * (α * n * α⁻¹ * n⁻¹) * a := by group
    have hTI' : IsTI (conjSubgroup n A) := isTI_conjSubgroup hATI n
    have hle : conjSubgroup n⁻¹ (conjSubgroup n A) ≤
        Subgroup.normalizer (conjSubgroup n A : Set G) := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
      intro a ha
      exact Tim77.mem_normalizer_of_commute_of_isTI hTI' hmem hne (hcomm a ha)
    have hne' : conjSubgroup n A ≠ ⊥ := fun h => hne (by
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem)
    have h := commute_of_le_normalizer (Tim78.comm_conj hAc n)
      ((K.two_conj g).map (MulAut.conj n).toMonoidHom) hne' hTI' hle
    intro b hb a ha
    exact h b hb a (by rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]; exact ha)
  have hpair : ∀ i j : ↥N, ∀ a ∈ conjSubgroup (i : G) A, ∀ b ∈ conjSubgroup (j : G) A,
      a * b = b * a := by
    intro i j a ha b hb
    have hij : (i : G)⁻¹ * j ∈ N := N.mul_mem (N.inv_mem i.2) j.2
    have h := hAn _ hij ((i : G)⁻¹ * b * i) (by
      rw [mem_conjSubgroup, show ((i : G)⁻¹ * j)⁻¹ * ((i : G)⁻¹ * b * i) * ((i : G)⁻¹ * j) =
        (j : G)⁻¹ * b * j by group]
      exact mem_conjSubgroup.mp hb) ((i : G)⁻¹ * a * i) (mem_conjSubgroup.mp ha)
    calc a * b = (i : G) * (((i : G)⁻¹ * a * i) * ((i : G)⁻¹ * b * i)) * (i : G)⁻¹ := by group
      _ = (i : G) * (((i : G)⁻¹ * b * i) * ((i : G)⁻¹ * a * i)) * (i : G)⁻¹ := by rw [h]
      _ = b * a := by group
  obtain ⟨-, hW2⟩ := iSup_comm_pGroup (fun i : ↥N => conjSubgroup (i : G) A)
    (fun i => (K.two_conj g).map (MulAut.conj (i : G)).toMonoidHom) hpair
  set W := ⨆ i : ↥N, conjSubgroup (i : G) A with hW
  have hU₀W : PartTwo.omegaOneSub U ≤ Subgroup.normalizer (W : Set G) :=
    le_trans le_sup_left le_normalizer_iSup
  have hS : IsPGroup 2 ↥(PartTwo.omegaOneSub U ⊔ W) := IsPGroup.to_sup_of_normal_right'
    (K.two.to_le (PartTwo.omegaOneSub_le U)) hW2 hU₀W
  have hAS : A ≤ PartTwo.omegaOneSub U ⊔ W := by
    intro a ha
    refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem ⟨1, N.one_mem⟩ ?_)
    rw [conjSubgroup_one]
    exact ha
  have hgA : conjSubgroup g⁻¹ A = U := by
    rw [hA, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have h4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub (conjSubgroup g⁻¹ A) ⊓
      (PartTwo.omegaOneSub U ⊔ W)) := by
    rw [hgA, inf_of_le_left le_sup_left]
    exact K.card4
  have hcomm := tim78_2_14_b hCen hU hAc (K.two_conj g) hATI (K.omega_ne_conj g) hS hAS g⁻¹ h4
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have hβ' : β ∈ PartTwo.omegaOneSub (conjSubgroup g⁻¹ A) := by rw [hgA]; exact hβ
  exact K.not_comm D.mem D.ne_one hβ hβ1 (hcomm α D.mem β hβ')

theorem not_comm_AA {β : G} (hβ : β ∈ PartTwo.omegaOneSub U) (hβ1 : β ≠ 1) :
    ¬ ∀ a ∈ conjSubgroup g U, ∀ b ∈ conjSubgroup β (conjSubgroup g U), a * b = b * a := by
  intro hAA
  have K := D.core
  have hαA : α ∈ conjSubgroup g U := PartTwo.omegaOneSub_le _ D.mem
  have hz := D.comm_α_β hCen hU hβ
  have hz1 : α * β * α⁻¹ * β⁻¹ ≠ 1 := fun h => K.not_comm D.mem D.ne_one hβ hβ1 (by
    calc α * β = α * β * α⁻¹ * β⁻¹ * (β * α) := by group
      _ = β * α := by rw [h, one_mul])
  have hzc : ∀ a ∈ conjSubgroup g U, a * (α * β * α⁻¹ * β⁻¹) = (α * β * α⁻¹ * β⁻¹) * a := by
    intro a ha
    have h1 := K.comm_conj' g a ha α hαA
    have hmem : β * α⁻¹ * β⁻¹ ∈ conjSubgroup β (conjSubgroup g U) := by
      rw [mem_conjSubgroup, show β⁻¹ * (β * α⁻¹ * β⁻¹) * β = α⁻¹ by group]
      exact (conjSubgroup g U).inv_mem hαA
    have h2 := hAA a ha _ hmem
    calc a * (α * β * α⁻¹ * β⁻¹) = (a * α) * (β * α⁻¹ * β⁻¹) := by group
      _ = (α * a) * (β * α⁻¹ * β⁻¹) := by rw [h1]
      _ = α * (a * (β * α⁻¹ * β⁻¹)) := by group
      _ = α * ((β * α⁻¹ * β⁻¹) * a) := by rw [h2]
      _ = α * β * α⁻¹ * β⁻¹ * a := by group
  have hCTI : IsTI (conjSubgroup x U) := isTI_conjSubgroup K.ti x
  have hle : conjSubgroup (g * x⁻¹) (conjSubgroup x U) ≤
      Subgroup.normalizer (conjSubgroup x U : Set G) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
    intro a ha
    exact Tim77.mem_normalizer_of_commute_of_isTI hCTI (PartTwo.omegaOneSub_le _ hz) hz1
      (hzc a ha)
  have hC1 : conjSubgroup x U ≠ ⊥ := fun h => hz1 (by
    have := PartTwo.omegaOneSub_le _ hz
    rwa [h, Subgroup.mem_bot] at this)
  have h := commute_of_le_normalizer (K.comm_conj' x) (K.two_conj x) hC1 hCTI hle
  apply D.not_comm_CA hCen hU
  intro c hc a ha
  exact h c hc a (by rw [← conjSubgroup_mul, inv_mul_cancel_right]; exact ha)

theorem comm_mem_C₀ {a β : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (hβ : β ∈ PartTwo.omegaOneSub U) :
    a * β * a⁻¹ * β⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  have K := D.core
  by_cases hβ1 : β = 1
  · rw [hβ1, mul_one, mul_inv_cancel, inv_one, mul_one]
    exact Subgroup.one_mem _
  set A := conjSubgroup g U with hA
  have hββ : β * β = 1 := K.sq_omega (h := 1) (by rw [conjSubgroup_one]; exact hβ)
  have hβA : β ∈ PartTwo.omegaOneSub (conjSubgroup g⁻¹ A) := by
    rw [hA, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    exact hβ
  have h4 : (β * α) ^ 4 = 1 := by
    rw [← K.ord' D.mem D.ne_one hβ hβ1]
    exact pow_orderOf_eq_one _
  have hc := comm_of_orderOf_eq_four hββ D.sq_α h4
  have hαA : α ∈ A := PartTwo.omegaOneSub_le _ D.mem
  have hmem : β * α * β⁻¹ ∈ conjSubgroup β A := by
    rw [mem_conjSubgroup, show β⁻¹ * (β * α * β⁻¹) * β = α by group]
    exact hαA
  have hne : β * α * β⁻¹ ≠ 1 := fun h => D.ne_one (by
    calc α = β⁻¹ * (β * α * β⁻¹) * β := by group
      _ = 1 := by rw [h]; group)
  have hTIA : IsTI A := isTI_conjSubgroup K.ti g
  have T : Setup210 A (conjSubgroup β A) :=
    { comm := K.comm_conj' g
      two := K.two_conj g
      exp_ne := K.exp_ne_conj g
      ti := hTIA
      conj := ⟨β, rfl⟩
      ne_bot := by
        intro hbot
        have hαN : α ∈ A ⊓ Subgroup.normalizer (conjSubgroup β A : Set G) :=
          Subgroup.mem_inf.mpr ⟨hαA, Tim77.mem_normalizer_of_commute_of_isTI
            (isTI_conjSubgroup hTIA β) hmem hne hc⟩
        rw [hbot, Subgroup.mem_bot] at hαN
        exact D.ne_one hαN }
  have Q : NCPair A (conjSubgroup β A) := ⟨T, K.exp_conj g, D.not_comm_AA hCen hU hβ hβ1⟩
  obtain ⟨x₀, hx₀, he⟩ := Q.exists_conj hCen hU
  obtain ⟨x', hx', hD⟩ := Q.exists_fixed hCen hU hββ (mem_normalizer_sup_of_swap hββ A)
    ⟨x₀, hx₀, he⟩
  have hw := Q.commutator_mem_omega_of_swap hCen hU hββ hβ1 rfl hβA hx' hD
    (Subgroup.mem_sup_left D.mem)
  have hw' : β * α * β⁻¹ * α⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
    have := (PartTwo.omegaOneSub (conjSubgroup x U)).inv_mem (D.comm_α_β hCen hU hβ)
    rwa [show (α * β * α⁻¹ * β⁻¹)⁻¹ = β * α * β⁻¹ * α⁻¹ by group] at this
  have hw1 : β * α * β⁻¹ * α⁻¹ ≠ 1 := fun h => K.not_comm D.mem D.ne_one hβ hβ1 (by
    calc α * β = (β * α * β⁻¹ * α⁻¹)⁻¹ * (β * α) := by group
      _ = β * α := by rw [h, inv_one, one_mul])
  have e : conjSubgroup x' A = conjSubgroup (x' * g) U := by rw [hA, conjSubgroup_mul]
  have hDC : conjSubgroup x' A = conjSubgroup x U := by
    rw [e]
    refine Tim77.conjSubgroup_eq_of_inf_ne_bot K.ti fun hbot => hw1 ?_
    have hw'' : β * α * β⁻¹ * α⁻¹ ∈ conjSubgroup (x' * g) U := by
      rw [← e]
      exact PartTwo.omegaOneSub_le _ hw
    have : β * α * β⁻¹ * α⁻¹ ∈ conjSubgroup (x' * g) U ⊓ conjSubgroup x U :=
      Subgroup.mem_inf.mpr ⟨hw'', PartTwo.omegaOneSub_le _ hw'⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h := Q.commutator_mem_omega_of_swap hCen hU hββ hβ1 rfl hβA hx' hD
    (Subgroup.mem_sup_left ha)
  rw [hDC] at h
  have := (PartTwo.omegaOneSub (conjSubgroup x U)).inv_mem h
  rwa [show (β * a * β⁻¹ * a⁻¹)⁻¹ = a * β * a⁻¹ * β⁻¹ by group] at this

omit [Finite G] hCen hU in
theorem comm_ne_one {a β : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1)
    (hβ : β ∈ PartTwo.omegaOneSub U) (hβ1 : β ≠ 1) : a * β * a⁻¹ * β⁻¹ ≠ 1 := fun h =>
  D.core.not_comm ha ha1 hβ hβ1 (by
    calc a * β = a * β * a⁻¹ * β⁻¹ * (β * a) := by group
      _ = β * a := by rw [h, one_mul])

omit hCen hU in
theorem ne_C : U ≠ conjSubgroup x U := by
  intro h
  apply D.pair.ne
  rw [h, D.fix, ← h]

theorem ncomm_a {a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1) :
    ¬ ∀ u ∈ U, ∀ b ∈ conjSubgroup a U, u * b = b * u := by
  intro hUU
  have K := D.core
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have hβU := PartTwo.omegaOneSub_le U hβ
  have hz : β * a * β⁻¹ * a⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
    have := (PartTwo.omegaOneSub (conjSubgroup x U)).inv_mem (D.comm_mem_C₀ hCen hU ha hβ)
    rwa [show (a * β * a⁻¹ * β⁻¹)⁻¹ = β * a * β⁻¹ * a⁻¹ by group] at this
  have hz1 : β * a * β⁻¹ * a⁻¹ ≠ 1 := fun h => D.comm_ne_one ha ha1 hβ hβ1 (by
    calc a * β * a⁻¹ * β⁻¹ = (β * a * β⁻¹ * a⁻¹)⁻¹ := by group
      _ = 1 := by rw [h, inv_one])
  have hzc : ∀ u ∈ U, u * (β * a * β⁻¹ * a⁻¹) = (β * a * β⁻¹ * a⁻¹) * u := by
    intro u hu
    have h1 := K.comm u hu β hβU
    have hmem : a * β⁻¹ * a⁻¹ ∈ conjSubgroup a U := by
      rw [mem_conjSubgroup, show a⁻¹ * (a * β⁻¹ * a⁻¹) * a = β⁻¹ by group]
      exact U.inv_mem hβU
    have h2 := hUU u hu _ hmem
    calc u * (β * a * β⁻¹ * a⁻¹) = (u * β) * (a * β⁻¹ * a⁻¹) := by group
      _ = (β * u) * (a * β⁻¹ * a⁻¹) := by rw [h1]
      _ = β * (u * (a * β⁻¹ * a⁻¹)) := by group
      _ = β * ((a * β⁻¹ * a⁻¹) * u) := by rw [h2]
      _ = β * a * β⁻¹ * a⁻¹ * u := by group
  have hCTI : IsTI (conjSubgroup x U) := isTI_conjSubgroup K.ti x
  have hle : conjSubgroup x⁻¹ (conjSubgroup x U) ≤
      Subgroup.normalizer (conjSubgroup x U : Set G) := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    intro u hu
    exact Tim77.mem_normalizer_of_commute_of_isTI hCTI (PartTwo.omegaOneSub_le _ hz) hz1
      (hzc u hu)
  have hC1 : conjSubgroup x U ≠ ⊥ := fun h => hz1 (by
    have := PartTwo.omegaOneSub_le _ hz
    rwa [h, Subgroup.mem_bot] at this)
  have h := commute_of_le_normalizer (K.comm_conj' x) (K.two_conj x) hC1 hCTI hle
  have P := D.pair
  obtain ⟨v, hv, hvN⟩ := P.exists_not_mem_N hCen hU (U ⊔ conjSubgroup α U).one_mem
  obtain ⟨w, hw, hwN⟩ := P.exists_not_mem_N hCen hU D.memX
  rw [conjSubgroup_one] at hv
  have hvw : w * v = v * w :=
    h w hw v (by rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]; exact hv)
  have heq := P.eq_of_commute hCen hU (U ⊔ conjSubgroup α U).one_mem D.memX
    (by rw [conjSubgroup_one]; exact hv) hvN hw hwN
    (by rw [← hvw, mul_inv_cancel]; exact Subgroup.one_mem _)
  rw [conjSubgroup_one] at heq
  exact D.ne_C heq

theorem pair_a {a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1) :
    NCPair U (conjSubgroup a U) :=
  D.core.ncpair ha ha1 (D.ncomm_a hCen hU ha ha1)

theorem fix_a {a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1) :
    ∃ xa ∈ U ⊔ conjSubgroup a U, conjSubgroup xa U = conjSubgroup x U ∧
      conjSubgroup a (conjSubgroup x U) = conjSubgroup x U := by
  have K := D.core
  have Pa := D.pair_a hCen hU ha ha1
  have haa := K.sq_omega ha
  obtain ⟨x₀, hx₀, he⟩ := Pa.exists_conj hCen hU
  obtain ⟨xa, hxa, hxaC⟩ := Pa.exists_fixed hCen hU haa
    (mem_normalizer_sup_of_swap haa U) ⟨x₀, hx₀, he⟩
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have hw := Pa.commutator_mem_omega_of_swap hCen hU haa ha1 rfl ha hxa hxaC
    (Subgroup.mem_sup_left hβ)
  have hw' := D.comm_mem_C₀ hCen hU ha hβ
  have hw1 := D.comm_ne_one ha ha1 hβ hβ1
  have hCa : conjSubgroup xa U = conjSubgroup x U := by
    refine Tim77.conjSubgroup_eq_of_inf_ne_bot K.ti fun hbot => hw1 ?_
    have : a * β * a⁻¹ * β⁻¹ ∈ conjSubgroup xa U ⊓ conjSubgroup x U :=
      Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le _ hw, PartTwo.omegaOneSub_le _ hw'⟩
    rwa [hbot, Subgroup.mem_bot] at this
  exact ⟨xa, hxa, hCa, by rw [← hCa]; exact hxaC⟩

end Data31

end CFSG.RankThree.GF2n.Tim78
