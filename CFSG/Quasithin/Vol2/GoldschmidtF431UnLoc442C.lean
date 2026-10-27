module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442B

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Open CFSG.Quasithin.Shult CFSG.QuasithinUnique
open scoped commutatorElement


section Final


variable {H : Type} [Group H] [Finite H]

theorem bender_case {X Uh K : Subgroup H} (hU1 : Uh ≠ ⊥)
    (hUn : ∀ x ∈ X, ∀ u ∈ Uh, x * u * x⁻¹ ∈ Uh) (hU2 : ∀ a ∈ Uh, a ^ 2 = 1)
    (hKp : ⁅K, K⁆ = K) (hUK : Uh ≤ K) (hKX : K ≤ X)
    (hH : IsBenderHull (Subgroup.normalClosure (Uh : Set H))) : False := by
  set L : Subgroup H := Subgroup.normalClosure (Uh : Set H) with hLdef
  have hUL : Uh ≤ L := Subgroup.le_normalClosure
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [hH.2.1]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥L
  set Z := Subgroup.center ↥L with hZ
  let π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z
  let Vb : Subgroup (↥L ⧸ Z) := (Uh.subgroupOf L).map π
  have hxsq : ∀ x ∈ Uh.subgroupOf L, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (hU2 (x : H) (Subgroup.mem_subgroupOf.mp hx))
  have hVb2 : IsPGroup 2 Vb := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hxy, ← map_pow, hxsq x hx, map_one]
  obtain ⟨⟨u0, hu0⟩, hu01⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu0z : (⟨u0, hUL hu0⟩ : ↥L) ∉ Z := by
    intro hz
    exact hu01 (Subtype.ext (congrArg (fun y : ↥L => (y : H))
      (eq_one_of_mem_odd hZodd hz
        ⟨1, by simpa using hxsq ⟨u0, hUL hu0⟩ (Subgroup.mem_subgroupOf.mpr hu0)⟩)))
  have hVb : Vb ≠ ⊥ := by
    intro hbot
    have hxV : (⟨u0, hUL hu0⟩ : ↥L) ∈ Uh.subgroupOf L := Subgroup.mem_subgroupOf.mpr hu0
    have hmem : π ⟨u0, hUL hu0⟩ ∈ Vb := Subgroup.mem_map_of_mem π hxV
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu0z ((QuotientGroup.eq_one_iff _).1 hmem)
  have hSolv := isSolvable_autStab hH.2.2 hVb hVb2
  have hmap : ∀ m ∈ X, ∀ y ∈ Vb, actK L m y ∈ Vb := by
    intro m hm y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨MulAut.conjNormal m x, ?_, rfl⟩
    change MulAut.conjNormal m x ∈ Uh.subgroupOf L
    rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact hUn m hm _ (Subgroup.mem_subgroupOf.mp hx)
  have hstab : ∀ m ∈ X, actK L m ∈ autStab (↥L ⧸ Z) Vb := by
    intro m hm y
    refine ⟨hmap m hm y, fun hy => ?_⟩
    have h1 := hmap m⁻¹ (X.inv_mem hm) _ hy
    have h2 : (actK L m⁻¹) ((actK L m) y) = y := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rwa [h2] at h1
  let ρ : ↥K →* ↥(autStab (↥L ⧸ Z) Vb) :=
    ((actK L).comp K.subtype).codRestrict (autStab (↥L ⧸ Z) Vb) (fun k => hstab k (hKX k.2))
  have hρ : ∀ k : ↥K, actK L (k : H) = 1 := fun k =>
    congrArg Subtype.val (hom_eq_one_of_perfect hKp ρ k)
  have hcen : ∀ x : ↥L, (QuotientGroup.mk x : ↥L ⧸ Z) * QuotientGroup.mk ⟨u0, hUL hu0⟩ =
      QuotientGroup.mk ⟨u0, hUL hu0⟩ * QuotientGroup.mk x := by
    intro x
    have := actK_mk L u0 x
    have h1 := hρ ⟨u0, hUK hu0⟩
    simp only [] at h1
    rw [h1, MulAut.one_apply] at this
    have h3 : (QuotientGroup.mk (MulAut.conjNormal u0 x) : ↥L ⧸ Z) = QuotientGroup.mk x := this.symm
    have hcx : (MulAut.conjNormal u0 x) * ⟨u0, hUL hu0⟩ = ⟨u0, hUL hu0⟩ * x := by
      apply Subtype.ext
      simp [MulAut.conjNormal_apply]
    calc (QuotientGroup.mk x : ↥L ⧸ Z) * QuotientGroup.mk ⟨u0, hUL hu0⟩
        = QuotientGroup.mk (MulAut.conjNormal u0 x) * QuotientGroup.mk ⟨u0, hUL hu0⟩ := by
          rw [h3]
      _ = QuotientGroup.mk (MulAut.conjNormal u0 x * ⟨u0, hUL hu0⟩) :=
          (QuotientGroup.mk_mul Z _ _).symm
      _ = QuotientGroup.mk (⟨u0, hUL hu0⟩ * x) := by rw [hcx]
      _ = QuotientGroup.mk ⟨u0, hUL hu0⟩ * QuotientGroup.mk x := QuotientGroup.mk_mul Z _ _
  have hsimple : IsSimpleGroup (↥L ⧸ Z) := hH.1.2
  have hz : (⟨u0, hUL hu0⟩ : ↥L) ∈ Z := by
    have hC : (QuotientGroup.mk ⟨u0, hUL hu0⟩ : ↥L ⧸ Z) ∈ Subgroup.center (↥L ⧸ Z) :=
      Subgroup.mem_center_iff.2 (fun g => by
        induction g using QuotientGroup.induction_on with
        | H x => exact hcen x)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ Z)) with h | h
    · rw [h, Subgroup.mem_bot] at hC
      exact (QuotientGroup.eq_one_iff _).1 hC
    · have hab : ∀ a b : ↥L ⧸ Z, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a
      have hcomm : commutator ↥L ≤ Z := by
        rw [commutator]
        refine Subgroup.commutator_le.2 (fun x _ y _ => ?_)
        have h1 : ⁅(π x), (π y)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hab _ _)
        rw [← map_commutatorElement] at h1
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hZtop : Z = ⊤ := top_le_iff.1 (hH.1.1 ▸ hcomm)
      rw [hZtop]
      exact Subgroup.mem_top _
  exact hu0z hz

theorem loc442U_final {X Uh R K : Subgroup H} (hX : X ≠ ⊤) (hU1 : Uh ≠ ⊥) (hUX : Uh ≤ X)
    (hUn : ∀ x ∈ X, ∀ u ∈ Uh, x * u * x⁻¹ ∈ Uh) (hUab : ∀ a ∈ Uh, ∀ b ∈ Uh, a * b = b * a)
    (hU2 : ∀ a ∈ Uh, a ^ 2 = 1)
    (hfix : ∀ u ∈ Uh, u ≠ 1 → ∀ g : H, g⁻¹ * u * g ∈ X → g ∈ X)
    (hNX : Subgroup.normalizer (Uh : Set H) ≤ X)
    (hR2 : ∃ a ∈ R, ∃ b ∈ R, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRsq : ∀ a ∈ R, a ^ 2 = 1)
    (_hRU : ∀ r ∈ R, r ∈ Uh → r = 1)
    (hRC : ∀ r ∈ R, r ≠ 1 → ∀ g : H, g * r = r * g → g ∈ X)
    (hKX : K ≤ X) (hKp : ⁅K, K⁆ = K) (hUK : Uh ≤ K)
    (_hKc : ∀ k ∈ K, ∀ u ∈ Uh, k * u = u * k) : False := by
  classical
  have hVn : (Uh.subgroupOf X).Normal := ⟨fun n hn g => hUn _ g.2 _ hn⟩
  have hel : IsElemAbelian 2 Uh :=
    ⟨⟨⟨fun a b => Subtype.ext (hUab a.1 a.2 b.1 b.2)⟩⟩, fun a ha => hU2 a ha⟩
  have hmk : ∀ g : H, ((g : H ⧸ X) = ((1 : H) : H ⧸ X)) ↔ g ∈ X := fun g => by
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  have hfix' : ShultFixedPoint X Uh := by
    intro v hv hv1
    refine ⟨((1 : H) : H ⧸ X), ?_, ?_⟩
    · show ((v * 1 : H) : H ⧸ X) = ((1 : H) : H ⧸ X)
      rw [mul_one]
      exact (hmk v).2 (hUX hv)
    · intro c hc
      induction c using QuotientGroup.induction_on with
      | H g =>
        have h' : ((v * g : H) : H ⧸ X) = (g : H ⧸ X) := hc
        rw [QuotientGroup.eq] at h'
        have hg : g⁻¹ * v * g ∈ X := by
          have := X.inv_mem h'
          simpa [mul_assoc] using this
        exact (hmk g).2 (hfix v hv hv1 g hg)
  have hyp : ShultI85Hyp X Uh := ⟨hX, hU1, hUX, hVn, hel, hfix'⟩
  rcases shultI85Part1 H X Uh hyp with ⟨h2, hL⟩ | ⟨f, hcard, hQ, -, -, -⟩
  · exact odd_case hX hUn hU2 hNX hR2 hRab hRsq hRC hL
  · exact bender_case hU1 hUn hU2 hKp hUK hKX hQ.isBenderHull

end Final

end CFSG.Quasithin.H13.F431.Un
