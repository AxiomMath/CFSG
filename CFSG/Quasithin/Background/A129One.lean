module

public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.DicksonPerfectSL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank.Ccomm CFSG.Quasithin.Dickson
open scoped MatrixGroups commutatorElement

namespace A129

variable {G : Type} [Group G]

@[expose] noncomputable def frattiniActionOn (P H : Subgroup G) [P.Normal] :
    ↥H →* MulAut (↥P ⧸ frattini ↥P) :=
  (autQuotient (frattini ↥P)).comp ((MulAut.conjNormal : G →* MulAut ↥P).comp H.subtype)

theorem mem_ker_frattiniActionOn (P H : Subgroup G) [P.Normal] (h : ↥H) :
    h ∈ (frattiniActionOn P H).ker ↔ ActsTriviallyOnFrattiniQuotient P (h : G) := by
  rw [MonoidHom.mem_ker]
  change autQuotient (frattini ↥P) (MulAut.conjNormal (h : G)) = 1 ↔ _
  rw [← MonoidHom.mem_ker, mem_ker_autQuotient]
  unfold ActsTriviallyOnFrattiniQuotient frattiniIn
  constructor
  · intro hx d hd
    refine ⟨_, hx ⟨d, hd⟩, ?_⟩
    simp [MulAut.conjNormal_apply]
  · intro hx x
    obtain ⟨y, hy, hyd⟩ := hx (x : G) x.2
    have hy' : y = x⁻¹ * MulAut.conjNormal (h : G) x := by
      apply Subtype.ext
      simpa [MulAut.conjNormal_apply] using hyd
    rw [← hy']
    exact hy

theorem commutator_eq_bot_of_trivial_action {p : ℕ} [Fact p.Prime] [Finite G] (P H : Subgroup G)
    [P.Normal] (hP : IsPGroup p ↥P) (hH : ⁅H, H⁆ = H)
    (htriv : (frattiniActionOn P H).ker = ⊤) : ⁅P, H⁆ = ⊥ := by
  let ψ : ↥H →* MulAut ↥P := (MulAut.conjNormal : G →* MulAut ↥P).comp H.subtype
  have hKb : IsPGroup p (autQuotient (frattini ↥P)).ker := isPGroup_ker_autQuotient_frattini hP
  have hJle : ψ.range ≤ (autQuotient (frattini ↥P)).ker := by
    rintro _ ⟨h, rfl⟩
    have : h ∈ (frattiniActionOn P H).ker := htriv ▸ Subgroup.mem_top h
    exact this
  have hJp : IsPGroup p ψ.range := hKb.to_le hJle
  have hperf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.2 hH
  have hJperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hJtriv : ψ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hJp.isNilpotent
    exact Group.IsPerfect.not_isNilpotent ψ.range ‹_›
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx h hh
  have h1 : ψ ⟨h, hh⟩ = 1 := by
    have : ψ ⟨h, hh⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hJtriv] at this
    exact Subgroup.mem_bot.1 this
  have h2 := congrArg (fun α : MulAut ↥P => (α ⟨x, hx⟩ : G)) h1
  simp only [ψ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

theorem exists_hom_sl2_of_perfect {p : ℕ} [Fact p.Prime] {H W : Type*} [Group H] [Group W]
    [Group.IsPerfect H] (e : W ≃* Multiplicative (Fin 2 → ZMod p)) (ρ : H →* MulAut W) :
    ∃ σ : H →* SL(2, ZMod p), ∀ h, σ h = 1 ↔ ρ h = 1 := by
  let ρGL : H →* GL (Fin 2) (ZMod p) := (elemAutEquivGL e).toMonoidHom.comp ρ
  let d : H →* (ZMod p)ˣ := Matrix.GeneralLinearGroup.det.comp ρGL
  have hdet : ∀ h, Matrix.det (ρGL h : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
    intro h
    have hker : commutator H ≤ d.ker := Abelianization.commutator_subset_ker d
    have h1 : d h = 1 := hker (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
    have h2 : (Matrix.GeneralLinearGroup.det (ρGL h) : ZMod p) = 1 := by
      have := congrArg Units.val h1
      simpa [d] using this
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h2
  let σ : H →* SL(2, ZMod p) :=
    { toFun := fun h => ⟨(ρGL h : Matrix (Fin 2) (Fin 2) (ZMod p)), hdet h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp; rfl) }
  refine ⟨σ, fun h => ?_⟩
  constructor
  · intro h1
    have h2 : ρGL h = 1 := Units.ext (congrArg Subtype.val h1)
    exact (elemAutEquivGL e).injective (by simpa [ρGL] using h2)
  · intro h1
    apply Subtype.ext
    have : ρGL h = 1 := by simp [ρGL, h1]
    change (ρGL h : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      ((1 : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
    rw [this]
    rfl

end A129

theorem a129One : A129One := by
  intro p hp hp2 G _ _ P H hPn hPp hΩ hcl hrank hHperf hPH
  have : Fact p.Prime := ⟨hp⟩
  have hset : P.subtype '' {x : ↥P | x ^ p = 1} = {x : G | x ∈ P ∧ x ^ p = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxp), rfl⟩
  have hΩ' : Subgroup.closure {x : ↥P | x ^ p = 1} = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [MonoidHom.map_closure, hset, hΩ, Subgroup.map_top, Subgroup.range_subtype]
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup ↥P) = 2 := by
    rw [pRank_top_subtype]; exact hrank
  have hcl' : ClassLeTwo (⊤ : Subgroup ↥P) := classLeTwo_top_of hcl
  have hcases := isElemAbelianOfRank_two_or_isPOnePlusTwo hp2 hPp hΩ' hrank' hcl'
  have hW : Nat.card (↥P ⧸ frattini ↥P) = p ^ 2 := A37.card_frattini_quotient_two hp hPp hcases
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hPp
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hW
  have hHperf' : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.2 hHperf
  obtain ⟨σ, hσ⟩ := A129.exists_hom_sl2_of_perfect e (A129.frattiniActionOn P H)
  have hmem : ∀ h : ↥H, h ∈ σ.ker ↔ ActsTriviallyOnFrattiniQuotient P (h : G) := fun h => by
    rw [MonoidHom.mem_ker, hσ, ← MonoidHom.mem_ker]
    exact A129.mem_ker_frattiniActionOn P H h
  refine ⟨σ.ker, inferInstance, hmem, ?_⟩
  have hKperf : ⁅σ.range, σ.range⁆ = σ.range :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.range σ)
  have hKne : σ.range ≠ ⊥ := by
    intro hbot
    apply hPH
    refine A129.commutator_eq_bot_of_trivial_action P H hPp hHperf ?_
    rw [eq_top_iff]
    intro h _
    rw [MonoidHom.mem_ker, ← hσ]
    have : σ h ∈ σ.range := ⟨h, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  let eK := QuotientGroup.quotientKerEquivRange σ
  have hp35 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hcon
    push Not at hcon
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  rcases hp35 with rfl | hp5
  · exact absurd (sl2_three_perfect_eq_bot _ hKperf) hKne
  · rcases perfect_subgroup_sl2_prime hp5 hKperf hKne with htop | ⟨⟨eS⟩, h5mod, -⟩
    · left
      exact ⟨eK.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩
    · right
      refine ⟨?_, ⟨eK.trans eS⟩⟩
      have hr : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have hsq : p ^ 2 % 5 = (p % 5) ^ 2 % 5 := by rw [Nat.pow_mod]
      rw [hsq] at h5mod
      interval_cases h : p % 5 <;> simp_all

end CFSG.Quasithin
