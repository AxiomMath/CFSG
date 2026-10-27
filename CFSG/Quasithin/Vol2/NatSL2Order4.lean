module

public import CFSG.Quasithin.Vol2.Ch12Sec8NatL

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
  CFSG.Quasithin.SL2Model
open scoped IsMulCommutative MatrixGroups

namespace NatSL2

variable {G : Type} [Group G]

theorem isNaturalSL2Module_one_of {A R V V₁ : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hVe : IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hres : A = oTwoUpper A)
    (hker : ∀ x ∈ A, x ∈ Subgroup.centralizer (V : Set G) ↔ x ∈ R)
    (hne : ¬ A ≤ Subgroup.centralizer (V : Set G)) (hV₁V : V₁ ≤ V) (hV₁2 : Nat.card V₁ = 2) :
    IsNaturalSL2Module 1 A R V V₁ := by
  set F := GaloisField 2 1 with hFdef
  have hF : Nat.card F = 2 := card_galoisField_two_one
  have h01 : ∀ x : F, x = 0 ∨ x = 1 := eq_zero_or_one_of_card_two hF
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hsq : ∀ v : ↥V, v * v = 1 := fun v =>
    Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  obtain ⟨ψ⟩ := exists_mulEquiv_Wm_of_card_four (A := ↥V) hV4 hsq
  let α : ↥A →* MulAut (Wm F) :=
    (MulAut.congr ψ).toMonoidHom.comp ((conjAct V).comp (Subgroup.inclusion hAN))
  let e : SL(2, F) ≃* MulAut (Wm F) :=
    MulEquiv.ofBijective (SL2Model.natAct : SL(2, F) →* MulAut (Wm F))
      ⟨natAct_injective, natAct_surjective_of_card_two hF⟩
  let θ : ↥A →* SL(2, F) := e.symm.toMonoidHom.comp α
  have hθ : ∀ a : ↥A, SL2Model.natAct (θ a) = α a := fun a => by
    show e (e.symm (α a)) = α a
    exact e.apply_symm_apply _
  have hαa : ∀ (a : ↥A) (v : ↥V), α a (ψ v) = ψ (conjAct V ⟨a, hAN a.2⟩ v) := fun a v => by
    simp [α, MulAut.congr_apply]
    rfl
  have hα1 : ∀ a : ↥A, α a = 1 ↔ conjAct V ⟨a, hAN a.2⟩ = 1 := fun a => by
    constructor
    · intro h1
      refine MulEquiv.ext fun v => ?_
      have := hαa a v
      rw [h1, MulAut.one_apply] at this
      rw [MulAut.one_apply]
      exact (ψ.injective this).symm
    · intro h1
      refine MulEquiv.ext fun w => ?_
      obtain ⟨v, rfl⟩ := ψ.surjective w
      rw [hαa, h1, MulAut.one_apply, MulAut.one_apply]
  have hθ1 : ∀ a : ↥A, θ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := fun a => by
    have hc : conjAct V ⟨a, hAN a.2⟩ = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) :=
      conjAct_eq_one_iff_mem_centralizer (V := V) (g := ⟨a, hAN a.2⟩)
    rw [← hc, ← hα1]
    constructor
    · intro h1
      rw [← hθ a, h1, map_one]
    · intro h1
      exact natAct_injective (by rw [hθ a, h1, map_one])
  have hkerθ : θ.ker = R.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hθ1, hker _ a.2]
  have hcomm := commutator_eq_zpowers_c3 (F := F) hF
  have hNn : (Subgroup.zpowers (c3 F)).Normal :=
    Subgroup.normal_of_index_eq_two (index_zpowers_c3 hF)
  have hrange_le : θ.range ≤ Subgroup.zpowers (c3 F) := by
    have htop : (Subgroup.zpowers (c3 F)).comap θ = ⊤ := by
      refine eq_top_of_oTwoUpper_eq hres _ fun x => ⟨1, ?_⟩
      rw [Subgroup.mem_comap, map_pow, pow_one]
      have := Subgroup.pow_index_mem (Subgroup.zpowers (c3 F)) (θ x)
      rwa [index_zpowers_c3 hF] at this
    rintro _ ⟨x, rfl⟩
    have : x ∈ (Subgroup.zpowers (c3 F)).comap θ := by rw [htop]; exact Subgroup.mem_top x
    exact this
  have hrange_ne : θ.range ≠ ⊥ := by
    intro hbot
    apply hne
    intro x hx
    have : θ ⟨x, hx⟩ = 1 := by
      have hmem : θ ⟨x, hx⟩ ∈ θ.range := ⟨_, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact (hθ1 ⟨x, hx⟩).mp this
  have hrange : θ.range = commutator SL(2, F) := by
    rw [hcomm]
    have hcard : Nat.card (Subgroup.zpowers (c3 F)) = 3 := by rw [Nat.card_zpowers, orderOf_c3]
    have hdvd : Nat.card θ.range ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le hrange_le
    have h1 : Nat.card θ.range ≠ 1 := fun h1 => hrange_ne (Subgroup.card_eq_one.mp h1)
    have h3 : Nat.card θ.range = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h h1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hcard, h3])
  obtain ⟨z, hz1, hz⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hV₁2
  have hz1' : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hzall : ∀ w ∈ V₁, w = 1 ∨ w = (z : G) := fun w hw => by
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val (hz ⟨w, hw⟩ fun he => hw1 (congrArg Subtype.val he)))
  have hzV : (z : G) ∈ V := hV₁V z.2
  refine ⟨hAN, θ, ψ, hkerθ, hrange, fun a v => ?_, Multiplicative.toAdd (ψ ⟨z, hzV⟩), ?_,
    fun v => ?_⟩
  · rw [hθ, hαa]
  · intro h0
    have : ψ ⟨z, hzV⟩ = 1 := Multiplicative.toAdd.injective h0
    have := ψ.injective (this.trans (map_one ψ).symm)
    exact hz1' (congrArg Subtype.val this)
  · constructor
    · intro hv
      rcases hzall _ hv with h1 | h1
      · refine ⟨0, ?_⟩
        have : v = 1 := Subtype.ext h1
        rw [this, map_one]
        simp
      · refine ⟨1, ?_⟩
        have : v = ⟨z, hzV⟩ := Subtype.ext h1
        rw [this, one_smul]
    · rintro ⟨c, hc⟩
      rcases h01 c with rfl | rfl
      · rw [zero_smul] at hc
        have : ψ v = 1 := Multiplicative.toAdd.injective hc
        have hv1 : v = 1 := ψ.injective (this.trans (map_one ψ).symm)
        have : (v : G) = 1 := congrArg Subtype.val hv1
        rw [this]
        exact Subgroup.one_mem _
      · rw [one_smul] at hc
        have : ψ v = ψ ⟨z, hzV⟩ := Multiplicative.toAdd.injective hc
        have hv1 : v = ⟨z, hzV⟩ := ψ.injective this
        have : (v : G) = z := congrArg Subtype.val hv1
        rw [this]
        exact z.2

end NatSL2

end CFSG.Quasithin.H13
