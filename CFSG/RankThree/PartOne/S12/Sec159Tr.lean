module

public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace Sec159Tr

variable {G : Type} [Group G]

theorem isElementaryAbelian_subgroupOf {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hH : IsElementaryAbelian p ↥H) : IsElementaryAbelian p ↥(H.subgroupOf K) := by
  have := hH
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥H => (z : G))
      (hH.is_comm.comm ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
    apply Subtype.ext
    apply Subtype.ext
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := H) (x.1.1 : G) x.2
    simpa using this

theorem card_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv

theorem normalizer_subgroupOf_le {M₀ N : Subgroup G} {B : Subgroup ↥M₀}
    (hB : Subgroup.normalizer ((B.map M₀.subtype : Subgroup G) : Set G) ≤ N) :
    Subgroup.normalizer (B : Set ↥M₀) ≤ N.subgroupOf M₀ := by
  intro g hg
  refine Subgroup.mem_subgroupOf.2 (hB ?_)
  have key : ∀ g' : ↥M₀, g' ∈ Subgroup.normalizer (B : Set ↥M₀) → ∀ y : G,
      y ∈ B.map M₀.subtype → (g' : G) * y * (g' : G)⁻¹ ∈ B.map M₀.subtype := by
    rintro g' hg' y ⟨b, hb, rfl⟩
    exact ⟨g' * b * g'⁻¹, (Subgroup.mem_normalizer_iff.1 hg' b).1 hb, by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have h1 := key g⁻¹ ((Subgroup.normalizer (B : Set ↥M₀)).inv_mem hg) _ hy
  simpa [mul_assoc] using h1

theorem exists_aut_hom {M₀ X E : Subgroup G} (hE : E ≤ M₀) :
    ∃ f : ↥(X.subgroupOf M₀ ⊓
        Subgroup.normalizer ((E.subgroupOf M₀ : Subgroup ↥M₀) : Set ↥M₀)) →* ↥(torusImage E X),
      ∀ n, f n = 1 → ∀ e ∈ E.subgroupOf M₀, (n : ↥M₀) * e = e * n := by
  set Dm := X.subgroupOf M₀ ⊓
    Subgroup.normalizer ((E.subgroupOf M₀ : Subgroup ↥M₀) : Set ↥M₀) with hDm
  have hnorm : ∀ n : ↥Dm, ((n : ↥M₀) : G) ∈ Subgroup.normalizer (E : Set G) := by
    intro n
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ M₀
    · have := Subgroup.mem_normalizer_iff.1 n.2.2 ⟨y, hy⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have hy' : y ∉ E := fun h => hy (hE h)
      have hy'' : ((n : ↥M₀) : G) * y * ((n : ↥M₀) : G)⁻¹ ∉ E := by
        intro h
        apply hy
        have h1 := hE h
        have hn : ((n : ↥M₀) : G) ∈ M₀ := (n : ↥M₀).2
        have := M₀.mul_mem (M₀.mul_mem (M₀.inv_mem hn) h1) hn
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd h hy', fun h => absurd h hy''⟩
  let ι : ↥Dm →* ↥(Subgroup.normalizer (E : Set G)) :=
    { toFun := fun n => ⟨((n : ↥M₀) : G), hnorm n⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f₀ : ↥Dm →* MulAut ↥E := E.normalizerMonoidHom.comp ι
  have hf₀ : ∀ n, f₀ n ∈ torusImage E X := fun n =>
    Subgroup.mem_map.2 ⟨ι n, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 n.2.1), rfl⟩
  refine ⟨f₀.codRestrict (torusImage E X) hf₀, ?_⟩
  intro n hn e he
  have h1 : f₀ n = 1 := congrArg Subtype.val hn
  have h2 := congrArg (fun φ : MulAut ↥E => ((φ ⟨((e : ↥M₀) : G), Subgroup.mem_subgroupOf.1 he⟩ : ↥E) : G)) h1
  simp only [f₀, MonoidHom.comp_apply, MulAut.one_apply,
    Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  apply Subtype.ext
  have h3 : ((n : ↥M₀) : G) * ((e : ↥M₀) : G) = ((e : ↥M₀) : G) * ((n : ↥M₀) : G) := by
    have := congrArg (fun z : G => z * ((n : ↥M₀) : G)) h2
    simpa [ι, mul_assoc] using this
  exact h3

end Sec159Tr

end CFSG.RankThree.PartOne
