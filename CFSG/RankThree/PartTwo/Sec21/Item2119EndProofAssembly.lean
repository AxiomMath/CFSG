module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item215
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

namespace Item2119EndProof

theorem exists_fun_of_forall {α β : Type*} [Nonempty β] {S : α → Prop} {P : α → β → Prop}
    (h : ∀ x, S x → ∃ y, P x y) : ∃ f : α → β, ∀ x, S x → P x (f x) := by
  classical
  refine ⟨fun x => if hx : S x then (h x hx).choose else Classical.arbitrary β, fun x hx => ?_⟩
  simp only [hx, ↓reduceDIte]
  exact (h x hx).choose_spec

theorem exists_lf {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c d : G}
    (h : ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∃ Le : Subgroup G, IsLOf2125 L c d e Le) :
    ∃ Lf : G → Subgroup G, ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e) := by
  obtain ⟨f, hf⟩ := exists_fun_of_forall (S := fun e => e ∈ A ∧ e ∉ Subgroup.zpowers d)
    (P := fun e Le => IsLOf2125 L c d e Le) fun e he => h e he.1 he.2
  exact ⟨f, fun e he hed => hf e ⟨he, hed⟩⟩

section Certs

theorem exists_config2119End (h211 : Item211) (h214 : Item214) (h215 : Item215)
    {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}
    (hcfg : Config2119 G A E U c L) {d : G} (hd : d ∈ A ⊓ L) (hd1 : d ≠ 1)
    (hdT : Sec4.InducesTypeOn L d 1)
    (hnorm : ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d) :
    ∃ (U₀ : Subgroup G) (a : G) (X : Subgroup G), Config2119End G A E U c L d U₀ a X := by
  have hpair := hcfg.pair
  have hL : ¬ ∃ n : ℕ, Odd n ∧ Nonempty (L ≃* projSU 4 2 n) := by
    rintro ⟨n, hn, ⟨e⟩⟩
    exact Item21LateProof.false_of_projSU4_odd h211 hpair hcfg.card hn e
  obtain ⟨U₀, hU₀, hU₀L⟩ := (h214 G A E U c L hpair).mpr hL
  obtain ⟨a, haB, hac, X, -, haX⟩ := h215 G A E U c L hpair U₀ hU₀
  exact ⟨U₀, a, X, ⟨hcfg, hd, hd1, hdT, hnorm, hU₀, hU₀L, haB, hac, haX⟩⟩

end Certs

end Item2119EndProof

open Item2119EndProof

end CFSG.RankThree.PartTwo.Sec21
