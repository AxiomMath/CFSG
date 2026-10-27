module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGCompList.of_rawMarking {lab : LargeEvenLabel} {p : ℕ}
    {S : LargeEvenLabel → Prop} (h : GGCompList lab p S)
    {T : Type} [Group T] [Finite T] (hperf : commutator T = ⊤)
    {α : MulAut T} (hαp : α ^ p = 1) (hα1 : α ≠ 1)
    (hraw : LargeEvenRawDatum lab fun R _ I _ =>
      ∃ θ : T ⧸ Subgroup.center T ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun x y => y = α x) β)
    {K : Subgroup T} (hK : IsComponentOf K (ggFixSub α)) :
    ∃ labK : LargeEvenLabel, S labK ∧ GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨R, _, I, F, ⟨θ, β, hβ, hind⟩, hlist⟩ := largeEvenRawDatum_exists (h _ hraw)
  let π : T →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T))
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center T))
  have hker : π.ker ≤ Subgroup.center T := by
    intro x hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center T) x) = 1 := hx
    have hx'' : QuotientGroup.mk' (Subgroup.center T) x = 1 :=
      θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  have hβπ : ∀ x : T, β (π x) = π (α x) := by
    intro x
    exact hind x (α x) rfl
  exact hlist T π hπ hker hperf α hαp hα1 ⟨β, hβ, hβπ⟩ K hK

end CFSG.StandardType
