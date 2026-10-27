module

public import CFSG.Quasithin.EmptyFaithful.S151S9E
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Sporadic.Schreier.RuAutInnerBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Sporadic.RuSchreier
  CFSG.QuasithinUnique.Ch1.SporLat.Ru

theorem ru_overgroup_orders
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .Ru)) {T Y : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ Nat.card Y = 16384 ∨ Nat.card Y = 245760 ∨ Nat.card Y = 344064 ∨
      Nat.card Y = 49152 := by
  rcases ru_overgroups hX hT hTY with h | ⟨m, hm, hcard, -, -⟩
  · exact Or.inl h
  · right
    simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hcard
    · exact Or.inr (Or.inl hcard)
    · exact Or.inr (Or.inr (Or.inl hcard))
    · exact Or.inr (Or.inr (Or.inr hcard))
    · exact Or.inr (Or.inr (Or.inr hcard))

theorem centMaxProp_ruP :
    CentMaxProp ↥ruP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₀ : Subgroup ↥ruP := (ruSylow : Subgroup ↥ruP) with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := ruSylow.isPGroup'
  have hS₀i : ¬ 2 ∣ S₀.index := ruSylow.not_dvd_index
  have hz2 : orderOf ruZ' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_ruZ
  have hcen : centerOf S₀ = Subgroup.zpowers ruZ' := by
    apply le_antisymm
    · rintro x ⟨hxS, hxc⟩
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · have hxz : x = ruZ' :=
          eq_ruZ'_of_central hxS (fun s hs => (Subgroup.mem_centralizer_iff.mp hxc s hs).symm) hx1
        rw [hxz]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨ruZ'_mem_sylow, Subgroup.mem_centralizer_iff.mpr fun s hs => (ruZ'_comm hs).symm⟩
  set C : Subgroup ↥ruP := Subgroup.centralizer ({ruZ'} : Set ↥ruP) with hC
  have hCmap : C.map ruP.subtype = ruP ⊓ Subgroup.centralizer ({ruZ} : Set (Equiv.Perm (Fin 4060))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp hy
      exact congrArg Subtype.val this
    · rintro ⟨hxP, hxc⟩
      refine ⟨⟨x, hxP⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp hxc
  have hCcard : Nat.card C = 245760 := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective ruP), hCmap,
      ← ruC_eq_centralizer]
    exact card_ruC
  have hne : C ≠ ⊤ := by
    intro htop
    have hz : ruZ' ∈ Subgroup.center ↥ruP := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ C := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    rw [center_ruP, Subgroup.mem_bot] at hz
    rw [hz, orderOf_one] at hz2
    omega
  have hSC : S₀ ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (ruZ'_comm hs).symm
  have hT : IsSylowTwoOf S₀ ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hS₀2, hS₀i⟩
  have hmax : IsMaxSubgroupIn ⊤ C := by
    refine ⟨lt_top_iff_ne_top.mpr hne, fun K hCK _ => ?_⟩
    have hSK : S₀ ≤ K := hSC.trans hCK.le
    have hdvd : 245760 ∣ Nat.card K := hCcard ▸ Subgroup.card_dvd_of_le hCK.le
    rcases ru_overgroup_orders ⟨ruEquivP.symm⟩ hT hSK with h | h | h | h | h
    · exact h
    · exfalso
      rw [h] at hdvd
      exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
    · exact absurd (Subgroup.eq_of_le_of_card_ge hCK.le (by rw [h, hCcard])) hCK.ne
    · exfalso
      rw [h] at hdvd
      omega
    · exfalso
      rw [h] at hdvd
      exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  exact centMaxProp_of_data hS₀2 hS₀i hz2 hcen hmax

end CFSG.Quasithin
