module

public import CFSG.Quasithin.EmptyFaithful.S153YA5Thomp
public import CFSG.Quasithin.EmptyFaithful.S153YA5Cfg
public import CFSG.Quasithin.EmptyFaithful.S153YGBound
public import CFSG.Quasithin.EmptyFaithful.S153UMain

public section

namespace CFSG.Quasithin.YG

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem gmate_of_zpowers {H S : Subgroup G} {ρ : G} (hρN : ρ ∈ Subgroup.normalizer (S : Set G))
    (hρS : ρ ∉ S) (hρ2 : ρ ^ 2 ∈ S)
    (hb : ∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → H ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) :
    AppD.GMate H S (S ⊔ Subgroup.zpowers ρ) ρ := by
  have hρM : ρ ∈ S ⊔ Subgroup.zpowers ρ := Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ)
  refine ⟨le_sup_left, ?_, S153U.relIndex_sup_zpowers hρN hρS hρ2, hρM, hρS⟩
  intro X hXS hX1 hHX hMX
  exact hρS (hb X hXS hX1 hHX ⟨hρM, hMX hρM⟩)

theorem card_le_a5_single {I S Iz K : Subgroup G} {ρ : G} (hmp : MinParabolic I S Iz) (hchar : CharTwo I)
    (hblk : IsChi0Block I K) (h5 : IsAltType K 5) (hSN : S ≤ Subgroup.normalizer (K : Set G))
    (hI : I = S ⊔ K) (hρN : ρ ∈ Subgroup.normalizer (S : Set G)) (hρS : ρ ∉ S) (hρ2 : ρ ^ 2 ∈ S)
    (hb : ∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) :
    Nat.card S ≤ 2 ^ 9 := by
  have m := gmate_of_zpowers hρN hρS hρ2 hb
  have hM₀N : S ⊔ Subgroup.zpowers ρ ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hρN)
  have hth : ⁅K, thompsonJ S⁆ = K :=
    commutator_thompsonJ_eq_single hmp.isSylow hblk.1.1 h5 hSN hI hM₀N m.hC52
  have hj : conjJoin S K = K := C56.conjJoin_eq_of_le_normalizer hSN
  have hcs : WGen I S K :=
    ⟨hchar, hmp.isSylow, hblk, hth, by rw [hj, hI, sup_comm],
      Or.inl hj, minParabolic_exists_iff.1 ⟨Iz, hmp⟩⟩
  obtain ⟨C⟩ := AppC.nonempty_cfg hcs hj h5
  exact m.card_S_le (AppD.GCfg.ofCfg C)

end CFSG.Quasithin.YG
