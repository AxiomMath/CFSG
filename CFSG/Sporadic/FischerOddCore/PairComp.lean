module

public import CFSG.Sporadic.FischerOddCore.Fi22LocalComp

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG CFSG.LocalCores

section Pair

variable {G : Type*} [Group G] {d d1 : G}

theorem conj_d1_of_pair (hd : d * d = 1) (hd1 : d1 * d1 = 1) (hcomm : d * d1 = d1 * d)
    {c : G} (hc : c * (d * d1) = d * d1 * c) :
    (c * d * c⁻¹ = d → c * d1 * c⁻¹ = d1) ∧ (c * d * c⁻¹ = d1 → c * d1 * c⁻¹ = d) := by
  have e1 : d1 = d * (d * d1) := by rw [← mul_assoc, hd, one_mul]
  have key : c * d1 * c⁻¹ = c * d * c⁻¹ * (d * d1) := by
    calc c * d1 * c⁻¹ = c * (d * (d * d1)) * c⁻¹ := by rw [← e1]
      _ = c * d * c⁻¹ * (c * (d * d1) * c⁻¹) := by group
      _ = c * d * c⁻¹ * (d * d1) := by rw [hc, mul_inv_cancel_right]
  refine ⟨fun h => by rw [key, h, ← e1], fun h => ?_⟩
  rw [key, h, ← mul_assoc, ← hcomm, mul_assoc, hd1, mul_one]

open scoped Classical in
@[expose] def pairSign (hd : d * d = 1) (hd1 : d1 * d1 = 1) (hcomm : d * d1 = d1 * d)
    (hne : d ≠ d1)
    (huniq : ∀ c : G, c * (d * d1) = d * d1 * c → c * d * c⁻¹ = d ∨ c * d * c⁻¹ = d1) :
    ↥(Subgroup.centralizer ({d * d1} : Set G)) →* ℤˣ where
  toFun c := if (c : G) * d * (c : G)⁻¹ = d then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    have e : ((x * y : ↥(Subgroup.centralizer ({d * d1} : Set G))) : G) * d *
        ((x * y : ↥(Subgroup.centralizer ({d * d1} : Set G))) : G)⁻¹ =
        (x : G) * ((y : G) * d * (y : G)⁻¹) * (x : G)⁻¹ := by
      rw [Subgroup.coe_mul]
      group
    rw [e]
    rcases huniq y hy with hy' | hy'
    · rw [hy', ite_eq_left (rfl : d = d), mul_one]
    · rw [hy', ite_eq_right (fun h : d1 = d => hne h.symm)]
      rcases huniq x hx with hx' | hx'
      · rw [(conj_d1_of_pair hd hd1 hcomm hx).1 hx', ite_eq_right (fun h : d1 = d => hne h.symm),
          ite_eq_left hx']
        simp
      · have hxd : ¬ (x : G) * d * (x : G)⁻¹ = d := fun h => hne (h.symm.trans hx')
        rw [(conj_d1_of_pair hd hd1 hcomm hx).2 hx', ite_eq_left (rfl : d = d), ite_eq_right hxd]
        simp

theorem commute_of_perfect_pair (hd : d * d = 1) (hd1 : d1 * d1 = 1) (hcomm : d * d1 = d1 * d)
    (hne : d ≠ d1)
    (huniq : ∀ c : G, c * (d * d1) = d * d1 * c → c * d * c⁻¹ = d ∨ c * d * c⁻¹ = d1)
    {B : Subgroup ↥(Subgroup.centralizer ({d * d1} : Set G))} (hB : Group.IsPerfect B)
    {b : ↥(Subgroup.centralizer ({d * d1} : Set G))} (hb : b ∈ B) :
    (b : G) * d = d * (b : G) := by
  classical
  have hmem : (⟨b, hb⟩ : B) ∈ commutator B := by
    rw [hB.commutator_eq_top]
    exact Subgroup.mem_top _
  have h := Abelianization.commutator_subset_ker
    ((pairSign hd hd1 hcomm hne huniq).comp B.subtype) hmem
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
  change (if (b : G) * d * (b : G)⁻¹ = d then (1 : ℤˣ) else -1) = 1 at h
  by_cases hbd : (b : G) * d * (b : G)⁻¹ = d
  · calc (b : G) * d = (b : G) * d * (b : G)⁻¹ * (b : G) := by group
      _ = d * (b : G) := by rw [hbd]
  · rw [ite_eq_right hbd] at h
    exact absurd h (by decide)

theorem card_quotient_center_of_component_pair [Finite G] {Q : Type*} [Group Q]
    (hd : d * d = 1) (hd1 : d1 * d1 = 1) (hcomm : d * d1 = d1 * d) (hne : d ≠ d1)
    (huniq : ∀ c : G, c * (d * d1) = d * d1 * c → c * d * c⁻¹ = d ∨ c * d * c⁻¹ = d1)
    (ρ : ↥(Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {d1}) →* Q)
    (hρ : Function.Surjective ρ) (hρk : ∀ u, ρ u = 1 → u * u * (u * u) = 1)
    (hQs : IsSimpleGroup Q) (hQnc : ∃ a b : Q, a * b ≠ b * a)
    {B : Subgroup ↥(Subgroup.centralizer ({d * d1} : Set G))} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = Nat.card Q := by
  have hp : IsPGroup 2 ρ.ker := fun g => ⟨2, by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, sq, sq]
    exact hρk g (MonoidHom.mem_ker.1 g.2)⟩
  have hker : Group.IsSolvable ρ.ker := @IsNilpotent.to_isSolvable _ _ hp.isNilpotent
  let W : Subgroup ↥(Subgroup.centralizer ({d * d1} : Set G)) :=
    (Subgroup.centralizer ({d} : Set G)).comap (Subgroup.centralizer ({d * d1} : Set G)).subtype
  have hBW : B ≤ W := fun b hb => by
    show (b : G) ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_perfect_pair hd hd1 hcomm hne huniq hB.1.1 hb
  have hd1e : d1 = d * (d * d1) := by rw [← mul_assoc, hd, one_mul]
  have φ : ↥W ≃* ↥(Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {d1}) :=
    { toFun := fun w => ⟨(w : G), Subgroup.mem_inf.2 ⟨w.2, by
        have h1 : (w : G) * d = d * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 w.2
        have h2 : (w : G) * (d * d1) = d * d1 * (w : G) :=
          Subgroup.mem_centralizer_singleton_iff.1 w.1.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (w : G) * d1 = (w : G) * (d * (d * d1)) := by rw [← hd1e]
          _ = (w : G) * d * (d * d1) := by group
          _ = d * (w : G) * (d * d1) := by rw [h1]
          _ = d * ((w : G) * (d * d1)) := by group
          _ = d * (d * d1 * (w : G)) := by rw [h2]
          _ = d * (d * d1) * (w : G) := by group
          _ = d1 * (w : G) := by rw [← hd1e]⟩⟩
      invFun := fun u => ⟨⟨u, by
        obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 u.2
        rw [Subgroup.mem_centralizer_singleton_iff] at h1 h2 ⊢
        calc (u : G) * (d * d1) = (u : G) * d * d1 := by group
          _ = d * (u : G) * d1 := by rw [h1]
          _ = d * ((u : G) * d1) := by group
          _ = d * (d1 * (u : G)) := by rw [h2]
          _ = d * d1 * (u : G) := by group⟩, (Subgroup.mem_inf.1 u.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  rw [card_quotient_center_mulEquiv (Subgroup.subgroupOfEquivOfLe hBW).symm]
  exact card_quotient_center_of_component_of_equiv φ ρ hρ hker hQs hQnc
    (component_overgroup hB hBW)

theorem exists_hom_inf_centralizer {F Q : Type*} [Group F] [Group Q] (hd : d * d = 1)
    (hd1c : d1 ∈ Subgroup.centralizer ({d} : Set G))
    (κ : ↥(Subgroup.centralizer ({d} : Set G)) →* F) (hκ : Function.Surjective κ)
    (hkerκ : ∀ c, κ c = 1 → (c : G) = 1 ∨ (c : G) = d)
    (hnd : ∀ c : G, c * d1 * c⁻¹ ≠ d * d1) {a : F} (ha : IsConj a (κ ⟨d1, hd1c⟩))
    (ψ : ↥(Subgroup.centralizer ({a} : Set F)) →* Q) (hψ : Function.Surjective ψ)
    (hkerψ : ∀ y, ψ y = 1 → y * y = 1) :
    ∃ ρ : ↥(Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {d1}) →* Q,
      Function.Surjective ρ ∧ ∀ u, ρ u = 1 → u * u * (u * u) = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ha
  set f1 := κ ⟨d1, hd1c⟩
  let incl : ↥(Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {d1}) →*
      ↥(Subgroup.centralizer ({d} : Set G)) :=
    Subgroup.inclusion inf_le_left
  have hcomm_f1 : ∀ u, κ (incl u) * f1 = f1 * κ (incl u) := fun u => by
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 u.2).2
    have : incl u * ⟨d1, hd1c⟩ = ⟨d1, hd1c⟩ * incl u := Subtype.ext h2
    rw [← map_mul, this, map_mul]
  have hconj : ∀ y : F, y * f1 = f1 * y → g⁻¹ * y * g ∈ Subgroup.centralizer ({a} : Set F) :=
    fun y hy => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [hg, hy]
        _ = a * (g⁻¹ * y * g) := by group
  let θ : ↥(Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {d1}) →*
      ↥(Subgroup.centralizer ({a} : Set F)) :=
    { toFun := fun u => ⟨g⁻¹ * κ (incl u) * g, hconj _ (hcomm_f1 u)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }
  refine ⟨ψ.comp θ, ?_, ?_⟩
  · intro q
    obtain ⟨y, rfl⟩ := hψ q
    obtain ⟨c, hc⟩ := hκ (g * y * g⁻¹)
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    have hcf : κ c * f1 = f1 * κ c := by
      rw [hc, ← hg]
      calc g * ↑y * g⁻¹ * (g * a * g⁻¹) = g * (↑y * a) * g⁻¹ := by group
        _ = g * (a * ↑y) * g⁻¹ := by rw [hy]
        _ = g * a * g⁻¹ * (g * ↑y * g⁻¹) := by group
    have hk : κ (c * ⟨d1, hd1c⟩ * c⁻¹ * (⟨d1, hd1c⟩ : ↥(Subgroup.centralizer ({d} : Set G)))⁻¹) =
        1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcf, mul_inv_cancel_right, mul_inv_cancel]
    have hcd1 : (c : G) * d1 = d1 * (c : G) := by
      rcases hkerκ _ hk with h | h
      · have h' : (c : G) * d1 * (c : G)⁻¹ * d1⁻¹ = 1 := by simpa using h
        calc (c : G) * d1 = (c : G) * d1 * (c : G)⁻¹ * d1⁻¹ * (d1 * (c : G)) := by group
          _ = d1 * (c : G) := by rw [h', one_mul]
      · exfalso
        have h' : (c : G) * d1 * (c : G)⁻¹ * d1⁻¹ = d := by simpa using h
        apply hnd c
        calc (c : G) * d1 * (c : G)⁻¹ = (c : G) * d1 * (c : G)⁻¹ * d1⁻¹ * d1 := by group
          _ = d * d1 := by rw [h']
    refine ⟨⟨c, Subgroup.mem_inf.2 ⟨c.2, Subgroup.mem_centralizer_singleton_iff.2 hcd1⟩⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    show g⁻¹ * κ (incl _) * g = (y : F)
    have : incl ⟨c, Subgroup.mem_inf.2 ⟨c.2, Subgroup.mem_centralizer_singleton_iff.2 hcd1⟩⟩ =
        c := rfl
    rw [this, hc]
    group
  · intro u hu
    rw [MonoidHom.comp_apply] at hu
    have h1 := hkerψ _ hu
    have h1' : g⁻¹ * κ (incl u) * g * (g⁻¹ * κ (incl u) * g) = 1 := congrArg Subtype.val h1
    have h2 : κ (incl (u * u)) = 1 := by
      rw [map_mul, map_mul]
      calc κ (incl u) * κ (incl u) =
          g * (g⁻¹ * κ (incl u) * g * (g⁻¹ * κ (incl u) * g)) * g⁻¹ := by group
        _ = 1 := by rw [h1']; group
    have h3 : ((incl (u * u) : ↥(Subgroup.centralizer ({d} : Set G))) : G) * (incl (u * u) : G) =
        1 := by
      rcases hkerκ _ h2 with h | h
      · rw [h, one_mul]
      · rw [h, hd]
    apply Subtype.ext
    simpa [incl, mul_assoc] using h3

end Pair

end CFSG.Sporadic.FischerOddCore
