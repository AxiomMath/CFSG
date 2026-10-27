module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CardZvSq
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem index_two_coset {T N : Subgroup G} (hidx : (N.subgroupOf T).index = 2)
    {x : G} (hx : x ∈ T) (hxN : x ∉ N) :
    (∀ t ∈ T, t ∉ N → x⁻¹ * t ∈ N) ∧ x ^ 2 ∈ N := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp hidx
  have key : ∀ u ∈ T, u ∉ N → (a : G) * u ∈ N := by
    intro u hu huN
    have h := ha ⟨u, hu⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h
    rcases h with h | h
    · exact h.1
    · exact absurd h.1 huN
  have hxa : (a : G) * x ∈ N := key x hx hxN
  have hcos : ∀ t ∈ T, t ∉ N → x⁻¹ * t ∈ N := by
    intro t ht htN
    have h2 := N.mul_mem (N.inv_mem hxa) (key t ht htN)
    have e : ((a : G) * x)⁻¹ * ((a : G) * t) = x⁻¹ * t := by group
    rwa [e] at h2
  refine ⟨hcos, ?_⟩
  have hx'T : x⁻¹ ∈ T := T.inv_mem hx
  have hx'N : x⁻¹ ∉ N := fun h => hxN (by simpa using N.inv_mem h)
  have h3 := N.inv_mem (hcos x⁻¹ hx'T hx'N)
  simpa [pow_two] using h3

theorem comm_Zv_comm {H M S : Subgroup G} (hA : F53Amalgam H M S) (μ : Geo H M) :
    ∀ a ∈ Zv μ, ∀ b ∈ Zv μ, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val ((isElemAbelian_Zv hA μ).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem comm_Zv_into {H M S : Subgroup G} (hA : F53Amalgam H M S) {β μ : Geo H M}
    (hβ : vtype β = false) (hμ : μ ∈ nbrs β) (hz : Zv β ≤ centerOf (stab β))
    {x : G} (hx : x ∈ stab μ ⊓ stab β) (hxQ : x ∉ Qv μ) :
    ∀ y ∈ Zv μ, x * y * x⁻¹ * y⁻¹ ∈ Zv β := by
  have hβμ' : (graph (H ⊔ M) H M).Adj β μ := hμ
  have hadj : (graph (H ⊔ M) H M).Adj μ β := hβμ'.symm
  have hvμ : vtype μ = true := by
    have h := vtype_ne_of_adj hβμ'
    rw [hβ] at h
    generalize vtype μ = b at h ⊢
    cases b <;> simp_all
  have hβμ : β ∈ nbrs μ := hadj
  have hidx : ((Qv μ).subgroupOf (stab μ ⊓ stab β)).index = 2 :=
    relIndex_Qv_inf_true hA hβμ hvμ
  obtain ⟨hgen, hx2⟩ := index_two_coset hidx hx hxQ
  have hAeq : Zv μ ⊓ Subgroup.centralizer ((stab μ ⊓ stab β : Subgroup G) : Set G) = Zv β :=
    Zv_inf_centralizer_edge_eq hA hadj hz
  have hQc : ∀ q ∈ Qv μ, ∀ z ∈ Zv μ, q * z = z * q := fun q hq z hz' =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz').2 q hq
  have hsq : ∀ c ∈ Zv μ, c * c = 1 := fun c hc => by
    rw [← pow_two]; exact (isElemAbelian_Zv hA μ).2 c hc
  have hnorm : ∀ y ∈ Zv μ, x * y * x⁻¹ ∈ Zv μ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA μ hx.1) y).mp hy
  have hcZv : ∀ y ∈ Zv μ, x * y * x⁻¹ * y⁻¹ ∈ Zv μ := fun y hy =>
    Subgroup.mul_mem _ (hnorm y hy) (Subgroup.inv_mem _ hy)
  intro y hy
  have hc : x * y * x⁻¹ * y⁻¹ ∈ Zv μ := hcZv y hy
  have hxc' : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    have hx2y : x * x * y = y * (x * x) := by
      have h := hQc _ hx2 y hy
      rwa [pow_two] at h
    calc x * (x * y * x⁻¹ * y⁻¹) * x⁻¹
        = (x * x * y) * x⁻¹ * y⁻¹ * x⁻¹ := by group
      _ = (y * (x * x)) * x⁻¹ * y⁻¹ * x⁻¹ := by rw [hx2y]
      _ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
  have hcinv : (x * y * x⁻¹ * y⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ :=
    (inv_eq_of_mul_eq_one_right (hsq _ hc))
  have hxc : x * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * x := by
    calc x * (x * y * x⁻¹ * y⁻¹)
        = (x * (x * y * x⁻¹ * y⁻¹) * x⁻¹) * x := by group
      _ = (x * y * x⁻¹ * y⁻¹) * x := by rw [hxc', hcinv]
  have hTc : ∀ t ∈ stab μ ⊓ stab β,
      t * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * t := by
    intro t ht
    by_cases htQ : t ∈ Qv μ
    · exact hQc t htQ _ hc
    · have hn := hgen t ht htQ
      have hnc : (x⁻¹ * t) * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * (x⁻¹ * t) :=
        hQc _ hn _ hc
      calc t * (x * y * x⁻¹ * y⁻¹)
          = x * ((x⁻¹ * t) * (x * y * x⁻¹ * y⁻¹)) := by group
        _ = x * ((x * y * x⁻¹ * y⁻¹) * (x⁻¹ * t)) := by rw [hnc]
        _ = (x * (x * y * x⁻¹ * y⁻¹)) * (x⁻¹ * t) := by group
        _ = ((x * y * x⁻¹ * y⁻¹) * x) * (x⁻¹ * t) := by rw [hxc]
        _ = (x * y * x⁻¹ * y⁻¹) * t := by group
  have hcZ : x * y * x⁻¹ * y⁻¹ ∈
      Zv μ ⊓ Subgroup.centralizer ((stab μ ⊓ stab β : Subgroup G) : Set G) :=
    ⟨hc, Subgroup.mem_centralizer_iff.mpr (fun t ht => hTc t ht)⟩
  rw [hAeq] at hcZ
  exact hcZ

theorem comm_Zv_ker {H M S : Subgroup G} (hA : F53Amalgam H M S) {β μ : Geo H M}
    (hβ : vtype β = false) (hμ : μ ∈ nbrs β) (hz : Zv β ≤ centerOf (stab β))
    {x : G} (hx : x ∈ stab μ ⊓ stab β) (hxQ : x ∉ Qv μ) :
    ∀ y ∈ Zv μ, x * y * x⁻¹ * y⁻¹ = 1 ↔ y ∈ Zv β := by
  have hβμ' : (graph (H ⊔ M) H M).Adj β μ := hμ
  have hadj : (graph (H ⊔ M) H M).Adj μ β := hβμ'.symm
  have hvμ : vtype μ = true := by
    have h := vtype_ne_of_adj hβμ'
    rw [hβ] at h
    generalize vtype μ = b at h ⊢
    cases b <;> simp_all
  have hβμ : β ∈ nbrs μ := hadj
  have hidx : ((Qv μ).subgroupOf (stab μ ⊓ stab β)).index = 2 :=
    relIndex_Qv_inf_true hA hβμ hvμ
  obtain ⟨hgen, -⟩ := index_two_coset hidx hx hxQ
  have hAeq : Zv μ ⊓ Subgroup.centralizer ((stab μ ⊓ stab β : Subgroup G) : Set G) = Zv β :=
    Zv_inf_centralizer_edge_eq hA hadj hz
  have hQc : ∀ q ∈ Qv μ, ∀ z ∈ Zv μ, q * z = z * q := fun q hq z hz' =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz').2 q hq
  intro y hy
  constructor
  · intro h
    have hxy : x * y = y * x := by
      have h' : x * y * x⁻¹ = y := mul_inv_eq_one.mp h
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [h']
    rw [← hAeq]
    refine ⟨hy, Subgroup.mem_centralizer_iff.mpr (fun t ht => ?_)⟩
    by_cases htQ : t ∈ Qv μ
    · exact hQc t htQ _ hy
    · have hn := hgen t ht htQ
      have hny : (x⁻¹ * t) * y = y * (x⁻¹ * t) := hQc _ hn _ hy
      calc t * y = x * ((x⁻¹ * t) * y) := by group
        _ = x * (y * (x⁻¹ * t)) := by rw [hny]
        _ = (x * y) * (x⁻¹ * t) := by group
        _ = (y * x) * (x⁻¹ * t) := by rw [hxy]
        _ = y * t := by group
  · intro hy'
    rw [← hAeq] at hy'
    have hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hy'.2) x hx
    calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [hxy]
      _ = 1 := by group

theorem comm_Zv_mul {H M S : Subgroup G} (hA : F53Amalgam H M S) {μ : Geo H M}
    {x : G} (hx : x ∈ stab μ) :
    ∀ a ∈ Zv μ, ∀ b ∈ Zv μ,
      x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by
  have hnorm : ∀ y ∈ Zv μ, x * y * x⁻¹ ∈ Zv μ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA μ hx) y).mp hy
  have hcZv : ∀ y ∈ Zv μ, x * y * x⁻¹ * y⁻¹ ∈ Zv μ := fun y hy =>
    Subgroup.mul_mem _ (hnorm y hy) (Subgroup.inv_mem _ hy)
  intro a ha b hb
  have hcomm' : (x * b * x⁻¹ * b⁻¹) * a⁻¹ = a⁻¹ * (x * b * x⁻¹ * b⁻¹) :=
    comm_Zv_comm hA μ _ (hcZv b hb) _ (Subgroup.inv_mem _ ha)
  calc x * (a * b) * x⁻¹ * (a * b)⁻¹
      = (x * a * x⁻¹) * ((x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    _ = (x * a * x⁻¹) * (a⁻¹ * (x * b * x⁻¹ * b⁻¹)) := by rw [hcomm']
    _ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group

theorem comm_Zv_hom {H M S : Subgroup G} (hA : F53Amalgam H M S) {μ : Geo H M}
    {x : G} (hx : x ∈ stab μ) :
    ∃ φ : ↥(Zv μ) →* G, ∀ y : ↥(Zv μ), φ y = x * y * x⁻¹ * y⁻¹ :=
  ⟨MonoidHom.mk' (fun y : ↥(Zv μ) => x * (y : G) * x⁻¹ * (y : G)⁻¹)
      (fun a b => by
        rw [Subgroup.coe_mul]
        exact comm_Zv_mul hA hx a a.2 b b.2),
    fun _ => rfl⟩

theorem range_eq_of_card_ker {A : Type} [Group A] [Finite A] (φ : A →* G) (S : Subgroup G)
    (hle : φ.range ≤ S) (hkerc : Nat.card φ.ker = Nat.card S)
    (hAc : Nat.card A = Nat.card S ^ 2) : φ.range = S := by
  have hsplit : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have : Nonempty S := ⟨1⟩
  have hn : 0 < Nat.card S := Nat.card_pos
  have hR : Nat.card φ.range = Nat.card S := by
    have h1 : Nat.card A = Nat.card φ.range * Nat.card S := by rw [hsplit, hkerc]
    have h2 : Nat.card S ^ 2 = Nat.card φ.range * Nat.card S := by rw [← hAc, h1]
    exact Nat.eq_of_mul_eq_mul_right hn (by rw [← h2]; ring)
  exact Subgroup.eq_of_le_of_card_ge hle hR.ge

omit [Finite G] in
theorem card_ker_eq_of_mem_iff {S T : Subgroup G} (φ : S →* G)
    (h : ∀ y : S, y ∈ φ.ker ↔ (y : G) ∈ T) (hT : T ≤ S) :
    Nat.card φ.ker = Nat.card T := by
  apply Nat.card_congr
  exact
    { toFun := fun y => ⟨(y.1 : G), (h y.1).mp y.2⟩
      invFun := fun g => ⟨⟨(g : G), hT g.2⟩, (h ⟨(g : G), hT g.2⟩).mpr g.2⟩
      left_inv := fun y => Subtype.ext (Subtype.ext rfl)
      right_inv := fun g => Subtype.ext rfl }

theorem comm_Zv_surj {H M S : Subgroup G} (hA : F53Amalgam H M S) {β μ : Geo H M}
    (hβ : vtype β = false) (hμ : μ ∈ nbrs β) (hz : Zv β ≤ centerOf (stab β))
    {x : G} (hx : x ∈ stab μ ⊓ stab β) (hxQ : x ∉ Qv μ) :
    (∀ y ∈ Zv μ, x * y * x⁻¹ * y⁻¹ ∈ Zv β) ∧
      ∀ z ∈ Zv β, ∃ y ∈ Zv μ, x * y * x⁻¹ * y⁻¹ = z := by
  have hβμ' : (graph (H ⊔ M) H M).Adj β μ := hμ
  have hadj : (graph (H ⊔ M) H M).Adj μ β := hβμ'.symm
  have hvμ : vtype μ = true := by
    have h := vtype_ne_of_adj hβμ'
    rw [hβ] at h
    generalize vtype μ = b at h ⊢
    cases b <;> first | rfl | exact absurd rfl h
  have hβμ : β ∈ nbrs μ := hadj
  have hAeq : Zv μ ⊓ Subgroup.centralizer ((stab μ ⊓ stab β : Subgroup G) : Set G) = Zv β :=
    Zv_inf_centralizer_edge_eq hA hadj hz
  have hZβμ : Zv β ≤ Zv μ := by rw [← hAeq]; exact inf_le_left
  obtain ⟨φ, hφ⟩ := comm_Zv_hom hA hx.1
  have hker : ∀ y : ↥(Zv μ), y ∈ φ.ker ↔ (y : G) ∈ Zv β := fun y => by
    rw [MonoidHom.mem_ker, hφ]
    exact comm_Zv_ker hA hβ hμ hz hx hxQ y y.2
  have hKcard : Nat.card φ.ker = Nat.card (Zv β) :=
    card_ker_eq_of_mem_iff φ hker hZβμ
  have hB : Nat.card ↥(Zv μ) = Nat.card ↥(Zv β) ^ 2 := card_Zv_eq_sq hA hvμ hadj hz
  have hinto := comm_Zv_into hA hβ hμ hz hx hxQ
  have hrange_le : φ.range ≤ Zv β := by
    intro g hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
    rw [hφ]
    exact hinto y y.2
  have hrange_eq : φ.range = Zv β :=
    range_eq_of_card_ker φ (Zv β) hrange_le hKcard hB
  refine ⟨hinto, fun z hz' => ?_⟩
  have hzR : z ∈ φ.range := by rw [hrange_eq]; exact hz'
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hzR
  exact ⟨y, y.2, (hφ y).symm.trans hy⟩

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
