module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocGeomD
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocCollapse2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocX1

public section

namespace CFSG.Quasithin.H13.F431.U42

variable {G : Type} [Group G] (D : GeomData G)

namespace GeomData

theorem comm_t {x : G} (hx : x ∈ D.V2) : x * D.t = D.t * x := D.hVab x hx D.t D.ht

theorem mem_H {x : G} (hx : x ∈ D.V2) : x ∈ Subgroup.centralizer ({D.t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 (D.comm_t hx)

theorem mem_normalizer_of_pt {u h : G} (hu : D.Pt u) (huV : u ∈ D.V2) (hh : h * D.t = D.t * h)
    (hu' : h * u * h⁻¹ ∈ D.V2) : h ∈ Subgroup.normalizer (D.V2 : Set G) := by
  have hht : h * D.t * h⁻¹ = D.t := by rw [hh]; group
  have hcomm : (h * u * h⁻¹) * D.t = D.t * (h * u * h⁻¹) := D.comm_t hu'
  have hconj : D.V2 = D.V2.map (MulAut.conj h).toMonoidHom := by
    refine D.line_unique (h * u * h⁻¹) (D.hPt h u hu) hcomm D.V2 _ D.hLnV (D.hLn h D.V2 D.hLnV)
      hu' D.ht ?_ ?_
    · exact ⟨u, huV, rfl⟩
    · exact ⟨D.t, D.ht, hht⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hconj]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [hconj] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h2 : h * y * h⁻¹ = h * x * h⁻¹ := hyx
      exact mul_left_cancel (mul_right_cancel h2)
    rwa [← this]

theorem ne_one_t : D.t ≠ 1 := by
  intro h
  apply D.hnPt0
  rw [h, mul_one]
  exact D.hPt0

theorem card_zpowers_t : Nat.card (Subgroup.zpowers D.t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact D.ht2) D.ne_one_t

theorem conj_t {h : G} (hh : h ∈ Subgroup.centralizer ({D.t} : Set G)) : h * D.t * h⁻¹ = D.t := by
  have := Subgroup.mem_centralizer_singleton_iff.1 hh
  rw [this]
  group

theorem normalizer_of_comm {u : G} (hPtu : D.Pt u) (huV : u ∈ D.V2) (hnp : ¬ D.Pt (u * D.t))
    {h : G} (hh : h ∈ Subgroup.centralizer ({D.t} : Set G))
    (hmem : h * u * h⁻¹ * u⁻¹ ∈ Subgroup.zpowers D.t) :
    h ∈ Subgroup.normalizer (D.V2 : Set G) := by
  have hht : h * D.t = D.t * h := Subgroup.mem_centralizer_singleton_iff.1 hh
  rcases mem_zpowers_two D.ht2 hmem with h1 | h1
  · have : h * u * h⁻¹ = u := by
      calc h * u * h⁻¹ = (h * u * h⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [h1, one_mul]
    exact D.mem_normalizer_of_pt hPtu huV hht (by rw [this]; exact huV)
  · exfalso
    have : h * u * h⁻¹ = u * D.t := by
      calc h * u * h⁻¹ = (h * u * h⁻¹ * u⁻¹) * u := by group
        _ = D.t * u := by rw [h1]
        _ = u * D.t := (D.comm_t huV).symm
    apply hnp
    rw [← this]
    exact D.hPt h u hPtu

theorem comm_conj {h : G} (hh : h ∈ Subgroup.centralizer ({D.t} : Set G)) {x : G}
    (hx : x ∈ D.V2) : (h * x * h⁻¹) * D.t = D.t * (h * x * h⁻¹) := by
  have hht := D.conj_t hh
  calc h * x * h⁻¹ * D.t = h * x * h⁻¹ * (h * D.t * h⁻¹) := by rw [hht]
    _ = h * (x * D.t) * h⁻¹ := by group
    _ = h * (D.t * x) * h⁻¹ := by rw [D.comm_t hx]
    _ = (h * D.t * h⁻¹) * (h * x * h⁻¹) := by group
    _ = D.t * (h * x * h⁻¹) := by rw [hht]

end GeomData

variable [Finite G]

theorem GeomData.centralizer_le_normalizer :
    Subgroup.centralizer ({D.t} : Set G) ≤ Subgroup.normalizer (D.V2 : Set G) := by
  have hz : ∀ x ∈ Subgroup.zpowers D.t, x = 1 ∨ x = D.t := fun x hx =>
    mem_zpowers_two D.ht2 hx
  have hmemH : ∀ x ∈ D.V2, x ∈ Subgroup.centralizer ({D.t} : Set G) := fun x hx => D.mem_H hx
  have hNc : ∀ n ∈ Subgroup.zpowers D.t, ∀ h ∈ Subgroup.centralizer ({D.t} : Set G),
      n * h = h * n := by
    intro n hn h hh
    rcases hz n hn with rfl | rfl
    · simp
    · exact (Subgroup.mem_centralizer_singleton_iff.1 hh).symm
  have huN : D.u15 ∉ Subgroup.zpowers D.t := by
    intro hu
    rcases hz _ hu with h | h
    · exact D.hu15ne h
    · apply D.hnPt
      rw [← h]
      exact D.hPt15
  have huc : ∀ q ∈ D.Q, q * D.u15 * q⁻¹ * D.u15⁻¹ ∈ Subgroup.zpowers D.t := by
    intro q hq
    rcases D.hQact q hq with h | h
    · rw [h]
      simp
    · rw [h]
      have : D.u15 * D.t * D.u15⁻¹ = D.t := by
        rw [D.comm_t D.hu15]
        group
      rw [this]
      exact Subgroup.mem_zpowers D.t
  have hU1 : ∀ h ∈ Subgroup.centralizer ({D.t} : Set G), h * D.u15 * h⁻¹ * D.u15⁻¹ ∈
      Subgroup.zpowers D.t → h ∈ Subgroup.normalizer (D.V2 : Set G) := by
    intro h hh hmem
    have hht : h * D.t = D.t * h := Subgroup.mem_centralizer_singleton_iff.1 hh
    have hu' : h * D.u15 * h⁻¹ ∈ D.V2 := by
      rcases hz _ hmem with h1 | h1
      · have : h * D.u15 * h⁻¹ = D.u15 := by
          calc h * D.u15 * h⁻¹ = (h * D.u15 * h⁻¹ * D.u15⁻¹) * D.u15 := by group
            _ = D.u15 := by rw [h1, one_mul]
        rw [this]
        exact D.hu15
      · have : h * D.u15 * h⁻¹ = D.t * D.u15 := by
          calc h * D.u15 * h⁻¹ = (h * D.u15 * h⁻¹ * D.u15⁻¹) * D.u15 := by group
            _ = D.t * D.u15 := by rw [h1]
        rw [this]
        exact D.V2.mul_mem D.ht D.hu15
    exact D.mem_normalizer_of_pt D.hPt15 D.hu15 hht hu'
  have hU3 : ∀ h ∈ Subgroup.centralizer ({D.t} : Set G), h * D.u15 * h⁻¹ ∈ D.Q →
      h * D.u15 * h⁻¹ * D.u15⁻¹ ∈ Subgroup.zpowers D.t := by
    intro h hh hq
    have hht : h * D.t = D.t * h := Subgroup.mem_centralizer_singleton_iff.1 hh
    have hht' := D.conj_t hh
    have hu'V : h * D.u15 * h⁻¹ ∈ D.V2 :=
      D.line_comm D.u0 (h * D.u15 * h⁻¹) D.hPt0 (D.hPt h D.u15 D.hPt15) (D.comm_t D.hu0)
        (D.comm_conj hh D.hu15) (D.hQz _ hq).symm D.V2 D.hLnV D.hu0 D.ht
    have hn := D.mem_normalizer_of_pt D.hPt15 D.hu15 hht hu'V
    rcases D.hXact h hn hht' with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      have : D.u15 * D.t * D.u15⁻¹ = D.t := by
        rw [D.comm_t D.hu15]
        group
      rw [this]
      exact Subgroup.mem_zpowers D.t
  have hUab : ∀ h ∈ Subgroup.centralizer ({D.t} : Set G),
      h * (D.u0 * D.u20) * h⁻¹ * (D.u0 * D.u20)⁻¹ ∈ Subgroup.zpowers D.t →
      h ∈ Subgroup.normalizer (D.V2 : Set G) := by
    intro h hh hmem
    have hht' := D.conj_t hh
    rw [D.hrel] at hmem
    refine D.normalizer_of_comm D.hPt24 D.hu24 D.hnPt24 hh ?_
    have : h * (D.u24 * D.t) * h⁻¹ * (D.u24 * D.t)⁻¹ = h * D.u24 * h⁻¹ * D.u24⁻¹ := by
      calc h * (D.u24 * D.t) * h⁻¹ * (D.u24 * D.t)⁻¹
          = h * D.u24 * h⁻¹ * (h * D.t * h⁻¹) * D.t⁻¹ * D.u24⁻¹ := by group
        _ = h * D.u24 * h⁻¹ * D.u24⁻¹ := by rw [hht']; group
    rwa [this] at hmem
  have key := collapse' (Subgroup.centralizer ({D.t} : Set G)) (Subgroup.zpowers D.t)
    (Subgroup.normalizer (D.V2 : Set G)) D.Q ((Subgroup.zpowers_le).2 (D.mem_H D.ht)) hNc
    D.card_zpowers_t ((Subgroup.zpowers_le).2 (Subgroup.le_normalizer D.ht))
    ((Subgroup.zpowers_le).2 D.htQ) D.hQH D.hQp D.hQm D.u15 D.u0 D.u20 (hmemH _ D.hu15)
    (hmemH _ D.hu0) (hmemH _ D.hu20) D.hu15sq huN D.hu15Q huc hU1 hU3 D.hu0sq D.hu20sq
    (fun h hh hmem => D.normalizer_of_comm D.hPt0 D.hu0 D.hnPt0 hh hmem)
    (fun h hh hmem => D.normalizer_of_comm D.hPt20 D.hu20 D.hnPt20 hh hmem) hUab D.hX1
  exact fun h hh => key h hh

end CFSG.Quasithin.H13.F431.U42
