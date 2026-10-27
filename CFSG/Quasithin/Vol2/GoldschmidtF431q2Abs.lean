module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2NF

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

structure G2Data (G : Type) [Group G] (z : G) (T Q Tp : Subgroup G) : Prop where
  z_ne : z ≠ 1
  z_sq : z * z = 1
  T_syl : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G))
  T_card : Nat.card T = 64
  T_Z : ∀ w ∈ T, (∀ t ∈ T, t * w = w * t) → w = 1 ∨ w = z
  T_N : ∀ h ∈ Subgroup.centralizer ({z} : Set G), (∀ t ∈ T, h * t * h⁻¹ ∈ T) →
    (∀ t ∈ T, h⁻¹ * t * h ∈ T) → h ∈ T
  Q_le : Q ≤ T
  Q_card : Nat.card Q = 32
  Q_norm : ∀ h ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ Q, h * q * h⁻¹ ∈ Q
  Q_comm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z
  Q_Z : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = z
  Q_nonab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x
  Tp_le : Tp ≤ T
  Tp_card : Nat.card T = 2 * Nat.card Tp
  z_mem : z ∈ Tp
  Tp_norm : ∀ h ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ Q, (q ∈ Tp ↔ h * q * h⁻¹ ∈ Tp)
  Tp_conj : ∀ w ∈ Tp, w * w = 1 → w ≠ 1 → IsConj z w
  out_ex : ∃ v ∈ Q, v ∉ Tp ∧ v * v = 1
  out_pair : ∀ v ∈ Q, v ∉ Tp → v * v = 1 →
    ∃ a ∈ Q, ∃ b ∈ Q, a * v = v * a ∧ b * v = v * b ∧ a * b * a⁻¹ * b⁻¹ = z
  out_t : ∀ v ∈ Q, v ∉ Tp → v * v = 1 →
    ∃ t ∈ T, t * v * t⁻¹ * v⁻¹ ≠ 1 ∧ t * v * t⁻¹ * v⁻¹ ≠ z

namespace G2Data

variable {G : Type} [Group G] {z : G} {T Q Tp : Subgroup G}

theorem false_of_simple [Finite G] [IsSimpleGroup G] (D : G2Data G z T Q Tp) : False := by
  obtain ⟨v, hvQ, hvTp, hv2⟩ := D.out_ex
  have hTsyl : IsSylowTwoOf T ⊤ := isSylowTwoOf_top D.z_ne D.z_sq D.T_syl D.T_Z D.T_N
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨x, -, y, -, hxy⟩ := D.Q_nonab
    exact ⟨x, y, hxy⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_of_simple hTsyl D.Tp_le D.Tp_card (D.Q_le hvQ) hvTp hv2 hnab
  have hw2 : (g⁻¹ * v * g) * (g⁻¹ * v * g) = 1 := by
    calc (g⁻¹ * v * g) * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
      _ = 1 := by rw [hv2]; group
  have hw1 : g⁻¹ * v * g ≠ 1 := by
    intro h1
    apply hvTp
    have : v = 1 := by
      calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this]
    exact Tp.one_mem
  have hzw := D.Tp_conj _ hg hw2 hw1
  have hwv : IsConj (g⁻¹ * v * g) v := isConj_iff.2 ⟨g, by group⟩
  have hzv : IsConj z v := hzw.trans hwv
  have hvne : v ≠ z := fun h => hvTp (h ▸ D.z_mem)
  refine not_isConj_of_nf (O := fun v => v ∈ Q ∧ v ∉ Tp ∧ v * v = 1) D.z_sq D.z_ne D.T_syl
    D.Q_le D.T_card D.Q_card D.Q_norm D.Q_comm
    (fun A hAQ hA => card_abelian_le_eight D.Q_card D.Q_comm D.Q_Z hAQ hA) ?_ ?_
    ⟨hvQ, hvTp, hv2⟩ hvQ hvne
    (D.out_pair v hvQ hvTp hv2) hzv
  · rintro h hh w ⟨hwQ, hwTp, hw2⟩
    refine ⟨D.Q_norm h hh w hwQ, fun hmem => hwTp ((D.Tp_norm h hh w hwQ).2 hmem), ?_⟩
    calc h * w * h⁻¹ * (h * w * h⁻¹) = h * (w * w) * h⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  · rintro w ⟨hwQ, hwTp, hw2⟩
    exact D.out_t w hwQ hwTp hw2

end G2Data

end CFSG.Quasithin.H13.F431.G2Two
