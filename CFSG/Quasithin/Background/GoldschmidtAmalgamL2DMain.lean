module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DConj
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Sq

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2D

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem natural_cT_eq [Finite D] {H T : Subgroup D} {z : D} {V : Subgroup D}
    (hn : IsNaturalAt H T z V) : T ⊓ Subgroup.centralizer (V : Set D) = pCoreOf 2 H := by
  rw [hn.cT, hn.centralizer_eq, pCoreOf_eq_self_of_isPGroup (pCoreOf_isPGroup 2 H)]

theorem B2Setup.V'_le_QA [Finite D] (s : B2Setup A B z V) {z' : D} {V' : Subgroup D}
    (hn' : IsNaturalAt B (A ⊓ B) z' V') : V' ≤ pCoreOf 2 A := by
  intro v' hv'
  have hv'T : v' ∈ A ⊓ B := s.gold.pCoreOf_right_le (hn'.le_pCoreOf hv')
  have hc : v' ∈ Subgroup.centralizer (V : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hn'.le_center hv').2 w (s.V_le hw)
  rw [← natural_cT_eq s.natural]
  exact ⟨hv'T, hc⟩

theorem B2Setup.norm_ne_z [Finite D] (s : B2Setup A B z V) {ω x' z' : D}
    (hωZ : ω ∈ centerOf (A ⊓ B)) (hx'B : x' ∈ B) (hx'3 : x' * x' * x' = 1)
    (hx'ω : x' * ω * x'⁻¹ ≠ ω)
    (hz'def : z' = (x' * ω * x'⁻¹) * (x' * x' * ω * (x' * x')⁻¹)) : z' ≠ z := by
  intro hzz
  have hv := s.gold.vertex_right
  have hQN : B ≤ Subgroup.normalizer (pCoreOf 2 B : Set D) := le_normalizer_pCoreOf 2 B
  have hωQ : ω ∈ centerOf (pCoreOf 2 B) :=
    ⟨hv.centerOf_le hωZ, Subgroup.centralizer_le hv.pCoreOf_le hωZ.2⟩
  have heQ : x' * ω * x'⁻¹ ∈ centerOf (pCoreOf 2 B) := conj_mem_centerOf' (hQN hx'B) hωQ
  have he'Q : x' * x' * ω * (x' * x')⁻¹ ∈ centerOf (pCoreOf 2 B) := by
    have := conj_mem_centerOf' (hQN hx'B) heQ
    have e : x' * (x' * ω * x'⁻¹) * x'⁻¹ = x' * x' * ω * (x' * x')⁻¹ := by group
    rwa [e] at this
  have hcomm : x' * ω * x'⁻¹ * (x' * x' * ω * (x' * x')⁻¹) =
      x' * x' * ω * (x' * x')⁻¹ * (x' * ω * x'⁻¹) :=
    Subgroup.mem_centralizer_iff.mp he'Q.2 _ heQ.1
  have h1 : x' * z' * x'⁻¹ = (x' * x' * ω * (x' * x')⁻¹) * ω := by
    rw [hz'def]
    calc x' * ((x' * ω * x'⁻¹) * (x' * x' * ω * (x' * x')⁻¹)) * x'⁻¹
        = (x' * x' * ω * (x' * x')⁻¹) * ((x' * x' * x') * ω * (x' * x' * x')⁻¹) := by group
      _ = (x' * x' * ω * (x' * x')⁻¹) * ω := by rw [hx'3]; group
  have h2 : x' * z * x'⁻¹ = z := s.central x' hx'B
  rw [hzz] at h1 hz'def
  have h3 : (x' * x' * ω * (x' * x')⁻¹) * ω = (x' * ω * x'⁻¹) * (x' * x' * ω * (x' * x')⁻¹) := by
    rw [← h1, h2, hz'def]
  apply hx'ω
  have h4 : (x' * x' * ω * (x' * x')⁻¹) * ω =
      (x' * x' * ω * (x' * x')⁻¹) * (x' * ω * x'⁻¹) := by rw [h3, hcomm]
  exact (mul_left_cancel h4).symm

namespace Gen

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

variable [Finite D] in
theorem conj_u_mem_QB {z' : D} {V' : Subgroup D} (hn' : IsNaturalAt B (A ⊓ B) z' V')
    (hz' : z' ≠ z) {k : D} (hk : k ∈ A) : k * (a₁ * a₂) * k⁻¹ ∈ pCoreOf 2 B := by
  have s := g.setup
  have hV'QA := s.V'_le_QA hn'
  obtain ⟨a', ha'1, ha'z, hV'set⟩ := hn'.basis
  have ha'V' : a' ∈ V' := by
    have : a' ∈ (V' : Set D) := by rw [hV'set]; simp
    exact this
  have hqQA : k * (a₁ * a₂) * k⁻¹ ∈ pCoreOf 2 A :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hk) (a₁ * a₂)).mp g.u_mem_QA
  have hqT : k * (a₁ * a₂) * k⁻¹ ∈ A ⊓ B := s.gold.pCoreOf_left_le hqQA
  have hz'T : ∀ t ∈ A ⊓ B, t * z' = z' * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp hn'.z_mem.2 t ht
  have hqa : k * (a₁ * a₂) * k⁻¹ * a' * (k * (a₁ * a₂) * k⁻¹)⁻¹ = a' := by
    rcases hn'.conj_cases inf_le_right hqT ha'V' with h | h
    · exact h
    · exfalso
      have ha'QA : a' ∈ pCoreOf 2 A := hV'QA ha'V'
      have htQA : k⁻¹ * a' * k ∈ pCoreOf 2 A := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A (A.inv_mem hk)) a').mp
          ha'QA
        simpa using this
      have htT : k⁻¹ * a' * k ∈ A ⊓ B := s.gold.pCoreOf_left_le htQA
      have htB : k⁻¹ * a' * k ∈ B := htT.2
      have huB : a₁ * a₂ ∈ B := pCoreOf_le 2 B g.u_mem_QB
      have hu : a₁ * a₂ * (k⁻¹ * a' * k) * (a₁ * a₂)⁻¹ = (k⁻¹ * a' * k) * (k⁻¹ * z' * k) := by
        calc a₁ * a₂ * (k⁻¹ * a' * k) * (a₁ * a₂)⁻¹
            = k⁻¹ * (k * (a₁ * a₂) * k⁻¹ * a' * (k * (a₁ * a₂) * k⁻¹)⁻¹) * k := by group
          _ = k⁻¹ * (a' * z') * k := by rw [h]
          _ = (k⁻¹ * a' * k) * (k⁻¹ * z' * k) := by group
      have hzt : z * (k⁻¹ * a' * k) = (k⁻¹ * a' * k) * z := (s.z_comm htB).symm
      have hzu : z * (a₁ * a₂) = (a₁ * a₂) * z := (s.z_comm huB).symm
      have hz'1 : z' ≠ 1 := hn'.z_ne
      rcases g.conj_u htT with hc | hc
      ·
        have hcu : (k⁻¹ * a' * k) * (a₁ * a₂) = (a₁ * a₂) * (k⁻¹ * a' * k) := mul_eq_of_conj_eq hc
        have h1 : a₁ * a₂ * (k⁻¹ * a' * k) * (a₁ * a₂)⁻¹ = k⁻¹ * a' * k := by
          rw [← hcu]; group
        have h2 : (k⁻¹ * z' * k) = 1 := by
          have h3 : (k⁻¹ * a' * k) * (k⁻¹ * z' * k) = (k⁻¹ * a' * k) * 1 := by
            rw [← hu, h1, mul_one]
          exact mul_left_cancel h3
        apply hz'1
        calc z' = k * (k⁻¹ * z' * k) * k⁻¹ := by group
          _ = 1 := by rw [h2]; group
      ·
        have hzz := s.z_mul_z
        have e1 : (k⁻¹ * a' * k) * (a₁ * a₂) = z * ((a₁ * a₂) * (k⁻¹ * a' * k)) := by
          calc (k⁻¹ * a' * k) * (a₁ * a₂)
              = ((k⁻¹ * a' * k) * (a₁ * a₂) * (k⁻¹ * a' * k)⁻¹) * (k⁻¹ * a' * k) := by group
            _ = (z * (a₁ * a₂)) * (k⁻¹ * a' * k) := by rw [hc]
            _ = z * ((a₁ * a₂) * (k⁻¹ * a' * k)) := by group
        have e2 : (a₁ * a₂) * (k⁻¹ * a' * k) = z * ((k⁻¹ * a' * k) * (a₁ * a₂)) := by
          calc (a₁ * a₂) * (k⁻¹ * a' * k) = (z * z) * ((a₁ * a₂) * (k⁻¹ * a' * k)) := by
                rw [hzz, one_mul]
            _ = z * (z * ((a₁ * a₂) * (k⁻¹ * a' * k))) := by group
            _ = z * ((k⁻¹ * a' * k) * (a₁ * a₂)) := by rw [← e1]
        have h1 : a₁ * a₂ * (k⁻¹ * a' * k) * (a₁ * a₂)⁻¹ = z * (k⁻¹ * a' * k) := by
          calc a₁ * a₂ * (k⁻¹ * a' * k) * (a₁ * a₂)⁻¹
              = (z * ((k⁻¹ * a' * k) * (a₁ * a₂))) * (a₁ * a₂)⁻¹ := by rw [e2]
            _ = z * (k⁻¹ * a' * k) := by group
        have h2 : k⁻¹ * z' * k = z := by
          have h3 : (k⁻¹ * a' * k) * (k⁻¹ * z' * k) = (k⁻¹ * a' * k) * z := by
            rw [← hu, h1, hzt]
          exact mul_left_cancel h3
        have hz'eq : z' = k * z * k⁻¹ := by
          calc z' = k * (k⁻¹ * z' * k) * k⁻¹ := by group
            _ = k * z * k⁻¹ := by rw [h2]
        have hzV : z' ∈ V := by
          rw [hz'eq, s.natural.V_eq]
          exact mem_conjClosure hk (Subgroup.mem_zpowers z)
        have hmem : z' ∈ V ⊓ Subgroup.centralizer ((A ⊓ B : Subgroup D) : Set D) :=
          ⟨hzV, hn'.z_mem.2⟩
        rw [IsNaturalAt.inf_centralizer_eq_zpowers s.gold s.natural] at hmem
        rcases s.mem_zpowers hmem with h1 | h1
        · exact hz'1 h1
        · exact hz' h1
  have hqV' : k * (a₁ * a₂) * k⁻¹ ∈ Subgroup.centralizer (V' : Set D) := by
    have hqa' : k * (a₁ * a₂) * k⁻¹ * a' = a' * (k * (a₁ * a₂) * k⁻¹) := by
      calc k * (a₁ * a₂) * k⁻¹ * a' = (k * (a₁ * a₂) * k⁻¹ * a' * (k * (a₁ * a₂) * k⁻¹)⁻¹) *
            (k * (a₁ * a₂) * k⁻¹) := by group
        _ = a' * (k * (a₁ * a₂) * k⁻¹) := by rw [hqa]
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ ({1, z', a', z' * a'} : Set D) := by rw [← hV'set]; exact hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    rcases hw' with h | h | h | h <;> rw [h]
    · simp
    · exact (hz'T _ hqT).symm
    · exact hqa'.symm
    · calc z' * a' * (k * (a₁ * a₂) * k⁻¹) = z' * (a' * (k * (a₁ * a₂) * k⁻¹)) := by group
        _ = z' * (k * (a₁ * a₂) * k⁻¹ * a') := by rw [hqa']
        _ = (z' * (k * (a₁ * a₂) * k⁻¹)) * a' := by group
        _ = ((k * (a₁ * a₂) * k⁻¹) * z') * a' := by rw [← hz'T _ hqT]
        _ = k * (a₁ * a₂) * k⁻¹ * (z' * a') := by group
  rw [← natural_cT_eq hn']
  exact ⟨hqT, hqV'⟩

variable [Finite D] in
theorem false_of_conj_u_mem_QB (h : ∀ k ∈ A, k * (a₁ * a₂) * k⁻¹ ∈ pCoreOf 2 B) : False := by
  have s := g.setup
  have hconj : ∀ k ∈ A, (k * z * k⁻¹) * a₁ = a₁ * (k * z * k⁻¹) := by
    intro k hk
    have hsq : k * (a₁ * a₂) * k⁻¹ * (k * (a₁ * a₂) * k⁻¹) = k * z * k⁻¹ := by
      calc k * (a₁ * a₂) * k⁻¹ * (k * (a₁ * a₂) * k⁻¹) = k * (a₁ * a₂ * (a₁ * a₂)) * k⁻¹ := by
            group
        _ = k * z * k⁻¹ := by rw [g.u_sq]
    have := s.sq_comm (h k hk) g.a₁_mem_U
    calc (k * z * k⁻¹) * a₁ = (k * (a₁ * a₂) * k⁻¹ * (k * (a₁ * a₂) * k⁻¹)) * a₁ := by rw [hsq]
      _ = a₁ * (k * (a₁ * a₂) * k⁻¹) * (k * (a₁ * a₂) * k⁻¹) := this
      _ = a₁ * (k * (a₁ * a₂) * k⁻¹ * (k * (a₁ * a₂) * k⁻¹)) := by group
      _ = a₁ * (k * z * k⁻¹) := by rw [hsq]
  have hVc : V ≤ Subgroup.centralizer ({a₁} : Set D) := by
    rw [s.natural.V_eq]
    refine conjClosure_le fun k hk w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rcases s.mem_zpowers hw with hw1 | hw1
    · rw [hw1]; simp
    · rw [hw1]; exact (hconj k hk).symm
  have : a₁ * a = a * a₁ := Subgroup.mem_centralizer_iff.mp (hVc g.a_mem) a₁ (Set.mem_singleton a₁)
  exact g.not_comm01 this.symm

end Gen

variable [Finite D] in
theorem B2Setup.centralizes_omega (s : B2Setup A B z V) {ω : D}
    (hωZ : ω ∈ centerOf (A ⊓ B)) (hω2 : ω ^ 2 = 1) : ∀ y ∈ B, y * ω * y⁻¹ = ω := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀B, hy₀ω⟩ := hcon
  obtain ⟨x', z', V', hx'B, hx'3, hx'ω, hz'def, hn', -⟩ :=
    exists_natural_data s.gold.vertex_right hωZ hω2 ⟨y₀, hy₀B, hy₀ω⟩
  have hz' : z' ≠ z := s.norm_ne_z hωZ hx'B hx'3 hx'ω hz'def
  obtain ⟨x, a, a₁, a₂, g⟩ := s.exists_gen
  exact g.false_of_conj_u_mem_QB fun k hk => g.conj_u_mem_QB hn' hz' hk

theorem a1_trivial_of_critDist_two [Finite D] (h : GoldHyp A B)
    (h32 : 32 ≤ Nat.card ↥(A ⊓ B)) (hn : IsNaturalAt A (A ⊓ B) z V)
    (hb : critDist (A ⊔ B) A B V = 2) :
    ∀ ε ∈ centerOf (A ⊓ B), ε * ε = 1 → (∀ y ∈ A, y * ε = ε * y) → ε = 1 :=
  ((omega_labelling_iff h h32 hn hb).1).mp fun _ hωZ hω2 y hy =>
    (B2Setup.of_critDist_two h hn hb).centralizes_omega hωZ hω2 y hy

end GoldAmL2D

end F6

end CFSG.Quasithin
