module

public import CFSG.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_comm' {A X K : Subgroup G} (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hXA : X ≤ A) (hKA : K ≤ A) : K ≤ Subgroup.normalizer (X : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hab k (hKA hk) x (hXA hx), mul_inv_cancel_right]
    exact hx
  · intro hx
    have hxA : x ∈ A := by
      have h1 : k * x * k⁻¹ ∈ A := hXA hx
      have := A.mul_mem (A.mul_mem (A.inv_mem (hKA hk)) h1) (hKA hk)
      simpa [mul_assoc] using this
    rwa [hab k (hKA hk) x hxA, mul_inv_cancel_right] at hx

theorem relIndex_sup_le_two {A V₁ X K : Subgroup G} (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hXA : X ≤ A) (hKA : K ≤ A) (hV₁X : V₁ ≤ X) (hV₁K : V₁ ≤ K) (hK2 : V₁.relIndex K ≤ 2) :
    X.relIndex (X ⊔ K) ≤ 2 := by
  have h2 : X.relIndex (X ⊔ K) = X.relIndex K := by
    rw [sup_comm]
    exact A4.relIndex_sup_eq_of_le_normalizer' (le_normalizer_of_comm' hab hXA hKA)
  rw [h2]
  have hd : (X ⊓ K).relIndex K ∣ V₁.relIndex K :=
    Subgroup.relIndex_dvd_of_le_left K (le_inf hV₁X hV₁K)
  have hpos : 0 < V₁.relIndex K := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.inf_relIndex_right X K]
  exact (Nat.le_of_dvd hpos hd).trans hK2

theorem relIndex_sup_three_le {A V₁ K₁ K₂ K₃ : Subgroup G}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h₁ : K₁ ≤ A) (h₂ : K₂ ≤ A) (h₃ : K₃ ≤ A)
    (hV₁ : V₁ ≤ K₁) (hV₂ : V₁ ≤ K₂) (hV₃ : V₁ ≤ K₃) (hi₁ : V₁.relIndex K₁ ≤ 2)
    (hi₂ : V₁.relIndex K₂ ≤ 2) (hi₃ : V₁.relIndex K₃ ≤ 2) :
    V₁.relIndex (K₁ ⊔ K₂ ⊔ K₃) ≤ 8 := by
  have e1 := Subgroup.relIndex_mul_relIndex V₁ K₁ (K₁ ⊔ K₂) hV₁ le_sup_left
  have e2 := Subgroup.relIndex_mul_relIndex V₁ (K₁ ⊔ K₂) (K₁ ⊔ K₂ ⊔ K₃)
    (hV₁.trans le_sup_left) le_sup_left
  have b2 := relIndex_sup_le_two hab h₁ h₂ hV₁ hV₂ hi₂
  have b3 := relIndex_sup_le_two hab (sup_le h₁ h₂) h₃ (hV₁.trans le_sup_left) hV₃ hi₃
  rw [← e2, ← e1]
  calc V₁.relIndex K₁ * K₁.relIndex (K₁ ⊔ K₂) * (K₁ ⊔ K₂).relIndex (K₁ ⊔ K₂ ⊔ K₃) ≤ 2 * 2 * 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul hi₁ b2) b3
    _ = 8 := by norm_num

omit [Finite G] in
theorem exists_subset_three {α : Type*} {s : Set α} (hs : s.Finite) (hne : s.Nonempty)
    (h3 : s.ncard ≤ 3) : ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, s ⊆ {x, y, z} := by
  have hpos : 0 < s.ncard := (Set.ncard_pos hs).mpr hne
  rcases (by omega : s.ncard = 1 ∨ s.ncard = 2 ∨ s.ncard = 3) with h | h | h
  · obtain ⟨x, rfl⟩ := Set.ncard_eq_one.mp h
    exact ⟨x, rfl, x, rfl, x, rfl, fun a ha => Or.inl ha⟩
  · obtain ⟨x, y, -, rfl⟩ := Set.ncard_eq_two.mp h
    refine ⟨x, Or.inl rfl, y, Or.inr rfl, y, Or.inr rfl, fun a ha => ?_⟩
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · obtain ⟨x, y, z, -, -, -, rfl⟩ := Set.ncard_eq_three.mp h
    exact ⟨x, Or.inl rfl, y, Or.inr (Or.inl rfl), z, Or.inr (Or.inr rfl), le_rfl⟩

omit [Finite G] in
theorem conjClosure_mono {Z Z' H H' : Subgroup G} (hZ : Z ≤ Z') (hH : H ≤ H') :
    conjClosure Z H ≤ conjClosure Z' H' :=
  conjClosure_le fun _ hh _ hz => mem_conjClosure (hH hh) (hZ hz)

namespace Setting147

variable {T L V H : Subgroup G}

theorem inf_V_eq (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {I : Subgroup G} (hVI : fsuV1 T V ≤ I) (hIU : I < conjClosure V H)
    (hHI : H ≤ Subgroup.normalizer (I : Set G)) : V ⊓ I = fsuV1 T V := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  obtain ⟨x, hx, -, hxa, hxb⟩ := S14.exists_x hz hz1 ha haV hb hbV
  have hxl : x ∈ l1 T L V := hl1eq ▸ hx
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hxH : x ∈ H := hL1H hxl
  have hxI : ∀ w ∈ I, x * w * x⁻¹ ∈ I := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHI hxH) w).mp hw
  have haV' : a ∈ V := S14.hV2.2.1 ha
  have hVI' : a ∈ I → b ∈ I → V ≤ I := by
    intro haI hbI v hv
    rcases S14.mem_V hb hbV hv with h | h
    · rcases S14.mem_V2 ha haV h with h' | h'
      · exact hVI h'
      · rw [show v = a⁻¹ * (a * v) by group]
        exact mul_mem (inv_mem haI) (hVI h')
    · have hbv : b * v ∈ I := by
        rcases S14.mem_V2 ha haV h with h' | h'
        · exact hVI h'
        · rw [show b * v = a⁻¹ * (a * (b * v)) by group]
          exact mul_mem (inv_mem haI) (hVI h')
      rw [show v = b⁻¹ * (b * v) by group]
      exact mul_mem (inv_mem hbI) hbv
  have hnot : ¬ V ≤ I := fun h =>
    hIU.2 (conjClosure_le fun h' hh' v hv => (Subgroup.mem_normalizer_iff.mp (hHI hh') v).mp (h hv))
  refine le_antisymm (fun w hw => ?_) (le_inf (fun v hv => (Subgroup.mem_inf.mp hv).1) hVI)
  by_contra hwV
  apply hnot
  have hwV' := hw.1
  have hwI := hw.2
  have hbb : b * b = 1 := S14.mul_self_V hb
  have haa : a * a = 1 := S14.mul_self_V haV'
  rcases S14.mem_V hb hbV hwV' with h | h
  ·
    rcases S14.mem_V2 ha haV h with h' | h'
    · exact absurd h' hwV
    · have haI : a ∈ I := by
        rw [show a = a * w * w⁻¹ by group]
        exact mul_mem (hVI h') (inv_mem hwI)
      exact hVI' haI (hxa ▸ hxI a haI)
  · rcases S14.mem_V2 ha haV h with h' | h'
    ·
      have hbI : b ∈ I := by
        rw [show b = b * w * w⁻¹ by group]
        exact mul_mem (hVI h') (inv_mem hwI)
      have habI : a * b ∈ I := hxb ▸ hxI b hbI
      have haI : a ∈ I := by
        rw [show a = a * b * b⁻¹ by group]
        exact mul_mem habI (inv_mem hbI)
      exact hVI' haI hbI
    ·
      have habI : a * b ∈ I := by
        rw [show a * b = a * (b * w) * w⁻¹ by group]
        exact mul_mem (hVI h') (inv_mem hwI)
      have hx2 : x * (a * b) * x⁻¹ = a := by
        rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, hxa, hxb]
        calc b * (a * b) = b * a * b := by group
          _ = a * b * b := by rw [S14.comm_V hb haV']
          _ = a := by rw [mul_assoc, hbb, mul_one]
      have haI : a ∈ I := hx2 ▸ hxI _ habI
      exact hVI' haI (hxa ▸ hxI a haI)

end Setting147

end CFSG.Quasithin.H13.L32A
