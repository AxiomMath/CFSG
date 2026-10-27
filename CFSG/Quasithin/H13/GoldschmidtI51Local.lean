module

public import CFSG.Quasithin.H13.GoldschmidtI51Bridge
public import CFSG.Quasithin.H13.GoldschmidtI51Models
public import CFSG.Quasithin.H13.GoldschmidtI51ModelsA6
public import CFSG.Quasithin.H13.GoldschmidtI51Trans

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

abbrev TT (Gs : Fin 3 → Subgroup G) : Subgroup G := Gs 0 ⊓ Gs 1 ⊓ Gs 2

abbrev QQ (Gs : Fin 3 → Subgroup G) (i : Fin 3) : Subgroup G := pCoreOf 2 (Gs i)

omit [Finite G] in
theorem TT_le (i : Fin 3) : TT Gs ≤ Gs i := by
  fin_cases i
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right

theorem QQ_le_TT (hD : IsDSystem D Gs) (i : Fin 3) : QQ Gs i ≤ TT Gs :=
  pCoreOf_le_sylow (hD.d3sylow i)

omit [Finite G] in
theorem TT_le_inf (i j : Fin 3) : TT Gs ≤ Gs i ⊓ Gs j := le_inf (TT_le i) (TT_le j)

theorem QQ_le_inf (hD : IsDSystem D Gs) (i j : Fin 3) : QQ Gs i ≤ Gs i ⊓ Gs j :=
  (QQ_le_TT hD i).trans (TT_le_inf i j)

theorem Q0_le_P01 (hD : IsDSystem D Gs) : QQ Gs 0 ≤ Gs 0 ⊓ Gs 1 := QQ_le_inf hD 0 1

theorem Q0_le_P02 (hD : IsDSystem D Gs) : QQ Gs 0 ≤ Gs 0 ⊓ Gs 2 := QQ_le_inf hD 0 2

theorem Q1_le_P01 (hD : IsDSystem D Gs) : QQ Gs 1 ≤ Gs 0 ⊓ Gs 1 := by
  rw [inf_comm]; exact QQ_le_inf hD 1 0

theorem Q1_le_P12 (hD : IsDSystem D Gs) : QQ Gs 1 ≤ Gs 1 ⊓ Gs 2 := QQ_le_inf hD 1 2

theorem Q2_le_P02 (hD : IsDSystem D Gs) : QQ Gs 2 ≤ Gs 0 ⊓ Gs 2 := by
  rw [inf_comm]; exact QQ_le_inf hD 2 0

theorem Q2_le_P12 (hD : IsDSystem D Gs) : QQ Gs 2 ≤ Gs 1 ⊓ Gs 2 := by
  rw [inf_comm]; exact QQ_le_inf hD 2 1

theorem model2 (hD : IsDSystem D Gs) :
    ∃ (A B : Subgroup SL3.S) (φ : ↥(Gs 2) →* SL3.S), FanoModel A B ∧ Function.Surjective φ ∧
      φ.ker = CFSG.Open.pCore 2 ↥(Gs 2) ∧
      ((Gs 0 ⊓ Gs 2).subgroupOf (Gs 2)).map φ = A ∧
      ((Gs 1 ⊓ Gs 2).subgroupOf (Gs 2)).map φ = B ∧
      ((TT Gs).subgroupOf (Gs 2)).map φ = SL3.P0 := by
  obtain ⟨hne, hmax⟩ := hD.d3max 2 0 1 (by decide) (by decide) (by decide)
  rw [inf_comm (Gs 2) (Gs 0), inf_comm (Gs 2) (Gs 1)] at hne hmax
  obtain ⟨φ, hφ, hker, hT, h | h⟩ := exists_model_parabolics hD.d2two (hD.d3sylow 2)
    SL3.P0_sylow.1 SL3.P0_sylow.2 SL3.overgroups_SL3 inf_le_left inf_le_right
    SL3.X_incomparable.1 SL3.X_incomparable.2 inf_le_right inf_le_right hne hmax
  · exact ⟨_, _, φ, fanoModel_X1_X2, hφ, hker, h.1, h.2, hT⟩
  · exact ⟨_, _, φ, fanoModel_X2_X1, hφ, hker, h.1, h.2, hT⟩

theorem model1 (hD : IsDSystem D Gs) :
    ∃ (A B : Subgroup SL22.K) (φ : ↥(Gs 1) →* SL22.K), DigonModel A B ∧
      Function.Surjective φ ∧ φ.ker = CFSG.Open.pCore 2 ↥(Gs 1) ∧
      ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 1)).map φ = A ∧
      ((Gs 1 ⊓ Gs 2).subgroupOf (Gs 1)).map φ = B ∧
      ((TT Gs).subgroupOf (Gs 1)).map φ = SL22.P0 := by
  obtain ⟨hne, hmax⟩ := hD.d3max 1 0 2 (by decide) (by decide) (by decide)
  rw [inf_comm (Gs 1) (Gs 0)] at hne hmax
  obtain ⟨φ, hφ, hker, hT, h | h⟩ := exists_model_parabolics hD.d2one (hD.d3sylow 1)
    SL22.P0_sylow.1 SL22.P0_sylow.2 SL22.overgroups_SL22
    (fun x hx => SL22.mem_X1.2 (Subgroup.mem_prod.1 hx).2)
    (fun x hx => SL22.mem_X2.2 (Subgroup.mem_prod.1 hx).1)
    SL22.X_incomparable.1 SL22.X_incomparable.2 inf_le_right inf_le_left hne hmax
  · exact ⟨_, _, φ, digonModel_X1_X2, hφ, hker, h.1, h.2, hT⟩
  · exact ⟨_, _, φ, digonModel_X2_X1, hφ, hker, h.1, h.2, hT⟩

theorem loc2_core (hD : IsDSystem D Gs) :
    ∀ n ∈ Gs 2, (∀ g ∈ Gs 2, g⁻¹ * n * g ∈ Gs 0 ⊓ Gs 2) → n ∈ QQ Gs 2 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  exact bridge_core φ hφ hker hA hM.coreA

theorem loc2_fano (hD : IsDSystem D Gs) :
    ∀ g ∈ Gs 2, ∃ a ∈ Gs 0 ⊓ Gs 2, ∃ b ∈ Gs 1 ⊓ Gs 2, ∃ c ∈ Gs 0 ⊓ Gs 2, g = a * b * c := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  exact bridge_prod3 φ hker hA hB hA (Q2_le_P02 hD) hM.fanoA

theorem loc2_noNormal_20 (hD : IsDSystem D Gs) {M : Subgroup G} (hMP : M ≤ Gs 0 ⊓ Gs 2)
    (hnorm : ∀ a ∈ Gs 0 ⊓ Gs 2, ∀ m ∈ M, a * m * a⁻¹ ∈ M)
    (hord : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ ∈ QQ Gs 2 ∨ m₂ ∈ QQ Gs 2 ∨ m₁ * m₂⁻¹ ∈ QQ Gs 2) :
    M ≤ QQ Gs 2 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  exact bridge_noNormal φ hker hA hM.centerA hMP hnorm hord (hMP.trans inf_le_right)

theorem loc2_noNormal_21 (hD : IsDSystem D Gs) {M : Subgroup G} (hMP : M ≤ Gs 1 ⊓ Gs 2)
    (hnorm : ∀ a ∈ Gs 1 ⊓ Gs 2, ∀ m ∈ M, a * m * a⁻¹ ∈ M)
    (hord : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ ∈ QQ Gs 2 ∨ m₂ ∈ QQ Gs 2 ∨ m₁ * m₂⁻¹ ∈ QQ Gs 2) :
    M ≤ QQ Gs 2 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  exact bridge_noNormal φ hker hB hM.centerB hMP hnorm hord (hMP.trans inf_le_right)

theorem loc1_prod2 (hD : IsDSystem D Gs) :
    ∀ g ∈ Gs 1, ∃ a ∈ Gs 0 ⊓ Gs 1, ∃ b ∈ Gs 1 ⊓ Gs 2, g = a * b := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model1 hD
  exact bridge_prod2 φ hker hA hB (Q1_le_P12 hD) hM.prodAB

theorem loc1_prod2' (hD : IsDSystem D Gs) :
    ∀ g ∈ Gs 1, ∃ a ∈ Gs 1 ⊓ Gs 2, ∃ b ∈ Gs 0 ⊓ Gs 1, g = a * b := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model1 hD
  exact bridge_prod2 φ hker hB hA (Q1_le_P01 hD) hM.prodBA

theorem loc1_index_10 (hD : IsDSystem D Gs) : (Gs 0 ⊓ Gs 1).relIndex (Gs 1) = 3 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model1 hD
  rw [bridge_index φ hφ hker hA (Q1_le_P01 hD), hM.idxA]

theorem loc1_index_12 (hD : IsDSystem D Gs) : (Gs 1 ⊓ Gs 2).relIndex (Gs 1) = 3 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model1 hD
  rw [bridge_index φ hφ hker hB (Q1_le_P12 hD), hM.idxB]

theorem loc1_core (hD : IsDSystem D Gs) :
    ∀ n ∈ Gs 1, (∀ g ∈ Gs 1, g⁻¹ * n * g ∈ Gs 0 ⊓ Gs 1) →
      (∀ g ∈ Gs 1, g⁻¹ * n * g ∈ Gs 1 ⊓ Gs 2) → n ∈ QQ Gs 1 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model1 hD
  intro n hn h1 h2
  rw [← mem_ker_iff_mem_pCoreOf φ hker hn]
  apply (MonoidHom.mem_ker).2
  apply hM.core
  · intro g
    obtain ⟨g', rfl⟩ := hφ g
    rw [← hA]
    exact ⟨g'⁻¹ * ⟨n, hn⟩ * g', Subgroup.mem_subgroupOf.2 (h1 g' g'.2), by simp⟩
  · intro g
    obtain ⟨g', rfl⟩ := hφ g
    rw [← hB]
    exact ⟨g'⁻¹ * ⟨n, hn⟩ * g', Subgroup.mem_subgroupOf.2 (h2 g' g'.2), by simp⟩

theorem loc2_relIndex (hD : IsDSystem D Gs) : (QQ Gs 2).relIndex (TT Gs) = 8 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  rw [relIndex_pCoreOf_eq_card (TT_le 2) φ hker hT, SL3.card_P0]

theorem loc1_relIndex (hD : IsDSystem D Gs) : (QQ Gs 1).relIndex (TT Gs) = 4 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model1 hD
  rw [relIndex_pCoreOf_eq_card (TT_le 1) φ hker hT, SL22.card_P0]

theorem isPGroup_D6sub : IsPGroup 2 D6sub :=
  IsPGroup.of_card (n := 4) (by rw [card_D6sub]; norm_num)

theorem D6sub_odd_index : ¬ 2 ∣ D6sub.index := by
  have := Subgroup.card_mul_index D6sub
  rw [card_D6sub, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h : D6sub.index = 45 := by
    have h720 : Nat.factorial 6 = 720 := by decide
    rw [h720] at this
    omega
  rw [h]
  norm_num

theorem model0 (hD : IsDSystem .C3 Gs) :
    ∃ (R A B : Subgroup (Equiv.Perm (Fin 6))) (ψ : ↥(Gs 0) →* Equiv.Perm (Fin 6)),
      (R = ⊤ ∨ R = A6g) ∧ ψ.range = R ∧ ψ.ker = CFSG.Open.pCore 2 ↥(Gs 0) ∧
      ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)).map ψ = A ∧
      ((Gs 0 ⊓ Gs 2).subgroupOf (Gs 0)).map ψ = B ∧
      ((TT Gs).subgroupOf (Gs 0)).map ψ = D6sub ⊓ R ∧
      ((A = P1sub ⊓ R ∧ B = P2sub ⊓ R) ∨ (A = P2sub ⊓ R ∧ B = P1sub ⊓ R)) := by
  obtain ⟨hne, hmax⟩ := hD.d3max 0 1 2 (by decide) (by decide) (by decide)
  rcases hD.d1C3 rfl with h | h
  ·
    obtain ⟨φ, hφ, hker, hT, hh⟩ := exists_model_parabolics h (hD.d3sylow 0) P0a_sylow.1
      P0a_sylow.2 overgroups_A6sub P0a_le_X1a P0a_le_X2a X1a_not_le_X2a X2a_not_le_X1a
      inf_le_left inf_le_left hne hmax
    have hmap : ∀ (Y : Subgroup ↥(Gs 0)) (W : Subgroup ↥A6g), Y.map φ = W →
        Y.map (A6g.subtype.comp φ) = W.map A6g.subtype := fun Y W h => by
      rw [← Subgroup.map_map, h]
    have hX1 : X1a.map A6g.subtype = P1sub ⊓ A6g :=
      CFSG.Quasithin.H13.A6.map_subtype_subgroupOf inf_le_right
    have hX2 : X2a.map A6g.subtype = P2sub ⊓ A6g :=
      CFSG.Quasithin.H13.A6.map_subtype_subgroupOf inf_le_right
    have hrange : (A6g.subtype.comp φ).range = A6g := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφ, Subgroup.map_top,
        Subgroup.range_subtype]
    have hkerψ : (A6g.subtype.comp φ).ker = CFSG.Open.pCore 2 ↥(Gs 0) := by
      rw [← hker]; ext x; simp [MonoidHom.mem_ker]
    have hTψ : ((TT Gs).subgroupOf (Gs 0)).map (A6g.subtype.comp φ) = D6sub ⊓ A6g := by
      rw [hmap _ _ hT]
      exact CFSG.Quasithin.H13.A6.map_subtype_subgroupOf QA6sub_le_A6
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨A6g, P1sub ⊓ A6g, P2sub ⊓ A6g, A6g.subtype.comp φ, Or.inr rfl, hrange, hkerψ,
        by rw [hmap _ _ h1, hX1], by rw [hmap _ _ h2, hX2], hTψ, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨A6g, P2sub ⊓ A6g, P1sub ⊓ A6g, A6g.subtype.comp φ, Or.inr rfl, hrange, hkerψ,
        by rw [hmap _ _ h1, hX2], by rw [hmap _ _ h2, hX1], hTψ, Or.inr ⟨rfl, rfl⟩⟩
  ·
    obtain ⟨φ, hφ, hker, hT, hh⟩ := exists_model_parabolics h (hD.d3sylow 0) isPGroup_D6sub
      D6sub_odd_index overgroups_D6 (D6sub_le.trans inf_le_left) (D6sub_le.trans inf_le_right)
      P1_not_le_P2.1 P1_not_le_P2.2 inf_le_left inf_le_left hne hmax
    have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.2 hφ
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⊤, P1sub, P2sub, φ, Or.inl rfl, hrange, hker, h1, h2, by rw [hT, inf_top_eq],
        Or.inl ⟨(inf_top_eq _).symm, (inf_top_eq _).symm⟩⟩
    · exact ⟨⊤, P2sub, P1sub, φ, Or.inl rfl, hrange, hker, h1, h2, by rw [hT, inf_top_eq],
        Or.inr ⟨(inf_top_eq _).symm, (inf_top_eq _).symm⟩⟩

theorem loc0_center (hD : IsDSystem .C3 Gs) :
    ∀ n ∈ Gs 0, (∀ g ∈ Gs 0, g * n = n * g) → n ∈ QQ Gs 0 := by
  obtain ⟨R, A, B, ψ, hR, hrange, hker, -, -, -, -⟩ := model0 hD
  intro n hn hc
  rw [← mem_ker_iff_mem_pCoreOf ψ hker hn, MonoidHom.mem_ker]
  have hψn : ψ ⟨n, hn⟩ ∈ R := hrange ▸ ⟨⟨n, hn⟩, rfl⟩
  have hcomm : ∀ r ∈ R, r * ψ ⟨n, hn⟩ = ψ ⟨n, hn⟩ * r := by
    intro r hr
    rw [← hrange] at hr
    obtain ⟨g, rfl⟩ := hr
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc g g.2)
  rcases hR with rfl | rfl
  · exact center_perm6 _ (fun τ => (hcomm τ trivial).symm)
  · exact center_alt6 _ (Equiv.Perm.mem_alternatingGroup.1 hψn) (fun τ hτ =>
      (hcomm τ (Equiv.Perm.mem_alternatingGroup.2 hτ)).symm)

theorem loc0_relIndex (hD : IsDSystem .C3 Gs) :
    (QQ Gs 0).relIndex (TT Gs) = 8 ∨ (QQ Gs 0).relIndex (TT Gs) = 16 := by
  obtain ⟨R, A, B, ψ, hR, hrange, hker, -, -, hT, -⟩ := model0 hD
  rw [relIndex_pCoreOf_eq_card (TT_le 0) ψ hker hT]
  rcases hR with rfl | rfl
  · right; rw [inf_top_eq, card_D6sub]
  · left
    have : D6sub ⊓ A6g = QA6sub := rfl
    rw [this, card_QA6sub]

theorem loc2_index_20 (hD : IsDSystem D Gs) : (Gs 0 ⊓ Gs 2).relIndex (Gs 2) = 7 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  rw [bridge_index φ hφ hker hA (Q2_le_P02 hD), hM.idxA]

theorem model0A (hD : IsDSystem .A3 Gs) :
    ∃ (A B : Subgroup SL3.S) (φ : ↥(Gs 0) →* SL3.S), FanoModel A B ∧ Function.Surjective φ ∧
      φ.ker = CFSG.Open.pCore 2 ↥(Gs 0) ∧
      ((Gs 0 ⊓ Gs 1).subgroupOf (Gs 0)).map φ = A ∧
      ((Gs 0 ⊓ Gs 2).subgroupOf (Gs 0)).map φ = B ∧
      ((TT Gs).subgroupOf (Gs 0)).map φ = SL3.P0 := by
  obtain ⟨hne, hmax⟩ := hD.d3max 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨φ, hφ, hker, hT, h | h⟩ := exists_model_parabolics (hD.d1A3 rfl) (hD.d3sylow 0)
    SL3.P0_sylow.1 SL3.P0_sylow.2 SL3.overgroups_SL3
    inf_le_left inf_le_right SL3.X_incomparable.1 SL3.X_incomparable.2 inf_le_left inf_le_left
    hne hmax
  · exact ⟨_, _, φ, fanoModel_X1_X2, hφ, hker, h.1, h.2, hT⟩
  · exact ⟨_, _, φ, fanoModel_X2_X1, hφ, hker, h.1, h.2, hT⟩

theorem loc0A_fano (hD : IsDSystem .A3 Gs) :
    ∀ g ∈ Gs 0, ∃ a ∈ Gs 0 ⊓ Gs 1, ∃ b ∈ Gs 0 ⊓ Gs 2, ∃ c ∈ Gs 0 ⊓ Gs 1, g = a * b * c := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model0A hD
  exact bridge_prod3 φ hker hA hB hA (Q0_le_P01 hD) hM.fanoA

theorem loc0A_idx01 (hD : IsDSystem .A3 Gs) : (Gs 0 ⊓ Gs 1).relIndex (Gs 0) = 7 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model0A hD
  rw [bridge_index φ hφ hker hA (Q0_le_P01 hD), hM.idxA]

theorem loc0A_core (hD : IsDSystem .A3 Gs) :
    ∀ n ∈ Gs 0, (∀ g ∈ Gs 0, g⁻¹ * n * g ∈ Gs 0 ⊓ Gs 1) → n ∈ QQ Gs 0 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model0A hD
  exact bridge_core φ hφ hker hA hM.coreA

theorem loc0A_relIndex (hD : IsDSystem .A3 Gs) : (QQ Gs 0).relIndex (TT Gs) = 8 := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model0A hD
  rw [relIndex_pCoreOf_eq_card (TT_le 0) φ hker hT, SL3.card_P0]

theorem loc0A_card (hD : IsDSystem .A3 Gs) :
    Nat.card ↥(Gs 0) = 168 * Nat.card ↥(QQ Gs 0) := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model0A hD
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    CFSG.Quasithin.H13.A6.SL3.card_S] at h1
  have hker' : Nat.card φ.ker = Nat.card ↥(QQ Gs 0) := by
    rw [hker]
    exact (Subgroup.card_map_of_injective (Gs 0).subtype_injective).symm
  rw [h1, hker']

end CFSG.Quasithin.H13.I51
