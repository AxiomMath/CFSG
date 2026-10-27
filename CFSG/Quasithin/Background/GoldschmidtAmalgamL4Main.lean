module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Model
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Side
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4SideA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4CP
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Uniq

public section

namespace CFSG.Quasithin.F6.GoldAmL4

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

def prodMultEquiv : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃* Multiplicative V4 where
  toFun p := Multiplicative.ofAdd (Multiplicative.toAdd p.1, Multiplicative.toAdd p.2)
  invFun v := (Multiplicative.ofAdd (Multiplicative.toAdd v).1,
    Multiplicative.ofAdd (Multiplicative.toAdd v).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite D] in
theorem card_eq_of_relIndex_two {H K : Subgroup D} (hHK : H ≤ K) (h : H.relIndex K = 2) :
    Nat.card K = 2 * Nat.card H := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv] at h1
  have : (H.subgroupOf K).index = 2 := h
  rw [this] at h1
  omega

theorem card_of_shape {T : Subgroup D} (hv : Vertex G₁ T)
    (ε : ↥(pCoreOf 2 G₁) ≃* Multiplicative V4) : Nat.card ↥T = 32 := by
  have h16 : Nat.card ↥(pCoreOf 2 G₁) = 16 := by
    rw [Nat.card_congr ε.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := V4)),
      Nat.card_prod, Nat.card_zmod]
  have := card_eq_of_relIndex_two hv.pCoreOf_le hv.relIndex_pCoreOf_T
  omega

theorem pCoreOf_right_eq' {T : Subgroup D} {a b s : D} (hT : TRel a b s)
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32)
    (hTeq : Subgroup.closure ({a, b, s} : Set D) = T) (hv₂ : Vertex G₂ T)
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂) (Multiplicative (ZMod 4)) (QuaternionGroup 2)) :
    pCoreOf 2 G₂ = m2Sub.map hT.emb := by
  have hinj := hT.emb_injective hcard
  have hrange : hT.emb.range = T := by rw [hT.emb_range, hTeq]
  have hQ₂T : pCoreOf 2 G₂ ≤ hT.emb.range := by rw [hrange]; exact hv₂.pCoreOf_le
  have hmapN : ((pCoreOf 2 G₂).comap hT.emb).map hT.emb = pCoreOf 2 G₂ :=
    Subgroup.map_comap_eq_self hQ₂T
  have hcardT : Nat.card ↥T = 32 := by rw [← hTeq]; exact hcard
  have hcardQ₂ : Nat.card ↥(pCoreOf 2 G₂) = 16 := by
    have := card_eq_of_relIndex_two hv₂.pCoreOf_le hv₂.relIndex_pCoreOf_T
    omega
  have hcardN : Nat.card ↥((pCoreOf 2 G₂).comap hT.emb) = 16 := by
    have := Nat.card_congr
      (Subgroup.equivMapOfInjective ((pCoreOf 2 G₂).comap hT.emb) hT.emb hinj).toEquiv
    rw [this, hmapN]
    exact hcardQ₂
  have hidx : ((pCoreOf 2 G₂).comap hT.emb).index = 2 := by
    have h1 := Subgroup.card_mul_index ((pCoreOf 2 G₂).comap hT.emb)
    rw [hcardN, card_Tc] at h1
    omega
  have hab : ∃ x ∈ (pCoreOf 2 G₂).comap hT.emb, ∃ y ∈ (pCoreOf 2 G₂).comap hT.emb,
      x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := IsCentralProduct₂.not_comm h₂
    obtain ⟨u, hu⟩ := hQ₂T x.2
    obtain ⟨v, hv⟩ := hQ₂T y.2
    refine ⟨u, ?_, v, ?_, fun hc => hxy ?_⟩
    · show hT.emb u ∈ pCoreOf 2 G₂
      rw [hu]; exact x.2
    · show hT.emb v ∈ pCoreOf 2 G₂
      rw [hv]; exact y.2
    · apply Subtype.ext
      have := congrArg hT.emb hc
      rw [map_mul, map_mul, hu, hv] at this
      exact this
  have hexp : ∀ w ∈ (pCoreOf 2 G₂).comap hT.emb, w ^ 4 = 1 := by
    intro w hw
    have hw' : hT.emb w ∈ pCoreOf 2 G₂ := hw
    have h4 := IsCentralProduct₂.pow_four h₂ (⟨hT.emb w, hw'⟩ : ↥(pCoreOf 2 G₂))
    have h5 : (hT.emb w) ^ 4 = 1 := by simpa using congrArg Subtype.val h4
    apply hinj
    rw [map_pow, h5, map_one]
  have hN := eq_m2Sub_of _ hidx hab hexp
  calc pCoreOf 2 G₂ = ((pCoreOf 2 G₂).comap hT.emb).map hT.emb := hmapN.symm
    _ = m2Sub.map hT.emb := by rw [hN]

theorem exists_tuple_of_vertices {T : Subgroup D} (hv₁ : Vertex G₁ T) (hv₂ : Vertex G₂ T)
    (ε : ↥(pCoreOf 2 G₁) ≃* Multiplicative V4)
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂) (Multiplicative (ZMod 4)) (QuaternionGroup 2)) :
    ∃ a b s x y : D, ARel a b s x ∧ BRel a b s y ∧
      Subgroup.closure ({a, b, s} : Set D) = T ∧
      Subgroup.closure ({a, b, s, x} : Set D) = G₁ ∧
      Subgroup.closure ({a, b, s, y} : Set D) = G₂ ∧
      Nat.card ↥(Subgroup.closure ({a, b, s} : Set D)) = 32 ∧
      Subgroup.closure ({a, b} : Set D) = pCoreOf 2 G₁ := by
  obtain ⟨a, b, s, x, hA, hab, hTeq, hGx⟩ := exists_A_tuple hv₁ ε
  have hT := hA.toTRel
  have hcard : Nat.card ↥(Subgroup.closure ({a, b, s} : Set D)) = 32 := by
    rw [hTeq]; exact card_of_shape hv₁ ε
  have hinj := hT.emb_injective hcard
  have hQ₂ := pCoreOf_right_eq' hT hcard hTeq hv₂ h₂
  have hTG₂ : Subgroup.closure ({a, b, s} : Set D) ≤ G₂ := by
    rw [hTeq]; exact hv₂.T_le
  have hGQ : ∀ g ∈ G₂, ∀ q ∈ m2Sub.map hT.emb, g * q * g⁻¹ ∈ m2Sub.map hT.emb := by
    rw [← hQ₂]
    intro g hg q hq
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hg) q).mp hq
  have hC : ∀ g ∈ G₂, (∀ q ∈ m2Sub.map hT.emb, g * q = q * g) → g ∈ m2Sub.map hT.emb := by
    rw [← hQ₂]
    intro g hg hc
    apply hv₂.charTwo
    exact ⟨hg, Subgroup.mem_centralizer_iff.mpr fun q hq => (hc q hq).symm⟩
  obtain ⟨y', hy'G, hy'o⟩ := hv₂.exists_order_three
  have hy'3 : y' ^ 3 = 1 := hy'o ▸ pow_orderOf_eq_one y'
  have hy'1 : y' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy'o
    omega
  obtain ⟨y, hyG, hB⟩ := exists_B_elem hT hcard hTG₂ hGQ hC hy'G hy'3 hy'1
  have hyT : y ∉ T := by
    intro hy
    rw [← hTeq] at hy
    exact hB.ne_one hinj (hT.eq_one_of_pow_three hB.hy hy)
  have hTC : T ≤ Subgroup.closure ({a, b, s, y} : Set D) := by
    rw [← hTeq]
    exact Subgroup.closure_mono (by intro z hz; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz ⊢; tauto)
  have hCG : Subgroup.closure ({a, b, s, y} : Set D) ≤ G₂ := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hTG₂ (Subgroup.subset_closure (by simp))
    · exact hTG₂ (Subgroup.subset_closure (by simp))
    · exact hTG₂ (Subgroup.subset_closure (by simp))
    · exact hyG
  exact ⟨a, b, s, x, y, hA, hB, hTeq, hGx,
    le_antisymm hCG (hv₂.le_of_not_mem hTC hCG (Subgroup.subset_closure (by simp)) hyT),
    hcard, hab⟩

theorem exists_tuple (h : GoldHyp G₁ G₂) (ε : ↥(pCoreOf 2 G₁) ≃* Multiplicative V4)
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂) (Multiplicative (ZMod 4)) (QuaternionGroup 2)) :
    ∃ a b s x y : D, ARel a b s x ∧ BRel a b s y ∧
      Subgroup.closure ({a, b, s} : Set D) = G₁ ⊓ G₂ ∧
      Subgroup.closure ({a, b, s, x} : Set D) = G₁ ∧
      Subgroup.closure ({a, b, s, y} : Set D) = G₂ ∧
      Nat.card ↥(Subgroup.closure ({a, b, s} : Set D)) = 32 := by
  obtain ⟨a, b, s, x, y, hA, hB, h1, h2, h3, h4, -⟩ :=
    exists_tuple_of_vertices h.vertex_left h.vertex_right ε h₂
  exact ⟨a, b, s, x, y, hA, hB, h1, h2, h3, h4⟩

theorem isGoldCaseG22Prime_of_shape
    (h : GoldHyp G₁ G₂)
    (h₁ : Nonempty (↥(pCoreOf 2 G₁) ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂) (Multiplicative (ZMod 4)) (QuaternionGroup 2)) :
    IsGoldCaseG22Prime G₂ G₁ := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨a, b, s, x, y, hA, hB, hTeq, hGx, hGy, hcard⟩ :=
    exists_tuple h (e₁.trans prodMultEquiv) h₂
  have hT := hA.toTRel
  have hinj := hT.emb_injective hcard
  refine ⟨?_, ?_, h.amalgam.quotient₂, h.amalgam.quotient₁, h₂, ⟨e₁⟩⟩
  ·
    have hinf : Subgroup.closure ({a, b, s, y} : Set D) ⊓ Subgroup.closure ({a, b, s, x} : Set D) =
        Subgroup.closure ({a, b, s} : Set D) := by
      rw [hGy, hGx, hTeq, inf_comm]
    have hiso := isAmalgamIso_of_tuples hA hB u33_aRel u33_bRel hcard u33_card_T' hinf u33_inf
    rw [hGy, hGx] at hiso
    refine ⟨U33G, inferInstance, u33_finite, u33Data.B, u33Data.A, isG22Prime_u33,
      u33_isTwoLocalAmalgam, ?_⟩
    rw [u33Data_B, u33Data_A]
    exact hiso
  ·
    intro hc
    rcases hc with hc | hc
    · exact hc
    · exfalso
      have hab : a * b ∈ G₂ ⊓ G₁ := by
        rw [inf_comm, ← hTeq]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      have hcen : a * b ∈ centerOf (G₂ ⊓ G₁) := by
        refine ⟨hab, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
        rw [inf_comm, ← hTeq, ← hT.emb_range] at ht
        obtain ⟨w, rfl⟩ := ht
        rw [← hT.emb_tC, ← map_mul, ← map_mul, tC_central]
      have hx : x ∈ G₁ := by
        rw [← hGx]; exact Subgroup.subset_closure (by simp)
      have h1 : x * (a * b) = (a * b) * x := Subgroup.mem_centralizer_iff.mp (hc hcen) x hx
      have h2 : x⁻¹ * (a * b) * x = a * b := by
        calc x⁻¹ * (a * b) * x = x⁻¹ * ((a * b) * x) := by group
          _ = x⁻¹ * (x * (a * b)) := by rw [h1]
          _ = a * b := by group
      have h3 : x⁻¹ * (a * b) * x = a⁻¹ := by
        calc x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
          _ = b * (a⁻¹ * b⁻¹) := by rw [hA.hxa, hA.hxb]
          _ = a⁻¹ := by
              rw [← mul_assoc, show b * a⁻¹ = a⁻¹ * b from ?_]
              · group
              · have := hT.hab
                calc b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
                  _ = a⁻¹ * (b * a) * a⁻¹ := by rw [this]
                  _ = a⁻¹ * b := by group
      apply tC_ne_tA_inv
      apply hinj
      rw [map_inv, hT.emb_tA, hT.emb_tC, ← h2, h3]

end CFSG.Quasithin.F6.GoldAmL4
