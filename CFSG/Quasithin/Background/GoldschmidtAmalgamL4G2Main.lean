module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Rho
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Model

public section

namespace CFSG.Quasithin.F6.GoldAmL4

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem le_normalizer_of_relIndex_two {H K : Subgroup D} (hHK : H ≤ K) (h : H.relIndex K = 2) :
    K ≤ Subgroup.normalizer (H : Set D) := by
  have hN : (H.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two h
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN

omit [Finite D] in
theorem mem_or_mul_mem_of_relIndex_two {H K : Subgroup D} (h : H.relIndex K = 2) {ρ g : D}
    (hρK : ρ ∈ K) (hρ : ρ ∉ H) (hg : g ∈ K) : g ∈ H ∨ g * ρ ∈ H := by
  by_cases hgH : g ∈ H
  · exact Or.inl hgH
  · right
    have := Subgroup.mul_mem_iff_of_index_two (show (H.subgroupOf K).index = 2 from h)
      (a := ⟨g, hg⟩) (b := ⟨ρ, hρK⟩)
    simpa [Subgroup.mem_subgroupOf, hgH, hρ] using this

omit [Finite D] in
theorem mul_self_mem_of_relIndex_two {H K : Subgroup D} (h : H.relIndex K = 2) {g : D}
    (hg : g ∈ K) : g * g ∈ H := by
  have := Subgroup.sq_mem_of_index_two (show (H.subgroupOf K).index = 2 from h) ⟨g, hg⟩
  simpa [pow_two, Subgroup.mem_subgroupOf] using this

omit [Finite D] in
theorem inf_eq_of_relIndex_two {T T' K : Subgroup D} (hT'T : T' ≤ T) (hidx : T'.relIndex T = 2)
    (hT'K : T' ≤ K) (hnle : ¬ T ≤ K) : T ⊓ K = T' := by
  have h1 := Subgroup.relIndex_mul_relIndex T' (T ⊓ K) T (le_inf hT'T hT'K) inf_le_left
  rw [hidx] at h1
  have hdvd : (T ⊓ K).relIndex T ∣ 2 := ⟨T'.relIndex (T ⊓ K), by rw [← h1, mul_comm]⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h2 | h2
  · exfalso
    apply hnle
    have : T ≤ T ⊓ K := Subgroup.relIndex_eq_one.mp h2
    exact this.trans inf_le_right
  · rw [h2] at h1
    have h3 : T'.relIndex (T ⊓ K) = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) (le_inf hT'T hT'K)

omit [Finite D] in
theorem closure_union_eq_of_relIndex_two {H K : Subgroup D} (hHK : H ≤ K) (h : H.relIndex K = 2)
    {ρ : D} (hρK : ρ ∈ K) (hρ : ρ ∉ H) : Subgroup.closure ((H : Set D) ∪ {ρ}) = K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact hHK hg
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hρK
  · intro g hg
    rcases mem_or_mul_mem_of_relIndex_two h hρK hρ hg with hg1 | hg1
    · exact Subgroup.subset_closure (Or.inl hg1)
    · have h1 : g * ρ ∈ Subgroup.closure ((H : Set D) ∪ {ρ}) := Subgroup.subset_closure (Or.inl hg1)
      have h2 : ρ⁻¹ ∈ Subgroup.closure ((H : Set D) ∪ {ρ}) :=
        Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))
      have := Subgroup.mul_mem _ h1 h2
      simpa using this

omit [Finite D] in
theorem closure_four_eq (a b s ρ : D) :
    Subgroup.closure ({a, b, s, ρ} : Set D) =
      Subgroup.closure ((Subgroup.closure ({a, b, s} : Set D) : Set D) ∪ {ρ}) := by
  rw [← closure_union_closure]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

theorem exists_rho_tuple (h : GoldHyp G₁ G₂) {G₁' G₂' : Subgroup D} (hle₁ : G₁' ≤ G₁)
    (hle₂ : G₂' ≤ G₂) (hi₁ : G₁'.relIndex G₁ = 2) (hi₂ : G₂'.relIndex G₂ = 2)
    (hv₁ : Vertex G₁' (G₁' ⊓ G₂')) (hv₂ : Vertex G₂' (G₁' ⊓ G₂'))
    (e₁ : Nonempty (↥(pCoreOf 2 G₁') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (e₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂') (Multiplicative (ZMod 4)) (QuaternionGroup 2))
    (hsp : IsSpecialTwoOnePlusFour ↥(pCoreOf 2 G₂)) :
    ∃ a b s x y ρ : D, ARel a b s x ∧ BRel a b s y ∧ ARho a b s x ρ ∧ BRho a b s y ρ ∧
      Subgroup.closure ({a, b, s} : Set D) = G₁' ⊓ G₂' ∧
      Subgroup.closure ({a, b, s, x} : Set D) = G₁' ∧
      Subgroup.closure ({a, b, s, y} : Set D) = G₂' ∧
      Nat.card ↥(Subgroup.closure ({a, b, s} : Set D)) = 32 ∧
      ρ ∈ G₁ ⊓ G₂ ∧ ρ ∉ G₁' ∧ ρ ∉ G₂' ∧ (G₁' ⊓ G₂').relIndex (G₁ ⊓ G₂) = 2 ∧
      Nat.card ↥(pCoreOf 2 G₁) = 32 := by
  obtain ⟨ε⟩ := e₁
  have ε' := ε.trans prodMultEquiv
  obtain ⟨a, b, s, x, y, hA, hB, hTeq, hGx, hGy, hcard, hEeq⟩ :=
    exists_tuple_of_vertices hv₁ hv₂ ε' e₂
  have hT := hA.toTRel
  have hT'T : G₁' ⊓ G₂' ≤ G₁ ⊓ G₂ := le_inf (inf_le_left.trans hle₁) (inf_le_right.trans hle₂)
  have hidxT : (G₁' ⊓ G₂').relIndex (G₁ ⊓ G₂) = 2 := by
    have h1 := Subgroup.relIndex_mul_relIndex (G₁' ⊓ G₂') G₁' G₁ inf_le_left hle₁
    have h2 := Subgroup.relIndex_mul_relIndex (G₁' ⊓ G₂') (G₁ ⊓ G₂) G₁ hT'T inf_le_left
    rw [hv₁.index_eq, hi₁] at h1
    rw [h.vertex_left.index_eq] at h2
    omega
  have hQ₁card : Nat.card ↥(pCoreOf 2 G₁) = 32 := by
    have h1 := card_eq_of_relIndex_two h.pCoreOf_left_le h.relIndex_pCoreOf_T_left
    have h2 := card_eq_of_relIndex_two hT'T hidxT
    have h3 := card_of_shape hv₁ ε'
    omega
  have hEcard : Nat.card ↥(pCoreOf 2 G₁') = 16 := by
    rw [Nat.card_congr ε'.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := V4)),
      Nat.card_prod, Nat.card_zmod]
  have hnormG₁ : G₁ ≤ Subgroup.normalizer (G₁' : Set D) := le_normalizer_of_relIndex_two hle₁ hi₁
  have hnormG₂ : G₂ ≤ Subgroup.normalizer (G₂' : Set D) := le_normalizer_of_relIndex_two hle₂ hi₂
  have hnormE : G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₁' : Set D) :=
    hnormG₁.trans (normalizer_le_normalizer_pCoreOf 2 G₁')
  have hQ₁G : pCoreOf 2 G₁ ≤ G₁ := pCoreOf_le 2 G₁
  have hQ₁T : pCoreOf 2 G₁ ≤ G₁ ⊓ G₂ := h.pCoreOf_left_le
  have hEG₁' : pCoreOf 2 G₁' ≤ G₁' := pCoreOf_le 2 G₁'
  have hQ₁E : pCoreOf 2 G₁ ⊓ G₁' ≤ pCoreOf 2 G₁' := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (IsPGroup.to_le (pCoreOf_isPGroup 2 G₁) inf_le_left)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ (hle₁ hg)) u
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg : g ∈
      Subgroup.normalizer (G₁' : Set D)) u
    simp only [Subgroup.mem_inf] at h1 h2 ⊢
    exact and_congr h1 h2
  have hEQ₁ : pCoreOf 2 G₁' ≤ pCoreOf 2 G₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hEG₁'.trans hle₁) hnormE
      (pCoreOf_isPGroup 2 G₁')
  obtain ⟨ρ₀, hρ₀Q, hρ₀G⟩ : ∃ ρ₀ ∈ pCoreOf 2 G₁, ρ₀ ∉ G₁' := by
    by_contra hcon
    push Not at hcon
    have hle : pCoreOf 2 G₁ ≤ pCoreOf 2 G₁' := fun q hq => hQ₁E ⟨hq, hcon q hq⟩
    have := Subgroup.card_le_of_le hle
    omega
  have hρ₀G₁ : ρ₀ ∈ G₁ := hQ₁G hρ₀Q
  have hρ₀T : ρ₀ ∈ G₁ ⊓ G₂ := hQ₁T hρ₀Q
  have hρ₀G₂ : ρ₀ ∈ G₂ := hρ₀T.2
  have hx : x ∈ G₁' := hGx ▸ mem_closure_four_v a b s x
  have hy : y ∈ G₂' := hGy ▸ mem_closure_four_v a b s y
  have n1 : ∀ e ∈ Subgroup.closure ({a, b} : Set D),
      ρ₀ * e * ρ₀⁻¹ ∈ Subgroup.closure ({a, b} : Set D) := by
    rw [hEeq]
    intro e he
    exact (Subgroup.mem_normalizer_iff.mp (hnormE hρ₀G₁) e).mp he
  have n2 : ∀ e ∈ Subgroup.closure ({a, b} : Set D),
      ρ₀⁻¹ * e * ρ₀ ∈ Subgroup.closure ({a, b} : Set D) := by
    rw [hEeq]
    intro e he
    have := (Subgroup.mem_normalizer_iff.mp (hnormE (G₁.inv_mem hρ₀G₁)) e).mp he
    simpa using this
  have n3 : ∀ t ∈ Subgroup.closure ({a, b, s} : Set D),
      ρ₀ * t * ρ₀⁻¹ ∈ Subgroup.closure ({a, b, s} : Set D) := by
    rw [hTeq]
    intro t ht
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hnormG₁ hρ₀G₁) t).mp ht.1,
      (Subgroup.mem_normalizer_iff.mp (hnormG₂ hρ₀G₂) t).mp ht.2⟩
  have c1 : ρ₀⁻¹ * x * ρ₀ * x⁻¹ ∈ Subgroup.closure ({a, b} : Set D) := by
    rw [hEeq]
    apply hQ₁E
    constructor
    · have h1 : x * ρ₀ * x⁻¹ ∈ pCoreOf 2 G₁ :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ (hle₁ hx)) ρ₀).mp hρ₀Q
      have := Subgroup.mul_mem _ ((pCoreOf 2 G₁).inv_mem hρ₀Q) h1
      rwa [show ρ₀⁻¹ * (x * ρ₀ * x⁻¹) = ρ₀⁻¹ * x * ρ₀ * x⁻¹ by group] at this
    · have h1 : ρ₀⁻¹ * x * ρ₀ ∈ G₁' := by
        have := (Subgroup.mem_normalizer_iff.mp (hnormG₁ (G₁.inv_mem hρ₀G₁)) x).mp hx
        simpa using this
      exact G₁'.mul_mem h1 (G₁'.inv_mem hx)
  have c2 : ρ₀ * ρ₀ ∈ Subgroup.closure ({a, b} : Set D) := by
    rw [hEeq]
    apply hQ₁E
    exact ⟨(pCoreOf 2 G₁).mul_mem hρ₀Q hρ₀Q, mul_self_mem_of_relIndex_two hi₁ hρ₀G₁⟩
  obtain ⟨r, hrE, hρ2, hρx, hρs, hcase⟩ := exists_rho_A hA hcard n1 n2 n3 c1 c2
  have hrE' : r ∈ pCoreOf 2 G₁' := hEeq ▸ hrE
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = ρ₀ * r := ⟨_, rfl⟩
  rw [← hρdef] at hρ2 hρx hρs hcase
  have hρQ : ρ ∈ pCoreOf 2 G₁ := by
    rw [hρdef]; exact (pCoreOf 2 G₁).mul_mem hρ₀Q (hEQ₁ hrE')
  have hρT : ρ ∈ G₁ ⊓ G₂ := hQ₁T hρQ
  have hρG₁' : ρ ∉ G₁' := by
    intro hmem
    apply hρ₀G
    have : ρ₀ = ρ * r⁻¹ := by rw [hρdef]; group
    rw [this]
    exact G₁'.mul_mem hmem (G₁'.inv_mem (hEG₁' hrE'))
  have hρG₂' : ρ ∉ G₂' := by
    intro hmem
    have hnle : ¬ (G₁ ⊓ G₂ ≤ G₂') := by
      intro hle
      have h1 := Subgroup.relIndex_mul_relIndex (G₁ ⊓ G₂) G₂' G₂ hle hle₂
      rw [hi₂, h.vertex_right.index_eq] at h1
      omega
    have h2 := inf_eq_of_relIndex_two hT'T hidxT inf_le_right hnle
    have hρ' : ρ ∈ G₁' ⊓ G₂' := by
      rw [← h2]; exact ⟨hρT, hmem⟩
    exact hρG₁' hρ'.1
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hρs' : ρ * s = s * ρ := by
    calc ρ * s = ρ * s * (ρ * ρ) := by rw [hρ2, mul_one]
      _ = (ρ * s * ρ) * ρ := by group
      _ = s * ρ := by rw [hρs]
  have hy₂ : ρ * y * ρ ∈ Subgroup.closure ({a, b, s, y} : Set D) := by
    rw [hGy]
    have := (Subgroup.mem_normalizer_iff.mp (hnormG₂ hρT.2) y).mp hy
    rwa [hρinv] at this
  have hQ₂ := pCoreOf_right_eq' hT hcard hTeq hv₂ e₂
  have hC : ∀ g ∈ Subgroup.closure ({a, b, s, y} : Set D),
      (∀ q ∈ m2Sub.map hB.toTRel'.emb, g * q = q * g) → g ∈ m2Sub.map hB.toTRel'.emb := by
    rw [hGy]
    intro g hg hc
    have hmem : g ∈ pCoreOf 2 G₂' := by
      apply hv₂.charTwo
      refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      rw [SetLike.mem_coe, hQ₂] at hq
      exact (hc q hq).symm
    rwa [hQ₂] at hmem
  rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
  ·
    have hR : RhoRel a b s ρ := ⟨hρ2, ha, hb, hρs⟩
    have hρy := rho_y_eq hB hR hcard hy₂ hC
    exact ⟨a, b, s, x, y, ρ, hA, hB, ⟨hR, hρx⟩, ⟨hR, hρy⟩, hTeq, hGx, hGy, hcard, hρT,
      hρG₁', hρG₂', hidxT, hQ₁card⟩
  ·
    exfalso
    have hρy : ρ * y * ρ = y := rho_y_eq_one hB hρ2 hcard ha hb hρs' hy₂ hC
    have hρy' : ρ * y = y * ρ := by
      calc ρ * y = ρ * y * (ρ * ρ) := by rw [hρ2, mul_one]
        _ = (ρ * y * ρ) * ρ := by group
        _ = y * ρ := by rw [hρy]
    have hG₂'c : ∀ g ∈ G₂', ρ * g = g * ρ := by
      have : Subgroup.closure ({a, b, s, y} : Set D) ≤ Subgroup.centralizer ({ρ} : Set D) := by
        rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        rcases hz with hz | hz | hz | hz
        · rw [hz]; exact ha
        · rw [hz]; exact hb
        · rw [hz]; exact hρs'
        · rw [hz]; exact hρy'
      rw [← hGy]
      intro g hg
      exact Subgroup.mem_centralizer_iff.mp (this hg) ρ rfl
    have hG₂c : ∀ g ∈ G₂, ρ * g = g * ρ := by
      have : G₂ ≤ Subgroup.centralizer ({ρ} : Set D) := by
        rw [← closure_union_eq_of_relIndex_two hle₂ hi₂ hρT.2 hρG₂', Subgroup.closure_le]
        rintro g (hg | hg)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
          intro u hu
          rw [Set.mem_singleton_iff] at hu
          rw [hu]
          exact hG₂'c g hg
        · rw [Set.mem_singleton_iff] at hg
          rw [hg, SetLike.mem_coe, Subgroup.mem_centralizer_iff]
          intro u hu
          rw [Set.mem_singleton_iff] at hu
          rw [hu]
      intro g hg
      exact Subgroup.mem_centralizer_iff.mp (this hg) ρ rfl
    have hρO : ρ ∈ pCoreOf 2 G₂ := by
      have hord : IsPGroup 2 (Subgroup.zpowers ρ) := by
        have h1 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hρ2)
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
        · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h2]; rfl)
        · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2]; rfl)
      have hzp : ∀ g ∈ G₂, ∀ n : ℤ, g * ρ ^ n * g⁻¹ = ρ ^ n := by
        intro g hg n
        have hc : Commute g ρ := (hG₂c g hg).symm
        rw [(hc.zpow_right n).eq]
        group
      have hle : Subgroup.zpowers ρ ≤ pCoreOf 2 G₂ := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((Subgroup.zpowers_le).mpr hρT.2) ?_ hord
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · intro hu
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
          rw [hzp g hg n]
          exact Subgroup.zpow_mem_zpowers ρ n
        · intro hu
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu
          have h2 := hzp g⁻¹ (G₂.inv_mem hg) n
          rw [inv_inv] at h2
          have : u = ρ ^ n := by
            calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
              _ = g⁻¹ * ρ ^ n * g := by rw [← hn]
              _ = ρ ^ n := h2
          rw [this]
          exact Subgroup.zpow_mem_zpowers ρ n
      exact hle (Subgroup.mem_zpowers ρ)
    have hinj := hT.emb_injective hcard
    have hMQ : pCoreOf 2 G₂' ≤ pCoreOf 2 G₂ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 G₂').trans hle₂)
        (hnormG₂.trans (normalizer_le_normalizer_pCoreOf 2 G₂')) (pCoreOf_isPGroup 2 G₂')
    have hQ₂G : pCoreOf 2 G₂ ≤ G₂ := pCoreOf_le 2 G₂
    have hQ₂M : pCoreOf 2 G₂ ⊓ G₂' ≤ pCoreOf 2 G₂' := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        (IsPGroup.to_le (pCoreOf_isPGroup 2 G₂) inf_le_left)
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ (hle₂ hg)) u
      have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg : g ∈
        Subgroup.normalizer (G₂' : Set D)) u
      simp only [Subgroup.mem_inf] at h1 h2 ⊢
      exact and_congr h1 h2
    have hc_mem : a * b ∈ pCoreOf 2 G₂' := by
      rw [hQ₂]; exact ⟨tC, tC_mem, by rw [hT.emb_tC]⟩
    have hcQ : a * b ∈ pCoreOf 2 G₂ := hMQ hc_mem
    have hcM : ∀ q ∈ pCoreOf 2 G₂', (a * b) * q = q * (a * b) := by
      rw [hQ₂]
      rintro _ ⟨w, hw, rfl⟩
      rw [← hT.emb_tC, ← map_mul, ← map_mul, tC_central w]
    have hcρ : (a * b) * ρ = ρ * (a * b) := by
      calc (a * b) * ρ = a * (b * ρ) := by group
        _ = a * (ρ * b) := by rw [hb]
        _ = (a * ρ) * b := by group
        _ = (ρ * a) * b := by rw [ha]
        _ = ρ * (a * b) := by group
    have hqρρ : ∀ q : D, q * ρ * ρ = q := fun q => by rw [mul_assoc, hρ2, mul_one]
    have hcQc : ∀ q ∈ pCoreOf 2 G₂, (a * b) * q = q * (a * b) := by
      intro q hq
      rcases mem_or_mul_mem_of_relIndex_two hi₂ hρT.2 hρG₂' (hQ₂G hq) with h1 | h1
      · exact hcM q (hQ₂M ⟨hq, h1⟩)
      · have h2 := hQ₂M ⟨(pCoreOf 2 G₂).mul_mem hq hρO, h1⟩
        calc (a * b) * q = (a * b) * ((q * ρ) * ρ) := by rw [hqρρ]
          _ = ((a * b) * (q * ρ)) * ρ := by group
          _ = ((q * ρ) * (a * b)) * ρ := by rw [hcM _ h2]
          _ = (q * ρ) * ((a * b) * ρ) := by group
          _ = (q * ρ) * (ρ * (a * b)) := by rw [hcρ]
          _ = ((q * ρ) * ρ) * (a * b) := by group
          _ = q * (a * b) := by rw [hqρρ]
    have hZρ : (⟨ρ, hρO⟩ : ↥(pCoreOf 2 G₂)) ∈ Subgroup.center ↥(pCoreOf 2 G₂) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hG₂c g.1 (hQ₂G g.2)).symm
    have hZc : (⟨a * b, hcQ⟩ : ↥(pCoreOf 2 G₂)) ∈ Subgroup.center ↥(pCoreOf 2 G₂) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcQc g.1 g.2).symm
    have hZcard : Nat.card ↥(Subgroup.center ↥(pCoreOf 2 G₂)) = 2 := hsp.2.1
    obtain ⟨y₀, -, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥(pCoreOf 2 G₂)))).mp hZcard
    have hne₁ : (⟨⟨ρ, hρO⟩, hZρ⟩ : ↥(Subgroup.center ↥(pCoreOf 2 G₂))) ≠ 1 := by
      intro h1
      apply hρG₁'
      have := congrArg (fun z : ↥(Subgroup.center ↥(pCoreOf 2 G₂)) =>
        ((z : ↥(pCoreOf 2 G₂)) : D)) h1
      simp only [Subgroup.coe_one] at this
      rw [show ρ = 1 from this]
      exact G₁'.one_mem
    have hne₂ : (⟨⟨a * b, hcQ⟩, hZc⟩ : ↥(Subgroup.center ↥(pCoreOf 2 G₂))) ≠ 1 := by
      intro h1
      have := congrArg (fun z : ↥(Subgroup.center ↥(pCoreOf 2 G₂)) =>
        ((z : ↥(pCoreOf 2 G₂)) : D)) h1
      simp only [Subgroup.coe_one] at this
      apply tC_ne_one
      apply hinj
      rw [hT.emb_tC, show a * b = 1 from this, map_one]
    have e12 := (huniq _ hne₁).trans (huniq _ hne₂).symm
    have hρab : ρ = a * b := by
      have := congrArg (fun z : ↥(Subgroup.center ↥(pCoreOf 2 G₂)) =>
        ((z : ↥(pCoreOf 2 G₂)) : D)) e12
      exact this
    apply hρG₁'
    rw [hρab, ← hGx]
    exact Subgroup.mul_mem _ (mem_closure_four_a a b s x) (mem_closure_four_b a b s x)


omit [Finite D] in
theorem f112Convention_of_tuple {a b s x ρ : D} {G₁ G₂ : Subgroup D} (hA : ARel a b s x)
    (hR : RhoRel a b s ρ) (hcard : Nat.card ↥(Subgroup.closure ({a, b, s} : Set D)) = 32)
    (hT : G₂ ⊓ G₁ = Subgroup.closure ({a, b, s, ρ} : Set D)) (hx : x ∈ G₁) :
    F112Convention G₂ G₁ := by
  have hT0 := hA.toTRel
  have hinj := hT0.emb_injective hcard
  intro hc
  rcases hc with hc | hc
  · exact hc
  · exfalso
    obtain ⟨z, hz⟩ : ∃ z, z = hT0.emb (tC * tC) := ⟨_, rfl⟩
    have hzemb : ∀ w : Tc, z * hT0.emb w = hT0.emb w * z := by
      intro w
      rw [hz, ← map_mul, ← map_mul]
      congr 1
      calc tC * tC * w = tC * (tC * w) := by group
        _ = tC * (w * tC) := by rw [tC_central w]
        _ = (tC * w) * tC := by group
        _ = (w * tC) * tC := by rw [tC_central w]
        _ = w * (tC * tC) := by group
    have hzρ : z * ρ = ρ * z := by
      have h1 := hR.conj_emb hT0 (tC * tC)
      rw [sigma_tC_sq, ← hz] at h1
      calc z * ρ = (ρ * z * ρ) * ρ := by rw [h1]
        _ = ρ * z := by rw [mul_assoc, hR.hρ, mul_one]
    have hzT : z ∈ Subgroup.closure ({a, b, s, ρ} : Set D) := by
      have : z ∈ Subgroup.closure ({a, b, s} : Set D) := by
        rw [← hT0.emb_range, hz]; exact ⟨_, rfl⟩
      exact Subgroup.closure_mono (by intro g hg; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hg ⊢; tauto) this
    have hcentral : Subgroup.closure ({a, b, s, ρ} : Set D) ≤
        Subgroup.centralizer ({z} : Set D) := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      rcases hg with hg | hg | hg | hg
      · rw [hg, ← hT0.emb_tA]; exact hzemb tA
      · rw [hg, ← hT0.emb_tB]; exact hzemb tB
      · rw [hg, ← hT0.emb_tS]; exact hzemb tS
      · rw [hg]; exact hzρ
    have hzcen : z ∈ centerOf (G₂ ⊓ G₁) := by
      rw [hT]
      refine ⟨hzT, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp (hcentral ht) z rfl).symm
    have hxz : x * z = z * x := Subgroup.mem_centralizer_iff.mp (hc hzcen) x hx
    have hfix : hT0.emb (xAct (tC * tC)) = hT0.emb (tC * tC) := by
      rw [← hA.conj_emb (tC * tC) tCsq_mem_base, ← hz]
      calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
        _ = x⁻¹ * (x * z) := by rw [hxz]
        _ = z := by group
    exact xAct_tCsq (hinj hfix)

theorem isGoldCaseG22_of_index_two
    (h : GoldHyp G₁ G₂) {G₁' G₂' : Subgroup D} (hle₁ : G₁' ≤ G₁) (hle₂ : G₂' ≤ G₂)
    (hi₁ : G₁'.relIndex G₁ = 2) (hi₂ : G₂'.relIndex G₂ = 2)
    (hv₁ : Vertex G₁' (G₁' ⊓ G₂')) (hv₂ : Vertex G₂' (G₁' ⊓ G₂'))
    (e₁ : Nonempty (↥(pCoreOf 2 G₁') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (e₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂') (Multiplicative (ZMod 4)) (QuaternionGroup 2))
    (hsp : IsSpecialTwoOnePlusFour ↥(pCoreOf 2 G₂)) :
    IsGoldCaseG22 G₂ G₁ := by
  obtain ⟨a, b, s, x, y, ρ, hA, hB, hAρ, hBρ, hTeq, hGx, hGy, hcard, hρT, hρG₁', hρG₂', hidxT,
    hQ₁card⟩ := exists_rho_tuple h hle₁ hle₂ hi₁ hi₂ hv₁ hv₂ e₁ e₂ hsp
  obtain ⟨W, _, _, a', b', s', x', y', ρ', hW, hA', hB', hAρ', hBρ', hcard', hρA', hρB', hTL,
    hinf'⟩ := exists_g22_model
  have hT'T : G₁' ⊓ G₂' ≤ G₁ ⊓ G₂ := le_inf (inf_le_left.trans hle₁) (inf_le_right.trans hle₂)
  have eG₂ : Subgroup.closure ({a, b, s, y, ρ} : Set D) = G₂ := by
    rw [closure_five_eq, hGy]
    exact closure_union_eq_of_relIndex_two hle₂ hi₂ hρT.2 hρG₂'
  have eG₁ : Subgroup.closure ({a, b, s, x, ρ} : Set D) = G₁ := by
    rw [closure_five_eq, hGx]
    exact closure_union_eq_of_relIndex_two hle₁ hi₁ hρT.1 hρG₁'
  have eT : Subgroup.closure ({a, b, s, ρ} : Set D) = G₁ ⊓ G₂ := by
    rw [closure_four_eq, hTeq]
    exact closure_union_eq_of_relIndex_two hT'T hidxT hρT fun hm => hρG₁' hm.1
  have hinf : Subgroup.closure ({a, b, s, y, ρ} : Set D) ⊓
      Subgroup.closure ({a, b, s, x, ρ} : Set D) = Subgroup.closure ({a, b, s, ρ} : Set D) := by
    rw [eG₂, eG₁, eT, inf_comm]
  have hρA : ρ ∉ Subgroup.closure ({a, b, s, x} : Set D) := by rw [hGx]; exact hρG₁'
  have hρB : ρ ∉ Subgroup.closure ({a, b, s, y} : Set D) := by rw [hGy]; exact hρG₂'
  have hiso := isAmalgamIso_of_rho_tuples hA hB hA' hB' hAρ hBρ hAρ' hBρ' hcard hcard' hρA hρB
    hρA' hρB' hinf hinf'
  rw [eG₂, eG₁] at hiso
  refine ⟨⟨W, inferInstance, inferInstance, _, _, hW, hTL, hiso⟩, ?_, h.amalgam.quotient₂,
    h.amalgam.quotient₁, hsp, ?_⟩
  · refine f112Convention_of_tuple hA hBρ.toRhoRel hcard ?_ ?_
    · rw [inf_comm, ← eT]
    · exact hle₁ (hGx ▸ mem_closure_four_v a b s x)
  · rw [hQ₁card]; norm_num

end CFSG.Quasithin.F6.GoldAmL4
