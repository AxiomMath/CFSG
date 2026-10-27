module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Main

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.F6.GoldAmN

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ G₁' G₂' : Subgroup D}

omit [Finite D] in
theorem aut_conj_mem_sup {N N' : Subgroup D} (g : D)
    (hN : ∀ n ∈ N, g * n * g⁻¹ ∈ N ⊔ N') (hN' : ∀ n ∈ N', g * n * g⁻¹ ∈ N ⊔ N') :
    ∀ m ∈ N ⊔ N', g * m * g⁻¹ ∈ N ⊔ N' := by
  intro m hm
  have : N ⊔ N' ≤ (N ⊔ N').comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun n hn => hN n hn) (fun n hn => hN' n hn)
  exact this hm

omit [Finite D] in
theorem normalizer_sup_conj {K K' N : Subgroup D} (hle : K' ≤ K) (hi : K'.relIndex K = 2)
    (hKN : K' ≤ Subgroup.normalizer (N : Set D)) {τ : D} (hτK : τ ∈ K) (hτ : τ ∉ K') :
    K ≤ Subgroup.normalizer ((N ⊔ N.map (MulAut.conj τ).toMonoidHom : Subgroup D) : Set D) := by
  have hnormK' : K ≤ Subgroup.normalizer (K' : Set D) := le_normalizer_of_relIndex_two hle hi
  have hN'mem : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N.map (MulAut.conj τ).toMonoidHom := fun n hn =>
    Subgroup.mem_map_of_mem _ hn
  have hK'N : ∀ g ∈ K', ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (hKN hg) n).mp hn
  have hK'N' : ∀ g ∈ K', ∀ n' ∈ N.map (MulAut.conj τ).toMonoidHom,
      g * n' * g⁻¹ ∈ N.map (MulAut.conj τ).toMonoidHom := by
    intro g hg n' hn'
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hn'
    have hg' : τ⁻¹ * g * τ ∈ K' := by
      have := (Subgroup.mem_normalizer_iff.mp (hnormK' (K.inv_mem hτK)) g).mp hg
      simpa using this
    have h1 := hK'N _ hg' n hn
    refine ⟨_, h1, ?_⟩
    show τ * ((τ⁻¹ * g * τ) * n * (τ⁻¹ * g * τ)⁻¹) * τ⁻¹ = g * (τ * n * τ⁻¹) * g⁻¹
    group
  have hK'M : ∀ g ∈ K', ∀ m ∈ N ⊔ N.map (MulAut.conj τ).toMonoidHom,
      g * m * g⁻¹ ∈ N ⊔ N.map (MulAut.conj τ).toMonoidHom := fun g hg =>
    aut_conj_mem_sup g (fun n hn => Subgroup.mem_sup_left (hK'N g hg n hn))
      (fun n hn => Subgroup.mem_sup_right (hK'N' g hg n hn))
  have hτ2 : τ * τ ∈ K' := mul_self_mem_of_relIndex_two hi hτK
  have hτM : ∀ m ∈ N ⊔ N.map (MulAut.conj τ).toMonoidHom,
      τ * m * τ⁻¹ ∈ N ⊔ N.map (MulAut.conj τ).toMonoidHom := aut_conj_mem_sup τ
    (fun n hn => Subgroup.mem_sup_right (hN'mem n hn))
    (fun n' hn' => by
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hn'
      have h1 := hK'N _ hτ2 n hn
      have : τ * (τ * n * τ⁻¹) * τ⁻¹ = (τ * τ) * n * (τ * τ)⁻¹ := by group
      show τ * (τ * n * τ⁻¹) * τ⁻¹ ∈ N ⊔ N.map (MulAut.conj τ).toMonoidHom
      rw [this]
      exact Subgroup.mem_sup_left h1)
  have hτM' : ∀ m ∈ N ⊔ N.map (MulAut.conj τ).toMonoidHom,
      τ⁻¹ * m * τ ∈ N ⊔ N.map (MulAut.conj τ).toMonoidHom := by
    have key := aut_conj_mem_sup (N := N) (N' := N.map (MulAut.conj τ).toMonoidHom) τ⁻¹
      (fun n hn => by
        have hg : τ⁻¹ * τ⁻¹ ∈ K' := by
          have := K'.inv_mem hτ2
          simpa [mul_inv_rev] using this
        have h2 := hK'N' _ hg _ (hN'mem n hn)
        have e : τ⁻¹ * n * τ⁻¹⁻¹ = τ⁻¹ * τ⁻¹ * (τ * n * τ⁻¹) * (τ⁻¹ * τ⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.mem_sup_right h2)
      (fun n' hn' => by
        obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hn'
        have e : τ⁻¹ * (MulAut.conj τ).toMonoidHom n * τ⁻¹⁻¹ = n := by
          show τ⁻¹ * (τ * n * τ⁻¹) * τ⁻¹⁻¹ = n
          group
        rw [e]
        exact Subgroup.mem_sup_left hn)
    intro m hm
    simpa using key m hm
  intro g hg
  have hKeq := closure_union_eq_of_relIndex_two hle hi hτK hτ
  rw [← hKeq] at hg
  refine (Subgroup.closure_le (K := Subgroup.normalizer
    ((N ⊔ N.map (MulAut.conj τ).toMonoidHom : Subgroup D) : Set D))).mpr ?_ hg
  intro g hg
  rcases hg with hg | hg
  · refine mem_normalizer_of_both (hK'M g hg) (fun m hm => ?_)
    have := hK'M g⁻¹ (K'.inv_mem hg) m hm
    simpa using this
  · rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact mem_normalizer_of_both hτM hτM'

theorem SubAmalgam.eq_bot_of_normalizes (H : SubAmalgam G₁ G₂ G₁' G₂') {N : Subgroup D}
    (hN : N ≤ G₁' ⊓ G₂') (h₁ : G₁' ≤ Subgroup.normalizer (N : Set D))
    (h₂ : G₂' ≤ Subgroup.normalizer (N : Set D)) : N = ⊥ := by
  obtain ⟨τ, hτT, hτG⟩ : ∃ τ ∈ G₁ ⊓ G₂, τ ∉ G₁' := by
    by_contra hcon
    push Not at hcon
    exact H.not_T_le₁ (fun g hg => hcon g hg)
  have hτG₂ : τ ∉ G₂' := by
    intro h
    have : τ ∈ (G₁ ⊓ G₂) ⊓ G₂' := ⟨hτT, h⟩
    rw [H.T_inf₂] at this
    exact hτG this.1
  have hMT : N ⊔ N.map (MulAut.conj τ).toMonoidHom ≤ G₁ ⊓ G₂ := by
    refine sup_le (hN.trans H.T'_le_T) ?_
    rintro _ ⟨n, hn, rfl⟩
    have hnT : n ∈ G₁ ⊓ G₂ := H.T'_le_T (hN hn)
    exact (G₁ ⊓ G₂).mul_mem ((G₁ ⊓ G₂).mul_mem hτT hnT) ((G₁ ⊓ G₂).inv_mem hτT)
  have hbot := GoldAmN.eq_bot_of_normalizes_vAmalgam H.amalgam.amalgam hMT
    (normalizer_sup_conj H.le₁ H.idx₁ h₁ hτT.1 hτG)
    (normalizer_sup_conj H.le₂ H.idx₂ h₂ hτT.2 hτG₂)
  exact le_bot_iff.mp (le_sup_left.trans hbot.le)

theorem exists_A_tuple5' (hvA : Vertex G₁ (G₁ ⊓ G₂)) {G₁' : Subgroup D} (hle₁ : G₁' ≤ G₁)
    (hi₁ : G₁'.relIndex G₁ = 2) (hv₁ : Vertex G₁' (G₁' ⊓ G₂))
    (e₁ : Nonempty (↥(pCoreOf 2 G₁') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hnc : ∃ q ∈ pCoreOf 2 G₁, ∃ q' ∈ pCoreOf 2 G₁, q * q' ≠ q' * q) :
    ∃ (a b s x ρ : D) (hA : ARel a b s x) (hAρ : ARho a b s x ρ),
      Subgroup.closure ({a, b, s, ρ} : Set D) = G₁ ⊓ G₂ ∧
      Nat.card ↥(Subgroup.closure ({a, b, s, ρ} : Set D)) = 64 ∧
      Subgroup.closure ({a, b, s, ρ, x} : Set D) = G₁ ∧
      pCoreOf 2 G₁ = Q1r.map (embR hA.toTRel hAρ.toRhoRel) := by
  obtain ⟨ε⟩ := e₁
  have ε' := ε.trans prodMultEquiv
  obtain ⟨a, b, s, x, hA, hEeq, hT'eq, hG'eq⟩ := exists_A_tuple hv₁ ε'
  have hT := hA.toTRel
  have hcard' : Nat.card ↥(Subgroup.closure ({a, b, s} : Set D)) = 32 := by
    rw [hT'eq]; exact card_of_shape hv₁ ε'
  have hT'T : G₁' ⊓ G₂ ≤ G₁ ⊓ G₂ := le_inf (inf_le_left.trans hle₁) inf_le_right
  have hidxT : (G₁' ⊓ G₂).relIndex (G₁ ⊓ G₂) = 2 := by
    have h1 := Subgroup.relIndex_mul_relIndex (G₁' ⊓ G₂) G₁' G₁ inf_le_left hle₁
    have h2 := Subgroup.relIndex_mul_relIndex (G₁' ⊓ G₂) (G₁ ⊓ G₂) G₁ hT'T inf_le_left
    rw [hv₁.index_eq, hi₁] at h1
    rw [hvA.index_eq] at h2
    omega
  have hT'card : Nat.card ↥(G₁' ⊓ G₂) = 32 := card_of_shape hv₁ ε'
  have hTcard : Nat.card ↥(G₁ ⊓ G₂) = 64 := by
    have := card_eq_of_relIndex_two hT'T hidxT
    omega
  have hQ₁card : Nat.card ↥(pCoreOf 2 G₁) = 32 := by
    have := card_eq_of_relIndex_two hvA.pCoreOf_le hvA.relIndex_pCoreOf_T
    omega
  have hEcard : Nat.card ↥(pCoreOf 2 G₁') = 16 := by
    rw [Nat.card_congr ε'.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := V4)),
      Nat.card_prod, Nat.card_zmod]
  have hnormG₁ : G₁ ≤ Subgroup.normalizer (G₁' : Set D) := le_normalizer_of_relIndex_two hle₁ hi₁
  have hnormE : G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₁' : Set D) :=
    hnormG₁.trans (normalizer_le_normalizer_pCoreOf 2 G₁')
  have hQ₁G : pCoreOf 2 G₁ ≤ G₁ := pCoreOf_le 2 G₁
  have hQ₁T : pCoreOf 2 G₁ ≤ G₁ ⊓ G₂ := hvA.pCoreOf_le
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
  have hx : x ∈ G₁' := hG'eq ▸ mem_closure_four_v a b s x
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
    rw [hT'eq]
    intro t ht
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hnormG₁ hρ₀G₁) t).mp ht.1,
      G₂.mul_mem (G₂.mul_mem hρ₀G₂ ht.2) (G₂.inv_mem hρ₀G₂)⟩
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
  obtain ⟨r, hrE, hρ2, hρx, hρs, hcase⟩ := exists_rho_A hA hcard' n1 n2 n3 c1 c2
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
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  have hρs' : ρ * s = s * ρ := by
    calc ρ * s = ρ * s * (ρ * ρ) := by rw [hρ2, mul_one]
      _ = (ρ * s * ρ) * ρ := by group
      _ = s * ρ := by rw [hρs]
  rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
  ·
    have hR : RhoRel a b s ρ := ⟨hρ2, ha, hb, hρs⟩
    have hAρ : ARho a b s x ρ := ⟨hR, hρx⟩
    have hclo : Subgroup.closure ({a, b, s, ρ} : Set D) = G₁ ⊓ G₂ := by
      rw [closure_four_eq, hT'eq]
      exact closure_union_eq_of_relIndex_two hT'T hidxT hρT (fun hm => hρG₁' hm.1)
    have hcard : Nat.card ↥(Subgroup.closure ({a, b, s, ρ} : Set D)) = 64 := by
      rw [hclo]; exact hTcard
    refine ⟨a, b, s, x, ρ, hA, hAρ, hclo, hcard, ?_, ?_⟩
    ·
      have hxT : x ∉ Subgroup.closure ({a, b, s, ρ} : Set D) := by
        rw [hclo]
        exact hvA.not_mem_of_orderOf (orderOf_eq_prime hA.hx (by
          intro hx1
          have h1 := hA.hxa
          rw [hx1] at h1
          simp only [inv_one, one_mul, mul_one] at h1
          apply tA_ne_tB
          apply (hT.emb_injective hcard')
          rw [hT.emb_tA, hT.emb_tB]
          exact h1))
      have hTC : Subgroup.closure ({a, b, s, ρ} : Set D) ≤
          Subgroup.closure ({a, b, s, ρ, x} : Set D) :=
        Subgroup.closure_mono (by
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
          tauto)
      have hCG : Subgroup.closure ({a, b, s, ρ, x} : Set D) ≤ G₁ := by
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        have hmem : ∀ z ∈ ({a, b, s, ρ} : Set D), z ∈ G₁ := fun z hz => by
          have := Subgroup.subset_closure (G := D) hz
          rw [hclo] at this
          exact this.1
        rcases hg with rfl | rfl | rfl | rfl | rfl
        · exact hmem _ (by simp)
        · exact hmem _ (by simp)
        · exact hmem _ (by simp)
        · exact hmem _ (by simp)
        · exact hle₁ hx
      have hv₁' : Vertex G₁ (Subgroup.closure ({a, b, s, ρ} : Set D)) := by
        rw [hclo]; exact hvA
      exact le_antisymm hCG (hv₁'.le_of_not_mem hTC hCG (Subgroup.subset_closure (by simp)) hxT)
    ·
      have hT2 := hA.toTRel
      have hinj := embR_injective hT hAρ.toRhoRel hcard
      have hle : Q1r.map (embR hT hAρ.toRhoRel) ≤ pCoreOf 2 G₁ := by
        rintro _ ⟨w, hw, rfl⟩
        have hw' : w.e = 0 := hw
        have hbase : toTc w ∈ baseSub := mem_baseSub.mpr hw'
        have h1 : hT.emb (toTc w) ∈ pCoreOf 2 G₁ := by
          have : hT.emb (toTc w) ∈ Subgroup.closure ({a, b} : Set D) := by
            rw [closure_ab_eq hT]; exact Subgroup.mem_map_of_mem _ hbase
          rw [hEeq] at this
          exact hEQ₁ this
        rw [embR_apply]
        exact (pCoreOf 2 G₁).mul_mem h1 ((pCoreOf 2 G₁).pow_mem hρQ _)
      have hcardQ : Nat.card ↥(Q1r.map (embR hT hAρ.toRhoRel)) = 32 := by
        rw [← card_Q1r]
        exact (Nat.card_congr (Subgroup.equivMapOfInjective Q1r _ hinj).toEquiv).symm
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hQ₁card, hcardQ])).symm
  ·
    exfalso
    obtain ⟨q, hq, q', hq', hqq'⟩ := hnc
    apply hqq'
    have hEab : ∀ e ∈ Subgroup.closure ({a, b} : Set D), ∀ e' ∈ Subgroup.closure ({a, b} : Set D),
        e * e' = e' * e := by
      have hcomm : ∀ x ∈ ({a, b} : Set D), ∀ y ∈ ({a, b} : Set D), x * y = y * x := by
        intro x hx y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · exact hT.hab
        · exact hT.hab.symm
        · rfl
      intro e he e' he'
      have := Subgroup.isMulCommutative_closure
        (show ({a, b} : Set D).Pairwise Commute from fun x hx y hy _ => hcomm x hx y hy)
      exact setLike_mul_comm he he'
    have hρE : ∀ e ∈ Subgroup.closure ({a, b} : Set D), ρ * e = e * ρ := by
      intro e he
      have : Subgroup.closure ({a, b} : Set D) ≤ Subgroup.centralizer ({ρ} : Set D) := by
        rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        rcases hz with rfl | rfl
        · exact ha
        · exact hb
      exact Subgroup.mem_centralizer_iff.mp (this he) ρ rfl
    have hidxE : (pCoreOf 2 G₁').relIndex (pCoreOf 2 G₁) = 2 := by
      have h1 := Subgroup.card_mul_index ((pCoreOf 2 G₁').subgroupOf (pCoreOf 2 G₁))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ₁).toEquiv, hEcard, hQ₁card] at h1
      show ((pCoreOf 2 G₁').subgroupOf (pCoreOf 2 G₁)).index = 2
      omega
    have hρE' : ρ ∉ pCoreOf 2 G₁' := fun hm => hρG₁' (hEG₁' hm)
    have hform : ∀ g ∈ pCoreOf 2 G₁, ∃ e ∈ Subgroup.closure ({a, b} : Set D),
        g = e ∨ g = e * ρ := by
      intro g hg
      rw [hEeq]
      rcases mem_or_mul_mem_of_relIndex_two hidxE hρQ hρE' hg with h1 | h1
      · exact ⟨g, h1, Or.inl rfl⟩
      · exact ⟨g * ρ, h1, Or.inr (by rw [mul_assoc, hρ2, mul_one])⟩
    have hce : ∀ e ∈ Subgroup.closure ({a, b} : Set D), ∀ e' ∈ Subgroup.closure ({a, b} : Set D),
        Commute e e' := fun e he e' he' => hEab e he e' he'
    have hcρ : ∀ e ∈ Subgroup.closure ({a, b} : Set D), Commute ρ e := fun e he => hρE e he
    obtain ⟨e₁, he₁, hq1⟩ := hform q hq
    obtain ⟨e₂, he₂, hq2⟩ := hform q' hq'
    have h12 : Commute e₁ (e₂ * ρ) := (hce e₁ he₁ e₂ he₂).mul_right (hcρ e₁ he₁).symm
    have h21 : Commute e₂ (e₁ * ρ) := (hce e₂ he₂ e₁ he₁).mul_right (hcρ e₂ he₂).symm
    have hρ22 : Commute ρ (e₂ * ρ) := (hcρ e₂ he₂).mul_right (Commute.refl ρ)
    have h44 : Commute (e₁ * ρ) (e₂ * ρ) := h12.mul_left hρ22
    rcases hq1 with hq1 | hq1 <;> rcases hq2 with hq2 | hq2 <;> rw [hq1, hq2]
    · exact (hce e₁ he₁ e₂ he₂).eq
    · exact h12.eq
    · exact h21.eq.symm
    · exact h44.eq


theorem exists_B_tuple (H : SubAmalgam G₁ G₂ G₁' G₂') {a b s x ρ : D} (hA : ARel a b s x)
    (hAρ : ARho a b s x ρ) (hTeq : Subgroup.closure ({a, b, s, ρ} : Set D) = G₁' ⊓ G₂')
    (hcard : Nat.card ↥(Subgroup.closure ({a, b, s, ρ} : Set D)) = 64)
    (hG₁ : Subgroup.closure ({a, b, s, ρ, x} : Set D) = G₁')
    (hQ₁ : pCoreOf 2 G₁' = Q1r.map (embR hA.toTRel hAρ.toRhoRel))
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂') (QuaternionGroup 2) (QuaternionGroup 2))
    (hfpf : ∀ y ∈ G₂', y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ pCoreOf 2 G₂', y * q * y⁻¹ = q →
      ∀ v ∈ pCoreOf 2 G₂', q * v = v * q) :
    ∃ y : D, MRelB a b s ρ y ∧ Subgroup.closure ({a, b, s, ρ, y} : Set D) = G₂' ∧
      pCoreOf 2 G₂' = Q2r.map (embR hA.toTRel hAρ.toRhoRel) := by
  have hT := hA.toTRel
  have hR := hAρ.toRhoRel
  have hinj := embR_injective hT hR hcard
  set φ := embR hT hR with hφ
  have hrange : φ.range = G₁' ⊓ G₂' := by rw [embR_range hT hR, hTeq]
  have hv₂ := H.vertex₂
  have hcardT : Nat.card ↥(G₁' ⊓ G₂') = 64 := by rw [← hTeq]; exact hcard
  have hQ₂card : Nat.card ↥(pCoreOf 2 G₂') = 32 := by
    have := card_eq_of_relIndex_two hv₂.pCoreOf_le hv₂.relIndex_pCoreOf_T
    omega
  have hQ₂T : pCoreOf 2 G₂' ≤ φ.range := by rw [hrange]; exact hv₂.pCoreOf_le
  have hmapN : ((pCoreOf 2 G₂').comap φ).map φ = pCoreOf 2 G₂' :=
    Subgroup.map_comap_eq_self hQ₂T
  have hcardN : Nat.card ↥((pCoreOf 2 G₂').comap φ) = 32 := by
    have := Nat.card_congr
      (Subgroup.equivMapOfInjective ((pCoreOf 2 G₂').comap φ) φ hinj).toEquiv
    rw [this, hmapN]
    exact hQ₂card
  have hidx : ((pCoreOf 2 G₂').comap φ).index = 2 := by
    have h1 := Subgroup.card_mul_index ((pCoreOf 2 G₂').comap φ)
    rw [hcardN, card_Tr] at h1
    omega
  have hexp : ∀ w ∈ (pCoreOf 2 G₂').comap φ, w ^ 4 = 1 := by
    intro w hw
    have hw' : φ w ∈ pCoreOf 2 G₂' := hw
    have h4 := isCentralProduct_QQ_pow_four h₂ (⟨φ w, hw'⟩ : ↥(pCoreOf 2 G₂'))
    have h5 : (φ w) ^ 4 = 1 := by simpa using congrArg Subtype.val h4
    apply hinj
    rw [map_pow, h5, map_one]
  have hQ₂ : pCoreOf 2 G₂' = Q2r.map φ := by
    rcases eq_Q_of_index_two _ hidx hexp with hN1 | hN2
    · exfalso
      have hEq : pCoreOf 2 G₂' = pCoreOf 2 G₁' := by rw [hQ₁, ← hmapN, hN1]
      have h1 : G₁' ≤ Subgroup.normalizer (pCoreOf 2 G₂' : Set D) := by
        rw [hEq]; exact le_normalizer_pCoreOf 2 G₁'
      have h2 : G₂' ≤ Subgroup.normalizer (pCoreOf 2 G₂' : Set D) :=
        le_normalizer_pCoreOf 2 G₂'
      have hbot := H.eq_bot_of_normalizes hv₂.pCoreOf_le h1 h2
      rw [hbot] at hQ₂card
      simp at hQ₂card
    · rw [← hmapN, hN2]
  have hGQ : ∀ g ∈ G₂', ∀ q ∈ Q2r.map φ, g * q * g⁻¹ ∈ Q2r.map φ := by
    rw [← hQ₂]
    intro g hg q hq
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂' hg) q).mp hq
  have hC : ∀ g ∈ G₂', (∀ q ∈ Q2r.map φ, g * q = q * g) → g ∈ Q2r.map φ := by
    rw [← hQ₂]
    intro g hg hc
    apply hv₂.charTwo
    exact ⟨hg, Subgroup.mem_centralizer_iff.mpr fun q hq => (hc q hq).symm⟩
  have hfpf' : ∀ g ∈ G₂', g ≠ 1 → g ^ 3 = 1 → ∀ q ∈ Q2r.map φ, g * q * g⁻¹ = q →
      ∀ v ∈ Q2r.map φ, q * v = v * q := by
    rw [← hQ₂]
    exact hfpf
  have hv₂' : Vertex G₂' (Subgroup.closure ({a, b, s, ρ} : Set D)) := by rw [hTeq]; exact hv₂
  have hN : ¬ G₂' ≤ Subgroup.normalizer ((Nr.map φ : Subgroup D) : Set D) := by
    intro hG₂N
    have hTN := range_le_normalizer_N hT hR
    have hG₁N : G₁' ≤ Subgroup.normalizer ((Nr.map φ : Subgroup D) : Set D) := by
      rw [← hG₁, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hmem : ∀ w : Tr, φ w ∈ Subgroup.normalizer ((Nr.map φ : Subgroup D) : Set D) :=
        fun w => hTN ⟨w, rfl⟩
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · have := hmem rA; rwa [embR_rA hT hR] at this
      · have := hmem rB; rwa [embR_rB hT hR] at this
      · have := hmem rS; rwa [embR_rS hT hR] at this
      · have := hmem rR; rwa [embR_rR hT hR] at this
      · exact aRho_normalizes_N hA hAρ
    have hNT : Nr.map φ ≤ G₁' ⊓ G₂' := by
      rw [← hrange]
      exact Subgroup.map_le_range φ Nr
    have hbot := H.eq_bot_of_normalizes hNT hG₁N hG₂N
    have hmem : φ (rA * rA) ∈ Nr.map φ := Subgroup.mem_map_of_mem _ inN_rA_sq
    rw [hbot, Subgroup.mem_bot] at hmem
    exact rA_sq_ne_one (hinj (by rw [hmem, map_one]))
  obtain ⟨y', hy'G, hy'o⟩ := hv₂.exists_order_three
  have hy'3 : y' ^ 3 = 1 := hy'o ▸ pow_orderOf_eq_one y'
  have hy'1 : y' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy'o
    omega
  obtain ⟨y, hyG, hB⟩ := exists_B_elem5 hT hR hcard hv₂' hGQ hC hfpf' hN hy'G hy'3 hy'1
  have hyT : y ∉ Subgroup.closure ({a, b, s, ρ} : Set D) := by
    rw [hTeq]
    exact hv₂.not_mem_of_orderOf (orderOf_eq_prime hB.hy (hB.toMConj.ne_one hT hR hinj))
  have hTG₂ : Subgroup.closure ({a, b, s, ρ} : Set D) ≤ G₂' := by
    rw [hTeq]; exact inf_le_right
  have hTC : Subgroup.closure ({a, b, s, ρ} : Set D) ≤
      Subgroup.closure ({a, b, s, ρ, y} : Set D) :=
    Subgroup.closure_mono (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      tauto)
  have hCG : Subgroup.closure ({a, b, s, ρ, y} : Set D) ≤ G₂' := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hmem : ∀ z ∈ ({a, b, s, ρ} : Set D), z ∈ G₂' := fun z hz =>
      hTG₂ (Subgroup.subset_closure hz)
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hyG
  exact ⟨y, hB, le_antisymm hCG (hv₂'.le_of_not_mem hTC hCG (Subgroup.subset_closure (by simp))
    hyT), hQ₂⟩

theorem isGoldCaseAutM12Cat_of_shape
    (h : GoldHyp G₁ G₂)
    {G₁'' : Subgroup D} (hle₁ : G₁' ≤ G₁) (hle₂ : G₂' ≤ G₂) (hi₁ : G₁'.relIndex G₁ = 2)
    (hi₂ : G₂'.relIndex G₂ = 2) (hv₁ : Vertex G₁' (G₁' ⊓ G₂')) (hv₂ : Vertex G₂' (G₁' ⊓ G₂'))
    (hle'' : G₁'' ≤ G₁') (hi'' : G₁''.relIndex G₁' = 2) (hv'' : Vertex G₁'' (G₁'' ⊓ G₂'))
    (e₁ : Nonempty (↥(pCoreOf 2 G₁'') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hnc : ∃ q ∈ pCoreOf 2 G₁', ∃ q' ∈ pCoreOf 2 G₁', q * q' ≠ q' * q)
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂') (QuaternionGroup 2) (QuaternionGroup 2))
    (hfpf : ∀ y ∈ G₂', y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ pCoreOf 2 G₂', y * q * y⁻¹ = q →
      ∀ v ∈ pCoreOf 2 G₂', q * v = v * q) :
    IsGoldCaseAutM12Cat G₂ G₁ := by
  have H : SubAmalgam G₁ G₂ G₁' G₂' := ⟨h, hle₁, hle₂, hi₁, hi₂, hv₁, hv₂⟩
  obtain ⟨a, b, s, x, ρ, hA, hAρ, hTeq, hcard, hG₁, hQ₁⟩ :=
    exists_A_tuple5' hv₁ hle'' hi'' hv'' e₁ hnc
  obtain ⟨y, hB, hG₂, hQ₂⟩ := exists_B_tuple H hA hAρ hTeq hcard hG₁ hQ₁ h₂ hfpf
  have HH : AutHyp G₁ G₂ G₁' G₂' a b s ρ x y :=
    { toSubAmalgam := H, hA := hA, hAρ := hAρ, hB := hB, card := hcard, eT := hTeq, eG₁ := hG₁,
      eG₂ := hG₂, pCore₁ := hQ₁, pCore₂ := hQ₂ }
  exact isGoldCaseAutM12Cat_of_hyp HH h₂

end CFSG.Quasithin.F6.GoldAmL5
