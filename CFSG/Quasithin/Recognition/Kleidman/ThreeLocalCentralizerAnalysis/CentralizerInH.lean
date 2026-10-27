module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.CentralizerInQ

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem alt5_centralizer_three :
    ∀ a g : alternatingGroup (Fin 5), a ^ 3 = 1 → a ≠ 1 → g * a = a * g →
      g = 1 ∨ g = a ∨ g = a ^ 2 := by
  decide +kernel

theorem mem_pCoreOf_iff {G : Type} [Group G] (H : Subgroup G) {g : G} :
    g ∈ pCoreOf 2 H ↔ ∃ hg : g ∈ H, (⟨g, hg⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
  unfold pCoreOf
  simp only [Subgroup.mem_map, Subgroup.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hx⟩
    exact ⟨⟨g, hg⟩, hx, rfl⟩

variable {G : Type} [Group G] [Finite G] {z : G}

theorem _root_.CFSG.Quasithin.IsTypeH2.card_centralizer_inf_centralizer
    (h : IsTypeH2 G z) {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G))
    (hy3 : orderOf y = 3) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) = 24 := by
  classical
  set H := Subgroup.centralizer ({z} : Set G) with hH
  set CH : Subgroup G := H ⊓ Subgroup.centralizer ({y} : Set G) with hCH
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨hQ8, -⟩ := h.card_and_dihedral_pCoreOf_inf_centralizer hy hy3
  obtain ⟨e⟩ := h.quot
  set yH : ↥H := ⟨y, hy⟩ with hyH
  let φ : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  have hyCH : y ∈ CH := ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let incl : ↥CH →* ↥H := Subgroup.inclusion inf_le_left
  let ψ : ↥CH →* OTwoQuot H := φ.comp incl
  have hker_mem : ∀ c : ↥CH, ψ c = 1 → (c : G) ∈ pCoreOf 2 H := by
    intro c hc
    rw [mem_pCoreOf_iff]
    exact ⟨c.2.1, (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) (incl c)).mp hc⟩
  have hker_surj : ∀ g : G, g ∈ pCoreOf 2 H ⊓ Subgroup.centralizer ({y} : Set G) →
      ∃ c : ↥CH, (c : G) = g ∧ ψ c = 1 := by
    intro g hg
    obtain ⟨hgH, hgp⟩ := (mem_pCoreOf_iff H).mp hg.1
    refine ⟨⟨g, hgH, hg.2⟩, rfl, ?_⟩
    exact (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) (incl ⟨g, hgH, hg.2⟩)).mpr hgp
  have hker : Nat.card ψ.ker = 8 := by
    rw [← hQ8]
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : ψ.ker => (⟨c.1.1, hker_mem c.1 c.2, c.1.2.2⟩ :
        ↥(pCoreOf 2 H ⊓ Subgroup.centralizer ({y} : Set G)))) ⟨?_, ?_⟩)
    · intro c d hcd
      have h1 := congrArg Subtype.val hcd
      exact Subtype.ext (Subtype.ext h1)
    · intro d
      obtain ⟨c, hc1, hc2⟩ := hker_surj d.1 d.2
      exact ⟨⟨c, hc2⟩, Subtype.ext hc1⟩
  have hybar : φ yH ≠ 1 := by
    intro h1
    have h2 : yH ∈ CFSG.Open.pCore 2 ↥H := (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) yH).mp h1
    have h3 : y ∈ pCoreOf 2 H := (mem_pCoreOf_iff H).mpr ⟨hy, h2⟩
    exact not_mem_of_isPGroup_two (pCoreOf_isPGroup 2 H) hy3 h3
  have hybar3 : φ yH ^ 3 = 1 := by
    rw [← map_pow]
    have : yH ^ 3 = 1 := Subtype.ext (by simpa [hyH] using hy3')
    rw [this, map_one]
  have hordybar : orderOf (φ yH) = 3 := by
    have hd : orderOf (φ yH) ∣ 3 := orderOf_dvd_of_pow_eq_one hybar3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hybar
    · exact h1
  have hrange_le : ψ.range ≤ Subgroup.zpowers (φ yH) := by
    rintro r ⟨c, rfl⟩
    have hcy : (c : G) * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    have hcomm : ψ c * φ yH = φ yH * ψ c := by
      show φ (incl c) * φ yH = φ yH * φ (incl c)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcy
    set a : alternatingGroup (Fin 5) := e (φ yH) with ha
    have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hybar3, map_one]
    have ha1 : a ≠ 1 := by
      intro h1
      exact hybar (e.injective (by rw [← ha, h1, map_one]))
    have hgc : e (ψ c) * a = a * e (ψ c) := by
      rw [ha, ← map_mul, ← map_mul, hcomm]
    rcases alt5_centralizer_three a _ ha3 ha1 hgc with h1 | h1 | h1
    · have : ψ c = 1 := e.injective (by rw [h1, map_one])
      rw [this]; exact Subgroup.one_mem _
    · have : ψ c = φ yH := e.injective h1
      rw [this]; exact Subgroup.mem_zpowers _
    · have : ψ c = φ yH ^ 2 := e.injective (by rw [h1, map_pow])
      rw [this]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  have hzp_le : Subgroup.zpowers (φ yH) ≤ ψ.range := by
    rw [Subgroup.zpowers_le]
    exact ⟨⟨y, hyCH⟩, rfl⟩
  have hrange : Nat.card ψ.range = 3 := by
    have h1 : Nat.card ψ.range ≤ Nat.card (Subgroup.zpowers (φ yH)) :=
      Subgroup.card_le_of_le hrange_le
    have h2 : Nat.card (Subgroup.zpowers (φ yH)) ≤ Nat.card ψ.range :=
      Subgroup.card_le_of_le hzp_le
    rw [Nat.card_zpowers, hordybar] at h1 h2
    omega
  have := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at this
  omega

end CFSG.Quasithin.Kleidman.ThreeLocal
