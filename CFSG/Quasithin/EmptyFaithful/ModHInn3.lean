module

public import CFSG.Quasithin.EmptyFaithful.ModHInn2

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem sgp153_le (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) : Sgp153 T V₁ ≤ I :=
  le_sup_right.trans c.inH.1.1

theorem sgp153_le_normalizer_Yp (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
  have hSI := sgp153_le c
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans c.hyp.hyp.T_le
  intro s hs
  have : s ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by
    rw [c.facts.norm_eq]
    exact ⟨hSM hs, hSI hs⟩
  exact this.2

theorem hmin_prop0 (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) (hIeq : I = L ⊔ Sgp153 T V₁)
    (hYL : Yp ≤ L) (N : Subgroup (↥L ⧸ Subgroup.center ↥L)) (hNp : IsPGroup 2 ↥N) (hN1 : N ≠ ⊥)
    (hZN : img (rho0 hN hcen) Yp ⊔ img (rho0 hN hcen) (Sgp153 T V₁) ≤
      Subgroup.normalizer (N : Set (↥L ⧸ Subgroup.center ↥L)))
    (hinvN : ∀ (s : G) (hs : s ∈ Sgp153 T V₁),
      N.map (actQ hN ⟨s, sgp153_le c hs⟩).toMonoidHom = N)
    (hNtop : Subgroup.normalizer (N : Set (↥L ⧸ Subgroup.center ↥L)) ≠ ⊤) :
    Subgroup.normalizer (N : Set (↥L ⧸ Subgroup.center ↥L)) ≤
      Subgroup.normalizer ((img (rho0 hN hcen) Yp : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
        Set (↥L ⧸ Subgroup.center ↥L)) := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSI := sgp153_le c
  have hYI : Yp ≤ I := hYL.trans hLI
  have hYI0 : Yp ≤ innerPart hN := hYL.trans (le_innerPart hN hLI)
  have hker : IsPGroup 2 (rho0 hN hcen).ker := ker_rho0_isPGroup c hN hcen hIeq
  have hsurj := rho0_surjective hN hcen hLI
  set ρ := rho0 hN hcen with hρ
  set NN : Subgroup (↥L ⧸ Subgroup.center ↥L) := Subgroup.normalizer (N : Set _) with hNN
  set Nt : Subgroup ↥(innerPart hN) := N.comap ρ with hNt
  set Ntg : Subgroup G := Nt.map (innerPart hN).subtype with hNtg
  have memNtg : ∀ (g : G) (hg : g ∈ innerPart hN), g ∈ Ntg ↔ ρ ⟨g, hg⟩ ∈ N := by
    intro g hg
    constructor
    · rintro ⟨u, hu, hug⟩
      have : u = ⟨g, hg⟩ := Subtype.ext hug
      rw [this] at hu
      exact hu
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have memNtg' : ∀ g : G, g ∈ Ntg → ∃ hg : g ∈ innerPart hN, ρ ⟨g, hg⟩ ∈ N := by
    rintro g ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  have norm_of_inner : ∀ (i : G) (hi : i ∈ innerPart hN), ρ ⟨i, hi⟩ ∈ NN → i ∈ Subgroup.normalizer (Ntg : Set G) := by
    intro i hi hρi
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxI, hxN⟩ := memNtg' x hx
      have hixi : i * x * i⁻¹ ∈ innerPart hN :=
        (innerPart hN).mul_mem ((innerPart hN).mul_mem hi hxI) ((innerPart hN).inv_mem hi)
      rw [memNtg _ hixi]
      have : ρ ⟨i * x * i⁻¹, hixi⟩ = ρ ⟨i, hi⟩ * ρ ⟨x, hxI⟩ * (ρ ⟨i, hi⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this]
      exact (Subgroup.mem_normalizer_iff.1 hρi (ρ ⟨x, hxI⟩)).1 hxN
    · intro hx
      obtain ⟨hixI, hixN⟩ := memNtg' _ hx
      have hxI : x ∈ innerPart hN := by
        have := (innerPart hN).mul_mem ((innerPart hN).mul_mem ((innerPart hN).inv_mem hi) hixI) hi
        simpa [mul_assoc] using this
      rw [memNtg _ hxI]
      have h1 : ρ ⟨i * x * i⁻¹, hixI⟩ = ρ ⟨i, hi⟩ * ρ ⟨x, hxI⟩ * (ρ ⟨i, hi⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h1] at hixN
      exact (Subgroup.mem_normalizer_iff.1 hρi (ρ ⟨x, hxI⟩)).2 hixN
  have norm_to_inner : ∀ (i : G) (hi : i ∈ innerPart hN), i ∈ Subgroup.normalizer (Ntg : Set G) → ρ ⟨i, hi⟩ ∈ NN := by
    intro i hi hin
    rw [hNN, Subgroup.mem_normalizer_iff]
    intro n
    obtain ⟨x, rfl⟩ := hsurj n
    have hixi : i * x.1 * i⁻¹ ∈ innerPart hN :=
      (innerPart hN).mul_mem ((innerPart hN).mul_mem hi x.2) ((innerPart hN).inv_mem hi)
    have h1 := Subgroup.mem_normalizer_iff.1 hin x.1
    rw [memNtg _ x.2, memNtg _ hixi] at h1
    have : ρ ⟨i * x.1 * i⁻¹, hixi⟩ = ρ ⟨i, hi⟩ * ρ x * (ρ ⟨i, hi⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this] at h1
    exact h1
  have norm_of_S_fwd : ∀ (s : G) (hs : s ∈ Sgp153 T V₁) (x : G), x ∈ Ntg →
      s * x * s⁻¹ ∈ Ntg := by
    intro s hs x hx
    obtain ⟨hxI, hxN⟩ := memNtg' x hx
    have hsxI : s * x * s⁻¹ ∈ innerPart hN := innerPart_conj_mem hN (hSI hs) hxI
    rw [memNtg _ hsxI]
    have := rho0_conj hN hcen ⟨s, hSI hs⟩ ⟨x, hxI⟩
    have h2 : ρ ⟨s * x * s⁻¹, hsxI⟩ = actQ hN ⟨s, hSI hs⟩ (ρ ⟨x, hxI⟩) := this
    rw [h2]
    have : actQ hN ⟨s, hSI hs⟩ (ρ ⟨x, hxI⟩) ∈ N.map (actQ hN ⟨s, hSI hs⟩).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hxN
    rwa [hinvN s hs] at this
  have norm_of_S : ∀ (s : G), s ∈ Sgp153 T V₁ → s ∈ Subgroup.normalizer (Ntg : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨norm_of_S_fwd s hs x, fun hx => ?_⟩
    have := norm_of_S_fwd s⁻¹ ((Sgp153 T V₁).inv_mem hs) _ hx
    simpa [mul_assoc] using this
  set K : Subgroup G := Subgroup.normalizer (Ntg : Set G) ⊓ I with hK
  have hYSK : Yp ⊔ Sgp153 T V₁ ≤ K := by
    refine sup_le (fun y hy => ?_) (fun s hs => ?_)
    · refine ⟨norm_of_inner y (hYI0 hy) ?_, hYI hy⟩
      exact hZN (Subgroup.mem_sup_left (mem_img.2 ⟨y, hYI0 hy, hy, rfl⟩))
    · exact ⟨norm_of_S s hs, hSI hs⟩
  have hNtgp : IsPGroup 2 ↥Ntg := by
    intro g
    obtain ⟨u, hu, hug⟩ := g.2
    obtain ⟨a, ha⟩ := hNp ⟨ρ u, hu⟩
    have hua : u ^ (2 ^ a) ∈ ρ.ker := by
      show ρ (u ^ (2 ^ a)) = 1
      rw [map_pow]
      have := congrArg (fun z : ↥N => (z : ↥L ⧸ Subgroup.center ↥L)) ha
      simpa using this
    obtain ⟨m, hm⟩ := hker ⟨u ^ (2 ^ a), hua⟩
    refine ⟨a + m, Subtype.ext ?_⟩
    have h1 := congrArg (fun z : ↥ρ.ker => (((z : ↥(innerPart hN)) : G))) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    have h2 : ((g : ↥Ntg) : G) = (u : G) := hug.symm
    show ((g : G)) ^ (2 ^ (a + m)) = 1
    rw [h2, pow_add, pow_mul]
    simpa using h1
  have hNtgK : Ntg ≤ K := by
    intro x hx
    obtain ⟨hxI, hxN⟩ := memNtg' x hx
    exact ⟨norm_of_inner x hxI (Subgroup.le_normalizer hxN), innerPart_le hN hxI⟩
  have hNtgle : Ntg ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNtgK inf_le_left hNtgp
  have hNtg1 : Ntg ≠ ⊥ := by
    obtain ⟨⟨n, hn⟩, hn1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hN1
    have hn1 : n ≠ 1 := fun h => hn1' (Subtype.ext h)
    obtain ⟨u, hu⟩ := hsurj n
    intro hbot
    have hmem : (u : G) ∈ Ntg := (memNtg _ u.2).2 (by rw [show (⟨u.1, u.2⟩ : ↥(innerPart hN)) = u from rfl, hu]; exact hn)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : u = 1 := Subtype.ext hmem
    apply hn1
    rw [← hu, this, map_one]
  have hpc : pCoreOf 2 K ≠ ⊥ := fun h => hNtg1 (le_bot_iff.1 (h ▸ hNtgle))
  intro q hq
  obtain ⟨i, rfl⟩ := hsurj q
  have hiK : (i : G) ∈ K := ⟨norm_of_inner i.1 i.2 hq, innerPart_le hN i.2⟩
  by_cases hKM : K ≤ M
  · have hiM : (i : G) ∈ M ⊓ I := ⟨hKM hiK, innerPart_le hN i.2⟩
    have hiN : (i : G) ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by
      rw [c.facts.norm_eq]; exact hiM
    have hz : Subgroup.zpowers (i : G) ≤ Subgroup.normalizer (Yp : Set G) :=
      Subgroup.zpowers_le.2 hiN.2
    exact img_le_normalizer_img hz (mem_img.2 ⟨i.1, i.2, Subgroup.mem_zpowers _, rfl⟩)
  · exfalso
    have hHP : IsHPlus Yp (Sgp153 T V₁) M K := ⟨⟨hYSK, hpc⟩, hKM⟩
    have hKI : K = I := hmin K hHP inf_le_right
    apply hNtop
    rw [eq_top_iff]
    intro q' _
    obtain ⟨i', rfl⟩ := hsurj q'
    have hiK' : (i' : G) ∈ K := by rw [hKI]; exact innerPart_le hN i'.2
    exact norm_to_inner i'.1 i'.2 hiK'.1

end CFSG.Quasithin.ModH
