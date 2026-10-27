module

public import CFSG.Quasithin.Vol2.Ch11SecA15Fix
public import CFSG.Quasithin.Vol2.Ch11SecA15Lin
public import CFSG.Quasithin.Vol2.Ch11SecA15Coc
public import CFSG.Quasithin.Vol2.Ch11SecA15Kind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem cV_eq_bot_of_kindSL3 (hG2 : FactG2DerivedOrder) (h1103 : Stmt11_0_3)
    (h : Hyp11 G T L I n) (hk : KindSL3 L (fsuV T I) n) :
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨-, -, h3, -, -⟩ := h1103 G T L I n h
  rcases h3 with ⟨h0, -⟩ | ⟨hk' | hk', -⟩
  · exact h0
  · exact (kind_not_SL3_Sp4 (by have := h.one_lt; omega) hk hk').elim
  · exact (kind_not_SL3_G2 hG2 h.one_lt hk hk').elim

theorem card_fsuV_of_kindSL3 (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) (hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Nat.card (fsuV T I) = 2 ^ (3 * n) := by
  obtain ⟨hex, -, h3⟩ := h1110 G T L I n h
  obtain ⟨U₃, hU₃, -⟩ := hex 3 (by norm_num) le_rfl
  obtain ⟨U₁, hU₁, -⟩ := hex 1 le_rfl (by norm_num)
  have hV₃ : U₃ = fsuV T I := (h3 U₁ U₃ hU₁ hU₃).1 hk
  have := IsVi.relIndex_eq hU₃
  rw [hCV, Subgroup.relIndex_bot_left, hV₃] at this
  rw [this, mul_comm]

theorem irr_of_cV_eq_bot (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ J : Subgroup G, J ≤ fsuV T I → L ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = fsuV T I := by
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  intro J hJ hN
  have := hirr.2.2.2.2.2 J (hCV ▸ bot_le) hJ hN
  rwa [hCV] at this

theorem commute_of_mem_ker (h : Hyp11 G T L I n) {H : Type} [Group H] {α : ↥L →* H}
    (hα : IsModO2Surj L α) {z : G} (hz : z ∈ centerOf (T ⊓ (L ⊔ ROf T L V₁))) :
    ∀ l : ↥L, α l = 1 → (l : G) * z = z * l := by
  intro l hl
  have hl' : l ∈ CFSG.pCore 2 ↥L := hα.2 ▸ hl
  refine commute_pCoreOf_L h hz ⟨l, ?_, rfl⟩
  exact hl'

theorem ROf_eq_pCoreOf_centralizer (hF : Facts15) (hF11 : Facts11) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) {U : Subgroup G} {F : Type} [Field F] [Fintype F] {a k : ℕ}
    (hF' : Fintype.card F = 2 ^ a) {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α)
    (β : ↥U →* Multiplicative (Fin k → Fin 3 → F)) (hβs : Function.Surjective β)
    (hβi : Function.Injective β)
    (hβ : ∀ (l : ↥L) (u v : ↥U), (v : G) = l * u * l⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Multiplicative.toAdd (β u) i)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hVU : fsuV T I ≤ U)
    (hzU : ∀ z ∈ centerOf (T ⊓ (L ⊔ ROf T L V₁)), ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ U) :
    ROf T L V₁ = pCoreOf 2 ((L ⊔ ROf T L V₁) ⊓
      Subgroup.centralizer (omegaOneCenterOf (T ⊓ (L ⊔ ROf T L V₁)) : Set G)) := by
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨hk, ha⟩ := kindSL3_of_modO2Surj hG2 h1102 h hF' hα
  subst ha
  have hCV := cV_eq_bot_of_kindSL3 hG2 h1103 h hk
  have hcard : Nat.card (fsuV T I) = Fintype.card F ^ 3 := by
    rw [card_fsuV_of_kindSL3 h1110 h hk hCV, hF', ← pow_mul, mul_comm]
  set S := T ⊓ (L ⊔ ROf T L V₁) with hS
  have hZS : omegaOneCenterOf S ≤ centerOf S :=
    Subgroup.closure_le _ |>.mpr fun x hx => hx.1
  have hL₁ : ∀ z ∈ centerOf S, ∀ l ∈ LOf L V₁, l * z = z * l := by
    intro z hz
    obtain ⟨u₀, hu₀, hc⟩ := exists_mem_centralizer_of_cocycle hF' (by omega) α hα.1
      (MulEquiv.ofBijective β ⟨hβi, hβs⟩) hβ hLU (hzU z hz) (commute_of_mem_ker h hα hz)
    have hP : ∀ t ∈ T ⊓ L, t * u₀ * t⁻¹ = u₀ := by
      intro t ht
      have htz : t * z = z * t :=
        Subgroup.mem_centralizer_iff.mp hz.2 t ⟨ht.1, Subgroup.mem_sup_left ht.2⟩
      have htc : t * (u₀⁻¹ * z) = (u₀⁻¹ * z) * t :=
        Subgroup.mem_centralizer_iff.mp hc t ht.2
      have hu : u₀ = z * (u₀⁻¹ * z)⁻¹ := by group
      rw [hu]
      calc t * (z * (u₀⁻¹ * z)⁻¹) * t⁻¹ = (t * z) * (t * (u₀⁻¹ * z))⁻¹ := by group
        _ = (z * t) * ((u₀⁻¹ * z) * t)⁻¹ := by rw [htz, htc]
        _ = z * (u₀⁻¹ * z)⁻¹ := by group
    have hcent := centralizes_of_natural α β hβi hβ hLU hVU (L_le_normalizer_fsuV h)
      (irr_of_cV_eq_bot h1102 h hCV) (fsuV_ne_bot h) hcard inf_le_right lOf_le_L
      (fun v hv hfix => mem_V1_of_fixed_inf hF h1102 h hU hv hfix)
      (lOf_one_le_centralizer hF11 h1102 h hU) hu₀ hP
    intro l hl
    have h1 := hcent l hl
    have h2 : l * (u₀⁻¹ * z) = (u₀⁻¹ * z) * l :=
      Subgroup.mem_centralizer_iff.mp hc l (lOf_le_L hl)
    have hz' : z = u₀ * (u₀⁻¹ * z) := by group
    rw [hz']
    calc l * (u₀ * (u₀⁻¹ * z)) = (l * u₀ * l⁻¹) * (l * (u₀⁻¹ * z)) := by group
      _ = u₀ * ((u₀⁻¹ * z) * l) := by rw [h1, h2]
      _ = u₀ * (u₀⁻¹ * z) * l := by group
  have hle1 : LOf L V₁ ⊔ ROf T L V₁ ≤
      (L ⊔ ROf T L V₁) ⊓ Subgroup.centralizer (omegaOneCenterOf S : Set G) := by
    refine sup_le (le_inf (lOf_le_L.trans le_sup_left) fun l hl => ?_)
      (le_inf le_sup_right fun r hr => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hL₁ z (hZS hz) l hl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hZS hz).2 r
        ⟨ROf_le_T h hr, Subgroup.mem_sup_right hr⟩).symm
  have hle2 : (L ⊔ ROf T L V₁) ⊓ Subgroup.centralizer (omegaOneCenterOf S : Set G) ≤
      LOf L V₁ ⊔ ROf T L V₁ :=
    (inf_le_inf_left _
      (Subgroup.centralizer_le (V1_le_omegaOneCenter hF hF11 h1102 h hU hCV))).trans
      (msG0_inf_centralizer_le hF hG2 h1102 h hU hk hCV)
  rw [le_antisymm hle2 hle1, pCoreOf_lOf_sup_ROf h hU]

end CFSG.Quasithin.Vol2.Ch11.SecA
