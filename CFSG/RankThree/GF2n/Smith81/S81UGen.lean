module

public import CFSG.RankThree.GF2n.Smith81.S81UDict
public import CFSG.RankThree.GF2n.Smith81.S81UTorus
public import CFSG.RankThree.GF2n.Smith81.S81UElem
public import CFSG.RankThree.GF2n.Smith81.S81A5Vt1

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

theorem covW_F_of_adm (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (x : GL (Fin 6) F) (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    (adm : Fin 6 → Fin 6 → Prop)
    (H1 : ∀ (a b : Fin 6) (hab : a ≠ b), adm a b → ∀ c : F,
      transvGL F a b hab c * x = x * transvGL F a b hab c)
    (H2 : ∀ a b : Fin 6, adm a b → adm (partner b) (partner a))
    (H3 : ∀ I : Set.powersetCard (Fin 6) 3, ∃ a ∈ I.val, ∃ b, b ∉ I.val ∧ adm a b) :
    ∀ η : Cube F, η ∈ Submodule.span F {v : Cube F |
      ∃ g ∈ Gcent σ t, ∃ η' : Cube F, v = rho F (g : GL (Fin 6) F) η' - η'} := by
  have hX : Submodule.span F {v : Cube F |
      ∃ g ∈ Gcent σ t, ∃ η' : Cube F, v = rho F (g : GL (Fin 6) F) η' - η'} = ⊤ := by
    refine eq_top_of_rho_frame_cubeBasis_mem (frameGL σ ω hω) _ ?_
    intro I
    obtain ⟨a, haI, b, hbI, hadm⟩ := H3 I
    have hab : a ≠ b := by
      rintro rfl
      exact hbI haI
    have hcomm : (b = partner a ∧ gLong hσ hω a ∈ Gcent σ t) ∨
        ∃ hb : b ≠ partner a, ∀ c : F, gShort hσ hω hab hb c ∈ Gcent σ t := by
      by_cases hb : b = partner a
      · subst hb
        exact Or.inl ⟨rfl, gLong_mem_Gcent hσ hω a ht (H1 a (partner a) hab hadm 1)⟩
      · exact Or.inr ⟨hb, fun c => gShort_mem_Gcent hσ hω hab hb ht (H1 a b hab hadm)
          (H1 (partner b) (partner a) (partner_ne_partner hab) (H2 a b hadm)) c⟩
    exact rho_frame_cubeBasis_mem_of_pair hσ hω t ht hab hcomm I haI hbI
  intro η
  rw [hX]
  exact Submodule.mem_top

theorem covC_F_of_gens (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (x : GL (Fin 6) F) (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    (adm : Fin 6 → Fin 6 → Prop)
    (H1 : ∀ (a b : Fin 6) (hab : a ≠ b), adm a b → ∀ c : F,
      transvGL F a b hab c * x = x * transvGL F a b hab c)
    (H2 : ∀ a b : Fin 6, adm a b → adm (partner b) (partner a))
    (Gens : Set (Cube F)) (hGens : LinearMap.ker (rho F x - 1) ≤ Submodule.span F Gens)
    (hG : ∀ u ∈ Gens, u ∈ LinearMap.range (rho F x - 1) ∨
      ∃ (a b : Fin 6) (hab : a ≠ b), adm a b ∧ ∃ v ∈ LinearMap.ker (rho F x - 1), Nop F a b hab v = u) :
    ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
      ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1) ⊔ Submodule.span F {v : Cube F |
        ∃ g ∈ Gcent σ t, ∃ ξ' : Cube F, rho F (t : GL (Fin 6) F) ξ' = ξ' ∧
          v = rho F (g : GL (Fin 6) F) ξ' - ξ'} := by
  intro ξ hξ
  obtain ⟨X, hXdef⟩ : ∃ X : Submodule F (Cube F), X = LinearMap.range (rho F (t : GL (Fin 6) F) - 1) ⊔
      Submodule.span F {v : Cube F | ∃ g ∈ Gcent σ t, ∃ ξ' : Cube F,
        rho F (t : GL (Fin 6) F) ξ' = ξ' ∧ v = rho F (g : GL (Fin 6) F) ξ' - ξ'} := ⟨_, rfl⟩
  have hXr : ∀ w : Cube F, rho F (t : GL (Fin 6) F) w - w ∈ X := by
    intro w
    rw [hXdef]
    exact Submodule.mem_sup_left
      (LinearMap.mem_range.mpr ⟨w, by rw [LinearMap.sub_apply, Module.End.one_apply]⟩)
  have hXg : ∀ g : SUid σ 6, g ∈ Gcent σ t → ∀ w : Cube F, rho F (t : GL (Fin 6) F) w = w →
      rho F (g : GL (Fin 6) F) w - w ∈ X := by
    intro g hg w hw
    rw [hXdef]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨g, hg, w, hw, rfl⟩)
  have hSS : ∀ v : Cube F, rho F (frameGL σ ω hω) (rho F (frameGL σ ω hω)⁻¹ v) = v := by
    intro v
    rw [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply]
  have hSS' : ∀ v : Cube F, rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω) v) = v := by
    intro v
    rw [← rho_mul_apply, inv_mul_cancel, rho_one, Module.End.one_apply]
  have hT : ∀ v : Cube F, rho F (t : GL (Fin 6) F) (rho F (frameGL σ ω hω) v) =
      rho F (frameGL σ ω hω) (rho F x v) := by
    intro v
    rw [ht, ← rho_mul_apply, ← rho_mul_apply, inv_mul_cancel_right]
  have hNopS : ∀ (v : Cube F) (a b : Fin 6) (hab : a ≠ b),
      NopS (frameGL σ ω hω) hab (rho F (frameGL σ ω hω) v) =
        rho F (frameGL σ ω hω) (Nop F a b hab v) := by
    intro v a b hab
    rw [NopS_apply, hSS']
  have hNX : ∀ w : Cube F, rho F (t : GL (Fin 6) F) w = w → ∀ (a b : Fin 6) (hab : a ≠ b),
      adm a b → NopS (frameGL σ ω hω) hab w ∈ X := by
    intro w hw a b hab hadm
    by_cases hb : b = partner a
    · subst hb
      have e : NopS (frameGL σ ω hω) hab w = rho F (gLong hσ hω a : GL (Fin 6) F) w - w :=
        (rho_gLong_sub hσ hω a w).symm
      rw [e]
      exact hXg (gLong hσ hω a)
        (gLong_mem_Gcent hσ hω a ht (H1 a (partner a) (partner_ne a).symm hadm 1)) w hw
    · have h : ∀ c : F, rho F (gShort hσ hω hab hb c : GL (Fin 6) F) w - w ∈ X := fun c =>
        hXg (gShort hσ hω hab hb c)
          (gShort_mem_Gcent hσ hω hab hb ht (H1 a b hab hadm)
            (H1 (partner b) (partner a) (partner_ne_partner hab) (H2 a b hadm)) c) w hw
      exact (NopS_mem_short hσ hω hab hb X w h).1
  have hkey : Submodule.span F Gens ≤ Submodule.comap (rho F (frameGL σ ω hω)) X := by
    rw [Submodule.span_le]
    intro u hu
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rcases hG u hu with hr | ⟨a, b, hab, hadm, v, hv, hNop⟩
    · obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hr
      have e : rho F (frameGL σ ω hω) u = rho F (t : GL (Fin 6) F) (rho F (frameGL σ ω hω) v) -
          rho F (frameGL σ ω hω) v := by
        rw [hT v, ← hv, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      rw [e]
      exact hXr _
    · have hfix : rho F x v = v := by
        have h := LinearMap.mem_ker.mp hv
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
        exact h
      rw [← hNop, ← hNopS v a b hab]
      refine hNX (rho F (frameGL σ ω hω) v) ?_ a b hab hadm
      rw [hT v, hfix]
  have hξ0 : rho F x (rho F (frameGL σ ω hω)⁻¹ ξ) = rho F (frameGL σ ω hω)⁻¹ ξ := by
    have h1 := hT (rho F (frameGL σ ω hω)⁻¹ ξ)
    rw [hSS, hξ] at h1
    rw [← hSS' (rho F x (rho F (frameGL σ ω hω)⁻¹ ξ)), ← h1]
  have hmem : rho F (frameGL σ ω hω)⁻¹ ξ ∈ Submodule.span F Gens :=
    hGens (LinearMap.mem_ker.mpr
      (by rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]; exact hξ0))
  have hfin : rho F (frameGL σ ω hω) (rho F (frameGL σ ω hω)⁻¹ ξ) ∈ X :=
    Submodule.mem_comap.mp (hkey hmem)
  rw [hSS, hXdef] at hfin
  exact hfin

@[expose] def rootFam (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    (pos : Fin 6 → Fin 6 → Prop) : Set (SUid σ 6) :=
  {g | (∃ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a) (c : F), pos a b ∧
        g = gShort hσ hω hab hb c) ∨
      (∃ (a : Fin 6) (c : F) (hc : σ c = c), pos a (partner a) ∧ g = gLongC hσ hω a c hc)}

private theorem h75_conj_comm {G : Type*} [Group G] (S P x : G) (h : P * x = x * P) :
    (S * P * S⁻¹) * (S * x * S⁻¹) = (S * x * S⁻¹) * (S * P * S⁻¹) := by
  calc (S * P * S⁻¹) * (S * x * S⁻¹) = S * (P * x) * S⁻¹ := by group
    _ = S * (x * P) * S⁻¹ := by rw [h]
    _ = (S * x * S⁻¹) * (S * P * S⁻¹) := by group

private theorem h75_inv_rho (Sf : GL (Fin 6) F) (v : Cube F) :
    rho F Sf⁻¹ (rho F Sf v) = v := by
  rw [← rho_mul_apply, inv_mul_cancel, rho_one, Module.End.one_apply]

private theorem h75_rho_inv (Sf : GL (Fin 6) F) (v : Cube F) :
    rho F Sf (rho F Sf⁻¹ v) = v := by
  rw [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply]

private theorem h75_conj_apply (Sf x : GL (Fin 6) F) (η : Cube F) :
    rho F (Sf * x * Sf⁻¹) (rho F Sf η) = rho F Sf (rho F x η) := by
  rw [rho_mul_apply, rho_mul_apply, h75_inv_rho]

private theorem h75_range_le_ker (x : GL (Fin 6) F) (hx2 : x * x = 1) {w : Cube F}
    (hw : w ∈ LinearMap.range (rho F x - 1)) : w ∈ LinearMap.ker (rho F x - 1) := by
  obtain ⟨v, rfl⟩ := hw
  have hR : ∀ u : Cube F, rho F x (rho F x u) = u := fun u => by
    rw [← rho_mul_apply, hx2, rho_one, Module.End.one_apply]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdouble : ∀ u : Cube F, u + u = 0 := fun u => by
    rw [← two_smul F u, h2, zero_smul]
  rw [LinearMap.mem_ker]
  change rho F x (rho F x v - v) - (rho F x v - v) = 0
  rw [map_sub, hR, show v - rho F x v - (rho F x v - v) = (v + v) - (rho F x v + rho F x v) by abel,
    hdouble, hdouble, sub_self]

private theorem h75_push (Sf x : GL (Fin 6) F) {r : Cube F}
    (hr : r ∈ LinearMap.range (rho F x - 1)) :
    rho F Sf r ∈ LinearMap.range (rho F (Sf * x * Sf⁻¹) - 1) := by
  obtain ⟨η, rfl⟩ := hr
  refine LinearMap.mem_range.mpr ⟨rho F Sf η, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, h75_conj_apply]

private theorem h75_decomp (Sf x t : GL (Fin 6) F) (ht : t = Sf * x * Sf⁻¹) {ξ : Cube F}
    (hξ : rho F t ξ = ξ) : ∃ ξ₀ ∈ LinearMap.ker (rho F x - 1), ξ = rho F Sf ξ₀ := by
  subst ht
  refine ⟨rho F Sf⁻¹ ξ, ?_, (h75_rho_inv Sf ξ).symm⟩
  have h1 : rho F Sf (rho F x (rho F Sf⁻¹ ξ)) = ξ := by
    rw [← h75_conj_apply, h75_rho_inv]
    exact hξ
  have h2 : rho F Sf⁻¹ (rho F Sf (rho F x (rho F Sf⁻¹ ξ))) = rho F Sf⁻¹ ξ := by
    rw [h1]
  rw [h75_inv_rho] at h2
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  exact h2

private theorem h75_longC_mem (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (a : Fin 6)
    {t : SUid σ 6} {x : GL (Fin 6) F}
    (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹) (c : F) (hc : σ c = c)
    (hx : transvGL F a (partner a) (partner_ne a).symm c * x =
      x * transvGL F a (partner a) (partner_ne a).symm c) :
    gLongC hσ hω a c hc ∈ Gcent σ t := by
  show gLongC hσ hω a c hc * t = t * gLongC hσ hω a c hc
  refine Subtype.ext ?_
  show (gLongC hσ hω a c hc : GL (Fin 6) F) * (t : GL (Fin 6) F) =
    (t : GL (Fin 6) F) * (gLongC hσ hω a c hc : GL (Fin 6) F)
  rw [ht]
  exact h75_conj_comm (frameGL σ ω hω) (transvGL F a (partner a) (partner_ne a).symm c) x hx

private theorem h75_step (x : GL (Fin 6) F) (hx2 : x * x = 1) {P Q : GL (Fin 6) F}
    (hP : ∀ ξ ∈ LinearMap.ker (rho F x - 1), rho F P ξ - ξ ∈ LinearMap.range (rho F x - 1))
    (hQ : ∀ ξ ∈ LinearMap.ker (rho F x - 1), rho F Q ξ - ξ ∈ LinearMap.range (rho F x - 1))
    {ξ₀ : Cube F} (hξ₀ : ξ₀ ∈ LinearMap.ker (rho F x - 1)) :
    rho F P (rho F Q ξ₀) - ξ₀ ∈ LinearMap.range (rho F x - 1) := by
  have hA := hQ ξ₀ hξ₀
  have hC : rho F Q ξ₀ ∈ LinearMap.ker (rho F x - 1) := by
    have e : rho F Q ξ₀ = ξ₀ + (rho F Q ξ₀ - ξ₀) := by abel
    rw [e]
    exact Submodule.add_mem _ hξ₀ (h75_range_le_ker x hx2 hA)
  have hB := hP (rho F Q ξ₀) hC
  have e : rho F P (rho F Q ξ₀) - ξ₀ =
      (rho F P (rho F Q ξ₀) - rho F Q ξ₀) + (rho F Q ξ₀ - ξ₀) := by abel
  rw [e]
  exact Submodule.add_mem _ hB hA

theorem P3_F_of_pos (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (x : GL (Fin 6) F) (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    (hx2 : x * x = 1) (pos : Fin 6 → Fin 6 → Prop)
    (hpair : ∀ a b : Fin 6, pos a b → pos (partner b) (partner a))
    (hadm : ∀ (a b : Fin 6) (hab : a ≠ b), pos a b → ∀ c : F,
      transvGL F a b hab c * x = x * transvGL F a b hab c)
    (hUC : ∀ (a b : Fin 6) (hab : a ≠ b) (c : F), pos a b → ∀ ξ ∈ LinearMap.ker (rho F x - 1),
      rho F (transvGL F a b hab c) ξ - ξ ∈ LinearMap.range (rho F x - 1))
    (hUfix : ∀ ξ ∈ LinearMap.ker (rho F x - 1),
      (∀ (a b : Fin 6) (hab : a ≠ b) (c : F), pos a b →
        rho F (transvGL F a b hab c) ξ = ξ) → ξ ∈ LinearMap.range (rho F x - 1)) :
    (∀ u ∈ rootFam hσ hω pos, u ∈ Gcent σ t) ∧
      (∀ u ∈ rootFam hσ hω pos, ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
        rho F (u : GL (Fin 6) F) ξ - ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1)) ∧
      ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
        (∀ u ∈ rootFam hσ hω pos, rho F (u : GL (Fin 6) F) ξ = ξ) →
          ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1) := by
  have hmemS : ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a) (c : F), pos a b →
      gShort hσ hω hab hb c ∈ rootFam hσ hω pos :=
    fun a b hab hb c hp => Or.inl ⟨a, b, hab, hb, c, hp, rfl⟩
  have hmemL : ∀ (a : Fin 6) (c : F) (hc : σ c = c), pos a (partner a) →
      gLongC hσ hω a c hc ∈ rootFam hσ hω pos :=
    fun a c hc hp => Or.inr ⟨a, c, hc, hp, rfl⟩
  have hpart1 : ∀ u ∈ rootFam hσ hω pos, u ∈ Gcent σ t := by
    intro u hu
    rcases hu with ⟨a, b, hab, hb, c, hp, rfl⟩ | ⟨a, c, hc, hp, rfl⟩
    · exact gShort_mem_Gcent hσ hω hab hb ht (hadm a b hab hp)
        (hadm (partner b) (partner a) (partner_ne_partner hab) (hpair a b hp)) c
    · exact h75_longC_mem hσ hω a ht c hc (hadm a (partner a) (partner_ne a).symm hp c)
  have hpart2 : ∀ u ∈ rootFam hσ hω pos, ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
      rho F (u : GL (Fin 6) F) ξ - ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1) := by
    intro u hu ξ hξ
    obtain ⟨ξ₀, hξ₀, rfl⟩ := h75_decomp (frameGL σ ω hω) x (t : GL (Fin 6) F) ht hξ
    rw [ht]
    rcases hu with ⟨a, b, hab, hb, c, hp, rfl⟩ | ⟨a, c, hc, hp, rfl⟩
    · have hr := h75_step x hx2 (hUC a b hab c hp)
        (hUC (partner b) (partner a) (partner_ne_partner hab) (σ c) (hpair a b hp)) hξ₀
      have e : rho F (gShort hσ hω hab hb c : GL (Fin 6) F) (rho F (frameGL σ ω hω) ξ₀) -
          rho F (frameGL σ ω hω) ξ₀ = rho F (frameGL σ ω hω)
            (rho F (transvGL F a b hab c)
              (rho F (transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) ξ₀) -
                ξ₀) := by
        show rho F (frameGL σ ω hω * (transvGL F a b hab c *
            transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) *
            (frameGL σ ω hω)⁻¹) (rho F (frameGL σ ω hω) ξ₀) - rho F (frameGL σ ω hω) ξ₀ = _
        rw [h75_conj_apply, rho_mul_apply, map_sub]
      rw [e]
      exact h75_push _ _ hr
    · have hr := hUC a (partner a) (partner_ne a).symm c hp ξ₀ hξ₀
      have e : rho F (gLongC hσ hω a c hc : GL (Fin 6) F) (rho F (frameGL σ ω hω) ξ₀) -
          rho F (frameGL σ ω hω) ξ₀ = rho F (frameGL σ ω hω)
            (rho F (transvGL F a (partner a) (partner_ne a).symm c) ξ₀ - ξ₀) := by
        show rho F (frameGL σ ω hω * transvGL F a (partner a) (partner_ne a).symm c *
            (frameGL σ ω hω)⁻¹) (rho F (frameGL σ ω hω) ξ₀) - rho F (frameGL σ ω hω) ξ₀ = _
        rw [h75_conj_apply, map_sub]
      rw [e]
      exact h75_push _ _ hr
  have hpart3 : ∀ ξ : Cube F, rho F (t : GL (Fin 6) F) ξ = ξ →
      (∀ u ∈ rootFam hσ hω pos, rho F (u : GL (Fin 6) F) ξ = ξ) →
        ξ ∈ LinearMap.range (rho F (t : GL (Fin 6) F) - 1) := by
    intro ξ hξ hfix
    obtain ⟨ξ₀, hξ₀, rfl⟩ := h75_decomp (frameGL σ ω hω) x (t : GL (Fin 6) F) ht hξ
    have hNop : ∀ (a b : Fin 6) (hab : a ≠ b), pos a b → Nop F a b hab ξ₀ = 0 := by
      intro a b hab hp
      by_cases hb : b = partner a
      · subst hb
        have hf := hfix _ (hmemL a 1 (map_one σ) hp)
        have h1 : rho F (frameGL σ ω hω) (rho F (transvGL F a (partner a) hab 1) ξ₀) =
            rho F (frameGL σ ω hω) ξ₀ := by
          rw [← h75_conj_apply]
          exact hf
        have h2 : rho F (transvGL F a (partner a) hab 1) ξ₀ = ξ₀ := by
          have h3 : rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω)
              (rho F (transvGL F a (partner a) hab 1) ξ₀)) =
              rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω) ξ₀) := by
            rw [h1]
          rwa [h75_inv_rho, h75_inv_rho] at h3
        simp only [Nop, LinearMap.sub_apply, Module.End.one_apply, h2, sub_self]
      · have hmem : ∀ c : F, rho F (gShort hσ hω hab hb c : GL (Fin 6) F)
            (rho F (frameGL σ ω hω) ξ₀) - rho F (frameGL σ ω hω) ξ₀ ∈
              (⊥ : Submodule F (Cube F)) := by
          intro c
          rw [Submodule.mem_bot, sub_eq_zero]
          exact hfix _ (hmemS a b hab hb c hp)
        have hN := (NopS_mem_short hσ hω hab hb ⊥ (rho F (frameGL σ ω hω) ξ₀) hmem).1
        rw [NopS_apply, h75_inv_rho, Submodule.mem_bot] at hN
        have h4 : rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω) (Nop F a b hab ξ₀)) = 0 := by
          rw [hN, map_zero]
        rwa [h75_inv_rho] at h4
    have hH : ∀ (a b : Fin 6) (hab : a ≠ b) (c : F), pos a b →
        rho F (transvGL F a b hab c) ξ₀ = ξ₀ := by
      intro a b hab c hp
      rw [rho_transvGL_eq_add_Nop, hNop a b hab hp, smul_zero, add_zero]
    have hR := hUfix ξ₀ hξ₀ hH
    rw [ht]
    exact h75_push _ _ hR
  exact ⟨hpart1, hpart2, hpart3⟩

private theorem h76_conj_comm {G : Type*} [Group G] (S P x : G) (h : P * x = x * P) :
    (S * P * S⁻¹) * (S * x * S⁻¹) = (S * x * S⁻¹) * (S * P * S⁻¹) := by
  calc (S * P * S⁻¹) * (S * x * S⁻¹) = S * (P * x) * S⁻¹ := by group
    _ = S * (x * P) * S⁻¹ := by rw [h]
    _ = (S * x * S⁻¹) * (S * P * S⁻¹) := by group

private theorem h76_dtor_mem (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (x : GL (Fin 6) F) (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, σ (d i) * d (partner i) = 1)
    (hdet : ∏ i, d i = 1)
    (hdx : (diagGL d hd : GL (Fin 6) F) * x = x * (diagGL d hd : GL (Fin 6) F)) :
    dtor hσ hω d hd hu hdet ∈ Gcent σ t := by
  show dtor hσ hω d hd hu hdet * t = t * dtor hσ hω d hd hu hdet
  refine Subtype.ext ?_
  show (frameGL σ ω hω * diagGL d hd * (frameGL σ ω hω)⁻¹) * (t : GL (Fin 6) F) =
    (t : GL (Fin 6) F) * (frameGL σ ω hω * diagGL d hd * (frameGL σ ω hω)⁻¹)
  rw [ht]
  exact h76_conj_comm (frameGL σ ω hω) (diagGL d hd : GL (Fin 6) F) x hdx

theorem gShort_eq_comm (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (x : GL (Fin 6) F) (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    {a b : Fin 6} (hab : a ≠ b) (hb : b ≠ partner a)
    (hx : ∀ c : F, transvGL F a b hab c * x = x * transvGL F a b hab c)
    (hx' : ∀ c : F, transvGL F (partner b) (partner a) (partner_ne_partner hab) c * x =
      x * transvGL F (partner b) (partner a) (partner_ne_partner hab) c)
    (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, σ (d i) * d (partner i) = 1)
    (hdet : ∏ i, d i = 1)
    (hdx : (diagGL d hd : GL (Fin 6) F) * x = x * (diagGL d hd : GL (Fin 6) F))
    (hne : d a ≠ d b) (c : F) :
    ∃ A ∈ Gcent σ t, ∃ B ∈ Gcent σ t, gShort hσ hω hab hb c = ⁅A, B⁆ := by
  have hk : d a / d b - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hne ((div_eq_one_iff_eq (hd b)).mp h))
  refine ⟨dtor hσ hω d hd hu hdet, h76_dtor_mem hσ hω t x ht d hd hu hdet hdx,
    gShort hσ hω hab hb (c / (d a / d b - 1)),
    gShort_mem_Gcent hσ hω hab hb ht hx hx' (c / (d a / d b - 1)), ?_⟩
  rw [comm_dtor_gShort hσ hω d hd hu hdet hab hb (c / (d a / d b - 1)), mul_div_cancel₀ c hk]

theorem exists_fixed_roots [Finite F] (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (S : AddSubgroup (Wform σ)) (hS : S ≠ ⊥)
    (hstab : ∀ a ∈ Gcent σ t, ∀ b ∈ Gcent σ t, ∀ s ∈ S, Wact σ ⁅a, b⁆ s ∈ S)
    (pos : Fin 6 → Fin 6 → Prop) (lev : Fin 6 → ℕ) (hlev : ∀ i, lev i ≤ 3)
    (hposlev : ∀ a b : Fin 6, pos a b → lev a < lev b ∧ lev (partner b) < lev (partner a))
    (hcomm : ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a), pos a b → ∀ c : F,
      ∃ A ∈ Gcent σ t, ∃ B ∈ Gcent σ t, gShort hσ hω hab hb c = ⁅A, B⁆) :
    ∃ s ∈ S, s ≠ 0 ∧ ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a), pos a b → ∀ c : F,
      Wact σ (gShort hσ hω hab hb c) s = s := by
  haveI : Finite (Cube F) := Module.finite_of_finite F
  have hA2 : ∀ a : Wform σ, a + a = 0 := by
    intro a
    apply Subtype.ext
    show (a : Cube F) + (a : Cube F) = 0
    rw [← two_smul F (a : Cube F), CharTwo.two_eq_zero (R := F), zero_smul]
  obtain ⟨Y, hYdef⟩ : ∃ Y : Set (Wform σ ≃ₗ[Fσ σ] Wform σ),
      Y = {y | ∃ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a) (c : F), pos a b ∧
        y = Wact σ (gShort hσ hω hab hb c)} := ⟨_, rfl⟩
  have hmem : ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a) (c : F), pos a b →
      Wact σ (gShort hσ hω hab hb c) ∈ Y := by
    intro a b hab hb c hp
    rw [hYdef]
    exact ⟨a, b, hab, hb, c, hp, rfl⟩
  have hYS : ∀ y ∈ Y, ∀ s ∈ S, y s ∈ S := by
    intro y hy s hs
    rw [hYdef] at hy
    obtain ⟨a, b, hab, hb, c, hp, rfl⟩ := hy
    obtain ⟨A, hA, B, hB, hcq⟩ := hcomm a b hab hb hp c
    rw [hcq]
    exact hstab A hA B hB s hs
  have hY : ∀ g ∈ Subgroup.closure Y, g ^ 4 = 1 := by
    obtain ⟨H, hgens, h4⟩ := exists_two_group_conj (frameGL σ ω hω) lev hlev
    obtain ⟨H', hH'⟩ : ∃ H' : Subgroup (SUid σ 6), ∀ x : SUid σ 6,
        x ∈ H' ↔ (x : GL (Fin 6) F) ∈ H := ⟨H.comap (SUid σ 6).subtype, fun x => Iff.rfl⟩
    have hgmem : ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a) (c : F), pos a b →
        gShort hσ hω hab hb c ∈ H' := by
      intro a b hab hb c hp
      obtain ⟨h1, h2⟩ := hposlev a b hp
      have e1 := hgens a b hab c h1
      have e2 := hgens (partner b) (partner a) (partner_ne_partner hab) (σ c) h2
      have hgeq : (gShort hσ hω hab hb c : GL (Fin 6) F) =
          (frameGL σ ω hω * transvGL F a b hab c * (frameGL σ ω hω)⁻¹) *
            (frameGL σ ω hω * transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c) *
              (frameGL σ ω hω)⁻¹) := by
        show frameGL σ ω hω * (transvGL F a b hab c *
          transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) * (frameGL σ ω hω)⁻¹ = _
        group
      refine (hH' _).2 ?_
      rw [hgeq]
      exact H.mul_mem e1 e2
    have hsub : Y ⊆ (H'.map (Wact σ) : Set (Wform σ ≃ₗ[Fσ σ] Wform σ)) := by
      intro y hy
      rw [hYdef] at hy
      obtain ⟨a, b, hab, hb, c, hp, rfl⟩ := hy
      exact Subgroup.mem_map_of_mem (Wact σ) (hgmem a b hab hb c hp)
    have hle : Subgroup.closure Y ≤ H'.map (Wact σ) := (Subgroup.closure_le _).2 hsub
    intro g hg
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 (hle hg)
    have hh4 : h ^ 4 = 1 := by
      apply Subtype.ext
      simpa using h4 _ ((hH' h).1 hh)
    rw [← map_pow, hh4, map_one]
  obtain ⟨s, hs, hs0, hfix⟩ :=
    exists_nonzero_fixed (R := ↥(Fσ σ)) (A := ↥(Wform σ)) hA2 S hS Y hY hYS
  exact ⟨s, hs, hs0, fun a b hab hb hp c => hfix _ (hmem a b hab hb c hp)⟩

private theorem h78_rho_rho_inv (Sf : GL (Fin 6) F) (v : Cube F) :
    rho F Sf (rho F Sf⁻¹ v) = v := by
  rw [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply]

private theorem h78_rho_inv_rho (Sf : GL (Fin 6) F) (v : Cube F) :
    rho F Sf⁻¹ (rho F Sf v) = v := by
  rw [← rho_mul_apply, inv_mul_cancel, rho_one, Module.End.one_apply]

private theorem h78_conj_range (Sf x : GL (Fin 6) F) (η : Cube F) :
    rho F Sf⁻¹ (rho F (Sf * x * Sf⁻¹) η - η) = (rho F x - 1) (rho F Sf⁻¹ η) := by
  have hc : Sf⁻¹ * (Sf * x * Sf⁻¹) = x * Sf⁻¹ := by group
  rw [map_sub, LinearMap.sub_apply, Module.End.one_apply, ← rho_mul_apply, ← rho_mul_apply, hc]

theorem P2_of_roots [Finite F] (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (x : GL (Fin 6) F) (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    (pos : Fin 6 → Fin 6 → Prop) (lev : Fin 6 → ℕ) (hlev : ∀ i, lev i ≤ 3)
    (hposlev : ∀ a b : Fin 6, pos a b → lev a < lev b ∧ lev (partner b) < lev (partner a))
    (hposb : ∀ a b : Fin 6, pos a b → b ≠ partner a)
    (hcomm : ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a), pos a b → ∀ c : F,
      ∃ A ∈ Gcent σ t, ∃ B ∈ Gcent σ t, gShort hσ hω hab hb c = ⁅A, B⁆)
    (hpure : ∀ ξ ∈ LinearMap.range (rho F x - 1),
      (∀ (a b : Fin 6) (hab : a ≠ b), pos a b → rho F (transvGL F a b hab 1) ξ = ξ) → IsPure F ξ) :
    ∀ S : AddSubgroup (Wform σ), S ≠ ⊥ → (∀ s ∈ S, s ∈ Rw σ t) →
      (∀ a ∈ Gcent σ t, ∀ b ∈ Gcent σ t, ∀ s ∈ S, Wact σ ⁅a, b⁆ s ∈ S) →
        ∃ p ∈ S, p ≠ 0 ∧ (p : Cube F) ∈ RootPt σ := by
  intro S hS hSR hstab
  obtain ⟨s, hs, hs0, hfix⟩ := exists_fixed_roots hσ hω t S hS hstab pos lev hlev hposlev hcomm
  refine ⟨s, hs, hs0, ?_⟩
  have hfixV : ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a), pos a b → ∀ c : F,
      rho F (gShort hσ hω hab hb c : GL (Fin 6) F) (s : Cube F) = (s : Cube F) := by
    intro a b hab hb hp c
    have h' : ((Wact σ (gShort hσ hω hab hb c) s : Wform σ) : Cube F) =
        ((s : Wform σ) : Cube F) := by
      rw [hfix a b hab hb hp c]
    rwa [Wact_apply] at h'
  obtain ⟨η, hη⟩ := (mem_Rw_iff hσ t s).mp (hSR s hs)
  rw [ht] at hη
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Cube F, s₀ = rho F (frameGL σ ω hω)⁻¹ (s : Cube F) := ⟨_, rfl⟩
  have hs₀R : s₀ ∈ LinearMap.range (rho F x - 1) := by
    refine LinearMap.mem_range.mpr ⟨rho F (frameGL σ ω hω)⁻¹ η, ?_⟩
    rw [hs₀, hη, h78_conj_range]
  have hs₀fix : ∀ (a b : Fin 6) (hab : a ≠ b), pos a b → rho F (transvGL F a b hab 1) s₀ = s₀ := by
    intro a b hab hp
    have hb : b ≠ partner a := hposb a b hp
    have hall : ∀ c : F, rho F (gShort hσ hω hab hb c : GL (Fin 6) F) (s : Cube F) - (s : Cube F)
        ∈ (⊥ : Submodule F (Cube F)) := by
      intro c
      rw [Submodule.mem_bot, sub_eq_zero]
      exact hfixV a b hab hb hp c
    have hmem : NopS (frameGL σ ω hω) hab (s : Cube F) ∈ (⊥ : Submodule F (Cube F)) :=
      (NopS_mem_short hσ hω hab hb (⊥ : Submodule F (Cube F)) (s : Cube F) hall).1
    rw [Submodule.mem_bot, NopS_apply, ← hs₀] at hmem
    have hN : Nop F a b hab s₀ = 0 := by
      have h3 : rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω) (Nop F a b hab s₀)) =
          rho F (frameGL σ ω hω)⁻¹ 0 := by
        rw [hmem]
      rwa [h78_rho_inv_rho, map_zero] at h3
    rw [rho_transvGL_eq_add_Nop, one_smul, hN, add_zero]
  have hpur₀ : IsPure F s₀ := hpure s₀ hs₀R hs₀fix
  have hsr : (s : Cube F) = rho F (frameGL σ ω hω) s₀ := by
    rw [hs₀, h78_rho_rho_inv]
  have hpur : IsPure F (s : Cube F) := by
    rw [hsr]
    exact hpur₀.rho _
  show (s : Cube F) ∈ Wsub σ ∧ (s : Cube F) ≠ 0 ∧ IsPure F (s : Cube F)
  exact ⟨mem_Wform_iff.mp s.2, fun h => hs0 (Subtype.ext h), hpur⟩

theorem exists_fixed_ne_zero_one {f : ℕ} [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2) (h4 : 4 ≤ 2 ^ f) :
    ∃ l : F, unitaryInvolution F 2 f l = l ∧ l ≠ 0 ∧ l ≠ 1 := by
  by_contra hcon
  have hsub : (Fσ (unitaryInvolution F 2 f) : Set F) ⊆ ({0, 1} : Set F) := by
    intro x hx
    have hx' : x ∈ Fσ (unitaryInvolution F 2 f) := hx
    by_cases h0 : x = 0
    · simp [h0]
    · by_cases h1 : x = 1
      · simp [h1]
      · exact (hcon ⟨x, mem_Fσ_iff.mp hx', h0, h1⟩).elim
  have h2 : (Fσ (unitaryInvolution F 2 f) : Set F).ncard ≤ ({0, 1} : Set F).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair (zero_ne_one : (0 : F) ≠ 1)] at h2
  have h3 : Nat.card (Fσ (unitaryInvolution F 2 f)) =
      (Fσ (unitaryInvolution F 2 f) : Set F).ncard :=
    Nat.card_coe_set_eq _
  have h5 := card_Fσ_eq hF
  omega

end CFSG.RankThree.GF2n.Smith81.U6Cube
