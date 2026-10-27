module

public import CFSG.RankThree.GF2n.Smith81.S81URoot
public import CFSG.RankThree.GF2n.Smith81.S81UModelDef

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] noncomputable def NopS (Sf : GL (Fin 6) F) {a b : Fin 6} (hab : a ≠ b) : Cube F →ₗ[F] Cube F :=
  rho F Sf ∘ₗ Nop F a b hab ∘ₗ rho F Sf⁻¹

theorem NopS_apply (Sf : GL (Fin 6) F) {a b : Fin 6} (hab : a ≠ b) (ξ : Cube F) :
    NopS Sf hab ξ = rho F Sf (Nop F a b hab (rho F Sf⁻¹ ξ)) := rfl

private theorem h66_rho_rho_inv (Sf : GL (Fin 6) F) (v : Cube F) :
    rho F Sf (rho F Sf⁻¹ v) = v := by
  rw [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply]

private theorem h66_rho_inv_rho (Sf : GL (Fin 6) F) (v : Cube F) :
    rho F Sf⁻¹ (rho F Sf v) = v := by
  rw [← rho_mul_apply, inv_mul_cancel, rho_one, Module.End.one_apply]

private theorem h66_NopS_rho (Sf : GL (Fin 6) F) {a b : Fin 6} (hab : a ≠ b) (u : Cube F) :
    NopS Sf hab (rho F Sf u) = rho F Sf (Nop F a b hab u) := by
  rw [NopS_apply, h66_rho_inv_rho]

theorem NopS_cubeBasis (Sf : GL (Fin 6) F) {a b : Fin 6} (hab : a ≠ b) (I : Set.powersetCard (Fin 6) 3)
    (h : b ∈ I.val ∧ a ∉ I.val) :
    NopS Sf hab (rho F Sf (cubeBasis F I)) = rho F Sf (cubeBasis F (replSet I a b h.1 h.2)) := by
  rw [h66_NopS_rho, Nop_cubeBasis, dif_pos h]

@[expose] noncomputable def gShort (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (hab : a ≠ b) (hb : b ≠ partner a) (c : F) : SUid σ 6 :=
  ⟨frameGL σ ω hω * (transvGL F a b hab c *
      transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) * (frameGL σ ω hω)⁻¹,
    frameConj_short_mem hσ hω hab hb c⟩

private theorem h66_rho_conj_sub (Sf x : GL (Fin 6) F) (v : Cube F) :
    rho F (Sf * x * Sf⁻¹) v - v = rho F Sf (rho F x (rho F Sf⁻¹ v) - rho F Sf⁻¹ v) := by
  rw [rho_mul_apply, rho_mul_apply, map_sub, h66_rho_rho_inv]

theorem rho_gShort_sub (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (hab : a ≠ b) (hb : b ≠ partner a) (c : F) (v : Cube F) :
    rho F (gShort hσ hω hab hb c : GL (Fin 6) F) v - v =
      c • NopS (frameGL σ ω hω) hab v +
        σ c • NopS (frameGL σ ω hω) (partner_ne_partner hab) v +
        (c * σ c) • NopS (frameGL σ ω hω) hab (NopS (frameGL σ ω hω) (partner_ne_partner hab) v) := by
  show rho F (frameGL σ ω hω * (transvGL F a b hab c *
      transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) * (frameGL σ ω hω)⁻¹) v - v = _
  rw [h66_rho_conj_sub, rho_shortRoot_sub hab c (rho F (frameGL σ ω hω)⁻¹ v)]
  have e1 : NopS (frameGL σ ω hω) hab v =
      rho F (frameGL σ ω hω) (Nop F a b hab (rho F (frameGL σ ω hω)⁻¹ v)) :=
    NopS_apply _ _ _
  have e2 : NopS (frameGL σ ω hω) (partner_ne_partner hab) v =
      rho F (frameGL σ ω hω)
        (Nop F (partner b) (partner a) (partner_ne_partner hab) (rho F (frameGL σ ω hω)⁻¹ v)) :=
    NopS_apply _ _ _
  have e3 : NopS (frameGL σ ω hω) hab (NopS (frameGL σ ω hω) (partner_ne_partner hab) v) =
      rho F (frameGL σ ω hω)
        (Nop F a b hab (Nop F (partner b) (partner a) (partner_ne_partner hab)
          (rho F (frameGL σ ω hω)⁻¹ v))) := by
    rw [e2, h66_NopS_rho]
  rw [e3, e1, e2]
  simp only [map_add, map_smul]

@[expose] noncomputable def gLong (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (a : Fin 6) :
    SUid σ 6 :=
  ⟨frameGL σ ω hω * transvGL F a (partner a) (partner_ne a).symm 1 * (frameGL σ ω hω)⁻¹,
    frameConj_long_mem hσ hω a (map_one σ)⟩

theorem rho_gLong_sub (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (a : Fin 6) (v : Cube F) :
    rho F (gLong hσ hω a : GL (Fin 6) F) v - v =
      NopS (frameGL σ ω hω) (partner_ne a).symm v := by
  show rho F (frameGL σ ω hω * transvGL F a (partner a) (partner_ne a).symm 1 * (frameGL σ ω hω)⁻¹) v - v = _
  rw [h66_rho_conj_sub, rho_transvGL_eq_add_Nop, one_smul, add_sub_cancel_left, NopS_apply]

theorem NopS_mem_short (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (hab : a ≠ b) (hb : b ≠ partner a) (X : Submodule F (Cube F)) (v : Cube F)
    (h : ∀ c : F, rho F (gShort hσ hω hab hb c : GL (Fin 6) F) v - v ∈ X) :
    NopS (frameGL σ ω hω) hab v ∈ X ∧ NopS (frameGL σ ω hω) (partner_ne_partner hab) v ∈ X := by
  have key := three_vectors hσ X (x := NopS (frameGL σ ω hω) hab v)
    (y := NopS (frameGL σ ω hω) (partner_ne_partner hab) v)
    (z := NopS (frameGL σ ω hω) hab (NopS (frameGL σ ω hω) (partner_ne_partner hab) v))
    (fun c => by
      have hc := h c
      rwa [rho_gShort_sub hσ hω hab hb c v] at hc)
  exact ⟨key.1, key.2.1⟩

private theorem h67_conj_comm {G : Type*} [Group G] (S P x : G) (h : P * x = x * P) :
    (S * P * S⁻¹) * (S * x * S⁻¹) = (S * x * S⁻¹) * (S * P * S⁻¹) := by
  calc (S * P * S⁻¹) * (S * x * S⁻¹) = S * (P * x) * S⁻¹ := by group
    _ = S * (x * P) * S⁻¹ := by rw [h]
    _ = (S * x * S⁻¹) * (S * P * S⁻¹) := by group

private theorem h67_mul_comm {G : Type*} [Monoid G] {P Q x : G} (hP : P * x = x * P)
    (hQ : Q * x = x * Q) : (P * Q) * x = x * (P * Q) := by
  calc (P * Q) * x = P * (Q * x) := mul_assoc _ _ _
    _ = P * (x * Q) := by rw [hQ]
    _ = (P * x) * Q := (mul_assoc _ _ _).symm
    _ = (x * P) * Q := by rw [hP]
    _ = x * (P * Q) := mul_assoc _ _ _

theorem gShort_mem_Gcent (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (hab : a ≠ b) (hb : b ≠ partner a) {t : SUid σ 6} {x : GL (Fin 6) F}
    (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    (hx : ∀ c : F, transvGL F a b hab c * x = x * transvGL F a b hab c)
    (hx' : ∀ c : F, transvGL F (partner b) (partner a) (partner_ne_partner hab) c * x =
      x * transvGL F (partner b) (partner a) (partner_ne_partner hab) c) (c : F) :
    gShort hσ hω hab hb c ∈ Gcent σ t := by
  show gShort hσ hω hab hb c * t = t * gShort hσ hω hab hb c
  refine Subtype.ext ?_
  show (gShort hσ hω hab hb c : GL (Fin 6) F) * (t : GL (Fin 6) F) =
    (t : GL (Fin 6) F) * (gShort hσ hω hab hb c : GL (Fin 6) F)
  rw [ht]
  exact h67_conj_comm (frameGL σ ω hω)
    (transvGL F a b hab c * transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) x
    (h67_mul_comm (hx c) (hx' (σ c)))

theorem gLong_mem_Gcent (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (a : Fin 6)
    {t : SUid σ 6} {x : GL (Fin 6) F}
    (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹)
    (hx : transvGL F a (partner a) (partner_ne a).symm 1 * x =
      x * transvGL F a (partner a) (partner_ne a).symm 1) :
    gLong hσ hω a ∈ Gcent σ t := by
  show gLong hσ hω a * t = t * gLong hσ hω a
  refine Subtype.ext ?_
  show (gLong hσ hω a : GL (Fin 6) F) * (t : GL (Fin 6) F) =
    (t : GL (Fin 6) F) * (gLong hσ hω a : GL (Fin 6) F)
  rw [ht]
  exact h67_conj_comm (frameGL σ ω hω) (transvGL F a (partner a) (partner_ne a).symm 1) x hx

private theorem h67_gen {t g : SUid σ 6} (hg : g ∈ Gcent σ t) (v : Cube F) :
    rho F (g : GL (Fin 6) F) v - v ∈ Submodule.span F
      {w : Cube F | ∃ g' ∈ Gcent σ t, ∃ η : Cube F, w = rho F (g' : GL (Fin 6) F) η - η} :=
  Submodule.subset_span ⟨g, hg, v, rfl⟩

private theorem h67_NopS_mem (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    (t : SUid σ 6) {a b : Fin 6} (hab : a ≠ b)
    (hcomm : (b = partner a ∧ gLong hσ hω a ∈ Gcent σ t) ∨
      ∃ hb : b ≠ partner a, ∀ c : F, gShort hσ hω hab hb c ∈ Gcent σ t) (v : Cube F) :
    NopS (frameGL σ ω hω) hab v ∈ Submodule.span F
      {w : Cube F | ∃ g ∈ Gcent σ t, ∃ η : Cube F, w = rho F (g : GL (Fin 6) F) η - η} := by
  rcases hcomm with ⟨hb_eq, hg⟩ | ⟨hb, hgs⟩
  · subst hb_eq
    have h1 := h67_gen hg v
    rw [rho_gLong_sub hσ hω a v] at h1
    exact h1
  · exact (NopS_mem_short hσ hω hab hb _ v (fun c => h67_gen (hgs c) v)).1

theorem rho_frame_cubeBasis_mem_of_pair (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    (t : SUid σ 6) {x : GL (Fin 6) F}
    (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * x * (frameGL σ ω hω)⁻¹) {a b : Fin 6} (hab : a ≠ b)
    (hcomm : (b = partner a ∧ gLong hσ hω a ∈ Gcent σ t) ∨
      ∃ hb : b ≠ partner a, ∀ c : F, gShort hσ hω hab hb c ∈ Gcent σ t)
    (I : Set.powersetCard (Fin 6) 3) (haI : a ∈ I.val) (hbI : b ∉ I.val) :
    rho F (frameGL σ ω hω) (cubeBasis F I) ∈
      Submodule.span F {v : Cube F | ∃ g ∈ Gcent σ t, ∃ η : Cube F, v = rho F (g : GL (Fin 6) F) η - η} := by
  have hbJ : b ∈ (replSet I b a haI hbI).val ∧ a ∉ (replSet I b a haI hbI).val :=
    replSet_mem_imp hab haI hbI rfl
  have hrep : replSet (replSet I b a haI hbI) a b hbJ.1 hbJ.2 = I :=
    (replSet_eq_iff hbJ.1 hbJ.2 haI hbI).mpr rfl
  have hN := NopS_cubeBasis (frameGL σ ω hω) hab (replSet I b a haI hbI) hbJ
  rw [hrep] at hN
  rw [← hN]
  exact h67_NopS_mem hσ hω t hab hcomm _

end CFSG.RankThree.GF2n.Smith81.U6Cube
