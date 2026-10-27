module

public import CFSG.Sporadic.Recognition.JankoWongLemma14Cover

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

section KleinFour

variable {C : Type*} [Group C]

@[expose] def kleinFourSubgroup {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) : Subgroup C where
  carrier := {1, u₁, u₂, u₁ * u₂}
  one_mem' := by simp
  mul_mem' := by
    have i₁ : u₁ * u₁ = 1 := by rwa [← pow_two]
    have i₂ : u₂ * u₂ = 1 := by rwa [← pow_two]
    have e1 : u₁ * (u₁ * u₂) = u₂ := by rw [← mul_assoc, i₁, one_mul]
    have e3 : u₁ * u₂ * u₁ = u₂ := by rw [hc, mul_assoc, i₁, mul_one]
    have e4 : u₁ * u₂ * u₂ = u₁ := by rw [mul_assoc, i₂, mul_one]
    have e2 : u₂ * (u₁ * u₂) = u₁ := by
      calc u₂ * (u₁ * u₂) = (u₂ * u₁) * u₂ := (mul_assoc _ _ _).symm
        _ = (u₁ * u₂) * u₂ := by rw [← hc]
        _ = u₁ := e4
    have e5 : u₁ * u₂ * (u₁ * u₂) = 1 := by
      calc u₁ * u₂ * (u₁ * u₂) = (u₁ * u₂ * u₁) * u₂ := (mul_assoc _ _ _).symm
        _ = u₂ * u₂ := by rw [e3]
        _ = 1 := i₂
    have f1 : u₂ * u₁ = u₁ * u₂ := hc.symm
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, i₁, i₂, e1, e2, e3,
        e4, e5, f1, true_or, or_true]
  inv_mem' := by
    have i₁ : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    have i₂ : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · simp [i₁]
    · simp [i₂]
    · show (u₁ * u₂)⁻¹ ∈ ({1, u₁, u₂, u₁ * u₂} : Set C)
      rw [mul_inv_rev, i₁, i₂]
      exact Or.inr (Or.inr (Or.inr hc.symm))

theorem mem_kleinFourSubgroup {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) {x : C} :
    x ∈ kleinFourSubgroup hu₁ hu₂ hc ↔ x = 1 ∨ x = u₁ ∨ x = u₂ ∨ x = u₁ * u₂ := Iff.rfl

end KleinFour

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

@[expose] noncomputable def sdEmb : SemidihedralGroup 4 →* G :=
  c.exists_semidihedral_embedding.choose

theorem sdEmb_injective : Function.Injective c.sdEmb :=
  c.exists_semidihedral_embedding.choose_spec.1

theorem sdEmb_mem_H (x : SemidihedralGroup 4) : c.sdEmb x ∈ S.H :=
  c.exists_semidihedral_embedding.choose_spec.2.1 x

theorem sdEmb_mem_normalizer (x : SemidihedralGroup 4) :
    c.sdEmb x ∈ normalizer (c.PG : Set G) :=
  c.exists_semidihedral_embedding.choose_spec.2.2.1 x

theorem sdEmb_r_pow_four : c.sdEmb (CFSG.Semidihedral.r 4 ^ 4) = S.z :=
  c.exists_semidihedral_embedding.choose_spec.2.2.2.1

theorem sdEmb_s : c.sdEmb (CFSG.Semidihedral.s 4) = (c.d : G) :=
  c.exists_semidihedral_embedding.choose_spec.2.2.2.2.1

theorem sdEmb_r_conj_a : c.sdEmb (CFSG.Semidihedral.r 4) * (c.a : G) *
    (c.sdEmb (CFSG.Semidihedral.r 4))⁻¹ = (c.b : G) :=
  c.exists_semidihedral_embedding.choose_spec.2.2.2.2.2.1

theorem sdEmb_r_conj_b : c.sdEmb (CFSG.Semidihedral.r 4) * (c.b : G) *
    (c.sdEmb (CFSG.Semidihedral.r 4))⁻¹ = (c.a : G)⁻¹ :=
  c.exists_semidihedral_embedding.choose_spec.2.2.2.2.2.2

@[expose] noncomputable def Bg : Subgroup G := c.sdEmb.range

@[expose] noncomputable def BgEquiv : SemidihedralGroup 4 ≃* c.Bg :=
  MonoidHom.ofInjective c.sdEmb_injective

theorem card_Bg : Nat.card c.Bg = 16 := by
  have : Finite (SemidihedralGroup 4) := CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  rw [← Nat.card_congr c.BgEquiv.toEquiv, CFSG.Semidihedral.card 4 (by norm_num)]
  norm_num

theorem Bg_le_H : c.Bg ≤ S.H := by
  rintro _ ⟨x, rfl⟩
  exact c.sdEmb_mem_H x

theorem Bg_le_normalizer : c.Bg ≤ normalizer (c.PG : Set G) := by
  rintro _ ⟨x, rfl⟩
  exact c.sdEmb_mem_normalizer x

theorem z_mem_Bg : S.z ∈ c.Bg := ⟨_, c.sdEmb_r_pow_four⟩

theorem d_mem_Bg : (c.d : G) ∈ c.Bg := ⟨_, c.sdEmb_s⟩

theorem exists_mem_Bg_inv_a : ∃ e ∈ c.Bg, e * (c.a : G) * e⁻¹ = (c.a : G)⁻¹ := by
  refine ⟨c.sdEmb (CFSG.Semidihedral.r 4) * c.sdEmb (CFSG.Semidihedral.r 4),
    ⟨CFSG.Semidihedral.r 4 * CFSG.Semidihedral.r 4, map_mul _ _ _⟩, ?_⟩
  calc c.sdEmb (CFSG.Semidihedral.r 4) * c.sdEmb (CFSG.Semidihedral.r 4) * (c.a : G) *
        (c.sdEmb (CFSG.Semidihedral.r 4) * c.sdEmb (CFSG.Semidihedral.r 4))⁻¹
      = c.sdEmb (CFSG.Semidihedral.r 4) * (c.sdEmb (CFSG.Semidihedral.r 4) * (c.a : G) *
          (c.sdEmb (CFSG.Semidihedral.r 4))⁻¹) * (c.sdEmb (CFSG.Semidihedral.r 4))⁻¹ := by group
    _ = c.sdEmb (CFSG.Semidihedral.r 4) * (c.b : G) * (c.sdEmb (CFSG.Semidihedral.r 4))⁻¹ := by
        rw [c.sdEmb_r_conj_a]
    _ = (c.a : G)⁻¹ := c.sdEmb_r_conj_b

theorem isPGroup_Bg : IsPGroup 2 c.Bg := IsPGroup.of_card (n := 4) (by rw [c.card_Bg]; norm_num)

theorem Bg_inf_PG : c.Bg ⊓ c.PG = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have h2 : IsPGroup 2 (c.Bg ⊓ c.PG : Subgroup G) := c.isPGroup_Bg.to_le inf_le_left
  have h3 : IsPGroup 3 (c.Bg ⊓ c.PG : Subgroup G) := (c.hP.map S.H.subtype).to_le inf_le_right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp h2
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h3
  have h1 : Nat.card (c.Bg ⊓ c.PG : Subgroup G) = 1 := by
    have e : 2 ^ i = 3 ^ j := hi.symm.trans hj
    have hi0 : i = 0 := by
      by_contra hne
      have h2d : 2 ∣ 3 ^ j := e ▸ dvd_pow_self 2 hne
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2d)
      omega
    rw [hi, hi0]; rfl
  have hbot : (c.Bg ⊓ c.PG : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp h1
  rw [← hbot]; exact hy

@[expose] def CPH : Subgroup G := c.CP ⊓ S.H

theorem PG_le_H : c.PG ≤ S.H := by
  rintro _ ⟨p, -, rfl⟩
  exact p.2

theorem PG_le_CPH :
    c.PG ≤ c.CPH := by
  have h81 := c.card_OG_eq_81
  refine le_inf (fun y hy => c.OG_le_CP h81 (c.PG_le_OG h81 hy)) c.PG_le_H

theorem z_mem_CPH : S.z ∈ c.CPH := ⟨c.z_mem_CP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem card_CPH :
    Nat.card c.CPH = 18 := by
  have h81 := c.card_OG_eq_81
  have hOGCPH : c.OG ⊓ c.CPH = c.PG := by
    refine le_antisymm (fun y hy => ?_) (le_inf (c.PG_le_OG h81) (c.PG_le_CPH))
    rw [← c.CO_z_eq_PG h81]
    exact ⟨hy.1, hy.2.2⟩
  have hrel : c.OG.relIndex c.CPH ≤ 2 := by
    have h1 : c.OG.relIndex c.CP = 2 := by
      have := c.index_OG_CP
      exact this
    calc c.OG.relIndex c.CPH ≤ c.OG.relIndex c.CP :=
          Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h1]; norm_num)
      _ = 2 := h1
  have hmul := Subgroup.relIndex_mul_card c.OG c.CPH
  rw [hOGCPH, c.card_PG] at hmul
  have hle : Nat.card c.CPH ≤ 18 := by
    rw [← hmul]; nlinarith
  have h9 : 9 ∣ Nat.card c.CPH := by
    rw [← c.card_PG]; exact Subgroup.card_dvd_of_le c.PG_le_CPH
  have h2 : 2 ∣ Nat.card c.CPH := by
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr c.z_mem_CPH)
    rwa [Nat.card_zpowers, S.order_z] at this
  have h18 : 18 ∣ Nat.card c.CPH :=
    (show Nat.Coprime 9 2 by norm_num).mul_dvd_of_dvd_of_dvd h9 h2
  have hpos : 0 < Nat.card c.CPH := Nat.card_pos
  have := Nat.le_of_dvd hpos h18
  omega

theorem a_ne_b : (c.a : G) ≠ (c.b : G) := fun e => by
  have h := congrArg S.ρ (Subtype.ext e : c.a = c.b)
  rw [c.ha, c.hb] at h
  revert h; unfold permA3 permB3; decide

theorem a_ne_b_inv : (c.a : G) ≠ (c.b : G)⁻¹ := fun e => by
  have h := congrArg S.ρ (Subtype.ext (by simpa using e) : c.a = c.b⁻¹)
  rw [map_inv, c.ha, c.hb] at h
  revert h; unfold permA3 permB3; decide

theorem mem_CP_of_comm_ab {y : G} (ha : y * (c.a : G) = (c.a : G) * y)
    (hb : y * (c.b : G) = (c.b : G) * y) : y ∈ c.CP := by
  rw [c.mem_CP_iff]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨i, j, -, -, rfl⟩ := c.P_decomp p hp
  have hya : Commute y (c.a : G) := ha
  have hyb : Commute y (c.b : G) := hb
  have := ((hya.pow_right i).mul_right (hyb.pow_right j)).eq
  have e : (S.H.subtype (c.a ^ i * c.b ^ j)) = (c.a : G) ^ i * (c.b : G) ^ j := by simp
  rw [e]
  exact this.symm

theorem card_le_of_le_normalizer_PG (E : Subgroup G) (hE : E ≤ normalizer (c.PG : Set G)) :
    Nat.card E ≤ 8 * Nat.card (E ⊓ c.CP : Subgroup G) := by
  classical
  set K : Subgroup E := (E ⊓ c.CP).subgroupOf E with hK
  let T : Set (G × G) := {p | p.1 ∈ c.Xs ∧ p.2 ∈ c.Xs ∧ p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹}
  have hTcard : Nat.card T ≤ 8 := by
    let a : G := (c.a : G)
    let b : G := (c.b : G)
    let L : List (G × G) := [(a, b), (a, b⁻¹), (a⁻¹, b), (a⁻¹, b⁻¹), (b, a), (b, a⁻¹), (b⁻¹, a),
      (b⁻¹, a⁻¹)]
    have hsub : T ⊆ (L.toFinset : Set (G × G)) := by
      rintro ⟨x, y⟩ ⟨hx, hy, hne1, hne2⟩
      simp only [Finset.mem_coe, List.mem_toFinset, L, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false]
      have hx' : x = a ∨ x = a⁻¹ ∨ x = b ∨ x = b⁻¹ := hx
      have hy' : y = a ∨ y = a⁻¹ ∨ y = b ∨ y = b⁻¹ := hy
      rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
        simp_all
    calc Nat.card T ≤ Nat.card (L.toFinset : Set (G × G)) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ = L.toFinset.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ L.length := List.toFinset_card_le L
      _ = 8 := rfl
  have hnormP : ∀ g : E, ∀ p ∈ c.P,
      ∃ p' ∈ c.P, ((p' : S.H) : G) = (g : G) * (p : G) * (g : G)⁻¹ := by
    intro g p hp
    have hpPG : ((p : S.H) : G) ∈ c.PG := ⟨p, hp, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hE g.2) _).mp hpPG
  have hmem : ∀ g : E, ((g : G) * (c.a : G) * (g : G)⁻¹, (g : G) * (c.b : G) * (g : G)⁻¹) ∈ T := by
    intro g
    refine ⟨c.conj_mem_Xs (hnormP g) (Or.inl rfl),
      c.conj_mem_Xs (hnormP g) (Or.inr (Or.inr (Or.inl rfl))), ?_, ?_⟩
    · intro e
      apply c.a_ne_b
      have : (g : G) * (c.b : G) * (g : G)⁻¹ = (g : G) * (c.a : G) * (g : G)⁻¹ := e
      exact (mul_left_cancel (mul_right_cancel this)).symm
    · intro e
      apply c.a_ne_b_inv
      have h : (g : G) * (c.b : G) * (g : G)⁻¹ = ((g : G) * (c.a : G) * (g : G)⁻¹)⁻¹ := e
      have h' : (g : G) * (c.b : G) * (g : G)⁻¹ = (g : G) * (c.a : G)⁻¹ * (g : G)⁻¹ := by
        rw [h]; group
      have hb : (c.b : G) = (c.a : G)⁻¹ := mul_left_cancel (mul_right_cancel h')
      rw [hb, inv_inv]
  let φ : E → T := fun g => ⟨_, hmem g⟩
  have hφ : ∀ g g' : E, φ g = φ g' ↔ g⁻¹ * g' ∈ K := by
    intro g g'
    have hKmem : g⁻¹ * g' ∈ K ↔ ((g⁻¹ * g' : E) : G) ∈ c.CP := by
      rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨(g⁻¹ * g' : E).2, h⟩⟩
    rw [hKmem]
    simp only [φ, Subtype.mk.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      refine c.mem_CP_of_comm_ab ?_ ?_
      · show (g : G)⁻¹ * (g' : G) * (c.a : G) = (c.a : G) * ((g : G)⁻¹ * (g' : G))
        calc (g : G)⁻¹ * (g' : G) * (c.a : G)
            = (g : G)⁻¹ * ((g' : G) * (c.a : G) * (g' : G)⁻¹) * (g' : G) := by group
          _ = (g : G)⁻¹ * ((g : G) * (c.a : G) * (g : G)⁻¹) * (g' : G) := by rw [← h1]
          _ = (c.a : G) * ((g : G)⁻¹ * (g' : G)) := by group
      · show (g : G)⁻¹ * (g' : G) * (c.b : G) = (c.b : G) * ((g : G)⁻¹ * (g' : G))
        calc (g : G)⁻¹ * (g' : G) * (c.b : G)
            = (g : G)⁻¹ * ((g' : G) * (c.b : G) * (g' : G)⁻¹) * (g' : G) := by group
          _ = (g : G)⁻¹ * ((g : G) * (c.b : G) * (g : G)⁻¹) * (g' : G) := by rw [← h2]
          _ = (c.b : G) * ((g : G)⁻¹ * (g' : G)) := by group
    · intro h
      have hab := c.mem_CP_iff.mp h (c.a : G) c.a_mem_PG
      have hbb := c.mem_CP_iff.mp h (c.b : G) ⟨c.b, c.hbP, rfl⟩
      have hc : ((g⁻¹ * g' : E) : G) = (g : G)⁻¹ * (g' : G) := by simp
      rw [hc] at hab hbb
      have hu_a : ((g : G)⁻¹ * (g' : G)) * (c.a : G) * ((g : G)⁻¹ * (g' : G))⁻¹ = (c.a : G) := by
        rw [mul_inv_eq_iff_eq_mul]; exact hab.symm
      have hu_b : ((g : G)⁻¹ * (g' : G)) * (c.b : G) * ((g : G)⁻¹ * (g' : G))⁻¹ = (c.b : G) := by
        rw [mul_inv_eq_iff_eq_mul]; exact hbb.symm
      constructor
      · calc (g : G) * (c.a : G) * (g : G)⁻¹
            = (g : G) * (((g : G)⁻¹ * (g' : G)) * (c.a : G) * ((g : G)⁻¹ * (g' : G))⁻¹) *
                (g : G)⁻¹ := by rw [hu_a]
          _ = (g' : G) * (c.a : G) * (g' : G)⁻¹ := by group
      · calc (g : G) * (c.b : G) * (g : G)⁻¹
            = (g : G) * (((g : G)⁻¹ * (g' : G)) * (c.b : G) * ((g : G)⁻¹ * (g' : G))⁻¹) *
                (g : G)⁻¹ := by rw [hu_b]
          _ = (g' : G) * (c.b : G) * (g' : G)⁻¹ := by group
  let f : E ⧸ K → T :=
    Quotient.lift φ (fun g g' h => (hφ g g').mpr (QuotientGroup.leftRel_apply.mp h))
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    rename_i g g'
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hφ g g').mp hxy))
  have hidx : Nat.card (E ⧸ K) ≤ 8 := (Nat.card_le_card_of_injective f hf).trans hTcard
  have hKcard : Nat.card K = Nat.card (E ⊓ c.CP : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ c.CP ≤ E)).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, hKcard]
  exact Nat.mul_le_mul_right _ hidx

@[expose] def NH : Subgroup G := normalizer (c.PG : Set G) ⊓ S.H

theorem PG_le_NH : c.PG ≤ c.NH := le_inf Subgroup.le_normalizer c.PG_le_H

theorem Bg_le_NH : c.Bg ≤ c.NH := le_inf c.Bg_le_normalizer c.Bg_le_H

theorem NH_inf_CP_le_CPH : c.NH ⊓ c.CP ≤ c.CPH := fun _ hy => ⟨hy.2, hy.1.2⟩

theorem card_NH_le :
    Nat.card c.NH ≤ 144 := by
  have h1 := c.card_le_of_le_normalizer_PG c.NH inf_le_left
  have h2 : Nat.card (c.NH ⊓ c.CP : Subgroup G) ≤ 18 := by
    rw [← c.card_CPH]; exact Subgroup.card_le_of_le c.NH_inf_CP_le_CPH
  omega

theorem card_NH :
    Nat.card c.NH = 144 := by
  have h9 : 9 ∣ Nat.card c.NH := by
    rw [← c.card_PG]; exact Subgroup.card_dvd_of_le c.PG_le_NH
  have h16 : 16 ∣ Nat.card c.NH := by
    rw [← c.card_Bg]; exact Subgroup.card_dvd_of_le c.Bg_le_NH
  have h144 : 144 ∣ Nat.card c.NH :=
    (show Nat.Coprime 9 16 by norm_num).mul_dvd_of_dvd_of_dvd h9 h16
  have hpos : 0 < Nat.card c.NH := Nat.card_pos
  have := Nat.le_of_dvd hpos h144
  have := c.card_NH_le
  omega

theorem NH_eq_mul :
    ∀ g ∈ c.NH, ∃ p ∈ c.PG, ∃ b ∈ c.Bg, g = p * b := by
  classical
  let f : c.PG × c.Bg → c.NH := fun q =>
    ⟨(q.1 : G) * (q.2 : G), c.NH.mul_mem (c.PG_le_NH q.1.2) (c.Bg_le_NH q.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨p, hp⟩, ⟨b, hb⟩⟩ ⟨⟨p', hp'⟩, ⟨b', hb'⟩⟩ h
    have h1 : p * b = p' * b' := congrArg Subtype.val h
    have h2 : p'⁻¹ * p = b' * b⁻¹ := by
      calc p'⁻¹ * p = p'⁻¹ * (p * b) * b⁻¹ := by group
        _ = p'⁻¹ * (p' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have hmem : p'⁻¹ * p ∈ c.Bg ⊓ c.PG :=
      ⟨by rw [h2]; exact c.Bg.mul_mem hb' (c.Bg.inv_mem hb), c.PG.mul_mem (c.PG.inv_mem hp') hp⟩
    rw [c.Bg_inf_PG] at hmem
    have h3 : p'⁻¹ * p = 1 := hmem
    have hpp : p = p' := by
      calc p = p' * (p'⁻¹ * p) := by group
        _ = p' := by rw [h3, mul_one]
    have hbb : b = b' := by
      rw [hpp] at h1
      exact (mul_left_cancel h1)
    subst hpp; subst hbb; rfl
  have hcard : Nat.card c.NH ≤ Nat.card (c.PG × c.Bg) := by
    rw [Nat.card_prod, c.card_PG, c.card_Bg, c.card_NH]
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, by
    rw [Nat.card_prod, c.card_PG, c.card_Bg, c.card_NH]⟩
  intro g hg
  obtain ⟨⟨p, b⟩, hpb⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨p, p.2, b, b.2, (congrArg Subtype.val hpb).symm⟩

theorem mem_PG_of_odd_NH
    {g : G} (hg : g ∈ c.NH) (hodd : Odd (orderOf g)) :
    g ∈ c.PG := by
  have hle : c.PG ≤ c.NH := c.PG_le_NH
  have hnorm : (c.PG.subgroupOf c.NH).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp hk.1 h).mp hh
  have hquot : IsPGroup 2 (↥c.NH ⧸ c.PG.subgroupOf c.NH) := by
    refine IsPGroup.of_card (n := 4) ?_
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (c.PG.subgroupOf c.NH)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, c.card_PG, c.card_NH] at h1
    omega
  have hodd' : Odd (Nat.card (Subgroup.zpowers (⟨g, hg⟩ : c.NH))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]; exact hodd
  have hsub := CFSG.QuasiDihedralFusion.le_of_odd_of_isPGroup_quotient
    (c.PG.subgroupOf c.NH) hquot _ hodd'
  exact Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_zpowers _))

@[expose] def NG : Subgroup G := normalizer (c.OG : Set G)

theorem mem_NG_of_conj {g : G} (h1 : ∀ y ∈ c.OG, g * y * g⁻¹ ∈ c.OG)
    (h2 : ∀ y ∈ c.OG, g⁻¹ * y * g ∈ c.OG) : g ∈ c.NG := by
  rw [NG, Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  simpa [mul_assoc] using this

theorem Ng_le_NG : c.Ng ≤ c.NG := fun g hg =>
  c.mem_NG_of_conj (c.OG_normalized g hg) (fun y hy => by
    simpa using c.OG_normalized g⁻¹ (c.Ng.inv_mem hg) y hy)

theorem conj_mem_OG_of_mem_NG {g : G} (hg : g ∈ c.NG) {y : G} (hy : y ∈ c.OG) :
    g * y * g⁻¹ ∈ c.OG :=
  (Subgroup.mem_normalizer_iff.mp hg y).mp hy

theorem z_mem_NG : S.z ∈ c.NG := c.Ng_le_NG (c.cg_le_ng c.z_mem_cg)

theorem t_mem_NG : (c.t : G) ∈ c.NG := c.Ng_le_NG (c.cg_le_ng c.tC_mem)

theorem OG_le_NG : c.OG ≤ c.NG := Subgroup.le_normalizer

theorem NH_le_NG :
    c.NH ≤ c.NG := fun g hg =>
  c.mem_NG_of_conj (c.OG_normalized_of_normalizes_PG hg.1)
    (fun y hy => by
      simpa using c.OG_normalized_of_normalizes_PG (g := g⁻¹) (c.NH.inv_mem hg).1 y hy)

theorem NG_inf_H_le_NH :
    c.NG ⊓ S.H ≤ c.NH := by
  have h81 := c.card_OG_eq_81
  have key : ∀ g ∈ c.NG ⊓ S.H, ∀ y ∈ c.PG, g * y * g⁻¹ ∈ c.PG := by
    intro g hg y hy
    rw [← c.CO_z_eq_PG h81] at hy ⊢
    refine ⟨c.conj_mem_OG_of_mem_NG hg.1 hy.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hgz := Subgroup.mem_centralizer_singleton_iff.mp hg.2
    have hyz := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hgz' : g⁻¹ * S.z = S.z * g⁻¹ := by
      calc g⁻¹ * S.z = g⁻¹ * (S.z * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * S.z) * g⁻¹ := by rw [hgz]
        _ = S.z * g⁻¹ := by group
    calc g * y * g⁻¹ * S.z = g * y * (g⁻¹ * S.z) := by group
      _ = g * y * (S.z * g⁻¹) := by rw [hgz']
      _ = g * (y * S.z) * g⁻¹ := by group
      _ = g * (S.z * y) * g⁻¹ := by rw [hyz]
      _ = (g * S.z) * y * g⁻¹ := by group
      _ = (S.z * g) * y * g⁻¹ := by rw [hgz]
      _ = S.z * (g * y * g⁻¹) := by group
  intro g hg
  refine ⟨?_, hg.2⟩
  refine c.mem_normalizer_PG_of (key g hg) (fun y hy => ?_)
  simpa using key g⁻¹ ((c.NG ⊓ S.H).inv_mem hg) y hy

theorem exists_conj_PG_CO {v : G} (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hCO : Nat.card (c.CO v) = 9) :
    ∃ g₀ : G, g₀ * S.z * g₀⁻¹ = v ∧ ∀ x : G, x ∈ c.PG ↔ g₀ * x * g₀⁻¹ ∈ c.CO v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := isConj_iff.mp (S.oneClass S.z v S.order_z (orderOf_eq_prime hv2 hv1))
  have hYv : ∀ y ∈ c.CO v, y * v = v * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp hy.2
  set Y := c.CO v with hY
  have hmemH : ∀ y ∈ Y, k⁻¹ * y * k ∈ S.H := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k⁻¹ * y * k * S.z = k⁻¹ * y * (k * S.z * k⁻¹) * k := by group
      _ = k⁻¹ * (y * v) * k := by rw [hk]; group
      _ = k⁻¹ * (v * y) * k := by rw [hYv y hy]
      _ = S.z * (k⁻¹ * y * k) := by rw [← hk]; group
  have hconj : ∀ y : G, (MulAut.conj k⁻¹).toMonoidHom y = k⁻¹ * y * k := by
    intro y; simp
  let Y' : Subgroup G := Y.map (MulAut.conj k⁻¹).toMonoidHom
  have hY'H : Y' ≤ S.H := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hconj]; exact hmemH y hy
  have hY'mem : ∀ x : G, x ∈ Y' ↔ ∃ y ∈ Y, k⁻¹ * y * k = x := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (hconj y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, hconj y⟩
  have hY'card : Nat.card Y' = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hCO]
  let YH : Subgroup S.H := Y'.subgroupOf S.H
  have hYHcard : Nat.card YH = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY'H).toEquiv, hY'card]
  have hH3 : 3 ^ (Nat.card S.H).factorization 3 = 9 := by
    rw [S.card_H, factorization_three_40320]; norm_num
  let YS : Sylow 3 S.H := Sylow.ofCard YH (by rw [hYHcard, hH3])
  let PS : Sylow 3 S.H := Sylow.ofCard c.P (by rw [c.hP9, hH3])
  obtain ⟨h, hh⟩ := sylow_conj_mem PS YS
  simp only [YS, PS, Sylow.coe_ofCard] at hh
  have hz : (h : G) * S.z = S.z * (h : G) := Subgroup.mem_centralizer_singleton_iff.mp h.2
  have he : k * (h : G) * S.z * (k * (h : G))⁻¹ = v := by
    calc k * (h : G) * S.z * (k * (h : G))⁻¹ = k * ((h : G) * S.z * (h : G)⁻¹) * k⁻¹ := by group
      _ = k * S.z * k⁻¹ := by rw [hz]; group
      _ = v := hk
  refine ⟨k * (h : G), he, fun x => ?_⟩
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h1 : h * p * h⁻¹ ∈ YH := (hh (h * p * h⁻¹)).mpr (by
      have : h⁻¹ * (h * p * h⁻¹) * h = p := by group
      rw [this]; exact hp)
    have h2 : ((h * p * h⁻¹ : S.H) : G) ∈ Y' := Subgroup.mem_subgroupOf.mp h1
    obtain ⟨y, hy, hye⟩ := (hY'mem _).mp h2
    have : k * (h : G) * (p : G) * (k * (h : G))⁻¹ = y := by
      have e : ((h * p * h⁻¹ : S.H) : G) = (h : G) * (p : G) * (h : G)⁻¹ := by simp
      rw [e] at hye
      calc k * (h : G) * (p : G) * (k * (h : G))⁻¹
          = k * ((h : G) * (p : G) * (h : G)⁻¹) * k⁻¹ := by group
        _ = k * (k⁻¹ * y * k) * k⁻¹ := by rw [hye]
        _ = y := by group
    show k * (h : G) * (S.H.subtype p) * (k * (h : G))⁻¹ ∈ Y
    rw [show S.H.subtype p = (p : G) from rfl, this]
    exact hy
  · intro hx
    have hxv : x ∈ S.H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hYv _ hx
      calc x * S.z = (k * (h : G))⁻¹ * (k * (h : G) * x * (k * (h : G))⁻¹ * v) * (k * (h : G)) := by
            rw [← he]; group
        _ = (k * (h : G))⁻¹ * (v * (k * (h : G) * x * (k * (h : G))⁻¹)) * (k * (h : G)) := by
            rw [h1]
        _ = S.z * x := by rw [← he]; group
    have h3 : (h * (⟨x, hxv⟩ : S.H) * h⁻¹ : S.H) ∈ YH := by
      rw [Subgroup.mem_subgroupOf, hY'mem]
      refine ⟨k * (h : G) * x * (k * (h : G))⁻¹, hx, ?_⟩
      show k⁻¹ * (k * (h : G) * x * (k * (h : G))⁻¹) * k = (h : G) * x * (h : G)⁻¹
      group
    have h4 := (hh _).mp h3
    have h5 : (⟨x, hxv⟩ : S.H) ∈ c.P := by
      have : h⁻¹ * (h * (⟨x, hxv⟩ : S.H) * h⁻¹) * h = ⟨x, hxv⟩ := by group
      rwa [this] at h4
    exact ⟨⟨x, hxv⟩, h5, rfl⟩

theorem mem_CO_of_odd
    {v : G} (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hCO : Nat.card (c.CO v) = 9) {r : G} (hrNG : r ∈ c.NG) (hrv : r * v = v * r)
    (hodd : Odd (orderOf r)) : r ∈ c.CO v := by
  obtain ⟨g₀, hg₀z, hg₀⟩ := c.exists_conj_PG_CO hv2 hv1 hCO
  have key : ∀ r₁ ∈ c.NG, r₁ * v = v * r₁ →
      ∀ y ∈ c.PG, g₀⁻¹ * r₁ * g₀ * y * (g₀⁻¹ * r₁ * g₀)⁻¹ ∈ c.PG := by
    intro r₁ h1 h2 y hy
    have hy' := (hg₀ y).mp hy
    have hmem : r₁ * (g₀ * y * g₀⁻¹) * r₁⁻¹ ∈ c.CO v := by
      refine ⟨c.conj_mem_OG_of_mem_NG h1 hy'.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h3 := Subgroup.mem_centralizer_singleton_iff.mp hy'.2
      have h2' : r₁⁻¹ * v = v * r₁⁻¹ := by
        calc r₁⁻¹ * v = r₁⁻¹ * (v * r₁) * r₁⁻¹ := by group
          _ = r₁⁻¹ * (r₁ * v) * r₁⁻¹ := by rw [h2]
          _ = v * r₁⁻¹ := by group
      calc r₁ * (g₀ * y * g₀⁻¹) * r₁⁻¹ * v = r₁ * (g₀ * y * g₀⁻¹) * (r₁⁻¹ * v) := by group
        _ = r₁ * (g₀ * y * g₀⁻¹) * (v * r₁⁻¹) := by rw [h2']
        _ = r₁ * ((g₀ * y * g₀⁻¹) * v) * r₁⁻¹ := by group
        _ = r₁ * (v * (g₀ * y * g₀⁻¹)) * r₁⁻¹ := by rw [h3]
        _ = (r₁ * v) * (g₀ * y * g₀⁻¹) * r₁⁻¹ := by group
        _ = (v * r₁) * (g₀ * y * g₀⁻¹) * r₁⁻¹ := by rw [h2]
        _ = v * (r₁ * (g₀ * y * g₀⁻¹) * r₁⁻¹) := by group
    have := (hg₀ (g₀⁻¹ * (r₁ * (g₀ * y * g₀⁻¹) * r₁⁻¹) * g₀)).mpr (by
      have e : g₀ * (g₀⁻¹ * (r₁ * (g₀ * y * g₀⁻¹) * r₁⁻¹) * g₀) * g₀⁻¹ =
          r₁ * (g₀ * y * g₀⁻¹) * r₁⁻¹ := by group
      rw [e]; exact hmem)
    have e2 : g₀⁻¹ * r₁ * g₀ * y * (g₀⁻¹ * r₁ * g₀)⁻¹ =
        g₀⁻¹ * (r₁ * (g₀ * y * g₀⁻¹) * r₁⁻¹) * g₀ := by group
    rw [e2]; exact this
  have hrinv : r⁻¹ ∈ c.NG := c.NG.inv_mem hrNG
  have hrv' : r⁻¹ * v = v * r⁻¹ := by
    calc r⁻¹ * v = r⁻¹ * (v * r) * r⁻¹ := by group
      _ = r⁻¹ * (r * v) * r⁻¹ := by rw [hrv]
      _ = v * r⁻¹ := by group
  have hnorm : g₀⁻¹ * r * g₀ ∈ normalizer (c.PG : Set G) := by
    refine c.mem_normalizer_PG_of (key r hrNG hrv) (fun y hy => ?_)
    have := key r⁻¹ hrinv hrv' y hy
    have e : g₀⁻¹ * r⁻¹ * g₀ * y * (g₀⁻¹ * r⁻¹ * g₀)⁻¹ =
        (g₀⁻¹ * r * g₀)⁻¹ * y * (g₀⁻¹ * r * g₀) := by
      group
    rwa [e] at this
  have hH : g₀⁻¹ * r * g₀ ∈ S.H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : S.z = g₀⁻¹ * v * g₀ := by rw [← hg₀z]; group
    calc g₀⁻¹ * r * g₀ * S.z = g₀⁻¹ * (r * v) * g₀ := by rw [hz]; group
      _ = g₀⁻¹ * (v * r) * g₀ := by rw [hrv]
      _ = S.z * (g₀⁻¹ * r * g₀) := by rw [hz]; group
  have hord : orderOf (g₀⁻¹ * r * g₀) = orderOf r := by
    have h := orderOf_injective (MulAut.conj g₀⁻¹).toMonoidHom (MulAut.conj g₀⁻¹).injective r
    have e : (MulAut.conj g₀⁻¹).toMonoidHom r = g₀⁻¹ * r * g₀ := by simp
    rw [e] at h; exact h
  have hPG := c.mem_PG_of_odd_NH ⟨hnorm, hH⟩ (by rw [hord]; exact hodd)
  have := (hg₀ _).mp hPG
  have e : g₀ * (g₀⁻¹ * r * g₀) * g₀⁻¹ = r := by group
  rwa [e] at this

@[expose] def VG : Subgroup G :=
  kleinFourSubgroup (z_sq (S := S)) c.tG_sq' c.t_comm_z.symm

theorem card_VG : Nat.card c.VG = 4 := by
  have hz1 : S.z ≠ 1 := z_ne_one' (S := S)
  have ht1 : (c.t : G) ≠ 1 := c.tG_ne_one
  have hne : S.z ≠ (c.t : G) := fun e => c.t_ne_z (Subtype.ext e.symm)
  have hzz : S.z * S.z = 1 := by rw [← pow_two]; exact z_sq (S := S)
  have hztne1 : S.z * (c.t : G) ≠ 1 := fun h => hne (by
    have : (c.t : G) = S.z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right hzz).symm)
  have hzne : S.z ≠ S.z * (c.t : G) := fun h => ht1 (by
    have := congrArg (fun w => S.z⁻¹ * w) h
    simpa using this.symm)
  have htne : (c.t : G) ≠ S.z * (c.t : G) := fun h => hz1 (by
    have := congrArg (fun w => w * (c.t : G)⁻¹) h
    simpa using this.symm)
  have h1 : Nat.card c.VG = ({1, S.z, (c.t : G), S.z * (c.t : G)} : Set G).ncard :=
    Nat.card_coe_set_eq ({1, S.z, (c.t : G), S.z * (c.t : G)} : Set G)
  rw [h1, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair htne]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hzne⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz1.symm, ht1.symm, fun h => hztne1 h.symm⟩

theorem mem_VG {x : G} : x ∈ c.VG ↔ x = 1 ∨ x = S.z ∨ x = (c.t : G) ∨ x = S.z * (c.t : G) :=
  mem_kleinFourSubgroup _ _ _

theorem odd_card_oddCore_NG_map : Odd (Nat.card ((CFSG.oddCore ↥c.NG).map c.NG.subtype)) := by
  rw [Subgroup.card_map_of_injective c.NG.subtype_injective]
  exact CFSG.ABGDGroups.odd_card_oddCore _

theorem oddCore_NG_conj {g : G} (hg : g ∈ c.NG) {y : G}
    (hy : y ∈ (CFSG.oddCore ↥c.NG).map c.NG.subtype) :
    g * y * g⁻¹ ∈ (CFSG.oddCore ↥c.NG).map c.NG.subtype := by
  obtain ⟨o, ho, rfl⟩ := hy
  exact ⟨⟨g, hg⟩ * o * ⟨g, hg⟩⁻¹, (CFSG.oddCore_normal ↥c.NG).conj_mem o ho ⟨g, hg⟩, rfl⟩

theorem oddCore_NG_map :
    (CFSG.oddCore ↥c.NG).map c.NG.subtype = c.OG := by
  have h81 := c.card_OG_eq_81
  apply le_antisymm
  · set O : Subgroup G := (CFSG.oddCore ↥c.NG).map c.NG.subtype with hO
    have hOodd : Odd (Nat.card O) := c.odd_card_oddCore_NG_map
    have hOle : O ≤ c.NG := Subgroup.map_subtype_le _
    have hz2 := z_sq (S := S)
    have ht2 := c.tG_sq'
    have hzt2 : (S.z * (c.t : G)) ^ 2 = 1 := by
      rw [(show Commute S.z (c.t : G) from c.t_comm_z.symm).mul_pow, hz2, ht2, one_mul]
    have hpower : ∀ m : c.VG, (m : G) ^ 2 = 1 := by
      rintro ⟨m, hm⟩
      rcases c.mem_VG.mp hm with rfl | rfl | rfl | rfl
      · simp
      · exact hz2
      · exact ht2
      · exact hzt2
    have hnorm : c.VG ≤ normalizer (O : Set G) := by
      intro m hm
      have hmNG : m ∈ c.NG := by
        rcases c.mem_VG.mp hm with rfl | rfl | rfl | rfl
        · exact c.NG.one_mem
        · exact c.z_mem_NG
        · exact c.t_mem_NG
        · exact c.NG.mul_mem c.z_mem_NG c.t_mem_NG
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => c.oddCore_NG_conj hmNG hy, fun hy => ?_⟩
      have h := c.oddCore_NG_conj (c.NG.inv_mem hmNG) hy
      rwa [show m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y by group] at h
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      2 Nat.prime_two c.VG O (fun m => Subtype.ext (hpower m)) (by rw [c.card_VG]; norm_num)
      (by rcases hOodd with ⟨k, hk⟩; omega) hnorm
    refine hgen.le.trans (iSup_le fun m => iSup_le fun hm1 => ?_)
    have hmV := m.2
    have hkey : ∀ {v : G}, v ^ 2 = 1 → v ≠ 1 → Nat.card (c.CO v) = 9 → v = (m : G) →
        O ⊓ centralizer ({(m : G)} : Set G) ≤ c.OG := by
      intro v hv2 hv1 hCO hvm y hy
      have hyNG : y ∈ c.NG := hOle hy.1
      have hyv : y * v = v * y := by
        rw [hvm]; exact Subgroup.mem_centralizer_singleton_iff.mp hy.2
      have hyodd : Odd (orderOf y) := by
        have h1 : orderOf (⟨y, hy.1⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hOodd h1
      exact (c.mem_CO_of_odd hv2 hv1 hCO hyNG hyv hyodd).1
    have hz1 : S.z ≠ 1 := z_ne_one' (S := S)
    have ht1 : (c.t : G) ≠ 1 := c.tG_ne_one
    have hzinv : S.z⁻¹ = S.z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
    have hzt1 : S.z * (c.t : G) ≠ 1 := fun h => c.t_ne_z (Subtype.ext (by
      rw [eq_inv_of_mul_eq_one_right h, hzinv]; rfl))
    rcases c.mem_VG.mp hmV with h | h | h | h
    · exact absurd (Subtype.ext h) hm1
    · exact hkey hz2 hz1 (c.card_CO_z_t h81).1 h.symm
    · exact hkey ht2 ht1 (c.card_CO_z_t h81).2 h.symm
    · exact hkey hzt2 hzt1 (by rw [c.card_CO_zt]; exact (c.card_CO_z_t h81).2) h.symm
  · have hnormal : (c.OG.subgroupOf c.NG).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer c.OG_le_NG).mpr (le_refl _)
    have hodd : Odd (Nat.card (c.OG.subgroupOf c.NG)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.OG_le_NG).toEquiv]
      exact c.odd_card_OG
    have hle := le_oddCore_of_normal_odd _ hnormal hodd
    intro y hy
    exact ⟨⟨y, c.OG_le_NG hy⟩, hle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
