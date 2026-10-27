module

public import CFSG.RankThree.GF2n.Tim78S412Partner
public import CFSG.RankThree.GF2n.Tim78S412RankOne

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_classIn_conj_iff {V W U : Subgroup G} (g : G) :
    U ∈ classIn (conjSubgroup g V) W ↔ U ∈ classIn V W := by
  constructor
  · rintro ⟨⟨x, rfl⟩, hW⟩
    exact ⟨⟨x * g, (conjSubgroup_mul x g V).symm⟩, hW⟩
  · rintro ⟨⟨x, rfl⟩, hW⟩
    exact ⟨⟨x * g⁻¹, by rw [← conjSubgroup_mul, inv_mul_cancel_right]⟩, hW⟩

theorem mem_normalizer_of_mem_centralizer {L X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.centralizer (L : Set G)) (hX : X ≤ L) :
    u ∈ Subgroup.normalizer (X : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← Subgroup.mem_centralizer_iff.mp hu x (hX hx), mul_inv_cancel_right]
    exact hx
  · have hy := Subgroup.mem_centralizer_iff.mp hu _ (hX hx)
    have h2 : u * x = u * (u * x * u⁻¹) := by
      calc u * x = (u * x * u⁻¹) * u := by group
        _ = u * (u * x * u⁻¹) := hy
    have h3 : x = u * x * u⁻¹ := mul_left_cancel h2
    rw [h3]
    exact hx

theorem conj_comm_of_factor {L P' P'' : Subgroup G} {z : G}
    (hzN : z ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ x ∈ P'', ∃ y ∈ P', ∃ k ∈ Subgroup.centralizer (L : Set G), z⁻¹ * x * z = y * k)
    {l : G} (hl : l ∈ L) (hc : ∀ y ∈ P', y * l = l * y) :
    z * l * z⁻¹ ∈ L ∧ ∀ x ∈ P'', x * (z * l * z⁻¹) = (z * l * z⁻¹) * x := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hzN l).mp hl, fun x hx => ?_⟩
  obtain ⟨y, hy, k, hk, hxk⟩ := h x hx
  have hx' : x = z * (y * k) * z⁻¹ := by rw [← hxk]; group
  have hkl : k * l = l * k := (Subgroup.mem_centralizer_iff.mp hk l hl).symm
  have hyl := hc y hy
  rw [hx']
  calc z * (y * k) * z⁻¹ * (z * l * z⁻¹) = z * (y * (k * l)) * z⁻¹ := by group
    _ = z * (l * (y * k)) * z⁻¹ := by
      have : y * (l * k) = l * (y * k) := by rw [← mul_assoc, hyl, mul_assoc]
      rw [hkl, this]
    _ = (z * l * z⁻¹) * (z * (y * k) * z⁻¹) := by group

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
  (hmut : MutualPFull M B P g)
include H hmut

section Root


theorem pair_L_conj_eq :
    conjSubgroup g B ⊔ conjSubgroup g⁻¹ (conjSubgroup g B) = B ⊔ conjSubgroup g B := by
  rw [conjSubgroup_inv_conjSubgroup, sup_comm]

theorem pair_B_cen {b : G} (hb : b ∈ B) :
    b ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun l hl =>
    comm_of_isElemAbelian (H.outer_L_elemAb hmut.outer) hl (Subgroup.mem_sup_left hb)

theorem pair_A_cen {a : G} (ha : a ∈ conjSubgroup g B) :
    a ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun l hl =>
    comm_of_isElemAbelian (H.outer_L_elemAb hmut.outer) hl (Subgroup.mem_sup_right ha)

theorem pair_centP_cen {c : G} (hc : c ∈ centP B P g) :
    c ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  obtain ⟨hcP, hca⟩ := mem_centP.mp hc
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hmut.outer b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
  calc b * a * c = b * (a * c) := by group
    _ = b * (c * a) := by rw [(hca a ha).symm]
    _ = (b * c) * a := by group
    _ = (c * b) * a := by rw [H.center_Q hb (H.P_le_Q hcP)]
    _ = c * (b * a) := by group

theorem pair_Pg_comm_A {u a : G} (hu : u ∈ conjSubgroup g P) (ha : a ∈ conjSubgroup g B) :
    a * u = u * a :=
  (H.conj g).center_Q ha (Subgroup.map_mono H.P_le_Q hu)

theorem pair_Pg_le_normalizer_L :
    conjSubgroup g P ≤ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  have h := (H.conj g).outer_P_le_normalizer_L (H.outer_conj_of_mutual hmut)
  rwa [H.pair_L_conj_eq hmut] at h

theorem pair_classIn_cases_Pg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {U : Subgroup G} (hUc : U ∈ classIn B (B ⊔ conjSubgroup g B)) :
    U = conjSubgroup g B ∨ ∃ u ∈ conjSubgroup g P, U = conjSubgroup u B := by
  have h1 : U ∈ classIn (conjSubgroup g B)
      (conjSubgroup g B ⊔ conjSubgroup g⁻¹ (conjSubgroup g B)) := by
    rw [H.pair_L_conj_eq hmut]
    exact (mem_classIn_conj_iff g).mpr hUc
  have h2 := (H.conj g).outer_classIn_cases (H.outer_conj_of_mutual hmut) hCen hU h1
  rwa [conjSubgroup_inv_conjSubgroup] at h2

theorem pair_conj_mem_classIn_Pg {u : G} (hu : u ∈ conjSubgroup g P) :
    conjSubgroup u B ∈ classIn B (B ⊔ conjSubgroup g B) := by
  have h := (H.conj g).outer_conj_mem_classIn (H.outer_conj_of_mutual hmut) hu
  rw [conjSubgroup_inv_conjSubgroup, sup_comm] at h
  exact (mem_classIn_conj_iff g).mp h

theorem pair_cen_of_normalizes_B {u : G} (hu : u ∈ conjSubgroup g P)
    (hN : u ∈ Subgroup.normalizer (B : Set G)) :
    u ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hmut.outer b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
  have hbu : b * u = u * b := by
    have h1 : ⁅b, u⁆ ∈ conjSubgroup g B := hmut.partner b hb u hu
    have h2 : ⁅b, u⁆ ∈ B := by
      have e : ⁅b, u⁆ = b * (u * b⁻¹ * u⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.mp hN b⁻¹).mp (B.inv_mem hb))
    have h3 : ⁅b, u⁆ ∈ B ⊓ conjSubgroup g B := ⟨h2, h1⟩
    rw [H.outer_inf_B hmut.outer, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have hau : a * u = u * a := H.pair_Pg_comm_A hmut hu ha
  calc b * a * u = b * (a * u) := by group
    _ = b * (u * a) := by rw [hau]
    _ = (b * u) * a := by group
    _ = (u * b) * a := by rw [hbu]
    _ = u * (b * a) := by group

theorem pair_Pg_normalizes_A {u : G} (hu : u ∈ conjSubgroup g P) :
    u ∈ Subgroup.normalizer (conjSubgroup g B : Set G) :=
  mem_normalizer_of_mem_centralizer (L := conjSubgroup g B)
    (Subgroup.mem_centralizer_iff.mpr fun a ha => H.pair_Pg_comm_A hmut hu ha) le_rfl

theorem pair_rankOne (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card B = 2 ^ n ∧
      ∃ φ : ↥(P ⊔ conjSubgroup g P) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        Function.Surjective φ ∧
        (∀ z : ↥(P ⊔ conjSubgroup g P), φ z = 1 ↔
          (z : G) ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)) ∧
        (P.subgroupOf (P ⊔ conjSubgroup g P)).map φ = upperUnipotent (GaloisField 2 n) ∧
        ((conjSubgroup g P).subgroupOf (P ⊔ conjSubgroup g P)).map φ =
          lowerUnipotent (GaloisField 2 n) := by
  classical
  have hg := hmut.outer
  obtain ⟨y, hy, hy1⟩ := H.exists_ne_one_mem_conj g
  obtain ⟨h, hhP, e₀, he₀, hne⟩ := H.outer_exists_member hg hCen hU hy hy1
  obtain ⟨-, hfac⟩ := H.outer_exists_mul_cent hg hhP hy hy1 hCen hU he₀ hne
  have hP₁L := H.outer_P_le_normalizer_L hg
  have hP₂L := H.pair_Pg_le_normalizer_L hmut
  have hMouf : ∀ p ∈ P, p ∉ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) →
      ∃ u ∈ conjSubgroup g P,
        u ∉ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) ∧
        conjSubgroup u P = conjSubgroup p (conjSubgroup g P) := by
    intro p hp hpC
    have hpc : p ∉ centP B P g := fun hc => hpC (H.pair_centP_cen hmut hc)
    have hUc := H.outer_conj_mem_classIn hg hp
    have hUA := H.outer_conj_ne_of_not_cent hg hp hCen hU hpc
    obtain ⟨u, hu, hUu⟩ := (H.pair_classIn_cases_Pg hmut hCen hU hUc).resolve_left hUA
    refine ⟨u, hu, fun huC => ?_, ?_⟩
    · apply H.outer_conj_ne_B hg hp
      rw [hUu]
      exact conjSubgroup_eq_self_iff.mpr (mem_normalizer_of_mem_centralizer huC le_sup_left)
    · have := H.conj_P_eq_of_conj_B_eq (x := u) (y := p * g)
        (by rw [← hUu, conjSubgroup_mul])
      rw [this, conjSubgroup_mul]
  have hMouf' : ∀ u ∈ conjSubgroup g P,
      u ∉ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) →
      ∃ p ∈ P, p ∉ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) ∧
        conjSubgroup p (conjSubgroup g P) = conjSubgroup u P := by
    intro u hu huC
    have hUc := H.pair_conj_mem_classIn_Pg hmut hu
    have hUB : conjSubgroup u B ≠ B := fun h' =>
      huC (H.pair_cen_of_normalizes_B hmut hu (conjSubgroup_eq_self_iff.mp h'))
    obtain ⟨p, hp, hUp⟩ := (H.outer_classIn_cases hg hCen hU hUc).resolve_left hUB
    refine ⟨p, hp, fun hpC => ?_, ?_⟩
    · have h1 : conjSubgroup p (conjSubgroup g B) = conjSubgroup g B :=
        conjSubgroup_eq_self_iff.mpr (mem_normalizer_of_mem_centralizer hpC le_sup_right)
      have hunA := H.pair_Pg_normalizes_A hmut hu
      apply H.outer_ne_B hg
      calc conjSubgroup g B = conjSubgroup u⁻¹ (conjSubgroup g B) :=
            (conjSubgroup_eq_self_iff.mpr (Subgroup.inv_mem _ hunA)).symm
        _ = conjSubgroup u⁻¹ (conjSubgroup u B) := by rw [hUp, h1]
        _ = B := conjSubgroup_inv_conjSubgroup u B
    · have := H.conj_P_eq_of_conj_B_eq (x := p * g) (y := u)
        (by rw [conjSubgroup_mul, hUp])
      rw [← conjSubgroup_mul]
      exact this
  have hne' : ∀ p ∈ P, ∀ u ∈ conjSubgroup g P,
      p ∉ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) →
      p⁻¹ * u ∉ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
    intro p hp u hu hpC hk
    have hkA : conjSubgroup (p⁻¹ * u) (conjSubgroup g B) = conjSubgroup g B :=
      conjSubgroup_eq_self_iff.mpr (mem_normalizer_of_mem_centralizer hk le_sup_right)
    have huA : conjSubgroup u (conjSubgroup g B) = conjSubgroup g B :=
      conjSubgroup_eq_self_iff.mpr (H.pair_Pg_normalizes_A hmut hu)
    have hpA : conjSubgroup p (conjSubgroup g B) = conjSubgroup g B := by
      calc conjSubgroup p (conjSubgroup g B)
          = conjSubgroup p (conjSubgroup (p⁻¹ * u) (conjSubgroup g B)) := by rw [hkA]
        _ = conjSubgroup (p * (p⁻¹ * u)) (conjSubgroup g B) := (conjSubgroup_mul _ _ _).symm
        _ = conjSubgroup u (conjSubgroup g B) := by rw [mul_inv_cancel_left]
        _ = conjSubgroup g B := huA
    exact hpC (H.pair_centP_cen hmut (mem_centP.mpr ⟨hp,
      H.outer_comm_of_mem_normalizer hg hCen hU hp (conjSubgroup_eq_self_iff.mp hpA)⟩))
  obtain ⟨n, hn2, hn, φ, hs, hker, hPφ, hPgφ⟩ := exists_rankOne_pair
    (P₁ := P) (P₂ := conjSubgroup g P) (L := B ⊔ conjSubgroup g B)
    (H := P ⊔ conjSubgroup g P) (E := conjSubgroup h B) rfl hP₁L hP₂L
    (fun p hp p' hp' => H.pair_B_cen hmut (H.commutator_mem (H.P_le_Q hp) (H.P_le_Q hp')))
    (fun u hu u' hu' => H.pair_A_cen hmut ((H.conj g).commutator_mem
      (Subgroup.map_mono H.P_le_Q hu) (Subgroup.map_mono H.P_le_Q hu')))
    (fun p hp => H.pair_B_cen hmut (by
      have := H.sq_mem (H.P_le_Q hp)
      rwa [sq] at this))
    (fun u hu => H.pair_A_cen hmut (by
      have := (H.conj g).sq_mem (Subgroup.map_mono H.P_le_Q hu)
      rwa [sq] at this))
    hMouf hMouf' hne' hhP
    (fun e he hec => H.outer_ker_trivial hg hhP hy he₀ hne e he
      (Subgroup.mem_centralizer_iff.mp hec y (Subgroup.mem_sup_right hy)))
    (fun p hp => by
      obtain ⟨e, he, c, hc, hpec⟩ := hfac p hp
      exact ⟨e, he, c, H.pair_centP_cen hmut hc, (mem_centP.mp hc).1, hpec⟩)
    (by rw [card_conjSubgroup]; exact H.q4)
  exact ⟨n, hn2, by rwa [card_conjSubgroup] at hn, φ, hs, hker, hPφ, hPgφ⟩

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
