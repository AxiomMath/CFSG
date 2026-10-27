module

public import CFSG.Quasithin.Vol2.Ch10SecKL7p

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Helpers

variable {G : Type*} [Group G]

theorem conj_mem_sup_of {s : G} {X Y : Subgroup G} (hX : ∀ x ∈ X, s * x * s⁻¹ ∈ X ⊔ Y)
    (hY : ∀ y ∈ Y, s * y * s⁻¹ ∈ X ⊔ Y) {z : G} (hz : z ∈ X ⊔ Y) : s * z * s⁻¹ ∈ X ⊔ Y := by
  have hle : (X ⊔ Y).map (MulAut.conj s).toMonoidHom ≤ X ⊔ Y := by
    rw [Subgroup.map_sup]
    exact sup_le (Subgroup.map_le_iff_le_comap.2 fun x hx => hX x hx)
      (Subgroup.map_le_iff_le_comap.2 fun y hy => hY y hy)
  exact hle ⟨z, hz, rfl⟩

theorem conj_mem_zpowers_of {s q : G} {X : Subgroup G} (hq : s * q * s⁻¹ ∈ X) {z : G}
    (hz : z ∈ Subgroup.zpowers q) : s * z * s⁻¹ ∈ X := by
  have hle : Subgroup.zpowers q ≤ X.comap (MulAut.conj s).toMonoidHom :=
    Subgroup.zpowers_le.2 hq
  exact hle hz

theorem comm_sup {X Y : Subgroup G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hY : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) :
    ∀ a ∈ X ⊔ Y, ∀ b ∈ X ⊔ Y, a * b = b * a := by
  have key : X ⊔ Y ≤ Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · have hle : X ⊔ Y ≤ Subgroup.centralizer {a} := sup_le
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hX b hb a ha))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hXY a ha b hb).symm)
      exact Subgroup.mem_centralizer_iff.2 fun b hb =>
        Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
    · have hle : X ⊔ Y ≤ Subgroup.centralizer {a} := sup_le
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hXY b hb a ha))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hY b hb a ha))
      exact Subgroup.mem_centralizer_iff.2 fun b hb =>
        Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1 (key hb) a ha)

theorem mem_normalizer_of_conj_mem [Finite G] {g : G} {X : Subgroup G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := Subgroup.map_le_iff_le_comap.2 h
  have heq : X.map (MulAut.conj g).toMonoidHom = X := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hxy' : x = y := (MulAut.conj g).injective hxy
  rw [← hxy']
  exact hx

end Helpers

variable {W : Type} [CommGroup W]

namespace Coord

variable {L : Subgroup (MulAut W)} {U : Subgroup W} (c : Coord L U)

theorem P_le : U3.map c.phi ≤ L := (Subgroup.map_le_range _ _).trans c.range_phi.le

theorem isPGroup_P : IsPGroup 2 ↥(U3.map c.phi) := isPGroup_U3.map c.phi

theorem E_le_P : EE.map c.phi ≤ U3.map c.phi := Subgroup.map_mono EE_le_U3

theorem orderOf_q : orderOf (c.phi gq) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_injective c.phi c.phi_injective, orderOf_eq_prime gq_pow_three gq_ne_one]

theorem P_conj_E {p e : MulAut W} (hp : p ∈ U3.map c.phi) (he : e ∈ EE.map c.phi) :
    p * e * p⁻¹ ∈ EE.map c.phi := by
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨e', he', rfl⟩ := he
  exact ⟨u * e' * u⁻¹, U3_conj_EE hu he', by simp only [map_mul, map_inv]⟩

theorem q_conj_E {e : MulAut W} (he : e ∈ EE.map c.phi) :
    c.phi gq * e * (c.phi gq)⁻¹ ∈ EE.map c.phi := by
  obtain ⟨e', he', rfl⟩ := he
  exact ⟨gq * e' * gq⁻¹, gq_conj_EE he', by simp only [map_mul, map_inv]⟩

theorem P_conj_q {p : MulAut W} (hp : p ∈ U3.map c.phi) :
    p * c.phi gq * p⁻¹ ∈ EE.map c.phi ⊔ Subgroup.zpowers (c.phi gq) := by
  obtain ⟨u, hu, rfl⟩ := hp
  have h1 : c.phi (u * gq * u⁻¹) ∈ (EE ⊔ Subgroup.zpowers gq).map c.phi := ⟨_, U3_conj_gq hu, rfl⟩
  rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
  simpa only [map_mul, map_inv] using h1

theorem P_conj_A {p : MulAut W} (hp : p ∈ U3.map c.phi) {x : MulAut W}
    (hx : x ∈ EE.map c.phi ⊔ Subgroup.zpowers (c.phi gq)) :
    p * x * p⁻¹ ∈ EE.map c.phi ⊔ Subgroup.zpowers (c.phi gq) :=
  conj_mem_sup_of (fun _ he => Subgroup.mem_sup_left (c.P_conj_E hp he))
    (fun _ hz => conj_mem_zpowers_of (c.P_conj_q hp) hz) hx

end Coord

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
