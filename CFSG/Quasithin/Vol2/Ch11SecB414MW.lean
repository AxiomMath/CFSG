module

public import CFSG.Quasithin.Vol2.Ch11SecB414MV
public import CFSG.Quasithin.Vol2.Ch11SecB414PC
public import CFSG.Quasithin.Vol2.Ch11SecB414PD
public import CFSG.Quasithin.Vol2.Ch11SecB414MP
public import CFSG.Quasithin.Vol2.Ch11SecB414Defs
public import CFSG.Quasithin.Vol2.Ch11SecB414PA

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix

variable {G : Type} [Group G] {Γ V Z L X : Subgroup G} {F : Type} [Field F]

structure NHyp (Γ L X : Subgroup G) (F : Type) [Field F] (α : ↥Γ →* PGL3 F)
    (K : Subgroup (PGL3 F)) : Prop where
  map_L : (L.subgroupOf Γ).map α = K
  card_X : Nat.card ↥((X.subgroupOf Γ).map α) = 3
  comm_X : ∀ x ∈ (X.subgroupOf Γ).map α, ∀ p ∈ K, x * p * x⁻¹ * p⁻¹ ∈ pCoreOf 2 K

theorem NHyp.map {α : ↥Γ →* PGL3 F} {K : Subgroup (PGL3 F)} (h : NHyp Γ L X F α K)
    (φ : PGL3 F ≃* PGL3 F) : NHyp Γ L X F (φ.toMonoidHom.comp α) (K.map φ.toMonoidHom) where
  map_L := by rw [← Subgroup.map_map, h.map_L]
  card_X := by
    rw [← Subgroup.map_map, Subgroup.card_map_of_injective φ.injective, h.card_X]
  comm_X := by
    intro x hx p hp
    rw [← Subgroup.map_map] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨p', hp', rfl⟩ := hp
    rw [pCoreOf_map_inj φ.toMonoidHom φ.injective]
    exact ⟨_, h.comm_X x' hx' p' hp', by simp only [map_mul, map_inv]⟩

theorem concl_congr {α α' : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
    {K K' : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))} {k : ℕ} (hα : α = α')
    (hK : K = K') (h : Concl Γ V Z L X F α' K' k) : Concl Γ V Z L X F α K k := by
  subst hα hK
  exact h

abbrev NormHyp (F : Type) [Field F] : Prop :=
  ∀ Y : Subgroup (PGL3 F), Nat.card Y = 3 →
    (∀ y ∈ Y, ∀ p ∈ Ptheta F 0, y * p * y⁻¹ * p⁻¹ ∈ pCoreOf 2 (Ptheta F 0)) →
    ∃ g : GL (Fin 3) F, ∃ ν : Fˣ, ν ≠ 1 ∧
      (Ptheta F 0).map (MulAut.conj (ProjGenLinGroup.mk g)).toMonoidHom = Ptheta F 0 ∧
      Y.map (MulAut.conj (ProjGenLinGroup.mk g)).toMonoidHom =
        Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν))

section Main

variable [Finite F] [CharP F 2] (hF : Nat.card F = 4) {k : ℕ} {α : ↥Γ →* PGL3 F}
include hF

theorem Model.concl_P0 (hN : NormHyp F) (m : Model Γ V Z F k α) (hk3 : k < 3) (hLΓ : L ≤ Γ)
    (hXΓ : X ≤ Γ) (h : NHyp Γ L X F α (Ptheta F 0)) : Concl Γ V Z L X F α (Ptheta F 0) k := by
  obtain ⟨g, ν, hν, hP, hY⟩ := hN _ h.card_X h.comm_X
  refine concl_of_mulEquiv (MulAut.conj (ProjGenLinGroup.mk g)) (concl_congr rfl hP ?_)
  have hL' := (h.map (MulAut.conj (ProjGenLinGroup.mk g))).map_L
  rw [hP] at hL'
  have hX' : (X.subgroupOf Γ).map ((MulAut.conj (ProjGenLinGroup.mk g)).toMonoidHom.comp α) =
      Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)) := by
    rw [← Subgroup.map_map, hY]
  exact (m.conjGL g).concl_normal hF hk3 hLΓ hXΓ hL' hν hX'

theorem Model.concl_Ptheta (hN : NormHyp F) (m : Model Γ V Z F k α) (hk3 : k < 3)
    (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) {j : Fin 2} (h : NHyp Γ L X F α (Ptheta F j)) :
    Concl Γ V Z L X F α (Ptheta F j) k := by
  match j, h with
  | 0, h => exact m.concl_P0 hF hN hk3 hLΓ hXΓ h
  | 1, h =>
    refine concl_of_mulEquiv (graphAut F) (concl_congr rfl map_graphAut_Ptheta_one ?_)
    refine concl_of_iff (k' := (3 - k) % 3) (by omega) ?_
    have h' := h.map (graphAut F)
    rw [map_graphAut_Ptheta_one] at h'
    exact (m.graph hF hk3).concl_P0 hF hN (Nat.mod_lt _ (by norm_num)) hLΓ hXΓ h'

theorem Model.concl_parabolic (hN : NormHyp F) (m : Model Γ V Z F k α) (hk3 : k < 3)
    (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) {P : Subgroup (PGL3 F)} (hP : IsMaxParabolic2 ⊤ P)
    (h : NHyp Γ L X F α (perfectCore P)) : Concl Γ V Z L X F α (perfectCore P) k := by
  obtain ⟨c, j, hc⟩ := exists_conj_perfectCore hF hP
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective c
  refine concl_of_mulEquiv (MulAut.conj (ProjGenLinGroup.mk g)) (concl_congr rfl hc ?_)
  have h' := h.map (MulAut.conj (ProjGenLinGroup.mk g))
  rw [hc] at h'
  exact (m.conjGL g).concl_Ptheta hF hN hk3 hLΓ hXΓ h'

end Main

end CFSG.Quasithin.H13.Ch4.B414.M

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

theorem lemmaB414Model_of
    (hN : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 → M.NormHyp F) :
    LemmaB414Model := by
  intro G _ _ Γ V Z L X F _ _ α P hyp k hk3 hTw
  have hF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hyp.card]
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 2) (by norm_num) (by rw [hF]; norm_num)
  obtain ⟨hV, hZV, α₂, hα₂s, hker₂, β, hβsl, hβon, hβker, hact⟩ := hTw
  let a : ↥Γ →* PGL3 F := α
  let a₂ : ↥Γ →* PGL3 F := α₂
  let Q : Subgroup (PGL3 F) := P
  have m : M.Model Γ V Z F k a₂ :=
    { β := β
      sl := fun v => hβsl v
      onto := fun M hM => hβon M hM
      ker := fun v => by rw [← MonoidHom.mem_ker, hβker]; exact Iff.rfl
      act := fun γ u v h g hg => hact γ u v h g hg
      normV := hV
      le := hZV }
  obtain ⟨φ, hφ⟩ := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.exists_mulEquiv_of_ker_eq a a₂
    hyp.surj hα₂s hker₂.symm
  have hα₂ : φ.toMonoidHom.comp a = a₂ := MonoidHom.ext fun γ => (hφ γ).symm
  have h0 : M.NHyp Γ L X F a (perfectCore Q) := ⟨hyp.map_L, hyp.card_X, fun x hx p hp => by
    have h := hyp.comm_X x hx p (by rw [hyp.map_L]; exact hp)
    rwa [hyp.map_L] at h⟩
  have h2 := h0.map φ
  rw [hα₂, map_perfectCore] at h2
  have hc : M.Concl Γ V Z L X F a (perfectCore Q) k :=
    M.concl_of_mulEquiv φ (M.concl_congr hα₂ (map_perfectCore _ _)
      (m.concl_parabolic hF (hN F hF) hk3 hyp.le_L hyp.le_X
        (M.isMaxParabolic2_map φ hyp.maxParabolic) h2))
  exact hc

theorem lemmaB414Model_holds : LemmaB414Model :=
  lemmaB414Model_of fun _ _ _ _ hF _ hY3 hYL => M.exists_conj_normal hF hY3 hYL

end CFSG.Quasithin.H13.Ch4.B414
