module

public import CFSG.Quasithin.Background.Harris.KFact2d.ModelU3
public import CFSG.Quasithin.Vol2.Ch11SecU1U3E

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups

theorem exists_equiv_of_map_eq {A B : Type} [Group A] [Group B] (H : Subgroup A) (H' : Subgroup B)
    (f : A →* B) (hf : Function.Injective f) (h : H.map f = H') : Nonempty (↥H ≃* ↥H') :=
  ⟨(Subgroup.equivMapOfInjective H f hf).trans (MulEquiv.subgroupCongr h)⟩

theorem exists_equiv_commutator {A B : Type} [Group A] [Group B] (ψ : A ≃* B) :
    Nonempty (↥(commutator A) ≃* ↥(commutator B)) := by
  refine exists_equiv_of_map_eq _ _ ψ.toMonoidHom ψ.injective ?_
  show Subgroup.map ψ.toMonoidHom ⁅(⊤ : Subgroup A), ⊤⁆ = ⁅(⊤ : Subgroup B), ⊤⁆
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ ψ.surjective]

theorem exists_equiv_commutator_subgroup {B : Type} [Group B] (H : Subgroup B) :
    Nonempty (↥(commutator ↥H) ≃* ↥⁅H, H⁆) := by
  refine exists_equiv_of_map_eq _ _ H.subtype H.subtype_injective ?_
  show Subgroup.map H.subtype ⁅(⊤ : Subgroup ↥H), ⊤⁆ = ⁅H, H⁆
  rw [Subgroup.map_commutator]
  have : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [this]

variable {X : Type} [Group X] [Finite X]

theorem model_five {K S : Subgroup X} (hK : IsPSU 3 5 1 ↥K) (hS : IsSylowTwoOf S K) :
    Nat.card ↥(cenZ K S) = 240 ∧ Nonempty (↥(commutator ↥(cenZ K S)) ≃* SL(2, ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨F, _, _, hF, e, U₀, hU₀, hmap⟩ := exists_equiv_special_u (p := 5) (by norm_num) hK hS
  have hC : Subgroup.centralizer (E2P.zOf U₀ : Set (PSU3F 5 F)) = leviCU hF :=
    centralizer_zOf_eq_leviCU (by norm_num) hF hU₀.1 hU₀.2.1
  set Cenk : Subgroup ↥K := Subgroup.centralizer (E2P.zOf (S.subgroupOf K) : Set ↥K) with hCenk
  have hcenK : Cenk.map K.subtype = cenZ K S := by
    ext x
    rw [mem_cenZ_iff hS.1, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hyc, hy⟩
      exact ⟨y, hy, hyc⟩
    · rintro ⟨y, hy, hyc⟩
      exact ⟨y, hyc, hy⟩
  have hcen : Cenk.map e.toMonoidHom = leviCU hF := by
    rw [← hC, ← hmap]
    ext w
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have hy' := (mem_zOf_map_iff e _ y).1 hy
      have := h _ hy'
      apply e.symm.injective
      simpa using this
    · intro h z hz
      have hz' : e z ∈ E2P.zOf ((S.subgroupOf K).map e.toMonoidHom) :=
        (mem_zOf_map_iff e _ (e z)).2 (by simpa using hz)
      have := h _ hz'
      apply e.injective
      simpa using this
  obtain ⟨ψ₁⟩ := exists_equiv_of_map_eq Cenk (cenZ K S) K.subtype K.subtype_injective hcenK
  obtain ⟨ψ₂⟩ := exists_equiv_of_map_eq Cenk (leviCU hF) e.toMonoidHom e.injective hcen
  let ψ : ↥(cenZ K S) ≃* ↥(leviCU hF) := ψ₁.symm.trans ψ₂
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr ψ.toEquiv]
    have hK126 : Nat.card ↥K = 126000 :=
      (CFSG.RankThree.Classical.unitary_three_five_model ↥K hK).1
    have hP : Nat.card (PSU3F 5 F) = 126000 := (Nat.card_congr e.toEquiv).symm.trans hK126
    have hidx : (leviCU hF).index = 525 := by
      rw [index_leviCU (by norm_num) hF, index_leviU hF]
      norm_num
    have h := Subgroup.card_mul_index (leviCU hF)
    rw [hidx, hP] at h
    omega
  · obtain ⟨ψ₃⟩ := exists_equiv_commutator ψ
    obtain ⟨ψ₄⟩ := exists_equiv_commutator_subgroup (leviCU hF)
    have hc : ⁅leviCU hF, leviCU hF⁆ = CFSG.Quasithin.Vol2.Ch11.SecU1.U3.leviSL hF :=
      CFSG.Quasithin.Vol2.Ch11.SecU1.U3.commutator_leviCU (by norm_num) hF
    let ψ₅ := ψ₃.trans (ψ₄.trans (MulEquiv.subgroupCongr hc))
    exact ⟨ψ₅.trans (CFSG.Quasithin.Vol2.Ch11.SecU1.U3.leviSLEquiv hF).symm⟩

end CFSG.Quasithin.Background.Harris.KFact2d
