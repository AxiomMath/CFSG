module

public import CFSG.Quasithin.Background.G25Triple
public import CFSG.Quasithin.Background.G25Bridge

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G] {F : Type*} [Field F]

namespace TripleL3

variable [CharP F 2] {I S : Subgroup G} {Uk : Fin 3 → Subgroup G} {Φ : ↥I →* SL(3, F)}
  {p : Fin 3 → Fin 3 → F} {Q : SL(3, F)} {lam : Fin 3 → F}
  (hT : TripleL3 I S Uk Φ p Q lam)

include hT

theorem sectionFam_seven (hn : 2 ≤ 3) :
    SectionFam hn I S (TripleGrp.S₃ S Uk) Φ (MulAut.conj Q).toMonoidHom
      (fun k => TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk) where
  N_le := fun k => le_sup_right
  le_Sx := fun k => sup_le inf_le_right TripleGrp.S₃_le_S
  swap := fun k hk => by
    obtain ⟨x, hx, hxp⟩ := hT.exists_lift_wS hk
    have h1 : ∃ c : F, Φ x • p (idx0 hn) = c • p k := by
      obtain ⟨c, hc⟩ := hxp (idx0 hn)
      exact ⟨c, by rw [hc, Equiv.swap_apply_left]⟩
    refine ⟨x, hx, hT.conj_sup x h1, fun z hz => ?_⟩
    have := hT.conj_sup x⁻¹ (hT.inv_pt x h1) z hz
    simpa using this
  torus := fun d => by
    obtain ⟨x, hx, hxp⟩ := hT.exists_lift_diag (diagLike_embSL (idx0_ne_idx1 hn) d)
    exact ⟨x, hx, hT.conj_sup x (hxp (idx0 hn))⟩
  root := fun a b hab k hk c => by
    obtain ⟨x, hxU, hx, hxp⟩ := hT.exists_lift_transvection hab c
    refine ⟨x, hx, ?_⟩
    refine comm_mem_sup_of (J := I) (fun y hy z hz => hT.invS₃ y hy z hz) ?_ ?_ ?_ ?_
    · exact inf_le_right.trans hT.tg.S_le_I
    · exact TripleGrp.S₃_le_S.trans hT.tg.S_le_I
    · intro y hy
      rcases eq_or_ne k a with hka | hka
      · have hyU : y ∈ Uk a := hka ▸ hy.1
        exact hT.tg.S₂_le_S₃ (hT.tg.comm_U a x hxU y hyU)
      · have hfix : Φ x • p k = p k := hxp k hk
        have hxW : (x : G) * y * (x : G)⁻¹ ∈ TripleGrp.W S Uk k :=
          hT.conj_W x ⟨1, by rw [hfix, one_smul]⟩ y hy
        have h1 : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk k :=
          (TripleGrp.W S Uk k).mul_mem hxW ((TripleGrp.W S Uk k).inv_mem hy)
        have h2 : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk a :=
          hT.tg.comm_Uk_S a hxU hy.2
        exact TripleGrp.Wij_le_S₃ (Ne.symm hka) ⟨h2, h1⟩
    · intro y hy
      exact (TripleGrp.S₃ S Uk).mul_mem (hT.conj_S₃ x y hy) ((TripleGrp.S₃ S Uk).inv_mem hy)
  comm := fun c => by
    obtain ⟨x, hxU, hx, -⟩ := hT.exists_lift_transvection (idx0_ne_idx1 hn) c
    exact ⟨x, hx, fun y hy => Subgroup.mem_sup_left (hT.tg.comm_Uk_S (idx0 hn) hxU hy)⟩
  disj := fun z hz => hT.tg.inter_W_S₃ hz.1 hz.2
  sup := by
    apply le_antisymm
    · exact iSup_le fun k => sup_le inf_le_right TripleGrp.S₃_le_S
    · refine hT.tg.S_eq.le.trans (sup_le (sup_le ?_ ?_) ?_)
      · exact le_sup_left.trans
          (le_iSup (fun k => TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk) 0)
      · exact le_sup_left.trans
          (le_iSup (fun k => TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk) 1)
      · exact le_sup_left.trans
          (le_iSup (fun k => TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk) 2)

omit [CharP F 2] in
theorem quotSetting_seven : QuotSetting I S (TripleGrp.S₃ S Uk) where
  S₂_le := TripleGrp.S₃_le_S
  Sx_le := hT.tg.S_le_I
  nS := hT.tg.S_norm
  nS₂ := hT.invS₃
  abel := fun _ ha _ hb => hT.tg.S_abel ha hb
  sq := fun _ ha => hT.tg.S_sq ha

theorem exists_seven_core [Finite G] [Finite F] :
    ∃ (r : ℕ) (φ : ↥S →* Multiplicative (Fin r → Fin 3 → F)), Function.Surjective φ ∧
      (∀ x : ↥S, φ x = 1 ↔ (x : G) ∈ TripleGrp.S₃ S Uk) ∧
      (∀ (m : ↥I) (g : SL(3, F)) (x y : ↥S), Q * g * Q⁻¹ = Φ m →
        (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
          φ y = Multiplicative.ofAdd (fun l => g • Multiplicative.toAdd (φ x) l)) ∧
      (∀ (k : Fin 3) (x : ↥S), (x : G) ∈ TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk ↔
        ∀ (l : Fin r) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0) ∧
      Nat.card ↥(TripleGrp.W S Uk 0 ⊔ TripleGrp.S₃ S Uk) =
        Nat.card ↥(TripleGrp.S₃ S Uk) * Nat.card F ^ r := by
  have hker : ∀ x : ↥I, Φ x = 1 → ∀ y ∈ S, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.S₃ S Uk :=
    fun x hx y hy => hT.tg.S_abel ((hT.ker x).1 hx) hy
  obtain ⟨r, φ, hs, hk, he, hc, hcard⟩ := exists_phi_of_sectionFam (hn := (by norm_num : 2 ≤ 3))
    hT.quotSetting_seven Φ hT.surj hker (MulAut.conj Q).toMonoidHom
    (hT.sectionFam_seven (by norm_num))
  exact ⟨r, φ, hs, hk, fun m g x y hg hy => he m g x y hg hy, hc, hcard⟩

omit [CharP F 2] in
theorem seven_untwist {r : ℕ} (φ : ↥S →* Multiplicative (Fin r → Fin 3 → F))
    (hs : Function.Surjective φ) (hk : ∀ x : ↥S, φ x = 1 ↔ (x : G) ∈ TripleGrp.S₃ S Uk)
    (he : ∀ (m : ↥I) (g : SL(3, F)) (x y : ↥S), Q * g * Q⁻¹ = Φ m →
      (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
        φ y = Multiplicative.ofAdd (fun l => g • Multiplicative.toAdd (φ x) l))
    (hc : ∀ (k : Fin 3) (x : ↥S), (x : G) ∈ TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk ↔
      ∀ (l : Fin r) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0) :
    ∃ φ' : ↥S →* Multiplicative (Fin r → Fin 3 → F), Function.Surjective φ' ∧
      (∀ x : ↥S, φ' x = 1 ↔ (x : G) ∈ TripleGrp.S₃ S Uk) ∧
      (∀ (m : ↥I) (x y : ↥S), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
        φ' y = Multiplicative.ofAdd (fun l => Φ m • Multiplicative.toAdd (φ' x) l)) ∧
      (∀ (k : Fin 3) (x : ↥S), (x : G) ∈ TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk ↔
        ∀ l : Fin r, ∃ c : F, Multiplicative.toAdd (φ' x) l = c • p k) := by
  refine ⟨(copiesHom r Q).comp φ, (copiesHom_surjective r Q).comp hs, fun x => ?_,
    fun m x y hy => copiesHom_equivariant Φ (MonoidHom.id _) (fun g => rfl) Q φ he m x y hy,
    fun k x => ?_⟩
  · rw [MonoidHom.comp_apply, copiesHom_eq_one_iff, hk]
  · rw [hc k x]
    constructor
    · intro hx l
      obtain ⟨c, hc'⟩ := (forall_coord_eq_zero_iff Q k _).1 (hx l)
      refine ⟨c * lam k, ?_⟩
      rw [MonoidHom.comp_apply, copiesHom_toAdd, hc', hT.basis k, smul_smul]
    · intro hx l
      obtain ⟨c, hc'⟩ := hx l
      refine (forall_coord_eq_zero_iff Q k _).2 ⟨c * (lam k)⁻¹, ?_⟩
      rw [hT.basis k, smul_smul, mul_assoc, inv_mul_cancel₀ (hT.lam_ne k), mul_one]
      rw [MonoidHom.comp_apply, copiesHom_toAdd] at hc'
      exact hc'

end TripleL3

end CFSG.Quasithin
