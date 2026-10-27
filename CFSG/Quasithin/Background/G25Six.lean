module

public import CFSG.Quasithin.Background.G25Triple
public import CFSG.Quasithin.Background.G25Bridge

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G] {F : Type*} [Field F]

@[expose] def pairFam (S : Subgroup G) (Uk : Fin 3 → Subgroup G) : Fin 3 → Subgroup G :=
  ![TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2, TripleGrp.W S Uk 0 ⊓ TripleGrp.W S Uk 2,
    TripleGrp.W S Uk 0 ⊓ TripleGrp.W S Uk 1]

theorem mem_pairFam_iff (S : Subgroup G) (Uk : Fin 3 → Subgroup G) (k : Fin 3) (y : G) :
    y ∈ pairFam S Uk k ↔ ∀ m : Fin 3, m ≠ k → y ∈ TripleGrp.W S Uk m := by
  fin_cases k
  · constructor
    · intro hy m hm
      fin_cases m
      · exact absurd rfl hm
      · exact hy.1
      · exact hy.2
    · intro hy
      exact ⟨hy 1 (by decide), hy 2 (by decide)⟩
  · constructor
    · intro hy m hm
      fin_cases m
      · exact hy.1
      · exact absurd rfl hm
      · exact hy.2
    · intro hy
      exact ⟨hy 0 (by decide), hy 2 (by decide)⟩
  · constructor
    · intro hy m hm
      fin_cases m
      · exact hy.1
      · exact hy.2
      · exact absurd rfl hm
    · intro hy
      exact ⟨hy 0 (by decide), hy 1 (by decide)⟩

theorem pairFam_eq (S : Subgroup G) (Uk : Fin 3 → Subgroup G) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    pairFam S Uk k = TripleGrp.W S Uk i ⊓ TripleGrp.W S Uk j := by
  ext y
  rw [mem_pairFam_iff]
  constructor
  · intro hy
    exact ⟨hy i hik, hy j hjk⟩
  · intro hy m hm
    rcases TripleGrp.fin_three_cases i j k m hij hik hjk with rfl | rfl | rfl
    · exact hy.1
    · exact hy.2
    · exact absurd rfl hm

theorem pairFam_le_S₃ (S : Subgroup G) (Uk : Fin 3 → Subgroup G) (k : Fin 3) :
    pairFam S Uk k ≤ TripleGrp.S₃ S Uk := by
  fin_cases k
  · exact TripleGrp.Wij_le_S₃ (by decide : (1 : Fin 3) ≠ 2)
  · exact TripleGrp.Wij_le_S₃ (by decide : (0 : Fin 3) ≠ 2)
  · exact TripleGrp.Wij_le_S₃ (by decide : (0 : Fin 3) ≠ 1)

namespace TripleL3

variable [CharP F 2] {I S : Subgroup G} {Uk : Fin 3 → Subgroup G} {Φ : ↥I →* SL(3, F)}
  {p : Fin 3 → Fin 3 → F} {Q : SL(3, F)} {lam : Fin 3 → F}
  (hT : TripleL3 I S Uk Φ p Q lam)

include hT

omit [CharP F 2] in
theorem conj_pairFam {π : Equiv.Perm (Fin 3)} (x : ↥I)
    (hx : ∀ m, ∃ c : F, Φ x • p m = c • p (π m)) (k : Fin 3) :
    ∀ y ∈ pairFam S Uk k, (x : G) * y * (x : G)⁻¹ ∈ pairFam S Uk (π k) := by
  intro y hy
  rw [mem_pairFam_iff] at hy ⊢
  intro m' hm'
  have hm : π.symm m' ≠ k := fun h => hm' (by rw [← h, Equiv.apply_symm_apply])
  have := hT.conj_W x (hx (π.symm m')) y (hy _ hm)
  rwa [Equiv.apply_symm_apply] at this

omit [CharP F 2] in
theorem conj_pairFam_inv {π : Equiv.Perm (Fin 3)} (x : ↥I)
    (hx : ∀ m, ∃ c : F, Φ x • p m = c • p (π m)) (k : Fin 3) :
    ∀ z ∈ pairFam S Uk (π k), (x : G)⁻¹ * z * (x : G) ∈ pairFam S Uk k := by
  intro z hz
  rw [mem_pairFam_iff] at hz ⊢
  intro m' hm'
  have hm : π m' ≠ π k := fun h => hm' (π.injective h)
  have := hT.conj_W x⁻¹ (hT.inv_pt x (hx m')) z (hz _ hm)
  simpa using this

theorem sectionFam_six (hn : 2 ≤ 3) :
    SectionFam hn I (TripleGrp.S₃ S Uk) (TripleGrp.S₂ Uk) Φ
      ((MulAut.conj Q).toMonoidHom.comp (dualHom F 3)) (pairFam S Uk) where
  N_le := fun k z hz => (mem_pairFam_iff S Uk k z).2 fun m _ => hT.tg.S₂_le_W m hz
  le_Sx := fun k => pairFam_le_S₃ S Uk k
  swap := fun k hk => by
    obtain ⟨x, hx, hxp⟩ := hT.exists_lift_wS hk
    have hx' : Φ x = ((MulAut.conj Q).toMonoidHom.comp (dualHom F 3)) (wS F hk) := by
      rw [hx]
      show _ = Q * dualHom F 3 (wS F hk) * Q⁻¹
      rw [dualHom_wS]
    have hπ : (Equiv.swap (idx0 hn) k) (idx0 hn) = k := Equiv.swap_apply_left _ _
    refine ⟨x, hx', ?_, ?_⟩
    · intro y hy
      have := hT.conj_pairFam (π := Equiv.swap (idx0 hn) k) x hxp (idx0 hn) y hy
      rwa [Equiv.swap_apply_left] at this
    · intro z hz
      have := hT.conj_pairFam_inv (π := Equiv.swap (idx0 hn) k) x hxp (idx0 hn) z
        (by rwa [Equiv.swap_apply_left])
      exact this
  torus := fun d => by
    obtain ⟨x, hx, hxp⟩ := hT.exists_lift_diag
      ((diagLike_embSL (idx0_ne_idx1 hn) d).dualHom)
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact hT.conj_pairFam (π := Equiv.refl _) x hxp (idx0 hn) y hy
  root := fun a b hab k hk c => by
    obtain ⟨x, hxU, hx, hxp⟩ := hT.exists_lift_transvection hab.symm c
    have hx' : Φ x = ((MulAut.conj Q).toMonoidHom.comp (dualHom F 3))
        (Matrix.SpecialLinearGroup.transvection hab c) := by
      rw [hx]
      show _ = Q * dualHom F 3 (Matrix.SpecialLinearGroup.transvection hab c) * Q⁻¹
      rw [dualHom_transvection]
    refine ⟨x, hx', fun y hy => ?_⟩
    have hyW : y ∈ TripleGrp.W S Uk b := (mem_pairFam_iff S Uk k y).1 hy b (Ne.symm hk)
    exact hT.tg.comm_U b x hxU y hyW.1
  comm := fun c => by
    obtain ⟨x, hxU, hx, hxp⟩ := hT.exists_lift_transvection (idx0_ne_idx1 hn).symm c
    have hx' : Φ x = ((MulAut.conj Q).toMonoidHom.comp (dualHom F 3))
        (Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c) := by
      rw [hx]
      show _ = Q * dualHom F 3 (Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c) * Q⁻¹
      rw [dualHom_transvection]
    refine ⟨x, hx', ?_⟩
    have hN : ∀ s ∈ S, ∀ z ∈ TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2,
        s * z * s⁻¹ ∈ TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2 := fun s hs z hz =>
      (Subgroup.mem_normalizer_iff.1 (hT.tg.S_le_normalizer_Wij hs) z).1 hz
    have hS₂N : ∀ y ∈ Uk 1, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈
        TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2 := fun y hy =>
      ⟨hT.tg.S₂_le_W 1 (hT.tg.comm_U 1 x hxU y hy), hT.tg.S₂_le_W 2 (hT.tg.comm_U 1 x hxU y hy)⟩
    have hX₁ : ∀ y ∈ TripleGrp.W S Uk 0 ⊓ TripleGrp.W S Uk 1,
        (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2 :=
      fun y hy => hS₂N y hy.2.1
    have hX₃ : ∀ y ∈ TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2,
        (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2 :=
      fun y hy => hS₂N y hy.1.1
    have hX₂ : ∀ y ∈ TripleGrp.W S Uk 0 ⊓ TripleGrp.W S Uk 2,
        (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2 := by
      intro y hy
      have hfix : Φ x • p 2 = p 2 := hxp 2 (by rw [show idx0 hn = (0 : Fin 3) from rfl]; decide)
      have hxW : (x : G) * y * (x : G)⁻¹ ∈ TripleGrp.W S Uk 2 :=
        hT.conj_W x ⟨1, by rw [hfix, one_smul]⟩ y hy.2
      have h1 : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk 2 :=
        (TripleGrp.W S Uk 2).mul_mem hxW ((TripleGrp.W S Uk 2).inv_mem hy.2)
      have h2 : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk 1 :=
        hT.tg.comm_Uk_S 1 hxU hy.1.2
      exact ⟨h2, h1⟩
    have h01 : ∀ y ∈ (TripleGrp.W S Uk 0 ⊓ TripleGrp.W S Uk 1) ⊔
        (TripleGrp.W S Uk 0 ⊓ TripleGrp.W S Uk 2),
        (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.W S Uk 1 ⊓ TripleGrp.W S Uk 2 :=
      comm_mem_sup_of (J := S) hN (inf_le_left.trans inf_le_right)
        (inf_le_left.trans inf_le_right) hX₁ hX₂
    exact comm_mem_sup_of (J := S) hN (sup_le (inf_le_left.trans inf_le_right)
      (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right) h01 hX₃
  disj := by
    intro z hz
    have h0 : ∀ m : Fin 3, m ≠ 0 → z ∈ TripleGrp.W S Uk m :=
      (mem_pairFam_iff S Uk 0 z).1 hz.1
    have h1 : ∀ m : Fin 3, m ≠ 1 → z ∈ TripleGrp.W S Uk m :=
      (mem_pairFam_iff S Uk 1 z).1 hz.2
    refine TripleGrp.mem_S₂_of_forall fun m => ?_
    rcases TripleGrp.fin_three_cases 0 1 2 m (by decide) (by decide) (by decide) with
      rfl | rfl | rfl
    · exact (h1 0 (by decide)).1
    · exact (h0 1 (by decide)).1
    · exact (h0 2 (by decide)).1
  sup := by
    apply le_antisymm
    · exact iSup_le fun k => pairFam_le_S₃ S Uk k
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact (le_of_eq (pairFam_eq S Uk (i := 0) (j := 1) (k := 2) (by decide) (by decide)
          (by decide)).symm).trans (le_iSup (pairFam S Uk) 2)
      · exact (le_of_eq (pairFam_eq S Uk (i := 0) (j := 2) (k := 1) (by decide) (by decide)
          (by decide)).symm).trans (le_iSup (pairFam S Uk) 1)
      · exact (le_of_eq (pairFam_eq S Uk (i := 1) (j := 2) (k := 0) (by decide) (by decide)
          (by decide)).symm).trans (le_iSup (pairFam S Uk) 0)

omit [CharP F 2] in
theorem quotSetting_six : QuotSetting I (TripleGrp.S₃ S Uk) (TripleGrp.S₂ Uk) where
  S₂_le := hT.tg.S₂_le_S₃
  Sx_le := TripleGrp.S₃_le_S.trans hT.tg.S_le_I
  nS := fun x hx y hy => hT.invS₃ x hx y hy
  nS₂ := hT.tg.S₂_norm
  abel := fun _ ha _ hb => hT.tg.comm_S₃_S ha (TripleGrp.S₃_le_S hb)
  sq := fun _ ha => hT.tg.S₃_sq ha

theorem exists_six_core [Finite G] [Finite F] :
    ∃ (s : ℕ) (φ : ↥(TripleGrp.S₃ S Uk) →* Multiplicative (Fin s → Fin 3 → F)),
      Function.Surjective φ ∧ (∀ x : ↥(TripleGrp.S₃ S Uk), φ x = 1 ↔ (x : G) ∈ TripleGrp.S₂ Uk) ∧
      (∀ (m : ↥I) (g : SL(3, F)) (x y : ↥(TripleGrp.S₃ S Uk)), Q * dualHom F 3 g * Q⁻¹ = Φ m →
        (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
          φ y = Multiplicative.ofAdd (fun l => g • Multiplicative.toAdd (φ x) l)) ∧
      (∀ (k : Fin 3) (x : ↥(TripleGrp.S₃ S Uk)), (x : G) ∈ pairFam S Uk k ↔
        ∀ (l : Fin s) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0) ∧
      Nat.card ↥(pairFam S Uk 0) = Nat.card ↥(TripleGrp.S₂ Uk) * Nat.card F ^ s := by
  have hker : ∀ x : ↥I, Φ x = 1 → ∀ y ∈ TripleGrp.S₃ S Uk,
      (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ TripleGrp.S₂ Uk := by
    intro x hx y hy
    have h1 : ⁅y, (x : G)⁆ ∈ TripleGrp.S₂ Uk := hT.tg.comm_S₃_S hy ((hT.ker x).1 hx)
    have h2 : (x : G) * y * (x : G)⁻¹ * y⁻¹ = ⁅y, (x : G)⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact (TripleGrp.S₂ Uk).inv_mem h1
  obtain ⟨s, φ, hs, hk, he, hc, hcard⟩ := exists_phi_of_sectionFam (hn := (by norm_num : 2 ≤ 3))
    hT.quotSetting_six Φ hT.surj hker ((MulAut.conj Q).toMonoidHom.comp (dualHom F 3))
    (hT.sectionFam_six (by norm_num))
  exact ⟨s, φ, hs, hk, fun m g x y hg hy => he m g x y hg hy, hc, hcard⟩

omit [CharP F 2] in
theorem dual_dot_p (y : Fin 3 → F) (i : Fin 3) :
    (dualHom F 3 Q • y) ⬝ᵥ p i = (lam i)⁻¹ * y i := by
  have h1 := dualHom_smul_dot_single Q y i
  rw [hT.basis i, dotProduct_smul, smul_eq_mul] at h1
  rw [← h1, ← mul_assoc, inv_mul_cancel₀ (hT.lam_ne i), one_mul]

omit [CharP F 2] in
theorem six_untwist {s : ℕ} (φ : ↥(TripleGrp.S₃ S Uk) →* Multiplicative (Fin s → Fin 3 → F))
    (hs : Function.Surjective φ)
    (hk : ∀ x : ↥(TripleGrp.S₃ S Uk), φ x = 1 ↔ (x : G) ∈ TripleGrp.S₂ Uk)
    (he : ∀ (m : ↥I) (g : SL(3, F)) (x y : ↥(TripleGrp.S₃ S Uk)), Q * dualHom F 3 g * Q⁻¹ = Φ m →
      (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
        φ y = Multiplicative.ofAdd (fun l => g • Multiplicative.toAdd (φ x) l))
    (hc : ∀ (k : Fin 3) (x : ↥(TripleGrp.S₃ S Uk)), (x : G) ∈ pairFam S Uk k ↔
      ∀ (l : Fin s) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0) :
    ∃ φ' : ↥(TripleGrp.S₃ S Uk) →* Multiplicative (Fin s → Fin 3 → F),
      Function.Surjective φ' ∧ (∀ x : ↥(TripleGrp.S₃ S Uk), φ' x = 1 ↔ (x : G) ∈ TripleGrp.S₂ Uk) ∧
      (∀ (m : ↥I) (x y : ↥(TripleGrp.S₃ S Uk)), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
        φ' y = Multiplicative.ofAdd
          (fun l => dualHom F 3 (Φ m) • Multiplicative.toAdd (φ' x) l)) ∧
      (∀ (i j : Fin 3), i ≠ j → ∀ x : ↥(TripleGrp.S₃ S Uk),
        (x : G) ∈ TripleGrp.W S Uk i ⊓ TripleGrp.W S Uk j ↔
          ∀ l : Fin s, Multiplicative.toAdd (φ' x) l ⬝ᵥ p i = 0 ∧
            Multiplicative.toAdd (φ' x) l ⬝ᵥ p j = 0) := by
  refine ⟨(copiesHom s (dualHom F 3 Q)).comp φ, (copiesHom_surjective s _).comp hs,
    fun x => ?_, fun m x y hy => copiesHom_equivariant Φ (dualHom F 3) (dualHom_dualHom) Q φ he
      m x y hy, fun i j hij x => ?_⟩
  · rw [MonoidHom.comp_apply, copiesHom_eq_one_iff, hk]
  · obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      revert i j
      decide
    rw [← pairFam_eq S Uk hij hki hkj, hc k x]
    have hdot : ∀ (l : Fin s) (m : Fin 3), Multiplicative.toAdd
        (((copiesHom s (dualHom F 3 Q)).comp φ) x) l ⬝ᵥ p m =
          (lam m)⁻¹ * Multiplicative.toAdd (φ x) l m := fun l m => by
      rw [MonoidHom.comp_apply, copiesHom_toAdd]
      exact hT.dual_dot_p _ m
    have hzero : ∀ (l : Fin s) (m : Fin 3), Multiplicative.toAdd
        (((copiesHom s (dualHom F 3 Q)).comp φ) x) l ⬝ᵥ p m = 0 ↔
          Multiplicative.toAdd (φ x) l m = 0 := fun l m => by
      rw [hdot, mul_eq_zero]
      simp [hT.lam_ne m]
    constructor
    · intro hx l
      exact ⟨(hzero l i).2 (hx l i hki), (hzero l j).2 (hx l j hkj)⟩
    · intro hx l m hm
      rcases TripleGrp.fin_three_cases i j k m hij hki hkj with rfl | rfl | rfl
      · exact (hzero l _).1 (hx l).1
      · exact (hzero l _).1 (hx l).2
      · exact absurd rfl hm

end TripleL3

end CFSG.Quasithin
