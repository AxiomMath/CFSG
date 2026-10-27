module

public import CFSG.Quasithin.H13.L32NLem14333h

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

@[expose] def y0 : SL(3, ZMod 2) := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

theorem sl3_comm_A4 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (∀ b c : ZMod 2, M * (tq b c : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (tq b c : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M) →
    M * (y0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (y0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M →
    M = 0 ∨ M = 1 := by
  decide +kernel

theorem sl3_y0_mem : ∀ y : SL(3, ZMod 2), y ^ 3 = 1 → y ≠ 1 →
    y • vE (ZMod 2) 0 = vE (ZMod 2) 0 → ∃ b c : ZMod 2, ∃ k : Fin 3, y0 = tq b c * y ^ (k : ℕ) := by
  decide +kernel

theorem sl3_centralizer_Qv : ∀ g : SL(3, ZMod 2), (∀ b c : ZMod 2, g * tq b c = tq b c * g) →
    ∃ b c : ZMod 2, g = tq b c := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_pCoreOf_LT {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
    (pCoreOf_isPGroup 2 L)

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem conj_mem_V {l v : G} (hl : l ∈ L) (hv : v ∈ V) : l * v * l⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (c.L_le_normV hl) v).mp hv

theorem exists_coordZ (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    ∃ (θ : ↥L →* SL(3, ZMod 2)) (ψ : ↥V ≃* Multiplicative (Fin 3 → ZMod 2)),
      Function.Surjective θ ∧ (∀ l : ↥L, θ l = 1 ↔ (l : G) ∈ pCoreOf 2 L) ∧
      (∀ (l : ↥L) (v : ↥V),
        Multiplicative.toAdd (ψ ⟨(l : G) * v * (l : G)⁻¹, c.conj_mem_V l.2 v.2⟩) =
          θ l • Multiplicative.toAdd (ψ v)) ∧
      (∀ v : ↥V, (v : G) ∈ fsuV1 T V ↔
        ∃ e : ZMod 2, Multiplicative.toAdd (ψ v) = e • vE (ZMod 2) 0) ∧
      (∀ u : ↥L, (u : G) ∈ fsuU T V → θ u ∈ Qv (vE (ZMod 2) 0)) ∧
      (∀ q ∈ Qv (vE (ZMod 2) 0), ∃ u : ↥L, (u : G) ∈ fsuU T V ∧ θ u = q) := by
  obtain ⟨D'⟩ := hyp.natural.nonempty_data
  let St : L3Setting 1 V (fsuV1 T V) L T (l32nH T V) := ⟨hyp, D'⟩
  set F := GaloisField 2 1
  let e : F ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let Φ : SL(3, F) →* SL(3, ZMod 2) := Matrix.SpecialLinearGroup.map e.toRingHom
  have hΦ : ∀ A : SL(3, F), ((Φ A : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (A : Matrix (Fin 3) (Fin 3) F).map e := fun A => rfl
  have hΦinj : Function.Injective Φ := by
    intro A B h
    ext i j
    have := congrFun (congrFun (congrArg (fun M : SL(3, ZMod 2) =>
      (M : Matrix (Fin 3) (Fin 3) (ZMod 2))) h) i) j
    simp only [hΦ, Matrix.map_apply] at this
    exact e.injective this
  have hΦsurj : Function.Surjective Φ := by
    intro B
    refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom B, ?_⟩
    ext i j
    simp [hΦ, Matrix.SpecialLinearGroup.map_apply_coe]
  have hΦsmul : ∀ (A : SL(3, F)) (w : Fin 3 → F), Φ A • (e ∘ w) = e ∘ (A • w) := by
    intro A w
    ext i
    have := RingHom.map_mulVec e.toRingHom (A : Matrix (Fin 3) (Fin 3) F) w i
    exact this.symm
  have hΦtq : ∀ b' c' : F, Φ (tq b' c') = tq (e b') (e c') := by
    intro b' c'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hΦ, tq_coe]
  let ψ₀ : Multiplicative (Fin 3 → F) ≃* Multiplicative (Fin 3 → ZMod 2) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hψ₀ : ∀ w : Multiplicative (Fin 3 → F),
      Multiplicative.toAdd (ψ₀ w) = e ∘ Multiplicative.toAdd w := fun w => rfl
  have hPO : ∀ l : ↥L, (l : G) ∈ pCoreOf 2 (L ⊔ T) ↔ (l : G) ∈ pCoreOf 2 L := fun l =>
    ⟨fun h => inf_pCoreOf_LT l.2 h, fun h => pCoreOf_le_pCoreOf_LT c.T_le_normL h⟩
  have hUL := c.U_le_L hyp
  refine ⟨Φ.comp D'.θ, D'.ψ.trans ψ₀, hΦsurj.comp D'.surj, fun l => ?_, fun l v => ?_,
    fun v => ?_, fun u hu => ?_, fun q hq => ?_⟩
  · rw [MonoidHom.comp_apply, ← hPO, ← Subgroup.mem_subgroupOf (H := pCoreOf 2 (L ⊔ T)) (K := L),
      ← D'.ker_eq, MonoidHom.mem_ker]
    constructor
    · intro h
      exact hΦinj (h.trans (map_one Φ).symm)
    · intro h
      rw [h, map_one]
  · have h1 := D'.equiv l v
    rw [natAct3_apply] at h1
    have he : conjAct V ⟨l, D'.hnorm l.2⟩ v = ⟨(l : G) * v * (l : G)⁻¹, c.conj_mem_V l.2 v.2⟩ :=
      Subtype.ext (conjAct_coe_apply V _ _)
    rw [he] at h1
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψ₀, hψ₀, h1, toAdd_ofAdd, MonoidHom.comp_apply]
    exact (hΦsmul _ _).symm
  · rw [D'.line v, MulEquiv.trans_apply, hψ₀]
    constructor
    · rintro ⟨e', he'⟩
      refine ⟨e e', ?_⟩
      rw [he']
      ext i
      fin_cases i <;> simp [vE]
    · rintro ⟨e', he'⟩
      refine ⟨e.symm e', ?_⟩
      ext i
      have := congrFun he' i
      fin_cases i <;> simp [vE] at this ⊢ <;> (apply e.injective; simpa using this)
  · have hb : St.betaU ⟨u, hu⟩ = D'.θ u := by
      rw [L3Setting.betaU_apply]
      exact St.Phi_of_L u
    have hmem := St.betaU_mem_Qv ⟨u, hu⟩
    rw [hb] at hmem
    obtain ⟨b', c', hbc⟩ := mem_Qv_e0.mp hmem
    rw [MonoidHom.comp_apply, ← hbc, hΦtq]
    exact tq_mem_Qv _ _
  · obtain ⟨b', c', rfl⟩ := mem_Qv_e0.mp hq
    have hmem : tq (e.symm b') (e.symm c') ∈ St.Ubar := by
      rw [St.Ubar_eq_Qv]
      exact tq_mem_Qv _ _
    obtain ⟨⟨u, hu⟩, huq⟩ := hmem
    refine ⟨⟨u, hUL hu⟩, hu, ?_⟩
    have hb : St.betaU ⟨u, hu⟩ = D'.θ ⟨u, hUL hu⟩ := by
      rw [L3Setting.betaU_apply]
      exact St.Phi_of_L ⟨u, hUL hu⟩
    rw [MonoidHom.comp_apply, ← hb, huq, hΦtq]
    simp

end Ctx

end L14333

end CFSG.Quasithin.H13
