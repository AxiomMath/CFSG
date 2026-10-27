module

public import CFSG.Quasithin.Background.Harris.R1.QbetaMain

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem perm_eq_one_of_commute [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hΩ : 4 ≤ Fintype.card Ω) (σ : Equiv.Perm Ω)
    (h : ∀ k : ↥K1, σ * C.D.act k = C.D.act k * σ) : σ = 1 := by
  ext ω
  by_contra hne
  have hne' : σ ω ≠ ω := fun h' => hne (by simpa using h')
  obtain ⟨j, k', hj, -, hij, -, -⟩ := exists_two_ne hΩ ω (σ ω)
  obtain ⟨k, hk1, hk2⟩ := C.twoTrans (a := ω) (b := σ ω) (c := ω) (d := j) hne'.symm hj.symm
  have h1 := congrArg (fun p : Equiv.Perm Ω => p ω) (h k)
  simp only [Equiv.Perm.mul_apply] at h1
  rw [hk1, hk2] at h1
  exact hij h1

theorem pCore_le_kerM [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hΩ : 4 ≤ Fintype.card Ω) (hodd : Odd (Fintype.card Ω)) :
    pCoreOf 2 (K1 ⊔ S) ≤ C.kerM := by
  intro y hy
  have hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) := sup_le Subgroup.le_normalizer C.hSK
  have hyH : y ∈ K1 ⊔ S := pCoreOf_le 2 _ hy
  have hcomm : ∀ k : ↥K1, permHom C ⟨y, hyH⟩ * C.D.act k = C.D.act k * permHom C ⟨y, hyH⟩ := by
    intro k
    have hkH : (k : G) ∈ K1 ⊔ S := Subgroup.mem_sup_left k.2
    have hcK : y * k * y⁻¹ * (k : G)⁻¹ ∈ K1 :=
      K1.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN hyH) k).mp k.2) (K1.inv_mem k.2)
    have hcP : y * k * y⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 (K1 ⊔ S) := by
      have h1 : (k : G) * y⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 (K1 ⊔ S) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (K1 ⊔ S) hkH) y⁻¹).mp
          ((pCoreOf 2 (K1 ⊔ S)).inv_mem hy)
      have := (pCoreOf 2 (K1 ⊔ S)).mul_mem hy h1
      simpa [mul_assoc] using this
    have hNK : K1 ⊓ pCoreOf 2 (K1 ⊔ S) ≤ pCoreOf 2 K1 := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
      · exact F7.le_normalizer_inf Subgroup.le_normalizer
          (le_sup_left.trans (le_normalizer_pCoreOf 2 (K1 ⊔ S)))
      · exact (pCoreOf_isPGroup 2 (K1 ⊔ S)).to_le inf_le_right
    have hcO : y * k * y⁻¹ * (k : G)⁻¹ ∈ C.kerM := pCoreK1_le_kerM C hodd (hNK ⟨hcK, hcP⟩)
    have hcH : y * k * y⁻¹ * (k : G)⁻¹ ∈ K1 ⊔ S := Subgroup.mem_sup_left hcK
    have h1 := (permHom_eq_one_iff C ⟨_, hcH⟩).2 hcO
    have e : (⟨y * k * y⁻¹ * (k : G)⁻¹, hcH⟩ : ↥(K1 ⊔ S)) =
        ⟨y, hyH⟩ * ⟨(k : G), hkH⟩ * ⟨y, hyH⟩⁻¹ * ⟨(k : G), hkH⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, permHom_K1] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have h1 : permHom C ⟨y, hyH⟩ = 1 := perm_eq_one_of_commute C hΩ _ hcomm
  exact (permHom_eq_one_iff C ⟨y, hyH⟩).1 h1

theorem kerM_le_vBeta_of_abelian (C : FamCtx K1 L2 S Zs (Fin 5)) (hpt : C.D.pt = 4)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (hsurj : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → τ 4 = 4 → τ * τ = 1 →
      ∃ k : ↥K1, (k : G) ∈ S ∧ ∀ i, C.D.act k i = τ i)
    (hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32)
    (hDab : ∀ a ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G),
      ∀ b ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G), a * b = b * a) :
    C.kerM ≤ vBeta K1 L2 S Zs := by
  classical
  have hodd : Odd (Fintype.card (Fin 5)) := ⟨2, by simp⟩
  have hij : (0 : Fin 5) ≠ 1 := by decide
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  intro m hm
  obtain ⟨w, hw, hwc⟩ := exists_inner_of_kerM C hodd hij (List.finRange 5)
    (List.nodup_finRange 5) List.mem_finRange hcen hm
  have hdM : w⁻¹ * m ∈ C.kerM := C.kerM.mul_mem (C.kerM.inv_mem (C.vBeta_le_kerM hw)) hm
  have hdD : w⁻¹ * m ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) :=
    ⟨⟨hdM, hkS hdM⟩, hwc⟩
  have hdZ : w⁻¹ * m ∈ Zs :=
    D_mem_Z_aux C hpt hcen hZS hker hsurj hW32 hdD (fun _ e he => hDab _ hdD e he)
  have e : m = w * (w⁻¹ * m) := by group
  rw [e]
  exact (vBeta K1 L2 S Zs).mul_mem hw (F112J2.Zs_le_vBeta K1 L2 S Zs hdZ)

theorem n2_of_dAbel_inst (hRO : RankOneListedFacts.{0}) (hset : R1SettingLegacyBare K1 L2 S Zs)
    (hZS : ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥)
    (hD : ∀ a ∈ pCoreOf 2 (K1 ⊔ S) ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G),
      ∀ b ∈ pCoreOf 2 (K1 ⊔ S) ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G), a * b = b * a) :
    pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1 := by
  classical
  have hcen := f112R1aCenter_of_rankOne hRO G K1 L2 S Zs hset hL24 hna
  let C5 := F112J2.fiveCtxOfSetting hRO hset hL24 hna
  let C : FamCtx K1 L2 S Zs (Fin 5) := famCtxOfFive C5
  have hZS' : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs :=
    fun u hu hc h2 => hZS u hu h2 hc
  have hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32 := (C5.isQ8D8_vBeta hcen).1
  have hQ : pCoreOf 2 K1 = vBeta K1 L2 S Zs := qbeta_of_ZS_inst hRO hset hZS hL24 hna
  have hc5 : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
  have hodd : Odd (Fintype.card (Fin 5)) := ⟨2, by omega⟩
  have hker := hker_of_five hL24 C5
  have hOk : pCoreOf 2 (K1 ⊔ S) ≤ C.kerM := pCore_le_kerM C (by omega) hodd
  have hkO : C.kerM ≤ pCoreOf 2 (K1 ⊔ S) := kerM_le_pCore C hker
  have hKW : C.kerM ≤ vBeta K1 L2 S Zs :=
    kerM_le_vBeta_of_abelian C rfl hcen hZS' hker (hsurj_of_five C5) hW32 (fun a ha b hb =>
      hD a ⟨hkO ha.1.1, ha.2⟩ b ⟨hkO hb.1.1, hb.2⟩)
  have hWO : vBeta K1 L2 S Zs ≤ pCoreOf 2 (K1 ⊔ S) :=
    F112W.conjClosure_le_pCoreOf_G₂ C.h.V_le
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · rw [hQ]; exact hKW (hOk hy)
  · rw [hQ] at hy; exact hWO hy

end CFSG.Quasithin.Background.Harris.R1
