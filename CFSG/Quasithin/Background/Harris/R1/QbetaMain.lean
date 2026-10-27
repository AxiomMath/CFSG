module

public import CFSG.Quasithin.Background.Harris.R1.QbetaOut
public import CFSG.Quasithin.Background.Harris.R1.QbetaInst
public import CFSG.Quasithin.Background.Harris.R1.QbetaK1
public import CFSG.Quasithin.Background.Harris.R1.QbetaFin
public import CFSG.Quasithin.Background.Harris.R1.QbetaGen
public import CFSG.Quasithin.Background.Harris.R1.QbetaParFam
public import CFSG.Quasithin.Background.Harris.R1.QbetaS1
public import CFSG.Quasithin.Background.Harris.R1.QbetaKerS
public import CFSG.Quasithin.Background.Harris.R1.QbetaCore
public import CFSG.Quasithin.Recognition.SzR1CenterFull
public import CFSG.Quasithin.Background.Harris.R1.QbetaPar

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7
  CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem D_mem_Z_aux (C : FamCtx K1 L2 S Zs (Fin 5)) (hpt : C.D.pt = 4)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (hsurj : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → τ 4 = 4 → τ * τ = 1 →
      ∃ k : ↥K1, (k : G) ∈ S ∧ ∀ i, C.D.act k i = τ i)
    (hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32)
    {x : G} (hxD : x ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G))
    (hxd : (∀ k ∈ K1, ∀ d ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G),
        k * d = d * k) →
      ∀ d ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G), x * d = d * x) :
    x ∈ Zs := by
  classical
  have hc5 : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
  have hodd : Odd (Fintype.card (Fin 5)) := ⟨2, by omega⟩
  have hij : (0 : Fin 5) ≠ 1 := by decide
  obtain ⟨g, y, z, h, h4⟩ := qd_of_famCtx C hc5 hij (List.finRange 5) (List.nodup_finRange 5)
    List.mem_finRange hcen hZS
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  have hMeq : C.kerM ⊓ S = C.kerM := inf_eq_left.mpr hkS
  have hxC : x ∈ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) := hxD.2
  have hVA' : Zs ⊔ conjSub g Zs ≤ conjSub g (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) := by
    refine le_inf ?_ h.V_le_Q
    calc Zs ⊔ conjSub g Zs = conjSub g (Zs ⊔ conjSub g Zs) :=
          (F7.conjSub_eq_of_mem_normalizer (h.hVN h.hg)).symm
      _ ≤ conjSub g (vBeta K1 L2 S Zs) := conjSub_mono g h.V_le_W
  obtain ⟨a1, ha1, a2, ha2, hgen⟩ := exists_two_gen hVA' h4 (h.card_A' hW32)
  have hK1 : ⁅K1, K1⁆ = K1 := perfect_of_mem_cComp C.h.cComp_mem
  have hK1D : K1 ≤ Subgroup.normalizer
      ((C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) : Subgroup G) : Set G) := by
    rw [hMeq]
    refine F7.le_normalizer_inf (le_sup_left.trans C.sup_le_normalizer_kerM) (fun k hk => ?_)
    have hWc : conjSub k (vBeta K1 L2 S Zs) = vBeta K1 L2 S Zs :=
      F7.conjSub_eq_of_mem_normalizer
        (le_normalizer_conjClosure (conjClosure Zs L2) (K1 ⊔ S) (Subgroup.mem_sup_left hk))
    apply Vert.mem_normalizer_of_conjSub_eq
    rw [← conjSub_centralizer, hWc]
  have hK1Z : ∀ k ∈ K1, ∀ s ∈ Zs, k * s = s * k := fun k hk s hs =>
    (Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) s hs).symm
  have hKcomm : ∀ k ∈ K1, ∀ d ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G),
      k * d = d * k := fun k hk d hd =>
    h.K1_comm_D hK1 hK1D hK1Z ha1 ha2 hgen C.h.card_Z hk hd
  have hAc : ∀ a' ∈ conjSub g (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S), x * a' = a' * x := by
    intro a' ha'
    have ha'S : a' ∈ S := h.vh.qs ha'.2
    have hAV : ∀ x' ∈ vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S),
        x' * a' * x'⁻¹ * a'⁻¹ ∈ conjClosure Zs L2 := by
      intro x' hx'
      obtain ⟨hW', hQ', hsq⟩ := h.comm_A_A' hx' ha'
      have hzf : C.zf C.D.pt ∈ conjClosure Zs L2 := by
        have := C.zf_mem C.D.pt
        rwa [C.Vf_pt] at this
      have hc : ⁅x', a'⁆ * C.zf C.D.pt = C.zf C.D.pt * ⁅x', a'⁆ :=
        ((C.mem_pCore_iff.mp hQ').2 _ hzf).symm
      exact invol_mem_V C hc5 hij (List.finRange 5) (List.nodup_finRange 5) List.mem_finRange
        hcen hW' hsq hc
    obtain ⟨k, hkK, hkS', hkm⟩ := parity C hpt hsurj ha'S hAV
    obtain ⟨w, hw, hwc⟩ := exists_inner_of_kerM C hodd hij (List.finRange 5)
      (List.nodup_finRange 5) List.mem_finRange hcen hkm
    have hdM : w⁻¹ * (k⁻¹ * a') ∈ C.kerM :=
      C.kerM.mul_mem (C.kerM.inv_mem (C.vBeta_le_kerM hw)) hkm
    have hdD : w⁻¹ * (k⁻¹ * a') ∈ C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) :=
      ⟨⟨hdM, hkS hdM⟩, hwc⟩
    have hxk : Commute x k := (hKcomm k hkK x hxD).symm
    have hxw : Commute x w := (Subgroup.mem_centralizer_iff.mp hxC w hw).symm
    have hxd' : Commute x (w⁻¹ * (k⁻¹ * a')) := hxd hKcomm _ hdD
    have hc := hxk.mul_right (hxw.mul_right hxd')
    have e : k * (w * (w⁻¹ * (k⁻¹ * a'))) = a' := by group
    rw [e] at hc
    exact hc
  exact h.mem_Z_of_comm hxD hAc

theorem centralizer_le_Z_aux (C : FamCtx K1 L2 S Zs (Fin 5)) (hpt : C.D.pt = 4)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (hsurj : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → τ 4 = 4 → τ * τ = 1 →
      ∃ k : ↥K1, (k : G) ∈ S ∧ ∀ i, C.D.act k i = τ i)
    (hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32)
    {x : G} (hx : x ∈ pCoreOf 2 K1) (hxC : x ∈ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G)) :
    x ∈ Zs := by
  classical
  have hodd : Odd (Fintype.card (Fin 5)) := ⟨2, by simp⟩
  have hxker : x ∈ C.kerM := pCoreK1_le_kerM C hodd hx
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  have hxK : x ∈ K1 := pCoreOf_le 2 K1 hx
  exact D_mem_Z_aux C hpt hcen hZS hker hsurj hW32 ⟨⟨hxker, hkS hxker⟩, hxC⟩
    (fun hK d hd => hK x hxK d hd)

theorem hker_of_five (hL24 : IsL2Quot 2 (OTwoQuot K1)) (C5 : F112J2.FiveCtx K1 L2 S Zs) :
    ∀ k : ↥K1, (famCtxOfFive C5).D.act k = 1 → (k : G) ∈ pCoreOf 2 K1 := by
  intro k hk
  have h1 : C5.D.θ k = 1 := Subtype.ext hk
  have h2 : k ∈ C5.D.θ.ker := h1
  rw [ker_theta_eq hL24 C5.D.θ C5.D.surj] at h2
  exact (SplitAux.mem_pCoreOf_iff_mem_pCore k).mpr h2

theorem hsurj_of_five (C5 : F112J2.FiveCtx K1 L2 S Zs) :
    ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → τ 4 = 4 → τ * τ = 1 →
      ∃ k : ↥K1, (k : G) ∈ S ∧ ∀ i, (famCtxOfFive C5).D.act k i = τ i := by
  intro τ hs h4 hsq
  let σ : A5 := ⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
  have hσ4 : σ ∈ A4s := h4
  have hσ2 : σ * σ = 1 := Subtype.ext hsq
  have hσpow : σ ^ 4 = 1 := by
    have h2 : σ ^ 2 = 1 := by rw [pow_two, hσ2]
    calc σ ^ 4 = σ ^ 2 * σ ^ 2 := by rw [← pow_add]
      _ = 1 := by rw [h2, one_mul]
  obtain ⟨k, hkS, hkθ⟩ := exists_S1_act C5 (mem_K4_of_pow_four σ hσ4 hσpow)
  refine ⟨k, hkS, fun i => ?_⟩
  show ((C5.D.θ k : A5) : Equiv.Perm (Fin 5)) i = τ i
  rw [hkθ]

theorem qbeta_of_ZS_inst (hRO : RankOneListedFacts.{0}) (hset : R1SettingLegacyBare K1 L2 S Zs)
    (hZS : ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    pCoreOf 2 K1 = vBeta K1 L2 S Zs := by
  classical
  have hcen := f112R1aCenter_of_rankOne hRO G K1 L2 S Zs hset hL24 hna
  let C5 := F112J2.fiveCtxOfSetting hRO hset hL24 hna
  let C : FamCtx K1 L2 S Zs (Fin 5) := famCtxOfFive C5
  have hWK : vBeta K1 L2 S Zs ≤ K1 := vBeta_le_K1 C5 hcen
  have hZS' : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs :=
    fun u hu hc h2 => hZS u hu h2 hc
  have hc5 : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
  have hodd : Odd (Fintype.card (Fin 5)) := ⟨2, by omega⟩
  have hij : (0 : Fin 5) ≠ 1 := by decide
  have hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32 := (C5.isQ8D8_vBeta hcen).1
  exact pCoreK1_eq_vBeta C hodd hij (List.finRange 5) (List.nodup_finRange 5) List.mem_finRange
    hcen hWK (fun x hx hxC => centralizer_le_Z_aux C rfl hcen hZS' (hker_of_five hL24 C5)
      (hsurj_of_five C5) hW32 hx hxC)

end CFSG.Quasithin.Background.Harris.R1
