module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTableP

import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3TwE6Rank
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispEA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUC
public import Certificates.Certificate1952

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}


private noncomputable def qtwoDB24_E (βL : Additive ↥Bs ≃+ DVec m) (c : Fin m) :
    Subgroup ↥Bs :=
  AddSubgroup.toSubgroup'
    ((LinearMap.ker (LinearMap.proj (R := ZMod 3) (φ := fun _ : Fin m => ZMod 3) c)
      ).toAddSubgroup.comap
      βL.toAddMonoidHom)

private theorem qtwoDB24_mem_E (βL : Additive ↥Bs ≃+ DVec m) (c : Fin m) (s : ↥Bs) :
    s ∈ qtwoDB24_E βL c ↔ βL (Additive.ofMul s) c = 0 := by
  rw [qtwoDB24_E, AddSubgroup.mem_toSubgroup', AddSubgroup.mem_comap,
    Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  rfl

private noncomputable def qtwoDB24_hyperplaneEquiv (m : ℕ) (c : Fin m) :
    {v : DVec m // v c = 0} ≃ ({x : Fin m // x ≠ c} → ZMod 3) where
  toFun v := fun i => v.1 i.1
  invFun u := ⟨fun j => if h : j = c then 0 else u ⟨j, h⟩, by simp⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    simp only [Subtype.coe_mk]
    by_cases hj : j = c
    · rw [dif_pos hj, hj]
      exact v.2.symm
    · rw [dif_neg hj]
  right_inv u := by
    funext i
    simp only [Subtype.coe_mk]
    rw [dif_neg i.2]

private theorem qtwoDB24_card_ne_subtype (m : ℕ) (c : Fin m) :
    Nat.card {x : Fin m // x ≠ c} = m - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : Fin m => x = c),
    Fintype.card_subtype_eq c, Fintype.card_fin]

private theorem qtwoDB24_card_hyperplane (m : ℕ) (c : Fin m) :
    Nat.card {v : DVec m // v c = 0} = 3 ^ (m - 1) := by
  rw [Nat.card_congr (qtwoDB24_hyperplaneEquiv m c), Nat.card_fun, Nat.card_zmod,
    qtwoDB24_card_ne_subtype m c]

private noncomputable def qtwoDB24_E_equiv (βL : Additive ↥Bs ≃+ DVec m) (c : Fin m) :
    (qtwoDB24_E βL c) ≃ {v : DVec m // v c = 0} where
  toFun s := ⟨βL (Additive.ofMul (s : ↥Bs)), (qtwoDB24_mem_E βL c _).mp s.2⟩
  invFun v := ⟨Additive.toMul (βL.symm v.1), (qtwoDB24_mem_E βL c _).mpr (by
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
    exact v.2)⟩
  left_inv s := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

private theorem qtwoDB24_card_E (βL : Additive ↥Bs ≃+ DVec m) (c : Fin m) :
    Nat.card (qtwoDB24_E βL c) = 3 ^ (m - 1) := by
  rw [Nat.card_congr (qtwoDB24_E_equiv βL c)]
  exact qtwoDB24_card_hyperplane m c

theorem qtwoDB24_image_of (hBs3 : IsElemAbelian 3 Bs) {βL : Additive ↥Bs ≃+ DVec m} {c : Fin m}
    {N : Subgroup G} (hE_mem : ∀ s : ↥Bs, βL (Additive.ofMul s) c = 0 → (s : G) ∈ N)
    (hcent : ∀ s : ↥Bs, βL (Additive.ofMul s) c = 0 →
      (s : G) ∈ Subgroup.centralizer (N : Set G) → s = 1) :
    ∃ A : Subgroup (↥N ⧸ Subgroup.center ↥N),
      IsElemAbelian 3 A ∧ Nat.card A = 3 ^ (m - 1) := by
  let E : Subgroup ↥Bs := qtwoDB24_E βL c
  have hEea : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact hBs3.1.is_comm.comm (a : ↥Bs) (b : ↥Bs)
    · exact hBs3.2 (x : ↥Bs) x.2
  let hEN : E →* ↥N :=
    { toFun := fun s => ⟨(s : ↥Bs), hE_mem s ((qtwoDB24_mem_E βL c s).mp s.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  let f : E →* ↥N ⧸ Subgroup.center ↥N := (QuotientGroup.mk' (Subgroup.center ↥N)).comp hEN
  have hfker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hsZ : (hEN s : ↥N) ∈ Subgroup.center ↥N :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center ↥N) (hEN s)).mp hs
    have hsC : ((s : ↥Bs) : G) ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := Subgroup.mem_center_iff.mp hsZ ⟨y, hy⟩
      exact congrArg Subtype.val h
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (hcent (s : ↥Bs) ((qtwoDB24_mem_E βL c (s : ↥Bs)).mp s.2) hsC))
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hfker
  have hf_equiv : E ≃* f.range :=
    MulEquiv.ofBijective f.rangeRestrict
      ⟨fun a b h => hfinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hrange_ea : IsElemAbelian 3 f.range :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv hf_equiv hEea.isElementaryAbelian)
  exact ⟨f.range, hrange_ea,
    by rw [← Nat.card_congr hf_equiv.toEquiv, qtwoDB24_card_E βL c]⟩


private theorem qtwoDB24_image_E (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {N : Subgroup G} (hJ₁ : qtwoDelJ ψ c ≤ N)
    (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    ∃ A : Subgroup (↥N ⧸ Subgroup.center ↥N),
      IsElemAbelian 3 A ∧ Nat.card A = 3 ^ (m - 1) := by
  have hX_le : qtwoDelJ ψ c ⊔ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N :=
    sup_le hJ₁ hJ₂
  refine qtwoDB24_image_of (hbase.p_eq ▸ hbase.hyp.bstar.2.1) (fun s hβ => ?_)
    (fun s hβ hsC => ggQTwoDUnit_cent_E (by omega) hbase hcoords hdel s hβ
      (Subgroup.centralizer_le hJ₁ hsC) (Subgroup.centralizer_le hJ₂ hsC))
  have h0 := ggQTwoDUnit_torus (m := m) (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb
    hdel.sign hdel.norm hdel.conj s hβ
  exact hX_le (by simpa only [qtwoDelJ] using h0)

private theorem qtwoDB24_markedModel_twE6 {R : Type} [Group R]
    (h : GGHasLabel (⟨.twE6, 0, 1⟩ : LargeEvenLabel) R) :
    MarkedModel (⟨.twE6, 0, 1⟩ : LargeEvenLabel) R := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  refine LieModel.of_mulEquiv e.symm ?_
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩,
    twistedChevalleyModel_largeEven .E6 hK⟩)

private theorem qtwoDB24_equiv_E8
    {R : Type} [Group R]
    (h : GGHasLabel (⟨.E8, 0, 1⟩ : LargeEvenLabel) R) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (R ≃* adjointGroup .E8 K) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨ψ⟩ := centerQuot_chevGroup_equiv K .E8
  have hcenK : Subgroup.center (adjointGroup .E8 K) = ⊥ :=
    center_adjointGroup_eq_bot
  let q₀ : CFSG.Blueprint.AdjointQuotient .E8 K ≃* ↥(adjointGroup .E8 K) :=
    (QuotientGroup.quotientMulEquivOfEq hcenK).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, by simpa using hK, ⟨(e.trans ψ).trans q₀⟩⟩

theorem qtwoDB24_e7_exceptional
    (hm8 : m = 8) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {N : Subgroup G} (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hlab8 : lab = ⟨.E7, 0, 1⟩) : False := by
  subst hm8
  rw [hlab8] at hlab
  have hBsN : Bs ≤ Subgroup.normalizer (N : Set G) :=
    ggQTwoDUnit_normalizer_N (by omega) hbase b'.2 hN hJ₁
  obtain ⟨hker, hAcard, hAea, hAinn, -⟩ :=
    qtwoDB36_gamma (by omega : 5 ≤ 8) hbase hcoords hdel hN hJ₁ hJ₂ hBsN
  have hAcard7 : Nat.card (ggGamma N hBsN).range = 3 ^ 7 := by
    simpa using hAcard
  obtain ⟨hdiv, z, hzmem, hzinv⟩ :=
    qtwoDB40_e7_aut (qtwoDB36_perfect hN) hlab hAea hAcard7 hAinn
  let z' : ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range
      (ggGamma N hBsN).range) := ⟨z, hzmem⟩
  obtain ⟨Θ, hΘinj, hΘact⟩ :=
    qtwoDB36_weyl_embed (by omega : 5 ≤ 8) hbase hcoords hdel hN hJ₁ hJ₂ hBsN
  have hHcard : Nat.card Θ.range = 322560 := by
    have h1 : Nat.card Θ.range = Nat.card (dEvenStab 8 (Pi.single c 1)) := by
      rw [show Θ.range = (⊤ : Subgroup ↥(dEvenStab 8 (Pi.single c 1))).map Θ from
        MonoidHom.range_eq_map Θ]
      rw [Subgroup.card_map_of_injective (f := Θ) hΘinj, Subgroup.card_top]
    rw [h1, qtwoDB36_card_dEvenStab (m := 8) (by omega) c]
    norm_num
  have hzcent : ∀ y : ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range
      (ggGamma N hBsN).range), z' * y = y * z' := by
    intro y
    apply Subtype.ext
    refine MulEquiv.ext fun m0 => ?_
    change z ((y : MulAut ↥(ggGamma N hBsN).range) m0) =
      (y : MulAut ↥(ggGamma N hBsN).range) (z m0)
    rw [hzinv ((y : MulAut ↥(ggGamma N hBsN).range) m0), hzinv m0, map_inv]
  have hz2 : z' ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    refine MulEquiv.ext fun m0 => ?_
    change z (z m0) = m0
    rw [hzinv (z m0), hzinv m0, inv_inv]
  by_cases hzH : z' ∈ Θ.range
  · obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hzH
    have hzΘ : (Θ w : MulAut ↥(ggGamma N hBsN).range) =
        (z' : MulAut ↥(ggGamma N hBsN).range) := congrArg Subtype.val hw
    have hneg : ∀ (v : DVec 8) (k : Fin 8), k ≠ c →
        (w : DVec 8 ≃ₗ[ZMod 3] DVec 8) v k = -v k := by
      intro v k hk
      let s : ↥Bs := Additive.toMul (βL.symm v)
      have hs : βL (Additive.ofMul s) = v := by
        simp [s]
      let t : ↥Bs := Additive.toMul (βL.symm ((w : DVec 8 ≃ₗ[ZMod 3] DVec 8)
        (βL (Additive.ofMul s))))
      have ht : βL (Additive.ofMul t) =
          (w : DVec 8 ≃ₗ[ZMod 3] DVec 8) (βL (Additive.ofMul s)) := by
        simp [t]
      have hker_t : βL (Additive.ofMul (t * s)) k = 0 := by
        have h1 : (ggGamma N hBsN).rangeRestrict (t * s) = 1 := by
          rw [map_mul]
          have h2 : (ggGamma N hBsN).rangeRestrict t =
              ((ggGamma N hBsN).rangeRestrict s)⁻¹ := by
            rw [← hΘact w s, hzΘ]
            exact hzinv _
          rw [h2, inv_mul_cancel]
        have h3 : ggGamma N hBsN (t * s) = 1 := Subtype.ext_iff.mp h1
        exact ((hker (t * s)).mp h3) k hk
      have hh := hker_t
      rw [ofMul_mul, map_add, Pi.add_apply, ht, hs] at hh
      exact eq_neg_of_add_eq_zero_left hh
    exact qtwoDB40_not_neg (m := 8) (by norm_num) w.2 hneg
  · exact qtwoDB40_contra hdiv hHcard hzcent hz2 hzH

theorem ggQTwoDUnit_not_exceptional
    (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hE : (m = 7 ∧ lab = ⟨.twE6, 0, 1⟩) ∨ (m = 8 ∧ lab = ⟨.E7, 0, 1⟩) ∨
      (m = 10 ∧ lab = ⟨.E8, 0, 1⟩)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hAea, hAcard⟩ := qtwoDB24_image_E hm hbase hcoords hdel hJ₁ hJ₂
  rcases hE with ⟨hm7, hlab7⟩ | ⟨hm8, hlab8⟩ | ⟨hm10, hlab10⟩
  · subst hm7
    subst hlab7
    have hM : LieModel (↥N ⧸ Subgroup.center ↥N) .twistedE6 0 2 1 :=
      qtwoDB24_markedModel_twE6 hlab
    have hle := CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.card_le_of_lieModel_twistedE6_two
      hM A hAea
    rw [hAcard] at hle
    norm_num at hle
  · exact qtwoDB24_e7_exceptional hm8 hbase hcoords hdel hN hJ₁ hJ₂ hlab hlab8
  · subst hm10
    subst hlab10
    obtain ⟨K, _, _, hK2, ⟨e⟩⟩ := qtwoDB24_equiv_E8 hlab
    have hle := CFSG.StandardType.TableBExcTwo.card_le_adjoint_E8 hK2
      (E := A.map e.toMonoidHom) (hAea.map e.toMonoidHom)
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hAcard] at hle
    norm_num at hle

end CFSG.StandardType.QTwo

end
