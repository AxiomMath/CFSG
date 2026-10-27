module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EightTameSmith
public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithCore
public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithAsub
public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithSsub
public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithSection

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_wild_pre (h310chi : Stroth310ChiStatement) (h71 : Stroth71Statement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hSec : Sec7WVSecCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t)
    (h4 : OmegaPlusNat hc t 4) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hgM : g ∈ M)
    (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q)
    (hwild : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) :
    g * t * g⁻¹ ∈ H0 M Z ∧ (g * t * g⁻¹) ^ 2 ∈ Q ∧ ⁅g * t * g⁻¹, t⁆ ∈ Q ∧
      (∀ x ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, x⁆ ∈ Z) ∧
      Ut Q Z (g * t * g⁻¹) = conjSubgroup g (Vt M (LB M Q B) B Z t) ∧
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z ∧
      conjSubgroup (g * t * g⁻¹) (LB M Q B) = LB M Q B ∧
      (∀ y ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), y ∈ Wt Q (Vt M (LB M Q B) B Z t)) := by
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hVU : Ut Q Z t = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 hs.toSec5.notQ
  have hUt : ∀ h ∈ M, Ut Q Z (h * t * h⁻¹) = conjSubgroup h (Vt M (LB M Q B) B Z t) :=
    fun h hh => by
      rw [Ut_conj_of_normalizes (hc.conj_Q_eq hh) (hc.conj_Z_eq hh) t, hVU]
  have huM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hs1 : g * t * g⁻¹ * (g * t * g⁻¹)⁻¹ ∈ Q := by
    rw [mul_inv_cancel]
    exact Q.one_mem
  have huCent : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using htZ0
  have hut : ⁅g * t * g⁻¹, t⁆ ∈ Q := by
    have := Q.inv_mem (hΓ t htZ0 _ huCent)
    rwa [commutatorElement_inv] at this
  have huV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z :=
    sec7_pair_vanish h71 hc hs hno hgM hs1 hut
  obtain ⟨hu2, huH⟩ := sq_mem_Q_and_H0_of_mem_conj_centre hZc hc hs hZ0 hgM huCent
  have hQx : ∀ w ∈ Q, ⁅g * t * g⁻¹, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro w hw
    have h1 : ⁅w, g * t * g⁻¹⁆ ∈ ⁅Q, Subgroup.zpowers (g * t * g⁻¹)⁆ :=
      Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers _)
    have h2 : ⁅g * t * g⁻¹, w⁆ ∈ Ut Q Z (g * t * g⁻¹) := by
      rw [← commutatorElement_inv]
      exact (Ut Q Z (g * t * g⁻¹)).inv_mem (Subgroup.mem_sup_left h1)
    rwa [hUt g hgM] at h2
  obtain ⟨hVinf, -, -, -, -⟩ := sec7_wild_join h52a hA h310chi hSec hc hs h4 hgM huM hut huV hQx
    hwild
  have hconjLB : conjSubgroup (g * t * g⁻¹) (LB M Q B) = LB M Q B := by
    refine hc.conj_LB_eq_of_le_sup_Z huM ?_
    intro x hx
    have hx' := mem_conjSubgroup.mp hx
    have e : x = ⁅g * t * g⁻¹, (g * t * g⁻¹)⁻¹ * x * (g * t * g⁻¹)⁆ *
        ((g * t * g⁻¹)⁻¹ * x * (g * t * g⁻¹)) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (huV _ (hc.B_le_Vt ht hx')))
      (Subgroup.mem_sup_left hx')
  have hUW : ∀ y ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), y ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun y hy => by
      have h1 : g⁻¹ * y * g ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hy
      have h2 := sec7_pair_mem_W h71 h310chi hc hs hno hgM hs1 hut _ h1
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [e] at h2
  exact ⟨huH, hu2, hut, huV, hUt g hgM, hVinf, hconjLB, hUW⟩

end

section


theorem step76EightSmithCore_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h71 : Stroth71Statement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hSec : Sec7WVSecCardStatement) (hVan : Step71VanishStatement)
    (hSplit : Sec7WVSplitStatement) (hSmith : SmithOmegaPlusEightStatement) :
    Step76EightSmithCoreStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 f hfL hfc g hgM hΓ hwild a ha
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨huH, hu2, hut, huV, hUtv, hVinf, hconjLB, hUW⟩ :=
    sec7_wild_pre h310chi h71 hZc hZV h52a hA hSec hc hs hno h4 hZ0 hgM hΓ hwild
  have huM : g * t * g⁻¹ ∈ M := huH.1
  have hQx : ∀ w ∈ Q, ⁅g * t * g⁻¹, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro w hw
    have h1 : ⁅w, g * t * g⁻¹⁆ ∈ ⁅Q, Subgroup.zpowers (g * t * g⁻¹)⁆ :=
      Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers _)
    have h2 : ⁅g * t * g⁻¹, w⁆ ∈ Ut Q Z (g * t * g⁻¹) := by
      rw [← commutatorElement_inv]
      exact (Ut Q Z (g * t * g⁻¹)).inv_mem (Subgroup.mem_sup_left h1)
    rwa [hUtv] at h2
  obtain ⟨K, fK, finK, γ, M₀, ρ, b₀, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  haveI hchar : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hS.card.trans he)
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  obtain ⟨-, hUcard⟩ := sec7_Hset_card8 h34 h310chi hc hs h4 M₀ ρ b₀ hS ψ hψ hrange
  have hUiso : ∀ u ∈ hc.VtSub hS.model t, ∀ u' ∈ hc.VtSub hS.model t, M₀.B u u' = 0 := by
    intro u hu u' hu'
    obtain ⟨v₁, hvV, hvQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
    obtain ⟨v₂, hvV', hvQ', rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu')
    have hvW : v₁ ∈ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs hvV
    exact (M₀.comm_iff_B hS.model.reg hvQ hvQ').mp
      (Subgroup.mem_centralizer_iff.mp hvW.2 v₂ hvV').symm
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hVab : ∀ x ∈ Vt M (LB M Q B) B Z t, ∀ y ∈ Vt M (LB M Q B) B Z t, x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp (hVW hy).2 x hx
  obtain ⟨Tv, hTvop, -, hTviso, hTv_range, hTv_ker, -⟩ := sec7_op_data hc M₀ ρ b₀ hS huH hu2
  let ψv : M₀.E →ₗ[K] M₀.E := sec7Op hc hS huH - 1
  have hψv_apply : ∀ e, ψv e = sec7Op hc hS huH e - e := fun e => rfl
  have hψTv : ∀ e, ψv e = Tv e - e := fun e =>
    congrArg (fun x => x - e) (hTvop e).symm
  have hψv_eq : ψv = (Tv : M₀.E →ₗ[K] M₀.E) - 1 := LinearMap.ext fun e => hψTv e
  have hrs : ∀ e, e ∈ LinearMap.range ψv ↔
      e ∈ M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t)) :=
    fun e => by rw [hψv_eq]; exact (hTv_range e).trans (by rw [hUtv])
  have hker_v : LinearMap.ker ψv = M₀.B.orthogonal (LinearMap.range ψv) := by
    rw [hψv_eq]
    exact hTv_ker
  have hvU : ∀ e ∈ hc.VtSub hS.model t, sec7Op hc hS huH e = e := by
    intro e he
    obtain ⟨v₀, hv₀V, hv₀Q, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp he)
    have h1 := sec7Op_sub_comm hc hS huH hv₀Q
    rw [(M₀.π_ker _ (sec7_comm_mem_Q hc huM hv₀Q)).mpr (huV v₀ hv₀V)] at h1
    exact sub_eq_zero.mp h1
  have hψU : ∀ u ∈ hc.VtSub hS.model t, ψv u = 0 := fun u hu => by
    rw [hψv_apply, hvU u hu, sub_self]
  have hψW : ∀ e, ψv e ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [hψv_apply, sec7Op_sub_comm hc hS huH hxQ]
    exact (sec7_mem_Wt_iff_perp hc hS ψ hW (sec7_comm_mem_Q hc huM hxQ)).mp
      (hUW _ (hQx x hxQ))
  have hrangeiso : ∀ x ∈ LinearMap.range ψv, ∀ y ∈ LinearMap.range ψv, M₀.B x y = 0 := by
    intro x hx y hy
    obtain ⟨a₁, ha₁V, ha₁Q, rfl⟩ := M₀.mem_img.mp ((hrs x).mp hx)
    obtain ⟨a₂, ha₂V, ha₂Q, rfl⟩ := M₀.mem_img.mp ((hrs y).mp hy)
    refine (M₀.comm_iff_B hS.model.reg ha₁Q ha₂Q).mp ?_
    have h1 := mem_conjSubgroup.mp ha₁V
    have h2 := mem_conjSubgroup.mp ha₂V
    have h3 := hVab _ h1 _ h2
    calc a₁ * a₂ = g * ((g⁻¹ * a₁ * g) * (g⁻¹ * a₂ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a₂ * g) * (g⁻¹ * a₁ * g)) * g⁻¹ := by rw [h3]
      _ = a₂ * a₁ := by group
  have hψadj : ∀ e e', M₀.B (ψv e) e' = M₀.B e (ψv e') := by
    intro e e'
    have h1 := hTviso e e'
    have h2 : ∀ x, Tv x = x + ψv x := fun x => by rw [hψTv]; abel
    rw [h2 e, h2 e'] at h1
    simp only [map_add, LinearMap.add_apply] at h1
    rw [hrangeiso _ ⟨e, rfl⟩ _ ⟨e', rfl⟩, add_zero] at h1
    have h3 : M₀.B e (ψv e') + M₀.B (ψv e) e' = 0 := by linear_combination h1
    exact (eq_neg_of_add_eq_zero_right h3).trans (CharTwo.neg_eq _)
  obtain ⟨hc1, -, -⟩ := sec7_pair_card_meet8 hc M₀ ρ b₀ hS hgM ψv hrs hUcard
  have hd0 : Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψv) = 0 := by
    rw [hVinf, hZK] at hc1
    have h1 : 1 + Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψv) = 1 :=
      Nat.pow_right_injective hK2 (hc1.symm.trans (pow_one _).symm)
    omega
  have hcardR : Nat.card (LinearMap.range ψv) = Nat.card K ^ 8 := by
    have h1 : Nat.card (LinearMap.range ψv) =
        Nat.card (M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t))) :=
      Nat.card_congr (Equiv.subtypeEquivRight hrs)
    rw [h1, sec7_card_img_conj hc M₀ ρ b₀ hS hgM hZV']
    have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card (hc.VtSub hS.model t) := rfl
    rw [h2, hUcard]
  have hfR : Module.finrank K (LinearMap.range ψv) = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range ψv)
    rw [hcardR] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hfU : Module.finrank K (hc.VtSub hS.model t) = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := hc.VtSub hS.model t)
    rw [hUcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hmap := sec7_finrank_map_orthogonal M₀.B hf hr ψv hker_v (hc.VtSub hS.model t)
  rw [hd0, hfR] at hmap
  have hA8 : Module.finrank K ((M₀.B.orthogonal (hc.VtSub hS.model t)).map ψv) = 8 := by
    simpa using hmap
  have hAeq : (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψv = LinearMap.range ψv :=
    Submodule.eq_of_le_of_finrank_eq LinearMap.map_le_range (hA8.trans hfR.symm)
  have hUψ : hc.VtSub hS.model t ⊓ (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψv = ⊥ := by
    rw [hAeq]
    exact Submodule.finrank_eq_zero.mp hd0
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hVU' : Ut Q Z t = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 hs.toSec5.notQ
  obtain ⟨K', fK', finK', hchar', hKK', φ, u, hφ, hkerφ, hu, hu0, hL, hnorm⟩ :=
    sec7_point_data h34 hRoot hc hs.toSec5 h4
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite K'
  have hcardKK' : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKK', hZK]
  let θ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcardKK'
  let T := sec7OpHom hc hS (Rt M (LB M Q B) t) (hc.Rt_le_H0 t)
  have hTU : ∀ r : ↥(Rt M (LB M Q B) t), ∀ x ∈ hc.VtSub hS.model t,
      T r x ∈ hc.VtSub hS.model t := fun r x hx => sec7_op_mem_VtSub hc hS ht r.2 hx
  have hTW : ∀ r : ↥(Rt M (LB M Q B) t), ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      T r w ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := fun r w hw =>
    sec7_op_mem_perp hc hS ht r.2 hw
  have hvW' : ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      sec7Op hc hS huH w ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
    intro w hw
    have h1 := hψW w
    rw [hψv_apply] at h1
    have e : sec7Op hc hS huH w = (sec7Op hc hS huH w - w) + w := by abel
    rw [e]
    exact Submodule.add_mem _ h1 hw
  have hker' : ∀ ν : G, ν ∈ hc.CN t → ∀ hνH : ν ∈ H0 M Z,
      ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      sec7Op hc hS hνH w - w ∈ hc.VtSub hS.model t :=
    fun ν hν hνH w hw => sec7_ker_act hc hS h52a hA hs ψ hW hν hνH hw
  have hTψ : ∀ r : ↥(Rt M (LB M Q B) t), ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      T r (ψv w) - ψv (T r w) ∈ hc.VtSub hS.model t := fun r w hw =>
    sec7_equiv_wild hc hS ht hs huH hut huV hker' hvW' r.2 hw
  have hker : ∀ r ∈ φ.ker, ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      T r w - w ∈ hc.VtSub hS.model t := by
    intro r hr w hw
    have hrN : (r : G) ∈ hc.CN t := by
      rw [hkerφ] at hr
      exact Subgroup.mem_subgroupOf.mp hr
    exact hker' r hrN (hc.Rt_le_H0 t r.2) w hw
  set U : Submodule K M₀.E := hc.VtSub hS.model t with hUdef
  set W' : Submodule K M₀.E := M₀.B.orthogonal U with hW'def
  set R₀ : Submodule K M₀.E := W'.map ψv with hR₀def
  set P : Submodule K M₀.E := R₀ ⊔ U with hPdef
  have hUW : U ≤ W' := fun x hx n hn => hUiso n hn x hx
  have hR₀W : R₀ ≤ W' := by
    rintro _ ⟨w, -, rfl⟩
    exact hψW w
  have hPW : P ≤ W' := sup_le hR₀W hUW
  have hfinR : Module.finrank K R₀ = 8 := by
    rw [hAeq]
    exact hfR
  have hcardR' : Nat.card R₀ = Nat.card K ^ 8 := by
    rw [hAeq]
    exact hcardR
  have hfinP : Module.finrank K P = 16 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R₀ U
    rw [inf_comm, hUψ, finrank_bot, hfU, hfinR] at h
    omega
  have hcardP : Nat.card P = Nat.card K ^ 16 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := P)
    rw [hfinP] at h
    exact h
  have hirr : ∀ A : AddSubgroup M₀.E, A ≤ P.toAddSubgroup → U.toAddSubgroup ≤ A →
      (∀ r : ↥(Rt M (LB M Q B) t), ∀ a ∈ A, T r a ∈ A) →
      A = U.toAddSubgroup ∨ A = P.toAddSubgroup := fun A hAP hUA hAinv =>
    sec7_irred_E hc hS hSec hs h4 ψ hW P hPW hUcard hcardP A hUA hAP
      (fun r hr a ha' => hAinv ⟨r, hr⟩ a ha')
  have hLn : ∀ r : ↥(Rt M (LB M Q B) t),
      (∃ c : K', ((φ r : GL (Fin 4 ⊕ Fin 4) K') : Matrix _ _ K').mulVec u = c • u) →
      ∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t),
        r⁻¹ * l * r ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t) := by
    intro r hr l hl
    have hlL : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
    have h1 : (l : G) ∈ conjSubgroup (r : G) (LB M Q B) := by
      rw [hnorm r hr]
      exact hlL
    exact Subgroup.mem_subgroupOf.mpr (mem_conjSubgroup.mp h1)
  have hWR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r (Wt Q (Vt M (LB M Q B) B Z t)) =
      Wt Q (Vt M (LB M Q B) B Z t) := by
    intro r hr
    apply conjSubgroup_eq_self_iff.mpr
    exact Subgroup.mem_normalizer_fintype fun x hx =>
      conj_mem_Wt (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) (hc.Rt_normalizes_Vt ht hr) hx
  obtain ⟨r, hrA, hdec⟩ := hSplit G M Q Z B hc n t hs (Wt Q (Vt M (LB M Q B) B Z t)) hVW le_rfl
    hWR
  have hrM : r ∈ M := hc.Rt_le_M t hrA.mem
  have hcomm₁ : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓
      ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t),
      ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓
        ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t),
      x * y = y * x := fun x hx y hy => sec7_QBW_comm hc hVab x hx.2 y hy.2
  have hcomm₂ : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓
      ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t),
      ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t) ⊓
        ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t),
      x * y = y * x := fun x hx y hy =>
    sec7_QBW_comm (hc.conj_of_mem hrM) hVab x hx.2 y hy.2
  obtain ⟨hUA, hAiso, hAperp⟩ := sec7Asub_lagr hc hS ψ hW hdec hcomm₁ hcomm₂
  have hψA : ∀ a' ∈ sec7Asub hc hS t, ψv a' ∈ sec7Asub hc hS t := by
    intro a' ha'
    have h1 := sec7Asub_inv hc hS huH hconjLB hvW' (fun x hx => by rw [hvU x hx]; exact hx) a' ha'
    rw [hψv_apply]
    exact Submodule.sub_mem _ h1 ha'
  have hAmem : ∀ e, e ∈ sec7Asub hc hS t ↔ e ∈ W' ∧
      ∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t), T l e - e ∈ U := by
    intro e
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun l hl => h2 l (Subgroup.mem_subgroupOf.mp hl)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun l hl => h2 ⟨l, le_Rt (M := M) (LB M Q B) ht hl⟩
        (Subgroup.mem_subgroupOf.mpr hl)⟩
  have hpair := step76EightTamePair_of hVan hZV G M Q Z B hc n t hs hno
  have hSW : sec7Ssub M B M₀ t ≤ W' :=
    sec7Ssub_le_perp hc hS hVQ (fun f' hf'L hf'c a' ha' b hb =>
      (commutatorElement_eq_one_iff_mul_comm.mp
        (hpair f' hf'L hf'c t ht (ConjMod.of_mem htM) a' ha' b (by rw [hVU']; exact hb))).symm)
  have hSiso := sec7Ssub_iso hc hS hpair
  have hψS : ∀ s' ∈ sec7Ssub M B M₀ t, ψv s' ∈ sec7Ssub M B M₀ t := by
    intro s' hs'
    rw [hψv_apply]
    exact Submodule.sub_mem _ (sec7Ssub_inv hc hS huH hconjLB s' hs') hs'
  have hTS : ∀ r : ↥(Rt M (LB M Q B) t),
      (∃ c : K', ((φ r : GL (Fin 4 ⊕ Fin 4) K') : Matrix _ _ K').mulVec u = c • u) →
      ∀ s' ∈ sec7Ssub M B M₀ t, T r s' ∈ sec7Ssub M B M₀ t :=
    fun r hr s' hs' => sec7Ssub_inv hc hS (hc.Rt_le_H0 t r.2) (hnorm r hr) s' hs'
  have key := sec7_smith_core_twisted hSmith θ M₀.B hr U W' R₀ P rfl hUiso ψv hψadj hψU hψW rfl
    rfl hUψ hUcard hcardR' T hTU hTW hTψ φ hφ hker hirr
    ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)) hu hu0 hL hLn (sec7Asub hc hS t) hAmem hAperp
    hψA (sec7Ssub M B M₀ t) hSW hSiso hψS hTS
  have haQ : a ∈ Q := hc.Ut_le_Q hfc.1 ha
  have haS : M₀.π a ∈ sec7Ssub M B M₀ t :=
    Submodule.subset_span ⟨f, hfL, hfc, M₀.pi_mem_img ha haQ⟩
  have h1 := key _ haS
  rw [hψv_apply, sec7Op_sub_comm hc hS huH haQ] at h1
  have hvaQ : ⁅g * t * g⁻¹, a⁆ ∈ Q := sec7_comm_mem_Q hc huM haQ
  exact ((sec7Asub_iff hc hS ψ hW hdec hvaQ).mp h1).2

end

end CFSG.RankThree.GF2n.Stroth80
