module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EightWildMoves
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step7Algebra
public import CFSG.RankThree.GF2n.Stroth80.Sec7TamePair
public import CFSG.RankThree.GF2n.Stroth80.Sec7CentreImg
public import CFSG.RankThree.GF2n.Stroth80.Sec7OpData

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step76EightSmithCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ f ∈ LB M Q B, ConjMod M Q t f → ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∀ a ∈ Ut Q Z f, ⁅g * t * g⁻¹, a⁆ ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t

theorem step76EightKTame_of_smith_core (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h310chi : Stroth310ChiStatement) (h71 : Stroth71Statement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) (hSec : Sec7WVSecCardStatement)
    (hVan : Step71VanishStatement) (hSC : Step76EightSmithCoreStatement) :
    Step76EightKTameStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 f hfL hfc g hgM hΓ hwild a ha b hb
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
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
  obtain ⟨hfM, g₀, hg₀M, hq⟩ := hfc
  have hfN : f ∈ hc.CN t := by
    have hno_a : ¬ Conc71a hc t := fun h => hno (Or.inl h)
    unfold Conc71a at hno_a
    push Not at hno_a
    have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
    have htR : t ∈ Rt M (LB M Q B) t := hLR ht
    have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
    have e : g₀ * t * g₀⁻¹ = (f * (g₀ * t * g₀⁻¹)⁻¹)⁻¹ * f := by group
    have hg₀L : g₀ * t * g₀⁻¹ ∈ LB M Q B := by
      rw [e]
      exact (LB M Q B).mul_mem ((LB M Q B).inv_mem (hQL hq)) hfL
    have h1 := hno_a t htR (fun r hr => hZ0.comm_mem htZ0 hr) g₀ hg₀M hg₀L
    have hqN : f * (g₀ * t * g₀⁻¹)⁻¹ ∈ hc.CN t :=
      Ctx.mem_CN.mpr ⟨hLR (hQL hq), fun v hv =>
        hc.hyp.toHyp79.comm_mem_V hq (hVQ hv)⟩
    have e2 : f = (f * (g₀ * t * g₀⁻¹)⁻¹) * (g₀ * t * g₀⁻¹) := by group
    rw [e2]
    exact (hc.CN t).mul_mem hqN h1
  obtain ⟨hf'M, hf'L, hf'c, hconjLB⟩ : ∃ _ : (g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹ ∈ M,
      (g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹ ∈ LB M Q B ∧
      ConjMod M Q t ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹) ∧
      conjSubgroup (g * t * g⁻¹) (LB M Q B) = LB M Q B := by
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
    have hmem : (g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹ ∈ LB M Q B := by
      have h1 : (g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹ ∈ conjSubgroup (g * t * g⁻¹) (LB M Q B) := by
        rw [mem_conjSubgroup]
        have e : (g * t * g⁻¹)⁻¹ * ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) = f := by
          group
        rw [e]
        exact hfL
      rwa [hconjLB] at h1
    refine ⟨M.mul_mem (M.mul_mem huM hfM) (M.inv_mem huM), hmem,
      ⟨M.mul_mem (M.mul_mem huM hfM) (M.inv_mem huM), (g * t * g⁻¹) * g₀,
        M.mul_mem huM hg₀M, ?_⟩, hconjLB⟩
    have e : (g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹ * ((g * t * g⁻¹) * g₀ * t *
        ((g * t * g⁻¹) * g₀)⁻¹)⁻¹ = (g * t * g⁻¹) * (f * (g₀ * t * g₀⁻¹)⁻¹) *
          (g * t * g⁻¹)⁻¹ := by group
    rw [e]
    exact hQn _ huM _ hq
  have hf'H : (g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹ ∈ H0 M Z := hc.LB_le_H0 hf'L
  have hfH : f ∈ H0 M Z := hc.LB_le_H0 hfL
  have hf2 : f ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hfL
  have hf'2 : ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hf'L
  have hUtu : Ut Q Z (g * t * g⁻¹) = conjSubgroup g (Vt M (LB M Q B) B Z t) := hUt g hgM
  have hfc' : ConjMod M Q t f := ⟨hfM, g₀, hg₀M, hq⟩
  have hK1 := step76EightTamePair_of hVan hZV G M Q Z B hc n t hs hno f hfL hfc' _ hf'L hf'c
  have hSC' := hSC G M Q Z B hc n t hs hno h4 Z0 hZ0 f hfL hfc' g hgM hΓ hwild
  have hUW : ∀ y ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), y ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun y hy => by
      have h1 : g⁻¹ * y * g ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hy
      have h2 := sec7_pair_mem_W h71 h310chi hc hs hno hgM hs1 hut _ h1
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [e] at h2
  obtain ⟨K, fK, finK, γ, M₀, ρ, b₀, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hS.card.trans he)
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  have hreg := hS.model.reg
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  obtain ⟨-, hUcard⟩ := sec7_Hset_card8 h34 h310chi hc hs h4 M₀ ρ b₀ hS ψ hψ hrange
  obtain ⟨Tf, hTf_eq, hTf2, hTfiso, hTf_range, hTf_ker, hTf_comm⟩ :=
    sec7_op_data hc M₀ ρ b₀ hS hfH hf2
  obtain ⟨Tv, hTv_eq, hTv2, hTviso, hTv_range, hTv_ker, hTv_comm⟩ :=
    sec7_op_data hc M₀ ρ b₀ hS huH hu2
  obtain ⟨Tf', hTf'_eq, hTf'2, hTf'iso, hTf'_range, hTf'_ker, hTf'_comm⟩ :=
    sec7_op_data hc M₀ ρ b₀ hS hf'H hf'2
  have hmu : (QuotientGroup.mk (⟨g * t * g⁻¹, huM⟩ : ↥M) : Mbar M Q)⁻¹ =
      QuotientGroup.mk (⟨g * t * g⁻¹, huM⟩ : ↥M) := by
    have h1 : (QuotientGroup.mk (⟨g * t * g⁻¹, huM⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨g * t * g⁻¹, huM⟩ : ↥M) = 1 := by
      rw [← QuotientGroup.mk_mul]
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [pow_two] using hu2
    exact inv_eq_of_mul_eq_one_right h1
  have hTf'_form : ∀ e, Tf' e = Tv (Tf (Tv e)) := by
    intro e
    have hmk : (QuotientGroup.mk (⟨(g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹, hf'H.1⟩ : ↥M) :
        Mbar M Q) = QuotientGroup.mk (⟨g * t * g⁻¹, huM⟩ : ↥M) *
          QuotientGroup.mk (⟨f, hfM⟩ : ↥M) *
          (QuotientGroup.mk (⟨g * t * g⁻¹, huM⟩ : ↥M))⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [hTf'_eq, hmk, act_mul_apply ρ, act_mul_apply ρ, hmu, ← hTv_eq, ← hTf_eq, ← hTv_eq]
  have hperpF : ∀ e, Tf (Tv (Tf (Tv e)) - e) - (Tv (Tf (Tv e)) - e) = 0 := by
    intro e
    have hw : Tf' e - e ∈ LinearMap.range ((Tf' : M₀.E →ₗ[K] M₀.E) - 1) := ⟨e, rfl⟩
    obtain ⟨x', hx'U, hx'Q, hx'π⟩ := M₀.mem_img.mp ((hTf'_range _).mp hw)
    have hker : Tf' e - e ∈ LinearMap.ker ((Tf : M₀.E →ₗ[K] M₀.E) - 1) := by
      rw [hTf_ker, LinearMap.BilinForm.mem_orthogonal_iff]
      intro e'' he''
      obtain ⟨a'', ha''U, ha''Q, ha''π⟩ := M₀.mem_img.mp ((hTf_range _).mp he'')
      rw [← ha''π, ← hx'π]
      exact (M₀.comm_iff_B hreg ha''Q hx'Q).mp
        (commutatorElement_eq_one_iff_mul_comm.mp (hK1 a'' ha''U x' hx'U))
    have h0 : Tf (Tf' e - e) - (Tf' e - e) = 0 := LinearMap.mem_ker.mp hker
    rw [hTf'_form] at h0
    exact h0
  have hvU : ∀ e ∈ hc.VtSub hS.model t, Tv e = e := by
    intro e he
    obtain ⟨v₀, hv₀V, hv₀Q, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp he)
    have h1 := hTv_comm v₀ hv₀Q
    rw [(M₀.π_ker _ (sec7_comm_mem_Q hc huM hv₀Q)).mpr (huV v₀ hv₀V)] at h1
    exact sub_eq_zero.mp h1.symm
  have hfU : ∀ e ∈ hc.VtSub hS.model t, Tf e = e := by
    intro e he
    obtain ⟨v₀, hv₀V, hv₀Q, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp he)
    have h1 := hTf_comm v₀ hv₀Q
    rw [(M₀.π_ker _ (sec7_comm_mem_Q hc hfM hv₀Q)).mpr ((Ctx.mem_CN.mp hfN).2 v₀ hv₀V)] at h1
    exact sub_eq_zero.mp h1.symm
  have hvW : ∀ e, Tv e - e ∈ LinearMap.ker ψ := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hTv_comm x hxQ]
    exact LinearMap.mem_ker.mpr
      ((hW _ (sec7_comm_mem_Q hc huM hxQ)).mp (hUW _ (hQx x hxQ)))
  have hfW : ∀ w ∈ LinearMap.ker ψ, Tf w - w ∈ hc.VtSub hS.model t := by
    intro w hw
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj w
    have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := (hW x hxQ).mpr (LinearMap.mem_ker.mp hw)
    rw [← hTf_comm x hxQ]
    exact (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img
      (sec7_N_comm_W_le_V h52a hA hc hs f hfN x hxW) (sec7_comm_mem_Q hc hfM hxQ))
  have halg : ∀ e, Tf (Tv (Tf (Tv e))) - e =
      (Tv (Tf e - e) - (Tf e - e)) + (Tf (Tv e - e) - (Tv e - e)) := fun e =>
    sec7_step7_algebra (hc.VtSub hS.model t) (LinearMap.ker ψ)
      (Tf : M₀.E →ₗ[K] M₀.E) (Tv : M₀.E →ₗ[K] M₀.E) hTf2 hTv2 hvU hvW hfU hfW hperpF e
  have hyL : f * ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹) ∈ LB M Q B := (LB M Q B).mul_mem hfL hf'L
  have hyM : f * ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹) ∈ M := hc.LB_le_M hyL
  have hTy : ∀ e, (ρ (QuotientGroup.mk (⟨f * ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹), hyM⟩ :
      ↥M))).toAdd e = Tf (Tv (Tf (Tv e))) := by
    intro e
    have hmk : (QuotientGroup.mk (⟨f * ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹), hyM⟩ : ↥M) :
        Mbar M Q) = QuotientGroup.mk (⟨f, hfM⟩ : ↥M) *
          QuotientGroup.mk (⟨(g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹, hf'H.1⟩ : ↥M) := by
      rw [← QuotientGroup.mk_mul]
      rfl
    rw [hmk, act_mul_apply ρ, ← hTf'_eq, ← hTf_eq, hTf'_form]
  have hH : ∀ e : M₀.E, (ρ (QuotientGroup.mk (⟨f * ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹),
      hyM⟩ : ↥M))).toAdd e - e ∈ M₀.img ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t) := by
    intro e
    rw [hTy e, halg e]
    refine AddSubgroup.add_mem _ ?_ ?_
    · obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      have h1' : ⁅x, f⁆ ∈ ⁅Q, Subgroup.zpowers f⁆ :=
        Subgroup.commutator_mem_commutator hxQ (Subgroup.mem_zpowers f)
      have ha' : ⁅f, x⁆ ∈ Ut Q Z f := by
        rw [← commutatorElement_inv]
        exact (Ut Q Z f).inv_mem (Subgroup.mem_sup_left h1')
      have h1 := hTv_comm ⁅f, x⁆ (sec7_comm_mem_Q hc hfM hxQ)
      rw [hTf_comm x hxQ] at h1
      rw [← h1]
      exact M₀.pi_mem_img (hSC' _ ha')
        (sec7_comm_mem_Q hc huM (sec7_comm_mem_Q hc hfM hxQ))
    · exact M₀.img_mono le_sup_right ((hc.mem_VtSub hS.model t).mp (hfW _ (hvW e)))
  have hyZ0 : f * ((g * t * g⁻¹) * f * (g * t * g⁻¹)⁻¹) ∈ Z0 :=
    sec7_mem_centre_of_img_le h34 hRoot hZc hZcard hc hs hZ0 hyL M₀ ρ b₀ hS hH
  by_contra hne
  have haQ : a ∈ Q := hc.Ut_le_Q hfM ha
  have hbQ : b ∈ Q := hc.Ut_le_Q huM hb
  have hFb : Tf (M₀.π b) - M₀.π b ≠ 0 := by
    intro h0
    have hmem : M₀.π b ∈ LinearMap.ker ((Tf : M₀.E →ₗ[K] M₀.E) - 1) :=
      LinearMap.mem_ker.mpr h0
    rw [hTf_ker, LinearMap.BilinForm.mem_orthogonal_iff] at hmem
    have h1 := LinearMap.BilinForm.isOrtho_def.mp
      (hmem (M₀.π a) ((hTf_range _).mpr (M₀.pi_mem_img ha haQ)))
    exact hne (commutatorElement_eq_one_iff_mul_comm.mpr ((M₀.comm_iff_B hreg haQ hbQ).mpr h1))
  have hrs : ∀ e, e ∈ LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1) ↔
      e ∈ M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t)) := fun e =>
    (hTv_range e).trans (by rw [hUtu])
  obtain ⟨hc1, -, -⟩ := sec7_pair_card_meet8 hc M₀ ρ b₀ hS hgM
    ((Tv : M₀.E →ₗ[K] M₀.E) - 1) hrs hUcard
  have hd0 : Module.finrank K ↥(hc.VtSub hS.model t ⊓
      LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1)) = 0 := by
    rw [hVinf, hZK] at hc1
    have h1 : 1 + Module.finrank K ↥(hc.VtSub hS.model t ⊓
        LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1)) = 1 :=
      Nat.pow_right_injective hK2 (hc1.symm.trans (pow_one _).symm)
    omega
  have hfR : Module.finrank K (LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1)) = 8 := by
    have hcard : Nat.card (LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1)) = Nat.card K ^ 8 := by
      have h1 : Nat.card (LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1)) =
          Nat.card (M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t))) :=
        Nat.card_congr (Equiv.subtypeEquivRight hrs)
      rw [h1, sec7_card_img_conj hc M₀ ρ b₀ hS hgM hZV']
      have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
          Nat.card (hc.VtSub hS.model t) := rfl
      rw [h2, hUcard]
    have h := Module.natCard_eq_pow_finrank (K := K)
      (V := LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1))
    rw [hcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hmap := sec7_finrank_map_orthogonal M₀.B hf hr ((Tv : M₀.E →ₗ[K] M₀.E) - 1) hTv_ker
    (hc.VtSub hS.model t)
  rw [hd0, hfR] at hmap
  have hA8 : Module.finrank K ((M₀.B.orthogonal (hc.VtSub hS.model t)).map
      ((Tv : M₀.E →ₗ[K] M₀.E) - 1)) = 8 := by simpa using hmap
  have hAeq : (M₀.B.orthogonal (hc.VtSub hS.model t)).map ((Tv : M₀.E →ₗ[K] M₀.E) - 1) =
      LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1) :=
    Submodule.eq_of_le_of_finrank_eq LinearMap.map_le_range (hA8.trans hfR.symm)
  have hb' : b ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [← hUtu]
    exact hb
  have hπb : M₀.π b ∈ LinearMap.range ((Tv : M₀.E →ₗ[K] M₀.E) - 1) :=
    (hrs _).mpr (M₀.pi_mem_img hb' hbQ)
  rw [← hAeq] at hπb
  obtain ⟨w₁, hw₁, hw₁b⟩ := Submodule.mem_map.mp hπb
  have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b₀ hS ψ hW
  rw [← hk1] at hw₁
  have hw₁b' : Tv w₁ - w₁ = M₀.π b := by
    exact hw₁b
  have hGF : Tv (Tf w₁ - w₁) - (Tf w₁ - w₁) = 0 := by
    have h1 := hvU _ ((hfW w₁ hw₁))
    rw [h1, sub_self]
  have hmain : Tf (Tv (Tf (Tv w₁))) - w₁ = Tf (M₀.π b) - M₀.π b := by
    have h1 := halg w₁
    rw [hGF, zero_add, hw₁b'] at h1
    exact h1
  obtain ⟨x₁, hx₁Q, rfl⟩ := M₀.π_surj w₁
  have hx₁W : x₁ ∈ Wt Q (Vt M (LB M Q B) B Z t) := (hW x₁ hx₁Q).mpr (LinearMap.mem_ker.mp hw₁)
  have hyz := ((hZc G M Q Z B hc n t hs Z0 hZ0 _ hyZ0).2 x₁ hx₁W)
  have h2 := sec7_act_sub_comm hc M₀ ρ b₀ hS hyM hx₁Q
  rw [(M₀.π_ker _ (sec7_comm_mem_Q hc hyM hx₁Q)).mpr hyz, hTy] at h2
  rw [hmain] at h2
  exact hFb h2

end CFSG.RankThree.GF2n.Stroth80
