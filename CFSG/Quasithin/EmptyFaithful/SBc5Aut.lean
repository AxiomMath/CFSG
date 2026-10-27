module

public import CFSG.Quasithin.EmptyFaithful.S153H30
public import CFSG.Quasithin.EmptyFaithful.SBc5Block
public import CFSG.Quasithin.EmptyFaithful.SBc5BorelLift
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBc5SL2
open scoped commutatorElement

namespace SBc5

section Ker

variable {A : Type} [Group A]

theorem eq_top_or_le_ker_of_simple {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    (α : A →* SL2 F) (hα : Function.Surjective α) {N : Subgroup A} [N.Normal] (hQN : α.ker ≤ N) :
    N = ⊤ ∨ N ≤ α.ker := by
  have hsimple : IsSimpleGroup (SL2 F) := by
    have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo hF
    exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).isSimpleGroup
  have hn : (N.map α).Normal := Subgroup.Normal.map inferInstance α hα
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map α) with hb | ht
  · right
    intro x hx
    have : α x ∈ N.map α := Subgroup.mem_map_of_mem α hx
    rw [hb, Subgroup.mem_bot] at this
    exact this
  · left
    rw [eq_top_iff]
    intro a _
    have : α a ∈ N.map α := ht ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hna⟩ := this
    have h1 : n⁻¹ * a ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hna, inv_mul_cancel]
    have h2 : a = n * (n⁻¹ * a) := by group
    rw [h2]
    exact N.mul_mem hn (hQN h1)

end Ker

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input30AutCent_holds : Input30AutCent := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hBorel hBlock hlin0 s hs hsc
  obtain ⟨m, hm, hlin⟩ := hlin0
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hsyl.2.1
  obtain ⟨hLcJ, hLM, -, -, hStarQ, hLQ⟩ := c25.conc
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLcJ
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hSh : IsShort2 L := hBlock.1
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLN : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hIU
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hIL (hSI hs)
  obtain ⟨hle, hel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (omegaOneCenter_le_Sgp hh)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOCUI : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hle hu).2 x hx).symm
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hIL hg)) (pCoreOf_isPGroup 2 L)
  have hQC : pCoreOf 2 L ≤ Subgroup.centralizer (UI153 T I : Set G) := hOL.trans hOCUI
  let ψ₀ : ↥L →* MulAut ↥(UI153 T I) := A4.actionOn (UI153 T I) L hLN
  have hψ₀range : ψ₀.range = Star153 T I L := by
    ext a
    rw [MonoidHom.mem_range]
    exact (A4.mem_autOn_iff hLN).symm
  have hψ₀ker : ∀ x : ↥L, ψ₀ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
    fun x => A4.actionOn_eq_one_iff hLN x
  have hker_le : ∀ x : ↥L, ψ₀ x = 1 → (x : G) ∈ pCoreOf 2 L := by
    obtain ⟨F, hFf, hFfin, hFcard, α, hαs, hαk, -⟩ := hlin
    have hFfinite : Finite F := Finite.of_fintype F
    have hcardF : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hFcard]
    have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hcardF
    have h4 : 4 ≤ Nat.card F := by
      rw [hcardF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hkerQ : α.ker ≤ ψ₀.ker := fun x hx => by
      rw [hαk] at hx
      exact (hψ₀ker x).2 (hQC ((AppC.mem_pCore_iff_mem_blockQ x).1 hx))
    rcases eq_top_or_le_ker_of_simple h4 α hαs hkerQ with htop | hle'
    · exfalso
      apply hLM
      intro x hx
      have : ψ₀ ⟨x, hx⟩ = 1 := by
        have : (⟨x, hx⟩ : ↥L) ∈ ψ₀.ker := htop ▸ Subgroup.mem_top _
        exact this
      exact hF.cent_le ⟨hLI hx, (hψ₀ker _).1 this⟩
    · intro x hx
      have : x ∈ α.ker := hle' hx
      rw [hαk] at this
      exact (AppC.mem_pCore_iff_mem_blockQ x).1 this
  have hker2 : IsPGroup 2 ↥ψ₀.ker := by
    intro x
    have hxP : ((x : ↥L) : G) ∈ pCoreOf 2 L := hker_le x x.2
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨(x : G), hxP⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(pCoreOf 2 L) => (z : G)) hk
    simpa using this
  obtain ⟨Ps, hPs, hB⟩ := hBorel
  rw [← hψ₀range] at hPs
  have hBL : M ⊓ L ≤ L := inf_le_right
  have hBorelL : ∃ P : Subgroup G, IsSylowTwoOf P L ∧
      M ⊓ L = L ⊓ Subgroup.normalizer (P : Set G) := by
    refine exists_sylow_of_borel_image hBL ψ₀ hker2 hPs ?_ ?_
    · intro r
      rw [hψ₀range]
      have hMLN : M ⊓ L ≤ Subgroup.normalizer (UI153 T I : Set G) := inf_le_right.trans hLN
      have h1 : r ∈ Star153 T I L ⊓ Subgroup.normalizer (Ps : Set (MulAut ↥(UI153 T I))) ↔
          r ∈ Star153 T I (M ⊓ L) := by rw [hB]
      rw [h1]
      constructor
      · intro hr
        obtain ⟨h, hh⟩ := (A4.mem_autOn_iff hMLN).1 hr
        exact ⟨⟨(h : G), h.2.2⟩, h.2, hh⟩
      · rintro ⟨b, hb, rfl⟩
        exact (A4.mem_autOn_iff hMLN).2 ⟨⟨(b : G), hb⟩, rfl⟩
    · intro x hx
      exact ⟨hF.cent_le ⟨hLI x.2, (hψ₀ker x).1 hx⟩ |>.1, x.2⟩
  have h3L : ∀ x : G, x ∈ I → ∀ k : ℕ, orderOf x = 3 ^ k → x ∈ L := by
    intro x hx k hk
    obtain ⟨e, he⟩ := InternalSec.two_of_sup hS2 (hSI.trans hIL) x (hIeq ▸ hx)
    have hcop : Nat.Coprime (2 ^ e) (orderOf x) := by
      rw [hk]
      exact Nat.Coprime.pow e k (by norm_num)
    obtain ⟨c', hc'⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hc']
    exact L.pow_mem he c'
  have hYeq : oPrimeResidualOf 3 (M ⊓ L) = Yp := by
    rw [hF.yp_eq]
    unfold oPrimeResidualOf
    apply le_antisymm
    · refine Subgroup.closure_mono (fun x hx => ?_)
      obtain ⟨⟨hxM, hxL⟩, k, hk⟩ := hx
      exact ⟨⟨hxM, hLI hxL⟩, k, hk⟩
    · refine (Subgroup.closure_le _).2 (fun x hx => ?_)
      obtain ⟨⟨hxM, hxI⟩, k, hk⟩ := hx
      exact Subgroup.subset_closure ⟨⟨hxM, h3L x hxI k hk⟩, k, hk⟩
  have hY : ¬ oPrimeResidualOf 3 (M ⊓ L) ≤ pCoreOf 2 L := by
    rw [hYeq]
    intro hle'
    exact hF.star_ne (autI_eq_bot_of_le_centralizer hel (hle'.trans hQC))
  obtain ⟨P, hP, hBP⟩ := hBorelL
  exact autCent_of_lin2 hm hSh hlin ⟨P, hP, hBP⟩ hY hsN (fun y hy => hsc y (hYeq ▸ hy))

end Main

end SBc5

end CFSG.Quasithin
