module

public import CFSG.Quasithin.EmptyFaithful.SBc6Cover
public import CFSG.Quasithin.EmptyFaithful.SBc6Ov
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.Quasithin.EmptyFaithful.S153D30
public import CFSG.Quasithin.EmptyFaithful.SBc5BorelLift
public import CFSG.Quasithin.EmptyFaithful.SBc5Common

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace SBc6

section Generic

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {L S : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ L ⊔ S) : ∃ l ∈ L, ∃ s ∈ S, x = l * s := by
  have hx' : x ∈ (L : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L S hS]
    exact hx
  obtain ⟨l, hl, s, hs, rfl⟩ := hx'
  exact ⟨l, hl, s, hs, rfl⟩

end Generic

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem pCoreOf_le_of_ctx (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) :
    pCoreOf 2 L ≤ pCoreOf 2 I ∧ pCoreOf 2 L ≤ Subgroup.centralizer (UI153 T I : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  obtain ⟨hle, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (SBc5.omegaOneCenter_le_Sgp hh)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOCUI : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hle hu).2 x hx).symm
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hIL hg)) (pCoreOf_isPGroup 2 L)
  exact ⟨hOL, hOL.trans hOCUI⟩

theorem centralizer_inf_le_pCoreOf (c : Ctx15330 T Mc M V₁ V₂ Yp I L t)
    (hn : ∃ n : ℕ, 1 < n ∧ IsPSL 2 2 n ↥(Star153 T I L)) :
    L ⊓ Subgroup.centralizer (UI153 T I : Set G) ≤ pCoreOf 2 L := by
  obtain ⟨n, -, hPSL⟩ := hn
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hLQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := c25.conc.2.2.2.2.2
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLN : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hIU
  have hQC := (pCoreOf_le_of_ctx c).2
  let ψ₀ : ↥L →* MulAut ↥(UI153 T I) := A4.actionOn (UI153 T I) L hLN
  have hψ₀range : ψ₀.range = Star153 T I L := by
    ext a
    rw [MonoidHom.mem_range]
    exact (A4.mem_autOn_iff hLN).symm
  have hψ₀ker : ∀ x : ↥L, ψ₀ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
    fun x => A4.actionOn_eq_one_iff hLN x
  let ψ : ↥L →* ↥(Star153 T I L) :=
    ψ₀.codRestrict (Star153 T I L) (fun x => hψ₀range ▸ ⟨x, rfl⟩)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    rw [← hψ₀range] at ha
    obtain ⟨x, rfl⟩ := ha
    exact ⟨x, rfl⟩
  have hψker : ∀ x : ↥L, ψ x = 1 ↔ ψ₀ x = 1 := fun x =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hQ : CFSG.pCore 2 ↥L ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hψker]
    exact (hψ₀ker x).2 (hQC ((AppC.mem_pCore_iff_mem_blockQ x).1 hx))
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := exists_statedSL_equiv_of_psl hPSL
  have hcov := ker_le_pCore_of_cover ψ hψsurj hQ hLQ ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩
  rintro x ⟨hxL, hxC⟩
  have hx1 : ψ ⟨x, hxL⟩ = 1 := (hψker _).2 ((hψ₀ker _).2 hxC)
  exact (AppC.mem_pCore_iff_mem_blockQ _).1 (hcov hx1)


theorem minParabolic_of_ctx (c : Ctx15330 T Mc M V₁ V₂ Yp I L t)
    (hn : ∃ n : ℕ, 1 < n ∧ IsPSL 2 2 n ↥(Star153 T I L))
    (hBorel : IsBorelIn (Star153 T I L) (Star153 T I (M ⊓ L))) :
    MinParabolic I (Sgp153 T V₁) (M ⊓ I) := by
  have hker := centralizer_inf_le_pCoreOf c hn
  obtain ⟨hOL, -⟩ := pCoreOf_le_of_ctx c
  obtain ⟨n, -, hPSL⟩ := hn
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hLM : ¬ L ≤ M ⊓ I := c25.conc.2.1
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLN : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hIU
  have hSM : Sgp153 T V₁ ≤ M := inf_le_right.trans c.c29.norm_le
  have hLM' : ¬ L ≤ M := fun h => hLM (le_inf h hLI)
  let ψ₀ : ↥L →* MulAut ↥(UI153 T I) := A4.actionOn (UI153 T I) L hLN
  have hψ₀range : ψ₀.range = Star153 T I L := by
    ext a
    rw [MonoidHom.mem_range]
    exact (A4.mem_autOn_iff hLN).symm
  have hψ₀ker : ∀ x : ↥L, ψ₀ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
    fun x => A4.actionOn_eq_one_iff hLN x
  have hker_le : ∀ x : ↥L, ψ₀ x = 1 → (x : G) ∈ pCoreOf 2 L := fun x hx =>
    hker ⟨x.2, (hψ₀ker x).1 hx⟩
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
  obtain ⟨P, hP, hBP⟩ : ∃ P : Subgroup G, IsSylowTwoOf P L ∧
      M ⊓ L = L ⊓ Subgroup.normalizer (P : Set G) := by
    refine SBc5.exists_sylow_of_borel_image hBL ψ₀ hker2 hPs ?_ ?_
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
      exact ⟨(hF.cent_le ⟨hLI x.2, (hψ₀ker x).1 hx⟩).1, x.2⟩
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  have hQP : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    have hxM : x ∈ M ⊓ L := ⟨hSM hx.1, hx.2⟩
    rw [hBP] at hxM
    exact hxM.2
  have hPQ : Sgp153 T V₁ ⊓ L = P := eq_of_le_normalizer_of_isSylowTwoOf hQsyl hP hQP
  have hML : M ⊓ L = L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
    rw [hPQ]
    exact hBP
  let ψ : ↥L →* ↥(Star153 T I L) :=
    ψ₀.codRestrict (Star153 T I L) (fun x => hψ₀range ▸ ⟨x, rfl⟩)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    rw [← hψ₀range] at ha
    obtain ⟨x, rfl⟩ := ha
    exact ⟨x, rfl⟩
  have hψker : ∀ x : ↥L, ψ x = 1 ↔ ψ₀ x = 1 := fun x =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hQs : IsSylowTwoOf ((Sgp153 T V₁ ⊓ L).subgroupOf L) (⊤ : Subgroup ↥L) :=
    SBc5.isSylowTwoOf_subgroupOf_top hQsyl
  have hkerQ : ψ.ker ≤ (Sgp153 T V₁ ⊓ L).subgroupOf L := by
    intro x hx
    have hxO : (x : G) ∈ pCoreOf 2 L := hker_le x ((hψker x).1 hx)
    exact ⟨pCoreOf_le_of_isSylowTwoOf hsyl (hOL hxO), x.2⟩
  have hO : ∀ N : Subgroup G, Sgp153 T V₁ ≤ N → N ≤ I → N ≠ I → N ≤ M ⊓ I := by
    intro N hSN hNI hNne y hy
    have hyLS : y ∈ L ⊔ Sgp153 T V₁ := by
      rw [← hIeq]
      exact hNI hy
    obtain ⟨l, hl, s, hs, rfl⟩ := exists_mul_of_mem_sup (hSI.trans hIL) hyLS
    have hlN : l ∈ N := by
      have := N.mul_mem hy (N.inv_mem (hSN hs))
      simpa using this
    have hQD : (Sgp153 T V₁ ⊓ L).subgroupOf L ≤ (N ⊓ L).subgroupOf L := fun x hx =>
      ⟨hSN hx.1, hx.2⟩
    rcases SBc6.overgroup_of_cover hPSL ψ hψsurj hQs hkerQ hQD with htop | hnorm
    · exfalso
      apply hNne
      have hLN' : L ≤ N := fun z hz => by
        have : (⟨z, hz⟩ : ↥L) ∈ (N ⊓ L).subgroupOf L := htop ▸ Subgroup.mem_top _
        exact this.1
      refine le_antisymm hNI ?_
      rw [hIeq]
      exact sup_le hLN' hSN
    · have hlD : (⟨l, hl⟩ : ↥L) ∈ (N ⊓ L).subgroupOf L := ⟨hlN, hl⟩
      have h1 := hnorm hlD
      rw [SBc5.mem_normalizer_subgroupOf_iff inf_le_right] at h1
      have hlM : l ∈ M ⊓ L := by
        rw [hML]
        exact ⟨hl, h1⟩
      exact ⟨M.mul_mem hlM.1 (hSM hs), hNI hy⟩
  have hlt : M ⊓ I < I := lt_of_le_of_ne inf_le_right fun h => hLM' (fun x hx => by
    have hxI : x ∈ I := hLI hx
    rw [← h] at hxI
    exact hxI.1)
  have hmax : IsMaxSubgroupIn I (M ⊓ I) := ⟨hlt, fun K hMK hKI => by
    by_contra hne
    exact absurd hMK (not_lt_of_ge (hO K ((le_inf hSM hSI).trans hMK.le) hKI hne))⟩
  refine ⟨hsyl, ?_, isUniqueMaxOver_iff.mpr ⟨hmax, le_inf hSM hSI, fun N hN hSN => ?_⟩⟩
  · intro hnorm
    have hLnorm : ⊤ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L).subgroupOf L : Set ↥L) := by
      intro x _
      rw [SBc5.mem_normalizer_subgroupOf_iff inf_le_right]
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hnorm (hLI x.2), hIL (hLI x.2)⟩
    exact not_normal_of_cover hPSL ψ hψsurj hQs hLnorm
  · have hNle : N ≤ M ⊓ I := hO N hSN hN.1.le (ne_of_lt hN.1)
    by_contra hne
    exact hlt.ne (hN.2 _ (lt_of_le_of_ne hNle hne) inf_le_right)


theorem exists_cover_of_ctx (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) :
    ∃ ψ : ↥L →* ↥(Star153 T I L), Function.Surjective ψ ∧
      ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (UI153 T I : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLN : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hIU
  let ψ₀ : ↥L →* MulAut ↥(UI153 T I) := A4.actionOn (UI153 T I) L hLN
  have hψ₀range : ψ₀.range = Star153 T I L := by
    ext a
    rw [MonoidHom.mem_range]
    exact (A4.mem_autOn_iff hLN).symm
  refine ⟨ψ₀.codRestrict (Star153 T I L) (fun x => hψ₀range ▸ ⟨x, rfl⟩), ?_, fun x => ?_⟩
  · rintro ⟨a, ha⟩
    rw [← hψ₀range] at ha
    obtain ⟨x, rfl⟩ := ha
    exact ⟨x, rfl⟩
  · exact ⟨fun h => (A4.actionOn_eq_one_iff hLN x).1 (congrArg Subtype.val h),
      fun h => Subtype.ext ((A4.actionOn_eq_one_iff hLN x).2 h)⟩

end Basic

end SBc6

end CFSG.Quasithin
