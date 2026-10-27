module

public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Alt8

private theorem lred_eq_alt8 {K : Subgroup (Equiv.Perm (Fin 8))} (hn : K.Normal)
    (hperf : commutator ↥K = ⊤) (hbot : K ≠ ⊥) : K = alternatingGroup (Fin 8) := by
  have hle : K ≤ alternatingGroup (Fin 8) := by
    intro k hk
    have hker := Abelianization.commutator_subset_ker
      ((Equiv.Perm.sign : Equiv.Perm (Fin 8) →* ℤˣ).comp K.subtype)
    have hmem : (⟨k, hk⟩ : ↥K) ∈ commutator ↥K := by rw [hperf]; trivial
    have := hker hmem
    simpa [Equiv.Perm.mem_alternatingGroup] using this
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKn : (K.subgroupOf (alternatingGroup (Fin 8))).Normal := hn.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 8))) with h | h
  · exfalso
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 8))) ∈ K.subgroupOf (alternatingGroup (Fin 8)) := hx
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

private theorem lred_star_equiv_alt8 {G : Type} [Group G] {T I L : Subgroup G} (hLI : L ≤ I)
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) (hq : CFSG.IsQuasisimple ↥(Star153 T I L))
    (e : ↥(Star153 T I I) ≃* Equiv.Perm (Fin 8)) :
    Nonempty (↥(Star153 T I L) ≃* ↥(alternatingGroup (Fin 8))) := by
  have hAB : Star153 T I L ≤ Star153 T I I := InternalSec.autOn_le_autOn_of_le hLI
  set N : Subgroup ↥(Star153 T I I) := (Star153 T I L).subgroupOf (Star153 T I I) with hN
  set K : Subgroup (Equiv.Perm (Fin 8)) := N.map e.toMonoidHom with hK
  let eAK : ↥(Star153 T I L) ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hAB).symm.trans (e.subgroupMap N)
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨e.symm g * n * (e.symm g)⁻¹, ?_, by simp⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := InternalSec.autOn_normal_of (U := UI153 T I) hIL _ (e.symm g).2 _ hn
    simpa using this
  have hqK : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv eAK hq
  have hperf : commutator ↥K = ⊤ := hqK.1.commutator_eq_top
  have hbot : K ≠ ⊥ := by
    intro hb
    obtain ⟨-, -, a, b, hab⟩ := hqK
    have hs : Subsingleton ↥K := by rw [hb]; infer_instance
    have : Subsingleton (↥K ⧸ Subgroup.center ↥K) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim x y]⟩
    exact hab (Subsingleton.elim _ _)
  exact ⟨eAK.trans (MulEquiv.subgroupCongr (lred_eq_alt8 hKn hperf hbot))⟩

end Alt8

section Mult

private noncomputable def lredAlt8EquivStatedSL :
    ↥(alternatingGroup (Fin 8)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
  CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
    ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm.trans
      (specialLinearGroupEquivStatedSL 4 (ZMod 2)))

private theorem lred_autOnQuot_injective (hcover : AsA36NoOddCover) {G : Type} [Group G] [Finite G]
    {L W : Subgroup G} (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hsq : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G)) (hH : IsL345Type ↥(autOn L W)) :
    Function.Injective (S153D.autOnQuot hLN hker) := by
  have hcent := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
    (S153D.exists_autOnQuot_ne_one hLN hker hnt)
  have hodd : ∀ x ∈ (S153D.autOnQuot hLN hker).ker, Odd (orderOf x) := by
    intro x hx
    have hxc : x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := hcent hx
    by_contra hnodd
    obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.mp hnodd
    have hpos : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos
    have hc0 : 0 < c := by omega
    have hy2 : (x ^ c) ^ 2 ^ 1 = 1 := by
      rw [← pow_mul, pow_one]
      have : c * 2 = orderOf x := by omega
      rw [this, pow_orderOf_eq_one]
    have hy : x ^ c = 1 := S153D.eq_one_of_central_two_power (Subgroup.pow_mem _ hxc c) hy2
    have hd := Nat.le_of_dvd hc0 (orderOf_dvd_of_pow_eq_one hy)
    omega
  exact hcover _ _ hq hsq (S153D.autOnQuot hLN hker) (S153D.autOnQuot_surjective hLN hker) hodd hH

private theorem lred_inf_centralizer_eq {G : Type} [Group G] [Finite G] {L W : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hinj : Function.Injective (S153D.autOnQuot hLN hker)) :
    L ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 L := by
  refine le_antisymm (fun x hx => ?_) (le_inf (pCoreOf_le 2 L) hker)
  have h1 : S153D.autOnHom hLN ⟨x, hx.1⟩ = 1 :=
    (S153D.autOnHom_eq_one_iff hLN ⟨x, hx.1⟩).mpr hx.2
  have h2 : S153D.autOnQuot hLN hker (QuotientGroup.mk ⟨x, hx.1⟩) = 1 := h1
  have h3 : (QuotientGroup.mk ⟨x, hx.1⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
    hinj (h2.trans (map_one _).symm)
  have h4 : (⟨x, hx.1⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h3
  exact (S153D.mem_pCore_iff _).mp h4

private theorem lred_inf_centralizer_comm_eq {G : Type} [Group G] [Finite G] {UI L : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (UI : Set G)) (hperf : ⁅L, L⁆ = L)
    (hnt : ¬ L ≤ Subgroup.centralizer (UI : Set G))
    (hsimple : IsSimpleGroup ↥(autOn L UI))
    (hP1 : L ⊓ Subgroup.centralizer (UI : Set G) = pCoreOf 2 L) :
    L ⊓ Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G) = pCoreOf 2 L := by
  have hULle : ⁅UI, L⁆ ≤ UI := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hCle : Subgroup.centralizer (UI : Set G) ≤ Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hULle
  have hLNUL : L ≤ Subgroup.normalizer ((⁅UI, L⁆ : Subgroup G) : Set G) := fun g hg =>
    S153H.mem_normalizer_commutator (hLN hg) (Subgroup.le_normalizer hg)
  have hPle : pCoreOf 2 L ≤ L ⊓ Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G) :=
    hP1 ▸ inf_le_inf_left L hCle
  set ρ := S153D.autOnHom hLN with hρdef
  have hρ : Function.Surjective ρ := S153D.autOnHom_surjective hLN
  let Kc : Subgroup ↥L := (Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G)).subgroupOf L
  have hKcn : Kc.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (g : G) ∈ Subgroup.normalizer
        ((Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_centralizer hLNUL g.2
    have := (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp hx
    simpa using this
  have hKcN : (Kc.map ρ).Normal := hKcn.map ρ hρ
  rcases hsimple.eq_bot_or_eq_top_of_normal (Kc.map ρ) with hb | ht
  · refine le_antisymm (fun x hx => ?_) hPle
    have hxK : (⟨x, hx.1⟩ : ↥L) ∈ Kc := hx.2
    have h1 : ρ ⟨x, hx.1⟩ ∈ Kc.map ρ := Subgroup.mem_map_of_mem ρ hxK
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : x ∈ L ⊓ Subgroup.centralizer (UI : Set G) :=
      ⟨hx.1, (S153D.autOnHom_eq_one_iff hLN ⟨x, hx.1⟩).mp h1⟩
    rwa [hP1] at h2
  · exfalso
    have hLC : L ≤ Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G) := by
      intro l hl
      have h1 : ρ ⟨l, hl⟩ ∈ Kc.map ρ := by rw [ht]; trivial
      obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp h1
      have hk' : (k : G) ∈ Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G) := hk
      have h2 : ρ (k⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hkl, inv_mul_cancel]
      have h3 : ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ Subgroup.centralizer (UI : Set G) :=
        (S153D.autOnHom_eq_one_iff hLN _).mp h2
      have h4 := hCle h3
      have h5 : (k : G) * ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈
          Subgroup.centralizer ((⁅UI, L⁆ : Subgroup G) : Set G) := Subgroup.mul_mem _ hk' h4
      simpa using h5
    have hc1 : ⁅(⁅UI, L⁆ : Subgroup G), L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLC
    have hc2 : ⁅(⁅L, UI⁆ : Subgroup G), L⁆ = ⊥ := by rw [Subgroup.commutator_comm L UI]; exact hc1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hc2 hc1
    rw [hperf] at h3
    exact hnt (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)

private theorem lred_I_centralizer_le {G : Type} [Group G] [Finite G] {UL L I S : Subgroup G}
    (hIeq : I = L ⊔ S) (hS2 : IsPGroup 2 ↥S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hK : L ⊓ Subgroup.centralizer (UL : Set G) = pCoreOf 2 L)
    (hIUL : I ≤ Subgroup.normalizer (UL : Set G)) :
    I ⊓ Subgroup.centralizer (UL : Set G) ≤ pCoreOf 2 I := by
  have hD2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (UL : Set G)) := by
    rintro ⟨d, hdI, hdC⟩
    obtain ⟨e, he⟩ := InternalSec.two_of_sup hS2 hSL d (hIeq ▸ hdI)
    have hmem : d ^ 2 ^ e ∈ pCoreOf 2 L := hK ▸ ⟨he, Subgroup.pow_mem _ hdC _⟩
    obtain ⟨f, hf⟩ := pCoreOf_isPGroup 2 L ⟨d ^ 2 ^ e, hmem⟩
    refine ⟨e + f, Subtype.ext ?_⟩
    have := congrArg Subtype.val hf
    simpa [pow_add, pow_mul] using this
  have hID : I ≤ Subgroup.normalizer ((I ⊓ Subgroup.centralizer (UL : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B2F.le_normalizer_centralizer hIUL hg⟩
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hID hD2

private theorem lred_omegaOneCenter_le {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G}
    {t : G} (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

theorem input32Preamble_of_cover (hcover : AsA36NoOddCover) : Input32Preamble := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hsyl.2.1
  obtain ⟨hLc, hLM, -, -, hStarQ, hLQ⟩ := c25.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLleI : L ≤ I := le_of_mem_cComp hLI
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLN : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLleI.trans hIU
  have hUIc : UI153 T I ≤ centerOf (pCoreOf 2 I) :=
    (conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 c25.ctx.charTwo
      (lred_omegaOneCenter_le hh)).1
  have hOCUI : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hUIc hu).2 x hx).symm
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLleI)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hIL hg)) (pCoreOf_isPGroup 2 L)
  have hker : pCoreOf 2 L ≤ Subgroup.centralizer (UI153 T I : Set G) := hOL.trans hOCUI
  have hnt : ¬ L ≤ Subgroup.centralizer (UI153 T I : Set G) := fun h =>
    hLM (fun x hx => hF.cent_le ⟨hLleI hx, h hx⟩)
  have hsqI : SQTKGroup ↥I := sqtkGroup_of_pCoreOf_ne_bot hh.hyp.qtfe.qtke hh.hyp.qtfe.simple
    hh.hyp.qtfe.nonabelian c25.ctx.inH.1.2
  have hsq : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    S153D.sqtkGroup_quot_pCore (B5.sqtk_of_le hsqI hLleI)
  obtain ⟨e⟩ := c.c31
  obtain ⟨eA⟩ := lred_star_equiv_alt8 hLleI hIL hStarQ e
  have hH : IsL345Type ↥(autOn L (UI153 T I)) :=
    Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
      ⟨eA.trans lredAlt8EquivStatedSL⟩⟩)
  have hinj := lred_autOnQuot_injective hcover hLN hLQ hsq hker hnt hH
  have hP1 : L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L :=
    lred_inf_centralizer_eq hLN hker hinj
  have hsimpleA8 : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup ↥(autOn L (UI153 T I)) := eA.isSimpleGroup
  have hperfL : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hP4 : L ⊓ Subgroup.centralizer (UL153 T I L : Set G) = pCoreOf 2 L :=
    lred_inf_centralizer_comm_eq hLN hperfL hnt hsimple hP1
  have hIUL : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := S153H.I_le_normalizer_UL c
  have hD : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ pCoreOf 2 I :=
    lred_I_centralizer_le hIeq hS2 (hSI.trans hIL) hP4 hIUL
  have hOS : pCoreOf 2 I ≤ Sgp153 T V₁ := S153D.pCoreOf_le_Sgp153' hF
  have hULle : UL153 T I L ≤ UI153 T I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  unfold Preamble32
  refine ⟨hP1, le_antisymm (fun x hx => ⟨pCoreOf_le 2 I hx, Subgroup.centralizer_le hULle (hOCUI hx)⟩) hD, ?_⟩
  exact le_antisymm (fun x hx => ⟨hOS (hD hx), hx.2⟩) (inf_le_inf_right _ hSI)

end Mult

end CFSG.Quasithin
