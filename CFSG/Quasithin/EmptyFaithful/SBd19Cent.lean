module

public import CFSG.Quasithin.EmptyFaithful.SBd19Dc
public import CFSG.Quasithin.EmptyFaithful.SBd17I
public import CFSG.Quasithin.EmptyFaithful.SBd17Row
public import CFSG.Quasithin.EmptyFaithful.SBd17Quot
public import CFSG.Quasithin.EmptyFaithful.SBd17Syl
public import CFSG.Quasithin.EmptyFaithful.SBd17CentA
public import CFSG.Quasithin.EmptyFaithful.SBd17CentB
public import CFSG.Quasithin.EmptyFaithful.SBd16Main
public import CFSG.Quasithin.EmptyFaithful.SBd14Glue

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.centralizer_v_le_I_of_sylow_dc
    (r : RestHyp T Mc M V₁ V₂ Yp I L t)
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (hM : SBd19.M23NoDoubleCover) (hI : I = Subgroup.normalizer (V₁ : Set G))
    {v : G} (hv : v ∈ V₁) (hv1 : v ≠ 1)
    (hSyl : IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({v} : Set G))) :
    Subgroup.centralizer ({v} : Set G) ≤ I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := r.ctx.hyp
  have hq := hh.hyp.qtfe
  have D0 := r.ctx.hyp.decomp
  set S := Sgp153 T V₁ with hSdef
  set Hv : Subgroup G := Subgroup.centralizer ({v} : Set G) with hHv
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hLv : L ≤ Hv := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (r.h1 hv) x hx)
  have hv2 : v * v = 1 := r.V_sq v (D0.le₁ hv)
  have hvP : v ∈ pCoreOf 2 Hv := by
    have hord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers v) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hzH : Subgroup.zpowers v ≤ Hv := (Subgroup.zpowers_le).2
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have hnorm : Hv ≤ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
      intro g hg
      have hc : Commute g v := Subgroup.mem_centralizer_singleton_iff.mp hg
      refine Subgroup.centralizer_le_normalizer (s := ((Subgroup.zpowers v : Subgroup G) : Set G))
        (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (hc.zpow_right k).eq.symm
    exact le_pCoreOf_of_le_normalizer 2 hzH hnorm hz2 (Subgroup.mem_zpowers v)
  have hpC : pCoreOf 2 Hv ≠ ⊥ := by
    intro hb
    rw [hb] at hvP
    exact hv1 (Subgroup.mem_bot.mp hvP)
  have hLloc : quasithinIsLocal S L :=
    isLocal_of_mem_cComp_of_sylow r.ctx.facts.sylow r.ctx.inH.1.2 r.ctx.c33.mem
  have hB : L ∈ lFamily S := mem_lFamily_of_isLocal hLloc
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := r.S_le_L
  have hqk := hq.qtke
  obtain ⟨L', hL', hLL'⟩ := lemma_1_2_4_exists hqk hq.simple hq.nonabelian h37 h39 hpC hSyl hLv hB
  have hnorm : (L'.subgroupOf Hv).Normal :=
    lemma_1_2_4_normal hqk hq.simple hq.nonabelian h37 h38 hpC hSyl hB hLL' hL' hSL
  have hlist := lemma_1_2_4_list hqk hq.simple hq.nonabelian h312 hpC hSyl hLv hB hL' hLL'
  have hOS : pCoreOf 2 Hv ≤ S := pCoreOf_two_le_of_sylowIn hSyl.1 hSyl.2.1 hSyl.2.2
  have hΩ : pCoreOf 2 Hv ≤ V₁ := r.pCoreOf_le_V₁ h113 hLv hOS
  have hperf : Group.IsPerfect ↥L := r.ctx.c33.quasisimple.1
  have hker : (L ⊓ pCoreOf 2 Hv).subgroupOf L ≤ Subgroup.center ↥L := by
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 Hv := (Subgroup.mem_subgroupOf.mp hx).2
    have h2 : (x : G) ∈ centerOf L := hV₁ ▸ hΩ h1
    exact SBd9.mem_centerOf_iff.mp h2
  have hvL : v ∈ L := (r.V₁_le_L h113) hv
  have hker2 : 2 ≤ Nat.card ↥(L ⊓ pCoreOf 2 Hv) := by
    have hne : L ⊓ pCoreOf 2 Hv ≠ ⊥ := by
      intro hb
      have : v ∈ L ⊓ pCoreOf 2 Hv := ⟨hvL, hvP⟩
      rw [hb] at this
      exact hv1 (Subgroup.mem_bot.mp this)
    have := (Subgroup.one_lt_card_iff_ne_bot (L ⊓ pCoreOf 2 Hv)).mpr hne
    omega
  have hshape := SBd17.l34Row_modO2Image hLv hperf (r.card_center_L h113) r.hn2 hker hker2
  have hmono : modO2Image Hv L ≤ modO2Image Hv L' := Subgroup.map_mono (fun x hx => hLL' hx)
  have hHN : Hv ≤ Subgroup.normalizer (L : Set G) := by
    rcases hlist with heq | hcase | hnq
    · exact r.le_normalizer_of_modO2Image_eq hOS hL' hLL' hnorm heq
    · exfalso
      obtain ⟨hpsl, hm23⟩ := SBd17.row_l34_case hshape hmono hcase
      exact r.false_of_m23_dc h113 hM hLL' hL' (r.pCoreOf_eq_V₁_of_psl h113 hLv hΩ hpsl) hm23
    · exact (SBd17.row_l34_nonquasi hshape hmono hnq).elim
  rw [hI]
  exact le_normalizer_of_eq_center hHN hV₁

theorem RestHyp.centralizer_v_le_I_dc (r : RestHyp T Mc M V₁ V₂ Yp I L t)
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (hM : SBd19.M23NoDoubleCover) (hI : I = Subgroup.normalizer (V₁ : Set G))
    {v : G} (hv : v ∈ V₁) (hv1 : v ≠ 1) (hS : ∀ s ∈ Sgp153 T V₁, s * v = v * s) :
    Subgroup.centralizer ({v} : Set G) ≤ I := by
  have hCI : I ⊓ Subgroup.centralizer ({v} : Set G) = L ⊔ Sgp153 T V₁ :=
    r.centralizer_I_v h113 hv hv1 hS
  exact r.centralizer_v_le_I_of_sylow_dc h113 h37 h38 h39 h312 hM hI hv hv1
    (r.isSylowTwoOf_centralizer_v h113 hI hv hv1 hS hCI
      (fun H _ _ N _ hNc hN2 hch _ ht1 ht2 _ hKC hK =>
        SBd17.no_twoComponent_of_charTwo_quotient N hNc hN2 hch ht1 ht2 hKC hK)
      (fun Γ _ _ K _ hq' hZ hK2 => SBd17.isTwoComponent_of_normal_quasisimple hq' hZ hK2))

end CFSG.Quasithin.SBd14

namespace CFSG.Quasithin.SBd19

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem input15338CentV_of_m23_dc (h113 : StageLemma14113)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hM : M23NoDoubleCover) :
    SBd16.Input15338CentV := by
  intro h312 G _ _ T Mc M V₁ V₂ Yp I L t r hI v hv hv1
  obtain ⟨v₀, hv₀, hv₀1, hS⟩ := r.exists_v h113
  obtain ⟨m, hm, hmv⟩ := r.V₁_transitive h113 v₀ hv₀ hv₀1 v hv hv1
  have hmI : m ∈ I := by rw [hI]; exact hm
  intro g hg
  have hv₀eq : v₀ = m * v * m⁻¹ := by rw [← hmv]; group
  have hg' : m * g * m⁻¹ ∈ Subgroup.centralizer ({v₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hv₀eq]
    have hgv : g * v = v * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc m * g * m⁻¹ * (m * v * m⁻¹) = m * (g * v) * m⁻¹ := by group
      _ = m * (v * g) * m⁻¹ := by rw [hgv]
      _ = (m * v * m⁻¹) * (m * g * m⁻¹) := by group
  have h1 := r.centralizer_v_le_I_dc h113 h37 h38 h39 h312 hM hI hv₀ hv₀1 hS hg'
  have : g = m⁻¹ * (m * g * m⁻¹) * m := by group
  rw [this]
  exact I.mul_mem (I.mul_mem (I.inv_mem hmI) h1) hmI

end CFSG.Quasithin.SBd19
