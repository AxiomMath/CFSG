module

public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S152FinConj
public import CFSG.Quasithin.EmptyFaithful.S152FinMain
public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.Quasithin.Background.B2FactorizationR2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem thompsonJ_isWeaklyClosedIn [Finite G] (T : Subgroup G) : IsWeaklyClosedIn (thompsonJ T) T := by
  intro g hg
  have hconj : ∀ A : Subgroup G, conjSubgroup A g = cjSub g⁻¹ A := fun _ => rfl
  have hcard : Nat.card (cjSub g⁻¹ (thompsonJ T)) = Nat.card (thompsonJ T) := card_cjSub _ _
  rw [hconj] at hg ⊢
  have hle : cjSub g⁻¹ (thompsonJ T) ≤ thompsonJ T := by
    unfold cjSub
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hAJ : A ≤ thompsonJ T :=
      le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) A hA
    have hAT : cjSub g⁻¹ A ≤ T := (cjSub_mono hAJ).trans hg
    have hmax : IsMaxElemAbelian T (cjSub g⁻¹ A) :=
      ⟨hAT, isElemAbelian_cjSub hA.2.1, fun B hBT hB => (hA.2.2 B hBT hB).trans (card_cjSub _ _).ge⟩
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) _ hmax
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem zSOf_le_V154 [Finite G] (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) :
    zSOf T Mc M B₀ ≤ V154 T Mc M := by
  refine (S152Fin.commutator_le_of_le_normalizer ?_)
  intro y hy
  obtain ⟨hyM, hyN⟩ := hy
  obtain ⟨z, -, rfl⟩ := hyN
  exact z.2

theorem centralizer_le_of_isUniqueM_zs [Finite G] {Mc ZS : Subgroup G}
    (hU : IsUniqueM (Mc ⊓ Subgroup.centralizer (ZS : Set G)) Mc) {z : G} (hzZ : z ∈ ZS)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : Subgroup.centralizer ({z} : Set G) ≤ Mc := by
  have hP : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]; norm_num)
  have hne : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    exact hz1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers z))
  have hloc : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :=
    ⟨Subgroup.zpowers z, hne, hP, rfl⟩
  obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
  have hCz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hcz : z * c = c * z := Subgroup.mem_centralizer_iff.1 hc z rfl
    exact ((Commute.zpow_left (show Commute z c from hcz) k).eq)
  have hMK : Mc ⊓ Subgroup.centralizer (ZS : Set G) ≤ K := by
    refine (inf_le_right.trans ?_).trans hle
    refine (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)).trans hCz
  exact hCz.trans (hU.2 K ⟨hK, hMK⟩ ▸ hle)

theorem centralizer_le_Mc_of_mem_zS [Finite G] {T Mc M : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))}
    (hU : IsUniqueM (Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) Mc) {z : G}
    (hzZ : z ∈ zSOf T Mc M B₀) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Mc :=
  centralizer_le_of_isUniqueM_zs hU hzZ hz2 hz1

@[expose] def Lemma15227Three [Finite G] (T Mc M : Subgroup G)
    (B₀ : Subgroup (MulAut (V154 T Mc M))) : Prop :=
  ∀ g : G, zSOf T Mc M B₀ ⊓ conjSub g (V154 T Mc M) ≠ ⊥ →
    ⁅V154 T Mc M, conjSub g (V154 T Mc M)⁆ = ⊥

theorem lemma15227_three_of [Finite G] {T Mc M : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))}
    (hs : Setting152 T Mc M) (h1519 : Lemma1519Concl T Mc M)
    (hU : IsUniqueM (Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) Mc)
    (hw0 : E3.wClos (V154 T Mc M) 0 T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
    (hV₂ : IsElemAbelian 2 (V154 T Mc M)) (hVc : V154 T Mc M ≤ pCoreOf 2 Mc) :
    Lemma15227Three T Mc M B₀ := by
  intro g hg
  obtain ⟨S, rfl⟩ := hs.qtfe.exists_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTMc : (S : Subgroup G) ≤ Mc := hs.qtfe.t_le_mc
  have hZV := zSOf_le_V154 (S : Subgroup G) Mc M B₀
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hg
  have hzZ : (a : G) ∈ zSOf (S : Subgroup G) Mc M B₀ := (Subgroup.mem_inf.1 a.2).1
  have hzg : (a : G) ∈ conjSub g (V154 (S : Subgroup G) Mc M) := (Subgroup.mem_inf.1 a.2).2
  have hz1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hz2 : (a : G) ^ 2 = 1 := hV₂.2 _ (hZV hzZ)
  have hyV : g⁻¹ * (a : G) * g ∈ V154 (S : Subgroup G) Mc M := mem_conjSub.1 hzg
  have hJT : thompsonJ (S : Subgroup G) ≤ S := thompsonJ_le_self151 _
  have hVC : V154 (S : Subgroup G) Mc M ≤
      Subgroup.centralizer (thompsonJ (S : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1519.one_commute
  obtain ⟨n, hn, hnz⟩ := burnside_fusion_lemma_centralizer S hJT
    (thompsonJ_isWeaklyClosedIn (S : Subgroup G)) (hVC (hZV hzZ)) (hVC hyV) (g := g) rfl
  have hnM : n ∈ M :=
    h1519.one_cgs ((S1414.normalizer_thompsonJ_le_CGS hs.qtfe.sylow.1 hs.qtfe.ne_bot) hn)
  have hnV : n ∈ Subgroup.normalizer (V154 (S : Subgroup G) Mc M : Set G) :=
    le_normalizer_V154 _ Mc M hnM
  have hcz : (g * n⁻¹)⁻¹ * (a : G) * (g * n⁻¹) = (a : G) := by
    calc (g * n⁻¹)⁻¹ * (a : G) * (g * n⁻¹) = n * (g⁻¹ * (a : G) * g) * n⁻¹ := by group
      _ = n * (n⁻¹ * (a : G) * n) * n⁻¹ := by rw [hnz]
      _ = (a : G) := by group
  have hcMc : g * n⁻¹ ∈ Mc := by
    refine centralizer_le_Mc_of_mem_zS hU hzZ hz2 hz1 ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    calc (a : G) * (g * n⁻¹) = (g * n⁻¹) * ((g * n⁻¹)⁻¹ * (a : G) * (g * n⁻¹)) := by group
      _ = (g * n⁻¹) * (a : G) := by rw [hcz]
  have hgc : conjSub g (V154 (S : Subgroup G) Mc M) =
      conjSub (g * n⁻¹) (V154 (S : Subgroup G) Mc M) := by
    have hg' : g = (g * n⁻¹) * n := by group
    conv_lhs => rw [hg', conjSub_mul, F7.conjSub_eq_of_mem_normalizer hnV]
  have hcV : conjSub (g * n⁻¹) (V154 (S : Subgroup G) Mc M) ≤ S :=
    (conjSub_mono _ hVc).trans (((S152Fin.conjSub_pCoreOf_of_mem hcMc).le).trans
      (pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le151 hs.qtfe.sylow hTMc)))
  have hcw := (S152Fin.conjSub_le_wClos_zero (V := V154 (S : Subgroup G) Mc M) (g * n⁻¹) hcV).trans hw0
  rw [hgc, Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hcw.trans inf_le_right)

@[expose] def StageLemma15227Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    V154 T Mc M ≤ pCoreOf 2 Mc

end CFSG.Quasithin
