module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenRootNormCtx
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6RootData
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Subtype
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6InnerPart

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Inclusion

variable {G : Type*} [Group G]

theorem ggQR_sup_eq_of_subtype {H : Subgroup G} {R' J₀' : Subgroup ↥H} {Q : Subgroup G}
    (hQ : Q = pCoreOf 2 (H ⊓ Subgroup.normalizer ((R'.map H.subtype : Subgroup G) : Set G)))
    (h1 : pCoreOf 2 (Subgroup.normalizer (R' : Set H)) ⊔ J₀' = ⊤) :
    Q ⊔ J₀'.map H.subtype = H := by
  have h := congrArg (Subgroup.map H.subtype) h1
  rw [Subgroup.map_sup, ggPCoreOf_normalizer_map_subtype, Subgroup.map_top,
    Subgroup.range_subtype] at h
  rw [hQ]
  exact h

theorem ggItemFour_of_subtype {H J : Subgroup G} (hJH : J ≤ H) {R' : Subgroup ↥H} {Q : Subgroup G}
    (hQ : Q = pCoreOf 2 (H ⊓ Subgroup.normalizer ((R'.map H.subtype : Subgroup G) : Set G)))
    (h4 : ∀ Q' : Subgroup ↥H, Q' = pCoreOf 2 (Subgroup.normalizer (R' : Set H)) →
      ∀ U : Subgroup ↥H, (Subgroup.center ↥Q').map Q'.subtype ≤ U → U ≤ Q' →
        U ≠ (Subgroup.center ↥Q').map Q'.subtype → U ≠ Q' →
        Subgroup.normalizer (R' : Set H) ≤ Subgroup.normalizer (U : Set H) →
        J.subgroupOf H ⊔ U = ⊤) :
    ∀ U : Subgroup G, (Subgroup.center ↥Q).map Q.subtype ≤ U → U ≤ Q →
      U ≠ (Subgroup.center ↥Q).map Q.subtype → U ≠ Q →
      H ⊓ Subgroup.normalizer ((R'.map H.subtype : Subgroup G) : Set G) ≤
        Subgroup.normalizer (U : Set G) →
      J ⊔ U = H := by
  intro U
  have hι : Function.Injective H.subtype := Subgroup.subtype_injective H
  have hQ' : Q = (pCoreOf 2 (Subgroup.normalizer (R' : Set H))).map H.subtype :=
    hQ.trans (ggPCoreOf_normalizer_map_subtype H R').symm
  have hcen :=
    ggCenter_map_map_of_injective H.subtype hι (pCoreOf 2 (Subgroup.normalizer (R' : Set H)))
  subst hQ'
  intro hZU hUQ hUZ hUQne hN
  have hUH : U ≤ H := by
    refine hUQ.trans ?_
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hU'map : (U.subgroupOf H).map H.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUH
  have h1 : (Subgroup.center ↥(pCoreOf 2 (Subgroup.normalizer (R' : Set H)))).map
      (pCoreOf 2 (Subgroup.normalizer (R' : Set H))).subtype ≤ U.subgroupOf H := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, hU'map, ← hcen]
    exact hZU
  have h2 : U.subgroupOf H ≤ pCoreOf 2 (Subgroup.normalizer (R' : Set H)) := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, hU'map]
    exact hUQ
  have h3 : U.subgroupOf H ≠
      (Subgroup.center ↥(pCoreOf 2 (Subgroup.normalizer (R' : Set H)))).map
        (pCoreOf 2 (Subgroup.normalizer (R' : Set H))).subtype := by
    intro heq
    apply hUZ
    rw [hcen, ← heq, hU'map]
  have h4' : U.subgroupOf H ≠ pCoreOf 2 (Subgroup.normalizer (R' : Set H)) := by
    intro heq
    apply hUQne
    rw [← heq, hU'map]
  have h5 : Subgroup.normalizer (R' : Set H) ≤
      Subgroup.normalizer ((U.subgroupOf H : Subgroup H) : Set H) := by
    intro n hn
    have hnR : H.subtype n ∈ Subgroup.normalizer ((R'.map H.subtype : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ hn)
    have hnU : H.subtype n ∈ Subgroup.normalizer (U : Set G) := hN ⟨n.2, hnR⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp hnU (H.subtype u)
    simpa using this
  have h6 := h4 _ rfl (U.subgroupOf H) h1 h2 h3 h4' h5
  have h7 := congrArg (Subgroup.map H.subtype) h6
  rw [Subgroup.map_sup, hU'map, Subgroup.map_subgroupOf_eq_of_le hJH, Subgroup.map_top,
    Subgroup.range_subtype] at h7
  exact h7

theorem ggRootNormData_of_subtype {H K : Subgroup G} (hKH : K ≤ H) {R' : Subgroup ↥H}
    {P : G → Prop} {P' : ↥H → Prop} (hP : ∀ δ : ↥H, P' δ → P (δ : G))
    (h : GGRootNormNoCentral (R'.subgroupOf (K.subgroupOf H)) ∧
      (GGRootNormInner (R'.subgroupOf (K.subgroupOf H)) ∨
        ∃ δ : ↥(Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H)),
          P' (δ : ↥H) ∧ (δ : ↥H) ∈ Subgroup.normalizer (R' : Set ↥H) ∧
            GGRootNormInnerDiag (R'.subgroupOf (K.subgroupOf H))
              ((K.subgroupOf H).normalizerMonoidHom δ))) :
    GGRootNormNoCentral ((R'.map H.subtype).subgroupOf K) ∧
      (GGRootNormInner ((R'.map H.subtype).subgroupOf K) ∨
        ∃ δ : ↥(Subgroup.normalizer (K : Set G)),
          (δ : G) ∈ H ∧ P (δ : G) ∧
            (δ : G) ∈ Subgroup.normalizer ((R'.map H.subtype : Subgroup G) : Set G) ∧
              GGRootNormInnerDiag ((R'.map H.subtype).subgroupOf K) (K.normalizerMonoidHom δ)) := by
  obtain ⟨hNC, hI⟩ := h
  have hι : Function.Injective H.subtype := Subgroup.subtype_injective H
  have hK : (K.subgroupOf H).map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  refine ⟨ggRootNormNoCentral_of_map_injective H.subtype hι hK rfl hNC, ?_⟩
  rcases hI with hI | ⟨δ, hδP, hδR, hδ⟩
  · exact Or.inl (ggRootNormInner_of_map_injective H.subtype hι hK rfl hI)
  · right
    have hδN : H.subtype (δ : ↥H) ∈ Subgroup.normalizer (K : Set G) := by
      have h1 : H.subtype (δ : ↥H) ∈
          (Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype :=
        Subgroup.mem_map_of_mem _ δ.2
      have h2 := Subgroup.le_normalizer_map H.subtype h1
      rwa [hK] at h2
    refine ⟨⟨H.subtype (δ : ↥H), hδN⟩, (δ : ↥H).2, hP _ hδP, ?_, ?_⟩
    · exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ hδR)
    · exact ggRootNormInnerDiag_of_map_injective H.subtype hι hK rfl rfl hδ

end Inclusion

section Main

theorem ggSixLSixSevenCentJE6Input_of_rootData (h64 : GGSixCentreOddInput)
    (h : GGSixE6A24RootData) : GGSixLSixSevenCentJE6Input := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC2 hodd hcomp hE
  obtain ⟨rfl, rfl, rfl, hL6, hJ3⟩ := hE
  have hlie := hctx.lieModel
  have hn : n = 0 := ggLieModel_E6_n_eq_zero hlie
  subst hn
  obtain ⟨hZtriv, hmain⟩ := h ↥(ggG0 3 B x L D J) hctx.perfect hlie
  have hZ1 : ∀ y ∈ ggG0 3 B x L D J, y ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G) →
      y = 1 := by
    intro y hy hyc
    have hmem : (⟨y, hy⟩ : ↥(ggG0 3 B x L D J)) ∈ Subgroup.center ↥(ggG0 3 B x L D J) := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc (z : G) z.2)
    rw [hZtriv, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hinner : ∀ b ∈ Bs, ∃ (c : G) (g : ↥(ggG0 3 B x L D J)),
      c ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G) ∧ b = c * (g : G) := by
    intro b hb
    obtain ⟨g, hg, hcg⟩ := ggPsiInnerDiag_E6_two_exists_centralizing ψ hctx.2.2.2.2.1.2
      (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hctx.range_eq] at hg hcg
    exact ⟨b * g, ⟨g⁻¹, inv_mem hg⟩, hcg, by simp⟩
  have hxB : x ∈ B := hctx.sstar.2.1
  have hxBs : x ∈ Bs := hctx.bstar.1 hxB
  obtain ⟨cx, x₀, hcx, hxeq⟩ := hinner x hxBs
  have hx₀3 : x₀ ^ 3 = 1 :=
    ggPow_eq_one_of_mul_centralizer hZ1 hcx (by rw [← hxeq]; exact hctx.bstar.2.1.2 x hxBs)
  have hLG₀ : L ≤ ggG0 3 B x L D J := le_sup_left
  have hJG₀ : J ≤ ggG0 3 B x L D J := hctx.le_ggG0
  have hL'comp : IsComponentOf (L.subgroupOf (ggG0 3 B x L D J))
      (Subgroup.centralizer {x₀}) := by
    have h1 := ggIsComponentOf_subgroupOf_of_le (ggG0 3 B x L D J) hLG₀ hctx.sstar.2.2.2.1
    have h2 := ggCentralizer_singleton_subgroupOf hcx x₀
    rw [← hxeq] at h2
    rw [h2] at h1
    exact h1
  have hL'6 : LieModel (↥(L.subgroupOf (ggG0 3 B x L D J)) ⧸
      Subgroup.center ↥(L.subgroupOf (ggG0 3 B x L D J))) .PSL 6 2 1 :=
    ggLieModel_centerQuot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG₀) hL6
  have hJL' : J.subgroupOf (ggG0 3 B x L D J) ≤ L.subgroupOf (ggG0 3 B x L D J) :=
    Subgroup.subgroupOf_mono _ (hctx.j_le_inf.trans inf_le_left)
  have hJqs : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf (ggG0 3 B x L D J)) :=
    ggIsQuasisimple_subgroupOf hJG₀ hctx.stdSub.1.2.2.2.2.2.1.2.2
  have hJ'3 : LieModel (↥(J.subgroupOf (ggG0 3 B x L D J)) ⧸
      Subgroup.center ↥(J.subgroupOf (ggG0 3 B x L D J))) .PSL 3 2 2 :=
    ggLieModel_centerQuot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJG₀) hJ3
  obtain ⟨R', J₀', hR'J', hR'1, hR'2, hJ₀'J', h1, h4, h3, h2⟩ :=
    hmain x₀ _ _ hx₀3 hL'comp hL'6 hJL' hJqs hJ'3
  have hι : Function.Injective (ggG0 3 B x L D J).subtype := Subgroup.subtype_injective _
  have hJ'J : (J.subgroupOf (ggG0 3 B x L D J)).map (ggG0 3 B x L D J).subtype = J :=
    Subgroup.map_subgroupOf_eq_of_le hJG₀
  have hRJ : R'.map (ggG0 3 B x L D J).subtype ≤ J :=
    (Subgroup.map_mono hR'J').trans hJ'J.le
  have hR1 : R'.map (ggG0 3 B x L D J).subtype ≠ ⊥ := by
    intro hbot
    exact hR'1 ((Subgroup.map_eq_bot_iff_of_injective R' hι).mp hbot)
  have hR2 : IsPGroup 2 (R'.map (ggG0 3 B x L D J).subtype) := hR'2.map _
  have hJ₀J : J₀'.map (ggG0 3 B x L D J).subtype ≤ J :=
    (Subgroup.map_mono hJ₀'J').trans hJ'J.le
  have hgen : ggQR 3 B x L D J (R'.map (ggG0 3 B x L D J).subtype) ⊔
      J₀'.map (ggG0 3 B x L D J).subtype = ggG0 3 B x L D J :=
    ggQR_sup_eq_of_subtype rfl h1
  have h4' := ggItemFour_of_subtype hJG₀ rfl h4
  have hI₀ : GGRootNormInner
      ((R'.map (ggG0 3 B x L D J).subtype).subgroupOf (ggG0 3 B x L D J)) := by
    have hsub : (R'.map (ggG0 3 B x L D J).subtype).subgroupOf (ggG0 3 B x L D J) = R' :=
      Subgroup.comap_map_eq_self_of_injective hι R'
    rw [hsub]
    exact h3
  obtain ⟨hZJ, hZK⟩ := h64 G 3 B Bs x L D J .E6 0 1 ψ hctx hodd
  refine hctx.centralizer_le_ggM_of_rootNorm hodd hZJ hZK hcomp hRJ hR1 hR2 hJ₀J hgen h4' hI₀ ?_
  intro d hd hd1
  have hdBs : d ∈ Bs := hctx.d_le_bstar hd
  have hd3 : d ^ 3 = 1 := hctx.bstar.2.1.2 d hdBs
  obtain ⟨cd, g, hcd, hdeq⟩ := hinner d hdBs
  have hg3 : g ^ 3 = 1 :=
    ggPow_eq_one_of_mul_centralizer hZ1 hcd (by rw [← hdeq]; exact hd3)
  have hg1 : g ≠ 1 := by
    intro hg
    have hdc : d ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G) := by
      rw [hdeq, hg, Subgroup.coe_one, mul_one]
      exact hcd
    have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    have hdvd : orderOf (⟨d, hdc⟩ : Subgroup.centralizer (ggG0 3 B x L D J : Set G)) ∣
        Nat.card (Subgroup.centralizer (ggG0 3 B x L D J : Set G)) := orderOf_dvd_natCard _
    have hordmk : orderOf (⟨d, hdc⟩ : Subgroup.centralizer (ggG0 3 B x L D J : Set G)) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hord
    rw [hordmk] at hdvd
    exact not_dvd_card_centralizer_ggG0_of_stdSub hctx.prime hctx.sstar hctx.stdType
      hctx.stdSub hdvd
  have hdx : d * x = x * d :=
    congrArg Subtype.val (hctx.bstar.2.1.1.is_comm.comm (⟨d, hdBs⟩ : ↥Bs) ⟨x, hxBs⟩)
  have hcomm : (cd * (g : G)) * (cx * (x₀ : G)) = (cx * (x₀ : G)) * (cd * (g : G)) := by
    rw [← hdeq, ← hxeq]
    exact hdx
  have hgx : g ∈ Subgroup.centralizer ({x₀} : Set ↥(ggG0 3 B x L D J)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ggCommute_of_commute_mul_centralizer hZ1 hcx hcd hcomm
  have hgJ : g ∈ Subgroup.centralizer
      ((J.subgroupOf (ggG0 3 B x L D J) : Subgroup ↥(ggG0 3 B x L D J)) :
        Set ↥(ggG0 3 B x L D J)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjJ : (j : G) ∈ J := hj
    have e1 : (j : G) * d = d * (j : G) :=
      Subgroup.mem_centralizer_iff.mp (hctx.le_centralizer_J hd) (j : G) hjJ
    have e2 : (j : G) * cd = cd * (j : G) :=
      Subgroup.mem_centralizer_iff.mp hcd (j : G) j.2
    apply Subtype.ext
    have e3 : cd * ((j : G) * (g : G)) = cd * ((g : G) * (j : G)) := by
      calc cd * ((j : G) * (g : G)) = (cd * (j : G)) * (g : G) := by rw [mul_assoc]
        _ = ((j : G) * cd) * (g : G) := by rw [e2]
        _ = (j : G) * (cd * (g : G)) := by rw [mul_assoc]
        _ = (j : G) * d := by rw [← hdeq]
        _ = d * (j : G) := e1
        _ = (cd * (g : G)) * (j : G) := by rw [← hdeq]
        _ = cd * ((g : G) * (j : G)) := by rw [mul_assoc]
    exact mul_left_cancel e3
  have hKG₀ : ggKd 3 B x L D J d ≤ ggG0 3 B x L D J := hctx.ggKd_le_ggG0 hd
  have hJK : J ≤ ggKd 3 B x L D J d := le_ggKd 3 B x L D J d
  have hKcomp : IsComponentOf (ggKd 3 B x L D J d) (Subgroup.centralizer {d}) :=
    hcomp d hd hd1
  have hcentd : (Subgroup.centralizer ({d} : Set G)).subgroupOf (ggG0 3 B x L D J) =
      Subgroup.centralizer {g} := by
    have := ggCentralizer_singleton_subgroupOf hcd g
    rwa [← hdeq] at this
  have hK'comp : IsComponentOf ((ggKd 3 B x L D J d).subgroupOf (ggG0 3 B x L D J))
      (Subgroup.centralizer {g}) := by
    have := ggIsComponentOf_subgroupOf_of_le (ggG0 3 B x L D J) hKG₀ hKcomp
    rwa [hcentd] at this
  have hJK' : J.subgroupOf (ggG0 3 B x L D J) ≤
      (ggKd 3 B x L D J d).subgroupOf (ggG0 3 B x L D J) :=
    Subgroup.subgroupOf_mono _ hJK
  have hmain2 := h2 g hg3 hg1 hgx hgJ _ hJK' hK'comp
  refine ggRootNormData_of_subtype hKG₀ (P := fun y => y ∈ Subgroup.centralizer {d})
    (P' := fun y => y ∈ Subgroup.centralizer {g}) ?_ hmain2
  intro δ hδ
  rw [Subgroup.mem_centralizer_singleton_iff] at hδ ⊢
  have e2 : (δ : G) * cd = cd * (δ : G) :=
    Subgroup.mem_centralizer_iff.mp hcd (δ : G) δ.2
  have e4 : (δ : G) * (g : G) = (g : G) * (δ : G) := congrArg Subtype.val hδ
  calc (δ : G) * d = (δ : G) * (cd * (g : G)) := by rw [← hdeq]
    _ = ((δ : G) * cd) * (g : G) := by rw [mul_assoc]
    _ = (cd * (δ : G)) * (g : G) := by rw [e2]
    _ = cd * ((δ : G) * (g : G)) := by rw [mul_assoc]
    _ = cd * ((g : G) * (δ : G)) := by rw [e4]
    _ = (cd * (g : G)) * (δ : G) := by rw [mul_assoc]
    _ = d * (δ : G) := by rw [← hdeq]

end Main

end CFSG.StandardType
