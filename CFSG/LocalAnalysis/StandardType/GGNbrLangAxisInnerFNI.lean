module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisCases
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeASixNonSplit
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
import CFSG.LocalAnalysis.StandardType.GGKGroupFusionBridge
import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrLangAxisInnerFNIAux_centerQuotEquiv
    {A B : Type*} [Group A] [Group B] (f : A →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center A) (hperf : commutator A = ⊤) :
    ∃ e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B,
      ∀ a : A, e (a : A ⧸ Subgroup.center A) = (f a : B ⧸ Subgroup.center B) := by
  haveI : Group.IsPerfect A := ⟨hperf⟩
  exact ⟨CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hf hker, fun _ => rfl⟩

private theorem ggNbrLangAxisInnerFNIAux_kgInducedAut_mk {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) (k : K) :
    kgInducedAut θ α (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k)) := by
  change (MulAut.congr θ) ((centerQuotAut K) α) (θ (QuotientGroup.mk k)) = _
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, centerQuotAut_mk]

theorem ggNbrLangAxisInnerOn_open_notT3 (hsub : GGNbrSubcomponentInput)
    (hLID : GGBstarInnerDiagLInputOn fun _ _ => True) (hQ1 : GGBstarInnerDiagJInput)
    (hFNI : KGFieldNotInnerInput) :
    GGNbrLangAxisInnerOn fun p lab =>
      GGNbrLangRest12NonRegOpenLabel p lab ∧ ¬ GGNbrLangT3Label p lab := by
  intro G _ _ p B Bs x L D J hcfg y K hnbr hN P hMark
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hM := largeEvenMarking_and_labelAll_simple_imp
      (S := fun lab => GGNbrLangRest12NonRegOpenLabel p lab ∧ ¬ GGNbrLangT3Label p lab)
      (P' := KGFieldNotInnerCont p)
      (fun lab hlab hS => LargeEvenLabelAll.mono (fun R _ I F h _ _ => h)
        (hFNI p lab hp hp2 hlab hS.2)) hMark
  refine largeEvenMarking_mono ?_ hM
  rintro lab R _ I F θ ⟨hP, hSfni⟩
  refine ⟨hP, ?_⟩
  intro hS hxin hall b₀ hb₀ hb₀I
  exfalso
  have hI : GGThmIHyp p B x L := hcfg.1
  have hBstar : GGBstar p B Bs := hcfg.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hSstar : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hSstar.2.1
  have hBBs : B ≤ Bs := hBstar.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hxpow : x ^ p = 1 := hBstar.2.1.2 x hxBs
  have hBsab : IsElemAbelian p Bs := hBstar.2.1
  have hJK : J ≤ K := hsub G p B x L D J hI hDJ y K hnbr
  have hJc : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSstar hDJ hnbr hJK
  have hLid : GGInnerDiagOn Bs L :=
    (hLID G p B Bs x L D J hcfg
      (ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hI)).innerDiagOn
  have hJid : GGInnerDiagOn Bs J := hQ1 G p B Bs x L D J hcfg hLid
  obtain ⟨hJperf, labJ, hlabJ, hrawJ⟩ := hJid
  obtain ⟨RJ, _, IJ, FJ, -, -, θJ, hPJ⟩ := largeEvenRawDatum_exists hrawJ
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := hPJ.1
  have hb₀J : b₀ ∈ Subgroup.normalizer (J : Set G) := hBsJ hb₀
  have hFNIc : KGFieldNotInnerCont p R I F := hSfni hS
  have hαpow : (ggLAut K θ ⟨b₀, hN hb₀⟩) ^ p = 1 :=
    ggLAut_pow_eq_one_of_pow K θ (hN hb₀) (hBsab.2 b₀ hb₀)
  have hhpow : (ggLAut K θ ⟨x, hN hxBs⟩) ^ p = 1 :=
    ggLAut_pow_eq_one_of_pow K θ (hN hxBs) hxpow
  have hcomm : ggLAut K θ ⟨x, hN hxBs⟩ * ggLAut K θ ⟨b₀, hN hb₀⟩ =
      ggLAut K θ ⟨b₀, hN hb₀⟩ * ggLAut K θ ⟨x, hN hxBs⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show x * b₀ = b₀ * x
    exact congrArg Subtype.val (hBsab.1.is_comm.comm ⟨x, hxBs⟩ ⟨b₀, hb₀⟩)
  set ρ : ↥K →* R := (θ : ↥K ⧸ Subgroup.center ↥K →* R).comp
    (QuotientGroup.mk' (Subgroup.center ↥K)) with hρdef
  set J₀ : Subgroup R := (J.subgroupOf K).map ρ with hJ₀def
  have hρker : ρ.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    change θ (k : ↥K ⧸ Subgroup.center ↥K) = 1 ↔ k ∈ Subgroup.center ↥K
    rw [← map_one θ, θ.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hρsurj : Function.Surjective ρ := fun r => by
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨k, hq⟩
  have hmap : ∀ (g : Subgroup.normalizer (K : Set G)) (k : ↥K),
      ggLAut K θ g (ρ k) = ρ (K.normalizerMonoidHom g k) := by
    intro g k
    change ggLAut K θ g (θ (k : ↥K ⧸ Subgroup.center ↥K)) =
      θ (K.normalizerMonoidHom g k : ↥K ⧸ Subgroup.center ↥K)
    rw [ggLAut_apply]
  let ρJ : ↥J →* ↥J₀ :=
    { toFun := fun j => ⟨ρ (Subgroup.inclusion hJK j), by
        rw [hJ₀def]
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJK j,
          Subgroup.mem_subgroupOf.mpr j.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hρJsurj : Function.Surjective ρJ := by
    intro b
    obtain ⟨k, hk, hkρ⟩ := Subgroup.mem_map.mp (by rw [← hJ₀def]; exact b.2)
    rw [Subgroup.mem_subgroupOf] at hk
    exact ⟨⟨k, hk⟩, Subtype.ext hkρ⟩
  have hkerJ : ρJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    have hjZ : Subgroup.inclusion hJK j ∈ Subgroup.center ↥K := by
      have h2 : ρ (Subgroup.inclusion hJK j) = 1 := by
        have := congrArg (fun q : ↥J₀ => (q : R)) hj
        simpa [ρJ] using this
      have h2' : Subgroup.inclusion hJK j ∈ ρ.ker := h2
      rwa [hρker] at h2'
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hc := congrArg (fun z : ↥K => (z : G)) (Subgroup.mem_center_iff.mp hjZ
      (Subgroup.inclusion hJK y))
    simpa using hc
  obtain ⟨e, he⟩ := ggNbrLangAxisInnerFNIAux_centerQuotEquiv ρJ hρJsurj hkerJ hJperf
  have hJ₀comp : CFSG.Assembly.IsComponentOf J₀ (MonoidHom.eqLocus
      (ggLAut K θ ⟨x, hN hxBs⟩ : R →* R) (MonoidHom.id R)) := by
    have hfixK : (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
        ggFix (K.normalizerMonoidHom ⟨x, hN hxBs⟩) := by
      ext k
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_ggFix]
      constructor
      · rintro ⟨-, hk⟩
        apply Subtype.ext
        rw [normalizerMonoidHom_coe]
        have hkC : (k : G) * x = x * (k : G) := Subgroup.mem_centralizer_singleton_iff.mp hk
        calc x * (k : G) * x⁻¹ = (k : G) * x * x⁻¹ := by rw [← hkC]
          _ = (k : G) := by group
      · intro hk
        refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h2 := congrArg Subtype.val hk
        rw [normalizerMonoidHom_coe] at h2
        calc (k : G) * x = (x * (k : G) * x⁻¹) * x := by rw [h2]
          _ = x * (k : G) := by group
    have hJs := ggIsComponentOf_subgroupOf hJc inf_le_left
    rw [hfixK] at hJs
    have hc : ∀ k : ↥K, ggLAut K θ ⟨x, hN hxBs⟩ (ρ k) =
        ρ (K.normalizerMonoidHom ⟨x, hN hxBs⟩ k) := fun k => hmap _ k
    have h := USixTwo.isComponentOf_map_fix hρsurj (le_of_eq hρker) hc hJs
    rw [← hJ₀def] at h
    exact h
  have hαJ₀ : ∀ r ∈ J₀, ggLAut K θ ⟨b₀, hN hb₀⟩ r ∈ J₀ := by
    intro r hr
    rw [hJ₀def, Subgroup.mem_map] at hr ⊢
    obtain ⟨k, hk, rfl⟩ := hr
    rw [Subgroup.mem_subgroupOf] at hk
    refine ⟨K.normalizerMonoidHom ⟨b₀, hN hb₀⟩ k, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp hb₀J (k : G)).mp hk
    · exact (hmap ⟨b₀, hN hb₀⟩ k).symm
  have hαinvJ₀ : ∀ r ∈ J₀, (ggLAut K θ ⟨b₀, hN hb₀⟩)⁻¹ r ∈ J₀ := by
    intro r hr
    rw [hJ₀def, Subgroup.mem_map] at hr ⊢
    obtain ⟨k, hk, rfl⟩ := hr
    rw [Subgroup.mem_subgroupOf] at hk
    refine ⟨K.normalizerMonoidHom ⟨b₀⁻¹, hN (Bs.inv_mem hb₀)⟩ k, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (J : Set G)).inv_mem hb₀J) (k : G)).mp hk
    · rw [← map_inv]
      exact (hmap ⟨b₀⁻¹, hN (Bs.inv_mem hb₀)⟩ k).symm
  let α' : MulAut ↥J₀ :=
    { toFun := fun j => ⟨ggLAut K θ ⟨b₀, hN hb₀⟩ j, hαJ₀ j j.2⟩
      invFun := fun j => ⟨(ggLAut K θ ⟨b₀, hN hb₀⟩)⁻¹ j, hαinvJ₀ j j.2⟩
      left_inv := fun j => Subtype.ext (by simp)
      right_inv := fun j => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hKG := hFNIc (ggLAut K θ ⟨b₀, hN hb₀⟩) (hall b₀ hb₀) hb₀I hαpow
      (ggLAut K θ ⟨x, hN hxBs⟩) (hxin hxBs) hhpow hcomm J₀ hJ₀comp α' (fun j => rfl)
  have hP₀ : LargeEvenMarking ↥J₀ (fun _ R' _ I' F' θ' => kgInducedAut θ' α' ∈ I') := by
    refine ⟨?_, labJ, hlabJ, largeEvenRawDatum_mono ?_ hrawJ⟩
    · haveI : Group.IsPerfect ↥J := ⟨hJperf⟩
      exact (Group.IsPerfect.ofSurjective (f := ρJ) hρJsurj).commutator_eq_top
    · rintro R' _ I' F' ⟨hs, hna, θJ', hPJ'⟩
      refine ⟨hs, hna, e.symm.trans θJ', ?_⟩
      obtain ⟨φ₀, hφ₀I, hφ₀ind⟩ := hPJ'.2 b₀⁻¹ (Bs.inv_mem hb₀)
      have hψ : ∀ j : ↥J, α' (ρJ j) = ρJ (J.normalizerMonoidHom ⟨b₀, hb₀J⟩ j) := by
        intro j
        apply Subtype.ext
        change ggLAut K θ ⟨b₀, hN hb₀⟩ (ρ (Subgroup.inclusion hJK j)) =
          ρ (Subgroup.inclusion hJK (J.normalizerMonoidHom ⟨b₀, hb₀J⟩ j))
        rw [hmap]
        congr 1
      have hθ' : ∀ j : ↥J, (e.symm.trans θJ') (ρJ j : ↥J₀ ⧸ Subgroup.center ↥J₀) =
          θJ' (j : ↥J ⧸ Subgroup.center ↥J) := by
        intro j
        rw [MulEquiv.trans_apply]
        congr 1
        exact (MulEquiv.symm_apply_eq e).mpr (he j).symm
      have hcoher : kgInducedAut (e.symm.trans θJ') α' = φ₀ := by
        ext r
        obtain ⟨q, rfl⟩ := (e.symm.trans θJ').surjective r
        obtain ⟨xq, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨j, rfl⟩ := hρJsurj xq
        rw [hθ' j]
        rw [show θJ' (j : ↥J ⧸ Subgroup.center ↥J) =
            (e.symm.trans θJ') (ρJ j : ↥J₀ ⧸ Subgroup.center ↥J₀) from (hθ' j).symm]
        rw [ggNbrLangAxisInnerFNIAux_kgInducedAut_mk]
        rw [hψ j]
        rw [hθ' (J.normalizerMonoidHom ⟨b₀, hb₀J⟩ j)]
        rw [hθ' j]
        exact (hφ₀ind j (J.normalizerMonoidHom ⟨b₀, hb₀J⟩ j) (by
          change ((J.normalizerMonoidHom ⟨b₀, hb₀J⟩ j : ↥J) : G) =
            (b₀⁻¹)⁻¹ * (j : G) * b₀⁻¹
          rw [normalizerMonoidHom_coe, inv_inv])).symm
      rw [hcoher]
      exact hφ₀I
  obtain ⟨-, lab', hlab', hraw'⟩ := hKG _ hP₀
  obtain ⟨R', _, I', F', -, -, θ', hconj⟩ := largeEvenRawDatum_exists hraw'
  exact hconj.2 hconj.1

end CFSG.StandardType
