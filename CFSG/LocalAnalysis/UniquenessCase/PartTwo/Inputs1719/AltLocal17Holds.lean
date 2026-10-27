module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.Quasithin.Background.Harris.KFact2d.F5Three
public import CFSG.GroupTheory.SylowInfNormal
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312KG
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocU33
public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33
public import CFSG.GroupTheory.PermSylowTwo.Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Config

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin (IsPSL IsPSU)
open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem k_L33Local_holds : K_L33Local := by
  intro Y _ _ K S hKY hLie
  obtain ⟨hKN, hKq, hZodd, hCent, ⟨a, hIndex⟩, hSylY⟩ := hKY
  have hKpsl : CFSG.Quasithin.IsPSL 3 3 1 ↥K := (LieModel.classical_iff (by decide)).mp hLie
  have hKsimple : IsSimpleGroup ↥K := CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSL hKpsl
  have hKnoncomm : ∃ x y : ↥K, x * y ≠ y * x :=
    CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSL hKpsl
  have hKcenter : Subgroup.center ↥K = ⊥ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.F618Comp.center_eq_bot_of_isSimpleGroup hKnoncomm
  have hSylY' : IsSylowTwoOf S ⊤ := hSylY
  set T : Subgroup Y := S ⊓ K with hTdef
  have hTsyl : IsSylowTwoOf T K := by
    have h := CFSG.isSylowTwoOf_inf_of_normal (S := S) (X := ⊤) (N := K) hSylY'
      (le_top : K ≤ ⊤) (by rw [Subgroup.normalizer_eq_top_iff.mpr hKN])
    simpa [T, inf_comm] using h
  have hTcard : Nat.card ↥T = 16 :=
    CFSG.Quasithin.Background.Harris.KFact2d.card_sylow_three hKpsl hTsyl
  have hPcard : Nat.card ↥(CFSG.Quasithin.Background.Harris.KFact2d.cenZ K T) = 48 :=
    CFSG.Quasithin.Background.Harris.KFact2d.card_cenZ_three hKpsl hTsyl
  set P₀ : Subgroup Y := CFSG.Quasithin.Background.Harris.KFact2d.cenZ K T with hP₀def
  have hTP₀ : T ≤ P₀ := by
    exact le_inf hTsyl.1 (CFSG.Quasithin.E2P.le_centralizer_zOf T)
  have hSK : S ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKN]; exact le_top
  have hST : S ≤ Subgroup.normalizer (T : Set Y) :=
    (le_inf Subgroup.le_normalizer hSK).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hSz : S ≤ Subgroup.normalizer (CFSG.Quasithin.E2P.zOf T : Set Y) :=
    (le_inf hST (hST.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer T))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hSC : S ≤ Subgroup.normalizer
      (Subgroup.centralizer (CFSG.Quasithin.E2P.zOf T : Set Y) : Set Y) :=
    hSz.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (CFSG.Quasithin.E2P.zOf T))
  have hSP₀ : S ≤ Subgroup.normalizer (P₀ : Set Y) :=
    (le_inf hSK hSC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hinf : S ⊓ P₀ = T := by
    refine le_antisymm ?_ (le_inf (by rw [hTdef]; exact inf_le_left) hTP₀)
    intro x hx
    exact ⟨hx.1, hx.2.1⟩
  have hsupcard : Nat.card ↥(P₀ ⊔ S) = 3 * Nat.card ↥S := by
    have hform :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := S) (K := P₀) hSP₀
    rw [hinf, hPcard, hTcard, sup_comm] at hform
    have h1 : Nat.card ↥(P₀ ⊔ S) * 16 = (3 * Nat.card ↥S) * 16 := by
      calc Nat.card ↥(P₀ ⊔ S) * 16 = Nat.card ↥S * 48 := hform
        _ = Nat.card ↥S * (3 * 16) := by norm_num
        _ = (3 * Nat.card ↥S) * 16 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have h3dvd : 3 ∣ Nat.card ↥P₀ := by rw [hPcard]; norm_num
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₀) 3 h3dvd
  let E : Subgroup Y := Subgroup.zpowers (y : Y)
  have hyord' : orderOf (y : Y) = 3 := (Subgroup.orderOf_coe y).trans hyord
  have hEcard : Nat.card ↥E = 3 := by
    rw [Nat.card_zpowers, hyord']
  have hE3 : IsPGroup 3 ↥E := IsPGroup.of_card (n := 1) (by rw [hEcard]; norm_num)
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hx
      rwa [hyord'] at this
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  have hEle : E ≤ P₀ := Subgroup.zpowers_le.mpr y.2
  have hEK : E ≤ K := hEle.trans inf_le_left
  have hEnot : ¬ E ≤ (Subgroup.center ↥K).map K.subtype := by
    intro hle
    have hbot : E ≤ ⊥ := by simpa [hKcenter] using hle
    exact hEne (le_bot_iff.mp hbot)
  have hEdisj : E ⊓ S = ⊥ := by
    have hdisj : Disjoint E S := IsPGroup.disjoint_of_ne 3 2 (by omega) E S hE3 hSylY'.2.1
    exact hdisj.eq_bot
  have hEcardS : Nat.card ↥(E ⊔ S) ≤ Nat.card ↥E * Nat.card ↥S := by
    have hle : E ⊔ S ≤ P₀ ⊔ S := sup_le (hEle.trans le_sup_left) le_sup_right
    have hcard := Subgroup.card_le_of_le hle
    rw [hsupcard] at hcard
    rw [hEcard]
    exact hcard
  exact ⟨E, hEK, hEne, hE3, hEexp, hEnot,
    CFSG.Quasithin.H.L3Wr.permute_of_card hEdisj hEcardS⟩

theorem k_U33SThreePair_holds :
    K_U33SThreePair := by
  intro Y _ _ K S hKY hLie
  obtain ⟨hKN, hKq, hZodd, hCent, ⟨a, hIndex⟩, hSylY⟩ := hKY
  have hKpsu : CFSG.Quasithin.IsPSU 3 3 1 ↥K := (LieModel.classical_iff (by decide)).mp hLie
  have hKnoncomm : ∃ x y : ↥K, x * y ≠ y * x :=
    CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSU hKpsu
  have : IsSimpleGroup ↥K := CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSU hKpsu
  have hKcenter : Subgroup.center ↥K = ⊥ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.F618Comp.center_eq_bot_of_isSimpleGroup hKnoncomm
  have hSylY' : IsSylowTwoOf S ⊤ := hSylY
  set T : Subgroup Y := S ⊓ K with hTdef
  have hTsyl : IsSylowTwoOf T K := by
    have h := CFSG.isSylowTwoOf_inf_of_normal (S := S) (X := ⊤) (N := K) hSylY'
      (le_top : K ≤ ⊤) (by rw [Subgroup.normalizer_eq_top_iff.mpr hKN])
    simpa [T, inf_comm] using h
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.nonempty_mulEquiv_u33G_of_statedClassicalModel
      hKpsu
  let TK : Subgroup ↥K := T.subgroupOf K
  have hTKtop : IsSylowTwoOf TK ⊤ :=
    CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_subgroupOf_top hTsyl
  have hT'syl : IsSylowTwoOf (TK.map e.toMonoidHom) ⊤ := by
    have h := CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_map_mulEquiv e hTKtop
    simpa using h
  obtain ⟨k, -, hk⟩ :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hT'syl).exists_mem_conj
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1
        (CFSG.Quasithin.GoldC3.u33_isSylowT))
  have hconj : (TK.map e.toMonoidHom).map (MulAut.conj k).toMonoidHom = u33Data.T := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  let e' : ↥K ≃* U33G := e.trans (MulAut.conj k)
  have hTeq : TK.map e'.toMonoidHom = u33Data.T := by
    simpa [e', MulEquiv.trans_apply, Subgroup.map_map] using hconj
  have hTmap : u33Data.T.map e'.symm = TK := by
    have h := congrArg (Subgroup.map e'.symm.toMonoidHom) hTeq
    rw [Subgroup.map_map] at h
    simpa using h.symm
  have hTKcard : Nat.card ↥TK = 32 := by
    rw [← CFSG.Quasithin.u33_card_T, ← hTeq, Subgroup.card_map_of_injective e'.injective]
  have hTKcardT : Nat.card ↥TK = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTsyl.1).toEquiv
  have hTcard : Nat.card ↥T = 32 := by rw [← hTKcardT, hTKcard]
  let AK : Subgroup ↥K := u33Data.A.map e'.symm
  have hc3' : CFSG.Quasithin.GoldC3.C3Facts ↥K (u33Data.T.map e'.symm) AK :=
    CFSG.Quasithin.GoldC3.c3Facts_u33.map e'.symm
  have hc3 : CFSG.Quasithin.GoldC3.C3Facts ↥K TK AK := hTmap ▸ hc3'
  have hAKcard : Nat.card ↥AK = 96 := by
    have h := hc3.card
    rw [hTKcard] at h
    norm_num at h
    exact h
  have hBcen : u33Data.B = Subgroup.centralizer (centerOf u33Data.T : Set U33G) := by
    refine le_antisymm CFSG.Quasithin.GoldC3.u33_B_le_C ?_
    have hCtop : Subgroup.centralizer (centerOf u33Data.T : Set U33G) ≠ ⊤ :=
      CFSG.Quasithin.GoldCMax.centralizer_ne_top_u33 CFSG.Quasithin.GoldC3.u33_centerOf_ne_bot
    have hTle : u33Data.T ≤ Subgroup.centralizer (centerOf u33Data.T : Set U33G) :=
      u33Data.T_le_B.trans CFSG.Quasithin.GoldC3.u33_B_le_C
    have hAB : u33Data.A ≠ u33Data.B := by
      intro h
      apply u33Data.T_ne_A
      rw [← u33Data.inf_AB, h, inf_idem]
    rcases CFSG.Quasithin.OvergroupData.lattice u33Data _ hTle with h | h | h | h
    · have hBT : u33Data.B ≤ u33Data.T := h ▸ CFSG.Quasithin.GoldC3.u33_B_le_C
      exact absurd (le_antisymm u33Data.T_le_B hBT) u33Data.T_ne_B
    · have hBA : u33Data.B ≤ u33Data.A := h ▸ CFSG.Quasithin.GoldC3.u33_B_le_C
      exact absurd (Subgroup.eq_of_le_of_card_ge hBA (by
        rw [CFSG.Quasithin.H13.U3.card_u33_B, CFSG.Quasithin.H13.U3.card_u33_A]))
        (fun h' => hAB h'.symm)
    · exact le_of_eq h
    · exact absurd h hCtop
  let BK : Subgroup ↥K := Subgroup.centralizer (centerOf TK : Set ↥K)
  have hBKmap : BK.map e'.toMonoidHom = u33Data.B := by
    have h1 : BK.map e'.toMonoidHom =
        Subgroup.centralizer (centerOf (TK.map e'.toMonoidHom) : Set U33G) := by
      change (Subgroup.centralizer (centerOf TK : Set ↥K)).map e'.toMonoidHom = _
      rw [← CFSG.Quasithin.centralizer_map_equiv e' (centerOf TK),
        ← CFSG.Quasithin.centerOf_map_equiv e' TK]
    rw [h1, hTeq, hBcen]
  have hBKcard : Nat.card ↥BK = 96 := by
    have h := Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective (K := BK)
    rw [hBKmap, CFSG.Quasithin.H13.U3.card_u33_B] at h
    exact h.symm
  have hBK_eq : BK = u33Data.B.map e'.symm := by
    apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
    rw [hBKmap, Subgroup.map_map]
    simp
  have hAKBK : AK ⊔ BK = ⊤ := by
    change u33Data.A.map e'.symm ⊔ BK = ⊤
    rw [hBK_eq, ← Subgroup.map_sup, CFSG.Quasithin.GoldC3.u33_sup_AB]
    exact Subgroup.map_top_of_surjective e'.symm.toMonoidHom e'.symm.surjective
  have hNTK : Subgroup.normalizer (TK : Set ↥K) = TK := by
    have hTmap' : Subgroup.map e'.symm.toMonoidHom u33Data.T = TK := hTmap
    have h := Subgroup.map_equiv_normalizer_eq u33Data.T e'.symm
    rw [CFSG.Quasithin.GoldC3.u33_normalizer_T, hTmap'] at h
    exact h.symm
  have hTKfix : ∀ s ∈ S, TK.map (MulAut.conjNormal (H := K) s).toMonoidHom = TK := by
    intro s hs
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((MulAut.conjNormal (H := K) s y : ↥K) : Y) ∈ T
      have hyT : (y : Y) ∈ T := hy
      rw [MulAut.conjNormal_apply]
      exact ⟨S.mul_mem (S.mul_mem hs hyT.1) (S.inv_mem hs),
        hKN.conj_mem (y : Y) hyT.2 s⟩
    · intro hx
      have hxT : (x : Y) ∈ T := hx
      refine ⟨(MulAut.conjNormal (H := K) s)⁻¹ x, ?_, by simp⟩
      change (((MulAut.conjNormal (H := K) s)⁻¹ x : ↥K) : Y) ∈ T
      have hcoe : (((MulAut.conjNormal (H := K) s)⁻¹ x : ↥K) : Y) = s⁻¹ * (x : Y) * s := by
        have hαinv : (MulAut.conjNormal (H := K) s)⁻¹ = MulAut.conjNormal (H := K) s⁻¹ :=
          (map_inv _ _).symm
        rw [hαinv, MulAut.conjNormal_apply]
        group
      rw [hcoe]
      exact ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hxT.1) hs,
        by simpa using hKN.conj_mem (x : Y) hxT.2 s⁻¹⟩
  have hAKfix : ∀ s ∈ S, AK.map (MulAut.conjNormal (H := K) s).toMonoidHom = AK :=
    fun s hs => hc3.inv _ (hTKfix s hs)
  have hBKfix : ∀ s ∈ S, BK.map (MulAut.conjNormal (H := K) s).toMonoidHom = BK := by
    intro s hs
    have hcenterfix : (centerOf TK).map (MulAut.conjNormal (H := K) s).toMonoidHom =
        centerOf TK := by
      rw [← CFSG.Quasithin.centerOf_map_equiv (MulAut.conjNormal (H := K) s) TK,
        hTKfix s hs]
    have h1 := CFSG.Quasithin.centralizer_map_equiv (MulAut.conjNormal (H := K) s)
      (centerOf TK)
    change (Subgroup.centralizer (centerOf TK : Set ↥K)).map
      (MulAut.conjNormal (H := K) s).toMonoidHom = _
    rw [hcenterfix] at h1
    exact h1.symm
  let AY : Subgroup Y := AK.map K.subtype
  let BY : Subgroup Y := BK.map K.subtype
  have hnorm_of_fix : ∀ H : Subgroup ↥K,
      (∀ s ∈ S, H.map (MulAut.conjNormal (H := K) s).toMonoidHom = H) →
      S ≤ Subgroup.normalizer (H.map K.subtype : Set Y) := by
    intro H hH s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨xk, hxk, rfl⟩ := Subgroup.mem_map.mp hx
      have hmem : (MulAut.conjNormal (H := K) s) xk ∈ H := by
        rw [← hH s hs]
        exact Subgroup.mem_map_of_mem _ hxk
      change s * ((xk : ↥K) : Y) * s⁻¹ ∈ H.map K.subtype
      rw [← MulAut.conjNormal_apply s xk]
      exact Subgroup.mem_map_of_mem K.subtype hmem
    · intro hx
      obtain ⟨xk, hxk, hxkcoe⟩ := Subgroup.mem_map.mp hx
      have hmem : (MulAut.conjNormal (H := K) s⁻¹) xk ∈ H := by
        rw [← hH s⁻¹ (S.inv_mem hs)]
        exact Subgroup.mem_map_of_mem _ hxk
      have hcoe : (((MulAut.conjNormal (H := K) s⁻¹) xk : ↥K) : Y) = x := by
        rw [MulAut.conjNormal_apply]
        calc s⁻¹ * ((xk : ↥K) : Y) * (s⁻¹)⁻¹
            = s⁻¹ * (s * (x : Y) * s⁻¹) * (s⁻¹)⁻¹ := by
                rw [show ((xk : ↥K) : Y) = s * (x : Y) * s⁻¹ from hxkcoe]
          _ = x := by group
      rw [← hcoe]
      exact Subgroup.mem_map_of_mem K.subtype hmem
  have hSAY : S ≤ Subgroup.normalizer (AY : Set Y) := hnorm_of_fix AK hAKfix
  have hSBY : S ≤ Subgroup.normalizer (BY : Set Y) := hnorm_of_fix BK hBKfix
  have hAYcard : Nat.card ↥AY = 96 := by
    change Nat.card ↥(AK.map K.subtype) = 96
    rw [Subgroup.card_map_of_injective K.subtype_injective, hAKcard]
  have hBYcard : Nat.card ↥BY = 96 := by
    change Nat.card ↥(BK.map K.subtype) = 96
    rw [Subgroup.card_map_of_injective K.subtype_injective, hBKcard]
  have hTKmap : TK.map K.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTsyl.1
  have hTAY : T ≤ AY := by
    rw [← hTKmap]
    exact Subgroup.map_mono hc3.le
  have hTBY : T ≤ BY := by
    rw [← hTKmap]
    exact Subgroup.map_mono (CFSG.Quasithin.GoldC3.le_centralizer_centerOf TK)
  have hAYinfS : AY ⊓ S = T := by
    refine le_antisymm ?_ (le_inf hTAY (by rw [hTdef]; exact inf_le_left))
    intro x hx
    exact ⟨hx.2, Subgroup.map_subtype_le AK hx.1⟩
  have hBYinfS : BY ⊓ S = T := by
    refine le_antisymm ?_ (le_inf hTBY (by rw [hTdef]; exact inf_le_left))
    intro x hx
    exact ⟨hx.2, Subgroup.map_subtype_le BK hx.1⟩
  have hPAcard : Nat.card ↥(AY ⊔ S) = 3 * Nat.card ↥S := by
    have hform :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := S) (K := AY) hSAY
    rw [inf_comm, hAYinfS, hAYcard, hTcard, sup_comm] at hform
    have h1 : Nat.card ↥(AY ⊔ S) * 32 = (3 * Nat.card ↥S) * 32 := by
      calc Nat.card ↥(AY ⊔ S) * 32 = Nat.card ↥S * 96 := hform
        _ = Nat.card ↥S * (3 * 32) := by norm_num
        _ = (3 * Nat.card ↥S) * 32 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hPBcard : Nat.card ↥(BY ⊔ S) = 3 * Nat.card ↥S := by
    have hform :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := S) (K := BY) hSBY
    rw [inf_comm, hBYinfS, hBYcard, hTcard, sup_comm] at hform
    have h1 : Nat.card ↥(BY ⊔ S) * 32 = (3 * Nat.card ↥S) * 32 := by
      calc Nat.card ↥(BY ⊔ S) * 32 = Nat.card ↥S * 96 := hform
        _ = Nat.card ↥S * (3 * 32) := by norm_num
        _ = (3 * Nat.card ↥S) * 32 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hPAidx : S.relIndex (AY ⊔ S) = 3 := by
    have h := Subgroup.relIndex_mul_card S (AY ⊔ S)
    rw [inf_eq_left.mpr le_sup_right, hPAcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hPBidx : S.relIndex (BY ⊔ S) = 3 := by
    have h := Subgroup.relIndex_mul_card S (BY ⊔ S)
    rw [inf_eq_left.mpr le_sup_right, hPBcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hPAsyl : IsSylowTwoOf S (AY ⊔ S) := by
    refine ⟨le_sup_right, hSylY'.2.1, ?_⟩
    rw [show (S.subgroupOf (AY ⊔ S)).index = S.relIndex (AY ⊔ S) from rfl, hPAidx]
    norm_num
  have hPBsyl : IsSylowTwoOf S (BY ⊔ S) := by
    refine ⟨le_sup_right, hSylY'.2.1, ?_⟩
    rw [show (S.subgroupOf (BY ⊔ S)).index = S.relIndex (BY ⊔ S) from rfl, hPBidx]
    norm_num
  have hAKnotN : ¬ AK ≤ Subgroup.normalizer (TK : Set ↥K) := hc3.not_normal
  have htoAK : AY ≤ Subgroup.normalizer (T : Set Y) →
      AK ≤ Subgroup.normalizer (TK : Set ↥K) := by
    intro hAYT
    intro x hx
    have hxAY : (x : Y) ∈ AY := Subgroup.mem_map_of_mem K.subtype hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyT : (y : Y) ∈ T := hy
      have hmem : (x : Y) * (y : Y) * (x : Y)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hAYT hxAY) (y : Y)).mp hyT
      rw [Subgroup.mem_subgroupOf]
      simpa using hmem
    · intro hy
      have hyT : ((x * y * x⁻¹ : ↥K) : Y) ∈ T := hy
      have hmem := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (T : Set Y)).inv_mem (hAYT hxAY)) _).mp hyT
      have hEq : (x : Y)⁻¹ * (((x * y * x⁻¹ : ↥K) : Y)) * ((x : Y)⁻¹)⁻¹ = (y : Y) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hEq] at hmem
      rw [Subgroup.mem_subgroupOf]
      exact hmem
  have hPA_notN : ¬ (AY ⊔ S) ≤ Subgroup.normalizer (S : Set Y) := by
    intro hle
    have hAYnorm : AY ≤ Subgroup.normalizer (S : Set Y) := le_sup_left.trans hle
    have hAYK : AY ≤ K := Subgroup.map_subtype_le AK
    have hNKn : AY ≤ Subgroup.normalizer (K : Set Y) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hKN]
      exact le_top
    have hAYT : AY ≤ Subgroup.normalizer (T : Set Y) := by
      have h := (le_inf hNKn hAYnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
      simpa [T, inf_comm] using h
    exact hAKnotN (htoAK hAYT)
  have hBKnotN : ¬ BK ≤ Subgroup.normalizer (TK : Set ↥K) := by
    intro hle
    have hBKTK : BK ≤ TK := hNTK ▸ hle
    have hcard := Subgroup.card_le_of_le hBKTK
    rw [hBKcard, hTKcard] at hcard
    norm_num at hcard
  have htoBK : BY ≤ Subgroup.normalizer (T : Set Y) →
      BK ≤ Subgroup.normalizer (TK : Set ↥K) := by
    intro hBYT
    intro x hx
    have hxBY : (x : Y) ∈ BY := Subgroup.mem_map_of_mem K.subtype hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyT : (y : Y) ∈ T := hy
      have hmem : (x : Y) * (y : Y) * (x : Y)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hBYT hxBY) (y : Y)).mp hyT
      rw [Subgroup.mem_subgroupOf]
      simpa using hmem
    · intro hy
      have hyT : ((x * y * x⁻¹ : ↥K) : Y) ∈ T := hy
      have hmem := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (T : Set Y)).inv_mem (hBYT hxBY)) _).mp hyT
      have hEq : (x : Y)⁻¹ * (((x * y * x⁻¹ : ↥K) : Y)) * ((x : Y)⁻¹)⁻¹ = (y : Y) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hEq] at hmem
      rw [Subgroup.mem_subgroupOf]
      exact hmem
  have hPB_notN : ¬ (BY ⊔ S) ≤ Subgroup.normalizer (S : Set Y) := by
    intro hle
    have hBYnorm : BY ≤ Subgroup.normalizer (S : Set Y) := le_sup_left.trans hle
    have hNKn : BY ≤ Subgroup.normalizer (K : Set Y) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hKN]
      exact le_top
    have hBYT : BY ≤ Subgroup.normalizer (T : Set Y) := by
      have h := (le_inf hNKn hBYnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
      simpa [T, inf_comm] using h
    exact hBKnotN (htoBK hBYT)
  have hKS : K ⊔ S = ⊤ := by
    have hodd : Odd S.index := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      exact hSylY'.2.2 (by
        rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S]
        exact even_iff_two_dvd.mp heven)
    have hdvd : (K ⊔ S).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_right
    have h2dvd : (K ⊔ S).index ∣ 2 ^ a := by
      have h : (K ⊔ S).index ∣ K.index :=
        Subgroup.index_dvd_of_le (le_sup_left : K ≤ K ⊔ S)
      rwa [hIndex] at h
    have hcopS : Nat.Coprime S.index (2 ^ a) :=
      Nat.Coprime.pow_right a hodd.coprime_two_right
    have hcop : Nat.Coprime (K ⊔ S).index (2 ^ a) := hcopS.coprime_dvd_left hdvd
    exact Subgroup.index_eq_one.mp (hcop.eq_one_of_dvd h2dvd)
  refine ⟨AY ⊔ S, BY ⊔ S, le_sup_right, le_sup_right, ?_, ?_, ?_⟩
  · calc (AY ⊔ S) ⊔ (BY ⊔ S) = (AY ⊔ BY) ⊔ S := by ac_rfl
      _ = K ⊔ S := by
          congr 1
          have h := congrArg (Subgroup.map K.subtype) hAKBK
          rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h
          exact h
      _ = ⊤ := hKS
  · exact CFSG.Quasithin.nonempty_quotient_pCore_of_relIndex_eq_three' hPAsyl hPAidx hPA_notN
  · exact CFSG.Quasithin.nonempty_quotient_pCore_of_relIndex_eq_three' hPBsyl hPBidx hPB_notN

theorem k_U33Local_holds :
    K_U33Local := by
  intro Y _ _ K S hKY hLie
  have hKY' := hKY
  obtain ⟨hKN, hKq, hZodd, hCent, ⟨a, hIndex⟩, hSylY⟩ := hKY
  have hKpsu : CFSG.Quasithin.IsPSU 3 3 1 ↥K := (LieModel.classical_iff (by decide)).mp hLie
  have hKnoncomm : ∃ x y : ↥K, x * y ≠ y * x :=
    CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSU hKpsu
  have : IsSimpleGroup ↥K := CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSU hKpsu
  have hKcenter : Subgroup.center ↥K = ⊥ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.F618Comp.center_eq_bot_of_isSimpleGroup hKnoncomm
  have hSylY' : IsSylowTwoOf S ⊤ := hSylY
  set T : Subgroup Y := S ⊓ K with hTdef
  have hTsyl : IsSylowTwoOf T K := by
    have h := CFSG.isSylowTwoOf_inf_of_normal (S := S) (X := ⊤) (N := K) hSylY'
      (le_top : K ≤ ⊤) (by rw [Subgroup.normalizer_eq_top_iff.mpr hKN])
    simpa [T, inf_comm] using h
  have hpair := k_U33SThreePair_holds (Y := Y) (K := K) (S := S)
  unfold K_U33SThreePair at hpair
  obtain ⟨P₁, P₂, hSP₁, hSP₂, hsup, hbar₁, hbar₂⟩ := hpair hKY' hLie
  have hSylP₁ : IsSylowTwoOf S P₁ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15420.isSylowTwoOf_of_le_of_le hSylY' hSP₁ le_top
  have hO2le : pCoreOf 2 P₁ ≤ S :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSylP₁
  have hperm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hbarP₁ : Nat.card (Bar2 P₁) = 6 := by
    obtain ⟨e⟩ := hbar₁
    rw [Nat.card_congr e.toEquiv, hperm3]
  have hP₁card : Nat.card ↥P₁ = Nat.card ↥(pCoreOf 2 P₁) * 6 := by
    rw [card_eq_card_pCoreOf_mul_card_bar2, hbarP₁]
  have hP₁Ktop : P₁ ⊔ K = ⊤ := by
    have hodd : Odd S.index := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      exact hSylY'.2.2 (by
        rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S]
        exact even_iff_two_dvd.mp heven)
    have hdvd : (K ⊔ S).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_right
    have h2dvd : (K ⊔ S).index ∣ 2 ^ a := by
      have h : (K ⊔ S).index ∣ K.index :=
        Subgroup.index_dvd_of_le (le_sup_left : K ≤ K ⊔ S)
      rwa [hIndex] at h
    have hcopS : Nat.Coprime S.index (2 ^ a) :=
      Nat.Coprime.pow_right a hodd.coprime_two_right
    have hcop : Nat.Coprime (K ⊔ S).index (2 ^ a) := hcopS.coprime_dvd_left hdvd
    have hKS : K ⊔ S = ⊤ := Subgroup.index_eq_one.mp (hcop.eq_one_of_dvd h2dvd)
    exact eq_top_iff.mpr (hKS ▸ sup_le le_sup_right (hSP₁.trans le_sup_left))
  have hP₁NK : P₁ ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKN]
    exact le_top
  have hcardPK : Nat.card ↥(P₁ ⊓ K) * 2 ^ a = Nat.card ↥P₁ := by
    have hform :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := P₁) (K := K) hP₁NK
    rw [hP₁Ktop, Subgroup.card_top] at hform
    have hY : Nat.card Y = Nat.card ↥K * 2 ^ a := by
      have h := Subgroup.card_mul_index K
      rw [hIndex] at h
      exact h.symm
    rw [hY] at hform
    have h' : Nat.card ↥K * (Nat.card ↥(P₁ ⊓ K) * 2 ^ a) = Nat.card ↥K * Nat.card ↥P₁ := by
      calc Nat.card ↥K * (Nat.card ↥(P₁ ⊓ K) * 2 ^ a)
          = (Nat.card ↥K * 2 ^ a) * Nat.card ↥(P₁ ⊓ K) := by ring
        _ = Nat.card ↥P₁ * Nat.card ↥K := hform
        _ = Nat.card ↥K * Nat.card ↥P₁ := by ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h'
  have h3dvd : 3 ∣ Nat.card ↥(P₁ ⊓ K) := by
    have h : 3 ∣ Nat.card ↥(P₁ ⊓ K) * 2 ^ a := by
      rw [hcardPK, hP₁card]
      exact ⟨Nat.card ↥(pCoreOf 2 P₁) * 2, by ring⟩
    have hcop : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
    exact hcop.dvd_of_dvd_mul_right h
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P₁ ⊓ K)) 3 h3dvd
  let E : Subgroup Y := Subgroup.zpowers (y : Y)
  have hyord' : orderOf (y : Y) = 3 := (Subgroup.orderOf_coe y).trans hyord
  have hEcard : Nat.card ↥E = 3 := by rw [Nat.card_zpowers, hyord']
  have hE3 : IsPGroup 3 ↥E := IsPGroup.of_card (n := 1) (by rw [hEcard]; norm_num)
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hx
      rwa [hyord'] at this
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  have hEP₁ : E ≤ P₁ := (Subgroup.zpowers_le.mpr y.2).trans inf_le_left
  have hEK : E ≤ K := (Subgroup.zpowers_le.mpr y.2).trans inf_le_right
  have hEnot : ¬ E ≤ (Subgroup.center ↥K).map K.subtype := by
    intro hle
    have hbot : E ≤ ⊥ := by simpa [hKcenter] using hle
    exact hEne (le_bot_iff.mp hbot)
  have hEdisj : E ⊓ S = ⊥ := by
    have hdisj : Disjoint E S := IsPGroup.disjoint_of_ne 3 2 (by omega) E S hE3 hSylY'.2.1
    exact hdisj.eq_bot
  have hperm : Permutes E S := by
    by_cases hle : P₁ ≤ Subgroup.normalizer (S : Set Y)
    · have hES : E ≤ Subgroup.normalizer (S : Set Y) := hEP₁.trans hle
      rw [Permutes]
      ext x
      constructor
      · rintro ⟨e, he, s, hs, rfl⟩
        refine ⟨e * s * e⁻¹, ?_, e, he, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (hES he) s).mp hs
      · rintro ⟨s, hs, e, he, rfl⟩
        refine ⟨e, he, e⁻¹ * s * e, ?_, by group⟩
        simpa using (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (S : Set Y)).inv_mem (hES he)) s).mp hs
    · have hO2ne : pCoreOf 2 P₁ ≠ S := by
        intro h
        apply hle
        rw [← h]
        exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P₁
      have hO2leP : pCoreOf 2 P₁ ≤ P₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 P₁
      have hO2rel : (pCoreOf 2 P₁).relIndex P₁ = 6 := by
        have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 P₁) (K := P₁)
        rw [inf_eq_left.mpr hO2leP] at h
        have h6 : (pCoreOf 2 P₁).relIndex P₁ * Nat.card ↥(pCoreOf 2 P₁) =
            6 * Nat.card ↥(pCoreOf 2 P₁) := by
          rw [h, hP₁card]
          ring
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h6
      have hrel_dvd : (pCoreOf 2 P₁).relIndex S ∣ 6 := by
        have htrans := Subgroup.relIndex_mul_relIndex (H := pCoreOf 2 P₁) (K := S)
          (L := P₁) hO2le hSP₁
        rw [hO2rel] at htrans
        exact ⟨S.relIndex P₁, htrans.symm⟩
      have hpow : ∃ j, (pCoreOf 2 P₁).relIndex S = 2 ^ j := by
        have hnorm : S ≤ Subgroup.normalizer (pCoreOf 2 P₁ : Set Y) :=
          hSP₁.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P₁)
        have : ((pCoreOf 2 P₁).subgroupOf S).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer hnorm
        have hq : IsPGroup 2 (↥S ⧸ (pCoreOf 2 P₁).subgroupOf S) :=
          hSylY'.2.1.to_quotient ((pCoreOf 2 P₁).subgroupOf S)
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hq
        refine ⟨j, ?_⟩
        rw [Subgroup.relIndex, Subgroup.index_eq_card]
        exact hj
      have hO2relne : (pCoreOf 2 P₁).relIndex S ≠ 1 := by
        intro h1
        apply hO2ne
        exact (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hO2le).symm
      obtain ⟨j, hj⟩ := hpow
      have hjle : j ≤ 2 := by
        by_contra h3
        have hj3 : 3 ≤ j := by omega
        have h8 : 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num : 0 < 2) hj3
        have h6 : 2 ^ j ≤ 6 := by
          have hdvd2 : 2 ^ j ∣ 6 := by simpa [hj] using hrel_dvd
          exact Nat.le_of_dvd (by norm_num : 0 < 6) hdvd2
        omega
      have hrel2 : (pCoreOf 2 P₁).relIndex S = 2 := by
        interval_cases j
        · exact absurd (by simpa using hj) hO2relne
        · simpa using hj
        · exfalso
          have h4 : (2 : ℕ) ^ 2 ∣ 6 := hj ▸ hrel_dvd
          norm_num at h4
      have hScard : Nat.card ↥S = 2 * Nat.card ↥(pCoreOf 2 P₁) := by
        have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 P₁) (K := S)
        rw [inf_eq_left.mpr hO2le] at h
        rw [← h, hrel2]
      have hP₁card3 : Nat.card ↥P₁ = 3 * Nat.card ↥S := by
        rw [hP₁card, hScard]
        ring
      have hcardES : Nat.card ↥(E ⊔ S) ≤ Nat.card ↥E * Nat.card ↥S := by
        have hleES : E ⊔ S ≤ P₁ := sup_le hEP₁ hSP₁
        have hcard := Subgroup.card_le_of_le hleES
        rw [hP₁card3] at hcard
        rw [hEcard]
        exact hcard
      exact CFSG.Quasithin.H.L3Wr.permute_of_card hEdisj hcardES
  exact ⟨E, hEK, hEne, hE3, hEexp, hEnot, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
