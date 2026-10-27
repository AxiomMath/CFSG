module

public import CFSG.Quasithin.Vol2.Ch12Sec6L16a
public import CFSG.Quasithin.Vol2.Ch12Sec6L69
public import CFSG.Quasithin.Vol2.Ch12Sec6L3
public import CFSG.Quasithin.Vol2.Ch12Sec6L1d

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_g1 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h51 : AsB51) (hD2 : Lemma12_6_4_5) (hD3 : Lemma12_6_6_9) (hD8 : Lemma12_6_14)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ g₁ : G, Kv.map (MulAut.conj g₁).toMonoidHom = L ∧
      (Lv L v).map (MulAut.conj g₁).toMonoidHom = Lv L v ∧
      (Rv T L v).map (MulAut.conj g₁).toMonoidHom = Rv T L v ∧
      L ≤ Subgroup.centralizer ({g₁ * v * g₁⁻¹} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hyp := hH.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  obtain ⟨hJT, -⟩ := (hD3 G T L V F v Kv S hC).2.2.2.2 (hD8 G T L V F v Kv S hC)
  have hLZ := S126L1d.part6 h51 h1222 hH (L_eq_comm h1222 F hH hJT) hZ
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_top
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf hS hTsyl
  set c := (MulAut.conj g).toMonoidHom with hc
  have hST : S.map c = T := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hg]
      simpa [hc, mul_assoc] using hs
    · intro hx
      exact ⟨g⁻¹ * x * g, (hg x).1 hx, by simp [hc, mul_assoc]⟩
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  have hvG : v ∈ Gv v := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hvS : v ∈ S := hC.tv_le ⟨hVT hv, hvG⟩
  have hv2 : v ^ 2 = 1 := hVe.2 v hv
  have hv1 : v ≠ 1 := by
    have hnv : IsNonsing (F.β ⟨v, hv⟩) := hβ ▸ ⟨pe 0 1, rfl, S126L20a.wt_pe (by decide)⟩
    exact fun h => ne_one_of_nonsing hnv (by
      rw [show (⟨v, hv⟩ : ↥V) = 1 from Subtype.ext h, map_one])
  set w := g * v * g⁻¹ with hw
  have hwT : w ∈ T := hST ▸ ⟨v, hvS, rfl⟩
  have hwC : w ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [← hST] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have hsv : s * v = v * s := Subgroup.mem_centralizer_singleton_iff.1
      (show s ∈ Subgroup.centralizer {v} from hC.sylow.1 hs)
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hw]
    calc g * s * g⁻¹ * (g * v * g⁻¹) = g * (s * v) * g⁻¹ := by group
      _ = g * (v * s) * g⁻¹ := by rw [hsv]
      _ = g * v * g⁻¹ * (g * s * g⁻¹) := by group
  have hw2 : w ^ 2 = 1 := by rw [hw, conj_pow, hv2, mul_one, mul_inv_cancel]
  have hw1 : w ≠ 1 := fun h => hv1 (by
    have : v = g⁻¹ * w * g := by rw [hw]; group
    rw [this, h]
    group)
  have hwZ : w ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hwT, hwC⟩, hw2⟩
  have hLw : L ≤ Subgroup.centralizer ({w} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hLZ hl) w hwZ).symm
  have hGwM : Gv w ≤ Subgroup.normalizer (L : Set G) := centralizer_le_M h331 hH hwC hw2 hw1 hLw
  have hGvg : (Gv v).map c = Gv w := map_conj_Gv g v
  have hK1 : Kv.map c = oThreePrimeResidual (perfectCore (Gv w)) := by
    rw [hC.kv_eq, map_conj_oThreePrimeResidual, map_perfectCore, hGvg]
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hyp.maximal.1.2.1
  have hL5 := S126L1a.part5 h1222 h1228 hH
  have hKvg : Kv.map c = L := by
    apply le_antisymm
    · rw [hK1]
      calc oThreePrimeResidual (perfectCore (Gv w))
          ≤ oThreePrimeResidual (Subgroup.normalizer (L : Set G)) :=
            Subgroup.closure_mono fun x hx => ⟨hGwM (perfectCore_le _ hx.1), hx.2⟩
        _ = L := hL5
    · have hLG : L ≤ perfectCore (Gv w) := le_perfectCore_of_perfect hLw hLperf
      rw [hK1]
      calc L = oThreePrimeResidual (Subgroup.normalizer (L : Set G)) := hL5.symm
        _ ≤ oThreePrimeResidual (perfectCore (Gv w)) := by
            refine (Subgroup.closure_le _).2 fun x hx => Subgroup.subset_closure ⟨hLG ?_, hx.2⟩
            rw [← hL5]
            exact Subgroup.subset_closure hx
  set A := (Lv L v).map c with hA
  have hAL : A ≤ L := hKvg ▸ Subgroup.map_mono hC.lv_le
  have hAp : ⁅A, A⁆ = A := by
    rw [hA, ← Subgroup.map_commutator]
    congr 1
    exact perfectCore_perfect _
  obtain ⟨-, hRvR, -, -, -, hO2R, hRN, hcommR, -⟩ := hD2 G T L V F v Kv S hC
  have hKS : (Kv ⊔ S).map c = L ⊔ T := by rw [Subgroup.map_sup, hKvg, hST]
  have hO2A : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hKS, hc, pCoreOf_map_mulEquiv 2 (MulAut.conj g) (Kv ⊔ S), hA, hc,
      ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (hO2R.trans hRN)
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hCLV : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left)
      (B2F.le_normalizer_inf hXL (B2F.le_normalizer_centralizer hXV)) (isPGroup_CL h1222 hH)
  have hAn : L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (A : Set G) :=
    hCLV.trans hO2A
  obtain ⟨τ, hτ, hAτ⟩ : ∃ τ ∈ alternatingGroup (Fin 8),
      (A.subgroupOf L).map (psiP F hH) = A6s.map (MulAut.conj τ).toMonoidHom := by
    obtain ⟨f, hf, hk, -⟩ := exists_psiLv h1222 F hH hv hβ
    let e : ↥(Lv L v) ≃* ↥A := Subgroup.equivMapOfInjective (Lv L v) c (MulAut.conj g).injective
    let ψA : ↥A →* Equiv.Perm (Fin 8) := (psiP F hH).comp (Subgroup.inclusion hAL)
    have hrange : ψA.range = (A.subgroupOf L).map (psiP F hH) := by
      ext σ
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨Subgroup.inclusion hAL a, a.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    have hψk : IsPGroup 2 ↥ψA.ker := by
      intro x
      have hx1 : psiP F hH (Subgroup.inclusion hAL (x : ↥A)) = 1 := x.2
      have hq : S126L19a.psi F hH (Subgroup.inclusion hAL (x : ↥A)) = 1 := Subtype.ext hx1
      have hC' := (S126L19a.psi_eq_one_iff F hH _).1 hq
      obtain ⟨n, hn⟩ := isPGroup_CL h1222 hH ⟨((x : ↥A) : G), hAL (x : ↥A).2, hC'⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hn
      simpa using this
    let φ : ↥A →* ↥A6s := f.comp e.symm.toMonoidHom
    have hφ : Function.Surjective φ := hf.comp e.symm.surjective
    have hφk : IsPGroup 2 ↥φ.ker := by
      have h1 : φ.ker = f.ker.map e.toMonoidHom := by
        ext x
        simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map]
        constructor
        · intro hx
          exact ⟨e.symm x, hx, by simp⟩
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
      rw [h1]
      exact hk.map _
    have hB : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = (⊤ : Subgroup ↥A) := by
      apply Subgroup.map_injective A.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hAp]
    obtain ⟨τ, hτ, h⟩ := eq_conj_A6s_of_hom hB ψA hψk φ hφ hφk
    exact ⟨τ, hτ, hrange ▸ h⟩
  obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH ⟨τ, hτ⟩
  have hlτ : psiP F hH l = τ := congrArg Subtype.val hl
  set B := (Lv L v).map (MulAut.conj (l : G)).toMonoidHom with hB
  have hBeq : B = Lv L ((l : G) * v * (l : G)⁻¹) := (Lv_conj l.2 v).symm
  have hBL : B ≤ L := hBeq ▸ Lv_le_L L _
  have hBp : ⁅B, B⁆ = B := by rw [hBeq]; exact perfectCore_perfect _
  have hlvV : (l : G) * v * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV l.2) v).1 hv
  have hBn : L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (B : Set G) := by
    rw [hBeq]
    refine le_trans ?_ (normalizer_le_normalizer_perfectCore _)
    intro x hx
    refine Subgroup.le_normalizer ⟨hx.1, ?_⟩
    show x ∈ Subgroup.centralizer {(l : G) * v * (l : G)⁻¹}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hx.2 _ hlvV).symm
  have hψB : (B.subgroupOf L).map (psiP F hH) = A6s.map (MulAut.conj τ).toMonoidHom := by
    have hLvA : ((Lv L v).subgroupOf L).map (psiP F hH) = A6s := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact psiP_mem_A6s h1222 F hH hv hβ hy
      · intro a ha
        obtain ⟨y, hy, rfl⟩ := exists_Lv_of_A6s h1222 F hH hv hβ a ha
        exact ⟨y, hy, rfl⟩
    rw [← hLvA, Subgroup.map_map]
    ext σ
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hy
      have hxL : x ∈ L := Lv_le_L L v hx
      have hy' : y = l * ⟨x, hxL⟩ * l⁻¹ := by
        apply Subtype.ext
        have := hxy
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype] at this
        rw [← this]
        simp
      refine ⟨⟨x, hxL⟩, hx, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hy', map_mul, map_mul, map_inv, hlτ]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨l * y * l⁻¹, ⟨(y : G), hy, by simp⟩, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, hlτ]
  have hAB : A = B := le_antisymm
    (le_of_psi_le h1222 F hH hAL hAp hBn (le_of_eq (hAτ.trans hψB.symm)))
    (le_of_psi_le h1222 F hH hBL hBp hAn (le_of_eq (hψB.trans hAτ.symm)))
  set g₁ := (l : G)⁻¹ * g with hg₁
  set c₁ := (MulAut.conj g₁).toMonoidHom with hc₁
  have hconj : ∀ H : Subgroup G, H.map c₁ = (H.map c).map (MulAut.conj (l : G)⁻¹).toMonoidHom := by
    intro H
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [hc₁, hc, hg₁, mul_assoc]
  have hLv1 : (Lv L v).map c₁ = Lv L v := by
    rw [hconj, ← hA, hAB, hB, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id (Lv L v)]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hKv1 : Kv.map c₁ = L := by rw [hconj, hKvg, map_conj_self (L.inv_mem l.2)]
  have hS1 : S.map c₁ ≤ L ⊔ T := by
    rw [hconj, hST]
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((le_sup_left : L ≤ L ⊔ T) (L.inv_mem l.2))
      ((le_sup_right : T ≤ L ⊔ T) ht)) ((le_sup_left : L ≤ L ⊔ T) l.2)
  have hO2Lv1 : (pCoreOf 2 (Lv L v)).map c₁ = pCoreOf 2 (Lv L v) := by
    rw [hc₁, ← pCoreOf_map_mulEquiv, ← hc₁, hLv1]
  have hRsS : Rsec L Kv S v ≤ S := centralizerSection_le_left _ _ _
  have hRY : (Rsec L Kv S v).map c₁ ≤
      centralizerSection (L ⊔ T) (Lv L v) (pCoreOf 2 (Lv L v)) := by
    rintro _ ⟨r, hrR, rfl⟩
    refine ⟨hS1 ⟨r, hRsS hrR, rfl⟩, ?_, ?_, fun x hx => ?_⟩
    · rw [← hLv1, hc₁, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨r, hRN hrR, rfl⟩
    · rw [← hO2Lv1, hc₁, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨r, normalizer_le_normalizer_pCoreOf 2 _ (hRN hrR), rfl⟩
    · rw [← hLv1] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      have h1 : x' * r * x'⁻¹ * r⁻¹ ∈ pCoreOf 2 (Lv L v) := by
        have := hcommR (Subgroup.commutator_mem_commutator hx' hrR)
        rwa [commutatorElement_def] at this
      have h2 : c₁ (x' * r * x'⁻¹ * r⁻¹) ∈ pCoreOf 2 (Lv L v) := hO2Lv1 ▸ ⟨_, h1, rfl⟩
      simpa only [map_mul, map_inv] using h2
  have hRvRs : Rv T L v ≤ Rsec L Kv S v := hRvR ▸ inf_le_left
  have hRv1 : (Rv T L v).map c₁ = Rv T L v :=
    Subgroup.eq_of_le_of_card_ge
      (((Subgroup.map_mono hRvRs).trans hRY).trans (centralizerSection_le_Rv h1222 F hH hv hβ))
      (by rw [hc₁, Subgroup.card_map_of_injective (MulAut.conj g₁).injective])
  have hw1' : g₁ * v * g₁⁻¹ = w := by
    have hlw : (l : G)⁻¹ * w * (l : G) = w := by
      have := Subgroup.mem_centralizer_singleton_iff.1 (hLw (L.inv_mem l.2))
      calc (l : G)⁻¹ * w * l = w * (l : G)⁻¹ * l := by rw [this]
        _ = w := by group
    rw [hg₁, ← hlw, hw]
    group
  exact ⟨g₁, hKv1, hLv1, hRv1, hw1' ▸ hLw⟩

theorem part1216_one (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h51 : AsB51) (hD2 : Lemma12_6_4_5) (hD3 : Lemma12_6_6_9) (hD5 : Lemma12_6_11)
    (hD8 : Lemma12_6_14) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ¬ Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro hRM
  obtain ⟨g₁, hKv1, -, hRv1, -⟩ := exists_g1 h331 h1222 h1228 h51 hD2 hD3 hD8 hC hZ hS
  have hL1 := (Subgroup.mem_normalizer_iff_map_conj_eq).1
    (hRM ((Subgroup.mem_normalizer_iff_map_conj_eq).2 hRv1))
  have hKvL : Kv = L := Subgroup.map_injective (MulAut.conj g₁).injective (hKv1.trans hL1.symm)
  exact (hD5 G T L V F v Kv S hC).2 (hKvL ▸ Subgroup.le_normalizer)

end S126T2

end CFSG.Quasithin.H13
