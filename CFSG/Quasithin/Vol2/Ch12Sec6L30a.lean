module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final
public import CFSG.Quasithin.Vol2.Ch12Sec6L23a
public import CFSG.Quasithin.Vol2.Ch12Sec6L23d
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126

namespace S126L30

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem hypF98_of_inHz (h1224 : Lemma12_6_24) (h1227 : Lemma12_6_27) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : InHz T L F.V1 H) : HypF98 T V L F.V1 F.V5 H := by
  obtain ⟨-, -, -, -, -, ⟨-, -, hC5, -⟩, h78⟩ := h1224 G T L V F hH hZ
  have hF := (h78 H hHz).2.1
  refine ⟨hF, fun g hg => h1227 G T L V F hH hZ g fun hbot => hF.V₁_ne_bot ?_, Or.inl ?_⟩
  · rw [eq_bot_iff, ← hbot]
    exact le_inf hF.V₁_le_V hg
  · have hle : H ⊓ Subgroup.centralizer (F.V5 : Set G) ≤ Subgroup.centralizer (V : Set G) := by
      rw [← hC5]
      exact inf_le_right
    have hb : ⁅V, H ⊓ Subgroup.centralizer (F.V5 : Set G)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) v hv).symm
    rw [hb]
    exact bot_le

omit [Finite G] in
theorem conjClosure_le_of_le {K H₁ : Subgroup G} (hKH : K ≤ H₁) (hTH : T ≤ H₁) :
    conjClosure K T ≤ H₁ :=
  conjClosure_le fun _ ht _ hk => H₁.mul_mem (H₁.mul_mem (hTH ht) (hKH hk)) (H₁.inv_mem (hTH ht))

theorem inHz_of_isHK (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H₁ K : Subgroup G} (hH₁ : InHz T L F.V1 H₁)
    (hK : K ∈ cComp H₁) (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) :
    InHz T L F.V1 (conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T)) ∧
      conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T) ≤ H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hLTH, -⟩, -, hHC⟩ := hH₁
  have hTH : T ≤ H₁ := le_sup_right.trans hLTH
  have hle : conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T) ≤ H₁ :=
    sup_le (conjClosure_le_of_le (le_of_mem_cComp hK) hTH) hLTH
  obtain ⟨hVT, -, -, -, -⟩ := S126L23a.basics h1222 F hH
  have hV1T : F.V1 ≤ T := (Subgroup.map_subtype_le _).trans hVT
  have hV1X : F.V1 ≤ conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T) :=
    hV1T.trans (le_sup_right.trans le_sup_right)
  have hO2 : pCoreOf 2 (conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T)) ≠ ⊥ := by
    intro hbot
    have h1 : F.V1 ≤ pCoreOf 2 (conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T)) :=
      le_pCoreOf_of_le_normalizer 2 hV1X
        ((hle.trans hHC).trans (Subgroup.centralizer_le_normalizer _))
        (hH.hyp.sylow.1.to_le hV1T)
    rw [hbot, le_bot_iff] at h1
    have hc := (S126L23d.part2 h1222 F hH hZ).2
    rw [h1, Subgroup.card_bot] at hc
    omega
  exact ⟨⟨⟨le_sup_right, hO2⟩,
    fun h => hKM ((le_conjClosure K T).trans (le_sup_left.trans h)), hle.trans hHC⟩, hle⟩

theorem qInt_le_two (h1224 : Lemma12_6_24) (h1227 : Lemma12_6_27) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : InHz T L F.V1 H) :
    ∃ hE : IsElemAbelian 2 (tildeOf F.V1 (conjClosure F.V5 H)),
      qInt (tildeOf F.V1 H) (tildeOf F.V1 (conjClosure F.V5 H)) hE ≤ 2 :=
  ⟨_, (hypF98_of_inHz h1224 h1227 F hH hZ hHz).F916_3.1⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem mem_cComp_of_le {K H H₁ : Subgroup G} (hK : K ∈ cComp H₁) (hKH : K ≤ H)
    (hHH₁ : H ≤ H₁) : K ∈ cComp H :=
  ⟨hK.1, hK.2.1, A3.subnormal_of_le_of_le hK.2.2.1 hKH hHH₁, fun J hJK hJ1 hJp hJH =>
    hK.2.2.2 J hJK hJ1 hJp
      (A3.subnormal_trans (A3.subnormal_of_le_of_le hJH hJK.le hKH) hK.2.2.1)⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem isQuasisimple_quot_pCoreOf' {K : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) := by
  have e : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
    rw [pCoreOf, map_subtype_subgroupOf']
  have key : ∀ (N₁ N₂ : Subgroup ↥K) [N₁.Normal] [N₂.Normal], N₁ = N₂ →
      CFSG.IsQuasisimple (↥K ⧸ N₂) → CFSG.IsQuasisimple (↥K ⧸ N₁) := by
    intro N₁ N₂ _ _ h
    subst h
    exact id
  exact key _ _ e hq

theorem hypF918_of_isHK (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (h1227 : Lemma12_6_27)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H K : Subgroup G}
    (hHK : IsHK T L F.V1 H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    HypF918 T V L F.V1 F.V5 H K := by
  obtain ⟨⟨H₁, hH₁, hK⟩, hKM, rfl⟩ := hHK
  obtain ⟨hHz, hle⟩ := inHz_of_isHK h1222 F hH hZ hH₁ hK hKM
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hTH : T ≤ H₁ := le_sup_right.trans hH₁.1.1
  have hTs : IsSylowTwoOf T H₁ := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have hK0 : H₁ ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hH₁.1.2 hTs hK
  have hKH : K ≤ conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T) := (le_conjClosure K T).trans le_sup_left
  refine ⟨hypF98_of_inHz h1224 h1227 F hH hZ hHz, mem_cComp_of_le hK hKH hle,
    isQuasisimple_quot_pCoreOf' hq, le_antisymm ?_ (sup_le le_sup_left inf_le_right),
    hle.trans hK0⟩
  refine sup_le le_sup_left (le_sup_of_le_right (le_inf ?_ le_sup_right))
  exact sup_le ((S126L19b.L1_le_L F).trans le_sup_left) le_sup_right

end S126L30

end CFSG.Quasithin.H13
