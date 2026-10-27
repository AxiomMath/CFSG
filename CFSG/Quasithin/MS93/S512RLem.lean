module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S512TStmt
public import CFSG.Quasithin.MS93.S512TThree
public import CFSG.Quasithin.MS93.S512ZBase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512R

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem relIndex_le_card_commutator_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ Nat.card ↥⁅Uq M T L, E⁆ := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  rw [S512T.relIndex_eq_pow_M h hd hEM, ← hFq, ← Module.natCard_eq_pow_finrank (K := F)]
  have hUE : ⁅Uq M T L, E⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hEM.trans (le_normalizer_Uq h.le_normalizer))
  let f : ↥⁅Uq M T L, E⁆ → ↥(MSP.commSp ((E.subgroupOf M).map a)) := fun x =>
    ⟨c.vec ⟨x, hUE x.2⟩, S5B.vec_mem_commSp h c hEM ⟨x, hUE x.2⟩ x.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, rfl⟩ := S5B.exists_mem_commutator_vec_eq h c hw
    exact ⟨⟨u, hu⟩, rfl⟩
  exact Nat.card_le_card_of_surjective f hf

theorem relIndex_le_card_commutator (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) :
    (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L δ) ≤
      Nat.card ↥⁅S5.uSub h.le L δ, E⁆ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M, S5B.uSub_smul h.le hLn, S5B.uSub_baseA h,
    ← Subgroup.map_commutator, ← imM_commutator h.le (Uq_le h.L_le) hE₀M,
    Subgroup.card_map_of_injective (MulAut.conj g).injective,
    S5B.card_imM h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)]
  exact relIndex_le_card_commutator_M h hd hE₀M

omit [Finite G] in
theorem centralizer_sup_eq (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  refine le_antisymm (le_inf (Subgroup.centralizer_le fun x hx => Subgroup.mem_sup_left hx)
    (Subgroup.centralizer_le fun x hx => Subgroup.mem_sup_right hx)) ?_
  rintro x ⟨hA, hB⟩
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro z rfl
      exact (Subgroup.mem_centralizer_iff.1 hA y hy).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro z rfl
      exact (Subgroup.mem_centralizer_iff.1 hB y hy).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hy) x rfl).symm

theorem zm_smul_le_nclStab (h : PUHyp M T L) {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) (γ : Vtx (puAmalgam h.le)) :
    ZM _ (y • γ) ≤ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) := by
  rw [zm_smul]
  exact le_iSup (f := fun g : ↥(stab (puAmalgam h.le) (baseA (puAmalgam h.le))) =>
    (ZM _ γ).map (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom) ⟨y, hy⟩

theorem zm_le_nclStab (h : PUHyp M T L) (γ : Vtx (puAmalgam h.le)) :
    ZM _ γ ≤ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) := by
  have := zm_smul_le_nclStab h (one_mem _) γ
  rwa [one_smul] at this

@[expose] def Lem56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ l : Submodule F (MSP.V4 F),
        S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
        2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
          Set (puAmalgam h.le).Universal)).relIndex
            (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) →
        ∀ R : Subgroup (puAmalgam h.le).Universal,
          R ≤ ⁅S5.nclStab _ (baseA (puAmalgam h.le))
              (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
            S5.nclStab _ (baseA (puAmalgam h.le))
              (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2))⁆ →
          R ≤ stabCenter _ (baseA (puAmalgam h.le)) → Nat.card R ≤ 2 ^ k

@[expose] def Three56ResA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le),
        S5B.IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        ∀ l : Submodule F (MSP.V4 F),
          S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
        ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
          S5.Concl56 h (2 ^ k) a α' l g x →
          ∀ w : (puAmalgam h.le).Universal,
            ((w = x ∧ μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ∨
              (w = x⁻¹ ∧ μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)) →
          ¬ ZM _ (w • α') ≤ Subgroup.normalizer
            (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
              XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) →
          2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
            Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁) →
          ¬ IsCritical _ μ₁ (w • geo _ (baseA (puAmalgam h.le)) α' 2) →
          (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k

@[expose] def ThreeAlt2L : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        (∀ l : Submodule F (MSP.V4 F),
          ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) →
        (∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) →
        ¬ Xq M = Uq M T L ⊔ Zq M L →
        ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
          S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x →
          (μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
            μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) →
          ¬ puTrans h.le L (baseA _) ≤
            S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
              S5.zHat _ (baseA _) α' →
          ¬ Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤ Subgroup.normalizer
            ((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Subgroup _) :
              Set (puAmalgam h.le).Universal) →
          2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
            Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁) →
          (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k

theorem threeAlt2_of (h32 : S32) (h58 : S5B.S58) (hres : ThreeAlt2L) : S512T.ThreeAlt2 := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hq1 hq h56 hline hXU g hg x hx hc55
    hμeq hL hTY
  by_cases hlarge : 2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁)
  · exact hres G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hq1 hq h56 hline hXU g hg x hx
      hc55 hμeq hL hTY hlarge
  push Not at hlarge
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨hc, hαβ, hcμ, ⟨y, hy, hμy⟩, hdμ, hmid, -⟩ := S512T.chain_geo h hb4 hch
  rw [S512T.relIndex_bSub_zm_eq h hb4 hcμ hmid]
  refine le_antisymm
    ((S512Z.relIndex_bSub_le_relIndex_centralizer h32 h hb hcμ.1 hdμ).trans hlarge) ?_
  have h1 := (h58 G M T L h hmin hb k F _ _ a hd α' hc hαβ).2.2
  rw [hμy, S5B.relIndex_bSub_uSub_smul h hy]
  exact h1

end S512R

end CFSG.Quasithin.MS93
