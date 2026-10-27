module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Irr
public import CFSG.Quasithin.Background.B610
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SL2Model
open scoped MatrixGroups IsMulCommutative

@[expose] def Stmt5_1_7_one_nat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → ⁅V, thompsonJ T⁆ ≠ ⊥ → IsNatQuotCh5 L V n →
      IsSylowTwoOf (baum T ⊓ L) L

@[expose] def Stmt5_1_7_one_A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → ⁅V, thompsonJ T⁆ ≠ ⊥ → n = 2 → IsCommCentralSplit L T V →
    IsBarS5 L T V → IsS5ModCh5 L T ⁅V, L⁆ →
      Subgroup.normalizer (baum T : Set G) ≤ M

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem noncentralTwoChiefFactorsInO2 (h : Hyp5_0_1 G T M L n) :
    NoncentralTwoChiefFactorsInO2 L := by
  rintro A B ⟨hOB, hBA, hAL, hLA, hLB, -, h2⟩
  exfalso
  rcases h.le_pCoreOf_or_eq hAL hLA with hA | hAeq
  · exact (not_le_of_gt hBA) (hA.trans hOB)
  · have hBL : B ≤ L := hBA.le.trans hAL
    have hBn : (B.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBL).mpr hLB
    have h2' : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ B := fun x hx => h2 x (by rw [hAeq]; exact hx)
    exact hBA.ne ((h.eq_of_isPGroup_quot hBL hBn h2').trans hAeq.symm)

theorem exists_isCh5Module (h : Hyp5_0_1 G T M L n) : ∃ V : Subgroup G, IsCh5Module T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hXf⟩ := isFaithfulLocal_iff_isXf.mp h.faithful
  have hsub : IsSubnormal L (L ⊔ T) :=
    IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr h.sup_le_normalizer)
      (IsSubnormal.refl _)
  obtain ⟨V, hV, hVL⟩ :=
    A4.exists_isTwoReducedIn_of_isXf hXf.1 hsub h.noncentralTwoChiefFactorsInO2 hXf.2
  obtain ⟨hVle, hR⟩ := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hV
  exact ⟨V, hVle, hR, hVL⟩

end Hyp5_0_1

section Natural

variable {G : Type} [Group G]

theorem isNaturalL2Prime_of_isNatQuotCh5 {L V : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hnq : IsNatQuotCh5 L V n) : IsNaturalL2Prime n L V := by
  classical
  obtain ⟨hLV, hVc, F, _, _, hF, π, hπ⟩ := hnq
  have hπi : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  have : Fintype F := Fintype.ofFinite F
  set U : Subgroup G := ⁅V, L⁆ with hU
  have hUV : U ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hLU : L ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of hLV Subgroup.le_normalizer
  let φ : ↥L →* ↥(autOn L V) := InternalSec.autOnHom hLV
  let πe : ↥(StatedSL 2 F) ≃* ↥(autOn L V) := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let α : ↥L →* ↥(StatedSL 2 F) := πe.symm.toMonoidHom.comp φ
  have hαs : Function.Surjective α :=
    πe.symm.surjective.comp (InternalSec.autOnHom_surjective hLV)
  have hπα : ∀ a : ↥L, π (α a) = φ a := fun a => πe.apply_symm_apply (φ a)
  have hφ : ∀ (a : ↥L) (v : ↥V),
      (((φ a : ↥(autOn L V)) : MulAut ↥V) v : G) = a * v * (a : G)⁻¹ :=
    fun a v => CFSG.QuasithinUnique.Setup.rho_apply_coe hLV a v
  let ι₀ : ↥(FFModel.nat (StatedSL 2 F)).sec →* Multiplicative (Fin 2 → F) :=
    { toFun := fun m => m.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ε : ↥(FFModel.nat (StatedSL 2 F)).sec ⧸
      (FFModel.nat (StatedSL 2 F)).ker.subgroupOf (FFModel.nat (StatedSL 2 F)).sec →*
      Multiplicative (Fin 2 → F) :=
    QuotientGroup.lift _ ι₀ (by
      intro m hm
      rw [MonoidHom.mem_ker]
      exact Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp hm))
  have hε : ∀ m, ε (QuotientGroup.mk m) = ι₀ m := fun _ => rfl
  have hεi : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    induction q using QuotientGroup.induction_on with | H m => ?_
    rw [MonoidHom.mem_ker, hε] at hq
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_bot.mpr hq
  have hβV : ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * (a : G)⁻¹ →
      Multiplicative.toAdd (ε (β ⟨v, Subgroup.mem_top v⟩)) =
        ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (ε (β ⟨u, Subgroup.mem_top u⟩))) := by
    intro a u v huv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, Subgroup.mem_top u⟩)
    have key := hβe (α a) ⟨u, Subgroup.mem_top u⟩ m (Subgroup.mem_top _) (Subgroup.mem_top _)
      hm.symm
    have hv : (⟨((π (α a) : ↥(autOn L V)) : MulAut ↥V) u, Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup ↥V)) = ⟨v, Subgroup.mem_top v⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      show ((((π (α a)) : ↥(autOn L V)) : MulAut ↥V) u : G) = v
      rw [hπα, hφ, huv]
    rw [hv] at key
    rw [key, hε, ← hm, hε]
    rfl
  have hsurj : ∀ x : Multiplicative (Fin 2 → F), ∃ v : ↥V,
      ε (β ⟨v, Subgroup.mem_top v⟩) = x := by
    intro x
    obtain ⟨q, hq⟩ := hβs (QuotientGroup.mk ⟨x, Subgroup.mem_top x⟩)
    have hq1 : (⟨q.1, Subgroup.mem_top q.1⟩ : ↥(⊤ : Subgroup ↥V)) = q := rfl
    exact ⟨q.1, by rw [hq1, hq]; rfl⟩
  let ι : ↥U →* ↥(⊤ : Subgroup ↥V) :=
    { toFun := fun u => ⟨⟨u, hUV u.2⟩, Subgroup.mem_top _⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let β' : ↥U →* Multiplicative (Fin 2 → F) := ε.comp (β.comp ι)
  have hc : ∀ (a : ↥L) (v : ↥V), (a : G) * v * (a : G)⁻¹ * (v : G)⁻¹ ∈ U := by
    intro a v
    rw [hU, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator a.2 v.2
  have hcomm : ∀ (a : ↥L) (v : ↥V), Multiplicative.toAdd (β' ⟨_, hc a v⟩) =
      ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (ε (β ⟨v, Subgroup.mem_top v⟩))) -
        Multiplicative.toAdd (ε (β ⟨v, Subgroup.mem_top v⟩)) := by
    intro a v
    have hav : (a : G) * v * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV a.2) v).mp v.2
    have e1 : (⟨⟨_, hUV (hc a v)⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥V)) =
        ⟨⟨_, hav⟩, Subgroup.mem_top _⟩ * (⟨v, Subgroup.mem_top v⟩)⁻¹ := rfl
    show Multiplicative.toAdd (ε (β ⟨⟨_, hUV (hc a v)⟩, Subgroup.mem_top _⟩)) = _
    rw [e1, map_mul, map_mul, map_inv, map_inv, toAdd_mul, toAdd_inv,
      hβV a v ⟨_, hav⟩ rfl, sub_eq_add_neg]
  refine Or.inl ⟨hn, F, inferInstance, inferInstance,
    by rw [← Nat.card_eq_fintype_card]; exact hF, hLU, α, hαs, ?_, β', ?_, ?_, ?_⟩
  ·
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have h1 : α a = 1 ↔ φ a = 1 := by
      show πe.symm (φ a) = 1 ↔ φ a = 1
      rw [MulEquiv.map_eq_one_iff]
    rw [h1, ← MonoidHom.mem_ker, InternalSec.mem_ker_autOnHom]
    exact ⟨fun h2 => ⟨a.2, h2⟩, fun h2 => h2.2⟩
  ·
    intro y
    obtain ⟨v₁, hv₁⟩ := hsurj (Multiplicative.ofAdd ![0, Multiplicative.toAdd y 0])
    obtain ⟨v₂, hv₂⟩ := hsurj (Multiplicative.ofAdd ![Multiplicative.toAdd y 1, 0])
    obtain ⟨a₁, ha₁⟩ := hαs (specialLinearGroupEquivStatedSL 2 F (e12 1))
    obtain ⟨a₂, ha₂⟩ := hαs (specialLinearGroupEquivStatedSL 2 F (e21 1))
    refine ⟨⟨_, hc a₁ v₁⟩ * ⟨_, hc a₂ v₂⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, hcomm, hcomm, hv₁, hv₂, ha₁, ha₂,
      specialLinearGroupEquivStatedSL_coe, specialLinearGroupEquivStatedSL_coe, e12_coe, e21_coe,
      toAdd_ofAdd, toAdd_ofAdd]
    funext i
    fin_cases i <;>
      simp [Matrix.vecHead, Matrix.vecTail]
  ·
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show ε (β (ι u)) = 1 ↔ _
    rw [map_eq_one_iff ε hεi, hβk, Subgroup.mem_subgroupOf]
    exact ⟨fun h2 => ⟨u.2, h2⟩, fun h2 => h2.2⟩
  ·
    intro a u v huv
    exact hβV a ⟨u, hUV u.2⟩ ⟨v, hUV v.2⟩ huv

end Natural

theorem stmt5_1_7_one_of (h512 : Stmt5_1_2) (h432 : Stmt4_3_2) (hnat : Stmt5_1_7_one_nat)
    (hA5 : Stmt5_1_7_one_A5) : A5.Stmt5_1_7_one := by
  intro G _ _ T L M hs hnab hK hT hLmax hLf hlie hM hTM hLM hMN
  obtain ⟨n, hn2, hL2⟩ := hlie
  have h : Hyp5_0_1 G T M L n :=
    { simple := hs
      nonabelian := hnab
      qtke := hK
      sylow := hT
      maxTwoLocal := hM
      T_le := hTM
      maximal := hLmax
      faithful := hLf
      L_le := hLM
      normal := hMN
      two_le := hn2
      lie := hL2 }
  obtain ⟨V, hV⟩ := h.exists_isCh5Module
  rcases h512 G T M L V n h hV with ⟨-, -, -, -, hU⟩ | ⟨hJ, hnq⟩ |
      ⟨hJ, hn, hsplit, hbar, hS5⟩
  · exact hU.1.2
  · exact (h432 G T M L hs hnab hK hT hM hTM hLmax hLf hLM hMN ⟨n, hn2, hL2⟩).2 (baum T)
      inf_le_left (hnat G T M L V n h hV hJ hnq)
  · exact hA5 G T M L V n h hV hJ hn hsplit hbar hS5

end CFSG.Quasithin.H13
