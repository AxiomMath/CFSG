module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofCasesTools
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_center_pCoreOf_of_mem_zTwenty_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) {z : G} (hz : z ∈ zTwenty T) :
    z ∈ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ∧
      ∀ o ∈ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T), z * o * z⁻¹ = o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hXM : kTwenty M c ⊔ T ≤ M := sup_le hKM hT.sylow.le
  have hF : CFSG.generalizedFitting ↥(kTwenty M c ⊔ T) = CFSG.pCore 2 ↥(kTwenty M c ⊔ T) := by
    obtain ⟨P, hP, hP2, hMP⟩ := hT.mem_scriptM.1.1
    exact generalizedFitting_eq_of_pCoreOf_le hT.charTwoType ⟨P, hP, hP2, hMP⟩ hXM
      ((pCoreOf_le_of_isSylowOf hT.sylow).trans le_sup_right)
  have hTKT : CFSG.ABGLocalTools.IsSylowOf 2 T (kTwenty M c ⊔ T) :=
    hT.sylow.of_le le_sup_right hXM
  obtain ⟨w, hw, rfl⟩ := omegaZOf_le_omegaZOf_pCoreOf hF hTKT hz
  rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hw
  refine ⟨w.2, fun o ho => ?_⟩
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw.1 ⟨o, ho⟩)
  simp only [Subgroup.coe_mul] at h
  show (w : G) * o * (w : G)⁻¹ = o
  rw [← h]
  group

omit [Finite G] in
theorem commutator_le_left_of_le_normalizer {H K : Subgroup G}
    (hKH : K ≤ Subgroup.normalizer (H : Set G)) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  rw [commutatorElement_def]
  have : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hKH hk) _).mp (H.inv_mem hh)
  rw [show h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) by group]
  exact H.mul_mem hh this

@[expose] noncomputable def toSL {K : Subgroup G} {F : Type} [Field F]
    (α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
    ↥K →* SpecialLinearGroup (Fin 3) F :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp α

omit [Finite G] in
theorem coe_toSL {K : Subgroup G} {F : Type} [Field F]
    (α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (k : ↥K) :
    ((toSL α k : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((α k : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := by
  have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm (α k))
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

omit [Finite G] in
theorem toSL_surjective {K : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α) :
    Function.Surjective (toSL α) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.surjective.comp hα

omit [Finite G] in
theorem toSL_eq_one_iff {K : Subgroup G} {F : Type} [Field F]
    (α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (k : ↥K) :
    toSL α k = 1 ↔ α k = 1 := by
  simp [toSL]

omit [Finite G] in
theorem fix_of_natural {K B P : Subgroup G} {F : Type} [Field F] {r : ℕ}
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (β : ↥B →* Multiplicative (Fin r → Fin 3 → F))
    (hβinj : Function.Injective β)
    (hβ : ∀ (a : ↥K) (u v : ↥B), (v : G) = a * u * (a : G)⁻¹ → ∀ i,
      Multiplicative.toAdd (β v) i =
        (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u) i)
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) {g : SpecialLinearGroup (Fin 3) F}
    (hcoords : ∀ (x : Fin 3 → F),
      (∀ p : ↥K, (p : G) ∈ P → (α p : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) →
      ∀ k : ↥K, g⁻¹ * α k * g ∈ vstab F → (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x)
    {m : G} (hm : m ∈ B) (hmP : ∀ p ∈ P, p * m * p⁻¹ = m) (k : ↥K)
    (hk : g⁻¹ * α k * g ∈ vstab F) : (k : G) * m * (k : G)⁻¹ = m := by
  have hkm : (k : G) * m * (k : G)⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (hKB k.2) m).mp hm
  have heq : β ⟨_, hkm⟩ = β ⟨m, hm⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [hβ k ⟨m, hm⟩ ⟨_, hkm⟩ rfl i]
    refine hcoords _ (fun p hp => ?_) k hk
    exact (hβ p ⟨m, hm⟩ ⟨m, hm⟩ (hmP p hp).symm i).symm
  exact congrArg Subtype.val (hβinj heq)

theorem false_of_module_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (α : ↥(kTwenty M c) →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥(kTwenty M c), α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 (kTwenty M c))
    {B : Subgroup G} (hBQ : B ≤ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))
    (hKB : kTwenty M c ≤ Subgroup.normalizer (B : Set G))
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hZK : ∀ z ∈ zTwenty T, ∀ k ∈ kTwenty M c, k * z * k⁻¹ * z⁻¹ ∈ B)
    (hfix : ∀ g : SpecialLinearGroup (Fin 3) F, (∀ (x : Fin 3 → F),
        (∀ p : ↥(kTwenty M c), (p : G) ∈ T ⊓ kTwenty M c →
          (α p : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) →
        ∀ k : ↥(kTwenty M c), g⁻¹ * α k * g ∈ vstab F →
          (α k : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) →
      ∀ m ∈ B, (∀ p ∈ T ⊓ kTwenty M c, p * m * p⁻¹ = m) →
        ∀ k : ↥(kTwenty M c), g⁻¹ * α k * g ∈ vstab F → (k : G) * m * (k : G)⁻¹ = m)
    (hcore : CFSG.Quasithin.C134NotCentralizerCore (kTwenty M c ⊔ T) (sTwenty M N c T)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ kTwenty M c) (kTwenty M c) :=
    hT.sylow.inf_of_le_normalizer hKM hMK
  obtain ⟨g, hg⟩ := exists_coords_fixed α hαs hP
  set α' : ↥(kTwenty M c) →* SpecialLinearGroup (Fin 3) F :=
    (MulAut.conj g⁻¹).toMonoidHom.comp α with hα'
  have hα'_apply : ∀ k, α' k = g⁻¹ * α k * g := by
    intro k
    simp [hα']
  have hB2 : IsPGroup 2 B := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hBQ
  have hK0 : ∀ k : ↥(kTwenty M c), α' k ∈ vstab F →
      (k : G) ∈ Subgroup.centralizer (zTwenty T : Set G) := by
    intro k hk
    rw [hα'_apply] at hk
    have h := centralizer_of_transfer (A := B) (P := T ⊓ kTwenty M c) (Z := (zTwenty T : Set G))
      hKB hBc hB2 hP
      (fun z hz a ha => (mem_center_pCoreOf_of_mem_zTwenty_core hT hz).2 a (hBQ ha))
      (fun z hz p hp => by rw [(mem_and_commute_of_mem_zTwenty hz).2 p hp.1]; group)
      hZK k.2 (fun m hm hmP => hfix g hg m hm hmP k hk)
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have := h z hz
    calc z * (k : G) = (k : G) * z * (k : G)⁻¹ * k := by rw [this]
      _ = k * z := by group
  have hS := sTwenty_eq_of_vstab hT.sylow hKM hMK hTN h207 hKN hLQ α'
    (fun x => by
      obtain ⟨k, hk⟩ := hαs (g * x * g⁻¹)
      exact ⟨k, by rw [hα'_apply, hk]; group⟩)
    (fun k => by
      rw [hα'_apply, ← hαk k]
      constructor
      · intro h
        calc α k = g * (g⁻¹ * α k * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      · intro h
        rw [h]
        group)
    hK0
  exact false_of_sTwenty_eq_core hT hTN hS hcore

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf_two {K : Subgroup G} (x : ↥K) :
    x ∈ CFSG.pCore 2 ↥K ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff x).symm

omit [Finite G] in
theorem toSL_eq_one_iff_mem {K : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hαk : α.ker = CFSG.pCore 2 ↥K)
    (k : ↥K) : toSL α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K := by
  rw [toSL_eq_one_iff, ← MonoidHom.mem_ker, hαk, mem_pCore_iff_mem_pCoreOf_two]

theorem commutator_mem_c134Q_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) {z k : G} (hz : z ∈ zTwenty T) (hk : k ∈ kTwenty M c) :
    k * z * k⁻¹ * z⁻¹ ∈ CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) := by
  have h := Subgroup.commutator_mem_commutator
    (mem_center_pCoreOf_of_mem_zTwenty_core hT hz).1 hk
  rw [commutatorElement_def] at h
  rw [show k * z * k⁻¹ * z⁻¹ = (z * k * z⁻¹ * k⁻¹)⁻¹ by group]
  exact Subgroup.inv_mem _ h

omit [Finite G] in
theorem c134Q_le {M T : Subgroup G} {c : G} :
    CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤
      CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) :=
  commutator_le_left_of_le_normalizer
    (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

omit [Finite G] in
theorem comm_of_injective {B : Subgroup G} {W : Type} [CommGroup W] (β : ↥B →* W)
    (hβ : Function.Injective β) : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  intro x hx y hy
  have : β (⟨x, hx⟩ * ⟨y, hy⟩) = β (⟨y, hy⟩ * ⟨x, hx⟩) := by rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val (hβ this)

omit [Finite G] in
theorem injective_of_ker_eq {B : Subgroup G} {W : Type} [Group W] (β : ↥B →* W)
    (hβ : β.ker = (⊥ : Subgroup G).subgroupOf B) : Function.Injective β := by
  rw [← MonoidHom.ker_eq_bot_iff, hβ]
  ext x
  simp

theorem false_of_isC134Case_two_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 2 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False := by
  obtain ⟨⟨n', F, _, _, α, hF, ⟨hαs, hαk⟩, hKQ, -, β, -, hβk, hβ⟩, hcore⟩ := hi
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hβinj := injective_of_ker_eq β hβk
  refine false_of_module_core hT hTN h207 hKN hLQ (toSL α) (toSL_surjective hαs)
    (toSL_eq_one_iff_mem hαk) c134Q_le hKQ (comm_of_injective β hβinj)
    (fun z hz k hk => commutator_mem_c134Q_core hT hz hk) (fun g hg m hm hmP k hk => ?_) hcore
  refine fix_of_natural (toSL α) β hβinj (fun a u v huv i => ?_) hKQ hg hm hmP k hk
  rw [hβ a u v huv i, coe_toSL]
  rfl

theorem false_of_isC134Case_two {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 2 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False :=
  false_of_isC134Case_two_core hT.toCtx20 hTN h207 hKN hLQ hi

omit [Finite G] in
theorem equivariance_toSL {K B : Subgroup G} {F : Type} [Field F] {r : ℕ}
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    {β : ↥B →* Multiplicative (Fin r → Fin 3 → F)}
    (hβ : ∀ (a : ↥K) (u v : ↥B), (v : G) = a * u * (a : G)⁻¹ → ∀ i : Fin r,
      Multiplicative.toAdd (β v) i =
        (CFSG.Quasithin.moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
          (Multiplicative.toAdd (β u) i)) :
    ∀ (a : ↥K) (u v : ↥B), (v : G) = a * u * (a : G)⁻¹ → ∀ i,
      Multiplicative.toAdd (β v) i =
        (toSL α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u) i := by
  intro a u v huv i
  rw [hβ a u v huv i, coe_toSL]
  rfl

omit [Finite G] in
theorem le_normalizer_centerOf {Q K : Subgroup G}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) :
    K ≤ Subgroup.normalizer ((CFSG.Quasithin.centerOf Q : Subgroup G) : Set G) := by
  have key : ∀ k ∈ Subgroup.normalizer (Q : Set G), ∀ m ∈ CFSG.Quasithin.centerOf Q,
      k * m * k⁻¹ ∈ CFSG.Quasithin.centerOf Q := by
    intro k hk m hm
    have hQ := Subgroup.mem_normalizer_iff.mp hk
    refine ⟨(hQ m).mp hm.1, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq' : k⁻¹ * q * k ∈ Q :=
      (hQ _).mpr (by rw [show k * (k⁻¹ * q * k) * k⁻¹ = q by group]; exact hq)
    have h := Subgroup.mem_centralizer_iff.mp hm.2 _ hq'
    calc q * (k * m * k⁻¹) = k * ((k⁻¹ * q * k) * m) * k⁻¹ := by group
      _ = k * (m * (k⁻¹ * q * k)) * k⁻¹ := by rw [h]
      _ = k * m * k⁻¹ * q := by group
  intro k hk
  refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨key k (hKQ hk) m, fun h => ?_⟩
  have := key k⁻¹ (Subgroup.inv_mem _ (hKQ hk)) _ h
  rwa [show k⁻¹ * (k * m * k⁻¹) * k⁻¹⁻¹ = m by group] at this

omit [Finite G] in
theorem comm_of_mem_centerOf {Q : Subgroup G} :
    ∀ x ∈ CFSG.Quasithin.centerOf Q, ∀ y ∈ CFSG.Quasithin.centerOf Q, x * y = y * x :=
  fun x hx _ hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx.1

theorem commutator_mem_centerOf_c134Q_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T)
    (hKQ : kTwenty M c ≤ Subgroup.normalizer
      ((CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) : Subgroup G) : Set G))
    {z k : G} (hz : z ∈ zTwenty T) (hk : k ∈ kTwenty M c) :
    k * z * k⁻¹ * z⁻¹ ∈
      CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)) := by
  refine ⟨commutator_mem_c134Q_core hT hz hk, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  have hzc := (mem_center_pCoreOf_of_mem_zTwenty_core hT hz).2
  have hq1 : z * q * z⁻¹ = q := hzc q (c134Q_le hq)
  have hq2' : k⁻¹ * q * k ∈ CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) := by
    have := (Subgroup.mem_normalizer_iff.mp (hKQ (Subgroup.inv_mem _ hk)) q).mp hq
    rwa [inv_inv] at this
  have hq2 : z * (k⁻¹ * q * k) * z⁻¹ = k⁻¹ * q * k := hzc _ (c134Q_le hq2')
  have e1 : z⁻¹ * q = q * z⁻¹ := by
    calc z⁻¹ * q = z⁻¹ * (z * q * z⁻¹) := by rw [hq1]
      _ = q * z⁻¹ := by group
  have e2 : z * (k⁻¹ * q * k) = (k⁻¹ * q * k) * z := by
    calc z * (k⁻¹ * q * k) = z * (k⁻¹ * q * k) * z⁻¹ * z := by group
      _ = (k⁻¹ * q * k) * z := by rw [hq2]
  calc q * (k * z * k⁻¹ * z⁻¹) = k * ((k⁻¹ * q * k) * z) * k⁻¹ * z⁻¹ := by group
    _ = k * (z * (k⁻¹ * q * k)) * k⁻¹ * z⁻¹ := by rw [e2]
    _ = k * z * k⁻¹ * (q * z⁻¹) := by group
    _ = k * z * k⁻¹ * (z⁻¹ * q) := by rw [e1]
    _ = k * z * k⁻¹ * z⁻¹ * q := by group

theorem false_of_isC134Case_three_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 3 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False := by
  obtain ⟨⟨n', F, _, _, α, hF, ⟨hαs, hαk⟩, ⟨hKZ, -, β, -, hβk, hβ⟩, ⟨hKQ, -⟩⟩, hcore⟩ := hi
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hβinj := injective_of_ker_eq β hβk
  refine false_of_module_core hT hTN h207 hKN hLQ (toSL α) (toSL_surjective hαs)
    (toSL_eq_one_iff_mem hαk) (inf_le_left.trans c134Q_le) hKZ comm_of_mem_centerOf
    (fun z hz k hk => commutator_mem_centerOf_c134Q_core hT hKQ hz hk)
    (fun g hg m hm hmP k hk => ?_) hcore
  exact fix_of_natural (toSL α) β hβinj (equivariance_toSL hβ) hKZ hg hm hmP k hk

theorem false_of_isC134Case_three {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 3 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False :=
  false_of_isC134Case_three_core hT.toCtx20 hTN h207 hKN hLQ hi

theorem false_of_isC134Case_four_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 4 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False := by
  obtain ⟨⟨n', F, _, _, α, hF, ⟨hαs, hαk⟩, -, -, hZdec, -, ⟨hKU, -, β, -, hβk, hβ⟩, -, -,
    ⟨hKQ, -⟩⟩, hcore⟩ := hi
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hβinj := injective_of_ker_eq β hβk
  refine false_of_module_core hT hTN h207 hKN hLQ (toSL α) (toSL_surjective hαs)
    (toSL_eq_one_iff_mem hαk) (inf_le_left.trans c134Q_le) (le_normalizer_centerOf hKQ)
    comm_of_mem_centerOf (fun z hz k hk => commutator_mem_centerOf_c134Q_core hT hKQ hz hk)
    (fun g hg m hm hmP k hk => ?_) hcore
  have hZc := comm_of_mem_centerOf (Q := CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c))
  have hCZ := (le_sup_left (a := CFSG.Quasithin.c134CQ (kTwenty M c ⊔ T) (kTwenty M c))).trans_eq
    hZdec.symm
  have hUZ := (le_sup_right (b := ⁅CFSG.Quasithin.centerOf
    (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)), kTwenty M c⁆)).trans_eq hZdec.symm
  have hLE : CFSG.Quasithin.c134CQ (kTwenty M c ⊔ T) (kTwenty M c) ≤
      Subgroup.normalizer ((⁅CFSG.Quasithin.centerOf
        (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)), kTwenty M c⁆ :
          Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [show x * u * x⁻¹ = u by rw [hZc x (hCZ hx) u (hUZ hu)]; group]
      exact hu
    · intro hu
      have h := hZc x (hCZ hx) _ (hUZ hu)
      have h2 : x * (x * u * x⁻¹) = x * u := by rw [h]; group
      have h3 : x * u * x⁻¹ = u := mul_left_cancel h2
      rw [← h3]
      exact hu
  have hm' : m ∈ ((CFSG.Quasithin.c134CQ (kTwenty M c ⊔ T) (kTwenty M c) : Set G) *
      ((⁅CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)),
        kTwenty M c⁆ : Subgroup G) : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE, ← hZdec]
    exact hm
  obtain ⟨a, ha, u, hu, rfl⟩ := hm'
  have hapc : ∀ p ∈ kTwenty M c, p * a * p⁻¹ = a := fun p hp => by
    rw [Subgroup.mem_centralizer_iff.mp ha.2 p hp]
    group
  have huP : ∀ p ∈ T ⊓ kTwenty M c, p * u * p⁻¹ = u := by
    intro p hp
    have h1 := hmP p hp
    have h2 := hapc p hp.2
    calc p * u * p⁻¹ = (p * a * p⁻¹)⁻¹ * (p * (a * u) * p⁻¹) := by group
      _ = u := by rw [h1, h2]; group
  have hku := fix_of_natural (toSL α) β hβinj (equivariance_toSL hβ) hKU hg hu huP k hk
  calc (k : G) * (a * u) * (k : G)⁻¹ = ((k : G) * a * (k : G)⁻¹) * ((k : G) * u * (k : G)⁻¹) :=
        by group
    _ = a * u := by rw [hapc k k.2, hku]

theorem false_of_isC134Case_four {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 4 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False :=
  false_of_isC134Case_four_core hT.toCtx20 hTN h207 hKN hLQ hi

end CFSG.RankThree.PartTwo.Sec20
