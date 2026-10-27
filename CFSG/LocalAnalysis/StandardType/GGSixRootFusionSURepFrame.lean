module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepNoSingle

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv diagHom_unitary unitary_mul
  permGL_unitary det_permGL diagHom_commute)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace SURep

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F]

@[expose] def GGFrameActs (φ : ↥(unitarySU 2 f F n) →* G) (b : G) (τ : Fin n → Fˣ) : Prop :=
  (∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) ∧ ∀ s s' : ↥(unitarySU 2 f F n),
    (s' : GL (Fin n) F) = diagHom n τ * s * (diagHom n τ)⁻¹ → b * φ s * b⁻¹ = φ s'

@[expose] def GGFrameDiagU (φ : ↥(unitarySU 2 f F n) →* G) (b : G) : Prop :=
  ∃ τ : Fin n → Fˣ, GGFrameActs φ b τ

@[expose] def GGFrameKer (φ : ↥(unitarySU 2 f F n) →* G) : Prop :=
  ∀ z : ↥(unitarySU 2 f F n), φ z = 1 →
    ∃ c : F, ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c

theorem norm_inv_eq_one {τ : Fin n → Fˣ} (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) (i : Fin n) :
    ((τ⁻¹ i : Fˣ) : F) ^ (2 ^ f + 1) = 1 := by
  rw [Pi.inv_apply, Units.val_inv_eq_inv_val, inv_pow, hτ i, inv_one]

theorem conj_mem_unitarySU (h : UnitaryFieldData 2 f F) {τ : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) {s : GL (Fin n) F} (hs : s ∈ unitarySU 2 f F n) :
    diagHom n τ * s * (diagHom n τ)⁻¹ ∈ unitarySU 2 f F n := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).mp hs
  rw [mem_unitarySU_iff h]
  have hinv : (diagHom n τ)⁻¹ = diagHom n τ⁻¹ := (map_inv _ τ).symm
  rw [hinv]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, det_diagHom, det_diagHom,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (τ i).ne_zero]
  · rw [Units.val_mul, Units.val_mul]
    exact unitary_mul h (unitary_mul h (diagHom_unitary h hτ) hu)
      (diagHom_unitary h (norm_inv_eq_one hτ))

@[expose] noncomputable def conjU (h : UnitaryFieldData 2 f F) {τ : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) (s : ↥(unitarySU 2 f F n)) :
    ↥(unitarySU 2 f F n) :=
  ⟨_, conj_mem_unitarySU h hτ s.2⟩

theorem coe_conjU (h : UnitaryFieldData 2 f F) {τ : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) (s : ↥(unitarySU 2 f F n)) :
    ((conjU h hτ s : ↥(unitarySU 2 f F n)) : GL (Fin n) F) =
      diagHom n τ * s * (diagHom n τ)⁻¹ :=
  rfl

theorem GGFrameActs.apply {φ : ↥(unitarySU 2 f F n) →* G} {b : G} {τ : Fin n → Fˣ}
    (hb : GGFrameActs φ b τ) (h : UnitaryFieldData 2 f F) (s : ↥(unitarySU 2 f F n)) :
    b * φ s * b⁻¹ = φ (conjU h hb.1 s) :=
  hb.2 s _ rfl

theorem frameActs_one (φ : ↥(unitarySU 2 f F n) →* G) : GGFrameActs φ 1 1 := by
  refine ⟨fun i => by simp, fun s s' hs' => ?_⟩
  have : s' = s := Subtype.ext (by rw [hs', map_one, one_mul, inv_one, mul_one])
  rw [this, one_mul, inv_one, mul_one]

theorem GGFrameActs.mul {φ : ↥(unitarySU 2 f F n) →* G} (h : UnitaryFieldData 2 f F) {b c : G}
    {τ τ' : Fin n → Fˣ} (hb : GGFrameActs φ b τ) (hc : GGFrameActs φ c τ') :
    GGFrameActs φ (b * c) (τ * τ') := by
  refine ⟨fun i => by rw [Pi.mul_apply, Units.val_mul, mul_pow, hb.1 i, hc.1 i, one_mul],
    fun s s' hs' => ?_⟩
  have e1 := hc.apply h s
  have e2 := hb.apply h (conjU h hc.1 s)
  have hs'' : s' = conjU h hb.1 (conjU h hc.1 s) := by
    apply Subtype.ext
    rw [coe_conjU, coe_conjU, hs', map_mul]
    group
  calc b * c * φ s * (b * c)⁻¹ = b * (c * φ s * c⁻¹) * b⁻¹ := by group
    _ = φ s' := by rw [e1, e2, hs'']

theorem GGFrameActs.pow {φ : ↥(unitarySU 2 f F n) →* G} (h : UnitaryFieldData 2 f F) {b : G}
    {τ : Fin n → Fˣ} (hb : GGFrameActs φ b τ) : ∀ k : ℕ, GGFrameActs φ (b ^ k) (τ ^ k)
  | 0 => by rw [pow_zero, pow_zero]; exact frameActs_one φ
  | k + 1 => by rw [pow_succ, pow_succ]; exact (hb.pow h k).mul h hb

theorem conjU_apply (h : UnitaryFieldData 2 f F) {τ : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) (s : ↥(unitarySU 2 f F n)) (a c : Fin n) :
    (((conjU h hτ s : ↥(unitarySU 2 f F n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c =
      (τ a : F) * ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c * ((τ c)⁻¹ : Fˣ) := by
  have hinv : (diagHom n τ)⁻¹ = diagHom n τ⁻¹ := (map_inv _ τ).symm
  rw [coe_conjU, hinv, Units.val_mul, Units.val_mul, coe_diagHom, coe_diagHom, mul_diagonal,
    diagonal_mul]
  rfl

theorem conjU_eq_of_ratio (h : UnitaryFieldData 2 f F) {τ τ' : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) (hτ' : ∀ i, (τ' i : F) ^ (2 ^ f + 1) = 1)
    (hr : ∀ a c, τ a * (τ c)⁻¹ = τ' a * (τ' c)⁻¹) (s : ↥(unitarySU 2 f F n)) :
    conjU h hτ s = conjU h hτ' s := by
  apply Subtype.ext
  apply Units.ext
  ext a c
  rw [conjU_apply, conjU_apply]
  have e := congrArg (fun u : Fˣ => (u : F)) (hr a c)
  simp only [Units.val_mul] at e
  calc (τ a : F) * ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c * ((τ c)⁻¹ : Fˣ) =
      ((τ a : F) * ((τ c)⁻¹ : Fˣ)) * ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c := by
        ring
    _ = ((τ' a : F) * ((τ' c)⁻¹ : Fˣ)) * ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c := by
        rw [e]
    _ = _ := by ring

theorem conjU_eq_self_of_diag (h : UnitaryFieldData 2 f F) {τ : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) {d : ↥(unitarySU 2 f F n)} {δ : Fin n → Fˣ}
    (hd : (d : GL (Fin n) F) = diagHom n δ) : conjU h hτ d = d := by
  apply Subtype.ext
  rw [coe_conjU, hd, (diagHom_commute τ δ).eq, mul_inv_cancel_right]

theorem conjU_one (h : UnitaryFieldData 2 f F) (s : ↥(unitarySU 2 f F n)) :
    conjU h (τ := 1) (fun i => by simp) s = s := by
  apply Subtype.ext
  rw [coe_conjU, map_one, one_mul, inv_one, mul_one]

@[expose] noncomputable def swapU (h : UnitaryFieldData 2 f F) (i j : Fin n) :
    ↥(unitarySU 2 f F n) :=
  ⟨permGL (Equiv.swap i j), TableBUE.permGL_swap_mem h i j⟩

theorem exists_ne_ne (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  have key : ∀ a b : ℕ, ∃ k : Fin n, (k : ℕ) ≠ a ∧ (k : ℕ) ≠ b := by
    intro a b
    by_cases h0 : 0 ≠ a ∧ 0 ≠ b
    · exact ⟨⟨0, by omega⟩, h0.1, h0.2⟩
    by_cases h1 : 1 ≠ a ∧ 1 ≠ b
    · exact ⟨⟨1, by omega⟩, h1.1, h1.2⟩
    · exact ⟨⟨2, by omega⟩, by simp only; omega, by simp only; omega⟩
  obtain ⟨k, hk1, hk2⟩ := key i j
  exact ⟨k, fun h => hk1 (by rw [h]), fun h => hk2 (by rw [h])⟩

theorem ggFrameKer_of_ker_le_center [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {φ : ↥(unitarySU 2 f F n) →* G}
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n)) : GGFrameKer φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hn hnq).2
  have hzc : z ∈ Subgroup.center ↥(StatedSU n (2 ^ f) F) := hker hz
  rw [hZ, Subgroup.mem_subgroupOf] at hzc
  obtain ⟨c, hc⟩ := hzc
  refine ⟨(c : F), ?_⟩
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]

theorem ratio_eq_of_conjU_swap {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    (h : UnitaryFieldData 2 f F) (hn : 3 ≤ n) {τ τ' : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) (hτ' : ∀ i, (τ' i : F) ^ (2 ^ f + 1) = 1)
    {i j : Fin n} (he : φ (conjU h hτ (swapU h i j)) = φ (conjU h hτ' (swapU h i j))) :
    τ i * τ' j = τ j * τ' i := by
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨k, hki, hkj⟩ := exists_ne_ne hn i j
  set z := conjU h hτ (swapU h i j) * (conjU h hτ' (swapU h i j))⁻¹ with hzdef
  have hz : φ z = 1 := by rw [hzdef, map_mul, map_inv, he, mul_inv_cancel]
  obtain ⟨c, hc⟩ := hker z hz
  set π := Equiv.swap i j with hπ
  set ρ : Fin n → Fˣ := τ * ((τ⁻¹ * τ') ∘ π.symm) * τ'⁻¹ with hρ
  have hzGL : (z : GL (Fin n) F) = diagHom n ρ := by
    have e1 : diagHom n τ * (permGL π * ((diagHom n τ)⁻¹ * diagHom n τ') * (permGL π)⁻¹) *
        (diagHom n τ')⁻¹ = diagHom n ρ := by
      rw [← map_inv (diagHom n) τ, ← map_mul (diagHom n), permGL_mul_diagHom_mul_inv,
        ← map_inv (diagHom n) τ', ← map_mul (diagHom n), ← map_mul (diagHom n)]
    rw [← e1, hzdef, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjU, coe_conjU]
    change diagHom n τ * permGL π * (diagHom n τ)⁻¹ *
      (diagHom n τ' * permGL π * (diagHom n τ')⁻¹)⁻¹ = _
    group
  have hent : ∀ a : Fin n, (ρ a : F) = c := by
    intro a
    have h1 := congrFun (congrFun hc a) a
    rw [hzGL, coe_diagHom, diagonal_apply_eq, Matrix.scalar_apply, diagonal_apply_eq] at h1
    exact h1
  have hk1 : ρ k = 1 := by
    simp only [hρ, Pi.mul_apply, Function.comp_apply, Pi.inv_apply, hπ, Equiv.symm_swap,
      Equiv.swap_apply_of_ne_of_ne hki hkj]
    group
  have hik : ρ i = 1 := by
    rw [← hk1]
    exact Units.ext ((hent i).trans (hent k).symm)
  have hρi : ρ i = τ i * (τ j)⁻¹ * τ' j * (τ' i)⁻¹ := by
    simp only [hρ, Pi.mul_apply, Function.comp_apply, Pi.inv_apply, hπ, Equiv.symm_swap,
      Equiv.swap_apply_left]
    group
  rw [hρi] at hik
  apply Units.ext
  have e := congrArg (fun u : Fˣ => (u : F)) hik
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one] at e ⊢
  have h1 := (τ j).ne_zero
  have h2 := (τ' i).ne_zero
  field_simp at e
  linear_combination e

theorem ratio_eq_of_frameActs {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    (h : UnitaryFieldData 2 f F) (hn : 3 ≤ n) {b : G} {τ τ' : Fin n → Fˣ}
    (hb : GGFrameActs φ b τ) (hb' : GGFrameActs φ b τ') (i j : Fin n) :
    τ i * τ' j = τ j * τ' i :=
  ratio_eq_of_conjU_swap hker h hn hb.1 hb'.1 (by rw [← hb.apply h, ← hb'.apply h])

theorem ne_one_of_frameActs {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    (h : UnitaryFieldData 2 f F) (hn : 3 ≤ n) {b : G} {τ : Fin n → Fˣ}
    (hb : GGFrameActs φ b τ) {i j : Fin n} (hij : τ i ≠ τ j) : b ≠ 1 := by
  rintro rfl
  have := ratio_eq_of_frameActs hker h hn hb (frameActs_one φ) i j
  simp only [Pi.one_apply, mul_one] at this
  exact hij this

theorem pow_eq_pow_of_frameActs {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    (h : UnitaryFieldData 2 f F) (hn : 3 ≤ n) {b : G} {τ : Fin n → Fˣ} {p : ℕ}
    (hbp : b ^ p = 1) (hb : GGFrameActs φ b τ) (i j : Fin n) : τ i ^ p = τ j ^ p := by
  have h1 := hb.pow h p
  rw [hbp] at h1
  have := ratio_eq_of_frameActs hker h hn h1 (frameActs_one φ) i j
  simpa only [Pi.pow_apply, Pi.one_apply, mul_one] using this

theorem const_of_mem_centralizer_blockSU {φ : ↥(unitarySU 2 f F n) →* G}
    (hker : GGFrameKer φ) (h : UnitaryFieldData 2 f F) (hn : 3 ≤ n) {S : Finset (Fin n)}
    {b : G} (hbL : b ∈ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := f) S).map φ : Subgroup G) : Set G))
    {τ : Fin n → Fˣ} (hb : GGFrameActs φ b τ) {i₀ : Fin n} (hi₀ : i₀ ∈ S) :
    ∀ i ∈ S, τ i = τ i₀ := by
  intro i hi
  have hs : swapU h i i₀ ∈ TableBUE.blockSU (K := F) (n := f) S :=
    TableBUE.isBlockOn_permGL_swap hi hi₀
  have hc := Subgroup.mem_centralizer_iff.mp hbL _ ⟨_, hs, rfl⟩
  have h1 : φ (conjU h hb.1 (swapU h i i₀)) = φ (conjU h (τ := 1) (fun i => by simp)
      (swapU h i i₀)) := by
    rw [conjU_one, ← hb.apply h, ← hc]
    group
  have := ratio_eq_of_conjU_swap hker h hn hb.1 _ h1
  simpa only [Pi.one_apply, mul_one] using this

theorem eq_of_act_eqU {φ : ↥(unitarySU 2 f F n) →* G}
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {x y : G}
    (h : ∀ s, x * φ s * x⁻¹ = y * φ s * y⁻¹) : x = y := by
  have hc : y⁻¹ * x ∈ Subgroup.centralizer (φ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    calc φ s * (y⁻¹ * x) = y⁻¹ * (y * φ s * y⁻¹) * x := by group
      _ = y⁻¹ * (x * φ s * x⁻¹) * x := by rw [h]
      _ = y⁻¹ * x * φ s := by group
  rw [hcent, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem commute_of_frameActs {φ : ↥(unitarySU 2 f F n) →* G} (h : UnitaryFieldData 2 f F)
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {g b : G} {τ τ' : Fin n → Fˣ}
    (hg : GGFrameActs φ g τ) (hb : GGFrameActs φ b τ') : g * b = b * g := by
  have h1 := hg.mul h hb
  have h2 := hb.mul h hg
  rw [mul_comm τ' τ] at h2
  refine eq_of_act_eqU hcent fun s => ?_
  rw [h1.apply h, h2.apply h]

theorem mem_of_frame_inner {p : ℕ} {B Bs : Subgroup G} (hBs : GGBstar p B Bs)
    {φ : ↥(unitarySU 2 f F n) →* G} (h : UnitaryFieldData 2 f F)
    (hframe : ∀ b ∈ Bs, GGFrameDiagU φ b) {d : ↥(unitarySU 2 f F n)} {δ : Fin n → Fˣ}
    (hd : (d : GL (Fin n) F) = diagHom n δ) (hdp : d ^ p = 1) : φ d ∈ Bs := by
  refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    (by rw [← map_pow, hdp, map_one])
  obtain ⟨τ, hτ⟩ := hframe b hb
  have h1 : b * φ d * b⁻¹ = φ d := by rw [hτ.apply h, conjU_eq_self_of_diag h hτ.1 hd]
  calc b * φ d = b * φ d * b⁻¹ * b := by group
    _ = φ d * b := by rw [h1]

theorem mem_of_frameDiag {p : ℕ} {B Bs : Subgroup G} (hBs : GGBstar p B Bs)
    {φ : ↥(unitarySU 2 f F n) →* G} (h : UnitaryFieldData 2 f F)
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) (hframe : ∀ b ∈ Bs, GGFrameDiagU φ b)
    {g : G} (hg : GGFrameDiagU φ g) (hgp : g ^ p = 1) : g ∈ Bs := by
  refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) hgp
  obtain ⟨τ, hτ⟩ := hg
  obtain ⟨τ', hτ'⟩ := hframe b hb
  exact commute_of_frameActs h hcent hτ' hτ

theorem card_le_of_frameU [Finite F] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1)
    (h : UnitaryFieldData 2 f F) (hn : 3 ≤ n) {φ : ↥(unitarySU 2 f F n) →* G}
    (hker : GGFrameKer φ) (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥)
    {X : Subgroup G} (hXp : ∀ b ∈ X, b ^ p = 1) (hframe : ∀ b ∈ X, GGFrameDiagU φ b)
    {S : Finset (Fin n)} {i₀ : Fin n}
    (hXS : ∀ b ∈ X, ∀ τ : Fin n → Fˣ, GGFrameActs φ b τ → ∀ i ∈ S, τ i = τ i₀) :
    Nat.card X ≤ p ^ Sᶜ.card := by
  classical
  choose τ hτ using fun x : X => hframe x.1 x.2
  let r : X → (↥Sᶜ → rootsOfUnity p F) := fun x j =>
    ⟨τ x j * (τ x i₀)⁻¹, by
      rw [mem_rootsOfUnity, mul_pow, inv_pow,
        pow_eq_pow_of_frameActs hker h hn (hXp x.1 x.2) (hτ x) j i₀, mul_inv_cancel]⟩
  have hr : Function.Injective r := by
    intro x y hxy
    have hk : ∀ k, τ x k * (τ x i₀)⁻¹ = τ y k * (τ y i₀)⁻¹ := by
      intro k
      by_cases hkS : k ∈ S
      · rw [hXS x.1 x.2 _ (hτ x) k hkS, hXS y.1 y.2 _ (hτ y) k hkS, mul_inv_cancel,
          mul_inv_cancel]
      · have h1 := congrArg (fun g => ((g ⟨k, by simpa using hkS⟩ : rootsOfUnity p F) : Fˣ)) hxy
        simpa [r] using h1
    have hrat : ∀ a c, τ x a * (τ x c)⁻¹ = τ y a * (τ y c)⁻¹ := by
      intro a c
      calc τ x a * (τ x c)⁻¹ = (τ x a * (τ x i₀)⁻¹) * (τ x c * (τ x i₀)⁻¹)⁻¹ := by group
        _ = (τ y a * (τ y i₀)⁻¹) * (τ y c * (τ y i₀)⁻¹)⁻¹ := by rw [hk a, hk c]
        _ = τ y a * (τ y c)⁻¹ := by group
    exact Subtype.ext (eq_of_act_eqU hcent fun s => by
      rw [(hτ x).apply h, (hτ y).apply h, conjU_eq_of_ratio h (hτ x).1 (hτ y).1 hrat])
  calc Nat.card X ≤ Nat.card (↥Sᶜ → rootsOfUnity p F) := Nat.card_le_card_of_injective r hr
    _ = p ^ Sᶜ.card := by
      rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpF, Nat.card_eq_fintype_card,
        Fintype.card_coe]

@[expose] def GGFrameSingleU (φ : ↥(unitarySU 2 f F n) →* G) (b : G) : Prop :=
  b ≠ 1 ∧ ∃ (τ : Fin n → Fˣ) (j : Fin n), GGFrameActs φ b τ ∧
    ∀ i i', i ≠ j → i' ≠ j → τ i = τ i'

theorem card_le_of_frameU_of_not_single [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F - 1) (h : UnitaryFieldData 2 f F) (hn : 3 ≤ n)
    {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {X : Subgroup G}
    (hXp : ∀ b ∈ X, b ^ p = 1) (hframe : ∀ b ∈ X, GGFrameDiagU φ b) {S : Finset (Fin n)}
    {i₀ : Fin n} (hXS : ∀ b ∈ X, ∀ τ : Fin n → Fˣ, GGFrameActs φ b τ → ∀ i ∈ S, τ i = τ i₀)
    (hns : ∀ b ∈ X, ¬ GGFrameSingleU φ b) {j₀ : Fin n} (hj₀ : j₀ ∉ S) :
    Nat.card X ≤ p ^ (Sᶜ.card - 1) := by
  classical
  choose τ hτ using fun x : X => hframe x.1 x.2
  have hroot : ∀ (x : X) (j : Fin n), τ x j * (τ x i₀)⁻¹ ∈ rootsOfUnity p F := by
    intro x j
    rw [mem_rootsOfUnity, mul_pow, inv_pow,
      pow_eq_pow_of_frameActs hker h hn (hXp x.1 x.2) (hτ x) j i₀, mul_inv_cancel]
  let r : X → (↥Sᶜ → rootsOfUnity p F) := fun x j => ⟨τ x j * (τ x i₀)⁻¹, hroot x j⟩
  have hrmul : ∀ x y, r (x * y) = r x * r y := by
    intro x y
    funext j
    apply Subtype.ext
    change τ (x * y) j * (τ (x * y) i₀)⁻¹ = (τ x j * (τ x i₀)⁻¹) * (τ y j * (τ y i₀)⁻¹)
    have h2 := ratio_eq_of_frameActs hker h hn (hτ (x * y)) ((hτ x).mul h (hτ y)) j i₀
    apply Units.ext
    have e := congrArg (fun u : Fˣ => (u : F)) h2
    simp only [Pi.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val] at e ⊢
    have := (τ (x * y) i₀).ne_zero
    have := (τ x i₀).ne_zero
    have := (τ y i₀).ne_zero
    field_simp
    linear_combination e
  let R : X →* (↥Sᶜ → rootsOfUnity p F) :=
    { toFun := r
      map_one' := by
        funext j
        apply Subtype.ext
        change τ 1 j * (τ 1 i₀)⁻¹ = 1
        have h2 := ratio_eq_of_frameActs hker h hn (hτ 1) (frameActs_one φ) j i₀
        simp only [Pi.one_apply, mul_one] at h2
        rw [h2, mul_inv_cancel]
      map_mul' := hrmul }
  have hinj : Function.Injective R := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hk : ∀ k, τ x k * (τ x i₀)⁻¹ = 1 := by
      intro k
      by_cases hkS : k ∈ S
      · rw [hXS x.1 x.2 _ (hτ x) k hkS, mul_inv_cancel]
      · have h1 := congrArg (fun g => ((g ⟨k, by simpa using hkS⟩ : rootsOfUnity p F) : Fˣ)) hx
        simpa [R, r] using h1
    have hrat : ∀ a c, τ x a * (τ x c)⁻¹ = (1 : Fin n → Fˣ) a * ((1 : Fin n → Fˣ) c)⁻¹ := by
      intro a c
      have ha := hk a
      have hc := hk c
      rw [mul_inv_eq_one] at ha hc
      rw [ha, hc, mul_inv_cancel]
      simp
    refine Subtype.ext (eq_of_act_eqU hcent fun s => ?_)
    rw [(hτ x).apply h, conjU_eq_of_ratio h (hτ x).1 (fun i => by simp) hrat, conjU_one]
    simp
  have hcod : Nat.card (↥Sᶜ → rootsOfUnity p F) = p ^ Sᶜ.card := by
    rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpF, Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hcardR : Nat.card R.range = Nat.card X := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hnt : R.range ≠ ⊤ := by
    intro htop
    obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpF
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    have hζu : Units.mk0 ζ hζ0 ∈ rootsOfUnity p F := by
      rw [mem_rootsOfUnity]
      ext
      simp [hζ.pow_eq_one]
    set j₁ : ↥Sᶜ := ⟨j₀, by simpa using hj₀⟩ with hj₁
    set v : ↥Sᶜ → rootsOfUnity p F := Pi.mulSingle j₁ ⟨Units.mk0 ζ hζ0, hζu⟩ with hv
    obtain ⟨x, hx⟩ : v ∈ R.range := htop ▸ Subgroup.mem_top _
    have hxv : ∀ j : ↥Sᶜ, τ x j * (τ x i₀)⁻¹ = ((v j : rootsOfUnity p F) : Fˣ) := by
      intro j
      rw [← hx]
      rfl
    have hvj₀ : τ x j₀ * (τ x i₀)⁻¹ = Units.mk0 ζ hζ0 := by
      have := hxv j₁
      rw [hv, Pi.mulSingle_eq_same] at this
      exact this
    have hvo : ∀ k, k ≠ j₀ → τ x k = τ x i₀ := by
      intro k hk
      by_cases hkS : k ∈ S
      · exact hXS x.1 x.2 _ (hτ x) k hkS
      · have h1 := hxv ⟨k, by simpa using hkS⟩
        rw [hv, Pi.mulSingle_eq_of_ne
          (fun h' => hk (by rw [hj₁] at h'; exact congrArg Subtype.val h'))] at h1
        have h2 : τ x k * (τ x i₀)⁻¹ = 1 := by simpa using h1
        exact mul_inv_eq_one.mp h2
    apply hns x.1 x.2
    refine ⟨?_, τ x, j₀, hτ x, fun i i' hi hi' => by rw [hvo i hi, hvo i' hi']⟩
    have hne : τ x j₀ ≠ τ x i₀ := by
      intro he
      rw [he, mul_inv_cancel] at hvj₀
      have := congrArg (fun u : Fˣ => (u : F)) hvj₀
      simp only [Units.val_one, Units.val_mk0] at this
      exact hζ.ne_one hp.one_lt this.symm
    exact ne_one_of_frameActs hker h hn (hτ x) hne
  have hdvd : Nat.card R.range ∣ p ^ Sᶜ.card := hcod ▸ Subgroup.card_subgroup_dvd_card R.range
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hjS : j ≠ Sᶜ.card := by
    rintro rfl
    exact hnt (Subgroup.eq_top_of_card_eq _ (by rw [hjeq, hcod]))
  rw [← hcardR, hjeq]
  exact Nat.pow_le_pow_right hp.pos (by omega)

end SURep

end CFSG.StandardType
