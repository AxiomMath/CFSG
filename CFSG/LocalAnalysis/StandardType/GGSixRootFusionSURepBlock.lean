module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace SURep

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F]

@[expose] def fixU (τ : Fin n → Fˣ) : Subgroup ↥(unitarySU 2 f F n) where
  carrier := {s | diagHom n τ * (s : GL (Fin n) F) = (s : GL (Fin n) F) * diagHom n τ}
  mul_mem' {a b} ha hb := by
    change diagHom n τ * ((a : GL (Fin n) F) * b) = ((a : GL (Fin n) F) * b) * diagHom n τ
    rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  one_mem' := by
    change diagHom n τ * 1 = 1 * diagHom n τ
    rw [mul_one, one_mul]
  inv_mem' {a} ha := by
    change diagHom n τ * ((a : GL (Fin n) F))⁻¹ = ((a : GL (Fin n) F))⁻¹ * diagHom n τ
    have ha' : diagHom n τ * (a : GL (Fin n) F) = (a : GL (Fin n) F) * diagHom n τ := ha
    calc diagHom n τ * ((a : GL (Fin n) F))⁻¹ =
        ((a : GL (Fin n) F))⁻¹ * ((a : GL (Fin n) F) * diagHom n τ) *
          ((a : GL (Fin n) F))⁻¹ := by group
      _ = ((a : GL (Fin n) F))⁻¹ * (diagHom n τ * (a : GL (Fin n) F)) *
          ((a : GL (Fin n) F))⁻¹ := by rw [ha']
      _ = ((a : GL (Fin n) F))⁻¹ * diagHom n τ := by group

theorem mem_fixU {τ : Fin n → Fˣ} {s : ↥(unitarySU 2 f F n)} :
    s ∈ fixU (f := f) τ ↔ diagHom n τ * (s : GL (Fin n) F) = (s : GL (Fin n) F) * diagHom n τ :=
  Iff.rfl

theorem mem_fixU_of_commute {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    (h : UnitaryFieldData 2 f F) {b : G} {τ : Fin n → Fˣ} (hb : GGFrameActs φ b τ)
    {T : Finset (Fin n)} (htc : ∀ i j, i ∉ T → j ∉ T → τ i = τ j) (hT : T.card < Tᶜ.card)
    {s : ↥(unitarySU 2 f F n)} (hs : b * φ s = φ s * b) : s ∈ fixU (f := f) τ := by
  set u := conjU h hb.1 s with hu
  have h1 : φ u = φ s := by
    rw [hu, ← hb.apply h, hs, mul_inv_cancel_right]
  have hz : φ (s⁻¹ * u) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c, hc⟩ := hker _ hz
  have hus : ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Matrix.scalar (Fin n) c := by
    have h2 : u = s * (s⁻¹ * u) := by group
    rw [h2, Subgroup.coe_mul, Units.val_mul, hc]
  by_cases hc1 : c = 1
  · rw [mem_fixU]
    have h3 : (u : GL (Fin n) F) = s := by
      apply Units.ext
      rw [hus, hc1, map_one, Matrix.mul_one]
    rw [hu, coe_conjU] at h3
    calc diagHom n τ * (s : GL (Fin n) F) =
        diagHom n τ * (s : GL (Fin n) F) * (diagHom n τ)⁻¹ * diagHom n τ := by group
      _ = (s : GL (Fin n) F) * diagHom n τ := by rw [h3]
  · exfalso
    have hblock : ∀ k ∈ Tᶜ, ∀ l ∈ Tᶜ,
        ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0 := by
      intro k hk l hl
      have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) F => M k l) hus
      rw [hu, conjU_apply, htc k l (by simpa using hk) (by simpa using hl),
        Matrix.mul_apply] at h2
      rw [Finset.sum_eq_single l (fun m _ hm => by
        rw [Matrix.scalar_apply, diagonal_apply_ne _ hm, mul_zero])
        (fun h' => absurd (Finset.mem_univ l) h'), Matrix.scalar_apply,
        diagonal_apply_eq] at h2
      have h4 : (τ l : F) * (((τ l)⁻¹ : Fˣ) : F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have h3 : ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l * (1 - c) = 0 := by
        have e : (τ l : F) * ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l *
            (((τ l)⁻¹ : Fˣ) : F) = ((s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l := by
          rw [mul_comm (τ l : F), mul_assoc, h4, mul_one]
        rw [e] at h2
        rw [mul_sub, mul_one, ← h2, sub_self]
      rcases mul_eq_zero.mp h3 with h5 | h5
      · exact h5
      · exact absurd (sub_eq_zero.mp h5).symm hc1
    have hdet := TypeA.det_eq_zero_of_block_zero (S := Tᶜ) (by rwa [compl_compl]) hblock
    obtain ⟨hdet1, -⟩ := (mem_unitarySU_iff h).mp s.2
    rw [hdet1] at hdet
    exact one_ne_zero hdet

theorem range_inf_centralizer_eq_mapU {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    (h : UnitaryFieldData 2 f F) {b : G} {τ : Fin n → Fˣ} (hb : GGFrameActs φ b τ)
    {T : Finset (Fin n)} (htc : ∀ i j, i ∉ T → j ∉ T → τ i = τ j) (hT : T.card < Tᶜ.card) :
    φ.range ⊓ Subgroup.centralizer {b} = (fixU (f := f) τ).map φ := by
  ext g
  constructor
  · rintro ⟨⟨s, rfl⟩, hc⟩
    refine ⟨s, mem_fixU_of_commute hker h hb htc hT ?_, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h2 : conjU h hb.1 s = s := by
      apply Subtype.ext
      rw [coe_conjU, (mem_fixU.mp hs), mul_inv_cancel_right]
    have h1 : b * φ s * b⁻¹ = φ s := by rw [hb.apply h, h2]
    calc φ s * b = b * φ s * b⁻¹ * b := by rw [h1]
      _ = b * φ s := by group

theorem isBlockOn_conj {S : Finset (Fin n)} {C C' X : Matrix (Fin n) (Fin n) F}
    (hC : ∀ i j, (i ∈ S ↔ j ∉ S) → C i j = 0) (hC' : ∀ i j, (i ∈ S ↔ j ∉ S) → C' i j = 0)
    (hCC' : C * C' = 1) (hX : TableBUE.IsBlockOn S X) : TableBUE.IsBlockOn S (C * X * C') := by
  intro i j hij
  have hN : ∀ k l, (k ∉ S ∨ l ∉ S) → (X - 1) k l = 0 := fun k l hkl => by
    rw [Matrix.sub_apply, hX k l hkl, sub_self]
  have hsplit : C * X * C' = 1 + C * (X - 1) * C' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hCC', add_sub_cancel]
  rw [hsplit, Matrix.add_apply, add_eq_left, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ S
  · by_cases hl : l ∈ S
    · rcases hij with hi | hj
      · rw [hC i k (by tauto), zero_mul, zero_mul]
      · rw [hC' l j (by tauto), mul_zero]
    · rw [hN k l (Or.inr hl), mul_zero, zero_mul]
  · rw [hN k l (Or.inl hk), mul_zero, zero_mul]

theorem entry_eq_zero_of_mem_fixU {τ : Fin n → Fˣ} {S : Finset (Fin n)} {μ : Fˣ}
    (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ) {c : ↥(unitarySU 2 f F n)}
    (hc : c ∈ fixU (f := f) τ) (i j : Fin n) (hij : i ∈ S ↔ j ∉ S) :
    ((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
  refine TableBUE.entry_eq_zero_of_commute (mem_fixU.mp hc).symm ?_
  by_cases hi : i ∈ S
  · have hj : j ∉ S := hij.mp hi
    rw [hS i hi]
    exact (hSc j hj).symm
  · have hj : j ∈ S := by by_contra hj; exact hi (hij.mpr hj)
    rw [hS j hj]
    exact hSc i hi

theorem isComponentOf_map_blockSU [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (h : UnitaryFieldData 2 f F) {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ)
    {b : G} {τ : Fin n → Fˣ} (hb : GGFrameActs φ b τ) {S : Finset (Fin n)} {μ : Fˣ}
    (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ) (hcard : Sᶜ.card < S.card)
    (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ f) ≠ (3, 2)) {i₀ : Fin n} (hi₀ : i₀ ∉ S) :
    IsComponentOf ((TableBUE.blockSU (K := F) (n := f) S).map φ)
      (φ.range ⊓ Subgroup.centralizer {b}) := by
  have htc : ∀ i j, i ∉ Sᶜ → j ∉ Sᶜ → τ i = τ j := fun i j hi hj => by
    rw [hS i (by simpa using hi), hS j (by simpa using hj)]
  rw [range_inf_centralizer_eq_mapU hker h hb htc (by rwa [compl_compl])]
  set C := fixU (f := f) τ with hC
  set J₀ := TableBUE.blockSU (K := F) (n := f) S with hJ₀
  have hJ₀C : J₀ ≤ C := by
    intro x hx
    rw [hC, mem_fixU]
    exact TableBUE.diagHom_mul_comm_of_isBlockOn (fun i hi j hj => by rw [hS i hi, hS j hj]) hx
  have hJn : ∀ c ∈ C, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀ := by
    intro c hc j hj
    have hc' : c⁻¹ ∈ C := C.inv_mem hc
    change TableBUE.IsBlockOn S ((((c * j * c⁻¹ : ↥(unitarySU 2 f F n)) : GL (Fin n) F)) :
      Matrix (Fin n) (Fin n) F)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    refine isBlockOn_conj (fun i k hik => entry_eq_zero_of_mem_fixU hS hSc hc i k hik)
      (fun i k hik => entry_eq_zero_of_mem_fixU hS hSc hc' i k hik) ?_ hj
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have hinj : ∀ j ∈ J₀, φ j = 1 → j = 1 := by
    intro j hj h1
    obtain ⟨c, hc⟩ := hker j h1
    have hii := hj i₀ i₀ (Or.inl hi₀)
    rw [hc, Matrix.scalar_apply, diagonal_apply_eq, Matrix.one_apply_eq] at hii
    apply Subtype.ext
    apply Units.ext
    rw [hc, hii, map_one, Subgroup.coe_one, Units.val_one]
  have hq : CFSG.IsQuasisimple J₀ := TableBUE.isQuasisimple_blockSU S h hF hS3 hSq
  have hinj' : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (φ.comp J₀.subtype).range = J₀.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple (J₀.map φ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange)) hq
  have hJF : J₀.map φ ≤ C.map φ := Subgroup.map_mono hJ₀C
  have hJn' : ((J₀.map φ).subgroupOf (C.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ g ⟨j, hj, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * j * c⁻¹, hJn c hc j hj, by rw [map_mul, map_mul, map_inv]⟩
  exact ⟨hJF, IsSubnormal.step hJF hJn' (IsSubnormal.refl _),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJq⟩

theorem ggSixFusionWitness_of_frameU_bound [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (h : UnitaryFieldData 2 f F) {p : ℕ} {Bs D E G₀ : Subgroup G} {t : StatedLieTag} {e : ℕ}
    {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ) (hrange : φ.range = G₀)
    {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1) {τ : Fin n → Fˣ} (hb : GGFrameActs φ b τ)
    {S : Finset (Fin n)} {μ : Fˣ} (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ)
    (hcard : Sᶜ.card < S.card) (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ f) ≠ (3, 2))
    {i₁ : Fin n} (hi₁ : i₁ ∉ S)
    (hbound : Nat.card (Bs ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := f) S).map φ : Subgroup G) : Set G) : Subgroup G) ≤
        p ^ 2) :
    GGSixFusionWitness p Bs D E G₀ t e b := by
  have hcomp := isComponentOf_map_blockSU hF h hker hb hS hSc hcard hS3 hSq hi₁
  rw [hrange] at hcomp
  exact ⟨hb1, Or.inr (Or.inr ⟨hbBs, _, hcomp, Or.inl hbound⟩)⟩

theorem ggSixFusionWitness_of_frameU [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (h : UnitaryFieldData 2 f F) {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1) (hn : 3 ≤ n)
    {B Bs D E G₀ : Subgroup G} {t : StatedLieTag} {e : ℕ} (hBs : GGBstar p B Bs)
    {φ : ↥(unitarySU 2 f F n) →* G} (hker : GGFrameKer φ) (hrange : φ.range = G₀)
    (hcent : Subgroup.centralizer (G₀ : Set G) = ⊥) (hframe : ∀ b ∈ Bs, GGFrameDiagU φ b)
    {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1) {τ : Fin n → Fˣ} (hb : GGFrameActs φ b τ)
    {S : Finset (Fin n)} {μ : Fˣ} (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ)
    (hcard : Sᶜ.card < S.card) (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ f) ≠ (3, 2))
    (hSc2 : Sᶜ.card ≤ 2) {i₁ : Fin n} (hi₁ : i₁ ∉ S) :
    GGSixFusionWitness p Bs D E G₀ t e b := by
  have hcent' : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hrange]; exact hcent
  obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  refine ggSixFusionWitness_of_frameU_bound hF h hker hrange hbBs hb1 hb hS hSc hcard hS3 hSq
    hi₁ ((card_le_of_frameU hp hpF h hn hker hcent' (X := Bs ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := F) (n := f) S).map φ : Subgroup G) : Set G))
      (fun c hc => hBs.2.1.2 c hc.1) (fun c hc => hframe c hc.1) (S := S) (i₀ := i₀) ?_).trans
      (Nat.pow_le_pow_right hp.pos hSc2))
  intro c hc τ' hτ' i hi
  exact const_of_mem_centralizer_blockSU hker h hn hc.2 hτ' hi₀ i hi

end SURep

end CFSG.StandardType
