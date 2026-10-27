module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNPerm6
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNC0
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G} {n : ℕ}

omit [Finite K] in
theorem e6QTwoN_frameAct_comm
    (hK : Nat.card K = 4) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))}
    {e₁ e₂ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))}
    {σ₁ σ₂ : Fin (n + 1) → Kˣ} (hσ₁ : ∀ k, σ₁ k ^ 3 = 1) (hσ₂ : ∀ k, σ₂ k ^ 3 = 1)
    (h₁ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e₁ σ₁)
    (h₂ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e₂ σ₂) : e₁ * e₂ = e₂ * e₁ := by
  have hcube : ∀ (σ : Fin (n + 1) → Kˣ), (∀ k, σ k ^ 3 = 1) →
      ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
    intro σ hσ k
    rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num]
    simpa using congrArg (fun z : Kˣ => (z : K)) (hσ k)
  have h12 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e₁ * e₂) (σ₁ * σ₂) :=
    TableBUD.FrameAct.mul h₁ h₂ (hcube σ₂ hσ₂)
  have h21 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e₂ * e₁) (σ₂ * σ₁) :=
    TableBUD.FrameAct.mul h₂ h₁ (hcube σ₁ hσ₁)
  have hcomm : σ₁ * σ₂ = σ₂ * σ₁ := by
    funext k
    exact mul_comm _ _
  rw [hcomm] at h12
  exact TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
    (hσ := hcube (σ₂ * σ₁) (fun k => by
      rw [Pi.mul_apply, mul_pow, hσ₂ k, hσ₁ k, mul_one])) h12 h21

theorem e6QTwoN_conj_mem_sup
    (hK : Nat.card K = 4) (hn : 3 ≤ n) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))}
    (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ b) σ)
    (hrange : Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (τ : Equiv.Perm (Fin (n + 1))) (b : Bs) :
    (e6QTwoNPermPre hK hQ θ τ : G) * (b : G) * (e6QTwoNPermPre hK hQ θ τ : G)⁻¹ ∈
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  let ν : ↥L := e6QTwoNPermPre hK hQ θ τ
  let β := e6QTwoNFrameAction hNL θ
  let w := e6QTwoNFramePerm hK hQ τ
  have hnL : (ν : G) ∈ L := ν.2
  have hgN : (ν : G) * (b : G) * (ν : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer hnL) (hNL b.2))
      ((Subgroup.normalizer (L : Set G)).inv_mem (Subgroup.le_normalizer hnL))
  have hbL : (ν : G) * (b : G) * (ν : G)⁻¹ * (b : G)⁻¹ ∈ L := by
    have h1 : (b : G) * (ν : G)⁻¹ * (b : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hNL b.2) ((ν : G)⁻¹)).mp (L.inv_mem hnL)
    have h2 : (ν : G) * ((b : G) * (ν : G)⁻¹ * (b : G)⁻¹) ∈ L := L.mul_mem hnL h1
    convert h2 using 1
    group
  have hgSup : (ν : G) * (b : G) * (ν : G)⁻¹ ∈ L ⊔ Bs := by
    have h_eq : (ν : G) * (b : G) * (ν : G)⁻¹ =
        ((ν : G) * (b : G) * (ν : G)⁻¹ * (b : G)⁻¹) * (b : G) := by group
    rw [h_eq]
    exact (L ⊔ Bs).mul_mem (Subgroup.mem_sup_left hbL) (Subgroup.mem_sup_right b.2)
  obtain ⟨σ, hσ0, hσ3, hσfr⟩ :=
    e6QTwoNFrameAct_of_mem_range hK hn hNL θ hfull hrange ⟨b, rfl⟩
  have hperm : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (w * β b * w⁻¹) (σ ∘ ⇑τ.symm) := e6QTwoNFrameAct_perm hK hσfr τ
  let c0 : Kˣ := ((σ ∘ ⇑τ.symm) (0 : Fin (n + 1)))⁻¹
  have hperm' : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (w * β b * w⁻¹) (fun k => c0 * (σ ∘ ⇑τ.symm) k) :=
    TableBUD.FrameAct.smul hperm c0
  have h0' : (fun k => c0 * (σ ∘ ⇑τ.symm) k) (0 : Fin (n + 1)) = 1 := by
    show c0 * (σ (τ.symm 0)) = 1
    exact inv_mul_cancel _
  have h3' : ∀ k, (c0 * (σ ∘ ⇑τ.symm) k) ^ 3 = 1 := by
    intro k
    rw [mul_pow]
    simp only [Function.comp_apply]
    rw [hσ3 (τ.symm k), mul_one]
    exact USixTwo.cube_unit_eq_one hK c0
  obtain ⟨b', hb'⟩ := hfull (fun k => c0 * (σ ∘ ⇑τ.symm) k) h0' h3'
  have hb'eq : β b' = w * β b * w⁻¹ :=
    TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
      (hσ := fun k => e6QTwoNPowThreeVal hK h3' k) hb' hperm'
  have hL_n : e6QTwoNNormAction θ ⟨ν, Subgroup.le_normalizer hnL⟩ = w :=
    (e6QTwoNNormAction_of_mem_L θ ν).trans (e6QTwoNConjOnQuot_permPre hK hQ θ τ)
  have hB_b : e6QTwoNNormAction θ ⟨b, hNL b.2⟩ = β b :=
    e6QTwoNNormAction_of_mem_Bs θ hNL b
  have hg_eq : (⟨(ν : G) * (b : G) * (ν : G)⁻¹, hgN⟩ :
      ↥(Subgroup.normalizer (L : Set G))) =
      ⟨ν, Subgroup.le_normalizer hnL⟩ * ⟨b, hNL b.2⟩ *
        ⟨ν, Subgroup.le_normalizer hnL⟩⁻¹ := Subtype.ext rfl
  have hact : e6QTwoNNormAction θ ⟨(ν : G) * (b : G) * (ν : G)⁻¹, hgN⟩ =
      w * β b * w⁻¹ := by
    rw [hg_eq, map_mul, map_mul, map_inv, hL_n, hB_b]
  let c : G := (b' : G)⁻¹ * ((ν : G) * (b : G) * (ν : G)⁻¹)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem (hNL (Bs.inv_mem b'.2)) hgN
  have hc_act : e6QTwoNNormAction θ ⟨c, hcN⟩ = 1 := by
    have hc_eq : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨b', hNL b'.2⟩⁻¹ * ⟨(ν : G) * (b : G) * (ν : G)⁻¹, hgN⟩ := Subtype.ext rfl
    rw [hc_eq, map_mul, map_inv, e6QTwoNNormAction_of_mem_Bs θ hNL b', hact, hb'eq]
    group
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
    have hφ : e6QTwoQuotCenterAutHom L (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩) = 1 := by
      apply (MulAut.congr θ).injective
      change e6QTwoNNormAction θ ⟨c, hcN⟩ = (MulAut.congr θ) 1
      rw [hc_act, map_one]
    have hψ : Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ = 1 := by
      apply e6QTwoQuotCenterAutHom_injective hperf
      rw [hφ, map_one]
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) hψ
    simp only [MulAut.one_apply] at h
    have h3 : ((Subgroup.normalizerMonoidHom L ⟨c, hcN⟩) ⟨l, hl⟩ : G) = c * l * c⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨c, hcN⟩ ⟨l, hl⟩
    have h4 : c * l * c⁻¹ = l := by
      rw [← h3]
      exact congrArg Subtype.val h
    calc l * c = (c * l * c⁻¹) * c := by rw [h4]
      _ = c * l := by group
  have hcSup : c ∈ L ⊔ Bs := by
    change (b' : G)⁻¹ * ((ν : G) * (b : G) * (ν : G)⁻¹) ∈ L ⊔ Bs
    exact (L ⊔ Bs).mul_mem (Subgroup.mem_sup_right (Bs.inv_mem b'.2)) hgSup
  have hcX : c ∈ Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) :=
    e6QTwoN_C0_le_sup_Z hZcop hBs hstar hNL
      (Subgroup.mem_inf.mpr ⟨hcC, hcSup⟩)
  have hg_eq2 : (ν : G) * (b : G) * (ν : G)⁻¹ = (b' : G) * c := by
    change (ν : G) * (b : G) * (ν : G)⁻¹ =
      (b' : G) * ((b' : G)⁻¹ * ((ν : G) * (b : G) * (ν : G)⁻¹))
    group
  rw [hg_eq2]
  exact (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).mul_mem
    (Subgroup.mem_sup_left b'.2) hcX

theorem e6QTwoN_normalizes_sup
    (hK : Nat.card K = 4) (hn : 3 ≤ n) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))}
    (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ b) σ)
    (hrange : Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (τ : Equiv.Perm (Fin (n + 1))) :
    (e6QTwoNPermPre hK hQ θ τ : G) ∈
      Subgroup.normalizer
        (((Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))) : Subgroup G) : Set G) := by
  classical
  let ν : ↥L := e6QTwoNPermPre hK hQ θ τ
  have hLN : L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G) :=
    e6QTwoNNormalizesCenter (Bs := L) (hNL := Subgroup.le_normalizer)
  have hnZ : (ν : G) ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G) := hLN ν.2
  have hle : (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).map
        (MulAut.conj (ν : G)).toMonoidHom ≤
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro - ⟨y, hy, rfl⟩
      exact e6QTwoN_conj_mem_sup hK hn hZcop θ hNL hfull hrange hperf hBs hstar τ ⟨y, hy⟩
    · rintro - ⟨z, hz, rfl⟩
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hnZ z).mp hz)
  have hcard : Nat.card ↥((Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).map
        (MulAut.conj (ν : G)).toMonoidHom) =
      Nat.card ↥(Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))) :=
    Subgroup.card_map_of_injective (MulAut.conj (ν : G)).injective
  have hEq : (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))).map
        (MulAut.conj (ν : G)).toMonoidHom =
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq

theorem e6QTwoN_exists_sylow_conj
    (hK : Nat.card K = 4) (hn : 3 ≤ n) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))}
    (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ b) σ)
    (hrange : Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (τ : Equiv.Perm (Fin (n + 1))) :
    ∃ z ∈ Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)),
      (Bs.map (MulAut.conj (e6QTwoNPermPre hK hQ θ τ : G))).map
        (MulAut.conj z).toMonoidHom = Bs := by
  classical
  let ν : ↥L := e6QTwoNPermPre hK hQ θ τ
  let X : Subgroup G := Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G))
  have hNX : (ν : G) ∈ Subgroup.normalizer (X : Set G) := by
    dsimp only [ν, X]
    exact e6QTwoN_normalizes_sup hK hn hZcop θ hNL hfull hrange hperf hBs hstar τ
  have hXmap : X.map (MulAut.conj (ν : G)).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hNX
  have hP₁ : Bs ≤ X := le_sup_left
  have hP₂ : Bs.map (MulAut.conj (ν : G)).toMonoidHom ≤ X := by
    calc Bs.map (MulAut.conj (ν : G)).toMonoidHom
        ≤ X.map (MulAut.conj (ν : G)).toMonoidHom := Subgroup.map_mono le_sup_left
      _ = X := hXmap
  have hP₁g : IsPGroup 3 Bs :=
    CFSG.StandardType.Line63.H5.isPGroup_three_of_isElemAbelian hBs
  have hP₂g : IsPGroup 3 (Bs.map (MulAut.conj (ν : G)).toMonoidHom) := hP₁g.map _
  have hcard' : Nat.card Bs = Nat.card ↥(Bs.map (MulAut.conj (ν : G)).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj (ν : G)).injective).symm
  have hindex : ¬ 3 ∣ (Bs.subgroupOf X).index :=
    e6QTwoNSylowIndex hZcop hK θ hperf hBs hx hBL hstar hNL
  obtain ⟨z, hzX, hz⟩ :=
    e6QTwoN_sylow_conj_of_card_eq (p := 3) hP₁ hP₂ hP₁g hP₂g hcard' hindex
  exact ⟨z, hzX, hz⟩

theorem e6QTwoN_exists_mem_normalizer
    (hK : Nat.card K = 4) (hn : 3 ≤ n) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))}
    (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ b) σ)
    (hrange : Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (τ : Equiv.Perm (Fin (n + 1))) :
    ∃ (n' : G) (hnL : n' ∈ L) (_hn' : n' ∈ Subgroup.normalizer (Bs : Set G)) (b₀ : ↥Bs),
      e6QTwoNNormAction θ ⟨n', Subgroup.le_normalizer hnL⟩ =
        e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
          (e6QTwoNFrameAction hNL θ b₀)⁻¹ := by
  classical
  let ν : ↥L := e6QTwoNPermPre hK hQ θ τ
  let Z : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)
  obtain ⟨z, hzX, hz⟩ :=
    e6QTwoN_exists_sylow_conj hK hn hZcop θ hNL hfull hrange hperf hBs hx hBL hstar τ
  have hZnorm : Bs ≤ Subgroup.normalizer (Z : Set G) := e6QTwoNNormalizesCenter hNL
  have hXeq : (↑(Bs ⊔ Z) : Set G) = (Z : Set G) * (Bs : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left Z Bs hZnorm
  have hz_mul : z ∈ (Z : Set G) * (Bs : Set G) := by
    rw [← hXeq]
    exact hzX
  obtain ⟨c, hcZ, b₀, hb₀, hz_eq⟩ := hz_mul
  let n' : G := c * (b₀ * (ν : G) * b₀⁻¹)
  have hcL : c ∈ L := (Subgroup.mem_inf.mp hcZ).1
  have hb₀n : b₀ * (ν : G) * b₀⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hNL hb₀) (ν : G)).mp ν.2
  have hn'L : n' ∈ L := L.mul_mem hcL hb₀n
  have hn'N : n' ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Bs.map (MulAut.conj n').toMonoidHom ≤ Bs := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      have hbb : b₀ * (b : G) = (b : G) * b₀ :=
        congrArg (fun w : ↥Bs => (w : G)) (hBs.1.is_comm.comm ⟨b₀, hb₀⟩ ⟨b, hb⟩)
      have heq : (MulAut.conj n').toMonoidHom (b : G) =
          z * ((ν : G) * (b : G) * (ν : G)⁻¹) * z⁻¹ := by
        change n' * (b : G) * n'⁻¹ = z * ((ν : G) * (b : G) * (ν : G)⁻¹) * z⁻¹
        rw [show n' = c * (b₀ * (ν : G) * b₀⁻¹) from rfl, ← hz_eq]
        calc c * (b₀ * (ν : G) * b₀⁻¹) * (b : G) * (c * (b₀ * (ν : G) * b₀⁻¹))⁻¹
            = c * (b₀ * (ν : G) * (b₀⁻¹ * (b : G) * b₀) * (ν : G)⁻¹ * b₀⁻¹) * c⁻¹ := by
              group
          _ = c * (b₀ * (ν : G) * (b : G) * (ν : G)⁻¹ * b₀⁻¹) * c⁻¹ := by
              rw [show b₀⁻¹ * (b : G) * b₀ = (b : G) from by
                rw [mul_assoc, ← hbb, inv_mul_cancel_left]]
          _ = c * b₀ * ((ν : G) * (b : G) * (ν : G)⁻¹) * (c * b₀)⁻¹ := by group
      rw [heq]
      have hmem : z * ((ν : G) * (b : G) * (ν : G)⁻¹) * z⁻¹ ∈ Bs := by
        rw [← hz]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hb)
      exact hmem
    have hcard' : Nat.card ↥(Bs.map (MulAut.conj n').toMonoidHom) = Nat.card ↥Bs :=
      Subgroup.card_map_of_injective (MulAut.conj n').injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard'.symm)
  refine ⟨n', hn'L, hn'N, ⟨b₀, hb₀⟩, ?_⟩
  have hn_eq : (⟨n', Subgroup.le_normalizer hn'L⟩ :
      ↥(Subgroup.normalizer (L : Set G))) =
      ⟨c, Subgroup.le_normalizer hcL⟩ * ⟨b₀ * (ν : G) * b₀⁻¹,
        (Subgroup.normalizer (L : Set G)).mul_mem
          ((Subgroup.normalizer (L : Set G)).mul_mem (hNL hb₀) (Subgroup.le_normalizer ν.2))
          ((Subgroup.normalizer (L : Set G)).inv_mem (hNL hb₀))⟩ := Subtype.ext rfl
  have hb₀n_eq : (⟨b₀ * (ν : G) * b₀⁻¹,
      (Subgroup.normalizer (L : Set G)).mul_mem
        ((Subgroup.normalizer (L : Set G)).mul_mem (hNL hb₀) (Subgroup.le_normalizer ν.2))
        ((Subgroup.normalizer (L : Set G)).inv_mem (hNL hb₀))⟩ :
      ↥(Subgroup.normalizer (L : Set G))) =
      ⟨b₀, hNL hb₀⟩ * ⟨ν, Subgroup.le_normalizer ν.2⟩ * ⟨b₀, hNL hb₀⟩⁻¹ := Subtype.ext rfl
  have hc_act : e6QTwoNNormAction θ ⟨c, Subgroup.le_normalizer hcL⟩ = 1 := by
    have hcent : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcZ).2 (l : G) l.2
    have hconj : MulAut.conj (⟨c, hcL⟩ : ↥L) = 1 := by
      ext l
      rw [MulAut.one_apply, MulAut.conj_apply]
      change c * (l : G) * c⁻¹ = (l : G)
      have h : (⟨c, hcL⟩ : ↥L) * l = l * ⟨c, hcL⟩ :=
        (Subgroup.mem_center_iff.mp hcent l).symm
      have h' : c * (l : G) = (l : G) * c := congrArg Subtype.val h
      rw [h', mul_assoc, mul_inv_cancel, mul_one]
    rw [e6QTwoNNormAction_apply]
    have h1 : Subgroup.normalizerMonoidHom L ⟨c, Subgroup.le_normalizer hcL⟩ =
        MulAut.conj (⟨c, hcL⟩ : ↥L) := by
      ext l
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [h1, hconj, map_one, map_one]
  rw [hn_eq, map_mul, hb₀n_eq, map_mul, map_mul, map_inv, hc_act, one_mul,
    e6QTwoNNormAction_of_mem_Bs θ hNL ⟨b₀, hb₀⟩, e6QTwoNNormAction_of_mem_L θ ν,
    e6QTwoNConjOnQuot_permPre hK hQ θ τ]

theorem e6QTwoN_exists_mem_normalizer_frameAct_perm
    (hK : Nat.card K = 4) (hn : 3 ≤ n) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))}
    (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ b) σ)
    (hrange : Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (τ : Equiv.Perm (Fin (n + 1))) :
    ∃ (n' : G) (hnL : n' ∈ L) (hn' : n' ∈ Subgroup.normalizer (Bs : Set G)),
      (∃ b₀ : ↥Bs, e6QTwoNNormAction θ ⟨n', Subgroup.le_normalizer hnL⟩ =
        e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
          (e6QTwoNFrameAction hNL θ b₀)⁻¹) ∧
      ∀ (b : ↥Bs) (σ : Fin (n + 1) → Kˣ), (∀ k, σ k ^ 3 = 1) →
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
          (e6QTwoNFrameAction hNL θ b) σ →
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
          (e6QTwoNFrameAction hNL θ
            ⟨n' * (b : G) * n'⁻¹,
              (Subgroup.mem_normalizer_iff.mp hn' (b : G)).mp b.2⟩) (σ ∘ ⇑τ.symm) := by
  obtain ⟨n', hnL, hn', b₀, hact⟩ :=
    e6QTwoN_exists_mem_normalizer hK hn hZcop θ hNL hfull hrange hperf hBs hx hBL hstar τ
  refine ⟨n', hnL, hn', ⟨b₀, hact⟩, ?_⟩
  intro b σ hσ3 hσ
  have hb0 : n' * (b : G) * n'⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hn' (b : G)).mp b.2
  have hperm : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoNFramePerm hK hQ τ * e6QTwoNFrameAction hNL θ b *
        (e6QTwoNFramePerm hK hQ τ)⁻¹) (σ ∘ ⇑τ.symm) :=
    e6QTwoNFrameAct_perm hK hσ τ
  obtain ⟨σ₀, hσ₀0, hσ₀3, hσ₀fr⟩ :=
    e6QTwoNFrameAct_of_mem_range hK hn hNL θ hfull hrange
      (MonoidHom.mem_range.mpr ⟨b₀, rfl⟩)
  have hσ3' : ∀ k, (σ ∘ ⇑τ.symm) k ^ 3 = 1 := by
    intro k
    rw [Function.comp_apply]
    exact hσ3 (τ.symm k)
  have hcomm : e6QTwoNFrameAction hNL θ b₀ *
      (e6QTwoNFramePerm hK hQ τ * e6QTwoNFrameAction hNL θ b *
        (e6QTwoNFramePerm hK hQ τ)⁻¹) =
      (e6QTwoNFramePerm hK hQ τ * e6QTwoNFrameAction hNL θ b *
        (e6QTwoNFramePerm hK hQ τ)⁻¹) * e6QTwoNFrameAction hNL θ b₀ :=
    e6QTwoN_frameAct_comm hK hσ₀3 hσ3' hσ₀fr hperm
  have hbb : e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFrameAction hNL θ b =
      e6QTwoNFrameAction hNL θ b * e6QTwoNFrameAction hNL θ b₀ :=
    e6QTwoN_frameAct_comm hK hσ₀3 hσ3 hσ₀fr hσ
  have hconj := GGQ2S08RoN.e6QTwoNFrameAction_conj θ hNL hnL (b := b) hb0
  rw [hconj]
  rw [show e6QTwoNConjOnQuot θ ⟨n', hnL⟩ =
      e6QTwoNNormAction θ ⟨n', Subgroup.le_normalizer hnL⟩ from
    (e6QTwoNNormAction_of_mem_L θ ⟨n', hnL⟩).symm]
  rw [hact]
  have hbb_inv : (e6QTwoNFrameAction hNL θ b₀)⁻¹ * e6QTwoNFrameAction hNL θ b *
      e6QTwoNFrameAction hNL θ b₀ = e6QTwoNFrameAction hNL θ b := by
    calc (e6QTwoNFrameAction hNL θ b₀)⁻¹ * e6QTwoNFrameAction hNL θ b *
          e6QTwoNFrameAction hNL θ b₀
        = (e6QTwoNFrameAction hNL θ b₀)⁻¹ *
            (e6QTwoNFrameAction hNL θ b * e6QTwoNFrameAction hNL θ b₀) := by group
      _ = (e6QTwoNFrameAction hNL θ b₀)⁻¹ *
            (e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFrameAction hNL θ b) := by rw [hbb]
      _ = e6QTwoNFrameAction hNL θ b := by group
  have heq : (e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
        (e6QTwoNFrameAction hNL θ b₀)⁻¹) * e6QTwoNFrameAction hNL θ b *
        (e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
          (e6QTwoNFrameAction hNL θ b₀)⁻¹)⁻¹ =
      e6QTwoNFramePerm hK hQ τ * e6QTwoNFrameAction hNL θ b *
        (e6QTwoNFramePerm hK hQ τ)⁻¹ := by
    calc (e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
          (e6QTwoNFrameAction hNL θ b₀)⁻¹) * e6QTwoNFrameAction hNL θ b *
          (e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
            (e6QTwoNFrameAction hNL θ b₀)⁻¹)⁻¹
        = e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
            ((e6QTwoNFrameAction hNL θ b₀)⁻¹ * e6QTwoNFrameAction hNL θ b *
              e6QTwoNFrameAction hNL θ b₀) * (e6QTwoNFramePerm hK hQ τ)⁻¹ *
            (e6QTwoNFrameAction hNL θ b₀)⁻¹ := by group
      _ = e6QTwoNFrameAction hNL θ b₀ * e6QTwoNFramePerm hK hQ τ *
            e6QTwoNFrameAction hNL θ b * (e6QTwoNFramePerm hK hQ τ)⁻¹ *
            (e6QTwoNFrameAction hNL θ b₀)⁻¹ := by rw [hbb_inv]
      _ = e6QTwoNFrameAction hNL θ b₀ *
            (e6QTwoNFramePerm hK hQ τ * e6QTwoNFrameAction hNL θ b *
              (e6QTwoNFramePerm hK hQ τ)⁻¹) *
            (e6QTwoNFrameAction hNL θ b₀)⁻¹ := by group
      _ = (e6QTwoNFramePerm hK hQ τ * e6QTwoNFrameAction hNL θ b *
              (e6QTwoNFramePerm hK hQ τ)⁻¹) *
            e6QTwoNFrameAction hNL θ b₀ * (e6QTwoNFrameAction hNL θ b₀)⁻¹ := by
          rw [hcomm]
      _ = e6QTwoNFramePerm hK hQ τ * e6QTwoNFrameAction hNL θ b *
            (e6QTwoNFramePerm hK hQ τ)⁻¹ := by group
  rw [heq]
  exact hperm

end CFSG.StandardType.E6QTwo
