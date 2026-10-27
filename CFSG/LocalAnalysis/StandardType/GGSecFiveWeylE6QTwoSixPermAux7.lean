module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux6

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G}

theorem e6QTwoSix_frameAct_comm
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    {e₁ e₂ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    {σ₁ σ₂ : Fin 6 → Kˣ} (hσ₁ : ∀ k, σ₁ k ^ 3 = 1) (hσ₂ : ∀ k, σ₂ k ^ 3 = 1)
    (h₁ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e₁ σ₁)
    (h₂ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e₂ σ₂) : e₁ * e₂ = e₂ * e₁ := by
  have hcube : ∀ (σ : Fin 6 → Kˣ), (∀ k, σ k ^ 3 = 1) →
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

theorem e6QTwoSixFrameAct_mem_range
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ)
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))} {σ : Fin 6 → Kˣ}
    (hσ0 : σ (0 : Fin 6) = 1) (hσ3 : ∀ k, σ k ^ 3 = 1)
    (he : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ) :
    e ∈ (e6QTwoSixFrameAction hNL θ).range := by
  obtain ⟨b, hb⟩ := hfull σ hσ0 hσ3
  have heq : e = e6QTwoSixFrameAction hNL θ b :=
    TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
      (hσ := fun k => e6QTwoSixPowThreeVal hK hσ3 k) he hb
  exact heq ▸ MonoidHom.mem_range.mpr ⟨b, rfl⟩

theorem e6QTwoSix_exists_mem_normalizer
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ)
    (hrange5 : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) (τ : Equiv.Perm (Fin 6)) :
    ∃ (n' : G) (hnL : n' ∈ L) (hn' : n' ∈ Subgroup.normalizer (Bs : Set G)) (b₀ : ↥Bs),
      e6QTwoSixNormAction θ ⟨n', Subgroup.le_normalizer hnL⟩ =
        e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFramePerm hK hQ τ *
          (e6QTwoSixFrameAction hNL θ b₀)⁻¹ := by
  classical
  let n : ↥L := e6QTwoSixPermPre hK hQ θ τ
  let Z : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)
  obtain ⟨z, hzX, hz⟩ :=
    e6QTwoSix_exists_sylow_conj hK θ hNL hfull hrange5 hperf hBs hcard hx hx1 hBL hstar
      hI hLx τ
  have hZnorm : Bs ≤ Subgroup.normalizer (Z : Set G) := e6QTwoSixNormalizesCenter hNL
  have hXeq : (↑(Bs ⊔ Z) : Set G) = (Z : Set G) * (Bs : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left Z Bs hZnorm
  have hz_mul : z ∈ (Z : Set G) * (Bs : Set G) := by
    rw [← hXeq]
    exact hzX
  obtain ⟨c, hcZ, b₀, hb₀, hz_eq⟩ := hz_mul
  let n' : G := c * (b₀ * (n : G) * b₀⁻¹)
  have hcL : c ∈ L := (Subgroup.mem_inf.mp hcZ).1
  have hb₀n : b₀ * (n : G) * b₀⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hNL hb₀) (n : G)).mp n.2
  have hn'L : n' ∈ L := L.mul_mem hcL hb₀n
  have hn'N : n' ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Bs.map (MulAut.conj n').toMonoidHom ≤ Bs := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      have hbb : b₀ * (b : G) = (b : G) * b₀ :=
        congrArg (fun w : ↥Bs => (w : G)) (hBs.1.is_comm.comm ⟨b₀, hb₀⟩ ⟨b, hb⟩)
      have heq : (MulAut.conj n').toMonoidHom (b : G) =
          z * ((n : G) * (b : G) * (n : G)⁻¹) * z⁻¹ := by
        change n' * (b : G) * n'⁻¹ = z * ((n : G) * (b : G) * (n : G)⁻¹) * z⁻¹
        rw [show n' = c * (b₀ * (n : G) * b₀⁻¹) from rfl, ← hz_eq]
        calc c * (b₀ * (n : G) * b₀⁻¹) * (b : G) * (c * (b₀ * (n : G) * b₀⁻¹))⁻¹
            = c * (b₀ * (n : G) * (b₀⁻¹ * (b : G) * b₀) * (n : G)⁻¹ * b₀⁻¹) * c⁻¹ := by
              group
          _ = c * (b₀ * (n : G) * (b : G) * (n : G)⁻¹ * b₀⁻¹) * c⁻¹ := by
              rw [show b₀⁻¹ * (b : G) * b₀ = (b : G) from by
                rw [mul_assoc, ← hbb, inv_mul_cancel_left]]
          _ = c * b₀ * ((n : G) * (b : G) * (n : G)⁻¹) * (c * b₀)⁻¹ := by group
      rw [heq]
      have hmem : z * ((n : G) * (b : G) * (n : G)⁻¹) * z⁻¹ ∈ Bs := by
        rw [← hz]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hb)
      exact hmem
    have hcard' : Nat.card ↥(Bs.map (MulAut.conj n').toMonoidHom) = Nat.card ↥Bs :=
      Subgroup.card_map_of_injective (MulAut.conj n').injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard'.symm)
  refine ⟨n', hn'L, hn'N, ⟨b₀, hb₀⟩, ?_⟩
  have hn_eq : (⟨n', Subgroup.le_normalizer hn'L⟩ :
      ↥(Subgroup.normalizer (L : Set G))) =
      ⟨c, Subgroup.le_normalizer hcL⟩ * ⟨b₀ * (n : G) * b₀⁻¹,
        (Subgroup.normalizer (L : Set G)).mul_mem
          ((Subgroup.normalizer (L : Set G)).mul_mem (hNL hb₀) (Subgroup.le_normalizer n.2))
          ((Subgroup.normalizer (L : Set G)).inv_mem (hNL hb₀))⟩ := Subtype.ext rfl
  have hb₀n_eq : (⟨b₀ * (n : G) * b₀⁻¹,
      (Subgroup.normalizer (L : Set G)).mul_mem
        ((Subgroup.normalizer (L : Set G)).mul_mem (hNL hb₀) (Subgroup.le_normalizer n.2))
        ((Subgroup.normalizer (L : Set G)).inv_mem (hNL hb₀))⟩ :
      ↥(Subgroup.normalizer (L : Set G))) =
      ⟨b₀, hNL hb₀⟩ * ⟨n, Subgroup.le_normalizer n.2⟩ * ⟨b₀, hNL hb₀⟩⁻¹ := Subtype.ext rfl
  have hc_act : e6QTwoSixNormAction θ ⟨c, Subgroup.le_normalizer hcL⟩ = 1 := by
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
    rw [e6QTwoSixNormAction_apply]
    have h1 : Subgroup.normalizerMonoidHom L ⟨c, Subgroup.le_normalizer hcL⟩ =
        MulAut.conj (⟨c, hcL⟩ : ↥L) := by
      ext l
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [h1, hconj, map_one, map_one]
  rw [hn_eq, map_mul, hb₀n_eq, map_mul, map_mul, map_inv, hc_act, one_mul,
    e6QTwoSixNormAction_of_mem_Bs θ hNL ⟨b₀, hb₀⟩, e6QTwoSixNormAction_of_mem_L θ n,
    e6QTwoSixConjOnQuot_permPre hK hQ θ τ]

theorem exists_mem_normalizer_frameAct_perm
    (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ)
    (hrange5 : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) (τ : Equiv.Perm (Fin 6)) :
    ∃ n' : G, n' ∈ L ∧ ∃ hn' : n' ∈ Subgroup.normalizer (Bs : Set G),
      ∀ (b : ↥Bs) (σ : Fin 6 → Kˣ), (∀ k, σ k ^ 3 = 1) →
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
          (e6QTwoSixFrameAction hNL θ b) σ →
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
          (e6QTwoSixFrameAction hNL θ
            ⟨n' * (b : G) * n'⁻¹,
              (Subgroup.mem_normalizer_iff.mp hn' (b : G)).mp b.2⟩) (σ ∘ ⇑τ.symm) := by
  obtain ⟨n', hnL, hn', b₀, hact⟩ :=
    e6QTwoSix_exists_mem_normalizer hK θ hNL hfull hrange5 hperf hBs hcard hx hx1 hBL
      hstar hI hLx τ
  refine ⟨n', hnL, hn', ?_⟩
  intro b σ hσ3 hσ
  have hb0 : n' * (b : G) * n'⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hn' (b : G)).mp b.2
  have hperm : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoSixFramePerm hK hQ τ * e6QTwoSixFrameAction hNL θ b *
        (e6QTwoSixFramePerm hK hQ τ)⁻¹) (σ ∘ ⇑τ.symm) :=
    e6QTwoSixFrameAct_perm hK hσ τ
  obtain ⟨σ₀, hσ₀0, hσ₀3, hσ₀fr⟩ :=
    e6QTwoSixFrameAct_of_mem_range hK hNL θ hfull hrange5
      (MonoidHom.mem_range.mpr ⟨b₀, rfl⟩)
  have hσ3' : ∀ k, (σ ∘ ⇑τ.symm) k ^ 3 = 1 := by
    intro k
    rw [Function.comp_apply]
    exact hσ3 (τ.symm k)
  have hcomm : e6QTwoSixFrameAction hNL θ b₀ *
      (e6QTwoSixFramePerm hK hQ τ * e6QTwoSixFrameAction hNL θ b *
        (e6QTwoSixFramePerm hK hQ τ)⁻¹) =
      (e6QTwoSixFramePerm hK hQ τ * e6QTwoSixFrameAction hNL θ b *
        (e6QTwoSixFramePerm hK hQ τ)⁻¹) * e6QTwoSixFrameAction hNL θ b₀ :=
    e6QTwoSix_frameAct_comm hK hσ₀3 hσ3' hσ₀fr hperm
  have hbb : e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFrameAction hNL θ b =
      e6QTwoSixFrameAction hNL θ b * e6QTwoSixFrameAction hNL θ b₀ :=
    e6QTwoSix_frameAct_comm hK hσ₀3 hσ3 hσ₀fr hσ
  have hconj := e6QTwoSixFrameAction_conj θ hNL hnL (b := b) hb0
  rw [hconj]
  rw [show e6QTwoSixConjOnQuot θ ⟨n', hnL⟩ =
      e6QTwoSixNormAction θ ⟨n', Subgroup.le_normalizer hnL⟩ from
    (e6QTwoSixNormAction_of_mem_L θ ⟨n', hnL⟩).symm]
  rw [hact]
  have hbb_inv : (e6QTwoSixFrameAction hNL θ b₀)⁻¹ * e6QTwoSixFrameAction hNL θ b *
      e6QTwoSixFrameAction hNL θ b₀ = e6QTwoSixFrameAction hNL θ b := by
    calc (e6QTwoSixFrameAction hNL θ b₀)⁻¹ * e6QTwoSixFrameAction hNL θ b *
          e6QTwoSixFrameAction hNL θ b₀
        = (e6QTwoSixFrameAction hNL θ b₀)⁻¹ *
            (e6QTwoSixFrameAction hNL θ b * e6QTwoSixFrameAction hNL θ b₀) := by group
      _ = (e6QTwoSixFrameAction hNL θ b₀)⁻¹ *
            (e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFrameAction hNL θ b) := by rw [hbb]
      _ = e6QTwoSixFrameAction hNL θ b := by group
  have heq : (e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFramePerm hK hQ τ *
        (e6QTwoSixFrameAction hNL θ b₀)⁻¹) * e6QTwoSixFrameAction hNL θ b *
        (e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFramePerm hK hQ τ *
          (e6QTwoSixFrameAction hNL θ b₀)⁻¹)⁻¹ =
      e6QTwoSixFramePerm hK hQ τ * e6QTwoSixFrameAction hNL θ b *
        (e6QTwoSixFramePerm hK hQ τ)⁻¹ := by
    calc (e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFramePerm hK hQ τ *
          (e6QTwoSixFrameAction hNL θ b₀)⁻¹) * e6QTwoSixFrameAction hNL θ b *
          (e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFramePerm hK hQ τ *
            (e6QTwoSixFrameAction hNL θ b₀)⁻¹)⁻¹
        = e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFramePerm hK hQ τ *
            ((e6QTwoSixFrameAction hNL θ b₀)⁻¹ * e6QTwoSixFrameAction hNL θ b *
              e6QTwoSixFrameAction hNL θ b₀) * (e6QTwoSixFramePerm hK hQ τ)⁻¹ *
            (e6QTwoSixFrameAction hNL θ b₀)⁻¹ := by group
      _ = e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFramePerm hK hQ τ *
            e6QTwoSixFrameAction hNL θ b * (e6QTwoSixFramePerm hK hQ τ)⁻¹ *
            (e6QTwoSixFrameAction hNL θ b₀)⁻¹ := by rw [hbb_inv]
      _ = e6QTwoSixFrameAction hNL θ b₀ *
            (e6QTwoSixFramePerm hK hQ τ * e6QTwoSixFrameAction hNL θ b *
              (e6QTwoSixFramePerm hK hQ τ)⁻¹) *
            (e6QTwoSixFrameAction hNL θ b₀)⁻¹ := by group
      _ = (e6QTwoSixFramePerm hK hQ τ * e6QTwoSixFrameAction hNL θ b *
              (e6QTwoSixFramePerm hK hQ τ)⁻¹) *
            e6QTwoSixFrameAction hNL θ b₀ * (e6QTwoSixFrameAction hNL θ b₀)⁻¹ := by
          rw [hcomm]
      _ = e6QTwoSixFramePerm hK hQ τ * e6QTwoSixFrameAction hNL θ b *
            (e6QTwoSixFramePerm hK hQ τ)⁻¹ := by group
  rw [heq]
  exact hperm

end CFSG.StandardType.E6QTwo

end
