module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] {n : ℕ}

@[expose] noncomputable def e6QTwoNFrameAction {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) :
    Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) :=
  (MulAut.congr θ).toMonoidHom.comp
    ((e6QTwoQuotCenterAutHom L).comp (e6QTwoBstarConjAction hNL))

omit [Finite G] [Finite K] in
theorem e6QTwoNFrameAction_eq {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (b : Bs) :
    e6QTwoNFrameAction hNL θ b =
      (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b)) := rfl

omit [Finite G] [Finite K] in
theorem e6QTwoNFrameAction_apply {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (b : Bs) (l : L) :
    e6QTwoNFrameAction hNL θ b (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
      θ (QuotientGroup.mk' (Subgroup.center L) ⟨(b : G) * (l : G) * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩) := by
  rw [e6QTwoNFrameAction_eq, e6QTwoMulAutCongrApply, e6QTwoQuotCenterAutHom_mk]
  exact congrArg θ (congrArg (QuotientGroup.mk' (Subgroup.center L))
    (Subtype.ext (e6QTwoBstarConjAction_apply hNL b l)))

omit [Finite G] [Finite K] in
theorem e6QTwoNFrameAction_ker {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) :
    (e6QTwoNFrameAction hNL θ).ker =
      (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hb
    have hβb : (MulAut.congr θ)
        (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b)) = 1 := hb
    have hφ1 : e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b) = 1 :=
      (MulAut.congr θ).injective (by rw [hβb]; exact (map_one (MulAut.congr θ)).symm)
    have h2 : e6QTwoBstarConjAction hNL b = 1 :=
      e6QTwoQuotCenterAutHom_injective hperf (by rw [hφ1, map_one])
    exact ⟨b.2, (e6QTwoBstarConjAction_eq_one_iff hNL b).mp h2⟩
  · rintro ⟨-, hbC⟩
    have h1 : e6QTwoBstarConjAction hNL b = 1 :=
      (e6QTwoBstarConjAction_eq_one_iff hNL b).mpr hbC
    have h2 : e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b) = 1 := by
      rw [h1, map_one]
    rw [e6QTwoNFrameAction_eq hNL θ b, h2, map_one]

omit [Finite G] [Finite K] in
theorem e6QTwoNFrameAction_isElemAbelian_range {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hBs : IsElemAbelian 3 Bs) :
    IsElemAbelian 3 (e6QTwoNFrameAction hNL θ).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨a', ha'⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha', ← hb', ← map_mul, ← map_mul, hBs.1.is_comm.comm a' b']
  · obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp ha
    rw [← hb', ← map_pow]
    have hb3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 (b' : G) b'.2)
    rw [hb3, map_one]

omit [Finite G] [Finite K] in
theorem e6QTwoNFrameAction_mem_matConjImage {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) (LargeEvenGUSet (Fin (n + 1))
          K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (b : Bs) :
    e6QTwoNFrameAction hNL θ b ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
      (LargeEvenGUSet (Fin (n + 1)) K (2 ^ 1)) := by
  obtain ⟨ψ, hψ, hψind⟩ := hI (b : G)⁻¹ (inv_mem b.2)
  have hβind : LargeEvenInduces θ
      (fun l l' : L => (l' : G) = (b : G) * l * (b : G)⁻¹) (e6QTwoNFrameAction hNL θ b) := by
    intro l l' hl'
    have hsub : (⟨(b : G) * (l : G) * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩ : L) = l' := by
      apply Subtype.ext
      simpa using hl'.symm
    rw [← hsub]
    exact e6QTwoNFrameAction_apply hNL θ b l
  have hrel : ∀ l : L, ∃ l' : L, (l' : G) = (b : G) * l * (b : G)⁻¹ := fun l =>
    ⟨⟨_, (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩, rfl⟩
  have hψβ : ψ = e6QTwoNFrameAction hNL θ b := by
    apply e6QTwoLargeEvenInducesEqOfForallExists hrel
    · intro l l' hl'
      exact hψind l l' (by rw [inv_inv]; exact hl')
    · exact hβind
  rwa [hψβ] at hψ

omit [Finite G] in
theorem e6QTwoNFrameAction_range_le_inndiag (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) (LargeEvenGUSet (Fin (n + 1))
          K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    (e6QTwoNFrameAction hNL θ).range ≤
      InndiagSU.inndiagU (USixTwo.fieldDataFour hK) (by omega : 1 ≤ n + 1) := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  rintro φ' ⟨b, rfl⟩
  rw [InndiagSU.mem_inndiagU]
  exact InndiagSU.congr_mem_primeFormD (USixTwo.fieldDataFour hK) (by omega : 1 ≤ n + 1) hK'
    (e6QTwoNFrameAction_mem_matConjImage hNL θ hI b)

omit [Finite G] in
omit [Finite G] [Finite K] in
theorem e6QTwoNFrameAction_card_ker_le {Bs L : Subgroup G} {x : G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) :
    Nat.card ↥(e6QTwoNFrameAction hNL θ).ker ≤ 3 := by
  rw [e6QTwoNFrameAction_ker hNL θ hperf]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ Bs)).toEquiv]
  rw [hBL, Nat.card_zpowers]
  have hx3 : x ^ 3 = 1 := hBs.2 x hx
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hx3)

omit [Finite G] in
theorem e6QTwoNFrameAction_card_range_le (hK : Nat.card K = 4) (hn : 3 ≤ n) {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hBs : IsElemAbelian 3 Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) (LargeEvenGUSet (Fin (n + 1))
          K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    Nat.card ↥(e6QTwoNFrameAction hNL θ).range ≤ 3 ^ n := by
  let β := e6QTwoNFrameAction hNL θ
  change Nat.card β.range ≤ 3 ^ n
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  by_cases hbig : 3 ^ ((n + 1) / 3 + 1) < Nat.card β.range
  · obtain ⟨Q, hQ, hQfr⟩ := TableBUD.exists_frame_inndiag (h := USixTwo.fieldDataFour hK) hK'
      (by omega : 3 ≤ n + 1) (by simp; omega : (n + 1, 2 ^ 1) ≠ (3, 2))
      (by omega : ¬(n + 1 = 3 ∧ 2 ^ 1 = 2)) (by norm_num : Nat.Prime 3)
      (by norm_num : 3 ∣ 2 ^ 1 + 1)
      (e6QTwoNFrameAction_isElemAbelian_range hNL θ hBs)
      (e6QTwoNFrameAction_range_le_inndiag hK hNL θ hI) (by simpa using hbig)
    have hQ' : ∀ e : β.range, ∃ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 ∧
        (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e : MulAut _) σ :=
      fun e => hQfr e.1 e.2
    choose σ hσ0 hσ3 hσn hσfr using hQ'
    let f : β.range → (Fin n → Kˣ) := fun e i => σ e (Fin.succAbove 0 i)
    have hf_inj : Function.Injective f := by
      intro e e' he
      have hσeq : σ e = σ e' := by
        funext k
        by_cases hk : k = 0
        · rw [hk, hσ0 e, hσ0 e']
        · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (x := k) (y := (0 : Fin (n + 1))) hk
          exact congrFun he i
      have h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e : MulAut _) (σ e) := hσfr e
      have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e' : MulAut _) (σ e) :=
        hσeq ▸ hσfr e'
      exact Subtype.ext (TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK)
        (Q := Q) (hQ := hQ) (hσ := hσn e) h1 h2)
    have hcard : Nat.card β.range ≤ Nat.card (Fin n → Kˣ) :=
      Nat.card_le_card_of_injective f hf_inj
    rw [Nat.card_pi] at hcard
    have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hunits] using hcard
  · have hle : Nat.card β.range ≤ 3 ^ ((n + 1) / 3 + 1) := by omega
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

structure GGQ2S08RoN {G : Type} [Group G] [Finite G] (n : ℕ) (Bs L : Subgroup G) (x : G) where
  K : Type
  instField : Field K
  instFinite : Finite K
  hK : Nat.card K = 4
  hn : 5 ≤ n
  θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))
  Q : GL (Fin (n + 1)) K
  hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
    (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))
  hperf : commutator ↥L = ⊤
  hBs : IsElemAbelian 3 Bs
  hcard : Nat.card Bs = 3 ^ (n + 1)
  hx : x ∈ Bs
  hx1 : x ≠ 1
  hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x
  hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs
  hNL : Bs ≤ Subgroup.normalizer (L : Set G)
  hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) (LargeEvenGUSet (Fin (n + 1)) K
        (2 ^ 1)),
    LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ
  hLx : L ≤ Subgroup.centralizer {x}
  hLsn : IsSubnormal L (Subgroup.centralizer {x})
  hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) ∨
    ((Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) ∧ ¬ 3 ∣ n)
  hfull : ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
    ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoNFrameAction hNL θ b) σ
  hrange : Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n

attribute [instance] GGQ2S08RoN.instField GGQ2S08RoN.instFinite

namespace GGQ2S08RoN

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {n : ℕ}

noncomputable abbrev act (c : GGQ2S08RoN n Bs L x) :
    Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) c.K (2 ^ 1))) :=
  e6QTwoNFrameAction c.hNL c.θ

abbrev FrameDiag (c : GGQ2S08RoN n Bs L x) (b : Bs) (σ : Fin (n + 1) → c.Kˣ) : Prop :=
  TableBUD.FrameAct (USixTwo.fieldDataFour c.hK) c.Q c.hQ (c.act b) σ

end GGQ2S08RoN

end CFSG.StandardType.E6QTwo

end
