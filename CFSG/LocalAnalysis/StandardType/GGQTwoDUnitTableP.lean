module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrB
public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePDefs

import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

@[expose] def QTwoDeletedUnitaryCandidate (d : ℕ) (X : LargeEvenLabel) : Prop :=
  X = ⟨.twA, d, 1⟩ ∨ (X = ⟨.twA, d + 1, 1⟩ ∧ 3 ∣ d + 2) ∨ X = ⟨.C, d, 1⟩ ∨
    (Even d ∧ (X = ⟨.D, d, 1⟩ ∨ X = ⟨.D, d + 1, 1⟩)) ∨
    (Odd d ∧ (X = ⟨.twD, d, 1⟩ ∨ X = ⟨.twD, d + 1, 1⟩)) ∨
    (d = 6 ∧ X = ⟨.twE6, 0, 1⟩) ∨ (d = 7 ∧ X = ⟨.E7, 0, 1⟩) ∨ (d = 9 ∧ X = ⟨.E8, 0, 1⟩)

theorem ggQTwoDUnit_tablePRow {d : ℕ} (hd : 5 ≤ d) {X : LargeEvenLabel}
    (h : GGTablePRow 3 ⟨.twA, d - 1, 1⟩ X) : QTwoDeletedUnitaryCandidate d X := by
  unfold GGTablePRow at h
  simp only [LargeEvenLabel.mk.injEq] at h
  norm_num at h
  obtain ⟨-, h⟩ := h
  have e1 : d - 1 + 1 = d := by omega
  have e2 : d - 1 + 2 = d + 1 := by omega
  have e3 : (d - 1) + 3 = d + 2 := by omega
  have hEven : Odd (d - 1) → Even d := by
    intro ho
    have hd1 : d = (d - 1) + 1 := by omega
    rw [hd1, Nat.even_add_one, Nat.not_even_iff_odd]
    exact ho
  have hOdd : Even (d - 1) → Odd d := by
    intro he
    have hd1 : d = (d - 1) + 1 := by omega
    rw [hd1, Nat.odd_add_one, Nat.not_odd_iff_even]
    exact he
  rcases h with h | ⟨h, hdvd⟩ | h | ⟨ho, h⟩ | ⟨ho, h⟩ | ⟨he, h⟩ | ⟨he, h⟩ |
    ⟨h6, h⟩ | ⟨h7, h⟩ | ⟨h9, h⟩
  · exact Or.inl (by simpa [e1] using h)
  · refine Or.inr (Or.inl ⟨by simpa [e2] using h, ?_⟩)
    have h3 : 3 ∣ (d - 1) + 3 := dvd_add hdvd (dvd_refl 3)
    rwa [e3] at h3
  · exact Or.inr (Or.inr (Or.inl (by simpa [e1] using h)))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hEven ho, ?_⟩)))
    exact Or.inl (by simpa [e1] using h)
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hEven ho, ?_⟩)))
    exact Or.inr (by simpa [e2] using h)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hOdd he, ?_⟩))))
    exact Or.inl (by simpa [e1] using h)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hOdd he, ?_⟩))))
    exact Or.inr (by simpa [e2] using h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h6, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h7, h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h9, h⟩))))))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem qtwoDB18_label_of_chart {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) {n : ℕ} (hn : 4 ≤ n) {J : Subgroup G} {θ : Su F0 2 1 n →* G}
    (hθinj : Function.Injective θ) (hθrange : θ.range = J) :
    GGHasLabel ⟨.twA, n - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  have hcard : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF0]; norm_num
  have hsu := (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hcard n).symm
  have hθmem : ∀ y : Su F0 2 1 n, θ y ∈ J := fun y => by
    rw [← hθrange]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  let θ' : Su F0 2 1 n →* ↥J := θ.codRestrict J hθmem
  let φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F0 n) →* ↥J :=
    θ'.comp (MulEquiv.subgroupCongr hsu).toMonoidHom
  have hθ'inj : Function.Injective θ' := by
    intro y z hyz
    exact hθinj (Subtype.ext_iff.mp hyz)
  have hφinj : Function.Injective φ := by
    intro y z hyz
    change θ' ((MulEquiv.subgroupCongr hsu) y) = θ' ((MulEquiv.subgroupCongr hsu) z) at hyz
    exact (MulEquiv.subgroupCongr hsu).injective (hθ'inj hyz)
  have hφsurj : Function.Surjective φ := by
    intro w
    have hw : (w : G) ∈ θ.range := by rw [hθrange]; exact w.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hw
    refine ⟨(MulEquiv.subgroupCongr hsu).symm y, ?_⟩
    apply Subtype.ext
    change θ y = (w : G)
    exact hy
  have hφker : ∀ y : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F0 n),
      φ y = 1 → ∃ c : F0,
        ((y : GL (Fin n) F0) : Matrix (Fin n) (Fin n) F0) = Matrix.diagonal (fun _ => c) := by
    intro y hy
    have hy1 : y = 1 := hφinj (by rw [hy, map_one])
    cases hy1
    exact ⟨1, by simp [Matrix.diagonal_one]⟩
  have hM : UnitTB.Model φ :=
    ⟨⟨Nat.prime_two, le_refl 1, by rw [hF0]; norm_num⟩, hφsurj, hφker⟩
  exact ggHasLabel_of_unitaryModel (φ := φ) hM (by omega : 3 ≤ n)
    (by intro hh; have := congrArg Prod.fst hh; omega)


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem ggQTwoDUnit_label_J (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε) (c : Fin m) :
    GGHasLabel ⟨.twA, m - 2, 1⟩ (↥(qtwoDelJ ψ c) ⧸ Subgroup.center ↥(qtwoDelJ ψ c)) := by
  obtain ⟨θ, hθinj, hθrange, -⟩ := ggQTwoDUnit_J_iso (by omega) hbase c 1
  have hlab := qtwoDB18_label_of_chart (J := qtwoDelJ ψ c) hbase.card_field
    (by omega : 4 ≤ m - 1) hθinj hθrange
  simpa only [show (m - 1) - 1 = m - 2 by omega] using hlab

private theorem qtwoDB18_labelIso_twA_left {r n : ℕ} (hr : 4 ≤ r) {lab : LargeEvenLabel}
    (h : GGLabelIso ⟨.twA, r, n⟩ lab) : lab = ⟨.twA, r, n⟩ := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all <;> omega

private theorem qtwoDB18_label_eq {t : LargeEvenLieTag} {r r' n : ℕ} (h : r = r') :
    (⟨t, r, n⟩ : LargeEvenLabel) = ⟨t, r', n⟩ := by
  subst h
  rfl

theorem ggQTwoDUnit_candidate
    (hTP : GGNbrTablePNbrInputI1On GGRegimeDeletedUnitary1836) (hRig : GGLabelRigidInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥N ⧸ Subgroup.center ↥N) ∧
      QTwoDeletedUnitaryCandidate (m - 1) lab := by
  obtain rfl := hbase.p_eq
  have hK : GGInnerDiagOn Bs N :=
    ggQTwoDUnit_innerDiag_N hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂
  obtain ⟨labN, hΛN, hhasN, -⟩ := largeEvenMarking_exists_hasLabel hK
  have hstd := ggQTwoDUnit_stdSub hcfg hm hbase hcoords hdel.coord hb'B
  have hcfg' : GGConfig 3 B Bs x L (Subgroup.closure {x, (b' : G)}) (qtwoDelJ ψ c) :=
    ⟨hcfg.1.1.1.1, hcfg.1.1.1.2.1, hstd⟩
  have hL : GGInnerDiagOn Bs L := hcfg.1.1.2.2.1.1
  have hnbr : GGNbr 3 B x (Subgroup.closure {x, (b' : G)}) (qtwoDelJ ψ c) (b' : G) N :=
    ggQTwoDUnit_nbr hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂
  have hI1 : Bs ⊓ Subgroup.centralizer ((qtwoDelJ ψ c) : Set G) ≤
      Subgroup.closure {x, (b' : G)} :=
    le_of_eq (ggQTwoDUnit_cent_J (by omega) hbase hcoords hdel.coord)
  have hΛJ : LargeEvenInLambda2 (⟨.twA, m - 2, 1⟩ : LargeEvenLabel) := by
    refine ⟨by norm_num, ?_, ?_⟩
    · change 2 ≤ m - 2
      omega
    · change m - 2 = 2 → 2 ≤ (1 : ℕ)
      intro hh
      omega
  have hregime : GGRegimeDeletedUnitary1836 3 (Nat.card Bs) ⟨.twA, m - 2, 1⟩ labN := by
    refine ⟨rfl, m - 1, by omega, ?_, ?_⟩
    · rw [hbase.card_bs]; congr 1; omega
    · exact qtwoDB18_label_eq (by omega)
  have hhJ : GGHasLabel ⟨.twA, m - 2, 1⟩
      (↥(qtwoDelJ ψ c) ⧸ Subgroup.center ↥(qtwoDelJ ψ c)) :=
    ggQTwoDUnit_label_J (by omega) hbase c
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hhasJ', hhasK'⟩ :=
    hTP G 3 B Bs x L (Subgroup.closure {x, (b' : G)}) (qtwoDelJ ψ c) (b' : G) N
      hcfg' hL hK hnbr hI1 ⟨.twA, m - 2, 1⟩ labN hΛJ hΛN hregime hhJ hhasN
  refine ⟨labK', hΛK', hhasK', ?_⟩
  have hiso : GGLabelIso ⟨.twA, m - 2, 1⟩ labJ' :=
    hRig ⟨.twA, m - 2, 1⟩ labJ'
      (↥(qtwoDelJ ψ c) ⧸ Subgroup.center ↥(qtwoDelJ ψ c)) hΛJ hΛJ' hhJ hhasJ'
  have hlabJ' : labJ' = ⟨.twA, m - 2, 1⟩ := qtwoDB18_labelIso_twA_left (by omega) hiso
  rw [hlabJ'] at hrow
  have hrow' : GGTablePRow 3 ⟨.twA, (m - 1) - 1, 1⟩ labK' := by
    have hlab : (⟨.twA, (m - 1) - 1, 1⟩ : LargeEvenLabel) = ⟨.twA, m - 2, 1⟩ :=
      qtwoDB18_label_eq (by omega)
    rwa [hlab]
  exact ggQTwoDUnit_tablePRow (by omega : 5 ≤ m - 1) hrow'

end CFSG.StandardType.QTwo

end
