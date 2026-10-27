module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.StandardType.Line63 CFSG.StandardType.Line63.H5
  CFSG.StandardType.USixTwo CFSG.ClassicalGroups.UnitaryFlag

theorem redMkL_rangeRestrict_ker {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    ((redMkL X).rangeRestrict).ker = zTwo X := by
  ext l
  change (redMkL X).rangeRestrict l = 1 ↔ _
  have hval : (redMkL X).rangeRestrict l = 1 ↔ redMkL X l = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hval, redMkL_eq_one_iff]
  constructor
  · rintro ⟨hlX, hlc, hlpow⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (hlc x x.2).symm
    · exact pow_two_pow_card l (Subtype.ext hlpow)
  · rintro ⟨hlc, hlpow⟩
    refine ⟨l.2, ?_, ?_⟩
    · intro x hx
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hlc (⟨x,hx⟩ : X))).symm
    · exact pow_two_pow_card (l : G) (congrArg Subtype.val hlpow)

noncomputable def redQtEquiv {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    Qt X ≃* (redMkL X).range :=
  QuotientGroup.liftEquiv (zTwo X) (redMkL X).rangeRestrict_surjective
    (redMkL_rangeRestrict_ker X).symm

theorem redQtEquiv_mk {G : Type} [Group G] [Finite G] (X : Subgroup G) (l : X) :
    redQtEquiv X (qmk X l) = (redMkL X).rangeRestrict l := by
  exact QuotientGroup.liftEquiv_coe _ _ _ l

open CFSG.ClassicalGroups.UnitaryFlag

theorem redQtEquiv_gamma {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hNbar : (redMkB hN).range ≤ Subgroup.normalizer ((redMkL X).range : Set (RedGrp X)))
    (b : Bs) (l : Qt X) :
    ggGamma (redMkL X).range hNbar ((redMkB hN).rangeRestrict b) (redQtEquiv X l) =
      redQtEquiv X ((qAutHom X (ggGamma X hN b)) l) := by
  obtain ⟨l, rfl⟩ := qmk_surjective l
  rw [qAutHom_mk, redQtEquiv_mk, redQtEquiv_mk]
  apply Subtype.ext
  change (redMkB hN b) * redMkL X l * (redMkB hN b)⁻¹ =
    redMkL X (ggGamma X hN b l)
  exact redMk_conj (L := X) (Subgroup.inclusion hN b) l

theorem exists_diag_redQt {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} {d : ℕ}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hNbar : (redMkB hN).range ≤ Subgroup.normalizer ((redMkL X).range : Set (RedGrp X)))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {φQ : ↥(unitarySU 2 1 F d) →* Qt X} (hM : UnitTB.Model φQ)
    (hdiag : ∀ a ∈ ((ggGamma X hN).range.map (qAutHom X)),
      ∃ t : Fin d → F, LineU.ActsDiagU φQ a t) :
    ∃ φ : ↥(unitarySU 2 1 F d) →* (redMkL X).range,
      UnitTB.Model φ ∧ ∀ a ∈ (ggGamma (redMkL X).range hNbar).range,
        ∃ t : Fin d → F, LineU.ActsDiagU φ a t := by
  let e := redQtEquiv X
  let φ := e.toMonoidHom.comp φQ
  refine ⟨φ, ⟨hM.field, e.surjective.comp hM.surj, ?_⟩, ?_⟩
  · intro g hg
    apply hM.ker g
    apply e.injective
    simpa [φ] using hg
  · rintro a ⟨b, rfl⟩
    obtain ⟨b0, hb0⟩ := (redMkB hN).rangeRestrict_surjective b
    obtain ⟨t, D, hD, hd, hact⟩ := hdiag (qAutHom X (ggGamma X hN b0))
      (Subgroup.mem_map.mpr ⟨ggGamma X hN b0, ⟨b0, rfl⟩, rfl⟩)
    refine ⟨t, D, hD, hd, ?_⟩
    intro g
    subst b
    change ggGamma (redMkL X).range hNbar ((redMkB hN).rangeRestrict b0) (e (φQ g)) =
      e (φQ (LineU.conjN D hD g))
    rw [redQtEquiv_gamma hN hNbar, hact g]


theorem exists_diagonal_cover_of_unitary_six_two_red
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (hXp : commutator X = ⊤)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (unitarySU 2 1 F 6))
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 1 F 6)) (LargeEvenGUSet (Fin 6) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hγcard : 3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    ∃ (hNbar : (redMkB hN).range ≤
        Subgroup.normalizer ((redMkL X).range : Set (RedGrp X))),
      ∃ φ : ↥(unitarySU 2 1 F 6) →* (redMkL X).range,
        UnitTB.Model φ ∧
          ∀ a ∈ (ggGamma (redMkL X).range hNbar).range,
            ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t := by
  classical
  let Xbar : Subgroup (RedGrp X) := (redMkL X).range
  let Bbar : Subgroup (RedGrp X) := (redMkB hN).range
  have hNbar : Bbar ≤ Subgroup.normalizer (Xbar : Set (RedGrp X)) := by
    intro b hb
    have : Xbar.Normal := by
      change (redMkL X).range.Normal
      infer_instance
    have htop : Subgroup.normalizer (Xbar : Set (RedGrp X)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [htop]
    exact Subgroup.mem_top b
  let ψ : ↥X →* LargeEvenProj (unitarySU 2 1 F 6) := ggQuotHom θ
  have hzker : zTwo X ≤ ψ.ker := by
    rw [show ψ.ker = Subgroup.center ↥X by
      simpa [ψ] using ker_ggQuotHom θ]
    exact zTwo_le_center
  let ψQ : Qt X →* LargeEvenProj (unitarySU 2 1 F 6) := qLift ψ hzker
  have hψQ : Function.Surjective ψQ :=
    qLift_surjective hzker (ggQuotHom_surjective θ)
  have hkerQ : ψQ.ker ≤ Subgroup.center (Qt X) :=
    qLift_ker_le_center hzker (by simpa [ψ] using (ker_ggQuotHom θ).le)
  have hperfQ : commutator (Qt X) = ⊤ := qmk_perfect hXp
  have hoddQ : Odd (Nat.card ψQ.ker) :=
    qLift_odd_ker hzker (by simpa [ψ] using (ker_ggQuotHom θ).le)
  let AQ : Subgroup (MulAut (Qt X)) := (ggGamma X hN).range.map (qAutHom X)
  have hγrange : IsElemAbelian 3 (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hAQ : IsElemAbelian 3 AQ := by
    simpa [AQ] using IsElemAbelian.map hγrange (qAutHom X)
  have hcardQ : 3 ^ 4 ≤ Nat.card AQ := by
    change 3 ^ 4 ≤ Nat.card ((ggGamma X hN).range.map (qAutHom X))
    rw [Subgroup.card_map_of_injective (qAutHom_injective hXp)]
    exact hγcard
  have hAIQ : ∀ a ∈ AQ, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 1 F 6)) (LargeEvenGUSet (Fin 6) F (2 ^ 1)),
      ∀ l : Qt X, x (ψQ l) = ψQ (a l) := by
    intro a ha
    change a ∈ (ggGamma X hN).range.map (qAutHom X) at ha
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, rfl⟩ := hγ
    obtain ⟨x, hxI, hxind⟩ := hBI (b⁻¹) (Subgroup.inv_mem Bs b.2)
    refine ⟨x, hxI, ?_⟩
    intro l
    obtain ⟨l0, rfl⟩ := qmk_surjective l
    rw [qAutHom_mk]
    change x (ggQuotHom θ l0) = ggQuotHom θ (ggGamma X hN b l0)
    have hrel : ((ggGamma X hN b l0 : ↥X) : G) = (b⁻¹ : ↥Bs)⁻¹ * (l0 : G) * (b⁻¹ : ↥Bs) := by
      simp only [Subgroup.coe_inv, inv_inv]
      exact ggGamma_coe X hN b l0
    have hx := hxind l0 (ggGamma X hN b l0) hrel
    simpa [ggQuotHom_apply, ψQ, qLift_mk] using hx
  obtain ⟨φQ, hMQ, hdiagQ⟩ := USixTwo.exists_diagModel_odd
    (by simpa using hF) hψQ hkerQ hperfQ hoddQ hAQ hAIQ hcardQ
  obtain ⟨φ, hM, hdiag⟩ := exists_diag_redQt hN hNbar hMQ hdiagQ
  exact ⟨hNbar, φ, hM, hdiag⟩
