module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTSpin
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Holds
public import CFSG.RankThree.GF2n.Stroth80.Sec118SpFieldLe

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.LieType.Universal.Symplectic
open TauCeti.GLSymplecticFin
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module
open scoped commutatorElement


theorem cmSpNotTransv_holds {G : Type} [Group G] [Finite G] (M Q Z B : Subgroup G)
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (n m x : ℕ) (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (hx : 2 ^ x = Nat.card Z)
    (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G))
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h) :
    m = 3 ∧ Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ 9 ∧
      (∀ W : Subgroup G, Z ≤ W → W ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆ →
        (∀ g ∈ XbarPre M Q Z B, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        W = Z ∨ W = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) :=
  cmSpNotTransv_of_negT (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => negT_producer) M Q Z B hc n m x hw hn
    ha2 hLm hx a h hnT

theorem Ctx.exists_spin_input {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {m x : ℕ} (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (hK : Nat.card K = 2 ^ x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) :
    m = 3 ∧ 4 ≤ Nat.card K ∧ finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 8 ∧
      (polarBilin (cmCommQf B φ)).Nondegenerate ∧
      ∃ (Θ : ↥(XbarH M Q Z B) →* StatedSp m K)
        (ψ : StatedSp m K →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))),
        Function.Surjective Θ ∧ (∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
        (∀ s, ψ (Θ s) = cmCommAct hc φ s) ∧
        (∀ g v, cmCommQf B φ (ψ g v) = cmCommQf B φ v) ∧
        (∀ W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ), (∀ g, ∀ w ∈ W, ψ g w ∈ W) →
          W = ⊥ ∨ W = ⊤) ∧
        ∀ r : RootSubgroupIndex m, (∀ i, r ≠ .positiveLong i) → (∀ i, r ≠ .negativeLong i) →
          ∀ c : K, c ≠ 0 → IsLongRootElement (cmCommQf B φ) (ψ (SpExtras.elt r c)) :=
  hc.exists_spin_input_of_negT (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => negT_producer) hLm ha2 hnT hD
    hK φ hφπ hφk hφQ

theorem cmSpStructure_of_M2
    (hM2 : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal],
      Ctx M Q Z B → ∀ (n m x : ℕ), Width Q Z n → 2 < n → (∃ a ∈ LB M Q B, IsA2 Q Z a) →
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x → 2 ^ x = Nat.card Z →
      ∀ (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)),
        ¬ CMSpTransvAt M Q Z B m x a h →
        ∃ y : ↥M, (QuotientGroup.mk y : Mbar M Q) ∈ Xbar M Q Z B ∧
          Odd (orderOf (QuotientGroup.mk y : Mbar M Q)) ∧
          ∀ v ∈ Z ⊔ ⁅Q, XbarPre M Q Z B⁆, ⁅(y : G), v⁆ ∈ Z → v ∈ Z) :
    CMSpStructure := by
  intro G _ _ M Q Z B _ hc n m x hw hn ha2 hLm
  refine ⟨hc.two_pow_le_card_Z_of_psp hw ha2 hLm, fun hx a h => ⟨fun hT => ?_, fun hnT => ?_⟩⟩
  · exact cmSpTransv_holds M Q Z B hc n m x hw hn ha2 hLm hx a h hT
  · obtain ⟨h3, h9, hM1⟩ := cmSpNotTransv_holds M Q Z B hc n m x hw hn ha2 hLm hx a h hnT
    exact ⟨h3, h9, hM1, hM2 G M Q Z B hc n m x hw hn ha2 hLm hx a h hnT⟩

theorem Ctx.m2_of_fixedPointFree {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {G' : Type*} [Group G'] (Θ : ↥(XbarH M Q Z B) →* G') (hΘ : Function.Surjective Θ)
    (hΘk : ∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q)
    (ψ : G' →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)))
    (hψΘ : ∀ s, ψ (Θ s) = cmCommAct hc φ s) {g : G'} (hgodd : Odd (orderOf g))
    (hgfix : ∀ v, ψ g v = v → v = 0) :
    ∃ y : ↥M, (QuotientGroup.mk y : Mbar M Q) ∈ Xbar M Q Z B ∧
      Odd (orderOf (QuotientGroup.mk y : Mbar M Q)) ∧
      ∀ v ∈ Z ⊔ ⁅Q, XbarPre M Q Z B⁆, ⁅(y : G), v⁆ ∈ Z → v ∈ Z := by
  obtain ⟨s, rfl⟩ := hΘ g
  have hmk : (QuotientGroup.mk (⟨((s : ↥(H0 M Z)) : G), ((s : ↥(H0 M Z)).2).1⟩ : ↥M) :
      Mbar M Q) = ((xbarHToXbar M Q Z B s : ↥(Xbar M Q Z B)) : Mbar M Q) :=
    (coe_xbarHToXbar s).symm
  refine ⟨⟨((s : ↥(H0 M Z)) : G), ((s : ↥(H0 M Z)).2).1⟩, ?_, ?_, ?_⟩
  · rw [hmk]
    exact (xbarHToXbar M Q Z B s).2
  · have hord : orderOf (xbarHToXbar M Q Z B s) = orderOf (Θ s) := by
      rw [orderOf_eq_orderOf_iff]
      intro n
      rw [← map_pow, ← map_pow, xbarHToXbar_eq_one_iff, hΘk]
    rw [hmk, Subgroup.orderOf_coe, hord]
    exact hgodd
  · intro v hv hcomm
    have hYQ : (Z ⊔ ⁅Q, XbarPre M Q Z B⁆ : Subgroup G) ≤ Q :=
      sup_le hc.Z_le_Q (commutator_le_Q hc)
    have hvQ : v ∈ Q := hYQ hv
    have hπv : M₀.π v ∈ cmComm M Q Z B K γ M₀ φ :=
      (hc.mem_img_sup_iff_mem_cmComm hD φ hφπ _).mp ⟨v, hv, hvQ, rfl⟩
    have hcQ : ⁅((s : ↥(H0 M Z)) : G), v⁆ ∈ Q := hc.Z_le_Q hcomm
    have hconj : ((s : ↥(H0 M Z)) : G) * v * ((s : ↥(H0 M Z)) : G)⁻¹ =
        ⁅((s : ↥(H0 M Z)) : G), v⁆ * v := by
      rw [commutatorElement_def]
      group
    have hfix : φ (s : ↥(H0 M Z)) (M₀.π v) = M₀.π v := by
      rw [← hφπ _ v hvQ, hconj, M₀.π_mul _ hcQ _ hvQ, (M₀.π_ker _ hcQ).mpr hcomm, zero_add]
    have h0 := hgfix ⟨M₀.π v, hπv⟩ (by
      rw [hψΘ s]
      exact Subtype.ext hfix)
    exact (M₀.π_ker v hvQ).mp (congrArg Subtype.val h0)

theorem cmSpStructure_of_spinFPF
    (hFPF : ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Qf : QuadraticForm K V),
      4 ≤ Nat.card K → finrank K V = 8 → (polarBilin Qf).Nondegenerate →
      ∀ ψ : StatedSp 3 K →* (V ≃ₗ[K] V), (∀ g v, Qf (ψ g v) = Qf v) →
      (∀ W : Submodule K V, (∀ g, ∀ w ∈ W, ψ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      (∀ r : RootSubgroupIndex 3, (∀ i, r ≠ .positiveLong i) → (∀ i, r ≠ .negativeLong i) →
        ∀ c : K, c ≠ 0 → IsLongRootElement Qf (ψ (SpExtras.elt r c))) →
      ∃ g : StatedSp 3 K, Odd (orderOf g) ∧ ∀ v, ψ g v = v → v = 0) :
    CMSpStructure := by
  refine cmSpStructure_of_M2 fun G _ _ M Q Z B _ hc n m x _ _ ha2 hLm hx a h hnT => ?_
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hK : Nat.card K = 2 ^ x := hD.card.trans hx.symm
  obtain ⟨rfl, hq4, h8, hpol, Θ, ψ, hΘ, hΘk, hψΘ, hψQ, hirr, hsieg⟩ :=
    hc.exists_spin_input hLm ha2 hnT hD hK φ hφπ hφk hφQ
  obtain ⟨g, hgodd, hgfix⟩ := hFPF K _ (cmCommQf B φ) hq4 h8 hpol ψ hψQ hirr hsieg
  exact hc.m2_of_fixedPointFree hD φ hφπ Θ hΘ hΘk ψ hψΘ hgodd hgfix

end CFSG.RankThree.GF2n.Stroth80
