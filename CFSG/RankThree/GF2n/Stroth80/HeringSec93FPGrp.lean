module

public import CFSG.GroupTheory.PGroup.ExistsNeOneCommute
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93Core
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_fixed_mod_Z (hc : Ctx M Q Z B) {P : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hPM : P ≤ M) (hQZ : ¬ Q ≤ Z) : ∃ x ∈ Q, x ∉ Z ∧ ∀ p ∈ P, ⁅p, x⁆ ∈ Z := by
  classical
  have hMN : M ≤ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2
  set N : Subgroup G := Subgroup.normalizer (Z : Set G) with hNdef
  have hPN : P ≤ N := hPM.trans hMN
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQN : Q ≤ N := hQM.trans hMN
  haveI hnorm : (Z.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let π : ↥N →* ↥N ⧸ Z.subgroupOf N := QuotientGroup.mk' (Z.subgroupOf N)
  have hPp : IsPGroup 2 ↥(P.subgroupOf N) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  have hQp : IsPGroup 2 ↥(Q.subgroupOf N) :=
    (isPGroup_Q' hc.hyp).of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  have hP' : IsPGroup 2 ↥((P.subgroupOf N).map π) :=
    hPp.of_surjective (π.subgroupMap _) (π.subgroupMap_surjective _)
  have hO : IsPGroup 2 ↥((Q.subgroupOf N).map π) :=
    hQp.of_surjective (π.subgroupMap _) (π.subgroupMap_surjective _)
  obtain ⟨x₀, hx₀Q, hx₀Z⟩ := Set.not_subset.mp hQZ
  have hO1 : (Q.subgroupOf N).map π ≠ ⊥ := by
    intro hbot
    have hmem : π ⟨x₀, hQN hx₀Q⟩ ∈ (Q.subgroupOf N).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx₀Q)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hx₀Z (Subgroup.mem_subgroupOf.mp hmem)
  have hn : ∀ g ∈ (P.subgroupOf N).map π, ∀ o ∈ (Q.subgroupOf N).map π,
      g * o * g⁻¹ ∈ (Q.subgroupOf N).map π := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have ha' : (a : G) ∈ P := Subgroup.mem_subgroupOf.mp ha
    have hb' : (b : G) ∈ Q := Subgroup.mem_subgroupOf.mp hb
    refine ⟨a * b * a⁻¹, ?_, by simp⟩
    show a * b * a⁻¹ ∈ Q.subgroupOf N
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hPM ha')) (b : G)).mp hb'
    simpa using this
  obtain ⟨o, ⟨b, hb, rfl⟩, ho1, hoc⟩ :=
    CFSG.GroupTheory.exists_ne_one_commute_of_normalizes hP' hO hO1 hn
  have hbQ : (b : G) ∈ Q := Subgroup.mem_subgroupOf.mp hb
  refine ⟨b, hbQ, fun hbZ => ho1 ?_, fun p hp => ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hbZ
  · have hpN : p ∈ N := hPN hp
    have hmemP : π ⟨p, hpN⟩ ∈ (P.subgroupOf N).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hp)
    have h1 := hoc _ hmemP
    have h2 : π (⟨p, hpN⟩ * b * ⟨p, hpN⟩⁻¹ * b⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      group
    rw [QuotientGroup.mk'_apply] at h2
    rw [QuotientGroup.eq_one_iff] at h2
    have := Subgroup.mem_subgroupOf.mp h2
    simpa [commutatorElement_def] using this

theorem comm_mem_Z_of_isPGroup (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    {P : Subgroup G} (hP : IsPGroup 2 ↥P) (hPH : P ≤ H0 M Z) (hLP : LB M Q B ≤ P) :
    ∀ p ∈ P, ∀ b ∈ B, ⁅p, b⁆ ∈ Z := by
  classical
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  have hPM : P ≤ M := fun p hp => (hPH hp).1
  have hPZ : ∀ p ∈ P, ∀ z ∈ Z, p * z * p⁻¹ = z := by
    intro p hp z hz
    have h1 : z * p = p * z := Subgroup.mem_centralizer_iff.mp (hPH hp).2 z hz
    calc p * z * p⁻¹ = (z * p) * p⁻¹ := by rw [h1]
      _ = z := by group
  have hQZ : ¬ Q ≤ Z := by
    intro hle
    have h1 : Nat.card Q ≤ Nat.card Z := Subgroup.card_le_of_le hle
    rw [hw] at h1
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have h3 : Nat.card Z ^ 3 ≤ Nat.card Z ^ (2 * n + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : Nat.card Z ^ 3 = Nat.card Z * (Nat.card Z * Nat.card Z) := by ring
    nlinarith
  obtain ⟨x, hxQ, hxZ, hfix⟩ := exists_fixed_mod_Z hc hP hPM hQZ
  have hxB : x ∈ B ⊔ Z := by
    have hx : x ∈ CQt Q Z (LB M Q B) := ⟨hxQ, fun t ht => hfix t (hLP ht)⟩
    rw [h35] at hx
    exact hx
  obtain ⟨K, fK, finK, hchar, γ, M₀, hglob⟩ := stroth_globalModelData hc.hyp
  have hline : M₀.IsLine B := by
    obtain ⟨g, hg⟩ := hc.conj
    have hgZ : conjSubgroup g Z ≠ Z := fun h => hc.ne (hg.trans h)
    have hgQ : conjSubgroup g Z ≤ Q := hg ▸ hc.le
    have := hglob.line g hgZ hgQ
    rwa [← hg] at this
  have hBZ : ∀ b ∈ B, ∀ z ∈ Z, b * z = z * b := fun b hb z hz => by
    have := hc.conj_Z_of_mem_Q (hc.le hb) hz
    calc b * z = (b * z * b⁻¹) * b := by group
      _ = z * b := by rw [this]
  obtain ⟨b₀, hb₀B, z₀, hz₀Z, rfl⟩ := exists_mul_of_mem_sup hBZ hxB
  have hcomm : ∀ p ∈ P, ⁅p, b₀⁆ ∈ Z := by
    intro p hp
    have h1 := hfix p hp
    have hz := hPZ p hp z₀ hz₀Z
    have e : ⁅p, b₀ * z₀⁆ = ⁅p, b₀⁆ := by
      simp only [commutatorElement_def]
      calc p * (b₀ * z₀) * p⁻¹ * (b₀ * z₀)⁻¹
          = p * b₀ * p⁻¹ * (p * z₀ * p⁻¹) * z₀⁻¹ * b₀⁻¹ := by group
        _ = p * b₀ * p⁻¹ * z₀ * z₀⁻¹ * b₀⁻¹ := by rw [hz]
        _ = p * b₀ * p⁻¹ * b₀⁻¹ := by group
    rwa [e] at h1
  have hπb₀ : M₀.π b₀ ≠ 0 := by
    intro h0
    apply hxZ
    exact Z.mul_mem ((M₀.π_ker b₀ (hc.le hb₀B)).mp h0) hz₀Z
  obtain ⟨e, he0, he⟩ := hline
  obtain ⟨s₀, hs₀⟩ := (he (M₀.π b₀)).mp (M₀.pi_mem_img hb₀B (hc.le hb₀B))
  have hs₀ne : s₀ ≠ 0 := by
    rintro rfl
    exact hπb₀ (by rw [hs₀, zero_smul])
  intro p hp b hb
  obtain ⟨T, hTπ, -, -⟩ := hglob.linear_of_centralizes (hPM hp) (hPZ p hp)
  obtain ⟨s, hs⟩ := (he (M₀.π b)).mp (M₀.pi_mem_img hb (hc.le hb))
  have hπb : M₀.π b = (s * s₀⁻¹) • M₀.π b₀ := by
    rw [hs, hs₀, smul_smul, mul_assoc, inv_mul_cancel₀ hs₀ne, mul_one]
  have hpb₀ : M₀.π (p * b₀ * p⁻¹) = M₀.π b₀ := by
    have hz := hcomm p hp
    have e1 : p * b₀ * p⁻¹ = ⁅p, b₀⁆ * b₀ := by
      simp only [commutatorElement_def]
      group
    rw [e1, M₀.π_mul _ (hc.Z_le_Q hz) _ (hc.le hb₀B),
      (M₀.π_ker _ (hc.Z_le_Q hz)).mpr hz, zero_add]
  have hpb : M₀.π (p * b * p⁻¹) = M₀.π b := by
    rw [hTπ b (hc.le hb), hπb, map_smul, ← hTπ b₀ (hc.le hb₀B), hpb₀]
  have hpbQ : p * b * p⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hPM hp)) b).mp (hc.le hb)
  have hz : b⁻¹ * (p * b * p⁻¹) ∈ Z := (M₀.pi_eq_iff (hc.le hb) hpbQ).mp hpb.symm
  have e2 : ⁅p, b⁆ = b * (b⁻¹ * (p * b * p⁻¹)) * b⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e2, hc.conj_Z_of_mem_Q (hc.le hb) hz]
  exact hz

theorem isPGroup_pCoreIn (X : Subgroup G) : IsPGroup 2 ↥(inSubgroup (pCore 2) X) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype

theorem le_normalizer_pCoreIn (X : Subgroup G) :
    X ≤ Subgroup.normalizer (inSubgroup (pCore 2) X : Set G) := by
  have key : ∀ k ∈ X, ∀ o ∈ inSubgroup (pCore 2) X, k * o * k⁻¹ ∈ inSubgroup (pCore 2) X := by
    intro k hk o ho
    obtain ⟨o', ho', rfl⟩ := ho
    exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, by simp⟩
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key k hk x hx, fun h => ?_⟩
  have := key k⁻¹ (X.inv_mem hk) _ h
  have e : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x := by group
  rwa [e] at this

theorem pCoreIn_le (X : Subgroup G) : inSubgroup (pCore 2) X ≤ X := Subgroup.map_subtype_le _

theorem comm_mem_Z_of_pCoreIn (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    {X : Subgroup G} (hLX : LB M Q B ≤ X) (hXH : X ≤ H0 M Z) :
    ∀ f ∈ inSubgroup (pCore 2) X, ∀ b ∈ B, ⁅f, b⁆ ∈ Z := by
  have hLn : LB M Q B ≤ Subgroup.normalizer (inSubgroup (pCore 2) X : Set G) :=
    hLX.trans (le_normalizer_pCoreIn X)
  have hP : IsPGroup 2 ↥(inSubgroup (pCore 2) X ⊔ LB M Q B) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_pCoreIn X) (isPGroup_LB_of_ctx hc) hLn
  have hPH : inSubgroup (pCore 2) X ⊔ LB M Q B ≤ H0 M Z :=
    sup_le ((pCoreIn_le X).trans hXH) (hLX.trans hXH)
  exact fun f hf b hb =>
    comm_mem_Z_of_isPGroup h34 hc hw hn hno hgen hP hPH le_sup_right f
      (Subgroup.mem_sup_left hf) b hb

end HS9

end CFSG.RankThree.GF2n.Stroth80
