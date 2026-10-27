module

public import CFSG.RankThree.GF2n.Smith81.LinCoord
public import CFSG.RankThree.GF2n.Smith81.LinTLAbelian
public import CFSG.RankThree.GF2n.Smith81.LinTLFixed

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

private theorem LinSetup.facts_TL (hS : LinSetup M Q Z B n V₁ V₂) :
    Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ V₁ ⊓ V₂ = Z ∧
      Lgen M (LB M Q B) ≤ Subgroup.normalizer (V₁ : Set G) ∧
      Lgen M (LB M Q B) ≤ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨K, _, _, -, φ, -, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, -, hs₁, hs₂, -, -⟩ := hS
  obtain ⟨hN₁, -⟩ := hs₁
  obtain ⟨hN₂, -⟩ := hs₂
  exact ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hN₁, hN₂⟩

private theorem comm_mul_central (H : StrothHyp M Q Z) {x h c : G} (hx : x ∈ Q) (hh : h ∈ Q)
    (hc : c ∈ Z) : ⁅x, c * h⁆ = ⁅x, h⁆ := by
  have h1 : c * h = h * c := Z_central H hc hh
  have h2 : c * x⁻¹ = x⁻¹ * c := Z_central H hc (Q.inv_mem hx)
  simp only [commutatorElement_def]
  rw [h1]
  calc x * (h * c) * x⁻¹ * (h * c)⁻¹ = x * h * (c * x⁻¹) * (c⁻¹ * h⁻¹) := by group
    _ = x * h * (x⁻¹ * c) * (c⁻¹ * h⁻¹) := by rw [h2]
    _ = x * h * x⁻¹ * h⁻¹ := by group

theorem LinSetup.mem_sup_of_comm_V₂ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) (hB : B ≤ V₁) {x : G} (hx : x ∈ V₁)
    (hxc : ∀ h ∈ V₂ ⊓ Subgroup.centralizer (B : Set G), x * h = h * x) : x ∈ B ⊔ Z := by
  obtain ⟨-, hV₁Q, -, -, -, -, -⟩ := LinSetup.facts_TL hS
  refine hc.mem_sup_of_comm_centralizer (hV₁Q hx) fun y hy => ?_
  obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨a, ha, h, hh, rfl⟩ := LinSetup.exists_mul hc.hyp hS y hyQ
  have haC : a ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb => comm_eq_one_V₁ hc hS hn (hB hb) ha
  have hhC : h ∈ Subgroup.centralizer (B : Set G) := by
    have h1 : a⁻¹ * (a * h) ∈ Subgroup.centralizer (B : Set G) :=
      (Subgroup.centralizer (B : Set G)).mul_mem
        ((Subgroup.centralizer (B : Set G)).inv_mem haC) hyC
    rwa [inv_mul_cancel_left] at h1
  have hxa : x * a = a * x := comm_eq_one_V₁ hc hS hn hx ha
  have hxh : x * h = h * x := hxc h (Subgroup.mem_inf.mpr ⟨hh, hhC⟩)
  calc x * (a * h) = x * a * h := (mul_assoc x a h).symm
    _ = a * x * h := by rw [hxa]
    _ = a * (x * h) := mul_assoc a x h
    _ = a * (h * x) := by rw [hxh]
    _ = a * h * x := (mul_assoc a h x).symm

theorem LinSetup.comm_mem_sup_of_le_V₁ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) (hB : B ≤ V₁) {t : G} (ht : t ∈ LB M Q B) {v : G} (hv : v ∈ V₁) :
    ⁅v, t⁆ ∈ B ⊔ Z := by
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hnV₁, hnV₂⟩ := LinSetup.facts_TL hS
  have htL : t ∈ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B) ht
  have hvQ : v ∈ Q := hV₁Q hv
  have hw : ⁅v, t⁆ ∈ V₁ := by
    have htv : t * v * t⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hnV₁ htL) v).mp hv
    have e : ⁅v, t⁆ = v * (t * v * t⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V₁.mul_mem hv (V₁.inv_mem htv)
  obtain ⟨w, hwdef⟩ : ∃ w, ⁅v, t⁆ = w := ⟨_, rfl⟩
  rw [hwdef] at hw ⊢
  have hwQ : w ∈ Q := hV₁Q hw
  refine LinSetup.mem_sup_of_comm_V₂ hc hS hn hB hw fun h hh => ?_
  obtain ⟨hhV₂, hhC⟩ := Subgroup.mem_inf.mp hh
  have hhQ : h ∈ Q := hV₂Q hhV₂
  have hcD : ⁅t, h⁆ ∈ Q ⊓ QB B :=
    hc.comm_mem_inf_of_mem_LB ht (Subgroup.mem_inf.mpr ⟨hhQ, hhC⟩)
  have hcV₂ : ⁅t, h⁆ ∈ V₂ := by
    rw [commutatorElement_def]
    exact V₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnV₂ htL) h).mp hhV₂)
      (V₂.inv_mem hhV₂)
  have hBV₂ : (B ⊔ Z) ⊓ V₂ = Z := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ V₁ ⊓ V₂ :=
        Subgroup.mem_inf.mpr ⟨sup_le hB hZV₁ (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
      rw [hint] at hx'
      exact hx'
    · exact le_inf le_sup_right hZV₂
  have hEq : Q ⊓ QB B ⊓ V₂ = Z :=
    hc.inf_QB_inf_eq_of_sup_inf hZV₂ (le_trans (le_Lgen_self M (LB M Q B)) hnV₂) hBV₂
  have hcZ : ⁅t, h⁆ ∈ Z := by
    rw [← hEq]
    exact Subgroup.mem_inf.mpr ⟨hcD, hcV₂⟩
  obtain ⟨c, hcdef⟩ : ∃ c, ⁅t, h⁆ = c := ⟨_, rfl⟩
  rw [hcdef] at hcZ
  have hφh : t * h * t⁻¹ = c * h := by
    rw [← hcdef]
    simp only [commutatorElement_def]
    group
  have hφv : t * v * t⁻¹ = w⁻¹ * v := by
    rw [← hwdef]
    simp only [commutatorElement_def]
    group
  have hd : ⁅v, h⁆ ∈ Z := comm_mem_Z hc.hyp hvQ hhQ
  have e1 : ⁅v, h⁆ = ⁅t * v * t⁻¹, t * h * t⁻¹⁆ := by
    have e0 : t * ⁅v, h⁆ * t⁻¹ = ⁅v, h⁆ := hc.LB_centralizes_Z ht _ hd
    have e2 : t * ⁅v, h⁆ * t⁻¹ = ⁅t * v * t⁻¹, t * h * t⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    exact e0.symm.trans e2
  have hx : w⁻¹ * v ∈ Q := Q.mul_mem (Q.inv_mem hwQ) hvQ
  rw [hφv, hφh, comm_mul_central hc.hyp hx hhQ hcZ] at e1
  have hcw : w⁻¹ * ⁅v, h⁆ * w = ⁅v, h⁆ := by
    rw [← Z_central hc.hyp hd (Q.inv_mem hwQ)]
    group
  have hid : ⁅w⁻¹ * v, h⁆ = ⁅v, h⁆ * ⁅w⁻¹, h⁆ := by
    calc ⁅w⁻¹ * v, h⁆ = (w⁻¹ * ⁅v, h⁆ * w) * ⁅w⁻¹, h⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅v, h⁆ * ⁅w⁻¹, h⁆ := by rw [hcw]
  have hone : ⁅w⁻¹, h⁆ = 1 := by
    apply mul_left_cancel (a := ⁅v, h⁆)
    rw [mul_one, ← hid, ← e1]
  have hcomm : w⁻¹ * h = h * w⁻¹ := commutatorElement_eq_one_iff_mul_comm.mp hone
  calc w * h = w * (h * w⁻¹) * w := by group
    _ = w * (w⁻¹ * h) * w := by rw [hcomm]
    _ = h * w := by group

theorem LinSetup.transv_of_le_V₁ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) (hB : B ≤ V₁) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q) :
    ⁅V₁, Subgroup.zpowers t⁆ ⊔ Z = B ⊔ Z ∧ HasDimOn V₁ Z 1 t ∧ HasDimOn V₂ Z 1 t := by
  obtain ⟨-, -, -, -, -, -, -⟩ := LinSetup.facts_TL hS
  have htL : t ∈ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B) ht
  have htt : t * t ∈ Q := by
    have h2 := hc.sq_mem_Q_of_mem_LB ht
    rwa [pow_two] at h2
  obtain ⟨k, hk1, -, hkV₁, hkV₂⟩ :=
    linRankBoundStatement_holds G M Q Z B n V₁ V₂ hc hS t htL htQ htt
  have hcardBZ : Nat.card ↥(B ⊔ Z) = Nat.card ↥Z ^ 2 := by
    have hBn : B ≤ Subgroup.normalizer (Z : Set G) :=
      le_trans hc.le (Q_le_normalizer_of_Z_le hc.hyp le_rfl hc.Z_le_Q)
    have hBcard : Nat.card ↥B = Nat.card ↥Z := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [hg, card_conjSubgroup]
    have h := card_sup_mul_card_inf_of_normalizer hBn
    rw [hc.inf_eq_bot, Subgroup.card_bot, mul_one, hBcard, sup_comm] at h
    rw [h, sq]
  have hle : ⁅V₁, Subgroup.zpowers t⁆ ⊔ Z ≤ B ⊔ Z := by
    refine sup_le (Subgroup.commutator_le.mpr fun v hv s hs => ?_) le_sup_right
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact LinSetup.comm_mem_sup_of_le_V₁ hc hS hn hB ((LB M Q B).zpow_mem ht j) hv
  have hkcard : Nat.card ↥(⁅V₁, Subgroup.zpowers t⁆ ⊔ Z) = Nat.card ↥Z ^ (k + 1) := hkV₁
  have hq1 : 1 < Nat.card ↥Z := by
    have := hc.hyp.q4
    omega
  have hpow : Nat.card ↥Z ^ (k + 1) ≤ Nat.card ↥Z ^ 2 := by
    rw [← hkcard, ← hcardBZ]
    exact Subgroup.card_le_of_le hle
  have hk : k = 1 := by
    have h3 := (Nat.pow_le_pow_iff_right hq1).mp hpow
    omega
  subst hk
  have hkcard2 : Nat.card ↥(⁅V₁, Subgroup.zpowers t⁆ ⊔ Z) = Nat.card ↥Z ^ 2 := hkcard
  have hEq : ⁅V₁, Subgroup.zpowers t⁆ ⊔ Z = B ⊔ Z :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcardBZ, hkcard2]))
  exact ⟨hEq, hkV₁, hkV₂⟩

end CFSG.RankThree.GF2n.Smith81
