module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aIsolationFix
import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aXtau

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.mem_B1_of_tau_inv (h : FF81Hyp b L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L)
    (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    {y : G} (hyB : y ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hyinv : τ * y * τ⁻¹ = y⁻¹) :
    y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := by
  classical
  set B₁ : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁
  have hB₁L : B₁ ≤ L :=
    (Subgroup.closure_le L).mpr (by
      rintro x (rfl | rfl | rfl)
      exacts [hb₁, hb₂, hb₃])
  have hcommB₁ : ∀ x ∈ B₁, ∀ z ∈ B₁, x * z = z * x :=
    fun x hx z hz =>
      congrArg Subtype.val (hE.1.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hinv' : ∀ x ∈ ({b₁, b₂, b₃} : Set G), τ * x * τ⁻¹ = x⁻¹ := by
    rintro x (rfl | rfl | rfl)
    exacts [hinv.1, hinv.2.1, hinv.2.2]
  have hinvB₁ : ∀ z ∈ B₁, τ * z * τ⁻¹ = z⁻¹ :=
    fun z hz => conj_eq_inv_of_closure hcommB₁ hinv' hz
  have hB_eq : Subgroup.closure ({b, b₁, b₂, b₃} : Set G) = Subgroup.zpowers b ⊔ B₁ := by
    rw [hB₁]
    exact closure_four_eq b b₁ b₂ b₃
  have hy : y ∈ Subgroup.zpowers b ⊔ B₁ := by
    rw [← hB_eq]
    exact hyB
  have hcomm_sup : ∀ a ∈ Subgroup.zpowers b, ∀ c ∈ B₁, a * c = c * a := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbc : Commute b c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h.hLC (hB₁L hc))).symm
    exact (hbc.zpow_left k).eq
  obtain ⟨a, ha, c, hc, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_sup hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hτb : Commute τ b := by
    show τ * b = b * τ
    calc τ * b = (τ * b * τ⁻¹) * τ := by group
      _ = b * τ := by rw [hb]
  have hτa : τ * (b ^ k) * τ⁻¹ = b ^ k := by
    rw [(hτb.zpow_right k).eq]
    group
  have hτc : τ * c * τ⁻¹ = c⁻¹ := hinvB₁ c hc
  have hbc : Commute (b ^ k) c := by
    have hcb : Commute b c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h.hLC (hB₁L hc))).symm
    exact hcb.zpow_left k
  have hkey : b ^ k * c⁻¹ = c⁻¹ * (b ^ k)⁻¹ := by
    calc b ^ k * c⁻¹ = (τ * (b ^ k) * τ⁻¹) * (τ * c * τ⁻¹) := by rw [hτa, hτc]
      _ = τ * (b ^ k * c) * τ⁻¹ := by group
      _ = (b ^ k * c)⁻¹ := hyinv
      _ = c⁻¹ * (b ^ k)⁻¹ := by rw [mul_inv_rev]
  have hcancel : b ^ k = (b ^ k)⁻¹ := by
    have hcomm_inv : Commute (b ^ k) c⁻¹ := hbc.inv_right
    have hkey' : b ^ k * c⁻¹ = (b ^ k)⁻¹ * c⁻¹ :=
      hkey.trans (hcomm_inv.inv_left.eq).symm
    exact mul_right_cancel hkey'
  have hsq : b ^ k * b ^ k = 1 := by
    nth_rewrite 2 [hcancel]
    exact mul_inv_cancel (b ^ k)
  have h2k : b ^ (k + k) = 1 := by
    rw [zpow_add]
    exact hsq
  have hdvd2' : (orderOf b : ℤ) ∣ 2 * k := by
    rw [orderOf_dvd_iff_zpow_eq_one]
    rwa [show (2 : ℤ) * k = k + k by ring]
  have hdvd2 : (3 : ℤ) ∣ 2 * k := by
    simpa [h.ord] using hdvd2'
  have hdvd : (3 : ℤ) ∣ k :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hdvd2 (by norm_num)
  have hbk : b ^ k = 1 := by
    have h' : (orderOf b : ℤ) ∣ k := by simpa [h.ord] using hdvd
    exact orderOf_dvd_iff_zpow_eq_one.mp h'
  rw [hbk, one_mul]
  exact hc

theorem FF81Hyp.no_inverting_conj (h : FF81Hyp b L)
    (hnoL : ∀ g : G, g * b * g⁻¹ ∉ L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hτN : τ ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    {σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hσX : σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) :
    (σ * FF81X.tau hτN * σ⁻¹) ⟨b, hbB⟩ ≠ (⟨b, hbB⟩)⁻¹ := by
  intro hconj
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let bB : ↥B := ⟨b, hbB⟩
  let τN : ↥(Nor B) := ⟨τ, hτN⟩
  let τX : MulAut ↥B := FF81X.tau hτN
  obtain ⟨n, hn⟩ := mem_FF81X_iff.mp hσX
  have hhom : Subgroup.normalizerMonoidHom (H := B) (n * τN * n⁻¹) =
      σ * τX * σ⁻¹ := by
    rw [← hn]
    change Subgroup.normalizerMonoidHom (H := B) (n * τN * n⁻¹) =
      Subgroup.normalizerMonoidHom (H := B) n *
        Subgroup.normalizerMonoidHom (H := B) τN *
        (Subgroup.normalizerMonoidHom (H := B) n)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul]
  have hcoe : (((σ * τX * σ⁻¹) bB : ↥B) : G) =
      (n : G) * τ * (n : G)⁻¹ * b * ((n : G) * τ * (n : G)⁻¹)⁻¹ := by
    rw [← hhom]
    change (((Subgroup.normalizerMonoidHom (H := B) (n * τN * n⁻¹)) bB : ↥B) : G) =
      (n : G) * τ * (n : G)⁻¹ * b * ((n : G) * τ * (n : G)⁻¹)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [τN, bB]
  have hG : (n : G) * τ * (n : G)⁻¹ * b * ((n : G) * τ * (n : G)⁻¹)⁻¹ = b⁻¹ := by
    rw [← hcoe]
    have hval := congrArg Subtype.val hconj
    simpa [bB] using hval
  let y : G := (n : G)⁻¹ * b * (n : G)
  have hyB : y ∈ B := by
    have hmem : (n : G)⁻¹ * b * (n : G) ∈ B :=
      (Subgroup.mem_normalizer_iff''.mp n.2 b).mp hbB
    simpa [y] using hmem
  have hyinv : τ * y * τ⁻¹ = y⁻¹ := by
    have hconj_n : (n : G)⁻¹ *
        ((n : G) * τ * (n : G)⁻¹ * b * ((n : G) * τ * (n : G)⁻¹)⁻¹) * (n : G) =
        (n : G)⁻¹ * b⁻¹ * (n : G) :=
      congrArg (fun z : G => (n : G)⁻¹ * z * (n : G)) hG
    calc τ * y * τ⁻¹ = (n : G)⁻¹ *
        ((n : G) * τ * (n : G)⁻¹ * b * ((n : G) * τ * (n : G)⁻¹)⁻¹) * (n : G) := by
          simp [y]
          group
      _ = (n : G)⁻¹ * b⁻¹ * (n : G) := hconj_n
      _ = y⁻¹ := by
          simp [y]
          group
  have hyB₁ : y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) :=
    FF81Hyp.mem_B1_of_tau_inv h hτL hb₁ hb₂ hb₃ hE hb hinv hbB hb₁B hb₂B hb₃B
      (by simpa [B] using hyB) (by simpa [y] using hyinv)
  have hB₁L : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L :=
    (Subgroup.closure_le L).mpr (by
      rintro x (rfl | rfl | rfl)
      exacts [hb₁, hb₂, hb₃])
  exact hnoL (n : G)⁻¹ (by simpa [y] using hB₁L hyB₁)

theorem FF81Hyp.tau_isolated_of_no_conj_into_L (h : FF81Hyp b L)
    (hnoL : ∀ g : G, g * b * g⁻¹ ∉ L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hτN : τ ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    {σ : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hσX : σ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hcomm : (σ * FF81X.tau hτN * σ⁻¹) * FF81X.tau hτN =
      FF81X.tau hτN * (σ * FF81X.tau hτN * σ⁻¹)) :
    σ * FF81X.tau hτN * σ⁻¹ = FF81X.tau hτN := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  set B₁ : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁
  let bB : ↥B := ⟨b, hbB⟩
  let τX : MulAut ↥B := FF81X.tau hτN
  let τ' : MulAut ↥B := σ * τX * σ⁻¹
  change τ' = τX
  have hE4 : IsElemAb 3 4 B := by
    have hh := FF81Hyp.isElemAb_B4 h hb₁ hb₂ hb₃ hE hbB
    simpa [B] using hh
  have hτXcoe : ∀ x : ↥B, (τX x : G) = τ * (x : G) * τ⁻¹ := by
    intro x
    change ((Subgroup.normalizerMonoidHom (H := B) ⟨τ, hτN⟩) x : G) = τ * (x : G) * τ⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hτXb : τX bB = bB := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa [bB] using hb
  have hτX₁ : τX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹ := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa using hinv.1
  have hτX₂ : τX ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹ := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa using hinv.2.1
  have hτX₃ : τX ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹ := by
    refine Subtype.ext ?_
    rw [hτXcoe]
    simpa using hinv.2.2
  have hB₁L : B₁ ≤ L := by
    rw [hB₁]
    exact (Subgroup.closure_le L).mpr (by
      rintro x (rfl | rfl | rfl)
      exacts [hb₁, hb₂, hb₃])
  have hB_eq : Subgroup.closure ({b, b₁, b₂, b₃} : Set G) = Subgroup.zpowers b ⊔ B₁ := by
    rw [hB₁]
    exact closure_four_eq b b₁ b₂ b₃
  have hcomm_sup : ∀ a ∈ Subgroup.zpowers b, ∀ c ∈ B₁, a * c = c * a := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbc : Commute b c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h.hLC (hB₁L hc))).symm
    exact (hbc.zpow_left k).eq
  have hdecomp : ∀ x : ↥B, ∃ k : ℤ, ∃ c ∈ B₁, (x : G) = b ^ k * c := by
    intro x
    have hx : (x : G) ∈ Subgroup.zpowers b ⊔ B₁ := by
      rw [← hB_eq]
      exact x.2
    obtain ⟨a, ha, c, hc, hxac⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm_sup hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨k, c, hc, hxac.symm⟩
  have hτb : Commute τ b := by
    show τ * b = b * τ
    calc τ * b = (τ * b * τ⁻¹) * τ := by group
      _ = b * τ := by rw [hb]
  have hτa : ∀ k : ℤ, τ * (b ^ k) * τ⁻¹ = b ^ k := by
    intro k
    rw [(hτb.zpow_right k).eq]
    group
  have hcommB₁ : ∀ x ∈ B₁, ∀ z ∈ B₁, x * z = z * x :=
    fun x hx z hz =>
      congrArg Subtype.val (hE.1.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hinv' : ∀ x ∈ ({b₁, b₂, b₃} : Set G), τ * x * τ⁻¹ = x⁻¹ := by
    rintro x (rfl | rfl | rfl)
    exacts [hinv.1, hinv.2.1, hinv.2.2]
  have hinvB₁ : ∀ c ∈ B₁, τ * c * τ⁻¹ = c⁻¹ :=
    fun c hc => conj_eq_inv_of_closure hcommB₁ hinv' hc
  have hτX_apply_decomp : ∀ (x : ↥B) (k : ℤ) (c : G), c ∈ B₁ →
      (x : G) = b ^ k * c → (τX x : G) = b ^ k * c⁻¹ := by
    intro x k c hc hx
    rw [hτXcoe x, hx]
    calc τ * (b ^ k * c) * τ⁻¹ = (τ * (b ^ k) * τ⁻¹) * (τ * c * τ⁻¹) := by group
      _ = b ^ k * c⁻¹ := by rw [hτa k, hinvB₁ c hc]
  have hτX2_apply : ∀ x : ↥B, (τX * τX) x = x := by
    intro x
    obtain ⟨k, c, hc, hx⟩ := hdecomp x
    have hx1 : (τX x : G) = b ^ k * c⁻¹ := hτX_apply_decomp x k c hc hx
    have hx2 : (τX (τX x) : G) = b ^ k * (c⁻¹)⁻¹ :=
      hτX_apply_decomp (τX x) k (c⁻¹) (B₁.inv_mem hc) hx1
    apply Subtype.ext
    change (τX (τX x) : G) = (x : G)
    rw [hx2, hx, inv_inv]
  have hτX2 : τX * τX = 1 := by
    apply MulEquiv.ext
    intro x
    simpa using hτX2_apply x
  have hτXfix : ∀ x : ↥B, τX x = x ↔ x ∈ Subgroup.zpowers bB := by
    intro x
    constructor
    · intro hxfix
      obtain ⟨k, c, hc, hx⟩ := hdecomp x
      have hτx : (τX x : G) = b ^ k * c⁻¹ := hτX_apply_decomp x k c hc hx
      have hval : (τX x : G) = (x : G) := congrArg Subtype.val hxfix
      have hfixG : b ^ k * c⁻¹ = b ^ k * c := by
        rw [← hτx, hval, hx]
      have hc_eq : c = c⁻¹ := (mul_left_cancel hfixG).symm
      have hc2 : c ^ 2 = 1 := by
        rw [pow_two]
        exact eq_inv_iff_mul_eq_one.mp hc_eq
      have hc3 : c ^ 3 = 1 := by
        have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.1.exponent_dvd_p ⟨c, hc⟩
        simpa using congrArg Subtype.val h
      have hc1 : c = 1 := by
        calc c = c ^ 3 * (c ^ 2)⁻¹ := by
              rw [show c ^ 3 = c * c ^ 2 by rw [pow_succ']]
              group
          _ = 1 := by rw [hc3, hc2, inv_one, mul_one]
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow]
      change b ^ k = (x : G)
      rw [hx, hc1, mul_one]
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hk]
      calc τX (bB ^ k) = (τX bB) ^ k := map_zpow τX bB k
        _ = bB ^ k := by rw [hτXb]
  have hcomm' : τ' * τX = τX * τ' := by
    simpa [τ', τX] using hcomm
  have hτ'b_fixed : τX (τ' bB) = τ' bB := by
    have h := congrArg (fun f : MulAut ↥B => f bB) hcomm'
    simpa [MulAut.mul_apply, hτXb] using h.symm
  have hτ'b_mem : τ' bB ∈ Subgroup.zpowers bB := (hτXfix (τ' bB)).mp hτ'b_fixed
  have horderB : orderOf bB = 3 := by
    rw [← Subgroup.orderOf_coe bB]
    simpa [bB] using h.ord
  have hbB_ne : bB ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at horderB
    norm_num at horderB
  have hτ'b_ne : τ' bB ≠ 1 := by
    intro h1
    apply hbB_ne
    have h := congrArg (fun z => τ'⁻¹ z) h1
    simpa using h
  rcases eq_or_eq_inv_of_mem_zpowers (b := bB) horderB hτ'b_mem hτ'b_ne with hfix | hinv'
  · exact tau_eq_of_conj_commute_fix_b (B := B) hbB hb₁B hb₂B hb₃B rfl hE4 h.ord
      (FF81X.tau_mem hτN) hτX2 hτXb hτX₁ hτX₂ hτX₃ hτXfix hσX hcomm' hfix
  · exact absurd hinv'
      (FF81Hyp.no_inverting_conj h hnoL hτL hb₁ hb₂ hb₃ hE hb hinv hbB hb₁B hb₂B hb₃B
        hτN hσX)

end CFSG.RankThree.PartTwo.Sec21.FF81
