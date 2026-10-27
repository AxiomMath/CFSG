module

public import CFSG.Timmesfeld.Bridge.RootStructR2OneBasic
public import CFSG.Timmesfeld.Bridge.RootStructWTIModStep
public import CFSG.Timmesfeld.Bridge.RootSetsSyl

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace RootOne

variable {G : Type} [Group G] {D : Set G}

theorem false_of_lineN₀_eq {a d x y : G} (C : LineConf D a d x y) {K : Type*} [Field K]
    [Finite K] [CharP K 2] [PerfectRing K 2] (hK : Nat.card K = Nat.card (rootGroup D a))
    (hK2 : 2 < Nat.card K)
    (φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφx : ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      upperUnipotent K)
    (hφy : ((rootGroup D y).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      lowerUnipotent K)
    (hXN : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ n ∈ lineN D a d, g * n * g⁻¹ ∈ lineN D a d)
    {θ₁ : (Fin 2 → K) → G} (hθ₁ : Higman.IsNaturalQuotient φ (lineN D a d) (lineN₀ D a d) θ₁)
    (hθd : ∀ s : K, θ₁ ![0, s] ∈ nCore D d ⊓ Subgroup.centralizer {a})
    (hN₀ : lineN₀ D a d = rootGroup D a ⊔ rootGroup D d) : False := by
  have hD := C.root
  obtain ⟨θ₀, hθ₀, hrange, -, -⟩ := C.exists_natural hK φ hφx hφy
  have hext : Higman.IsNaturalExtension φ (lineN D a d) (lineN₀ D a d) θ₀ θ₁ :=
    { le := lineN₀_le_Na.trans le_sup_left
      normal := fun n hn t ht => by
        rw [hN₀] at ht ⊢
        rw [(C.commute_of_mem_lineN hn ht).eq, mul_inv_cancel_right]
        exact ht
      conj_mem := hXN
      natural := hθ₀
      range := fun t => by rw [hN₀]; exact hrange t
      quotient := hθ₁ }
  set n := θ₁ ![0, 1] with hn
  have hnN : n ∈ lineN D a d := hθ₁.mem _
  have hnNa : n ∉ nCore D a ⊓ Subgroup.centralizer {d} := by
    intro h
    have h0 := hθ₁.eq_zero_of_mem _ (mem_lineN₀_of_mem h (hθd 1))
    have := congrFun h0 1
    simp at this
  have hxX : x ∈ rootGroup D x ⊔ rootGroup D y :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D x (mem_rootSet_self C.hx))
  have hw : x * n * x⁻¹ * n⁻¹ ∈ lineN D a d :=
    Subgroup.mul_mem _ (hXN x hxX n hnN) (Subgroup.inv_mem _ hnN)
  have hw2 := hext.mul_self_eq_one hK2 hw
  have hx'D : n * x * n⁻¹ ∈ D := conj_mem_of_isClass C.isClass n C.hx
  have hcomm : Commute x (n * x * n⁻¹) := by
    rw [commute_iff_mul_sq_eq_one (hD.mul_self_eq_one C.hx) (hD.mul_self_eq_one hx'D)]
    rw [show x * (n * x * n⁻¹) = x * n * x⁻¹ * n⁻¹ by rw [hD.inv_eq C.hx]; group, sq]
    exact hw2
  exact hnNa (C.mem_Na_of_commute hnN hcomm)

theorem false_of_eq_q {q : ℕ} (C : ThinGateCounter G D) (K : ThinGateCount G D q 1 q) : False := by
  classical
  obtain ⟨a, d, x, y, L⟩ := exists_lineConf C
  have := L.finite
  have hD := L.root
  have hq : Nat.card (rootGroup D a) = q := K.card_rootGroup a L.ha
  have hq4 : 4 ≤ q := hq ▸ four_le_card_rootGroup L.isClass hD L.setting.closure C.nontrivial L.ha
  obtain ⟨-, e, he, φ, hφx, hφy, hXN, -, -, -, -, ⟨m, Nf, θ, hNf, hθ, hsup, hcardN, -, hcardNd⟩,
    -⟩ := rootLinesModuleStep G D L.setting a L.ha d L.hd L.had L.hadD L.hdT x L.hx L.hax L.haxD
      L.hxT y L.hy L.hdy L.hdyD L.hyT
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    omega
  have hKq : Nat.card (GaloisField 2 e) = Nat.card (rootGroup D a) := by
    rw [GaloisField.card 2 e he0, he]
  have hT := L.mem_rootLines_a
  have hsub : gatedPoints D a (rootGroup D a ⊔ rootGroup D d) ⊆ oneOmega D a := fun B hB => hB.1
  have hΩ : (oneOmega D a \ gatedPoints D a (rootGroup D a ⊔ rootGroup D d)).ncard = q ^ 4 := by
    rw [Set.ncard_sdiff hsub, K.ncard_gatedPoints a L.ha _ hT]
    have h1 := K.ncard_oneOmega a L.ha
    have h2 : (oneOmega D a).ncard = (q + 1) * q ^ 4 := by
      have h3 : (oneOmega D a).ncard * q = (q + 1) * q ^ 4 * q := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) h3
    rw [h2, show (q + 1) * q ^ 4 = q ^ (2 * 1 + 3) + q ^ 4 by ring, Nat.add_sub_cancel_left]
  have hdvd := card_dvd_ncard_of_centralizes C L.ha L.hd L.had L.hadD L.hdT (lineN D a d)
    (fun g hg t ht => L.commute_of_mem_lineN hg ht)
  rw [hΩ, hcardN, hq] at hdvd
  have hTN₀ := Subgroup.card_dvd_of_le L.T_le_lineN₀
  rw [L.card_T, hq] at hTN₀
  have hq1 : 1 < q := by omega
  have hm1 : m ≤ 1 := by
    have h1 : q ^ (2 + 2 * m) ∣ q ^ 4 := by
      rw [pow_add]
      exact (Nat.mul_dvd_mul_right hTN₀ _).trans hdvd
    have := (Nat.pow_dvd_pow_iff_le_right hq1).1 h1
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hcardNd
    have hNd : lineN₀ D a d = nCore D d ⊓ Subgroup.centralizer {a} :=
      Subgroup.eq_of_le_of_card_ge lineN₀_le_Nd hcardNd.le
    have h3 : 3 ≤ (rootLines D a).ncard := by rw [K.ncard_rootLines a L.ha, pow_one]; omega
    obtain ⟨k, hk, hkM⟩ := L.exists_mem_Nd_not_mem h3
    rw [← hNd] at hk
    exact hkM (Subgroup.mem_inf.1 hk).1
  obtain rfl : m = 1 := by omega
  have hN₀ : lineN₀ D a d = rootGroup D a ⊔ rootGroup D d := by
    refine (Subgroup.eq_of_le_of_card_ge L.T_le_lineN₀ ?_).symm
    rw [L.card_T, hq]
    have h1 : Nat.card (lineN₀ D a d) ∣ q ^ 2 := by
      have h2 : Nat.card (lineN₀ D a d) * q ^ 2 ∣ q ^ 2 * q ^ 2 := by
        rw [← pow_add]
        exact hdvd
      exact Nat.dvd_of_mul_dvd_mul_right (by positivity) h2
    exact Nat.le_of_dvd (by positivity) h1
  have hNf0 : Nf 0 = lineN D a d := by
    rw [← hsup, iSup_unique, show (default : Fin 1) = 0 from rfl]
    exact (sup_eq_right.2 (hNf 0).1).symm
  have hθ₁ := (hNf 0).2
  rw [hNf0] at hθ₁
  exact false_of_lineN₀_eq L hKq (by rw [hKq, hq]; omega) φ hφx hφy hXN hθ₁
    (fun s => (hθ 0 s).2) hN₀

end RootOne

end CFSG.Timmesfeld.Bridge
