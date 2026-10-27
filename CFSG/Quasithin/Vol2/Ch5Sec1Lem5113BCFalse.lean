module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BCSmall

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open Equiv Equiv.Perm
open CFSG.QuasithinUnique.Setup.X3E (Vec lin wmap wapp toVec toVec_wapp exists_toVec toVec_injOn
  toVec_zero)
open CFSG.Quasithin.B45Alt7 (gen7 eval7 indBlk)

namespace BCFalse

theorem a_fix_check : ∀ j < 2, ∀ x < 16,
    wapp 4 (indBlk true j) [false] x < 16 ∧ (wapp 4 (indBlk true j) [false] x = x → x = 0) := by
  decide +kernel

theorem eval7_a : ∀ i : Fin 7, ((eval7 [false] : alternatingGroup (Fin 7)) : Perm (Fin 7)) i =
    (swap 0 2 * swap 0 1 : Perm (Fin 7)) i := by
  decide +kernel

theorem eq_zero_of_wmap_a {j : ℕ} (hj : j < 2) {s : Vec 4}
    (h : wmap (fun b => lin 4 (indBlk true j b)) [false] s = s) : s = 0 := by
  obtain ⟨x, hx, rfl⟩ := exists_toVec s
  have hx' : x < 16 := by simpa using hx
  obtain ⟨hlt, hfix⟩ := a_fix_check j hj x hx'
  rw [← toVec_wapp] at h
  have h2 := toVec_injOn (by simpa using hlt) hx h
  rw [hfix h2, toVec_zero]

variable {G : Type} [Group G]

omit [Group G] in
theorem isThreeCycle_of_pow_three {σ : Perm (Fin 7)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (hs : σ.support.card ≤ 4) : σ.IsThreeCycle := by
  have hord : orderOf σ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (by rw [hord]; exact Nat.prime_three)
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hk, hord, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk0 : k = 0 := by omega
  rw [hk0] at hsum
  exact card_support_eq_three_iff.mp (by omega)

theorem conjAut_eq_of_eq {Y U : Subgroup G} (e : O2Q Y ≃* alternatingGroup (Fin 7))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hO : pCoreOf 2 Y ≤ Subgroup.centralizer (U : Set G)) {y₁ y₂ : ↥Y}
    (h12 : e (QuotientGroup.mk y₁) = e (QuotientGroup.mk y₂)) :
    A7ZK.conjAut hYU y₁ = A7ZK.conjAut hYU y₂ := by
  have h1 : (QuotientGroup.mk y₁ : O2Q Y) = QuotientGroup.mk y₂ := e.injective h12
  rw [QuotientGroup.eq] at h1
  have h2 : ((y₁⁻¹ * y₂ : ↥Y) : G) ∈ Subgroup.centralizer (U : Set G) :=
    hO ((mem_pCore_iff_mem_pCoreOf Y _).mp h1)
  have h3 : A7ZK.conjAut hYU (y₁⁻¹ * y₂) = 1 := by
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [A7ZK.coe_conjAut, MulAut.one_apply, ← Subgroup.mem_centralizer_iff.mp h2 v v.2,
      mul_inv_cancel_right]
  calc A7ZK.conjAut hYU y₁ = A7ZK.conjAut hYU y₁ * A7ZK.conjAut hYU (y₁⁻¹ * y₂) := by
        rw [h3, mul_one]
    _ = A7ZK.conjAut hYU y₂ := by rw [← map_mul, mul_inv_cancel_left]

theorem eq_one_of_isThreeCycle {Y U : Subgroup G} (e : O2Q Y ≃* alternatingGroup (Fin 7))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hO : pCoreOf 2 Y ≤ Subgroup.centralizer (U : Set G)) {j : ℕ} (hj : j < 2) {Ψ : Vec 4 ≃ ↥U}
    (hΨ0 : Ψ 0 = 1)
    (hΨ : ∀ (w : List Bool) (y : ↥Y), e (QuotientGroup.mk y) = eval7 w → ∀ s : Vec 4,
      Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s) = A7ZK.conjAut hYU y (Ψ s))
    {y : ↥Y}
    (hy : ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) : Perm (Fin 7)).IsThreeCycle)
    {u : ↥U} (hu : A7ZK.conjAut hYU y u = u) : u = 1 := by
  have ha : ((eval7 [false] : alternatingGroup (Fin 7)) : Perm (Fin 7)).IsThreeCycle := by
    rw [show ((eval7 [false] : alternatingGroup (Fin 7)) : Perm (Fin 7)) = swap 0 2 * swap 0 1
      from Equiv.ext eval7_a]
    exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  obtain ⟨g, hg⟩ := isConj_iff.mp (alternatingGroup.isThreeCycle_isConj (by simp) ha hy)
  obtain ⟨g', hg'⟩ : ∃ g' : ↥Y, e (QuotientGroup.mk g') = g := by
    obtain ⟨q, hq⟩ := e.surjective g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨g', hq⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ↥Y, e (QuotientGroup.mk a') = eval7 [false] := by
    obtain ⟨q, hq⟩ := e.surjective (eval7 [false])
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a', hq⟩
  have hy' : A7ZK.conjAut hYU y = A7ZK.conjAut hYU (g' * a' * g'⁻¹) := by
    refine conjAut_eq_of_eq e hYU hO ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv,
      hg', ha', hg]
  have hu1 : ((y : G) * u * (y : G)⁻¹) = u := congrArg Subtype.val hu
  have hu2 : ((g' * a' * g'⁻¹ : ↥Y) : G) * u * ((g' * a' * g'⁻¹ : ↥Y) : G)⁻¹ = u := by
    have := congrArg Subtype.val (congrArg (fun f : MulAut ↥U => f u) hy')
    simp only [A7ZK.coe_conjAut] at this
    rw [← this]
    exact hu1
  set u' : ↥U := A7ZK.conjAut hYU g'⁻¹ u with hu'def
  have hu' : A7ZK.conjAut hYU a' u' = u' := by
    apply Subtype.ext
    rw [hu'def, A7ZK.coe_conjAut, A7ZK.coe_conjAut]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hu2 ⊢
    calc (a' : G) * ((g' : G)⁻¹ * u * (g' : G)⁻¹⁻¹) * (a' : G)⁻¹ =
        (g' : G)⁻¹ * ((g' : G) * a' * (g' : G)⁻¹ * u * ((g' : G) * a' * (g' : G)⁻¹)⁻¹) *
          (g' : G) := by group
      _ = (g' : G)⁻¹ * u * (g' : G) := by rw [hu2]
      _ = (g' : G)⁻¹ * u * (g' : G)⁻¹⁻¹ := by group
  have hu'1 : u' = 1 := by
    have h1 := hΨ [false] a' ha' (Ψ.symm u')
    rw [Equiv.apply_symm_apply, hu'] at h1
    have h2 : wmap (fun b => lin 4 (indBlk true j b)) [false] (Ψ.symm u') = Ψ.symm u' :=
      Ψ.injective (by rw [h1, Equiv.apply_symm_apply])
    rw [← Equiv.apply_symm_apply Ψ u', eq_zero_of_wmap_a hj h2, hΨ0]
  have h3 : ((u' : ↥U) : G) = (g' : G)⁻¹ * u * (g' : G) := by
    rw [hu'def, A7ZK.coe_conjAut]
    simp
  rw [hu'1, Subgroup.coe_one] at h3
  apply Subtype.ext
  rw [Subgroup.coe_one]
  calc (u : G) = (g' : G) * ((g' : G)⁻¹ * u * (g' : G)) * (g' : G)⁻¹ := by group
    _ = 1 := by rw [← h3]; group

omit [Group G] in
theorem eq_of_fixedPointFree {U : Type*} [Group U] (hcomm : ∀ x y : U, x * y = y * x)
    (hU2 : ∀ u : U, u * u = 1) {a b : MulAut U} (hab : a * b = b * a) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha : ∀ u, a u = u → u = 1) (hb : ∀ u, b u = u → u = 1)
    (hc : ∀ u, (a * b) u = u → u = 1) : a = b := by
  have hinv : ∀ v : U, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hU2 v)
  have key : ∀ x : MulAut U, x ^ 3 = 1 → (∀ u, x u = u → u = 1) → ∀ u, x (x u) = u * x u := by
    intro x hx3 hx u
    have h3 : x (x (x u)) = u := by
      have := congrArg (fun f : MulAut U => f u) hx3
      simpa [pow_succ, MulAut.mul_apply] using this
    have hfix : x (u * x u * x (x u)) = u * x u * x (x u) := by
      rw [map_mul, map_mul, h3, hcomm (x u * x (x u)) u]
      simp only [mul_assoc]
    have h1 := hx _ hfix
    calc x (x u) = (u * x u)⁻¹ := eq_inv_of_mul_eq_one_right h1
      _ = (x u)⁻¹ * u⁻¹ := mul_inv_rev _ _
      _ = x u * u := by rw [hinv, hinv]
      _ = u * x u := hcomm _ _
  have hab3 : (a * b) ^ 3 = 1 := by
    rw [(show Commute a b from hab).mul_pow, ha3, hb3, one_mul]
  refine MulEquiv.ext fun u => ?_
  have h1 := key (a * b) hab3 hc u
  have hba : ∀ w, b (a w) = a (b w) := fun w => by
    have := congrArg (fun f : MulAut U => f w) hab
    simpa [MulAut.mul_apply] using this.symm
  simp only [MulAut.mul_apply] at h1
  rw [hba (b u), key b hb3 hb u, map_mul, map_mul, key a ha3 ha u, key a ha3 ha (b u)] at h1
  have h2 : a u * b u = 1 := by
    have h3 : u * (a u * b u) * a (b u) = u * 1 * a (b u) := by
      rw [mul_one, ← h1]
      group
    exact mul_left_cancel (mul_right_cancel h3)
  calc a u = (b u)⁻¹ := eq_inv_of_mul_eq_one_left h2
    _ = b u := hinv _

end BCFalse

variable {G : Type} [Group G] [Finite G]

namespace Hyp5_0_1

theorem false_of_card_le {T M L D K Kh W D₃ V' : Subgroup G} {n : ℕ} (h : Hyp5_0_1 G T M L n)
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hV' : IsCh5Module T L V') (hnat : IsNatQuotCh5 L V' n)
    {e : O2Q Kh ≃* alternatingGroup (Fin 7)} (pk : A7Pack T K Kh W e)
    (hOU : pCoreOf 2 Kh = ⁅W, Kh⁆) (hO16 : Nat.card ↥(pCoreOf 2 Kh) = 2 ^ 4)
    (hT : Nat.card T ≤ 2 ^ 7) (hD₃ : D₃ ≤ D ⊓ Kh) (h3 : Nat.card D₃ = 3) {d₀ : ↥Kh}
    (hd₀ : (d₀ : G) ∈ D₃)
    (hstab : ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) →
      ((e (QuotientGroup.mk d₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 0 ∨
        ((e (QuotientGroup.mk d₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 5 ∨
        ((e (QuotientGroup.mk d₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 6)
    (hd₀0 : ((e (QuotientGroup.mk d₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 0 ≠ 0) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTK : Nat.card ↥(T ⊓ Kh) = 128 := by rw [pk.card_inf_eq_eight_mul, hO16]; norm_num
  have hT' : Nat.card T ≤ 128 := by simpa using hT
  have hTKh : T ≤ Kh := by
    have h1 : T ⊓ Kh = T := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact inf_eq_left.mp h1
  have hU16 : Nat.card ↥⁅W, Kh⁆ = 16 := by
    rw [← hOU, hO16]
    norm_num
  set U := ⁅W, Kh⁆ with hU
  set φ : ↥Kh →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh))) with hφ
  have hφe : ∀ y : ↥Kh, φ y = ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) := fun _ => rfl
  have hφU : ∀ y : ↥Kh, φ y = 1 ↔ (y : G) ∈ U := by
    intro y
    rw [← hOU, ← mem_pCore_iff_mem_pCoreOf Kh y, ← QuotientGroup.eq_one_iff, hφe]
    constructor
    · intro h1
      have h2 : e (QuotientGroup.mk y) = 1 := Subtype.ext h1
      rwa [MulEquiv.map_eq_one_iff] at h2
    · intro h1
      rw [h1, map_one]
      rfl
  have hφP0 : ∀ s : ↥Kh, (s : G) ∈ T → φ s ∈ A7Std.p0L := by
    intro s hs
    have h1 : e (QuotientGroup.mk s) ∈ (modO2Image Kh (T ⊓ Kh)).map e.toMonoidHom :=
      ⟨QuotientGroup.mk s, ⟨s, Subgroup.mem_subgroupOf.mpr ⟨hs, s.2⟩, rfl⟩, rfl⟩
    rw [pk.p0] at h1
    exact h1
  have hUe := pk.elemAbelian
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hU2 : ∀ x ∈ U, x * x = 1 := fun x hx => by rw [← sq]; exact hUe.2 x hx
  have hKhU : Kh ≤ Subgroup.normalizer (U : Set G) := pk.le_normalizer
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le_normalizer
  have hred := hV'.isTwoReducedIn
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V' : Set G) := hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V' : Set G) := le_sup_left.trans hLTV
  have hTV : T ≤ Subgroup.normalizer (V' : Set G) := le_sup_right.trans hLTV
  have hVe : IsElemAbelian 2 V' := hred.2.2.1
  have hVcomm : ∀ v ∈ V', ∀ w ∈ V', v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hVR2 : V' ≤ reducedAggregate (L ⊔ T) := hV'.le_reducedAggregate
  have hVT : V' ≤ T := hVR2.trans h.reducedAggregate_le_T
  have hS := h.setting516 hD hV'
  have hQV : pCoreOf 2 L ≤ Subgroup.centralizer (V' : Set G) :=
    hS.pCoreOf_le.trans (Subgroup.centralizer_le hVR2)
  have hQT : pCoreOf 2 L ≤ T := h.pCoreOf_le_pCoreOf_sup.trans
    (F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf le_sup_right))
  have hCTL := h.inf_centralizer_eq_bot_of_omega hZL
  have hVCL : V' ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hCTL]
    exact inf_le_inf_right _ hVT
  obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := hnat.exists_qcoord h.isSylowTwoOf_inf
  have hYinj := BCOrd.injective_of_qcoord hc hVCL
  have hVcard := BCOrd.card_eq_of_qcoord hc hYinj
  have hV'L : V' ≤ L := by
    have h1 : ⁅V', L⁆ ≤ V' ⊓ L := BCOrd.commutator_le_inf_of_le_normalizer (hVT.trans hTL) hLV
    have h2 := BCOrd.le_of_qcoord hc hYinj (h1.trans inf_le_left)
      (le_normalizer_commutator_of hLV Subgroup.le_normalizer) hV'.2.2
    exact h2.trans (h1.trans inf_le_right)
  have hd₀L : (d₀ : G) ∈ L := (hD.1 (hD₃ hd₀).1).1
  have hd₀N : (d₀ : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (hD.1 (hD₃ hd₀).1).2
  have hd₀3 : (d₀ : G) ^ 3 = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard D₃ hd₀
    rw [h3] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hd₀3' : d₀ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hd₀3, Subgroup.coe_one])
  have hodd : Odd (orderOf (d₀ : G)) := by
    have h1 : orderOf (d₀ : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hd₀3
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2 <;> rw [h2] <;> decide
  set π : Perm (Fin 7) := φ d₀ with hπdef
  have hπ3 : π ^ 3 = 1 := by rw [hπdef, ← map_pow, hd₀3', map_one]
  have hπ0 : π 0 ≠ 0 := hd₀0
  have hπS : ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) → (π i = 0 ∨ π i = 5 ∨ π i = 6) :=
    hstab
  have hd₀Q : (d₀ : G) ∉ pCoreOf 2 L := by
    intro hdQ
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨(d₀ : G), hdQ⟩
    have hk' : (d₀ : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf (d₀ : G) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hd₀3)
    rw [show Nat.gcd (2 ^ k) 3 = 1 from Nat.Coprime.pow_left k (by norm_num), Nat.dvd_one,
      orderOf_eq_one_iff] at hord
    apply hπ0
    have h1 : d₀ = 1 := Subtype.ext hord
    rw [hπdef, h1, map_one]
    rfl
  have hTLK : T ⊓ L ≤ Kh := inf_le_left.trans hTKh
  have hfix56 : ∀ s : ↥Kh, (s : G) ∈ T ⊓ L → φ s ∈ A7Std.p0L ∧ φ s 5 = 5 ∧ φ s 6 = 6 := by
    intro s hs
    have hP := hφP0 s hs.1
    have hconj : ∀ g : ↥Kh, (g : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) →
        φ (g * s * g⁻¹) 0 = 0 := by
      intro g hg
      have h1 : ((g * s * g⁻¹ : ↥Kh) : G) ∈ T ⊓ L := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp hg _).mp hs
      exact A7Std.p0L_zero (hφP0 _ h1.1)
    have hd₀N' : ((d₀⁻¹ : ↥Kh) : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inv]
      exact inv_mem hd₀N
    have ha : φ s (π 0) = π 0 := by
      have h1 := hconj d₀⁻¹ hd₀N'
      rw [map_mul, map_mul, inv_inv, ← hπdef] at h1
      simp only [Perm.mul_apply, map_inv] at h1
      have h2 := congrArg (fun x => π x) h1
      rwa [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply] at h2
    have hb : φ s (π⁻¹ 0) = π⁻¹ 0 := by
      have h1 := hconj d₀ hd₀N
      rw [map_mul, map_mul, map_inv, ← hπdef] at h1
      simp only [Perm.mul_apply] at h1
      have h2 := congrArg (fun x => π⁻¹ x) h1
      rwa [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply] at h2
    have hπi0 : π⁻¹ 0 = π (π 0) := by
      rw [Perm.inv_eq_iff_eq]
      have := congrArg (fun f : Perm (Fin 7) => f 0) hπ3
      simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply] at this
      exact this.symm
    have h56 : (π 0 = 5 ∧ π (π 0) = 6) ∨ (π 0 = 6 ∧ π (π 0) = 5) := by
      have hpi := hπS 0 (Or.inl rfl)
      have hpp : π (π 0) = 0 ∨ π (π 0) = 5 ∨ π (π 0) = 6 :=
        hπS (π 0) (hpi.resolve_left hπ0 |>.elim (fun h => Or.inr (Or.inl h))
          (fun h => Or.inr (Or.inr h)))
      have hne1 : π (π 0) ≠ π 0 := fun h1 => hπ0 (π.injective h1)
      have hne0 : π (π 0) ≠ 0 := by
        intro h1
        have := congrArg (fun f : Perm (Fin 7) => f 0) hπ3
        simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply] at this
        rw [h1] at this
        exact hπ0 this
      rcases hpi with h0 | h5 | h6
      · exact absurd h0 hπ0
      · rcases hpp with h | h | h
        · exact absurd h hne0
        · exact absurd (h.trans h5.symm) hne1
        · exact Or.inl ⟨h5, h⟩
      · rcases hpp with h | h | h
        · exact absurd h hne0
        · exact Or.inr ⟨h6, h⟩
        · exact absurd (h.trans h6.symm) hne1
    rw [hπi0] at hb
    rcases h56 with ⟨h5, h6⟩ | ⟨h6, h5⟩
    · rw [h5] at ha
      rw [h6] at hb
      exact ⟨hP, ha, hb⟩
    · rw [h6] at ha
      rw [h5] at hb
      exact ⟨hP, hb, ha⟩
  set V4 : Finset (Perm (Fin 7)) := A7Std.p0L.toFinset.filter (fun p => p 5 = 5 ∧ p 6 = 6)
    with hV4def
  have hV4 : V4.card = 4 := by decide
  have hmemV4 : ∀ q : O2Q Kh, q ∈ modO2Image Kh (T ⊓ L) →
      ((e q : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ V4 := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨hP, h5, h6⟩ := hfix56 s hs'
    rw [hV4def, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hP, h5, h6⟩
  have himg : Nat.card (modO2Image Kh (T ⊓ L)) ≤ 4 := by
    have h1 := Nat.card_le_card_of_injective
      (fun q : ↥(modO2Image Kh (T ⊓ L)) =>
        (⟨((e q.1 : alternatingGroup (Fin 7)) : Perm (Fin 7)), hmemV4 q.1 q.2⟩ : {p // p ∈ V4}))
      (fun q₁ q₂ h12 => by
        have h2 := congrArg Subtype.val h12
        have h3 : e q₁.1 = e q₂.1 := Subtype.ext h2
        exact Subtype.ext (e.injective h3))
    rwa [Nat.card_eq_finsetCard, hV4] at h1
  have hcardTL : Nat.card ↥(T ⊓ L) =
      Nat.card (modO2Image Kh (T ⊓ L)) * Nat.card ↥((T ⊓ L) ⊓ U) := by
    rw [A6.L13825.card_modO2Image hTLK, hOU]
    have h1 := Subgroup.relIndex_mul_card ((T ⊓ L) ⊓ U) (T ⊓ L)
    rw [inf_of_le_left inf_le_left] at h1
    exact h1.symm
  have hcardTLU : Nat.card ↥((T ⊓ L) ⊓ U) ≤ 16 :=
    (Subgroup.card_le_of_le inf_le_right).trans hU16.le
  have hTL64 : Nat.card ↥(T ⊓ L) ≤ 64 := by
    rw [hcardTL]
    calc Nat.card (modO2Image Kh (T ⊓ L)) * Nat.card ↥((T ⊓ L) ⊓ U) ≤ 4 * 16 :=
          Nat.mul_le_mul himg hcardTLU
      _ = 64 := by norm_num
  have hautTL := BCOrd.card_autOn_eq_of_qcoord hc (inf_le_right : T ⊓ L ≤ L)
  have hcardTL' : Nat.card ↥(T ⊓ L) = Nat.card (autOn (T ⊓ L) V') *
      Nat.card ↥((T ⊓ L) ⊓ Subgroup.centralizer (V' : Set G)) := by
    rw [card_autOn_eq_relIndex (inf_le_left.trans hTV)]
    have h1 := Subgroup.relIndex_mul_card ((T ⊓ L) ⊓ Subgroup.centralizer (V' : Set G)) (T ⊓ L)
    rw [inf_of_le_left inf_le_left] at h1
    exact h1.symm
  have hVC : V' ≤ (T ⊓ L) ⊓ Subgroup.centralizer (V' : Set G) :=
    le_inf (le_inf hVT hV'L) fun v hv =>
      Subgroup.mem_centralizer_iff.mpr fun w hw => hVcomm w hw v hv
  have hcVC := Subgroup.card_le_of_le hVC
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hFeq : Nat.card F = 4 := by
    have h1 : Nat.card F * Nat.card F ^ 2 ≤ 64 := by
      rw [← hVcard, ← hautTL]
      calc Nat.card (autOn (T ⊓ L) V') * Nat.card V' ≤
          Nat.card (autOn (T ⊓ L) V') *
            Nat.card ↥((T ⊓ L) ⊓ Subgroup.centralizer (V' : Set G)) :=
            Nat.mul_le_mul_left _ hcVC
        _ = Nat.card ↥(T ⊓ L) := hcardTL'.symm
        _ ≤ 64 := hTL64
    nlinarith
  have hn2 : n = 2 := by
    have h1 : 2 ^ n = 2 ^ 2 := by rw [← hF, hFeq]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h1
  subst hn2
  have hV16 : Nat.card V' = 16 := by rw [hVcard, hFeq]; norm_num
  have hTLge : 64 ≤ Nat.card ↥(T ⊓ L) := by
    rw [hcardTL', hautTL, hFeq]
    calc 64 = 4 * 16 := by norm_num
      _ ≤ 4 * Nat.card ↥((T ⊓ L) ⊓ Subgroup.centralizer (V' : Set G)) := by
          rw [← hV16]
          exact Nat.mul_le_mul_left _ hcVC
  have hCV : (T ⊓ L) ⊓ Subgroup.centralizer (V' : Set G) = V' := by
    refine (Subgroup.eq_of_le_of_card_ge hVC ?_).symm
    have h1 := hcardTL'
    rw [hautTL, hFeq] at h1
    omega
  have hUTL : U ≤ T ⊓ L := by
    have h1 : (T ⊓ L) ⊓ U = U := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      have h2 := hcardTL
      rw [hU16]
      have h3 : Nat.card (modO2Image Kh (T ⊓ L)) * Nat.card ↥((T ⊓ L) ⊓ U) ≥ 64 := by
        rw [← h2]
        exact hTLge
      by_contra hlt
      have hlt' := not_le.mp hlt
      have h4 : Nat.card (modO2Image Kh (T ⊓ L)) * Nat.card ↥((T ⊓ L) ⊓ U) ≤ 4 * 15 :=
        Nat.mul_le_mul himg (by omega)
      omega
    exact h1 ▸ inf_le_left
  have hO2V : pCoreOf 2 L ≤ V' := by
    rw [← hCV]
    exact le_inf (le_inf hQT (pCoreOf_le 2 L)) hQV
  obtain ⟨e0⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 2) 2 2
    (by norm_num) (GaloisField.card 2 2 (by norm_num)) h.lie
  have hd₀V : (d₀ : G) ∉ Subgroup.centralizer (V' : Set G) := fun hdV =>
    hd₀Q (h.inf_centralizer_le hLV hV'.2.2 ⟨hd₀L, hdV⟩)
  have hcent : ∀ t ∈ T ⊓ L, (d₀ : G) * t = t * d₀ → t = 1 := by
    intro t ht htd
    have htQ : t ∈ pCoreOf 2 L := by
      by_contra htQ
      set tq : ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk ⟨t, ht.2⟩ with htq
      set dq : ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk ⟨d₀, hd₀L⟩ with hdq
      have htq1 : tq ≠ 1 := by
        intro h1
        rw [htq, QuotientGroup.eq_one_iff] at h1
        exact htQ ((mem_pCore_iff_mem_pCoreOf L _).mp h1)
      obtain ⟨k, hk⟩ := hT2 ⟨t, ht.1⟩
      have htk : tq ^ 2 ^ k = 1 := by
        rw [htq, ← QuotientGroup.mk_pow]
        have h1 : (⟨t, ht.2⟩ : ↥L) ^ 2 ^ k = 1 :=
          Subtype.ext (by simpa using congrArg Subtype.val hk)
        rw [h1, QuotientGroup.mk_one]
      have h2 : 2 ∣ orderOf tq := by
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one htk)
        rcases i with _ | i
        · exact absurd (orderOf_eq_one_iff.mp (by simpa using hi)) htq1
        · rw [hi, pow_succ]
          exact dvd_mul_left 2 _
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers tq) 2
        (by rwa [Nat.card_zpowers])
      have hcomm : dq * (y : ↥L ⧸ CFSG.pCore 2 ↥L) = (y : ↥L ⧸ CFSG.pCore 2 ↥L) * dq := by
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp y.2
        rw [← hi]
        have h3 : dq * tq = tq * dq := by
          rw [hdq, htq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          exact Subtype.ext htd
        exact ((Commute.zpow_right h3 i).eq)
      have hdodd : Odd (orderOf dq) := by
        have h3 : orderOf dq ∣ orderOf (⟨d₀, hd₀L⟩ : ↥L) := by
          rw [hdq]
          exact orderOf_map_dvd (QuotientGroup.mk' _) _
        rw [Subgroup.orderOf_mk] at h3
        exact Odd.of_dvd_nat hodd h3
      have hdq1 := CFSG.Walter.JT.eq_one_of_commute_of_psl24 e0 hdodd
        (by rw [Subgroup.orderOf_coe, hy]) hcomm
      apply hd₀Q
      rw [hdq, QuotientGroup.eq_one_iff] at hdq1
      exact (mem_pCore_iff_mem_pCoreOf L _).mp hdq1
    have htV : t ∈ V' := hO2V htQ
    have htC := hnat.mem_centralizer_of_conj_eq_of_odd hd₀L hodd hd₀V htV
      (by rw [htd, mul_inv_cancel_right])
    have h1 : t ∈ V' ⊓ Subgroup.centralizer (L : Set G) := ⟨htV, htC⟩
    rw [hVCL] at h1
    exact h1
  let p56 : Fin 7 → Prop := fun i => i = 0 ∨ i = 5 ∨ i = 6
  have hπp : ∀ i, p56 (π i) ↔ p56 i := by
    intro i
    refine ⟨fun hi => ?_, hπS i⟩
    have h1 := hπS _ (hπS _ hi)
    have h2 : (π ^ 3) i = i := by rw [hπ3]; rfl
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply] at h2
    rwa [h2] at h1
  have hπpc : ∀ i, ¬ p56 (π i) ↔ ¬ p56 i := fun i => not_congr (hπp i)
  set π₀ : Perm (Fin 7) := Perm.ofSubtype (π.subtypePerm (p := p56) hπp) with hπ₀def
  set π₁ : Perm (Fin 7) := Perm.ofSubtype (π.subtypePerm (p := fun i => ¬ p56 i) hπpc)
    with hπ₁def
  have hπ₀a : ∀ i, p56 i → π₀ i = π i := fun i hi => Perm.ofSubtype_subtypePerm_of_mem hπp hi
  have hπ₀b : ∀ i, ¬ p56 i → π₀ i = i := fun i hi => Perm.ofSubtype_apply_of_not_mem _ hi
  have hπ₁a : ∀ i, p56 i → π₁ i = i := fun i hi =>
    Perm.ofSubtype_apply_of_not_mem _ (not_not.mpr hi)
  have hπ₁b : ∀ i, ¬ p56 i → π₁ i = π i := fun i hi => Perm.ofSubtype_subtypePerm_of_mem hπpc hi
  have hdecomp : π = π₀ * π₁ := by
    ext i
    by_cases hi : p56 i
    · rw [Perm.mul_apply, hπ₁a i hi, hπ₀a i hi]
    · rw [Perm.mul_apply, hπ₁b i hi, hπ₀b _ ((hπpc i).mpr hi)]
  have hcomm01 : π₀ * π₁ = π₁ * π₀ := by
    ext i
    by_cases hi : p56 i
    · rw [Perm.mul_apply, Perm.mul_apply, hπ₁a i hi, hπ₀a i hi, hπ₁a _ ((hπp i).mpr hi)]
    · rw [Perm.mul_apply, Perm.mul_apply, hπ₀b i hi, hπ₁b i hi, hπ₀b _ ((hπpc i).mpr hi)]
  have hpow : ∀ (q : Fin 7 → Prop) [DecidablePred q] (hq : ∀ i, q (π i) ↔ q i),
      (Perm.ofSubtype (π.subtypePerm hq)) ^ 3 = 1 := by
    intro q _ hq
    ext i
    rw [← map_pow, Perm.subtypePerm_pow, Perm.one_apply]
    by_cases hi : q i
    · rw [Perm.ofSubtype_subtypePerm_of_mem _ hi, hπ3]
      rfl
    · rw [Perm.ofSubtype_apply_of_not_mem _ hi]
  have hπ₀3 : π₀ ^ 3 = 1 := hpow p56 hπp
  have hπ₁3 : π₁ ^ 3 = 1 := hpow (fun i => ¬ p56 i) hπpc
  have hπ₀0 : π₀ 0 ≠ 0 := by
    rw [hπ₀a 0 (Or.inl rfl)]
    exact hπ0
  have hπ₀c : π₀.IsThreeCycle := by
    refine BCFalse.isThreeCycle_of_pow_three hπ₀3 (fun h1 => hπ₀0 (by rw [h1]; rfl)) ?_
    calc π₀.support.card ≤ (Finset.univ.filter p56).card := by
          refine Finset.card_le_card fun i hi => ?_
          rw [Perm.mem_support] at hi
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ i, by_contra fun hn => hi (hπ₀b i hn)⟩
      _ ≤ 4 := by decide
  by_cases hπ₁1 : π₁ = 1
  ·
    have hππ₀ : π = π₀ := by rw [hdecomp, hπ₁1, mul_one]
    obtain ⟨s, hsTL, hs1⟩ : ∃ s, ∃ hs : s ∈ T ⊓ L, φ ⟨s, hTLK hs⟩ ≠ 1 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      have h1 : T ⊓ L ≤ U := fun s hs => (hφU ⟨s, hTLK hs⟩).mp (hall s hs)
      have h2 := Subgroup.card_le_of_le h1
      omega
    set sK : ↥Kh := ⟨s, hTLK hsTL⟩ with hsK
    obtain ⟨hsP, hs5, hs6⟩ := hfix56 sK hsTL
    have hs0 : φ sK 0 = 0 := A7Std.p0L_zero hsP
    have hsfix : ∀ i, p56 i → φ sK i = i := by
      rintro i (rfl | rfl | rfl)
      · exact hs0
      · exact hs5
      · exact hs6
    have hsc : π * φ sK = φ sK * π := by
      rw [hππ₀]
      ext i
      by_cases hi : p56 i
      · have hπ₀i : p56 (π₀ i) := by
          rw [hπ₀a i hi]
          exact (hπp i).mpr hi
        rw [Perm.mul_apply, Perm.mul_apply, hsfix i hi, hsfix _ hπ₀i]
      · have hsi : ¬ p56 (φ sK i) := by
          intro hsi
          apply hi
          have h1 := hsfix _ hsi
          rwa [(φ sK).injective h1] at hsi
        rw [Perm.mul_apply, Perm.mul_apply, hπ₀b _ hsi, hπ₀b i hi]
    set u₀ : G := s⁻¹ * ((d₀ : G) * s * (d₀ : G)⁻¹) with hu₀def
    have hu₀U : u₀ ∈ U := by
      have h1 : (sK⁻¹ * (d₀ * sK * d₀⁻¹) : ↥Kh) ∈ (φ.ker) := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hπdef]
        rw [hsc]
        group
      have h2 := (hφU _).mp h1
      simpa [hu₀def] using h2
    have hu₀TL : u₀ ∈ T ⊓ L := by
      refine Subgroup.mul_mem _ (Subgroup.inv_mem _ hsTL) ?_
      exact (Subgroup.mem_normalizer_iff.mp hd₀N s).mp hsTL
    have hd₀K : (d₀ : G) ∈ Kh := d₀.2
    have hconjU : ∀ x ∈ U, (d₀ : G) * x * (d₀ : G)⁻¹ ∈ U := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hKhU hd₀K) x).mp hx
    set u₁ : G := (d₀ : G) * u₀ * (d₀ : G)⁻¹ with hu₁def
    set u₂ : G := (d₀ : G) * u₁ * (d₀ : G)⁻¹ with hu₂def
    have hu₁U : u₁ ∈ U := hconjU _ hu₀U
    have hu₂U : u₂ ∈ U := hconjU _ hu₁U
    have hc1 : (d₀ : G) * s * (d₀ : G)⁻¹ = s * u₀ := by rw [hu₀def]; group
    have hrel : u₀ * u₁ * u₂ = 1 := by
      have e1 : s = s * (u₀ * u₁ * u₂) := by
        have hd₀3m : (d₀ : G) * ((d₀ : G) * (d₀ : G)) = 1 := by rw [← pow_three]; exact hd₀3
        calc s = ((d₀ : G) * ((d₀ : G) * (d₀ : G))) * s *
              ((d₀ : G) * ((d₀ : G) * (d₀ : G)))⁻¹ := by rw [hd₀3m]; group
          _ = (d₀ : G) * ((d₀ : G) * ((d₀ : G) * s * (d₀ : G)⁻¹) * (d₀ : G)⁻¹) *
              (d₀ : G)⁻¹ := by group
          _ = (d₀ : G) * ((d₀ : G) * (s * u₀) * (d₀ : G)⁻¹) * (d₀ : G)⁻¹ := by rw [hc1]
          _ = (d₀ : G) * (((d₀ : G) * s * (d₀ : G)⁻¹) * u₁) * (d₀ : G)⁻¹ := by
              rw [hu₁def]; group
          _ = (d₀ : G) * ((s * u₀) * u₁) * (d₀ : G)⁻¹ := by rw [hc1]
          _ = ((d₀ : G) * s * (d₀ : G)⁻¹) * u₁ * u₂ := by rw [hu₂def, hu₁def]; group
          _ = s * (u₀ * u₁ * u₂) := by rw [hc1]; group
      have e2 : s * (u₀ * u₁ * u₂) = s * 1 := by rw [mul_one, ← e1]
      exact mul_left_cancel e2
    have hu02 : u₀ * u₂ = u₁ := by
      have h1 : u₀ * u₂ * u₁ = 1 := by
        rw [mul_assoc, hUcomm u₂ hu₂U u₁ hu₁U, ← mul_assoc]
        exact hrel
      calc u₀ * u₂ = (u₀ * u₂ * u₁) * u₁ := by
            rw [mul_assoc (u₀ * u₂), hU2 u₁ hu₁U, mul_one]
        _ = u₁ := by rw [h1, one_mul]
    have hs'TL : s * u₁ ∈ T ⊓ L :=
      Subgroup.mul_mem _ hsTL ((Subgroup.mem_normalizer_iff.mp hd₀N u₀).mp hu₀TL)
    have hs'fix : (d₀ : G) * (s * u₁) = (s * u₁) * d₀ := by
      have h1 : (d₀ : G) * (s * u₁) * (d₀ : G)⁻¹ = s * u₁ := by
        calc (d₀ : G) * (s * u₁) * (d₀ : G)⁻¹ =
            ((d₀ : G) * s * (d₀ : G)⁻¹) * ((d₀ : G) * u₁ * (d₀ : G)⁻¹) := by group
          _ = s * u₀ * u₂ := by rw [hc1, hu₂def]
          _ = s * u₁ := by rw [mul_assoc, hu02]
      calc (d₀ : G) * (s * u₁) = ((d₀ : G) * (s * u₁) * (d₀ : G)⁻¹) * d₀ := by group
        _ = (s * u₁) * d₀ := by rw [h1]
    have hs'1 : s * u₁ ≠ 1 := by
      intro h1
      apply hs1
      have hu₁K : u₁ ∈ Kh := (hUTL hu₁U).1 |> fun h => hTKh h
      have h2 : sK = (⟨u₁, hu₁K⟩ : ↥Kh)⁻¹ :=
        Subtype.ext (eq_inv_of_mul_eq_one_left h1)
      rw [h2, map_inv, (hφU _).mpr hu₁U, inv_one]
    exact hs'1 (hcent _ hs'TL hs'fix)
  ·
    have hπ₁c : π₁.IsThreeCycle := by
      refine BCFalse.isThreeCycle_of_pow_three hπ₁3 hπ₁1 ?_
      calc π₁.support.card ≤ (Finset.univ.filter fun i => ¬ p56 i).card := by
            refine Finset.card_le_card fun i hi => ?_
            rw [Perm.mem_support] at hi
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ i, fun hn => hi (hπ₁a i hn)⟩
        _ ≤ 4 := by decide
    obtain ⟨j, hj, Ψ, hΨ0, hΨ⟩ := A7ZK.exists_four_equiv e hKhU hUe pk.pCoreOf_le pk.irr
      pk.not_le_centralizer (by rw [hU16]; norm_num)
    obtain ⟨x, hx⟩ : ∃ x : ↥Kh, e (QuotientGroup.mk x) = ⟨π₀, hπ₀c.mem_alternatingGroup⟩ := by
      obtain ⟨q, hq⟩ := e.surjective ⟨π₀, hπ₀c.mem_alternatingGroup⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, hq⟩
    obtain ⟨y, hy⟩ : ∃ y : ↥Kh, e (QuotientGroup.mk y) = ⟨π₁, hπ₁c.mem_alternatingGroup⟩ := by
      obtain ⟨q, hq⟩ := e.surjective ⟨π₁, hπ₁c.mem_alternatingGroup⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨y, hq⟩
    have hφx : φ x = π₀ := by rw [hφe, hx]
    have hφy : φ y = π₁ := by rw [hφe, hy]
    have hsame : ∀ y₁ y₂ : ↥Kh, φ y₁ = φ y₂ →
        A7ZK.conjAut hKhU y₁ = A7ZK.conjAut hKhU y₂ := fun y₁ y₂ h12 =>
      BCFalse.conjAut_eq_of_eq e hKhU pk.pCoreOf_le (Subtype.ext h12)
    set a := A7ZK.conjAut hKhU x with ha
    set b := A7ZK.conjAut hKhU y with hb
    have hab : a * b = b * a := by
      rw [ha, hb, ← map_mul, ← map_mul]
      apply hsame
      rw [map_mul, map_mul, hφx, hφy, hcomm01]
    have ha3 : a ^ 3 = 1 := by
      rw [ha, ← map_pow, hsame (x ^ 3) 1 (by rw [map_pow, hφx, hπ₀3, map_one]), map_one]
    have hb3 : b ^ 3 = 1 := by
      rw [hb, ← map_pow, hsame (y ^ 3) 1 (by rw [map_pow, hφy, hπ₁3, map_one]), map_one]
    have hafp : ∀ u, a u = u → u = 1 := fun u hu =>
      BCFalse.eq_one_of_isThreeCycle e hKhU pk.pCoreOf_le hj hΨ0 hΨ (by rw [hx]; exact hπ₀c) hu
    have hbfp : ∀ u, b u = u → u = 1 := fun u hu =>
      BCFalse.eq_one_of_isThreeCycle e hKhU pk.pCoreOf_le hj hΨ0 hΨ (by rw [hy]; exact hπ₁c) hu
    have hcfp : ∀ u, (a * b) u = u → u = 1 := by
      intro u hu
      have h1 : A7ZK.conjAut hKhU d₀ u = u := by
        rw [hsame d₀ (x * y) (by rw [map_mul, hφx, hφy, ← hdecomp]), map_mul]
        exact hu
      have h2 : (d₀ : G) * u * (d₀ : G)⁻¹ = u := congrArg Subtype.val h1
      have h3 : (d₀ : G) * u = u * d₀ := by
        calc (d₀ : G) * u = ((d₀ : G) * u * (d₀ : G)⁻¹) * d₀ := by group
          _ = u * d₀ := by rw [h2]
      exact Subtype.ext (hcent _ (hUTL u.2) h3)
    have hcommU : ∀ v w : ↥U, v * w = w * v := fun v w =>
      Subtype.ext (hUcomm v v.2 w w.2)
    have hU2' : ∀ v : ↥U, v * v = 1 := fun v => Subtype.ext (hU2 v v.2)
    have heq := BCFalse.eq_of_fixedPointFree hcommU hU2' hab ha3 hb3 hafp hbfp hcfp
    have hxy : ((x * y⁻¹ : ↥Kh) : G) ∈ Kh ⊓ Subgroup.centralizer (U : Set G) := by
      refine ⟨(x * y⁻¹).2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have h1 : A7ZK.conjAut hKhU (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, ← ha, ← hb, heq, mul_inv_cancel]
      have h2 := congrArg (fun f : MulAut ↥U => ((f ⟨u, hu⟩ : ↥U) : G)) h1
      simp only [A7ZK.coe_conjAut, MulAut.one_apply] at h2
      calc u * ((x * y⁻¹ : ↥Kh) : G) =
          ((x * y⁻¹ : ↥Kh) : G) * (((x * y⁻¹ : ↥Kh) : G)⁻¹ * u * ((x * y⁻¹ : ↥Kh) : G)) := by
            group
        _ = ((x * y⁻¹ : ↥Kh) : G) * u := by
            congr 1
            calc ((x * y⁻¹ : ↥Kh) : G)⁻¹ * u * ((x * y⁻¹ : ↥Kh) : G) =
                ((x * y⁻¹ : ↥Kh) : G)⁻¹ * (((x * y⁻¹ : ↥Kh) : G) * u *
                  ((x * y⁻¹ : ↥Kh) : G)⁻¹) * ((x * y⁻¹ : ↥Kh) : G) := by rw [h2]
              _ = u := by group
    have hO := A7ZK.inf_centralizer_le_pCoreOf pk.perf pk.simple hKhU pk.not_le_centralizer hxy
    rw [hOU] at hO
    have h1 := (hφU _).mpr hO
    rw [map_mul, map_inv, hφx, hφy, mul_inv_eq_one] at h1
    apply hπ₀0
    rw [h1]
    exact hπ₁a 0 (Or.inl rfl)

end Hyp5_0_1

theorem stmt5_1_13_bc_false_of (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51) (h510 : Stmt5_1_10) :
    Stmt5_1_13_bc_false := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' _ hnat hT
  obtain ⟨e, pk⟩ := m.exists_a7Pack h5171 h51 hc5 hX hnZ hA7
  obtain ⟨hOU, hO16⟩ := stmt5_1_13_bc_small_of h5171 h51 G T M L V H B D K₁ X Kh₁ n m hc5 hty
    hX hnZ hA7 hZL hZK hT
  obtain ⟨D₃, hD₃, h3, hD₃K, hDK, -⟩ := hty.2.2
  obtain ⟨hstab, d₀, hd₀, hd₀0⟩ :=
    m.d3_stab_zero_five_six h510 hc5 pk.r0 pk.p0 hD₃ h3 hD₃K hDK
  exact m.hyp.toHyp5_0_1.false_of_card_le m.nota.2.1 hZL hV' hnat pk hOU hO16 hT hD₃ h3 hd₀
    (hstab d₀ hd₀) hd₀0

theorem stmt5_1_13_four_block_bc_of_hat (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51)
    (h510 : Stmt5_1_10) (hhat : Stmt5_1_13_bc_hat) : Stmt5_1_13_four_block_bc :=
  stmt5_1_13_four_block_bc_of hhat stmt5_1_13_bc_order_holds
    (stmt5_1_13_bc_false_of h5171 h51 h510)

end CFSG.Quasithin.H13
