module

public import CFSG.RankThree.PartOne.D4RC.SpecialLines
public import CFSG.RankThree.PartOne.D4RC.S3Lite

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Abstract

variable {G : Type*} [Group G]

theorem rcy_isCyclic_of_injective [Finite G] {L : Type*} [Field L] (χ : G →* Lˣ)
    (h : Function.Injective χ) : IsCyclic G := by
  have e := MonoidHom.ofInjective h
  have : Finite χ.range := Finite.of_equiv _ e.toEquiv
  exact (MulEquiv.isCyclic e).2 inferInstance

theorem rcy_not_dvd_relIndex [Finite G] {p : ℕ} {S P G' : Subgroup G} (hSG : S ≤ G')
    (hPG : P ≤ G') (hPn : ∀ g ∈ G', ∀ u ∈ P, g * u * g⁻¹ ∈ P) (hS : ¬ p ∣ S.index) :
    ¬ p ∣ (S ⊓ P).relIndex P := by
  set T := S.subgroupOf G' with hT
  set N := P.subgroupOf G' with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hPn g g.2 n hn⟩
  have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ N) T (T ⊔ N) inf_le_left le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex (T ⊓ N) N (T ⊔ N) inf_le_right le_sup_right
  rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_left T N] at h2
  have h0 : (T ⊓ N).relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : (T ⊓ N).relIndex N = T.relIndex (T ⊔ N) := by
    have h4 := h1.trans h2.symm
    rw [mul_comm ((T ⊓ N).relIndex N)] at h4
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) h4).symm
  have h5 : (S ⊓ P).relIndex P = (T ⊓ N).relIndex N := by
    rw [← Subgroup.relIndex_subgroupOf hPG]
    rfl
  have h6 : T.relIndex (T ⊔ N) ∣ T.index := Subgroup.relIndex_dvd_index_of_le le_sup_left
  have h7 : S.relIndex G' ∣ S.index := ⟨G'.index, (Subgroup.relIndex_mul_index hSG).symm⟩
  intro hp
  rw [h5, h3] at hp
  exact hS (hp.trans (h6.trans h7))

theorem rcy_mem_of_pow_eq_one {L : Type*} [Field L] {p : ℕ} (hp : p.Prime) {Q E : Subgroup G}
    (κ : Q →* Lˣ × Lˣ) (hκ : Function.Injective κ) (hEQ : E ≤ Q) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hEc : Nat.card E = p ^ 2) {y : G} (hyQ : y ∈ Q) (hy : y ^ p = 1) : y ∈ E := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b => hκ (by rw [map_mul, map_mul, mul_comm])
  let Ω : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ Q, g ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨Q.mul_mem ha hb, ?_⟩
        have hab : Commute a b := congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
        rw [hab.mul_pow, hap, hbp, one_mul]
      one_mem' := ⟨Q.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        exact ⟨Q.inv_mem ha, by rw [inv_pow, hap, inv_one]⟩ }
  have hmem : ∀ g : Ω, ∃ hg : (g : G) ∈ Q, (g : G) ^ p = 1 := fun g => g.2
  have hval : ∀ g : Ω, κ ⟨g, (hmem g).1⟩ ^ p = 1 := fun g => by
    rw [← map_pow]
    have : (⟨g, (hmem g).1⟩ : Q) ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact (hmem g).2)
    rw [this, map_one]
  let φ : Ω → rootsOfUnity p L × rootsOfUnity p L := fun g =>
    (⟨(κ ⟨g, (hmem g).1⟩).1, (mem_rootsOfUnity _ _).2 (by
      have := congrArg Prod.fst (hval g)
      rwa [Prod.pow_fst] at this)⟩,
     ⟨(κ ⟨g, (hmem g).1⟩).2, (mem_rootsOfUnity _ _).2 (by
      have := congrArg Prod.snd (hval g)
      rwa [Prod.pow_snd] at this)⟩)
  have hφ : Function.Injective φ := by
    intro g g' h
    have h1 := congrArg (fun z => (z.1 : Lˣ)) h
    have h2 := congrArg (fun z => (z.2 : Lˣ)) h
    have h3 : κ ⟨g, (hmem g).1⟩ = κ ⟨g', (hmem g').1⟩ := Prod.ext h1 h2
    have h4 := congrArg (fun z : Q => (z : G)) (hκ h3)
    exact Subtype.ext h4
  have hfin : Finite (rootsOfUnity p L × rootsOfUnity p L) := by
    have : Finite (rootsOfUnity p L) :=
      Nat.finite_of_card_ne_zero (Nat.pos_iff_ne_zero.1 (Nat.card_pos))
    infer_instance
  have hΩc : Nat.card Ω ≤ p ^ 2 := by
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_prod] at h1
    have h2 := card_rootsOfUnity L p
    calc Nat.card Ω ≤ _ := h1
      _ ≤ p * p := Nat.mul_le_mul h2 h2
      _ = p ^ 2 := (sq p).symm
  have hEΩ : E ≤ Ω := fun e he => ⟨hEQ he, hEp e he⟩
  have : Finite Ω := Finite.of_injective φ hφ
  have heq : E = Ω := Subgroup.eq_of_le_of_card_ge hEΩ (hEc ▸ hΩc)
  rw [heq]
  exact ⟨hyQ, hy⟩

end Abstract

section Arith

theorem rcy_ordProj_card {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : 2 ≤ q) (hpd : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) {N : ℕ}
    (hN : (ε = 1 → N = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) ∧
      (ε = -1 → N = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1))) :
    ordProj[p] N = ordProj[p] (d4T36d ε q) := by
  have hq1 : 1 ≤ q := by omega
  have hdz := d4T36d_cast hε hq1
  have hd0 : d4T36d ε q ≠ 0 := (d4T36d_odd hε hq1).pos.ne'
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsmall : ∀ m : ℤ, m = 1 ∨ m = 3 → ¬ (p : ℤ) ∣ m := by
    intro m hm h
    rcases hm with rfl | rfl
    · exact hpz.not_dvd_one h
    · have : p ∣ 3 := by exact_mod_cast h
      have := Nat.le_of_dvd (by norm_num) this
      omega
  have hq0 : ¬ (p : ℤ) ∣ q := by
    intro h
    have h1 : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - q * (q + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h _)
    exact hpz.not_dvd_one h1
  have hqm1 : ¬ (p : ℤ) ∣ (q : ℤ) - 1 := by
    intro h
    have h3 : (p : ℤ) ∣ 2 + ε := by
      have e : (2 + ε : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - ((q : ℤ) - 1) * (q + 1 + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h _)
    refine hsmall (2 + ε) ?_ h3
    rcases hε with rfl | rfl <;> norm_num
  have hqp1 : ¬ (p : ℤ) ∣ (q : ℤ) + 1 := by
    intro h
    have h3 : (p : ℤ) ∣ 2 - ε := by
      have e : (2 - ε : ℤ) = ((q : ℤ) ^ 2 + ε * q + 1) - ((q : ℤ) + 1) * (q - 1 + ε) := by ring
      rw [e]
      exact dvd_sub hpd (dvd_mul_of_dvd_left h _)
    refine hsmall (2 - ε) ?_ h3
    rcases hε with rfl | rfl <;> norm_num
  have hR : ¬ (p : ℤ) ∣ (q : ℤ) ^ 3 * (((q : ℤ) - 1) * ((q : ℤ) + 1)) * ((q : ℤ) - ε) := by
    intro h
    rcases hpz.dvd_or_dvd h with h | h
    · rcases hpz.dvd_or_dvd h with h | h
      · exact hq0 (hpz.dvd_of_dvd_pow h)
      · rcases hpz.dvd_or_dvd h with h | h
        · exact hqm1 h
        · exact hqp1 h
    · rcases hε with rfl | rfl
      · exact hqm1 h
      · exact hqp1 (by simpa using h)
  refine CTTw.ordProj_eq_of_int_cofactor hd0 ?_ hR
  rw [hdz]
  rcases hε with rfl | rfl
  · rw [hN.1 rfl]
    push_cast [CTTw.cast_pow_sub_one hq1]
    ring
  · rw [hN.2 rfl]
    push_cast [CTTw.cast_pow_sub_one hq1]
    ring

end Arith

section Frame

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

@[expose] def RclConj (F : RclFrame ℓ f K σ ε p L) (Q : Subgroup 𝒞[K, σ]) (c : 𝒞[K, σ]) :
    Prop :=
  ∀ y ∈ Q, F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∈
    twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))

theorem rcy_coord (F : RclFrame ℓ f K σ ε p L) {Q : Subgroup 𝒞[K, σ]} {c : 𝒞[K, σ]}
    (hc : RclConj F Q c) :
    ∃ β : Q →* (Fin TwistTag.D4.tag.rank → Lˣ),
      (∀ y : Q, rootDiagUnit TwistTag.D4.tag (β y) =
        F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0) ∧
      (∀ y : Q, β y ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f)) ∧
      Function.Injective β ∧
      ∃ κ : Q →* Lˣ × Lˣ, Function.Injective κ ∧
        ∀ y : Q, (κ y).1 ^ d4T36d ε (ℓ ^ f) = 1 ∧ (κ y).2 ^ d4T36d ε (ℓ ^ f) = 1 := by
  obtain ⟨β, hβ, -, hβfix⟩ := rcl_char_data_of_conj F Q c hc
  have hβinj : Function.Injective β := by
    intro y y' h
    have h1 : F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0 =
        F.g0⁻¹ * triEmb K σ L (c * (y' : 𝒞[K, σ]) * c⁻¹) * F.g0 := by
      rw [← hβ, ← hβ, h]
    have h2 := triEmb_injective (mul_left_cancel (mul_right_cancel h1))
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  have hℓ : ℓ.Prime := Fact.out
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  let κ : Q →* Lˣ × Lˣ := ((Pi.evalMonoidHom (fun _ => Lˣ) i0).comp β).prod
    ((Pi.evalMonoidHom (fun _ => Lˣ) i2).comp β)
  refine ⟨β, hβ, hβfix, hβinj, κ, ?_, fun y => ?_⟩
  · intro y y' h
    apply hβinj
    apply eq_of_d4QCoord_eq_d4T36 F.hε hFr (hβfix y) (hβfix y')
    have h1 : β y i0 = β y' i0 := congrArg Prod.fst h
    have h2 : β y i2 = β y' i2 := congrArg Prod.snd h
    rw [d4QCoord_apply, d4QCoord_apply, h1, h2]
  · obtain ⟨-, -, h2, h0⟩ := (mem_fixedCharTuples_d4T36 F.hε hFr (β y)).1 (hβfix y)
    rw [← d4T36d_cast F.hε hq1, zpow_natCast] at h2 h0
    exact ⟨h0, h2⟩

theorem rcy_rootChar_sigma (F : RclFrame ℓ f K σ ε p L) {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : b ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f)) {i : Fin 4}
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ d4Sigma i) (h1 : rootChar b α = 1) :
    ∀ γ ∈ d4Sigma i, rootChar b γ = 1 := by
  intro γ hγ
  obtain ⟨n, -, hn | hn⟩ := d4T36_sigma_orbit i α (mem_trialitySigma.1 hα) γ
    (mem_trialitySigma.1 hγ)
  · rw [hn]
    exact rootChar_powA_eq_one F.hε hb h1 n
  · have h2 : rootChar b (-((d4T36A ^ n) *ᵥ α)) = 1 := by
      rw [d4Q_rootChar_neg, rootChar_powA_eq_one F.hε hb h1 n, inv_one]
    rw [hn]
    exact h2

theorem rcy_mem_centralizer_of_rootChar (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) {y : 𝒞[K, σ]} (hy : y ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]))
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (sp.c * y * sp.c⁻¹) * F.g0)
    (hbfix : b ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f))
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ d4Sigma i) (h1 : rootChar b α = 1) :
    y ∈ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]) := by
  have hall := rcy_rootChar_sigma F hbfix hα h1
  have hcent : rootDiagUnit TwistTag.D4.tag b ∈ Subgroup.centralizer
      ((rootSpan TwistTag.D4.tag L (d4Sigma i) : Subgroup _) : Set _) :=
    (rootDiagUnit_mem_centralizer_rootSpan_iff b (fun α hα => isRoot_of_mem_d4Sigma hα)).2 hall
  have hψy : rclPsi sp ⟨y, hy⟩ = rootDiagUnit TwistTag.D4.tag b := by
    rw [hb]
    exact d4QPsi_apply _ _ _ _ _
  have hψ : Function.Injective (rclPsi sp) := d4QPsi_injective triEmb_injective F.g0 sp.c x
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hz' : rclPsi sp z ∈ rootSpan TwistTag.D4.tag L (d4Sigma i) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hz)).1
  have hc := Subgroup.mem_centralizer_iff.1 hcent _ hz'
  have h2 : z * ⟨y, hy⟩ = ⟨y, hy⟩ * z := hψ (by rw [map_mul, map_mul, hψy]; exact hc)
  exact congrArg Subtype.val h2

theorem rcy_pow_three_of_mem_center (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) {z : 𝒞[K, σ]} (hz : z ∈ rclPx sp)
    (hzc : z ∈ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ])) : z ^ 3 = 1 := by
  classical
  obtain ⟨D⟩ := rcl_exists_algData F i
  have hrange : D.ρ.range = rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    rw [D.frame.range, D.sigma_eq]
  obtain ⟨-, -, -, -, -, hQψ, -, hcentψ⟩ := rcl_psi_props F sp
  have hzx : z ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]) := rclPx_le_centralizer sp hz
  set z' : Subgroup.centralizer ({x} : Set 𝒞[K, σ]) := ⟨z, hzx⟩ with hz'
  have hzQ : rclPsi sp z' ∈ rclQ F i := (mem_rclPx_iff sp hzx).1 hz
  have hψ : Function.Injective (rclPsi sp) := d4QPsi_injective triEmb_injective F.g0 sp.c x
  have hcomm : ∀ u ∈ rclQ F i, rclPsi sp z' * u = u * rclPsi sp z' := by
    intro u hu
    obtain ⟨w, hw⟩ := hQψ hu
    have hwP : (w : 𝒞[K, σ]) ∈ rclPx sp := (mem_rclPx_iff sp w.2).2 (by
      rw [show (⟨(w : 𝒞[K, σ]), w.2⟩ : Subgroup.centralizer ({x} : Set 𝒞[K, σ])) = w from rfl,
        hw]
      exact hu)
    have h1 := Subgroup.mem_centralizer_iff.1 hzc _ hwP
    have h2 : w * z' = z' * w := Subtype.ext h1
    rw [← hw, ← map_mul, ← map_mul, h2]
  have hzT := hcentψ z' hcomm
  have hzC : rclPsi sp z' ∈ Subgroup.centralizer
      ((rootSpan TwistTag.D4.tag L (d4Sigma i) : Subgroup _) : Set _) :=
    (Subgroup.mem_inf.1 hzT).2
  have hzR : rclPsi sp z' ∈ D.ρ.range := by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hzQ).1
  obtain ⟨X, hX⟩ := hzR
  have hXc : X ∈ Subgroup.center SL(3, L) := by
    rw [Subgroup.mem_center_iff]
    intro Y
    apply D.frame.injective
    have hY : D.ρ Y ∈ rootSpan TwistTag.D4.tag L (d4Sigma i) := by
      rw [← hrange]
      exact ⟨Y, rfl⟩
    rw [map_mul, map_mul, hX]
    exact Subgroup.mem_centralizer_iff.1 hzC _ hY
  obtain ⟨r, hr3, hrX⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hXc
  rw [Fintype.card_fin] at hr3
  have hX3 : X ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrX, ← map_pow, hr3, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have h3 : rclPsi sp (z' ^ 3) = rclPsi sp 1 := by
    rw [map_pow, ← hX, ← map_pow, hX3, map_one, map_one]
  have h4 : z' ^ 3 = 1 := hψ h3
  exact congrArg Subtype.val h4

end Frame

section Split

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem rcy_card_sylow (F : RclFrame ℓ f K σ ε p L) [Fact p.Prime] (S : Sylow p 𝒞[K, σ]) :
    Nat.card (S : Subgroup 𝒞[K, σ]) =
      ordProj[p] (d4T36d ε (ℓ ^ f)) * ordProj[p] (d4T36d ε (ℓ ^ f)) := by
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := F.hf; omega) hℓ.one_lt
  have hd0 : d4T36d ε (ℓ ^ f) ≠ 0 := (d4T36d_odd F.hε (by omega)).pos.ne'
  have hC := (triality_both_orientations_exact_finite_order ℓ f hℓ F.hf K F.hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact F.hσ c)).1
  rw [S.card_eq_multiplicity, hC, d4T36_ordProj F.hε F.hp F.hp3 hq2 F.hpd,
    Nat.factorization_mul hd0 hd0, Finsupp.add_apply, pow_add]

theorem rcy_sylow_split (F : RclFrame ℓ f K σ ε p L) [Fact p.Prime] (S : Sylow p 𝒞[K, σ])
    {c : 𝒞[K, σ]} (hc : RclConj F S c) {x : 𝒞[K, σ]} {i : Fin 4} (sp : RclSpecial F x i)
    (hspc : sp.c = c) (hxS : x ∈ (S : Subgroup 𝒞[K, σ])) :
    IsCyclic ↥((S : Subgroup 𝒞[K, σ]) ⊓ rclPx sp) ∧
      (S : Subgroup 𝒞[K, σ]) ⊓ rclPx sp ≠ ⊥ ∧
      ¬ p ∣ ((S : Subgroup 𝒞[K, σ]) ⊓ rclPx sp).relIndex (rclPx sp) ∧
      (S : Subgroup 𝒞[K, σ]) ⊓ rclPx sp ⊓ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]) = ⊥ ∧
      x ∈ (S : Subgroup 𝒞[K, σ]) ⊓ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]) ∧
      ∀ s ∈ (S : Subgroup 𝒞[K, σ]), ∃ a ∈ (S : Subgroup 𝒞[K, σ]) ⊓ rclPx sp,
        ∃ b ∈ (S : Subgroup 𝒞[K, σ]) ⊓ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]),
          s = a * b := by
  classical
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := F.hf; omega) hℓ.one_lt
  set T : Subgroup 𝒞[K, σ] := (S : Subgroup 𝒞[K, σ]) with hT
  set P := rclPx sp with hP
  set Z := Subgroup.centralizer (P : Set 𝒞[K, σ]) with hZ
  set d := d4T36d ε (ℓ ^ f) with hd
  set pa := ordProj[p] d with hpa
  have hd0 : d ≠ 0 := (d4T36d_odd F.hε (by omega)).pos.ne'
  obtain ⟨β, hβ, hβfix, hβinj, κ, hκ, hκd⟩ := rcy_coord F hc
  have hTp : IsPGroup p T := S.isPGroup'
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h := hβinj (show β (⟨a, ha⟩ * ⟨b, hb⟩) = β (⟨b, hb⟩ * ⟨a, ha⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have hTx : T ≤ Subgroup.centralizer ({x} : Set 𝒞[K, σ]) := fun s hs => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h = x := hh
    rw [hh']
    exact hcomm x hxS s hs
  have hord : ∀ s ∈ T, ∃ k, orderOf s = p ^ k := fun s hs => by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hTp) ⟨s, hs⟩
    exact ⟨k, (Subgroup.orderOf_coe (⟨s, hs⟩ : T)).trans hk⟩
  have hexp : ∀ s ∈ T, s ^ pa = 1 := by
    intro s hs
    have hsd : (⟨s, hs⟩ : T) ^ d = 1 := hκ (by
      rw [map_pow, map_one]
      exact Prod.ext (hκd _).1 (hκd _).2)
    have hsd' : s ^ d = 1 := congrArg Subtype.val hsd
    obtain ⟨k, hk⟩ := hord s hs
    have h1 : p ^ k ∣ d := hk ▸ orderOf_dvd_of_pow_eq_one hsd'
    have h2 : k ≤ d.factorization p := (hp.pow_dvd_iff_le_factorization hd0).1 h1
    have h3 : orderOf s ∣ pa := by
      rw [hk]
      exact pow_dvd_pow p h2
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  have hAZ : T ⊓ P ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h3 := rcy_pow_three_of_mem_center F sp hz.1.2 hz.2
    obtain ⟨k, hk⟩ := hord z hz.1.1
    have h4 : p ^ k ∣ 3 := hk ▸ orderOf_dvd_of_pow_eq_one h3
    have hk0 : k = 0 := by
      by_contra hk0
      have h5 : p ∣ 3 := (dvd_pow_self p hk0).trans h4
      have := Nat.le_of_dvd (by norm_num) h5
      have := F.hp3
      omega
    rw [hk0, pow_zero] at hk
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.1 hk
  have hxZ : x ∈ T ⊓ Z := by
    refine ⟨hxS, ?_⟩
    show x ∈ Subgroup.centralizer (P : Set 𝒞[K, σ])
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.1 (rclPx_le_centralizer sp hu) x rfl).symm
  have hidx : ¬ p ∣ (T ⊓ P).relIndex P :=
    rcy_not_dvd_relIndex hTx (rclPx_le_centralizer sp) (fun g hg u hu => rclPx_normal sp hg hu)
      S.not_dvd_index
  have hα : trialityU i ∈ d4Sigma i := mem_trialitySigma.2 List.mem_cons_self
  let χ : T →* Lˣ := MonoidHom.mk' (fun s => rootChar (β s) (trialityU i)) (fun a b => by
    rw [map_mul]
    exact CTTorus.rootChar_mul _ _ _)
  have hkerZ : ∀ s : T, χ s = 1 → (s : 𝒞[K, σ]) ∈ Z := by
    intro s hs
    exact rcy_mem_centralizer_of_rootChar F sp (hTx s.2) (by rw [hβ s, hspc]) (hβfix s) hα hs
  let χA : ↥(T ⊓ P) →* Lˣ := χ.comp (Subgroup.inclusion inf_le_left)
  have hχA : Function.Injective χA := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hkerZ _ ha
    have h2 : (a : 𝒞[K, σ]) ∈ T ⊓ P ⊓ Z := ⟨a.2, h1⟩
    rw [hAZ, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hcyc : IsCyclic ↥(T ⊓ P) := rcy_isCyclic_of_injective χA hχA
  have hpa0 : 0 < pa := Nat.ordProj_pos d p
  have hTc : Nat.card T = pa * pa := rcy_card_sylow F S
  have hrange : Nat.card χ.range ≤ pa := by
    have : NeZero pa := ⟨hpa0.ne'⟩
    have hle : χ.range ≤ rootsOfUnity pa L := by
      rintro _ ⟨s, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow]
      have : s ^ pa = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hexp s s.2)
      rw [this, map_one]
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity L pa)
  have hker : pa ≤ Nat.card χ.ker := by
    have h := Subgroup.card_ker_mul_card_range χ
    rw [hTc] at h
    by_contra hlt
    have hlt' := Nat.lt_of_not_ge hlt
    nlinarith
  have hBc : pa ≤ Nat.card ↥(T ⊓ Z) := by
    let ι : χ.ker → ↥(T ⊓ Z) := fun k => ⟨((k : T) : 𝒞[K, σ]), (k : T).2, hkerZ _ k.2⟩
    have hι : Function.Injective ι := by
      intro a b h
      have h1 : ((a : T) : 𝒞[K, σ]) = ((b : T) : 𝒞[K, σ]) :=
        congrArg (fun z : ↥(T ⊓ Z) => (z : 𝒞[K, σ])) h
      exact Subtype.ext (Subtype.ext h1)
    exact hker.trans (Nat.card_le_card_of_injective ι hι)
  have hAc : Nat.card ↥(T ⊓ P) = pa := by
    have hrel := Subgroup.relIndex_mul_card T P
    rw [← Subgroup.inf_relIndex_right] at hrel
    obtain ⟨m, hm⟩ := (hTp.to_inf_left (K := P)).exists_card_eq
    have hPp : ordProj[p] (Nat.card P) = pa := by
      rw [hP, card_rclPx]
      exact rcy_ordProj_card F.hε hp F.hp3 hq2 F.hpd (rcl_card_rclQ F i)
    have hr0 : (T ⊓ P).relIndex P ≠ 0 := fun h0 => hidx (h0 ▸ dvd_zero p)
    rw [← hrel, hm, Nat.factorization_mul hr0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, hp.factorization_pow, Finsupp.single_eq_same,
      zero_add] at hPp
    rw [hm, hPp]
  have hsplit : ∀ s ∈ T, ∃ a ∈ T ⊓ P, ∃ b ∈ T ⊓ Z, s = a * b := by
    let μ : ↥(T ⊓ P) × ↥(T ⊓ Z) → T := fun ab => ⟨ab.1 * ab.2, T.mul_mem ab.1.2.1 ab.2.2.1⟩
    have hμ : Function.Injective μ := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : 𝒞[K, σ]) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : 𝒞[K, σ])⁻¹ * a = b' * (b : 𝒞[K, σ])⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_assoc, mul_inv_cancel, mul_one]
      have h3 : (a' : 𝒞[K, σ])⁻¹ * a ∈ T ⊓ P ⊓ Z := by
        refine ⟨(T ⊓ P).mul_mem ((T ⊓ P).inv_mem a'.2) a.2, ?_⟩
        rw [h2]
        exact Z.mul_mem b'.2.2 (Z.inv_mem b.2.2)
      rw [hAZ, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : (b : 𝒞[K, σ]) = b' := by
        rw [← h3] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
    have hcard : Nat.card T ≤ Nat.card (↥(T ⊓ P) × ↥(T ⊓ Z)) := by
      rw [Nat.card_prod, hAc, hTc]
      exact Nat.mul_le_mul_left pa hBc
    have hbij := hμ.bijective_of_nat_card_le hcard
    intro s hs
    obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨s, hs⟩
    exact ⟨a, a.2, b, b.2, (congrArg Subtype.val hab).symm⟩
  refine ⟨hcyc, ?_, hidx, hAZ, hxZ, hsplit⟩
  intro hbot
  rw [hbot, Subgroup.card_bot] at hAc
  have hpd : p ∣ d := by
    have h := F.hpd
    rw [← d4T36d_cast F.hε (by omega : 1 ≤ ℓ ^ f)] at h
    exact_mod_cast h
  have h1 : 1 ≤ d.factorization p := (hp.dvd_iff_one_le_factorization hd0).1 hpd
  have h2 : p ∣ pa := by
    rw [hpa]
    exact (dvd_pow_self p (by omega)).trans (pow_dvd_pow p h1) |>.trans (by rfl)
  rw [← hAc] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem rcy_perfect_rclPx (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) : ⁅rclPx sp, rclPx sp⁆ = rclPx sp := by
  obtain ⟨-, hq, -, -, -, hQψ, -, -⟩ := rcl_psi_props F sp
  have hψ : Function.Injective (rclPsi sp) := d4QPsi_injective triEmb_injective F.g0 sp.c x
  set W := (rclQ F i).comap (rclPsi sp) with hW
  have hWQ : W.map (rclPsi sp) = rclQ F i := by
    rw [hW, Subgroup.map_comap_eq, inf_eq_right.2 hQψ]
  let e1 : ↥(rclPx sp) ≃* ↥W :=
    (Subgroup.equivMapOfInjective W _ (Subgroup.subtype_injective _)).symm
  let e2 : ↥W ≃* ↥(W.map (rclPsi sp)) := Subgroup.equivMapOfInjective W _ hψ
  let e : ↥(rclPx sp) ≃* ↥(rclQ F i) := (e1.trans e2).trans (MulEquiv.subgroupCongr hWQ)
  have : Group.IsPerfect ↥(rclQ F i) := hq.1
  have hperf : Group.IsPerfect ↥(rclPx sp) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
    Subgroup.range_subtype]

theorem rcy_exists_normalizer_line (F : RclFrame ℓ f K σ ε p L) [Fact p.Prime]
    (S : Sylow p 𝒞[K, σ]) {c : 𝒞[K, σ]} (hc : RclConj F S c) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) (hspc : sp.c = c) (hxS : x ∈ (S : Subgroup 𝒞[K, σ]))
    {E : Subgroup 𝒞[K, σ]} (hES : E ≤ S) (hEp : ∀ y ∈ E, y ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ∃ g ∈ rclPx sp, g ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]) ∧
      ∀ ℓ' : Subgroup 𝒞[K, σ], ℓ' ≤ E → Nat.card ℓ' = p → (∀ y ∈ ℓ', g * y * g⁻¹ ∈ ℓ') →
        ℓ' = E ⊓ rclPx sp ∨ ℓ' = E ⊓ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]) := by
  obtain ⟨hcyc, hP1, hidx, hAZ, hxZ, hsplit⟩ := rcy_sylow_split F S hc sp hspc hxS
  obtain ⟨-, -, -, -, κ, hκ, -⟩ := rcy_coord F hc
  have hΩ : ∀ s ∈ (S : Subgroup 𝒞[K, σ]), s ^ p = 1 → s ∈ E := fun s hs hsp =>
    rcy_mem_of_pow_eq_one F.hp κ hκ hES hEp hEc hs hsp
  have hZ1 : (S : Subgroup 𝒞[K, σ]) ⊓ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]) ≠ ⊥ := by
    intro h
    have hx := hxZ
    rw [h, Subgroup.mem_bot] at hx
    have hord := sp.hx
    rw [hx, orderOf_one] at hord
    have := F.hp3
    omega
  exact rcn_exists_normalizer_line (by have := F.hp3; omega) S.isPGroup' hES hEp hEc hΩ
    (fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a ha) (rcy_perfect_rclPx F sp) hidx hcyc
    hP1 hZ1 hAZ hsplit

end Split

end CFSG.RankThree.PartOne.D4RC
