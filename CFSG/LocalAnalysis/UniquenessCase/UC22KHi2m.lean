module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sq
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ye

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Open.StatedAPI
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x
open scoped Matrix commutatorElement

namespace P22k2

section KleinMod

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X} {A B : Submodule (ZMod 2) V} {F : Type} [Field F]

structure KleinNat (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) (A B : Submodule (ZMod 2) V) (F : Type)
    [Field F] where
  φ : ↥Y ≃* ↥(StatedSL 2 F)
  ψ : V →+ (Fin 2 → F)
  invA : ∀ a ∈ Y, ∀ x ∈ A, ρ a x ∈ A
  BA : B ≤ A
  ψB : ∀ x ∈ B, ψ x = 0
  memB : ∀ x ∈ A, ψ x = 0 → x ∈ B
  surj : ∀ y : Fin 2 → F, ∃ x ∈ A, ψ x = y
  equi : ∀ (h : ↥Y) (x : V), x ∈ A →
    ψ (ρ (h : X) x) = ((φ h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ ψ x

theorem KleinNat.exists_of_secNat (h : CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.SecNat ρ Y A B (StatedSL 2 F)) :
    Nonempty (KleinNat ρ Y A B F) := by
  obtain ⟨hinvA, -, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := h
  exact ⟨⟨φ, ψ, hinvA, hBA, hψB, hψA, hψs, hψφ⟩⟩

variable (K : KleinNat ρ Y A B F)

include K

@[expose] def kleinW0 (ρ : Representation (ZMod 2) X V) (A : Submodule (ZMod 2) V) (k : X) :
    Submodule (ZMod 2) V := commOn ρ (Subgroup.zpowers k) A

variable {k : X}

theorem KleinNat.W0_le (hk : k ∈ Y) : kleinW0 ρ A k ≤ A :=
  commOn_le_of_invariant fun a ha u hu => K.invA a (Subgroup.zpowers_le.2 hk ha) u hu

theorem KleinNat.W0_sum_eq_zero (hk3 : orderOf k = 3) :
    ∀ x ∈ kleinW0 ρ A k, x + ρ k x + ρ k (ρ k x) = 0 := by
  have hkk : k * k * k = 1 := by
    have : k ^ 3 = 1 := hk3 ▸ pow_orderOf_eq_one k
    simpa [pow_succ] using this
  have h3 : ∀ v : V, ρ k (ρ k (ρ k v)) = v := fun v => by
    have := congrArg (fun f : V →ₗ[ZMod 2] V => f v) (show ρ (k * k * k) = ρ 1 by rw [hkk])
    simpa [map_mul] using this
  set N : V →ₗ[ZMod 2] V := LinearMap.id + ρ k + (ρ k).comp (ρ k) with hN
  have hNapp : ∀ v, N v = v + ρ k v + ρ k (ρ k v) := fun v => rfl
  have hle : kleinW0 ρ A k ≤ LinearMap.ker N := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨a, ha, u, hu, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hNapp]
    classical
    have hfin : IsOfFinOrder k := orderOf_pos_iff.1 (by omega)
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, hk3] at ha
    simp only [Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨n, hn, rfl⟩ := ha
    interval_cases n
    · simp
    · simp only [pow_one, map_sub]
      rw [h3 u]
      abel
    · simp only [pow_two, map_mul, Module.End.mul_apply, map_sub, map_add]
      have e1 : ρ k (ρ k (ρ k (ρ k u))) = ρ k u := by rw [h3 (ρ k u)]
      have e2 := h3 u
      calc _ = (ρ k (ρ k u) - u) + (ρ k (ρ k (ρ k u)) - ρ k u) +
            (ρ k (ρ k (ρ k (ρ k u))) - ρ k (ρ k u)) := by simp [map_sub]
        _ = 0 := by rw [e1, e2]; abel
  intro x hx
  exact hle hx

theorem KleinNat.W0_inf_B (hk3 : orderOf k = 3) (hBfix : ∀ b ∈ B, ρ k b = b) : kleinW0 ρ A k ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx0, hxB⟩
  have h := K.W0_sum_eq_zero hk3 x hx0
  rw [hBfix x hxB, hBfix x hxB] at h
  have h2 : x + x = 0 := by
    rw [← two_smul (ZMod 2) x]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_smul]
  rw [h2, zero_add] at h
  exact (Submodule.mem_bot _).2 h

theorem KleinNat.g3 (hk : k ∈ Y) (hk3 : orderOf k = 3) :
    (K.φ ⟨k, hk⟩) ^ 3 = 1 ∧ K.φ ⟨k, hk⟩ ≠ 1 := by
  have ho : orderOf (K.φ ⟨k, hk⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hk3
  refine ⟨?_, fun h => ?_⟩
  · rw [← ho]
    exact pow_orderOf_eq_one _
  · rw [h, orderOf_one] at ho
    omega

variable [Finite F]

theorem KleinNat.psi_W0_surj [CharP F 2] (hk : k ∈ Y) (hk3 : orderOf k = 3) (y : Fin 2 → F) :
    ∃ x ∈ kleinW0 ρ A k, K.ψ x = y := by
  obtain ⟨hg3, hg1⟩ := K.g3 hk hk3
  obtain ⟨w, hw⟩ := P22sq.exists_mulVec_sub_eq hg3 hg1 y
  obtain ⟨u, huA, huψ⟩ := K.surj w
  refine ⟨ρ k u - u, sub_mem_commOn (Subgroup.mem_zpowers k) huA, ?_⟩
  rw [map_sub, K.equi ⟨k, hk⟩ u huA, huψ]
  exact hw

theorem KleinNat.psi_inj_W0 (hk : k ∈ Y) (hk3 : orderOf k = 3) (hBfix : ∀ b ∈ B, ρ k b = b) {x : V}
    (hx : x ∈ kleinW0 ρ A k) (h0 : K.ψ x = 0) : x = 0 := by
  have hxB : x ∈ B := K.memB x (K.W0_le hk hx) h0
  have hmem : x ∈ kleinW0 ρ A k ⊓ B := ⟨hx, hxB⟩
  rw [K.W0_inf_B hk3 hBfix] at hmem
  exact (Submodule.mem_bot _).1 hmem

theorem KleinNat.card_W0 [CharP F 2] (hF : Nat.card F = 2) (hk : k ∈ Y) (hk3 : orderOf k = 3)
    (hBfix : ∀ b ∈ B, ρ k b = b) : Nat.card ↥(kleinW0 ρ A k) = 4 := by
  have hbij : Function.Bijective (fun x : ↥(kleinW0 ρ A k) => K.ψ (x : V)) := by
    constructor
    · intro x x' h
      apply Subtype.ext
      have h1 : K.ψ ((x : V) - x') = 0 := by rw [map_sub]; exact sub_eq_zero.2 h
      exact sub_eq_zero.1 (K.psi_inj_W0 hk hk3 hBfix (Submodule.sub_mem _ x.2 x'.2) h1)
    · intro y
      obtain ⟨x, hx, hxy⟩ := K.psi_W0_surj hk hk3 y
      exact ⟨⟨x, hx⟩, hxy⟩
  calc Nat.card ↥(kleinW0 ρ A k) = Nat.card (Fin 2 → F) := Nat.card_congr (Equiv.ofBijective _ hbij)
    _ = 4 := by
        rw [Nat.card_pi, Fin.prod_univ_two, hF]
        norm_num

theorem KleinNat.A_le_sup [CharP F 2] (hk : k ∈ Y) (hk3 : orderOf k = 3) : A ≤ kleinW0 ρ A k ⊔ B := by
  intro u hu
  obtain ⟨w, hw, hwψ⟩ := K.psi_W0_surj hk hk3 (K.ψ u)
  have hdiff : u - w ∈ B :=
    K.memB _ (A.sub_mem hu (K.W0_le hk hw)) (by rw [map_sub, hwψ, sub_self])
  have e : u = w + (u - w) := by abel
  rw [e]
  exact Submodule.add_mem_sup hw hdiff

theorem KleinNat.faithful_W0 [CharP F 2] (hk : k ∈ Y) (hk3 : orderOf k = 3) {a : X} (ha : a ∈ Y)
    (h : ∀ x ∈ kleinW0 ρ A k, ρ a x = x) : a = 1 := by
  have h1 : K.φ ⟨a, ha⟩ = 1 := by
    apply sl2_eq_one_of_fix
    intro y
    obtain ⟨x, hx, rfl⟩ := K.psi_W0_surj hk hk3 y
    have := K.equi ⟨a, ha⟩ x (K.W0_le hk hx)
    rw [← this, h x hx]
  have := K.φ.injective (h1.trans (map_one K.φ).symm)
  exact congrArg Subtype.val this

theorem KleinNat.fixfree_W0 [CharP F 2] (hk : k ∈ Y) (hk3 : orderOf k = 3) (hBfix : ∀ b ∈ B, ρ k b = b) {a : X}
    (ha : a ∈ Y) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) {x : V} (hx : x ∈ kleinW0 ρ A k) (hfix : ρ a x = x) : x = 0 := by
  have hψ : ((K.φ ⟨a, ha⟩ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ K.ψ x = K.ψ x := by
    rw [← K.equi ⟨a, ha⟩ x (K.W0_le hk hx), hfix]
  have hg3 : (K.φ ⟨a, ha⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hg1 : K.φ ⟨a, ha⟩ ≠ 1 := fun h =>
    ha1 (congrArg Subtype.val (K.φ.injective (h.trans (map_one K.φ).symm)))
  exact K.psi_inj_W0 hk hk3 hBfix hx (P22sq.eq_zero_of_mulVec_eq_self hg3 hg1 hψ)

theorem KleinNat.commOn_le [CharP F 2] {Q : Subgroup X} (hBQ : ∀ q ∈ Q, ∀ b ∈ B, ρ q b = b) (hk : k ∈ Y)
    (hk3 : orderOf k = 3) : commOn ρ Q A ≤ commOn ρ Q (kleinW0 ρ A k) := by
  rw [commOn_le_iff]
  intro a ha u hu
  obtain ⟨w, hw, b, hb, rfl⟩ := Submodule.mem_sup.1 (K.A_le_sup hk hk3 hu)
  have e : ρ a (w + b) - (w + b) = ρ a w - w := by
    rw [map_add, hBQ a ha b hb]
    abel
  rw [e]
  exact sub_mem_commOn ha hw

theorem KleinNat.W0_inv {g : X} (hg : ∀ a ∈ Subgroup.zpowers k, g * a * g⁻¹ ∈ Subgroup.zpowers k)
    (hgA : ∀ u ∈ A, ρ g u ∈ A) : ∀ w ∈ kleinW0 ρ A k, ρ g w ∈ kleinW0 ρ A k :=
  commOn_invariant hg hgA

end KleinMod

section KleinGroup

variable {G : Type} [Group G] [Finite G]

theorem mk_conj_mem (D : Data G) {Y : Subgroup (MBar D.M D.U)} (hY : Y ≤ mbarImage D.M D.U (proofN D)) {x : G}
    (hxM : x ∈ D.M) (hxN : x ∈ normalizer (preN D Y : Set G)) {y : MBar D.M D.U} (hy : y ∈ Y) :
    (QuotientGroup.mk ⟨x, hxM⟩ : MBar D.M D.U) * y * (QuotientGroup.mk ⟨x, hxM⟩ : MBar D.M D.U)⁻¹ ∈ Y := by
  have hy' : y ∈ mbarImage D.M D.U (preN D Y) := by rw [mbarImage_preN D hY]; exact hy
  obtain ⟨n, hn, rfl⟩ := hy'
  have hnN : (n : G) ∈ preN D Y := hn
  have hcN : x * (n : G) * x⁻¹ ∈ preN D Y := (Subgroup.mem_normalizer_iff.1 hxN _).1 hnN
  have hcM : x * (n : G) * x⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hxM n.2) (D.M.inv_mem hxM)
  have hmem : (QuotientGroup.mk ⟨x * (n : G) * x⁻¹, hcM⟩ : MBar D.M D.U) ∈ mbarImage D.M D.U (preN D Y) :=
    ⟨⟨_, hcM⟩, hcN, rfl⟩
  rw [mbarImage_preN D hY] at hmem
  convert hmem using 1
  change _ = QuotientGroup.mk ((⟨x, hxM⟩ : ↥D.M) * n * (⟨x, hxM⟩ : ↥D.M)⁻¹)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rfl

theorem sq_mem_of_card {X : Type} [Group X] {Y K₃ : Subgroup X} (hK : K₃ ≤ Y) (h6 : Nat.card Y = 6)
    (h3 : Nat.card K₃ = 3) {z : X} (hz : z ∈ Y) : z ^ 2 ∈ K₃ := by
  have hcard : Nat.card (K₃.subgroupOf Y) = 3 := by
    rw [← h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hidx : (K₃.subgroupOf Y).index = 2 := by
    have h := (K₃.subgroupOf Y).card_mul_index
    rw [hcard, h6] at h
    omega
  have := Subgroup.sq_mem_of_index_two hidx (⟨z, hz⟩ : ↥Y)
  exact this

theorem mem_of_pow_three {X : Type} [Group X] {Y K₃ : Subgroup X} (hK : K₃ ≤ Y) (h6 : Nat.card Y = 6)
    (h3 : Nat.card K₃ = 3) {z : X} (hz : z ∈ Y) (hz3 : z ^ 3 = 1) : z ∈ K₃ := by
  have h1 : z = (z ^ 2) ^ 2 := by
    calc z = z ^ 3 * z := by rw [hz3, one_mul]
      _ = (z ^ 2) ^ 2 := by group
  rw [h1]
  exact K₃.pow_mem (sq_mem_of_card hK h6 h3 hz) 2

end KleinGroup

section KleinMain

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_commutator (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D)) {k : MBar D.M D.U} (hk : k ∈ ⁅Y, Y⁆) :
    ∃ y ∈ ⁅preN D Y, preN D Y⁆, ∃ hy : y ∈ D.M, (QuotientGroup.mk ⟨y, hy⟩ : MBar D.M D.U) = k := by
  have hYim : Y = ((preN D Y).subgroupOf D.M).map (QuotientGroup.mk' (kerAct D.M D.U).normalCore) :=
    (mbarImage_preN D hY).symm
  rw [hYim, ← Subgroup.map_commutator] at hk
  obtain ⟨y', hy', rfl⟩ := hk
  refine ⟨(y' : G), ?_, y'.2, rfl⟩
  have h := Subgroup.mem_map_of_mem D.M.subtype hy'
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (preN_le_M D Y)] at h
  exact h

structure KleinPkg (D : Data G) (Y : Subgroup (MBar D.M D.U)) (V₀ : Subgroup G)
    (K₃ : Subgroup (MBar D.M D.U)) : Prop where
  le_Ii : V₀ ≤ proofIi D (preN D Y)
  elem : IsElemAbelian 2 V₀
  card : Nat.card V₀ = 4
  norm : ∀ x ∈ D.M, x ∈ normalizer (preN D Y : Set G) → x ∈ normalizer (V₀ : Set G)
  faith : ∀ x ∈ preN D Y, x ∈ centralizer (V₀ : Set G) → x ∈ centralizer (D.U : Set G)
  K3_le : K₃ ≤ Y
  K3_card : Nat.card K₃ = 3
  K3_cube : ∀ z ∈ Y, z ^ 3 = 1 → z ∈ K₃
  K3_sq : ∀ z ∈ Y, z ^ 2 ∈ K₃
  K3_pcore : K₃ ≤ pCoreOf 3 (mbarImage D.M D.U (proofN D))
  gen : ∃ y ∈ ⁅preN D Y, preN D Y⁆, ∃ hy : y ∈ D.M,
    (QuotientGroup.mk ⟨y, hy⟩ : MBar D.M D.U) ∈ K₃ ∧ (QuotientGroup.mk ⟨y, hy⟩ : MBar D.M D.U) ≠ 1
  ord3 : ∀ x (hx : x ∈ D.M), (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) ∈ K₃ →
    (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) ≠ 1 →
      x ∉ centralizer (V₀ : Set G) ∧ x ^ 3 ∈ centralizer (V₀ : Set G)
  fixfree : ∀ x (hx : x ∈ D.M), (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) ∈ K₃ →
    (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) ≠ 1 → ∀ v ∈ V₀, x * v = v * x → v = 1
  hat : ⁅V₀, jOf D.T⁆ = proofEiHat D (preN D Y)
  hat_ne : ⁅V₀, jOf D.T⁆ ≠ ⊥
  nat : ∀ L : Subgroup G, L ≤ D.M → L ≤ preMbar D K₃ → L ≤ normalizer (V₀ : Set G) →
    (∃ l ∈ L, l ∉ centralizer (V₀ : Set G) ∧ l ^ 3 ∈ centralizer (V₀ : Set G)) →
      CFSG.Quasithin.IsNaturalL2Prime 1 L V₀

theorem bsub_bsup_eq {V : Subgroup G} {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (S : Submodule (ZMod 2) Vmod) : bsub e (bsup e S) = S := by
  ext x
  rw [mem_bsub, iota_mem_bsup]

theorem uc22k_klein_exists (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) (i : Fin m) (hS3 : IsL2Ev ↥(Nb i) 1) :
    ∃ (V₀ : Subgroup G) (K₃ : Subgroup (MBar D.M D.U)), KleinPkg D (Nb i) V₀ K₃ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  set Nbar : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (proofN D) with hNbar
  set Y : Subgroup (MBar D.M D.U) := Nb i with hYdef
  have hYN : Y ≤ Nbar := d.le i
  obtain ⟨n, hn, F, _, _, hF, hsec⟩ := d.nat i
  obtain ⟨K⟩ := KleinNat.exists_of_secNat hsec
  have hY6 : Nat.card Y = 6 := P22y.card_of_isL2Ev_one hS3
  have hq : Nat.card F * (Nat.card F ^ 2 - 1) = 6 := by
    rw [← card_statedSL_two, ← Nat.card_congr K.φ.toEquiv]
    exact hY6
  have hF2 : Nat.card F = 2 := by
    have hdvd : Nat.card F ∣ 6 := ⟨_, hq.symm⟩
    have hle : Nat.card F ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ Nat.card F := by
      rw [hF]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    interval_cases h : Nat.card F
    · rfl
    all_goals (exfalso; norm_num at hq)
  haveI : CharP F 2 := P22y.charP_two_of_card (n := 1) (by rw [hF2, pow_one])
  have hZ : Subgroup.center ↥Y = ⊥ := P22y.center_eq_bot_of_isL2Ev hS3
  have hcom3 : Nat.card ↥⁅Y, Y⁆ = 3 := P22y.card_commutator_factor Y hY6 hZ
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card ↥⁅Y, Y⁆ by rw [hcom3])
  set k : MBar D.M D.U := (g : MBar D.M D.U) with hkdef
  have hk3 : orderOf k = 3 := by rw [hkdef, Subgroup.orderOf_coe, hg]
  have hkYY : k ∈ ⁅Y, Y⁆ := g.2
  have hkY : k ∈ Y := P22y.commutator_self_le Y hkYY
  have hkkk : k ^ 3 = 1 := hk3 ▸ pow_orderOf_eq_one k
  set K₃ : Subgroup (MBar D.M D.U) := Subgroup.zpowers k with hK₃
  have hK₃Y : K₃ ≤ Y := Subgroup.zpowers_le.2 hkY
  have hK₃card : Nat.card K₃ = 3 := by rw [hK₃, Nat.card_zpowers, hk3]
  have hK₃pow : ∀ z ∈ K₃, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkkk, one_zpow]
  set A : Submodule (ZMod 2) Umod := natIi ρ Nbar Y with hA
  set B : Submodule (ZMod 2) Umod := natIi ρ Nbar Y ⊓ natC ρ Nbar with hB
  have hBfix : ∀ b ∈ B, ρ k b = b := fun b hb => natC_fix (hYN hkY) hb.2
  set W₀ : Submodule (ZMod 2) Umod := kleinW0 ρ A k with hW₀
  set V₀ : Subgroup G := bsup e W₀ with hV₀
  have hW0A : W₀ ≤ A := K.W0_le hkY
  have hV₀U : V₀ ≤ D.U := bsup_le_V e W₀
  have hbsub : bsub e V₀ = W₀ := bsub_bsup_eq e W₀
  have hIi : bsub e (proofIi D (preN D Y)) = A := bsub_proofIi D e ρ hc hYN
  have hmemV₀ : ∀ v ∈ V₀, ∃ u ∈ W₀, iota e u = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := exists_iota e (hV₀U hv)
    have hu : u ∈ bsub e V₀ := mem_bsub.2 hv
    rw [hbsub] at hu
    exact ⟨u, hu, rfl⟩
  have hiotaV₀ : ∀ u ∈ W₀, iota e u ∈ V₀ := fun u hu => iota_mem_bsup.2 hu
  have hcentW0 : ∀ (x : G) (hx : x ∈ D.M), (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) ∈ Y →
      x ∈ centralizer (V₀ : Set G) → (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) = 1 := by
    intro x hx hxY hxC
    refine K.faithful_W0 hkY hk3 hxY fun w hw => ?_
    apply iota_injective e
    rw [iota_rho hV e ρ hc ⟨x, hx⟩ w]
    have := Subgroup.mem_centralizer_iff.1 hxC _ (hiotaV₀ w hw)
    calc x * iota e w * x⁻¹ = (iota e w * x) * x⁻¹ := by rw [← this]
      _ = iota e w := by group
  have hmk_one : ∀ (x : G) (hx : x ∈ D.M), (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) = 1 →
      x ∈ centralizer (V₀ : Set G) := fun x hx h =>
    Subgroup.centralizer_le hV₀U ((uc22br_gt_mk_eq_one_iff hV ⟨x, hx⟩).1 h)
  have hconj : ∀ (x : G) (hx : x ∈ D.M), x ∈ normalizer (preN D Y : Set G) →
      ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀ := by
    intro x hx hxN v hv
    obtain ⟨u, hu, rfl⟩ := hmemV₀ v hv
    have hgY : ∀ a ∈ Y, (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) * a *
        (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U)⁻¹ ∈ Y := fun a ha => mk_conj_mem D hYN hx hxN ha
    have hg : ∀ a ∈ Subgroup.zpowers k, (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) * a *
        (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U)⁻¹ ∈ Subgroup.zpowers k := by
      intro a ha
      have haY : a ∈ Y := hK₃Y ha
      refine mem_of_pow_three hK₃Y hY6 hK₃card (hgY a haY) ?_
      rw [conj_pow, hK₃pow a ha]
      simp
    have hI : ∀ w ∈ natI ρ Nbar, ρ (QuotientGroup.mk ⟨x, hx⟩) w ∈ natI ρ Nbar :=
      commOn_invariant (A := Nbar) (U := ⊤) (fun a ha => (uc22p22ya_nbar_normal D).conj_mem a ha _)
        (fun w _ => trivial)
    have hgA : ∀ w ∈ A, ρ (QuotientGroup.mk ⟨x, hx⟩) w ∈ A := commOn_invariant (A := Y) (U := natI ρ Nbar) hgY hI
    have hu' := K.W0_inv hg hgA u hu
    have := iota_rho hV e ρ hc ⟨x, hx⟩ u
    rw [← this]
    exact hiotaV₀ _ hu'
  have hK3sq : ∀ z ∈ Y, z ^ 2 ∈ K₃ := fun z hz => sq_mem_of_card hK₃Y hY6 hK₃card hz
  have hK3cube : ∀ z ∈ Y, z ^ 3 = 1 → z ∈ K₃ := fun z hz hz3 =>
    mem_of_pow_three hK₃Y hY6 hK₃card hz hz3
  have hJM : jOf D.T ≤ D.M := (uc22p22e_jOf_le_self D.T).trans D.sylowM.le
  have hat : ⁅V₀, jOf D.T⁆ = proofEiHat D (preN D Y) := by
    obtain ⟨hle1, h1⟩ := bsub_commutator hV e ρ hc (W := V₀) (X := jOf D.T) hV₀U hJM
    have hle2 : proofEiHat D (preN D Y) ≤ D.U := proofEiHat_le D (preN_le_M D Y)
    refine bsub_injective_of_le e hle1 hle2 ?_
    rw [h1, hbsub, bsub_proofEiHat D e ρ hc hYN]
    refine le_antisymm (commOn_mono le_rfl hW0A) (K.commOn_le (fun q hq b hb => ?_) hkY hk3)
    exact natC_fix (mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM) hq) hb.2
  have hnat : ∀ L : Subgroup G, L ≤ D.M → L ≤ preMbar D K₃ → L ≤ normalizer (V₀ : Set G) →
      (∃ l ∈ L, l ∉ centralizer (V₀ : Set G) ∧ l ^ 3 ∈ centralizer (V₀ : Set G)) →
        CFSG.Quasithin.IsNaturalL2Prime 1 L V₀ := by
    intro L hLM hLK hLV ⟨l₃, hl₃L, hl₃nc, hl₃c⟩
    letI : Fintype F := Fintype.ofFinite F
    have hF2' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF2]
    have hVL : ⁅V₀, L⁆ ≤ V₀ := commutator_le_of_normalizer le_rfl hLV
    have hVLU : ⁅V₀, L⁆ ≤ D.U := hVL.trans hV₀U
    have hLnorm : L ≤ normalizer ((⁅V₀, L⁆ : Subgroup G) : Set G) := fun l hl =>
      mem_normalizer_commutator (hLV hl) (Subgroup.le_normalizer hl)
    have hπmem : ∀ l : ↥L,
        ((QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (Subgroup.inclusion hLM)) l ∈ Y := by
      intro l
      obtain ⟨hl, hlK⟩ := (mem_preMbar D).1 (hLK l.2)
      exact hK₃Y hlK
    set πL : ↥L →* ↥Y := ((QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp
      (Subgroup.inclusion hLM)).codRestrict Y hπmem with hπL
    have hπLc : ∀ l : ↥L, ((πL l : ↥Y) : MBar D.M D.U) = QuotientGroup.mk ⟨l, hLM l.2⟩ := fun l => rfl
    set α₀ : ↥L →* ↥(StatedSL 2 F) := K.φ.toMonoidHom.comp πL with hα₀
    set β₀ : ↥⁅V₀, L⁆ →* Multiplicative (Fin 2 → F) :=
      (AddMonoidHom.toMultiplicative K.ψ).comp (e.toMonoidHom.comp (Subgroup.inclusion hVLU)) with hβ₀
    have hβ₀app : ∀ v : ↥⁅V₀, L⁆, Multiplicative.toAdd (β₀ v) =
        K.ψ (Multiplicative.toAdd (e (Subgroup.inclusion hVLU v))) := fun v => rfl
    have hxv : ∀ v : ↥⁅V₀, L⁆,
        iota e (Multiplicative.toAdd (e (Subgroup.inclusion hVLU v))) = (v : G) := by
      intro v
      simp [iota]
    have hxW0 : ∀ v : ↥⁅V₀, L⁆, Multiplicative.toAdd (e (Subgroup.inclusion hVLU v)) ∈ W₀ := by
      intro v
      have h : Multiplicative.toAdd (e (Subgroup.inclusion hVLU v)) ∈ bsub e V₀ := by
        rw [mem_bsub, hxv]
        exact hVL v.2
      rwa [hbsub] at h
    have hl₃M : l₃ ∈ D.M := hLM hl₃L
    have hl₃K : (QuotientGroup.mk ⟨l₃, hl₃M⟩ : MBar D.M D.U) ∈ K₃ := ((mem_preMbar D).1 (hLK hl₃L)).2
    have hl₃1 : (QuotientGroup.mk ⟨l₃, hl₃M⟩ : MBar D.M D.U) ≠ 1 := fun h =>
      hl₃nc (hmk_one l₃ hl₃M h)
    have hl₃3 : (QuotientGroup.mk ⟨l₃, hl₃M⟩ : MBar D.M D.U) ^ 3 = 1 := hK₃pow _ hl₃K
    have hπl₃ : πL ⟨l₃, hl₃L⟩ ≠ 1 := fun h => hl₃1 (congrArg (fun z : ↥Y => (z : MBar D.M D.U)) h)
    have hπl₃3 : (πL ⟨l₃, hl₃L⟩) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hl₃3)
    have hg1 : α₀ ⟨l₃, hl₃L⟩ ≠ 1 := fun h =>
      hπl₃ (K.φ.injective (by rw [map_one]; exact h))
    have hg3 : (α₀ ⟨l₃, hl₃L⟩) ^ 3 = 1 := by
      change (K.φ (πL ⟨l₃, hl₃L⟩)) ^ 3 = 1
      rw [← map_pow, hπl₃3, map_one]
    have hαker : α₀.ker = (L ⊓ centralizer (V₀ : Set G)).subgroupOf L := by
      ext l
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h1 : πL l = 1 := K.φ.injective (by rw [map_one]; exact h)
        have h2 : (QuotientGroup.mk ⟨(l : G), hLM l.2⟩ : MBar D.M D.U) = 1 := by
          rw [← hπLc, h1]
          rfl
        exact ⟨l.2, hmk_one (l : G) (hLM l.2) h2⟩
      · rintro ⟨-, hlC⟩
        have h1 : ((πL l : ↥Y) : MBar D.M D.U) = 1 := by
          rw [hπLc]
          exact hcentW0 (l : G) (hLM l.2) (hπmem l) hlC
        have h2 : πL l = 1 := Subtype.ext h1
        change K.φ (πL l) = 1
        rw [h2, map_one]
    have hβker : β₀.ker = (⁅V₀, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V₀, L⁆ := by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hβ1 : β₀ v = 1 ↔ K.ψ (Multiplicative.toAdd (e (Subgroup.inclusion hVLU v))) = 0 := by
        rw [← hβ₀app]
        exact ⟨fun h => by rw [h]; rfl, fun h => by
          apply Multiplicative.toAdd.injective
          rw [h]
          rfl⟩
      rw [hβ1]
      constructor
      · intro h0
        have hz := K.psi_inj_W0 hkY hk3 hBfix (hxW0 v) h0
        have hv1 : (v : G) = 1 := by rw [← hxv v, hz, iota_zero]
        refine ⟨v.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
        rw [hv1]
        simp
      · rintro ⟨-, hvc⟩
        have hcomm : (v : G) = l₃ * v * l₃⁻¹ := by
          have := Subgroup.mem_centralizer_iff.1 hvc l₃ hl₃L
          calc (v : G) = (v * l₃) * l₃⁻¹ := by group
            _ = l₃ * v * l₃⁻¹ := by rw [this]
        have hfix : ρ (QuotientGroup.mk ⟨l₃, hl₃M⟩)
            (Multiplicative.toAdd (e (Subgroup.inclusion hVLU v))) =
            Multiplicative.toAdd (e (Subgroup.inclusion hVLU v)) := by
          apply iota_injective e
          rw [iota_rho hV e ρ hc ⟨l₃, hl₃M⟩, hxv v, ← hcomm]
        rw [K.fixfree_W0 hkY hk3 hBfix (hK₃Y hl₃K) hl₃1 hl₃3 (hxW0 v) hfix, map_zero]
    have hβsurj : Function.Surjective β₀ := by
      intro y
      obtain ⟨u, hu⟩ := P22sq.exists_mulVec_sub_eq hg3 hg1 (Multiplicative.toAdd y)
      obtain ⟨x, hx, hxu⟩ := K.psi_W0_surj hkY hk3 u
      have hw : iota e x ∈ V₀ := hiotaV₀ x hx
      have hcmem : l₃ * iota e x * l₃⁻¹ * (iota e x)⁻¹ ∈ ⁅V₀, L⁆ := by
        have h1 := Subgroup.commutator_mem_commutator hw hl₃L
        have h2 := (⁅V₀, L⁆).inv_mem h1
        rw [commutatorElement_inv, commutatorElement_def] at h2
        exact h2
      have hcx : iota e (ρ (QuotientGroup.mk ⟨l₃, hl₃M⟩) x - x) =
          l₃ * iota e x * l₃⁻¹ * (iota e x)⁻¹ := by
        rw [iota_sub, iota_rho hV e ρ hc ⟨l₃, hl₃M⟩ x]
      refine ⟨⟨_, hcmem⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hβ₀app]
      have hx' : Multiplicative.toAdd (e (Subgroup.inclusion hVLU ⟨_, hcmem⟩)) =
          ρ (QuotientGroup.mk ⟨l₃, hl₃M⟩) x - x := by
        apply iota_injective e
        rw [hxv, hcx]
      rw [hx', map_sub]
      have h2 := K.equi (πL ⟨l₃, hl₃L⟩) x (hW0A hx)
      change K.ψ (ρ ((πL ⟨l₃, hl₃L⟩ : ↥Y) : MBar D.M D.U) x) - K.ψ x = _
      rw [h2, hxu]
      exact hu
    have hequi : ∀ (l : ↥L) (u v : ↥⁅V₀, L⁆), (v : G) = l * u * l⁻¹ →
        Multiplicative.toAdd (β₀ v) = (((α₀ l : ↥(StatedSL 2 F)) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β₀ u)) := by
      intro l u v huv
      have h1 := hc ⟨l, hLM l.2⟩ (Subgroup.inclusion hVLU u) (Subgroup.inclusion hVLU v) huv
      rw [hβ₀app, hβ₀app, h1, toAdd_ofAdd]
      exact K.equi (πL l) _ (hW0A (hxW0 u))
    have hα3 : Nat.card α₀.range = 3 := by
      have hg3o : orderOf (α₀ ⟨l₃, hl₃L⟩) = 3 := orderOf_eq_prime hg3 hg1
      have hge : 3 ≤ Nat.card α₀.range := by
        have hz : Subgroup.zpowers (α₀ ⟨l₃, hl₃L⟩) ≤ α₀.range := Subgroup.zpowers_le.2 ⟨_, rfl⟩
        calc 3 = Nat.card (Subgroup.zpowers (α₀ ⟨l₃, hl₃L⟩)) := by rw [Nat.card_zpowers, hg3o]
          _ ≤ Nat.card α₀.range := Subgroup.card_le_of_le hz
      have hle : Nat.card α₀.range ≤ 3 := by
        have hrange : α₀.range ≤ (K₃.subgroupOf Y).map K.φ.toMonoidHom := by
          rintro _ ⟨l, rfl⟩
          have hl : ((πL l : ↥Y) : MBar D.M D.U) ∈ K₃ := ((mem_preMbar D).1 (hLK l.2)).2
          exact ⟨πL l, hl, rfl⟩
        calc Nat.card α₀.range ≤ Nat.card ((K₃.subgroupOf Y).map K.φ.toMonoidHom) :=
              Subgroup.card_le_of_le hrange
          _ = Nat.card (K₃.subgroupOf Y) := Subgroup.card_map_of_injective K.φ.injective
          _ = 3 := by
              rw [← hK₃card]
              exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₃Y).toEquiv
      omega
    exact P22sq.natL2Prime_one_of hF2' hLnorm α₀ hαker hα3 β₀ hβsurj hβker hequi
  refine ⟨V₀, K₃, ?_⟩
  have hlift := fun k' (hk' : k' ∈ ⁅Y, Y⁆) => exists_lift_commutator D hYN hk'
  refine
    { le_Ii := (bsub_le_iff e hV₀U).1 (by rw [hbsub, hIi]; exact hW0A)
      elem := (uc22p22xf_hel D).mono hV₀U
      card := by
        rw [← card_bsub e hV₀U, hbsub]
        exact K.card_W0 hF2 hkY hk3 hBfix
      norm := fun x hx hxN => by
        rw [Subgroup.mem_normalizer_iff]
        intro v
        refine ⟨hconj x hx hxN v, fun h => ?_⟩
        have := hconj x⁻¹ (D.M.inv_mem hx) (inv_mem hxN) _ h
        simpa [mul_assoc] using this
      faith := fun x hxNi hxC => by
        obtain ⟨-, hxM, hxY⟩ := (mem_preN D).1 hxNi
        exact (uc22br_gt_mk_eq_one_iff hV ⟨x, hxM⟩).1 (hcentW0 x hxM hxY hxC)
      K3_le := hK₃Y
      K3_card := hK₃card
      K3_cube := hK3cube
      K3_sq := hK3sq
      K3_pcore := ?_
      gen := ?_
      ord3 := ?_
      fixfree := ?_
      hat := hat
      hat_ne := ?_
      nat := hnat }
  ·
    have hK₃p : IsPGroup 3 ↥K₃ := IsPGroup.of_card (by rw [hK₃card, pow_one])
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 (hK₃Y.trans hYN) ?_ hK₃p
    have hconjK : ∀ g ∈ Nbar, ∀ z ∈ K₃, g * z * g⁻¹ ∈ K₃ := by
      intro g hg z hz
      refine mem_of_pow_three hK₃Y hY6 hK₃card (d.conj_mem hg i (hK₃Y hz)) ?_
      rw [conj_pow, hK₃pow z hz]
      simp
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨hconjK g hg z, fun hz => by
      have := hconjK g⁻¹ (Nbar.inv_mem hg) _ hz
      simpa [mul_assoc] using this⟩
  ·
    obtain ⟨y, hy, hyM, hyk⟩ := hlift k hkYY
    refine ⟨y, hy, hyM, ?_, ?_⟩
    · rw [hyk]
      exact Subgroup.mem_zpowers k
    · rw [hyk]
      intro h
      rw [h, orderOf_one] at hk3
      omega
  ·
    intro x hx hxK hx1
    refine ⟨fun hxC => hx1 (hcentW0 x hx (hK₃Y hxK) hxC), ?_⟩
    have e3 : (⟨x ^ 3, D.M.pow_mem hx 3⟩ : ↥D.M) = (⟨x, hx⟩ : ↥D.M) ^ 3 := rfl
    refine hmk_one (x ^ 3) (D.M.pow_mem hx 3) ?_
    rw [e3, QuotientGroup.mk_pow]
    exact hK₃pow _ hxK
  ·
    intro x hx hxK hx1 v hv hxv
    obtain ⟨u, hu, rfl⟩ := hmemV₀ v hv
    have hfix : ρ (QuotientGroup.mk ⟨x, hx⟩) u = u := by
      apply iota_injective e
      rw [iota_rho hV e ρ hc ⟨x, hx⟩ u]
      calc x * iota e u * x⁻¹ = (iota e u * x) * x⁻¹ := by rw [← hxv]
        _ = iota e u := by group
    have h0 := K.fixfree_W0 hkY hk3 hBfix (hK₃Y hxK) hx1 (hK₃pow _ hxK) hu hfix
    rw [h0, iota_zero]
  ·
    rw [hat]
    exact (uc22p22xg_proofEiHat_ne_bot D Ch h2 h3 h51 hH c m Nb hNb i).1

end KleinMain

end P22k2

end CFSG.LocalAnalysis.UniquenessCase.UC22
