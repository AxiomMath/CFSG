module

public import CFSG.Quasithin.H13.L32A767d
public import CFSG.Quasithin.H13.L32A767e
public import CFSG.Quasithin.H13.U3L15Core

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem centralizer_eq_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) {z : G} (hzA : z ∈ A)
    (hz : z ≠ 1) : Subgroup.centralizer (A : Set G) = Subgroup.centralizer ({z} : Set G) := by
  refine le_antisymm (Subgroup.centralizer_le (by simpa using hzA)) ?_
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro a ha
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  have e1 : (⟨a, ha⟩ : ↥A) = y := hy _ fun h => ha1 (congrArg Subtype.val h)
  have e2 : (⟨z, hzA⟩ : ↥A) = y := hy _ fun h => hz (congrArg Subtype.val h)
  have e3 : a = z := congrArg Subtype.val (e1.trans e2.symm)
  rw [e3]
  exact hg z rfl

theorem exists_theta (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h13322 : Stmt13_3_2_two)
    {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1) :
    ∃ θ : ↥L →* SL(3, ZMod 2), Function.Surjective θ ∧ θ.ker = (pCoreOf 2 L).subgroupOf L ∧
      ∀ l : ↥L, θ l ∈ SL3.Stab0 ↔ (l : G) * z * (l : G)⁻¹ = z := by
  obtain ⟨hVel, hV8, hLTV, -, hcomm, -⟩ := hMod G T L V h.hyp h.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hAut : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One (h.hyp1281One h13322 hMod)
  obtain ⟨e₀⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) := by
    have := hcomm
    refine Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one (fun w => ?_)
      (hV8.trans (by norm_num))
    apply Subtype.ext
    simpa using hVel.2 w w.2
  have hp : Multiplicative.toAdd (e₀ ⟨z, hzV⟩) ≠ 0 := by
    intro h0
    apply hz1
    have h1 : e₀ ⟨z, hzV⟩ = 1 := h0
    exact congrArg Subtype.val (e₀.injective (h1.trans (map_one e₀).symm))
  obtain ⟨g, hg⟩ := SL3.SL3_transitive _ SL3.e0 hp (by decide)
  set e := e₀.trans (SL3.natEquiv g) with he
  have hez : Multiplicative.toAdd (e ⟨z, hzV⟩) = SL3.e0 := by
    rw [he, MulEquiv.trans_apply, SL3.natEquiv_apply, hg]
  set θ := repV hLV e with hθ
  have hθs : Function.Surjective θ := repV_surjective hLV e hAut
  refine ⟨θ, hθs, ?_, fun l => ?_⟩
  ·
    obtain ⟨θ₀, hθ₀, hker₀⟩ := exists_surj_SL32_of_lieModel h.hyp.linear
    have hTL := h.normalizes h13322
    have hred := (h.hyp1223 h13322).irrPlus.1
    have hO : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
        (pCoreOf_isPGroup 2 L)
    have hle : (pCoreOf 2 L).subgroupOf L ≤ θ.ker := by
      rw [hθ, repV_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact ((U3.mem_reducedAggregate' (hred hv)).2.1 x (hO hx)).symm
    have hcard168 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := SL3.card_SL3
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ₀.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv,
      hcard168] at h1
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ₀ hθ₀).toEquiv,
      hcard168, hker₀] at h2
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  ·
    rw [SL3.mem_Stab0]
    have hlz : (l : G) * z * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV l.2) z).mp hzV
    have key := repV_mulVec hLV e l ⟨z, hzV⟩ ⟨_, hlz⟩ rfl
    rw [hez] at key
    have key' : Multiplicative.toAdd (e ⟨_, hlz⟩) = natAct3 (θ l) SL3.e0 := by
      rw [key]
      rfl
    constructor
    · intro hfix
      have he' : e ⟨_, hlz⟩ = e ⟨z, hzV⟩ := by
        apply Multiplicative.toAdd.injective
        rw [key', hfix, hez]
      exact congrArg Subtype.val (e.injective he')
    · intro hl
      rw [← key', ← hez]
      congr 2
      exact Subtype.ext hl

section Theta

variable {z : G} {θ : ↥L →* SL(3, ZMod 2)} (hθs : Function.Surjective θ)
  (hθk : θ.ker = (pCoreOf 2 L).subgroupOf L)
  (hθz : ∀ l : ↥L, θ l ∈ SL3.Stab0 ↔ (l : G) * z * (l : G)⁻¹ = z)

omit [Finite G] in
include hθk in
theorem mem_pCoreOf_of_theta_eq_one {l : ↥L} (hl : θ l = 1) : (l : G) ∈ pCoreOf 2 L := by
  have : l ∈ θ.ker := hl
  rwa [hθk, Subgroup.mem_subgroupOf] at this

include hθk in
theorem exists_pow_two_pow_eq_one_of_theta {l : ↥L} {m : ℕ} (hl : θ l ^ m = 1) :
    ∃ n : ℕ, ((l : G) ^ m) ^ 2 ^ n = 1 := by
  have h1 : (l ^ m : ↥L) ∈ θ.ker := by rw [MonoidHom.mem_ker, map_pow, hl]
  rw [hθk, Subgroup.mem_subgroupOf] at h1
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 L) ⟨_, h1⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

omit [Finite G] in
include hθs hθz in
theorem theta_mem_R0 {X : Subgroup G} (hX : IsPGroup 2 ↥X)
    (hXz : ∀ x ∈ X, x * z * x⁻¹ = z)
    (hXn : ∀ l : ↥L, (l : G) * z * (l : G)⁻¹ = z → ∀ x ∈ X, (l : G) * x * (l : G)⁻¹ ∈ X)
    {w : ↥L} (hw : (w : G) ∈ X) : θ w ∈ SL3.R0 := by
  by_contra hR
  have hwS : θ w ∈ SL3.Stab0 := (hθz w).mpr (hXz _ hw)
  obtain ⟨n, hn⟩ := hX ⟨_, hw⟩
  have hwn : θ w ^ 2 ^ n = 1 := by
    have : w ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [← map_pow, this, map_one]
  have h8 : θ w ^ 8 = 1 := by
    have h1 : orderOf (θ w) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hwn
    have h2 : orderOf (θ w) ∣ 8 * 21 := by
      rw [show (8 * 21 : ℕ) = Nat.card SL(3, ZMod 2) by rw [SL3.card_SL3]]
      exact orderOf_dvd_natCard _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hcop : Nat.Coprime (orderOf (θ w)) 21 := by
      rw [hk]
      exact Nat.Coprime.pow_left _ (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h2)
  obtain ⟨g, hg, hg1, hg3⟩ := SL3.exists_comm_order_three _ hwS hR
    (SL3.pow_four_of_pow_eight _ h8)
  obtain ⟨l, rfl⟩ := hθs g
  have hlz := (hθz l).mp hg
  have hc : (w : G) * l * (w : G)⁻¹ * (l : G)⁻¹ ∈ X := by
    have h1 := hXn l hlz _ (inv_mem hw)
    rw [show (w : G) * l * (w : G)⁻¹ * (l : G)⁻¹ = (w : G) * ((l : G) * (w : G)⁻¹ * (l : G)⁻¹) by
      group]
    exact mul_mem hw h1
  obtain ⟨m, hm⟩ := hX ⟨_, hc⟩
  have hcm : (θ (w * l * w⁻¹ * l⁻¹)) ^ 2 ^ m = 1 := by
    have : (w * l * w⁻¹ * l⁻¹) ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
    rw [← map_pow, this, map_one]
  simp only [map_mul, map_inv] at hcm
  have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨hg3, hcm⟩
  rw [hcop.gcd_eq_one, pow_one] at this
  exact hg1 this

include hθs hθk hθz in
theorem exists_mem_l1_theta_eq (hV1 : Nat.card ↥(fsuV1 T V) = 2) (hzV1 : z ∈ fsuV1 T V)
    (hz1 : z ≠ 1) {a : SL(3, ZMod 2)} (ha : a ∈ SL3.Stab0) (ha3 : a ^ 3 = 1) :
    ∃ x : ↥L, (x : G) ∈ L₁Of L (fsuV1 T V) ∧ (x : G) ^ 3 = 1 ∧ θ x = a := by
  obtain ⟨l, rfl⟩ := hθs a
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_theta hθk ha3
  have hpow : ∀ k : ℕ, θ l ^ 4 ^ k = θ l := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, show 4 = 3 + 1 by rfl, pow_succ, ha3, one_mul]
  have hx3 : ((l : G) ^ 4 ^ n) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, show (4 : ℕ) ^ n = 2 ^ n * 2 ^ n by
      rw [← mul_pow]; norm_num, pow_mul, hn, one_pow]
  have hθx : θ (l ^ 4 ^ n) = θ l := by rw [map_pow, hpow]
  refine ⟨l ^ 4 ^ n, ?_, by simpa using hx3, hθx⟩
  have hxz : ((l ^ 4 ^ n : ↥L) : G) * z * ((l ^ 4 ^ n : ↥L) : G)⁻¹ = z :=
    (hθz _).mp (by rw [hθx]; exact ha)
  rw [← lOne_eq_L₁Of]
  refine mem_oTwoUpper_of_odd (Subgroup.mem_inf.mpr ⟨(l ^ 4 ^ n).2, ?_⟩) ?_
  · rw [normalizer_eq_centralizer_of_card_two hV1, centralizer_eq_of_card_two hV1 hzV1 hz1,
      Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    calc w * ((l ^ 4 ^ n : ↥L) : G) =
        ((l ^ 4 ^ n : ↥L) : G) * w * ((l ^ 4 ^ n : ↥L) : G)⁻¹ * ((l ^ 4 ^ n : ↥L) : G) := by
          rw [hxz]
      _ = ((l ^ 4 ^ n : ↥L) : G) * w := by group
  · have h1 : orderOf ((l ^ 4 ^ n : ↥L) : G) ∣ 3 := orderOf_dvd_of_pow_eq_one (by simpa using hx3)
    exact Odd.of_dvd_nat (by decide) h1

end Theta

omit [Finite G] in
theorem autHom_coe {K : Subgroup G} {Q : Type} [Group Q] (π : ↥K →* Q)
    (hπs : Function.Surjective π) (hπk : π.ker = (pCoreOf 2 K).subgroupOf K) (k : ↥K) :
    autHom π hπs hπk ⟨k, Subgroup.le_normalizer k.2⟩ = MulAut.conj (π k) := by
  refine MulEquiv.ext fun A => ?_
  obtain ⟨k', rfl⟩ := hπs A
  rw [autHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

omit [Finite G] in
theorem mem_centralizer_singleton_iff_conj {g z : G} :
    g ∈ Subgroup.centralizer ({z} : Set G) ↔ g * z * g⁻¹ = z := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem comm_mem_pCoreOf_L_of_odd (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (h13322 : Stmt13_3_2_two) {y : G} (hyD : y ∈ dK T V)
    (hyM : y ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf y)) :
    ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨⟨z, hzV1⟩, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV1
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hzV1
  have hHz : ∀ g : G, g ∈ hz T V ↔ g * z * g⁻¹ = z := fun g => by
    show g ∈ Subgroup.centralizer (fsuV1 T V : Set G) ↔ _
    rw [centralizer_eq_of_card_two hV1 hzV1 hz1', mem_centralizer_singleton_iff_conj]
  obtain ⟨θ, hθs, hθk, hθz⟩ := exists_theta h hMod h13322 hzV hz1'
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 h hMod h63
  obtain ⟨c, hc, hc21⟩ : ∃ c, autHom θ hθs hθk ⟨y, hyM⟩ = MulAut.conj c ∧ c ^ 21 = 1 := by
    refine exists_conj_of_pow_eq_one hodd ?_
    have hy1 : (⟨y, hyM⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ orderOf y = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← map_pow, hy1, map_one]
  have hθy : ∀ l : ↥L, θ (conjOn L ⟨y, hyM⟩ l) = c * θ l * c⁻¹ := fun l => by
    rw [← autHom_apply θ hθs hθk, hc, MulAut.conj_apply]
  have hcS : c ∈ SL3.Stab0 ∧ c ^ 3 = 1 := by
    refine sl3_mem_stab0_of_comm c hc21 fun a ha ha3 => ?_
    obtain ⟨x, hxL1, -, rfl⟩ := exists_mem_l1_theta_eq hθs hθk hθz hV1 hzV1 hz1' ha ha3
    have hxK : (x : G) ∈ kz T V := l1_le_kz h hMod hxL1
    have hmem : ((conjOn L ⟨y, hyM⟩ x * x⁻¹ : ↥L) : G) ∈ pCoreOf 2 (kz T V) := by
      simpa [coe_conjOn] using hyD.2 x hxK
    have hR := theta_mem_R0 hθs hθz (X := pCoreOf 2 (kz T V)) (pCoreOf_isPGroup 2 _)
      (fun w hw => (hHz w).mp (oTwoUpper_le _ (pCoreOf_le 2 _ hw)))
      (fun l hl w hw => (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2
        (kz T V) (le_normalizer_oTwoUpper _ ((hHz _).mpr hl))) w).mp hw) hmem
    rwa [map_mul, map_inv, hθy] at hR
  obtain ⟨x₀, hx₀L1, hx₀3, hθx₀⟩ :=
    exists_mem_l1_theta_eq hθs hθk hθz hV1 hzV1 hz1' hcS.1 hcS.2
  obtain ⟨s, hsS, hscs⟩ := sl3_exists_inv c hcS.1 hcS.2
  obtain ⟨t, rfl⟩ := hθs s
  have htH : (t : G) ∈ hz T V := (hHz _).mpr ((hθz t).mp hsS)
  have hx₀K : (x₀ : G) ∈ kz T V := l1_le_kz h hMod hx₀L1
  have hy'1 : autHom θ hθs hθk (⟨(x₀ : G), Subgroup.le_normalizer x₀.2⟩⁻¹ * ⟨y, hyM⟩) = 1 := by
    rw [map_mul, map_inv, autHom_coe θ hθs hθk x₀, hθx₀, hc, inv_mul_cancel]
  have hw := (autHom_eq_one_iff θ hθs hθk _).mp hy'1 t t.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hw
  have htMK : (t : G) ∈ mK T V := le_normalizer_oTwoUpper _ htH
  set X0 : ↥(mK T V) := ⟨x₀, kz_le_mK hx₀K⟩ with hX0
  set Y0 : ↥(mK T V) := ⟨y, hyD.1⟩ with hY0def
  set T0 : ↥(mK T V) := ⟨t, htMK⟩ with hT0
  have hY0 : autHom π hπs hπk Y0 = 1 := (autHom_eq_one_iff π hπs hπk Y0).mpr hyD.2
  set W := X0⁻¹ * Y0 * T0 * (X0⁻¹ * Y0)⁻¹ * T0⁻¹ with hW
  set R := T0 * X0 * T0⁻¹ * X0 with hR
  set Q := (X0⁻¹ * R * X0)⁻¹ * W with hQ
  have hX03 : autHom π hπs hπk X0 ^ 3 = 1 := by
    rw [← map_pow]
    have : X0 ^ 3 = 1 := Subtype.ext (by simpa [hX0] using hx₀3)
    rw [this, map_one]
  have hQX : autHom π hπs hπk Q = autHom π hπs hπk X0 := by
    have e1 : autHom π hπs hπk W = autHom π hπs hπk (X0⁻¹ * R * X0⁻¹) := by
      simp only [hW, hR, map_mul, map_inv, hY0, mul_one]
      group
    have e2 : autHom π hπs hπk Q = (autHom π hπs hπk X0)⁻¹ * (autHom π hπs hπk X0)⁻¹ := by
      rw [hQ, map_mul, e1]
      simp only [map_mul, map_inv]
      group
    rw [e2]
    calc (autHom π hπs hπk X0)⁻¹ * (autHom π hπs hπk X0)⁻¹ =
        (autHom π hπs hπk X0)⁻¹ * (autHom π hπs hπk X0)⁻¹ * autHom π hπs hπk X0 ^ 3 := by
          rw [hX03, mul_one]
      _ = autHom π hπs hπk X0 := by group
  have hwL : x₀⁻¹ * y * t * (x₀⁻¹ * y)⁻¹ * t⁻¹ ∈ L := pCoreOf_le 2 L hw
  set WL : ↥L := ⟨_, hwL⟩ with hWL
  have hθW : θ WL = 1 := by
    have : WL ∈ θ.ker := by rw [hθk, Subgroup.mem_subgroupOf]; exact hw
    exact this
  set QL : ↥L := (x₀⁻¹ * (t * x₀ * t⁻¹ * x₀) * x₀)⁻¹ * WL with hQL
  have hθQ : θ QL ∈ SL3.R0 := by
    have hr : θ (t * x₀ * t⁻¹ * x₀) ∈ SL3.R0 := by
      simpa only [map_mul, map_inv, hθx₀] using hscs
    have h1 := SL3.conj_mem_R0 c⁻¹ (inv_mem hcS.1) _ hr
    rw [inv_inv] at h1
    rw [hQL, map_mul, hθW, mul_one]
    simpa only [map_mul, map_inv, hθx₀] using inv_mem h1
  obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_theta hθk
    (show θ QL ^ 2 = 1 by rw [sq]; exact sl3_R0_mul_self _ hθQ)
  have hQm : Q ^ (2 * 2 ^ m) = 1 := by
    apply Subtype.ext
    have e : ((Q : ↥(mK T V)) : G) = (QL : G) := by
      simp [hQ, hW, hR, hX0, hY0def, hT0, hQL, hWL]
    rw [Subgroup.coe_pow, e, pow_mul]
    simpa using hm
  have hX01 : autHom π hπs hπk X0 = 1 := by
    have h2 : autHom π hπs hπk X0 ^ (2 * 2 ^ m) = 1 := by rw [← hQX, ← map_pow, hQm, map_one]
    have hcop : Nat.Coprime 3 (2 * 2 ^ m) := by
      rw [← pow_succ']
      exact Nat.Coprime.pow_right _ (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hX03, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hx₀D : (x₀ : G) ∈ dK T V := ⟨kz_le_mK hx₀K, (autHom_eq_one_iff π hπs hπk X0).mp hX01⟩
  have hx₀O := mem_pCoreOf_of_mem_dK h hMod h63 hx₀K hx₀D
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (kz T V)) ⟨_, hx₀O⟩
  have hx₀k : (x₀ : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hx₀1 : x₀ = 1 := by
    apply Subtype.ext
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hx₀3, hx₀k⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hc1 : c = 1 := by rw [← hθx₀, hx₀1, map_one]
  rw [hc1, map_one] at hc
  exact (autHom_eq_one_iff θ hθs hθk _).mp hc

end CFSG.Quasithin.H13.L32A
