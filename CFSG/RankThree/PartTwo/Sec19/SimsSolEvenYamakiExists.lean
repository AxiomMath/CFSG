module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiCent
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiTheta
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiFusion
public import CFSG.GF2Type.Aschbacher1976Common.NotZStar
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiHat
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiTwist

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 CFSG.ClassicalInvolution.Sp62Rec Equiv CFSG.Open
open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki

set_option maxRecDepth 100000 in
theorem exists_sum_bW : ∀ x : SC, ∃ s : Finset (Fin 7), x = ∑ j ∈ s, bW j := by decide +kernel

theorem sum_bW : ∑ j, bW j = 0 := by decide

theorem p7_inv_apply (c : Perm (Fin 7)) (x : Fin 7) : c⁻¹ (c x) = x :=
  Perm.inv_eq_iff_eq.mpr rfl

theorem sc_center_ne : sc [0, 1, 2] ≠ sc [2] ∧ sc [0, 1, 2] ≠ sc [0, 1] ∧ sc [2] ≠ sc [0, 1] := by
  decide

theorem nonempty_ydata {G : Type} [Group G] {z : G} (hz : z ≠ 1)
    (e : ↥(Subgroup.centralizer ({z} : Set G)) ≃* YamakiHat) : Nonempty (YData z) := by
  set z' : ↥(Subgroup.centralizer ({z} : Set G)) := ⟨z, mem_centralizer_self' z⟩
  have hcen : ∀ b : ↥Wsub, hatEquivWsub (e z') * b = b * hatEquivWsub (e z') := by
    intro b
    obtain ⟨y, rfl⟩ := (e.trans hatEquivWsub).surjective b
    have hy : z' * y = y * z' :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
    have := congrArg (e.trans hatEquivWsub) hy
    simpa only [map_mul, MulEquiv.trans_apply] using this
  have hne : hatEquivWsub (e z') ≠ 1 := by
    intro h1
    apply hz
    have : z' = 1 := (e.trans hatEquivWsub).injective (by simpa using h1)
    exact congrArg Subtype.val this
  exact ⟨⟨e.trans hatEquivWsub, congrArg Subtype.val (eq_allOnes_of_central hcen hne)⟩⟩

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

theorem exists_sylow_T (S : Sylow 2 G) (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = Y.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 Y.T := IsPGroup.of_card (n := 9) (by rw [Y.card_T]; norm_num)
  obtain ⟨P, hTP⟩ := hT2.exists_le_sylow
  refine ⟨P, (Subgroup.eq_of_le_of_card_ge hTP ?_).symm⟩
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs)
  have hcardC : Nat.card (Subgroup.centralizer ({z} : Set G)) = 23040 := by
    rw [Nat.card_congr Y.ϑ.toEquiv, card_Wsub]
  have hS : Nat.card S ∣ 23040 := hcardC ▸ Subgroup.card_dvd_of_le hSC
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hPS : Nat.card P = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  rw [Y.card_T, hPS, hk]
  rw [hk] at hS
  have hk14 : k ≤ 14 := by
    by_contra h
    have : 2 ^ 15 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) hS
    omega
  interval_cases k <;> first | exact absurd hS (by decide) | norm_num

end YData

section Certs


namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

theorem theta_T {Θ : ↥Wsub ≃* ↥Hhat}
    (hΘD : ∀ a (ha : a ∈ Wsub), a ∈ DW ↔ (Θ ⟨a, ha⟩ : StatedSp 3 (ZMod 2)) ∈ S0) (x : G)
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    x ∈ Y.T ↔ ((Y.ϑ.trans Θ) ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ S0 := by
  rw [T, Y.mem_lift]
  constructor
  · rintro ⟨hx', hD⟩
    exact (hΘD _ _).mp hD
  · intro h
    exact ⟨hx, (hΘD _ _).mpr h⟩

theorem theta_A {Θ : ↥Wsub ≃* ↥Hhat}
    (hΘS : ∀ a (ha : a ∈ Wsub), a ∈ SW ↔ (Θ ⟨a, ha⟩ : StatedSp 3 (ZMod 2)) ∈ A0) (x : G)
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    x ∈ Y.A ↔ ((Y.ϑ.trans Θ) ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ A0 := by
  rw [A, Y.mem_lift]
  constructor
  · rintro ⟨hx', hS⟩
    exact (hΘS _ _).mp hS
  · intro h
    exact ⟨hx, (hΘS _ _).mpr h⟩

theorem zrig (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T) :
    ¬ IsConj z Y.π3 ∧ ¬ IsConj z Y.π12 ∧ ¬ IsConj Y.π3 Y.π12 ∧
      ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A := by
  obtain ⟨Θ, -, hΘD, hΘS⟩ := exists_thetaW
  set θ := Y.ϑ.trans Θ with hθ
  have hTC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := hP ▸ Y.T_le_C
  have hθT : ∀ x (hx : x ∈ Subgroup.centralizer ({z} : Set G)),
      x ∈ (P : Subgroup G) ↔ ((θ ⟨x, hx⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ S0 := by
    intro x hx
    rw [hP]
    exact Y.theta_T hΘD x hx
  set φ := mulEquivS0OfLe S0_le_Hhat θ hTC hθT
  have hmemT : ∀ {x}, x ∈ Y.A → x ∈ (P : Subgroup G) := fun hx => hP ▸ Y.A_le_T hx
  have hcen : ∀ {x}, x ∈ Y.A → (∀ t ∈ Y.T, t * x = x * t) →
      ∀ t ∈ (P : Subgroup G), t * x = x * t := fun _ h t ht => h t (hP ▸ ht)
  have hzc : ∀ t ∈ Y.T, t * z = z * t := fun t ht => (Y.commute_of_mem_T ht).2.2
  have h3c : ∀ t ∈ Y.T, t * Y.π3 = Y.π3 * t := fun t ht => (Y.commute_of_mem_T ht).1
  have h12c : ∀ t ∈ Y.T, t * Y.π12 = Y.π12 * t := fun t ht => (Y.commute_of_mem_T ht).2.1
  have hZ : ∀ {x y : G}, x ∈ Y.A → (∀ t ∈ Y.T, t * x = x * t) → y ∈ Y.A →
      (∀ t ∈ Y.T, t * y = y * t) → IsConj x y → x = y := fun hx hxc hy hyc hxy =>
    eq_of_isConj_of_mem_center P φ (hmemT hx) (hcen hx hxc) (hmemT hy) (hcen hy hyc) hxy
  obtain ⟨n1, n2, n3⟩ := sc_center_ne
  have hz' : z = Y.σA (sc [0, 1, 2]) := by rw [sc012_eq, Y.σA_one_zero]
  refine ⟨fun h => n1 ?_, fun h => n2 ?_, fun h => n3 ?_, ?_⟩
  · have := hZ Y.z_mem_A hzc Y.π3_mem_A h3c h
    refine Y.σA_injective ?_
    rw [Y.σA_pi3, ← this]
    exact hz'.symm
  · have := hZ Y.z_mem_A hzc Y.π12_mem_A h12c h
    refine Y.σA_injective ?_
    rw [Y.σA_pi12, ← this]
    exact hz'.symm
  · have := hZ Y.π3_mem_A h3c Y.π12_mem_A h12c h
    refine Y.σA_injective ?_
    rw [Y.σA_pi3, Y.σA_pi12]
    exact this
  · intro B hBT hB
    set B' : Subgroup (StatedSp 3 (ZMod 2)) :=
      ((B.subgroupOf (Subgroup.centralizer ({z} : Set G))).map θ.toMonoidHom).map
        Hhat.subtype with hB'
    have hB'S0 : B' ≤ S0 := by
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact (hθT b b.2).mp (hP ▸ hBT hb)
    have hB'E : IsE64 B' := by
      obtain ⟨hcomm, hsq, hcard⟩ := hB
      refine ⟨?_, ?_, ?_⟩
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
        have hab : a * b = b * a := Subtype.ext (hcomm _ ha _ hb)
        show ((θ a : ↥Hhat) : StatedSp 3 (ZMod 2)) * θ b = θ b * θ a
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        have haa : a * a = 1 := Subtype.ext (hsq _ ha)
        show ((θ a : ↥Hhat) : StatedSp 3 (ZMod 2)) * θ a = 1
        rw [← Subgroup.coe_mul, ← map_mul, haa, map_one]
        rfl
      · rw [hB', Subgroup.card_map_of_injective Hhat.subtype_injective,
          Subgroup.card_map_of_injective θ.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBT.trans Y.T_le_C)).toEquiv, hcard]
    have hA0 := eq_A0_of_isE64 B' hB'S0 hB'E
    have hBA : B ≤ Y.A := by
      intro b hb
      have hbC := Y.T_le_C (hBT hb)
      have h1 : ((θ ⟨b, hbC⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ B' :=
        ⟨_, ⟨⟨b, hbC⟩, hb, rfl⟩, rfl⟩
      rw [hA0] at h1
      exact (Y.theta_A hΘS b hbC).mpr h1
    exact Subgroup.eq_of_le_of_card_ge hBA (by rw [Y.card_A, hB.2.2])

theorem exists_conj_ne (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T) (hz : orderOf z = 2) :
    ∃ a ∈ Y.A, a ≠ z ∧ IsConj z a := by
  haveI := hs
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  by_contra hno
  push Not at hno
  let _ : Fintype G := Fintype.ofFinite G
  have hisolated : ∀ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have hxC : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hg
    have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      rw [show (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, zz_one hz]
      group
    obtain ⟨c, hc, hcA⟩ := Y.exists_conj_mem_A_of_mem_C P hP hxC h2
    by_contra hne
    have hconj : IsConj z (c * (g * z * g⁻¹) * c⁻¹) :=
      isConj_iff.mpr ⟨c * g, by group⟩
    have hne' : c * (g * z * g⁻¹) * c⁻¹ ≠ z := by
      intro h
      apply hne
      have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc g * z * g⁻¹ = c⁻¹ * (c * (g * z * g⁻¹) * c⁻¹) * c := by group
        _ = c⁻¹ * z * c := by rw [h]
        _ = z := by rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hno _ hcA hne' hconj
  obtain ⟨N, hN, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar G z hz1 (zz_one hz) hisolated
  exact CFSG.GF2Type.Aschbacher1976Common.not_inZStar_of_isSimpleGroup hnab hz ⟨N, hN, hNodd, hNc⟩

theorem prod_ofFn_σA {n : ℕ} (f : Fin n → SC) :
    (List.ofFn fun j => Y.σA (f j)).prod = Y.σA (∑ j, f j) := by
  induction n with
  | zero => simp [Y.σA_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => f j.succ), Fin.sum_univ_succ, Y.σA_add]


theorem nonempty_fusionOut_of_std (hchar : IsCharTwoType G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = Y.T) (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3)
    (h12 : ¬ IsConj z Y.π12) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hstd : Y.coord (conjSet Y.NA z) = scOrb 0 ∪ scOrb 6) : Nonempty (FusionOut z) := by
  obtain ⟨Θ, hΘα, hΘD, hΘS⟩ := exists_thetaW
  obtain ⟨c, hc, hL⟩ := Y.exists_perm_l32 hstd
  set b : Fin 7 → G := fun j => Y.σA (bW (c⁻¹ j)) with hb
  have hbz : b (c 0) = z := by
    simp only [hb, p7_inv_apply, bW_zero, sc012_eq, Y.σA_one_zero]
  have hb_orbit : ∀ x, (∃ n ∈ Subgroup.normalizer (Y.A : Set G), n * z * n⁻¹ = x) ↔
      ∃ i, b i = x := by
    intro x
    constructor
    · intro hx
      have hxN : x ∈ conjSet Y.NA z := hx
      have hxA := conjSet_normalizer_subset Y.z_mem_A hxN
      have hF : Y.coordOf x ∈ scOrb 0 ∪ scOrb 6 := by
        rw [← Y.mem_conj_z_iff hstd, Y.σA_coordOf hxA]
        exact hxN
      obtain ⟨k, hk⟩ := (mem_Omega_iff _).mp hF
      refine ⟨c k, ?_⟩
      simp only [hb, p7_inv_apply, hk, Y.σA_coordOf hxA]
    · rintro ⟨i, rfl⟩
      exact (Y.mem_conj_z_iff hstd _).mpr ((mem_Omega_iff _).mpr ⟨_, rfl⟩)
  have hsum_mem : ∀ s : Finset (Fin 7), Y.σA (∑ j ∈ s, bW j) ∈ Subgroup.closure (Set.range b) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Y.σA_zero]; exact Subgroup.one_mem _
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Y.σA_add]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c a, ?_⟩) ih
      simp only [hb, p7_inv_apply]
  have hb_closure : Subgroup.closure (Set.range b) = Y.A := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩
      exact Y.σA_mem_A _
    · obtain ⟨x0, rfl⟩ := Y.exists_σA hx
      obtain ⟨s, rfl⟩ := exists_sum_bW x0
      exact hsum_mem s
  have hb_prod : (List.ofFn b).prod = 1 := by
    rw [show b = fun j => Y.σA (bW (c⁻¹ j)) from rfl, Y.prod_ofFn_σA,
      Equiv.sum_comp c⁻¹ bW, sum_bW, Y.σA_zero]
  have hb_perm : ∀ n ∈ Subgroup.normalizer (Y.A : Set G), ∃ σ ∈ l32, ∀ i,
      n * b i * n⁻¹ = b (σ i) := by
    intro n hn
    refine ⟨c * Y.permHom hstd ⟨n, hn⟩ * c⁻¹, hL ⟨n, hn⟩, fun i => ?_⟩
    simp only [hb]
    rw [← Y.σA_cc hn, ← Y.bW_permHom hstd ⟨n, hn⟩]
    simp only [Perm.mul_apply, p7_inv_apply]
  have hgen : Subgroup.closure {x | x ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf x = 2} =
      Subgroup.centralizer ({z} : Set G) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
    set I := Subgroup.closure {x | x ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf x = 2}
      with hI
    have key : ∀ m ∈ Hhat, ∀ hm : m ∈ Hhat, (((Y.ϑ.trans Θ).symm ⟨m, hm⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) : G) ∈ I := by
      intro m hm0
      induction hm0 using Subgroup.closure_induction with
      | mem y hy =>
        intro hm
        obtain ⟨i, -, rfl⟩ := hy
        set y' := (Y.ϑ.trans Θ).symm ⟨yamakiSp i, hm⟩
        have hsq : (y' : G) * y' = 1 := by
          have h1 : (Y.ϑ.trans Θ).symm (⟨yamakiSp i, hm⟩ * ⟨yamakiSp i, hm⟩) = 1 := by
            have : (⟨yamakiSp i, hm⟩ * ⟨yamakiSp i, hm⟩ : ↥Hhat) = 1 :=
              Subtype.ext (yamakiSp_mul_self i)
            rw [this, map_one]
          rw [map_mul] at h1
          exact congrArg Subtype.val h1
        by_cases h1 : (y' : G) = 1
        · rw [h1]
          exact I.one_mem
        · exact Subgroup.subset_closure ⟨y'.2, orderOf_eq_prime (by rw [sq]; exact hsq) h1⟩
      | one =>
        intro hm
        have e : (⟨1, hm⟩ : ↥Hhat) = 1 := rfl
        rw [e, map_one]
        exact I.one_mem
      | mul a b' ha hb' iha ihb =>
        intro hm
        have e : (⟨a * b', hm⟩ : ↥Hhat) = ⟨a, ha⟩ * ⟨b', hb'⟩ := rfl
        rw [e, map_mul, Subgroup.coe_mul]
        exact I.mul_mem (iha ha) (ihb hb')
      | inv a ha iha =>
        intro hm
        have e : (⟨a⁻¹, hm⟩ : ↥Hhat) = (⟨a, ha⟩)⁻¹ := rfl
        rw [e, map_inv, Subgroup.coe_inv]
        exact I.inv_mem (iha ha)
    intro x hx
    have h := key _ ((Y.ϑ.trans Θ) ⟨x, hx⟩).2 ((Y.ϑ.trans Θ) ⟨x, hx⟩).2
    rwa [Subtype.coe_eta, MulEquiv.symm_apply_apply] at h
  obtain ⟨hU1, hU2, hU3⟩ := Y.compl_A
  refine ⟨{
    θ := Y.ϑ.trans Θ
    θ_z := ?_
    T := P
    T_le := hP ▸ Y.T_le_C
    θ_T := fun x hx => by rw [hP]; exact Y.theta_T hΘD x hx
    A := Y.A
    A_le := Y.A_le_C
    θ_A := Y.theta_A hΘS
    cent_A := Y.centralizer_A_le
    b := b
    b_inj := fun i j h => c⁻¹.injective (bW_injective (Y.σA_injective h))
    z_mem := ⟨c 0, hbz⟩
    b_orbit := hb_orbit
    b_prod := hb_prod
    b_closure := hb_closure
    perm_mem := hb_perm
    card_N := Y.card_NA hstd
    compl := ⟨Y.U, hP ▸ hU1, hU2, hP ▸ hU3⟩
    cent_le := fun x hx hx1 =>
      Y.centralizer_le_K hstd hc hL hchar P hP hE hz h3 h12 hx hx1
    conj_A := fun t ht ht2 => Y.exists_conj_mem_A (hP ▸ ht)
      (by rw [← sq, ← ht2, pow_orderOf_eq_one])
    gen_inv := hgen }⟩
  show ((Θ (Y.ϑ ⟨z, _⟩) : ↥Hhat) : StatedSp 3 (ZMod 2)) = alpha
  rw [show Y.ϑ ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ =
    ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ from Subtype.ext Y.ϑ_z]
  exact hΘα

end YData

theorem exists_fusionOut : FusionOutStatement := by
  intro G _ _ hs hnab hchar S z hz hzS hzc ⟨e⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  obtain ⟨Y⟩ := nonempty_ydata hz1 e
  obtain ⟨P, hP⟩ := Y.exists_sylow_T S hzc
  obtain ⟨h3, h12, h312, hE⟩ := Y.zrig P hP
  have hiso := Y.exists_conj_ne hs hnab P hP hz
  obtain ⟨Y', hA', hT', h3', h12', hstd⟩ := Y.exists_std hchar P hP hz h3 h12 h312 hE hiso
  refine Y'.nonempty_fusionOut_of_std hchar P (hP.trans hT'.symm) hz (h3' ▸ h3) (h12' ▸ h12)
    ?_ hstd
  rw [hA', hT']
  exact hE

end Certs

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
