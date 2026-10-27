module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannQuot
public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofA6
import CFSG.RankThree.PartTwo.KFacts.KS12Moves

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

variable {X : Type} [Group X] [Finite X]

private theorem sba6q_mem_of_max {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) {a : X}
    (ha3 : a ^ 3 = 1) (haE : A ≤ Subgroup.centralizer ({a} : Set X)) : a ∈ A := by
  have hsup := isElemAbelian_sup_zpowers hA ha3 fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (haE he)
  rw [← hAmax _ hsup le_sup_left]
  exact (le_sup_right : Subgroup.zpowers a ≤ A ⊔ Subgroup.zpowers a) (Subgroup.mem_zpowers a)

private theorem sba6q_exists_mem_inf_of_fixed {A Y : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set X)) {y : X} (hy : y ∈ Y)
    (hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y)
    (hy3 : y ^ 3 ∈ CFSG.Open.pCoreOf 2 Y) :
    ∃ a₀ ∈ A ⊓ Y, a₀ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := CFSG.Open.pCoreOf 2 Y with hVdef
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hVY : V ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYV : Y ≤ Subgroup.normalizer (V : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAV : A ≤ Subgroup.normalizer (V : Set X) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hA3 : IsPGroup 3 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩
  let α : ↥A →* MulAut X := MulAut.conj.comp A.subtype
  have hcop : ¬ 3 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨c, hcV, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA3 α V
    hcop y).1 (by
    intro a x hx
    change (a : X) * x * (a : X)⁻¹ * y⁻¹ ∈ V
    have h1 : (a : X) * (x * y⁻¹) * (a : X)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) _).mp hx
    have e : (a : X) * x * (a : X)⁻¹ * y⁻¹ =
        ((a : X) * (x * y⁻¹) * (a : X)⁻¹) * ((a : X) * y * (a : X)⁻¹ * y⁻¹) := by group
    rw [e]
    exact V.mul_mem h1 (hfix a a.2))
  have hcA : ∀ a ∈ A, a * c * a⁻¹ = c := fun a ha => hcfix ⟨a, ha⟩
  have hcY : c ∈ Y := by
    have : c = (c * y⁻¹) * y := by group
    rw [this]
    exact Y.mul_mem (hVY hcV) hy
  have hc3 : c ^ 3 ∈ V := by
    have h := Push153B.pow_mul_mem_of_mem hYV hcV hy 3
    have e : c * y⁻¹ * y = c := by group
    rw [e] at h
    have e2 : c ^ 3 = (c ^ 3 * (y ^ 3)⁻¹) * y ^ 3 := by group
    rw [e2]
    exact V.mul_mem h hy3
  obtain ⟨k, hk⟩ := hV2 ⟨c ^ 3, hc3⟩
  have hk' : (c ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : ∃ m, 4 ^ k = 3 * m + 1 := by
    have h4 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    exact ⟨4 ^ k / 3, by omega⟩
  refine ⟨c ^ (3 * m + 1), ⟨?_, Y.pow_mem hcY _⟩, ?_⟩
  · apply sba6q_mem_of_max hA hAmax
    · rw [← pow_mul, show (3 * m + 1) * 3 = 3 * (2 ^ k * 2 ^ k) by
        rw [← hm, ← mul_pow]; norm_num; ring, pow_mul, pow_mul, hk', one_pow]
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      have h := congrArg (· ^ (3 * m + 1)) (hcA a ha)
      simp only [conj_pow] at h
      calc c ^ (3 * m + 1) * a = a * (a⁻¹ * c ^ (3 * m + 1) * a) := by group
        _ = a * c ^ (3 * m + 1) := by
          congr 1
          have h' := congrArg (fun z => a⁻¹ * z * a) h
          rw [← h']
          group
  · have e : c ^ (3 * m + 1) * y⁻¹ = (c ^ 3) ^ m * (c * y⁻¹) := by
      rw [← pow_mul, pow_succ]
      group
    rw [e]
    exact V.mul_mem (V.pow_mem hc3 m) hcV

private theorem sba6q_exists_mem_inf_center {A Y : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set X))
    (hperf : commutator (Push153B.Ybar Y) = ⊤)
    (hZ : Nat.card (Subgroup.center (Push153B.Ybar Y)) = 3)
    (e6 : Push153B.Ybar Y ⧸ Subgroup.center (Push153B.Ybar Y) ≃* alternatingGroup (Fin 6)) :
    ∃ (d : X) (hd : d ∈ A ⊓ Y), (QuotientGroup.mk ⟨d, hd.2⟩ : Push153B.Ybar Y) ∈
      Subgroup.center (Push153B.Ybar Y) ∧
        (QuotientGroup.mk ⟨d, hd.2⟩ : Push153B.Ybar Y) ≠ 1 := by
  obtain ⟨⟨z₀, hz₀⟩, hz₁⟩ : ∃ z : Subgroup.center (Push153B.Ybar Y), z ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton (Subgroup.center (Push153B.Ybar Y)) :=
      ⟨fun a b => (h a).trans (h b).symm⟩
    rw [Nat.card_of_subsingleton (1 : Subgroup.center (Push153B.Ybar Y))] at hZ
    omega
  have hz₁' : z₀ ≠ 1 := fun h => hz₁ (Subtype.ext h)
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective z₀
  have hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
    intro a ha
    obtain ⟨q₀, hq₀⟩ := Push153B.exists_inner_of_pow_three hperf e6 (g := ⟨a, hAY ha⟩)
      (Subtype.ext (by simpa using hA.2 a ha))
    have h1 := Push153B.barAct_mk ⟨a, hAY ha⟩ y hy
    rw [hq₀, MulAut.conj_apply, Subgroup.mem_center_iff.mp hz₀ q₀, mul_inv_cancel_right] at h1
    have h2 := (Push153B.mk_eq_mk_iff _ hy).mp h1.symm
    simpa [mul_assoc] using h2
  have hy3 : y ^ 3 ∈ CFSG.Open.pCoreOf 2 Y := by
    have h := Push153B.pow_three_of_mem_center hZ hz₀
    rw [← QuotientGroup.mk_pow] at h
    have : (⟨y, hy⟩ : ↥Y) ^ 3 = ⟨y ^ 3, Y.pow_mem hy 3⟩ := Subtype.ext (by simp)
    rw [this, Push153B.mk_eq_one_iff] at h
    exact h
  obtain ⟨d, hd, hdV⟩ := sba6q_exists_mem_inf_of_fixed hA hAmax hAY hy hfix hy3
  refine ⟨d, hd, ?_⟩
  have he : (QuotientGroup.mk ⟨d, hd.2⟩ : Push153B.Ybar Y) = QuotientGroup.mk ⟨y, hy⟩ :=
    (Push153B.mk_eq_mk_iff hd.2 hy).mpr hdV
  rw [he]
  exact ⟨hz₀, hz₁'⟩

private theorem sba6q_m10_mul_self_mem {u : P10} (hu : u ∈ A6Models.m10) :
    u * u ∈ A6Models.psl29 := by
  obtain ⟨r, hr, hur⟩ := (Out21.A6.mem_m10_iff u).mp hu
  simp only [Out21.A6.m10Reps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have h : u ∈ A6Models.psl29 := by simpa using hur
    exact A6Models.psl29.mul_mem h h
  · have e : u * u = (u * A6Models.tMulFrob⁻¹) *
        (A6Models.tMulFrob * (u * A6Models.tMulFrob⁻¹) * A6Models.tMulFrob⁻¹) *
          (A6Models.tMulFrob * A6Models.tMulFrob) := by group
    rw [e]
    exact A6Models.psl29.mul_mem (A6Models.psl29.mul_mem hur
      (psl29_normal _ Out21.A6.tMulFrob_mem_autA6 _ hur)) Out21.A6.tMulFrob_sq_mem

section Middle

open Push153B

private theorem sba6q_rho_mem_psl {A S Y : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set X)) (hAS : A ≤ Subgroup.normalizer (S : Set X))
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set X))
    (hperf : commutator (Ybar Y) = ⊤) (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3)
    (hcard : Nat.card (Ybar Y) = 1080)
    (e6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* alternatingGroup (Fin 6))
    (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29) :
    ∀ (s : X) (hs : s ∈ S), ((autAct ψ6 ⟨s, hSY hs⟩ : ↥A6Models.autA6) : P10) ∈
      A6Models.psl29 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, hdZ, hd1⟩ := sba6q_exists_mem_inf_center hA hAmax hAY hperf hZ e6
  have hfixZ : ∀ (s : X) (hs : s ∈ S), ∀ z ∈ Subgroup.center (Ybar Y),
      barAct Y ⟨s, hSY hs⟩ z = z := fun s hs z hz =>
    fixes_center_of_mem_sup hAS hS2 hSY hZ hd hdZ hd1 (Subgroup.mem_sup_right hs) hz
  have hinner : ∀ (a : X) (ha : a ∈ A), ∃ q₀ : Ybar Y,
      barAct Y ⟨a, hAY ha⟩ = MulAut.conj q₀ ∧
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) =
        (ψ6 (q₀ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) := by
    intro a ha
    obtain ⟨q₀, hq₀⟩ := exists_inner_of_pow_three hperf e6 (g := ⟨a, hAY ha⟩)
      (Subtype.ext (by simpa using hA.2 a ha))
    exact ⟨q₀, hq₀, autAct_of_inner ψ6 hq₀⟩
  have hlift : ∀ q : Ybar Y, q ^ 3 = 1 → (∀ (a : X) (ha : a ∈ A), barAct Y ⟨a, hAY ha⟩ q = q) →
      ∃ (a₀ : X) (ha₀ : a₀ ∈ A ⊓ Y), (QuotientGroup.mk ⟨a₀, ha₀.2⟩ : Ybar Y) = q := by
    intro q hq3 hqA
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
      intro a ha
      have h1 := hqA a ha
      rw [barAct_mk] at h1
      have h2 := (mk_eq_mk_iff _ hy).mp h1
      simpa [mul_assoc] using h2
    have hy3 : y ^ 3 ∈ CFSG.Open.pCoreOf 2 Y := by
      rw [← QuotientGroup.mk_pow] at hq3
      have : (⟨y, hy⟩ : ↥Y) ^ 3 = ⟨y ^ 3, Y.pow_mem hy 3⟩ := Subtype.ext (by simp)
      rw [this, mk_eq_one_iff] at hq3
      exact hq3
    obtain ⟨a₀, ha₀, hV⟩ := sba6q_exists_mem_inf_of_fixed hA hAmax hAY hy hfix hy3
    exact ⟨a₀, ha₀, (mk_eq_mk_iff ha₀.2 hy).mpr hV⟩
  have hlift6 : ∀ x ∈ A6Models.psl29, x ^ 3 = 1 → ∃ q : Ybar Y, q ^ 3 = 1 ∧
      ((ψ6 (q : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) : P10) = x := by
    intro x hx hx3
    obtain ⟨xt, hxt⟩ := ψ6.surjective ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective xt
    refine ⟨q, pow_three_of_image hZ e6 ?_, by rw [hxt]⟩
    apply ψ6.injective
    rw [map_pow, hxt, map_one]
    exact Subtype.ext (by simpa using hx3)
  by_cases h8a : ∀ (a : X) (ha : a ∈ A),
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) = 1
  · exfalso
    have hcen : ∀ (a : X) (ha : a ∈ A) (q : Ybar Y), barAct Y ⟨a, hAY ha⟩ q = q := by
      intro a ha q
      have h1 : autAct ψ6 ⟨a, hAY ha⟩ = 1 := Subtype.ext (h8a a ha)
      rw [barAct_eq_one_of_autAct ψ6 hperf h1, MulAut.one_apply]
    obtain ⟨x, hx, y, hy, hx3, hy3, hxy⟩ := A6.exists_noncomm_three
    obtain ⟨qx, hqx3, hqx⟩ := hlift6 x hx hx3
    obtain ⟨qy, hqy3, hqy⟩ := hlift6 y hy hy3
    obtain ⟨ax, hax, hmx⟩ := hlift qx hqx3 (fun a ha => hcen a ha qx)
    obtain ⟨ay, hay, hmy⟩ := hlift qy hqy3 (fun a ha => hcen a ha qy)
    have hcomm : ax * ay = ay * ax :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨ax, hax.1⟩ ⟨ay, hay.1⟩)
    have hq : qx * qy = qy * qx := by
      rw [← hmx, ← hmy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hcomm
    apply hxy
    rw [← hqx, ← hqy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hq]
  push Not at h8a
  obtain ⟨a₁, ha₁, hx1⟩ := h8a
  set x : P10 := ((autAct ψ6 ⟨a₁, hAY ha₁⟩ : ↥A6Models.autA6) : P10) with hxdef
  obtain ⟨q₁₀, -, hx_eq⟩ := hinner a₁ ha₁
  have hx : x ∈ A6Models.psl29 := by rw [hxdef, hx_eq]; exact (ψ6 _).2
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, ← map_pow]
    have : (⟨a₁, hAY ha₁⟩ : ↥(Subgroup.normalizer (Y : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA.2 a₁ ha₁)
    rw [this, map_one, OneMemClass.coe_one]
  set R : Subgroup P10 := imgP ψ6 S with hRdef
  have hR2 : IsPGroup 2 R := isPGroup_imgP ψ6 hS2
  have hRA : R ≤ A6Models.autA6 := imgP_le_autA6 ψ6 S
  have hxn : x ∈ Subgroup.normalizer (R : Set P10) :=
    mem_normalizer_imgP ψ6 (a := ⟨a₁, hAY ha₁⟩) (hAS ha₁)
  have hexclR : ∀ u ∈ R, u * x = x * u → u ∈ A6Models.m10 := by
    intro u hu hux
    obtain ⟨t, ht, htN, rfl⟩ := exists_of_mem_imgP ψ6 hu
    exact autAct_mem_m10 hperf hZ hcard e6 ψ6 (hfixZ t ht) hx hx3 hx1 hux
  have hxp : ∀ h : P10, h ∈ A6Models.psl29 ↔ x * h * x⁻¹ ∈ A6Models.psl29 := by
    intro h
    refine ⟨psl29_normal x (psl29_le_autA6 hx) h, fun h' => ?_⟩
    have := psl29_normal x⁻¹ (A6Models.autA6.inv_mem (psl29_le_autA6 hx)) _ h'
    simpa [mul_assoc] using this
  have hRpsl : R ≤ A6Models.psl29 := by
    by_cases hR1 : R ⊓ A6Models.psl29 = ⊥
    ·
      intro u hu
      have hcomm : u * x = x * u := by
        have hxu : x * u⁻¹ * x⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp hxn u⁻¹).mp (R.inv_mem hu)
        have h1 : u * x * u⁻¹ * x⁻¹ ∈ R := by
          have e : u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
          rw [e]
          exact R.mul_mem hu hxu
        have h2 : u * x * u⁻¹ * x⁻¹ ∈ A6Models.psl29 :=
          A6Models.psl29.mul_mem (psl29_normal u (hRA hu) x hx) (A6Models.psl29.inv_mem hx)
        have h3 : u * x * u⁻¹ * x⁻¹ ∈ R ⊓ A6Models.psl29 := ⟨h1, h2⟩
        rw [hR1, Subgroup.mem_bot] at h3
        calc u * x = (u * x * u⁻¹ * x⁻¹) * (x * u) := by group
          _ = x * u := by rw [h3, one_mul]
      have hum : u ∈ A6Models.m10 := hexclR u hu hcomm
      have huu : u * u ∈ R ⊓ A6Models.psl29 := ⟨R.mul_mem hu hu, sba6q_m10_mul_self_mem hum⟩
      rw [hR1, Subgroup.mem_bot] at huu
      exact Out21.A6.m10_involution_mem_psl29 hum huu
    · have hn1 : x ∈ Subgroup.normalizer ((R ⊓ A6Models.psl29 : Subgroup P10) : Set P10) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have h1 := Subgroup.mem_normalizer_iff.mp hxn h
        simp only [Subgroup.mem_inf] at h1 ⊢
        rw [h1, hxp h]
      exact (A6.le_of_lattice_a6 hx hx3 hx1 hRA hR2 inf_le_left hR1 hn1 hxn hexclR).1.trans
        inf_le_right
  intro s hs
  exact hRpsl (mem_imgP ψ6 hs (hSY hs))

end Middle

private theorem sba6q_mem_normalizer (g : X) :
    g ∈ Subgroup.normalizer ((oResidual 2 X : Subgroup X) : Set X) := by
  have hn : (oResidual 2 X).Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
  rw [Subgroup.normalizer_eq_top_iff.mpr hn]
  exact Subgroup.mem_top g

private theorem sba6q_isPGroup_quotient [(oResidual 2 X).Normal] :
    IsPGroup 2 (X ⧸ oResidual 2 X) := by
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  have hy : x ^ 2 ^ a ∈ oResidual 2 X := by
    refine Subgroup.subset_closure ?_
    show Nat.Coprime (orderOf (x ^ 2 ^ a)) 2
    have hd : orderOf (x ^ 2 ^ a) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, ← hxm]
      exact pow_orderOf_eq_one x
    exact Nat.Coprime.coprime_dvd_left hd (Nat.coprime_two_right.mpr hm)
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr hy

private theorem sba6q_sup_sylow_eq_top (P : Sylow 2 X) :
    oResidual 2 X ⊔ (P : Subgroup X) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (oResidual 2 X).Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
  have h1 : (oResidual 2 X ⊔ (P : Subgroup X)).index ∣ (oResidual 2 X).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have h2 : (oResidual 2 X ⊔ (P : Subgroup X)).index ∣ (P : Subgroup X).index :=
    Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨n, hn2⟩ := IsPGroup.iff_card.mp (sba6q_isPGroup_quotient (X := X))
  have hidx : (oResidual 2 X).index = 2 ^ n := by
    rw [Subgroup.index, hn2]
  rw [hidx] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [← Subgroup.index_eq_one]
  by_contra hne
  have hj1 : j ≠ 0 := fun h0 => hne (by rw [hj, h0, pow_zero])
  apply P.not_dvd_index
  refine dvd_trans ?_ h2
  rw [hj]
  exact dvd_pow_self 2 hj1

private theorem sba6q_pCoreOf_top_le :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup X)))
  exact CFSG.LieType.BorelTits.le_pCore 2 hnorm
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X))

private theorem sba6q_exists_mul_eq {x : X} {a b : ℕ} (hab : Nat.Coprime a b)
    (hx : orderOf x = a * b) :
    ∃ y z : X, y ∈ Subgroup.zpowers x ∧ z ∈ Subgroup.zpowers x ∧ x = y * z ∧
      orderOf y ∣ a ∧ orderOf z ∣ b := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have hxab : x ^ (a * b) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨x ^ (v * (b : ℤ)), x ^ (u * (a : ℤ)), Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _,
    Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _, ?_, ?_, ?_⟩
  · have : v * (b : ℤ) + u * a = 1 := by linarith
    rw [← zpow_add, this, zpow_one]
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul]
    have : v * (b : ℤ) * a = ((a * b : ℕ) : ℤ) * v := by push_cast; ring
    rw [this, zpow_mul, zpow_natCast, hxab, one_zpow]
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul]
    have : u * (a : ℤ) * b = ((a * b : ℕ) : ℤ) * u := by push_cast; ring
    rw [this, zpow_mul, zpow_natCast, hxab, one_zpow]

private theorem sba6q_ker_le
    (hZ : Nat.card (Subgroup.center (Push153B.Ybar (oResidual 2 X))) = 3)
    {d : X} (hdY : d ∈ oResidual 2 X)
    (hdZ : (QuotientGroup.mk ⟨d, hdY⟩ : Push153B.Ybar (oResidual 2 X)) ∈
      Subgroup.center (Push153B.Ybar (oResidual 2 X)))
    (hd1 : (QuotientGroup.mk ⟨d, hdY⟩ : Push153B.Ybar (oResidual 2 X)) ≠ 1) {k : X}
    (hk : Push153B.barAct (oResidual 2 X) ⟨k, sba6q_mem_normalizer k⟩ = 1) :
    k ∈ oResidual 2 X ⊔ CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hLP := sba6q_sup_sylow_eq_top P
  have hP2 : IsPGroup 2 (P : Subgroup X) := P.isPGroup'
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  obtain ⟨y, z, hy, hz, hkyz, hya, hzm⟩ := sba6q_exists_mul_eq
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)) hom
  have hzL : z ∈ oResidual 2 X := by
    refine Subgroup.subset_closure ?_
    show Nat.Coprime (orderOf z) 2
    exact Nat.Coprime.coprime_dvd_left hzm (Nat.coprime_two_right.mpr hm)
  have hy1 : Push153B.barAct (oResidual 2 X) ⟨y, sba6q_mem_normalizer y⟩ = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have e : (⟨y, sba6q_mem_normalizer y⟩ : ↥(Subgroup.normalizer
        ((oResidual 2 X : Subgroup X) : Set X))) = ⟨k, sba6q_mem_normalizer k⟩ ^ n :=
      Subtype.ext (by simpa using hn.symm)
    rw [e, map_zpow, hk, one_zpow]
  have hym : y ^ 2 ^ a = 1 := orderOf_dvd_iff_pow_eq_one.mp hya
  have hyP : y ∈ CFSG.Open.pCoreOf 2 (oResidual 2 X ⊔ (P : Subgroup X)) :=
    Push153B.mem_pCoreOf_of_barAct_eq_one (Y := oResidual 2 X) hP2
      (fun g _ => sba6q_mem_normalizer g) hZ hdY hdZ hd1 (by rw [hLP]; exact Subgroup.mem_top y)
      hy1 hym
  have hyQ : y ∈ CFSG.pCore 2 X := by
    rw [hLP] at hyP
    exact sba6q_pCoreOf_top_le hyP
  rw [hkyz]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyQ) (Subgroup.mem_sup_left hzL)

private theorem sba6q_isTripleCover_of_mulEquiv {A B Y : Type*} [Group A] [Group B] [Group Y]
    (e : A ≃* B) (h : Sec4.IsTripleCover A Y) : Sec4.IsTripleCover B Y := by
  obtain ⟨hc, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center A).map (e : A →* B) = Subgroup.center B :=
    Subgroup.map_center_eq e
  refine ⟨by rw [← hcen, Subgroup.card_map_of_injective e.injective, hc], ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e hcen).symm.trans f

theorem le_sup_of_isTripleCover
    {A S : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hT : Sec4.IsTripleCover ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) (alternatingGroup (Fin 6))) :
    S ≤ oResidual 2 X ⊔ CFSG.pCore 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ⟩ := nonempty_oResidual_quot_equiv (X := X)
  have hq' : CFSG.IsQuasisimple (Push153B.Ybar (oResidual 2 X)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hq
  have hT' : Sec4.IsTripleCover (Push153B.Ybar (oResidual 2 X)) (alternatingGroup (Fin 6)) :=
    sba6q_isTripleCover_of_mulEquiv ψ.symm hT
  have hperf : commutator (Push153B.Ybar (oResidual 2 X)) = ⊤ := by
    have h1 := hq'.1
    rwa [Group.isPerfect_def] at h1
  have hcard : Nat.card (Push153B.Ybar (oResidual 2 X)) = 1080 := by
    rw [KFacts.card_of_isTripleCover hT', DoubleA3.card_alt6']
  obtain ⟨hZ, ⟨e6⟩⟩ := hT'
  obtain ⟨ψ0, -⟩ := DoubleA3.exists_psl_equiv
  set ψ6 : Push153B.Ybar (oResidual 2 X) ⧸ Subgroup.center (Push153B.Ybar (oResidual 2 X)) ≃*
      ↥A6Models.psl29 := e6.trans ψ0.symm with hψ6
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  have hAS : A ≤ Subgroup.normalizer (S : Set X) := hS.prop.2.2
  have hAN : A ≤ Subgroup.normalizer ((oResidual 2 X : Subgroup X) : Set X) :=
    fun a _ => sba6q_mem_normalizer a
  have hSN : S ≤ Subgroup.normalizer ((oResidual 2 X : Subgroup X) : Set X) :=
    fun s _ => sba6q_mem_normalizer s
  have hρ := sba6q_rho_mem_psl hA hAmax hAN hAS hS2 hSN hperf hZ hcard e6 ψ6
  obtain ⟨d, hd, hdZ, hd1⟩ := sba6q_exists_mem_inf_center hA hAmax hAN hperf hZ e6
  intro s hs
  obtain ⟨y₀, hy₀⟩ := ψ6.surjective ⟨_, hρ s hs⟩
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective y₀
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective y₁
  have hρl := Push153B.autAct_mem ψ6 l hl
  have hlsρ : Push153B.autAct ψ6 ⟨l, Subgroup.le_normalizer hl⟩ =
      Push153B.autAct ψ6 ⟨s, sba6q_mem_normalizer s⟩ :=
    Subtype.ext (hρl.trans (congrArg Subtype.val hy₀))
  have hk1 : Push153B.autAct ψ6 ⟨l⁻¹ * s, sba6q_mem_normalizer _⟩ = 1 := by
    have e : (⟨l⁻¹ * s, sba6q_mem_normalizer _⟩ : ↥(Subgroup.normalizer
        ((oResidual 2 X : Subgroup X) : Set X))) =
          (⟨l, Subgroup.le_normalizer hl⟩ : ↥(Subgroup.normalizer
            ((oResidual 2 X : Subgroup X) : Set X)))⁻¹ * ⟨s, sba6q_mem_normalizer s⟩ :=
      Subtype.ext rfl
    rw [e, map_mul, map_inv, hlsρ, inv_mul_cancel]
  have hkβ := Push153B.barAct_eq_one_of_autAct ψ6 hperf hk1
  have hkmem := sba6q_ker_le hZ hd.2 hdZ hd1 hkβ
  have e2 : s = l * (l⁻¹ * s) := by group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) hkmem

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
