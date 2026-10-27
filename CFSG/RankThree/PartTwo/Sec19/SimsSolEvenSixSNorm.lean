module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSFusion

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

namespace H2

variable {G : Type} [Group G] [Finite G]

private def stabSubE (K P E : Subgroup G) (hEK : ∀ k ∈ K, ∀ e ∈ E, k * e * k⁻¹ = e) :
    Subgroup G where
  carrier := {a | a ∈ K ∧ ∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ E}
  mul_mem' := by
    rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, fun p hp => ?_⟩
    have e : a * b * p * (a * b)⁻¹ * p⁻¹ =
        a * (b * p * b⁻¹ * p⁻¹) * a⁻¹ * (a * p * a⁻¹ * p⁻¹) := by group
    rw [e, hEK a haK _ (hb p hp)]
    exact E.mul_mem (hb p hp) (ha p hp)
  one_mem' := ⟨K.one_mem, fun p _ => by simpa using E.one_mem⟩
  inv_mem' := by
    rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, fun p hp => ?_⟩
    have e : a⁻¹ * p * a⁻¹⁻¹ * p⁻¹ = a⁻¹ * (a * p * a⁻¹ * p⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e, hEK a⁻¹ (K.inv_mem haK) _ (E.inv_mem (ha p hp))]
    exact E.inv_mem (ha p hp)

theorem le_pCoreOf_of_stabE {K A E : Subgroup G} (hEK : ∀ k ∈ K, ∀ e ∈ E, k * e * k⁻¹ = e)
    (hE2 : IsPGroup 2 E)
    (hcons : ∀ k ∈ K, (∀ p ∈ CFSG.Open.pCoreOf 2 K, p * k = k * p) →
      k ∈ CFSG.Open.pCoreOf 2 K)
    (hAK : A ≤ K)
    (hA : ∀ a ∈ A, ∀ p ∈ CFSG.Open.pCoreOf 2 K, a * p * a⁻¹ * p⁻¹ ∈ E) :
    A ≤ CFSG.Open.pCoreOf 2 K := by
  classical
  set P := CFSG.Open.pCoreOf 2 K with hP
  set S := stabSubE K P E hEK with hS
  have hSK : S ≤ K := fun a ha => ha.1
  have hnorm : ∀ k ∈ K, ∀ a ∈ S, k * a * k⁻¹ ∈ S := by
    rintro k hk a ⟨haK, ha⟩
    refine ⟨K.mul_mem (K.mul_mem hk haK) (K.inv_mem hk), fun p hp => ?_⟩
    have hp' : k⁻¹ * p * k ∈ P := by
      have := pCoreOf_normalized K (K.inv_mem hk) hp
      simpa using this
    have e : k * a * k⁻¹ * p * (k * a * k⁻¹)⁻¹ * p⁻¹ =
        k * (a * (k⁻¹ * p * k) * a⁻¹ * (k⁻¹ * p * k)⁻¹) * k⁻¹ := by group
    rw [e, hEK k hk _ (ha _ hp')]
    exact ha _ hp'
  have h2 : ∀ b ∈ S, ∃ j : ℕ, b ^ (2 ^ j) = 1 := by
    intro b hb
    obtain ⟨e, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos b).ne'
    refine ⟨e, ?_⟩
    set u : G := b ^ (2 ^ e) with hu
    have huS : u ∈ S := S.pow_mem hb _
    have hum : u ^ m = 1 := by
      rw [hu, ← pow_mul, ← hbm]
      exact pow_orderOf_eq_one b
    have hcomm : ∀ p ∈ P, p * u = u * p := by
      intro p hp
      obtain ⟨z, hz⟩ : ∃ z : G, z = u * p * u⁻¹ * p⁻¹ := ⟨_, rfl⟩
      have hzE : z ∈ E := hz ▸ huS.2 p hp
      have hpow : ∀ k : ℕ, u ^ k * p * (u ^ k)⁻¹ = z ^ k * p := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hz1 : u * z ^ k * u⁻¹ = z ^ k := hEK u huS.1 _ (E.pow_mem hzE k)
          have hz2 : u * p * u⁻¹ = z * p := by rw [hz]; group
          calc u ^ (k + 1) * p * (u ^ (k + 1))⁻¹
              = u * (u ^ k * p * (u ^ k)⁻¹) * u⁻¹ := by group
            _ = u * (z ^ k * p) * u⁻¹ := by rw [ih]
            _ = (u * z ^ k * u⁻¹) * (u * p * u⁻¹) := by group
            _ = z ^ (k + 1) * p := by rw [hz1, hz2, pow_succ, mul_assoc]
      have hzm : z ^ m = 1 := by
        have h1 := hpow m
        rw [hum] at h1
        have h3 : z ^ m * p = 1 * p := by rw [← h1]; group
        exact mul_right_cancel h3
      obtain ⟨j, hj⟩ := hE2 ⟨z, hzE⟩
      have hz2 : z ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      have hz1 : z = 1 := eq_one_of_pow_odd hm hzm hz2
      have : u * p * u⁻¹ = p := by
        have h4 : u * p * u⁻¹ * p⁻¹ = 1 := by rw [← hz]; exact hz1
        exact mul_inv_eq_one.1 h4
      calc p * u = (u * p * u⁻¹) * u := by rw [this]
        _ = u * p := by group
    have huK : u ∈ K := huS.1
    have huP : u ∈ P := hcons u huK hcomm
    obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf K huP
    exact eq_one_of_pow_odd hm hum hj
  have hS2 : IsPGroup 2 S := isPGroup_two_of_forall h2
  have hSP : S ≤ P := le_pCoreOf_of_normalized hSK hnorm hS2
  exact fun a ha => hSP ⟨hAK ha, hA a ha⟩

end H2

namespace SixSNorm

section Generic

variable {G : Type} [Group G] [Finite G]

theorem conjSubgroup_le_of_normalizer {H K : Subgroup G} (hKH : K ≤ H) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjSubgroup g K ≤ H := by
  intro y hy
  have h1 := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)).1 (hKH (mem_conjSubgroup.1 hy))
  simpa [mul_assoc] using h1

theorem comm_of_mem_conjSubgroup {K : Subgroup G} (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (g : G) : ∀ a ∈ conjSubgroup g K, ∀ b ∈ conjSubgroup g K, a * b = b * a := by
  intro a ha b hb
  have h1 := hK _ (mem_conjSubgroup.1 ha) _ (mem_conjSubgroup.1 hb)
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = b * a := by group

theorem card_conjSubgroup (K : Subgroup G) (g : G) :
    Nat.card ↥(conjSubgroup g K) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_zpowers_swap {i j : Fin 6} (hij : i ≠ j) :
    Nat.card ↥(Subgroup.zpowers (swap i j)) = 2 := by
  rw [Nat.card_zpowers]
  exact Equiv.Perm.IsSwap.orderOf ⟨i, j, hij, rfl⟩

variable {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

theorem mem_Q_of_theta_eq_one (hR : Nat.card ↥(Rc X) ≤ 2) {s : G} (hsM : s ∈ M)
    (h : C.θ ⟨s, hsM⟩ = 1) : s ∈ CFSG.Open.pCoreOf 2 M := by
  have : s ∈ C.K := C.mem_K.2 ⟨hsM, h⟩
  rwa [C.K_eq_Q hR] at this

end Generic

section Six

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 6)

theorem theta_eq_swap_of_mem_T2 (hR : Nat.card ↥(Rc X) ≤ 2) {i j : Fin 6} {t : G}
    (htT : t ∈ C.T2 i j) (htQ : t ∉ CFSG.Open.pCoreOf 2 M) (htM : t ∈ M) :
    C.θ ⟨t, htM⟩ = swap i j := by
  obtain ⟨_, h⟩ := C.mem_thetaPre.1 htT
  rcases SixS.mem_zpowers_swap h with h1 | h1
  · exact absurd (mem_Q_of_theta_eq_one C hR htM h1) htQ
  · exact h1

theorem T2_le_of_mem (hR : Nat.card ↥(Rc X) ≤ 2) {i j : Fin 6} {H : Subgroup G}
    (hQH : CFSG.Open.pCoreOf 2 M ≤ H) {t : G} (htT : t ∈ C.T2 i j)
    (htQ : t ∉ CFSG.Open.pCoreOf 2 M) (htH : t ∈ H) : C.T2 i j ≤ H := by
  intro s hs
  obtain ⟨hsM, hsθ⟩ := C.mem_thetaPre.1 hs
  obtain ⟨htM, -⟩ := C.mem_thetaPre.1 htT
  have ht : C.θ ⟨t, htM⟩ = swap i j := theta_eq_swap_of_mem_T2 C hR htT htQ htM
  rcases SixS.mem_zpowers_swap hsθ with h1 | h1
  · exact hQH (mem_Q_of_theta_eq_one C hR hsM h1)
  · have hM' : t⁻¹ * s ∈ M := M.mul_mem (M.inv_mem htM) hsM
    have hθ1 : C.θ ⟨t⁻¹ * s, hM'⟩ = 1 := by
      have e : (⟨t⁻¹ * s, hM'⟩ : ↥M) = ⟨t, htM⟩⁻¹ * ⟨s, hsM⟩ := rfl
      rw [e, map_mul, map_inv, ht, h1, inv_mul_cancel]
    have hQ' := hQH (mem_Q_of_theta_eq_one C hR hM' hθ1)
    have e2 : s = t * (t⁻¹ * s) := by group
    rw [e2]
    exact H.mul_mem htH hQ'

theorem mul_self_of_mem_sup {i j : Fin 6} (hij : i ≠ j) {σ : Perm (Fin 6)}
    (hσ : σ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6))) : σ * σ = 1 := by
  have hJ := SixS.card_compl_pair hij
  rcases (SixS.mem_sup_iff hij).1 hσ with h | h
  · exact ((mem_klein4_iff hJ).1 h).2
  · set v := σ * swap i j with hv
    have hv2 : v * v = 1 := ((mem_klein4_iff hJ).1 h).2
    have hc : v * swap i j = swap i j * v :=
      SixS.commute_swap_of_fix (SixS.klein4_fix hij h).1 (SixS.klein4_fix hij h).2
    have hττ : swap i j * swap i j = 1 := Equiv.swap_mul_self i j
    have e : σ = v * swap i j := by
      rw [hv, mul_assoc, hττ, mul_one]
    calc σ * σ = (v * swap i j) * (v * swap i j) := by rw [← e]
      _ = v * (swap i j * v) * swap i j := by group
      _ = v * (v * swap i j) * swap i j := by rw [← hc]
      _ = (v * v) * (swap i j * swap i j) := by group
      _ = 1 := by rw [hv2, hττ, one_mul]

theorem comm_of_mem_sup {i j : Fin 6} (hij : i ≠ j) {a b : Perm (Fin 6)}
    (ha : a ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)))
    (hb : b ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6))) :
    a * b = b * a := by
  have h1 := mul_self_of_mem_sup hij ha
  have h2 := mul_self_of_mem_sup hij hb
  have h3 := mul_self_of_mem_sup hij (Subgroup.mul_mem _ ha hb)
  have e : (a * b) * (a * b) * (b * a) = a * b := by
    calc (a * b) * (a * b) * (b * a) = a * b * a * (b * b) * a := by group
      _ = a * b * a * a := by rw [h2, mul_one]
      _ = a * b * (a * a) := by group
      _ = a * b := by rw [h1, mul_one]
  calc a * b = (a * b) * (a * b) * (b * a) := e.symm
    _ = b * a := by rw [h3, one_mul]

theorem eq_one_or_swap_of_stab_pairs {i j : Fin 6} (hij : i ≠ j) {σ : Perm (Fin 6)}
    (h : ∀ a ∈ ({i, j}ᶜ : Finset (Fin 6)), ∀ b ∈ ({i, j}ᶜ : Finset (Fin 6)), a ≠ b →
      σ ∈ setStab ({a, b} : Finset (Fin 6))) : σ = 1 ∨ σ = swap i j := by
  classical
  set J : Finset (Fin 6) := {i, j}ᶜ with hJ
  have hJc : J.card = 4 := SixS.card_compl_pair hij
  have hiJ : i ∉ J := by simp [hJ]
  have hjJ : j ∉ J := by simp [hJ]
  have hfixJ : ∀ a ∈ J, σ a = a := by
    intro a ha
    obtain ⟨b, hbJ, hb⟩ := exists_fourth hJc {a} (by simp)
    obtain ⟨c, hcJ, hc⟩ := exists_fourth hJc {a, b} (Finset.card_le_two.trans (by norm_num))
    simp only [Finset.mem_singleton] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨hca, hcb⟩ := hc
    have hab := h a ha b hbJ (Ne.symm hb)
    have hac := h a ha c hcJ (Ne.symm hca)
    have h1 : σ a ∈ ({a, b} : Finset (Fin 6)) := (mem_setStab.1 hab a).2 (by simp)
    have h2 : σ a ∈ ({a, c} : Finset (Fin 6)) := (mem_setStab.1 hac a).2 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) (Ne.symm hcb)
  have hout : ∀ y, y ∉ J → σ y ∉ J := by
    intro y hy hσy
    have h2 : σ y = y := σ.injective (hfixJ _ hσy)
    exact hy (h2 ▸ hσy)
  have hi : σ i = i ∨ σ i = j := by
    have h' := hout i hiJ
    simp only [hJ, Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton] at h'
    exact h'
  have hj : σ j = i ∨ σ j = j := by
    have h' := hout j hjJ
    simp only [hJ, Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton] at h'
    exact h'
  have hne : σ i ≠ σ j := fun e => hij (σ.injective e)
  have hy : ∀ y, y ∉ J → y = i ∨ y = j := by
    intro y hy'
    simp only [hJ, Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton] at hy'
    exact hy'
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact absurd (hi.trans hj.symm) hne
  · left
    refine Equiv.ext fun y => ?_
    by_cases hyJ : y ∈ J
    · simpa using hfixJ y hyJ
    · rcases hy y hyJ with rfl | rfl
      · simpa using hi
      · simpa using hj
  · right
    refine Equiv.ext fun y => ?_
    by_cases hyJ : y ∈ J
    · have hyi : y ≠ i := fun e => hiJ (e ▸ hyJ)
      have hyj : y ≠ j := fun e => hjJ (e ▸ hyJ)
      rw [hfixJ y hyJ, swap_apply_of_ne_of_ne hyi hyj]
    · rcases hy y hyJ with rfl | rfl
      · rw [hi, swap_apply_left]
      · rw [hj, swap_apply_right]
  · exact absurd (hi.trans hj.symm) hne

end Six

section PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem exists_piQ_eq_uvec (a b : Fin 6) :
    ∃ q : ↥(CFSG.Open.pCoreOf 2 M), Multiplicative.toAdd (D.piQ q) = uvec a b := by
  obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_Q (pairEW a b : altHeart 6))
  refine ⟨q, ?_⟩
  rw [hq]
  exact heartToBar_pairEW_eq_uvec a b

include D in
theorem exists_barLen_one_of_conj_le_T2 (hR : Nat.card ↥(Rc X) ≤ 2) (hRb : Rc X = ⊥)
    (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {i j : Fin 6} (hij : i ≠ j) {g : G}
    (hle : conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ C.T2 i j)
    (hne : conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≠ CFSG.Open.pCoreOf 2 M) :
    ∃ s : G, ∃ hs : s ∈ CFSG.Open.pCoreOf 2 M, s ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M) ∧
      barLen (Multiplicative.toAdd (D.piQ ⟨s, hs⟩)) = 1 := by
  classical
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  set Q' := conjSubgroup g Q with hQ'
  have hbij := D.piQ_bijective_of_bot hRb hQ16
  have hQcard : Nat.card ↥Q = 32 := by
    have h1 : Nat.card ↥Q = Nat.card (Multiplicative (permBar 6)) :=
      Nat.card_congr (Equiv.ofBijective _ hbij)
    have h2 : Nat.card (Multiplicative (permBar 6)) = Nat.card (permBar 6) :=
      Nat.card_congr Multiplicative.toAdd
    rw [h1, h2, Comb.card_permBar (by norm_num)]
    norm_num
  have hQ'M : Q' ≤ M := hle.trans (C.thetaPre_le_M _)
  have hQ'ab := SixSNorm.comm_of_mem_conjSubgroup (C.Q_comm hR) g
  have hQ'card : Nat.card ↥Q' = 32 := (SixSNorm.card_conjSubgroup Q g).trans hQcard
  obtain ⟨t, htQ', htQ⟩ : ∃ t ∈ Q', t ∉ Q := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_of_le_of_card_ge hcon (by rw [hQcard, hQ'card]))
  have htM : t ∈ M := hQ'M htQ'
  have htθ : C.θ ⟨t, htM⟩ = swap i j := SixSNorm.theta_eq_swap_of_mem_T2 C hR (hle htQ') htQ htM
  set Z : Subgroup G := Q ⊓ Q' with hZ
  have hZQ : ∀ z : ↥Z, (z : G) ∈ Q := fun z => (Subgroup.mem_inf.1 z.2).1
  have hfix : ∀ z : ↥Z, barAct (swap i j) (Multiplicative.toAdd (D.piQ ⟨(z : G), hZQ z⟩)) =
      Multiplicative.toAdd (D.piQ ⟨(z : G), hZQ z⟩) := by
    intro z
    have hcomm : (t : G) * z * t⁻¹ = z :=
      mul_inv_eq_iff_eq_mul.2 (hQ'ab t htQ' z (Subgroup.mem_inf.1 z.2).2)
    have h := D.piQ_conj ⟨t, htM⟩ ⟨z, hZQ z⟩ ⟨z, hZQ z⟩ hcomm.symm
    rw [htθ] at h
    exact h.symm
  have hZcard : 16 ≤ Nat.card ↥Z := by
    have h1 := C.card_eq_card_inf_mul hR hQ'M
    have h2 : Nat.card ↥((Q'.subgroupOf M).map C.θ) ≤ 2 := by
      have hsub : (Q'.subgroupOf M).map C.θ ≤ Subgroup.zpowers (swap i j) := by
        rintro σ ⟨m, hm, rfl⟩
        obtain ⟨_, h⟩ := C.mem_thetaPre.1 (hle (Subgroup.mem_subgroupOf.1 hm))
        exact h
      calc Nat.card ↥((Q'.subgroupOf M).map C.θ)
          ≤ Nat.card ↥(Subgroup.zpowers (swap i j)) := Subgroup.card_le_of_le hsub
        _ = 2 := SixSNorm.card_zpowers_swap hij
    have h3 : Nat.card ↥(Q' ⊓ Q) = Nat.card ↥Z := by rw [hZ, inf_comm]
    rw [hQ'card, h3] at h1
    by_contra hlt
    have hZ15 : Nat.card ↥Z ≤ 15 := by omega
    have := Nat.mul_le_mul hZ15 h2
    omega
  have hZfix : ∀ z : ↥Z, Multiplicative.toAdd (D.piQ ⟨(z : G), hZQ z⟩) ∈
      Comb.fixSub ({swap i j} : Set (Perm (Fin 6))) := by
    intro z σ hσ
    rw [Set.mem_singleton_iff.1 hσ]
    exact hfix z
  let f : ↥Z → ↥(Comb.fixSub ({swap i j} : Set (Perm (Fin 6)))) := fun z =>
    ⟨Multiplicative.toAdd (D.piQ ⟨(z : G), hZQ z⟩), hZfix z⟩
  have hf : Function.Injective f := by
    intro z z' h
    have h1 : Multiplicative.toAdd (D.piQ ⟨(z : G), hZQ z⟩) =
        Multiplicative.toAdd (D.piQ ⟨(z' : G), hZQ z'⟩) := congrArg Subtype.val h
    have h2 := hbij.1 (Multiplicative.toAdd.injective h1)
    exact Subtype.ext (Subtype.mk.inj h2)
  have hcardfix : Nat.card ↥(Comb.fixSub ({swap i j} : Set (Perm (Fin 6)))) = 16 := by
    rw [Comb.card_fixSub_swap (by norm_num) i j hij]
    norm_num
  have hbijf := hf.bijective_of_nat_card_le (by rw [hcardfix]; exact hZcard)
  obtain ⟨k, hkJ⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty :=
    Finset.card_pos.1 (by rw [SixS.card_compl_pair hij]; norm_num)
  have hk := Finset.mem_compl.1 hkJ
  have hki : k ≠ i := fun h => hk (by simp [h])
  have hkj : k ≠ j := fun h => hk (by simp [h])
  have hkfix : barInd ({k} : Finset (Fin 6)) ∈ Comb.fixSub ({swap i j} : Set (Perm (Fin 6))) := by
    intro σ hσ
    rw [Set.mem_singleton_iff.1 hσ, barAct_barInd, Finset.image_singleton,
      swap_apply_of_ne_of_ne hki hkj]
  obtain ⟨z, hz⟩ := hbijf.2 ⟨barInd {k}, hkfix⟩
  refine ⟨(z : G), hZQ z, (Subgroup.mem_inf.1 z.2).2, ?_⟩
  have h1 : Multiplicative.toAdd (D.piQ ⟨(z : G), hZQ z⟩) = barInd {k} := congrArg Subtype.val hz
  rw [h1, barLen_barInd, Finset.card_singleton]
  norm_num

end PiData

end SixSNorm

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem normalizer_T1_le (hR : Nat.card ↥(Rc X) ≤ 2) {i j : Fin 6} (hij : i ≠ j) :
    Subgroup.normalizer ((C.T1 i j : Subgroup G) : Set G) ≤ M := by
  obtain ⟨D⟩ := C.exists_piData (by norm_num) (by decide)
  intro g hg
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hJ := SixS.card_compl_pair hij
  have hQT : Q ≤ C.T1 i j := C.Q_le_thetaPre hR _
  have hQgT : conjSubgroup g Q ≤ C.T1 i j := SixSNorm.conjSubgroup_le_of_normalizer hQT hg
  have hAM : conjSubgroup g Q ≤ M := hQgT.trans (C.thetaPre_le_M _)
  have hFN : ((conjSubgroup g Q).subgroupOf M).map C.θ ≤
      klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
    rintro σ ⟨m, hm, rfl⟩
    obtain ⟨hmM, hmθ⟩ := C.mem_thetaPre.1 (hQgT (Subgroup.mem_subgroupOf.1 hm))
    exact hmθ
  have heq := D.eq_Q_of_theta_le_klein4 hR hJ hAM hFN
    (SixSNorm.comm_of_mem_conjSubgroup (C.Q_comm hR) g)
    (SixSNorm.card_conjSubgroup Q g).ge
  rw [← C.S.normalizer_Q_eq]
  exact TI.mem_normalizer_iff_conj.2 heq

theorem normalizer_T2_le (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
    (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {i j : Fin 6} (hij : i ≠ j) :
    Subgroup.normalizer ((C.T2 i j : Subgroup G) : Set G) ≤ M := by
  obtain ⟨D⟩ := C.exists_piData (by norm_num) (by decide)
  intro g hg
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQgT : conjSubgroup g Q ≤ C.T2 i j :=
    SixSNorm.conjSubgroup_le_of_normalizer (C.Q_le_thetaPre hR _) hg
  by_cases hQg : conjSubgroup g Q = Q
  · rw [← C.S.normalizer_Q_eq]
    exact TI.mem_normalizer_iff_conj.2 hQg
  suffices hgM : g⁻¹ ∈ M by simpa using M.inv_mem hgM
  by_cases hRb : Rc X = ⊥
  · obtain ⟨s, hsQ, hsQg, hl⟩ :=
      SixSNorm.exists_barLen_one_of_conj_le_T2 D hR hRb hQ16 hij hQgT hQg
    have hs1 : s ≠ 1 := by
      rintro rfl
      have h1 : D.piQ ⟨1, hsQ⟩ = 1 := map_one D.piQ
      rw [h1, toAdd_one, H4b.barLen_zero'] at hl
      exact absurd hl (by norm_num)
    exact D.mem_M_of_conj_len_ne_two hR hsurj hsQ hs1 (by omega) (g := g⁻¹)
      (by simpa using mem_conjSubgroup.1 hsQg)
  · obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRb
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
    have hrR : r ∈ Rc X := hr
    have hrQ : r ∈ Q := by
      have h := hr
      rw [C.S.R_eq_inf] at h
      exact (Subgroup.mem_inf.1 h).1
    have hconj : g⁻¹ * r * g ∈ Q := by
      have hCQ := C.centralizer_Q_eq hR
      rw [← hQ] at hCQ
      rw [← hCQ, Subgroup.mem_centralizer_iff]
      intro q hq
      have hgq : g * q * g⁻¹ ∈ conjSubgroup g Q :=
        mem_conjSubgroup.2 (by simpa [mul_assoc] using hq)
      have hgqM : g * q * g⁻¹ ∈ M := (C.thetaPre_le_M _) (hQgT hgq)
      have hc := mul_inv_eq_iff_eq_mul.1 (C.S.R_central hR hgqM hrR)
      calc q * (g⁻¹ * r * g) = g⁻¹ * ((g * q * g⁻¹) * r) * g := by group
        _ = g⁻¹ * (r * (g * q * g⁻¹)) * g := by rw [hc]
        _ = (g⁻¹ * r * g) * q := by group
    have hl : barLen (Multiplicative.toAdd (D.piQ ⟨r, hrQ⟩)) ≠ 2 := by
      rw [(D.piQ_eq_one_iff ⟨r, hrQ⟩).2 hr, toAdd_one, H4b.barLen_zero']
      norm_num
    exact D.mem_M_of_conj_len_ne_two hR hsurj hrQ hr1' hl (g := g⁻¹) (by simpa using hconj)

variable (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j})
include hR hsurj hQ16 hij hπ

theorem centralizer_commutator_le_T2 :
    M ⊓ Subgroup.centralizer
      ((⁅CFSG.Open.pCoreOf 2 M, TOf M x⁆ : Subgroup G) : Set G) ≤ C.T2 i j := by
  classical
  intro m hm
  obtain ⟨hmM, hmc⟩ := Subgroup.mem_inf.1 hm
  set J : Finset (Fin 6) := {i, j}ᶜ with hJdef
  have hJ : J.card = 4 := SixS.card_compl_pair hij
  have hF := klein4_fourGroup hJ
  have hN1 : klein4 J ≠ ⊥ := by
    intro h
    have := card_klein4 hJ
    rw [h, Subgroup.card_bot] at this
    omega
  have hstab : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → C.θ ⟨m, hmM⟩ ∈ setStab ({a, b} : Finset (Fin 6)) := by
    intro a haJ b hbJ hab
    obtain ⟨q, hq⟩ := SixSNorm.exists_piQ_eq_uvec D b i
    obtain ⟨σ, hσK, hσb⟩ := hF.transitive hJ hN1 hbJ haJ
    obtain ⟨hσi, -⟩ := SixS.klein4_fix hij hσK
    have hσT : σ ∈ C.thetaN x := D.klein4_le_thetaN_six hR hx (Finset.card_pair hij) hπ hσK
    obtain ⟨t, htT, htσ⟩ := C.mem_thetaN.1 hσT
    have htM : (t : G) ∈ M := t.2
    have hq' : (t : G) * q * (t : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M htM q.2
    have hπq' := D.piQ_conj t q ⟨(t : G) * q * (t : G)⁻¹, hq'⟩ rfl
    rw [htσ, hq, barAct_uvec, hσb, hσi] at hπq'
    set c : ↥(CFSG.Open.pCoreOf 2 M) := q * ⟨(t : G) * q * (t : G)⁻¹, hq'⟩⁻¹ with hc
    have hcG : (c : G) = ⁅(q : G), (t : G)⁆ := by
      show (q : G) * ((t : G) * q * (t : G)⁻¹)⁻¹ = _
      simp only [commutatorElement_def]
      group
    have hcmem : (c : G) ∈ ⁅CFSG.Open.pCoreOf 2 M, TOf M x⁆ := by
      rw [hcG]
      exact Subgroup.commutator_mem_commutator q.2 htT
    have hπc : Multiplicative.toAdd (D.piQ c) = uvec a b := by
      rw [hc, map_mul, map_inv, toAdd_mul, toAdd_inv, hπq', hq, add_comm]
      exact neg_uvec_add_uvec a b i
    have hmcomm : (c : G) = m * c * m⁻¹ :=
      (mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hmc _ hcmem).symm).symm
    have h1 := D.piQ_conj ⟨m, hmM⟩ c c hmcomm
    rw [hπc, H4b.uvec_eq_barInd hab] at h1
    exact (barAct_barInd_eq_self_iff (by rw [Finset.card_pair hab]; norm_num) _).1 h1.symm
  rcases SixSNorm.eq_one_or_swap_of_stab_pairs hij hstab with h | h
  · exact C.mem_thetaPre.2 ⟨hmM, by rw [h]; exact Subgroup.one_mem _⟩
  · exact C.mem_thetaPre.2 ⟨hmM, by rw [h]; exact Subgroup.mem_zpowers _⟩

theorem normalizer_le_of_commutator_le {E : Subgroup G}
    (hQ1E : ⁅CFSG.Open.pCoreOf 2 M, TOf M x⁆ ≤ E) (hEQ : E ≤ CFSG.Open.pCoreOf 2 M) :
    Subgroup.normalizer (E : Set G) ≤ M := by
  classical
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQab := C.Q_comm hR
  have hE2 : IsPGroup 2 E := isPGroup_of_le (isPGroup_pCoreOf' M) hEQ
  set C₀ : Subgroup G := Subgroup.centralizer (E : Set G) with hC₀
  set P₀ : Subgroup G := CFSG.Open.pCoreOf 2 C₀ with hP₀
  have hQC₀ : Q ≤ C₀ := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun e he => hQab e (hEQ he) q hq
  have hCET2 : M ⊓ C₀ ≤ C.T2 i j := fun c hc =>
    D.centralizer_commutator_le_T2 hR hsurj hQ16 hx hij hπ
      ⟨hc.1, Subgroup.centralizer_le
        (show ((⁅Q, TOf M x⁆ : Subgroup G) : Set G) ⊆ (E : Set G) from hQ1E) hc.2⟩
  have hEbot : E ≠ ⊥ := by
    intro hE
    have hMT2 : ∀ m ∈ M, m ∈ C.T2 i j := fun m hm => hCET2 ⟨hm, by
      rw [hC₀]
      refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
      have he1 : e = 1 := by
        rw [hE] at he
        exact Subgroup.mem_bot.1 he
      rw [he1, one_mul, mul_one]⟩
    obtain ⟨k, hkJ⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty :=
      Finset.card_pos.1 (by rw [SixS.card_compl_pair hij]; norm_num)
    have hk := Finset.mem_compl.1 hkJ
    have hki : i ≠ k := fun h => hk (by simp [h])
    have hkj : j ≠ k := fun h => hk (by simp [h])
    obtain ⟨m, hm⟩ := hsurj (swap i k)
    obtain ⟨_, hθ⟩ := C.mem_thetaPre.1 (hMT2 m m.2)
    have hmθ : C.θ m = swap i k := hm
    rcases SixS.mem_zpowers_swap (show C.θ ⟨(m : G), m.2⟩ ∈ Subgroup.zpowers (swap i j) from hθ)
      with h1 | h1
    · have h2 := congrArg (fun f : Perm (Fin 6) => f i) (hmθ.symm.trans h1)
      simp only [swap_apply_left, Perm.one_apply] at h2
      exact hki h2.symm
    · have h2 := congrArg (fun f : Perm (Fin 6) => f i) (hmθ.symm.trans h1)
      simp only [swap_apply_left] at h2
      exact hkj h2.symm
  have hcons2 : C₀ ⊓ Subgroup.centralizer (P₀ : Set G) ≤ P₀ :=
    centralizer_two_constrained C.S.charTwo hEbot hE2
  have hcons : ∀ k ∈ C₀, (∀ p ∈ P₀, p * k = k * p) → k ∈ P₀ := fun k hk hc =>
    hcons2 ⟨hk, Subgroup.mem_centralizer_iff.2 hc⟩
  have hgN : ∀ g ∈ Subgroup.normalizer (E : Set G), g ∈ Subgroup.normalizer (P₀ : Set G) := by
    intro g hg
    have hnorm : ∀ n ∈ Subgroup.normalizer (E : Set G), ∀ k ∈ C₀, n * k * n⁻¹ ∈ C₀ :=
      fun n hn k hk => centralizer_normalized hn hk
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => pCoreOf_normalized_of_normal hnorm hg hp, fun hp => ?_⟩
    have := pCoreOf_normalized_of_normal hnorm ((Subgroup.normalizer (E : Set G)).inv_mem hg) hp
    simpa [mul_assoc] using this
  by_cases hP₀Q : P₀ ≤ Q
  ·
    have hQP₀ : Q ≤ P₀ := fun q hq =>
      hcons2 ⟨hQC₀ hq, Subgroup.mem_centralizer_iff.2 fun p hp => hQab p (hP₀Q hp) q hq⟩
    have hPQ : P₀ = Q := le_antisymm hP₀Q hQP₀
    intro g hg
    have h1 := hgN g hg
    rw [hPQ] at h1
    rw [← C.S.normalizer_Q_eq]
    exact h1
  ·
    have hP₀2 : IsPGroup 2 P₀ := isPGroup_pCoreOf' C₀
    have hQnormP₀ : Q ≤ Subgroup.normalizer (P₀ : Set G) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro p
      refine ⟨fun hp => pCoreOf_normalized C₀ (hQC₀ hq) hp, fun hp => ?_⟩
      have := pCoreOf_normalized C₀ (C₀.inv_mem (hQC₀ hq)) hp
      simpa [mul_assoc] using this
    set H : Subgroup G := P₀ ⊔ Q with hH
    have hH2 : IsPGroup 2 H := hP₀2.to_sup_of_normal_left' (isPGroup_pCoreOf' M) hQnormP₀
    have hHC₀ : H ≤ C₀ := sup_le (pCoreOf_le_self C₀) hQC₀
    have hHMle : H ⊓ M ≤ C.T2 i j := fun h hh => hCET2 ⟨hh.2, hHC₀ hh.1⟩
    have hQH : Q ≠ H := fun heq => hP₀Q (by rw [heq]; exact le_sup_left)
    obtain ⟨t, htH, htQ, htN⟩ := exists_mem_normalizer_of_lt hH2 le_sup_right hQH
    have htM : t ∈ M := by
      rw [← C.S.normalizer_Q_eq]
      exact htN
    have hT2H : C.T2 i j ≤ H :=
      SixSNorm.T2_le_of_mem C hR le_sup_right (hHMle ⟨htH, htM⟩) htQ htH
    have hHT2 : H = C.T2 i j := by
      by_contra hne
      obtain ⟨h, hhH, hhT, hhN⟩ := exists_mem_normalizer_of_lt hH2 hT2H (Ne.symm hne)
      exact hhT (hHMle ⟨hhH, normalizer_T2_le hR hsurj hQ16 hij hhN⟩)
    have hP₀T : P₀ ≤ TOf M x :=
      (le_sup_left.trans hHT2.le).trans (D.T2_le_TOf hR hsurj hx hij hπ)
    have hQP₀ : Q ≤ P₀ := by
      refine H2.le_pCoreOf_of_stabE (K := C₀) (E := E) (fun k hk e he => ?_) hE2 hcons hQC₀
        (fun a ha p hp => ?_)
      · exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hk e he).symm
      · exact hQ1E (Subgroup.commutator_mem_commutator ha (hP₀T hp))
    have hP₀eq : P₀ = C.T2 i j := by
      refine le_antisymm (le_sup_left.trans hHT2.le) ?_
      have hHP₀ : H ≤ P₀ := sup_le le_rfl hQP₀
      rw [← hHT2]
      exact hHP₀
    intro g hg
    have h1 := hgN g hg
    rw [hP₀eq] at h1
    exact normalizer_T2_le hR hsurj hQ16 hij h1

theorem normalizer_TOf_le : Subgroup.normalizer ((TOf M x : Subgroup G) : Set G) ≤ M := by
  classical
  set T := TOf M x with hT
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQT : Q ≤ T := Q_le_TOf (C.Q_comm hR) hx
  have hTM : T ≤ M := TOf_le_M M x
  have hTT : ⁅T, T⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haM := hTM ha
    have hbM := hTM hb
    have hθa : C.θ ⟨a, haM⟩ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
      rw [← D.thetaN_eq_sym hR hsurj hx hij hπ]
      exact C.mem_thetaN.2 ⟨⟨a, haM⟩, ha, rfl⟩
    have hθb : C.θ ⟨b, hbM⟩ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
      rw [← D.thetaN_eq_sym hR hsurj hx hij hπ]
      exact C.mem_thetaN.2 ⟨⟨b, hbM⟩, hb, rfl⟩
    have hcomm := SixSNorm.comm_of_mem_sup hij hθa hθb
    have hcM : ⁅a, b⁆ ∈ M := by
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem haM hbM) (M.inv_mem haM)) (M.inv_mem hbM)
    refine SixSNorm.mem_Q_of_theta_eq_one C hR hcM ?_
    have e : (⟨⁅a, b⁆, hcM⟩ : ↥M) = ⁅(⟨a, haM⟩ : ↥M), (⟨b, hbM⟩ : ↥M)⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_def, hcomm]
    group
  intro g hg
  have hconj : conjSubgroup g T = T := TI.mem_normalizer_iff_conj.1 hg
  have hcT : conjSubgroup g ⁅T, T⁆ = ⁅T, T⁆ := by
    have h1 : conjSubgroup g ⁅T, T⁆ = ⁅conjSubgroup g T, conjSubgroup g T⁆ :=
      Subgroup.map_commutator T T (MulAut.conj g).toMonoidHom
    rw [h1, hconj]
  have hgE : g ∈ Subgroup.normalizer ((⁅T, T⁆ : Subgroup G) : Set G) :=
    TI.mem_normalizer_iff_conj.2 hcT
  exact D.normalizer_le_of_commutator_le hR hsurj hQ16 hx hij hπ
    (Subgroup.commutator_mono hQT le_rfl) hTT hgE

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
