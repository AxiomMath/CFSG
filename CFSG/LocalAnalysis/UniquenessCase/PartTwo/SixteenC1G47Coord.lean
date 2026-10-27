module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47CoordDefs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_coord_elem {U N : Subgroup G} (hNU : N ≤ U)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hUsq : ∀ x ∈ U, x * x = 1)
    (hU : Nat.card ↥U = 32) (hNc : Nat.card ↥N = 2) :
    ∃ κ : G → (Fin 4 → ZMod 2), (∀ u ∈ U, ∀ u' ∈ U, κ (u * u') = κ u + κ u') ∧
      (∀ u ∈ U, κ u = 0 ↔ u ∈ N) ∧ ∀ x : Fin 4 → ZMod 2, ∃ u ∈ U, κ u = x := by
  classical
  have hnormal : (N.subgroupOf U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) = (n : G) * (g : G) := hUab (g : G) g.2 (n : G) (hNU hn)
    have h2 : ((g * n * g⁻¹ : ↥U) : G) = (n : G) := by
      show (g : G) * (n : G) * (g : G)⁻¹ = (n : G)
      rw [h1]
      group
    rw [h2]
    exact hn
  letI := hnormal
  let Q := ↥U ⧸ N.subgroupOf U
  have hQcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a ?_
    intro a
    refine QuotientGroup.induction_on b ?_
    intro b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have hsub : a * b = b * a := Subtype.ext (hUab (a : G) a.2 (b : G) b.2)
    exact congrArg QuotientGroup.mk hsub
  have hQpow : ∀ a : Q, a ^ 2 = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro a
    have hsq : (a : ↥U) * a = 1 := Subtype.ext (hUsq (a : G) a.2)
    rw [← QuotientGroup.mk_pow, pow_two, hsq, QuotientGroup.mk_one]
  have hNsubcard : Nat.card ↥(N.subgroupOf U) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNU).toEquiv]
    exact hNc
  have hQcard : Nat.card Q = 2 ^ 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf U)
    rw [hNsubcard, hU] at h
    have h32 : Nat.card Q * 2 = 32 := h.symm
    have h16 : Nat.card Q = 16 := by omega
    rw [h16]
    norm_num
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 2) (W := Q) hQcomm hQpow (n := 4) hQcard
  let κ : G → (Fin 4 → ZMod 2) := fun g =>
    if h : g ∈ U then (e ((⟨g, h⟩ : ↥U) : Q)).toAdd else 0
  have hκ_mem : ∀ g (h : g ∈ U), κ g = (e ((⟨g, h⟩ : ↥U) : Q)).toAdd := by
    intro g h
    simp only [κ, dif_pos h]
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro u hu u' hu'
    rw [hκ_mem (u * u') (U.mul_mem hu hu'), hκ_mem u hu, hκ_mem u' hu']
    have hsub : ((⟨u * u', U.mul_mem hu hu'⟩ : ↥U) : Q) =
        ((⟨u, hu⟩ : ↥U) : Q) * ((⟨u', hu'⟩ : ↥U) : Q) := by
      rw [← QuotientGroup.mk_mul]
      rfl
    rw [hsub, map_mul, toAdd_mul]
  · intro u hu
    rw [hκ_mem u hu, toAdd_eq_zero, e.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  · intro x
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm (Multiplicative.ofAdd x))
    refine ⟨(a : G), a.2, ?_⟩
    rw [hκ_mem (a : G) a.2]
    have h : e ((a : ↥U) : Q) = Multiplicative.ofAdd x := by
      rw [ha, MulEquiv.apply_symm_apply]
    rw [h, toAdd_ofAdd]

theorem s16c1_G47_coord_dual {K U B N : Subgroup G} (hUK : U ≤ K) (hBK : B ≤ K)
    (hN : N = U ⊓ B) (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hNcent : ∀ n ∈ N, ∀ k ∈ K, k * n = n * k)
    (hBZ : ∀ b ∈ B, (∀ u ∈ U, u * b = b * u) → b ∈ U)
    (hB : Nat.card ↥B = 32) (hNc : Nat.card ↥N = 2) {κU : G → (Fin 4 → ZMod 2)}
    (hadd : ∀ u ∈ U, ∀ u' ∈ U, κU (u * u') = κU u + κU u')
    (hker : ∀ u ∈ U, κU u = 0 ↔ u ∈ N) (hsurj : ∀ x : Fin 4 → ZMod 2, ∃ u ∈ U, κU u = x) :
    ∃ κB : G → (Fin 4 → ZMod 2), (∀ b ∈ B, ∀ b' ∈ B, κB (b * b') = κB b + κB b') ∧
      (∀ b ∈ B, κB b = 0 ↔ b ∈ N) ∧ (∀ y : Fin 4 → ZMod 2, ∃ b ∈ B, κB b = y) ∧
      ∀ u ∈ U, ∀ b ∈ B, ⁅u, b⁆ = 1 ↔ dotProduct (κU u) (κB b) = 0 := by
  classical
  have hNU : N ≤ U := by rw [hN]; exact inf_le_left
  have hNB : N ≤ B := by rw [hN]; exact inf_le_right
  have hNK : N ≤ K := hNU.trans hUK
  let ν : G → ZMod 2 := fun n => if n = 1 then 0 else 1
  have hν_zero : ∀ n : G, ν n = 0 ↔ n = 1 := by
    intro n
    simp only [ν]
    by_cases h : n = 1
    · simp [h]
    · simp [h]
  have hν_one : ν 1 = 0 := (hν_zero 1).mpr rfl
  have hN2 : ∀ n ∈ N, n * n = 1 := by
    intro n hn
    have h := pow_card_eq_one' (G := ↥N) (x := ⟨n, hn⟩)
    rw [hNc] at h
    have h' : (⟨n, hn⟩ : ↥N) * ⟨n, hn⟩ = 1 := by
      rwa [pow_two] at h
    simpa using congrArg Subtype.val h'
  have hνmul : ∀ n ∈ N, ∀ n' ∈ N, ν (n * n') = ν n + ν n' := by
    intro n hn n' hn'
    by_cases hn1 : n = 1
    · subst n
      simp [hν_one]
    by_cases hn'1 : n' = 1
    · subst n'
      simp [hν_one]
    obtain ⟨n0, _hn0, huniq⟩ := (Nat.card_eq_two_iff' (α := ↥N) 1).mp hNc
    have hnn : n = n' := by
      have h1 : (⟨n, hn⟩ : ↥N) = n0 := huniq ⟨n, hn⟩ (by simpa using hn1)
      have h2 : (⟨n', hn'⟩ : ↥N) = n0 := huniq ⟨n', hn'⟩ (by simpa using hn'1)
      exact congrArg Subtype.val (h1.trans h2.symm)
    have hn'ν : ν n' = 1 := by simp [ν, hn'1]
    subst n
    rw [hN2 n' hn', hν_one, hn'ν]
    decide
  have hcommN : ∀ u ∈ U, ∀ b ∈ B, ⁅u, b⁆ ∈ N := by
    intro u hu b hb
    exact hKcomm u (hUK hu) b (hBK hb)
  have hcomm_mul_left : ∀ u ∈ U, ∀ u' ∈ U, ∀ b ∈ B,
      ⁅u * u', b⁆ = ⁅u, b⁆ * ⁅u', b⁆ := by
    intro u hu u' hu' b hb
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hc : ⁅u', b⁆ ∈ N := hcommN u' hu' b hb
    have hub : u * ⁅u', b⁆ = ⁅u', b⁆ * u := hNcent _ hc u (hUK hu)
    calc u * ⁅u', b⁆ * u⁻¹ * ⁅u, b⁆
        = (u * ⁅u', b⁆ * u⁻¹) * ⁅u, b⁆ := by group
      _ = ⁅u', b⁆ * ⁅u, b⁆ := by rw [hub]; group
      _ = ⁅u, b⁆ * ⁅u', b⁆ := by
            rw [hNcent ⁅u, b⁆ (hcommN u hu b hb) ⁅u', b⁆ (hNK hc)]
  have hcomm_mul_right : ∀ u ∈ U, ∀ b ∈ B, ∀ b' ∈ B,
      ⁅u, b * b'⁆ = ⁅u, b⁆ * ⁅u, b'⁆ := by
    intro u hu b hb b' hb'
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hc : ⁅u, b'⁆ ∈ N := hcommN u hu b' hb'
    have hbb : b * ⁅u, b'⁆ = ⁅u, b'⁆ * b := hNcent _ hc b (hBK hb)
    calc ⁅u, b⁆ * b * ⁅u, b'⁆ * b⁻¹
        = ⁅u, b⁆ * (b * ⁅u, b'⁆ * b⁻¹) := by group
      _ = ⁅u, b⁆ * ⁅u, b'⁆ := by rw [hbb]; group
  choose ux huxU huxκ using hsurj
  let Fb : G → (Fin 4 → ZMod 2) → ZMod 2 := fun b x => ν ⁅ux x, b⁆
  let κB : G → (Fin 4 → ZMod 2) := fun b i => ν ⁅ux (Pi.single i 1), b⁆
  have hκB_apply : ∀ b i, κB b i = Fb b (Pi.single i 1) := fun _ _ => rfl
  have hker_ratio : ∀ u ∈ U, ∀ u' ∈ U, κU u = κU u' → u⁻¹ * u' ∈ N := by
    intro u hu u' hu' h
    have hzero1 : κU 1 = 0 := (hker 1 (hNU N.one_mem)).mpr N.one_mem
    have hinv : κU u⁻¹ = - κU u := by
      have h1 : κU (u * u⁻¹) = κU u + κU u⁻¹ := hadd u hu u⁻¹ (U.inv_mem hu)
      rw [mul_inv_cancel u, hzero1] at h1
      exact eq_neg_of_add_eq_zero_right h1.symm
    have hzero : κU (u⁻¹ * u') = 0 := by
      rw [hadd u⁻¹ (U.inv_mem hu) u' hu', hinv, ← h]
      exact neg_add_cancel _
    exact (hker (u⁻¹ * u') (U.mul_mem (U.inv_mem hu) hu')).mp hzero
  have hFb_eq : ∀ b ∈ B, ∀ u ∈ U, ν ⁅u, b⁆ = Fb b (κU u) := by
    intro b hb u hu
    have hratio : u⁻¹ * ux (κU u) ∈ N :=
      hker_ratio u hu (ux (κU u)) (huxU _) (huxκ _).symm
    have hux_eq : ux (κU u) = u * (u⁻¹ * ux (κU u)) := by group
    have hnb : ⁅u⁻¹ * ux (κU u), b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hNcent (u⁻¹ * ux (κU u)) hratio b (hBK hb)).symm
    have hcomm_eq : ⁅ux (κU u), b⁆ = ⁅u, b⁆ := by
      rw [hux_eq, hcomm_mul_left u hu (u⁻¹ * ux (κU u)) (hNU hratio) b hb, hnb,
        mul_one]
    show ν ⁅u, b⁆ = ν ⁅ux (κU u), b⁆
    rw [hcomm_eq]
  have hFb_add : ∀ b ∈ B, ∀ x x' : Fin 4 → ZMod 2,
      Fb b (x + x') = Fb b x + Fb b x' := by
    intro b hb x x'
    have hprodU : ux x * ux x' ∈ U := U.mul_mem (huxU x) (huxU x')
    have hprodκ : κU (ux x * ux x') = x + x' := by
      rw [hadd (ux x) (huxU x) (ux x') (huxU x'), huxκ x, huxκ x']
    have h1 := hFb_eq b hb (ux x * ux x') hprodU
    rw [hprodκ] at h1
    rw [← h1, hcomm_mul_left (ux x) (huxU x) (ux x') (huxU x') b hb]
    exact hνmul _ (hcommN _ (huxU x) b hb) _ (hcommN _ (huxU x') b hb)
  have hFb_lin : ∀ b ∈ B, ∀ x, Fb b x = dotProduct x (κB b) := by
    intro b hb x
    let L : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      @AddMonoidHom.toZModLinearMap 2 (Fin 4 → ZMod 2) (ZMod 2)
        (inferInstance : AddCommGroup (Fin 4 → ZMod 2))
        (inferInstance : AddCommGroup (ZMod 2))
        (Pi.Function.module (Fin 4) (ZMod 2) (ZMod 2))
        (inferInstance : Module (ZMod 2) (ZMod 2))
        (AddMonoidHom.mk' (Fb b) (hFb_add b hb))
    have hLx : L x = Fb b x := rfl
    rw [← hLx, LinearMap.pi_apply_eq_sum_univ, dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hsingle : (fun j : Fin 4 => if i = j then (1 : ZMod 2) else 0) =
        Pi.single i 1 := by
      funext j
      rw [Pi.single_apply]
      by_cases h : j = i
      · subst j
        simp
      · have h' : i ≠ j := fun hh => h hh.symm
        simp [h, h']
    rw [smul_eq_mul]
    have hLi : L (fun j : Fin 4 => if i = j then (1 : ZMod 2) else 0) = κB b i := by
      rw [hsingle]
      exact (hκB_apply b i).symm
    rw [hLi]
  have hBadd : ∀ b ∈ B, ∀ b' ∈ B, κB (b * b') = κB b + κB b' := by
    intro b hb b' hb'
    funext i
    show ν ⁅ux (Pi.single i 1), b * b'⁆ = ν ⁅ux (Pi.single i 1), b⁆ +
      ν ⁅ux (Pi.single i 1), b'⁆
    rw [hcomm_mul_right (ux (Pi.single i 1)) (huxU _) b hb b' hb']
    exact hνmul _ (hcommN _ (huxU _) b hb) _ (hcommN _ (huxU _) b' hb')
  have hpair : ∀ u ∈ U, ∀ b ∈ B, ⁅u, b⁆ = 1 ↔
      dotProduct (κU u) (κB b) = 0 := by
    intro u hu b hb
    rw [← hν_zero ⁅u, b⁆, hFb_eq b hb u hu, hFb_lin b hb (κU u)]
  have hBker : ∀ b ∈ B, κB b = 0 ↔ b ∈ N := by
    intro b hb
    constructor
    · intro hzero
      have hbU : b ∈ U := by
        apply hBZ b hb
        intro u hu
        have hdot : dotProduct (κU u) (κB b) = 0 := by simp [hzero]
        exact commutatorElement_eq_one_iff_mul_comm.mp ((hpair u hu b hb).mpr hdot)
      rw [hN]
      exact ⟨hbU, hb⟩
    · intro hbN
      funext i
      show ν ⁅ux (Pi.single i 1), b⁆ = 0
      rw [hν_zero]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (hNcent b hbN (ux (Pi.single i 1)) (hUK (huxU _)))
  have hBone : κB 1 = 0 := (hBker 1 B.one_mem).mpr N.one_mem
  have hNsubcardB : Nat.card ↥(N.subgroupOf B) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv]
    exact hNc
  let φ : ↥B →* Multiplicative (Fin 4 → ZMod 2) :=
    { toFun := fun b => Multiplicative.ofAdd (κB (b : G))
      map_one' := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, toAdd_one]
        exact hBone
      map_mul' := by
        intro b b'
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
        exact hBadd (b : G) b.2 (b' : G) b'.2 }
  have hkerφ : φ.ker = N.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (κB (b : G)) = 1 ↔ (b : G) ∈ N
    rw [ofAdd_eq_one]
    exact hBker (b : G) b.2
  have hrange : Nat.card ↥φ.range = 16 := by
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hkerφ, hNsubcardB, hB] at h
    omega
  have htop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange, Nat.card_congr (Multiplicative.toAdd), Nat.card_fun]
    simp [Nat.card_zmod]
  have hsurjφ : Function.Surjective φ := MonoidHom.range_eq_top.mp htop
  refine ⟨κB, hBadd, hBker, ?_, hpair⟩
  intro y
  obtain ⟨b, hb⟩ := hsurjφ (Multiplicative.ofAdd y)
  refine ⟨(b : G), b.2, ?_⟩
  have h := congrArg Multiplicative.toAdd hb
  simpa [φ] using h

theorem s16c1_G47_coord {K U B N : Subgroup G} (hUK : U ≤ K) (hBK : B ≤ K)
    (hKUB : ∀ k ∈ K, ∃ u ∈ U, ∃ b ∈ B, k = u * b)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hUsq : ∀ x ∈ U, x * x = 1)
    (hBsq : ∀ x ∈ B, x * x = 1) (hN : N = U ⊓ B) (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hNcent : ∀ n ∈ N, ∀ k ∈ K, k * n = n * k)
    (hBZ : ∀ b ∈ B, (∀ u ∈ U, u * b = b * u) → b ∈ U)
    (hU : Nat.card ↥U = 32) (hB : Nat.card ↥B = 32) (hNc : Nat.card ↥N = 2) :
    ∃ κ : G → (Fin 4 ⊕ Fin 4 → ZMod 2), G47Coord K U B N κ := by
  classical
  have hNU : N ≤ U := by rw [hN]; exact inf_le_left
  have hNB : N ≤ B := by rw [hN]; exact inf_le_right
  have hNK : N ≤ K := hNU.trans hUK
  obtain ⟨κU, hUadd, hUker, hUsurj⟩ := s16c1_G47_coord_elem hNU hUab hUsq hU hNc
  obtain ⟨κB, hBadd, hBker, hBsurj, hpair⟩ :=
    s16c1_G47_coord_dual hUK hBK hN hKcomm hNcent hBZ hB hNc hUadd hUker hUsurj
  have hUone : κU 1 = 0 := (hUker 1 (hNU N.one_mem)).mpr N.one_mem
  have hBone : κB 1 = 0 := (hBker 1 (hNB N.one_mem)).mpr N.one_mem
  have hwd : ∀ u ∈ U, ∀ u' ∈ U, ∀ b ∈ B, ∀ b' ∈ B, u * b = u' * b' →
      κU u = κU u' ∧ κB b = κB b' := by
    intro u hu u' hu' b hb b' hb' heq
    have hmemU : u'⁻¹ * u ∈ U := U.mul_mem (U.inv_mem hu') hu
    have hmemB : b' * b⁻¹ ∈ B := B.mul_mem hb' (B.inv_mem hb)
    have hEq : u'⁻¹ * u = b' * b⁻¹ := by
      calc u'⁻¹ * u = u'⁻¹ * (u * b) * b⁻¹ := by group
        _ = u'⁻¹ * (u' * b') * b⁻¹ := by rw [heq]
        _ = b' * b⁻¹ := by group
    have hinN : u'⁻¹ * u ∈ N := by
      rw [hN]
      exact ⟨hmemU, hEq ▸ hmemB⟩
    have hUzero : κU (u'⁻¹ * u) = 0 := (hUker _ hmemU).mpr hinN
    have hBzero : κB (b' * b⁻¹) = 0 := (hBker _ hmemB).mpr (hEq ▸ hinN)
    constructor
    · calc κU u = κU (u' * (u'⁻¹ * u)) := by congr 1; group
        _ = κU u' + κU (u'⁻¹ * u) := hUadd u' hu' _ hmemU
        _ = κU u' := by rw [hUzero, add_zero]
    · symm
      have hb'b : (b' * b⁻¹) * b = b' := by group
      calc κB b' = κB ((b' * b⁻¹) * b) := by rw [hb'b]
        _ = κB (b' * b⁻¹) + κB b := hBadd _ hmemB b hb
        _ = κB b := by rw [hBzero, zero_add]
  let κ : G → (Fin 4 ⊕ Fin 4 → ZMod 2) := fun k =>
    if h : ∃ u ∈ U, ∃ b ∈ B, k = u * b then
      Sum.elim (κU h.choose) (κB h.choose_spec.2.choose)
    else 0
  have hκ : ∀ u ∈ U, ∀ b ∈ B, κ (u * b) = Sum.elim (κU u) (κB b) := by
    intro u hu b hb
    have hex : ∃ u' ∈ U, ∃ b' ∈ B, u * b = u' * b' := ⟨u, hu, b, hb, rfl⟩
    have hspec := hex.choose_spec
    have hspec2 := hspec.2.choose_spec
    have hwd' := hwd u hu hex.choose hspec.1 b hb hex.choose_spec.2.choose hspec2.1
      hspec2.2
    simp only [κ, dif_pos hex]
    rw [← hwd'.1, ← hwd'.2]
  refine ⟨κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k1 hk1 k2 hk2
    obtain ⟨u1, hu1, b1, hb1, rfl⟩ := hKUB k1 hk1
    obtain ⟨u2, hu2, b2, hb2, rfl⟩ := hKUB k2 hk2
    have hcN : ⁅b1, u2⁆ ∈ N := hKcomm b1 (hBK hb1) u2 (hUK hu2)
    have hcU : ⁅b1, u2⁆ ∈ U := hNU hcN
    have hbu : b1 * u2 = ⁅b1, u2⁆ * u2 * b1 := by
      rw [commutatorElement_def]
      group
    have hprod : (u1 * b1) * (u2 * b2) =
        (u1 * ⁅b1, u2⁆ * u2) * (b1 * b2) := by
      rw [show (u1 * b1) * (u2 * b2) = u1 * (b1 * u2) * b2 from by group, hbu]
      group
    have hU12 : u1 * ⁅b1, u2⁆ * u2 ∈ U :=
      U.mul_mem (U.mul_mem hu1 hcU) hu2
    have hB12 : b1 * b2 ∈ B := B.mul_mem hb1 hb2
    have hUc : κU (u1 * ⁅b1, u2⁆ * u2) = κU u1 + κU u2 := by
      rw [hUadd (u1 * ⁅b1, u2⁆) (U.mul_mem hu1 hcU) u2 hu2,
        hUadd u1 hu1 ⁅b1, u2⁆ hcU, (hUker _ hcU).mpr hcN, add_zero]
    calc κ ((u1 * b1) * (u2 * b2))
        = Sum.elim (κU (u1 * ⁅b1, u2⁆ * u2)) (κB (b1 * b2)) := by
            rw [hprod]
            exact hκ _ hU12 _ hB12
      _ = Sum.elim (κU u1) (κB b1) + Sum.elim (κU u2) (κB b2) := by
            rw [hUc, hBadd b1 hb1 b2 hb2]
            funext i
            rcases i with i | i <;> simp [Sum.elim, add_assoc]
      _ = κ (u1 * b1) + κ (u2 * b2) := by
            rw [hκ u1 hu1 b1 hb1, hκ u2 hu2 b2 hb2]
  · intro k hk
    obtain ⟨u, hu, b, hb, rfl⟩ := hKUB k hk
    rw [hκ u hu b hb]
    constructor
    · intro hzero
      have hUzero : κU u = 0 := by
        funext i
        have := congrFun hzero (Sum.inl i)
        simpa [Sum.elim] using this
      have hBzero : κB b = 0 := by
        funext i
        have := congrFun hzero (Sum.inr i)
        simpa [Sum.elim] using this
      exact N.mul_mem ((hUker u hu).mp hUzero) ((hBker b hb).mp hBzero)
    · intro hkN
      have hkU : u * b ∈ U := hNU hkN
      have hwd' := hwd u hu (u * b) hkU b hb 1 B.one_mem (by rw [mul_one])
      have hUk : κU (u * b) = 0 := (hUker (u * b) hkU).mpr hkN
      funext i
      rcases i with i | i
      · have hUi : κU u i = 0 := by
          rw [hwd'.1]
          exact congrFun hUk i
        simpa [Sum.elim] using hUi
      · have hBi : κB b i = 0 := by
          rw [hwd'.2, hBone]
          rfl
        simpa [Sum.elim] using hBi
  · intro x
    obtain ⟨u, hu, hux⟩ := hUsurj x
    refine ⟨u, hu, ?_⟩
    rw [show u = u * 1 from (mul_one u).symm, hκ u hu 1 B.one_mem, hux, hBone]
  · intro y
    obtain ⟨b, hb, hby⟩ := hBsurj y
    refine ⟨b, hb, ?_⟩
    rw [show b = 1 * b from (one_mul b).symm, hκ 1 U.one_mem b hb, hUone, hby]
  · intro u hu i
    rw [show u = u * 1 from (mul_one u).symm, hκ u hu 1 B.one_mem]
    simp [Sum.elim, hBone]
  · intro b hb i
    rw [show b = 1 * b from (one_mul b).symm, hκ 1 U.one_mem b hb]
    simp [Sum.elim, hUone]
  · intro k hk
    obtain ⟨u, hu, b, hb, rfl⟩ := hKUB k hk
    have hcN : ⁅b, u⁆ ∈ N := hKcomm b (hBK hb) u (hUK hu)
    have hsq : (u * b) * (u * b) = ⁅b, u⁆ := by
      have hbu : b * u = ⁅b, u⁆ * u * b := by
        rw [commutatorElement_def]
        group
      have huc : u * ⁅b, u⁆ = ⁅b, u⁆ * u := hNcent _ hcN u (hUK hu)
      calc (u * b) * (u * b) = u * (b * u) * b := by group
        _ = u * (⁅b, u⁆ * u * b) * b := by rw [hbu]
        _ = (u * ⁅b, u⁆) * u * (b * b) := by group
        _ = (⁅b, u⁆ * u) * u * 1 := by rw [huc, hBsq b hb]
        _ = ⁅b, u⁆ * (u * u) := by group
        _ = ⁅b, u⁆ := by rw [hUsq u hu, mul_one]
    rw [hsq, hκ u hu b hb]
    have hdot : dotProduct (fun i => Sum.elim (κU u) (κB b) (Sum.inl i))
        (fun i => Sum.elim (κU u) (κB b) (Sum.inr i)) =
        dotProduct (κU u) (κB b) := by
      simp [Sum.elim]
    rw [hdot, ← commutatorElement_inv u b, inv_eq_one]
    exact hpair u hu b hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
