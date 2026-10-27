module

public import CFSG.Quasithin.Vol2.KGFact3312Base
public import CFSG.GH74.KGroups.L3EpsUniInv
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.KGroups.L3EpsSylow

public section

namespace CFSG.Quasithin.H13.KG3312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.GH74.KGroups.L3Eps (InvData tInv tInv_mul_self tInv_ne_one invData_of_equiv
  exists_projectiveSL_equiv l3eps_center_sylow)
open CFSG.GH74.Generic.S3 (SingleInv singleInv_psl singleInv_psu)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped Pointwise MatrixGroups commutatorElement

structure SL2Like {G : Type*} [Group G] (B : Subgroup G) (n : ℕ) : Prop where
  perfect : ⁅B, B⁆ = B
  card : Nat.card B = n
  inv_exists : ∃ z ∈ B, z * z = 1 ∧ z ≠ 1
  inv_unique : ∀ x ∈ B, ∀ y ∈ B, x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → x = y
  center_sq : ∀ x ∈ B, (∀ y ∈ B, x * y = y * x) → x * x = 1

theorem SL2Like.of_isSL2 {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {B : Subgroup G} (hB : IsSL2 p ↥B) : SL2Like B (p * (p ^ 2 - 1)) := by
  obtain ⟨f⟩ := hB
  have : Fact p.Prime := ⟨hp⟩
  have hcardF : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  have hq : CFSG.IsQuasisimple SL(2, ZMod p) :=
    CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by rw [hcardF]; omega)
  have hneg : ∀ x : ↥B, x * x = 1 → x ≠ 1 → f x = -1 := by
    intro x hx hx1
    rcases CFSG.GH74.KGroups.L3Eps.sl2c_sq_eq_one hchar (A := f x) (by rw [← map_mul, hx, map_one])
      with h | h
    · exact absurd (f.injective (h.trans (map_one f).symm)) hx1
    · exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : Group.IsPerfect SL(2, ZMod p) := hq.1
    have : Group.IsPerfect ↥B :=
      Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
    exact Subgroup.isPerfect_iff.mp this
  · rw [Nat.card_congr f.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      hcardF]
  · refine ⟨(f.symm (-1) : G), (f.symm (-1)).2, ?_, ?_⟩
    · have h : f.symm (-1) * f.symm (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
      exact congrArg Subtype.val h
    · intro h
      have h' : f.symm (-1) = 1 := Subtype.ext h
      apply CFSG.GH74.KGroups.L3Eps.neg_one_ne_one h2
      have := congrArg f h'
      rwa [MulEquiv.apply_symm_apply, map_one] at this
  · intro x hx y hy hx2 hx1 hy2 hy1
    have hX := hneg ⟨x, hx⟩ (Subtype.ext hx2) (fun h => hx1 (congrArg Subtype.val h))
    have hY := hneg ⟨y, hy⟩ (Subtype.ext hy2) (fun h => hy1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (f.injective (hX.trans hY.symm))
  · intro x hx hxc
    have hcen : f ⟨x, hx⟩ ∈ Subgroup.center SL(2, ZMod p) := by
      rw [Subgroup.mem_center_iff]
      intro A
      obtain ⟨y, rfl⟩ := f.surjective A
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (hxc y y.2).symm)
    have hsq : f ⟨x, hx⟩ * f ⟨x, hx⟩ = 1 := by
      rcases CFSG.GH74.KGroups.L3Eps.sl2c_center_eq hcen with h | h
      · rw [h, mul_one]
      · rw [h, neg_one_mul, neg_neg]
    have h1 : (⟨x, hx⟩ : ↥B) * ⟨x, hx⟩ = 1 := f.injective (by rw [map_mul, hsq, map_one])
    exact congrArg Subtype.val h1

section Uniq

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem SL2Like.conj_eq {B : Subgroup K} {n : ℕ} (hB : SL2Like B n) {z : K} (hz : z ∈ B)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {g : K} (hg : g ∈ Subgroup.normalizer (B : Set K)) :
    g * z * g⁻¹ = z := by
  refine hB.inv_unique _ ((Subgroup.mem_normalizer_iff.mp hg z).mp hz) z hz ?_ ?_ hz2 hz1
  · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
  · intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]

omit [Finite K] in
theorem mem_of_commute_sylow {U : Subgroup K} (hU : IsSylowTwoOf U ⊤) {z : K} (hz2 : z * z = 1)
    (hzU : ∀ u ∈ U, u * z = z * u) : z ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hU
  have hH : IsPGroup 2 (Subgroup.zpowers z) := by
    have hd : Nat.card (Subgroup.zpowers z) ∣ 2 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (x := z) (n := 2) (by rw [sq]; exact hz2)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card hk
  have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (U : Set K) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun u => ?_
    constructor
    · intro hu
      have h1 : z * u * z⁻¹ = u := by rw [← hzU u hu, mul_inv_cancel_right]
      rw [h1]
      exact hu
    · intro hu
      have h1 : z * u * z⁻¹ ∈ U := hu
      have h2 : u = z⁻¹ * (z * u * z⁻¹) * z := by group
      rw [h2]
      have h3 := hzU _ h1
      have h4 : z⁻¹ * (z * u * z⁻¹) * z = z * u * z⁻¹ := by
        calc z⁻¹ * (z * u * z⁻¹) * z = z⁻¹ * ((z * u * z⁻¹) * z) := by group
          _ = z⁻¹ * (z * (z * u * z⁻¹)) := by rw [h3]
          _ = z * u * z⁻¹ := by group
      rw [h4]
      exact h1
  have heq := (hp.toSylow hi).is_maximal' (IsPGroup.to_sup_of_normal_left' hp hH hle) le_sup_left
  have hz : z ∈ U ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  rw [heq] at hz
  exact hz

theorem eq_of_sl2Like {n : ℕ}
    (hinv : ∀ x : K, x * x = 1 → x ≠ 1 → ∃ S : Subgroup K, Nat.card S = n ∧
      ∀ a ∈ Subgroup.centralizer ({x} : Set K), ∀ b ∈ Subgroup.centralizer ({x} : Set K),
        ⁅a, b⁆ ∈ S)
    {U : Subgroup K} (hU : IsSylowTwoOf U ⊤)
    (hZU : ∀ a ∈ U ⊓ Subgroup.centralizer (U : Set K), ∀ b ∈ U ⊓ Subgroup.centralizer (U : Set K),
      a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → a = b)
    {B₁ B₂ : Subgroup K} (h₁ : SL2Like B₁ n) (h₂ : SL2Like B₂ n)
    (hN₁ : U ≤ Subgroup.normalizer (B₁ : Set K)) (hN₂ : U ≤ Subgroup.normalizer (B₂ : Set K)) :
    B₁ = B₂ := by
  have key : ∀ B : Subgroup K, SL2Like B n → U ≤ Subgroup.normalizer (B : Set K) →
      ∃ z ∈ U ⊓ Subgroup.centralizer (U : Set K), z * z = 1 ∧ z ≠ 1 ∧
        B ≤ Subgroup.centralizer ({z} : Set K) := by
    intro B hB hN
    obtain ⟨z, hzB, hz2, hz1⟩ := hB.inv_exists
    have hcomm : ∀ u ∈ U, u * z = z * u := by
      intro u hu
      have h := hB.conj_eq hzB hz2 hz1 (hN hu)
      calc u * z = u * z * u⁻¹ * u := by group
        _ = z * u := by rw [h]
    refine ⟨z, Subgroup.mem_inf.mpr ⟨mem_of_commute_sylow hU hz2 hcomm, ?_⟩, hz2, hz1, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hcomm u hu
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hB.conj_eq hzB hz2 hz1 (Subgroup.le_normalizer hb)
      calc b * z = b * z * b⁻¹ * b := by group
        _ = z * b := by rw [h]
  obtain ⟨z₁, hz₁U, hz₁2, hz₁1, hB₁⟩ := key B₁ h₁ hN₁
  obtain ⟨z₂, hz₂U, hz₂2, hz₂1, hB₂⟩ := key B₂ h₂ hN₂
  have hz : z₁ = z₂ := hZU z₁ hz₁U z₂ hz₂U hz₁2 hz₁1 hz₂2 hz₂1
  subst hz
  obtain ⟨S, hS, hSc⟩ := hinv z₁ hz₁2 hz₁1
  have hle : ∀ B : Subgroup K, SL2Like B n → B ≤ Subgroup.centralizer ({z₁} : Set K) → B = S := by
    intro B hB hBC
    have h1 : B ≤ S := by
      rw [← hB.perfect, Subgroup.commutator_le]
      intro a ha b hb
      exact hSc a (hBC ha) b (hBC hb)
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hS, hB.card])
  rw [hle B₁ h₁ hB₁, hle B₂ h₂ hB₂]

theorem eq_of_isCyclic_involution {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype G := Fintype.ofFinite G
  have hoa : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hob : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hd : 2 ∣ Fintype.card G := by
    rw [← hoa]
    exact orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h
  exact Finset.card_le_one.mp h.le a (by simp [hoa]) b (by simp [hob])

end Uniq

theorem two_ne_zero_of_odd_card' {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h2 => by
    have h' := (FiniteField.even_card_iff_char_two (F := F)).1 h2
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨k, hk⟩ := h
    omega
  exact Ring.two_ne_zero hF2

theorem invData_psl {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hX : StatedClassicalModel K .PSL 3 p 1) :
    ∀ x : K, x * x = 1 → x ≠ 1 → ∃ S : Subgroup K, InvData (p ^ 1) K x S := by
  have hX' := hX
  obtain ⟨-, F₀, _, _, hF₀, ⟨e₀⟩⟩ := hX'
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card' (by rw [hF, pow_one]; exact hpodd)
  have h20 : (2 : F₀) ≠ 0 := two_ne_zero_of_odd_card' (by rw [hF₀, pow_one]; exact hpodd)
  have hSK : SingleInv K :=
    SingleInv.of_mulEquiv e₀.symm (singleInv_psl h20)
  have hS : SingleInv (projectiveSL 3 F) :=
    SingleInv.of_mulEquiv e hSK
  intro x hx2 hx1
  have hex2 : e x * e x = 1 := by rw [← map_mul, hx2, map_one]
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := hS (e x) tInv hex2 hex1 tInv_mul_self (tInv_ne_one h2)
  let e' : K ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
  have he' : e' x = tInv := by
    show MulAut.conj g (e x) = _
    rw [MulAut.conj_apply]
    exact hg
  exact ⟨_, invData_of_equiv hp hF (by decide) h2 (by rw [hF, pow_one]; omega) e' he'⟩

theorem invData_psu {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hX : StatedClassicalModel K .PSU 3 p 1) :
    ∀ x : K, x * x = 1 → x ≠ 1 → ∃ S : Subgroup K, InvData (p ^ 1) K x S := by
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := hX
  have hp2 : p ≠ 2 := by omega
  have hU : UnitaryFieldData p 1 F :=
    ⟨hp, le_rfl, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq : Odd (p ^ 1) := (hp.odd_of_ne_two hp2).pow
  have hS : SingleInv K :=
    SingleInv.of_mulEquiv e₀.symm (singleInv_psu hU hp2)
  intro x hx2 hx1
  obtain ⟨θ₀, hθ₀⟩ := CFSG.GH74.KGroups.L3Eps.Uni.exists_cover_of_equiv hU e₀
  obtain ⟨g, hg⟩ := hS (θ₀ (CFSG.GH74.KGroups.L3Eps.Uni.dU hq)) x
    (CFSG.GH74.KGroups.L3Eps.Uni.theta_dU_sq hq θ₀)
    (CFSG.GH74.KGroups.L3Eps.Uni.theta_dU_ne_one hU hq hθ₀) hx2 hx1
  have hθ : CFSG.GH74.KGroups.L3Eps.Uni.IsCover hU ((MulAut.conj g).toMonoidHom.comp θ₀) :=
    hθ₀.comp_equiv (MulAut.conj g)
  have hinv := CFSG.GH74.KGroups.L3Eps.Uni.invData_of_cover hU hp2 (by rw [pow_one]; exact hp5)
    hq hθ
  have hθt : ((MulAut.conj g).toMonoidHom.comp θ₀) (CFSG.GH74.KGroups.L3Eps.Uni.dU hq) = x := by
    simpa [MulAut.conj_apply] using hg
  rw [hθt] at hinv
  exact ⟨_, hinv⟩

theorem eq_of_model {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K] (hX : StatedClassicalModel K t 3 p 1)
    {U : Subgroup K} (hU : IsSylowTwoOf U ⊤) {B₁ B₂ : Subgroup K}
    (h₁ : SL2Like B₁ (p * (p ^ 2 - 1))) (h₂ : SL2Like B₂ (p * (p ^ 2 - 1)))
    (hN₁ : U ≤ Subgroup.normalizer (B₁ : Set K)) (hN₂ : U ≤ Subgroup.normalizer (B₂ : Set K)) :
    B₁ = B₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ x : K, x * x = 1 → x ≠ 1 →
      ∃ S : Subgroup K, InvData (p ^ 1) K x S := by
    rcases ht with rfl | rfl
    · exact invData_psl hp hp5 hX
    · exact invData_psu hp hp5 hX
  refine eq_of_sl2Like (fun x hx2 hx1 => ?_) hU ?_ h₁ h₂ hN₁ hN₂
  · obtain ⟨S, hS⟩ := hinv x hx2 hx1
    exact ⟨S, by rw [hS.card, pow_one], fun a ha b hb => hS.commutator_mem a ha b hb⟩
  · obtain ⟨hp2, hi⟩ := K1.isSylowTwoOf_top_iff.mp hU
    have hmax : ∀ T : Subgroup K, IsPGroup 2 T → U ≤ T → T ≤ U := fun T hT hUT =>
      ((hp2.toSylow hi).is_maximal' hT hUT).le
    have hcyc := (l3eps_center_sylow ht (by omega) hX hp2 hmax).1
    intro a ha b hb ha2 ha1 hb2 hb1
    have h := eq_of_isCyclic_involution (G := ↥(U ⊓ Subgroup.centralizer (U : Set K)))
      (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (Subtype.ext ha2) (fun h => ha1 (congrArg Subtype.val h))
      (Subtype.ext hb2) (fun h => hb1 (congrArg Subtype.val h))
    exact congrArg Subtype.val h

theorem map_center_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro h z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, h w]
  · intro h w
    apply e.injective
    rw [map_mul, map_mul, h (e w)]

theorem eq_of_cover {Q K : Type} [Group Q] [Finite Q] [Group K] [Finite K] (π : Q →* K)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center Q)
    (h3 : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1) {n : ℕ}
    (huniq : ∀ U' : Subgroup K, IsSylowTwoOf U' ⊤ → ∀ B₁ B₂ : Subgroup K, SL2Like B₁ n →
      SL2Like B₂ n → U' ≤ Subgroup.normalizer (B₁ : Set K) →
        U' ≤ Subgroup.normalizer (B₂ : Set K) → B₁ = B₂)
    {U : Subgroup Q} (hU : IsSylowTwoOf U ⊤) {B₁ B₂ : Subgroup Q} (h₁ : SL2Like B₁ n)
    (h₂ : SL2Like B₂ n) (hN₁ : U ≤ Subgroup.normalizer (B₁ : Set Q))
    (hN₂ : U ≤ Subgroup.normalizer (B₂ : Set Q)) : B₁ = B₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : ∀ B : Subgroup Q, SL2Like B n → ∀ x ∈ B, π x = 1 → x = 1 := by
    intro B hB x hx hπx
    have hxZ : x ∈ Subgroup.center Q := hker ▸ (MonoidHom.mem_ker.mpr hπx)
    have hsq := hB.center_sq x hx fun y _ => (Subgroup.mem_center_iff.mp hxZ y).symm
    have hcube := h3 x hxZ
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [hcube, hsq, inv_one, one_mul]
  have hmap : ∀ B : Subgroup Q, SL2Like B n → SL2Like (B.map π) n := by
    intro B hB
    have hinj : Function.Injective (π.comp B.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      exact Subtype.ext (hinf B hB x x.2 hx)
    have hrange : (π.comp B.subtype).range = B.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_commutator, hB.perfect]
    · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hB.card]
    · obtain ⟨z, hzB, hz2, hz1⟩ := hB.inv_exists
      refine ⟨π z, ⟨z, hzB, rfl⟩, by rw [← map_mul, hz2, map_one], fun h => hz1 ?_⟩
      exact hinf B hB z hzB h
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hx2 hx1 hy2 hy1
      have hx2' : x * x = 1 := hinf B hB _ (B.mul_mem hx hx) (by rw [map_mul, hx2])
      have hy2' : y * y = 1 := hinf B hB _ (B.mul_mem hy hy) (by rw [map_mul, hy2])
      have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
      have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
      rw [hB.inv_unique x hx y hy hx2' hx1' hy2' hy1']
    · rintro _ ⟨x, hx, rfl⟩ hxc
      have hc : ∀ y ∈ B, x * y = y * x := by
        intro y hy
        have h1 := hxc (π y) ⟨y, hy, rfl⟩
        have h2 : x * y * (y * x)⁻¹ = 1 := hinf B hB _
          (B.mul_mem (B.mul_mem hx hy) (B.inv_mem (B.mul_mem hy hx)))
          (by rw [map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel])
        exact mul_inv_eq_one.mp h2
      rw [← map_mul, hB.center_sq x hx hc, map_one]
  have hU' : IsSylowTwoOf (U.map π) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hU
    exact K1.isSylowTwoOf_top_iff.mpr
      ⟨hp.map π, fun h => hi (h.trans (Subgroup.index_map_dvd U hπ))⟩
  have hN : ∀ B : Subgroup Q, U ≤ Subgroup.normalizer (B : Set Q) →
      U.map π ≤ Subgroup.normalizer ((B.map π : Subgroup K) : Set K) :=
    fun B hNB => (Subgroup.map_mono hNB).trans (Subgroup.le_normalizer_map π)
  have heq := huniq _ hU' _ _ (hmap B₁ h₁) (hmap B₂ h₂) (hN B₁ hN₁) (hN B₂ hN₂)
  have hsup : B₁ ⊔ π.ker = B₂ ⊔ π.ker := by
    rw [← Subgroup.comap_map_eq, ← Subgroup.comap_map_eq, heq]
  have hcore : ∀ B : Subgroup Q, SL2Like B n → perfectCore (B ⊔ π.ker) = B := by
    intro B hB
    have hZs : Group.IsSolvable ↥π.ker := by
      rw [hker]
      exact Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
    have hle : B ⊔ π.ker ≤ Subgroup.normalizer (B : Set Q) := by
      refine sup_le Subgroup.le_normalizer fun z hz => ?_
      rw [hker] at hz
      refine Subgroup.mem_normalizer_iff.mpr fun b => ?_
      rw [(Subgroup.mem_center_iff.mp hz b).symm, mul_inv_cancel_right]
    exact le_antisymm
      (perfectCore_le_of_sup_solvable le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hle) rfl hZs)
      (le_perfectCore_of_perfect le_sup_left hB.perfect)
  rw [← hcore B₁ h₁, hsup, hcore B₂ h₂]

theorem sl3_cover {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] (hQ : IsSL3 p Q) :
    StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 3 p 1 ∧
      ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hQ
  let e₁ : Q ≃* SL(3, K) := φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
  have hmap := map_center_equiv e₁
  let e₂ : Q ⧸ Subgroup.center Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    QuotientGroup.congr _ _ e₁ hmap
  refine ⟨⟨⟨hp, le_rfl, by simp⟩, K, inferInstance, inferInstance, by rw [pow_one]; exact hK,
    ⟨e₂.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K)⟩⟩, fun z hz => ?_⟩
  have h1 : e₁ z ∈ Subgroup.center SL(3, K) := hmap ▸ ⟨z, hz, rfl⟩
  have h2 := CFSG.GH74.GLS.LU.center_pow_three (e₁ z) h1
  apply e₁.injective
  rw [map_pow, h2, map_one]

theorem su3_cover {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {Q : Type} [Group Q] (hQ : IsSU3 p Q) :
    StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 3 p 1 ∧
      ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 := by
  obtain ⟨K, _, _, hK, ⟨φ₀⟩⟩ := hQ
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hnq : ((3 : ℕ), p ^ 1) ≠ (3, 2) := by
    simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
    omega
  have hSU : StatedSU 3 p K = StatedSU 3 (p ^ 1) K := by rw [pow_one]
  let φ : Q ≃* ↥(StatedSU 3 (p ^ 1) K) := φ₀.trans (MulEquiv.subgroupCongr hSU)
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (n := 3) hK'
    le_rfl hnq).2
  have hscal := (CFSG.LinearGroups.unitary_scalar_kernel hp hK' (n := 3) (by norm_num)).2.2
  have hmap : (Subgroup.center Q).map φ.toMonoidHom =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K) := by
    rw [map_center_equiv φ, hZ]
  let e₂ : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSU 3 (p ^ 1) K) :=
    QuotientGroup.congr _ _ φ hmap
  refine ⟨⟨⟨hp, le_rfl, le_rfl, hnq⟩, K, inferInstance, inferInstance, hK', ⟨e₂⟩⟩,
    fun z hz => ?_⟩
  have h1 : φ z ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K) :=
    hmap ▸ ⟨z, hz, rfl⟩
  have h2 : orderOf
      (⟨φ z, h1⟩ : ↥((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K))) ∣ 3 :=
    (orderOf_dvd_natCard _).trans (hscal ▸ Nat.gcd_dvd_left 3 (p ^ 1 + 1))
  have h4 : (φ z) ^ 3 = 1 := congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h2)
  apply φ.injective
  rw [map_pow, h4, map_one]

theorem eq_of_l3eps {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {s : Bool} {Q : Type} [Group Q]
    [Finite Q] (hQ : IsPSLEps3 s p 1 Q ∨ IsSLEps3 s p Q) {U : Subgroup Q} (hU : IsSylowTwoOf U ⊤)
    {B₁ B₂ : Subgroup Q} (h₁ : SL2Like B₁ (p * (p ^ 2 - 1))) (h₂ : SL2Like B₂ (p * (p ^ 2 - 1)))
    (hN₁ : U ≤ Subgroup.normalizer (B₁ : Set Q)) (hN₂ : U ≤ Subgroup.normalizer (B₂ : Set Q)) :
    B₁ = B₂ := by
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p
      exact absurd hp (by norm_num)
    · exact h
  rcases hQ with hQ | hQ
  · cases s
    · exact eq_of_model (Or.inr rfl) hp hp5 hQ hU h₁ h₂ hN₁ hN₂
    · exact eq_of_model (Or.inl rfl) hp hp5 hQ hU h₁ h₂ hN₁ hN₂
  · cases s
    · obtain ⟨hX, h3⟩ := su3_cover hp hp3 hQ
      exact eq_of_cover (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _) h3
        (fun U' hU' C₁ C₂ g₁ g₂ hM₁ hM₂ => eq_of_model (Or.inr rfl) hp hp5 hX hU' g₁ g₂ hM₁ hM₂)
        hU h₁ h₂ hN₁ hN₂
    · obtain ⟨hX, h3⟩ := sl3_cover hp hQ
      exact eq_of_cover (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _) h3
        (fun U' hU' C₁ C₂ g₁ g₂ hM₁ hM₂ => eq_of_model (Or.inl rfl) hp hp5 hX hU' g₁ g₂ hM₁ hM₂)
        hU h₁ h₂ hN₁ hN₂

theorem factL3EpsNorm3312_holds : FactL3EpsNorm3312 := by
  intro p hp hp3 s Q _ _ hQ A S B hA hS hB hSB d hd _
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p
      exact absurd hp (by norm_num)
    · exact h
  obtain ⟨U, hU, hUT, -⟩ := exists_sylow_comap_conj hA hS
  have hdN := (Subgroup.mem_inf.mp hd).1
  have hB' : IsSL2 p ↥(d • B) := by
    obtain ⟨f⟩ := hB
    exact ⟨(Subgroup.equivSMul d B).symm.trans f⟩
  have h := eq_of_l3eps hp hp3 hQ hU (SL2Like.of_isSL2 hp hp5 hB) (SL2Like.of_isSL2 hp hp5 hB')
    (hUT.trans (comap_conj_le_normalizer hSB))
    (hUT.trans (comap_conj_le_normalizer (le_stabilizer_smul hSB hdN)))
  exact MulAction.mem_stabilizer_iff.mpr h.symm

end CFSG.Quasithin.H13.KG3312
