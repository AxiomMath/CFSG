module

public import CFSG.Quasithin.H13.A6S13813i

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin
open scoped commutatorElement

namespace A6Four

variable {V : Type*} [CommGroup V] [Finite V]

theorem card_fix_mul_self_le {U : Subgroup V} {y b : MulAut V} (hyU : ∀ u ∈ U, y u ∈ U)
    (hby : b * y * b⁻¹ = y⁻¹) (hy5 : y ^ 5 = 1) (hfix : ∀ u ∈ U, y u = u → u = 1) :
    Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) * Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) ≤
      Nat.card U := by
  set K := U ⊓ fixV (Subgroup.zpowers b) with hK
  have hKmem : ∀ v, v ∈ K ↔ v ∈ U ∧ b v = v := fun v => by
    rw [hK, Subgroup.mem_inf, mem_fixV_zpowers_iff]
  set K' := K.map y.toMonoidHom with hK'
  have hcard : Nat.card K' = Nat.card K := Subgroup.card_map_of_injective y.injective
  have hbyu : ∀ v : V, b (y v) = y⁻¹ (b v) := by
    intro v
    have e : b * y = y⁻¹ * b := by
      calc b * y = (b * y * b⁻¹) * b := by group
        _ = y⁻¹ * b := by rw [hby]
    exact congrArg (fun g : MulAut V => g v) e
  have hinf : K ⊓ K' = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hk, ⟨k, hkK, rfl⟩⟩
    obtain ⟨hkU, hbk⟩ := (hKmem k).1 hkK
    have hbyk : b (y k) = y k := ((hKmem _).1 hk).2
    have h1 : y (y k) = k := by
      rw [hbyu, hbk] at hbyk
      calc y (y k) = y (y⁻¹ k) := by rw [hbyk]
        _ = k := by simp
    have hs : y ^ 2 ∈ MulAction.stabilizer (MulAut V) k := by
      show (y ^ 2) k = k
      rw [pow_two, MulAut.mul_apply, h1]
    have h6 := Subgroup.pow_mem _ hs 3
    have e : (y ^ 2) ^ 3 = y := by
      rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hy5, one_mul]
    rw [e] at h6
    have hk1 : k = 1 := hfix k hkU h6
    rw [Subgroup.mem_bot, hk1]
    exact map_one _
  have hle : K ⊔ K' ≤ U := sup_le (fun v hv => ((hKmem v).1 hv).1) (by
    rintro _ ⟨k, hk, rfl⟩
    exact hyU k ((hKmem k).1 hk).1)
  have h1 := card_sup_mul_card_inf K K'
  rw [hinf, Subgroup.card_bot, mul_one, hcard] at h1
  rw [← h1]
  exact Subgroup.card_le_of_le hle

theorem card_le_card_fix_mul {U B : Subgroup V} {b : MulAut V}
    (hbB : ∀ u ∈ U, b u * u⁻¹ ∈ B) :
    Nat.card U ≤ Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) * Nat.card B := by
  set f : ↥U →* V := (commHom b).comp U.subtype with hf
  have e1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at e1
  have hmap : f.ker.map U.subtype = U ⊓ fixV (Subgroup.zpowers b) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, mem_fixV_zpowers_iff.2 ?_⟩
      have : b u * (u : V)⁻¹ = 1 := MonoidHom.mem_ker.1 hu
      exact mul_inv_eq_one.1 this
    · rintro ⟨hv, hb⟩
      refine ⟨⟨v, hv⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      show b v * v⁻¹ = 1
      rw [mem_fixV_zpowers_iff.1 hb, mul_inv_cancel]
  have hker : Nat.card f.ker = Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) := by
    rw [← hmap, Subgroup.card_map_of_injective U.subtype_injective]
  have hrange : f.range ≤ B := by
    rintro _ ⟨u, rfl⟩
    exact hbB u u.2
  calc Nat.card U = Nat.card f.ker * Nat.card f.range := e1.symm
    _ ≤ Nat.card f.ker * Nat.card B := Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrange)
    _ = _ := by rw [hker]

theorem card_fix_le_four {U : Subgroup V} {y b : MulAut V} (hU : Nat.card U = 16)
    (hyU : ∀ u ∈ U, y u ∈ U) (hby : b * y * b⁻¹ = y⁻¹) (hy5 : y ^ 5 = 1)
    (hfix : ∀ u ∈ U, y u = u → u = 1) : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers b)) ≤ 4 := by
  have h1 := card_fix_mul_self_le hyU hby hy5 hfix
  rw [hU] at h1
  nlinarith

theorem false_of_inverts {U B : Subgroup V} {y b : MulAut V} (hU : Nat.card U = 16)
    (hyU : ∀ u ∈ U, y u ∈ U) (hby : b * y * b⁻¹ = y⁻¹) (hy5 : y ^ 5 = 1)
    (hfix : ∀ u ∈ U, y u = u → u = 1) (hB : Nat.card B ≤ 2) (hbB : ∀ u ∈ U, b u * u⁻¹ ∈ B) :
    False := by
  have h1 := card_fix_le_four hU hyU hby hy5 hfix
  have h2 := card_le_card_fix_mul hbB
  rw [hU] at h2
  have h3 := h2.trans (Nat.mul_le_mul h1 hB)
  omega

theorem false_of_two_inverts {U₁ U₂ D A : Subgroup V} {y₁ t y₂ t' : MulAut V}
    (hU₁ : Nat.card U₁ = 16) (hU₂ : Nat.card U₂ = 16) (h12 : U₁ ⊓ U₂ = ⊥)
    (hy₁ : ∀ u ∈ U₁, y₁ u ∈ U₁) (hty₁ : t * y₁ * t⁻¹ = y₁⁻¹) (hy₁5 : y₁ ^ 5 = 1)
    (hfix₁ : ∀ u ∈ U₁, y₁ u = u → u = 1) (htU₁ : ∀ u ∈ U₁, t u ∈ U₁)
    (htU₂ : ∀ u ∈ U₂, t u = u) (hy₂ : ∀ u ∈ U₂, y₂ u ∈ U₂) (hty₂ : t' * y₂ * t'⁻¹ = y₂⁻¹)
    (hy₂5 : y₂ ^ 5 = 1) (hfix₂ : ∀ u ∈ U₂, y₂ u = u → u = 1) (ht'U₁ : ∀ u ∈ U₁, t' u ∈ U₁)
    (ht'U₂ : ∀ u ∈ U₂, t' u ∈ U₂) (hA : Nat.card A ≤ 2) (hD : Nat.card V ≤ 4 * Nat.card D)
    (hDt : ∀ d ∈ D, t d * d⁻¹ ∈ A) (hDt' : ∀ d ∈ D, t' d * d⁻¹ ∈ A) : False := by
  have hsup : Nat.card ↥(U₁ ⊔ U₂) = 256 := by
    have := card_sup_mul_card_inf U₁ U₂
    rw [h12, Subgroup.card_bot, mul_one, hU₁, hU₂] at this
    exact this
  set E := D ⊓ (U₁ ⊔ U₂) with hE
  have hE64 : 64 ≤ Nat.card E := by
    have h1 := card_sup_mul_card_inf D (U₁ ⊔ U₂)
    rw [hsup] at h1
    have h2 : Nat.card ↥(D ⊔ (U₁ ⊔ U₂)) ≤ 4 * Nat.card D :=
      (Subgroup.card_le_card_group _).trans hD
    have hDpos : 0 < Nat.card D := Nat.card_pos
    have h3 : Nat.card D * 256 ≤ Nat.card D * (4 * Nat.card E) := by
      calc Nat.card D * 256 = Nat.card ↥(D ⊔ (U₁ ⊔ U₂)) * Nat.card E := h1.symm
        _ ≤ (4 * Nat.card D) * Nat.card E := Nat.mul_le_mul_right _ h2
        _ = Nat.card D * (4 * Nat.card E) := by ring
    have := Nat.le_of_mul_le_mul_left h3 hDpos
    omega
  set B₁ := U₁ ⊓ A with hB₁
  set B₂ := U₂ ⊓ (U₁ ⊔ A) with hB₂
  have hB : Nat.card B₁ * Nat.card B₂ ≤ 2 := by
    have i1 := card_sup_mul_card_inf U₁ A
    have i2 := card_sup_mul_card_inf U₂ (U₁ ⊔ A)
    have i3 : 256 ≤ Nat.card ↥(U₂ ⊔ (U₁ ⊔ A)) := by
      rw [← hsup]
      exact Subgroup.card_le_of_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    rw [hU₁] at i1
    rw [hU₂] at i2
    have h4 : 256 * (Nat.card B₁ * Nat.card B₂) ≤ 512 := by
      calc 256 * (Nat.card B₁ * Nat.card B₂) ≤
            Nat.card ↥(U₂ ⊔ (U₁ ⊔ A)) * (Nat.card B₁ * Nat.card B₂) :=
            Nat.mul_le_mul_right _ i3
        _ = (Nat.card ↥(U₂ ⊔ (U₁ ⊔ A)) * Nat.card B₂) * Nat.card B₁ := by ring
        _ = 16 * (Nat.card ↥(U₁ ⊔ A) * Nat.card B₁) := by rw [i2]; ring
        _ = 16 * (16 * Nat.card A) := by rw [i1]
        _ ≤ 16 * (16 * 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA)
    omega
  set N₁ := U₁ ⊓ B₁.comap (commHom t) with hN₁
  set N₂ := U₂ ⊓ B₂.comap (commHom t') with hN₂
  have hN₁c : Nat.card N₁ ≤ 4 * Nat.card B₁ := by
    have h1 := card_le_card_fix_mul (U := N₁) (B := B₁) (b := t) (fun u hu => hu.2)
    have h2 : Nat.card ↥(N₁ ⊓ fixV (Subgroup.zpowers t)) ≤ 4 :=
      (Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)).trans
        (card_fix_le_four hU₁ hy₁ hty₁ hy₁5 hfix₁)
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hN₂c : Nat.card N₂ ≤ 4 * Nat.card B₂ := by
    have h1 := card_le_card_fix_mul (U := N₂) (B := B₂) (b := t') (fun u hu => hu.2)
    have h2 : Nat.card ↥(N₂ ⊓ fixV (Subgroup.zpowers t')) ≤ 4 :=
      (Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)).trans
        (card_fix_le_four hU₂ hy₂ hty₂ hy₂5 hfix₂)
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hEN : E ≤ N₁ ⊔ N₂ := by
    rintro e ⟨heD, he12⟩
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Subgroup.mem_sup.1 he12
    have ht : t (e₁ * e₂) * (e₁ * e₂)⁻¹ = t e₁ * e₁⁻¹ := by
      rw [map_mul, htU₂ e₂ he₂, mul_inv, mul_mul_mul_comm, mul_inv_cancel e₂, mul_one]
    have ht' : t' (e₁ * e₂) * (e₁ * e₂)⁻¹ = (t' e₁ * e₁⁻¹) * (t' e₂ * e₂⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    have h1 : t e₁ * e₁⁻¹ ∈ B₁ :=
      ⟨U₁.mul_mem (htU₁ e₁ he₁) (U₁.inv_mem he₁), ht ▸ hDt _ heD⟩
    have h2 : t' e₂ * e₂⁻¹ ∈ B₂ := by
      refine ⟨U₂.mul_mem (ht'U₂ e₂ he₂) (U₂.inv_mem he₂), ?_⟩
      have h3 : t' e₂ * e₂⁻¹ = (t' e₁ * e₁⁻¹)⁻¹ * (t' (e₁ * e₂) * (e₁ * e₂)⁻¹) := by
        rw [ht', ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h3]
      exact (U₁ ⊔ A).mul_mem ((U₁ ⊔ A).inv_mem (Subgroup.mem_sup_left
        (U₁.mul_mem (ht'U₁ e₁ he₁) (U₁.inv_mem he₁)))) (Subgroup.mem_sup_right (hDt' _ heD))
    exact Subgroup.mul_mem_sup ⟨he₁, h1⟩ ⟨he₂, h2⟩
  have h1 : Nat.card E ≤ Nat.card ↥(N₁ ⊔ N₂) := Subgroup.card_le_of_le hEN
  have h2 := card_sup_mul_card_inf N₁ N₂
  have h3 : Nat.card ↥(N₁ ⊔ N₂) ≤ Nat.card N₁ * Nat.card N₂ := by
    rw [← h2]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have h4 : Nat.card E ≤ 32 := by
    calc Nat.card E ≤ Nat.card N₁ * Nat.card N₂ := h1.trans h3
      _ ≤ (4 * Nat.card B₁) * (4 * Nat.card B₂) := Nat.mul_le_mul hN₁c hN₂c
      _ = 16 * (Nat.card B₁ * Nat.card B₂) := by ring
      _ ≤ 16 * 2 := Nat.mul_le_mul_left _ hB
  omega

theorem exists_fpf_gen (hV : ∀ v : V, v ^ 2 = 1) {X Y : Subgroup (MulAut V)}
    (hY : Y ∈ Xk X 2) : ∃ y ∈ Y, y ^ 5 = 1 ∧ ∀ u ∈ commV Y, y u = u → u = 1 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hYc : Nat.card Y = 5 := hY.2.1
  obtain ⟨y, hyY, -, hyz, hyo⟩ := exists_generator_of_prime_card hYc
  refine ⟨y, hyY, by rw [← hyo]; exact pow_orderOf_eq_one y, fun u hu hyu => ?_⟩
  have hfix : u ∈ fixV Y := by
    rw [← hyz]
    exact mem_fixV_zpowers_iff.2 hyu
  have : u ∈ commV Y ⊓ fixV Y := ⟨hu, hfix⟩
  rw [(Xk_decomp hV hY).2] at this
  exact (Subgroup.mem_bot).1 this

theorem p5_structure (hV : ∀ v : V, v ^ 2 = 1) {X P : Subgroup (MulAut V)} (hPX : P ≤ X)
    (hPn : ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ ∈ P) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hcard : Nat.card P = 25) (hexp : ∀ x ∈ P, x ^ 5 = 1) {t : MulAut V} (htX : t ∈ X)
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htrk : rk (commV (Subgroup.zpowers t)) = 2)
    (hP1 : Nat.card (⁅P, Subgroup.zpowers t⁆ : Subgroup (MulAut V)) = 5)
    (hP1rk : rk (commV ⁅P, Subgroup.zpowers t⁆) = 4) {x : MulAut V} (hxX : x ∈ X)
    (hx : conjBy x ⁅P, Subgroup.zpowers t⁆ ≠ ⁅P, Subgroup.zpowers t⁆) :
    ⁅P, Subgroup.zpowers t⁆ ∈ Xk X 2 ∧ conjBy x ⁅P, Subgroup.zpowers t⁆ ∈ Xk X 2 ∧
      ⁅P, Subgroup.zpowers t⁆ ≤ P ∧ conjBy x ⁅P, Subgroup.zpowers t⁆ ≤ P ∧
      (∀ y ∈ ⁅P, Subgroup.zpowers t⁆, t * y * t⁻¹ = y⁻¹) ∧
      (∀ z ∈ conjBy x ⁅P, Subgroup.zpowers t⁆, t * z * t⁻¹ = z) ∧
      (∀ w ∈ commV (conjBy x ⁅P, Subgroup.zpowers t⁆), t w = w) ∧
      (∀ c ∈ P, t * c * t⁻¹ = c → c ∈ conjBy x ⁅P, Subgroup.zpowers t⁆) ∧
      (∀ c ∈ P, t * c * t⁻¹ = c⁻¹ → c ∈ ⁅P, Subgroup.zpowers t⁆) ∧
      commV ⁅P, Subgroup.zpowers t⁆ ⊓ commV (conjBy x ⁅P, Subgroup.zpowers t⁆) = ⊥ := by
  set P₁ := ⁅P, Subgroup.zpowers t⁆ with hP₁
  set Z := conjBy x P₁ with hZ
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left htt).symm
  have hzt : ∀ s ∈ Subgroup.zpowers t, s = 1 ∨ s = t := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
    · left
      rw [hn, zpow_mul, zpow_two, htt, one_zpow]
    · right
      rw [hn, zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul]
  have htP : ∀ y ∈ P, t * y * t⁻¹ ∈ P := hPn t htX
  have hcommt : ∀ y ∈ P, t * ⁅y, t⁆ * t⁻¹ = ⁅y, t⁆⁻¹ := by
    intro y _
    rw [commutatorElement_def, htinv]
    calc t * (y * t * y⁻¹ * t) * t = t * y * t * y⁻¹ * (t * t) := by group
      _ = t * y * t * y⁻¹ := by rw [htt, mul_one]
      _ = t⁻¹ * y * t⁻¹ * y⁻¹ := by rw [htinv]
      _ = (y * t * y⁻¹ * t)⁻¹ := by group
  have hcommP : ∀ y ∈ P, ⁅y, t⁆ ∈ P := by
    intro y hy
    rw [commutatorElement_def]
    have e : y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) := by group
    rw [e]
    exact P.mul_mem hy (htP _ (P.inv_mem hy))
  have hP₁le : P₁ ≤ invSub P hcomm t := by
    rw [hP₁, Subgroup.commutator_le]
    intro y hy s hs
    rcases hzt s hs with h | h
    · rw [h, commutatorElement_one_right]
      exact (invSub P hcomm t).one_mem
    · rw [h]
      exact ⟨hcommP y hy, hcommt y hy⟩
  have hP₁P : P₁ ≤ P := fun y hy => (hP₁le hy).1
  have hP₁inv : ∀ y ∈ P₁, t * y * t⁻¹ = y⁻¹ := fun y hy => (hP₁le hy).2
  have hPp : IsPGroup 5 P := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  have hPfit : P ≤ fittingOf X := le_fittingOf_of_normal hPX hPp hPn
  have hP₁X : P₁ ∈ Xk X 2 := ⟨hP₁P.trans hPfit, hP1, hP1rk⟩
  have hZX : Z ∈ Xk X 2 := conjBy_mem_Xk hxX hP₁X
  have hZP : Z ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hPn x hxX y (hP₁P hy)
  have hZcard : Nat.card Z = 5 := by rw [hZ, card_conjBy]; exact hP1
  have htT : t ∈ TInv X := ⟨htX, ht1, ht2, htrk.le⟩
  obtain ⟨hZc, hZw⟩ : (∀ z ∈ Z, t * z = z * t) ∧ ∀ w ∈ commV Z, t w = w := by
    rcases D2_12_3 hV (Or.inr rfl) htT htrk with ⟨hc, -⟩ | ⟨Y, -, -, huniq, -, hrest⟩
    · exfalso
      obtain ⟨y, hyP₁, hy1, -, -⟩ := exists_generator_of_prime_card hP1
      have hyG : y ∈ Gk X 2 := le_iSup₂ (f := fun Y (_ : Y ∈ Xk X 2) => Y) P₁ hP₁X hyP₁
      have h1 := hP₁inv y hyP₁
      rw [← hc y hyG, mul_inv_cancel_right] at h1
      refine hy1 (eq_one_of_sq_of_pow_odd (p := 5) (by decide) (hexp y (hP₁P hyP₁)) ?_)
      nth_rewrite 2 [h1]
      exact mul_inv_cancel y
    · have hYP₁ : P₁ = Y := huniq P₁ hP₁X hP₁inv
      exact hrest Z hZX (hYP₁ ▸ hx)
  have hZfix : ∀ z ∈ Z, t * z * t⁻¹ = z := fun z hz => by rw [hZc z hz, mul_inv_cancel_right]
  have hcf := card_fix_mul_card_inv hcomm (p := 5) (by decide) hexp htt htP
  rw [hcard] at hcf
  have hZle : Z ≤ P ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := fun z hz =>
    mem_fixSub.2 ⟨hZP hz, hZfix z hz⟩
  have c1 : 5 ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set (MulAut V))) :=
    hZcard ▸ Subgroup.card_le_of_le hZle
  have c2 : 5 ≤ Nat.card ↥(invSub P hcomm t) := hP1 ▸ Subgroup.card_le_of_le hP₁le
  have c3 : Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set (MulAut V))) = 5 := by nlinarith
  have c4 : Nat.card ↥(invSub P hcomm t) = 5 := by nlinarith
  have e1 : Z = P ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [c3, hZcard])
  have e2 : P₁ = invSub P hcomm t := Subgroup.eq_of_le_of_card_ge hP₁le (by rw [c4, hP1])
  refine ⟨hP₁X, hZX, hP₁P, hZP, hP₁inv, hZfix, hZw, fun c hc hct => ?_, fun c hc hct => ?_, ?_⟩
  · rw [e1]
    exact mem_fixSub.2 ⟨hc, hct⟩
  · rw [e2]
    exact ⟨hc, hct⟩
  ·
    have hZP₁ : Z ≠ P₁ := hx
    have hcZ := Xk_centralizes hV (Or.inr rfl) hZX hP₁X hZP₁
      (fun y hy z hz => hcomm y (hZP hy) z (hP₁P hz))
    have hle : commV Z ≤ fixV P₁ := fun w hw z hz => hcZ z hz w hw
    rw [eq_bot_iff, ← (Xk_decomp hV hP₁X).2]
    exact inf_le_inf_left _ hle

theorem card_commV_of_Xk (hV : ∀ v : V, v ^ 2 = 1) {X Y : Subgroup (MulAut V)}
    (hY : Y ∈ Xk X 2) : Nat.card (commV Y) = 16 := by
  rw [card_eq_two_pow_rk (V := ↥(commV Y)) (fun v => Subtype.ext (by simpa using hV v)), hY.2.2]
  norm_num

omit [Finite V] in
theorem eq_of_same_signs {Y P₁ P₂ : Subgroup (MulAut V)}
    (hs₁ : ∀ r ∈ Y, (∀ y ∈ P₁, r * y * r⁻¹ = y) ∨ (∀ y ∈ P₁, r * y * r⁻¹ = y⁻¹))
    (hs₂ : ∀ r ∈ Y, (∀ y ∈ P₂, r * y * r⁻¹ = y) ∨ (∀ y ∈ P₂, r * y * r⁻¹ = y⁻¹))
    (hf : ∀ r ∈ Y, (∀ y ∈ P₁, r * y * r⁻¹ = y) → (∀ y ∈ P₂, r * y * r⁻¹ = y) → r = 1)
    {a b : MulAut V} (ha : a ∈ Y) (hb : b ∈ Y)
    (h₁ : (∀ y ∈ P₁, a * y * a⁻¹ = y) ↔ (∀ y ∈ P₁, b * y * b⁻¹ = y))
    (h₂ : (∀ y ∈ P₂, a * y * a⁻¹ = y) ↔ (∀ y ∈ P₂, b * y * b⁻¹ = y)) : a = b := by
  have key : ∀ S : Subgroup (MulAut V),
      ((∀ y ∈ S, a * y * a⁻¹ = y) ∨ (∀ y ∈ S, a * y * a⁻¹ = y⁻¹)) →
      ((∀ y ∈ S, b * y * b⁻¹ = y) ∨ (∀ y ∈ S, b * y * b⁻¹ = y⁻¹)) →
      ((∀ y ∈ S, a * y * a⁻¹ = y) ↔ (∀ y ∈ S, b * y * b⁻¹ = y)) →
        ∀ y ∈ S, (b⁻¹ * a) * y * (b⁻¹ * a)⁻¹ = y := by
    intro S hsa hsb hiff
    have e : ∀ y ∈ S, a * y * a⁻¹ = b * y * b⁻¹ := by
      by_cases hca : ∀ y ∈ S, a * y * a⁻¹ = y
      · intro y hy
        rw [hca y hy, hiff.1 hca y hy]
      · have hcb : ¬ ∀ y ∈ S, b * y * b⁻¹ = y := fun h => hca (hiff.2 h)
        intro y hy
        rw [hsa.resolve_left hca y hy, hsb.resolve_left hcb y hy]
    intro y hy
    calc (b⁻¹ * a) * y * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * y * a⁻¹) * b := by group
      _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [e y hy]
      _ = y := by group
  have hc := hf _ (Y.mul_mem (Y.inv_mem hb) ha) (key P₁ (hs₁ a ha) (hs₁ b hb) h₁)
    (key P₂ (hs₂ a ha) (hs₂ b hb) h₂)
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hc, mul_one]

theorem false_of_p5_module (hV : ∀ v : V, v ^ 2 = 1) {X P U Y : Subgroup (MulAut V)}
    (hPX : P ≤ X) (hPn : ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ ∈ P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hcard : Nat.card P = 25)
    (hexp : ∀ x ∈ P, x ^ 5 = 1) {t : MulAut V} (htU : t ∈ U) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htrk : rk (commV (Subgroup.zpowers t)) = 2)
    (hP1 : Nat.card (⁅P, Subgroup.zpowers t⁆ : Subgroup (MulAut V)) = 5)
    (hP1rk : rk (commV ⁅P, Subgroup.zpowers t⁆) = 4) {x : MulAut V} (hxX : x ∈ X)
    (hx : conjBy x ⁅P, Subgroup.zpowers t⁆ ≠ ⁅P, Subgroup.zpowers t⁆) (hUY : U ≤ Y)
    (hYX : Y ≤ X) (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ a ∈ Y, a * a = 1)
    (hYf : ∀ r ∈ Y, (∀ y ∈ P, r * y * r⁻¹ = y) → r = 1)
    (hYfour : ∃ a ∈ Y, ∃ b ∈ Y, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b) {D A : Subgroup V}
    (hA : Nat.card A ≤ 2) (hDidx : ∀ k : ℕ, Nat.card U ≤ 2 ^ k → Nat.card V ≤ 2 ^ k * Nat.card D)
    (hDU : ∀ u ∈ U, ∀ d ∈ D, u d * d⁻¹ ∈ A)
    (hcent : ∀ w ∈ D, (∀ u ∈ U, u w = w) → ∀ b ∈ Y, b w * w⁻¹ ∈ A) : False := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have htY : t ∈ Y := hUY htU
  obtain ⟨hP₁X, hZX, hP₁P, hZP, hP₁inv, hZfix, hZw, hCZ, hIP₁, h12⟩ :=
    p5_structure hV hPX hPn hcomm hcard hexp (hYX htY) ht1 ht2 htrk hP1 hP1rk hxX hx
  set P₁ := ⁅P, Subgroup.zpowers t⁆ with hP₁
  set Z := conjBy x P₁ with hZ
  have htt : t * t = 1 := hY2 t htY
  have hodd : Odd 5 := by decide
  have hZc : Nat.card Z = 5 := hZX.2.1
  have hconj : ∀ r ∈ Y, ∀ y, t * (r * y * r⁻¹) * t⁻¹ = r * (t * y * t⁻¹) * r⁻¹ := by
    intro r hr y
    have e1 : t * r = r * t := (hYc r hr t htY).symm
    calc t * (r * y * r⁻¹) * t⁻¹ = (t * r) * y * (t * r)⁻¹ := by group
      _ = (r * t) * y * (r * t)⁻¹ := by rw [e1]
      _ = r * (t * y * t⁻¹) * r⁻¹ := by group
  have hnP₁ : ∀ r ∈ Y, ∀ y ∈ P₁, r * y * r⁻¹ ∈ P₁ := by
    intro r hr y hy
    refine hIP₁ _ (hPn r (hYX hr) y (hP₁P hy)) ?_
    rw [hconj r hr y, hP₁inv y hy]
    group
  have hnZ : ∀ r ∈ Y, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z := by
    intro r hr z hz
    refine hCZ _ (hPn r (hYX hr) z (hZP hz)) ?_
    rw [hconj r hr z, hZfix z hz]
  have hsP₁ : ∀ r ∈ Y, (∀ y ∈ P₁, r * y * r⁻¹ = y) ∨ (∀ y ∈ P₁, r * y * r⁻¹ = y⁻¹) :=
    fun r hr => fix_or_inv_of_card_prime (p := 5) (by norm_num) hP1 (hY2 r hr) (hnP₁ r hr)
  have hsZ : ∀ r ∈ Y, (∀ z ∈ Z, r * z * r⁻¹ = z) ∨ (∀ z ∈ Z, r * z * r⁻¹ = z⁻¹) :=
    fun r hr => fix_or_inv_of_card_prime (p := 5) (by norm_num) hZc (hY2 r hr) (hnZ r hr)
  have hf : ∀ r ∈ Y, (∀ y ∈ P₁, r * y * r⁻¹ = y) → (∀ z ∈ Z, r * z * r⁻¹ = z) → r = 1 := by
    intro r hr h1 h2
    refine hYf r hr fun c hc => ?_
    obtain ⟨c₁, hc₁, i, hi, hc₁t, hit, rfl⟩ :=
      exists_fix_mul_inv hcomm hodd hexp htt (hPn t (hYX htY)) hc
    have h1' := h1 i (hIP₁ i hi hit)
    have h2' := h2 c₁ (hCZ c₁ hc₁ hc₁t)
    calc r * (c₁ * i) * r⁻¹ = (r * c₁ * r⁻¹) * (r * i * r⁻¹) := by group
      _ = c₁ * i := by rw [h1', h2']
  have hinj := fun {a b : MulAut V} (ha : a ∈ Y) (hb : b ∈ Y) =>
    eq_of_same_signs hsP₁ hsZ hf ha hb
  obtain ⟨y₂, hy₂Z, hy₂5, hfix₂⟩ := exists_fpf_gen hV hZX
  have hU₂ := card_commV_of_Xk hV hZX
  have hy₂U : ∀ u ∈ commV Z, y₂ u ∈ commV Z := fun u hu =>
    commV_smul_mem (fun p hp => Z.mul_mem (Z.mul_mem hy₂Z hp) (Z.inv_mem hy₂Z)) hu
  by_cases hB : ∀ u ∈ U, ∀ z ∈ Z, u * z * u⁻¹ = z
  ·
    have hUt : ∀ u ∈ U, u = 1 ∨ u = t := by
      intro u hu
      by_cases h1 : ∀ y ∈ P₁, u * y * u⁻¹ = y
      · exact Or.inl (hf u (hUY hu) h1 (hB u hu))
      · right
        refine hinj (hUY hu) htY ⟨fun h => absurd h h1, fun h => ?_⟩
          ⟨fun _ => hB t htU, fun _ => hB u hu⟩
        exfalso
        obtain ⟨y, hyP₁, hy1, -, -⟩ := exists_generator_of_prime_card hP1
        have h3 := hP₁inv y hyP₁
        rw [h y hyP₁] at h3
        refine hy1 (eq_one_of_sq_of_pow_odd hodd (hexp y (hP₁P hyP₁)) ?_)
        nth_rewrite 2 [h3]
        exact mul_inv_cancel y
    have hU2 : Nat.card U ≤ 2 ^ 1 := by
      classical
      have hi : Function.Injective fun u : ↥U => decide ((u : MulAut V) = 1) := by
        intro a b hab
        simp only at hab
        rcases hUt a a.2 with ha | ha <;> rcases hUt b b.2 with hb | hb
        · exact Subtype.ext (ha.trans hb.symm)
        · rw [ha, hb] at hab
          simp [ht1] at hab
        · rw [ha, hb] at hab
          simp [ht1] at hab
        · exact Subtype.ext (ha.trans hb.symm)
      have := Nat.card_le_card_of_injective _ hi
      rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    have hD2 := hDidx 1 hU2
    have hCD : ∀ w : V, t w = w → w ∈ D := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hct, hcD⟩ := hcon
      have hidx : D.index = 2 := by
        have h1 := Subgroup.card_mul_index D
        have hpos : 0 < Nat.card D := Nat.card_pos
        have h2 : D.index ≤ 2 := by nlinarith
        have h3 : D.index ≠ 1 := fun h => hcD (Subgroup.index_eq_one.1 h ▸ Subgroup.mem_top c)
        have h4 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have hall : ∀ w : V, t w * w⁻¹ ∈ A := by
        intro w
        by_cases hw : w ∈ D
        · exact hDU t htU w hw
        · have hwc : w * c⁻¹ ∈ D := by
            rw [Subgroup.mul_mem_iff_of_index_two hidx]
            exact ⟨fun h => absurd h hw, fun h => absurd (D.inv_mem_iff.1 h) hcD⟩
          have := hDU t htU _ hwc
          rwa [map_mul, map_inv, hct, mul_inv, inv_inv, mul_mul_mul_comm, inv_mul_cancel,
            mul_one] at this
      have hle : commV (Subgroup.zpowers t) ≤ A := by
        rw [commV_zpowers_eq_map]
        rintro _ ⟨w, -, rfl⟩
        exact hall w
      have h4 : Nat.card (commV (Subgroup.zpowers t)) = 4 := by
        rw [card_eq_two_pow_rk (V := ↥(commV (Subgroup.zpowers t)))
          (fun v => Subtype.ext (by simpa using hV v)), htrk]
        rfl
      have := Subgroup.card_le_of_le hle
      omega
    have hfixU : ∀ w ∈ commV Z, ∀ u ∈ U, u w = w := by
      intro w hw u hu
      rcases hUt u hu with rfl | rfl
      · rfl
      · exact hZw w hw
    obtain ⟨b, hbY, hbinv⟩ : ∃ b ∈ Y, ∀ z ∈ Z, b * z * b⁻¹ = z⁻¹ := by
      obtain ⟨a, haY, a', ha'Y, ha1, ha'1, hne⟩ := hYfour
      by_contra hcon
      push Not at hcon
      have hcZ : ∀ r ∈ Y, ∀ z ∈ Z, r * z * r⁻¹ = z := fun r hr =>
        (hsZ r hr).resolve_right fun h => by
          obtain ⟨z, hz, hne'⟩ := hcon r hr
          exact hne' (h z hz)
      have hnc : ∀ r ∈ Y, r ≠ 1 → ¬ ∀ y ∈ P₁, r * y * r⁻¹ = y := fun r hr hr1 h =>
        hr1 (hf r hr h (hcZ r hr))
      exact hne (hinj haY ha'Y ⟨fun h => absurd h (hnc a haY ha1),
        fun h => absurd h (hnc a' ha'Y ha'1)⟩ ⟨fun _ => hcZ a' ha'Y, fun _ => hcZ a haY⟩)
    exact false_of_inverts hU₂ hy₂U (hbinv y₂ hy₂Z) hy₂5 hfix₂ hA fun u hu =>
      hcent u (hCD u (hZw u hu)) (hfixU u hu) b hbY
  ·
    push Not at hB
    obtain ⟨t', ht'U, z₀, hz₀, hz₀ne⟩ := hB
    have ht'inv : ∀ z ∈ Z, t' * z * t'⁻¹ = z⁻¹ :=
      (hsZ t' (hUY ht'U)).resolve_left fun h => hz₀ne (h z₀ hz₀)
    have hU4 : Nat.card U ≤ 2 ^ 2 := by
      classical
      have hi : Function.Injective fun u : ↥U =>
          (decide (∀ y ∈ P₁, (u : MulAut V) * y * (u : MulAut V)⁻¹ = y),
            decide (∀ z ∈ Z, (u : MulAut V) * z * (u : MulAut V)⁻¹ = z)) := by
        intro a b hab
        simp only [Prod.mk.injEq] at hab
        exact Subtype.ext (hinj (hUY a.2) (hUY b.2) (decide_eq_decide.1 hab.1)
          (decide_eq_decide.1 hab.2))
      have := Nat.card_le_card_of_injective _ hi
      rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    obtain ⟨y₁, hy₁P₁, hy₁5, hfix₁⟩ := exists_fpf_gen hV hP₁X
    have hU₁ := card_commV_of_Xk hV hP₁X
    have hy₁U : ∀ u ∈ commV P₁, y₁ u ∈ commV P₁ := fun u hu =>
      commV_smul_mem (fun p hp => P₁.mul_mem (P₁.mul_mem hy₁P₁ hp) (P₁.inv_mem hy₁P₁)) hu
    have htU₁ : ∀ u ∈ commV P₁, t u ∈ commV P₁ := fun u hu =>
      commV_smul_mem (fun p hp => by rw [hP₁inv p hp]; exact P₁.inv_mem hp) hu
    exact false_of_two_inverts hU₁ hU₂ h12 hy₁U (hP₁inv y₁ hy₁P₁) hy₁5 hfix₁ htU₁ hZw hy₂U
      (ht'inv y₂ hy₂Z) hy₂5 hfix₂ (fun u hu => commV_smul_mem (hnP₁ t' (hUY ht'U)) hu)
      (fun u hu => commV_smul_mem (hnZ t' (hUY ht'U)) hu) hA (hDidx 2 hU4) (hDU t htU)
      (hDU t' ht'U)

end A6Four

end CFSG.Quasithin.H13.A6
