module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofA10
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

namespace Proof1721

theorem normal_three_eq_bot_of_s4 {H : Type} [Group H] [Finite H]
    (hH : Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))
    (N : Subgroup H) (hN : N.Normal) (h3 : IsPGroup 3 N) : N = ⊥ := by
  rcases hH with hH | ⟨⟨e⟩⟩
  · exact CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_perm_four hH 3
      Nat.prime_three (by decide) N hN h3
  · set f : H →* Equiv.Perm (Fin 4) := (MonoidHom.snd _ _).comp e.toMonoidHom with hf
    have hfs : Function.Surjective f := fun y => ⟨e.symm (1, y), by simp [hf]⟩
    have hM : N.map f = ⊥ := CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
      ⟨MulEquiv.refl _⟩ 3 Nat.prime_three (by decide) (N.map f) (hN.map f hfs) (h3.map f)
    rw [eq_bot_iff]
    intro n hn
    have hfn : f n = 1 := by
      have : f n ∈ N.map f := Subgroup.mem_map_of_mem f hn
      rwa [hM, Subgroup.mem_bot] at this
    obtain ⟨k, hk⟩ := h3 ⟨n, hn⟩
    have hk' : n ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have he2 : (e n).2 = 1 := hfn
    have hz : (e n).1 ^ 3 ^ k = 1 := by
      have := congrArg (fun h => (e h).1) hk'
      simpa using this
    have hz2 : (e n).1 ^ 2 = 1 := by
      have h : (e n).1 ^ Nat.card (Multiplicative (ZMod 2)) = 1 := pow_card_eq_one'
      rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
    have hz1 : (e n).1 = 1 := by
      obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
      rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul] at hz
      exact hz
    have hen : e n = 1 := Prod.ext hz1 he2
    exact Subgroup.mem_bot.mpr (e.injective (hen.trans e.map_one.symm))

section Frame

variable {E : Type} [Group E]

omit [Group E] in
theorem zpow_emod_three {M : Type} [Group M] {x : M} (hx : x ^ 3 = 1) (k : ℤ) :
    x ^ k = x ^ (k % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
  rw [zpow_add, zpow_mul, show x ^ (3 : ℤ) = 1 by exact_mod_cast hx, one_zpow, mul_one]

theorem exists_zpow_mul_of_sup_eq_top (hcomm : ∀ x y : E, x * y = y * x) {B : Subgroup E}
    {a : E} (htop : Subgroup.zpowers a ⊔ B = ⊤) (x : E) : ∃ k : ℤ, ∃ b ∈ B, x = a ^ k * b := by
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer (B : Set E) := fun y _ =>
    Subgroup.mem_normalizer_iff.mpr fun h => by rw [hcomm y h, mul_inv_cancel_right]
  have hx : x ∈ ((Subgroup.zpowers a ⊔ B : Subgroup E) : Set E) := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx
  obtain ⟨y, hy, b, hb, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨k, b, hb, rfl⟩

theorem false_of_orbit_le_three [Finite E] (hcomm : ∀ x y : E, x * y = y * x)
    (hE3 : ∀ x : E, x ^ 3 = 1) (hE27 : Nat.card E = 27) (H : Subgroup (MulAut E))
    (hH3 : ∀ N : Subgroup H, N.Normal → IsPGroup 3 N → N = ⊥) (hH : 12 < Nat.card H)
    (e : E) (horb : (MulAction.orbit H e).ncard ≤ 3) (o : E)
    (ho : o ∈ MulAction.orbit H e) (hoe : o ∉ Subgroup.zpowers e) : False := by
  classical
  set St := MulAction.stabilizer H e with hSt
  set K₀ := St.normalCore with hK₀
  have hidx : St.index ≤ 3 := by rw [hSt, MulAction.index_stabilizer]; exact horb
  have hK₀dvd : K₀.index ∣ Nat.factorial 3 := by
    refine Dvd.dvd.trans ?_ (Nat.factorial_dvd_factorial hidx)
    rw [hK₀, Subgroup.normalCore_eq_ker, Subgroup.index_ker, Subgroup.index_eq_card,
      ← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card _
  have hK₀le : K₀.index ≤ 6 := Nat.le_of_dvd (by decide) hK₀dvd
  have hK₀card : 2 < Nat.card K₀ := by
    have h := Subgroup.card_mul_index K₀
    by_contra hle
    have hle' : Nat.card K₀ ≤ 2 := by omega
    have := Nat.mul_le_mul hle' hK₀le
    omega
  have hfix : ∀ σ ∈ K₀, ∀ τ : H, σ • τ • e = τ • e := by
    intro σ hσ τ
    have h1 : τ⁻¹ * σ * τ ∈ St := by simpa using hσ τ⁻¹
    rw [MulAction.mem_stabilizer_iff] at h1
    calc σ • τ • e = (τ * (τ⁻¹ * σ * τ)) • e := by
          rw [smul_smul]; exact congrArg (· • e) (by group)
      _ = τ • e := by rw [← smul_smul, h1]
  set B := Subgroup.closure (MulAction.orbit H e) with hB
  have horbB : MulAction.orbit H e ⊆ B := Subgroup.subset_closure
  have hBfix : ∀ σ ∈ K₀, ∀ y ∈ B, (σ : MulAut E) y = y := by
    intro σ hσ y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨τ, rfl⟩ := hx
      exact hfix σ hσ τ
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have hBinv : ∀ τ : H, ∀ y ∈ B, (τ : MulAut E) y ∈ B := by
    intro τ y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨τ', rfl⟩ := hx
      exact horbB (MulAction.mem_orbit_iff.mpr ⟨τ * τ', (smul_smul τ τ' e).symm⟩)
    | one => rw [map_one]; exact B.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact B.inv_mem hx
  by_cases hBtop : B = ⊤
  ·
    have hK₀bot : K₀ = ⊥ := by
      rw [eq_bot_iff]
      intro σ hσ
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      ext y
      exact hBfix σ hσ y (by rw [hBtop]; exact Subgroup.mem_top y)
    rw [hK₀bot, Subgroup.card_bot] at hK₀card
    omega
  have he1 : e ≠ 1 := by
    rintro rfl
    obtain ⟨τ, rfl⟩ := ho
    exact hoe (by
      show (τ : MulAut E) 1 ∈ Subgroup.zpowers (1 : E)
      rw [map_one]
      exact Subgroup.one_mem _)
  have he3 : orderOf e = 3 := orderOf_eq_prime (hE3 e) he1
  have hcard_e : Nat.card (Subgroup.zpowers e) = 3 := by rw [Nat.card_zpowers, he3]
  have heB : Subgroup.zpowers e ≤ B :=
    Subgroup.zpowers_le.mpr (horbB (MulAction.mem_orbit_self e))
  have hlt : Subgroup.zpowers e < B :=
    lt_of_le_of_ne heB (fun h => hoe (h ▸ horbB ho))
  have h3B : 3 < Nat.card B := hcard_e ▸ Subgroup.card_lt_of_lt hlt
  have hB27 : Nat.card B ∣ 27 := hE27 ▸ Subgroup.card_subgroup_dvd_card B
  have hBne : Nat.card B ≠ 27 := fun h =>
    hBtop (Subgroup.eq_top_of_card_eq B (h.trans hE27.symm))
  have hB9 : Nat.card B = 9 := by
    obtain ⟨k, hk, hkB⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card B ∣ 3 ^ 3 from hB27)
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · rw [hkB] at h3B; norm_num at h3B
    · rw [hkB] at h3B; norm_num at h3B
    · rw [hkB]; norm_num
    · exact absurd (hkB.trans (by norm_num)) hBne
  obtain ⟨a, -, haB⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hBtop)
  have htop : Subgroup.zpowers a ⊔ B = ⊤ := by
    have hlt' : B < Subgroup.zpowers a ⊔ B :=
      lt_of_le_of_ne le_sup_right (fun h => haB (h ▸
        (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ B) (Subgroup.mem_zpowers a)))
    have h1 := Subgroup.card_lt_of_lt hlt'
    have h3 : Nat.card (Subgroup.zpowers a ⊔ B : Subgroup E) ∣ 3 ^ 3 := by
      have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers a ⊔ B)
      rw [hE27] at h
      exact h
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
    apply Subgroup.eq_top_of_card_eq
    rw [hE27, hjc]
    rw [hB9, hjc] at h1
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · norm_num at h1
    · norm_num at h1
    · norm_num at h1
    · norm_num
  have hdec := exists_zpow_mul_of_sup_eq_top hcomm htop
  let K'' : Subgroup H :=
    { carrier := {σ | (∀ y ∈ B, (σ : MulAut E) y = y) ∧ ∀ x, (σ : MulAut E) x * x⁻¹ ∈ B}
      one_mem' := ⟨fun y _ => rfl, fun x => by simp⟩
      mul_mem' := by
        rintro σ τ ⟨hσ1, hσ2⟩ ⟨hτ1, hτ2⟩
        refine ⟨fun y hy => ?_, fun x => ?_⟩
        · show (σ : MulAut E) ((τ : MulAut E) y) = y
          rw [hτ1 y hy, hσ1 y hy]
        · show (σ : MulAut E) ((τ : MulAut E) x) * x⁻¹ ∈ B
          have : (σ : MulAut E) ((τ : MulAut E) x) * x⁻¹ =
              ((σ : MulAut E) ((τ : MulAut E) x) * ((τ : MulAut E) x)⁻¹) *
                ((τ : MulAut E) x * x⁻¹) := by group
          rw [this]
          exact B.mul_mem (hσ2 _) (hτ2 x)
      inv_mem' := by
        rintro σ ⟨hσ1, hσ2⟩
        refine ⟨fun y hy => ?_, fun x => ?_⟩
        · show (σ : MulAut E)⁻¹ y = y
          calc (σ : MulAut E)⁻¹ y = (σ : MulAut E)⁻¹ ((σ : MulAut E) y) := by rw [hσ1 y hy]
            _ = y := MulAut.inv_apply_self _ _ y
        · show (σ : MulAut E)⁻¹ x * x⁻¹ ∈ B
          have h := B.inv_mem (hσ2 ((σ : MulAut E)⁻¹ x))
          rwa [MulAut.apply_inv_self, mul_inv_rev, inv_inv] at h }
  have hK''n : K''.Normal := by
    refine ⟨fun σ hσ τ => ⟨fun y hy => ?_, fun x => ?_⟩⟩
    · show (τ : MulAut E) ((σ : MulAut E) ((τ : MulAut E)⁻¹ y)) = y
      have hy' : (τ : MulAut E)⁻¹ y ∈ B := hBinv τ⁻¹ y hy
      rw [hσ.1 _ hy', MulAut.apply_inv_self]
    · show (τ : MulAut E) ((σ : MulAut E) ((τ : MulAut E)⁻¹ x)) * x⁻¹ ∈ B
      have h := hBinv τ _ (hσ.2 ((τ : MulAut E)⁻¹ x))
      rwa [map_mul, map_inv, MulAut.apply_inv_self] at h
  have hK''3 : IsPGroup 3 K'' := by
    rintro ⟨σ, hσ1, hσ2⟩
    refine ⟨1, ?_⟩
    ext x
    set f : MulAut E := (σ : MulAut E) with hf
    obtain ⟨b, hbB, hfx⟩ : ∃ b ∈ B, f x = b * x :=
      ⟨f x * x⁻¹, hσ2 x, by rw [inv_mul_cancel_right]⟩
    have hfb : f b = b := hσ1 b hbB
    show (f ^ 3) x = x
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hfx, map_mul, hfb, hfx,
      map_mul, hfb, map_mul, hfb, hfx, ← mul_assoc, ← mul_assoc, ← pow_three', hE3, one_mul]
  have hK''bot : K'' = ⊥ := hH3 K'' hK''n hK''3
  have hK'' : ∀ σ ∈ K₀, (σ : MulAut E) a * a⁻¹ ∈ B → σ ∈ K'' := by
    intro σ hσ hσa
    refine ⟨hBfix σ hσ, fun x => ?_⟩
    obtain ⟨k, b, hb, rfl⟩ := hdec x
    rw [map_mul, map_zpow, hBfix σ hσ b hb, mul_inv_rev, mul_assoc, mul_inv_cancel_left,
      ← inv_zpow, ← (Commute.mul_zpow (hcomm ((σ : MulAut E) a) a⁻¹) k)]
    exact B.zpow_mem hσa k
  have hsign : ∀ σ ∈ K₀, (σ : MulAut E) a * a⁻¹ ∈ B ∨ (σ : MulAut E) a * a ∈ B := by
    intro σ hσ
    obtain ⟨k, b, hb, hk⟩ := hdec ((σ : MulAut E) a)
    rw [zpow_emod_three (hE3 a)] at hk
    obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    · exfalso
      rw [h, zpow_zero, one_mul] at hk
      have hfaB : (σ : MulAut E) a ∈ B := by rw [hk]; exact hb
      have h1 := hBfix σ⁻¹ (K₀.inv_mem hσ) _ hfaB
      have h2 : ((σ⁻¹ : H) : MulAut E) ((σ : MulAut E) a) = a := MulAut.inv_apply_self _ _ a
      exact haB (by rw [← h2, h1]; exact hfaB)
    · left
      rw [hk, h, zpow_one, hcomm a b, mul_inv_cancel_right]
      exact hb
    · right
      rw [hk, h, hcomm (a ^ (2 : ℤ)) b, mul_assoc, ← zpow_add_one,
        show (2 : ℤ) + 1 = 3 by norm_num, show a ^ (3 : ℤ) = 1 by exact_mod_cast hE3 a, mul_one]
      exact hb
  have hneg : ∀ σ ∈ K₀, ∀ τ ∈ K₀, (σ : MulAut E) a * a ∈ B → (τ : MulAut E) a * a ∈ B →
      ((σ * τ⁻¹ : H) : MulAut E) a * a⁻¹ ∈ B := by
    intro σ hσ τ hτ hσa hτa
    set f := (σ : MulAut E) with hf
    set g := (τ : MulAut E) with hg
    have hga : g⁻¹ a = a⁻¹ * (g a * a) := by
      have h1 : g (a⁻¹ * (g a * a)) = a := by
        rw [map_mul, map_inv, hBfix τ hτ _ hτa, inv_mul_cancel_left]
      calc g⁻¹ a = g⁻¹ (g (a⁻¹ * (g a * a))) := by rw [h1]
        _ = a⁻¹ * (g a * a) := MulAut.inv_apply_self _ g _
    show f (g⁻¹ a) * a⁻¹ ∈ B
    rw [hga, map_mul, map_inv, hBfix σ hσ _ hτa, hcomm ((f a)⁻¹ * (g a * a)) a⁻¹, ← mul_assoc,
      ← mul_inv_rev]
    exact B.mul_mem (B.inv_mem hσa) hτa
  have hεinj : ∀ σ ∈ K₀, ∀ τ ∈ K₀,
      ((σ : MulAut E) a * a⁻¹ ∈ B ↔ (τ : MulAut E) a * a⁻¹ ∈ B) → σ = τ := by
    intro σ hσ τ hτ hiff
    by_cases hσa : (σ : MulAut E) a * a⁻¹ ∈ B
    · have h1 : σ ∈ K'' := hK'' σ hσ hσa
      have h2 : τ ∈ K'' := hK'' τ hτ (hiff.mp hσa)
      rw [hK''bot, Subgroup.mem_bot] at h1 h2
      rw [h1, h2]
    · have hτa : (τ : MulAut E) a * a⁻¹ ∉ B := fun h => hσa (hiff.mpr h)
      have h3 : σ * τ⁻¹ ∈ K'' := hK'' (σ * τ⁻¹) (K₀.mul_mem hσ (K₀.inv_mem hτ))
        (hneg σ hσ τ hτ ((hsign σ hσ).resolve_left hσa) ((hsign τ hτ).resolve_left hτa))
      rw [hK''bot, Subgroup.mem_bot, mul_inv_eq_one] at h3
      exact h3
  have hcard2 : Nat.card K₀ ≤ 2 := by
    let ε : K₀ → Bool := fun σ => decide (((σ : H) : MulAut E) a * a⁻¹ ∈ B)
    have hε : Function.Injective ε := fun σ τ hστ =>
      Subtype.ext (hεinj σ σ.2 τ τ.2 (decide_eq_decide.mp hστ))
    have := Nat.card_le_card_of_injective ε hε
    simpa using this
  omega

theorem conj_eq_of_mem_zpowers {M : Type} [Group M] {c k : M} (hc3 : orderOf c = 3)
    (hk : k * c * k⁻¹ ∈ Subgroup.zpowers c) (hkc : k * c * k⁻¹ ≠ c⁻¹) : k * c * k⁻¹ = c := by
  have hc : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk
  rw [zpow_emod_three hc] at hn
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · exfalso
    rw [h, zpow_zero] at hn
    have h1 : k * c * k⁻¹ = 1 := hn.symm
    rw [mul_inv_eq_one, mul_eq_left] at h1
    rw [h1, orderOf_one] at hc3
    omega
  · rw [h, zpow_one] at hn
    exact hn.symm
  · exfalso
    apply hkc
    rw [← hn, h, eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]
    exact_mod_cast hc

end Frame

end Proof1721

open Proof1721 in
theorem ks1721Frame_proof : KS1721Frame := by
  intro G _ _ A hA hW Ω hΩ3 hΩA hΩinv c hcΩ hΩtr
  by_contra hno
  have hno' : ∀ g ∈ Subgroup.normalizer (A : Set G), g * c * g⁻¹ ≠ c⁻¹ :=
    fun g hg h => hno ⟨g, hg, h⟩
  have hcA : c ∈ A := (hΩA _ hcΩ).1 (Subgroup.mem_zpowers c)
  have hc3 : orderOf c = 3 := by rw [← Nat.card_zpowers]; exact (hΩA _ hcΩ).2
  set H := wStar A with hH
  have hHmem : ∀ σ : H, ∃ g ∈ Subgroup.normalizer (A : Set G),
      ∀ x : A, (((σ : MulAut A) x : A) : G) = g * x * g⁻¹ := by
    intro σ
    obtain ⟨g, hg, -, hσ⟩ := Sec4.mem_autIn_iff.mp σ.2
    exact ⟨g, hg, fun x => by rw [← hσ, Sec4.normalizerMonoidHom_apply_coe]⟩
  set e : A := ⟨c, hcA⟩ with he
  have hΩfin : Ω.Finite := Set.finite_of_ncard_ne_zero (by rw [hΩ3]; norm_num)
  have hmaps : ∀ x ∈ MulAction.orbit H e, Subgroup.zpowers (x : G) ∈ Ω := by
    intro x hx
    obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    obtain ⟨g, hg, hσ⟩ := hHmem σ
    have hσe : ((σ • e : A) : G) = g * c * g⁻¹ := hσ e
    rw [hσe]
    have := hΩinv g hg _ hcΩ
    rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hinj : Set.InjOn (fun x : A => Subgroup.zpowers (x : G)) (MulAction.orbit H e) := by
    intro x hx y hy hxy
    obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    obtain ⟨τ, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨g, hg, hσ⟩ := hHmem σ
    obtain ⟨h, hh, hτ⟩ := hHmem τ
    have hσe : ((σ • e : A) : G) = g * c * g⁻¹ := hσ e
    have hτe : ((τ • e : A) : G) = h * c * h⁻¹ := hτ e
    simp only [hσe, hτe] at hxy
    apply Subtype.ext
    rw [hσe, hτe]
    have hmem : (h⁻¹ * g) * c * (h⁻¹ * g)⁻¹ ∈ Subgroup.zpowers c := by
      have h1 : g * c * g⁻¹ ∈ Subgroup.zpowers (h * c * h⁻¹) := by
        rw [← hxy]
        exact Subgroup.mem_zpowers _
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [show (h⁻¹ * g) * c * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * c * g⁻¹) * h by group, ← hn, conj_zpow]
      group
    have hk := conj_eq_of_mem_zpowers hc3 hmem (hno' _ (mul_mem (inv_mem hh) hg))
    calc g * c * g⁻¹ = h * ((h⁻¹ * g) * c * (h⁻¹ * g)⁻¹) * h⁻¹ := by group
      _ = h * c * h⁻¹ := by rw [hk]
  have horb : (MulAction.orbit H e).ncard ≤ 3 := by
    have := Set.ncard_le_ncard_of_injOn _ hmaps hinj hΩfin
    rwa [hΩ3] at this
  obtain ⟨F, hF, hFc⟩ :=
    Set.exists_ne_of_one_lt_ncard (by rw [hΩ3]; norm_num) (Subgroup.zpowers c)
  obtain ⟨g, hg, rfl⟩ := hΩtr F hF
  set σ : H := ⟨A.normalizerMonoidHom ⟨g, hg⟩,
    Sec4.mem_autIn_iff.mpr ⟨g, hg, Subgroup.mem_top g, rfl⟩⟩ with hσ
  have hσe : ((σ • e : A) : G) = g * c * g⁻¹ := Sec4.normalizerMonoidHom_apply_coe hg e
  have hoe : σ • e ∉ Subgroup.zpowers e := by
    intro hmem
    apply hFc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : g * c * g⁻¹ = c ^ n := by
      rw [← hσe, ← hn]
      rfl
    have hle : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers c := by
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h1]
      exact Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers c n)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [(hΩA _ hcΩ).2, (hΩA _ hF).2]
  have hHcard : 12 < Nat.card H := by
    rcases hW with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    · rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin,
        Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      decide
  have hH3 : ∀ N : Subgroup H, N.Normal → IsPGroup 3 N → N = ⊥ :=
    fun N hN h3 => normal_three_eq_bot_of_s4 hW N hN h3
  exact false_of_orbit_le_three (fun x y => hA.1.1.is_comm.comm x y)
    (fun x => Subtype.ext (by simpa using hA.1.2 x x.2)) hA.2 H hH3 hHcard e horb (σ • e)
    (MulAction.mem_orbit e σ) hoe

theorem claim1721SA10_proof (h1715 : Item1715) : Claim1721SA10 :=
  claim1721SA10_of h1715 ks1721Frame_proof

end CFSG.RankThree.PartTwo.Sec17
