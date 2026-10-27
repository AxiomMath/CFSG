module

public import CFSG.OddTranspositions.PartThree.Nine.SixAEightSetup
import CFSG.OddTranspositions.PartThree.Nine.FinalNonabelian
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightCoordinates

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm
  cosetNormalizerPerm_apply cosetNormalizerPerm_ker_eq_entire_centralizer)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace NineSixSetting

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

omit [Finite G] in
private theorem exists_mul_eq_of_mem_sup {K H : Subgroup G}
    (hKH : K ≤ Subgroup.normalizer (H : Set G)) {m : G} (hm : m ∈ K ⊔ H) :
    ∃ k ∈ K, ∃ x ∈ H, k * x = m := by
  let P : Subgroup G :=
    { carrier := {m | ∃ k ∈ K, ∃ x ∈ H, k * x = m}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, x₁, hx₁, rfl⟩ ⟨k₂, hk₂, x₂, hx₂, rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₂⁻¹ * x₁ * k₂⁻¹⁻¹ * x₂,
          H.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKH (K.inv_mem hk₂)) x₁).mp hx₁) hx₂, ?_⟩
        group
      one_mem' := ⟨1, K.one_mem, 1, H.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨k, hk, x, hx, rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k * x⁻¹ * k⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hKH hk) x⁻¹).mp (H.inv_mem hx), ?_⟩
        group }
  exact (sup_le (fun k hk => ⟨k, hk, 1, H.one_mem, mul_one k⟩)
    (fun x hx => ⟨1, K.one_mem, x, hx, one_mul x⟩) : K ⊔ H ≤ P) hm

omit [Finite G] in
private theorem card_sup_of_le_normalizer {K H : Subgroup G}
    (hKH : K ≤ Subgroup.normalizer (H : Set G)) (hinf : K ⊓ H = ⊥) :
    Nat.card ↥(K ⊔ H) = Nat.card K * Nat.card H := by
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective (fun p : K × H => (⟨p.1 * p.2, (K ⊔ H).mul_mem
    (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ : ↥(K ⊔ H))) ⟨?_, ?_⟩).symm
  · rintro ⟨⟨k₁, hk₁⟩, ⟨x₁, hx₁⟩⟩ ⟨⟨k₂, hk₂⟩, ⟨x₂, hx₂⟩⟩ h12
    have h12 : k₁ * x₁ = k₂ * x₂ := congrArg Subtype.val h12
    have hk : k₂⁻¹ * k₁ ∈ K ⊓ H := ⟨K.mul_mem (K.inv_mem hk₂) hk₁, by
      rw [show k₂⁻¹ * k₁ = x₂ * x₁⁻¹ by rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h12]; group]
      exact H.mul_mem hx₂ (H.inv_mem hx₁)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hk
    subst hk
    simp only [mul_right_inj] at h12
    subst h12
    rfl
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk, x, hx, rfl⟩ := exists_mul_eq_of_mem_sup hKH hm
    exact ⟨(⟨k, hk⟩, ⟨x, hx⟩), rfl⟩

omit [Finite G] in
private theorem eq_one_or_eq_of_mem_zpowers {a m : G} (ha : a * a = 1)
    (hm : m ∈ Subgroup.zpowers a) : m = 1 ∨ m = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · exact Or.inl (zpow_zero a)
  · exact Or.inr (zpow_one a)

private theorem sup_zpowers_eq {H K : Subgroup G} (hHK : H ≤ K)
    (hcard : Nat.card K = 2 * Nat.card H) {w : G} (hwK : w ∈ K) (hwH : w ∉ H) :
    H ⊔ Subgroup.zpowers w = K := by
  have hle : H ⊔ Subgroup.zpowers w ≤ K := sup_le hHK (Subgroup.zpowers_le.mpr hwK)
  have hH0 : 0 < Nat.card H := Nat.card_pos
  have hdvd1 : Nat.card H ∣ Nat.card ↥(H ⊔ Subgroup.zpowers w) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(H ⊔ Subgroup.zpowers w) ∣ Nat.card K := Subgroup.card_dvd_of_le hle
  have hne : Nat.card ↥(H ⊔ Subgroup.zpowers w) ≠ Nat.card H := fun he =>
    hwH ((Subgroup.eq_of_le_of_card_ge le_sup_left he.le) ▸
      Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  obtain ⟨c, hc⟩ := hdvd1
  obtain ⟨d, hd⟩ := hdvd2
  rw [hcard, hc, mul_assoc] at hd
  have hcd : c * d = 2 := Nat.eq_of_mul_eq_mul_left hH0 (hd.symm.trans (mul_comm 2 _))
  have hc1 : c ≠ 1 := fun h1 => hne (by rw [hc, h1, mul_one])
  have hc2 : c = 2 := by
    rcases Nat.dvd_prime Nat.prime_two |>.mp (Dvd.intro d hcd) with h | h
    · exact absurd h hc1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hc, hc2, mul_comm])

private theorem card_inf_centralizer_eq_four {W : Subgroup G}
    (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hsq : ∀ v ∈ W, v * v = 1)
    (hW8 : Nat.card W = 8) {x : G} (hxW : ∀ v ∈ W, x * v * x⁻¹ ∈ W) (hx2 : x * x = 1)
    (hxc : ∃ v ∈ W, x * v * x⁻¹ ≠ v) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) = 4 := by
  classical
  set F := W ⊓ Subgroup.centralizer ({x} : Set G) with hF
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hmemF : ∀ v, v ∈ F ↔ v ∈ W ∧ x * v * x⁻¹ = v := fun v => by
    rw [hF, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ⟨fun h => by rw [← h, mul_inv_cancel_right], fun h => ?_⟩
    calc v * x = x * v * x⁻¹ * x := by rw [h]
      _ = x * v := by group
  let κ : ↥W →* ↥W :=
    { toFun := fun v => ⟨(v : G)⁻¹ * (x * v * x⁻¹), W.mul_mem (W.inv_mem v.2) (hxW v v.2)⟩
      map_one' := by ext; simp
      map_mul' := fun v w => by
        ext
        simp only [Subgroup.coe_mul, mul_inv_rev]
        have h1 := hcomm _ (W.inv_mem w.2) _
          (W.mul_mem (W.inv_mem v.2) (hxW v v.2))
        calc (w : G)⁻¹ * (v : G)⁻¹ * (x * (v * w) * x⁻¹)
            = (w : G)⁻¹ * ((v : G)⁻¹ * (x * v * x⁻¹)) * (x * w * x⁻¹) := by group
          _ = (v : G)⁻¹ * (x * v * x⁻¹) * ((w : G)⁻¹ * (x * w * x⁻¹)) := by
            rw [h1]; group }
  have hker : ∀ v : W, κ v = 1 ↔ (v : G) ∈ F := fun v => by
    rw [hmemF, Subtype.ext_iff]
    simp only [κ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one, inv_mul_eq_one]
    exact ⟨fun h => ⟨v.2, h.symm⟩, fun h => h.2.symm⟩
  have hrange : ∀ v : W, ((κ v : W) : G) ∈ F := fun v => by
    rw [hmemF]
    refine ⟨(κ v).2, ?_⟩
    change x * ((v : G)⁻¹ * (x * v * x⁻¹)) * x⁻¹ = (v : G)⁻¹ * (x * v * x⁻¹)
    have hv := hsq _ v.2
    have hvinv : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right hv
    rw [hvinv, hxinv]
    have hc := hcomm _ (hxW v v.2) _ v.2
    rw [hxinv] at hc
    calc x * (↑v * (x * ↑v * x)) * x = x * ↑v * x * ↑v * (x * x) := by group
      _ = ↑v * (x * ↑v * x) := by rw [hx2, mul_one, hc]
  have hkerF : Nat.card κ.ker = Nat.card F := by
    refine Nat.card_congr ⟨fun v => ⟨((v : W) : G), (hker v).mp v.2⟩,
      fun v => ⟨⟨v, (hmemF v).mp v.2 |>.1⟩, (hker _).mpr v.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hrangeF : Nat.card κ.range ≤ Nat.card F := by
    refine Nat.card_le_card_of_injective (fun v => ⟨((v : W) : G), ?_⟩) ?_
    · obtain ⟨w, hw⟩ := v.2
      rw [← hw]
      exact hrange w
    · intro v w hvw
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hvw))
  have hmul : Nat.card κ.range * Nat.card κ.ker = 8 := by
    rw [← hW8, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange κ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hF8 : Nat.card F ≠ 8 := by
    intro h8
    have hFW : F = W := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hW8])
    obtain ⟨v, hv, hxv⟩ := hxc
    exact hxv ((hmemF v).mp (hFW ▸ hv)).2
  have hFdvd : Nat.card F ∣ 8 := hW8 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hFle : Nat.card F ≤ 8 := Nat.le_of_dvd (by norm_num) hFdvd
  rw [hkerF] at hmul
  have hpos : 0 < Nat.card κ.range := Nat.card_pos
  have hsq8 : 8 ≤ Nat.card F * Nat.card F := by
    calc 8 = Nat.card κ.range * Nat.card F := hmul.symm
      _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul_right _ hrangeF
  interval_cases h : Nat.card F <;> omega

omit [Finite G] in
private theorem zpowers_le_normalizer_of_commute {a b : G} (hab : a * b = b * a) :
    Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro m
  have hc : ∀ k : ℤ, a * b ^ k * a⁻¹ = b ^ k := fun k => by
    rw [((Commute.zpow_right (show Commute a b from hab) k)).eq, mul_inv_cancel_right]
  constructor
  · rintro hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    rw [hc]
    exact Subgroup.zpow_mem_zpowers b k
  · intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have : m = b ^ k := by
      calc m = a⁻¹ * (a * m * a⁻¹) * a := by group
        _ = a⁻¹ * (a * b ^ k * a⁻¹) * a := by rw [← hk, hc k]
        _ = b ^ k := by group
    rw [this]
    exact Subgroup.zpow_mem_zpowers b k

theorem exists_dihedral (h : NineSixSetting hC T S U) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    {g : G} (hgc : Commute (g * z * g⁻¹) z)
    (hgT : g * z * g⁻¹ ∉
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    ∃ D₀ : Subgroup G, D₀ ≤ commutator G ∧ D₀ ≤ Subgroup.normalizer ((S : Set G) ∩ D) ∧
      Nat.card D₀ = 8 ∧
        (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ D₀ = ⊥ := by
  classical
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  have hcent : Subgroup.centralizer (U : Set G) = TG := h.centralizer_eq_sylow_map
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hUT : ∀ v ∈ U, v ∈ TG := fun v hv => by
    rw [hTG, h.sylow_map_eq_sup]; exact Subgroup.mem_sup_right hv
  have huT : hC.d ∈ TG := by
    rw [hTG, h.sylow_map_eq_sup]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hcU : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v := fun v hv w hw =>
    h.sylow_map_commute (hUT v hv) (hUT w hw)
  have hsqU : ∀ v ∈ U, v * v = 1 := fun v hv => h.sylow_map_mul_self (hUT v hv)
  have hmemΔ : ∀ x, x ∈ (S : Set G) ∩ D ↔ ∃ v ∈ U, hC.d * v = x := fun x => by
    rw [h.delta.sylow_inter]; simp only [Set.mem_image, SetLike.mem_coe]
  have hΔΔ : ∀ δ₁ ∈ (S : Set G) ∩ D, ∀ δ₂ ∈ (S : Set G) ∩ D, δ₁ * δ₂ ∈ U := by
    intro δ₁ h₁ δ₂ h₂
    obtain ⟨v₁, hv₁, rfl⟩ := (hmemΔ δ₁).mp h₁
    obtain ⟨v₂, hv₂, rfl⟩ := (hmemΔ δ₂).mp h₂
    have hc := h.sylow_map_commute huT (hUT v₁ hv₁)
    rw [show hC.d * v₁ * (hC.d * v₂) = (hC.d * hC.d) * (v₁ * v₂) by
      rw [mul_assoc, ← mul_assoc v₁, ← hc.eq]; group, hu2, one_mul]
    exact U.mul_mem hv₁ hv₂
  have hCN : ∀ w ∈ U, w ≠ 1 → ∀ c : G, c * w = w * c →
      c ∈ Subgroup.normalizer ((S : Set G) ∩ D) := by
    intro w hw hw1 c hc
    have hcw : c * w * c⁻¹ = w := by rw [hc, mul_inv_cancel_right]
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    rw [h.mem_inter_iff_commute hw hw1, h.mem_inter_iff_commute hw hw1]
    have hD : x ∈ D ↔ c * x * c⁻¹ ∈ D := ⟨hC.setup.conj_mem c, fun hx => by
      simpa [mul_assoc] using hC.setup.conj_mem c⁻¹ hx⟩
    rw [hD]
    refine and_congr_right fun _ => ?_
    conv_rhs => rw [← hcw]
    exact (Commute.conj_iff c).symm
  have hNU : ∀ n ∈ Subgroup.normalizer ((S : Set G) ∩ D), ∀ v ∈ U, n * v * n⁻¹ ∈ U := by
    intro n hn v hv
    have hu : hC.d ∈ (S : Set G) ∩ D := (hmemΔ _).mpr ⟨1, U.one_mem, mul_one _⟩
    have huv : hC.d * v ∈ (S : Set G) ∩ D := (hmemΔ _).mpr ⟨v, hv, rfl⟩
    have := hΔΔ _ ((Subgroup.mem_set_normalizer_iff.mp hn _).mp hu) _
      ((Subgroup.mem_set_normalizer_iff.mp hn _).mp huv)
    rwa [show n * hC.d * n⁻¹ * (n * (hC.d * v) * n⁻¹) = n * (hC.d * hC.d * v) * n⁻¹ by group,
      hu2, one_mul] at this
  have hz2 : z * z = 1 := hsqU z hzU
  have heU : g * z * g⁻¹ ∉ U := fun h' => hgT (hUT _ h')
  have heN : g * z * g⁻¹ ∈ Subgroup.normalizer ((S : Set G) ∩ D) := hCN z hzU hz1 _ hgc.eq
  have he2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz2]; group
  set E := U.map (MulAut.conj g).toMonoidHom with hE
  have hmemE : ∀ y, y ∈ E ↔ g⁻¹ * y * g ∈ U := fun y => by
    rw [hE, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
    · intro hy
      exact ⟨_, hy, by simp [mul_assoc]⟩
  have hconjE : ∀ w ∈ U, g * w * g⁻¹ ∈ E := fun w hw => (hmemE _).mpr (by simpa [mul_assoc])
  have hcE : ∀ v ∈ E, ∀ w ∈ E, v * w = w * v := fun v hv w hw => by
    have := hcU _ ((hmemE v).mp hv) _ ((hmemE w).mp hw)
    calc v * w = g * (g⁻¹ * v * g * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = w * v := by rw [this]; group
  have hsqE : ∀ v ∈ E, v * v = 1 := fun v hv => by
    have := hsqU _ ((hmemE v).mp hv)
    calc v * v = g * (g⁻¹ * v * g * (g⁻¹ * v * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hE8 : Nat.card E = 8 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card]
  have hET : ∀ k ∈ E, k ∈ TG → k = 1 := fun k hk hkT => by
    have h1 := DeltaSetup.eq_one_of_conj_mem_sylow_map h.hyp h.three h.five h.delta hzU heU
      ((hmemE k).mp hk) (by rw [show g * (g⁻¹ * k * g) * g⁻¹ = k by group]; exact hkT)
    calc k = g * (g⁻¹ * k * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hz' : ∃ z' ∈ U, g⁻¹ * z' * g⁻¹⁻¹ ∉ U := by
    by_contra hcon
    push Not at hcon
    have hle : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ U := by
      rintro _ ⟨w, hw, rfl⟩
      exact hcon w hw
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])
    obtain ⟨w, hw, hwz⟩ : z ∈ U.map (MulAut.conj g⁻¹).toMonoidHom := by rw [heq]; exact hzU
    apply heU
    have : g * z * g⁻¹ = w := by rw [← hwz]; simp [mul_assoc]
    rw [this]
    exact hw
  obtain ⟨z', hz'U, hz'⟩ := hz'
  have hUTE : ∀ w ∈ U, g⁻¹ * w * g ∈ TG → w = 1 := fun w hw hwT =>
    DeltaSetup.eq_one_of_conj_mem_sylow_map h.hyp h.three h.five h.delta hz'U hz' hw
      (by rw [inv_inv]; exact hwT)
  have hCNE : ∀ c : G, c * (g * z * g⁻¹) = g * z * g⁻¹ * c → ∀ v ∈ E, c * v * c⁻¹ ∈ E := by
    intro c hc v hv
    have hc' : g⁻¹ * c * g * z = z * (g⁻¹ * c * g) := by
      calc g⁻¹ * c * g * z = g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹ * c) * g := by rw [hc]
        _ = z * (g⁻¹ * c * g) := by group
    have := hNU _ (hCN z hzU hz1 _ hc') _ ((hmemE v).mp hv)
    rw [hmemE]
    simpa [mul_assoc] using this
  set A := E ⊓ Subgroup.centralizer ({z} : Set G) with hA
  set B := U ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G) with hB
  have hmemA : ∀ a, a ∈ A ↔ a ∈ E ∧ a * z = z * a := fun a => by
    rw [hA, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hmemB : ∀ b, b ∈ B ↔ b ∈ U ∧ b * (g * z * g⁻¹) = g * z * g⁻¹ * b := fun b => by
    rw [hB, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hA4 : Nat.card A = 4 := by
    refine card_inf_centralizer_eq_four hcE hsqE hE8 (hCNE z hgc.eq.symm) hz2 ?_
    by_contra hcon
    push Not at hcon
    have hmem : g⁻¹ * z * g ∈ TG := by
      rw [← hcent, Subgroup.mem_centralizer_iff]
      intro w hw
      have := hcon _ (hconjE w hw)
      calc w * (g⁻¹ * z * g) = g⁻¹ * (g * w * g⁻¹ * z) * g := by group
        _ = g⁻¹ * (z * (g * w * g⁻¹) * z⁻¹ * z) * g := by rw [this]
        _ = g⁻¹ * z * g * w := by group
    exact hz1 (hUTE z hzU hmem)
  have hB4 : Nat.card B = 4 := by
    refine card_inf_centralizer_eq_four hcU hsqU h.card (hNU _ heN) he2 ?_
    by_contra hcon
    push Not at hcon
    apply hgT
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro w hw
    have := hcon w hw
    calc w * (g * z * g⁻¹) = g * z * g⁻¹ * w * (g * z * g⁻¹)⁻¹ * (g * z * g⁻¹) := by rw [this]
      _ = g * z * g⁻¹ * w := by group
  have hzB : z ∈ B := (hmemB z).mpr ⟨hzU, hgc.eq.symm⟩
  have heA : g * z * g⁻¹ ∈ A := (hmemA _).mpr ⟨hconjE z hzU, hgc.eq⟩
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer ((S : Set G) ∩ D) := fun a ha =>
    hCN z hzU hz1 a ((hmemA a).mp ha).2
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨haE, haz⟩ := (hmemA a).mp ha
    obtain ⟨hbU, hbe⟩ := (hmemB b).mp hb
    have hae := hcE a haE _ ((hmemA _).mp heA).1
    have h1 : a * b * a⁻¹ ∈ B := (hmemB _).mpr ⟨hNU a (hAN a ha) b hbU, by
      generalize g * z * g⁻¹ = ev at hae hbe ⊢
      have hae' : a⁻¹ * ev = ev * a⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hae, mul_inv_cancel_right]
      calc a * b * a⁻¹ * ev = a * b * (a⁻¹ * ev) := by group
        _ = a * (b * ev) * a⁻¹ := by rw [hae']; group
        _ = a * ev * b * a⁻¹ := by rw [hbe]; group
        _ = ev * (a * b * a⁻¹) := by rw [hae]; group⟩
    have h2 : b * a⁻¹ * b⁻¹ ∈ A := (hmemA _).mpr ⟨hCNE b hbe _ (E.inv_mem haE), by
      have hbz := hcU b hbU z hzU
      have haz' : a⁻¹ * z = z * a⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, haz, mul_inv_cancel_right]
      have hbz' : b⁻¹ * z = z * b⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hbz, mul_inv_cancel_right]
      calc b * a⁻¹ * b⁻¹ * z = b * a⁻¹ * (b⁻¹ * z) := by group
        _ = b * (a⁻¹ * z) * b⁻¹ := by rw [hbz']; group
        _ = b * z * a⁻¹ * b⁻¹ := by rw [haz']; group
        _ = z * (b * a⁻¹ * b⁻¹) := by rw [hbz]; group⟩
    have hk : a * b * a⁻¹ * b⁻¹ = 1 := hET _ (by
      rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact E.mul_mem haE ((hmemA _).mp h2).1)
      (hUT _ ((hmemB _).mp (B.mul_mem h1 (B.inv_mem hb))).1)
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hk, one_mul]
  have hord2 : ∀ w : G, w ≠ 1 → w * w = 1 → Nat.card (Subgroup.zpowers w) = 2 := fun w hw1 hw2 => by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hgen : ∀ m : G, ∀ y ∈ U, y ∉ B → (∀ v ∈ B, m * v = v * m) → m * y = y * m → m ∈ TG := by
    intro m y hyU hyB hmB hmy
    have hUeq := sup_zpowers_eq (inf_le_left : B ≤ U) (by rw [h.card, hB4]) hyU hyB
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro w hw
    have hle : B ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({m} : Set G) := sup_le
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hmB v hv).symm)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hmy.symm))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (by rw [hUeq]; exact hw))
  obtain ⟨y, hyU, hyB⟩ : ∃ y ∈ U, y ∉ B := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun v hv => hcon v hv : U ≤ B)
    rw [h.card, hB4] at this
    omega
  have hex : ∀ c ∈ B, c ≠ 1 → ∃ d ∈ B, d ∉ Subgroup.zpowers c := fun c hc hc1 => by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun v hv => hcon v hv : B ≤ Subgroup.zpowers c)
    rw [hB4, hord2 c hc1 (hsqU c ((hmemB c).mp hc).1)] at this
    omega
  obtain ⟨x, hxB, hxz⟩ := hex z hzB hz1
  have hxU := ((hmemB x).mp hxB).1
  have hBeq : Subgroup.zpowers z ⊔ Subgroup.zpowers x = B :=
    sup_zpowers_eq (Subgroup.zpowers_le.mpr hzB) (by rw [hB4, hord2 z hz1 hz2]) hxB hxz
  have hcenB : ∀ m : G, m * z = z * m → m * x = x * m → ∀ v ∈ B, m * v = v * m := by
    intro m hmz hmx v hv
    have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({m} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hmz.symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hmx.symm))
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (by rw [hBeq]; exact hv))).symm
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro m
    have hfix : m ∈ U → y * m * y⁻¹ = m := fun hm => by rw [hcU y hyU m hm, mul_inv_cancel_right]
    refine ⟨fun hm => by rwa [hfix ((hmemB m).mp hm).1], fun hm => ?_⟩
    have hmU : m ∈ U := by
      have := U.mul_mem (U.mul_mem (U.inv_mem hyU) ((hmemB _).mp hm).1) hyU
      rwa [show y⁻¹ * (y * m * y⁻¹) * y = m by group] at this
    rwa [hfix hmU] at hm
  have hcos : ∀ w ∈ U, w ∉ B → y⁻¹ * w ∈ B := by
    intro w hw hwB
    have hUeq : Subgroup.zpowers y ⊔ B = U := by
      rw [sup_comm]; exact sup_zpowers_eq inf_le_left (by rw [h.card, hB4]) hyU hyB
    obtain ⟨k, hk, b₀, hb₀, rfl⟩ := exists_mul_eq_of_mem_sup hyN (by rw [hUeq]; exact hw)
    rcases eq_one_or_eq_of_mem_zpowers (hsqU y hyU) hk with rfl | rfl
    · rw [one_mul] at hwB; exact absurd hb₀ hwB
    · rwa [inv_mul_cancel_left]
  have hf : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ B := by
    intro a ha
    refine hcos _ (hNU a (hAN a ha) y hyU) fun hwB => hyB ?_
    have hc := hAB a ha _ hwB
    have h3 : a⁻¹ * (a * y * a⁻¹) * a = a * y * a⁻¹ := by
      rw [show a⁻¹ * (a * y * a⁻¹) * a = a⁻¹ * (a * y * a⁻¹ * a) by group, ← hc,
        inv_mul_cancel_left]
    rw [show y = a⁻¹ * (a * y * a⁻¹) * a by group, h3]
    exact hwB
  have hCT : ∀ a ∈ A, a ≠ 1 → ∀ w ∈ TG, a * w = w * a → w ∈ B := by
    intro a ha ha1 w hwT haw
    have haE := ((hmemA a).mp ha).1
    rcases h.mem_or_mul_mem hwT with hwU | hwU
    · by_contra hwB
      exact ha1 (hET a haE (hgen a w hwU hwB (hAB a ha) haw))
    exfalso
    have ha0 : g⁻¹ * a * g ≠ 1 := fun h0 => ha1 (by
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = 1 := by rw [h0]; group)
    have hpt : ∀ δ ∈ (S : Set G) ∩ D, a * δ = δ * a → g⁻¹ * δ * g ∈ (S : Set G) ∩ D := by
      intro δ hδ hc
      rw [h.mem_inter_iff_commute ((hmemE a).mp haE) ha0]
      refine ⟨by simpa using hC.setup.conj_mem g⁻¹ hδ.2, ?_⟩
      have := (Commute.conj_iff g⁻¹ (a := δ) (b := a)).mpr hc.symm
      simpa using this
    have hw2 : w * w = 1 := h.sylow_map_mul_self hwT
    have hwΔ : w ∈ (S : Set G) ∩ D := (hmemΔ w).mpr ⟨_, hwU, by rw [← mul_assoc, hu2, one_mul]⟩
    have hwzΔ : w * z ∈ (S : Set G) ∩ D := (hmemΔ _).mpr ⟨_, U.mul_mem hwU hzU, by
      rw [← mul_assoc, ← mul_assoc, hu2, one_mul]⟩
    have haz := hAB a ha z hzB
    have hprod := hΔΔ _ (hpt w hwΔ haw) _ (hpt _ hwzΔ (by
      rw [← mul_assoc, haw, mul_assoc, haz, mul_assoc]))
    rw [show g⁻¹ * w * g * (g⁻¹ * (w * z) * g) = g⁻¹ * (w * w) * z * g by group, hw2,
      mul_one] at hprod
    exact hz1 (hET z ((hmemE z).mpr hprod) (hUT z hzU))
  let F : A → B := fun a => ⟨y⁻¹ * ((a : G) * y * (a : G)⁻¹), hf a a.2⟩
  have hFinj : Function.Injective F := by
    intro a₁ a₂ h12
    have h12 : (a₁ : G) * y * (a₁ : G)⁻¹ = a₂ * y * (a₂ : G)⁻¹ := by
      simpa [F] using congrArg Subtype.val h12
    have hm : (a₂ : G)⁻¹ * a₁ ∈ A := A.mul_mem (A.inv_mem a₂.2) a₁.2
    have hmy : (a₂ : G)⁻¹ * a₁ * y = y * ((a₂ : G)⁻¹ * a₁) := by
      calc (a₂ : G)⁻¹ * a₁ * y = (a₂ : G)⁻¹ * (a₁ * y * (a₁ : G)⁻¹) * a₁ := by group
        _ = (a₂ : G)⁻¹ * (a₂ * y * (a₂ : G)⁻¹) * a₁ := by rw [h12]
        _ = y * ((a₂ : G)⁻¹ * a₁) := by group
    have := hET _ ((hmemA _).mp hm).1 (hgen _ y hyU hyB (hAB _ hm) hmy)
    rw [inv_mul_eq_one] at this
    exact Subtype.ext this.symm
  have hFbij := hFinj.bijective_of_nat_card_le (by rw [hA4, hB4])
  obtain ⟨⟨a, ha⟩, haF⟩ := hFbij.2 ⟨z, hzB⟩
  obtain ⟨⟨b, hb⟩, hbF⟩ := hFbij.2 ⟨x, hxB⟩
  have hay : a * y * a⁻¹ = y * z := by
    have := congrArg Subtype.val haF
    simp only [F] at this
    rw [← this, mul_inv_cancel_left]
  have hby : b * y * b⁻¹ = y * x := by
    have := congrArg Subtype.val hbF
    simp only [F] at this
    rw [← this, mul_inv_cancel_left]
  have hx1 : x ≠ 1 := fun h1 => hxz (h1 ▸ Subgroup.one_mem _)
  have ha1 : a ≠ 1 := by rintro rfl; apply hz1; simpa using hay
  have hb1 : b ≠ 1 := by rintro rfl; apply hx1; simpa using hby
  have hab : a ≠ b := by
    rintro rfl
    exact hxz (by rw [hay, mul_right_inj] at hby; rw [← hby]; exact Subgroup.mem_zpowers z)
  have hcB := hf _ heA
  set c := y⁻¹ * (g * z * g⁻¹ * y * (g * z * g⁻¹)⁻¹) with hcdef
  have hey : g * z * g⁻¹ * y * (g * z * g⁻¹)⁻¹ = y * c := by rw [hcdef, mul_inv_cancel_left]
  have hc1 : c ≠ 1 := fun hc1 => hgT (hgen _ y hyU hyB (fun v hv => ((hmemB v).mp hv).2.symm) (by
    rw [hc1, mul_one] at hey
    rw [← inv_mul_cancel_right (g * z * g⁻¹ * y) (g * z * g⁻¹), hey]))
  obtain ⟨d, hdB, hdc⟩ := hex c hcB hc1
  have hcU := ((hmemB c).mp hcB).1
  have hdU := ((hmemB d).mp hdB).1
  have := h.delta.isElementaryAbelian
  have hy1 : y ≠ 1 := fun h1 => hyB (h1 ▸ B.one_mem)
  have hval : ∀ {p q : G} {hp : p ∈ U} {hq : q ∈ U}, p ≠ q → (⟨p, hp⟩ : U) ≠ ⟨q, hq⟩ :=
    fun hpq h' => hpq (congrArg Subtype.val h')
  have n1 : c ≠ y := fun h' => hyB (h' ▸ hcB)
  have n2 : d ≠ 1 := fun h' => hdc (h' ▸ Subgroup.one_mem _)
  have n3 : d ≠ y := fun h' => hyB (h' ▸ hdB)
  have n4 : d ≠ c := fun h' => hdc (h' ▸ Subgroup.mem_zpowers c)
  have n5 : d ≠ y * c := fun h' => hyB (by
    have := B.mul_mem (h' ▸ hdB) (B.inv_mem hcB); rwa [mul_inv_cancel_right] at this)
  have hbx : ProperTwoGeneratedCore.ExceptionalEight.Independent
      (![⟨y, hyU⟩, ⟨c, hcU⟩, ⟨d, hdU⟩] : Fin 3 → U) :=
    ProperTwoGeneratedCore.ExceptionalEight.independent_of_ne (hval hy1) (hval hc1) (hval n1)
      (hval n2) (hval n3) (hval n4) (hval n5)
  have hzxB : z * x ∈ B := B.mul_mem hzB hxB
  have m1 : z * x ≠ 1 := fun h' => hxz (by
    rw [eq_inv_of_mul_eq_one_right h']; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z))
  have m2 : z * x ≠ z := fun h' => hx1 (mul_eq_left.mp h')
  have m3 : y ≠ z := fun h' => hyB (h' ▸ hzB)
  have m4 : y ≠ z * x := fun h' => hyB (h' ▸ hzxB)
  have m5 : y ≠ z * (z * x) := fun h' => hyB (by rw [h', ← mul_assoc, hz2, one_mul]; exact hxB)
  have hby' : ProperTwoGeneratedCore.ExceptionalEight.Independent
      (![⟨z, hzU⟩, ⟨z * x, U.mul_mem hzU hxU⟩, ⟨y, hyU⟩] : Fin 3 → U) :=
    ProperTwoGeneratedCore.ExceptionalEight.independent_of_ne (hval hz1) (hval m1) (hval m2)
      (hval hy1) (hval m3) (hval m4) (hval m5)
  obtain ⟨k, hkN, hk⟩ := h.exists_mem_normalizer_conj_eq
    (ProperTwoGeneratedCore.ExceptionalEight.basisAut hbx hby' h.card)
  have hky : k * y * k⁻¹ = z := (hk ⟨y, hyU⟩).trans (congrArg Subtype.val
    (ProperTwoGeneratedCore.ExceptionalEight.basisAut_apply hbx hby' h.card 0))
  have hkc : k * c * k⁻¹ = z * x := (hk ⟨c, hcU⟩).trans (congrArg Subtype.val
    (ProperTwoGeneratedCore.ExceptionalEight.basisAut_apply hbx hby' h.card 1))
  have hkd : k * d * k⁻¹ = y := (hk ⟨d, hdU⟩).trans (congrArg Subtype.val
    (ProperTwoGeneratedCore.ExceptionalEight.basisAut_apply hbx hby' h.card 2))
  set t := k * (g * z * g⁻¹) * k⁻¹ with htdef
  have ht2 : t * t = 1 := by
    rw [htdef, show k * (g * z * g⁻¹) * k⁻¹ * (k * (g * z * g⁻¹) * k⁻¹) =
      k * (g * z * g⁻¹ * (g * z * g⁻¹)) * k⁻¹ by group, he2]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hed : g * z * g⁻¹ * d * (g * z * g⁻¹)⁻¹ = d := by
    rw [← ((hmemB d).mp hdB).2, mul_inv_cancel_right]
  have htz : t * z * t⁻¹ = x := by
    calc t * z * t⁻¹ = k * (g * z * g⁻¹ * (k⁻¹ * z * k) * (g * z * g⁻¹)⁻¹) * k⁻¹ := by
          rw [htdef]; group
      _ = k * y * k⁻¹ * (k * c * k⁻¹) := by
          rw [show k⁻¹ * z * k = y by rw [← hky]; group, hey]; group
      _ = x := by rw [hky, hkc, ← mul_assoc, hz2, one_mul]
  have hty : t * y * t⁻¹ = y := by
    calc t * y * t⁻¹ = k * (g * z * g⁻¹ * (k⁻¹ * y * k) * (g * z * g⁻¹)⁻¹) * k⁻¹ := by
          rw [htdef]; group
      _ = y := by rw [show k⁻¹ * y * k = d by rw [← hkd]; group, hed, hkd]
  have htx : t * x * t⁻¹ = z := by
    rw [← htz, show t * (t * z * t⁻¹) * t⁻¹ = t * t * z * (t * t)⁻¹ by group, ht2]; group
  have hti : ∀ w, t⁻¹ * w * t = t * w * t⁻¹ := fun w => by rw [htinv]
  have haA := (hmemA a).mp ha
  have hbA := (hmemA b).mp hb
  have haz := hAB a ha z hzB
  have hax := hAB a ha x hxB
  have hbz := hAB b hb z hzB
  have hbx2 := hAB b hb x hxB
  set b' := t * a * t⁻¹ with hb'def
  have hconj : ∀ w, b' * w * b'⁻¹ = t * (a * (t⁻¹ * w * t) * a⁻¹) * t⁻¹ := fun w => by
    rw [hb'def]; group
  have hfix : ∀ p w : G, p * w = w * p → p * w * p⁻¹ = w := fun p w hw => by
    rw [hw, mul_inv_cancel_right]
  have hb'z : b' * z * b'⁻¹ = z := by rw [hconj, hti, htz, hfix a x hax, htx]
  have hb'x : b' * x * b'⁻¹ = x := by rw [hconj, hti, htx, hfix a z haz, htz]
  have hb'y : b' * y * b'⁻¹ = y * x := by
    rw [hconj, hti, hty, hay, show t * (y * z) * t⁻¹ = t * y * t⁻¹ * (t * z * t⁻¹) by group,
      hty, htz]
  have hcomm_of : ∀ w, b' * w * b'⁻¹ = b * w * b⁻¹ → b⁻¹ * b' * w = w * (b⁻¹ * b') :=
    fun w hw => by
      calc b⁻¹ * b' * w = b⁻¹ * (b' * w * b'⁻¹) * b' := by group
        _ = b⁻¹ * (b * w * b⁻¹) * b' := by rw [hw]
        _ = w * (b⁻¹ * b') := by group
  have hmz := hcomm_of z (by rw [hb'z, hfix b z hbz])
  have hmx := hcomm_of x (by rw [hb'x, hfix b x hbx2])
  have hmy := hcomm_of y (by rw [hb'y, hby])
  have hvT : b⁻¹ * b' ∈ TG := hgen _ y hyU hyB (hcenB _ hmz hmx) hmy
  have hb2 : b * b = 1 := hsqE b hbA.1
  have ha2 : a * a = 1 := hsqE a haA.1
  have hb'2 : b' * b' = 1 := by
    rw [hb'def, show t * a * t⁻¹ * (t * a * t⁻¹) = t * (a * a) * t⁻¹ by group, ha2]; group
  have hv2 : b⁻¹ * b' * (b⁻¹ * b') = 1 := h.sylow_map_mul_self hvT
  have hbv : b * (b⁻¹ * b') = b⁻¹ * b' * b := by
    have h1 : b * (b⁻¹ * b') * (b * (b⁻¹ * b')) = 1 := by rw [mul_inv_cancel_left]; exact hb'2
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hv2,
      inv_eq_of_mul_eq_one_right hb2]
  have hvB : b⁻¹ * b' ∈ B := hCT b hb hb1 _ hvT hbv
  have hab' : a * b' = b' * a := by
    calc a * b' = a * b * (b⁻¹ * b') := by group
      _ = b * (a * (b⁻¹ * b')) := by rw [hcE a haA.1 b hbA.1, mul_assoc]
      _ = b' * a := by rw [hAB a ha _ hvB]; group
  have hab'ne : a ≠ b' := fun he' => hab (by
    have := hET (b⁻¹ * a) (E.mul_mem (E.inv_mem hbA.1) haA.1) (by rw [he']; exact hvT)
    rw [inv_mul_eq_one] at this; exact this.symm)
  have hb'1 : b' ≠ 1 := fun h1 => ha1 (by
    calc a = t⁻¹ * b' * t := by rw [hb'def]; group
      _ = 1 := by rw [h1]; group)
  set V := Subgroup.zpowers a ⊔ Subgroup.zpowers b' with hV
  have hinfV : Subgroup.zpowers a ⊓ Subgroup.zpowers b' = ⊥ := by
    rw [eq_bot_iff]
    rintro m ⟨hm1, hm2⟩
    rcases eq_one_or_eq_of_mem_zpowers ha2 hm1 with rfl | rfl
    · exact Subgroup.one_mem _
    · rcases eq_one_or_eq_of_mem_zpowers hb'2 hm2 with h' | h'
      · exact absurd h' ha1
      · exact absurd h' hab'ne
  have hVcard : Nat.card V = 4 := by
    rw [hV, card_sup_of_le_normalizer (zpowers_le_normalizer_of_commute hab') hinfV,
      hord2 a ha1 ha2, hord2 b' hb'1 hb'2]
  have hVz : V ≤ Subgroup.centralizer ({z} : Set G) := sup_le
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr haz))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc b' * z = b' * z * b'⁻¹ * b' := by group
        _ = z * b' := by rw [hb'z])))
  have htb' : t * b' * t⁻¹ = a := by
    rw [hb'def, show t * (t * a * t⁻¹) * t⁻¹ = t * t * a * (t * t)⁻¹ by group, ht2]; group
  have hfwd : ∀ m ∈ V, t * m * t⁻¹ ∈ V := by
    intro m hm
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ :=
      exists_mul_eq_of_mem_sup (zpowers_le_normalizer_of_commute hab') hm
    rw [show t * (k₁ * k₂) * t⁻¹ = t * k₁ * t⁻¹ * (t * k₂ * t⁻¹) by group]
    refine V.mul_mem ?_ ?_
    · rcases eq_one_or_eq_of_mem_zpowers ha2 hk₁ with rfl | rfl
      · rw [mul_one, mul_inv_cancel]; exact V.one_mem
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rcases eq_one_or_eq_of_mem_zpowers hb'2 hk₂ with rfl | rfl
      · rw [mul_one, mul_inv_cancel]; exact V.one_mem
      · rw [htb']; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have htV : Subgroup.zpowers t ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨hfwd m, fun hm => ?_⟩
    have := hfwd _ hm
    rwa [show t * (t * m * t⁻¹) * t⁻¹ = t * t * m * (t * t)⁻¹ by group, ht2, one_mul, inv_one,
      mul_one] at this
  have htnz : t * z ≠ z * t := fun h' => hxz (by
    rw [← htz, h', mul_inv_cancel_right]; exact Subgroup.mem_zpowers z)
  have hinfD : Subgroup.zpowers t ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro m ⟨hm1, hm2⟩
    rcases eq_one_or_eq_of_mem_zpowers ht2 hm1 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd (Subgroup.mem_centralizer_singleton_iff.mp (hVz hm2)) htnz
  have hKn : (commutator G).Normal := inferInstance
  have ha' : a ∈ commutator G := by
    have := hKn.conj_mem _ (h.le_commutator ((hmemE a).mp haA.1)) g
    rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at this
  have htN : t ∈ Subgroup.normalizer ((S : Set G) ∩ D) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN heN) (Subgroup.inv_mem _ hkN)
  refine ⟨Subgroup.zpowers t ⊔ V, ?_, ?_, ?_, ?_⟩
  · have ht' : t ∈ commutator G :=
      hKn.conj_mem _ (hKn.conj_mem _ (h.le_commutator hzU) g) k
    exact sup_le (Subgroup.zpowers_le.mpr ht') (sup_le (Subgroup.zpowers_le.mpr ha')
      (Subgroup.zpowers_le.mpr (hKn.conj_mem _ ha' t)))
  · exact sup_le (Subgroup.zpowers_le.mpr htN) (sup_le (Subgroup.zpowers_le.mpr (hAN a ha))
      (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mul_mem _ htN (hAN a ha))
        (Subgroup.inv_mem _ htN))))
  · rw [card_sup_of_le_normalizer htV hinfD, hord2 t (fun h1 => htnz (by rw [h1, one_mul,
      mul_one])) ht2, hVcard]
  · rw [eq_bot_iff]
    rintro m ⟨hmT, hmD⟩
    obtain ⟨k₀, hk₀, w, hw, rfl⟩ := exists_mul_eq_of_mem_sup htV hmD
    have hmz : z * (k₀ * w) = k₀ * w * z :=
      Subgroup.mem_centralizer_iff.mp (by rw [hcent]; exact hmT) z hzU
    have hwz := Subgroup.mem_centralizer_singleton_iff.mp (hVz hw)
    rcases eq_one_or_eq_of_mem_zpowers ht2 hk₀ with rfl | rfl
    · obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ :=
        exists_mul_eq_of_mem_sup (zpowers_le_normalizer_of_commute hab') hw
      rcases eq_one_or_eq_of_mem_zpowers ha2 hk₁ with rfl | rfl <;>
        rcases eq_one_or_eq_of_mem_zpowers hb'2 hk₂ with rfl | rfl <;>
        simp only [one_mul, mul_one] at hmT ⊢
      · exact Subgroup.one_mem _
      · exact absurd (hET b hbA.1 (by
          rw [show b = b' * (b⁻¹ * b')⁻¹ by group]; exact TG.mul_mem hmT (TG.inv_mem hvT))) hb1
      · exact absurd (hET k₁ haA.1 hmT) ha1
      · have h1 := hET (k₁ * b) (E.mul_mem haA.1 hbA.1) (by
          rw [show k₁ * b = k₁ * b' * (b⁻¹ * b')⁻¹ by group]
          exact TG.mul_mem hmT (TG.inv_mem hvT))
        exact absurd (by rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hb2]) hab
    · exfalso
      apply htnz
      calc t * z = t * (z * w) * w⁻¹ := by group
        _ = t * w * z * w⁻¹ := by rw [← hwz]; group
        _ = z * (t * w) * w⁻¹ := by rw [← hmz]
        _ = z * t := by group

end NineSixSetting

end CFSG.OddTranspositions.PartThree.Nine
