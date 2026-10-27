module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GNotIii
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129G

variable {X : Type} [Group X] [Finite X]

theorem isElemAbelian_zpowers_sup {F : Subgroup X} (hF : CFSG.Assembly.IsElemAbelian 3 F)
    {g : X} (hg3 : g ^ 3 = 1) (hgF : ∀ f ∈ F, g * f = f * g) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers g ⊔ F) := by
  have hdec : ∀ e ∈ Subgroup.zpowers g ⊔ F, ∃ k : ℤ, ∃ f ∈ F, e = g ^ k * f :=
    exists_zpow_mul_of_mem_sup_zpowers_sup rfl hgF
  have hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := fun f hf f' hf' =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨f, hf⟩ ⟨f', hf'⟩)
  have hcg : ∀ f ∈ F, ∀ n : ℤ, f * g ^ n = g ^ n * f := fun f hf n =>
    (Commute.zpow_right (show Commute f g from (hgF f hf).symm) n).eq
  have hg3' : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg3
  refine ⟨⟨⟨fun s t => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
  · obtain ⟨k, f, hf, hs⟩ := hdec s s.2
    obtain ⟨l, f', hf', ht⟩ := hdec t t.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs, ht]
    have e1 : g ^ k * f * (g ^ l * f') = g ^ (k + l) * (f * f') := by
      rw [zpow_add]
      calc g ^ k * f * (g ^ l * f') = g ^ k * (f * g ^ l) * f' := by group
        _ = g ^ k * (g ^ l * f) * f' := by rw [hcg f hf l]
        _ = g ^ k * g ^ l * (f * f') := by group
    have e2 : g ^ l * f' * (g ^ k * f) = g ^ (l + k) * (f' * f) := by
      rw [zpow_add]
      calc g ^ l * f' * (g ^ k * f) = g ^ l * (f' * g ^ k) * f := by group
        _ = g ^ l * (g ^ k * f') * f := by rw [hcg f' hf' k]
        _ = g ^ l * g ^ k * (f' * f) := by group
    rw [e1, e2, add_comm k l, hFc f hf f' hf']
  · obtain ⟨k, f, hf, rfl⟩ := hdec e he
    have hc : Commute (g ^ k) f := (hcg f hf k).symm
    have hk3 : (g ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      have h3 : g ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hg3
      rw [h3, one_zpow]
    rw [hc.mul_pow, hk3, hF.2 f hf, one_mul]

theorem card_zpowers_sup_of_not_mem {F : Subgroup X} {g : X} (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (hgF : g ∉ F) (hcomm : ∀ f ∈ F, g * f = f * g) :
    Nat.card (Subgroup.zpowers g ⊔ F : Subgroup X) = 3 * Nat.card F := by
  have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers g) F (fun u hu v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left (show Commute g v from hcomm v hv) k).eq)
  have hinf : Subgroup.zpowers g ⊓ F = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers g ⊓ F : Subgroup X) ∣ 3 := by
      rw [← hgo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hgF
      have heq : Subgroup.zpowers g ⊓ F = Subgroup.zpowers g :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hgo])
      have : g ∈ Subgroup.zpowers g ⊓ F := by
        rw [heq]; exact Subgroup.mem_zpowers g
      exact this.2
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hgo] at hcard
  exact hcard

theorem isElemAbelian_bot : CFSG.Assembly.IsElemAbelian 3 (⊥ : Subgroup X) :=
  ⟨⟨⟨fun a b => Subtype.ext (by
    have ha : (a : X) = 1 := Subgroup.mem_bot.mp a.2
    have hb : (b : X) = 1 := Subgroup.mem_bot.mp b.2
    simp [ha, hb])⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩

theorem exists_R_F_u {X₀ : Type} [Group X₀] (ι₁ ι₂ : X₀ →* X) (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂) (hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a)
    (hZ : Nat.card (Subgroup.center X₀) = 3)
    {δ σ u z : X₀} (hzc : z ∈ Subgroup.center X₀) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hδ : δ ^ 3 = z) (hσ3 : σ ^ 3 = 1) (hσc : σ ∉ Subgroup.center X₀)
    (hσδ : ∀ k : ℤ, σ ≠ δ ^ k) (hσδc : σ * δ = δ * σ) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (huδ : u * δ = δ * u) {ζ₁ ζ₂ : X₀} (hζ₁ : ζ₁ ∈ Subgroup.center X₀)
    (hζ₂ : ζ₂ ∈ Subgroup.center X₀) (hζ₁1 : ζ₁ ≠ 1) (hζ : ι₁ ζ₁ = ι₂ ζ₂) :
    ∃ (R F : Subgroup X) (v : X), CFSG.Assembly.IsElemAbelian 3 R ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ F ≤ R ∧ F ≠ R ∧ Nat.card F = 27 ∧ v ^ 2 = 1 ∧ v ≠ 1 ∧
      ∀ f ∈ F, f * v = v * f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Subgroup.center X₀) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZz : Subgroup.zpowers z = Subgroup.center X₀ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc)
      (by rw [hZ, Nat.card_zpowers, hzo])
  obtain ⟨k₁, hk₁⟩ : ζ₁ ∈ Subgroup.zpowers z := by rw [hZz]; exact hζ₁
  obtain ⟨k₂, hk₂⟩ : ζ₂ ∈ Subgroup.zpowers z := by rw [hZz]; exact hζ₂
  have hk₁' : z ^ k₁ = ζ₁ := hk₁
  have hk₂' : z ^ k₂ = ζ₂ := hk₂
  have hzp : ∀ w ∈ Subgroup.center X₀, w ^ 3 = 1 := by
    intro w hw
    rw [← hZz] at hw
    obtain ⟨m, rfl⟩ := hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hζ₁3 : ζ₁ ^ 3 = 1 := hzp _ hζ₁
  have hζ₁o : orderOf ζ₁ = 3 := orderOf_eq_prime hζ₁3 hζ₁1
  have hZζ : Subgroup.zpowers ζ₁ = Subgroup.center X₀ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hζ₁)
      (by rw [hZ, Nat.card_zpowers, hζ₁o])
  have hINT : ∀ a b, ι₁ a = ι₂ b → ∃ m : ℤ, ι₁ a = ι₁ ζ₁ ^ m := by
    intro a b hab
    have hac : a ∈ Subgroup.center X₀ := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply h₁
      rw [map_mul, map_mul, hab, hcomm x b]
    rw [← hZζ] at hac
    obtain ⟨m, rfl⟩ := hac
    exact ⟨m, map_zpow ι₁ ζ₁ m⟩
  set ζ : X := ι₁ ζ₁ with hζdef
  set δ₁ : X := ι₁ (δ ^ k₁) with hδ₁
  set δ₂ : X := ι₂ (δ ^ k₂) with hδ₂
  set σ₁ : X := ι₁ σ with hσ₁
  set σ₂ : X := ι₂ σ with hσ₂
  set v : X := ι₁ u with hv
  have hcube : ∀ k : ℤ, (δ ^ k) ^ 3 = z ^ k := by
    intro k
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hδ]
  have hδ₁3 : δ₁ ^ 3 = ζ := by
    rw [hδ₁, ← map_pow, hcube, hk₁']
  have hδ₂3 : δ₂ ^ 3 = ζ := by
    rw [hδ₂, ← map_pow, hcube, hk₂']
    exact hζ.symm
  have hζ1 : ζ ≠ 1 := fun h => hζ₁1 (h₁ (by rw [← hζdef, h, map_one]))
  have hζ3 : ζ ^ 3 = 1 := by rw [hζdef, ← map_pow, hζ₁3, map_one]
  have hζ₁comm : ∀ x : X₀, Commute ζ (ι₁ x) := fun x => by
    rw [hζdef, Commute, SemiconjBy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hζ₁ x).symm]
  have hζ₂comm : ∀ x : X₀, Commute ζ (ι₂ x) := fun x => by
    rw [hζ, Commute, SemiconjBy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hζ₂ x).symm]
  set ε : X := δ₁ * δ₂⁻¹ with hε
  have hδ₁δ₂ : δ₁ * δ₂ = δ₂ * δ₁ := hcomm _ _
  have hε3 : ε ^ 3 = 1 := by
    have hc : Commute δ₁ δ₂⁻¹ := (Commute.inv_right (show Commute δ₁ δ₂ from hδ₁δ₂))
    rw [hε, hc.mul_pow, hδ₁3, inv_pow, hδ₂3, mul_inv_cancel]
  have hc12 : ∀ a b, Commute (ι₁ a) (ι₂ b) := fun a b => hcomm a b
  have hσδk : ∀ k : ℤ, σ * δ ^ k = δ ^ k * σ := fun k =>
    (Commute.zpow_right (show Commute σ δ from hσδc) k).eq
  have huδk : ∀ k : ℤ, u * δ ^ k = δ ^ k * u := fun k =>
    (Commute.zpow_right (show Commute u δ from huδ) k).eq
  have hσ₂δ₂ : Commute σ₂ δ₂ := by
    rw [hσ₂, hδ₂, Commute, SemiconjBy, ← map_mul, ← map_mul, hσδk]
  have hσ₁δ₁ : Commute σ₁ δ₁ := by
    rw [hσ₁, hδ₁, Commute, SemiconjBy, ← map_mul, ← map_mul, hσδk]
  have hvδ₁ : Commute v δ₁ := by
    rw [hv, hδ₁, Commute, SemiconjBy, ← map_mul, ← map_mul, huδk]
  have hσ₂ε : Commute σ₂ ε := by
    rw [hε]
    exact Commute.mul_right (hc12 (δ ^ k₁) σ).symm (hσ₂δ₂.inv_right)
  have hσ₁ε : Commute σ₁ ε := by
    rw [hε]
    exact Commute.mul_right hσ₁δ₁ ((hc12 σ (δ ^ k₂)).inv_right)
  have hvε : Commute v ε := by
    rw [hε]
    exact Commute.mul_right hvδ₁ ((hc12 u (δ ^ k₂)).inv_right)
  have hσ₁σ₂ : Commute σ₁ σ₂ := hc12 σ σ
  have hζσ₂ : Commute ζ σ₂ := hζ₂comm σ
  have hζσ₁ : Commute ζ σ₁ := hζ₁comm σ
  have hζv : Commute ζ v := hζ₁comm u
  have hvσ₂ : Commute v σ₂ := hc12 u σ
  have hζε : Commute ζ ε := by
    rw [hε]
    exact Commute.mul_right (hζ₁comm (δ ^ k₁)) ((hζ₂comm (δ ^ k₂)).inv_right)
  have hσ₂3 : σ₂ ^ 3 = 1 := by rw [hσ₂, ← map_pow, hσ3, map_one]
  have hσ₁3 : σ₁ ^ 3 = 1 := by rw [hσ₁, ← map_pow, hσ3, map_one]
  set F₁ : Subgroup X := Subgroup.zpowers ζ ⊔ ⊥ with hF₁
  set F₂ : Subgroup X := Subgroup.zpowers σ₂ ⊔ F₁ with hF₂
  set F₃ : Subgroup X := Subgroup.zpowers ε ⊔ F₂ with hF₃
  set R : Subgroup X := Subgroup.zpowers σ₁ ⊔ F₃ with hR
  have hcent : ∀ g : X, Commute g ζ → Commute g σ₂ → Commute g ε →
      F₃ ≤ Subgroup.centralizer {g} := by
    intro g h1 h2 h3
    refine sup_le ?_ (sup_le ?_ (sup_le ?_ bot_le))
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h3.symm)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h2.symm)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h1.symm)
  have hF₁mem : ∀ e ∈ F₁, ∃ a : ℤ, e = ζ ^ a := by
    intro e he
    rw [hF₁, sup_bot_eq] at he
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨a, rfl⟩
  have hcF₁ : ∀ g : X, Commute g ζ → ∀ f ∈ F₁, g * f = f * g := by
    intro g hg f hf
    obtain ⟨a, rfl⟩ := hF₁mem f hf
    exact (hg.zpow_right a).eq
  have hF₂dec : ∀ e ∈ F₂, ∃ b : ℤ, ∃ f ∈ F₁, e = σ₂ ^ b * f :=
    exists_zpow_mul_of_mem_sup_zpowers_sup hF₂ (hcF₁ σ₂ hζσ₂.symm)
  have hF₂mem : ∀ e ∈ F₂, ∃ b a : ℤ, e = σ₂ ^ b * ζ ^ a := by
    intro e he
    obtain ⟨b, f, hf, rfl⟩ := hF₂dec e he
    obtain ⟨a, rfl⟩ := hF₁mem f hf
    exact ⟨b, a, rfl⟩
  have hcF₂ : ∀ g : X, Commute g ζ → Commute g σ₂ → ∀ f ∈ F₂, g * f = f * g := by
    intro g h1 h2 f hf
    obtain ⟨b, a, rfl⟩ := hF₂mem f hf
    exact (h2.zpow_right b).mul_right (h1.zpow_right a) |>.eq
  have hF₃dec : ∀ e ∈ F₃, ∃ j : ℤ, ∃ f ∈ F₂, e = ε ^ j * f :=
    exists_zpow_mul_of_mem_sup_zpowers_sup hF₃ (hcF₂ ε hζε.symm hσ₂ε.symm)
  have hcF₃ : ∀ g : X, Commute g ζ → Commute g σ₂ → Commute g ε → ∀ f ∈ F₃, g * f = f * g := by
    intro g h1 h2 h3 f hf
    obtain ⟨j, f', hf', rfl⟩ := hF₃dec f hf
    obtain ⟨b, a, rfl⟩ := hF₂mem f' hf'
    exact ((h3.zpow_right j).mul_right ((h2.zpow_right b).mul_right (h1.zpow_right a))).eq
  have hpow3 : ∀ m : ℤ, (ζ ^ m) ^ 3 = 1 := by
    intro m
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ3, one_zpow]
  have hE₁ : CFSG.Assembly.IsElemAbelian 3 F₁ :=
    isElemAbelian_zpowers_sup isElemAbelian_bot hζ3 (fun f hf => by
      rw [Subgroup.mem_bot.mp hf, mul_one, one_mul])
  have hE₂ : CFSG.Assembly.IsElemAbelian 3 F₂ :=
    isElemAbelian_zpowers_sup hE₁ hσ₂3 (hcF₁ σ₂ hζσ₂.symm)
  have hE₃ : CFSG.Assembly.IsElemAbelian 3 F₃ :=
    isElemAbelian_zpowers_sup hE₂ hε3 (hcF₂ ε hζε.symm hσ₂ε.symm)
  have hER : CFSG.Assembly.IsElemAbelian 3 R :=
    isElemAbelian_zpowers_sup hE₃ hσ₁3 (hcF₃ σ₁ hζσ₁.symm hσ₁σ₂ hσ₁ε)
  have hnm₁ : σ₂ ∉ F₁ := by
    intro hm
    obtain ⟨a, ha⟩ := hF₁mem σ₂ hm
    apply hσc
    have h' : ι₂ σ = ι₂ (ζ₂ ^ a) := by rw [map_zpow, ← hζ]; exact ha
    rw [h₂ h']
    exact Subgroup.zpow_mem _ hζ₂ a
  have hnm₂ : ε ∉ F₂ := by
    intro hm
    obtain ⟨b, a, hba⟩ := hF₂mem ε hm
    have hδ₁eq : δ₁ = ι₂ (σ ^ b * ζ₂ ^ a * δ ^ k₂) := by
      have h1 : δ₁ = ε * δ₂ := by rw [hε]; group
      rw [h1, hba, map_mul, map_mul, map_zpow ι₂ σ b, map_zpow ι₂ ζ₂ a, ← hζ]
    obtain ⟨m, hm'⟩ := hINT (δ ^ k₁) _ hδ₁eq
    have h3 : δ₁ ^ 3 = 1 := by rw [hδ₁, hm']; exact hpow3 m
    exact hζ1 (hδ₁3 ▸ h3)
  have hnm₃ : σ₁ ∉ F₃ := by
    intro hm
    obtain ⟨j, f, hf, hjf⟩ := hF₃dec σ₁ hm
    obtain ⟨b, a, rfl⟩ := hF₂mem f hf
    have hεj : ε ^ j = δ₁ ^ j * (δ₂⁻¹) ^ j :=
      (show Commute δ₁ δ₂⁻¹ from (Commute.inv_right (show Commute δ₁ δ₂ from hδ₁δ₂))).mul_zpow j
    have hab : ι₁ ((δ ^ k₁) ^ (-j) * σ * ζ₁ ^ (-a)) = ι₂ ((δ ^ k₂) ^ (-j) * σ ^ b) := by
      have e1 : ι₁ ((δ ^ k₁) ^ (-j) * σ * ζ₁ ^ (-a)) = δ₁ ^ (-j) * σ₁ * ζ ^ (-a) := by
        rw [map_mul, map_mul, map_zpow ι₁ (δ ^ k₁) (-j), map_zpow ι₁ ζ₁ (-a)]
      have e2 : ι₂ ((δ ^ k₂) ^ (-j) * σ ^ b) = δ₂ ^ (-j) * σ₂ ^ b := by
        rw [map_mul, map_zpow ι₂ (δ ^ k₂) (-j), map_zpow ι₂ σ b]
      rw [e1, e2, hjf, hεj]
      simp only [inv_zpow', zpow_neg]
      group
    obtain ⟨m, hm'⟩ := hINT _ _ hab
    have hm'' : (δ ^ k₁) ^ (-j) * σ * ζ₁ ^ (-a) = ζ₁ ^ m := h₁ (by rw [hm', map_zpow])
    have hζ₁d : ζ₁ = (δ ^ k₁) ^ 3 := by rw [hcube, hk₁']
    have key : ∀ (d : X₀) (j m a : ℤ),
        d ^ j * (d ^ 3) ^ m * (d ^ 3) ^ a = d ^ (j + 3 * m + 3 * a) := by
      intro d j m a
      rw [← zpow_natCast d 3, ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add]
      congr 1
      try push_cast
      try ring
    have hσd : σ = (δ ^ k₁) ^ (j + 3 * m + 3 * a) := by
      have h1 : σ = (δ ^ k₁) ^ j * ζ₁ ^ m * ζ₁ ^ a := by
        calc σ = (δ ^ k₁) ^ j * ((δ ^ k₁) ^ (-j) * σ * ζ₁ ^ (-a)) * ζ₁ ^ a := by group
          _ = _ := by rw [hm'']
      rw [h1, hζ₁d, key]
    exact hσδ (k₁ * (j + 3 * m + 3 * a)) (by rw [zpow_mul]; exact hσd)
  have hζnb : ζ ∉ (⊥ : Subgroup X) := fun h => hζ1 (Subgroup.mem_bot.mp h)
  have hcard₁ : Nat.card F₁ = 3 := by
    have h := card_zpowers_sup_of_not_mem (F := (⊥ : Subgroup X)) hζ3 hζ1 hζnb (fun f hf => by
      rw [Subgroup.mem_bot.mp hf, mul_one, one_mul])
    rw [Subgroup.card_bot] at h
    exact h
  have hσ₂1 : σ₂ ≠ 1 := fun h => hnm₁ (h ▸ F₁.one_mem)
  have hcard₂ : Nat.card F₂ = 9 := by
    have h := card_zpowers_sup_of_not_mem hσ₂3 hσ₂1 hnm₁ (hcF₁ σ₂ hζσ₂.symm)
    rw [hcard₁] at h
    exact h
  have hε1 : ε ≠ 1 := fun h => hnm₂ (h ▸ F₂.one_mem)
  have hcard₃ : Nat.card F₃ = 27 := by
    have h := card_zpowers_sup_of_not_mem hε3 hε1 hnm₂ (hcF₂ ε hζε.symm hσ₂ε.symm)
    rw [hcard₂] at h
    exact h
  refine ⟨R, F₃, v, hER, hE₃, le_sup_right, ?_, hcard₃, ?_, ?_, ?_⟩
  · intro h
    apply hnm₃
    have h1 : σ₁ ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers σ₁)
    rw [← h] at h1
    exact h1
  · rw [hv, ← map_pow, hu2, map_one]
  · intro h
    exact hu1 (h₁ (h.trans (map_one ι₁).symm))
  · intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent v hζv.symm hvσ₂ hvε hf)

end CFSG.RankThree.PartTwo.Sec12.Hering129G
