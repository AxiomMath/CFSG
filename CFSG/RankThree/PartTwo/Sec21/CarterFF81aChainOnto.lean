module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aChainStab
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aX

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

private def chainDiff {B B₁ : Subgroup G} {X : Subgroup (MulAut ↥B)}
    (σ : FF81ChainStabilizer B B₁ X) (x : ↥B) : ↥B :=
  (σ : MulAut ↥B) x * x⁻¹

private theorem chainDiff_mem {B B₁ : Subgroup G} (hB₁B : B₁ ≤ B)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {X : Subgroup (MulAut ↥B)} (σ : FF81ChainStabilizer B B₁ X) (x : ↥B) :
    chainDiff σ x ∈ B₁.subgroupOf B := by
  haveI hcomm : IsMulCommutative ↥B :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hB x x.2 y y.2)
  obtain ⟨y, hy, hxy⟩ := σ.2.2 x
  show (σ : MulAut ↥B) x * x⁻¹ ∈ B₁.subgroupOf B
  rw [hxy]
  have hxy' : (x * y) * x⁻¹ = y := by
    calc (x * y) * x⁻¹ = x * (y * x⁻¹) := mul_assoc _ _ _
      _ = x * (x⁻¹ * y) := by rw [mul_comm' y x⁻¹]
      _ = (x * x⁻¹) * y := (mul_assoc _ _ _).symm
      _ = y := by rw [mul_inv_cancel, one_mul]
  rw [hxy']
  exact hy

private theorem chainDiff_one {B B₁ : Subgroup G} {X : Subgroup (MulAut ↥B)}
    (σ : FF81ChainStabilizer B B₁ X) {h : ↥B}
    (hh : h ∈ B₁.subgroupOf B) : chainDiff σ h = 1 := by
  show (σ : MulAut ↥B) h * h⁻¹ = 1
  rw [σ.2.1 h hh, mul_inv_cancel]

private theorem chainDiff_mul {B B₁ : Subgroup G}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {X : Subgroup (MulAut ↥B)} (σ : FF81ChainStabilizer B B₁ X) (a b : ↥B) :
    chainDiff σ (a * b) = chainDiff σ a * chainDiff σ b := by
  haveI hcomm : IsMulCommutative ↥B :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hB x x.2 y y.2)
  show (σ : MulAut ↥B) (a * b) * (a * b)⁻¹ =
    ((σ : MulAut ↥B) a * a⁻¹) * ((σ : MulAut ↥B) b * b⁻¹)
  rw [map_mul, mul_inv_rev]
  ac_rfl

private theorem chainDiff_pow {B B₁ : Subgroup G}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {X : Subgroup (MulAut ↥B)} (σ : FF81ChainStabilizer B B₁ X)
    {z : ↥B} (n : ℕ) :
    chainDiff σ (z ^ n) = (chainDiff σ z) ^ n := by
  haveI hcomm : IsMulCommutative ↥B :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hB x x.2 y y.2)
  show (σ : MulAut ↥B) (z ^ n) * (z ^ n)⁻¹ =
    ((σ : MulAut ↥B) z * z⁻¹) ^ n
  rw [map_pow, ← inv_pow, ← mul_pow]

private theorem chainDiff_pow_mul {B B₁ : Subgroup G}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {X : Subgroup (MulAut ↥B)} (σ : FF81ChainStabilizer B B₁ X)
    {z : ↥B} (n : ℕ) {h : ↥B} (hh : h ∈ B₁.subgroupOf B) :
    chainDiff σ (z ^ n * h) = (chainDiff σ z) ^ n := by
  rw [chainDiff_mul hB σ, chainDiff_one σ hh, mul_one, chainDiff_pow hB σ n]

private theorem chainDiff_mul_apply {B B₁ : Subgroup G} (hB₁B : B₁ ≤ B)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {X : Subgroup (MulAut ↥B)}
    {σ τ : FF81ChainStabilizer B B₁ X} {z : ↥B} :
    chainDiff (σ * τ) z = chainDiff σ z * chainDiff τ z := by
  haveI hcomm : IsMulCommutative ↥B :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hB x x.2 y y.2)
  have hdτ : chainDiff τ z ∈ B₁.subgroupOf B := chainDiff_mem hB₁B hB τ z
  have hfix : (σ : MulAut ↥B) (chainDiff τ z) = chainDiff τ z := σ.2.1 _ hdτ
  have hτz : (τ : MulAut ↥B) z = chainDiff τ z * z := by
    rw [chainDiff, mul_assoc, inv_mul_cancel, mul_one]
  show ((σ : MulAut ↥B) * (τ : MulAut ↥B)) z * z⁻¹ =
    chainDiff σ z * chainDiff τ z
  rw [MulAut.mul_apply, hτz, map_mul, hfix]
  simp only [chainDiff]
  ac_rfl

private noncomputable def chainDiffHom {B B₁ : Subgroup G} (hB₁B : B₁ ≤ B)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {X : Subgroup (MulAut ↥B)} (z : ↥B) :
    FF81ChainStabilizer B B₁ X →* B₁.subgroupOf B where
  toFun σ := ⟨chainDiff σ z, chainDiff_mem hB₁B hB σ z⟩
  map_one' := by
    apply Subtype.ext
    simp [chainDiff]
  map_mul' σ τ := by
    apply Subtype.ext
    exact chainDiff_mul_apply hB₁B hB

private theorem chainDiff_surj_inj {B B₁ : Subgroup G} {X : Subgroup (MulAut ↥B)}
    {τX : MulAut ↥B}
    (hB₁B : B₁ ≤ B) (hBcard : Nat.card B = 81) (hB₁card : Nat.card B₁ = 27)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB₁X : ∀ σ : MulAut ↥B, σ ∈ X →
      Subgroup.map σ (B₁.subgroupOf B) = B₁.subgroupOf B)
    (hAne : FF81ChainStabilizer B B₁ X ≠ ⊥)
    (hirr : ∀ U : Subgroup ↥B, U ≤ B₁.subgroupOf B →
      (∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ → Subgroup.map σ U = U) →
      U = ⊥ ∨ U = B₁.subgroupOf B)
    {z : ↥B} (hz : z ∉ B₁.subgroupOf B) :
    (∀ y : ↥B, y ∈ B₁.subgroupOf B →
      ∃ σ : FF81ChainStabilizer B B₁ X, chainDiff σ z = y) ∧
      Function.Injective
        (fun σ : FF81ChainStabilizer B B₁ X => chainDiff σ z) := by
  let H : Subgroup ↥B := B₁.subgroupOf B
  let A : Subgroup X := FF81ChainStabilizer B B₁ X
  haveI hcomm : IsMulCommutative ↥B :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hB x x.2 y y.2)
  haveI hHnormal : H.Normal := Subgroup.normal_of_isMulCommutative H
  have hHcard : Nat.card H = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁B).toEquiv).trans hB₁card
  have hBcard' : Nat.card ↥B = 81 := hBcard
  have hindex : H.index = 3 := by
    have h := H.index_mul_card
    rw [hHcard, hBcard'] at h
    omega
  have hQcard : Nat.card (↥B ⧸ H) = 3 := by
    rw [← Subgroup.index_eq_card, hindex]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq_ne : (QuotientGroup.mk' H z : ↥B ⧸ H) ≠ 1 := by
    simpa using hz
  have hdecomp : ∀ x : ↥B, ∃ (n : ℕ) (h : ↥B), h ∈ H ∧ x = z ^ n * h := by
    intro x
    have hmem : (QuotientGroup.mk' H x : ↥B ⧸ H) ∈
        Submonoid.powers (QuotientGroup.mk' H z) :=
      mem_powers_of_prime_card (p := 3) hQcard hq_ne
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
    refine ⟨n, (z ^ n)⁻¹ * x, ?_, (mul_inv_cancel_left (z ^ n) x).symm⟩
    have hzk : (QuotientGroup.mk' H (z ^ n) : ↥B ⧸ H) = QuotientGroup.mk' H x := by
      rw [map_pow, hn]
    exact QuotientGroup.eq.mp hzk
  have hz3 : z ^ 3 ∈ H := by
    simpa [hindex] using Subgroup.pow_index_mem H z
  have hdecomp2 : ∀ x : ↥B, x ∉ H →
      ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∃ h : ↥B, h ∈ H ∧ x = z ^ r * h := by
    intro x hx
    obtain ⟨n, h, hh, hxeq⟩ := hdecomp x
    have hn : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
    have hpow : z ^ n = (z ^ 3) ^ (n / 3) * z ^ (n % 3) := by
      calc z ^ n = z ^ (3 * (n / 3) + n % 3) := by
            conv_lhs => rw [hn]
        _ = z ^ (3 * (n / 3)) * z ^ (n % 3) := pow_add _ _ _
        _ = (z ^ 3) ^ (n / 3) * z ^ (n % 3) := by rw [← pow_mul]
    have hmem : (z ^ 3) ^ (n / 3) * h ∈ H :=
      H.mul_mem (H.pow_mem hz3 _) hh
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : n % 3 ≠ 0 := by
      intro hzero
      apply hx
      rw [hxeq, hpow, hzero]
      simpa using hmem
    refine ⟨n % 3, by omega, (z ^ 3) ^ (n / 3) * h, hmem, ?_⟩
    calc x = z ^ n * h := hxeq
      _ = ((z ^ 3) ^ (n / 3) * z ^ (n % 3)) * h := by rw [hpow]
      _ = z ^ (n % 3) * ((z ^ 3) ^ (n / 3) * h) := by ac_rfl
  let Φ : A →* H := chainDiffHom hB₁B hB z
  let W : Subgroup ↥B := Φ.range.map H.subtype
  have hWmem : ∀ w : ↥B, w ∈ W ↔ ∃ σ : A, chainDiff σ z = w := by
    intro w
    constructor
    · intro hw
      obtain ⟨h, hh, hEq⟩ := Subgroup.mem_map.mp hw
      obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hh
      refine ⟨σ, ?_⟩
      rw [← hEq]
      exact congrArg Subtype.val hσ
    · rintro ⟨σ, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Φ σ, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, rfl⟩
  have hWle : W ≤ H := Subgroup.map_subtype_le Φ.range
  have hΦinj : Function.Injective Φ := by
    intro σ τ hστ
    have hz_eq : chainDiff σ z = chainDiff τ z := congrArg Subtype.val hστ
    have hfun : chainDiff σ = chainDiff τ := by
      funext x
      obtain ⟨n, h, hh, hx⟩ := hdecomp x
      rw [hx, chainDiff_pow_mul hB σ n hh, chainDiff_pow_mul hB τ n hh, hz_eq]
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact mul_right_cancel (congrFun hfun x)
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have hmemW : chainDiff (⟨σ, hσ⟩ : A) z ∈ W :=
      (hWmem _).mpr ⟨⟨σ, hσ⟩, rfl⟩
    rw [hbot] at hmemW
    have h1 : chainDiff (⟨σ, hσ⟩ : A) z = 1 := Subgroup.mem_bot.mp hmemW
    have hΦ1 : Φ (⟨σ, hσ⟩ : A) = Φ 1 := by
      apply Subtype.ext
      change chainDiff (⟨σ, hσ⟩ : A) z = chainDiff (1 : A) z
      rw [show chainDiff (1 : A) z = 1 by simp [chainDiff]]
      exact h1
    have hσ1 : (⟨σ, hσ⟩ : A) = 1 := hΦinj hΦ1
    simpa using congrArg (fun a : A => (a : X)) hσ1
  have hW_smul : ∀ (g : MulAut ↥B), g ∈ X → ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    obtain ⟨σ, rfl⟩ := (hWmem w).mp hw
    have hgzH : g z ∉ H := by
      intro hmem
      apply hz
      have hmapinv : Subgroup.map (g⁻¹ : MulAut ↥B) H = H :=
        hB₁X g⁻¹ (X.inv_mem hg)
      have hzmem : z ∈ Subgroup.map (g⁻¹ : MulAut ↥B) H :=
        Subgroup.mem_map.mpr ⟨g z, hmem, by simp⟩
      rwa [hmapinv] at hzmem
    obtain ⟨r, -, h, hh, hgz⟩ := hdecomp2 (g z) hgzH
    have hAnormal : A.Normal := FF81ChainStabilizer.normal B B₁ X hB₁X
    let gX : X := ⟨g, hg⟩
    let β : A :=
      ⟨gX * (σ : X) * gX⁻¹, hAnormal.conj_mem (σ : X) σ.2 gX⟩
    have hβcoe : (β : MulAut ↥B) = g * (σ : MulAut ↥B) * g⁻¹ := rfl
    have hkey : g (chainDiff σ z) = chainDiff β (g z) := by
      rw [chainDiff, chainDiff, hβcoe, map_mul, map_inv]
      simp only [MulAut.mul_apply]
      rw [MulAut.inv_apply_self]
    rw [hkey, hgz, chainDiff_mul hB β (z ^ r) h, chainDiff_pow hB β r,
      chainDiff_one β hh, mul_one]
    exact W.pow_mem ((hWmem _).mpr ⟨β, rfl⟩) r
  have hWmap : ∀ (g : MulAut ↥B), g ∈ X → Subgroup.map g W = W := by
    intro g hg
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro w hw
      exact hW_smul g hg w hw
    · intro w hw
      refine Subgroup.mem_map.mpr ⟨g⁻¹ w, ?_, ?_⟩
      · exact hW_smul g⁻¹ (X.inv_mem hg) w hw
      · exact MulAut.apply_inv_self (M := ↥B) g w
  have hW : W = H := by
    rcases hirr W hWle (fun g hg _ => hWmap g hg) with hbot | htop
    · exact absurd hbot hWne
    · exact htop
  refine ⟨?_, ?_⟩
  · intro y hy
    have hyW : y ∈ W := by rw [hW]; exact hy
    exact (hWmem y).mp hyW
  · intro σ τ hστ
    have hz_eq : chainDiff σ z = chainDiff τ z := hστ
    have hfun : chainDiff σ = chainDiff τ := by
      funext x
      obtain ⟨n, h, hh, hx⟩ := hdecomp x
      rw [hx, chainDiff_pow_mul hB σ n hh, chainDiff_pow_mul hB τ n hh, hz_eq]
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact mul_right_cancel (congrFun hfun x)

theorem FF81Hyp.exists_conj_b_mul
    {B B₁ : Subgroup G} {X : Subgroup (MulAut ↥B)} {τX : MulAut ↥B}
    (hbB : b ∈ B) (hB₁B : B₁ ≤ B) (hbnot : b ∉ B₁)
    (hBcard : Nat.card B = 81) (hB₁card : Nat.card B₁ = 27)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB₁X : ∀ σ : MulAut ↥B, σ ∈ X →
      Subgroup.map σ (B₁.subgroupOf B) = B₁.subgroupOf B)
    (hAne : FF81ChainStabilizer B B₁ X ≠ ⊥)
    (hirr : ∀ U : Subgroup ↥B, U ≤ B₁.subgroupOf B →
      (∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ → Subgroup.map σ U = U) →
      U = ⊥ ∨ U = B₁.subgroupOf B)
    (hXle : X ≤ FF81X B)
    {y : G} (hy : y ∈ B₁) :
    ∃ a : G, a ∈ Nor B ∧ (∀ z ∈ B₁, a * z * a⁻¹ = z) ∧ a * b * a⁻¹ = b * y := by
  let bB : ↥B := ⟨b, hbB⟩
  let yB : ↥B := ⟨y, hB₁B hy⟩
  have hbH : bB ∉ B₁.subgroupOf B := by
    intro hmem
    exact hbnot (Subgroup.mem_subgroupOf.mp hmem)
  obtain ⟨hsurj, -⟩ :=
    chainDiff_surj_inj (B := B) (B₁ := B₁) (X := X) (τX := τX)
      hB₁B hBcard hB₁card hB hB₁X hAne hirr hbH
  have hyH : yB ∈ B₁.subgroupOf B := Subgroup.mem_subgroupOf.mpr hy
  obtain ⟨σ, hσ⟩ := hsurj yB hyH
  have hσAutX : (σ : MulAut ↥B) ∈ FF81X B := hXle (σ : X).2
  obtain ⟨n, hn⟩ := mem_FF81X_iff.mp hσAutX
  have hfixσ : ∀ (z : G) (hz : z ∈ B₁),
      (σ : MulAut ↥B) ⟨z, hB₁B hz⟩ = ⟨z, hB₁B hz⟩ := by
    intro z hz
    exact σ.2.1 ⟨z, hB₁B hz⟩ (Subgroup.mem_subgroupOf.mpr hz)
  have hcen : ∀ z ∈ B₁, (n : G) * z * (n : G)⁻¹ = z := by
    intro z hz
    calc (n : G) * z * (n : G)⁻¹
        = ((Subgroup.normalizerMonoidHom (H := B) n) ⟨z, hB₁B hz⟩ : G) := by
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      _ = z := by rw [hn, hfixσ z hz]
  have hσb : (σ : MulAut ↥B) bB = bB * yB := by
    have hσ' : (σ : MulAut ↥B) bB * bB⁻¹ = yB := by
      simpa [chainDiff] using hσ
    calc (σ : MulAut ↥B) bB
        = ((σ : MulAut ↥B) bB * bB⁻¹) * bB := by group
      _ = yB * bB := by rw [hσ']
      _ = bB * yB := by
          apply Subtype.ext
          exact hB y (hB₁B hy) b hbB
  have hconj : (n : G) * b * (n : G)⁻¹ = b * y := by
    calc (n : G) * b * (n : G)⁻¹
        = ((Subgroup.normalizerMonoidHom (H := B) n) bB : G) := by
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      _ = ((σ : MulAut ↥B) bB : G) := by rw [hn]
      _ = ((bB * yB : ↥B) : G) := by rw [hσb]
      _ = b * y := rfl
  exact ⟨(n : G), n.2, hcen, hconj⟩

end CFSG.RankThree.PartTwo.Sec21.FF81