module

public import CFSG.Quasithin.EmptyFaithful.S146zNBrY
public import CFSG.Quasithin.EmptyFaithful.S146E4
public import CFSG.Quasithin.EmptyFaithful.S146zNCtx
public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Sec

variable {G : Type*} [Group G] {A B : Subgroup G} [(B.subgroupOf A).Normal]

theorem a6g_secImg_sup {X Y : Subgroup G} (hX : X ≤ A) (hY : Y ≤ A) :
    secImg A B (X ⊔ Y) = secImg A B X ⊔ secImg A B Y := by
  unfold secImg
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem a6g_secImg_conjSub {X : Subgroup G} (g : A) :
    secImg A B (conjSub (g : G) X) = conjSub (secMk A B g) (secImg A B X) := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro hy
    obtain ⟨a, haX, rfl⟩ := mem_secImg.mp hy
    have ha' : (g : G)⁻¹ * (a : G) * (g : G) ∈ X := mem_conjSub.mp haX
    refine mem_secImg.mpr ⟨g⁻¹ * a * g, by simpa using ha', ?_⟩
    simp [map_mul, map_inv]
  · intro hy
    obtain ⟨b, hbX, hb⟩ := mem_secImg.mp hy
    refine mem_secImg.mpr ⟨g * b * g⁻¹, ?_, ?_⟩
    · simpa using mul_mem_conjSub (g := (g : G)) hbX
    · simp only [map_mul, map_inv, hb]
      group

theorem a6g_secImg_zpowers (x : A) :
    secImg A B (Subgroup.zpowers (x : G)) = Subgroup.zpowers (secMk A B x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := mem_secImg.mp hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
    have : a = x ^ n := Subtype.ext (by simpa using hn.symm)
    rw [this, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine mem_secImg.mpr ⟨x ^ n, ?_, by rw [map_zpow]⟩
    simp

theorem a6g_secMk_mem_centralizer_iff {E : Subgroup G} (hEA : E ≤ A) (g : A) :
    secMk A B g ∈ Subgroup.centralizer (secImg A B E : Set (SecQuot A B)) ↔
      ∀ e ∈ E, (g : G) * e * (g : G)⁻¹ * e⁻¹ ∈ B := by
  constructor
  · intro h e he
    have := Subgroup.mem_centralizer_iff.mp h (secMk A B ⟨e, hEA he⟩)
      (secMk_mem_secImg (x := ⟨e, hEA he⟩) he)
    exact commutator_mem_of_secMk_commute (x := g) (y := ⟨e, hEA he⟩) this.symm
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨e, he, rfl⟩ := mem_secImg.mp hy
    exact (secMk_comm_of_commutator_mem (x := g) (y := e) (h e he)).symm

end Sec

section Irr

variable {G : Type*} [Group G]

theorem a6g_irr {Z₀ U₁ K : Subgroup G} (hZU : Z₀ ≤ U₁) (hKN : K ≤ Subgroup.normalizer (Z₀ : Set G))
    (hirr : ∀ W : Subgroup G, Z₀ ≤ W → W ≤ U₁ → K ≤ Subgroup.normalizer (W : Set G) →
      W = Z₀ ∨ W = U₁)
    {S : Subgroup (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀)} (hS : S ≤ tildeOf Z₀ U₁)
    (hSK : tildeOf Z₀ K ≤
      Subgroup.normalizer (S : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀))) :
    S = ⊥ ∨ S = tildeOf Z₀ U₁ := by
  let W : Subgroup G := (S.comap (secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀)).map
    (Subgroup.normalizer (Z₀ : Set G)).subtype
  have hWN : ∀ x ∈ W, x ∈ Subgroup.normalizer (Z₀ : Set G) := by
    rintro x ⟨a, -, rfl⟩
    exact a.2
  have hmemW : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (Z₀ : Set G)),
      x ∈ W ↔ secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀ ⟨x, hx⟩ ∈ S := by
    intro x hx
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hZW : Z₀ ≤ W := fun z hz => by
    rw [hmemW z (Subgroup.le_normalizer hz),
      (secMk_eq_one_iff (x := ⟨z, Subgroup.le_normalizer hz⟩)).mpr hz]
    exact S.one_mem
  have hWU : W ≤ U₁ := by
    intro x hx
    have hxN := hWN x hx
    have := hS ((hmemW x hxN).mp hx)
    exact (secMk_mem_secImg_iff hZU).mp this
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hkN : k ∈ Subgroup.normalizer (Z₀ : Set G) := hKN hk
    have hk' := hSK (secMk_mem_secImg (A := Subgroup.normalizer (Z₀ : Set G)) (B := Z₀)
      (x := ⟨k, hkN⟩) hk)
    rw [Subgroup.mem_normalizer_iff] at hk'
    constructor
    · intro hx
      have hxN := hWN x hx
      have hkxN : k * x * k⁻¹ ∈ Subgroup.normalizer (Z₀ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN hxN) (Subgroup.inv_mem _ hkN)
      rw [hmemW _ hkxN]
      have := (hk' _).mp ((hmemW x hxN).mp hx)
      have e : (⟨k * x * k⁻¹, hkxN⟩ : Subgroup.normalizer (Z₀ : Set G)) =
          ⟨k, hkN⟩ * ⟨x, hxN⟩ * ⟨k, hkN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact this
    · intro hx
      have hkxN := hWN _ hx
      have hxN : x ∈ Subgroup.normalizer (Z₀ : Set G) := by
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hkxN) hkN
        simpa [mul_assoc] using this
      rw [hmemW x hxN]
      have h1 := (hmemW _ hkxN).mp hx
      have e : (⟨k * x * k⁻¹, hkxN⟩ : Subgroup.normalizer (Z₀ : Set G)) =
          ⟨k, hkN⟩ * ⟨x, hxN⟩ * ⟨k, hkN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv] at h1
      exact (hk' _).mpr h1
  rcases hirr W hZW hWU hKW with hW | hW
  · left
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨a, rfl⟩ := secMk_surjective y
    have : (a : G) ∈ W := (hmemW _ a.2).mpr hy
    rw [hW] at this
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.mpr this
  · right
    refine le_antisymm hS fun y hy => ?_
    obtain ⟨a, haU, rfl⟩ := mem_secImg.mp hy
    have : (a : G) ∈ W := by rw [hW]; exact haU
    exact (hmemW _ a.2).mp this

omit [Group G] in
theorem a6g_card_tilde [Group G] [Finite G] {Z₀ U₁ : Subgroup G} (hZU : Z₀ ≤ U₁)
    (hU₁N : U₁ ≤ Subgroup.normalizer (Z₀ : Set G)) (hU₁2 : IsPGroup 2 U₁) {n : ℕ}
    (hn : mIdx U₁ Z₀ = n) : Nat.card ↥(tildeOf Z₀ U₁) = 2 ^ n := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (Z₀ : Set G)) (B := Z₀) (le_refl Z₀) hZU hU₁N
  have h2 : secImg (Subgroup.normalizer (Z₀ : Set G)) Z₀ Z₀ = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left, HypF98.relIndex_eq_two_pow_mIdx (Y := Z₀) hU₁2, hn] at h1
  exact h1

end Irr

section Iso

variable {G : Type} [Group G]

omit [Group G] in
theorem a6g_secRho_mem_autOn [Group G] {Z U X : Subgroup G}
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (x : ↥X) : secRho hXZ hXU x ∈ autOn (tildeOf Z X) (tildeOf Z U) := by
  refine Subgroup.mem_map.mpr ⟨⟨secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ x),
    secMk_mem_normalizer_secImg (a := Subgroup.inclusion hXZ x) (hXU x.2)⟩, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr (secMk_mem_secImg (x := Subgroup.inclusion hXZ x) x.2)

omit [Group G] in
theorem a6g_range_secRho [Group G] {Z U X : Subgroup G}
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) (hXU : X ≤ Subgroup.normalizer (U : Set G)) :
    (secRho hXZ hXU).range = autOn (tildeOf Z X) (tildeOf Z U) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact a6g_secRho_mem_autOn hXZ hXU x
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x', hx', hxy⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨⟨(x' : G), hx'⟩, ?_⟩
    show conjAct (tildeOf Z U) _ = conjAct (tildeOf Z U) y
    congr 1
    exact Subtype.ext hxy

omit [Group G] in
theorem a6g_ker_secRho [Group G] {Z U X : Subgroup G}
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hU : U ≤ Subgroup.normalizer (Z : Set G)) :
    (secRho hXZ hXU).ker = (centralizerMod Z X U).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact ⟨x.2, hXZ x.2, fun u hu => commutator_mem_of_secRho_eq_one hXZ hXU hU h hu⟩
  · intro h
    exact ThreeC.secRho_eq_one_of_comm hXZ hXU hU h.2.2

theorem a6g_nonempty_equiv {Z₀ E K : Subgroup G} (hKZ : K ≤ Subgroup.normalizer (Z₀ : Set G))
    (hKE : K ≤ Subgroup.normalizer (E : Set G)) (hE : E ≤ Subgroup.normalizer (Z₀ : Set G))
    (hker : centralizerMod Z₀ K E = pCoreOf 2 K) (hA : KbarIsA6 K) :
    Nonempty (↥(autOn (tildeOf Z₀ K) (tildeOf Z₀ E)) ≃* ↥(alternatingGroup (Fin 6))) := by
  obtain ⟨e⟩ := hA
  have hk : (secRho hKZ hKE).ker = (pCoreOf 2 K).subgroupOf K := by
    rw [a6g_ker_secRho hKZ hKE hE, hker]
  let e1 : KBar K ≃* ↥(secRho hKZ hKE).range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange (secRho hKZ hKE))
  let e2 : ↥(secRho hKZ hKE).range ≃* ↥(autOn (tildeOf Z₀ K) (tildeOf Z₀ E)) :=
    MulEquiv.subgroupCongr (a6g_range_secRho hKZ hKE)
  exact ⟨(e1.trans e2).symm.trans e⟩

theorem a6g_fuse {Z₀ E K H : Subgroup G} {s : G} (hE : E ≤ Subgroup.normalizer (Z₀ : Set G))
    (hKH : K ≤ H) (hHZ : H ≤ Subgroup.normalizer (Z₀ : Set G))
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hsH : s ∈ H)
    (hker : centralizerMod Z₀ K E = pCoreOf 2 K) (hf : KbarFusesThrees K s) :
    ∃ x ∈ tildeOf Z₀ K,
      x ^ 3 ∈ Subgroup.centralizer (tildeOf Z₀ E : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀)) ∧
      x ∉ Subgroup.centralizer (tildeOf Z₀ E : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀)) ∧
      ∀ k ∈ tildeOf Z₀ K, (k * x * k⁻¹)⁻¹ *
          (secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀ ⟨s, hHZ hsH⟩ * x *
            (secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀ ⟨s, hHZ hsH⟩)⁻¹) ∉
        Subgroup.centralizer (tildeOf Z₀ E : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀)) := by
  obtain ⟨x, hxK, hx3, hxn, hk⟩ := hf
  have hxN : x ∈ Subgroup.normalizer (Z₀ : Set G) := hHZ (hKH hxK)
  have hsN : s ∈ Subgroup.normalizer (Z₀ : Set G) := hHZ hsH
  have key : ∀ g : Subgroup.normalizer (Z₀ : Set G), (g : G) ∈ K →
      (secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀ g ∈
        Subgroup.centralizer (tildeOf Z₀ E : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀)) ↔
          (g : G) ∈ pCoreOf 2 K) := by
    intro g hg
    rw [← hker]
    exact (a6g_secMk_mem_centralizer_iff (B := Z₀) hE g).trans
      ⟨fun h => ⟨hg, g.2, h⟩, fun h => h.2.2⟩
  refine ⟨secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀ ⟨x, hxN⟩,
    secMk_mem_secImg (x := ⟨x, hxN⟩) hxK, ?_, ?_, ?_⟩
  · rw [← map_pow]
    exact (key ⟨x ^ 3, Subgroup.pow_mem _ hxN 3⟩ (Subgroup.pow_mem _ hxK 3)).mpr hx3
  · intro h
    exact hxn ((key ⟨x, hxN⟩ hxK).mp h)
  · intro k hk' h
    obtain ⟨k₀, hk₀, rfl⟩ := mem_secImg.mp hk'
    have hk₀N : (k₀ : G) ∈ Subgroup.normalizer (Z₀ : Set G) := k₀.2
    have hsK : s ∈ Subgroup.normalizer (K : Set G) := hHK hsH
    have hc : (k₀ : G)⁻¹ ∈ K := K.inv_mem hk₀
    have h1 : (k₀ : G) * x * (k₀ : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hk₀ hxK) (K.inv_mem hk₀)
    have h2 : s * x * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hsK x).mp hxK
    have hcK : ((k₀ : G) * x * (k₀ : G)⁻¹)⁻¹ * (s * x * s⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem h1) h2
    have hcN : ((k₀ : G) * x * (k₀ : G)⁻¹)⁻¹ * (s * x * s⁻¹) ∈
        Subgroup.normalizer (Z₀ : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₀N hxN)
        (Subgroup.inv_mem _ hk₀N))) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsN hxN)
        (Subgroup.inv_mem _ hsN))
    have e : (⟨((k₀ : G) * x * (k₀ : G)⁻¹)⁻¹ * (s * x * s⁻¹), hcN⟩ :
        Subgroup.normalizer (Z₀ : Set G)) =
        (k₀ * ⟨x, hxN⟩ * k₀⁻¹)⁻¹ * (⟨s, hsN⟩ * ⟨x, hxN⟩ * ⟨s, hsN⟩⁻¹) := rfl
    have h3 : secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀
        ⟨((k₀ : G) * x * (k₀ : G)⁻¹)⁻¹ * (s * x * s⁻¹), hcN⟩ ∈
        Subgroup.centralizer (tildeOf Z₀ E : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀)) := by
      rw [e]
      simpa only [map_mul, map_inv] using h
    exact hk k₀ hk₀ ((key _ hcK).mp h3)

end Iso

section Main

variable {G : Type} [Group G] [Finite G]

theorem a6amt_group (hA6 : A6Amt) {Z₀ E H K X U U₁ U₂ Q : Subgroup G} {s : G}
    (hUab : IsElemAbelian 2 U) (hZE : Z₀ ≤ E) (hEU : E ≤ U)
    (hHZ : H ≤ Subgroup.normalizer (Z₀ : Set G)) (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hKH : K ≤ H) (hXH : X ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hsH : s ∈ H)
    (hQ : centralizerMod Z₀ H E = Q) (hker : centralizerMod Z₀ K E = pCoreOf 2 K)
    (hZ₁ : Z₀ ≤ U₁) (hsup : U₁ ⊔ U₂ = E) (hU₂s : U₂ = conjSub s U₁)
    (hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G)) (hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G))
    (hcard : mIdx U₁ Z₀ = 4)
    (hirr : ∀ W : Subgroup G, Z₀ ≤ W → W ≤ U₁ → K ≤ Subgroup.normalizer (W : Set G) →
      W = Z₀ ∨ W = U₁)
    (hA : KbarIsA6 K) (hf : KbarFusesThrees K s)
    (hXab : IsElemAbelian 2 X) (hXnt : ¬ X ≤ Q)
    (hquad : ∀ b₁ ∈ X, ∀ b₂ ∈ X, ∀ e ∈ E,
      b₂ * (b₁ * e * b₁⁻¹ * e⁻¹) * b₂⁻¹ * (b₁ * e * b₁⁻¹ * e⁻¹)⁻¹ ∈ Z₀)
    (hr : mIdx E (centralizerMod Z₀ E X) ≤ 2 * mIdx X (X ⊓ Q)) :
    mIdx E (centralizerMod Z₀ E X) = 2 * mIdx X (X ⊓ Q) ∧
      ∃ x ∈ X, mIdx X (X ⊓ Q) + 2 ≤ mIdx E (centralizerMod Z₀ E (Subgroup.zpowers x)) := by
  classical
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hU₁E : U₁ ≤ E := hsup ▸ le_sup_left
  have hU₂E : U₂ ≤ E := hsup ▸ le_sup_right
  have hUN : ∀ W : Subgroup G, W ≤ U → W ≤ Subgroup.normalizer (Z₀ : Set G) := fun W hW =>
    le_normalizer_of_forall_commute fun w hw z hz => hUc w (hW hw) z (hEU (hZE hz))
  have hEN : E ≤ Subgroup.normalizer (Z₀ : Set G) := hUN E hEU
  have hU₁N : U₁ ≤ Subgroup.normalizer (Z₀ : Set G) := hUN U₁ (hU₁E.trans hEU)
  have hU₂N : U₂ ≤ Subgroup.normalizer (Z₀ : Set G) := hUN U₂ (hU₂E.trans hEU)
  have hKZ : K ≤ Subgroup.normalizer (Z₀ : Set G) := hKH.trans hHZ
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := hKH.trans hHE
  have hXZ : X ≤ Subgroup.normalizer (Z₀ : Set G) := hXH.trans hHZ
  have hsN : s ∈ Subgroup.normalizer (Z₀ : Set G) := hHZ hsH
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Z₀ := fun x hx y hy => by
    have : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hUc x (hEU hx) y (hEU hy)]; group
    rw [this]; exact Z₀.one_mem
  have hEsq : ∀ x ∈ E, x ^ 2 ∈ Z₀ := fun x hx => by
    rw [hUab.2 x (hEU hx)]; exact Z₀.one_mem
  have hV : IsElemAbelian 2 (tildeOf Z₀ E) := isElemAbelian_secImg_normalizer hEc hEsq
  have hU₁2 : IsPGroup 2 U₁ := (isPGroup_of_isElemAbelian hUab).to_le (hU₁E.trans hEU)
  have hCX : centralizerMod Z₀ X E = X ⊓ Q := by
    ext x
    constructor
    · rintro ⟨hxX, hxN, h⟩
      exact ⟨hxX, by rw [← hQ]; exact ⟨hXH hxX, hxN, h⟩⟩
    · rintro ⟨hxX, hxQ⟩
      rw [← hQ] at hxQ
      exact ⟨hxX, hxQ.2.1, hxQ.2.2⟩
  have e1 : mIdx (tildeOf Z₀ E) (tildeOf Z₀ E ⊓ Subgroup.centralizer
        (tildeOf Z₀ X : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀))) =
      mIdx E (centralizerMod Z₀ E X) :=
    congrArg (padicValNat 2) (relIndex_secImg_fix (K := Z₀) (E := E) (X := X) hXZ hEN)
  have e2 : mIdx (tildeOf Z₀ X) (tildeOf Z₀ X ⊓ Subgroup.centralizer
        (tildeOf Z₀ E : Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀))) =
      mIdx X (X ⊓ Q) := by
    rw [← hCX]
    exact congrArg (padicValNat 2) (relIndex_secImg_fix (K := Z₀) (E := X) (X := E) hEN hXZ)
  have hbridge := a6amt_bridge hA6 (V₀ := tildeOf Z₀ E) (H := tildeOf Z₀ H) (K := tildeOf Z₀ K)
    (X := tildeOf Z₀ X) (W₁ := tildeOf Z₀ U₁) (W₂ := tildeOf Z₀ U₂)
    (s := secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀ ⟨s, hsN⟩) hV
    (secImg_le_normalizer_secImg hHE) (secImg_mono hKH) (secImg_mono hXH)
    (secImg_le_normalizer_secImg hHK) (secMk_mem_secImg (x := ⟨s, hsN⟩) hsH)
    (secImg_mono hU₁E) (secImg_mono hU₂E)
    ((a6g_secImg_sup (B := Z₀) hU₁N hU₂N).symm.trans
      (congrArg (secImg (Subgroup.normalizer (Z₀ : Set G)) Z₀) hsup))
    (secImg_le_normalizer_secImg hKU₁) (secImg_le_normalizer_secImg hKU₂)
    (by rw [hU₂s]; exact a6g_secImg_conjSub (B := Z₀) ⟨s, hsN⟩)
    (by rw [a6g_card_tilde hZ₁ hU₁N hU₁2 hcard]; norm_num)
    (fun W hW hKW => a6g_irr hZ₁ hKZ hirr hW hKW)
    (a6g_nonempty_equiv hKZ hKE hEN hker hA)
    (a6g_fuse hEN hKH hHZ hHK hsH hker hf)
    (isElemAbelian_secImg hXab)
    (by
      intro h
      apply hXnt
      intro x hx
      rw [← hQ]
      refine ⟨hXH hx, hHZ (hXH hx), ?_⟩
      have := h (secMk_mem_secImg (x := ⟨x, hHZ (hXH hx)⟩) hx)
      exact (a6g_secMk_mem_centralizer_iff (B := Z₀) hEN ⟨x, hHZ (hXH hx)⟩).mp this)
    (by
      intro b₁ hb₁ b₂ hb₂ e he
      obtain ⟨x₁, hx₁, rfl⟩ := mem_secImg.mp hb₁
      obtain ⟨x₂, hx₂, rfl⟩ := mem_secImg.mp hb₂
      obtain ⟨u, hu, rfl⟩ := mem_secImg.mp he
      have h1 := (secMk_eq_one_iff (A := Subgroup.normalizer (Z₀ : Set G)) (B := Z₀)
        (x := x₂ * (x₁ * u * x₁⁻¹ * u⁻¹) * x₂⁻¹ * (x₁ * u * x₁⁻¹ * u⁻¹)⁻¹)).mpr
        (by simpa using hquad _ hx₁ _ hx₂ _ hu)
      simpa only [map_mul, map_inv] using h1)
    (by rw [e1, e2]; exact hr)
  obtain ⟨hc1, x', hx', hc2⟩ := hbridge
  rw [e1, e2] at hc1
  obtain ⟨x, hxX, rfl⟩ := mem_secImg.mp hx'
  refine ⟨hc1, x, hxX, ?_⟩
  rw [e2] at hc2
  have e3 : mIdx (tildeOf Z₀ E) (tildeOf Z₀ E ⊓ Subgroup.centralizer
        ((Subgroup.zpowers (secMk (Subgroup.normalizer (Z₀ : Set G)) Z₀ x) : Subgroup _) :
          Set (SecQuot (Subgroup.normalizer (Z₀ : Set G)) Z₀))) =
      mIdx E (centralizerMod Z₀ E (Subgroup.zpowers (x : G))) := by
    rw [← a6g_secImg_zpowers (B := Z₀) x]
    exact congrArg (padicValNat 2) (relIndex_secImg_fix (K := Z₀) (E := E)
      (X := Subgroup.zpowers (x : G)) (Subgroup.zpowers_le.mpr x.2) hEN)
  rw [e3] at hc2
  exact hc2

end Main

end CFSG.Quasithin
