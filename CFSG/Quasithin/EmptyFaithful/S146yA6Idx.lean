module

public import CFSG.Quasithin.EmptyFaithful.S146yA6Gen
public import CFSG.Quasithin.EmptyFaithful.S146yA6Mod
public import CFSG.Quasithin.EmptyFaithful.S146xRk

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section ModSub

variable {G : Type} [Group G] {Z U : Subgroup G}

@[expose] def modSub (Z U X : Subgroup G) : Subgroup ↥(tildeOf Z U) :=
  (tildeOf Z X).subgroupOf (tildeOf Z U)

theorem mem_modSub {X : Subgroup G} {x : ↥(tildeOf Z U)} :
    x ∈ modSub Z U X ↔ (x : SecQuot (Subgroup.normalizer (Z : Set G)) Z) ∈ tildeOf Z X :=
  Iff.rfl

theorem modSub_mono {X X' : Subgroup G} (h : X ≤ X') : modSub Z U X ≤ modSub Z U X' :=
  fun _ hx => secImg_mono h hx

theorem modSub_injective {X X' : Subgroup G} (hZX : Z ≤ X) (hZX' : Z ≤ X') (hXU : X ≤ U)
    (hX'U : X' ≤ U) (hUN : U ≤ Subgroup.normalizer (Z : Set G)) (h : modSub Z U X = modSub Z U X') :
    X = X' := by
  have key : ∀ {Y Y' : Subgroup G}, Z ≤ Y' → Y ≤ U → Y' ≤ U → modSub Z U Y ≤ modSub Z U Y' →
      Y ≤ Y' := by
    intro Y Y' hZY' hYU hY'U hle y hy
    have hyN : y ∈ Subgroup.normalizer (Z : Set G) := hUN (hYU hy)
    have h1 : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨y, hyN⟩ ∈ tildeOf Z Y := secMk_mem_secImg hy
    have h2 : (⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨y, hyN⟩, secMk_mem_secImg (hYU hy)⟩ :
        ↥(tildeOf Z U)) ∈ modSub Z U Y := h1
    have h3 := hle h2
    exact (secMk_mem_secImg_iff (A := Subgroup.normalizer (Z : Set G)) (B := Z) hZY' |>.mp h3)
  exact le_antisymm (key hZX' hXU hX'U h.le) (key hZX hX'U hXU h.ge)

theorem card_modSub {X : Subgroup G} (hZX : Z ≤ X) (hXU : X ≤ U)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G)) : Nat.card (modSub Z U X) = Z.relIndex X := by
  have h1 : Nat.card (modSub Z U X) = Nat.card (tildeOf Z X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (secImg_mono hXU)).toEquiv
  have h2 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := Z) (H := X)
    le_rfl hZX (hXU.trans hUN)
  have h3 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h3, Subgroup.relIndex_bot_left] at h2
  rw [h1]
  exact h2

theorem tildeOf_sup_eq {X X' : Subgroup G} (hX : X ≤ Subgroup.normalizer (Z : Set G))
    (hX' : X' ≤ Subgroup.normalizer (Z : Set G)) :
    tildeOf Z (X ⊔ X') = tildeOf Z X ⊔ tildeOf Z X' := by
  unfold tildeOf secImg
  rw [Subgroup.subgroupOf_sup hX hX', Subgroup.map_sup]

theorem modSub_sup {X X' : Subgroup G} (hX : X ≤ U) (hX' : X' ≤ U)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G)) :
    modSub Z U (X ⊔ X') = modSub Z U X ⊔ modSub Z U X' := by
  unfold modSub
  rw [tildeOf_sup_eq (hX.trans hUN) (hX'.trans hUN),
    Subgroup.subgroupOf_sup (A := tildeOf Z X) (A' := tildeOf Z X') (B := tildeOf Z U)
      (secImg_mono hX) (secImg_mono hX')]

end ModSub

section Act

variable {G : Type} [Group G] [Finite G] {Z U K : Subgroup G} {s : G}

omit [Finite G] in
theorem isElemAbelian_tilde_of (hel : IsElemAbelian 2 U) :
    IsElemAbelian 2 (tildeOf Z U) := by
  refine isElemAbelian_secImg_normalizer (fun x hx y hy => ?_) (fun x hx => ?_)
  · have hc : x * y = y * x :=
      congrArg Subtype.val (hel.1.is_comm.comm (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)
    rw [show x * y * x⁻¹ * y⁻¹ = 1 by rw [hc]; group]
    exact Z.one_mem
  · rw [hel.2 x hx]
    exact Z.one_mem

@[expose] noncomputable def repKBar (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) :
    KBar K →* MulAut ↥(tildeOf Z U) :=
  QuotientGroup.lift ((pCoreOf 2 K).subgroupOf K) (secRho hKZ hKU) (by
    intro p hp
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, hu, rfl⟩ := exists_tildeElt hUZ y
    rw [MulAut.one_apply]
    exact (secRho_apply_tildeElt_iff hKZ hKU hUZ p u hu).mpr (hQ p hp u hu))

@[expose] noncomputable def repA6 (e : KBar K ≃* A6Mod.A6) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) : A6Mod.A6 →* MulAut ↥(tildeOf Z U) :=
  (repKBar hKZ hKU hQ hUZ).comp e.symm.toMonoidHom

omit [Finite G] in
theorem repA6_mk (e : KBar K ≃* A6Mod.A6) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) (k : ↥K) :
    repA6 e hKZ hKU hQ hUZ (e (QuotientGroup.mk k)) = secRho hKZ hKU k := by
  unfold repA6 repKBar
  simp

omit [Finite G] in
theorem exists_repA6_eq (e : KBar K ≃* A6Mod.A6) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) (g : A6Mod.A6) :
    ∃ k : ↥K, e (QuotientGroup.mk k) = g ∧ repA6 e hKZ hKU hQ hUZ g = secRho hKZ hKU k := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm g)
  refine ⟨k, by rw [hk]; simp, ?_⟩
  have : e (QuotientGroup.mk k) = g := by rw [hk]; simp
  rw [← this]
  exact repA6_mk e hKZ hKU hQ hUZ k

omit [Finite G] in
theorem inv_modSub (e : KBar K ≃* A6Mod.A6) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) {X : Subgroup G}
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) :
    A6Mod.Inv (repA6 e hKZ hKU hQ hUZ) (modSub Z U X) := by
  intro g v hv
  obtain ⟨k, -, hk⟩ := exists_repA6_eq e hKZ hKU hQ hUZ g
  rw [hk]
  have h1 : ((secRho hKZ hKU k v : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) ∈
      tildeOf Z X := by
    rw [secRho_coe]
    exact secMk_conj_mem_secImg (a := Subgroup.inclusion hKZ k) (hKX k.2)
      (show (v : SecQuot (Subgroup.normalizer (Z : Set G)) Z) ∈ tildeOf Z X from hv)
  exact h1

@[expose] noncomputable def twistAut (hsZ : s ∈ Subgroup.normalizer (Z : Set G))
    (hsU : s ∈ Subgroup.normalizer (U : Set G)) : MulAut ↥(tildeOf Z U) :=
  secRho (X := Subgroup.zpowers s) (Subgroup.zpowers_le.mpr hsZ) (Subgroup.zpowers_le.mpr hsU)
    ⟨s, Subgroup.mem_zpowers s⟩

omit [Finite G] in
theorem twistAut_coe (hsZ : s ∈ Subgroup.normalizer (Z : Set G))
    (hsU : s ∈ Subgroup.normalizer (U : Set G)) (w : ↥(tildeOf Z U)) :
    ((twistAut hsZ hsU w : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨s, hsZ⟩ * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨s, hsZ⟩)⁻¹ := by
  unfold twistAut
  rw [secRho_coe]
  rfl

@[expose] noncomputable def sigmaA6 (e : KBar K ≃* A6Mod.A6) (hsK : s ∈ Subgroup.normalizer (K : Set G)) :
    MulAut A6Mod.A6 :=
  e.symm.trans ((kbarActHom K ⟨s, hsK⟩).trans e)

theorem twistAut_rel (e : KBar K ≃* A6Mod.A6) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) (hsZ : s ∈ Subgroup.normalizer (Z : Set G))
    (hsU : s ∈ Subgroup.normalizer (U : Set G)) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (g : A6Mod.A6) :
    twistAut hsZ hsU * repA6 e hKZ hKU hQ hUZ g * (twistAut hsZ hsU)⁻¹ =
      repA6 e hKZ hKU hQ hUZ (sigmaA6 e hsK g) := by
  obtain ⟨k, hk1, hk2⟩ := exists_repA6_eq e hKZ hKU hQ hUZ g
  have hσ : sigmaA6 e hsK g = e (QuotientGroup.mk (conjAutOn K s hsK k)) := by
    rw [← hk1]
    simp only [sigmaA6, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [kbarActHom_mk]
  rw [hσ, repA6_mk, hk2]
  have key : ∀ w : ↥(tildeOf Z U),
      twistAut hsZ hsU (secRho hKZ hKU k w) = secRho hKZ hKU (conjAutOn K s hsK k) (twistAut hsZ hsU w) := by
    intro w
    apply Subtype.ext
    rw [twistAut_coe, secRho_coe, secRho_coe, twistAut_coe]
    have hc : Subgroup.inclusion hKZ (conjAutOn K s hsK k) =
        ⟨s, hsZ⟩ * Subgroup.inclusion hKZ k * ⟨s, hsZ⟩⁻¹ := by
      apply Subtype.ext
      simp [conjAutOn_apply]
    rw [hc]
    simp only [map_mul, map_inv]
    group
  refine MulEquiv.ext fun w => ?_
  have h2 : (twistAut hsZ hsU)⁻¹ w = (twistAut hsZ hsU).symm w := rfl
  show twistAut hsZ hsU (secRho hKZ hKU k ((twistAut hsZ hsU)⁻¹ w)) = _
  rw [key, MulAut.apply_inv_self]

@[expose] def preimg (Z : Subgroup G) (Xa : Subgroup (SecQuot (Subgroup.normalizer (Z : Set G)) Z)) :
    Subgroup G :=
  (Xa.comap (secMk (Subgroup.normalizer (Z : Set G)) Z)).map (Subgroup.normalizer (Z : Set G)).subtype

omit [Finite G] in
theorem mem_preimg {Xa : Subgroup (SecQuot (Subgroup.normalizer (Z : Set G)) Z)} {g : G} :
    g ∈ preimg Z Xa ↔ ∃ h : g ∈ Subgroup.normalizer (Z : Set G),
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨g, h⟩ ∈ Xa := by
  unfold preimg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

omit [Finite G] in
theorem Z_le_preimg (Xa : Subgroup (SecQuot (Subgroup.normalizer (Z : Set G)) Z)) :
    Z ≤ preimg Z Xa := by
  intro z hz
  rw [mem_preimg]
  have hzN : z ∈ Subgroup.normalizer (Z : Set G) := Subgroup.le_normalizer hz
  exact ⟨hzN, by rw [(secMk_eq_one_iff).mpr hz]; exact Xa.one_mem⟩

omit [Finite G] in
theorem secImg_preimg (Xa : Subgroup (SecQuot (Subgroup.normalizer (Z : Set G)) Z)) :
    secImg (Subgroup.normalizer (Z : Set G)) Z (preimg Z Xa) = Xa := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
    obtain ⟨h, hx'⟩ := mem_preimg.mp hx
    exact hx'
  · intro hy
    obtain ⟨n, rfl⟩ := secMk_surjective (A := Subgroup.normalizer (Z : Set G)) (B := Z) y
    exact mem_secImg.mpr ⟨n, mem_preimg.mpr ⟨n.2, hy⟩, rfl⟩

theorem hL1_modSub (e : KBar K ≃* A6Mod.A6) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) {U₁ : Subgroup G} (hA6 : KbarIsA6 K)
    (hab : IsElemAbelian 2 U₁) (hZU₁ : Z ≤ U₁) (hU₁U : U₁ ≤ U) (hgen : ⁅U₁, K⁆ ⊔ Z = U₁)
    (hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G)) :
    ∀ X : Subgroup ↥(tildeOf Z U), X ≤ modSub Z U U₁ → A6Mod.Inv (repA6 e hKZ hKU hQ hUZ) X →
      Nat.card (modSub Z U U₁) < 16 * Nat.card X → X = modSub Z U U₁ := by
  intro X hXV hXinv hcard
  set Xa : Subgroup (SecQuot (Subgroup.normalizer (Z : Set G)) Z) := X.map (tildeOf Z U).subtype
    with hXa
  set W : Subgroup G := preimg Z Xa with hW
  have hZW : Z ≤ W := Z_le_preimg Xa
  have hXaU₁ : Xa ≤ tildeOf Z U₁ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact hXV hx
  have hWU₁ : W ≤ U₁ := by
    intro g hg
    obtain ⟨hgN, hgX⟩ := mem_preimg.mp hg
    exact (secMk_mem_secImg_iff hZU₁).mp (hXaU₁ hgX)
  have hconj : ∀ k ∈ K, ∀ h ∈ W, k * h * k⁻¹ ∈ W := by
    intro k hk h hh
    obtain ⟨hhN, hhX⟩ := mem_preimg.mp hh
    obtain ⟨x, hx, hxh⟩ := Subgroup.mem_map.mp hhX
    obtain ⟨g, -, hg⟩ := exists_repA6_eq e hKZ hKU hQ hUZ
      (e (QuotientGroup.mk (⟨k, hk⟩ : ↥K)))
    have hinv := hXinv (e (QuotientGroup.mk (⟨k, hk⟩ : ↥K))) x hx
    rw [repA6_mk] at hinv
    have hkN : k ∈ Subgroup.normalizer (Z : Set G) := hKZ hk
    have hkhN : k * h * k⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN hhN) (Subgroup.inv_mem _ hkN)
    refine mem_preimg.mpr ⟨hkhN, ?_⟩
    have hval : ((secRho hKZ hKU ⟨k, hk⟩ x : ↥(tildeOf Z U)) :
        SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨k * h * k⁻¹, hkhN⟩ := by
      rw [secRho_coe]
      have : (x : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
          secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hhN⟩ := hxh
      rw [this]
      simp only [← map_inv, ← map_mul]
      rfl
    rw [← hval]
    exact Subgroup.mem_map.mpr ⟨_, hinv, rfl⟩
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj k hk h, fun hh => ?_⟩
    have := hconj k⁻¹ (Subgroup.inv_mem _ hk) _ hh
    simpa [mul_assoc] using this
  have hQ₁ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Z := fun p hp w hw => hQ p hp w (hU₁U hw)
  have hrel : W.relIndex U₁ < 16 := by
    have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := W) (H := U₁)
      hZW hWU₁ (hU₁U.trans hUZ)
    rw [secImg_preimg] at h1
    have h2 : (modSub Z U U₁).map (tildeOf Z U).subtype = tildeOf Z U₁ :=
      Subgroup.map_subgroupOf_eq_of_le (secImg_mono hU₁U)
    have h3 : Xa.relIndex (tildeOf Z U₁) = X.relIndex (modSub Z U U₁) := by
      rw [← h2, hXa]
      exact Subgroup.relIndex_map_map_of_injective _ _ (Subgroup.subtype_injective _)
    have h4 := Subgroup.relIndex_mul_card (H := X) (K := modSub Z U U₁)
    rw [inf_of_le_left hXV] at h4
    rw [← h1]
    show Xa.relIndex (tildeOf Z U₁) < 16
    rw [h3]
    by_contra hge
    push Not at hge
    have : 16 * Nat.card X ≤ X.relIndex (modSub Z U U₁) * Nat.card X :=
      Nat.mul_le_mul_right _ hge
    omega
  have hWeq := eq_of_relIndex_lt_sixteen hA6 hab hZW hWU₁ hgen hKU₁ hKW hQ₁ hrel
  have hXaeq : Xa = tildeOf Z U₁ := by
    have := secImg_preimg Xa
    rw [← this, ← hW, hWeq]
    rfl
  have h2 : (modSub Z U U₁).map (tildeOf Z U).subtype = tildeOf Z U₁ :=
    Subgroup.map_subgroupOf_eq_of_le (secImg_mono hU₁U)
  exact Subgroup.map_injective (Subgroup.subtype_injective _) (by rw [← hXa, hXaeq, h2])

omit [Finite G] in
theorem modSub_conjSub (hsZ : s ∈ Subgroup.normalizer (Z : Set G))
    (hsU : s ∈ Subgroup.normalizer (U : Set G)) {X : Subgroup G} :
    modSub Z U (conjSub s X) = (modSub Z U X).map (twistAut hsZ hsU).toMonoidHom := by
  ext v
  rw [Subgroup.mem_map_equiv, mem_modSub, mem_modSub]
  obtain ⟨w, rfl⟩ := (twistAut hsZ hsU).surjective v
  rw [MulEquiv.symm_apply_apply]
  have hcoe := twistAut_coe hsZ hsU w
  constructor
  · intro h
    obtain ⟨n, hn, hnv⟩ := mem_secImg.mp h
    have hn' : s⁻¹ * (n : G) * s ∈ X := mem_conjSub.mp hn
    have hmN : s⁻¹ * (n : G) * s ∈ Subgroup.normalizer (Z : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsZ) n.2) hsZ
    have : (w : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨s⁻¹ * (n : G) * s, hmN⟩ := by
      have h1 : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨s⁻¹ * (n : G) * s, hmN⟩ =
          (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨s, hsZ⟩)⁻¹ *
            secMk (Subgroup.normalizer (Z : Set G)) Z n *
              secMk (Subgroup.normalizer (Z : Set G)) Z ⟨s, hsZ⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h1, hnv, hcoe]
      group
    rw [this]
    exact secMk_mem_secImg hn'
  · intro h
    obtain ⟨m, hm, hmw⟩ := mem_secImg.mp h
    have hnN : s * (m : G) * s⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hsZ m.2) (Subgroup.inv_mem _ hsZ)
    have hn : s * (m : G) * s⁻¹ ∈ conjSub s X := by
      rw [mem_conjSub]
      simpa [mul_assoc] using hm
    have : ((twistAut hsZ hsU w : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨s * (m : G) * s⁻¹, hnN⟩ := by
      rw [hcoe, ← hmw]
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact secMk_mem_secImg hn

omit [Finite G] in
theorem exists_not_fix (e : KBar K ≃* A6Mod.A6) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) {X : Subgroup G} (hXU : X ≤ U)
    (hnc : ∃ x ∈ K, ∃ w ∈ X, x * w * x⁻¹ * w⁻¹ ∉ Z) :
    ∃ g : A6Mod.A6, ∃ v ∈ modSub Z U X, repA6 e hKZ hKU hQ hUZ g v ≠ v := by
  obtain ⟨x, hx, w, hw, hne⟩ := hnc
  refine ⟨e (QuotientGroup.mk (⟨x, hx⟩ : ↥K)), tildeElt hUZ w (hXU hw), secMk_mem_secImg hw, ?_⟩
  rw [repA6_mk]
  intro h
  exact hne ((secRho_apply_tildeElt_iff hKZ hKU hUZ ⟨x, hx⟩ w (hXU hw)).mp h)

theorem core_lattice (hA6 : KbarIsA6 K) {U₁ U₂ Yg : Subgroup G}
    (hel : IsElemAbelian 2 U) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (hZU₁ : Z ≤ U₁) (hU₁U : U₁ ≤ U) (hZU₂ : Z ≤ U₂) (hU₂U : U₂ ≤ U)
    (hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G)) (hgen : ⁅U₁, K⁆ ⊔ Z = U₁)
    (hZ16 : Z.relIndex U₁ = 16 ∨ Z.relIndex U₁ = 32)
    (hnc₁ : ∃ x ∈ K, ∃ w ∈ U₁, x * w * x⁻¹ * w⁻¹ ∉ Z)
    (hsZ : s ∈ Subgroup.normalizer (Z : Set G)) (hsU : s ∈ Subgroup.normalizer (U : Set G))
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hconj : U₂ = conjSub s U₁)
    (hfuse : KbarFusesThrees K s)
    (hZY : Z ≤ Yg) (hYU : Yg ≤ U) (hKY : K ≤ Subgroup.normalizer (Yg : Set G))
    (hYle : Yg ≤ U₁ ⊔ U₂) (hYcard : Z.relIndex Yg = Z.relIndex U₁)
    (hncY : ∃ x ∈ K, ∃ w ∈ Yg, x * w * x⁻¹ * w⁻¹ ∉ Z) :
    U₁ ≠ U₂ ∧ (Yg = U₁ ∨ Yg = U₂) := by
  obtain ⟨e⟩ := hA6
  have hA6' : KbarIsA6 K := ⟨e⟩
  have hel' := isElemAbelian_tilde_of (Z := Z) hel
  have hcomm : ∀ a b : ↥(tildeOf Z U), a * b = b * a := fun a b =>
    Subtype.ext (isElemAbelian_comm hel' a.2 b.2)
  have hsq : ∀ a : ↥(tildeOf Z U), a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel' a.2)
  have hτ := twistAut_rel e hKZ hKU hQ hUZ hsZ hsU hsK
  obtain ⟨x, hxK, hx3, hxQ, hxfuse⟩ := hfuse
  let q : ↥K →* KBar K := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)
  have hx3' : (e (q ⟨x, hxK⟩)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨x, hxK⟩ : ↥K) ^ 3 ∈ (pCoreOf 2 K).subgroupOf K := hx3
    have h1 : q ((⟨x, hxK⟩ : ↥K) ^ 3) = 1 :=
      (QuotientGroup.eq_one_iff (N := (pCoreOf 2 K).subgroupOf K) _).mpr this
    rw [h1, map_one]
  have hx1' : e (q ⟨x, hxK⟩) ≠ 1 := by
    intro h
    have h1 : q ⟨x, hxK⟩ = 1 := e.injective (h.trans (map_one e).symm)
    exact hxQ ((QuotientGroup.eq_one_iff (N := (pCoreOf 2 K).subgroupOf K) _).mp h1)
  have hnc' : ∀ k' : A6Mod.A6, k' * e (q ⟨x, hxK⟩) * k'⁻¹ ≠
      sigmaA6 e hsK (e (q ⟨x, hxK⟩)) := by
    intro k' hk'
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm k')
    have hk'e : k' = e (QuotientGroup.mk k) := by rw [hk]; simp
    have hσ : sigmaA6 e hsK (e (q ⟨x, hxK⟩)) =
        e (QuotientGroup.mk (conjAutOn K s hsK ⟨x, hxK⟩)) := by
      simp only [sigmaA6, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact congrArg e (kbarActHom_mk K ⟨s, hsK⟩ ⟨x, hxK⟩)
    rw [hσ, hk'e, ← map_inv, ← map_mul, ← map_mul] at hk'
    have h1 := e.injective hk'
    have h1' : (↑k * ↑(⟨x, hxK⟩ : ↥K) * (↑k)⁻¹ : ↥K ⧸ (pCoreOf 2 K).subgroupOf K) =
        ↑(conjAutOn K s hsK ⟨x, hxK⟩) := h1
    have h2 : (↑(k * (⟨x, hxK⟩ : ↥K) * k⁻¹) : ↥K ⧸ (pCoreOf 2 K).subgroupOf K) =
        ↑(conjAutOn K s hsK ⟨x, hxK⟩) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact h1'
    have h3 := QuotientGroup.eq.mp h2
    apply hxfuse (k : G) k.2
    have h4 := Subgroup.mem_subgroupOf.mp h3
    simpa [conjAutOn_apply] using h4
  have hab₁ : IsElemAbelian 2 U₁ := isElemAbelian_two_of_le hel hU₁U
  have hinvV₁ : A6Mod.Inv (repA6 e hKZ hKU hQ hUZ) (modSub Z U U₁) :=
    inv_modSub e hKZ hKU hQ hUZ hKU₁
  have hinvY : A6Mod.Inv (repA6 e hKZ hKU hQ hUZ) (modSub Z U Yg) :=
    inv_modSub e hKZ hKU hQ hUZ hKY
  have hcard : Nat.card (modSub Z U U₁) = 16 ∨ Nat.card (modSub Z U U₁) = 32 := by
    rw [card_modSub hZU₁ hU₁U hUZ]; exact hZ16
  have hYcard' : Nat.card (modSub Z U Yg) = Nat.card (modSub Z U U₁) := by
    rw [card_modSub hZY hYU hUZ, card_modSub hZU₁ hU₁U hUZ]; exact hYcard
  have hnt₁ := exists_not_fix e hKZ hKU hQ hUZ hU₁U hnc₁
  have hntY := exists_not_fix e hKZ hKU hQ hUZ hYU hncY
  have hL1 := hL1_modSub e hKZ hKU hQ hUZ hA6' hab₁ hZU₁ hU₁U hgen hKU₁
  have hV₂ : (modSub Z U U₁).map (twistAut hsZ hsU).toMonoidHom = modSub Z U U₂ := by
    rw [← modSub_conjSub hsZ hsU, hconj]
  have hYle' : modSub Z U Yg ≤ modSub Z U U₁ ⊔ (modSub Z U U₁).map (twistAut hsZ hsU).toMonoidHom := by
    rw [hV₂, ← modSub_sup hU₁U hU₂U hUZ]
    exact modSub_mono hYle
  obtain ⟨hne, hY⟩ := A6Mod.lattice_two hcomm hsq (repA6 e hKZ hKU hQ hUZ) hτ hx3' hx1' hnc'
    hinvV₁ hinvY hcard hYcard' hnt₁ hntY hL1 hYle'
  refine ⟨?_, ?_⟩
  · intro h
    apply hne
    rw [hV₂, h]
  · rcases hY with h | h
    · left
      exact modSub_injective hZY hZU₁ hYU hU₁U hUZ h
    · right
      rw [hV₂] at h
      exact modSub_injective hZY hZU₂ hYU hU₂U hUZ h

end Act

section Orbit

variable {G : Type} [Group G]

theorem relIndex_normalizer_eq_two (T U₁ U₂ : Subgroup G) (hne : U₁ ≠ U₂)
    (hs : ∃ s ∈ T, conjSub s U₁ = U₂)
    (hall : ∀ t ∈ T, conjSub t U₁ = U₁ ∨ conjSub t U₁ = U₂) :
    (T ⊓ Subgroup.normalizer (U₁ : Set G)).relIndex T = 2 := by
  classical
  let act : MulAction ↥T (Subgroup G) :=
    { smul := fun t X => conjSub (t : G) X
      one_smul := fun X => conjSub_one X
      mul_smul := fun a b X => conjSub_mul (a : G) (b : G) X }
  have hsmul : ∀ (t : ↥T) (X : Subgroup G), t • X = conjSub (t : G) X := fun t X => rfl
  have hstab : (T ⊓ Subgroup.normalizer (U₁ : Set G)).subgroupOf T = MulAction.stabilizer ↥T U₁ := by
    ext t
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, hsmul]
    constructor
    · intro h
      exact conjSub_eq_of_mem_normalizer h.2
    · intro h
      exact ⟨t.2, mem_normalizer_of_conjSub_eq h⟩
  have horb : MulAction.orbit ↥T U₁ = {U₁, U₂} := by
    ext X
    constructor
    · rintro ⟨t, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      show t • U₁ = U₁ ∨ t • U₁ = U₂
      rw [hsmul]
      exact hall t t.2
    · rintro (rfl | rfl)
      · exact ⟨1, one_smul _ _⟩
      · obtain ⟨s, hsT, hsU⟩ := hs
        exact ⟨⟨s, hsT⟩, by show (⟨s, hsT⟩ : ↥T) • U₁ = X; rw [hsmul]; exact hsU⟩
  unfold Subgroup.relIndex
  rw [hstab, MulAction.index_stabilizer, horb]
  exact Set.ncard_pair hne

end Orbit

section Final

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_two_pow {Z U₁ : Subgroup G} (hab : IsElemAbelian 2 U₁) {n : ℕ}
    (h : mIdx U₁ Z = n) : Z.relIndex U₁ = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥U₁ := fun g => ⟨1, by
    have := hab.2 g.1 g.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have hdvd := Subgroup.relIndex_dvd_card Z U₁
  rw [ha] at hdvd
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h5' : padicValNat 2 (Z.relIndex U₁) = n := h
  rw [hb, padicValNat.prime_pow] at h5'
  rw [hb, h5']

omit [Finite G] in
theorem conjSub_hyps {Z U U₁ K : Subgroup G} {t : G} (htZ : t ∈ Subgroup.normalizer (Z : Set G))
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (htK : t ∈ Subgroup.normalizer (K : Set G))
    (hZU₁ : Z ≤ U₁) (hU₁U : U₁ ≤ U) (hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G)) :
    Z ≤ conjSub t U₁ ∧ conjSub t U₁ ≤ U ∧ K ≤ Subgroup.normalizer (conjSub t U₁ : Set G) ∧
      Z.relIndex (conjSub t U₁) = Z.relIndex U₁ := by
  have hZ : conjSub t Z = Z := conjSub_eq_of_mem_normalizer htZ
  have hU : conjSub t U = U := conjSub_eq_of_mem_normalizer htU
  refine ⟨?_, ?_, le_normalizer_conjSub htK hKU₁, ?_⟩
  · calc Z = conjSub t Z := hZ.symm
      _ ≤ conjSub t U₁ := conjSub_mono t hZU₁
  · calc conjSub t U₁ ≤ conjSub t U := conjSub_mono t hU₁U
      _ = U := hU
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t).toMonoidHom) Z U₁
      (MulAut.conj t).injective
    have hZ' : Z.map (MulAut.conj t).toMonoidHom = Z := hZ
    rw [hZ'] at h
    exact h

omit [Finite G] in
theorem conjSub_commutator_sup_eq {Z U K : Subgroup G} {t : G}
    (htZ : t ∈ Subgroup.normalizer (Z : Set G)) (htU : t ∈ Subgroup.normalizer (U : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) :
    conjSub t (⁅U, K⁆ ⊔ Z) = ⁅U, K⁆ ⊔ Z := by
  rw [conjSub_sup, ← conjSub_commutator, conjSub_eq_of_mem_normalizer htU,
    conjSub_eq_of_mem_normalizer htK, conjSub_eq_of_mem_normalizer htZ]

end Final

theorem a6Index_proof : A6Index := by
  intro G _ _ T M S hB K U₁ U₂ s u hctx hA
  have hctx' := hctx
  obtain ⟨_c19, _c20, _c23, hK, c21, _c22, hdec, hch⟩ := hctx'
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rcases c21 with ⟨hper, -⟩ | ⟨-, hL3⟩ | ⟨-, -, -, -, -, -, hL3, -⟩
    · rw [← hper]
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
  obtain ⟨huU, hunc, hN⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T ∧
      T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u := by
    rcases hch with ⟨-, huU, hunc, hN⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
    · exact ⟨huU, hunc, hN⟩
    · exact absurd (hKn (hTH ht)) htn
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  obtain ⟨hU₁U, hU₂U⟩ := le_U_of_decomp hK hdec
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hU₁U huU)
  have hnc : ∃ x ∈ K, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hcon
    push Not at hcon
    exact hunc (commutator_zpowers_le_of_forall (fun k hk => S.normalizer_Z.ge (hKG hk))
      (fun z hz => S146T.comm_Z huG hz) hcon)
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUZ : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hG
  have hTZ : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun t ht =>
    S.normalizer_Z.ge (hTH ht)
  have hTU : T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun t ht =>
    le_normalizer_conjClosure _ _ (hTH ht)
  have hKZ : K ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun k hk =>
    S.normalizer_Z.ge (hKG hk)
  have hKU : K ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
    hKG.trans (le_normalizer_conjClosure _ _)
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  have hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ uOfL22 T M,
      p * w * p⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T := fun p hp w hw =>
    S.comm_mem_Z hG hw (hQK hp)
  have hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G) := S.le_normalizer_U₁_of_decomp hK hdec
  have hab₁ : IsElemAbelian 2 U₁ := isElemAbelian_two_of_le hUab hU₁U
  obtain ⟨hgen, hZ16⟩ : ⁅U₁, K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ∧
      ((quasithinOmegaOneCenter T).relIndex U₁ = 16 ∨
        (quasithinOmegaOneCenter T).relIndex U₁ = 32) := by
    rcases hdec.natural with ⟨hL3, -, -⟩ | ⟨-, hnat⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
    · rcases hnat with ⟨h4, -, hg⟩ | ⟨h5, hg⟩
      · exact ⟨hg, Or.inl (by rw [relIndex_eq_two_pow hab₁ h4]; norm_num)⟩
      · exact ⟨hg, Or.inr (by rw [relIndex_eq_two_pow hab₁ h5]; norm_num)⟩
  have hfuse : KbarFusesThrees K s := by
    rcases hdec.dynkin with ⟨hL3, -⟩ | ⟨-, hf⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
    · exact hf
  have hsT : s ∈ T := hdec.mem.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hdec.mem.2
  have hnc₁ : ∃ x ∈ K, ∃ w ∈ U₁, x * w * x⁻¹ * w⁻¹ ∉ quasithinOmegaOneCenter T := by
    obtain ⟨x, hx, hxn⟩ := hnc
    exact ⟨x, hx, u, huU, hxn⟩
  have hlat : ∀ Yg : Subgroup G, quasithinOmegaOneCenter T ≤ Yg → Yg ≤ uOfL22 T M →
      K ≤ Subgroup.normalizer (Yg : Set G) → Yg ≤ U₁ ⊔ U₂ →
      (quasithinOmegaOneCenter T).relIndex Yg = (quasithinOmegaOneCenter T).relIndex U₁ →
      (∃ x ∈ K, ∃ w ∈ Yg, x * w * x⁻¹ * w⁻¹ ∉ quasithinOmegaOneCenter T) →
      U₁ ≠ U₂ ∧ (Yg = U₁ ∨ Yg = U₂) := fun Yg hZY hYU hKY hYle hYcard hncY =>
    core_lattice hA hUab hKZ hKU hQ hUZ hdec.Z₁ hU₁U hdec.Z₂ hU₂U hKU₁ hgen hZ16 hnc₁
      (hTZ hsT) (hTU hsT) hsK hdec.conj hfuse hZY hYU hKY hYle hYcard hncY
  have hne : U₁ ≠ U₂ := (hlat U₁ hdec.Z₁ hU₁U hKU₁ le_sup_left rfl hnc₁).1
  have hall : ∀ t ∈ T, conjSub t U₁ = U₁ ∨ conjSub t U₁ = U₂ := by
    intro t ht
    have htK : t ∈ Subgroup.normalizer (K : Set G) := hKn (hTH ht)
    obtain ⟨hZY, hYU, hKY, hYcard⟩ := conjSub_hyps (hTZ ht) (hTU ht) htK hdec.Z₁ hU₁U hKU₁
    have hYle : conjSub t U₁ ≤ U₁ ⊔ U₂ := by
      have h1 : U₁ ≤ ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T := by
        rw [hdec.sup]
        exact le_sup_left
      calc conjSub t U₁ ≤ conjSub t (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T) :=
            conjSub_mono t h1
        _ = ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T :=
            conjSub_commutator_sup_eq (hTZ ht) (hTU ht) htK
        _ = U₁ ⊔ U₂ := hdec.sup
    have hncY : ∃ x ∈ K, ∃ w ∈ conjSub t U₁, x * w * x⁻¹ * w⁻¹ ∉ quasithinOmegaOneCenter T := by
      obtain ⟨x, hxK, hxn⟩ := hnc
      refine ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK x).mp hxK, t * u * t⁻¹,
        mul_mem_conjSub huU, fun hmem => hxn ?_⟩
      have e : t * x * t⁻¹ * (t * u * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * u * t⁻¹)⁻¹ =
          t * (x * u * x⁻¹ * u⁻¹) * t⁻¹ := by group
      rw [e] at hmem
      exact (Subgroup.mem_normalizer_iff.mp (hTZ ht) _).mpr hmem
    exact (hlat _ hZY hYU hKY hYle hYcard hncY).2
  have hCN := S.centralizerMod_le_normalizer_U₁ a6CoverGen_proof hK hdec hKn huU hnc
  have htz : tZero T u = T ⊓ Subgroup.normalizer (U₁ : Set G) :=
    le_antisymm (fun x hx => ⟨S146T.tZero_le T u hx,
      hCN ⟨hTH (S146T.tZero_le T u hx), hx.2.1, hx.2.2⟩⟩) hN
  rw [htz]
  exact relIndex_normalizer_eq_two T U₁ U₂ hne ⟨s, hsT, hdec.conj.symm⟩ hall

theorem input14624U1_proof : Input14624U1 :=
  input14624U1_of_gen_index a6CoverGen_proof a6Index_proof

theorem input14624U3_proof : Input14624U3 :=
  input14624U3_of_gen_index a6CoverGen_proof a6Index_proof

end CFSG.Quasithin
