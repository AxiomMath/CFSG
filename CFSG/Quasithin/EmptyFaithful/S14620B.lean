module

public import CFSG.Quasithin.Background.C2PushLift
public import CFSG.Quasithin.EmptyFaithful.S146F1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.C2Push CFSG.LieType.BorelTits

section Lift

variable {G : Type} [Group G]

theorem preimageOTwoQuot_le (X : Subgroup G) (P : Subgroup (OTwoQuot X)) :
    preimageOTwoQuot X P ≤ X := fun _ hx => (mem_preimageOTwoQuot_iff.mp hx).1

theorem pCoreOf_le_preimageOTwoQuot (X : Subgroup G) (P : Subgroup (OTwoQuot X)) :
    pCoreOf 2 X ≤ preimageOTwoQuot X P := by
  intro x hx
  have hxX : x ∈ X := pCoreOf_le 2 X hx
  refine mem_preimageOTwoQuot_iff.mpr ⟨hxX, ?_⟩
  have h1 : (QuotientGroup.mk ⟨x, hxX⟩ : OTwoQuot X) = 1 :=
    (mk_eq_one_iff_mem_pCoreOf ⟨x, hxX⟩).mpr hx
  rw [h1]
  exact P.one_mem

theorem imageOTwoQuot_preimageOTwoQuot (X : Subgroup G) (P : Subgroup (OTwoQuot X)) :
    imageOTwoQuot X (preimageOTwoQuot X P) = P := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, hxX, hxP, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact (mem_preimageOTwoQuot_iff.mp hxP).2
  · intro hu
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
    exact mem_imageOTwoQuot_iff.mpr ⟨z, z.2, mem_preimageOTwoQuot_iff.mpr ⟨z.2, hu⟩, rfl⟩

theorem le_preimageOTwoQuot_of_imageOTwoQuot_le {X A : Subgroup G} {P : Subgroup (OTwoQuot X)}
    (hAX : A ≤ X) (h : imageOTwoQuot X A ≤ P) : A ≤ preimageOTwoQuot X P := fun x hx =>
  mem_preimageOTwoQuot_iff.mpr ⟨hAX hx, h (mem_imageOTwoQuot_iff.mpr ⟨x, hAX hx, hx, rfl⟩)⟩

theorem isSolvable_preimageOTwoQuot [Finite G] {X : Subgroup G} {P : Subgroup (OTwoQuot X)}
    (hP : Group.IsSolvable ↥P) : Group.IsSolvable ↥(preimageOTwoQuot X P) := by
  set Y := preimageOTwoQuot X P with hY
  have hYX : Y ≤ X := preimageOTwoQuot_le X P
  let π : ↥Y →* OTwoQuot X :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)).comp (Subgroup.inclusion hYX)
  have hπP : ∀ y : ↥Y, π y ∈ P := fun y => (mem_preimageOTwoQuot_iff.mp y.2).2
  let g : ↥Y →* ↥P := π.codRestrict P hπP
  have hQ : Group.IsSolvable ↥((pCoreOf 2 X).subgroupOf Y) := by
    have h2 : IsPGroup 2 ↥((pCoreOf 2 X).subgroupOf Y) :=
      (pCoreOf_isPGroup 2 X).of_injective (Subgroup.subgroupOfEquivOfLe
        (pCoreOf_le_preimageOTwoQuot X P)).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe (pCoreOf_le_preimageOTwoQuot X P)).injective
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := h2.isNilpotent
    infer_instance
  refine Group.isSolvable_of_ker_le_range ((pCoreOf 2 X).subgroupOf Y).subtype g ?_
  intro y hy
  have h1 : π y = 1 := by
    have := congrArg Subtype.val ((MonoidHom.mem_ker).mp hy)
    simpa [g] using this
  have h2 : (y : G) ∈ pCoreOf 2 X := by
    have : (QuotientGroup.mk (Subgroup.inclusion hYX y) : OTwoQuot X) = 1 := h1
    exact (mk_eq_one_iff_mem_pCoreOf (Subgroup.inclusion hYX y)).mp this
  exact ⟨⟨y, h2⟩, rfl⟩

theorem solvGen_eq_of_quotient [Finite G] {T X : Subgroup G} (hTX : T ≤ X) (hQT : pCoreOf 2 X ≤ T)
    (hT2 : IsPGroup 2 ↥T) (𝒴 : Set (Subgroup (OTwoQuot X)))
    (hs : ∀ Y ∈ 𝒴, Group.IsSolvable ↥Y) (hTY : ∀ Y ∈ 𝒴, imageOTwoQuot X T ≤ Y)
    (hjoin : sSup 𝒴 ⊔ imageOTwoQuot X T = ⊤) : solvGen T X = X := by
  refine le_antisymm solvGen_le_right ?_
  have hTs : Group.IsSolvable ↥T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hT2.isNilpotent
    infer_instance
  have hTJ : T ≤ solvGen T X := le_solvGen le_rfl hTX hTs
  have hQJ : pCoreOf 2 X ≤ solvGen T X := hQT.trans hTJ
  have hY : ∀ Y ∈ 𝒴, Y ≤ imageOTwoQuot X (solvGen T X) := by
    intro Y hYmem
    have hTP : T ≤ preimageOTwoQuot X Y := le_preimageOTwoQuot_of_imageOTwoQuot_le hTX (hTY Y hYmem)
    have hP : preimageOTwoQuot X Y ≤ solvGen T X :=
      le_solvGen hTP (preimageOTwoQuot_le X Y) (isSolvable_preimageOTwoQuot (hs Y hYmem))
    calc Y = imageOTwoQuot X (preimageOTwoQuot X Y) := (imageOTwoQuot_preimageOTwoQuot X Y).symm
      _ ≤ imageOTwoQuot X (solvGen T X) := imageOTwoQuot_mono hP
  have hTi : imageOTwoQuot X T ≤ imageOTwoQuot X (solvGen T X) := imageOTwoQuot_mono hTJ
  have htop : imageOTwoQuot X (solvGen T X) = ⊤ := by
    rw [eq_top_iff, ← hjoin]
    exact sup_le (sSup_le hY) hTi
  intro x hx
  have hmem : (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot X) ∈ imageOTwoQuot X (solvGen T X) := by
    rw [htop]
    trivial
  exact mem_of_mk_mem_imageOTwoQuot hQJ hmem

theorem isSolvable_conjSub (g : G) (E : Subgroup G) (hE : Group.IsSolvable ↥E) :
    Group.IsSolvable ↥(conjSub g E) :=
  Group.isSolvable_of_surjective (f := ((MulAut.conj g).subgroupMap E).toMonoidHom)
    ((MulAut.conj g).subgroupMap E).surjective

theorem imageOTwoQuot_self_eq_top (X : Subgroup G) : imageOTwoQuot X X = ⊤ := by
  unfold imageOTwoQuot
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem isPGroup_imageOTwoQuot' {M X : Subgroup G} (hX : IsPGroup 2 ↥X) :
    IsPGroup 2 ↥(imageOTwoQuot M X) := by
  intro u
  obtain ⟨x, hxM, hxX, hu⟩ := mem_imageOTwoQuot_iff.mp u.2
  obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : OTwoQuot M) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, QuotientGroup.mk_one]
  show (u : OTwoQuot M) ^ 2 ^ k = 1
  rw [← hu]
  exact h1

theorem imageOTwoQuot_conjSub {X K : Subgroup G} {s : G} (hs : s ∈ X) :
    imageOTwoQuot X (conjSub s K) =
      conjSub (QuotientGroup.mk ⟨s, hs⟩ : OTwoQuot X) (imageOTwoQuot X K) := by
  ext u
  rw [mem_conjSub]
  constructor
  · intro hu
    obtain ⟨x, hxX, hxK, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have hx' : s⁻¹ * x * s ∈ K := mem_conjSub.mp hxK
    refine mem_imageOTwoQuot_iff.mpr
      ⟨s⁻¹ * x * s, X.mul_mem (X.mul_mem (X.inv_mem hs) hxX) hs, hx', ?_⟩
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  · intro hu
    obtain ⟨y, hyX, hyK, hy⟩ := mem_imageOTwoQuot_iff.mp hu
    refine mem_imageOTwoQuot_iff.mpr
      ⟨s * y * s⁻¹, X.mul_mem (X.mul_mem hs hyX) (X.inv_mem hs), mul_mem_conjSub hyK, ?_⟩
    have h1 : u = (QuotientGroup.mk ⟨s, hs⟩ : OTwoQuot X) * (QuotientGroup.mk ⟨y, hyX⟩) *
        (QuotientGroup.mk ⟨s, hs⟩)⁻¹ := by
      rw [hy]
      group
    rw [h1, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem le_normalizer_of_mk_mem_normalizer_imageOTwoQuot [Finite G] {X K : Subgroup G} (hK : K ∈ cComp X) {s : G}
    (hs : s ∈ X)
    (h : (QuotientGroup.mk ⟨s, hs⟩ : OTwoQuot X) ∈
      Subgroup.normalizer (imageOTwoQuot X K : Set (OTwoQuot X))) :
    s ∈ Subgroup.normalizer (K : Set G) := by
  refine le_normalizer_of_imageOTwoQuot_le_normalizer (R := Subgroup.zpowers s)
    (Subgroup.zpowers_le.mpr hs) hK ?_ (Subgroup.mem_zpowers s)
  intro u hu
  obtain ⟨x, hxX, hxz, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have : (QuotientGroup.mk ⟨x, hxX⟩ : OTwoQuot X) = (QuotientGroup.mk ⟨s, hs⟩ : OTwoQuot X) ^ k := by
    subst hk
    rw [← QuotientGroup.mk_zpow]
    rfl
  rw [this]
  exact Subgroup.zpow_mem _ h k

end Lift

section Factors

variable {Y : Type*} [Group Y] [Finite Y]

theorem conjSub_eq_or_eq_of_commuting {A B : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : IsSimpleGroup ↥A)
    (hAz : ∀ x ∈ A, (∀ y ∈ A, y * x = x * y) → x = 1)
    (hcard : Nat.card ↥A = Nat.card ↥B) {g : Y}
    (hg : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Y) : Set Y)) :
    conjSub g A = A ∨ conjSub g A = B := by
  set N : Subgroup Y := A ⊔ B with hN
  set A' : Subgroup Y := conjSub g A with hA'
  have hBc : B ≤ Subgroup.centralizer (A : Set Y) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hAB a ha b hb
  have hAc : A ≤ Subgroup.centralizer (B : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hAB a ha b hb).symm
  have hNA : N ≤ Subgroup.normalizer (A : Set Y) :=
    sup_le Subgroup.le_normalizer (hBc.trans (Subgroup.centralizer_le_normalizer _))
  have hNB : N ≤ Subgroup.normalizer (B : Set Y) :=
    sup_le (hAc.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hgN : ∀ x : Y, x ∈ N ↔ g * x * g⁻¹ ∈ N := fun x => Subgroup.mem_normalizer_iff.mp hg x
  have hgN' : ∀ x : Y, x ∈ N → g⁻¹ * x * g ∈ N := fun x hx => by
    have := (hgN (g⁻¹ * x * g)).mpr (by simpa [mul_assoc] using hx)
    exact this
  have hA'N : A' ≤ N := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ A := mem_conjSub.mp hx
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ N := (hgN _).mp (Subgroup.mem_sup_left h1)
    simpa [mul_assoc] using h2
  have hNA' : N ≤ Subgroup.normalizer (A' : Set Y) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_conjSub, mem_conjSub]
    have hn' : g⁻¹ * n * g ∈ N := hgN' n hn
    have key := Subgroup.mem_normalizer_iff.mp (hNA hn') (g⁻¹ * x * g)
    have e : (g⁻¹ * n * g) * (g⁻¹ * x * g) * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * x * n⁻¹) * g := by group
    rw [e] at key
    exact key
  have eA : ↥A ≃* ↥A' := Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  have hA'simple : IsSimpleGroup ↥A' := MulEquiv.isSimpleGroup eA.symm
  have hcardA' : Nat.card ↥A' = Nat.card ↥A := (Nat.card_congr eA.toEquiv).symm
  have hAnt : Nontrivial ↥A := hA.toNontrivial
  have hA'z : ∀ x ∈ A', (∀ y ∈ A', y * x = x * y) → x = 1 := by
    intro x hx hxc
    have hx1 : g⁻¹ * x * g ∈ A := mem_conjSub.mp hx
    have : g⁻¹ * x * g = 1 := by
      refine hAz _ hx1 fun y hy => ?_
      have hy' : g * y * g⁻¹ ∈ A' := mem_conjSub.mpr (by simpa [mul_assoc] using hy)
      have := hxc _ hy'
      calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
        _ = (g⁻¹ * x * g) * y := by group
    have h2 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h2, this]
    group
  have hA'inf : A' ≤ Subgroup.normalizer ((A' ⊓ A : Subgroup Y) : Set Y) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hNA (hA'N hx)⟩
  have hnormA : ((A' ⊓ A).subgroupOf A').Normal := Subgroup.normal_subgroupOf_of_le_normalizer hA'inf
  have hA'inf' : A' ≤ Subgroup.normalizer ((A' ⊓ B : Subgroup Y) : Set Y) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hNB (hA'N hx)⟩
  have hnormB : ((A' ⊓ B).subgroupOf A').Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hA'inf'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A' ⊓ A).subgroupOf A') with h1 | h1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A' ⊓ B).subgroupOf A') with h2 | h2
    · exfalso
      have hAA' : ∀ x, x ∈ A' → x ∈ A → x = 1 := by
        intro x hxA' hxA
        have hm : (⟨x, hxA'⟩ : ↥A') ∈ (A' ⊓ A).subgroupOf A' :=
          Subgroup.mem_subgroupOf.mpr ⟨hxA', hxA⟩
        rw [h1] at hm
        exact congrArg Subtype.val (Subgroup.mem_bot.mp hm)
      have hBA' : ∀ x, x ∈ A' → x ∈ B → x = 1 := by
        intro x hxA' hxB
        have hm : (⟨x, hxA'⟩ : ↥A') ∈ (A' ⊓ B).subgroupOf A' :=
          Subgroup.mem_subgroupOf.mpr ⟨hxA', hxB⟩
        rw [h2] at hm
        exact congrArg Subtype.val (Subgroup.mem_bot.mp hm)
      have hcomm : ∀ x ∈ A', ∀ y ∈ N, y * x = x * y := by
        intro x hx
        have hle : N ≤ Subgroup.centralizer ({x} : Set Y) := by
          refine sup_le (fun a ha => ?_) (fun b hb => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            have hc1 : x * a * x⁻¹ * a⁻¹ ∈ A' := by
              have := (Subgroup.mem_normalizer_iff.mp (hNA' (Subgroup.mem_sup_left ha)) x⁻¹).mp
                (A'.inv_mem hx)
              have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
              rw [e]
              exact A'.mul_mem hx this
            have hc2 : x * a * x⁻¹ * a⁻¹ ∈ A :=
              A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNA (hA'N hx)) a).mp ha) (A.inv_mem ha)
            have h3 := hAA' _ hc1 hc2
            have h4 : x * a = a * x := by
              calc x * a = (x * a * x⁻¹ * a⁻¹) * (a * x) := by group
                _ = a * x := by rw [h3, one_mul]
            exact h4.symm
          · rw [Subgroup.mem_centralizer_singleton_iff]
            have hc1 : x * b * x⁻¹ * b⁻¹ ∈ A' := by
              have := (Subgroup.mem_normalizer_iff.mp (hNA' (Subgroup.mem_sup_right hb)) x⁻¹).mp
                (A'.inv_mem hx)
              have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
              rw [e]
              exact A'.mul_mem hx this
            have hc2 : x * b * x⁻¹ * b⁻¹ ∈ B :=
              B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNB (hA'N hx)) b).mp hb) (B.inv_mem hb)
            have h3 := hBA' _ hc1 hc2
            have h4 : x * b = b * x := by
              calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
                _ = b * x := by rw [h3, one_mul]
            exact h4.symm
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
      have hbot : ∀ x ∈ A', x = 1 := fun x hx => hA'z x hx fun y hy => hcomm x hx y (hA'N hy)
      have hA'bot : A' = ⊥ := (Subgroup.eq_bot_iff_forall A').mpr hbot
      have hc1 : Nat.card ↥A = 1 := by
        rw [← hcardA', hA'bot]
        exact Subgroup.card_bot
      have := (Nat.card_eq_one_iff_unique.mp hc1).1
      exact not_subsingleton ↥A inferInstance
    · right
      have hle : A' ≤ B := fun x hx => ((Subgroup.subgroupOf_eq_top.mp h2) hx).2
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA', hcard])
  · left
    have hle : A' ≤ A := fun x hx => ((Subgroup.subgroupOf_eq_top.mp h1) hx).2
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA'])

end Factors

end CFSG.Quasithin
