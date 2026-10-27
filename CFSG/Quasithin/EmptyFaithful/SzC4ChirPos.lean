module

public import CFSG.Quasithin.EmptyFaithful.A38c10MSa
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.FLc
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def PP (L : Subgroup G) (α : ↥L →* SLt 4) (Pbar : Subgroup (SLt 4)) : Subgroup G :=
  Subgroup.map L.subtype (Pbar.comap α)

theorem mem_PP {L : Subgroup G} {α : ↥L →* SLt 4} {Pbar : Subgroup (SLt 4)} {x : G} :
    x ∈ PP L α Pbar ↔ ∃ h : x ∈ L, α ⟨x, h⟩ ∈ Pbar := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem PP_le {L : Subgroup G} {α : ↥L →* SLt 4} {Pbar : Subgroup (SLt 4)} :
    PP L α Pbar ≤ L := fun _ hx => (mem_PP.1 hx).1

structure ParabData (Pbar Rbar : Subgroup (SLt 4)) (gb : SLt 4) : Prop where
  R_le : Rbar ≤ Pbar
  R_norm : ∀ x ∈ Pbar, ∀ r ∈ Rbar, x * r * x⁻¹ ∈ Rbar
  R_two : IsPGroup 2 ↥Rbar
  max : ∀ N : Subgroup (SLt 4), N ≤ Pbar → (∀ x ∈ Pbar, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
    IsPGroup 2 ↥N → N ≤ Rbar
  gb_mem : gb ∈ Pbar
  gb_pow : gb ^ 7 = 1
  comm : ⁅Rbar, Subgroup.zpowers gb⁆ = Rbar

theorem ParabData.gb_normalizes {Pbar Rbar : Subgroup (SLt 4)} {gb : SLt 4}
    (hPD : ParabData Pbar Rbar gb) : gb ∈ Subgroup.normalizer (Rbar : Set (SLt 4)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hPD.R_norm gb hPD.gb_mem y
  · intro hy
    have := hPD.R_norm gb⁻¹ (Pbar.inv_mem hPD.gb_mem) _ hy
    simpa [mul_assoc] using this

structure Hyp6 (L S : Subgroup G) (α : ↥L →* SLt 4) (Pbar : Subgroup (SLt 4)) : Prop where
  surj : Function.Surjective α
  ker : α.ker = CFSG.pCore 2 ↥L
  S2 : IsPGroup 2 ↥S
  SL : S ≤ Subgroup.normalizer (L : Set G)
  SP : S ≤ Subgroup.normalizer (PP L α Pbar : Set G)
  SLP : S ⊓ L ≤ PP L α Pbar
  PKS : PP L α Pbar ≤ perfectCore (PP L α Pbar) ⊔ S
  odd : ∀ x ∈ PP L α Pbar, Odd (orderOf x) → x ∈ perfectCore (PP L α Pbar)

section Positions

variable [Finite G] {L S : Subgroup G} {α : ↥L →* SLt 4} {Pbar : Subgroup (SLt 4)}

@[expose] def alphaP (L : Subgroup G) (α : ↥L →* SLt 4) (Pbar : Subgroup (SLt 4)) :
    ↥(PP L α Pbar) →* SLt 4 := α.comp (Subgroup.inclusion PP_le)

omit [Finite G] in
theorem alphaP_surj (h : Function.Surjective α) {x : SLt 4} (hx : x ∈ Pbar) :
    ∃ p : ↥(PP L α Pbar), alphaP L α Pbar p = x := by
  obtain ⟨l, hl⟩ := h x
  exact ⟨⟨l, mem_PP.2 ⟨l.2, by simpa [hl] using hx⟩⟩, hl⟩

omit [Finite G] in
theorem ker_eq_open (hker : α.ker = CFSG.pCore 2 ↥L) : α.ker = CFSG.Open.pCore 2 ↥L := by
  rw [hker]

omit [Finite G] in
theorem alpha_eq_one_iff (hker : α.ker = CFSG.pCore 2 ↥L) (y : ↥L) :
    α y = 1 ↔ (y : G) ∈ pCoreOf 2 L := by
  have hk := ker_eq_open hker
  constructor
  · intro h
    refine ⟨y, ?_, rfl⟩
    rw [← hk]
    exact h
  · rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    subst hzy'
    rw [← hk] at hz
    exact hz

omit [Finite G] in
theorem X_le_PP (hker : α.ker = CFSG.pCore 2 ↥L) (hpb : (1 : SLt 4) ∈ Pbar) :
    pCoreOf 2 L ≤ PP L α Pbar := by
  have hk := ker_eq_open hker
  rintro x ⟨y, hy, rfl⟩
  refine mem_PP.2 ⟨y.2, ?_⟩
  have : α y = 1 := by
    rw [← MonoidHom.mem_ker, hk]
    exact hy
  show α y ∈ Pbar
  rw [this]
  exact hpb

omit [Finite G] in
theorem image_le_R (h : Hyp6 L S α Pbar) {Rbar : Subgroup (SLt 4)} {gb : SLt 4}
    (hPD : ParabData Pbar Rbar gb) {E : Subgroup G} (hEP : E ≤ PP L α Pbar)
    (hnorm : ∀ x ∈ PP L α Pbar, ∀ e ∈ E, x * e * x⁻¹ ∈ E) (hE2 : ∀ e ∈ E, ∃ m : ℕ, e ^ 2 ^ m = 1) :
    ∀ e (he : e ∈ E), α ⟨e, PP_le (hEP he)⟩ ∈ Rbar := by
  set N : Subgroup (SLt 4) := Subgroup.map α (E.subgroupOf L) with hN
  have hNP : N ≤ Pbar := by
    rintro _ ⟨d, hd, rfl⟩
    exact (mem_PP.1 (hEP hd)).2
  have hNn : ∀ x ∈ Pbar, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    obtain ⟨d, hd, rfl⟩ := hn
    obtain ⟨l, hl⟩ := h.surj x
    have hlP : (l : G) ∈ PP L α Pbar := mem_PP.2 ⟨l.2, by simpa [hl] using hx⟩
    refine ⟨l * d * l⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hl]⟩
    have := hnorm l hlP d hd
    simpa [Subgroup.mem_subgroupOf] using this
  have hN2 : IsPGroup 2 ↥N := by
    intro n
    obtain ⟨d, hd, hdn⟩ := n.2
    obtain ⟨m, hm⟩ := hE2 d hd
    refine ⟨m, Subtype.ext ?_⟩
    have : ((n : SLt 4)) ^ 2 ^ m = 1 := by
      rw [← hdn, ← map_pow]
      have : d ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
      rw [this, map_one]
    simpa using this
  intro e he
  exact hPD.max N hNP hNn hN2 ⟨⟨e, PP_le (hEP he)⟩, he, rfl⟩

end Positions

section Positions2

variable [Finite G] {L S : Subgroup G} {α : ↥L →* SLt 4} {Pbar : Subgroup (SLt 4)}

omit [Finite G] in
theorem H_le_normalizer (h : Hyp6 L S α Pbar) :
    perfectCore (PP L α Pbar) ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
  sup_le (fun _ hx => Subgroup.le_normalizer (PP_le (perfectCore_le _ hx))) h.SL

omit [Finite G] in
theorem H_eq (h : Hyp6 L S α Pbar) : perfectCore (PP L α Pbar) ⊔ S = PP L α Pbar ⊔ S :=
  le_antisymm (sup_le_sup_right (perfectCore_le _) S) (sup_le h.PKS le_sup_right)

omit [Finite G] in
theorem H_inf_L (h : Hyp6 L S α Pbar) :
    (perfectCore (PP L α Pbar) ⊔ S) ⊓ L = PP L α Pbar := by
  apply le_antisymm
  · rintro x ⟨hxH, hxL⟩
    rw [H_eq h] at hxH
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left (PP L α Pbar) S h.SP
    have hx : x ∈ ((PP L α Pbar : Subgroup G) : Set G) * (S : Set G) := by
      rw [← hset]
      exact hxH
    obtain ⟨p, hp, s, hs, rfl⟩ := hx
    have hsL : s ∈ L := by
      have := L.mul_mem (L.inv_mem (PP_le hp)) hxL
      simpa [mul_assoc] using this
    have hsP := h.SLP ⟨hs, hsL⟩
    exact (PP L α Pbar).mul_mem hp hsP
  · exact fun x hx => ⟨h.PKS hx, PP_le hx⟩

theorem X_le_O (h : Hyp6 L S α Pbar) (hpb : (1 : SLt 4) ∈ Pbar) :
    pCoreOf 2 L ≤ pCoreOf 2 (perfectCore (PP L α Pbar) ⊔ S) := by
  have hXH : pCoreOf 2 L ≤ perfectCore (PP L α Pbar) ⊔ S := (X_le_PP h.ker hpb).trans h.PKS
  refine le_pCoreOf_of_le_normalizer 2 hXH ?_ (pCoreOf_isPGroup 2 L)
  refine sup_le (fun k hk => ?_) (fun s hs => normalizer_le_normalizer_pCoreOf 2 L (h.SL hs))
  exact le_normalizer_pCoreOf 2 L (PP_le (perfectCore_le _ hk))

omit [Finite G] in
theorem Q_le (h : Hyp6 L S α Pbar) :
    c134Q (perfectCore (PP L α Pbar) ⊔ S) (perfectCore (PP L α Pbar)) ≤
      pCoreOf 2 (perfectCore (PP L α Pbar) ⊔ S) ⊓ L := by
  set K := perfectCore (PP L α Pbar) with hK
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_left hl)
  refine le_inf ?_ ?_
  · refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (K ⊔ S) :=
      (Subgroup.mem_normalizer_iff.mp (hKO hl) _).mp ((pCoreOf 2 (K ⊔ S)).inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact (pCoreOf 2 (K ⊔ S)).mul_mem hx h1
  · refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have hxN : x ∈ Subgroup.normalizer (L : Set G) := H_le_normalizer h (pCoreOf_le 2 _ hx)
    have hlL : l ∈ L := PP_le (perfectCore_le _ hl)
    have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN l).mp hlL
    rw [commutatorElement_def]
    exact L.mul_mem h1 (L.inv_mem hlL)

theorem comm_X_K (h : Hyp6 L S α Pbar) (hpb : (1 : SLt 4) ∈ Pbar) {x k : G}
    (hx : x ∈ pCoreOf 2 L) (hk : k ∈ perfectCore (PP L α Pbar)) :
    k * x * k⁻¹ * x⁻¹ ∈
      c134Q (perfectCore (PP L α Pbar) ⊔ S) (perfectCore (PP L α Pbar)) ⊓ pCoreOf 2 L := by
  refine ⟨?_, ?_⟩
  · have hxO := X_le_O h hpb hx
    have := Subgroup.commutator_mem_commutator hxO hk
    have e : (k * x * k⁻¹ * x⁻¹) = (x * k * x⁻¹ * k⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ this
  · have hkN : k ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      le_normalizer_pCoreOf 2 L (PP_le (perfectCore_le _ hk))
    have h1 : k * x * k⁻¹ ∈ pCoreOf 2 L := (Subgroup.mem_normalizer_iff.mp hkN x).mp hx
    exact (pCoreOf 2 L).mul_mem h1 ((pCoreOf 2 L).inv_mem hx)

theorem alphaQ_le (h : Hyp6 L S α Pbar) {Rbar : Subgroup (SLt 4)} {gb : SLt 4}
    (hPD : ParabData Pbar Rbar gb) :
    ∀ q ∈ c134Q (perfectCore (PP L α Pbar) ⊔ S) (perfectCore (PP L α Pbar)),
      ∃ hq : q ∈ L, α ⟨q, hq⟩ ∈ Rbar := by
  set K := perfectCore (PP L α Pbar) with hK
  have hEP : pCoreOf 2 (K ⊔ S) ⊓ L ≤ PP L α Pbar := by
    rw [← H_inf_L h]
    exact inf_le_inf_right _ (pCoreOf_le 2 _)
  have hnorm : ∀ x ∈ PP L α Pbar, ∀ e ∈ pCoreOf 2 (K ⊔ S) ⊓ L,
      x * e * x⁻¹ ∈ pCoreOf 2 (K ⊔ S) ⊓ L := by
    intro x hx e he
    refine ⟨?_, ?_⟩
    · have hxH : x ∈ K ⊔ S := h.PKS hx
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (K ⊔ S) hxH) e).mp he.1
    · exact L.mul_mem (L.mul_mem (PP_le hx) he.2) (L.inv_mem (PP_le hx))
  have h2 : ∀ e ∈ pCoreOf 2 (K ⊔ S) ⊓ L, ∃ m : ℕ, e ^ 2 ^ m = 1 := by
    intro e he
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (K ⊔ S) ⟨e, he.1⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  intro q hq
  have hqE := Q_le h hq
  exact ⟨hqE.2, image_le_R h hPD hEP hnorm h2 q hqE⟩

theorem exists_lift (h : Hyp6 L S α Pbar) {Rbar : Subgroup (SLt 4)} {gb : SLt 4}
    (hPD : ParabData Pbar Rbar gb) {g : G} (hgK : g ∈ perfectCore (PP L α Pbar)) (hgL : g ∈ L)
    (hg : α ⟨g, hgL⟩ = gb) :
    ∀ r ∈ Rbar, ∃ q ∈ c134Q (perfectCore (PP L α Pbar) ⊔ S) (perfectCore (PP L α Pbar)),
      ∃ hq : q ∈ L, α ⟨q, hq⟩ = r := by
  set K := perfectCore (PP L α Pbar) with hK
  set P := PP L α Pbar with hP
  have hRle : PP L α Rbar ≤ P := by
    intro x hx
    obtain ⟨hxL, hxR⟩ := mem_PP.1 hx
    exact mem_PP.2 ⟨hxL, hPD.R_le hxR⟩
  have hRnorm : ∀ x ∈ P, ∀ y ∈ PP L α Rbar, x * y * x⁻¹ ∈ PP L α Rbar := by
    intro x hx y hy
    obtain ⟨hxL, hxP⟩ := mem_PP.1 hx
    obtain ⟨hyL, hyR⟩ := mem_PP.1 hy
    refine mem_PP.2 ⟨L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL), ?_⟩
    have : α ⟨x * y * x⁻¹, L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL)⟩ =
        α ⟨x, hxL⟩ * α ⟨y, hyL⟩ * (α ⟨x, hxL⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact hPD.R_norm _ hxP _ hyR
  have hRnormalizer : P ≤ Subgroup.normalizer (PP L α Rbar : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hRnorm x hx y
    · intro hy
      have := hRnorm x⁻¹ (P.inv_mem hx) _ hy
      simpa [mul_assoc] using this
  have hR2 : IsPGroup 2 ↥(PP L α Rbar) := by
    refine CFSG.Quasithin.A38c10.MS.isPGroup_two_of_pow fun x hx => ?_
    obtain ⟨hxL, hxR⟩ := mem_PP.1 hx
    obtain ⟨a, ha⟩ := hPD.R_two ⟨_, hxR⟩
    have h1 : α (⟨x, hxL⟩ ^ 2 ^ a) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val ha
    have hk := ker_eq_open h.ker
    have h2 : (⟨x, hxL⟩ ^ 2 ^ a : ↥L) ∈ CFSG.Open.pCore 2 ↥L := by
      rw [← hk]
      exact h1
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2) ⟨_, h2⟩
    refine ⟨a + b, ?_⟩
    have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥L) => ((y : ↥L) : G)) hb
    simpa [pow_add, pow_mul] using this
  have hRO : PP L α Rbar ≤ pCoreOf 2 (K ⊔ S) := by
    have h1 : PP L α Rbar ≤ pCoreOf 2 P := le_pCoreOf_of_le_normalizer 2 hRle hRnormalizer hR2
    refine h1.trans (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 P).trans h.PKS) ?_
      (pCoreOf_isPGroup 2 P))
    exact sup_le (fun k hk => le_normalizer_pCoreOf 2 P (perfectCore_le _ hk))
      (fun s hs => normalizer_le_normalizer_pCoreOf 2 P (h.SP hs))
  have hlift : ∀ r ∈ Rbar, ∃ p : G, ∃ hp : p ∈ L, p ∈ pCoreOf 2 (K ⊔ S) ∧ α ⟨p, hp⟩ = r := by
    intro r hr
    obtain ⟨p, hp⟩ := alphaP_surj h.surj (hPD.R_le hr)
    have hpL : (p : G) ∈ L := PP_le p.2
    have hpR : (p : G) ∈ PP L α Rbar := mem_PP.2 ⟨hpL, by
      have : alphaP L α Pbar p = α ⟨p, hpL⟩ := rfl
      rw [← this, hp]
      exact hr⟩
    exact ⟨p, hpL, hRO hpR, hp⟩
  set T : Subgroup (SLt 4) := Subgroup.map α ((c134Q (K ⊔ S) K).subgroupOf L) with hT
  have hcomm : ⁅Rbar, Subgroup.zpowers gb⁆ ≤ T := by
    refine Subgroup.commutator_le.2 fun r hr y hy => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨p, hpL, hpO, hpr⟩ := hlift r hr
    have hgm : g ^ m ∈ K := K.zpow_mem hgK m
    have hgmL : g ^ m ∈ L := L.zpow_mem hgL m
    have hcQ : ⁅p, g ^ m⁆ ∈ c134Q (K ⊔ S) K := Subgroup.commutator_mem_commutator hpO hgm
    have hcL : ⁅p, g ^ m⁆ ∈ L := by
      have := Q_le h hcQ
      exact this.2
    refine ⟨⟨⁅p, g ^ m⁆, hcL⟩, hcQ, ?_⟩
    have e1 : (⟨⁅p, g ^ m⁆, hcL⟩ : ↥L) = ⁅(⟨p, hpL⟩ : ↥L), (⟨g, hgL⟩ : ↥L) ^ m⁆ := rfl
    rw [e1, map_commutatorElement, map_zpow, hg, hpr]
  intro r hr
  have hr' : r ∈ ⁅Rbar, Subgroup.zpowers gb⁆ := by
    rw [hPD.comm]
    exact hr
  have : r ∈ T := hcomm hr'
  obtain ⟨x, hx, hxr⟩ := this
  exact ⟨x, hx, x.2, hxr⟩

end Positions2

end CFSG.Quasithin.SzC4
