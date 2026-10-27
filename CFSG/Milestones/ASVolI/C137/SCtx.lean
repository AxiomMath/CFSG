module

public import CFSG.Milestones.ASVolI.C137.SOff
public import CFSG.Milestones.ASVolI.C137.SFin
public import CFSG.Quasithin.H13.GoldschmidtC137L32Off

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.ASVolI.ChC
open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped commutatorElement

variable {G : Type} [Group G]

structure burnsideC137_SCtx (X T L P U : Subgroup G) (α : ↥L →* Γ) (U₁ U₂ : Subgroup G)
    (β₁ : ↥U₁ →* Multiplicative Vec) (β₂ : ↥U₂ →* Multiplicative Vec) : Prop where
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  lie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  hTP : T ≤ P
  hPX : P < X
  hmax : ∀ H : Subgroup G, P ≤ H → H ≤ X → H = P ∨ H = X
  hred : IsTwoReducedIn X U
  hUL : ⁅U, L⁆ = U
  hs : SumOfTwoNat L U α U₁ U₂ β₁ β₂
  hdyn : ∀ t ∈ T, ∃ l : ↥L, ∀ x y : ↥L, (y : G) = t * x * t⁻¹ →
      (QuotientGroup.mk y : ↥L ⧸ CFSG.pCore 2 ↥L) = QuotientGroup.mk (l * x * l⁻¹)

namespace burnsideC137_SCtx

variable [Finite G] {X T L P U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (h : burnsideC137_SCtx X T L P U α U₁ U₂ β₁ β₂)
include h

omit [Finite G] in
theorem hLX : L ≤ X := le_of_mem_cComp h.hL

theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL

omit [Finite G] in
theorem hXN : X ≤ normalizer (U : Set G) := h.hred.2.1

omit [Finite G] in
theorem hU : IsElemAbelian 2 U := h.hred.2.2.1

omit [Finite G] in
theorem hUX : U ≤ X := h.hred.1

omit [Finite G] in
theorem hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
  have h3 := Subgroup.relIndex_mul_relIndex T P X h.hTP h.hPX.le
  have h4 : 2 ∣ T.relIndex X := by
    rw [← h3]
    exact Dvd.dvd.mul_right h2 _
  exact h.hT.2.2 h4

theorem hRT : pCoreOf 2 P ≤ T :=
  pCoreOf_two_le_of_sylowIn h.hTP h.hT.2.1 h.hTodd

theorem hQR : pCoreOf 2 X ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans h.hTP)
    (h.hPX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem hRX : pCoreOf 2 P ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le

theorem hR2 : IsPGroup 2 (pCoreOf 2 P) := isPGroup_pCoreOf_two_gc P

theorem hUR : U ≤ pCoreOf 2 P := (C124.le_pCoreOf_of_reduced h.hred).trans h.hQR

theorem hOLQ : pCoreOf 2 L ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.hLX)
    (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem hOLC : pCoreOf 2 L ≤ centralizer (U : Set G) :=
  h.hOLQ.trans (C124.pCoreOf_le_centralizer h.hred)

omit [Finite G] in
theorem hLN : L ≤ normalizer (U : Set G) := h.hLX.trans h.hXN

theorem card_U : Nat.card U = 64 := burnsideC137_card_U h.hs h.hU

theorem hU1 : U ≠ ⊥ := by
  intro hb
  have h1 := h.card_U
  rw [hb, Subgroup.card_bot] at h1
  omega

theorem hVL : ⁅U, L⁆ ≠ ⊥ := by
  rw [h.hUL]
  exact h.hU1

theorem hb2102 :
    (IsSylowTwoOf (pCoreOf 2 (X ⊓ centralizer (U : Set G))) (X ⊓ centralizer (U : Set G)) ∧
      pCoreOf 2 X = pCoreOf 2 P ⊓ centralizer (U : Set G)) ∧
    (CFSG.IsQuasisimple ↥(autI h.hU L) ∨ Nat.card ↥(autI h.hU L) = 3) ∧
    quasithinGenFitting (autI h.hU X) = autI h.hU L ∧
    (baum (pCoreOf 2 P) = baum (pCoreOf 2 X) ∨
      (IsStableFF (autI h.hU X) (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P)) ∧
        ffJP (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P)) (autI h.hU X) ≤
          ffJ (autI h.hU X) ∧
        quasithinGenFitting (ffJP (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P))
          (autI h.hU X)) = autI h.hU L)) :=
  C124.B2_10_2 h.hU h.hred h.hQR h.hRT h.hT h.hLX h.hn h.hprod h.hVL
    (Or.inl (isQuasisimple_L32 h.lie))

theorem mem_cent {x : G} (hx : x ∈ X)
    (hc : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ centralizer (U : Set G)) :
    x ∈ centralizer (U : Set G) := by
  have hxN : x ∈ normalizer (U : Set G) := h.hXN hx
  have hcomm : ∀ (l : G) (hl : l ∈ L) (hlN : l ∈ normalizer (U : Set G)),
      convI h.hU ⟨x, hxN⟩ * convI h.hU ⟨l, hlN⟩ = convI h.hU ⟨l, hlN⟩ * convI h.hU ⟨x, hxN⟩ := by
    intro l hl hlN
    have hN : x * l * x⁻¹ * l⁻¹ ∈ normalizer (U : Set G) :=
      (normalizer _).mul_mem ((normalizer _).mul_mem ((normalizer _).mul_mem hxN hlN)
        ((normalizer _).inv_mem hxN)) ((normalizer _).inv_mem hlN)
    have h1 := (convI_eq_one_iff h.hU ⟨_, hN⟩).2 (hc l hl)
    have h2 : (⟨x * l * x⁻¹ * l⁻¹, hN⟩ : ↥(normalizer (U : Set G))) =
        ⟨x, hxN⟩ * ⟨l, hlN⟩ * ⟨x, hxN⟩⁻¹ * ⟨l, hlN⟩⁻¹ := Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hfs := h.hb2102.2.2.1
  have hycent : convI h.hU ⟨x, hxN⟩ ∈ centralizer
      ((quasithinGenFitting (autI h.hU X) : Subgroup (MulAut (IntMod U h.hU))) : Set _) := by
    rw [hfs, Subgroup.mem_centralizer_iff]
    intro φ hφ
    obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := (mem_autI h.hU).1 hφ
    exact (hcomm l hlL hlN).symm
  have hyL : convI h.hU ⟨x, hxN⟩ ∈ autI h.hU L := by
    rw [← hfs]
    exact centralizer_quasithinGenFitting_le (autI h.hU X) ⟨convI_mem_autI h.hU hx hxN, hycent⟩
  set a : ↥(autI h.hU L) := ⟨_, hyL⟩ with ha
  have hcent : ∀ b : ↥(autI h.hU L), a * b = b * a := by
    intro b
    apply Subtype.ext
    obtain ⟨⟨l, hlN⟩, hlL, hb⟩ := (mem_autI h.hU).1 b.2
    show convI h.hU ⟨x, hxN⟩ * (b : MulAut _) = (b : MulAut _) * convI h.hU ⟨x, hxN⟩
    rw [← hb]
    exact hcomm l hlL hlN
  have hψ : burnsideC137_ψ h.hs h.hU a = 1 := by
    apply burnsideC137_center_triv
    intro γ
    obtain ⟨b, rfl⟩ := (burnsideC137_ψ h.hs h.hU).surjective γ
    rw [← map_mul, ← map_mul, hcent b]
  have ha1 : a = 1 := (burnsideC137_ψ h.hs h.hU).injective (by rw [hψ, map_one])
  have : convI h.hU ⟨x, hxN⟩ = 1 := congrArg Subtype.val ha1
  exact (convI_eq_one_iff h.hU _).1 this

theorem exists_L {x : G} (hx : x ∈ X) : ∃ l ∈ L, l⁻¹ * x ∈ centralizer (U : Set G) := by
  obtain ⟨l₀, hl₀, t, ht, rfl⟩ := h.hprod x hx
  obtain ⟨l', hl'⟩ := h.hdyn t ht
  refine ⟨l₀ * l', L.mul_mem hl₀ l'.2, ?_⟩
  have htX : t ∈ X := h.hT.1 ht
  have hl'X : (l' : G) ∈ X := h.hLX l'.2
  have hcX : (l' : G)⁻¹ * t ∈ X := X.mul_mem (X.inv_mem hl'X) htX
  have hc : (l' : G)⁻¹ * t ∈ centralizer (U : Set G) := by
    refine h.mem_cent hcX fun y hy => ?_
    have hy' : t * y * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.hn htX) y).1 hy
    have hq := hl' ⟨y, hy⟩ ⟨_, hy'⟩ rfl
    rw [QuotientGroup.eq] at hq
    set m : G := (t * y * t⁻¹)⁻¹ * ((l' : G) * y * (l' : G)⁻¹) with hm
    have hmC : m ∈ centralizer (U : Set G) := h.hOLC ⟨_, hq, rfl⟩
    have e : (l' : G)⁻¹ * t * y * ((l' : G)⁻¹ * t)⁻¹ * y⁻¹ =
        y * ((l' : G)⁻¹ * m⁻¹ * (l' : G)⁻¹⁻¹) * y⁻¹ := by
      rw [hm]; group
    rw [e]
    exact C124.conj_mem_centralizer_of_le h.hXN (h.hLX hy)
      (C124.conj_mem_centralizer_of_le h.hXN (X.inv_mem hl'X) (Subgroup.inv_mem _ hmC))
  have : (l₀ * (l' : G))⁻¹ * (l₀ * t) = (l' : G)⁻¹ * t := by group
  rw [this]
  exact hc

theorem convI_eq {x l : G} (hx : x ∈ X) (hl : l ∈ L) (hc : l⁻¹ * x ∈ centralizer (U : Set G)) :
    convI h.hU ⟨x, h.hXN hx⟩ = convI h.hU ⟨l, h.hLN hl⟩ := by
  have hN : l⁻¹ * x ∈ normalizer (U : Set G) :=
    (normalizer _).mul_mem ((normalizer _).inv_mem (h.hLN hl)) (h.hXN hx)
  have h1 := (convI_eq_one_iff h.hU ⟨_, hN⟩).2 hc
  have h2 : (⟨l⁻¹ * x, hN⟩ : ↥(normalizer (U : Set G))) = ⟨l, h.hLN hl⟩⁻¹ * ⟨x, h.hXN hx⟩ :=
    Subtype.ext rfl
  rw [h2, map_mul, map_inv] at h1
  exact (inv_mul_eq_one.1 h1).symm

theorem autI_X : autI h.hU X = autI h.hU L := by
  refine le_antisymm (fun φ hφ => ?_) (autI_mono h.hU h.hLX)
  obtain ⟨⟨x, hxN⟩, hxX, rfl⟩ := (mem_autI h.hU).1 hφ
  obtain ⟨l, hl, hc⟩ := h.exists_L hxX
  rw [h.convI_eq hxX hl hc]
  exact convI_mem_autI h.hU hl (h.hLN hl)

theorem autR_pow {φ : MulAut (IntMod U h.hU)} (hφ : φ ∈ autI h.hU (pCoreOf 2 P)) :
    ∃ k : ℕ, φ ^ 2 ^ k = 1 := by
  obtain ⟨y, hy, rfl⟩ := (mem_autI h.hU).1 hφ
  obtain ⟨j, hj⟩ := h.hR2 ⟨(y : G), hy⟩
  refine ⟨j, ?_⟩
  have hj' : (y : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have : convI h.hU (y ^ 2 ^ j) = 1 := by
    rw [convI_eq_one_iff, Subgroup.coe_pow, hj']
    exact one_mem _
  rw [map_pow] at this
  exact this

theorem offImg (hst : IsStableFF (autI h.hU X) (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P)))
    {A : Subgroup G} (hA : IsMaxElemAbelian (pCoreOf 2 P) A) (hA1 : autI h.hU A ≠ ⊥) :
    autI h.hU A ≤ autI h.hU L ∧ ∃ S : Finset Vec, IsPlane S ∧
      (∀ a : ↥(autI h.hU L), (a : MulAut (IntMod U h.hU)) ∈ autI h.hU A ↔
        burnsideC137_ψ h.hs h.hU a ∈ BS S) ∧
      Nat.card (autI h.hU A) = 4 ∧ Nat.card (fixV (autI h.hU A)) = 16 := by
  have hmem : autI h.hU A ∈ C124.offenderImagesConjIn h.hU X (pCoreOf 2 P) :=
    ⟨hA1, A, rfl, 1, X.one_mem, by rwa [inv_one, cjSub_one_gc]⟩
  have hoff := hst.2.1 _ hmem
  have hBL : autI h.hU A ≤ autI h.hU L := h.autI_X ▸ hoff.1
  have hsq : ∀ b ∈ autI h.hU A, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact hoff.2.2.1.2 b hb
  have hc : Nat.card (IntMod U h.hU) ≤ Nat.card (autI h.hU A) * Nat.card (fixV (autI h.hU A)) := by
    have := hoff.2.2.2 ⊥ bot_le
    rw [Subgroup.card_bot, one_mul, B5.fixV_bot_eq_top, Subgroup.card_top] at this
    exact this
  exact ⟨hBL, burnsideC137_offender h.hs h.hU hBL hA1 hsq hc⟩

theorem plane_unique {A A' : Subgroup (MulAut (IntMod U h.hU))}
    (hAR : A ≤ autI h.hU (pCoreOf 2 P)) (hA'R : A' ≤ autI h.hU (pCoreOf 2 P))
    {S S' : Finset Vec} (hS : IsPlane S) (hS' : IsPlane S')
    (hAS : ∀ a : ↥(autI h.hU L), (a : MulAut (IntMod U h.hU)) ∈ A ↔
      burnsideC137_ψ h.hs h.hU a ∈ BS S)
    (hA'S : ∀ a : ↥(autI h.hU L), (a : MulAut (IntMod U h.hU)) ∈ A' ↔
      burnsideC137_ψ h.hs h.hU a ∈ BS S') : S = S' := by
  by_contra hne
  obtain ⟨a, ha, b, hb, h3⟩ := burnsideC137_BS_pair S hS S' hS' hne
  set x := (burnsideC137_ψ h.hs h.hU).symm a with hx
  set y := (burnsideC137_ψ h.hs h.hU).symm b with hy
  have hxA : (x : MulAut (IntMod U h.hU)) ∈ A := (hAS x).2 (by
    rw [hx, MulEquiv.apply_symm_apply]; exact burnsideC137_mem_BS.2 ha)
  have hyA : (y : MulAut (IntMod U h.hU)) ∈ A' := (hA'S y).2 (by
    rw [hy, MulEquiv.apply_symm_apply]; exact burnsideC137_mem_BS.2 hb)
  have hxy : ((x * y : ↥(autI h.hU L)) : MulAut (IntMod U h.hU)) ∈ autI h.hU (pCoreOf 2 P) :=
    Subgroup.mul_mem _ (hAR hxA) (hA'R hyA)
  obtain ⟨k, hk⟩ := h.autR_pow hxy
  have hk' : (x * y) ^ 2 ^ k = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hk)
  have : (a * b) ^ 2 ^ k = 1 := by
    have := congrArg (burnsideC137_ψ h.hs h.hU) hk'
    rw [map_pow, map_mul, hx, hy, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      map_one] at this
    exact this
  exact burnsideC137_not_ord3 h3 this

end burnsideC137_SCtx

end CFSG.ASVolI
