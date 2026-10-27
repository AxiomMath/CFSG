module

public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.Quasithin.Vol2.Ch10SecBInner3
public import CFSG.Quasithin.Vol2.Ch10SecDBasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem card_sup_of_comm {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXY : X ⊓ Y = ⊥) : Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  set φ : X × Y →* G := X.subtype.noncommCoprod Y.subtype
    (fun x y => show Commute (X.subtype x) (Y.subtype y) from h x x.2 y y.2) with hφ
  have hrange : φ.range = X ⊔ Y := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have h1 : (x : G) * y = 1 := hxy
    have hx : (x : G) ∈ X ⊓ Y := by
      refine ⟨x.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Y.inv_mem y.2
    rw [hXY, Subgroup.mem_bot] at hx
    have hy : (y : G) = 1 := by rw [hx, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

omit [Finite G] in
theorem exists_conj_of_l3Data {W : Subgroup G} [IsMulCommutative ↥W]
    (D : L3Data (V := ↥W) (autOn L W) ⊤ ⊥) {a b : G} (ha : a ∈ W) (hb : b ∈ W) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : ∃ l ∈ L, l * a * l⁻¹ = b := by
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hne : ∀ x : ↥(⊤ : Subgroup ↥W), ((x : ↥W) : G) ≠ 1 →
      Multiplicative.toAdd (D.β x) ≠ 0 := by
    intro x hx h0
    apply hx
    have h1 : D.β x = 1 := by
      have : D.β x = Multiplicative.ofAdd 0 := by rw [← h0]; rfl
      rw [this]; rfl
    have h2 := hβinj (h1.trans (map_one D.β).symm)
    rw [h2]
    rfl
  obtain ⟨γ, hγ⟩ := L3.act_trans _ _ (hne ⟨⟨a, ha⟩, trivial⟩ ha1) (hne ⟨⟨b, hb⟩, trivial⟩ hb1)
  have h1 := D.β_rho γ ⟨a, ha⟩ trivial trivial
  have h2 : D.β ⟨D.rho γ ⟨a, ha⟩, trivial⟩ = D.β ⟨⟨b, hb⟩, trivial⟩ := by
    rw [h1, hγ]
    rfl
  have h3 := hβinj h2
  obtain ⟨⟨l, hlN⟩, hl, hlρ⟩ := D.rho_mem γ
  refine ⟨l, Subgroup.mem_subgroupOf.mp hl, ?_⟩
  have h4 : ((D.rho γ ⟨a, ha⟩ : ↥W) : G) = b := congrArg (fun x => (x.1 : G)) h3
  rw [← hlρ, A1b.conjAct_coe] at h4
  exact h4

theorem faithful_five (h : Hyp10 G T L I) (hL32 : LBarL32 L) {s : G}
    (hsL : s ∈ Subgroup.normalizer (L : Set G)) {W : Subgroup G} (hLW : L ≤ Subgroup.normalizer
      (W : Set G)) (hsup : W ⊔ CFSG.conjugate W s = fsuUL T L I) [IsMulCommutative ↥W]
    (hnat : BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ 3 1) :
    L ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (fsuUL T L I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := hnat.toL3Coord
  set P := pCoreOf 2 L with hP
  have hLP := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hsP := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hsL
  have hCnorm : L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) :
      Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy,
      Subgroup.mem_normalizer_iff.mpr fun z => (SecB.conj_mem_centralizer_iff (hLW hy)).symm⟩
  have hne : L ⊓ Subgroup.centralizer (W : Set G) ≠ L := by
    intro heq
    obtain ⟨y, hyL, hy⟩ := SecB.mem_autOn_iff.mp (D.rho_mem L3.x12)
    have hyC : (y : G) ∈ L ⊓ Subgroup.centralizer (W : Set G) := heq.symm ▸ hyL
    have hy1 : conjAct W y = 1 := A1b.conjAct_eq_one_iff.mpr hyC.2
    have h1 : D.rho L3.x12 = D.rho 1 := by rw [← hy, hy1, map_one]
    exact L3.x12_invol.2 (D.rho_injective h1)
  have hCP := SecB.le_pCoreOf_of_normal_of_ne inf_le_left hCnorm
    (SecB.isSimpleGroup_of_LBarL32 hL32)
    (SecA.perfect_L h.fsu.maximal.1) hne
  have hWsq : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext
    ((SecA.isElemAbelian_fsuVM h).2 w (V1_le_V (hsup ▸ Subgroup.mem_sup_left w.2)))
  have hPN : P ≤ Subgroup.normalizer (W : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLW
  have hP2 : IsPGroup 2 ↥(autOn P W) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).comap_subtype.map (conjAct W)
  have hW1 : (⊤ : Subgroup ↥W) ≠ ⊥ := by
    intro h0
    have h1 : D.rho L3.x12 = 1 := by
      ext w
      have : w = 1 := by
        have hw : w ∈ (⊤ : Subgroup ↥W) := trivial
        rw [h0, Subgroup.mem_bot] at hw
        exact hw
      rw [this, map_one, MulAut.one_apply]
    exact L3.x12_invol.2 (D.rho_injective (h1.trans (map_one D.rho).symm))
  obtain ⟨w0, -, hw01, hw0fix⟩ := B1.exists_fixed_ne_one hWsq hP2 (M := ⊤) (fun _ _ _ _ => trivial)
    hW1
  have hw01' : (w0 : G) ≠ 1 := fun h1 => hw01 (Subtype.ext h1)
  have hPw0 : ∀ p ∈ P, p * (w0 : G) * p⁻¹ = w0 := by
    intro p hp
    have h1 := hw0fix _ ⟨⟨p, hPN hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    have h2 := congrArg Subtype.val h1
    rwa [A1b.conjAct_coe] at h2
  have hPW : ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ = w := by
    intro p hp w hw
    by_cases hw1 : w = 1
    · rw [hw1]; group
    obtain ⟨l, hl, hlw⟩ := exists_conj_of_l3Data D w0.2 hw hw01' hw1
    have hlp : l⁻¹ * p * l ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hLP (L.inv_mem hl)) p).mp hp
      simpa using this
    rw [← hlw]
    calc p * (l * w0 * l⁻¹) * p⁻¹ = l * ((l⁻¹ * p * l) * w0 * (l⁻¹ * p * l)⁻¹) * l⁻¹ := by group
      _ = l * w0 * l⁻¹ := by rw [hPw0 _ hlp]
  have hPWs : ∀ p ∈ P, ∀ w ∈ CFSG.conjugate W s, p * w * p⁻¹ = w := by
    intro p hp w hw
    rw [SecA.mem_conjugate_iff] at hw
    have hsp : s * p * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hsP p).mp hp
    have h1 := hPW _ hsp _ hw
    have e : s * (p * w * p⁻¹) * s⁻¹ = s * w * s⁻¹ := by
      calc s * (p * w * p⁻¹) * s⁻¹ = (s * p * s⁻¹) * (s * w * s⁻¹) * (s * p * s⁻¹)⁻¹ := by group
        _ = s * w * s⁻¹ := h1
    exact mul_left_cancel (mul_right_cancel e)
  intro x hx
  have hxP := hCP hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hle : W ⊔ CFSG.conjugate W s ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := hPW x hxP w hw
      calc w * x = x * w * x⁻¹ * x := by rw [this]
        _ = x * w := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := hPWs x hxP w hw
      calc w * x = x * w * x⁻¹ * x := by rw [this]
        _ = x * w := by group
  rw [← hsup] at hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

end CFSG.Quasithin.Vol2.Ch10.SecD
