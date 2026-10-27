module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKAct
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinD

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k j : ℕ}

structure RForm (D : StdData G T L I K m k (m + 1) j) : Prop where
  norm : ∀ r ∈ pCoreOf 2 I, ∀ z ∈ uZero I K, r * z * r⁻¹ ∈ uZero I K
  form : ∀ r ∈ pCoreOf 2 I, ∃ a : Fin (m + 1) → ZMod 2, a (Fin.last m) = 0 ∧
    ∀ z z' : G, z ∈ uZero I K → z' = r * z * r⁻¹ → ∀ i : Fin j,
      coG D z' i = coG D z i + (coG D z i (Fin.last m)) • a

theorem rForm_of (hIH : I ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hj : 0 < j)
    (D : StdData G T L I K m k (m + 1) j)
    (hRC : pCoreOf 2 I ≤ Subgroup.centralizer (vV T L : Set G)) : RForm D := by
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  refine ⟨fun r hr z hz => (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_right hr)) z).mp
    hz, fun r hr => ?_⟩
  obtain ⟨x, -, hx⟩ := exists_K_action_of_R hIH hHK (Nat.succ_pos m) hj D r hr
  have hFix : FixesA m ((D.α x : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) := by
    intro a ha
    obtain ⟨v, hvV, i, hi⟩ := D.cover (Pi.single a 1) (fun b hb => by
      have : b ≠ a := fun h => by subst h; omega
      simp [Pi.single_apply, this])
    have hvr : (v : G) * r = r * (v : G) :=
      Subgroup.mem_centralizer_iff.mp (hRC hr) (v : G) hvV
    have h := hx v v (by rw [← hvr, mul_inv_cancel_right]) i
    rw [hi] at h
    exact h.symm
  obtain ⟨a, ha, hform⟩ := fixes_std_succ_form rfl (D.α x) hFix
  refine ⟨a, ha, fun z z' hz hz' i => ?_⟩
  have hz'U : z' ∈ uZero I K := by
    rw [hz']
    exact (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_right hr)) z).mp hz
  have h := hx ⟨z, hz⟩ ⟨z', hz'U⟩ hz' i
  rw [← coG_of_mem D ⟨z', hz'U⟩, ← coG_of_mem D ⟨z, hz⟩] at h
  rw [show coG D z' i = _ from h, hform]
  rfl

section AR

variable (D : StdData G T L I K m k (m + 1) j) (hj : 0 < j)

noncomputable def zZero : G :=
  Classical.choose (exists_coG_eq D (Pi.single (⟨0, hj⟩ : Fin j)
    (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2)))

theorem zZero_mem : zZero D hj ∈ uZero I K :=
  (Classical.choose_spec (exists_coG_eq D (Pi.single (⟨0, hj⟩ : Fin j)
    (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2)))).1

theorem coG_zZero : coG D (zZero D hj) = Pi.single (⟨0, hj⟩ : Fin j)
    (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2) :=
  (Classical.choose_spec (exists_coG_eq D (Pi.single (⟨0, hj⟩ : Fin j)
    (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2)))).2

noncomputable def arOf (r : G) : Fin (m + 1) → ZMod 2 :=
  coG D (r * zZero D hj * r⁻¹) ⟨0, hj⟩ + Pi.single (Fin.last m) 1

theorem arOf_spec (F : RForm D) {r : G} (hr : r ∈ pCoreOf 2 I) :
    arOf D hj r (Fin.last m) = 0 ∧ ∀ z : G, z ∈ uZero I K → ∀ i : Fin j,
      coG D (r * z * r⁻¹) i = coG D z i + (coG D z i (Fin.last m)) • arOf D hj r := by
  obtain ⟨a, ha, hform⟩ := F.form r hr
  have hz0 := zZero_mem D hj
  have h1 := hform _ _ hz0 rfl ⟨0, hj⟩
  have harOf : arOf D hj r = a := by
    unfold arOf
    rw [h1, coG_zZero]
    funext b
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    generalize (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2) b = s
    generalize a b = c
    revert s c
    decide
  rw [harOf]
  exact ⟨ha, fun z hz i => hform z _ hz rfl i⟩

theorem arOf_mul (F : RForm D) {r₁ r₂ : G} (h₁ : r₁ ∈ pCoreOf 2 I) (h₂ : r₂ ∈ pCoreOf 2 I) :
    arOf D hj (r₁ * r₂) = arOf D hj r₁ + arOf D hj r₂ := by
  obtain ⟨h1e, h1⟩ := arOf_spec D hj F h₁
  obtain ⟨h2e, h2⟩ := arOf_spec D hj F h₂
  obtain ⟨h12e, h12⟩ := arOf_spec D hj F ((pCoreOf 2 I).mul_mem h₁ h₂)
  have hz0 := zZero_mem D hj
  have hz1 : r₂ * zZero D hj * r₂⁻¹ ∈ uZero I K := F.norm r₂ h₂ _ hz0
  have e1 := h2 _ hz0 ⟨0, hj⟩
  have e2 := h1 _ hz1 ⟨0, hj⟩
  have e3 := h12 _ hz0 ⟨0, hj⟩
  have hconj : (r₁ * r₂) * zZero D hj * (r₁ * r₂)⁻¹ =
      r₁ * (r₂ * zZero D hj * r₂⁻¹) * r₁⁻¹ := by group
  rw [hconj, e2, e1, coG_zZero] at e3
  have hsl : (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2) (Fin.last m) = 1 :=
    Pi.single_eq_same _ _
  funext b
  have e3b := congrFun e3 b
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, hsl, h2e, add_zero, smul_eq_mul,
    one_mul] at e3b ⊢
  generalize (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2) b = s0 at e3b
  generalize arOf D hj r₁ b = c1 at e3b ⊢
  generalize arOf D hj r₂ b = c2 at e3b ⊢
  generalize arOf D hj (r₁ * r₂) b = c12 at e3b ⊢
  revert s0 c1 c2 c12
  decide

theorem arOf_eq_zero_iff (F : RForm D) {r : G} (hr : r ∈ pCoreOf 2 I) :
    arOf D hj r = 0 ↔ ∀ z : G, z ∈ uZero I K → r * z * r⁻¹ = z := by
  obtain ⟨hre, hspec⟩ := arOf_spec D hj F hr
  constructor
  · intro h0 z hz
    apply coG_injOn D (F.norm r hr z hz) hz
    funext i
    rw [hspec z hz i, h0]
    simp
  · intro hfix
    have hz0 := zZero_mem D hj
    have h := hspec _ hz0 ⟨0, hj⟩
    rw [hfix _ hz0, coG_zZero] at h
    funext b
    have hb := congrFun h b
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Pi.zero_apply] at hb ⊢
    generalize (Pi.single (Fin.last m) (1 : ZMod 2) : Fin (m + 1) → ZMod 2) b = s0 at hb
    generalize arOf D hj r b = c at hb ⊢
    revert s0 c
    decide

end AR

section Centralizer

variable {n : ℕ}

theorem centralizer_uZero_le (h22 : ASC22Three G) (hc : Conf4212 G T M L I H K) (hIH : I ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hn : 0 < n) (hj : 0 < j)
    (D : StdData G T L I K m k n j) {x : G} (hx : x ∈ K ⊔ pCoreOf 2 I)
    (hfix : ∀ z ∈ uZero I K, x * z * x⁻¹ = z) : x ∈ pCoreOf 2 I := by
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    (pCoreOf_le 2 I).trans (hIH.trans hHK)
  have hOR : pCoreOf 2 (K ⊔ pCoreOf 2 I) ≤ pCoreOf 2 I :=
    C48Pf.pCoreOf_sup_le h22 hc.hypC28 hc.K_mem hRK
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  have hxmem : x ∈ (K : Set G) * (pCoreOf 2 I : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K (pCoreOf 2 I) hRK]
    exact hx
  obtain ⟨k₀, hk₀, r', hr', hxkr⟩ := Set.mem_mul.mp hxmem
  obtain ⟨x', hy, hact⟩ := exists_K_action_of_R hIH hHK hn hj D r' hr'
  set kk : ↥K := ⟨k₀, hk₀⟩ * x' with hkk
  have hr'U : ∀ z ∈ uZero I K, r' * z * r'⁻¹ ∈ uZero I K := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_right hr')) z).mp hz
  have hx'U : ∀ z ∈ uZero I K, (x' : G) * z * (x' : G)⁻¹ ∈ uZero I K := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_left x'.2)) z).mp hz
  have hsame : ∀ z ∈ uZero I K, (x' : G) * z * (x' : G)⁻¹ = r' * z * r'⁻¹ := by
    intro z hz
    apply coG_injOn D (hx'U z hz) (hr'U z hz)
    funext i
    rw [coG_conj_K D hz (hx'U z hz) i]
    have h := hact ⟨z, hz⟩ ⟨r' * z * r'⁻¹, hr'U z hz⟩ rfl i
    rw [← coG_of_mem D ⟨r' * z * r'⁻¹, hr'U z hz⟩, ← coG_of_mem D ⟨z, hz⟩] at h
    exact h.symm
  have hkkfix : ∀ z ∈ uZero I K, (kk : G) * z * (kk : G)⁻¹ = z := by
    intro z hz
    have h1 : (kk : G) * z * (kk : G)⁻¹ = k₀ * ((x' : G) * z * (x' : G)⁻¹) * k₀⁻¹ := by
      simp only [hkk, Subgroup.coe_mul]
      group
    have h2 : x * z * x⁻¹ = z := hfix z hz
    rw [h1, hsame z hz]
    calc k₀ * (r' * z * r'⁻¹) * k₀⁻¹ = (k₀ * r') * z * (k₀ * r')⁻¹ := by group
      _ = x * z * x⁻¹ := by rw [hxkr]
      _ = z := h2
  have hα1 : D.α kk = 1 := by
    have hv : ∀ v : Fin n → ZMod 2,
        ((D.α kk : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v = v := by
      intro v
      obtain ⟨z, hz, hzc⟩ := exists_coG_eq D (Pi.single (⟨0, hj⟩ : Fin j) v)
      have h := coG_conj_K D hz (by rw [hkkfix z hz]; exact hz) (⟨0, hj⟩ : Fin j)
      rw [hkkfix z hz, hzc] at h
      simpa using h.symm
    apply Units.ext
    ext a b
    have := congrFun (hv (Pi.single b 1)) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
  have hkkO : (kk : G) ∈ pCoreOf 2 K := by
    have hmem : kk ∈ CFSG.pCore 2 ↥K := by
      rw [← D.ker_eq]
      exact hα1
    rw [CFSG.Quasithin.C2A3Orbits.pCoreOf_eq_map_pCore]
    exact ⟨_, hmem, rfl⟩
  have hkkR : (kk : G) ∈ pCoreOf 2 I :=
    hOR (C48Pf.pCoreOf_le_pCoreOf_sup hRK hkkO)
  have hyR : (x' : G)⁻¹ * r' ∈ pCoreOf 2 I := hOR hy
  have hxe : x = (kk : G) * ((x' : G)⁻¹ * r') := by
    rw [← hxkr]
    simp only [hkk, Subgroup.coe_mul]
    group
  rw [hxe]
  exact (pCoreOf 2 I).mul_mem hkkR hyR

end Centralizer

section FromKerA

theorem exists_arOf_ne_zero (h22 : ASC22Three G) (hc : Conf4212 G T M L I H K) (hIH : I ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hj : 0 < j)
    (D : StdData G T L I K m k (m + 1) j) (F : RForm D)
    (hRΓ : pCoreOf 2 I ≤ gammaZero T M L I) {g : G}
    (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h3 : ∃ u ∈ uZero I K, g⁻¹ * u * g ∉ kerA (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) :
    ∃ v ∈ uZero I K, arOf D hj (g⁻¹ * v * g) ≠ 0 := by
  obtain ⟨u, hu, hnot⟩ := h3
  refine ⟨u, hu, fun h0 => hnot ?_⟩
  have hr := h1 u hu
  have hfix := (arOf_eq_zero_iff D hj F hr).mp h0
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  refine ⟨Subgroup.mem_sup_right hr, fun a ha => ?_⟩
  apply hRΓ
  refine centralizer_uZero_le h22 hc hIH hHK (Nat.succ_pos m) hj D
    ((K ⊔ pCoreOf 2 I).mul_mem ((K ⊔ pCoreOf 2 I).mul_mem ((K ⊔ pCoreOf 2 I).inv_mem ha)
      (Subgroup.mem_sup_right hr)) ha) ?_
  intro z hz
  have hz2 : a * z * a⁻¹ ∈ uZero I K := (Subgroup.mem_normalizer_iff.mp (hnormU ha) z).mp hz
  have h := hfix _ hz2
  calc a⁻¹ * (g⁻¹ * u * g) * a * z * (a⁻¹ * (g⁻¹ * u * g) * a)⁻¹
      = a⁻¹ * ((g⁻¹ * u * g) * (a * z * a⁻¹) * (g⁻¹ * u * g)⁻¹) * a := by group
    _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [h]
    _ = z := by group

theorem exists_arOf_ne_zero' (hj : 0 < j) (D : StdData G T L I K m k (m + 1) j) (F : RForm D)
    {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (hv : ∃ v ∈ uZero I K, arOf D hj (g⁻¹ * v * g) ≠ 0) :
    ∃ u ∈ uZero I K, arOf D hj (g * u * g⁻¹) ≠ 0 := by
  obtain ⟨v, hv, hne⟩ := hv
  have hr := h1 v hv
  by_contra hcon
  push Not at hcon
  apply hne
  rw [arOf_eq_zero_iff D hj F hr]
  intro z hz
  have h0 := (arOf_eq_zero_iff D hj F (h2 z hz)).mp (hcon z hz) v hv
  have hcomm : (g * z * g⁻¹) * v = v * (g * z * g⁻¹) := by
    calc (g * z * g⁻¹) * v = ((g * z * g⁻¹) * v * (g * z * g⁻¹)⁻¹) * (g * z * g⁻¹) := by group
      _ = v * (g * z * g⁻¹) := by rw [h0]
  have hc2 : (g⁻¹ * v * g) * z = z * (g⁻¹ * v * g) := by
    calc (g⁻¹ * v * g) * z = g⁻¹ * (v * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * v) * g := by rw [hcomm]
      _ = z * (g⁻¹ * v * g) := by group
  rw [mul_inv_eq_iff_eq_mul]
  exact hc2

end FromKerA

end CFSG.Quasithin.H13.Ch4.NSB
