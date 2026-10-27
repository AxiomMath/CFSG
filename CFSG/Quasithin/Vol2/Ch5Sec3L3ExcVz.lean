module

import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch5Sec3L3
public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcQ

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Fischer
  CFSG.LieType.BorelTits

section Generic

variable {G : Type} [Group G]

theorem conj_mem_zpowers {g z c : G} (hgz : g * z = z * g) (hc : c ∈ Subgroup.zpowers z) :
    g * c * g⁻¹ = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h : g * z * g⁻¹ = z := by
    rw [hgz]
    group
  rw [← conj_zpow, h]

theorem commute_of_mem_zpowers {g z c : G} (hgz : g * z = z * g)
    (hc : c ∈ Subgroup.zpowers z) : g * c = c * g := by
  have h := conj_mem_zpowers hgz hc
  calc g * c = g * c * g⁻¹ * g := by group
    _ = c * g := by rw [h]

theorem mul_self_of_mem_zpowers {z c : G} (hz : z * z = 1) (hc : c ∈ Subgroup.zpowers z) :
    c * c = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz, one_zpow]

theorem comm_eq_one_of_odd {g y z : G} (hz : z * z = 1) (hgz : g * z = z * g)
    (h : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) : g * y * g⁻¹ * y⁻¹ = 1 := by
  set c := g * y * g⁻¹ * y⁻¹ with hc
  have hcg : Commute g c := commute_of_mem_zpowers hgz h
  have hcc : c * c = 1 := mul_self_of_mem_zpowers hz h
  have h1 : g * y * g⁻¹ = c * y := by
    rw [hc]
    group
  have hk : ∀ k : ℕ, g ^ k * y * (g ^ k)⁻¹ = c ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : g * c ^ k = c ^ k * g := (hcg.pow_right k).eq
      calc g ^ (k + 1) * y * (g ^ (k + 1))⁻¹ = g * (g ^ k * y * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = (g * c ^ k) * y * g⁻¹ := by rw [ih]; group
        _ = c ^ k * (g * y * g⁻¹) := by rw [e]; group
        _ = c ^ (k + 1) * y := by rw [h1, pow_succ]; group
  have hm' := hk m
  rw [hgm, one_mul, inv_one, mul_one] at hm'
  have hcm : c ^ m = 1 := by
    have h2 := congrArg (· * y⁻¹) hm'
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h2
    exact h2.symm
  obtain ⟨j, rfl⟩ := hm
  have e : c ^ (2 * j + 1) = c := by
    rw [pow_succ, pow_mul, sq, hcc, one_pow, one_mul]
  rw [e] at hcm
  exact hcm

theorem eq_one_of_two_pow_of_odd {g : G} {k m : ℕ} (h1 : g ^ 2 ^ k = 1) (hm : Odd m)
    (h2 : g ^ m = 1) : g = 1 := by
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hd : orderOf g ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem isPGroup_two_of_odd [Finite G] {K : Subgroup G}
    (h : ∀ g ∈ K, ∀ m : ℕ, Odd m → g ^ m = 1 → g = 1) : IsPGroup 2 K := by
  rintro ⟨g, hg⟩
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have h1 : (g ^ 2 ^ k) ^ m = 1 := by rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  have h2 := h _ (K.pow_mem hg _) m hm h1
  exact ⟨k, Subtype.ext (by simpa using h2)⟩

@[expose] def zcommSub (X R : Subgroup G) (z : G) (hzX : ∀ g ∈ X, g * z = z * g)
    (hRX : X ≤ Subgroup.normalizer (R : Set G)) : Subgroup G where
  carrier := {g | g ∈ X ∧ ∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ Subgroup.zpowers z}
  mul_mem' := by
    rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
    refine ⟨X.mul_mem hgX hhX, fun r hr => ?_⟩
    have e : g * h * r * (g * h)⁻¹ * r⁻¹ =
        (g * (h * r * h⁻¹ * r⁻¹) * g⁻¹) * (g * r * g⁻¹ * r⁻¹) := by group
    rw [e, conj_mem_zpowers (hzX g hgX) (hh r hr)]
    exact Subgroup.mul_mem _ (hh r hr) (hg r hr)
  one_mem' := ⟨X.one_mem, fun r _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgX, hg⟩
    refine ⟨X.inv_mem hgX, fun r hr => ?_⟩
    have hr' : g⁻¹ * r * g ∈ R := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hRX (X.inv_mem hgX)) r).mp hr
      simpa using h1
    have e : g⁻¹ * r * g⁻¹⁻¹ * r⁻¹ = (g * (g⁻¹ * r * g) * g⁻¹ * (g⁻¹ * r * g)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (hg _ hr')

variable {X R : Subgroup G} {z : G} {hzX : ∀ g ∈ X, g * z = z * g}
  {hRX : X ≤ Subgroup.normalizer (R : Set G)}

theorem zcommSub_le : zcommSub X R z hzX hRX ≤ X := fun _ hg => hg.1

theorem le_normalizer_zcommSub :
    X ≤ Subgroup.normalizer ((zcommSub X R z hzX hRX : Subgroup G) : Set G) := by
  have hconj : ∀ h ∈ X, ∀ g ∈ zcommSub X R z hzX hRX, h * g * h⁻¹ ∈ zcommSub X R z hzX hRX := by
    rintro h hh g ⟨hgX, hg⟩
    refine ⟨X.mul_mem (X.mul_mem hh hgX) (X.inv_mem hh), fun r hr => ?_⟩
    have hr' : h⁻¹ * r * h ∈ R := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hRX (X.inv_mem hh)) r).mp hr
      simpa using h1
    have e : h * g * h⁻¹ * r * (h * g * h⁻¹)⁻¹ * r⁻¹ =
        h * (g * (h⁻¹ * r * h) * g⁻¹ * (h⁻¹ * r * h)⁻¹) * h⁻¹ := by group
    rw [e, conj_mem_zpowers (hzX h hh) (hg _ hr')]
    exact hg _ hr'
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hconj h hh g, fun hg => ?_⟩
  have h1 := hconj h⁻¹ (X.inv_mem hh) _ hg
  simpa [mul_assoc] using h1

theorem isPGroup_zcommSub [Finite G] (hz : z * z = 1) {P : Subgroup G}
    (hP : IsPGroup 2 P)
    (hCP : zcommSub X R z hzX hRX ⊓ Subgroup.centralizer (R : Set G) ≤ P) :
    IsPGroup 2 (zcommSub X R z hzX hRX) := by
  refine isPGroup_two_of_odd fun g hg m hm hgm => ?_
  have hgC : g ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := comm_eq_one_of_odd hz (hzX g hg.1) (hg.2 r hr) hm hgm
    calc r * g = (g * r * g⁻¹ * r⁻¹)⁻¹ * (g * r) := by group
      _ = g * r := by rw [h1, inv_one, one_mul]
  obtain ⟨k, hk⟩ := hP ⟨g, hCP (Subgroup.mem_inf.mpr ⟨hg, hgC⟩)⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    simpa using h1
  exact eq_one_of_two_pow_of_odd hk' hm hgm

theorem le_conjClosure {Z : Subgroup G} : Z ≤ conjClosure Z X := fun s hs =>
  Subgroup.subset_closure ⟨1, X.one_mem, s, hs, by group⟩

theorem conjClosure_le {Z W : Subgroup G} (hW : ∀ h ∈ X, ∀ s ∈ Z, h * s * h⁻¹ ∈ W) :
    conjClosure Z X ≤ W :=
  (Subgroup.closure_le W).mpr fun _ ⟨h, hh, s, hs, e⟩ => e ▸ hW h hh s hs

theorem le_normalizer_conjClosure {Z : Subgroup G} :
    X ≤ Subgroup.normalizer ((conjClosure Z X : Subgroup G) : Set G) := by
  have hconj : ∀ g ∈ X, ∀ y ∈ conjClosure Z X, g * y * g⁻¹ ∈ conjClosure Z X := by
    intro g hg y hy
    unfold conjClosure at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, s, hs, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨g * h, X.mul_mem hg hh, s, hs, by group⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj g hg y, fun hy => ?_⟩
  have h1 := hconj g⁻¹ (X.inv_mem hg) _ hy
  simpa [mul_assoc] using h1

theorem le_of_normalizes_aux [Finite G] (hK : quasithinIsQTKECat G) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) {S Zs V Mi A Y : Subgroup G} (hVT : V ≤ T)
    (hTS : T ⊓ Subgroup.centralizer (Zs : Set G) ≤ S)
    (hSA : S ⊓ Subgroup.centralizer (A : Set G) ≤ V) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hZA : Zs ≤ A) (hAV : A ≤ V) (hA : A ≠ ⊥) (hNV : Subgroup.normalizer (V : Set G) ≤ Mi)
    (hTY : T ≤ Y) (hYA : Y ≤ Subgroup.normalizer (A : Set G)) : Y ≤ Mi := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAT : A ≤ T := hAV.trans hVT
  have hAO : A ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 (hAT.trans hTY) hYA (hT.1.to_le hAT)
  have hO : pCoreOf 2 Y ≠ ⊥ := fun h => hA (le_bot_iff.mp (h ▸ hAO))
  have hCY : CharTwo Y := charTwo_of_inH' hK hT ⟨hTY, hO⟩
  set C := Y ⊓ Subgroup.centralizer (A : Set G) with hC
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) :=
    H13.le_normalizer_inf_of_normalizes Subgroup.le_normalizer
      (hYA.trans (H13.normalizer_le_normalizer_centralizer A))
  have hCC : CharTwo C := CharTwo.of_normal hCY inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hYC)
  have hOT : pCoreOf 2 C ≤ T := by
    have h1 : pCoreOf 2 C ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans inf_le_left)
        (hYC.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
    exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hT hTY))
  have hOV : pCoreOf 2 C ≤ V := by
    intro g hg
    have hgA : g ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp (pCoreOf_le 2 C hg)).2
    have hgZ : g ∈ Subgroup.centralizer (Zs : Set G) :=
      Subgroup.centralizer_le (show (Zs : Set G) ⊆ A from hZA) hgA
    exact hSA (Subgroup.mem_inf.mpr ⟨hTS (Subgroup.mem_inf.mpr ⟨hOT hg, hgZ⟩), hgA⟩)
  have hVO : V ≤ pCoreOf 2 C := by
    intro v hv
    refine hCC (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hTY (hVT hv), ?_⟩, ?_⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hVab a (hAV ha) v hv
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hVab g (hOV hg) v hv
  calc Y ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) :=
        hYC.trans (normalizer_le_normalizer_pCoreOf 2 C)
    _ = Subgroup.normalizer (V : Set G) := by rw [le_antisymm hOV hVO]
    _ ≤ Mi := hNV

theorem normalizer_le_of_isUniqueM [Finite G] {X V Mi : Subgroup G} (hU : IsUniqueM X Mi)
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup.normalizer (V : Set G) ≤ Mi := by
  obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (V : Set G))
    ⟨V, hV, hV2, rfl⟩
  have h1 := hU.2 K ⟨hK, hXV.trans hle⟩
  rw [← h1]
  exact hle

end Generic

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

omit [Finite G] in
theorem comm_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hA ha hb

theorem le_M1_of_normalizes (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {A Y : Subgroup G} (hZA : sec53ZS T L < A) (hAV : A ≤ pCoreOf 2 L)
    (hTY : T ≤ Y) (hYA : Y ≤ Subgroup.normalizer (A : Set G)) : Y ≤ sec53M1 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨⟨-, -, hU1, -, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  have hsup := sup_sec53 h527 hyp hty hf
  have hV₁T : pCoreOf 2 L ≤ T := (le_sup_left.trans hsup.le).trans inf_le_left
  have hab := (l3facts_two h527 hyp hty hf).1
  have hA : A ≠ ⊥ := (bot_le.trans_lt hZA).ne'
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  refine le_of_normalizes_aux h.qtke h.sylow hV₁T (l3facts_one h527 h531 hyp hty hf).le
    ((l3facts_three h527 hyp hty hf).2.1 A hZA hAV).le
    (fun a ha b hb => comm_of_isElemAbelian hab ha hb) hZA.le hAV hA ?_ hTY hYA
  refine normalizer_le_of_isUniqueM hU1 (fun h0 => hA (le_bot_iff.mp (h0 ▸ hAV)))
    (pCoreOf_isPGroup 2 L) (sup_le ?_ (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L)

theorem le_M2_of_normalizes (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {A Y : Subgroup G} (hZA : sec53ZS T L < A)
    (hAV : A ≤ pCoreOf 2 (oTwoUpper H)) (hTY : T ≤ Y)
    (hYA : Y ≤ Subgroup.normalizer (A : Set G)) : Y ≤ sec53M2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨⟨-, -, -, hU2, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  have hsup := sup_sec53 h527 hyp hty hf
  have hV₂T : pCoreOf 2 (oTwoUpper H) ≤ T := (le_sup_right.trans hsup.le).trans inf_le_left
  have hab := (l3facts_two h527 hyp hty hf).2.1
  have hA : A ≠ ⊥ := (bot_le.trans_lt hZA).ne'
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  refine le_of_normalizes_aux h.qtke h.sylow hV₂T (l3facts_one h527 h531 hyp hty hf).le
    ((l3facts_three h527 hyp hty hf).2.2 A hZA hAV).le
    (fun a ha b hb => comm_of_isElemAbelian hab ha hb) hZA.le hAV hA ?_ hTY hYA
  refine normalizer_le_of_isUniqueM hU2 (fun h0 => hA (le_bot_iff.mp (h0 ▸ hAV)))
    (pCoreOf_isPGroup 2 _) (sup_le ?_ (hTK.trans (normalizer_le_normalizer_pCoreOf 2 _)))
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _)

section Vz

variable {S V₁ V₂ Z : Subgroup G} (N : ExcNF T S V₁ V₂ Z)

theorem exc_Vz (hST : S ≤ T) (hT : quasithinIsSylowTwo T)
    (hTz : T ≤ Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G))
    (hCT : CharTwo (Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G))) :
    conjClosure Z (Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G)) ≤ T ∧
      Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G) ≤ Subgroup.normalizer
        ((conjClosure Z (Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G)) : Subgroup G) :
          Set G) ∧
      Z ≤ conjClosure Z (Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G)) ∧
      (∀ a ∈ conjClosure Z (Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G)),
        ∀ b ∈ conjClosure Z (Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G)),
          a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers (N.Φ (1, 0, 0))) ∧
      ∀ a ∈ conjClosure Z (Subgroup.centralizer ({N.Φ (1, 0, 0)} : Set G)),
        a * a ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z := N.Φ (1, 0, 0) with hz
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set R := pCoreOf 2 Gz with hR
  have hzX : ∀ g ∈ Gz, g * z = z * g := fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg
  have hRX : Gz ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 Gz
  have hRT : R ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hT hTz)
  set Dz := zcommSub Gz R z hzX hRX with hDz
  have hZT : Z ≤ T := fun g hg => by
    obtain ⟨c, rfl⟩ := (N.mem_Z g).mp hg
    exact hST (N.mem _)
  have hD2 : IsPGroup 2 Dz := isPGroup_zcommSub N.z_mul_self (pCoreOf_isPGroup 2 Gz)
    (fun g hg => hCT (Subgroup.mem_inf.mpr ⟨zcommSub_le (Subgroup.mem_inf.mp hg).1,
      (Subgroup.mem_inf.mp hg).2⟩))
  have hDR : Dz ≤ R := le_pCoreOf_of_le_normalizer 2 zcommSub_le le_normalizer_zcommSub hD2
  have hZD : Z ≤ Dz := by
    intro s hs
    refine ⟨hTz (hZT hs), fun r hr => ?_⟩
    obtain ⟨c, rfl⟩ := (N.mem_Z s).mp hs
    exact N.comm_mem_zpowers_Z hST c (hRT hr)
  have hVD : conjClosure Z Gz ≤ Dz := conjClosure_le fun h hh s hs =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_zcommSub hh) s).mp (hZD hs)
  have hVR : conjClosure Z Gz ≤ R := hVD.trans hDR
  have hcomm : ∀ a ∈ conjClosure Z Gz, ∀ b ∈ conjClosure Z Gz,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := fun a ha b hb => (hVD ha).2 b (hVR hb)
  refine ⟨hVR.trans hRT, le_normalizer_conjClosure, le_conjClosure, hcomm, ?_⟩
  intro a ha
  have ha' := ha
  unfold conjClosure at ha'
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨h, hh, s, hs, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := (N.mem_Z s).mp hs
    have e : h * N.Φ (c, 0, 0) * h⁻¹ * (h * N.Φ (c, 0, 0) * h⁻¹) =
        h * (N.Φ (c, 0, 0) * N.Φ (c, 0, 0)) * h⁻¹ := by group
    rw [e, N.sq_Φ, mul_zero, N.Φ_zero, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : x * y * (x * y) = (x * y * x⁻¹ * y⁻¹) * (y * (x * x) * y⁻¹) * (y * y) := by group
    have hyz : y * z = z * y := hzX y (hTz ((hVR.trans hRT) hy))
    rw [e, conj_mem_zpowers hyz ihx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hcomm x hx y hy) ihx) ihy
  | inv x hx ihx =>
    rw [← mul_inv_rev]
    exact Subgroup.inv_mem _ ihx

end Vz

end CFSG.Quasithin.H13.Sec53L3
