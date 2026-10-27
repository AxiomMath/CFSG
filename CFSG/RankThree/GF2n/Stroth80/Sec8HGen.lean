module

public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec8HLin

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_gen_points_card (hc : Ctx M Q Z B) (m : G) :
    Nat.card (conjSubgroup m B) = Nat.card Z := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [card_conjSubgroup, hg, card_conjSubgroup]

theorem sec8_gen_points_exists_out (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    ∃ c ∈ conjSubgroup m B, c ∉ Z := by
  have hnle : ¬ conjSubgroup m B ≤ Z := fun hle =>
    (hc.conj_of_mem hm).ne (Subgroup.eq_of_le_of_card_ge hle (sec8_gen_points_card hc m).ge)
  exact SetLike.not_le_iff_exists.mp hnle

theorem sec8_gen_points (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {C D : Subgroup G} (hCm : ∃ m ∈ M, C = conjSubgroup m B)
    (hDm : ∃ m ∈ M, D = conjSubgroup m B) (hCV : C ≤ Vt M (LB M Q B) B Z t)
    (hDV : D ≤ Vt M (LB M Q B) B Z t) (hnp : ¬ D ≤ QB C) :
    Rt M (LB M Q B) t = LB M Q C ⊔ LB M Q D := by
  obtain ⟨m₁, hm₁, rfl⟩ := hCm
  obtain ⟨m₂, hm₂, rfl⟩ := hDm
  have hcC : Ctx M Q Z (conjSubgroup m₁ B) := hc.conj_of_mem hm₁
  have hcD : Ctx M Q Z (conjSubgroup m₂ B) := hc.conj_of_mem hm₂
  obtain ⟨c₀, hc₀C, hc₀Z⟩ := sec8_gen_points_exists_out hc hm₁
  obtain ⟨d₀, hd₀D, hd₀Z⟩ := sec8_gen_points_exists_out hc hm₂
  obtain ⟨h, hhR, hc₀h⟩ := sec8PointsTrans hc hs (hCV hc₀C) hc₀Z
  obtain ⟨h', hh'R, hd₀h'⟩ := sec8PointsTrans hc hs (hDV hd₀D) hd₀Z
  have hhM : h ∈ M := hc.Rt_le_M t hhR
  have hh'M : h' ∈ M := hc.Rt_le_M t hh'R
  have hc₀C' : c₀ ∈ conjSubgroup m₁ B ⊔ Z := Subgroup.mem_sup_left hc₀C
  have hd₀D' : d₀ ∈ conjSubgroup m₂ B ⊔ Z := Subgroup.mem_sup_left hd₀D
  have hCh : conjSubgroup m₁ B ⊔ Z = conjSubgroup h B ⊔ Z :=
    sec8_point_eq (hc := hc) hm₁ hhM hc₀C' hc₀h hc₀Z
  have hDh' : conjSubgroup m₂ B ⊔ Z = conjSubgroup h' B ⊔ Z :=
    sec8_point_eq (hc := hc) hm₂ hh'M hd₀D' hd₀h' hd₀Z
  have hnp' : ¬ conjSubgroup h' B ≤ QB (conjSubgroup h B) := fun hh' =>
    hnp ((sec8_le_QB_iff_of_sup_eq hcC (hc.conj_of_mem hhM) hCh hcD.le
      (hc.conj_of_mem hh'M).le hDh').mpr hh')
  have hrR : h⁻¹ * h' ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem hhR) hh'R
  have hnpB : ¬ conjSubgroup (h⁻¹ * h') B ≤ QB B := by
    intro hle
    apply hnp'
    have h1 : conjSubgroup h (conjSubgroup (h⁻¹ * h') B) ≤ conjSubgroup h (QB B) :=
      Subgroup.map_mono hle
    rw [← conjSubgroup_mul, mul_inv_cancel_left, ← QB_conj] at h1
    exact h1
  have hplane : HypPlane Q Z B (conjSubgroup (h⁻¹ * h') B) t :=
    (sec8_hypPlane_iff h34 hs hrR).mpr hnpB
  have hgen : Rt M (LB M Q B) t = LB M Q B ⊔ LB M Q (conjSubgroup (h⁻¹ * h') B) :=
    (sec7A_of_hypPlane h34 hRoot h51 hs hrR hplane).gen
  have hfix : conjSubgroup h (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hhR)
  have hconjR : Rt M (LB M Q B) t =
      conjSubgroup h (LB M Q B) ⊔ conjSubgroup h (LB M Q (conjSubgroup (h⁻¹ * h') B)) := by
    calc Rt M (LB M Q B) t = conjSubgroup h (Rt M (LB M Q B) t) := hfix.symm
      _ = conjSubgroup h (LB M Q B ⊔ LB M Q (conjSubgroup (h⁻¹ * h') B)) :=
        congrArg (conjSubgroup h) hgen
      _ = conjSubgroup h (LB M Q B) ⊔ conjSubgroup h (LB M Q (conjSubgroup (h⁻¹ * h') B)) :=
        conjSubgroup_sup' h _ _
  have hr_M : h⁻¹ * h' ∈ M := hc.Rt_le_M t hrR
  have hLBh : conjSubgroup h (LB M Q B) = LB M Q (conjSubgroup h B) :=
    (hc.LB_conj hhM).symm
  have hLBr : LB M Q (conjSubgroup (h⁻¹ * h') B) = conjSubgroup (h⁻¹ * h') (LB M Q B) :=
    hc.LB_conj hr_M
  have hmul : conjSubgroup h (conjSubgroup (h⁻¹ * h') (LB M Q B)) =
      conjSubgroup h' (LB M Q B) := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  have hLBh' : conjSubgroup h' (LB M Q B) = LB M Q (conjSubgroup h' B) :=
    (hc.LB_conj hh'M).symm
  have hR : Rt M (LB M Q B) t = LB M Q (conjSubgroup h B) ⊔ LB M Q (conjSubgroup h' B) := by
    rw [hconjR, hLBh, hLBr, hmul, hLBh']
  have hLC : LB M Q (conjSubgroup m₁ B) = LB M Q (conjSubgroup h B) :=
    sec8_LB_eq_of_sup_eq hcC (hc.conj_of_mem hhM) hCh
  have hLD : LB M Q (conjSubgroup m₂ B) = LB M Q (conjSubgroup h' B) :=
    sec8_LB_eq_of_sup_eq hcD (hc.conj_of_mem hh'M) hDh'
  rw [hLC, hLD]
  exact hR

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_exists_pair_conj_le {h : G} {X Y : Subgroup G} :
    conjSubgroup h X ≤ conjSubgroup h Y ↔ X ≤ Y := by
  constructor
  · intro hle x hx
    have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    have h1 : h * x * h⁻¹ ∈ conjSubgroup h X := by
      rw [mem_conjSubgroup, e]
      exact hx
    have h2 := hle h1
    rw [mem_conjSubgroup, e] at h2
    exact h2
  · intro hXY y hy
    rw [mem_conjSubgroup] at hy ⊢
    exact hXY hy

theorem sec8_exists_pair_conj_sup (g : G) (A C : Subgroup G) :
    conjSubgroup g (A ⊔ C) = conjSubgroup g A ⊔ conjSubgroup g C :=
  Subgroup.map_sup _ _ _

theorem sec8_exists_pair_vec {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {m : ℕ}
    {K : Type} [Field K] {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K}
    {u : Fin m ⊕ Fin m → K} [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hBiff : ∀ x : Fin m ⊕ Fin m → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {h : G} (hh : h ∈ Rt M (LB M Q B) t) (x : ↥(Vt M (LB M Q B) B Z t))
    (hxh : (x : G) ∈ conjSubgroup h B ⊔ Z) :
    ∃ c : K, secVec ψ x =
      c • ((φ ⟨h, hh⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hhM
  obtain ⟨b, hb, z, hz, hxbz⟩ :=
    sec8PointTI_mul_of_mem_sup (B := conjSubgroup h B) (Z := Z)
      (fun b' hb' z' hz' => sec8PointTI_central hc' hb' hz') hxh
  have hbV' : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup h B ≤ conjSubgroup h B ⊔ Z).trans
      (hc.conj_Rt_le_Vt hs.toSec5.mem hh)
  have hbV : b ∈ Vt M (LB M Q B) B Z t := hbV' hb
  have hb₁ : h⁻¹ * b * h ∈ B := mem_conjSubgroup.mp hb
  have hb₁V : h⁻¹ * b * h ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.toSec5.mem hb₁
  obtain ⟨c, hcu⟩ := (hBiff (secVec ψ ⟨h⁻¹ * b * h, hb₁V⟩)).mp
    ⟨⟨h⁻¹ * b * h, hb₁V⟩, hb₁, rfl⟩
  have hpsi : secVec ψ ⟨b, hbV⟩ =
      (φ ⟨h, hh⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        secVec ψ ⟨h⁻¹ * b * h, hb₁V⟩ :=
    hψ ⟨h, hh⟩ ⟨h⁻¹ * b * h, hb₁V⟩ ⟨b, hbV⟩ (by show b = h * (h⁻¹ * b * h) * h⁻¹; group)
  have hbvec : secVec ψ ⟨b, hbV⟩ =
      c • ((φ ⟨h, hh⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
    rw [hpsi, hcu, Matrix.mulVec_smul]
  have hzV : z ∈ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt hz
  have hzero : secVec ψ ⟨z, hzV⟩ = 0 := (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz
  have hxeq : x = (⟨b, hbV⟩ : ↥(Vt M (LB M Q B) B Z t)) * (⟨z, hzV⟩ : ↥(Vt M (LB M Q B) B Z t)) :=
    Subtype.ext hxbz
  refine ⟨c, ?_⟩
  rw [hxeq, secVec_mul, hzero, add_zero, hbvec]

theorem sec8_exists_pair_point {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {g : G}
    (hg : g ∈ M) {x : G} (hxV : x ∈ Vt M (LB M Q B) B Z t)
    (hxg : x ∈ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) (hxZ : x ∉ Z) :
    ∃ h ∈ Rt M (LB M Q B) t, x ∈ conjSubgroup h B ⊔ Z ∧
      conjSubgroup h B ≤ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := by
  obtain ⟨h, hh, hxh⟩ := sec8PointsTrans hc hs hxV hxZ
  refine ⟨h, hh, hxh, ?_⟩
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have hgi : g⁻¹ ∈ M := M.inv_mem hg
  have hx'V : g * x * g⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    rw [mem_conjSubgroup, inv_inv] at hxg
    exact hxg
  have hx'Z : g * x * g⁻¹ ∉ Z := by
    intro hz
    apply hxZ
    have h1 : x ∈ conjSubgroup g⁻¹ Z := by
      rw [mem_conjSubgroup, inv_inv]
      exact hz
    rwa [hc.conj_Z_eq hgi] at h1
  obtain ⟨h₂, hh₂, hx'h₂⟩ := sec8PointsTrans hc hs hx'V hx'Z
  have hh₂M : g⁻¹ * h₂ ∈ M := M.mul_mem hgi (hc.Rt_le_M t hh₂)
  have hB₂V : conjSubgroup h₂ B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup h₂ B ≤ conjSubgroup h₂ B ⊔ Z).trans
      (hc.conj_Rt_le_Vt hs.toSec5.mem hh₂)
  have e : conjSubgroup (g⁻¹ * h₂) B ⊔ Z = conjSubgroup g⁻¹ (conjSubgroup h₂ B ⊔ Z) := by
    rw [sec8_exists_pair_conj_sup, conjSubgroup_mul, hc.conj_Z_eq hgi]
  have hxg₂ : x ∈ conjSubgroup (g⁻¹ * h₂) B ⊔ Z := by
    rw [e, mem_conjSubgroup, inv_inv]
    exact hx'h₂
  have heq := sec8_point_eq (hc := hc) hhM hh₂M hxh hxg₂ hxZ
  have hsub : conjSubgroup (g⁻¹ * h₂) B ⊔ Z ≤ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := by
    refine sup_le ?_ ?_
    · rw [conjSubgroup_mul]
      exact Subgroup.map_mono hB₂V
    · intro z hz
      have hz' : z ∈ conjSubgroup g⁻¹ Z := by
        rw [hc.conj_Z_eq hgi]
        exact hz
      exact mem_conjSubgroup.mpr (sec39_Z_le_Vt (mem_conjSubgroup.mp hz'))
  intro y hy
  have hy' : y ∈ conjSubgroup h B ⊔ Z := Subgroup.mem_sup_left hy
  rw [heq] at hy'
  exact hsub hy'

theorem sec8_exists_pair_form {m : ℕ} {K : Type} [Field K] {A A' R0 : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ CFSG.Open.StatedSp m K) (hA' : A' = A * R0) (u : Fin m ⊕ Fin m → K) (c c' : K)
    (hne : spForm m K (c • ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u))
      (c' • ((A' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)) ≠ 0) :
    spForm m K u ((R0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 := by
  intro h0
  apply hne
  have key : spForm m K ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
      ((A' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) = 0 := by
    rw [hA', Units.val_mul, ← Matrix.mulVec_mulVec, (mem_statedSp_iff_forall A).mp hA u _]
    exact h0
  simp only [map_smul, LinearMap.smul_apply, key, smul_zero]

theorem sec8_exists_pair (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {m : ℕ}
    (hmSp : SpMNat hc t m) {g : G} (hg : g ∈ M)
    (hlarge : Nat.card Z ^ (m + 1) <
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t))) :
    ∃ C D : Subgroup G, (∃ m₁ ∈ M, C = conjSubgroup m₁ B) ∧ (∃ m₂ ∈ M, D = conjSubgroup m₂ B) ∧
      C ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) ∧
      D ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) ∧ ¬ D ≤ QB C := by
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, _u', hpts, hhyp, hBiff, hψ, _nn, _γ, _M₀,
    _hglob, _θ, _hθ⟩ := sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  letI := hpts.vecAct
  have hκ := sec8_isSecMod_psi hpts ψ hψ
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hSV : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) ≤
      Vt M (LB M Q B) B Z t := inf_le_left
  have hZS : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨sec39_Z_le_Vt hz, ?_⟩
    have hz' : z ∈ conjSubgroup g⁻¹ Z := by
      rw [hc.conj_Z_eq (M.inv_mem hg)]
      exact hz
    exact mem_conjSubgroup.mpr (sec39_Z_le_Vt (mem_conjSubgroup.mp hz'))
  obtain ⟨x, y, hxS, hyS, hxy⟩ : ∃ x y : ↥(Vt M (LB M Q B) B Z t),
      (x : G) ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) ∧
      (y : G) ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) ∧
      spForm m K (secVec ψ x) (secVec ψ y) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hT : ∀ a ∈ secSub (ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf
        (Vt M (LB M Q B) B Z t)))) (Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹
          (Vt M (LB M Q B) B Z t)),
        ∀ b ∈ secSub (ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf
          (Vt M (LB M Q B) B Z t)))) (Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹
            (Vt M (LB M Q B) B Z t)),
        spForm m K a b = 0 := by
      intro a ha b hb
      obtain ⟨x', hx'S, hx'a⟩ := mem_secSub.mp ha
      obtain ⟨y', hy'S, hy'b⟩ := mem_secSub.mp hb
      have ea : secVec ψ x' = a := by
        have h1 := congrArg Multiplicative.toAdd hx'a
        rw [toAdd_ofAdd] at h1
        exact h1
      have eb : secVec ψ y' = b := by
        have h1 := congrArg Multiplicative.toAdd hy'b
        rw [toAdd_ofAdd] at h1
        exact h1
      have h2 := hcon x' y' hx'S hy'S
      rw [ea, eb] at h2
      exact h2
    have hcardT := card_addSubgroup_le_of_totallyIsotropic _ hT
    have hmul := natCard_secSub_mul hZV hκ hZS hSV
    rw [hpts.card] at hcardT
    have hle : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) ≤
        Nat.card Z ^ (m + 1) := by
      rw [← hmul, pow_succ]
      exact Nat.mul_le_mul hcardT le_rfl
    exact absurd hlarge (not_lt.mpr hle)
  have hxV : (x : G) ∈ Vt M (LB M Q B) B Z t := (Subgroup.mem_inf.mp hxS).1
  have hxg : (x : G) ∈ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := (Subgroup.mem_inf.mp hxS).2
  have hyV : (y : G) ∈ Vt M (LB M Q B) B Z t := (Subgroup.mem_inf.mp hyS).1
  have hyg : (y : G) ∈ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := (Subgroup.mem_inf.mp hyS).2
  have hxZ : (x : G) ∉ Z := by
    intro hz
    apply hxy
    rw [(secVec_eq_zero_iff ψ x).mpr hz]
    simp
  have hyZ : (y : G) ∉ Z := by
    intro hz
    apply hxy
    rw [(secVec_eq_zero_iff ψ y).mpr hz]
    simp
  obtain ⟨h, hh, hxh, hCg⟩ := sec8_exists_pair_point hs hg hxV hxg hxZ
  obtain ⟨h', hh', hyh, hDg⟩ := sec8_exists_pair_point hs hg hyV hyg hyZ
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have hh'M : h' ∈ M := hc.Rt_le_M t hh'
  have hCV : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup h B ≤ conjSubgroup h B ⊔ Z).trans
      (hc.conj_Rt_le_Vt hs.toSec5.mem hh)
  have hDV : conjSubgroup h' B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup h' B ≤ conjSubgroup h' B ⊔ Z).trans
      (hc.conj_Rt_le_Vt hs.toSec5.mem hh')
  obtain ⟨c, hc₁⟩ := sec8_exists_pair_vec hs ψ hBiff hψ hh x hxh
  obtain ⟨c', hc₂⟩ := sec8_exists_pair_vec hs ψ hBiff hψ hh' y hyh
  have hA : φ ⟨h, hh⟩ ∈ CFSG.Open.StatedSp m K := by
    rw [← hpts.range]
    exact MonoidHom.mem_range.mpr ⟨⟨h, hh⟩, rfl⟩
  obtain ⟨r₀, hr0⟩ : ∃ r₀ : ↥(Rt M (LB M Q B) t), (r₀ : G) = h⁻¹ * h' :=
    ⟨⟨h⁻¹ * h', (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem hh) hh'⟩, rfl⟩
  have hφ : φ ⟨h', hh'⟩ = φ ⟨h, hh⟩ * φ r₀ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, hr0]
    show h' = h * (h⁻¹ * h')
    group
  rw [hc₁, hc₂] at hxy
  have hform : spForm m K u ((φ r₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 :=
    sec8_exists_pair_form hA hφ u c c' hxy
  have hplane : HypPlane Q Z B (conjSubgroup (r₀ : G) B) t := (hhyp r₀).mpr hform
  have hnot : ¬ conjSubgroup (r₀ : G) B ≤ QB B := (sec8_hypPlane_iff h34 hs r₀.2).mp hplane
  have hnotDC : ¬ conjSubgroup h' B ≤ QB (conjSubgroup h B) := by
    intro hcontra
    apply hnot
    rw [QB_conj] at hcontra
    have e : conjSubgroup h' B = conjSubgroup h (conjSubgroup (r₀ : G) B) := by
      rw [hr0, ← conjSubgroup_mul, mul_inv_cancel_left]
    rw [e] at hcontra
    exact sec8_exists_pair_conj_le.mp hcontra
  exact ⟨conjSubgroup h B, conjSubgroup h' B, ⟨h, hhM, rfl⟩, ⟨h', hh'M, rfl⟩,
    le_inf hCV hCg, le_inf hDV hDg, hnotDC⟩

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_subspace_dichotomy {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K}
    {u u' : Fin m ⊕ Fin m → K} (hpts : Sec8Pts hc t r m K φ u u')
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {D : Subgroup G} (hZD : Z ≤ D) (hDV : D ≤ Vt M (LB M Q B) B Z t)
    (hDK : ∀ (c : K) (d : ↥(Vt M (LB M Q B) B Z t)), (d : G) ∈ D →
      ∃ d' : ↥(Vt M (LB M Q B) B Z t), (d' : G) ∈ D ∧ secVec ψ d' = c • secVec ψ d)
    (huD : ∃ d : ↥(Vt M (LB M Q B) B Z t), (d : G) ∈ D ∧ secVec ψ d = u)
    (hDinv : ∀ l ∈ LB M Q B, ∀ d ∈ D, l * d * l⁻¹ ∈ D) :
    (∀ d : ↥(Vt M (LB M Q B) B Z t), (d : G) ∈ D → spForm m K u (secVec ψ d) = 0) ∨
      Vt M (LB M Q B) B Z t ≤ D := by
  letI := hpts.vecAct
  obtain ⟨hRnorm, -⟩ := hpts.act
  obtain ⟨κ, hκdef⟩ : ∃ κ : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative (Fin m ⊕ Fin m → K),
      κ = ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf (Vt M (LB M Q B) B Z t))) :=
    ⟨_, rfl⟩
  have hκ : @IsSecMod G _ (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (Fin m ⊕ Fin m → K) _
      hpts.vecAct κ := by
    subst hκdef
    exact sec8_isSecMod_psi hpts ψ hψ
  have hsec : ∀ v : ↥(Vt M (LB M Q B) B Z t), secVec ψ v = Multiplicative.toAdd (κ v) := by
    intro v
    subst hκdef
    rfl
  have hDK' : ∀ (c : K) (d : ↥(Vt M (LB M Q B) B Z t)), (d : G) ∈ D →
      ∃ d' : ↥(Vt M (LB M Q B) B Z t), (d' : G) ∈ D ∧
        Multiplicative.toAdd (κ d') = c • Multiplicative.toAdd (κ d) := by
    intro c d hd
    obtain ⟨d', hd', h⟩ := hDK c d hd
    refine ⟨d', hd', ?_⟩
    rw [← hsec d', ← hsec d]
    exact h
  obtain ⟨D'', hD''⟩ : ∃ D'' : Submodule K (Fin m ⊕ Fin m → K),
      ∀ a : Fin m ⊕ Fin m → K, a ∈ D'' ↔ a ∈ secSub κ D := by
    refine ⟨{ carrier := {a | a ∈ secSub κ D}
              add_mem' := fun ha hb => (secSub κ D).add_mem ha hb
              zero_mem' := (secSub κ D).zero_mem
              smul_mem' := fun c a ha => ?_ }, fun a => Iff.rfl⟩
    show c • a ∈ secSub κ D
    have ha' : a ∈ secSub κ D := ha
    obtain ⟨x, hxD, hxa⟩ := mem_secSub.mp ha'
    obtain ⟨d, hdD, hdc⟩ := hDK' c x hxD
    refine mem_secSub.mpr ⟨d, hdD, ?_⟩
    have h2 : Multiplicative.toAdd (κ x) = a := by rw [hxa, toAdd_ofAdd]
    apply Multiplicative.toAdd.injective
    rw [hdc, toAdd_ofAdd, h2]
  have hD''mem : ∀ a : Fin m ⊕ Fin m → K, a ∈ D'' ↔
      ∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ D ∧ κ w = Multiplicative.ofAdd a :=
    fun a => (hD'' a).trans mem_secSub
  have hu_mem : u ∈ D'' := by
    obtain ⟨d, hdD, hdu⟩ := huD
    refine (hD''mem u).mpr ⟨d, hdD, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact (hsec d).symm.trans hdu
  have hinv : ∀ A ∈ LspGL m K u, ∀ d ∈ D'',
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ d ∈ D'' := by
    intro A hA d hd
    have hAL : A ∈ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ := by
      rw [hpts.hL]
      exact hA
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hAL
    have hsL : (s : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨x, hxD, hxd⟩ := mem_secSub.mp ((hD'' d).mp hd)
    have hconj : (s : G) * (x : G) * (s : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hRnorm s.2) (x : G)).mp x.2
    have hwD : (s : G) * (x : G) * (s : G)⁻¹ ∈ D := hDinv (s : G) hsL (x : G) hxD
    refine (hD''mem _).mpr ⟨⟨(s : G) * (x : G) * (s : G)⁻¹, hconj⟩, hwD, ?_⟩
    have h := hκ.act s x ⟨(s : G) * (x : G) * (s : G)⁻¹, hconj⟩ rfl
    rw [hxd, toAdd_ofAdd] at h
    exact h
  rcases LspGL_invariant_subspace_dichotomy hpts.u_ne_zero D'' hu_mem hinv with hperp | htop
  · left
    intro d hd
    have hdD : Multiplicative.toAdd (κ d) ∈ D'' :=
      (hD'' _).mpr (mem_secSub.mpr ⟨d, hd, (ofAdd_toAdd (κ d)).symm⟩)
    rw [hsec d]
    exact hperp _ hdD
  · right
    intro v hv
    have hmem : Multiplicative.toAdd (κ ⟨v, hv⟩) ∈ D'' := by
      rw [htop]
      exact Submodule.mem_top
    exact (toAdd_mem_secSub_iff hκ hZD ⟨v, hv⟩).mp ((hD'' _).mp hmem)

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_inf_conjSubgroup_inv (g : G) (U : Subgroup G) :
    Nat.card ↥(U ⊓ conjSubgroup g⁻¹ U) = Nat.card ↥(U ⊓ conjSubgroup g U) := by
  have e1 : conjSubgroup g (U ⊓ conjSubgroup g⁻¹ U) = conjSubgroup g U ⊓ U := by
    rw [conjSubgroup_inf, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  rw [← card_conjSubgroup g, e1, inf_comm]

theorem sec8_normR_of_pair (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {g : G} (hgM : g ∈ M) {C D : Subgroup G} (hCm : ∃ m ∈ M, C = conjSubgroup m B)
    (hDm : ∃ m ∈ M, D = conjSubgroup m B)
    (hC : C ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t))
    (hD : D ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t))
    (hnp : ¬ D ≤ QB C) :
    g ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) := by
  classical
  have hgen := sec8_gen_points h34 hRoot h51 hs hCm hDm (hC.trans inf_le_left)
    (hD.trans inf_le_left) hnp
  have hconjV : ∀ X : Subgroup G, X ≤ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) →
      conjSubgroup g X ≤ Vt M (LB M Q B) B Z t := by
    intro X hX
    have h1 : conjSubgroup g X ≤ conjSubgroup g (conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) :=
      Subgroup.map_mono hX
    rwa [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one] at h1
  have hmem : ∀ X : Subgroup G, (∃ m ∈ M, X = conjSubgroup m B) →
      ∃ m ∈ M, conjSubgroup g X = conjSubgroup m B := by
    rintro X ⟨m, hm, rfl⟩
    exact ⟨g * m, M.mul_mem hgM hm, (conjSubgroup_mul g m B).symm⟩
  have hLBg : ∀ X : Subgroup G, (∃ m ∈ M, X = conjSubgroup m B) →
      LB M Q (conjSubgroup g X) = conjSubgroup g (LB M Q X) := by
    rintro X ⟨m, hm, rfl⟩
    rw [← conjSubgroup_mul, hc.LB_conj (M.mul_mem hgM hm), hc.LB_conj hm, conjSubgroup_mul]
  have hnp' : ¬ conjSubgroup g D ≤ QB (conjSubgroup g C) := by
    intro h
    apply hnp
    rw [QB_conj] at h
    have h1 : conjSubgroup g⁻¹ (conjSubgroup g D) ≤ conjSubgroup g⁻¹ (conjSubgroup g (QB C)) :=
      Subgroup.map_mono h
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, ← conjSubgroup_mul,
      inv_mul_cancel, conjSubgroup_one] at h1
  have hgen' := sec8_gen_points h34 hRoot h51 hs (hmem C hCm) (hmem D hDm)
    (hconjV C (hC.trans inf_le_right)) (hconjV D (hD.trans inf_le_right)) hnp'
  rw [hLBg C hCm, hLBg D hDm] at hgen'
  have hfix : conjSubgroup g (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := by
    calc conjSubgroup g (Rt M (LB M Q B) t)
        = conjSubgroup g (LB M Q C ⊔ LB M Q D) := congrArg (conjSubgroup g) hgen
      _ = conjSubgroup g (LB M Q C) ⊔ conjSubgroup g (LB M Q D) := conjSubgroup_sup' g _ _
      _ = Rt M (LB M Q B) t := hgen'.symm
  exact conjSubgroup_eq_self_iff.mp hfix

end

end CFSG.RankThree.GF2n.Stroth80
