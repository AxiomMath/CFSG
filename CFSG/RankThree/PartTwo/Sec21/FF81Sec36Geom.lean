module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Matrix
open P51 (V Mat GL4 e)
open scoped IsMulCommutative

namespace S36

variable {G : Type} [Group G] [Finite G]

def ε4 (b₀ b₁ b₂ b₃ : G) (v : V) : G :=
  b₀ ^ (v 0).val * b₁ ^ (v 1).val * b₂ ^ (v 2).val * b₃ ^ (v 3).val

theorem sum_e (v : V) : v 0 • e 0 + v 1 • e 1 + v 2 • e 2 + v 3 • e 3 = v := by
  ext j; fin_cases j <;> simp [e, Pi.single_apply]

open P51T in
theorem cvG_ε4 {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {b₀ b₁ b₂ b₃ : G}
    (hβ : ∀ i, ((Additive.toMul (β i) : B) : G) = ![b₀, b₁, b₂, b₃] i) (v : V) :
    cvG β (ε4 b₀ b₁ b₂ b₃ v) = v := by
  have hbB : ∀ i, ![b₀, b₁, b₂, b₃] i ∈ B := fun i => hβ i ▸ (Additive.toMul (β i)).2
  have hpow : ∀ (i : Fin 4) (n : ℕ), ![b₀, b₁, b₂, b₃] i ^ n ∈ B ∧
      cvG β (![b₀, b₁, b₂, b₃] i ^ n) = (n : ZMod 3) • e i := by
    intro i n
    refine ⟨B.pow_mem (hbB i) n, ?_⟩
    rw [cvG_of_mem β (B.pow_mem (hbB i) n)]
    have h1 : (⟨![b₀, b₁, b₂, b₃] i ^ n, B.pow_mem (hbB i) n⟩ : B) =
        (Additive.toMul (β i)) ^ (n : ℤ) := Subtype.ext (by simp [← hβ i])
    rw [h1, cv_zpow, cv_basis]
    ext j
    simp
  obtain ⟨h0, c0⟩ : b₀ ^ (v 0).val ∈ B ∧ cvG β (b₀ ^ (v 0).val) = ((v 0).val : ZMod 3) • e 0 :=
    hpow 0 _
  obtain ⟨h1, c1⟩ : b₁ ^ (v 1).val ∈ B ∧ cvG β (b₁ ^ (v 1).val) = ((v 1).val : ZMod 3) • e 1 :=
    hpow 1 _
  obtain ⟨h2, c2⟩ : b₂ ^ (v 2).val ∈ B ∧ cvG β (b₂ ^ (v 2).val) = ((v 2).val : ZMod 3) • e 2 :=
    hpow 2 _
  obtain ⟨h3, c3⟩ : b₃ ^ (v 3).val ∈ B ∧ cvG β (b₃ ^ (v 3).val) = ((v 3).val : ZMod 3) • e 3 :=
    hpow 3 _
  rw [ε4, cvG_mul β (B.mul_mem (B.mul_mem h0 h1) h2) h3, cvG_mul β (B.mul_mem h0 h1) h2,
    cvG_mul β h0 h1, c0, c1, c2, c3]
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  exact sum_e v

open P51T in
theorem ε4_eq_vB {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {b₀ b₁ b₂ b₃ : G}
    (hβ : ∀ i, ((Additive.toMul (β i) : B) : G) = ![b₀, b₁, b₂, b₃] i) (v : V) :
    ε4 b₀ b₁ b₂ b₃ v = (vB β v : G) := by
  have hbB : ∀ i, ![b₀, b₁, b₂, b₃] i ∈ B := fun i => hβ i ▸ (Additive.toMul (β i)).2
  have hmem : ε4 b₀ b₁ b₂ b₃ v ∈ B :=
    B.mul_mem (B.mul_mem (B.mul_mem (B.pow_mem (hbB 0) _) (B.pow_mem (hbB 1) _))
      (B.pow_mem (hbB 2) _)) (B.pow_mem (hbB 3) _)
  refine cvG_inj β hmem (vB β v).2 ?_
  rw [cvG_ε4 β hβ, cvG_of_mem β (vB β v).2, cv_vB]

open P51T P51 in
theorem conjLines_iff {b : G} {L B : Subgroup G}
    {b₁ b₂ b₃ : G} (hB : FF81Basis b L B b₁ b₂ b₃) (hbad : CaseBad b B) :
    ∃ m : Fin 7 → Bool, (m = mD ∨ m = mE) ∧ ∀ v : V, v ≠ 0 →
      (Subgroup.zpowers (ε4 b b₁ b₂ b₃ v) ∈ ConjLines B b ↔ m (orbOf v) = true) := by
  obtain ⟨hE, hcl, -⟩ := hB.mono
  haveI : IsElementaryAbelian 3 B := hE.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) hE.2 hcl
  set bs : Fin 4 → G := ![b, b₁, b₂, b₃] with hbs
  have hbB : ∀ i, bs i ∈ B := fun i => hβ i ▸ (Additive.toMul (β i)).2
  have hcol : ∀ (n : G) (hn : n ∈ Nor B) (i : Fin 4),
      ρM β ⟨n, hn⟩ *ᵥ e i = cvG β (n * bs i * n⁻¹) := fun n hn i => by
    rw [ρM_col, hβ i]
  have hconj : ∀ n ∈ Nor B, ∀ x ∈ B, n * x * n⁻¹ ∈ B := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  set Γ := (ρU β).range with hΓdef
  have hΓ : ∀ g ∈ Γ, ∃ (n : G) (hn : n ∈ Nor B), (g : Mat) = ρM β ⟨n, hn⟩ := by
    rintro g ⟨⟨n, hn⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  have hρΓ : ∀ (n : G) (hn : n ∈ Nor B), ρU β ⟨n, hn⟩ ∈ Γ := fun n hn => ⟨_, rfl⟩
  have hzp : ∀ n : G, conjBy n (Subgroup.zpowers b) = Subgroup.zpowers (n * b * n⁻¹) := by
    intro n
    rw [conjBy, MonoidHom.map_zpowers]
    rfl
  have hyp : Hyp Γ := hyp_of hB.mono hB.stab hB.meet β hβ
  have homneg : ∀ v ∈ Om Γ, -v ∈ Om Γ := by
    rintro v ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htT⟩ := hyp.t0
    refine ⟨g * t, Γ.mul_mem hg ht, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, htT, T0_e0, Matrix.mulVec_neg]
  have hlines : {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D} = Lv β '' Om Γ := by
    ext D
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨ρM β ⟨n, hn⟩ *ᵥ e 0, ⟨_, hρΓ n hn, rfl⟩, ?_⟩
      rw [hcol, Lv, hzp, cvG_of_mem β (hconj n hn _ (hbB 0)), vB_cv]
      rfl
    · rintro ⟨v, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨n, hn, hgn⟩ := hΓ g hg
      refine ⟨n, hn, ?_⟩
      rw [hgn, hcol, Lv, hzp, cvG_of_mem β (hconj n hn _ (hbB 0)), vB_cv]
      rfl
  have hCL : ConjLines B b = {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D} := by
    ext D
    constructor
    · exact fun hD => hB.fus D hD
    · rintro ⟨n, hn, rfl⟩
      refine ⟨?_, n, rfl⟩
      rw [hzp, Subgroup.zpowers_le]
      exact hconj n hn b (hbB 0)
  have hncard : (ConjLines B b).ncard = lineCount (cfgOf Γ).1 := by
    rw [hCL, hlines]
    have himg : Lv β '' Om Γ = Lv β '' (Om Γ ∩ {v | pos v = true}) := by
      apply le_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        have hn := mem_nonzeroL _ (ne_zero_of_mem_Om hv)
        rcases pos_or v hn with hp | hp
        · exact ⟨v, ⟨hv, hp⟩, rfl⟩
        · exact ⟨-v, ⟨homneg v hv, hp⟩, Lv_neg β v⟩
      · exact Set.image_mono Set.inter_subset_left
    have hinj : Set.InjOn (Lv β) (Om Γ ∩ {v | pos v = true}) := by
      rintro v ⟨hv, hpv⟩ w ⟨hw, hpw⟩ hvw
      rcases Lv_eq β (ne_zero_of_mem_Om hw) hvw with h | h
      · exact h.symm
      · exfalso
        exact not_pos_and v (mem_nonzeroL _ (ne_zero_of_mem_Om hv)) ⟨hpv, h ▸ hpw⟩
    rw [himg, hinj.ncard_image, lineCount]
    have : Om Γ ∩ {v | pos v = true} =
        ↑((nonzeroL.filter fun v => (cfgOf Γ).1 (tab v).1 && pos v).toFinset) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, om_iff hyp, List.coe_toFinset,
        List.mem_filter, Bool.and_eq_true]
      tauto
    rw [this, Set.ncard_coe_finset]
  have hm : (cfgOf Γ).1 = mD ∨ (cfgOf Γ).1 = mE := by
    rcases cfgOf_good hyp with h | ⟨h, -⟩ | ⟨h, -⟩ | h | h
    · rw [h, lineCount_mA] at hncard; rcases hbad with h' | h' <;> omega
    · rw [h, lineCount_mB] at hncard; rcases hbad with h' | h' <;> omega
    · rw [h, lineCount_mC] at hncard; rcases hbad with h' | h' <;> omega
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨(cfgOf Γ).1, hm, fun v hv => ?_⟩
  have hLv : Subgroup.zpowers (ε4 b b₁ b₂ b₃ v) = Lv β v := by rw [Lv, ε4_eq_vB β hβ]
  rw [hLv, hCL, hlines]
  constructor
  · rintro ⟨w, hw, hwv⟩
    rcases Lv_eq β (ne_zero_of_mem_Om hw) hwv.symm with h | h
    · rw [← h]; exact ((om_iff hyp w).1 hw).2
    · have := (om_iff hyp (-w)).1 (homneg w hw)
      rw [show -w = v by rw [h, neg_neg]] at this
      exact this.2
  · intro h
    exact ⟨v, (om_iff hyp v).2 ⟨mem_nonzeroL v hv, h⟩, rfl⟩

section Coord

variable {B : Subgroup G} {b₀ b₁ b₂ b₃ : G}

theorem ε4_mem (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) (v : V) :
    ε4 b₀ b₁ b₂ b₃ v ∈ B := by
  have h : ∀ x ∈ ({b₀, b₁, b₂, b₃} : Set G), x ∈ B := fun x hx =>
    hcl ▸ Subgroup.subset_closure hx
  exact B.mul_mem (B.mul_mem (B.mul_mem (B.pow_mem (h _ (by simp)) _)
    (B.pow_mem (h _ (by simp)) _)) (B.pow_mem (h _ (by simp)) _)) (B.pow_mem (h _ (by simp)) _)

open P51T in
theorem cvG_pow [IsElementaryAbelian 3 B] (β : Module.Basis (Fin 4) (ZMod 3) (Additive B))
    {x : G} (hx : x ∈ B) (n : ℕ) : cvG β (x ^ n) = (n : ZMod 3) • cvG β x := by
  rw [cvG_of_mem β (B.pow_mem hx n), cvG_of_mem β hx]
  have h1 : (⟨x ^ n, B.pow_mem hx n⟩ : B) = (⟨x, hx⟩ : B) ^ (n : ℤ) := Subtype.ext (by simp)
  rw [h1, cv_zpow]
  ext j
  simp

open P51T in
theorem ε4_add (hE : IsElemAb 3 4 B) (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) (v w : V) :
    ε4 b₀ b₁ b₂ b₃ (v + w) = ε4 b₀ b₁ b₂ b₃ v * ε4 b₀ b₁ b₂ b₃ w := by
  haveI : IsElementaryAbelian 3 B := hE.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) hE.2 hcl
  refine cvG_inj β (ε4_mem hcl _) (B.mul_mem (ε4_mem hcl _) (ε4_mem hcl _)) ?_
  rw [cvG_mul β (ε4_mem hcl _) (ε4_mem hcl _), cvG_ε4 β hβ, cvG_ε4 β hβ, cvG_ε4 β hβ]

open P51T in
theorem ε4_smul (hE : IsElemAb 3 4 B) (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) (c : ZMod 3)
    (v : V) : ε4 b₀ b₁ b₂ b₃ (c • v) = ε4 b₀ b₁ b₂ b₃ v ^ c.val := by
  haveI : IsElementaryAbelian 3 B := hE.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) hE.2 hcl
  refine cvG_inj β (ε4_mem hcl _) (B.pow_mem (ε4_mem hcl _) _) ?_
  rw [cvG_pow β (ε4_mem hcl _), cvG_ε4 β hβ, cvG_ε4 β hβ, ZMod.natCast_zmod_val]

open P51T in
theorem ε4_inj (hE : IsElemAb 3 4 B) (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) {v w : V}
    (h : ε4 b₀ b₁ b₂ b₃ v = ε4 b₀ b₁ b₂ b₃ w) : v = w := by
  haveI : IsElementaryAbelian 3 B := hE.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) hE.2 hcl
  rw [← cvG_ε4 β hβ v, ← cvG_ε4 β hβ w, h]

open P51T in
theorem ε4_surj (hE : IsElemAb 3 4 B) (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) {x : G}
    (hx : x ∈ B) : ∃ v, ε4 b₀ b₁ b₂ b₃ v = x := by
  haveI : IsElementaryAbelian 3 B := hE.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) hE.2 hcl
  refine ⟨cvG β x, ?_⟩
  rw [ε4_eq_vB β hβ, cvG_of_mem β hx, vB_cv]

theorem ε4_zero : ε4 b₀ b₁ b₂ b₃ 0 = 1 := by simp [ε4]

theorem ε4_e0 (s : ZMod 3) : ε4 b₀ b₁ b₂ b₃ (s • e 0) = b₀ ^ s.val := by
  simp [ε4, e, Pi.single_apply]

end Coord

def emb (x : Fin 3 → ZMod 3) : V := ![0, x 0, x 1, x 2]

def ε3 (b₁ b₂ b₃ : G) (x : Fin 3 → ZMod 3) : G :=
  b₁ ^ (x 0).val * b₂ ^ (x 1).val * b₃ ^ (x 2).val

theorem ε4_emb (b₀ b₁ b₂ b₃ : G) (x : Fin 3 → ZMod 3) :
    ε4 b₀ b₁ b₂ b₃ (emb x) = ε3 b₁ b₂ b₃ x := by
  simp [ε4, ε3, emb]

theorem emb_add (x y : Fin 3 → ZMod 3) : emb (x + y) = emb x + emb y := by
  ext j; fin_cases j <;> simp [emb]

theorem emb_smul (c : ZMod 3) (x : Fin 3 → ZMod 3) : emb (c • x) = c • emb x := by
  ext j; fin_cases j <;> simp [emb]

theorem emb_inj {x y : Fin 3 → ZMod 3} (h : emb x = emb y) : x = y := by
  ext j
  fin_cases j
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3

def wt3 (x : Fin 3 → ZMod 3) : ℕ :=
  (if x 0 ≠ 0 then 1 else 0) + (if x 1 ≠ 0 then 1 else 0) + (if x 2 ≠ 0 then 1 else 0)

def hypU : Fin 13 → (Fin 3 → ZMod 3) :=
  ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0], ![1, 2, 0], ![1, 1, 0], ![1, 0, 2], ![1, 0, 1],
    ![0, 1, 2], ![0, 1, 1], ![1, 2, 0], ![1, 2, 0], ![1, 1, 0], ![1, 1, 0]]

def hypA : Fin 13 → (Fin 3 → ZMod 3) :=
  ![![0, 1, 0], ![1, 0, 0], ![1, 0, 0], ![0, 0, 1], ![0, 0, 1], ![0, 1, 0], ![0, 1, 0],
    ![1, 0, 0], ![1, 0, 0], ![0, 1, 2], ![1, 0, 1], ![0, 1, 1], ![1, 0, 1]]

def hypZ : Fin 13 → (Fin 3 → ZMod 3) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0],
    ![0, 1, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0]]

theorem hypZ_indep : ∀ i : Fin 13, ∀ t t' c : ZMod 3,
    hypZ i + t' • hypU i ≠ c • (hypA i + t • hypU i) := by
  decide +kernel

def hypW : Fin 13 → ℕ := ![1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3]

def φw : ℕ → ℕ := fun w => if w = 1 then 2 else if w = 2 then 1 else w

def KA (m : Fin 7 → Bool) (i : Fin 13) (t : ZMod 3) : ℕ :=
  ((List.product [0, 1, 2] [0, 1, 2]).filter fun p : ZMod 3 × ZMod 3 =>
    m (P51.orbOf (emb (p.1 • hypU i + p.2 • (hypA i + t • hypU i))))).length

def KL (m : Fin 7 → Bool) (s : ZMod 3) (x : Fin 3 → ZMod 3) : ℕ :=
  ((List.product [0, 1, 2] [0, 1, 2]).filter fun p : ZMod 3 × ZMod 3 =>
    m (P51.orbOf ((p.1 * s) • e 0 + p.2 • emb x))).length

open P51 in
theorem KA_eq : ∀ m ∈ [mD, mE], ∀ i : Fin 13, ∀ t : ZMod 3,
    KA m i t = if m = mD then 2 * (if hypW i = 1 then 2 else if hypW i = 2 then 1 else 3)
      else 2 * (if hypW i = 1 then 4 else if hypW i = 2 then 2 else 3) := by
  decide +kernel

open P51 in
theorem KL_eq : ∀ m ∈ [mD, mE], ∀ s : ZMod 3, s ≠ 0 → ∀ x0 x1 x2 : ZMod 3,
    ![x0, x1, x2] ≠ 0 →
    KL m s ![x0, x1, x2] = if m = mD then 2 * (if wt3 ![x0, x1, x2] = 1 then 1
      else if wt3 ![x0, x1, x2] = 2 then 2 else 3)
      else 2 * (if wt3 ![x0, x1, x2] = 1 then 2 else if wt3 ![x0, x1, x2] = 2 then 4 else 3) := by
  decide +kernel

open P51 in
theorem hypU_pat : ∀ m ∈ [mD, mE], ∀ i : Fin 13, m (orbOf (emb (hypU i))) = true := by
  decide +kernel

theorem hypU_ne : ∀ i : Fin 13, emb (hypU i) ≠ 0 := by decide +kernel

theorem hypA_ne : ∀ i : Fin 13, ∀ t : ZMod 3, emb (hypA i + t • hypU i) ≠ 0 := by
  decide +kernel

theorem wt3_pos : ∀ x0 x1 x2 : ZMod 3, ![x0, x1, x2] ≠ 0 →
    1 ≤ wt3 ![x0, x1, x2] ∧ wt3 ![x0, x1, x2] ≤ 3 := by decide +kernel

theorem hypW_mem : ∀ i : Fin 13, 1 ≤ hypW i ∧ hypW i ≤ 3 := by decide

theorem vec3_eta (x : Fin 3 → ZMod 3) : x = ![x 0, x 1, x 2] := by
  ext j; fin_cases j <;> rfl

theorem conjBy_zp (g y : G) : conjBy g (Subgroup.zpowers y) = Subgroup.zpowers (g * y * g⁻¹) := by
  rw [conjBy, MonoidHom.map_zpowers]; rfl

theorem conjBy_conjBy' (g h : G) (H : Subgroup G) : conjBy g (conjBy h H) = conjBy (g * h) H := by
  rw [conjBy, conjBy, conjBy, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjLines_conj {B : Subgroup G} {b g : G} (hg : g ∈ Nor B) {y : G} :
    Subgroup.zpowers y ∈ ConjLines B b → Subgroup.zpowers (g * y * g⁻¹) ∈ ConjLines B b := by
  rintro ⟨hle, h, hh⟩
  refine ⟨?_, g * h, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hle (Subgroup.mem_zpowers y))
  · rw [← conjBy_conjBy', hh, conjBy_zp]

theorem conjLines_conj_iff {B : Subgroup G} {b g : G} (hg : g ∈ Nor B) {y : G} :
    Subgroup.zpowers (g * y * g⁻¹) ∈ ConjLines B b ↔ Subgroup.zpowers y ∈ ConjLines B b := by
  refine ⟨fun h => ?_, conjLines_conj hg⟩
  have := conjLines_conj (Subgroup.inv_mem _ hg) h
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

open P51 in
theorem geom {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}
    (hB : FF81Basis b L B b₁ b₂ b₃) (hbad : CaseBad b B) (i : Fin 13) :
    ∃ g ∈ Nor B, ∃ x : Fin 3 → ZMod 3, x ≠ 0 ∧ wt3 x = φw (hypW i) ∧
      (g * ε3 b₁ b₂ b₃ (hypU i) * g⁻¹ = b ∨ g * ε3 b₁ b₂ b₃ (hypU i) * g⁻¹ = b⁻¹) ∧
      (∃ t : ZMod 3, g * ε3 b₁ b₂ b₃ (hypA i + t • hypU i) * g⁻¹ = ε3 b₁ b₂ b₃ x) ∧
      ∃ t' : ZMod 3, ∃ y : Fin 3 → ZMod 3, (∀ c : ZMod 3, y ≠ c • x) ∧
        g * ε3 b₁ b₂ b₃ (hypZ i + t' • hypU i) * g⁻¹ = ε3 b₁ b₂ b₃ y := by
  obtain ⟨m, hm, hiff⟩ := conjLines_iff hB hbad
  have hE := hB.mono.1
  have hcl := hB.mono.2.1
  have hmL : m ∈ [mD, mE] := by rcases hm with rfl | rfl <;> simp
  set u := hypU i
  set a := hypA i
  have hεu : ε3 b₁ b₂ b₃ u ≠ 1 := by
    intro h
    rw [← ε4_emb b, ← ε4_zero (b₀ := b) (b₁ := b₁) (b₂ := b₂) (b₃ := b₃)] at h
    exact hypU_ne i (ε4_inj hE hcl h)
  have hu : Subgroup.zpowers (ε3 b₁ b₂ b₃ u) ∈ ConjLines B b := by
    rw [← ε4_emb b]
    exact (hiff _ (hypU_ne i)).2 (hypU_pat m hmL i)
  obtain ⟨n, hn, hnb⟩ := hB.fus _ hu
  have hg : n⁻¹ ∈ Nor B := Subgroup.inv_mem _ hn
  have hz : n⁻¹ * ε3 b₁ b₂ b₃ u * n⁻¹⁻¹ ∈ Subgroup.zpowers b := by
    have : ε3 b₁ b₂ b₃ u ∈ conjBy n (Subgroup.zpowers b) := hnb ▸ Subgroup.mem_zpowers _
    obtain ⟨z, hz, hzu⟩ := this
    rw [← hzu]
    simpa [mul_assoc] using hz
  have hb3 : b ^ 3 = 1 := by rw [← hB.hyp.ord]; exact pow_orderOf_eq_one b
  obtain ⟨s, hs0, hsb⟩ : ∃ s : ZMod 3, s ≠ 0 ∧ n⁻¹ * ε3 b₁ b₂ b₃ u * n⁻¹⁻¹ = b ^ s.val := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hk3 : b ^ k = b ^ (k % 3) := by
      rw [← zpow_mod_orderOf, hB.hyp.ord]; norm_cast
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with h | h | h
    · exfalso
      apply hεu
      have : n⁻¹ * ε3 b₁ b₂ b₃ u * n⁻¹⁻¹ = 1 := by rw [← hk, hk3, h, zpow_zero]
      have h2 : ε3 b₁ b₂ b₃ u = n * (n⁻¹ * ε3 b₁ b₂ b₃ u * n⁻¹⁻¹) * n⁻¹ := by group
      rw [h2, this]; group
    · exact ⟨1, by decide, by rw [← hk, hk3, h, show (1 : ZMod 3).val = 1 by decide]; simp⟩
    · exact ⟨2, by decide, by rw [← hk, hk3, h, show (2 : ZMod 3).val = 2 by decide]; simp⟩
  have hs2 : s * s = 1 := (by decide : ∀ s : ZMod 3, s ≠ 0 → s * s = 1) s hs0
  have haB : n⁻¹ * ε3 b₁ b₂ b₃ a * n⁻¹⁻¹ ∈ B := by
    have : ε3 b₁ b₂ b₃ a ∈ B := by rw [← ε4_emb b]; exact ε4_mem hcl _
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp this
  obtain ⟨w, hw⟩ := ε4_surj hE hcl haB
  set t : ZMod 3 := -(w 0 * s) with ht
  set w' : V := w + t • (s • e 0) with hw'
  have hw'0 : w' 0 = 0 := by
    rw [hw']
    simp only [Pi.add_apply, Pi.smul_apply, e, Pi.single_eq_same, smul_eq_mul, mul_one, ht]
    linear_combination (-(w 0)) * hs2
  set x : Fin 3 → ZMod 3 := ![w' 1, w' 2, w' 3] with hx
  have hembx : emb x = w' := by
    ext j; fin_cases j
    · exact hw'0.symm
    · rfl
    · rfl
    · rfl
  have hε : ∀ y, ε3 b₁ b₂ b₃ y = ε4 b b₁ b₂ b₃ (emb y) := fun y => (ε4_emb b _ _ _ y).symm
  set c := MulAut.conj n⁻¹ with hc
  have hgu : c (ε4 b b₁ b₂ b₃ (emb u)) = ε4 b b₁ b₂ b₃ (s • e 0) := by
    rw [← hε, hc, MulAut.conj_apply, hsb, ε4_e0]
  have hga0 : c (ε4 b b₁ b₂ b₃ (emb a)) = ε4 b b₁ b₂ b₃ w := by
    rw [← hε, hc, MulAut.conj_apply, hw]
  have hmap : ∀ p q : ZMod 3, c (ε4 b b₁ b₂ b₃ (emb (p • u + q • (a + t • u)))) =
      ε4 b b₁ b₂ b₃ ((p * s) • e 0 + q • emb x) := by
    intro p q
    rw [hembx, hw']
    simp only [emb_add, emb_smul, ε4_add hE hcl, ε4_smul hE hcl, map_mul, map_pow, hgu, hga0,
      mul_smul]
  have hzero : ∀ v w : V, c (ε4 b b₁ b₂ b₃ v) = ε4 b b₁ b₂ b₃ w → (v = 0 ↔ w = 0) := by
    intro v w h
    constructor
    · rintro rfl
      rw [ε4_zero, map_one, ← ε4_zero (b₀ := b) (b₁ := b₁) (b₂ := b₂) (b₃ := b₃)] at h
      exact (ε4_inj hE hcl h).symm
    · rintro rfl
      rw [ε4_zero, MulEquiv.map_eq_one_iff, ← ε4_zero (b₀ := b) (b₁ := b₁) (b₂ := b₂)
        (b₃ := b₃)] at h
      exact ε4_inj hE hcl h
  have h0pat : m (orbOf 0) = false := by rcases hm with rfl | rfl <;> decide
  have hpat : ∀ v w : V, c (ε4 b b₁ b₂ b₃ v) = ε4 b b₁ b₂ b₃ w → m (orbOf v) = m (orbOf w) := by
    intro v w h
    by_cases hv : v = 0
    · have hw0 := (hzero v w h).1 hv
      rw [hv, hw0]
    · have hw0 : w ≠ 0 := fun h' => hv ((hzero v w h).2 h')
      have key : Subgroup.zpowers (ε4 b b₁ b₂ b₃ v) ∈ ConjLines B b ↔
          Subgroup.zpowers (ε4 b b₁ b₂ b₃ w) ∈ ConjLines B b := by
        rw [← h, hc, MulAut.conj_apply, conjLines_conj_iff hg]
      rw [hiff v hv, hiff w hw0] at key
      exact Bool.eq_iff_iff.mpr key
  have hK : KA m i t = KL m s x := by
    unfold KA KL
    congr 1
    exact List.filter_congr fun p _ => hpat _ _ (hmap p.1 p.2)
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 := hmap 0 1
    simp only [zero_smul, zero_add, one_smul, zero_mul] at h1
    rw [h0] at h1
    have h2 := (hzero _ _ h1).2 (by ext j; fin_cases j <;> rfl)
    exact hypA_ne i t h2
  have hKA := KA_eq m hmL i t
  have hKL := KL_eq m hmL s hs0 (x 0) (x 1) (x 2) (by rwa [← vec3_eta])
  rw [← vec3_eta] at hKL
  have hwi := hypW_mem i
  have hwx := wt3_pos (x 0) (x 1) (x 2) (by rwa [← vec3_eta])
  rw [← vec3_eta] at hwx
  have hzB : n⁻¹ * ε3 b₁ b₂ b₃ (hypZ i) * n⁻¹⁻¹ ∈ B := by
    have : ε3 b₁ b₂ b₃ (hypZ i) ∈ B := by rw [← ε4_emb b]; exact ε4_mem hcl _
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp this
  obtain ⟨wz, hwz⟩ := ε4_surj hE hcl hzB
  set tz : ZMod 3 := -(wz 0 * s) with htz
  set wz' : V := wz + tz • (s • e 0) with hwz'
  have hwz'0 : wz' 0 = 0 := by
    rw [hwz']
    simp only [Pi.add_apply, Pi.smul_apply, e, Pi.single_eq_same, smul_eq_mul, mul_one, htz]
    linear_combination (-(wz 0)) * hs2
  set y : Fin 3 → ZMod 3 := ![wz' 1, wz' 2, wz' 3] with hy
  have hemby : emb y = wz' := by
    ext j; fin_cases j
    · exact hwz'0.symm
    · rfl
    · rfl
    · rfl
  have hz0 : c (ε4 b b₁ b₂ b₃ (emb (hypZ i))) = ε4 b b₁ b₂ b₃ wz := by
    rw [← hε, hc, MulAut.conj_apply, hwz]
  have hmapz : c (ε4 b b₁ b₂ b₃ (emb (hypZ i + tz • u))) = ε4 b b₁ b₂ b₃ (emb y) := by
    rw [hemby, hwz']
    simp only [emb_add, emb_smul, ε4_add hE hcl, ε4_smul hE hcl, map_mul, map_pow, hgu, hz0]
  have hya : c (ε4 b b₁ b₂ b₃ (emb (a + t • u))) = ε4 b b₁ b₂ b₃ (emb x) := by
    have h := hmap 0 1
    simp only [zero_smul, zero_add, one_smul, zero_mul] at h
    exact h
  have hindep : ∀ c' : ZMod 3, y ≠ c' • x := by
    intro c' hc'
    have h1 : c (ε4 b b₁ b₂ b₃ (emb (hypZ i + tz • u))) =
        c (ε4 b b₁ b₂ b₃ (emb (c' • (a + t • u)))) := by
      rw [hmapz, hc', emb_smul, ε4_smul hE hcl, emb_smul, ε4_smul hE hcl, map_pow, hya]
    exact hypZ_indep i t tz c' (emb_inj (ε4_inj hE hcl (c.injective h1)))
  refine ⟨n⁻¹, hg, x, hx0, ?_, ?_, ⟨t, ?_⟩, tz, y, hindep, ?_⟩
  · rw [hK, hKL] at hKA
    unfold φw
    rcases hm with rfl | rfl <;> simp only [if_true, show mE ≠ mD by decide, if_false] at hKA <;>
      split_ifs at hKA ⊢ <;> omega
  · rw [hsb]
    have hb2 : b ^ 2 = b⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hb3]
    rcases (by decide : ∀ s : ZMod 3, s ≠ 0 → s.val = 1 ∨ s.val = 2) s hs0 with h | h <;>
      rw [h]
    · exact Or.inl (pow_one b)
    · exact Or.inr hb2
  · rw [hε, hε]
    exact hya
  · rw [hε, hε]
    exact hmapz

end S36

end CFSG.RankThree.PartTwo.Sec21.FF81
