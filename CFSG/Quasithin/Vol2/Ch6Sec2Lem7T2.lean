module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7T1
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11G
public import CFSG.Quasithin.Vol2.Ch10SecG31J

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD

variable {V : Type} [CommGroup V]

@[expose] def moveIn627 (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, g v * v⁻¹ ∈ W}
  one_mem' v := by simp
  mul_mem' {a b} ha hb v := by
    have e : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact W.mul_mem (ha _) (hb _)
  inv_mem' {a} ha v := by
    have h1 := ha (a⁻¹ v)
    rw [MulAut.apply_inv_self] at h1
    have e : a⁻¹ v * v⁻¹ = (v * (a⁻¹ v)⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem h1

theorem g31G_le_moveIn627 (Gm : Subgroup (MulAut V)) (Δ : Set (Subgroup V)) :
    g31G Gm Δ ≤ moveIn627 (g31V Δ) :=
  iSup₂_le fun _ hX _ hg v => le_g31V hX ((G31.mem_transvGroup_iff.mp hg).2 v)

theorem map_g31V_orbit_le627 {Gm : Subgroup (MulAut V)} {X₀ : Subgroup V} {g : MulAut V}
    (hg : g ∈ Gm) : (g31V (orbitCh611 Gm X₀)).map g.toMonoidHom ≤ g31V (orbitCh611 Gm X₀) := by
  rw [g31V, Subgroup.map_iSup]
  refine iSup_le fun X => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hX => le_g31V (map_mem_orbitCh611 hX hg)

namespace G31Out

variable {Gm : Subgroup (MulAut V)} {X₀ : Subgroup V} (D : G31Out Gm X₀)

theorem exists_block627 {Y : Subgroup V} (hY : Y ∈ orbitCh611 Gm X₀) : ∃ j, Y ∈ D.Δ j := by
  rw [← D.union] at hY
  exact Set.mem_iUnion.mp hY

theorem map_mem_block627 {g : MulAut V} (hg : g ∈ Gm) {i j : Fin D.s} {X X' : Subgroup V}
    (hX : X ∈ D.Δ i) (hX' : X' ∈ D.Δ i) (hXj : X.map g.toMonoidHom ∈ D.Δ j) :
    X'.map g.toMonoidHom ∈ D.Δ j := by
  obtain ⟨k, hk, rfl⟩ := D.gtrans i X hX X' hX'
  have hinv : ∀ Y ∈ orbitCh611 Gm X₀, ∀ c ∈ Gm, Y.map (c : MulAut V).toMonoidHom ∈
      orbitCh611 Gm X₀ := fun Y hY c hc => map_mem_orbitCh611 hY hc
  have hk' : g * k * g⁻¹ ∈ g31G Gm (orbitCh611 Gm X₀) := G31.conj_mem_g31G hinv hg hk
  have e : (X.map k.toMonoidHom).map g.toMonoidHom =
      (X.map g.toMonoidHom).map (g * k * g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext v
    simp
  rw [e]
  exact D.ginv j _ hXj _ hk'

theorem three_le_s627 {g : MulAut V} (hg : g ∈ Gm) (hg3 : g ^ 3 = 1)
    (hmove : X₀.map g.toMonoidHom ∉ D.Δ ⟨0, D.hs⟩) : 3 ≤ D.s := by
  classical
  set i0 : Fin D.s := ⟨0, D.hs⟩ with hi0
  have hX0 : X₀ ∈ D.Δ i0 := D.mem0
  have horb : ∀ (c : MulAut V), c ∈ Gm → X₀.map c.toMonoidHom ∈ orbitCh611 Gm X₀ :=
    fun c hc => ⟨c, hc, rfl⟩
  obtain ⟨a, ha⟩ := D.exists_block627 (horb g hg)
  have hg2 : g ^ 2 ∈ Gm := Gm.pow_mem hg 2
  obtain ⟨b, hb⟩ := D.exists_block627 (horb (g ^ 2) hg2)
  have hmapmap : ∀ (c d : MulAut V) (Y : Subgroup V),
      (Y.map c.toMonoidHom).map d.toMonoidHom = Y.map (d * c).toMonoidHom := by
    intro c d Y
    rw [Subgroup.map_map]
    congr 1
  have hdisj : ∀ {i j : Fin D.s} {Y : Subgroup V}, Y ∈ D.Δ i → Y ∈ D.Δ j → i = j := by
    intro i j Y hi hj
    by_contra hij
    exact Set.disjoint_left.mp (D.disj i j hij) hi hj
  have ha0 : a ≠ i0 := fun h => hmove (h ▸ ha)
  have hb0 : b ≠ i0 := by
    intro hb0
    rw [hb0] at hb
    have h1 : (X₀.map (g ^ 2).toMonoidHom).map (g ^ 2).toMonoidHom ∈ D.Δ i0 :=
      D.map_mem_block627 hg2 hX0 hb hb
    rw [hmapmap, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hg3, one_mul] at h1
    exact ha0 (hdisj ha h1)
  have hba : b ≠ a := by
    intro hba
    rw [hba] at hb
    have h1 : (X₀.map g.toMonoidHom).map g.toMonoidHom ∈ D.Δ a := by
      rw [hmapmap, ← pow_two]
      exact hb
    have h2 : (X₀.map (g ^ 2).toMonoidHom).map g.toMonoidHom ∈ D.Δ a :=
      D.map_mem_block627 hg ha hb h1
    rw [hmapmap, ← pow_succ', hg3, show (1 : MulAut V).toMonoidHom = MonoidHom.id V from rfl,
      Subgroup.map_id] at h2
    exact ha0 (hdisj h2 hX0)
  by_contra hs
  push Not at hs
  have ha' := a.2
  have hb' := b.2
  have hne1 : (a : ℕ) ≠ 0 := fun h => ha0 (Fin.ext h)
  have hne2 : (b : ℕ) ≠ 0 := fun h => hb0 (Fin.ext h)
  have hne3 : (b : ℕ) ≠ a := fun h => hba (Fin.ext h)
  omega


theorem eq_one_of_fix0_627 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 Gm = ⊥)
    {g : MulAut V} (hg : g ∈ g31G Gm (D.Δ ⟨0, D.hs⟩))
    (hfix : ∀ v ∈ g31V (D.Δ ⟨0, D.hs⟩), g v = v) : g = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  set W₀ := g31V (orbitCh611 Gm X₀) with hW₀
  set G₀ := g31G Gm (orbitCh611 Gm X₀) with hG₀
  set N : Subgroup (MulAut V) := G₀ ⊓ fixingSubgroup (MulAut V) (W₀ : Set V) with hN
  have hfixW : ∀ {x : MulAut V}, x ∈ fixingSubgroup (MulAut V) (W₀ : Set V) →
      ∀ w ∈ W₀, x w = w := fun hx w hw => (mem_fixingSubgroup_iff (MulAut V)).mp hx w hw
  have hgG₀ : g ∈ G₀ := by
    rw [hG₀, ← D.supG]
    exact le_iSup (fun i => g31G Gm (D.Δ i)) _ hg
  have hgW : g ∈ fixingSubgroup (MulAut V) (W₀ : Set V) := by
    have hle : (⨆ i, g31V (D.Δ i)) ≤ g.toMonoidHom.eqLocus (MonoidHom.id V) := by
      refine iSup_le fun i v hv => ?_
      by_cases hi : i = ⟨0, D.hs⟩
      · subst hi
        exact hfix v hv
      · exact D.cent ⟨0, D.hs⟩ i (Ne.symm hi) g hg v hv
    rw [D.supV] at hle
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact hle hv
  have hNle : N ≤ Gm := inf_le_left.trans (g31G_le Gm _)
  have hmove : ∀ x ∈ G₀, ∀ v : V, x v * v⁻¹ ∈ W₀ := fun x hx v =>
    g31G_le_moveIn627 Gm _ hx v
  have hW₀inv : ∀ y ∈ Gm, ∀ w ∈ W₀, y w ∈ W₀ := fun y hy w hw =>
    map_g31V_orbit_le627 hy ⟨w, hw, rfl⟩
  have hinvΔ : ∀ Y ∈ orbitCh611 Gm X₀, ∀ c ∈ Gm, Y.map (c : MulAut V).toMonoidHom ∈
      orbitCh611 Gm X₀ := fun Y hY c hc => map_mem_orbitCh611 hY hc
  have hconjN : ∀ y ∈ Gm, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
    intro y hy x hx
    refine ⟨G31.conj_mem_g31G hinvΔ hy hx.1, ?_⟩
    show y * x * y⁻¹ ∈ fixingSubgroup (MulAut V) (W₀ : Set V)
    rw [mem_fixingSubgroup_iff]
    intro w hw
    show (y * x * y⁻¹) w = w
    rw [MulAut.mul_apply, MulAut.mul_apply, hfixW hx.2 _ (hW₀inv _ (Gm.inv_mem hy) w hw),
      MulAut.apply_inv_self]
  have hNnorm : Gm ≤ Subgroup.normalizer (N : Set (MulAut V)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjN y hy x, fun hx => ?_⟩
    have := hconjN y⁻¹ (Gm.inv_mem hy) _ hx
    simpa [mul_assoc] using this
  have hN2 : IsPGroup 2 N := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    ext v
    have hw := hmove _ x.2.1 v
    set w := (x : MulAut V) v * v⁻¹ with hwdef
    have hxv : (x : MulAut V) v = w * v := by rw [hwdef]; group
    have hxw : (x : MulAut V) w = w := hfixW x.2.2 w hw
    show ((x : MulAut V) ^ 2) v = v
    rw [pow_two, MulAut.mul_apply, hxv, map_mul, hxw, hxv, ← mul_assoc, ← pow_two, hV w, one_mul]
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNle hNnorm hN2
  rw [hO2] at hle
  exact Subgroup.mem_bot.mp (hle ⟨hgG₀, hgW⟩)

theorem exists_elemAbelian_27_627 [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hfaith : ∀ g ∈ g31G Gm (D.Δ ⟨0, D.hs⟩), (∀ v ∈ g31V (D.Δ ⟨0, D.hs⟩), g v = v) → g = 1)
    (h3 : 3 ≤ D.s) :
    ∃ E : Subgroup (MulAut V), E ≤ g31G Gm (orbitCh611 Gm X₀) ∧ IsElemAbelian 3 E ∧
      27 ≤ Nat.card E := by
  classical
  have hV0sq : ∀ w : ↥D.V0, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  obtain ⟨φ, hφ⟩ := exists_mulAut_order_three_ch611 hV0sq D.eight
  obtain ⟨g₀, hg₀, hg₀φ⟩ := D.aut φ
  set i0 : Fin D.s := ⟨0, D.hs⟩ with hi0
  set i1 : Fin D.s := ⟨1, by omega⟩ with hi1
  set i2 : Fin D.s := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [hi0, hi2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [hi1, hi2, Fin.ext_iff]
  obtain ⟨c₁, -, hc₁V, hc₁G⟩ := D.trans i0 i1
  obtain ⟨c₂, -, hc₂V, hc₂G⟩ := D.trans i0 i2
  have hconjG : ∀ (c : MulAut V) (k : Fin D.s),
      (g31G Gm (D.Δ i0)).map (MulAut.conj c).toMonoidHom = g31G Gm (D.Δ k) →
        c * g₀ * c⁻¹ ∈ g31G Gm (D.Δ k) := by
    intro c k hk
    rw [← hk]
    exact ⟨g₀, hg₀, rfl⟩
  set g₁ := c₁ * g₀ * c₁⁻¹ with hg₁def
  set g₂ := c₂ * g₀ * c₂⁻¹ with hg₂def
  have hg₁ : g₁ ∈ g31G Gm (D.Δ i1) := hconjG c₁ i1 hc₁G
  have hg₂ : g₂ ∈ g31G Gm (D.Δ i2) := hconjG c₂ i2 hc₂G
  have hpow0 : ∀ k : ℕ, ∀ w : ↥D.V0, (g₀ ^ k) (w : V) = (((φ ^ k) w : ↥D.V0) : V) := by
    intro k
    induction k with
    | zero => intro w; rfl
    | succ k ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply, hg₀φ]
  have hconjpow : ∀ (c : MulAut V) (k : ℕ) (w : V),
      ((c * g₀ * c⁻¹) ^ k) (c w) = c ((g₀ ^ k) w) := by
    intro c k w
    rw [conj_pow, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hmemV : ∀ (c : MulAut V) (k : Fin D.s), (D.V0).map c.toMonoidHom = g31V (D.Δ k) →
      ∀ w ∈ D.V0, c w ∈ g31V (D.Δ k) := by
    intro c k hk w hw
    rw [← hk]
    exact ⟨w, hw, rfl⟩
  have hφeq : ∀ a b : ℕ, a < 3 → b < 3 → (∀ w : ↥D.V0, (((φ ^ a) w : ↥D.V0) : V) =
      (((φ ^ b) w : ↥D.V0) : V)) → a = b := by
    intro a b ha hb hab
    have h1 : φ ^ a = φ ^ b := by
      ext w
      exact hab w
    rw [pow_eq_pow_iff_modEq, hφ] at h1
    unfold Nat.ModEq at h1
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
    exact h1
  have hg₀3 : g₀ ^ 3 = 1 := by
    refine hfaith _ ((g31G Gm (D.Δ i0)).pow_mem hg₀ 3) ?_
    intro v hv
    rw [hpow0 3 ⟨v, hv⟩, ← hφ, pow_orderOf_eq_one]
    rfl
  set E := Subgroup.closure ({g₀, g₁, g₂} : Set (MulAut V)) with hE
  have hg₀E : g₀ ∈ E := Subgroup.subset_closure (by simp)
  have hg₁E : g₁ ∈ E := Subgroup.subset_closure (by simp)
  have hg₂E : g₂ ∈ E := Subgroup.subset_closure (by simp)
  have hcomm : ({g₀, g₁, g₂} : Set (MulAut V)).Pairwise Commute := by
    have c01 := D.comm i0 i1 h01 g₀ hg₀ g₁ hg₁
    have c02 := D.comm i0 i2 h02 g₀ hg₀ g₂ hg₂
    have c12 := D.comm i1 i2 h12 g₁ hg₁ g₂ hg₂
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hxy
      | exact c01 | exact c01.symm | exact c02 | exact c02.symm | exact c12 | exact c12.symm
  have hEcomm : IsMulCommutative ↥E := Subgroup.isMulCommutative_closure hcomm
  refine ⟨E, ?_, ⟨hEcomm, ?_⟩, ?_⟩
  · rw [hE, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hle : ∀ k : Fin D.s, g31G Gm (D.Δ k) ≤ g31G Gm (orbitCh611 Gm X₀) := fun k => by
      rw [← D.supG]
      exact le_iSup (fun i => g31G Gm (D.Δ i)) k
    rcases hx with rfl | rfl | rfl
    · exact hle _ hg₀
    · exact hle _ hg₁
    · exact hle _ hg₂
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hg₀3
      · rw [hg₁def, conj_pow, hg₀3, mul_one, mul_inv_cancel]
      · rw [hg₂def, conj_pow, hg₀3, mul_one, mul_inv_cancel]
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := by
        have := hEcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [hxy.mul_pow, ihx, ihy, mul_one]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  ·
    let F : Fin 3 × Fin 3 × Fin 3 → ↥E := fun t =>
      ⟨g₀ ^ (t.1 : ℕ) * g₁ ^ (t.2.1 : ℕ) * g₂ ^ (t.2.2 : ℕ),
        E.mul_mem (E.mul_mem (E.pow_mem hg₀E _) (E.pow_mem hg₁E _)) (E.pow_mem hg₂E _)⟩
    have hF : Function.Injective F := by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      have h1 : g₀ ^ (a : ℕ) * g₁ ^ (b : ℕ) * g₂ ^ (c : ℕ) =
          g₀ ^ (a' : ℕ) * g₁ ^ (b' : ℕ) * g₂ ^ (c' : ℕ) := congrArg Subtype.val h
      have hfix : ∀ (g : MulAut V) (i j : Fin D.s), i ≠ j → g ∈ g31G Gm (D.Δ i) →
          ∀ k : ℕ, ∀ v ∈ g31V (D.Δ j), (g ^ k) v = v := fun g i j hij hg k v hv =>
        D.cent i j hij _ ((g31G Gm (D.Δ i)).pow_mem hg k) v hv
      have ha : (a : ℕ) = a' := by
        apply hφeq a a' a.2 a'.2
        intro w
        have h2 := congrArg (fun g : MulAut V => g (w : V)) h1
        simp only [MulAut.mul_apply] at h2
        rw [hfix g₂ i2 i0 h02.symm hg₂ _ w w.2, hfix g₁ i1 i0 h01.symm hg₁ _ w w.2,
          hfix g₂ i2 i0 h02.symm hg₂ _ w w.2, hfix g₁ i1 i0 h01.symm hg₁ _ w w.2,
          hpow0, hpow0] at h2
        exact h2
      have hb : (b : ℕ) = b' := by
        apply hφeq b b' b.2 b'.2
        intro w
        have hw1 := hmemV c₁ i1 hc₁V w w.2
        have h2 := congrArg (fun g : MulAut V => g (c₁ w)) h1
        simp only [MulAut.mul_apply] at h2
        rw [hfix g₂ i2 i1 h12.symm hg₂ _ _ hw1, hfix g₂ i2 i1 h12.symm hg₂ _ _ hw1] at h2
        have hm : ∀ k : ℕ, (g₁ ^ k) (c₁ w) ∈ g31V (D.Δ i1) := by
          intro k
          rw [hg₁def, hconjpow]
          exact hmemV c₁ i1 hc₁V _ (by rw [hpow0]; exact ((φ ^ k) w).2)
        rw [hfix g₀ i0 i1 h01 hg₀ _ _ (hm _), hfix g₀ i0 i1 h01 hg₀ _ _ (hm _), hg₁def,
          hconjpow, hconjpow] at h2
        have h3 := c₁.injective h2
        rw [hpow0, hpow0] at h3
        exact h3
      have hc : (c : ℕ) = c' := by
        apply hφeq c c' c.2 c'.2
        intro w
        have hw2 := hmemV c₂ i2 hc₂V w w.2
        have h2 := congrArg (fun g : MulAut V => g (c₂ w)) h1
        simp only [MulAut.mul_apply] at h2
        have hm : ∀ k : ℕ, (g₂ ^ k) (c₂ w) ∈ g31V (D.Δ i2) := by
          intro k
          rw [hg₂def, hconjpow]
          exact hmemV c₂ i2 hc₂V _ (by rw [hpow0]; exact ((φ ^ k) w).2)
        rw [hfix g₁ i1 i2 h12 hg₁ _ _ (hm _), hfix g₁ i1 i2 h12 hg₁ _ _ (hm _),
          hfix g₀ i0 i2 h02 hg₀ _ _ (hm _), hfix g₀ i0 i2 h02 hg₀ _ _ (hm _), hg₂def,
          hconjpow, hconjpow] at h2
        have h3 := c₂.injective h2
        rw [hpow0, hpow0] at h3
        exact h3
      rw [Fin.ext ha, Fin.ext hb, Fin.ext hc]
    have := Nat.card_le_card_of_injective F hF
    simpa [Nat.card_prod] using this

end G31Out

@[expose] def restrictHom627 (W : Subgroup V) : ↥(stabSubCh611 W) →* MulAut ↥W where
  toFun g := restrictCh611 g.1 g.2
  map_one' := by
    ext w
    rfl
  map_mul' a b := by
    ext w
    rfl

theorem restrictHom627_apply (W : Subgroup V) (g : ↥(stabSubCh611 W)) (w : ↥W) :
    ((restrictHom627 W g w : ↥W) : V) = (g : MulAut V) w := rfl

namespace G31Out

variable {Gm : Subgroup (MulAut V)} {X₀ : Subgroup V} (D : G31Out Gm X₀)

theorem fix_V0_of_normalizes_sylow627 [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {δ : MulAut V} (hδV : δ ∈ stabSubCh611 (g31V (D.Δ ⟨0, D.hs⟩)))
    {P : Subgroup (MulAut V)} (hPG : P ≤ g31G Gm (D.Δ ⟨0, D.hs⟩)) (hP2 : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.relIndex (g31G Gm (D.Δ ⟨0, D.hs⟩)))
    (hδP : δ ∈ Subgroup.normalizer (P : Set (MulAut V))) (hodd : Odd (orderOf δ)) :
    ∀ v ∈ g31V (D.Δ ⟨0, D.hs⟩), δ v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V0 := g31V (D.Δ ⟨0, D.hs⟩) with hV0
  set G0 := g31G Gm (D.Δ ⟨0, D.hs⟩) with hG0
  have hG0S : G0 ≤ stabSubCh611 V0 := D.g31G_le_stab _
  have : Finite (MulAut ↥V0) :=
    Finite.of_injective (fun g : MulAut ↥V0 => (g : ↥V0 → ↥V0)) DFunLike.coe_injective
  set res := restrictHom627 V0 with hres
  set f : ↥G0 →* MulAut ↥V0 := res.comp (Subgroup.inclusion hG0S) with hf
  have hfsurj : Function.Surjective f := by
    intro φ
    obtain ⟨g, hg, hgφ⟩ := D.aut φ
    refine ⟨⟨g, hg⟩, ?_⟩
    ext w
    exact hgφ w
  set P' := (P.subgroupOf G0).map f with hP'
  have hPG2 : IsPGroup 2 (P.subgroupOf G0) := by
    intro x
    obtain ⟨k, hk⟩ := hP2 ⟨(x : ↥G0), x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hP'2 : IsPGroup 2 P' := hPG2.map f
  have hP'i : ¬ 2 ∣ P'.index := fun h2 => hPi (h2.trans (Subgroup.index_map_dvd _ hfsurj))
  set δ' := res ⟨δ, hδV⟩ with hδ'
  have hconj : ∀ (c : MulAut V) (hc : c ∈ Subgroup.normalizer (P : Set (MulAut V)))
      (hcS : c ∈ stabSubCh611 V0), ∀ y ∈ P', res ⟨c, hcS⟩ * y * (res ⟨c, hcS⟩)⁻¹ ∈ P' := by
    rintro c hc hcS _ ⟨x, hx, rfl⟩
    have hxP : ((x : ↥G0) : MulAut V) ∈ P := hx
    have hcx : c * (x : MulAut V) * c⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hc _).mp hxP
    refine ⟨⟨c * (x : MulAut V) * c⁻¹, hPG hcx⟩, hcx, ?_⟩
    ext w
    rfl
  have hδ'N : δ' ∈ Subgroup.normalizer (P' : Set (MulAut ↥V0)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj δ hδP hδV y, fun hy => ?_⟩
    have h1 := hconj δ⁻¹ ((Subgroup.normalizer _).inv_mem hδP)
      ((stabSubCh611 V0).inv_mem hδV) _ hy
    have e : res ⟨δ⁻¹, (stabSubCh611 V0).inv_mem hδV⟩ = δ'⁻¹ := by
      rw [hδ', ← map_inv]
      rfl
    rw [e, inv_inv] at h1
    simpa [mul_assoc] using h1
  have hoddδ' : Odd (orderOf δ') := by
    have h1 : orderOf δ' ∣ orderOf (⟨δ, hδV⟩ : ↥(stabSubCh611 V0)) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hV0sq : ∀ w : ↥V0, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have h1 := eq_one_of_mem_normalizer_sylow_ch627 hV0sq hP'2 hP'i hδ'N hoddδ'
  intro v hv
  have := congrArg (fun φ : MulAut ↥V0 => ((φ ⟨v, hv⟩ : ↥V0) : V)) h1
  rw [hδ', hres, restrictHom627_apply] at this
  simpa using this

theorem normalizes_block0_627 [Finite V] {δ : MulAut V} (hδ : δ ∈ Gm)
    (h0 : X₀.map δ.toMonoidHom ∈ D.Δ ⟨0, D.hs⟩) :
    δ ∈ Subgroup.normalizer ((g31G Gm (D.Δ ⟨0, D.hs⟩) : Subgroup (MulAut V)) : Set (MulAut V)) ∧
      δ ∈ stabSubCh611 (g31V (D.Δ ⟨0, D.hs⟩)) := by
  classical
  have : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  have hmap : ∀ X ∈ D.Δ ⟨0, D.hs⟩, X.map δ.toMonoidHom ∈ D.Δ ⟨0, D.hs⟩ := fun X hX =>
    D.map_mem_block627 hδ D.mem0 hX h0
  have hGle : (g31G Gm (D.Δ ⟨0, D.hs⟩)).map (MulAut.conj δ).toMonoidHom ≤
      g31G Gm (D.Δ ⟨0, D.hs⟩) := by
    rw [g31G, Subgroup.map_iSup]
    refine iSup_le fun X => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hX => ?_
    rw [G31.map_conj_transvGroup hδ]
    exact transvGroup_le_g31G Gm (hmap X hX)
  have hVle : (g31V (D.Δ ⟨0, D.hs⟩)).map δ.toMonoidHom ≤ g31V (D.Δ ⟨0, D.hs⟩) := by
    rw [g31V, Subgroup.map_iSup]
    refine iSup_le fun X => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hX => le_g31V (hmap X hX)
  have hGeq := Subgroup.eq_of_le_of_card_ge hGle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective])
  have hVeq := Subgroup.eq_of_le_of_card_ge hVle
    (by rw [Subgroup.card_map_of_injective δ.injective])
  refine ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hGeq, fun w hw => ⟨?_, ?_⟩⟩
  · exact hVle ⟨w, hw, rfl⟩
  · rw [← hVeq] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simpa using hw'

theorem isSylowTwoOf_inf_G0_627' [Finite V] {P Gm₁ : Subgroup (MulAut V)}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P Gm₁) (hGm₁ : Gm₁ ≤ Gm)
    (hN₁G : g31G Gm (orbitCh611 Gm X₀) ≤ Gm₁) :
    CFSG.QuasithinUnique.IsSylowTwoOf (P ⊓ g31G Gm (D.Δ ⟨0, D.hs⟩))
      (g31G Gm (D.Δ ⟨0, D.hs⟩)) := by
  classical
  have : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  set N₁ := g31G Gm (orbitCh611 Gm X₀) with hN₁
  have hN₁le : N₁ ≤ Gm₁ := hN₁G
  have hinvΔ : ∀ Y ∈ orbitCh611 Gm X₀, ∀ c ∈ Gm, Y.map (c : MulAut V).toMonoidHom ∈
      orbitCh611 Gm X₀ := fun Y hY c hc => map_mem_orbitCh611 hY hc
  have hN₁norm : Gm₁ ≤ Subgroup.normalizer (N₁ : Set (MulAut V)) := by
    intro y hy
    replace hy := hGm₁ hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => G31.conj_mem_g31G hinvΔ hy hx, fun hx => ?_⟩
    have := G31.conj_mem_g31G hinvΔ (Gm.inv_mem hy) hx
    simpa [mul_assoc] using this
  have h1 := A4.isSylowTwoOf_inf_normal hP hN₁le hN₁norm
  have hG0N₁ : g31G Gm (D.Δ ⟨0, D.hs⟩) ≤ N₁ := by
    rw [hN₁, ← D.supG]
    exact le_iSup (fun i => g31G Gm (D.Δ i)) _
  have hG0norm : N₁ ≤ Subgroup.normalizer ((g31G Gm (D.Δ ⟨0, D.hs⟩) : Subgroup (MulAut V)) :
      Set (MulAut V)) := by
    rw [hN₁, ← D.supG]
    refine iSup_le fun i => ?_
    by_cases hi : i = ⟨0, D.hs⟩
    · subst hi
      exact Subgroup.le_normalizer
    · intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro b
      have hcomm : ∀ a' ∈ g31G Gm (D.Δ i), ∀ b ∈ g31G Gm (D.Δ ⟨0, D.hs⟩),
          a' * b * a'⁻¹ = b := fun a' ha' b hb => by
        rw [D.comm i ⟨0, D.hs⟩ hi a' ha' b hb, mul_inv_cancel_right]
      constructor
      · intro hb
        rw [hcomm a ha b hb]
        exact hb
      · intro hb
        have e : b = a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ := by group
        rw [e, hcomm a⁻¹ ((g31G Gm (D.Δ i)).inv_mem ha) _ hb]
        exact hb
  have h2 := A4.isSylowTwoOf_inf_normal h1 hG0N₁ hG0norm
  rwa [inf_assoc, inf_eq_right.mpr hG0N₁] at h2

end G31Out

section PartA

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_of_two_elem627 {Gm : Subgroup Y} {δ : Y} (hδ3 : δ ^ 3 = 1)
    (hδN : δ ∈ Subgroup.normalizer (Gm : Set Y)) {g : Y} (hg : g ∈ Gm) {k : ℕ}
    (hk : (g * δ) ^ 2 ^ k = 1) : g * δ ∈ Gm := by
  have hpow : ∀ n : ℕ, (g * δ) ^ n * (δ ^ n)⁻¹ ∈ Gm := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : δ ^ n * g * (δ ^ n)⁻¹ ∈ Gm :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem hδN n) g).mp hg
      have e : (g * δ) ^ (n + 1) * (δ ^ (n + 1))⁻¹ =
          ((g * δ) ^ n * (δ ^ n)⁻¹) * (δ ^ n * g * (δ ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact Gm.mul_mem ih hc
  have h1 := hpow (2 ^ k)
  rw [hk, one_mul] at h1
  have hδk : δ ^ 2 ^ k ∈ Gm := by simpa using Gm.inv_mem h1
  have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have : 2 ^ k % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      omega
    omega
  have hδpow : ∀ m : ℕ, δ ^ m = δ ^ (m % 3) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hδ3, one_pow, one_mul]
  have hδmem : δ ∈ Gm := by
    rw [hδpow] at hδk
    rcases hmod with h | h
    · rw [h, pow_one] at hδk
      exact hδk
    · rw [h] at hδk
      have := Gm.pow_mem hδk 2
      rw [← pow_mul, hδpow] at this
      simpa using this
  exact Gm.mul_mem hg hδmem

end PartA

section PartA2

variable {Q : Type} [CommGroup Q]

theorem eq_of_ne_one_of_card_two627 {X : Type*} [Group X] (hX : Nat.card X = 2) {a b : X}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : X)).mp hX
  exact (hy a ha).trans (hy b hb).symm

theorem sq_eq_one_of_moves627 (hQ : ∀ q : Q, q ^ 2 = 1) {X : Subgroup Q}
    (hX : Nat.card X = 2) {g : MulAut Q} (hg : ∀ q : Q, g q * q⁻¹ ∈ X) : g ^ 2 = 1 := by
  have hfixX : ∀ x ∈ X, g x = x := by
    intro x hx
    by_contra hne
    have hx1 : x ≠ 1 := fun h0 => hne (by rw [h0, map_one])
    have hc1 : g x * x⁻¹ ≠ 1 := fun h0 => hne (by rwa [mul_inv_eq_one] at h0)
    have heq := eq_of_ne_one_of_card_two627 hX (a := ⟨g x * x⁻¹, hg x⟩) (b := ⟨x, hx⟩)
      (fun h0 => hc1 (congrArg Subtype.val h0)) (fun h0 => hx1 (congrArg Subtype.val h0))
    have heq' : g x * x⁻¹ = x := congrArg Subtype.val heq
    have hgx : g x = 1 := by
      calc g x = (g x * x⁻¹) * x := by group
        _ = x ^ 2 := by rw [heq', pow_two]
        _ = 1 := hQ x
    exact hx1 (g.injective (hgx.trans (map_one g).symm))
  ext q
  set c := g q * q⁻¹ with hc
  have h1 : g q = c * q := by rw [hc]; group
  show (g ^ 2) q = q
  rw [pow_two, MulAut.mul_apply, h1, map_mul, hfixX c (hg q), h1, ← mul_assoc, ← pow_two, hQ,
    one_mul]

end PartA2

end CFSG.Quasithin.H13
