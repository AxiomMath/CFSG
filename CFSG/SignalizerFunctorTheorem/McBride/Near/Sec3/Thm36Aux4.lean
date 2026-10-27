module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux3
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux2

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

variable {Γ : Type u} [Group Γ]

structure TermSetting (p : ℕ) (A W Y X₁ X₂ Z₁ Z₂ W₀ : Subgroup Γ) : Prop where
  near : NearAsolvAction p A W
  sol_eq : sol W = ⊥
  ne_bot : W ≠ ⊥
  pair : (Z₁, Z₂) ∈ iPairsY A W Y
  key : ∀ N : Subgroup Γ, N ≤ W → Admits W N → Admits A N → N ⊓ Z₁ ≤ Z₂ → N = ⊥
  hW : W = Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ)
  hX₁ : IsDAIn A W X₁
  hX₂ : IsDAIn A W X₂
  chief : IsChiefFactorOf (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) X₁ X₂
  nonsolv : ¬ IsSolvableSection X₁ X₂
  X₂Y : X₂ ⊓ cenIn W (A : Set Γ) ≤ Y
  W₀K : W₀ ≤ kOf W
  W₀perf : Group.IsPerfect ↥W₀
  W₀Z₁ : W₀ ≤ Z₁
  W₀adm : Admits (Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A) W₀
  W₀sup : W₀ ⊔ Z₂ = Z₁
  W₀inf : W₀ ⊓ Z₂ = ⊥

namespace TermSetting

variable [Finite Γ] {p : ℕ} {A W Y X₁ X₂ Z₁ Z₂ W₀ : Subgroup Γ}
  (S : TermSetting p A W Y X₁ X₂ Z₁ Z₂ W₀)

omit [Finite Γ] in
theorem D_le (_ : TermSetting p A W Y X₁ X₂ Z₁ Z₂ W₀) : cenIn W (A : Set Γ) ≤ W := inf_le_left

include S

omit [Finite Γ] in
theorem comm_A {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have := S.near.elemAbelian.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

omit S [Finite Γ] in
theorem D_cen : cenIn W (A : Set Γ) ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right

omit [Finite Γ] in
theorem W₀_DA : Admits (cenIn W (A : Set Γ) ⊔ A) W₀ :=
  (sup_le (le_sup_right.trans le_sup_left) le_sup_right : cenIn W (A : Set Γ) ⊔ A ≤
    Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A).trans S.W₀adm

omit [Finite Γ] in
theorem W₀_comm {w z : Γ} (hw : w ∈ W₀) (hz : z ∈ Z₂) : w * z = z * w := by
  have hZ₁adm : Admits Z₁ W₀ := Thm33a.le_H.trans S.W₀adm
  have hZ₂adm : Admits Z₁ Z₂ := Thm33a.le_H.trans (Thm33a.pair_admits_H₂ S.pair)
  have hZ₂Z₁ : Z₂ ≤ Z₁ := Thm32.le_of_mem_iPairsY S.pair
  exact (Thm33a.commute_of_inf_eq_bot hZ₁adm hZ₂adm S.W₀Z₁ hZ₂Z₁ S.W₀inf hw hz).eq

theorem admits_A_kOf : Admits A (kOf W) :=
  S.near.admits.trans (Thm211.normalizer_le_normalizer_kOf W)

theorem admits_kOf_k1 :
    Admits (kOf W) (k1 W W₀) := by
  have hdp := lemma213a S.near S.sol_eq S.ne_bot S.W₀K S.W₀_DA S.W₀perf
  rw [← hdp.sup_eq]
  refine sup_le Subgroup.le_normalizer ?_
  refine Thm211.admits_iff.mpr fun y hy x hx => ?_
  have hc : Commute x y := hdp.commute x hx y hy
  have : y * x * y⁻¹ = x := by
    rw [← hc.eq]
    group
  rw [this]
  exact hx

theorem admits_Z₂_k1 : Admits Z₂ (k1 W W₀) := by
  intro z hz
  have hzW : z ∈ W := (Thm32.le_of_mem_iPairsY S.pair |>.trans S.pair.1.1.1) hz
  have hzK : z ∈ Subgroup.normalizer (kOf W : Set Γ) := (Nonsolv.le_normalizer_kOf W) hzW
  have hzC : z ∈ Subgroup.centralizer (W₀ : Set Γ) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => S.W₀_comm hw hz
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hzK, Thm211.normalizer_le_normalizer_centralizer W₀
      ((Subgroup.centralizer_le_normalizer (W₀ : Set Γ)) hzC)⟩

theorem admits_A_k1 : Admits A (k1 W W₀) :=
  Lemma213.admits_cenIn S.admits_A_kOf (le_sup_right.trans S.W₀_DA)

theorem admits_D_k1 : Admits (cenIn W (A : Set Γ)) (k1 W W₀) :=
  Lemma213.admits_cenIn (S.D_le.trans (Nonsolv.le_normalizer_kOf W)) (le_sup_left.trans S.W₀_DA)

omit S [Finite Γ] in
theorem k1_le : k1 W W₀ ≤ W := inf_le_left.trans (kOf_le W)

theorem admits_W_k1
    (hX₁k : Admits X₁ (k1 W W₀)) : Admits W (k1 W W₀) := by
  have hW₀k : Admits W₀ (k1 W W₀) := S.W₀K.trans S.admits_kOf_k1
  have hZ₁k : Admits Z₁ (k1 W W₀) := by
    rw [← S.W₀sup]
    exact sup_le hW₀k S.admits_Z₂_k1
  calc W = Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ) := S.hW
    _ ≤ Subgroup.normalizer ((k1 W W₀ : Subgroup Γ) : Set Γ) :=
      sup_le (sup_le hZ₁k hX₁k) S.admits_D_k1

theorem k1_eq_bot
    (hX₁k : Admits X₁ (k1 W W₀)) : k1 W W₀ = ⊥ := by
  have hk := S.admits_W_k1 hX₁k
  have hZ₁W : Z₁ ≤ W := Thm33a.pair_le S.pair
  refine S.key _ (k1_le (W := W) (W₀ := W₀)) hk S.admits_A_k1 ?_
  by_contra hle
  have hHk : Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A ≤ Subgroup.normalizer ((k1 W W₀ : Subgroup Γ) : Set Γ) :=
    sup_le (sup_le (hZ₁W.trans hk) (S.D_le.trans hk)) S.admits_A_k1
  have hM : Admits (Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (k1 W W₀ ⊓ Z₁) :=
    Admits.inf hHk (Thm33a.pair_admits_H S.pair)
  rcases Thm33a.chief_dichotomy (Thm33a.pair_chief S.pair) hM inf_le_right with h1 | h1
  · exact hle h1
  · refine Thm33a.false_of_commute S.pair inf_le_right S.W₀Z₁ h1 S.W₀sup ?_
    intro m hm w hw
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hm).1).2 w
      hw).symm

theorem Z₂_eq_bot
    (hk : k1 W W₀ = ⊥) : Z₂ = ⊥ := by
  have hcen : cenIn W (W₀ : Set Γ) = ⊥ :=
    lemma213c S.near S.sol_eq S.ne_bot S.W₀K S.W₀_DA S.W₀perf hk
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzW : z ∈ W := (Thm33a.pair_le S.pair) (Thm33a.pair_le₂ S.pair hz)
  have hzC : z ∈ cenIn W (W₀ : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨hzW, Subgroup.mem_centralizer_iff.mpr fun w hw => S.W₀_comm hw hz⟩
  rw [hcen] at hzC
  exact hzC

theorem Y_eq_bot
    (hk : k1 W W₀ = ⊥) : Y = ⊥ := by
  rw [← Thm33a.pair_inf S.pair, S.Z₂_eq_bot hk, bot_inf_eq]

omit [Finite Γ] in
theorem D_nor_X₂ : cenIn W (A : Set Γ) ≤ Subgroup.normalizer (X₂ : Set Γ) :=
  le_sup_left.trans S.hX₂.2

omit [Finite Γ] in
theorem D_nor_X₁ : cenIn W (A : Set Γ) ≤ Subgroup.normalizer (X₁ : Set Γ) :=
  le_sup_left.trans S.hX₁.2

omit [Finite Γ] in
theorem X₁_nor_X₂ : X₁ ≤ Subgroup.normalizer (X₂ : Set Γ) :=
  (le_sup_left.trans le_sup_left).trans S.chief.1.2

theorem false_of_inf_le
    (hi : kOf W ⊓ X₁ ≤ X₂) : False := by
  set D := cenIn W (A : Set Γ) with hDdef
  set D₁ := cenIn (k1 W W₀) (A : Set Γ) with hD₁def
  have hD₁D : D₁ ≤ D := inf_le_inf_right _ (k1_le (W := W) (W₀ := W₀))
  have hD₁K : D₁ ≤ kOf W := inf_le_left.trans inf_le_left
  have hX₂X₁ : X₂ ≤ X₁ := S.chief.2.2.1.le
  have hD₁n₂ : D₁ ≤ Subgroup.normalizer (X₂ : Set Γ) := hD₁D.trans S.D_nor_X₂
  have hcomm1 : ∀ g ∈ X₁, ∀ y ∈ D₁, ⁅g, y⁆ ∈ X₂ := by
    intro g hg y hy
    apply hi
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp
        ((Nonsolv.le_normalizer_kOf W) (S.hX₁.1 hg)) y).mp (hD₁K hy)
      have e : ⁅g, y⁆ = (g * y * g⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact mul_mem h1 (inv_mem (hD₁K hy))
    · have h1 := (Subgroup.mem_normalizer_iff.mp (S.D_nor_X₁ (hD₁D hy)) g⁻¹).mp (inv_mem hg)
      have e : ⁅g, y⁆ = g * (y * g⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hg h1
  have hDD₁ : D ≤ Subgroup.normalizer (D₁ : Set Γ) := by
    refine Thm32.le_normalizer_inf S.admits_D_k1 ?_
    exact (inf_le_right : cenIn W (A : Set Γ) ≤ Subgroup.centralizer (A : Set Γ)).trans
      Subgroup.le_normalizer
  have hAD₁ : A ≤ Subgroup.normalizer (D₁ : Set Γ) := by
    refine Thm32.le_normalizer_inf S.admits_A_k1 ?_
    intro a ha
    exact Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.mpr fun b hb => S.comm_A hb ha)
  have hX₁X₂D₁ : X₁ ≤ Subgroup.normalizer ((X₂ ⊔ D₁ : Subgroup Γ) : Set Γ) :=
    le_normalizer_sup_of_commutator hD₁n₂ S.X₁_nor_X₂ hcomm1
  have hZ₀ : IsNormalIn (X₂ ⊔ D₁) (X₁ ⊔ D) :=
    ⟨sup_le (hX₂X₁.trans le_sup_left) (hD₁D.trans le_sup_right),
      sup_le hX₁X₂D₁ (Thm32.le_normalizer_sup S.D_nor_X₂ hDD₁)⟩
  have hadm₀ : Admits (D ⊔ A) (X₂ ⊔ D₁) :=
    Admits.sup S.hX₂.2 (sup_le hDD₁ hAD₁)
  have hadm : Admits (D ⊔ A) (X₁ ⊔ D) :=
    Admits.sup S.hX₁.2 (Thm33a.admits_cenIn_sup A W)
  have hDeq : (X₂ ⊔ D₁) ⊓ kOf W ⊓ D = D₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf le_sup_right hD₁K) hD₁D)
    obtain ⟨hxSK, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxS, hxK⟩ := Subgroup.mem_inf.mp hxSK
    obtain ⟨r, hr, d₁, hd₁, rfl⟩ := (Thm32.mem_sup_iff_mul hD₁n₂).mp hxS
    have hrD : r ∈ D := by
      have := mul_mem hxD (inv_mem (hD₁D hd₁))
      simpa using this
    have hrK : r ∈ kOf W := by
      have := mul_mem hxK (inv_mem (hD₁K hd₁))
      simpa using this
    have hrY : r ∈ Y := S.X₂Y (Subgroup.mem_inf.mpr ⟨hr, hrD⟩)
    have hrZ : r ∈ Z₂ := by
      rw [← Thm33a.pair_inf S.pair] at hrY
      exact (Subgroup.mem_inf.mp hrY).1
    have hrk1 : r ∈ k1 W W₀ := Subgroup.mem_inf.mpr ⟨hrK,
      Subgroup.mem_centralizer_iff.mpr fun w hw => S.W₀_comm hw hrZ⟩
    have hrD₁ : r ∈ D₁ := Subgroup.mem_inf.mpr ⟨hrk1, (Subgroup.mem_inf.mp hrD).2⟩
    exact mul_mem hrD₁ hd₁
  have hX₁k : Admits X₁ (k1 W W₀) :=
    le_sup_left.trans (lemma213d S.near S.sol_eq S.ne_bot S.W₀K S.W₀_DA S.W₀perf
      (sup_le S.hX₁.1 S.D_le) hZ₀ hadm₀ hadm hDeq)
  have hk := S.k1_eq_bot hX₁k
  have hYbot := S.Y_eq_bot hk
  have hZK : X₁ ⊓ kOf W ⊓ D = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxXK, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxX, hxK⟩ := Subgroup.mem_inf.mp hxXK
    have hxY : x ∈ Y := S.X₂Y (Subgroup.mem_inf.mpr ⟨hi (Subgroup.mem_inf.mpr ⟨hxK, hxX⟩), hxD⟩)
    rw [hYbot] at hxY
    exact hxY
  have hS := Thm33b.isGreatest_scalJoin S.near
  have h1 := lemma216d S.near S.sol_eq S.ne_bot hS S.hX₁.1 S.hX₁.2 hZK
  have hnil : Group.IsNilpotent ↥(s1 W (scalJoin W A (cenIn W (A : Set Γ)))) :=
    Thm210.isNilpotent_fittingSubgroupOf (s0 W (scalJoin W A (cenIn W (A : Set Γ))))
  have hsolv : Group.IsSolvable ↥X₁ := Thm211.isSolvable_of_le h1 inferInstance
  obtain ⟨n, hn⟩ := (Group.isSolvable_def ↥X₁).mp hsolv
  exact S.nonsolv ⟨n, hn ▸ bot_le⟩

theorem admits_kOf_k1_of
    {P : Subgroup Γ} (hPK : P ≤ kOf W)
    (hPDA : Admits (cenIn W (A : Set Γ) ⊔ A) P) (hPperf : Group.IsPerfect ↥P) :
    Admits (kOf W) (k1 W P) := by
  have hdp := lemma213a S.near S.sol_eq S.ne_bot hPK hPDA hPperf
  rw [← hdp.sup_eq]
  refine sup_le Subgroup.le_normalizer ?_
  refine Thm211.admits_iff.mpr fun y hy x hx => ?_
  have hc : Commute x y := hdp.commute x hx y hy
  have : y * x * y⁻¹ = x := by
    rw [← hc.eq]
    group
  rw [this]
  exact hx

theorem admits_W_k1_of
    {P : Subgroup Γ} (hPK : P ≤ kOf W)
    (hPDA : Admits (cenIn W (A : Set Γ) ⊔ A) P) (hPperf : Group.IsPerfect ↥P)
    (hZ₁K : Z₁ ≤ kOf W) (hX₁K : X₁ ≤ kOf W) : Admits W (k1 W P) := by
  have hKk := S.admits_kOf_k1_of hPK hPDA hPperf
  have hD : Admits (cenIn W (A : Set Γ)) (k1 W P) :=
    Lemma213.admits_cenIn (S.D_le.trans (Nonsolv.le_normalizer_kOf W)) (le_sup_left.trans hPDA)
  calc W = Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ) := S.hW
    _ ≤ Subgroup.normalizer ((k1 W P : Subgroup Γ) : Set Γ) :=
      sup_le (sup_le (hZ₁K.trans hKk) (hX₁K.trans hKk)) hD

omit [Finite Γ] in
theorem k1_eq_bot_of_chief {P : Subgroup Γ} (hPK : P ≤ kOf W) (hPne : P ≠ ⊥)
    (hk : k1 W W₀ = ⊥) (hZ₂ : Z₂ = ⊥) (hN : Admits W (k1 W P))
    (hAN : Admits A (k1 W P)) : k1 W P = ⊥ := by
  have hZ₁W : Z₁ ≤ W := Thm33a.pair_le S.pair
  have hk1W : k1 W P ≤ W := inf_le_left.trans (kOf_le W)
  refine S.key _ hk1W hN hAN ?_
  have hchief := Thm33a.pair_chief S.pair
  have hHN : Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A ≤ Subgroup.normalizer ((k1 W P : Subgroup Γ) : Set Γ) :=
    sup_le (sup_le (hZ₁W.trans hN) (S.D_le.trans hN)) hAN
  have hM : IsNormalIn (k1 W P ⊓ Z₁) (Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A) :=
    ⟨inf_le_right.trans Thm33a.le_H,
      Thm32.le_normalizer_inf hHN (Thm33a.pair_admits_H S.pair)⟩
  rcases hchief.2.2.2 (k1 W P ⊓ Z₁) hM (by rw [hZ₂]; exact bot_le) inf_le_right with h1 | h1
  · exact h1.le
  · exfalso
    apply hPne
    refine eq_bot_iff.mpr fun q hq => ?_
    have hqK : q ∈ kOf W := hPK hq
    have hqC : q ∈ k1 W W₀ := by
      refine Subgroup.mem_inf.mpr ⟨hqK, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hwM : w ∈ k1 W P ⊓ Z₁ := by
        rw [h1]
        exact S.W₀Z₁ hw
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hwM).1).2
        q hq
      exact this.symm
    rw [hk] at hqC
    exact hqC

omit S in
theorem isSolvable_of_perfRes_eq_bot {X : Subgroup Γ} (h : perfRes X = ⊥) :
    Group.IsSolvable ↥X := by
  obtain ⟨n, hn, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥X)
  refine (Group.isSolvable_def ↥X).mpr ⟨n, ?_⟩
  rw [← hn]
  exact Subgroup.map_injective X.subtype_injective (by rw [Subgroup.map_bot]; exact h)

theorem concl_of_perfect
    (hX₁K : X₁ ≤ kOf W) (hX₁perf : Group.IsPerfect ↥X₁) :
    X₁ ⊓ cenIn W (A : Set Γ) ≤ Y ∨ secCenIn (cenIn W (A : Set Γ)) X₁ X₂ = Y := by
  have hX₁ne : X₁ ≠ ⊥ := fun h => not_lt_bot (h ▸ S.chief.2.2.1)
  have hX₂X₁ : X₂ ≤ X₁ := S.chief.2.2.1.le
  have hKk := S.admits_kOf_k1_of hX₁K S.hX₁.2 hX₁perf
  have hk : k1 W W₀ = ⊥ := S.k1_eq_bot (hX₁K.trans S.admits_kOf_k1)
  have hZ₂ : Z₂ = ⊥ := S.Z₂_eq_bot hk
  have hYbot : Y = ⊥ := S.Y_eq_bot hk
  have hZ₁W₀ : Z₁ = W₀ := by
    have := S.W₀sup
    rw [hZ₂, sup_bot_eq] at this
    exact this.symm
  have hZ₁K : Z₁ ≤ kOf W := hZ₁W₀ ▸ S.W₀K
  have hk1X₁ : k1 W X₁ = ⊥ := by
    refine S.k1_eq_bot_of_chief hX₁K hX₁ne hk hZ₂ (S.admits_W_k1_of hX₁K S.hX₁.2 hX₁perf hZ₁K hX₁K)
      (Lemma213.admits_cenIn S.admits_A_kOf (le_sup_right.trans S.hX₁.2))
  have hcenX₁ : cenIn W (X₁ : Set Γ) = ⊥ :=
    lemma213c S.near S.sol_eq S.ne_bot hX₁K S.hX₁.2 hX₁perf hk1X₁
  by_cases hP : perfRes X₂ = ⊥
  ·
    have hsolv : Group.IsSolvable ↥X₂ := isSolvable_of_perfRes_eq_bot hP
    have hss := Thm33a.semisimpleAction_kOf S.near S.sol_eq S.ne_bot
    have hX₁DA' : Admits (cenIn (kOf W) (A : Set Γ) ⊔ A) X₁ :=
      (sup_le_sup_right (inf_le_inf_right _ (kOf_le W)) A).trans S.hX₁.2
    have hbot := Thm33a.inf_eq_bot_of_solvable hss hX₁K (hX₂X₁.trans hX₁K) hX₁DA' hX₁perf hsolv
      S.X₁_nor_X₂
    have hX₂bot : X₂ = ⊥ := eq_bot_iff.mpr fun x hx => by
      have : x ∈ X₁ ⊓ X₂ := ⟨hX₂X₁ hx, hx⟩
      rw [hbot] at this
      exact this
    right
    rw [hYbot]
    refine eq_bot_iff.mpr fun d hd => ?_
    obtain ⟨hdD, hdsc⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨-, -, hdcomm⟩ := mem_sectionCentralizer_iff.mp hdsc
    have hdc : d ∈ cenIn W (X₁ : Set Γ) := by
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hdD).1, Subgroup.mem_centralizer_iff.mpr
        fun y hy => ?_⟩
      have h1 := hdcomm y hy
      rw [hX₂bot, Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    rw [hcenX₁] at hdc
    exact hdc
  · have hPK : perfRes X₂ ≤ kOf W := (Subgroup.map_subtype_le _).trans (hX₂X₁.trans hX₁K)
    have hPperf : Group.IsPerfect ↥(perfRes X₂) := Nonsolvable.isPerfect_perfectResidual_map _
    have hPDA : Admits (cenIn W (A : Set Γ) ⊔ A) (perfRes X₂) :=
      S.hX₂.2.trans (Nonsolvable.normalizer_le_normalizer_perfectResidual_map X₂)
    have hk1P : k1 W (perfRes X₂) = ⊥ :=
      S.k1_eq_bot_of_chief hPK hP hk hZ₂
        (S.admits_W_k1_of hPK hPDA hPperf hZ₁K hX₁K)
        (Lemma213.admits_cenIn S.admits_A_kOf (le_sup_right.trans hPDA))
    have hb := (lemma213b S.near S.sol_eq S.ne_bot hPK hPDA hPperf).2
    have hk2 : k2 W (perfRes X₂) = kOf W := by
      unfold k2
      rw [hk1P]
      unfold cenIn
      rw [Thm211.centralizer_bot, inf_top_eq]
    rw [hk2] at hb
    left
    intro x hx
    obtain ⟨hxX, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxKA : x ∈ cenIn (kOf W) (A : Set Γ) := Subgroup.mem_inf.mpr ⟨hX₁K hxX, hxD.2⟩
    rw [hb] at hxKA
    have hxP : x ∈ perfRes X₂ := (Subgroup.mem_inf.mp hxKA).1
    exact S.X₂Y ⟨(Subgroup.map_subtype_le _) hxP, hxD⟩

end TermSetting

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36
