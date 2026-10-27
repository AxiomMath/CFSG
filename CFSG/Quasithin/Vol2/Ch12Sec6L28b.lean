module

public import CFSG.Quasithin.Vol2.Ch12Sec6L28a
public import CFSG.Quasithin.Vol2.Ch12Sec6Final
public import CFSG.Quasithin.Vol2.Ch12Sec6L24b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L22F Equiv

namespace S126L28

variable {W : Type*} [CommGroup W]

theorem perm_unique (e : W ≃* D8) {a : MulAut W} {σ τ : Perm (Fin 8)}
    (hσ : ∀ w, e (a w) = dAct σ (e w)) (hτ : ∀ w, e (a w) = dAct τ (e w)) : σ = τ := by
  have h : ∀ y : D8, dAct (σ⁻¹ * τ) y = y := by
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [dAct_mul, ← hτ, hσ, dAct_inv_dAct]
  have h1 := eq_one_of_dAct h
  calc σ = σ * (σ⁻¹ * τ) := by rw [h1, mul_one]
    _ = τ := by group

variable (e : W ≃* D8) {A : Subgroup (MulAut W)}
  (hA : ∀ a ∈ A, ∃ σ : Perm (Fin 8), ∀ w, e (a w) = dAct σ (e w))

@[expose] noncomputable def psiFun (a : ↥A) : Perm (Fin 8) := Classical.choose (hA a a.2)

theorem psiFun_spec (a : ↥A) (w : W) : e ((a : MulAut W) w) = dAct (psiFun e hA a) (e w) :=
  Classical.choose_spec (hA a a.2) w

@[expose] noncomputable def psiP : ↥A →* Perm (Fin 8) where
  toFun := psiFun e hA
  map_one' := perm_unique e (psiFun_spec e hA 1) fun w => by
    rw [dAct_one]
    rfl
  map_mul' a b := perm_unique e (psiFun_spec e hA (a * b)) fun w => by
    rw [dAct_mul, ← psiFun_spec e hA b, ← psiFun_spec e hA a]
    rfl

theorem psiP_spec (a : ↥A) (w : W) : e ((a : MulAut W) w) = dAct (psiP e hA a) (e w) :=
  psiFun_spec e hA a w

theorem psiP_eq {a : ↥A} {σ : Perm (Fin 8)} (h : ∀ w, e ((a : MulAut W) w) = dAct σ (e w)) :
    psiP e hA a = σ :=
  perm_unique e (psiP_spec e hA a) h

theorem psiP_injective : Function.Injective (psiP e hA) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  apply e.injective
  rw [psiP_spec e hA, MonoidHom.mem_ker.1 ha, dAct_one]
  rfl

@[expose] noncomputable def img (B : Subgroup (MulAut W)) : Subgroup (Perm (Fin 8)) :=
  (B.subgroupOf A).map (psiP e hA)

@[expose] noncomputable def pre (P : Subgroup (Perm (Fin 8))) : Subgroup (MulAut W) :=
  (P.comap (psiP e hA)).map A.subtype

theorem mem_img {B : Subgroup (MulAut W)} {σ : Perm (Fin 8)} :
    σ ∈ img e hA B ↔ ∃ a : ↥A, (a : MulAut W) ∈ B ∧ psiP e hA a = σ := by
  unfold img
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩

theorem mem_fixV_iff {B : Subgroup (MulAut W)} (hBA : B ≤ A) (w : W) :
    w ∈ fixV B ↔ e w ∈ fixD (img e hA B) := by
  constructor
  · intro hw σ hσ
    obtain ⟨a, haB, rfl⟩ := (mem_img e hA).1 hσ
    rw [← psiP_spec, hw a haB]
  · intro hw b hb
    apply e.injective
    have h := psiP_spec e hA ⟨b, hBA hb⟩ w
    rw [show ((⟨b, hBA hb⟩ : ↥A) : MulAut W) = b from rfl] at h
    rw [h]
    exact hw _ ((mem_img e hA).2 ⟨⟨b, hBA hb⟩, hb, rfl⟩)

theorem fixV_eq_iff {B B' : Subgroup (MulAut W)} (hBA : B ≤ A) (hB'A : B' ≤ A) :
    fixV B = fixV B' ↔ fixD (img e hA B) = fixD (img e hA B') := by
  constructor
  · intro h
    ext y
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [← mem_fixV_iff e hA hBA, ← mem_fixV_iff e hA hB'A, h]
  · intro h
    ext w
    rw [mem_fixV_iff e hA hBA, mem_fixV_iff e hA hB'A, h]

theorem fixV_lt_iff {B B' : Subgroup (MulAut W)} (hBA : B ≤ A) (hB'A : B' ≤ A) :
    fixV B < fixV B' ↔ fixD (img e hA B) < fixD (img e hA B') := by
  have hle : fixV B ≤ fixV B' ↔ fixD (img e hA B) ≤ fixD (img e hA B') := by
    constructor
    · intro h y hy
      obtain ⟨w, rfl⟩ := e.surjective y
      exact (mem_fixV_iff e hA hB'A w).1 (h ((mem_fixV_iff e hA hBA w).2 hy))
    · intro h w hw
      exact (mem_fixV_iff e hA hB'A w).2 (h ((mem_fixV_iff e hA hBA w).1 hw))
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, hle, Ne, Ne, fixV_eq_iff e hA hBA hB'A]

theorem img_pre {B : Subgroup (MulAut W)} {P : Subgroup (Perm (Fin 8))} (hP : P ≤ img e hA B) :
    img e hA (pre e hA P) = P := by
  ext σ
  rw [mem_img]
  constructor
  · rintro ⟨a, ⟨a', ha', hae⟩, rfl⟩
    rw [show a = a' from Subtype.ext hae.symm]
    exact ha'
  · intro hσ
    obtain ⟨a, -, rfl⟩ := (mem_img e hA).1 (hP hσ)
    exact ⟨a, ⟨a, hσ, rfl⟩, rfl⟩

theorem pre_le {B : Subgroup (MulAut W)} {P : Subgroup (Perm (Fin 8))} (hP : P ≤ img e hA B) :
    pre e hA P ≤ B := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨a', ha'B, he⟩ := (mem_img e hA).1 (hP ha)
  rw [show a = a' from psiP_injective e hA he.symm]
  exact ha'B

theorem pre_mono {P Q : Subgroup (Perm (Fin 8))} (h : P ≤ Q) : pre e hA P ≤ pre e hA Q :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem img_mono {B B' : Subgroup (MulAut W)} (h : B ≤ B') : img e hA B ≤ img e hA B' :=
  Subgroup.map_mono fun _ ha => h ha

theorem card_img {B : Subgroup (MulAut W)} (hBA : B ≤ A) :
    Nat.card (img e hA B) = Nat.card B := by
  unfold img
  rw [Subgroup.card_map_of_injective (psiP_injective e hA)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv

theorem relIndex_img [Finite W] {B B' : Subgroup (MulAut W)} (hBA : B ≤ A) (hB'B : B' ≤ B) :
    (img e hA B').relIndex (img e hA B) = B'.relIndex B := by
  have h1 := Subgroup.relIndex_mul_card (H := B') (K := B)
  have h2 := Subgroup.relIndex_mul_card (H := img e hA B') (K := img e hA B)
  rw [inf_of_le_left hB'B] at h1
  rw [inf_of_le_left (img_mono e hA hB'B), card_img e hA hBA,
    card_img e hA (hB'B.trans hBA)] at h2
  have : Finite (MulAut W) := Finite.of_injective (fun a : MulAut W => (a : W → W))
    fun _ _ h => MulEquiv.ext (congrFun h)
  have hpos : 0 < Nat.card B' := Nat.card_pos
  rw [← h1] at h2
  exact Nat.eq_of_mul_eq_mul_right hpos h2

end S126L28

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L22F Equiv

namespace S126L28

variable {W : Type*} [CommGroup W]

@[expose] noncomputable def dActEquiv (π : Perm (Fin 8)) : D8 ≃* D8 where
  toFun := dAct π
  invFun := dAct π⁻¹
  left_inv y := dAct_inv_dAct π y
  right_inv y := dAct_dAct_inv π y
  map_mul' := map_mul (dAct π)

variable (e : W ≃* D8) {A : Subgroup (MulAut W)}
  (hA : ∀ a ∈ A, ∃ σ : Perm (Fin 8), ∀ w, e (a w) = dAct σ (e w))

include hA in
theorem frame_act (π : Perm (Fin 8)) :
    ∀ a ∈ A, ∃ σ : Perm (Fin 8), ∀ w, (e.trans (dActEquiv π)) (a w) =
      dAct σ ((e.trans (dActEquiv π)) w) := fun a ha =>
  ⟨π * psiP e hA ⟨a, ha⟩ * π⁻¹, fun w => by
    have h := psiP_spec e hA ⟨a, ha⟩ w
    simp only [MulEquiv.trans_apply, dActEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    rw [show ((⟨a, ha⟩ : ↥A) : MulAut W) = a from rfl] at h
    rw [h, dAct_mul, dAct_mul, dAct_inv_dAct]⟩

theorem psiP_frame (π : Perm (Fin 8)) (a : ↥A) :
    psiP (e.trans (dActEquiv π)) (frame_act e hA π) a = π * psiP e hA a * π⁻¹ := by
  refine psiP_eq _ _ fun w => ?_
  have h := psiP_spec e hA a w
  simp only [MulEquiv.trans_apply, dActEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [h, dAct_mul, dAct_mul, dAct_inv_dAct]

theorem finite_mulAut [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun a : MulAut W => (a : W → W)) fun _ _ h => MulEquiv.ext (congrFun h)

section Core

variable {B : Subgroup (MulAut W)}

theorem img_comm (hab : IsElemAbelian2 B) :
    ∀ σ ∈ img e hA B, ∀ τ ∈ img e hA B, σ * τ = τ * σ := by
  intro σ hσ τ hτ
  obtain ⟨_, ha, rfl⟩ := (mem_img e hA).1 hσ
  obtain ⟨_, hb, rfl⟩ := (mem_img e hA).1 hτ
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hab.1 _ ha _ hb)

theorem img_sq (hab : IsElemAbelian2 B) : ∀ σ ∈ img e hA B, σ * σ = 1 := by
  intro σ hσ
  obtain ⟨_, ha, rfl⟩ := (mem_img e hA).1 hσ
  rw [← map_mul, ← map_one (psiP e hA)]
  congr 1
  apply Subtype.ext
  have := hab.2 _ ha
  rw [sq] at this
  exact this

theorem img_ne_bot (hBA : B ≤ A) (hne : B ≠ ⊥) : img e hA B ≠ ⊥ := by
  intro h
  apply hne
  rw [eq_bot_iff]
  intro b hb
  have hσ : psiP e hA ⟨b, hBA hb⟩ ∈ img e hA B := (mem_img e hA).2 ⟨⟨b, hBA hb⟩, hb, rfl⟩
  rw [h, Subgroup.mem_bot, ← map_one (psiP e hA)] at hσ
  have := psiP_injective e hA hσ
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem isPGroup_of_elemAbelian2 [Finite W] (hab : IsElemAbelian2 B) : IsPGroup 2 B := fun b =>
  ⟨1, Subtype.ext (by rw [pow_one]; exact hab.2 _ b.2)⟩

theorem mQuot_lt_of_relIndex_le [Finite W] (hab : IsElemAbelian2 B) {B' : Subgroup (MulAut W)}
    {k : ℕ} (h : B'.relIndex B ≤ 2 ^ (k - 1)) (hk : 0 < k) : E3.mQuot B B' < k := by
  have : Finite (MulAut W) := finite_mulAut
  have h2 := E3.relIndex_eq_two_pow (isPGroup_of_elemAbelian2 hab) B'
  rw [h2] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  omega

theorem core_three [Finite W] (hBA : B ≤ A) (hne : B ≠ ⊥)
    (hab : IsElemAbelian2 B) (hP : img e hA B ≤ S126Ex.presSub)
    (h3 : ∀ B' ≤ B, E3.mQuot B B' < 3 → fixV B' = fixV B) : False := by
  obtain ⟨P, hPB, hidx, hne'⟩ := (p8_facts (img_comm e hA hab) (img_sq e hA hab) hP
    (img_ne_bot e hA hBA hne)).1
  have hle := pre_le e hA hPB
  have hidx' : (pre e hA P).relIndex B ≤ 4 := by
    rw [← relIndex_img e hA hBA hle, img_pre e hA hPB]
    exact hidx
  have h := h3 _ hle (mQuot_lt_of_relIndex_le hab (k := 3) hidx' (by norm_num))
  rw [fixV_eq_iff e hA (hle.trans hBA) hBA, img_pre e hA hPB] at h
  exact hne' h

theorem core_two [Finite W] (hBA : B ≤ A) (hne : B ≠ ⊥)
    (hab : IsElemAbelian2 B) (hP : img e hA B ≤ S126Ex.presSub)
    (h2 : ∀ B' ≤ B, E3.mQuot B B' < 2 → fixV B' = fixV B) :
    8 ≤ Nat.card ↥B ∧ ∃ D : Subgroup (MulAut W), D ≤ B ∧ D.relIndex B = 8 ∧
      2 < (ESet B D).ncard := by
  have hfix : ∀ P ≤ img e hA B, P.relIndex (img e hA B) ≤ 2 → fixD P = fixD (img e hA B) := by
    intro P hPB hidx
    have hle := pre_le e hA hPB
    have hidx' : (pre e hA P).relIndex B ≤ 2 := by
      rw [← relIndex_img e hA hBA hle, img_pre e hA hPB]
      exact hidx
    have h := h2 _ hle (mQuot_lt_of_relIndex_le hab (k := 2) hidx' (by norm_num))
    rw [fixV_eq_iff e hA (hle.trans hBA) hBA, img_pre e hA hPB] at h
    exact h
  obtain ⟨h8, D, hDB, hD8, E₁, E₂, E₃, h12, h13, h23, hE⟩ :=
    (p8_facts (img_comm e hA hab) (img_sq e hA hab) hP (img_ne_bot e hA hBA hne)).2 hfix
  have hEB : ∀ E ∈ [E₁, E₂, E₃], E ≤ img e hA B := fun E hE' => (hE E hE').2.1
  have hmem : ∀ E ∈ [E₁, E₂, E₃], pre e hA E ∈ ESet B (pre e hA D) := by
    intro E hE'
    obtain ⟨hDE, hEB', hDE2, hlt⟩ := hE E hE'
    have hle := pre_le e hA hEB'
    refine ⟨pre_mono e hA hDE, hle, ?_, ?_⟩
    · rw [← relIndex_img e hA (hle.trans hBA) (pre_mono e hA hDE), img_pre e hA hEB',
        img_pre e hA (hDE.trans hEB')]
      exact hDE2
    · rw [fixV_lt_iff e hA hBA (hle.trans hBA), img_pre e hA hEB']
      exact hlt
  have hinj : ∀ E ∈ [E₁, E₂, E₃], ∀ E' ∈ [E₁, E₂, E₃], E ≠ E' → pre e hA E ≠ pre e hA E' := by
    intro E hE' E' hE'' hne'' heq
    apply hne''
    rw [← img_pre e hA (hEB E hE'), heq, img_pre e hA (hEB E' hE'')]
  have hm1 : E₁ ∈ [E₁, E₂, E₃] := by simp
  have hm2 : E₂ ∈ [E₁, E₂, E₃] := by simp
  have hm3 : E₃ ∈ [E₁, E₂, E₃] := by simp
  refine ⟨by rw [← card_img e hA hBA]; exact h8, pre e hA D, pre_le e hA hDB, ?_, ?_⟩
  · rw [← relIndex_img e hA hBA (pre_le e hA hDB), img_pre e hA hDB]
    exact hD8
  · have : Finite (MulAut W) := finite_mulAut
    have : Finite (Subgroup (MulAut W)) :=
      Finite.of_injective (fun H : Subgroup (MulAut W) => (H : Set (MulAut W)))
        SetLike.coe_injective
    have hsub : ({pre e hA E₁, pre e hA E₂, pre e hA E₃} : Set (Subgroup (MulAut W))) ⊆
        ESet B (pre e hA D) := by
      rintro E (rfl | rfl | rfl)
      exacts [hmem _ hm1, hmem _ hm2, hmem _ hm3]
    have h3 : ({pre e hA E₁, pre e hA E₂, pre e hA E₃} : Set (Subgroup (MulAut W))).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair (hinj _ hm2 _ hm3 h23)]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hinj _ hm1 _ hm2 h12, hinj _ hm1 _ hm3 h13⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega

end Core

include e hA in
theorem aSet_facts [Finite W] :
    E3.aSet 3 A = ∅ ∧ ∀ B ∈ E3.aSet 2 A, 8 ≤ Nat.card ↥B ∧
      ∃ D : Subgroup (MulAut W), D ≤ B ∧ D.relIndex B = 8 ∧ 2 < (ESet B D).ncard := by
  have hred : ∀ B ≤ A, IsElemAbelian2 B → ∃ (e' : W ≃* D8)
      (hA' : ∀ a ∈ A, ∃ σ : Perm (Fin 8), ∀ w, e' (a w) = dAct σ (e' w)),
      img e' hA' B ≤ S126Ex.presSub := by
    intro B _ hab
    have h2 : IsPGroup 2 (img e hA B) := fun σ =>
      ⟨1, Subtype.ext (by rw [pow_one, sq]; exact img_sq e hA hab σ σ.2)⟩
    obtain ⟨g, hg⟩ := S126Ex.exists_conj_le_P8 h2
    refine ⟨e.trans (dActEquiv g⁻¹), frame_act e hA g⁻¹, fun σ hσ => ?_⟩
    obtain ⟨a, haB, rfl⟩ := (mem_img _ _).1 hσ
    rw [psiP_frame e hA, inv_inv]
    exact S126Ex.P8_le_presSub (hg _ ((mem_img e hA).2 ⟨a, haB, rfl⟩))
  refine ⟨Set.eq_empty_of_forall_notMem fun B hB => ?_, fun B hB => ?_⟩
  · obtain ⟨hBA, hne, hab, h3⟩ := hB
    obtain ⟨e', hA', hP⟩ := hred B hBA hab
    exact core_three e' hA' hBA hne hab hP h3
  · obtain ⟨hBA, hne, hab, h2⟩ := hB
    obtain ⟨e', hA', hP⟩ := hred B hBA hab
    exact core_two e' hA' hBA hne hab hP h2

end S126L28

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P Equiv
open scoped IsMulCommutative

namespace S126L28

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def betaEquiv (F : Frame126 T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : ↥V ≃* D8 :=
  MulEquiv.ofBijective F.β ⟨S126L24.beta_injective F hZ, F.β_surj⟩

theorem mvbar_act (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ a ∈ hH.hyp.MVbar, ∃ σ : Perm (Fin 8), ∀ w,
      betaEquiv F hZ (a w) = dAct σ (betaEquiv F hZ w) := by
  intro a ha
  obtain ⟨x, hx, hxM, rfl⟩ := mem_autOn_iff_exists.mp ha
  obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH hxM.1 hx
  exact ⟨σ, fun w => hσ w _ rfl⟩

end S126L28

theorem lemma12_6_28_one_two {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} [IsMulCommutative ↥V] (F : Frame126 T L V) (h : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    E3.aSet 3 h.hyp.MVbar = ∅ ∧
      ∀ B ∈ E3.aSet 2 h.hyp.MVbar, 8 ≤ Nat.card ↥B ∧
        ∃ D : Subgroup (MulAut ↥V), D ≤ B ∧ D.relIndex B = 8 ∧ 2 < (ESet B D).ncard :=
  S126L28.aSet_facts (S126L28.betaEquiv F hZ) (S126L28.mvbar_act F h hZ)

end CFSG.Quasithin.H13
