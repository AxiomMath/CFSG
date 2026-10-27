module

public import CFSG.Quasithin.H13.NQCatKG68Singer
public import CFSG.Quasithin.H13.NQCatLieCentralSp4

public section

namespace CFSG.Quasithin.H13.KG68.Singer.Sp4

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.H13.NQCat.LieThompson.Sp4
open CFSG.Quasithin.H13.NQCat.Sp4 (xA xB xAB xC spMat_xAB spMat_xC xA_mem xB_mem xAB_mul xC_mul)
open CFSG.Quasithin.H13.NQCat.LieCentral.Sp4 (piA_eq_zero_of_commute piB_eq_zero_of_commute)

variable {F : Type} [Field F]

theorem spMat_xC_eq (t : F) : spMat (xC t) = uMat 0 t 0 0 := by
  rw [spMat_xC]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [uMat]

theorem spMat_xAB_eq (t : F) : spMat (xAB t) = uMat 0 0 t 0 := by
  rw [spMat_xAB]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [uMat]

@[expose] def zElt (a b : F) : StatedSp 2 F := xC a * xAB b

theorem zElt_zero : zElt (0 : F) 0 = 1 := by
  have h1 : xC (0 : F) = 1 := mul_eq_left.1 ((xC_mul 0 0).trans (by rw [add_zero]))
  have h2 : xAB (0 : F) = 1 := mul_eq_left.1 ((xAB_mul 0 0).trans (by rw [add_zero]))
  rw [zElt, h1, h2, mul_one]

variable [CharP F 2]

theorem spMat_zElt (a b : F) : spMat (zElt a b) = uMat 0 a b 0 := by
  rw [zElt, spMat_mul, spMat_xC_eq, spMat_xAB_eq, uMat_mul]
  simp

theorem zElt_mem (a b : F) : zElt a b ∈ unipotent 2 F :=
  mem_unipotent_of_uMat (spMat_zElt a b)

theorem zElt_mul (a b a' b' : F) : zElt a b * zElt a' b' = zElt (a + a') (b + b') := by
  apply statedSp_ext
  change spMat (zElt a b) * spMat (zElt a' b') = spMat (zElt (a + a') (b + b'))
  rw [spMat_zElt, spMat_zElt, spMat_zElt, uMat_mul]
  simp

theorem zC_zElt (a b : F) : zC (zElt a b) = a := by
  rw [zC_of (spMat_zElt a b)]
  ring

theorem zD_zElt (a b : F) : zD (zElt a b) = b := by
  rw [zD_of (spMat_zElt a b)]
  ring

theorem zElt_inj {a b a' b' : F} (h : zElt a b = zElt a' b') : a = a' ∧ b = b' :=
  ⟨by rw [← zC_zElt a b, h, zC_zElt], by rw [← zD_zElt a b, h, zD_zElt]⟩

theorem zElt_eq_one_iff {a b : F} : zElt a b = 1 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    rw [← zElt_zero] at h
    exact zElt_inj h
  · rintro ⟨rfl, rfl⟩
    exact zElt_zero

theorem mul_zElt_comm {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (a b : F) :
    u * zElt a b = zElt a b * u :=
  mul_comm_of_piA_eq_zero hu (zElt_mem a b) (piA_of (spMat_zElt a b)) (piB_of (spMat_zElt a b))

theorem eq_zElt_of_mem_center {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F)
    (hc : ∀ t ∈ unipotent 2 F, g * t = t * g) : g = zElt (zC g) (zD g) := by
  have hA := piA_eq_zero_of_commute hg one_ne_zero (hc _ (xB_mem 1)).symm
  have hB := piB_eq_zero_of_commute hg one_ne_zero (hc _ (xA_mem 1)).symm
  apply statedSp_ext
  change spMat g = spMat (zElt (zC g) (zD g))
  rw [spMat_eq_of_piA_eq_zero hg hA hB, spMat_zElt]

@[expose] def zCharT : (Fin 2 → Fˣ) →* Fˣ × Fˣ where
  toFun t := (t 0 ^ 2, t 0 * t 1)
  map_one' := by simp
  map_mul' s t := Prod.ext (by simp [mul_pow]) (by simp [mul_mul_mul_comm])

@[expose] noncomputable def zChar : borelSubgroup 2 F →* Fˣ × Fˣ := zCharT.comp (diagHom 2 F)

omit [CharP F 2] in
theorem zChar_apply (n : borelSubgroup 2 F) :
    zChar n = (diagHom 2 F n 0 ^ 2, diagHom 2 F n 0 * diagHom 2 F n 1) :=
  rfl

omit [CharP F 2] in
theorem diagHom_torusHom (t : Fin 2 → Fˣ) :
    diagHom 2 F ⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ = t := by
  funext i
  apply Units.ext
  simp [diagHom, diagEntry, coe_torusHom]

theorem torusHom_conj_zElt (t : Fin 2 → Fˣ) (a b : F) :
    torusHom t * zElt a b * (torusHom t)⁻¹ =
      zElt ((t 0 : F) ^ 2 * a) ((t 0 : F) * (t 1 : F) * b) := by
  apply statedSp_ext
  change spMat (torusHom t * zElt a b * (torusHom t)⁻¹) = spMat (zElt _ _)
  rw [spMat_torus_conj t (spMat_zElt a b), spMat_zElt]
  simp

theorem borel_conj_zElt (n : borelSubgroup 2 F) (a b : F) :
    (n : StatedSp 2 F) * zElt a b * (n : StatedSp 2 F)⁻¹ =
      zElt (((zChar n).1 : F) * a) (((zChar n).2 : F) * b) := by
  set t := diagHom 2 F n with ht
  set h : borelSubgroup 2 F := ⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ with hh
  have hu : ((n * h⁻¹ : borelSubgroup 2 F) : StatedSp 2 F) ∈ unipotent 2 F := by
    have h1 : n * h⁻¹ ∈ (diagHom 2 F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hh, diagHom_torusHom, ← ht, mul_inv_cancel]
    rw [ker_diagHom] at h1
    exact h1
  set u : StatedSp 2 F := ((n * h⁻¹ : borelSubgroup 2 F) : StatedSp 2 F) with hudef
  have e : (n : StatedSp 2 F) = u * torusHom t := by
    rw [hudef, Subgroup.coe_mul, Subgroup.coe_inv, hh, inv_mul_cancel_right]
  calc (n : StatedSp 2 F) * zElt a b * (n : StatedSp 2 F)⁻¹
      = u * (torusHom t * zElt a b * (torusHom t)⁻¹) * u⁻¹ := by rw [e]; group
    _ = zElt ((t 0 : F) ^ 2 * a) ((t 0 : F) * (t 1 : F) * b) := by
      rw [torusHom_conj_zElt, mul_zElt_comm hu, mul_inv_cancel_right]
    _ = zElt (((zChar n).1 : F) * a) (((zChar n).2 : F) * b) := by
      rw [zChar_apply, ← ht, Units.val_pow_eq_pow_val, Units.val_mul]

theorem zChar_surjective [Finite F] : Function.Surjective (zChar (F := F)) := by
  rintro ⟨l, m⟩
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (l : F)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact l.ne_zero (by rw [hr, mul_zero])
  set t : Fin 2 → Fˣ := ![Units.mk0 r hr0, (Units.mk0 r hr0)⁻¹ * m] with ht
  refine ⟨⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩, ?_⟩
  rw [zChar_apply, diagHom_torusHom]
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · simp [ht, hr, sq]
  · simp [ht]

@[expose] def yLong : StatedSp 2 F :=
  pairRootElt (a := (Sum.inr 1 : Fin 2 ⊕ Fin 2)) (b := Sum.inl 1) (by simp) 1

@[expose] def yShort : StatedSp 2 F :=
  pairRootElt (a := (Sum.inl 1 : Fin 2 ⊕ Fin 2)) (b := Sum.inl 0) (by simp) 1

theorem pairRootElt_one_mul_self {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b) :
    pairRootElt hab (1 : F) * pairRootElt hab 1 = 1 := by
  apply statedSp_ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_pairRootElt, pairRootMat_mul hab,
    CharTwo.add_self_eq_zero, pairRootMat_zero]
  rfl

theorem yLong_pow : ∃ k : ℕ, (yLong : StatedSp 2 F) ^ 2 ^ k = 1 :=
  ⟨1, by rw [pow_one, sq]; exact pairRootElt_one_mul_self _⟩

theorem yShort_pow : ∃ k : ℕ, (yShort : StatedSp 2 F) ^ 2 ^ k = 1 :=
  ⟨1, by rw [pow_one, sq]; exact pairRootElt_one_mul_self _⟩

omit [CharP F 2] in
theorem spMat_yLong : spMat (yLong : StatedSp 2 F) = 1 + single (Sum.inr 1) (Sum.inl 1) 1 := by
  change pairRootMat F _ _ 1 = _
  rw [pairRootMat_inr_inl_self, one_smul]

theorem spMat_yShort : spMat (yShort : StatedSp 2 F) =
    1 + single (Sum.inl 1) (Sum.inl 0) 1 + single (Sum.inr 0) (Sum.inr 1) 1 := by
  change pairRootMat F _ _ 1 = _
  rw [pairRootMat_inl_inl, one_smul, one_smul, sub_eq_add_neg]
  congr 1
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

theorem yLong_comm_iff (a b : F) : yLong * zElt a b = zElt a b * yLong ↔ b = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun g : StatedSp 2 F => spMat g (Sum.inr 1) (Sum.inr 0)) h
    simp only [spMat_mul, spMat_zElt, spMat_yLong] at h1
    simpa [uMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply] using h1
  · rintro rfl
    apply statedSp_ext
    change spMat yLong * spMat (zElt a 0) = spMat (zElt a 0) * spMat yLong
    rw [spMat_zElt, spMat_yLong]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [uMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply]

theorem yShort_comm_iff (a b : F) : yShort * zElt a b = zElt a b * yShort ↔ a = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun g : StatedSp 2 F => spMat g (Sum.inl 1) (Sum.inr 0)) h
    simp only [spMat_mul, spMat_zElt, spMat_yShort] at h1
    simpa [uMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply] using h1
  · rintro rfl
    apply statedSp_ext
    change spMat yShort * spMat (zElt 0 b) = spMat (zElt 0 b) * spMat yShort
    rw [spMat_zElt, spMat_yShort]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [uMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply,
        CharTwo.add_self_eq_zero]

theorem cartanSingerConcl_sp4_of [Finite F] {𝓡 : Subgroup (MulAut (StatedSp 2 F))}
    {G : Subgroup (StatedSp 2 F)} (hG : CartanSingerHyp (unipotent 2 F) 𝓡 G)
    {D : Type} [Group D] (χ : Fˣ × Fˣ →* D) (hχ : Function.Surjective χ) {a₀ b₀ : F}
    (hg₀ : zElt a₀ b₀ ∈ G) (hg₀1 : zElt a₀ b₀ ≠ 1)
    (hcancel : ∀ d d' : Fˣ × Fˣ, zElt ((d.1 : F) * a₀) ((d.2 : F) * b₀) =
      zElt ((d'.1 : F) * a₀) ((d'.2 : F) * b₀) → χ d = χ d')
    (htrans : ∀ a b : F, zElt a b ∈ G → zElt a b ≠ 1 →
      ∃ d : Fˣ × Fˣ, zElt ((d.1 : F) * a₀) ((d.2 : F) * b₀) = zElt a b)
    (hker : ∀ d : Fˣ × Fˣ, χ d = 1 → ∀ a b : F, zElt a b ∈ G →
      zElt ((d.1 : F) * a) ((d.2 : F) * b) = zElt a b)
    (hcyc : ∀ Λ : Subgroup D, (∀ d : Fˣ × Fˣ, χ d ∈ Λ →
      zElt ((d.1 : F) * a₀) ((d.2 : F) * b₀) ∈ G) → IsCyclic Λ) :
    CartanSingerConcl (unipotent 2 F) 𝓡 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := F) 2 2
  have hP : IsSylowTwoOf (unipotent 2 F) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  have hBN : borelSubgroup 2 F = Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) :=
    normalizer_unipotent.symm
  have hGz : ∀ g ∈ G, g = zElt (zC g) (zD g) := fun g hg =>
    eq_zElt_of_mem_center (hG.le g hg).1 fun t ht => (hG.le g hg).2 t ht
  refine cartanSingerConcl_of_hom hP unipotent_le_borelSubgroup hBN.le (χ.comp zChar)
    (hχ.comp zChar_surjective) hG (fun ρ hρ n hn => ?_) hg₀ hg₀1 (fun n n' h => ?_)
    (fun g hg hg1 => ?_) (fun n hn g hg => ?_) fun Λ hΛ => hcyc Λ fun d hd => ?_
  · rw [hBN] at hn ⊢
    exact hG.apply_mem_normalizer hρ hn
  · rw [borel_conj_zElt, borel_conj_zElt] at h
    exact hcancel _ _ h
  · have hg' : zElt (zC g) (zD g) ∈ G := by
      rw [← hGz g hg]
      exact hg
    have hg1' : zElt (zC g) (zD g) ≠ 1 := by
      rw [← hGz g hg]
      exact hg1
    obtain ⟨d, hd⟩ := htrans _ _ hg' hg1'
    obtain ⟨n, rfl⟩ := zChar_surjective d
    refine ⟨n, ?_⟩
    rw [borel_conj_zElt, hd, ← hGz g hg]
  · have hg' : zElt (zC g) (zD g) ∈ G := by
      rw [← hGz g hg]
      exact hg
    have h1 := hker (zChar n) hn (zC g) (zD g) hg'
    rw [← borel_conj_zElt, ← hGz g hg] at h1
    calc (n : StatedSp 2 F) * g = (n : StatedSp 2 F) * g * (n : StatedSp 2 F)⁻¹ * n := by group
      _ = g * n := by rw [h1]
  · obtain ⟨n, rfl⟩ := zChar_surjective d
    have h1 := hΛ n hd
    rwa [borel_conj_zElt] at h1

theorem cartanSinger_sp4 [Finite F] : CartanSinger (StatedSp 2 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := F) 2 2
  refine cartanSinger_of_sylow Q fun 𝓡 G hG hC => ?_
  rw [hQ] at hG ⊢
  have hGz : ∀ g ∈ G, g = zElt (zC g) (zD g) := fun g hg =>
    eq_zElt_of_mem_center (hG.le g hg).1 fun t ht => (hG.le g hg).2 t ht
  have hne : ∀ {a b : F}, (a ≠ 0 ∨ b ≠ 0) → zElt a b ≠ 1 := fun h h1 =>
    (zElt_eq_one_iff.1 h1).elim fun ha hb => h.elim (· ha) (· hb)
  by_cases hL : ∃ a : F, a ≠ 0 ∧ zElt a 0 ∈ G
  ·
    obtain ⟨a₀, ha₀, hga₀⟩ := hL
    have hlong : ∀ a b : F, zElt a b ∈ G → b = 0 := fun a b hab =>
      (yLong_comm_iff a b).1 (hC _ hga₀ (hne (Or.inl ha₀)) yLong ((yLong_comm_iff a₀ 0).2 rfl)
        yLong_pow _ hab)
    refine cartanSingerConcl_sp4_of hG (MonoidHom.fst _ _) Prod.fst_surjective hga₀
      (hne (Or.inl ha₀)) (fun d d' h => Units.ext (mul_right_cancel₀ ha₀ (zElt_inj h).1))
      (fun a b hab hab1 => ?_) (fun d hd a b hab => ?_) fun Λ _ => inferInstance
    · obtain rfl := hlong a b hab
      have ha : a ≠ 0 := fun h => hab1 (by rw [h, zElt_zero])
      exact ⟨(Units.mk0 (a / a₀) (div_ne_zero ha ha₀), 1), by
        rw [Units.val_mk0, div_mul_cancel₀ _ ha₀, mul_zero]⟩
    · obtain rfl := hlong a b hab
      change d.1 = 1 at hd
      rw [hd, Units.val_one, one_mul, mul_zero]
  by_cases hS : ∃ b : F, b ≠ 0 ∧ zElt 0 b ∈ G
  ·
    obtain ⟨b₀, hb₀, hgb₀⟩ := hS
    have hshort : ∀ a b : F, zElt a b ∈ G → a = 0 := fun a b hab =>
      (yShort_comm_iff a b).1 (hC _ hgb₀ (hne (Or.inr hb₀)) yShort
        ((yShort_comm_iff 0 b₀).2 rfl) yShort_pow _ hab)
    refine cartanSingerConcl_sp4_of hG (MonoidHom.snd _ _) Prod.snd_surjective hgb₀
      (hne (Or.inr hb₀)) (fun d d' h => Units.ext (mul_right_cancel₀ hb₀ (zElt_inj h).2))
      (fun a b hab hab1 => ?_) (fun d hd a b hab => ?_) fun Λ _ => inferInstance
    · obtain rfl := hshort a b hab
      have hb : b ≠ 0 := fun h => hab1 (by rw [h, zElt_zero])
      exact ⟨(1, Units.mk0 (b / b₀) (div_ne_zero hb hb₀)), by
        rw [Units.val_mk0, div_mul_cancel₀ _ hb₀, mul_zero]⟩
    · obtain rfl := hshort a b hab
      change d.2 = 1 at hd
      rw [hd, Units.val_one, one_mul, mul_zero]
  push Not at hL hS
  have hmixed : ∀ a b : F, zElt a b ∈ G → zElt a b ≠ 1 → a ≠ 0 ∧ b ≠ 0 := by
    intro a b hab hab1
    refine ⟨fun ha => ?_, fun hb => ?_⟩
    · subst ha
      exact hab1 (zElt_eq_one_iff.2 ⟨rfl, by_contra fun hb => hS b hb hab⟩)
    · subst hb
      exact hab1 (zElt_eq_one_iff.2 ⟨by_contra fun ha => hL a ha hab, rfl⟩)
  obtain ⟨g₀, hg₀G, hg₀⟩ : ∃ g ∈ G, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : G = ⊥ := (Subgroup.eq_bot_iff_forall G).2 hcon
    have := hG.four_le
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hg₀' : zElt (zC g₀) (zD g₀) ∈ G := by
    rw [← hGz g₀ hg₀G]
    exact hg₀G
  have hg₀1 : zElt (zC g₀) (zD g₀) ≠ 1 := by
    rw [← hGz g₀ hg₀G]
    exact hg₀
  obtain ⟨ha₀, hb₀⟩ := hmixed _ _ hg₀' hg₀1
  refine cartanSingerConcl_sp4_of hG (MonoidHom.id _) Function.surjective_id hg₀' hg₀1
    (fun d d' h => Prod.ext (Units.ext (mul_right_cancel₀ ha₀ (zElt_inj h).1))
      (Units.ext (mul_right_cancel₀ hb₀ (zElt_inj h).2))) (fun a b hab hab1 => ?_)
    (fun d hd a b _ => ?_) fun Λ hΛ => ?_
  · obtain ⟨ha, hb⟩ := hmixed a b hab hab1
    exact ⟨(Units.mk0 (a / zC g₀) (div_ne_zero ha ha₀), Units.mk0 (b / zD g₀) (div_ne_zero hb hb₀)),
      by rw [Units.val_mk0, Units.val_mk0, div_mul_cancel₀ _ ha₀, div_mul_cancel₀ _ hb₀]⟩
  · change d = 1 at hd
    rw [hd, Prod.fst_one, Prod.snd_one, Units.val_one, one_mul, one_mul]
  ·
    refine isCyclic_of_injective ((MonoidHom.snd _ _).comp Λ.subtype) fun d d' h => ?_
    have h2 : (d : Fˣ × Fˣ).2 = (d' : Fˣ × Fˣ).2 := h
    have h1 := mul_mem (hΛ d d.2) (hΛ d' d'.2)
    rw [zElt_mul, h2, CharTwo.add_self_eq_zero] at h1
    have h3 : ((d : Fˣ × Fˣ).1 : F) * zC g₀ + ((d' : Fˣ × Fˣ).1 : F) * zC g₀ = 0 :=
      by_contra fun h4 => hL _ h4 h1
    have h4 : ((d : Fˣ × Fˣ).1 : F) = (d' : Fˣ × Fˣ).1 :=
      mul_right_cancel₀ ha₀ ((eq_neg_of_add_eq_zero_left h3).trans (CharTwo.neg_eq _))
    exact Subtype.ext (Prod.ext (Units.ext h4) h2)

end CFSG.Quasithin.H13.KG68.Singer.Sp4
