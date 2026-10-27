module

public import CFSG.Quasithin.H13.L32AL2j
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.H13.L32AL2i

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

structure IsModel {F : Type} [Field F]
    (π : TensorG2 F →* ↥(X.img (conjClosure K T))) (β : Hat V (A6.g1 T V) W ≃* TensorE2 F) :
    Prop where
  surj : Function.Surjective π
  data : IsTensorData2 (X.img (conjClosure K T)) π β
  card : Nat.card F = 4

theorem exists_model (hD36 : D36) (hD37 : D37) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (π : TensorG2 F →* ↥(X.img (conjClosure K T)))
      (β : Hat V (A6.g1 T V) W ≃* TensorE2 F), X.IsModel π β := by
  obtain ⟨F, fF, finF, hF, π, β, hπ, hd⟩ :=
    exists_tensorData2 (X.omega4 hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334)
  exact ⟨F, fF, finF, π, β, hπ, hd, by rw [hF]; norm_num⟩

variable {X}

theorem IsModel.two {F : Type} [Field F] [Finite F]
    {π : TensorG2 F →* ↥(X.img (conjClosure K T))} {β : Hat V (A6.g1 T V) W ≃* TensorE2 F}
    (Y : X.IsModel π β) : (2 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h4 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, Y.card] at h4
  have : (2 : F) * 2 = 0 := by
    have e : (2 : F) * 2 = ((4 : ℕ) : F) := by norm_num
    rw [e, h4]
  exact mul_self_eq_zero.mp this

section Factors

variable {F : Type} [Field F] (π : TensorG2 F →* ↥(X.img (conjClosure K T)))

@[expose] noncomputable def leftImg : Subgroup (MulAut (Hat V (A6.g1 T V) W)) :=
  ((X.img (conjClosure K T)).subtype.comp (π.comp (MonoidHom.inl _ _))).range

@[expose] noncomputable def rightImg : Subgroup (MulAut (Hat V (A6.g1 T V) W)) :=
  ((X.img (conjClosure K T)).subtype.comp (π.comp (MonoidHom.inr _ _))).range

theorem mem_leftImg {y : MulAut (Hat V (A6.g1 T V) W)} :
    y ∈ leftImg π ↔ ∃ g : ↥(StatedSL 2 F), (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) = y := by
  simp [leftImg]

theorem mem_rightImg {y : MulAut (Hat V (A6.g1 T V) W)} :
    y ∈ rightImg π ↔ ∃ h : ↥(StatedSL 2 F), (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) = y := by
  simp [rightImg]

theorem leftImg_le : leftImg π ≤ X.img (conjClosure K T) := by
  rintro _ ⟨γ, rfl⟩
  exact (π _).2

theorem rightImg_le : rightImg π ≤ X.img (conjClosure K T) := by
  rintro _ ⟨γ, rfl⟩
  exact (π _).2

theorem card_leftImg_le [Finite F] : Nat.card (leftImg π) ≤ Nat.card ↥(StatedSL 2 F) :=
  Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem card_rightImg_le [Finite F] : Nat.card (rightImg π) ≤ Nat.card ↥(StatedSL 2 F) :=
  Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem left_right_comm (g h : ↥(StatedSL 2 F)) :
    (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) =
      (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) := by
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk,
    Prod.mk_mul_mk, mul_one, one_mul, one_mul, mul_one]

theorem split (g h : ↥(StatedSL 2 F)) :
    (π (g, h) : MulAut (Hat V (A6.g1 T V) W)) =
      (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) := by
  rw [← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

end Factors

section Ident

variable {F : Type} [Field F] [Finite F] {π : TensorG2 F →* ↥(X.img (conjClosure K T))}
  {β : Hat V (A6.g1 T V) W ≃* TensorE2 F}

theorem IsModel.card_sl (Y : X.IsModel π β) : Nat.card ↥(StatedSL 2 F) = 60 := by
  rw [card_statedSL_two1527d, Y.card]
  norm_num

omit [Finite F] in
theorem IsModel.conj_mem_leftImg (Y : X.IsModel π β) {m y : MulAut (Hat V (A6.g1 T V) W)}
    (hm : m ∈ X.img (conjClosure K T)) (hy : y ∈ leftImg π) : m * y * m⁻¹ ∈ leftImg π := by
  obtain ⟨γ, hγ⟩ := Y.surj ⟨m, hm⟩
  obtain ⟨g, rfl⟩ := (mem_leftImg π).mp hy
  have hm' : m = (π γ : MulAut (Hat V (A6.g1 T V) W)) := by rw [hγ]
  rw [mem_leftImg]
  refine ⟨γ.1 * g * γ.1⁻¹, ?_⟩
  rw [hm', ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
    ← map_mul]
  congr 2
  exact Prod.ext (by simp) (by simp)

omit [Finite F] in
theorem IsModel.conj_mem_rightImg (Y : X.IsModel π β) {m y : MulAut (Hat V (A6.g1 T V) W)}
    (hm : m ∈ X.img (conjClosure K T)) (hy : y ∈ rightImg π) : m * y * m⁻¹ ∈ rightImg π := by
  obtain ⟨γ, hγ⟩ := Y.surj ⟨m, hm⟩
  obtain ⟨g, rfl⟩ := (mem_rightImg π).mp hy
  have hm' : m = (π γ : MulAut (Hat V (A6.g1 T V) W)) := by rw [hγ]
  rw [mem_rightImg]
  refine ⟨γ.2 * g * γ.2⁻¹, ?_⟩
  rw [hm', ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
    ← map_mul]
  congr 2
  exact Prod.ext (by simp) (by simp)

theorem IsModel.eq_left_or_right (Y : X.IsModel π β)
    {N : Subgroup (MulAut (Hat V (A6.g1 T V) W))} (hNM : N ≤ X.img (conjClosure K T))
    (hnorm : ∀ m ∈ X.img (conjClosure K T), ∀ n ∈ N, m * n * m⁻¹ ∈ N) [IsSimpleGroup ↥N]
    (hnc : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) (hcard : Nat.card N = 60) :
    N = leftImg π ∨ N = rightImg π := by
  have key : ∀ P : Subgroup (MulAut (Hat V (A6.g1 T V) W)), P ≤ X.img (conjClosure K T) →
      (∀ m ∈ X.img (conjClosure K T), ∀ y ∈ P, m * y * m⁻¹ ∈ P) → Nat.card P ≤ 60 →
        N = P ∨ ∀ n ∈ N, ∀ p ∈ P, n * p = p * n := by
    intro P hPM hPn hPc
    have hNPn : ((N ⊓ P).subgroupOf N).Normal := by
      refine ⟨fun x hx n => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hx' := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨by simpa using mul_mem (mul_mem n.2 hx'.1) (inv_mem n.2),
        by simpa using hPn _ (hNM n.2) _ hx'.2⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ P).subgroupOf N) with h | h
    · right
      intro n hn p hp
      have hc : n * p * n⁻¹ * p⁻¹ ∈ N ⊓ P := by
        refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (hPn _ (hNM hn) _ hp) (inv_mem hp)⟩
        have := mul_mem hn (hnorm p (hPM hp) n⁻¹ (inv_mem hn))
        rwa [show n * (p * n⁻¹ * p⁻¹) = n * p * n⁻¹ * p⁻¹ by group] at this
      have hc' : (⟨_, hc.1⟩ : ↥N) ∈ (N ⊓ P).subgroupOf N := hc
      rw [h, Subgroup.mem_bot] at hc'
      have := congrArg Subtype.val hc'
      simp only [OneMemClass.coe_one] at this
      calc n * p = (n * p * n⁻¹ * p⁻¹) * p * n := by group
        _ = p * n := by rw [this, one_mul]
    · left
      have hle : N ≤ P := fun n hn => by
        have : (⟨n, hn⟩ : ↥N) ∈ (N ⊓ P).subgroupOf N := by rw [h]; exact Subgroup.mem_top _
        exact this.2
      exact Subgroup.eq_of_le_of_card_ge hle (hPc.trans hcard.ge)
  rcases key (leftImg π) (leftImg_le π) (fun m hm y hy => Y.conj_mem_leftImg hm hy)
      ((card_leftImg_le π).trans Y.card_sl.le) with h1 | h1
  · exact Or.inl h1
  rcases key (rightImg π) (rightImg_le π) (fun m hm y hy => Y.conj_mem_rightImg hm hy)
      ((card_rightImg_le π).trans Y.card_sl.le) with h2 | h2
  · exact Or.inr h2
  exfalso
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  obtain ⟨γ, hγ⟩ := Y.surj ⟨b, hNM hb⟩
  have hb' : b = (π (γ.1, 1) : MulAut (Hat V (A6.g1 T V) W)) * (π (1, γ.2) : MulAut _) := by
    rw [← split π γ.1 γ.2]
    exact (congrArg Subtype.val hγ).symm
  apply hab
  have c1 := h1 a ha _ ((mem_leftImg π).mpr ⟨γ.1, rfl⟩)
  have c2 := h2 a ha _ ((mem_rightImg π).mpr ⟨γ.2, rfl⟩)
  rw [hb', ← mul_assoc, c1, mul_assoc, c2, mul_assoc]

theorem img_K_comm (hA37 : A37ForSQTK) {a b : MulAut (Hat V (A6.g1 T V) W)} (ha : a ∈ X.img K)
    (hb : b ∈ X.img (K.map (MulAut.conj t₀ : G →* G))) : a * b = b * a := by
  rw [img_eq_map] at ha hb
  obtain ⟨k, hk, rfl⟩ := ha
  obtain ⟨k', hk', rfl⟩ := hb
  rw [← map_mul, ← map_mul, X.C.commute_kb hA37 hk hk']

theorem img_K_inf (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    X.img K ⊓ X.img (K.map (MulAut.conj t₀ : G →* G)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hinj := X.actDot_injective hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have h1 := (Subgroup.mem_inf.mp hy).1
  have h2 := (Subgroup.mem_inf.mp hy).2
  rw [img_eq_map] at h1 h2
  obtain ⟨k, hk, rfl⟩ := h1
  obtain ⟨k', hk', hkk'⟩ := h2
  rw [hinj hkk'] at hk'
  rw [X.C.eq_one_of_mem_kb_kt hA37 hk hk', map_one]
  exact one_mem _

theorem nonempty_equiv_img_Kt (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    Nonempty (↥(X.img (K.map (MulAut.conj t₀ : G →* G))) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨φ⟩ := X.nonempty_equiv_img_K hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  rw [img_Kt_eq]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulEquiv.injective _)).symm.trans φ⟩

omit [Finite G] in
theorem props_of_equiv {N : Subgroup (MulAut (Hat V (A6.g1 T V) W))}
    (φ : ↥N ≃* alternatingGroup (Fin 5)) :
    IsSimpleGroup ↥N ∧ Nat.card N = 60 ∧ ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨(MulEquiv.isSimpleGroup_congr φ).mpr hs, ?_, ?_⟩
  · rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  · obtain ⟨a, b, hab⟩ := alt5_noncomm
    refine ⟨φ.symm a, (φ.symm a).2, φ.symm b, (φ.symm b).2, fun h => hab ?_⟩
    have : φ.symm a * φ.symm b = φ.symm b * φ.symm a := Subtype.ext h
    have := congrArg φ this
    simpa using this

theorem IsModel.factors (Y : X.IsModel π β) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    (X.img K = leftImg π ∧ X.img (K.map (MulAut.conj t₀ : G →* G)) = rightImg π) ∨
      (X.img K = rightImg π ∧ X.img (K.map (MulAut.conj t₀ : G →* G)) = leftImg π) := by
  obtain ⟨φ⟩ := X.nonempty_equiv_img_K hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  obtain ⟨φ'⟩ := X.nonempty_equiv_img_Kt hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  obtain ⟨hs, hc, hnc⟩ := props_of_equiv φ
  obtain ⟨hs', hc', hnc'⟩ := props_of_equiv φ'
  have hinf := X.img_K_inf hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hKt : K.map (MulAut.conj t₀ : G →* G) ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    simpa using mem_conjClosure X.C.ht₀ hk
  have hle : X.img K ≤ X.img (conjClosure K T) :=
    Subgroup.map_mono fun x hx => le_conjClosure K T hx
  have hle' : X.img (K.map (MulAut.conj t₀ : G →* G)) ≤ X.img (conjClosure K T) :=
    Subgroup.map_mono fun x hx => hKt hx
  have hnormL : X.img (conjClosure K T) ≤
      Subgroup.normalizer (X.img K : Set (MulAut (Hat V (A6.g1 T V) W))) := by
    rw [img_K₀_eq]
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← X.img_K_comm hA37 ha hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have h2 := X.img_K_comm hA37 ha (inv_mem hb)
      have e : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [← h2]
          _ = b * a * b⁻¹ := by group
      rw [e]
      exact ha
  have hnormLt : X.img (conjClosure K T) ≤ Subgroup.normalizer
      (X.img (K.map (MulAut.conj t₀ : G →* G)) : Set (MulAut (Hat V (A6.g1 T V) W))) := by
    rw [img_K₀_eq]
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [X.img_K_comm hA37 ha hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have h2 := X.img_K_comm hA37 (inv_mem ha) hb
      have e : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
          _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h2]
          _ = a * b * a⁻¹ := by group
      rw [e]
      exact hb
  have hn1 : ∀ m ∈ X.img (conjClosure K T), ∀ n ∈ X.img K, m * n * m⁻¹ ∈ X.img K :=
    fun m hm n hn => (Subgroup.mem_normalizer_iff.mp (hnormL hm) n).mp hn
  have hn2 : ∀ m ∈ X.img (conjClosure K T), ∀ n ∈ X.img (K.map (MulAut.conj t₀ : G →* G)),
      m * n * m⁻¹ ∈ X.img (K.map (MulAut.conj t₀ : G →* G)) :=
    fun m hm n hn => (Subgroup.mem_normalizer_iff.mp (hnormLt hm) n).mp hn
  have hne : X.img K ≠ X.img (K.map (MulAut.conj t₀ : G →* G)) := by
    intro h
    rw [← h, inf_idem] at hinf
    have : Nat.card (X.img K) = 1 := by rw [hinf]; exact Subgroup.card_bot
    omega
  rcases Y.eq_left_or_right hle hn1 hnc hc with h1 | h1 <;>
    rcases Y.eq_left_or_right hle' hn2 hnc' hc' with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem IsModel.fix_left (Y : X.IsModel π β) (hcard : Nat.card (leftImg π) = 60)
    {y : MulAut (Hat V (A6.g1 T V) W)} (hy : y ∈ leftImg π) (hy1 : y ≠ 1) {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) {w : Hat V (A6.g1 T V) W} (hw : y w = w) : w = 1 := by
  set φ := (X.img (conjClosure K T)).subtype.comp (π.comp (MonoidHom.inl _ _)) with hφ
  have hbij : Function.Bijective φ.rangeRestrict :=
    (MonoidHom.rangeRestrict_surjective φ).bijective_of_nat_card_le
      (by rw [Y.card_sl]; exact hcard.ge)
  have hinj : Function.Injective φ := by
    intro a b h
    exact hbij.1 (Subtype.ext h)
  obtain ⟨g, rfl⟩ := (mem_leftImg π).mp hy
  have hgm : g ^ m = 1 := hinj (by
    show φ (g ^ m) = φ 1
    rw [map_pow, map_one]
    exact hym)
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hy1
    show φ 1 = 1
    exact map_one φ
  exact fix_eq_one_left Y.two Y.data hm hgm hg1 hw

theorem IsModel.fix_right (Y : X.IsModel π β) (hcard : Nat.card (rightImg π) = 60)
    {y : MulAut (Hat V (A6.g1 T V) W)} (hy : y ∈ rightImg π) (hy1 : y ≠ 1) {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) {w : Hat V (A6.g1 T V) W} (hw : y w = w) : w = 1 := by
  set φ := (X.img (conjClosure K T)).subtype.comp (π.comp (MonoidHom.inr _ _)) with hφ
  have hbij : Function.Bijective φ.rangeRestrict :=
    (MonoidHom.rangeRestrict_surjective φ).bijective_of_nat_card_le
      (by rw [Y.card_sl]; exact hcard.ge)
  have hinj : Function.Injective φ := by
    intro a b h
    exact hbij.1 (Subtype.ext h)
  obtain ⟨g, rfl⟩ := (mem_rightImg π).mp hy
  have hgm : g ^ m = 1 := hinj (by
    show φ (g ^ m) = φ 1
    rw [map_pow, map_one]
    exact hym)
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hy1
    show φ 1 = 1
    exact map_one φ
  exact fix_eq_one_right Y.two Y.data hm hgm hg1 hw

theorem IsModel.inner_left_of_right (Y : X.IsModel π β) {f : MulAut (Hat V (A6.g1 T V) W)}
    (hf : ∃ ℓ' ∈ rightImg π, ∀ y ∈ rightImg π, f * y * f⁻¹ = ℓ' * y * ℓ'⁻¹) :
    ∃ ℓ ∈ leftImg π, ∀ y ∈ leftImg π, f * y * f⁻¹ = ℓ * y * ℓ⁻¹ := by
  obtain ⟨ℓ', hℓ', hf'⟩ := hf
  have hc : ∀ h : ↥(StatedSL 2 F), (ℓ'⁻¹ * f) * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) =
      (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ'⁻¹ * f) := by
    intro h
    have e := hf' _ ((mem_rightImg π).mpr ⟨h, rfl⟩)
    calc (ℓ'⁻¹ * f) * (π (1, h) : MulAut (Hat V (A6.g1 T V) W))
        = ℓ'⁻¹ * (f * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * f⁻¹) * f := by group
      _ = ℓ'⁻¹ * (ℓ' * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * ℓ'⁻¹) * f := by rw [e]
      _ = (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ'⁻¹ * f) := by group
  obtain ⟨g₀, hg₀⟩ := exists_conj_left Y.two Y.data hc
  refine ⟨π (g₀, 1), (mem_leftImg π).mpr ⟨g₀, rfl⟩, fun y hy => ?_⟩
  obtain ⟨g, rfl⟩ := (mem_leftImg π).mp hy
  obtain ⟨h₁, rfl⟩ := (mem_rightImg π).mp hℓ'
  set ℓ : MulAut (Hat V (A6.g1 T V) W) := (π (1, h₁) : MulAut (Hat V (A6.g1 T V) W)) with hℓ
  set Z : MulAut (Hat V (A6.g1 T V) W) :=
    (π (g₀ * g * g₀⁻¹, 1) : MulAut (Hat V (A6.g1 T V) W)) with hZ
  have e1 : ℓ⁻¹ * f * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ⁻¹ * f)⁻¹ = Z := hg₀ g
  have hcomm : Z * ℓ = ℓ * Z := left_right_comm π (g₀ * g * g₀⁻¹) h₁
  have hsplit : Z = (π (g₀, 1) : MulAut (Hat V (A6.g1 T V) W)) *
      (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * (π (g₀, 1) : MulAut (Hat V (A6.g1 T V) W))⁻¹ := by
    rw [hZ, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
      ← map_mul]
    congr 2
    exact Prod.ext (by simp) (by simp)
  rw [← hsplit]
  calc f * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * f⁻¹
      = ℓ * (ℓ⁻¹ * f * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ⁻¹ * f)⁻¹) * ℓ⁻¹ := by
        group
    _ = ℓ * Z * ℓ⁻¹ := by rw [e1]
    _ = Z := by rw [← hcomm]; group

theorem IsModel.inner_right_of_left (Y : X.IsModel π β) {f : MulAut (Hat V (A6.g1 T V) W)}
    (hf : ∃ ℓ' ∈ leftImg π, ∀ y ∈ leftImg π, f * y * f⁻¹ = ℓ' * y * ℓ'⁻¹) :
    ∃ ℓ ∈ rightImg π, ∀ y ∈ rightImg π, f * y * f⁻¹ = ℓ * y * ℓ⁻¹ := by
  obtain ⟨ℓ', hℓ', hf'⟩ := hf
  have hc : ∀ g : ↥(StatedSL 2 F), (ℓ'⁻¹ * f) * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) =
      (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ'⁻¹ * f) := by
    intro g
    have e := hf' _ ((mem_leftImg π).mpr ⟨g, rfl⟩)
    calc (ℓ'⁻¹ * f) * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W))
        = ℓ'⁻¹ * (f * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * f⁻¹) * f := by group
      _ = ℓ'⁻¹ * (ℓ' * (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * ℓ'⁻¹) * f := by rw [e]
      _ = (π (g, 1) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ'⁻¹ * f) := by group
  obtain ⟨h₀, hh₀⟩ := exists_conj_right Y.two Y.data hc
  refine ⟨π (1, h₀), (mem_rightImg π).mpr ⟨h₀, rfl⟩, fun y hy => ?_⟩
  obtain ⟨h, rfl⟩ := (mem_rightImg π).mp hy
  obtain ⟨g₁, rfl⟩ := (mem_leftImg π).mp hℓ'
  set ℓ : MulAut (Hat V (A6.g1 T V) W) := (π (g₁, 1) : MulAut (Hat V (A6.g1 T V) W)) with hℓ
  set Z : MulAut (Hat V (A6.g1 T V) W) :=
    (π (1, h₀ * h * h₀⁻¹) : MulAut (Hat V (A6.g1 T V) W)) with hZ
  have e1 : ℓ⁻¹ * f * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ⁻¹ * f)⁻¹ = Z := hh₀ h
  have hcomm : ℓ * Z = Z * ℓ := left_right_comm π g₁ (h₀ * h * h₀⁻¹)
  have hsplit : Z = (π (1, h₀) : MulAut (Hat V (A6.g1 T V) W)) *
      (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * (π (1, h₀) : MulAut (Hat V (A6.g1 T V) W))⁻¹ := by
    rw [hZ, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
      ← map_mul]
    congr 2
    exact Prod.ext (by simp) (by simp)
  rw [← hsplit]
  calc f * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * f⁻¹
      = ℓ * (ℓ⁻¹ * f * (π (1, h) : MulAut (Hat V (A6.g1 T V) W)) * (ℓ⁻¹ * f)⁻¹) * ℓ⁻¹ := by
        group
    _ = ℓ * Z * ℓ⁻¹ := by rw [e1]
    _ = Z := by rw [hcomm]; group

end Ident

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
