module

public import CFSG.Quasithin.Background.B15P4Layer2Faith
public import CFSG.Quasithin.Background.B15P4Layer2Weight
public import CFSG.Quasithin.Background.B1MoreElevenC
public import CFSG.Quasithin.Background.B15P4Res

public section

namespace CFSG.Quasithin.B15P4

open CFSG.Open
open scoped commutatorElement

variable {V : Type*} [CommGroup V]

theorem apply_mul_inv_eq_of_comm {a b : MulAut V} (hab : b * a = a * b) (v : V)
    (h : b (a v * v⁻¹) = a v * v⁻¹) : a (b v * v⁻¹) = b v * v⁻¹ := by
  have hab' : b (a v) = a (b v) := by
    have := congrArg (fun t : MulAut V => t v) hab
    simpa only [MulAut.mul_apply] using this
  rw [map_mul, map_inv, hab'] at h
  have h2 : a (b v) = a v * v⁻¹ * b v := mul_inv_eq_iff_eq_mul.1 h
  rw [map_mul, map_inv, h2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem A2sub_comm_fix {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {b : MulAut V} (hb : b ∈ A2sub A) {a : MulAut V} (ha : a ∈ A) (v : V) :
    a (b v * v⁻¹) = b v * v⁻¹ :=
  apply_mul_inv_eq_of_comm (hc b (A2sub_le A hb) a ha) v (A2sub_fix_comm hc hb ha v)

theorem A2sub_eq_inf_centSub {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    A2sub A = A ⊓ centSub (commV A) := by
  ext b
  rw [mem_A2sub, Subgroup.mem_inf, mem_centSub]
  constructor
  · rintro ⟨hb, h⟩
    refine ⟨hb, fun u hu => ?_⟩
    have hle : commV A ≤ MonoidHom.eqLocus b.toMonoidHom (MonoidHom.id V) :=
      G6.commV_le_iff.2 fun a ha v => A2sub_fix_comm hc (mem_A2sub.2 ⟨hb, h⟩) ha v
    exact hle hu
  · rintro ⟨hb, h⟩
    refine ⟨hb, fun v a ha => ?_⟩
    rw [cv_eq]
    exact apply_mul_inv_eq_of_comm (hc b hb a ha) v (h _ (G6.mem_commV_of_mem ha v))

theorem commSub_commV_zpowers_eq_bot {A : Subgroup (MulAut V)}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {b : MulAut V} (hb : b ∈ A2sub A) :
    commSub (commV (Subgroup.zpowers b)) A = ⊥ := by
  rw [commSub_eq_bot_iff, G6.commV_le_iff]
  intro x hx v
  have hbT : b ∈ trivQuot (fixV A) := mem_trivQuot.2 fun v a ha => A2sub_comm_fix hc hb ha v
  exact mem_trivQuot.1 ((Subgroup.zpowers_le.2 hbT) hx) v

theorem apply_mem_of_mem_iSup {ι : Type*} {J : ι → Subgroup V} {S : Subgroup V} (f : MulAut V)
    (h : ∀ i, ∀ w ∈ J i, f w ∈ S) : ∀ w ∈ ⨆ i, J i, f w ∈ S := by
  intro w hw
  have : (⨆ i, J i) ≤ S.comap f.toMonoidHom := iSup_le fun i w hw => h i w hw
  exact this hw

section Moved

variable [Finite V]

theorem false_of_moved (hV : ∀ v : V, v ^ 2 = 1) {G A K : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) (hK : IsComponentOf K G) {a₀ : MulAut V} (ha₀ : a₀ ∈ A)
    (hn : a₀ ∉ Subgroup.normalizer (K : Set (MulAut V))) (hcomm : commV (Kspan A K) = ⊤)
    (hmin : ∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False)
    {b : MulAut V} (hb : b ∈ A2sub A) (hb1 : b ≠ 1) {I : Subgroup V}
    (hI : I ∈ IrrPlus (Kspan A K) (⊤ : Subgroup V)) {a : MulAut V} (ha : a ∈ A)
    (hmove : I.map a.toMonoidHom ≠ I) : False := by
  classical
  set E := Kspan A K with hE
  have hAG : A ≤ G := hA.1
  have hAab : IsElemAbelian2 A := hA.2.2.1
  have hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hAab.1
  have hEA : ⁅E, A⁆ = E := commutator_Kspan_eq hK hAG ha₀ hn
  have hoT : oTwoUpper E = E := oTwoUpper_Kspan hK hAG
  have hCF : AllTwoChiefFactorsCentral E := allTwoChiefFactorsCentral_Kspan hK hAG
  have hC : A ⊓ Subgroup.centralizer (E : Set (MulAut V)) = ⊥ :=
    centralizer_Kspan_eq_bot hV hAab (ne_bot_of_isComponentOf hK) hEA hcomm hmin
  have hbA : b ∈ A := A2sub_le A hb
  have hb0 := commSub_commV_zpowers_eq_bot hc hb
  have hbfix : ∀ J ∈ IrrPlus E (⊤ : Subgroup V), J.map b.toMonoidHom = J := fun J hJ =>
    B7_2_1 hV hA hoT hEA hCF hbA hb0 hJ
  have hAmap : ∀ g ∈ A, ∀ J ∈ IrrPlus E (⊤ : Subgroup V),
      J.map g.toMonoidHom ∈ IrrPlus E (⊤ : Subgroup V) := fun g hg J hJ =>
    irrPlus_map (fun x hx => mul_mul_inv_mem_Kspan A K hg hx)
      (fun x hx => inv_mul_mul_mem_Kspan A K hg hx) hJ
  have hIZ : ¬ I ≤ fixV E := by
    obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.1 hI
    intro h
    rw [inf_eq_left.2 h] at hlt
    exact lt_irrefl _ hlt
  have hIb : ∀ x ∈ I, b x * x⁻¹ ∈ fixV E := by
    intro x hx
    have hI' := hAmap a ha I hI
    rcases irrPlus_sup_inf hI hI' with h | h
    · exact absurd h.symm hmove
    · have huI : b x * x⁻¹ ∈ I := by
        have h1 : b x ∈ I.map b.toMonoidHom := Subgroup.mem_map_of_mem b.toMonoidHom hx
        rw [hbfix I hI] at h1
        exact I.mul_mem h1 (I.inv_mem hx)
      have huI' : b x * x⁻¹ ∈ I.map a.toMonoidHom := by
        have h2 : a (b x * x⁻¹) = b x * x⁻¹ := A2sub_comm_fix hc hb ha x
        have h3 : a (b x * x⁻¹) ∈ I.map a.toMonoidHom :=
          Subgroup.mem_map_of_mem a.toMonoidHom huI
        rw [h2] at h3
        exact h3
      have hmem : b x * x⁻¹ ∈ (I ⊔ fixV E) ⊓ (I.map a.toMonoidHom ⊔ fixV E) :=
        ⟨Subgroup.mem_sup_left huI, Subgroup.mem_sup_left huI'⟩
      rw [h] at hmem
      exact hmem
  let φ : V →* V := b.toMonoidHom * (MonoidHom.id V)⁻¹
  let Pb : Subgroup V := (fixV E).comap φ
  have hPb : ∀ v, v ∈ Pb ↔ b v * v⁻¹ ∈ fixV E := fun v => Iff.rfl
  have hgIPb : ∀ g ∈ A, I.map g.toMonoidHom ≤ Pb := by
    rintro g hg _ ⟨x, hx, rfl⟩
    rw [hPb]
    have hgb : b (g x) = g (b x) := by
      have := congrArg (fun t : MulAut V => t x) (hc b hbA g hg)
      simpa only [MulAut.mul_apply] using this
    show b (g x) * (g x)⁻¹ ∈ fixV E
    rw [hgb, ← map_inv, ← map_mul]
    exact apply_mem_fixV_Kspan A K hg (hIb x hx)
  let S : Subgroup V := ⨆ g : ↥A, I.map (g : MulAut V).toMonoidHom
  have hIS : I ≤ S := fun x hx =>
    le_iSup (fun g : ↥A => I.map (g : MulAut V).toMonoidHom) ⟨1, A.one_mem⟩ ⟨x, hx, rfl⟩
  have hSA : ∀ a' ∈ A, ∀ w ∈ S, a' w ∈ S := by
    intro a' ha' w hw
    refine apply_mem_of_mem_iSup a' (fun g w hw => ?_) w hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact le_iSup (fun g : ↥A => I.map (g : MulAut V).toMonoidHom) ⟨a' * g, A.mul_mem ha' g.2⟩
      ⟨x, hx, rfl⟩
  have hSE : ∀ e ∈ E, ∀ w ∈ S, e w ∈ S := by
    intro e he w hw
    refine apply_mem_of_mem_iSup e (fun g w hw => ?_) w hw
    have hinv := (mem_irrPlus_top_iff.1 (hAmap g g.2 I hI)).1 e he w hw
    exact le_iSup (fun g : ↥A => I.map (g : MulAut V).toMonoidHom) g hinv
  have hSTop : S = ⊤ := by
    by_contra hne
    exact hIZ (hIS.trans (le_fixV_of_not_restrictable hEA hSA hSE
      (fun h1 h2 => hmin S hne hSA hSE h1 h2)))
  have hSPb : S ≤ Pb := iSup_le fun g => hgIPb g g.2
  have hbZ : ∀ v : V, b v * v⁻¹ ∈ fixV E := fun v =>
    (hPb v).1 (hSPb (hSTop ▸ Subgroup.mem_top v))
  exact hb1 (eq_one_of_commV_le hK hAG hcomm hC hbA hbZ)

theorem top_mem_irrPlus_of_fixed {G A K : Subgroup (MulAut V)} (hK : IsComponentOf K G)
    (hAG : A ≤ G) (hEA : ⁅Kspan A K, A⁆ = Kspan A K)
    (hmin : ∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False)
    (hfix : ∀ g ∈ A, ∀ J ∈ IrrPlus (Kspan A K) (⊤ : Subgroup V), J.map g.toMonoidHom = J) :
    (⊤ : Subgroup V) ∈ IrrPlus (Kspan A K) (⊤ : Subgroup V) := by
  have hne : commV (Kspan A K) ≠ ⊥ := by
    intro h
    have hbot : Kspan A K = ⊥ := eq_bot_of_commV_eq_bot h
    exact ne_bot_of_isComponentOf hK (eq_bot_iff.2 ((le_Kspan A K).trans hbot.le))
  obtain ⟨I, hI⟩ := B1Red.exists_mem_irrPlus (Kspan_perfect hK hAG) hne
  have hIA : ∀ a ∈ A, ∀ w ∈ I, a w ∈ I := by
    intro a ha w hw
    have h1 : a w ∈ I.map a.toMonoidHom := Subgroup.mem_map_of_mem a.toMonoidHom hw
    rwa [hfix a ha I hI] at h1
  have hIE := (mem_irrPlus_top_iff.1 hI).1
  have hIZ : ¬ I ≤ fixV (Kspan A K) := by
    obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.1 hI
    intro h
    rw [inf_eq_left.2 h] at hlt
    exact lt_irrefl _ hlt
  have hIt : I = ⊤ := by
    by_contra hne'
    exact hIZ (le_fixV_of_not_restrictable hEA hIA hIE
      (fun h1 h2 => hmin I hne' hIA hIE h1 h2))
  rwa [hIt] at hI

end Moved

end CFSG.Quasithin.B15P4
