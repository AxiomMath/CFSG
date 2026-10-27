module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep7C
public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenFiveStmt

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def trivSub (Z I : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ Subgroup.normalizer (Z : Set G) ∧ k ∈ Subgroup.normalizer (I : Set G) ∧
    ∀ z ∈ Z, k * z * k⁻¹ * z⁻¹ ∈ I}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun z _ => by simp⟩
  mul_mem' := by
    rintro k k' ⟨hkZ, hkI, hk⟩ ⟨hk'Z, hk'I, hk'⟩
    refine ⟨Subgroup.mul_mem _ hkZ hk'Z, Subgroup.mul_mem _ hkI hk'I, fun z hz => ?_⟩
    have e : k * k' * z * (k * k')⁻¹ * z⁻¹ =
        (k * (k' * z * k'⁻¹ * z⁻¹) * k⁻¹) * (k * z * k⁻¹ * z⁻¹) := by group
    rw [e]
    exact I.mul_mem ((Subgroup.mem_normalizer_iff.1 hkI _).1 (hk' z hz)) (hk z hz)
  inv_mem' := by
    rintro k ⟨hkZ, hkI, hk⟩
    refine ⟨Subgroup.inv_mem _ hkZ, Subgroup.inv_mem _ hkI, fun z hz => ?_⟩
    have hz' : k⁻¹ * z * k ∈ Z := by
      simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hkZ) z).1 hz
    have h := hk _ hz'
    have e1 : k * (k⁻¹ * z * k) * k⁻¹ * (k⁻¹ * z * k)⁻¹ = z * (k⁻¹ * z * k)⁻¹ := by group
    rw [e1] at h
    have e2 : k⁻¹ * z * k⁻¹⁻¹ * z⁻¹ = (z * (k⁻¹ * z * k)⁻¹)⁻¹ := by group
    rw [e2]
    exact I.inv_mem h

theorem mem_trivSub {Z I : Subgroup G} {k : G} :
    k ∈ trivSub Z I ↔ k ∈ Subgroup.normalizer (Z : Set G) ∧ k ∈ Subgroup.normalizer (I : Set G) ∧
      ∀ z ∈ Z, k * z * k⁻¹ * z⁻¹ ∈ I := Iff.rfl

theorem trivSub_conj {Z I : Subgroup G} {h : G} (hhZ : h ∈ Subgroup.normalizer (Z : Set G))
    (hhI : h ∈ Subgroup.normalizer (I : Set G)) {k : G} (hk : k ∈ trivSub Z I) :
    h * k * h⁻¹ ∈ trivSub Z I := by
  obtain ⟨hkZ, hkI, hk⟩ := (mem_trivSub).1 hk
  refine mem_trivSub.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hhZ hkZ) (Subgroup.inv_mem _ hhZ),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhI hkI) (Subgroup.inv_mem _ hhI), fun z hz => ?_⟩
  have hz' : h⁻¹ * z * h ∈ Z := by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hhZ) z).1 hz
  have e : h * k * h⁻¹ * z * (h * k * h⁻¹)⁻¹ * z⁻¹ =
      h * (k * (h⁻¹ * z * h) * k⁻¹ * (h⁻¹ * z * h)⁻¹) * h⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 hhI _).1 (hk _ hz')

section Step8

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem K1_eq_commutator (h12813f : Lemma12_8_13_five) {T₀ L₀ V₀ V₁₀ V₂₀ K₁₀ : Subgroup G}
    (hs : Setting1282One G T₀ L₀ V₀ 4 V₁₀ V₂₀) (hLK : lOne L₀ V₁₀ ≤ K₁₀)
    {g₀ : G} (hgP : g₀ ∈ p128 T₀ L₀ V₀)
    (hgN : g₀ ∉ Subgroup.normalizer (V₁₀ : Set G)) (D₀ : HatModelU (u128 V₀ V₁₀))
    (hK₁C : quasithinIsCComponent K₁₀ (Subgroup.normalizer (V₁₀ : Set G)))
    (hK4 : Nonempty (↥K₁₀ ⧸ CFSG.pCore 2 ↥K₁₀ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hG5 : G112Concl5 D₀.B (D₀.img (Subgroup.normalizer (V₁₀ : Set G))))
    (himg : (D₀.img K₁₀).relIndex (D₀.img (Subgroup.normalizer (V₁₀ : Set G))) ≤ 2) :
    K₁₀ = ⁅K₁₀, CFSG.conjugate (zU128 V₀ V₁₀) g₀⁆ :=
  (h12813f G T₀ L₀ V₀ V₁₀ V₂₀ K₁₀ hs hLK hK₁C hK4 g₀ hgP hgN D₀ hG5 himg).2.2.2.2.2.1

end Step8

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem DIEnv.Dg_mem_trivSub (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13)
    (F2 : FactF2) (F3 : FactF3) (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    {d : G} (hd : d ∈ CFSG.conjugate (zU128 V V₁) g) :
    d ∈ trivSub (zU128 V V₁) E.I := by
  have hdN : d ∈ Subgroup.normalizer (u128 V V₁ : Set G) :=
    (Dg_mem_normalizers h12813 E.hs E.hgP E.hgN hd).2
  have hdZ : d ∈ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) hdN
  exact mem_trivSub.2 ⟨hdZ, E.hTI (Dg_le_T h1222 h1289 E.hcx E.hs E.hgP E.hgN hd),
    fun z hz => E.Dg_comm h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hd hz⟩

theorem DIEnv.K1_triv (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13)
    (h12813f : Lemma12_8_13_five) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    (hK₁C : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hG5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    {k : G} (hk : k ∈ K₁) {z : G} (hz : z ∈ zU128 V V₁) :
    k * z * k⁻¹ * z⁻¹ ∈ E.I := by
  have hcomm : K₁ = ⁅K₁, CFSG.conjugate (zU128 V V₁) g⁆ :=
    K1_eq_commutator h12813f E.hs E.hLK E.hgP E.hgN D hK₁C hK4 hG5 E.himg
  have hcl : ⁅K₁, CFSG.conjugate (zU128 V V₁) g⁆ ≤ trivSub (zU128 V V₁) E.I := by
    apply Subgroup.commutator_le.2
    intro h hh d hd
    rw [commutatorElement_def]
    have hhZ : h ∈ Subgroup.normalizer (zU128 V V₁ : Set G) :=
      CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) (E.hK₁U hh)
    have hhI : h ∈ Subgroup.normalizer (E.I : Set G) := E.hKI hh
    have hdT := E.Dg_mem_trivSub h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hd
    exact (trivSub (zU128 V V₁) E.I).mul_mem (trivSub_conj hhZ hhI hdT)
      ((trivSub (zU128 V V₁) E.I).inv_mem hdT)
  have hk' : k ∈ ⁅K₁, CFSG.conjugate (zU128 V V₁) g⁆ := by
    rw [← hcomm]
    exact hk
  exact (mem_trivSub.1 (hcl hk')).2.2 z hz

end Env

end CFSG.Quasithin.H13.C1294
