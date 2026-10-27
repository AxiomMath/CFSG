module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1e3_comm_sup_le {V A B : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    (hB : B ≤ normalizer (V : Set G)) : ⁅V, A ⊔ B⁆ ≤ ⁅V, A⁆ ⊔ ⁅V, B⁆ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro x hx v hv
  have hmain : ∀ y ∈ (A ⊔ B : Subgroup G),
      y ∈ normalizer (V : Set G) ∧ ∀ w ∈ V, ⁅y, w⁆ ∈ ⁅V, A⁆ ⊔ ⁅V, B⁆ := by
    intro y hy
    rw [Subgroup.sup_eq_closure] at hy
    refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
      (p := fun z _ => z ∈ normalizer (V : Set G) ∧
        ∀ w ∈ V, ⁅z, w⁆ ∈ ⁅V, A⁆ ⊔ ⁅V, B⁆) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with hzA | hzB
      · refine ⟨hA hzA, fun w hw => ?_⟩
        rw [← commutatorElement_inv]
        exact (⁅V, A⁆ ⊔ ⁅V, B⁆).inv_mem
          (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hw hzA))
      · refine ⟨hB hzB, fun w hw => ?_⟩
        rw [← commutatorElement_inv]
        exact (⁅V, A⁆ ⊔ ⁅V, B⁆).inv_mem
          (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hw hzB))
    · exact ⟨(normalizer (V : Set G)).one_mem, fun w _ => by
        rw [commutatorElement_one_left]
        exact (⁅V, A⁆ ⊔ ⁅V, B⁆).one_mem⟩
    · intro y z _ _ ihy ihz
      refine ⟨(normalizer (V : Set G)).mul_mem ihy.1 ihz.1, fun w hw => ?_⟩
      have hw' : z * w * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 ihz.1 w).1 hw
      have hid : ⁅y * z, w⁆ = ⁅y, z * w * z⁻¹⁆ * ⁅z, w⁆ := by
        simp only [commutatorElement_def]; group
      rw [hid]
      exact (⁅V, A⁆ ⊔ ⁅V, B⁆).mul_mem (ihy.2 _ hw') (ihz.2 w hw)
    · intro y _ ihy
      refine ⟨(normalizer (V : Set G)).inv_mem ihy.1, fun w hw => ?_⟩
      have hw' : y⁻¹ * w * y ∈ V := (Subgroup.mem_normalizer_iff''.1 ihy.1 w).1 hw
      have hid : ⁅y⁻¹, w⁆ = ⁅y, y⁻¹ * w * y⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [hid]
      exact (⁅V, A⁆ ⊔ ⁅V, B⁆).inv_mem (ihy.2 _ hw')
  exact (hmain x hx).2 v hv

theorem s16c4v1e3_card_comm_sup_le {V A B : Subgroup G}
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hA : A ≤ normalizer (V : Set G))
    (hB : B ≤ normalizer (V : Set G)) :
    Nat.card ↥(⁅V, A⁆ ⊔ ⁅V, B⁆) ≤ Nat.card ↥⁅V, A⁆ * Nat.card ↥⁅V, B⁆ := by
  have hUV : ⁅V, A⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    have ha' : a * v⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hA ha) v⁻¹).1 (V.inv_mem hv)
    show v * a * v⁻¹ * a⁻¹ ∈ V
    rw [show v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) by group]
    exact V.mul_mem hv ha'
  have hU'V : ⁅V, B⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    have hb' : b * v⁻¹ * b⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hB hb) v⁻¹).1 (V.inv_mem hv)
    show v * b * v⁻¹ * b⁻¹ ∈ V
    rw [show v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) by group]
    exact V.mul_mem hv hb'
  have hcomm : ⁅V, A⁆ ≤ Subgroup.centralizer ((⁅V, B⁆ : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hV u (hUV hu) w (hU'V hw)).symm
  have hnorm : ⁅V, A⁆ ≤ Subgroup.normalizer ((⁅V, B⁆ : Subgroup G) : Set G) :=
    hcomm.trans (Subgroup.centralizer_le_normalizer ((⁅V, B⁆ : Subgroup G) : Set G))
  have hset : ((⁅V, A⁆ ⊔ ⁅V, B⁆ : Subgroup G) : Set G) =
      ((⁅V, A⁆ : Subgroup G) : Set G) * ((⁅V, B⁆ : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (⁅V, A⁆) (⁅V, B⁆) hnorm
  let f : ↥⁅V, A⁆ × ↥⁅V, B⁆ → ↥(⁅V, A⁆ ⊔ ⁅V, B⁆) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), by
      show (p.1 : G) * (p.2 : G) ∈ ((⁅V, A⁆ ⊔ ⁅V, B⁆ : Subgroup G) : Set G)
      rw [hset]
      exact ⟨(p.1 : G), p.1.2, (p.2 : G), p.2.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (↑⁅V, A⁆ : Set G) * ↑⁅V, B⁆ := by
      rw [← hset]; exact x.2
    obtain ⟨u, hu, w, hw, huw⟩ := hx
    exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), Subtype.ext huw⟩
  calc Nat.card ↥(⁅V, A⁆ ⊔ ⁅V, B⁆)
      ≤ Nat.card (↥⁅V, A⁆ × ↥⁅V, B⁆) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card ↥⁅V, A⁆ * Nat.card ↥⁅V, B⁆ := Nat.card_prod _ _

theorem s16c4v1e3_comm_L_le (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {A : Subgroup G}
    (hAM : A ≤ D.M)
    (hgen : lBar (v1Sub D.M ⊥ V hV L) V hV L ≤ barSub (v1Sub D.M ⊥ V hV L) V hV A) :
    ⁅V, L⁆ ≤ ⁅V, A⁆ := by
  rw [Subgroup.commutator_le]
  intro v hv l₀ hl₀
  have hl₀M : l₀ ∈ D.M := S.sect.setting.hyp151.le hl₀
  have hl₀S : l₀ ∈ stabTil (v1Sub D.M ⊥ V hV L) V := s16c4v1_mem_stabTil S hl₀M
  let φ₀ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV) :=
    actTil (v1Sub D.M ⊥ V hV L) V hV ⟨l₀, hl₀S⟩
  have hφ₀ : φ₀ ∈ lBar (v1Sub D.M ⊥ V hV L) V hV L :=
    actTil_mem_barSub (v1Sub D.M ⊥ V hV L) V hV hl₀ hl₀S
  obtain ⟨a, haA, haeq⟩ :=
    (mem_barSub (v1Sub D.M ⊥ V hV L) V hV A φ₀).1 (hgen hφ₀)
  have haM : (a : G) ∈ D.M := hAM haA
  set c : G := (a : G)⁻¹ * l₀ with hc_def
  have hcM : c ∈ D.M := by
    rw [hc_def]
    exact D.M.mul_mem (D.M.inv_mem haM) hl₀M
  have hcS : c ∈ stabTil (v1Sub D.M ⊥ V hV L) V := by
    rw [hc_def]
    exact (stabTil _ _).mul_mem ((stabTil _ _).inv_mem a.2) hl₀S
  have hact : actTil (v1Sub D.M ⊥ V hV L) V hV ⟨c, hcS⟩ = 1 := by
    have heq : (⟨c, hcS⟩ : ↥(stabTil (v1Sub D.M ⊥ V hV L) V)) =
        a⁻¹ * ⟨l₀, hl₀S⟩ := Subtype.ext (by simp [hc_def])
    rw [heq, map_mul, map_inv, haeq]
    exact inv_mul_cancel φ₀
  have hc_cent : ∀ w ∈ V, c * w * c⁻¹ = w :=
    (s16c4v1_centralizes_iff S h1217 hcM).1
      ((actTil_eq_one_iff (v1Sub D.M ⊥ V hV L) V hV ⟨c, hcS⟩).1 hact)
  have hl₀_eq : l₀ = (a : G) * c := by
    rw [hc_def]; group
  have hcv' : c * v = v * c := by
    calc c * v = c * v * c⁻¹ * c := by group
      _ = v * c := by rw [hc_cent v hv]
  have hcv : ⁅v, c⁆ = 1 := by
    rw [commutatorElement_def, ← hcv']
    group
  have hcomm : ⁅v, l₀⁆ = ⁅v, (a : G)⁆ := by
    rw [hl₀_eq, commutatorElement_mul_right_eq_mul_conj, hcv, mul_one]
    group
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator hv haA

theorem s16c4v1e3_card_comm_conj {V : Subgroup G} (A : Subgroup G) {l : G}
    (hl : l ∈ normalizer (V : Set G)) :
    Nat.card ↥⁅V, A.map (MulAut.conj l).toMonoidHom⁆ = Nat.card ↥⁅V, A⁆ := by
  have hV : V.map (MulAut.conj l).toMonoidHom = V := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hl
  have hmap : ⁅V, A.map (MulAut.conj l).toMonoidHom⁆ =
      (⁅V, A⁆).map (MulAut.conj l).toMonoidHom := by
    rw [Subgroup.map_commutator (f := (MulAut.conj l).toMonoidHom), hV]
  rw [hmap, Subgroup.card_map_of_injective (MulAut.conj l).injective]

theorem s16c4v1e3_card_V_le (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {A : Subgroup G}
    (hAM : A ≤ D.M) {φ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)}
    (hφ : φ ∈ lBar (v1Sub D.M ⊥ V hV L) V hV L)
    (hgen : lBar (v1Sub D.M ⊥ V hV L) V hV L ≤
      barSub (v1Sub D.M ⊥ V hV L) V hV A ⊔
        (barSub (v1Sub D.M ⊥ V hV L) V hV A).map (MulAut.conj φ).toMonoidHom) :
    Nat.card V ≤ Nat.card ↥⁅V, A⁆ * Nat.card ↥⁅V, A⁆ := by
  obtain ⟨l, hlL, rfl⟩ := (mem_barSub _ _ _ L φ).1 hφ
  have hlM : (l : G) ∈ D.M := S.sect.setting.hyp151.le hlL
  have hN : D.M ≤ normalizer (V : Set G) := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hA'M : A.map (MulAut.conj (l : G)).toMonoidHom ≤ D.M := by
    rintro _ ⟨a, ha, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hlM (hAM ha)) (D.M.inv_mem hlM)
  have hbar := TwelveTwentyThree.barSub_map_conj hV
    (fun a ha => s16c4v1_mem_stabTil S (hAM ha)) l.2
  have hgen' : lBar (v1Sub D.M ⊥ V hV L) V hV L ≤ barSub (v1Sub D.M ⊥ V hV L) V hV
      (A ⊔ A.map (MulAut.conj (l : G)).toMonoidHom) :=
    hgen.trans (sup_le (barSub_mono _ _ _ le_sup_left)
      (hbar.symm.le.trans (barSub_mono _ _ _ le_sup_right)))
  have h1 : V ≤ ⁅V, A⁆ ⊔ ⁅V, A.map (MulAut.conj (l : G)).toMonoidHom⁆ :=
    (s16c4v1_comm_eq S).symm.le.trans ((s16c4v1e3_comm_L_le S h1217 (sup_le hAM hA'M) hgen').trans
      (s16c4v1e3_comm_sup_le (hAM.trans hN) (hA'M.trans hN)))
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    have := hV.1
    exact fun a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V) ⟨b, hb⟩)
  calc Nat.card V ≤ Nat.card ↥(⁅V, A⁆ ⊔ ⁅V, A.map (MulAut.conj (l : G)).toMonoidHom⁆) :=
        Subgroup.card_le_of_le h1
    _ ≤ Nat.card ↥⁅V, A⁆ * Nat.card ↥⁅V, A.map (MulAut.conj (l : G)).toMonoidHom⁆ :=
        s16c4v1e3_card_comm_sup_le hcomm (hAM.trans hN) (hA'M.trans hN)
    _ = Nat.card ↥⁅V, A⁆ * Nat.card ↥⁅V, A⁆ := by
        rw [s16c4v1e3_card_comm_conj A (hN hlM)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
