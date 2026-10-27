module

public import CFSG.Quasithin.H13.U4ParCore
public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutCenter
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem sl2_center_trivial (hf : 2 ≤ f) (g : SpecialLinearGroup (Fin 2) h.fixedField)
    (hg : ∀ x, g * x = x * g) : g = 1 := by
  have := CFSG.Quasithin.H13.U4Par.isSimpleGroup_sl2 h hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (SpecialLinearGroup (Fin 2) h.fixedField)) with e | e
  · have : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) h.fixedField) :=
      Subgroup.mem_center_iff.2 fun x => (hg x).symm
    rw [e, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have hc : upperSL2 (1 : h.fixedField) * lowerSL2 1 = lowerSL2 1 * upperSL2 1 :=
      Subgroup.mem_center_iff.1 (e ▸ Subgroup.mem_top (upperSL2 (1 : h.fixedField))) _ |>.symm
    have := congrArg (fun m : SpecialLinearGroup (Fin 2) h.fixedField =>
      (m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0) hc
    simp [coe_upperSL2, coe_lowerSL2, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem A2X_inf_N2X (hf : 2 ≤ f) {x : Xg h} (ha : x ∈ A2X h) (hn : x ∈ N2X h) : x = 1 := by
  have h1 : (x : GL (Fin 4) K) ∈ miyamotoA2 h ⊓ (miyamotoI2 h ⊔ miyamotoN2 h) :=
    ⟨ha, Subgroup.mem_sup_right hn⟩
  rw [miyamotoA2_inf_levi h hf, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem N2X_center_trivial (hf : 2 ≤ f) {n : Xg h} (hn : n ∈ N2X h)
    (hc : ∀ m ∈ N2X h, m * n = n * m) : n = 1 := by
  obtain ⟨g, hg⟩ := (miyamotoN2Equiv h).surjective ⟨(n : GL (Fin 4) K), hn⟩
  have hgn : ((miyamotoN2Equiv h g : miyamotoN2 h) : GL (Fin 4) K) = n := by rw [hg]
  have hg1 : g = 1 := by
    apply sl2_center_trivial h hf
    intro x
    have hx : ((miyamotoN2Equiv h x : miyamotoN2 h) : GL (Fin 4) K) ∈ gramSU h (miyamotoJ4 K) :=
      miyamotoN2_le_gramSU h (miyamotoN2Equiv h x).2
    have e := hc ⟨_, hx⟩ (show (⟨_, hx⟩ : Xg h) ∈ N2X h from (miyamotoN2Equiv h x).2)
    have e' : ((miyamotoN2Equiv h x : miyamotoN2 h) : GL (Fin 4) K) * n =
        n * ((miyamotoN2Equiv h x : miyamotoN2 h) : GL (Fin 4) K) := congrArg Subtype.val e
    rw [← hgn] at e'
    apply (miyamotoN2Equiv h).injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact e'.symm
  rw [hg1, map_one] at hg
  exact Subtype.ext (by rw [← congrArg Subtype.val hg]; rfl)

theorem N2X_le_Pt : N2X h ≤ Pt h := by
  rw [Pt_eq]
  exact le_sup_right.trans le_sup_right

theorem I2X_le_Pt : I2X h ≤ Pt h := by
  rw [Pt_eq]
  exact le_sup_left.trans le_sup_right

theorem exists_mul_of_sup {G : Type*} [Group G] {A N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ N) :
    ∃ a ∈ A, ∃ n ∈ N, x = a * n := by
  have hH : A ⊔ N ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hN
  have hAH : A ≤ A ⊔ N := le_sup_left
  have hNH : N ≤ A ⊔ N := le_sup_right
  have : (A.subgroupOf (A ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).2 hH
  have htop : A.subgroupOf (A ⊔ N) ⊔ N.subgroupOf (A ⊔ N) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAH hNH, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hx⟩ : ↥(A ⊔ N)) ∈ (↑(A.subgroupOf (A ⊔ N) ⊔ N.subgroupOf (A ⊔ N)) :
      Set ↥(A ⊔ N)) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.normal_mul] at hx'
  obtain ⟨a, ha, n, hn, e⟩ := hx'
  exact ⟨a, ha, n, hn, (congrArg Subtype.val e).symm⟩

theorem centerOf_A2X_sup_N2X (hf : 2 ≤ f) : centerOf (A2X h ⊔ N2X h) = ZX h := by
  apply le_antisymm
  · rintro x ⟨hxH, hxc⟩
    have hN : N2X h ≤ Subgroup.normalizer (A2X h : Set (Xg h)) := N2X_le_Pt h
    obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_of_sup hN hxH
    have hcomm : ∀ y ∈ A2X h ⊔ N2X h, y * (a * n) = (a * n) * y :=
      fun y hy => Subgroup.mem_centralizer_iff.1 hxc y hy
    have hn1 : n = 1 := by
      apply N2X_center_trivial h hf hn
      intro m hm
      have e := hcomm m (Subgroup.mem_sup_right hm)
      have hu : n * m * n⁻¹ * m⁻¹ ∈ A2X h := by
        have h1 : m * a * m⁻¹ ∈ A2X h := (Subgroup.mem_normalizer_iff.1 (hN hm) a).1 ha
        have e2 : n * m * n⁻¹ * m⁻¹ = a⁻¹ * (m * a * m⁻¹) := by
          have : n * m = a⁻¹ * (m * (a * n)) := by
            rw [e]
            group
          calc n * m * n⁻¹ * m⁻¹ = (n * m) * n⁻¹ * m⁻¹ := rfl
            _ = a⁻¹ * (m * (a * n)) * n⁻¹ * m⁻¹ := by rw [this]
            _ = a⁻¹ * (m * a * m⁻¹) := by group
        rw [e2]
        exact (A2X h).mul_mem ((A2X h).inv_mem ha) h1
      have hu1 : n * m * n⁻¹ * m⁻¹ = 1 :=
        A2X_inf_N2X h hf hu ((N2X h).mul_mem ((N2X h).mul_mem ((N2X h).mul_mem hn hm)
          ((N2X h).inv_mem hn)) ((N2X h).inv_mem hm))
      calc m * n = (n * m * n⁻¹ * m⁻¹)⁻¹ * (n * m) := by group
        _ = n * m := by rw [hu1]; group
    subst hn1
    rw [mul_one] at hxH hxc ⊢
    have hZ : (a : GL (Fin 4) K) ∈ miyamotoZ h := by
      rw [← centerIn_miyamotoA2]
      refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have hyX : y ∈ gramSU h (miyamotoJ4 K) := miyamotoUnipotent_le_SU h false true hy
      have e := hcomm ⟨y, hyX⟩ (Subgroup.mem_sup_left hy)
      rw [mul_one] at e
      exact congrArg Subtype.val e
    exact hZ
  · intro z hz
    have hzA : z ∈ A2X h := miyamotoZ2_le_A2 h (miyamotoZ_le_Z2 h hz)
    refine ⟨Subgroup.mem_sup_left hzA, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hC : A2X h ⊔ N2X h ≤ Subgroup.centralizer ({z} : Set (Xg h)) := by
      refine sup_le (fun a ha => ?_) (fun n hn => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (miyamotoA2_commute_Z h ha hz)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (miyamotoN2_commute_Z h hn hz)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hC hy)

end CFSG.Quasithin.H13.F431.Un.OL
