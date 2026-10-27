module

public import CFSG.Quasithin.Vol2.Ch10SecD211A
public import CFSG.Quasithin.Vol2.Ch10SecBSetup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}



theorem charTwo_of_le (hq : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    {H : Subgroup G} (hTH : T ≤ H) (hH : pCoreOf 2 H ≠ ⊥) : CharTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := charTwo_of_inH hq.2.1 (hT.1.toSylow hT.2)
    (H := H) (by rw [IsPGroup.toSylow_coe]; exact ⟨hTH, hH⟩)
  exact h

omit [Finite G] in
theorem le_centralizer_conjClosure {N E H : Subgroup G}
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hNE : N ≤ Subgroup.centralizer (E : Set G)) :
    N ≤ Subgroup.centralizer (conjClosure E H : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun g hg e he => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hn' : g⁻¹ * n * g⁻¹⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hN hg)) n).mp hn
  have h1 := (Subgroup.mem_centralizer_iff.mp (hNE hn')) e he
  simp only [inv_inv] at h1
  calc n * (g * e * g⁻¹) = g * ((g⁻¹ * n * g) * e) * g⁻¹ := by group
    _ = g * (e * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
    _ = g * e * g⁻¹ * n := by group

theorem closure_le_centralizer_z (h : Hyp10 G T L I) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) :
    Subgroup.closure {v₁, v₂} ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) := by
  obtain ⟨ht, -, hv1, -, hv2, -⟩ := hd
  have hV1 : v₁ ∈ fsuVM T L I := V1_le_V hv1.1
  have hV2 : v₂ ∈ fsuVM T L I :=
    commutator_le_left_of_le_normalizer ((SecA.conjugate_le_fsuL0 ht).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv2.1
  obtain ⟨hcomm, -⟩ := h.three
  have hab : ∀ a ∈ fsuVM T L I, ∀ b ∈ fsuVM T L I, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [Subgroup.closure_le]
  rintro w (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · calc w * (w * v₂) = w * (v₂ * w) := by rw [hab w hV1 v₂ hV2]
      _ = w * v₂ * w := by group
  · calc w * (v₁ * w) = w * v₁ * w := by group
      _ = v₁ * w * w := by rw [hab w hV2 v₁ hV1]

theorem stmt10_2_11_one (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1029 : Stmt10_2_9) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    Vz v₁ v₂ ≤ centerOf (pCoreOf 2 (Subgroup.centralizer ({v₁ * v₂} : Set G))) ∧
      Subgroup.centralizer ({v₁ * v₂} : Set G) ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) ≤
        fsuM T L ⊓ Subgroup.normalizer (Vi T L I L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gz := Subgroup.centralizer ({v₁ * v₂} : Set G) with hGz
  have hTz : T ≤ Gz := T_le_centralizer_z h37 h38 h h3 hc hd
  have hz1 := z_ne_one h37 h38 h hc hd
  have hEz := closure_le_centralizer_z h hd
  have hzV : v₁ * v₂ ∈ fsuVM T L I := by
    have h1 : v₁ * v₂ ∈ Subgroup.closure {v₁, v₂} :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    obtain ⟨ht, -, hv1, -, hv2, -⟩ := hd
    exact (fsuVM T L I).mul_mem (V1_le_V hv1.1) (commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv2.1)
  have hzp : IsPGroup 2 (Subgroup.zpowers (v₁ * v₂)) :=
    (SecA.isPGroup_fsuVM h).to_le (Subgroup.zpowers_le.mpr hzV)
  have hO2ne : pCoreOf 2 Gz ≠ ⊥ := fun h0 => hz1 (by
    have := SecB.mem_pCoreOf_centralizer hzp
    rwa [← hGz, h0, Subgroup.mem_bot] at this)
  have hchar := charTwo_of_le h.fsu.qtke h.fsu.sylow hTz hO2ne
  have hXz : Xz T L (v₁ * v₂) ≤ Gz := (oTwoUpper_le _).trans inf_le_right
  have hO2 : pCoreOf 2 Gz ≤ T1 T L :=
    (pCoreOf_le_pCoreOf_of_sylow (sup_le hXz hTz) h.fsu.sylow.1 le_sup_right
      (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz).2.2).trans
      (pCoreOf_XzT_le_T1 h37 h38 h h3 hc hd)
  obtain ⟨-, -, hv1, hv11, hv2, -⟩ := hd
  have hT1E : T1 T L ≤ Subgroup.centralizer ((Subgroup.closure {v₁, v₂} : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro w (rfl | rfl)
    · exact ((Subgroup.mem_centralizer_iff.mp hv1.2) s hs).symm
    · exact ((Subgroup.mem_centralizer_iff.mp hv2.2) s hs).symm
  have hO2C : pCoreOf 2 Gz ≤ Subgroup.centralizer (Vz v₁ v₂ : Set G) :=
    le_centralizer_conjClosure (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Gz)
      (hO2.trans hT1E)
  have hVzGz : Vz v₁ v₂ ≤ Gz := conjClosure_le fun g hg e he =>
    Gz.mul_mem (Gz.mul_mem hg (hEz he)) (Gz.inv_mem hg)
  have hVzO2 : Vz v₁ v₂ ≤ pCoreOf 2 Gz :=
    fun x hx => hchar ⟨hVzGz hx, Subgroup.le_centralizer_iff.mp hO2C hx⟩
  refine ⟨fun x hx => ⟨hVzO2 hx, Subgroup.le_centralizer_iff.mp hO2C hx⟩, ?_⟩
  have hv1C : v₁ ∉ Subgroup.centralizer (fsuL0 T L : Set G) := by
    intro h1
    have : v₁ ∈ fsuCVM T L I := ⟨V1_le_V hv1.1, h1⟩
    rw [hc, Subgroup.mem_bot] at this
    exact hv11 this
  have h1 := (h1029 G T L I h L (Or.inl rfl)).2.2 v₁ hv1.1 hv1C
  have hv1Vz : v₁ ∈ Vz v₁ v₂ := le_conjClosure _ _ (Subgroup.subset_closure (by simp))
  refine le_trans ?_ h1
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.mp hx.2) v₁ hv1Vz).symm

end CFSG.Quasithin.Vol2.Ch10.SecD
