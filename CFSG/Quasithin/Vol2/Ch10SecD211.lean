module

public import CFSG.Quasithin.Vol2.Ch10SecD211F
public import CFSG.Quasithin.Vol2.Ch10SecD211E
public import CFSG.Quasithin.Vol2.Ch10SecDFacts211b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem concl10_2_4_of_eq {T H K K' : Subgroup G} (hKK : K = K')
    (h : Concl10_2_4TwoThree T K H) : Concl10_2_4TwoThree T K' H :=
  hKK ▸ h

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' {V : Subgroup G} :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_centralizer hg hc, fun hc => ?_⟩
  have := conj_mem_centralizer ((Subgroup.normalizer _).inv_mem hg) hc
  simpa [mul_assoc] using this

theorem stmt10_2_11_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1013 : Stmt10_1_3) (h1024 : Stmt10_2_4) (h1029 : Stmt10_2_9) (hXI : FactXIrred)
    (hX3 : FactXThree) (hVE : FactVEIrred) (hVXE : FactVXE) (hMax : FactMaxP)
    (hTL : FactTransvList) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    fsuVM T L I ≤ pCoreOf 2 (Subgroup.centralizer ({v₁ * v₂} : Set G)) := by
  by_contra hVO
  have hz1 := z_ne_one h37 h38 h hc hd
  have hTz := T_le_centralizer_z h37 h38 h h3 hc hd
  obtain ⟨ht, -, hv1, -, hv2, -⟩ := id hd
  have hV1 : v₁ ∈ fsuVM T L I := V1_le_V hv1.1
  have hV2 : v₂ ∈ fsuVM T L I :=
    commutator_le_left_of_le_normalizer ((SecA.conjugate_le_fsuL0 ht).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv2.1
  have hzV : v₁ * v₂ ∈ fsuVM T L I := (fsuVM T L I).mul_mem hV1 hV2
  obtain ⟨hcomm, -⟩ := h.three
  have hVGz : fsuVM T L I ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨_, hzV⟩)
  have h1 := stmt10_2_11_one h37 h38 h1029 h h3 hc hd
  have hGzVz : Subgroup.centralizer ({v₁ * v₂} : Set G) ≤
      Subgroup.normalizer (Vz v₁ v₂ : Set G) := le_normalizer_conjClosure _ _
  have hGzC : Subgroup.centralizer ({v₁ * v₂} : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Vz v₁ v₂ : Set G) : Subgroup G) : Set G) :=
    hGzVz.trans normalizer_le_normalizer_centralizer'
  have hVC : ¬ fsuVM T L I ≤ Subgroup.centralizer (Vz v₁ v₂ : Set G) := by
    intro hVC
    apply hVO
    have hCM : Subgroup.centralizer ({v₁ * v₂} : Set G) ⊓
        Subgroup.centralizer (Vz v₁ v₂ : Set G) ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      h1.2.trans (inf_le_left.trans (SecA.fsuM_le_normalizer_fsuVM T L I))
    have hVO1 := le_pCoreOf_of_normalizes (le_inf hVGz hVC) hCM (SecA.isPGroup_fsuVM h)
    refine hVO1.trans (le_pCoreOf_of_normalizes ((Subgroup.map_subtype_le _).trans inf_le_left)
      ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
    have hN : Subgroup.centralizer ({v₁ * v₂} : Set G) ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({v₁ * v₂} : Set G) ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) :
          Subgroup G) : Set G) := fun g hg =>
      mem_normalizer_inf (Subgroup.le_normalizer hg) (hGzC hg)
    exact hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hEV : Subgroup.closure {v₁, v₂} ≤ fsuVM T L I := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hV1
    · exact hV2
  have hab := h1.1
  have hEVz : Subgroup.closure {v₁, v₂} ≤ Vz v₁ v₂ := le_conjClosure _ _
  have hEC : Subgroup.closure {v₁, v₂} ≤ Subgroup.centralizer (Vz v₁ v₂ : Set G) :=
    fun e he => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hab (hEVz he)).2) w (hab hw).1
  have hXGz : Xz T L (v₁ * v₂) ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hXN : Xz T L (v₁ * v₂) ≤ Subgroup.normalizer
      ((fsuVM T L I ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (SecA.fsuL0_le_normalizer_fsuVM T L I
      ((oTwoUpper_le _).trans inf_le_left hx)) (hGzC (hXGz hx))
  have hTN : T ≤ Subgroup.normalizer
      ((fsuVM T L I ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (SecA.le_normalizer_fsuVM T L I hx) (hGzC (hTz hx))
  have hE : fsuVM T L I ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) =
      Subgroup.closure {v₁, v₂} := by
    rcases hVE G T L I h h3 hc t v₁ v₂ hd _ (le_inf hEV hEC) inf_le_left hXN hTN with h' | h'
    · exact h'
    · exact absurd (le_of_eq h'.symm |>.trans inf_le_right) hVC
  have hlt : Xz T L (v₁ * v₂) < Kz T L (v₁ * v₂) := by
    refine lt_of_le_of_ne (le_conjClosure _ _) fun heq => hVC ?_
    have hGzX : Subgroup.centralizer ({v₁ * v₂} : Set G) ≤
        Subgroup.normalizer (Xz T L (v₁ * v₂) : Set G) := by
      rw [heq]
      exact le_normalizer_conjClosure _ _
    have hXE := (oTwoUpper_le _).trans (fsuL0_inf_centralizer_z_le h37 h38 h hc hd)
    have hXVz : Xz T L (v₁ * v₂) ≤ Subgroup.centralizer (Vz v₁ v₂ : Set G) :=
      le_centralizer_conjClosure hGzX hXE
    rw [hVXE G T L I h h3 hc t v₁ v₂ hd]
    refine sup_le ?_ hEC
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXVz, Subgroup.commutator_bot_left]
    · have hle : ⁅Vz v₁ v₂, fsuVM T L I⁆ ≤ Vz v₁ v₂ :=
        commutator_le_left_of_le_normalizer (hVGz.trans hGzVz)
      rw [eq_bot_iff]
      refine (Subgroup.commutator_mono hle le_rfl).trans ?_
      rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.mp hXVz
  have hR2 := (stmt10_2_11_two h37 h38 h1013 h1029 hXI hX3 h h3 hc hd hlt).2
  have hPX := oTwoUpper_P_eq (T := T) (L := L) h.fsu.sylow.1 (z := v₁ * v₂)
  have hKP : KOf ((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G))
      (Subgroup.centralizer ({v₁ * v₂} : Set G)) = Kz T L (v₁ * v₂) := by
    rw [KOf, hPX]
  have hH : InH (oTwoUpper ((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G)) ⊔ T)
      (Subgroup.centralizer ({v₁ * v₂} : Set G)) :=
    ⟨sup_le (hPX ▸ hXGz) hTz, pCoreOf_Gz_ne_bot h37 h38 h hc hd⟩
  have h4 := h1024 G T L I h h3.1 (not_case10_1_1Five h3 hc) _
    (hMax G T L I h h3 hc t v₁ v₂ hd) (le_inf le_sup_right hTz) _ hH
  have h4' : Concl10_2_4TwoThree T (Kz T L (v₁ * v₂))
      (Subgroup.centralizer ({v₁ * v₂} : Set G)) := by
    rcases h4 with h4 | h4 | h4
    · exact absurd (hKP.symm.trans (h4.trans hPX)) hlt.ne'
    · exact concl10_2_4_of_eq hKP (Or.inl h4)
    · exact concl10_2_4_of_eq hKP (Or.inr h4)
  obtain ⟨hz, hbot⟩ := hTL G T L I h h3 hc t v₁ v₂ hd hlt hR2 hE h4'
  have hKzGz : Kz T L (v₁ * v₂) ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) :=
    conjClosure_le fun g hg x hx => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hXGz hx))
      (Subgroup.inv_mem _ hg)
  have hzC : v₁ * v₂ ∈ Subgroup.centralizer (Kz T L (v₁ * v₂) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hKzGz hk))
  have hmem : v₁ * v₂ ∈ ⁅Vz v₁ v₂, Kz T L (v₁ * v₂)⁆ ⊓
      Subgroup.centralizer (Kz T L (v₁ * v₂) : Set G) := ⟨hz, hzC⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

theorem stmt10_2_11_of (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1013 : Stmt10_1_3) (h1024 : Stmt10_2_4) (h1029 : Stmt10_2_9) (hXI : FactXIrred)
    (hX3 : FactXThree) (hVE : FactVEIrred) (hVXE : FactVXE) (hMax : FactMaxP)
    (hTL : FactTransvList) : Stmt10_2_11 := by
  intro G _ _ T L I h h3 hc t v₁ v₂ hd
  exact ⟨stmt10_2_11_one h37 h38 h1029 h h3 hc hd,
    stmt10_2_11_two h37 h38 h1013 h1029 hXI hX3 h h3 hc hd,
    stmt10_2_11_three h37 h38 h1013 h1024 h1029 hXI hX3 hVE hVXE hMax hTL h h3 hc hd⟩

end CFSG.Quasithin.Vol2.Ch10.SecD
