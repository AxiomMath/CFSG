module

public import CFSG.Quasithin.Vol2.Ch10SecBCoordMain
public import CFSG.Quasithin.Vol2.Ch10SecBPre
public import CFSG.Quasithin.Vol2.Ch10SecBL32Prod

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}

theorem T0_eq_preIn (hT : quasithinIsSylowTwo T) (hC : L0Coord T L t Ψ c) :
    T0 T L = preIn Ψ (L32.U3.prod L32.U3) := by
  rw [← hC.T0]
  exact (preIn_imgIn inf_le_right fun x hx =>
    SecA.pCoreOf_fsuL0_le_T0 hT ((hC.ker x).mp hx)).symm

theorem conj_mem_preIn (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hC : L0Coord T L t Ψ c) {A : Subgroup L32.Γ} (hUA : L32.U3 ≤ A) {s y : G} (hs : s ∈ T)
    (hy : y ∈ preIn Ψ (A.prod A)) : s * y * s⁻¹ ∈ preIn Ψ (A.prod A) := by
  have hT1 : ∀ s' ∈ T1 T L, ∀ y ∈ preIn Ψ (A.prod A), s' * y * s'⁻¹ ∈ preIn Ψ (A.prod A) := by
    intro s' hs' y hy
    obtain ⟨hyL0, hyA⟩ := mem_preIn.mp hy
    obtain ⟨u, v, hu, hv, huv⟩ := hC.T1act s' hs'
    have hm : s' * y * s'⁻¹ ∈ fsuL0 T L :=
      (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L hs'.1) y).mp hyL0
    refine mem_preIn.mpr ⟨hm, ?_⟩
    rw [huv ⟨y, hyL0⟩ hm]
    exact ⟨A.mul_mem (A.mul_mem (hUA hu) hyA.1) (A.inv_mem (hUA hu)),
      A.mul_mem (A.mul_mem (hUA hv) hyA.2) (A.inv_mem (hUA hv))⟩
  have hsw : ∀ y ∈ preIn Ψ (A.prod A), t⁻¹ * y * t ∈ preIn Ψ (A.prod A) := by
    intro y hy
    obtain ⟨hyL0, hyA⟩ := mem_preIn.mp hy
    have hm : t⁻¹ * y * t ∈ fsuL0 T L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (SecA.le_fsuM T L ht)) y).mp
        hyL0
      simpa using this
    refine mem_preIn.mpr ⟨hm, ?_⟩
    rw [hC.swap ⟨y, hyL0⟩ hm]
    exact ⟨A.mul_mem (A.mul_mem (hUA hC.hc) hyA.2) (A.inv_mem (hUA hC.hc)), hyA.1⟩
  have ht2 : t * t ∈ T1 T L := ⟨T.mul_mem ht ht, SecA.mul_self_mem_normalizer h37 h38 hyp ht htn⟩
  have ht' : ∀ y ∈ preIn Ψ (A.prod A), t * y * t⁻¹ ∈ preIn Ψ (A.prod A) := by
    intro y hy
    have := hT1 _ ht2 _ (hsw y hy)
    convert this using 1
    group
  by_cases hsN : s ∈ Subgroup.normalizer (L : Set G)
  · exact hT1 s ⟨hs, hsN⟩ y hy
  · have h1 : s * t⁻¹ ∈ T1 T L :=
      ⟨T.mul_mem hs (T.inv_mem ht), SecA.mul_inv_mem_normalizer h37 h38 hyp ht htn hs hsN⟩
    have := hT1 _ h1 _ (ht' y hy)
    convert this using 1
    group

theorem classify_preIn (hT : quasithinIsSylowTwo T) (hC : L0Coord T L t Ψ c)
    {Y : Subgroup G} (hT0Y : T0 T L ≤ Y) (hYL0 : Y ≤ fsuL0 T L)
    (htY : ∀ y ∈ Y, t⁻¹ * y * t ∈ Y) :
    ∃ A : Subgroup L32.Γ, (A = L32.U3 ∨ A = L32.Pa ∨ A = L32.Pb ∨ A = ⊤) ∧
      Y = preIn Ψ (A.prod A) := by
  have hUB : L32.U3.prod L32.U3 ≤ imgIn Ψ Y := by
    rw [← hC.T0]
    exact imgIn_mono Ψ hT0Y
  have hσ : ∀ p ∈ imgIn Ψ Y, (c * p.2 * c⁻¹, p.1) ∈ imgIn Ψ Y := by
    intro p hp
    obtain ⟨y, hyL0, hyY, rfl⟩ := mem_imgIn.mp hp
    have hm : t⁻¹ * y * t ∈ fsuL0 T L := hYL0 (htY y hyY)
    exact mem_imgIn.mpr ⟨_, hm, htY y hyY, hC.swap ⟨y, hyL0⟩ hm⟩
  obtain ⟨A, hA, hB⟩ := L32.prod_classify hC.hc hUB hσ
  refine ⟨A, hA, ?_⟩
  rw [← hB]
  exact (preIn_imgIn hYL0 fun x hx => hT0Y (SecA.pCoreOf_fsuL0_le_T0 hT ((hC.ker x).mp hx))).symm

theorem le_normalizer_preIn (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hC : L0Coord T L t Ψ c) {A : Subgroup L32.Γ} (hUA : L32.U3 ≤ A) :
    T ≤ Subgroup.normalizer (preIn Ψ (A.prod A) : Set G) := fun s hs =>
  Subgroup.mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => conj_mem_preIn h37 h38 hyp ht htn hC hUA hs hy, fun hy => by
      have := conj_mem_preIn h37 h38 hyp ht htn hC hUA (T.inv_mem hs) hy
      simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem eq_inf_sup {P : Subgroup G} (hP : P ≤ fsuL0 T L ⊔ T) (hTP : T ≤ P) :
    P = (P ⊓ fsuL0 T L) ⊔ T := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hTP)
  have hx' : x ∈ ((fsuL0 T L ⊔ T : Subgroup G) : Set G) := hP hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (SecA.le_fsuM T L)] at hx'
  obtain ⟨l, hl, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  have hlP : l ∈ P := by simpa using P.mul_mem hx (P.inv_mem (hTP hs))
  exact Subgroup.mul_mem_sup ⟨hlP, hl⟩ hs

theorem inf_preIn_sup (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hC : L0Coord T L t Ψ c) {A : Subgroup L32.Γ} (hUA : L32.U3 ≤ A) :
    (preIn Ψ (A.prod A) ⊔ T) ⊓ fsuL0 T L = preIn Ψ (A.prod A) := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left (preIn_le Ψ _))
  have hx1 : x ∈ ((preIn Ψ (A.prod A) ⊔ T : Subgroup G) : Set G) := hx.1
  have hx2 : x ∈ fsuL0 T L := hx.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_preIn h37 h38 hyp ht htn hC hUA)] at hx1
  obtain ⟨y, hy, s, hs, rfl⟩ := Set.mem_mul.mp hx1
  have hsL0 : s ∈ fsuL0 T L := by
    have := (fsuL0 T L).mul_mem ((fsuL0 T L).inv_mem (preIn_le Ψ _ hy)) hx2
    simpa using this
  have hsT0 : s ∈ T0 T L := ⟨hs, hsL0⟩
  rw [T0_eq_preIn hyp.fsu.sylow hC] at hsT0
  exact (preIn Ψ (A.prod A)).mul_mem hy (preIn_mono Ψ (Subgroup.prod_mono hUA hUA) hsT0)

omit [Finite G] in
theorem le_of_preIn_le (hC : L0Coord T L t Ψ c) {A B : Subgroup L32.Γ}
    (h : preIn Ψ (A.prod A) ≤ preIn Ψ (B.prod B)) : A ≤ B := by
  intro g hg
  have h1 := imgIn_mono Ψ h
  rw [imgIn_preIn hC.surj, imgIn_preIn hC.surj] at h1
  exact (h1 (show (g, g) ∈ A.prod A from ⟨hg, hg⟩)).1

omit [Finite G] in
theorem preIn_top : preIn Ψ ((⊤ : Subgroup L32.Γ).prod ⊤) = fsuL0 T L :=
  le_antisymm (preIn_le Ψ _) fun _ hx =>
    mem_preIn.mpr ⟨hx, Subgroup.mem_top _, Subgroup.mem_top _⟩

theorem lt_preIn_sup (hT : quasithinIsSylowTwo T) (hC : L0Coord T L t Ψ c)
    {A : Subgroup L32.Γ} (hA : ¬ A ≤ L32.U3) : T < preIn Ψ (A.prod A) ⊔ T := by
  refine lt_of_le_of_ne le_sup_right fun h => hA (le_of_preIn_le hC ?_)
  rw [← T0_eq_preIn hT hC]
  exact le_inf (le_sup_left.trans h.symm.le) (preIn_le Ψ _)

theorem preIn_sup_lt (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hC : L0Coord T L t Ψ c) {A : Subgroup L32.Γ} (hUA : L32.U3 ≤ A) (hA : A ≠ ⊤) :
    preIn Ψ (A.prod A) ⊔ T < fsuL0 T L ⊔ T := by
  refine lt_of_le_of_ne (sup_le_sup_right (preIn_le Ψ _) _) fun h => hA (top_le_iff.mp ?_)
  refine le_of_preIn_le hC ?_
  rw [preIn_top, ← inf_preIn_sup h37 h38 hyp ht htn hC hUA, h]
  exact le_inf le_sup_left le_rfl

theorem pa_not_le_u3 : ¬ L32.Pa ≤ L32.U3 := fun h => L32.s_mem.2.1 (h L32.s_mem.1)

theorem pb_not_le_u3 : ¬ L32.Pb ≤ L32.U3 := fun h => L32.s_mem.2.2.2.1 (h L32.s_mem.2.2.1)

theorem pa_not_le_pb : ¬ L32.Pa ≤ L32.Pb := fun h => L32.s_mem.2.2.2.2.1 (h L32.s_mem.1)

theorem pb_not_le_pa : ¬ L32.Pb ≤ L32.Pa := fun h => L32.s_mem.2.2.2.2.2 (h L32.s_mem.2.2.1)

theorem pa_ne_top : L32.Pa ≠ ⊤ := fun h => pb_not_le_pa (h ▸ le_top)

theorem pb_ne_top : L32.Pb ≠ ⊤ := fun h => pa_not_le_pb (h ▸ le_top)

omit [Finite G] in
theorem inf_fsuL0_props {P : Subgroup G} (hTP : T ≤ P) (ht : t ∈ T) :
    T0 T L ≤ P ⊓ fsuL0 T L ∧ ∀ y ∈ P ⊓ fsuL0 T L, t⁻¹ * y * t ∈ P ⊓ fsuL0 T L := by
  refine ⟨le_inf (inf_le_left.trans hTP) inf_le_right, fun y hy => ⟨?_, ?_⟩⟩
  · exact P.mul_mem (P.mul_mem (P.inv_mem (hTP ht)) hy.1) (hTP ht)
  · have := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (SecA.le_fsuM T L ht)) y).mp hy.2
    simpa using this

theorem maximal_classify (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hC : L0Coord T L t Ψ c) {P : Subgroup G} (hP : IsMaxSubgroupIn (fsuL0 T L ⊔ T) P)
    (hTP : T ≤ P) :
    P = preIn Ψ (L32.Pa.prod L32.Pa) ⊔ T ∨ P = preIn Ψ (L32.Pb.prod L32.Pb) ⊔ T := by
  have hT : quasithinIsSylowTwo T := hyp.fsu.sylow
  have hPle : P ≤ fsuL0 T L ⊔ T := hP.1.le
  obtain ⟨hT0, htY⟩ := inf_fsuL0_props (L := L) hTP ht
  obtain ⟨A, hA, hY⟩ := classify_preIn hT hC hT0 inf_le_right htY
  have hPeq : P = preIn Ψ (A.prod A) ⊔ T := by rw [← hY]; exact eq_inf_sup hPle hTP
  rcases hA with rfl | rfl | rfl | rfl
  · exfalso
    have hPT : P = T := by
      rw [hPeq, ← T0_eq_preIn hT hC]
      exact sup_eq_right.mpr inf_le_left
    have hlt : P < preIn Ψ (L32.Pa.prod L32.Pa) ⊔ T := by
      rw [hPT]; exact lt_preIn_sup hT hC pa_not_le_u3
    have := hP.2 _ hlt (sup_le_sup_right (preIn_le Ψ _) _)
    exact (preIn_sup_lt h37 h38 hyp ht htn hC L32.u3_le_pa pa_ne_top).ne this
  · exact Or.inl hPeq
  · exact Or.inr hPeq
  · exfalso
    refine hP.1.ne (le_antisymm hPle (sup_le ?_ hTP))
    rw [hPeq, preIn_top]
    exact le_sup_left

theorem isMax_preIn_sup (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hC : L0Coord T L t Ψ c) {A : Subgroup L32.Γ} (hA : A = L32.Pa ∨ A = L32.Pb) :
    IsMaxSubgroupIn (fsuL0 T L ⊔ T) (preIn Ψ (A.prod A) ⊔ T) := by
  have hT : quasithinIsSylowTwo T := hyp.fsu.sylow
  have hUA : L32.U3 ≤ A := by rcases hA with rfl | rfl; exacts [L32.u3_le_pa, L32.u3_le_pb]
  have hAtop : A ≠ ⊤ := by rcases hA with rfl | rfl; exacts [pa_ne_top, pb_ne_top]
  refine ⟨preIn_sup_lt h37 h38 hyp ht htn hC hUA hAtop, fun K hK hKle => ?_⟩
  have hTK : T ≤ K := le_sup_right.trans hK.le
  obtain ⟨hT0, htY⟩ := inf_fsuL0_props (L := L) hTK ht
  obtain ⟨B, hB, hY⟩ := classify_preIn hT hC hT0 inf_le_right htY
  have hAB : A ≤ B := le_of_preIn_le hC (by
    rw [← hY]; exact le_inf (le_sup_left.trans hK.le) (preIn_le Ψ _))
  have hKeq : K = preIn Ψ (B.prod B) ⊔ T := by rw [← hY]; exact eq_inf_sup hKle hTK
  rcases hB with rfl | rfl | rfl | rfl
  · exfalso
    rcases hA with rfl | rfl
    exacts [pa_not_le_u3 hAB, pb_not_le_u3 hAB]
  · exfalso
    rcases hA with rfl | rfl
    · exact hK.ne hKeq.symm
    · exact pb_not_le_pa hAB
  · exfalso
    rcases hA with rfl | rfl
    · exact pa_not_le_pb hAB
    · exact hK.ne hKeq.symm
  · rw [hKeq, preIn_top]

end CFSG.Quasithin.Vol2.Ch10.SecB
