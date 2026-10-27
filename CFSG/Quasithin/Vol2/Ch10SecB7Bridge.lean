module

public import CFSG.Quasithin.Vol2.Ch10SecB7Fact
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13

variable {G : Type} [Group G]

abbrev modSub {V : Subgroup G} (hV : IsElemAbelian 2 V) (U : Subgroup G) :
    Subgroup (IntMod V hV) :=
  U.comap (E3.valHom hV)

theorem range_valHom {V : Subgroup G} (hV : IsElemAbelian 2 V) : (E3.valHom hV).range = V := by
  ext g
  constructor
  · intro hg
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hg
    exact w.val_mem
  · intro hg
    exact MonoidHom.mem_range.mpr ⟨IntMod.mk hV ⟨g, hg⟩, rfl⟩

theorem modSub_sup_eq_top {V U U' : Subgroup G} (hV : IsElemAbelian 2 V) (hU : U ≤ V)
    (hU' : U' ≤ V) (h : V = U ⊔ U') : modSub hV U ⊔ modSub hV U' = ⊤ := by
  have h1 : U ≤ (E3.valHom hV).range := by rw [range_valHom hV]; exact hU
  have h2 : U' ≤ (E3.valHom hV).range := by rw [range_valHom hV]; exact hU'
  rw [Subgroup.comap_sup_eq_of_le_range _ h1 h2, ← h]
  exact eq_top_iff.mpr fun w _ => w.val_mem

theorem comm_of_split {W : Type*} [CommGroup W] {W₁ W₂ : Subgroup W} (hW : W₁ ⊔ W₂ = ⊤)
    {x y : MulAut W} (hx₁ : ∀ w ∈ W₁, x w ∈ W₁) (hx₂ : ∀ w ∈ W₂, x w = w)
    (hy₁ : ∀ w ∈ W₁, y w = w) (hy₂ : ∀ w ∈ W₂, y w ∈ W₂) : x * y = y * x := by
  ext w
  have hw : w ∈ W₁ ⊔ W₂ := by rw [hW]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  simp only [MulAut.mul_apply, map_mul]
  rw [hy₁ a ha, hx₂ b hb, hx₂ (y b) (hy₂ b hb), hy₁ (x a) (hx₁ a ha)]

theorem convI_fix {V U : Subgroup G} (hV : IsElemAbelian 2 V) {g : Subgroup.normalizer (V : Set G)}
    (hg : (g : G) ∈ Subgroup.centralizer (U : Set G)) {w : IntMod V hV} (hw : w ∈ modSub hV U) :
    convI hV g w = w := by
  refine IntMod.val_injective ?_
  rw [convI_apply_val]
  have h := Subgroup.mem_centralizer_iff.mp hg w.val hw
  rw [← h, mul_inv_cancel_right]

theorem convI_mem {V U : Subgroup G} (hV : IsElemAbelian 2 V) {g : Subgroup.normalizer (V : Set G)}
    (hg : (g : G) ∈ Subgroup.normalizer (U : Set G)) {w : IntMod V hV} (hw : w ∈ modSub hV U) :
    convI hV g w ∈ modSub hV U := by
  show (convI hV g w).val ∈ U
  rw [convI_apply_val]
  exact (Subgroup.mem_normalizer_iff.mp hg _).mp hw

theorem pCore_autI_eq_bot {V M : Subgroup G} (hV : IsElemAbelian 2 V) (hVM : V ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hR : IsPrimeReduced 2 (V.subgroupOf M)) :
    CFSG.pCore 2 ↥(autI hV M) = ⊥ := by
  obtain ⟨_, -, hR⟩ := hR
  have hC : Subgroup.centralizer ((V.subgroupOf M : Subgroup ↥M) : Set ↥M) =
      (convHom hV M hMN).ker := by
    rw [ker_convHom]
    ext m
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨m.2, fun v hv => congrArg Subtype.val (h ⟨v, hVM hv⟩ hv)⟩
    · rintro ⟨-, h⟩ v hv
      exact Subtype.ext (h v hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hC).trans
    ((QuotientGroup.quotientKerEquivRange (convHom hV M hMN)).trans
      (MulEquiv.subgroupCongr (range_convHom hV M hMN)))
  rw [← CFSG.pCore_map_iso 2 e, hR, Subgroup.map_bot]

variable {T L I : Subgroup G}

theorem commutator_le_fsuVM {K : Subgroup G} (hK : K ≤ fsuM T L) :
    ⁅fsuVM T L I, K⁆ ≤ fsuVM T L I :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hK.trans (SecA.fsuM_le_normalizer_fsuVM T L I))

theorem map_modSub_conj (hV : IsElemAbelian 2 (fsuVM T L I)) {t : G} (htM : t ∈ fsuM T L)
    (hti : t⁻¹ ∈ Subgroup.normalizer (fsuVM T L I : Set G)) :
    (modSub hV ⁅fsuVM T L I, L⁆).map ((convI hV ⟨t⁻¹, hti⟩ : MulAut (IntMod (fsuVM T L I) hV)) :
      IntMod (fsuVM T L I) hV →* IntMod (fsuVM T L I) hV) =
      modSub hV ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  have htN : t ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuM_le_normalizer_fsuVM T L I htM
  have hc := SecA.conjugate_commutator_fsuVM (I := I) htM
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w', hw', rfl⟩
    show (convI hV ⟨t⁻¹, hti⟩ w').val ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆
    rw [convI_apply_val, ← hc, inv_inv]
    exact SecA.conj_mem_conjugate t hw'
  · intro hw
    have hw2 : w.val ∈ CFSG.conjugate ⁅fsuVM T L I, L⁆ t := by rw [hc]; exact hw
    rw [SecA.mem_conjugate_iff] at hw2
    refine ⟨convI hV ⟨t, htN⟩ w, ?_, ?_⟩
    · show (convI hV ⟨t, htN⟩ w).val ∈ ⁅fsuVM T L I, L⁆
      rw [convI_apply_val]
      exact hw2
    · refine IntMod.val_injective ?_
      show (convI hV ⟨t⁻¹, hti⟩ (convI hV ⟨t, htN⟩ w)).val = w.val
      simp [convI_apply_val, mul_assoc]

variable [Finite G]

theorem six_facts (hF : Fact10_2_7Six) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I)
    (h6 : Case10_1_1Six T L I) (hV : IsElemAbelian 2 (fsuVM T L I)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    rk (IntMod (fsuVM T L I) hV) = 24 ∧ E3.mParam (autI hV (fsuM T L)) = 4 ∧
      E3.aParam (autI hV (fsuM T L)) = 2 ∧ E3.nPrime (autI hV (fsuM T L)) = 4 ∧
      (∀ x ∈ autI hV (fsuM T L), x ≠ 1 → rkIdx (fixV (Subgroup.zpowers x)) ≤ 4 →
        orderOf x = 2 ∧ (modSub hV ⁅fsuVM T L I, L⁆ ≤ fixV (Subgroup.zpowers x) ∨
          modSub hV ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fixV (Subgroup.zpowers x))) ∧
      ∀ A ∈ E3.aSet 2 (autI hV (fsuM T L)),
        E3.mQuot A (A ⊓ fixingSubgroup (MulAut (IntMod (fsuVM T L I) hV))
          (modSub hV ⁅fsuVM T L I, L⁆ : Set (IntMod (fsuVM T L I) hV))) ≤ 2 ∧
        E3.mQuot A (A ⊓ fixingSubgroup (MulAut (IntMod (fsuVM T L I) hV))
          (modSub hV ⁅fsuVM T L I, CFSG.conjugate L t⁆ : Set (IntMod (fsuVM T L I) hV))) ≤ 2 := by
  obtain ⟨hVM, hR, h1, -⟩ := h1011 G T L I hyp
  obtain ⟨hsup, hV1, hV2, -⟩ := h1 t ht htn
  obtain ⟨-, _, hD, hres⟩ := h6
  have hLM : L ≤ fsuM T L := (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)
  have hLtM : CFSG.conjugate L t ≤ fsuM T L :=
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)
  have hMN := SecA.fsuM_le_normalizer_fsuVM T L I
  have htM : t ∈ fsuM T L := le_fsuM T L ht
  have hti : t⁻¹ ∈ Subgroup.normalizer (fsuVM T L I : Set G) := hMN ((fsuM T L).inv_mem htM)
  have hL0 : autI hV L ⊔ autI hV (CFSG.conjugate L t) = autI hV (fsuL0 T L) := by
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn, autI_sup hV (hLM.trans hMN) (hLtM.trans hMN)]
  have hW := modSub_sup_eq_top hV (commutator_le_fsuVM (I := I) hLM)
    (commutator_le_fsuVM (I := I) hLtM) hsup
  have hN1 : L ≤ Subgroup.normalizer ((⁅fsuVM T L I, L⁆ : Subgroup G) : Set G) :=
    SecA.le_normalizer_commutator (hLM.trans hMN) Subgroup.le_normalizer
  have hN2 : CFSG.conjugate L t ≤
      Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) :=
    SecA.le_normalizer_commutator (hLtM.trans hMN) Subgroup.le_normalizer
  have hC2 := Subgroup.le_centralizer_iff.mp hV2
  have hC1 := Subgroup.le_centralizer_iff.mp hV1
  have hnorm : autI hV (fsuM T L) ≤ Subgroup.normalizer
      ((autI hV L ⊔ autI hV (CFSG.conjugate L t) : Subgroup _) :
        Set (MulAut (IntMod (fsuVM T L I) hV))) := by
    rw [hL0]
    intro φ hφ
    obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := (mem_autI hV).1 hφ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
      autI_cjSub hV hgN]
    congr 1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hcent : autI hV (CFSG.conjugate L t) ≤
      Subgroup.centralizer (autI hV L : Set (MulAut (IntMod (fsuVM T L I) hV))) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨⟨a, haN⟩, ha, rfl⟩ := (mem_autI hV).1 hx
    obtain ⟨⟨b, hbN⟩, hb, rfl⟩ := (mem_autI hV).1 hy
    exact comm_of_split hW (fun w hw => convI_mem hV (hN1 ha) hw)
      (fun w hw => convI_fix hV (hC2 ha) hw) (fun w hw => convI_fix hV (hC1 hb) hw)
      (fun w hw => convI_mem hV (hN2 hb) hw)
  have hfix1 : ∀ x ∈ autI hV L, ∀ w ∈ modSub hV ⁅fsuVM T L I, CFSG.conjugate L t⁆, x w = w := by
    intro x hx w hw
    obtain ⟨⟨a, haN⟩, ha, rfl⟩ := (mem_autI hV).1 hx
    exact convI_fix hV (hC2 ha) hw
  have hfix2 : ∀ x ∈ autI hV (CFSG.conjugate L t), ∀ w ∈ modSub hV ⁅fsuVM T L I, L⁆,
      x w = w := by
    intro x hx w hw
    obtain ⟨⟨a, haN⟩, ha, rfl⟩ := (mem_autI hV).1 hx
    exact convI_fix hV (hC1 ha) hw
  have hmapL : (autI hV L).map (MulAut.conj (convI hV ⟨t⁻¹, hti⟩)).toMonoidHom =
      autI hV (CFSG.conjugate L t) := by
    rw [autI_cjSub hV hti]
    rfl
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hF (IntMod (fsuVM T L I) hV) (fun w => IntMod.sq_eq_one w)
    (autI hV (fsuM T L)) (autI hV L) (autI hV (CFSG.conjugate L t))
    (modSub hV ⁅fsuVM T L I, L⁆) (modSub hV ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (convI hV ⟨t⁻¹, hti⟩) hW (autI_mono hV hLM) (autI_mono hV hLtM) hnorm hcent hfix1 hfix2
    hD (convI_mem_autI hV ((fsuM T L).inv_mem htM) hti) hmapL
    (map_modSub_conj hV htM hti) (pCore_autI_eq_bot hV hVM hMN hR) (by rw [hL0]; exact hres)
  exact ⟨e1, e2, e3, e4, e5, fun A hA => ⟨(e6 A hA).2.2.1, (e6 A hA).2.2.2⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
