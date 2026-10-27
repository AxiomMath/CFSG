module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Comm
public import CFSG.Quasithin.Vol2.Ch10SecEE3Lift1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G]

theorem exists_commuting_pair {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Subgroup (MulAut (IntMod V hV))} {θ : ↥K ≃* Perm (Fin 5)}
    {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)} (hβ : A5Equivariant θ β)
    {x y : Subgroup.normalizer (V : Set G)} (hx2 : (x : G) ^ 2 = 1) (hy2 : (y : G) ^ 2 = 1)
    (hxK : convI hV x = ((θ.symm sA : ↥K) : MulAut (IntMod V hV)))
    (hyK : convI hV y = ((θ.symm sB : ↥K) : MulAut (IntMod V hV)))
    (hc : (x : G) * y * x * y ∈ V) (hcK : IntMod.mk hV ⟨_, hc⟩ ∈ commV K) :
    ∃ v w : ↥(commV K), ((x : G) * IntMod.val (w : IntMod V hV)) ^ 2 = 1 ∧
      ((y : G) * IntMod.val (v : IntMod V hV)) ^ 2 = 1 ∧
      (x : G) * IntMod.val (w : IntMod V hV) * ((y : G) * IntMod.val (v : IntMod V hV)) =
        (y : G) * IntMod.val (v : IntMod V hV) * ((x : G) * IntMod.val (w : IntMod V hV)) := by
  have hxx : (x : G) * x = 1 := by rw [← pow_two]; exact hx2
  have hyy : (y : G) * y = 1 := by rw [← pow_two]; exact hy2
  have hx' : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hy' : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  set c : G := (x : G) * y * x * y with hcdef
  have hcc : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV.2 c hc)
  have hcx : (x : G) * c * (x : G)⁻¹ = c := by
    have h : (x : G) * c * (x : G)⁻¹ = c⁻¹ := by
      rw [hcdef]
      calc (x : G) * (x * y * x * y) * (x : G)⁻¹ = (x * x) * y * x * y * (x : G)⁻¹ := by group
        _ = y * x * y * (x : G)⁻¹ := by rw [hxx, one_mul]
        _ = (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹ * (x : G)⁻¹ := by rw [hx', hy']
        _ = ((x : G) * y * x * y)⁻¹ := by group
    rw [h, hcc]
  have hcy : (y : G) * c * (y : G)⁻¹ = c := by
    have h : (y : G) * c * (y : G)⁻¹ = c⁻¹ := by
      rw [hcdef]
      calc (y : G) * (x * y * x * y) * (y : G)⁻¹ = y * x * y * x := by group
        _ = (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹ * (x : G)⁻¹ := by rw [hx', hy']
        _ = ((x : G) * y * x * y)⁻¹ := by group
    rw [h, hcc]
  set cb : ↥(commV K) := ⟨IntMod.mk hV ⟨c, hc⟩, hcK⟩
  have hfx : ((θ.symm sA : ↥K) : MulAut (IntMod V hV)) (cb : IntMod V hV) = cb := by
    rw [← hxK]
    exact (convI_fix_iff hV x _).mpr hcx
  have hfy : ((θ.symm sB : ↥K) : MulAut (IntMod V hV)) (cb : IntMod V hV) = cb := by
    rw [← hyK]
    exact (convI_fix_iff hV y _).mpr hcy
  obtain ⟨v, w, hw, hv, heq⟩ := exists_adjust_coord hβ (MulEquiv.apply_symm_apply θ sA)
    (MulEquiv.apply_symm_apply θ sB) cb hfx hfy
  rw [← hxK] at hw heq
  rw [← hyK] at hv heq
  have hwx := (convI_fix_iff hV x _).mp hw
  have hvy := (convI_fix_iff hV y _).mp hv
  have hval := congrArg IntMod.val heq
  simp only [IntMod.val_mul, convI_apply_val] at hval
  have hsq : ∀ (z : G) (u : IntMod V hV), z * z = 1 → z * u.val * z⁻¹ = u.val →
      (z * u.val) ^ 2 = 1 := by
    intro z u hz hzu
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    rw [pow_two]
    calc z * u.val * (z * u.val) = z * u.val * z⁻¹ * u.val := by rw [hz']; group
      _ = u.val * u.val := by rw [hzu]
      _ = 1 := by rw [← pow_two]; exact hV.2 _ (IntMod.val_mem u)
  refine ⟨v, w, hsq _ _ hxx hwx, hsq _ _ hyy hvy, commute_of_adjust hxx hyy rfl ?_⟩
  rw [hx', hy'] at hval
  exact hval

variable [Finite G] {T L I : Subgroup G}

theorem commute_of_mem_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) {a b : G}
    (ha : a ∈ Ch10.T1 T L ⊓ Subgroup.centralizer (CFSG.conjugate L t : Set G))
    (hb : b ∈ Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G)) : a * b = b * a := by
  have hT1 := T1_le_normalizer_conjugate h37 h38 hyp ht
  have hk1 : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have h1 := normalizer_le_normalizer_centralizer' L ha.1.2
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp h1 b).mp hb.2)
      (Subgroup.inv_mem _ hb.2)
  have hk2 : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := by
    have h1 := normalizer_le_normalizer_centralizer' (CFSG.conjugate L t) (hT1 hb.1)
    have h2 := (Subgroup.mem_normalizer_iff.mp h1 a⁻¹).mp (Subgroup.inv_mem _ ha.2)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha.2 h2
  have hkT : a * b * a⁻¹ * b⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem ha.1.1 hb.1.1) (T.inv_mem ha.1.1)) (T.inv_mem hb.1.1)
  have hk : a * b * a⁻¹ * b⁻¹ ∈ T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
    refine ⟨hkT, ?_⟩
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact mem_centralizer_sup_of hk1 hk2
  rw [hC0, Subgroup.mem_bot] at hk
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hk, one_mul]

end CFSG.Quasithin.Vol2.Ch10.SecE
