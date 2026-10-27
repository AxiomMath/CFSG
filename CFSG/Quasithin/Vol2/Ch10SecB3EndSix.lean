module

public import CFSG.Quasithin.Vol2.Ch10SecB3End

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_ne_one_fsuVM_centralizer_T (hyp : Hyp10 G T L I) :
    ∃ c ∈ fsuVM T L I, c ≠ 1 ∧ c ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVT := SecA.fsuVM_le_T hyp
  have hTN : T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuM T L).trans (SecA.fsuM_le_normalizer_fsuVM T L I)
  have hn : ((fsuVM T L I).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTN
  have hnil : Group.IsNilpotent ↥T := hyp.fsu.sylow.1.isNilpotent
  have hne : (fsuVM T L I).subgroupOf T ≠ ⊥ := by
    intro h
    apply SecA.fsuVM_ne_bot hyp.fsu
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVT hv⟩ : ↥T) ∈ (fsuVM T L I).subgroupOf T := hv
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨⟨x, hxV, hxZ⟩, hx1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(x : G), hxV, fun h => hx1 (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxZ) ⟨t, ht⟩)

theorem commutator_fsuUL_eq_bot_six (hF : FactCommGL4) (h6 : Case10_1_1Six T L I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpL : ¬ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L))
    {A : Subgroup G} (hA : A ≤ cenL0 T L I) (hAp : IsPGroup p A)
    (hAZ : fsuVM T L I ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (A : Set G))
    (hcL : ¬ fsuVM T L I ⊓ Subgroup.centralizer (T : Set G) ≤
      Subgroup.centralizer (L : Set G)) :
    ⁅fsuUL T L I, A⁆ = ⊥ := by
  obtain ⟨-, hab, hds, -⟩ := h6
  set V := fsuVM T L I with hVdef
  set U := fsuUL T L I with hUdef
  have hUV := fsuUL_le' T L I
  obtain ⟨c, hc, hcL'⟩ := IsConcreteLE.not_le_iff_exists.mp hcL
  rw [Subgroup.mem_centralizer_iff] at hcL'
  push Not at hcL'
  obtain ⟨l, hl, hlc⟩ := hcL'
  have hcV : c ∈ V := hc.1
  have hcA := hAZ hc
  set u := c * l * c⁻¹ * l⁻¹ with hudef
  have huU : u ∈ U := Subgroup.commutator_mem_commutator hcV hl
  have hu1 : u ≠ 1 := by
    intro h
    apply hlc
    have : c * l = l * c := by
      have h' : u * (l * c) = l * c := by rw [h, one_mul]
      rw [hudef] at h'
      simpa [mul_assoc] using h'
    exact this.symm
  have huA : ∀ a ∈ A, a * u * a⁻¹ = u := by
    intro a ha
    obtain ⟨-, hac⟩ := mem_cenL0.mp (hA ha)
    have hc' := hac l (SecA.le_fsuL0 T L hl)
    set d := a * l * a⁻¹ * l⁻¹ with hd
    have hca : a * c * a⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.mp hcA a ha
      rw [this, mul_inv_cancel_right]
    have hlc' : l * c⁻¹ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_fsuVM T L I hl) _).mp
        (Subgroup.inv_mem _ hcV)
    have hdc := Subgroup.mem_centralizer_iff.mp hc' _ hlc'
    calc a * u * a⁻¹ = (a * c * a⁻¹) * (d * l) * (a * c * a⁻¹)⁻¹ * (d * l)⁻¹ := by
          rw [hudef, hd]; group
      _ = c * (d * (l * c⁻¹ * l⁻¹) * d⁻¹) := by rw [hca]; group
      _ = c * (l * c⁻¹ * l⁻¹) := by rw [← hdc, mul_inv_cancel_right]
      _ = u := by rw [hudef]; group
  have hcV' : ∀ a ∈ A, ∀ l' ∈ L, a * l' * a⁻¹ * l'⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    fun a ha l' hl' => (mem_cenL0.mp (hA ha)).2 l' (SecA.le_fsuL0 T L hl')
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
    SecA.fsuM_le_normalizer_fsuVM T L I (mem_cenL0.mp (hA ha)).1
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    hA.trans (cenL0_le_normalizer_fsuUL T L I)
  have key := hF ↥V (autOn L V) (autOn A V) (U.subgroupOf V) p hds hp hp2
    (not_dvd_card_autOn_L hp hp2 hpL V) (isPGroup_autOn hAp) (autOn_comm hcV')
    (fun x hx w hw => by
      obtain ⟨a, ha, rfl⟩ := SecB.mem_autOn_iff.mp hx
      rw [Subgroup.mem_subgroupOf, conjAct_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hAU ha) w).mp hw)
    ⟨⟨u, hUV huU⟩, huU, fun h => hu1 (congrArg Subtype.val h), fun x hx => by
      obtain ⟨a, ha, rfl⟩ := SecB.mem_autOn_iff.mp hx
      exact Subtype.ext (by rw [conjAct_apply_coe]; exact huA a ha)⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hx : conjAct V ⟨a, hAN ha⟩ ∈ autOn A V := SecB.mem_autOn_iff.mpr ⟨⟨a, hAN ha⟩, ha, rfl⟩
  have h1 := congrArg Subtype.val (key _ hx ⟨w, hUV hw⟩ hw)
  rw [conjAct_apply_coe] at h1
  calc a * w = a * w * a⁻¹ * a := by group
    _ = w * a := by rw [h1]

theorem commutator_fsuVM_eq_bot_six (hF : FactCommGL4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h6 : Case10_1_1Six T L I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpL : ¬ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L))
    {A : Subgroup G} (hA : A ≤ cenL0 T L I) (hAp : IsPGroup p A)
    (hAZ : fsuVM T L I ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (A : Set G))
    (hcL : ¬ fsuVM T L I ⊓ Subgroup.centralizer (T : Set G) ≤
      Subgroup.centralizer (L : Set G)) :
    ⁅fsuVM T L I, A⁆ = ⊥ := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hAZ' : fsuVM T L I ⊓ Subgroup.centralizer (T : Set G) ≤
      Subgroup.centralizer ((A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hAZ hc) a ha
    have h2 := Subgroup.mem_centralizer_iff.mp hc.2 t ht
    have h3 : t⁻¹ * c = c * t⁻¹ := by
      calc t⁻¹ * c = t⁻¹ * (c * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * c) * t⁻¹ := by rw [h2]
        _ = c * t⁻¹ := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc t * a * t⁻¹ * c = t * (a * c) * t⁻¹ := by rw [mul_assoc (t * a), h3]; group
      _ = t * (c * a) * t⁻¹ := by rw [h1]
      _ = c * (t * a * t⁻¹) := by
          calc t * (c * a) * t⁻¹ = (t * c) * a * t⁻¹ := by group
            _ = (c * t) * a * t⁻¹ := by rw [h2]
            _ = c * (t * a * t⁻¹) := by group
  exact commutator_fsuVM_eq_bot_of_conj h37 h38 hyp ht htn
    (commutator_fsuUL_eq_bot_six hF h6 hp hp2 hpL hA hAp hAZ hcL)
    (commutator_fsuUL_eq_bot_six hF h6 hp hp2 hpL
      (map_conj_le_cenL0 (SecA.le_fsuM T L ht) hA) (hAp.map _) hAZ' hcL)

end CFSG.Quasithin.Vol2.Ch10.SecB
