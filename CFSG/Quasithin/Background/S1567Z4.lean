module

public import CFSG.Quasithin.Background.S1567Y
public import CFSG.Quasithin.Background.S1567Q
public import CFSG.Quasithin.Background.S1567Z3
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

abbrev VE67 {G : Type} [Group G] (T M E : Subgroup G) : Subgroup G :=
  conjClosure (VZ T M) (Subgroup.normalizer (E : Set G))

namespace S1567

section General

theorem perm3_inv_of_involution : ∀ x y : Equiv.Perm (Fin 3), x ≠ 1 → x ^ 3 = 1 → y ≠ 1 → y ^ 2 = 1 →
    y * x * y⁻¹ = x⁻¹ := by decide +kernel

theorem mulAut_conj_inv {E : Type*} [Group E] [IsKleinFour E] (a b : MulAut E) (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) : b * a * b⁻¹ = a⁻¹ := by
  let e := CFSG.kleinFourAutomorphismEquivSymmetricThree E
  apply e.injective
  rw [map_mul, map_mul, map_inv, map_inv]
  exact perm3_inv_of_involution (e a) (e b) (fun h' => ha1 (e.injective (by rw [h', map_one])))
    (by rw [← map_pow, ha3, map_one]) (fun h' => hb1 (e.injective (by rw [h', map_one])))
    (by rw [← map_pow, hb2, map_one])

theorem relIndex_pos_of_finite67 {G : Type*} [Group G] [Finite G] (H K : Subgroup G) : 0 < H.relIndex K :=
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

end General

section VE

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

omit [Finite G] in
theorem VZ_le_VE67 : VZ T M ≤ VE67 T M E := le_conjClosure _ _

theorem VE67_le_conjClosure_Mc (k : Ctx67 G T Mc M V₁ V₂ E t) :
    VE67 T M E ≤ conjClosure (VZ T M) Mc := by
  refine conjClosure_le fun g hg v hv => ?_
  obtain ⟨y, hy, u, hu, w, hw, rfl⟩ := exists_decomp_GE k.c k.r66 hg
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hy
  have hyM : y ∈ M := ((oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))) hy
  have huM : u ∈ M := k.c.hyp.T_le hu.1
  have hyuN : y * u ∈ Subgroup.normalizer (VZ T M : Set G) :=
    k.c.hyp.le_normalizer (M.mul_mem hyM huM)
  have hyuE : y * u ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).mul_mem hyE hu.2
  have hmV : (y * u) * v * (y * u)⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hyuN v).mp hv
  have hw' : (y * u) * w * (y * u)⁻¹ ∈ Subgroup.centralizer (E : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_CE E hyuE) w).mp hw
  have e : (y * (u * w)) * v * (y * (u * w))⁻¹ =
      ((y * u) * w * (y * u)⁻¹) * ((y * u) * v * (y * u)⁻¹) * ((y * u) * w * (y * u)⁻¹)⁻¹ := by
    group
  rw [e]
  exact mem_conjClosure (k.r66.centralizer_le_mc hw') hmV

theorem VE67_comm (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∀ a ∈ VE67 T M E, ∀ b ∈ VE67 T M E, a * b = b * a := fun a ha b hb =>
  k.r50 Mc (isHTM153_mc k.c) a (VE67_le_conjClosure_Mc k ha) b (VE67_le_conjClosure_Mc k hb)

theorem VE67_sq (k : Ctx67 G T Mc M V₁ V₂ E t) : ∀ a ∈ VE67 T M E, a ^ 2 = 1 := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, -, z, hz, rfl⟩ := hx
    have hz2 : z ^ 2 = 1 := k.c.hyp.elemAbelian.2 z hz
    have : (h * z * h⁻¹) ^ 2 = h * z ^ 2 * h⁻¹ := by simp only [pow_two]; group
    rw [this, hz2]
    group
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : x * y = y * x := VE67_comm k x hx y hy
    have : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
      rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc y x y, ← hc, mul_assoc, mul_assoc]
    rw [this, ihx, ihy, one_mul]
  | inv x hx ih =>
    rw [inv_pow, ih, inv_one]

theorem VE67_isElemAbelian (k : Ctx67 G T Mc M V₁ V₂ E t) : IsElemAbelian 2 (VE67 T M E) :=
  ⟨⟨⟨fun a b => Subtype.ext (VE67_comm k a.1 a.2 b.1 b.2)⟩⟩, VE67_sq k⟩

omit [Finite G] in
theorem normalizer_le_normalizer_VE67 (T M E : Subgroup G) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (VE67 T M E : Set G) :=
  le_normalizer_conjClosure _ _

theorem VZ_le_normalizer_E (k : Ctx67 G T Mc M V₁ V₂ E t) :
    VZ T M ≤ Subgroup.normalizer (E : Set G) := fun _ hv =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ he =>
    (F7.isElemAbelian_comm k.c.hyp.elemAbelian (k.L.le_V he) hv))

theorem VE67_le_normalizer_E (k : Ctx67 G T Mc M V₁ V₂ E t) :
    VE67 T M E ≤ Subgroup.normalizer (E : Set G) := by
  refine conjClosure_le fun g hg v hv => ?_
  exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hg (VZ_le_normalizer_E k hv))
    ((Subgroup.normalizer _).inv_mem hg)

theorem VE67_le_pCore (k : Ctx67 G T Mc M V₁ V₂ E t) :
    VE67 T M E ≤ pCoreOf 2 (Subgroup.normalizer (E : Set G)) := by
  have hp : IsPGroup 2 ↥(VE67 T M E) := fun x => ⟨1, Subtype.ext (by simpa using VE67_sq k x.1 x.2)⟩
  exact le_pCoreOf_of_le_normalizer 2 (VE67_le_normalizer_E k) (normalizer_le_normalizer_VE67 T M E) hp

theorem VE67_le_TE (k : Ctx67 G T Mc M V₁ V₂ E t) : VE67 T M E ≤ TE153 T E := by
  have hQD : pCoreOf 2 (Subgroup.normalizer (E : Set G)) ≤ Subgroup.normalizer (E : Set G) :=
    pCoreOf_le 2 _
  exact (VE67_le_pCore k).trans
    (A4.le_of_normal_of_isSylowTwoOf k.r2.sylow_GE hQD
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr (le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _))

theorem VE67_le_centralizer_V (k : Ctx67 G T Mc M V₁ V₂ E t) :
    VE67 T M E ≤ Subgroup.centralizer (VZ T M : Set G) := fun a ha =>
  Subgroup.mem_centralizer_iff.mpr fun v hv => VE67_comm k v (VZ_le_VE67 hv) a ha

theorem VE67_commutator_YE (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ⁅VE67 T M E, YE153 Mc M E⁆ = VE67 T M E := by
  have hYE : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) := (oTwoUpper_le _).trans inf_le_right
  apply le_antisymm
  · exact commutator_le_of_le_normalizer (hYE.trans (normalizer_le_normalizer_VE67 T M E))
  · have hVN : VZ T M ≤ ⁅VE67 T M E, YE153 Mc M E⁆ := by
      have h1 := (Y_facts h113 k.c k.L).1
      calc VZ T M = ⁅VZ T M, YE153 Mc M E⁆ := h1.symm
        _ ≤ ⁅VE67 T M E, YE153 Mc M E⁆ := Subgroup.commutator_mono VZ_le_VE67 le_rfl
    have hNorm : Subgroup.normalizer (E : Set G) ≤
        Subgroup.normalizer ((⁅VE67 T M E, YE153 Mc M E⁆ : Subgroup G) : Set G) := by
      intro g hg
      rw [← conjSubgroup_eq_iff_mem_normalizer, CFSG.QuasithinUnique.C5.conjSubgroup_commutator,
        conjSubgroup_eq_iff_mem_normalizer.mpr (normalizer_le_normalizer_VE67 T M E hg),
        conjSubgroup_eq_iff_mem_normalizer.mpr (normalizer_le_normalizer_YE h113 k hg)]
    exact conjClosure_le fun g hg z hz => (Subgroup.mem_normalizer_iff.mp (hNorm hg) z).mp (hVN hz)

@[expose] def K167 (T M E : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.centralizer (E : Set G) ∧ ∀ v ∈ VE67 T M E, g * v * g⁻¹ * v⁻¹ ∈ E}
  one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun v hv => ?_⟩
    have e : a * b * v * (a * b)⁻¹ * v⁻¹ =
        (a * (b * v * b⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
    rw [e]
    refine E.mul_mem ?_ (ha' v hv)
    have h1 := Subgroup.mem_centralizer_iff.mp ha _ (hb' v hv)
    have : a * (b * v * b⁻¹ * v⁻¹) * a⁻¹ = b * v * b⁻¹ * v⁻¹ := by
      calc a * (b * v * b⁻¹ * v⁻¹) * a⁻¹ = ((b * v * b⁻¹ * v⁻¹) * a) * a⁻¹ := by rw [h1]
        _ = b * v * b⁻¹ * v⁻¹ := by group
    rw [this]
    exact hb' v hv
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, fun v hv => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp ha _ (E.inv_mem (ha' v hv))
    have e : a⁻¹ * v * a⁻¹⁻¹ * v⁻¹ = a⁻¹ * (a * v * a⁻¹ * v⁻¹)⁻¹ * a := by group
    rw [e]
    have : a⁻¹ * (a * v * a⁻¹ * v⁻¹)⁻¹ * a = (a * v * a⁻¹ * v⁻¹)⁻¹ := by
      calc a⁻¹ * (a * v * a⁻¹ * v⁻¹)⁻¹ * a = a⁻¹ * ((a * v * a⁻¹ * v⁻¹)⁻¹ * a) := by group
        _ = a⁻¹ * (a * (a * v * a⁻¹ * v⁻¹)⁻¹) := by rw [← h1]
        _ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
    rw [this]
    exact E.inv_mem (ha' v hv)

omit [Finite G] in
theorem K167_le_centralizer : K167 T M E ≤ Subgroup.centralizer (E : Set G) := fun _ hk => hk.1

omit [Finite G] in
theorem normalizer_le_normalizer_K167 (T M E : Subgroup G) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (K167 T M E : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ x ∈ Subgroup.normalizer (E : Set G), ∀ g ∈ K167 T M E, x * g * x⁻¹ ∈ K167 T M E := by
    intro x hx g hg
    refine ⟨?_, fun v hv => ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
      have hxe : x⁻¹ * e * x ∈ E := by
        simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hx) e).mp he
      have h1 := Subgroup.mem_centralizer_iff.mp hg.1 _ hxe
      calc e * (x * g * x⁻¹) = x * ((x⁻¹ * e * x) * g) * x⁻¹ := by group
        _ = x * (g * (x⁻¹ * e * x)) * x⁻¹ := by rw [h1]
        _ = (x * g * x⁻¹) * e := by group
    · have hv' : x⁻¹ * v * x ∈ VE67 T M E := by
        simpa using (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_VE67 T M E
          ((Subgroup.normalizer _).inv_mem hx)) v).mp hv
      have h2 := hg.2 _ hv'
      have e : x * g * x⁻¹ * v * (x * g * x⁻¹)⁻¹ * v⁻¹ = x * (g * (x⁻¹ * v * x) * g⁻¹ * (x⁻¹ * v * x)⁻¹) * x⁻¹ := by
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hx _).mp h2
  exact fun g => ⟨fun hg => key x hx g hg, fun hg => by
    have := key x⁻¹ ((Subgroup.normalizer _).inv_mem hx) _ hg
    simpa [mul_assoc] using this⟩

theorem YE_inf_centralizer_le_centralizer_VE (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) :
    YE153 Mc M E ⊓ Subgroup.centralizer (E : Set G) ≤
      Subgroup.centralizer (VE67 T M E : Set G) := by
  have hP : ∀ y ∈ YE153 Mc M E ⊓ Subgroup.centralizer (E : Set G),
      y ∈ Subgroup.centralizer (VZ T M : Set G) := by
    intro y hy
    have hyY : y ∈ Y153 Mc M := (oTwoUpper_le _ |>.trans inf_le_left) hy.1
    have hyZ : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.centralizer_le k.r66.Z_le_E hy.2
    have h1 : y ∈ pCoreOf 2 (Y153 Mc M) := by
      rw [k.r49.pCore_eq_centralizer_Z]
      exact ⟨hyY, hyZ⟩
    rw [k.r49.case_one.1] at h1
    exact h1.2
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hle : VE67 T M E ≤ Subgroup.centralizer ({y} : Set G) := by
    refine conjClosure_le fun g hg z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    rw [Set.mem_singleton_iff] at hy'
    subst hy'
    have hgi : g⁻¹ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).inv_mem hg
    have hY' : g⁻¹ * y' * g ∈ YE153 Mc M E := by
      have := (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_YE h113 k hgi) y').mp hy.1
      simpa using this
    have hC' : g⁻¹ * y' * g ∈ Subgroup.centralizer (E : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_CE E hgi) y').mp hy.2
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp (hP _ ⟨hY', hC'⟩) z hz
    calc y' * (g * z * g⁻¹) = g * ((g⁻¹ * y' * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y' * g)) * g⁻¹ := by rw [← h2]
      _ = (g * z * g⁻¹) * y' := by group
  exact (Subgroup.mem_centralizer_iff.mp (hle hh) y (Set.mem_singleton y)).symm

theorem commutator_YE_K167_le_centralizer (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    {y κ : G} (hy : y ∈ YE153 Mc M E) (hκ : κ ∈ K167 T M E) :
    y * κ * y⁻¹ * κ⁻¹ ∈ Subgroup.centralizer (VE67 T M E : Set G) := by
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hy
  have hκE : κ ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _ (K167_le_centralizer hκ)
  apply YE_inf_centralizer_le_centralizer_VE h113 k
  refine ⟨?_, ?_⟩
  · have h1 : κ * y⁻¹ * κ⁻¹ ∈ YE153 Mc M E :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_YE h113 k hκE) y⁻¹).mp
        ((YE153 Mc M E).inv_mem hy)
    have : y * κ * y⁻¹ * κ⁻¹ = y * (κ * y⁻¹ * κ⁻¹) := by group
    rw [this]
    exact (YE153 Mc M E).mul_mem hy h1
  · have h1 : y * κ * y⁻¹ ∈ K167 T M E :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_K167 T M E hyE) κ).mp hκ
    exact K167_le_centralizer ((K167 T M E).mul_mem h1 ((K167 T M E).inv_mem hκ))

theorem K167_le_normalizer_V (k : Ctx67 G T Mc M V₁ V₂ E t) {κ : G} (hκ : κ ∈ K167 T M E) :
    κ ∈ Subgroup.normalizer (VZ T M : Set G) := by
  have key : ∀ κ ∈ K167 T M E, ∀ v ∈ VZ T M, κ * v * κ⁻¹ ∈ VZ T M := by
    intro κ hκ v hv
    have h1 : κ * v * κ⁻¹ * v⁻¹ ∈ E := hκ.2 v (VZ_le_VE67 hv)
    have : κ * v * κ⁻¹ = (κ * v * κ⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact (VZ T M).mul_mem (k.L.le_V h1) hv
  rw [Subgroup.mem_normalizer_iff]
  exact fun v => ⟨key κ hκ v, fun h => by
    have := key κ⁻¹ ((K167 T M E).inv_mem hκ) _ h
    simpa [mul_assoc] using this⟩

theorem K167_le_M_inf_normalizer (k : Ctx67 G T Mc M V₁ V₂ E t) :
    K167 T M E ≤ M ⊓ Subgroup.normalizer (E : Set G) := fun κ hκ =>
  ⟨by rw [← normalizer_V_eq k.c.hyp]; exact K167_le_normalizer_V k hκ,
    Subgroup.centralizer_le_normalizer _ (K167_le_centralizer hκ)⟩

theorem K167_sq_mem_centralizer_V (k : Ctx67 G T Mc M V₁ V₂ E t) {κ : G} (hκ : κ ∈ K167 T M E) :
    κ * κ ∈ Subgroup.centralizer (VZ T M : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have hκC : ∀ e ∈ E, κ * e * κ⁻¹ = e := fun e he => by
    have := Subgroup.mem_centralizer_iff.mp (K167_le_centralizer hκ) e he
    calc κ * e * κ⁻¹ = (e * κ) * κ⁻¹ := by rw [this]
      _ = e := by group
  have heE : κ * v * κ⁻¹ * v⁻¹ ∈ E := hκ.2 v (VZ_le_VE67 hv)
  have hee : (κ * v * κ⁻¹ * v⁻¹) * (κ * v * κ⁻¹ * v⁻¹) = 1 := by
    have := k.c.hyp.elemAbelian.2 _ (k.L.le_V heE)
    simpa [pow_two] using this
  have h1 : κ * v * κ⁻¹ = (κ * v * κ⁻¹ * v⁻¹) * v := by group
  have h2 : κ * κ * v * (κ * κ)⁻¹ = v := by
    calc κ * κ * v * (κ * κ)⁻¹ = κ * (κ * v * κ⁻¹) * κ⁻¹ := by group
      _ = κ * ((κ * v * κ⁻¹ * v⁻¹) * v) * κ⁻¹ := by rw [← h1]
      _ = (κ * (κ * v * κ⁻¹ * v⁻¹) * κ⁻¹) * (κ * v * κ⁻¹) := by group
      _ = (κ * v * κ⁻¹ * v⁻¹) * ((κ * v * κ⁻¹ * v⁻¹) * v) := by rw [hκC _ heE, ← h1]
      _ = v := by rw [← mul_assoc, hee, one_mul]
  calc v * (κ * κ) = (κ * κ * v * (κ * κ)⁻¹) * (κ * κ) := by rw [h2]
    _ = (κ * κ) * v := by group

theorem K167_le_TE_mul_centralizer (k : Ctx67 G T Mc M V₁ V₂ E t) {κ : G} (hκ : κ ∈ K167 T M E) :
    ∃ t' ∈ TE153 T E, κ * t'⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have h := k.c.hyp
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  have hsyl : IsSylowTwoOf (autI hV (TE153 T E)) (autI hV (M ⊓ Subgroup.normalizer (E : Set G))) :=
    B2F.isSylowTwoOf_autI hV (inf_le_left.trans hMN) k.L.sylow
  have hle : autI hV (K167 T M E) ≤ autI hV (M ⊓ Subgroup.normalizer (E : Set G)) :=
    autI_mono hV (K167_le_M_inf_normalizer k)
  have hconj : ∀ φ ∈ autI hV (M ⊓ Subgroup.normalizer (E : Set G)), ∀ ψ ∈ autI hV (K167 T M E),
      φ * ψ * φ⁻¹ ∈ autI hV (K167 T M E) := by
    intro φ hφ ψ hψ
    obtain ⟨m, hm, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨κ', hκ', rfl⟩ := (mem_autI hV).1 hψ
    have hmκ : (m : G) * κ' * (m : G)⁻¹ ∈ K167 T M E :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_K167 T M E hm.2) κ').mp hκ'
    have hN : (m : G) * κ' * (m : G)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem m.2 κ'.2)
        ((Subgroup.normalizer _).inv_mem m.2)
    have := convI_mem_autI hV hmκ hN
    have e : (⟨(m : G) * κ' * (m : G)⁻¹, hN⟩ : Subgroup.normalizer (VZ T M : Set G)) = m * κ' * m⁻¹ :=
      rfl
    rw [e, map_mul, map_mul, map_inv] at this
    exact this
  have hnorm : autI hV (M ⊓ Subgroup.normalizer (E : Set G)) ≤
      Subgroup.normalizer (autI hV (K167 T M E) : Set (MulAut (IntMod (VZ T M) hV))) := by
    intro φ hφ
    rw [Subgroup.mem_normalizer_iff]
    intro ψ
    refine ⟨fun hψ => hconj φ hφ ψ hψ, fun hψ => ?_⟩
    have := hconj φ⁻¹ ((autI hV (M ⊓ Subgroup.normalizer (E : Set G))).inv_mem hφ) _ hψ
    simpa [mul_assoc] using this
  have hp : IsPGroup 2 ↥(autI hV (K167 T M E)) := by
    intro x
    obtain ⟨g, hg, hgx⟩ := (mem_autI hV).1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    have hsq := K167_sq_mem_centralizer_V k hg
    have h1 : convI hV (g * g) = 1 := (convI_eq_one_iff hV _).2 hsq
    have h2 : (x : MulAut (IntMod (VZ T M) hV)) * x = 1 := by
      rw [← hgx, ← map_mul]
      exact h1
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [pow_two] using h2
  have hle2 := A4.le_of_normal_of_isSylowTwoOf hsyl hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm) hp
  have hκN := K167_le_normalizer_V k hκ
  obtain ⟨g, hgT, hg⟩ := (mem_autI hV).1 (hle2 (convI_mem_autI hV hκ hκN))
  refine ⟨(g : G), hgT, ?_⟩
  have hN : κ * (g : G)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    (Subgroup.normalizer _).mul_mem hκN ((Subgroup.normalizer _).inv_mem g.2)
  have e : (⟨κ * (g : G)⁻¹, hN⟩ : Subgroup.normalizer (VZ T M : Set G)) = ⟨κ, hκN⟩ * g⁻¹ := rfl
  have h1 : convI hV ⟨κ * (g : G)⁻¹, hN⟩ = 1 := by
    rw [e, map_mul, map_inv, hg, mul_inv_cancel]
  exact (convI_eq_one_iff hV _).1 h1

theorem commutator_TE_K167_le_centralizer_V (k : Ctx67 G T Mc M V₁ V₂ E t) {t₁ κ : G}
    (ht₁ : t₁ ∈ TE153 T E) (hκ : κ ∈ K167 T M E) :
    t₁ * κ * t₁⁻¹ * κ⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := k.c.hyp.elemAbelian
  have hMN := k.c.hyp.le_normalizer
  obtain ⟨t', ht', hct'⟩ := K167_le_TE_mul_centralizer k hκ
  have ht₁N : t₁ ∈ Subgroup.normalizer (VZ T M : Set G) := hMN (k.c.hyp.T_le ht₁.1)
  have hκN := K167_le_normalizer_V k hκ
  have ht'N : t' ∈ Subgroup.normalizer (VZ T M : Set G) := hMN (k.c.hyp.T_le ht'.1)
  have hκt : convI hV ⟨κ, hκN⟩ = convI hV ⟨t', ht'N⟩ := by
    have hN : κ * t'⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      (Subgroup.normalizer _).mul_mem hκN ((Subgroup.normalizer _).inv_mem ht'N)
    have h1 : convI hV ⟨κ * t'⁻¹, hN⟩ = 1 := (convI_eq_one_iff hV _).2 hct'
    have e : (⟨κ * t'⁻¹, hN⟩ : Subgroup.normalizer (VZ T M : Set G)) = ⟨κ, hκN⟩ * ⟨t', ht'N⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hcomm : convI hV ⟨t₁, ht₁N⟩ * convI hV ⟨t', ht'N⟩ =
      convI hV ⟨t', ht'N⟩ * convI hV ⟨t₁, ht₁N⟩ :=
    k.r66.barTE_klein.1.2.1 _ (convI_mem_autI hV ht₁ ht₁N) _ (convI_mem_autI hV ht' ht'N)
  have hN' : t₁ * κ * t₁⁻¹ * κ⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).mul_mem ht₁N hκN) ((Subgroup.normalizer _).inv_mem ht₁N))
      ((Subgroup.normalizer _).inv_mem hκN)
  have hres : convI hV ⟨t₁ * κ * t₁⁻¹ * κ⁻¹, hN'⟩ = 1 := by
    have e : (⟨t₁ * κ * t₁⁻¹ * κ⁻¹, hN'⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        ⟨t₁, ht₁N⟩ * ⟨κ, hκN⟩ * ⟨t₁, ht₁N⟩⁻¹ * ⟨κ, hκN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hκt, hcomm]
    group
  exact (convI_eq_one_iff hV _).1 hres

theorem commutator_tau_K167_le_centralizer_VE (k : Ctx67 G T Mc M V₁ V₂ E t) {τ κ : G}
    (hτQ : τ ∈ pCoreOf 2 Mc) (hτTE : τ ∈ TE153 T E) (hκ : κ ∈ K167 T M E) :
    τ * κ * τ⁻¹ * κ⁻¹ ∈ Subgroup.centralizer (VE67 T M E : Set G) := by
  set x := τ * κ * τ⁻¹ * κ⁻¹ with hx
  have hle : VE67 T M E ≤ Subgroup.centralizer ({x} : Set G) := by
    refine conjClosure_le fun g hg z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x' hx'
    rw [Set.mem_singleton_iff] at hx'
    subst hx'
    obtain ⟨y, hy, u, hu, w, hw, rfl⟩ := exists_decomp_GE k.c k.r66 hg
    have hyE : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hy
    have hyM : y ∈ M := ((oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))) hy
    have huM : u ∈ M := k.c.hyp.T_le hu.1
    have hyuM : y * u ∈ M := M.mul_mem hyM huM
    have hyuE : y * u ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).mul_mem hyE hu.2
    set w'' := (y * u) * w * (y * u)⁻¹ with hw''
    have hw''C : w'' ∈ Subgroup.centralizer (E : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_CE E hyuE) w).mp hw
    have hw''Mc : w'' ∈ Mc := k.r66.centralizer_le_mc hw''C
    have hw''E : w'' ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hw''C
    have hκ' : w''⁻¹ * κ * w'' ∈ K167 T M E := by
      have := (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_K167 T M E
        ((Subgroup.normalizer _).inv_mem hw''E)) κ).mp hκ
      simpa using this
    have hτ'Q : w''⁻¹ * τ * w'' ∈ pCoreOf 2 Mc := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mc
        ((Mc.inv_mem hw''Mc))) τ).mp hτQ
      simpa using this
    have hτ'E : w''⁻¹ * τ * w'' ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).inv_mem hw''E) hτTE.2) hw''E
    have hτ'TE : w''⁻¹ * τ * w'' ∈ TE153 T E := ⟨pCoreOf_Mc_le_T k.c hτ'Q, hτ'E⟩
    have h1 := commutator_TE_K167_le_centralizer_V k hτ'TE hκ'
    have h2 : (y * u)⁻¹ * ((w''⁻¹ * τ * w'') * (w''⁻¹ * κ * w'') * (w''⁻¹ * τ * w'')⁻¹ *
        (w''⁻¹ * κ * w'')⁻¹) * (y * u) ∈ Subgroup.centralizer (VZ T M : Set G) := by
      have hN : (y * u)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
        (Subgroup.normalizer _).inv_mem (k.c.hyp.le_normalizer hyuM)
      exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_CE (VZ T M) hN) _).mp h1 |>
        fun h => by simpa using h
    set g := y * (u * w) with hg_def
    have hXeq : g⁻¹ * (τ * κ * τ⁻¹ * κ⁻¹) * g =
        (y * u)⁻¹ * ((w''⁻¹ * τ * w'') * (w''⁻¹ * κ * w'') * (w''⁻¹ * τ * w'')⁻¹ *
          (w''⁻¹ * κ * w'')⁻¹) * (y * u) := by
      simp only [hw'', hg_def]; group
    have hXC : g⁻¹ * (τ * κ * τ⁻¹ * κ⁻¹) * g ∈ Subgroup.centralizer (VZ T M : Set G) := by
      rw [hXeq]; exact h2
    have h3 := Subgroup.mem_centralizer_iff.mp hXC z hz
    calc (τ * κ * τ⁻¹ * κ⁻¹) * (g * z * g⁻¹)
        = g * ((g⁻¹ * (τ * κ * τ⁻¹ * κ⁻¹) * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * (τ * κ * τ⁻¹ * κ⁻¹) * g)) * g⁻¹ := by rw [← h3]
      _ = (g * z * g⁻¹) * (τ * κ * τ⁻¹ * κ⁻¹) := by group
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hle hv) x (Set.mem_singleton x)).symm

theorem exists_eps_sigma (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {τ : G}
    (hτTE : τ ∈ TE153 T E) (hττ : τ * τ ∈ Subgroup.centralizer (VZ T M : Set G))
    (hmove : ∃ e ∈ E, τ * e * τ⁻¹ ≠ e) :
    ∃ y ∈ YE153 Mc M E, ∃ ε σ : MulAut ↥E,
      (∀ e : ↥E, ((ε e : ↥E) : G) = y * e * y⁻¹) ∧ (∀ e : ↥E, ((σ e : ↥E) : G) = τ * e * τ⁻¹) ∧
      (∀ e, ε (ε (ε e)) = e) ∧ (∃ e, ε e ≠ e) ∧ (∀ e, σ (ε e) = ε (ε (σ e))) := by
  have := isKleinFour_E k.c k.L
  obtain ⟨-, y, hyYE, ⟨e₁, he₁E, hye₁⟩, hy3⟩ := Y_facts h113 k.c k.L
  obtain ⟨e₂, he₂E, hτe₂⟩ := hmove
  have hYEN : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := hYEN hyYE
  have hτN : τ ∈ Subgroup.normalizer (E : Set G) := hτTE.2
  have hε1 : conjAct E ⟨y, hyN⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨y, hyN⟩).1 h
    apply hye₁
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e₁ he₁E
    rw [← h1]
    group
  have hε3 : conjAct E ⟨y, hyN⟩ ^ 3 = 1 := by
    have hy3N : y ^ 3 ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hyN 3
    have e1 : conjAct E ⟨y, hyN⟩ ^ 3 = conjAct E ⟨y ^ 3, hy3N⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact Subgroup.centralizer_le k.L.le_V hy3
  have hσ1 : conjAct E ⟨τ, hτN⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨τ, hτN⟩).1 h
    apply hτe₂
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e₂ he₂E
    rw [← h1]
    group
  have hσ2 : conjAct E ⟨τ, hτN⟩ ^ 2 = 1 := by
    have hττN : τ * τ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).mul_mem hτN hτN
    have e1 : conjAct E ⟨τ, hτN⟩ ^ 2 = conjAct E ⟨τ * τ, hττN⟩ := by
      rw [← map_pow, pow_two]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact Subgroup.centralizer_le k.L.le_V hττ
  have hrel := mulAut_conj_inv _ _ hε1 hε3 hσ1 hσ2
  have hinv : (conjAct E ⟨y, hyN⟩)⁻¹ = conjAct E ⟨y, hyN⟩ * conjAct E ⟨y, hyN⟩ := by
    apply inv_eq_of_mul_eq_one_right
    calc conjAct E ⟨y, hyN⟩ * (conjAct E ⟨y, hyN⟩ * conjAct E ⟨y, hyN⟩) =
          conjAct E ⟨y, hyN⟩ ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := hε3
  have hcomm : conjAct E ⟨τ, hτN⟩ * conjAct E ⟨y, hyN⟩ =
      (conjAct E ⟨y, hyN⟩)⁻¹ * conjAct E ⟨τ, hτN⟩ := mul_inv_eq_iff_eq_mul.mp hrel
  refine ⟨y, hyYE, conjAct E ⟨y, hyN⟩, conjAct E ⟨τ, hτN⟩, fun e => conjAct_apply_coe''' E _ e,
    fun e => conjAct_apply_coe''' E _ e, fun e => ?_, ⟨⟨e₁, he₁E⟩, fun h => hye₁ ?_⟩, fun e => ?_⟩
  · have := congrArg (fun φ : MulAut ↥E => φ e) hε3
    simpa [pow_succ, MulAut.mul_apply] using this
  · have := congrArg Subtype.val h
    simpa [conjAct_apply_coe'''] using this
  · have := congrArg (fun φ : MulAut ↥E => φ e) hcomm
    simp only [MulAut.mul_apply] at this
    rw [this, hinv]
    rfl

@[expose] noncomputable def phi67 (k : Ctx67 G T Mc M V₁ V₂ E t) {κ : G} (hκ : κ ∈ K167 T M E) :
    ↥(VE67 T M E) →* ↥E where
  toFun v := ⟨κ * (v : G) * κ⁻¹ * (v : G)⁻¹, hκ.2 v v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    have hb : κ * (b : G) * κ⁻¹ * (b : G)⁻¹ ∈ E := hκ.2 b b.2
    have ha : κ * (a : G) * κ⁻¹ * (a : G)⁻¹ ∈ E := hκ.2 a a.2
    have hcomm : (a : G) * (κ * (b : G) * κ⁻¹ * (b : G)⁻¹) = (κ * (b : G) * κ⁻¹ * (b : G)⁻¹) * a :=
      VE67_comm k a a.2 _ (VZ_le_VE67 (k.L.le_V hb))
    have hcomm' : (κ * (b : G) * κ⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
        (a : G)⁻¹ * (κ * (b : G) * κ⁻¹ * (b : G)⁻¹) := by
      calc (κ * (b : G) * κ⁻¹ * (b : G)⁻¹) * (a : G)⁻¹
          = (a : G)⁻¹ * ((a : G) * (κ * (b : G) * κ⁻¹ * (b : G)⁻¹)) * (a : G)⁻¹ := by group
        _ = (a : G)⁻¹ * ((κ * (b : G) * κ⁻¹ * (b : G)⁻¹) * a) * (a : G)⁻¹ := by rw [hcomm]
        _ = (a : G)⁻¹ * (κ * (b : G) * κ⁻¹ * (b : G)⁻¹) := by group
    show κ * ((a : G) * b) * κ⁻¹ * ((a : G) * b)⁻¹ =
      (κ * (a : G) * κ⁻¹ * (a : G)⁻¹) * (κ * (b : G) * κ⁻¹ * (b : G)⁻¹)
    calc κ * ((a : G) * b) * κ⁻¹ * ((a : G) * b)⁻¹
        = (κ * (a : G) * κ⁻¹) * ((κ * (b : G) * κ⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (κ * (a : G) * κ⁻¹) * ((a : G)⁻¹ * (κ * (b : G) * κ⁻¹ * (b : G)⁻¹)) := by rw [hcomm']
      _ = (κ * (a : G) * κ⁻¹ * (a : G)⁻¹) * (κ * (b : G) * κ⁻¹ * (b : G)⁻¹) := by group

omit [Finite G] in
theorem phi67_conj {κ : G} (hκ : κ ∈ K167 T M E) {g : G}
    (hc : g⁻¹ * κ * g * κ⁻¹ ∈ Subgroup.centralizer (VE67 T M E : Set G)) (u : ↥(VE67 T M E)) :
    κ * (g * (u : G) * g⁻¹) * κ⁻¹ * (g * (u : G) * g⁻¹)⁻¹ = g * (κ * (u : G) * κ⁻¹ * (u : G)⁻¹) * g⁻¹ := by
  have hκE : κ ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _ (K167_le_centralizer hκ)
  have hκu : κ * (u : G) * κ⁻¹ ∈ VE67 T M E :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_VE67 T M E hκE) u).mp u.2
  set c := g⁻¹ * κ * g * κ⁻¹ with hcdef
  have hcomm : (κ * (u : G) * κ⁻¹) * c = c * (κ * (u : G) * κ⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hc _ hκu
  have hg : g⁻¹ * κ * g = c * κ := by simp only [hcdef]; group
  have hcc : c * (κ * (u : G) * κ⁻¹) * c⁻¹ = κ * (u : G) * κ⁻¹ := by
    calc c * (κ * (u : G) * κ⁻¹) * c⁻¹ = ((κ * (u : G) * κ⁻¹) * c) * c⁻¹ := by rw [hcomm]
      _ = κ * (u : G) * κ⁻¹ := by group
  calc κ * (g * (u : G) * g⁻¹) * κ⁻¹ * (g * (u : G) * g⁻¹)⁻¹
      = g * ((g⁻¹ * κ * g) * (u : G) * (g⁻¹ * κ * g)⁻¹ * (u : G)⁻¹) * g⁻¹ := by group
    _ = g * ((c * κ) * (u : G) * (c * κ)⁻¹ * (u : G)⁻¹) * g⁻¹ := by rw [hg]
    _ = g * ((c * (κ * (u : G) * κ⁻¹) * c⁻¹) * (u : G)⁻¹) * g⁻¹ := by group
    _ = g * (κ * (u : G) * κ⁻¹ * (u : G)⁻¹) * g⁻¹ := by rw [hcc]

theorem phi67_mul (k : Ctx67 G T Mc M V₁ V₂ E t) {κ κ' : G} (hκ : κ ∈ K167 T M E)
    (hκ' : κ' ∈ K167 T M E) (hκκ' : κ * κ' ∈ K167 T M E) (v : ↥(VE67 T M E)) :
    phi67 k hκκ' v = phi67 k hκ v * phi67 k hκ' v := by
  apply Subtype.ext
  have hb : κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹ ∈ E := hκ'.2 v v.2
  have hEV : ∀ e ∈ E, e ∈ VE67 T M E := fun e he => VZ_le_VE67 (k.L.le_V he)
  have hcκ : κ * (κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹) * κ⁻¹ = κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hκ.1 _ hb
    calc κ * (κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹) * κ⁻¹
        = ((κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹) * κ) * κ⁻¹ := by rw [this]
      _ = κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹ := by group
  have hcomm : (κ * (v : G) * κ⁻¹ * (v : G)⁻¹) * (κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹) =
      (κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹) * (κ * (v : G) * κ⁻¹ * (v : G)⁻¹) :=
    VE67_comm k _ (hEV _ (hκ.2 v v.2)) _ (hEV _ hb)
  show (κ * κ') * (v : G) * (κ * κ')⁻¹ * (v : G)⁻¹ =
    (κ * (v : G) * κ⁻¹ * (v : G)⁻¹) * (κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹)
  rw [hcomm]
  calc (κ * κ') * (v : G) * (κ * κ')⁻¹ * (v : G)⁻¹
      = (κ * (κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹) * κ⁻¹) * (κ * (v : G) * κ⁻¹ * (v : G)⁻¹) := by group
    _ = (κ' * (v : G) * κ'⁻¹ * (v : G)⁻¹) * (κ * (v : G) * κ⁻¹ * (v : G)⁻¹) := by rw [hcκ]

theorem index_ge_sq_of_K167 (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (B : Subgroup G) (hB : B ≤ K167 T M E) :
    ((B ⊓ Subgroup.centralizer (VE67 T M E : Set G)).relIndex B) ^ 2 ≤
      (VE67 T M E ⊓ Subgroup.centralizer (B : Set G)).relIndex (VE67 T M E) := by
  classical
  obtain ⟨τ, hτQ, hτTE, hττ, hmove⟩ := exists_tau k
  obtain ⟨y, hyY, ε, σ, hεc, hσc, hε3, hεne, hσε⟩ := exists_eps_sigma h113 k hτTE hττ hmove
  have hVE := VE67_isElemAbelian k
  have hVEc := VE67_comm k
  have hEV : ∀ e ∈ E, e ∈ VE67 T M E := fun e he => VZ_le_VE67 (k.L.le_V he)
  have hEel : IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hVEc a.1 (hEV _ a.2) b.1 (hEV _ b.2))⟩⟩,
      fun x hx => VE67_sq k x (hEV _ hx)⟩
  let _ : CommGroup ↥(VE67 T M E) := commGroupOfElemAbelian hVE
  let _ : CommGroup ↥E := commGroupOfElemAbelian hEel
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hyY
  have hτE : τ ∈ Subgroup.normalizer (E : Set G) := hτTE.2
  let ψ : ↥B →* (↥(VE67 T M E) →* ↥E) :=
    { toFun := fun κ => phi67 k (hB κ.2)
      map_one' := by
        ext v
        show (1 : G) * (v : G) * (1 : G)⁻¹ * (v : G)⁻¹ = 1
        group
      map_mul' := fun κ κ' => by
        ext v
        exact congrArg (fun e : ↥E => (e : G)) (phi67_mul k (hB κ.2) (hB κ'.2) (hB (κ * κ').2) v) }
  have hψapp : ∀ (κ : ↥B) (v : ↥(VE67 T M E)),
      (((ψ κ) v : ↥E) : G) = (κ : G) * v * (κ : G)⁻¹ * (v : G)⁻¹ := fun _ _ => rfl
  let Θ : Subgroup (↥(VE67 T M E) →* ↥E) := ψ.range
  have hyU : ∀ u : ↥(VE67 T M E), y * (u : G) * y⁻¹ ∈ VE67 T M E := fun u =>
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_VE67 T M E hyE) u).mp u.2
  have hτU : ∀ u : ↥(VE67 T M E), τ * (u : G) * τ⁻¹ ∈ VE67 T M E := fun u =>
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_VE67 T M E hτE) u).mp u.2
  have hyeq : ∀ (κ : ↥B) (u : ↥(VE67 T M E)),
      (κ : G) * (y * (u : G) * y⁻¹) * (κ : G)⁻¹ * (y * (u : G) * y⁻¹)⁻¹ =
        y * ((κ : G) * u * (κ : G)⁻¹ * (u : G)⁻¹) * y⁻¹ := by
    intro κ u
    refine phi67_conj (hB κ.2) ?_ u
    have := commutator_YE_K167_le_centralizer h113 k ((YE153 Mc M E).inv_mem hyY) (hB κ.2)
    simpa using this
  have hτeq : ∀ (κ : ↥B) (u : ↥(VE67 T M E)),
      (κ : G) * (τ * (u : G) * τ⁻¹) * (κ : G)⁻¹ * (τ * (u : G) * τ⁻¹)⁻¹ =
        τ * ((κ : G) * u * (κ : G)⁻¹ * (u : G)⁻¹) * τ⁻¹ := by
    intro κ u
    refine phi67_conj (hB κ.2) ?_ u
    have hτiQ : τ⁻¹ ∈ pCoreOf 2 Mc := (pCoreOf 2 Mc).inv_mem hτQ
    have hτiTE : τ⁻¹ ∈ TE153 T E := (TE153 T E).inv_mem hτTE
    have := commutator_tau_K167_le_centralizer_VE k hτiQ hτiTE (hB κ.2)
    simpa using this
  have hy : ∀ f ∈ Θ, ∀ u : ↥(VE67 T M E), f (⟨y * (u : G) * y⁻¹, hyU u⟩ : ↥(VE67 T M E)) = ε (f u) := by
    rintro f ⟨κ, rfl⟩ u
    apply Subtype.ext
    rw [hεc, hψapp, hψapp, hyeq]
  have ht : ∀ f ∈ Θ, ∀ u : ↥(VE67 T M E), f (⟨τ * (u : G) * τ⁻¹, hτU u⟩ : ↥(VE67 T M E)) = σ (f u) := by
    rintro f ⟨κ, rfl⟩ u
    apply Subtype.ext
    rw [hσc, hψapp, hψapp, hτeq]
  have hE2 : ∀ e : ↥E, e ^ 2 = 1 := fun e => Subtype.ext (by
    have := k.c.hyp.elemAbelian.2 (e : G) (k.L.le_V e.2)
    simpa using this)
  have hE4 : Nat.card ↥E = 4 := k.L.card_eq
  have key := card_sq_le_index_iInf_ker hE2 hE4 ε σ hε3 hεne hσε
    (fun u => ⟨y * (u : G) * y⁻¹, hyU u⟩) (fun u => ⟨τ * (u : G) * τ⁻¹, hτU u⟩) Θ hy ht
  have hker : ψ.ker = (B ⊓ Subgroup.centralizer (VE67 T M E : Set G)).subgroupOf B := by
    ext κ
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨κ.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 := congrArg (fun f : ↥(VE67 T M E) →* ↥E => ((f ⟨v, hv⟩ : ↥E) : G)) h
      simp only [hψapp] at h1
      have h2 : (κ : G) * v * (κ : G)⁻¹ * v⁻¹ = 1 := h1
      have h3 : (κ : G) * v = v * (κ : G) := by
        calc (κ : G) * v = ((κ : G) * v * (κ : G)⁻¹ * v⁻¹) * (v * (κ : G)) := by group
          _ = v * (κ : G) := by rw [h2, one_mul]
      exact h3.symm
    · rintro ⟨-, hc⟩
      ext v
      have := Subgroup.mem_centralizer_iff.mp hc v v.2
      show (κ : G) * v * (κ : G)⁻¹ * (v : G)⁻¹ = 1
      calc (κ : G) * v * (κ : G)⁻¹ * (v : G)⁻¹ = ((κ : G) * v) * ((κ : G)⁻¹ * (v : G)⁻¹) := by group
        _ = (v * (κ : G)) * ((κ : G)⁻¹ * (v : G)⁻¹) := by rw [← this]
        _ = 1 := by group
  have hcardΘ : Nat.card Θ = (B ⊓ Subgroup.centralizer (VE67 T M E : Set G)).relIndex B := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hinf : (⨅ f ∈ Θ, f.ker) =
      (VE67 T M E ⊓ Subgroup.centralizer (B : Set G)).subgroupOf (VE67 T M E) := by
    ext v
    simp only [Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun κ hκ => ?_⟩
      have h1 := congrArg (fun e : ↥E => (e : G)) (h (ψ ⟨κ, hκ⟩) ⟨⟨κ, hκ⟩, rfl⟩)
      simp only [hψapp] at h1
      have h2 : κ * (v : G) * κ⁻¹ * (v : G)⁻¹ = 1 := h1
      calc κ * (v : G) = (κ * (v : G) * κ⁻¹ * (v : G)⁻¹) * ((v : G) * κ) := by group
        _ = (v : G) * κ := by rw [h2]; group
    · rintro ⟨-, hc⟩ f ⟨κ, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hc (κ : G) κ.2
      apply Subtype.ext
      show (κ : G) * v * (κ : G)⁻¹ * (v : G)⁻¹ = 1
      calc (κ : G) * v * (κ : G)⁻¹ * (v : G)⁻¹ = ((κ : G) * v) * ((κ : G)⁻¹ * (v : G)⁻¹) := by group
        _ = (v * (κ : G)) * ((κ : G)⁻¹ * (v : G)⁻¹) := by rw [this]
        _ = 1 := by group
  rw [hcardΘ, hinf] at key
  exact key

theorem step67_count (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) {A : Subgroup G} (hA : IsMaxElemAbelian (TE153 T E) A) :
    Nat.card (VE67 T M E) ≤ ((A ⊓ K167 T M E).relIndex A) ^ 2 *
      Nat.card ↥(VE67 T M E ⊓ Subgroup.centralizer (A : Set G)) := by
  have hAC : A ≤ Subgroup.centralizer (VZ T M : Set G) :=
    (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ (TE153 T E)).trans
      (C1Pack153.thompsonJ_TE_le_centralizer k.c k.L k.r66)
  have hAE : A ≤ Subgroup.centralizer (E : Set G) :=
    hAC.trans (Subgroup.centralizer_le k.L.le_V)
  set V := VE67 T M E with hV
  set D := A ⊓ Subgroup.centralizer (V : Set G) with hD
  set K := A ⊓ K167 T M E with hK
  have hDK167 : D ≤ K167 T M E := fun x hx =>
    ⟨hAE hx.1, fun v hv => by
      have := Subgroup.mem_centralizer_iff.mp hx.2 v hv
      have h2 : x * v * x⁻¹ * v⁻¹ = 1 := by
        calc x * v * x⁻¹ * v⁻¹ = (x * v) * x⁻¹ * v⁻¹ := by group
          _ = (v * x) * x⁻¹ * v⁻¹ := by rw [← this]
          _ = 1 := by group
      rw [h2]
      exact E.one_mem⟩
  have hDK : D ≤ K := le_inf inf_le_left hDK167
  have hKD : K ⊓ Subgroup.centralizer (V : Set G) = D := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1.1, hx.2⟩
    · exact fun x hx => ⟨hDK hx, hx.2⟩
  have htower := Subgroup.relIndex_mul_relIndex D K A hDK inf_le_left
  have h1 := card_le_relIndex_mul_card (VE67_isElemAbelian k) (VE67_le_TE k) hA
  have h2 := index_ge_sq_of_K167 h113 k K inf_le_right
  rw [hKD] at h2
  have hle : V ⊓ Subgroup.centralizer (A : Set G) ≤ V ⊓ Subgroup.centralizer (K : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left)
  have h3 : (V ⊓ Subgroup.centralizer (K : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V :=
    Nat.le_of_dvd (relIndex_pos_of_finite67 _ _) (Subgroup.relIndex_dvd_of_le_left V hle)
  have h4 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
  rw [inf_eq_left.mpr (inf_le_left : V ⊓ Subgroup.centralizer (A : Set G) ≤ V)] at h4
  have h4' : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = Nat.card V := by
    simpa [inf_assoc] using h4
  have hcpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have hi2pos : 0 < D.relIndex K := relIndex_pos_of_finite67 _ _
  set N := (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V with hN
  set c := Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) with hc
  set i₁ := K.relIndex A with hi₁
  set i₂ := D.relIndex K with hi₂
  have hDA : D.relIndex A = i₂ * i₁ := htower.symm
  rw [hDA] at h1
  rw [← h4'] at h1 ⊢
  have hN1 : N ≤ i₂ * i₁ := Nat.le_of_mul_le_mul_right h1 hcpos
  have hsq : i₂ ^ 2 ≤ N := h2.trans h3
  have hi : i₂ ≤ i₁ := by
    have : i₂ * i₂ ≤ i₂ * i₁ := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hi2pos
  calc N * c ≤ (i₂ * i₁) * c := Nat.mul_le_mul_right c hN1
    _ ≤ (i₁ * i₁) * c := Nat.mul_le_mul_right c (Nat.mul_le_mul_right i₁ hi)
    _ = i₁ ^ 2 * c := by ring

theorem not_thompsonJ_TE_le_K167 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ¬ thompsonJ (TE153 T E) ≤ K167 T M E := by
  obtain ⟨hJTE, hTJ, hYJ, hPJ, hNJM, -⟩ := commJ_data h113 k
  intro hJK
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hYE : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) := (oTwoUpper_le _).trans inf_le_right
  set I' : Subgroup G := conjClosure (thompsonJ (TE153 T E)) (Subgroup.centralizer (E : Set G))
    with hI'
  have hI'K : I' ≤ K167 T M E := conjClosure_le fun c hc z hz =>
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_K167 T M E (hCN hc)) z).mp (hJK hz)
  have hI'M : I' ≤ M := hI'K.trans ((K167_le_M_inf_normalizer k).trans inf_le_left)
  have hI'GE : I' ≤ Subgroup.normalizer (E : Set G) := hI'K.trans (K167_le_centralizer.trans hCN)
  have hGEI' : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (I' : Set G) := by
    rw [k.r66.GE_eq]
    refine sup_le (sup_le ?_ ?_) (le_normalizer_conjClosure _ _)
    · refine le_normalizer_conjClosure_of_le (K := YE153 Mc M E) (fun y hy => hYJ ?_)
        (fun y hy => normalizer_le_normalizer_CE E (hYE hy))
      exact ((oTwoUpper_le _).trans inf_le_left) hy
    · exact le_normalizer_conjClosure_of_le hTJ
        (fun y hy => normalizer_le_normalizer_CE E hy.2)
  have hsyl : IsSylowTwoOf (TE153 T E ⊓ I') I' :=
    A4.isSylowTwoOf_inf_normal k.r2.sylow_GE hI'GE hGEI'
  have hJP : thompsonJ (TE153 T E) ≤ TE153 T E ⊓ I' := le_inf hJTE (le_conjClosure _ _)
  apply k.L.not_le_M
  intro y hy
  obtain ⟨x, hx, n, hn, rfl⟩ := frattini_two hI'GE hGEI' hsyl hy
  exact M.mul_mem (hI'M hx) (hNJM (hPJ _ hJP inf_le_left hn.2))

theorem exists_isMaxElemAbelian_not_le_K167 (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∃ A : Subgroup G, IsMaxElemAbelian (TE153 T E) A ∧ ¬ A ≤ K167 T M E := by
  by_contra hno
  push Not at hno
  apply not_thompsonJ_TE_le_K167 h113 k
  exact iSup₂_le fun A hA => hno A hA

end VE

end S1567

end CFSG.Quasithin
