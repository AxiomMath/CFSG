module

public import CFSG.Monster.B.TwoA.Census.MonoFibre
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Monster.VisQuot.Stabilizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Visible CFSG.Monster.ScalarKernel

theorem decode_seedA (j : ℕ) : decode (seedA j) = seedPerm j := rfl

theorem coe_seedAut_eq {j : ℕ} (hj : j < 3) :
    (seedAut j : Equiv.Perm (Fin 24)) = seedPerm j :=
  coe_seedAut (seedPerm_mem hj)

theorem seedAut_zero : seedAut 0 = 1 :=
  Subtype.ext ((coe_seedAut_eq (by norm_num)).trans seedPerm_zero)

theorem decode_centGenArrs_mem
    {j : ℕ} (hj : j < 3) {a : Array ℕ} (ha : a ∈ centGenArrs j) :
    decode a ∈ AutPerm :=
  mem_AutPerm_of_arr (centGenArr_perm j hj a ha) (centGenArr_aut j hj a ha)

theorem coe_centAut_eq
    {j k : ℕ} (hj : j < 3) (hk : k < (centGenArrs j).length) :
    (centAut j k : Equiv.Perm (Fin 24)) = centGen j k :=
  coe_centAut (decode_centGenArrs_mem hj (getD_mem_of_lt hk _))

theorem centGenArrs_zero_length : (centGenArrs 0).length = 2 := rfl

theorem closure_centAut_zero :
    Subgroup.closure (centAut 0 '' {k | k < (centGenArrs 0).length}) =
      Subgroup.centralizer {seedAut 0} := by
  have hA : bridgePA = pA := Equiv.ext (by decide +kernel)
  have hB : bridgePB = pB := Equiv.ext (by decide +kernel)
  have h0 : centAut 0 0 = pAAut := Subtype.ext (by
    rw [coe_centAut_eq (by norm_num) (by decide), centGen_zero_zero, hA]
    rfl)
  have h1 : centAut 0 1 = pBAut := Subtype.ext (by
    rw [coe_centAut_eq (by norm_num) (by decide), centGen_zero_one, hB]
    rfl)
  have himg : centAut 0 '' {k | k < (centGenArrs 0).length} = {pAAut, pBAut} := by
    rw [centGenArrs_zero_length]
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      · exact Or.inl h0
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, h0⟩
      · exact ⟨1, by norm_num, h1⟩
  rw [himg, closure_pAAut_pBAut, seedAut_zero]
  symm
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul]

theorem closure_centAut_of
    {j : ℕ} (hj : j = 1 ∨ j = 2) :
    Subgroup.closure (centAut j '' {k | k < (centGenArrs j).length}) =
      Subgroup.centralizer {seedAut j} := by
  have hj3 : j < 3 := by omega
  apply Subgroup.map_injective (Subgroup.subtype_injective AutPerm)
  rw [MonoidHom.map_closure]
  have himg : AutPerm.subtype '' (centAut j '' {k | k < (centGenArrs j).length}) =
      Set.range fun k : Fin 5 => centGen j k := by
    rw [Set.image_image, centGenArrs_length hj]
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subgroup.coe_subtype]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, (coe_centAut_eq hj3 (by rw [centGenArrs_length hj]; exact hk)).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, coe_centAut_eq hj3 (by rw [centGenArrs_length hj]; exact k.2)⟩
  have hcl : Subgroup.closure (Set.range fun k : Fin 5 => centGen j k) =
      AutPerm ⊓ Subgroup.centralizer {seedPerm j} := by
    rcases hj with rfl | rfl
    · exact closure_centGen_one
    · exact closure_centGen_two
  rw [himg, hcl]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_seedAut_eq hj3]; exact hc)
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨y.2, ?_⟩
    have := congrArg Subtype.val hy
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_seedAut_eq hj3] at this

theorem decode_comm
    {j : ℕ} (hj : j < 3) {a : Array ℕ} (ha : a ∈ centGenArrs j) :
    decode a * decode (seedA j) = decode (seedA j) * decode a := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | hj'
  · rw [decode_seedA, seedPerm_zero, mul_one, one_mul]
  · have hca := centGenArr_perm j hj a ha
    have hs : PermArr (seedArr.getD j #[]) = true := seedArr_perm _ (getD_mem_of_lt (by
      simp [seedArr]; omega) _)
    show decode a * decode (seedArr.getD j #[]) = decode (seedArr.getD j #[]) * decode a
    rw [← decode_amul hca hs, ← decode_amul hs hca,
      centGenArr_comm j (by rcases hj' with rfl | rfl <;> simp) a ha]

theorem seedHyp
    {j : ℕ} (hj : j < 3) : SeedHyp j where
  lt := hj
  seed_mem := seedPerm_mem hj
  cent_mem _ ha := decode_centGenArrs_mem hj ha
  sq := by
    rw [decode_seedA]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | hj'
    · rw [seedPerm_zero, mul_one]
    · exact seedPerm_sq hj'
  comm _ ha := decode_comm hj ha
  gen := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | hj'
    · exact closure_centAut_zero
    · exact closure_centAut_of hj'

theorem monoSeed_lt (i : ℕ) : monoSeed.getD i 0 < 3 := by
  by_cases hi : i < 7
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [monoSeed]; omega)]
    norm_num

@[expose] def monoPt (i : ℕ) : MonoSD := fibPt (monoSeed.getD i 0) (monoSign.getD i 0)

theorem monoSign_valid {i : ℕ} (hi : i < 7) :
    validB (monoSeed.getD i 0) (monoSign.getD i 0) = true := by
  have h := monoCert_ok i hi
  have := natCertOK_valid h (natCertOK_pos h)
  rwa [natCertOK_root h] at this

theorem mem_pts_iff {c : NatCert} {n : ℕ} :
    n ∈ c.pts.toList ↔ ∃ t < c.pts.size, c.pts[t]! = n := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, getElem!_pos c.pts t ht⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (getElem!_pos c.pts t ht).symm⟩

theorem monoSign_mem
    {i : ℕ} (hi : i < 7) : monoSign.getD i 0 ∈ (monoCert i).pts.toList := by
  have h := monoCert_ok i hi
  exact mem_pts_iff.2 ⟨0, natCertOK_pos h, natCertOK_root h⟩

theorem monoPt_mem_fibre
    {i : ℕ} (hi : i < 7) :
    monoPt i ∈ fibre (seedAut (monoSeed.getD i 0)) := by
  have hv := monoSign_valid hi
  exact (fibPt_mem_fibre_iff (seedHyp (monoSeed_lt i)) (mem_validList_of_validB hv)).2
    (eligB_of_validB hv)

theorem conj_mul_self {G : Type*} [Group G] (g y : G) (hy : y * y = 1) :
    g * y * g⁻¹ * (g * y * g⁻¹) = 1 := by
  calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    _ = 1 := by rw [hy]; group

theorem conj_right (g y : MonoSD) : (g * y * g⁻¹).right = g.right * y.right * g.right⁻¹ := by
  simp

theorem conj_fibre_iff
    {j : ℕ} (hj : j < 3) (y : MonoSD) :
    (∀ x ∈ fibre (seedAut j), y * x * y⁻¹ ∈ fibre (seedAut j)) ↔ y ∈ fibreStab (seedAut j) := by
  rw [mem_fibreStab]
  constructor
  · intro h
    have hx : (SemidirectProduct.inr (seedAut j) : MonoSD) ∈ fibre (seedAut j) := by
      refine ⟨SemidirectProduct.right_inr _, ?_⟩
      rw [← map_mul, (seedHyp hj).seed_sq, map_one]
    have := (h _ hx).1
    rw [conj_right, SemidirectProduct.right_inr] at this
    calc y.right * seedAut j = y.right * seedAut j * y.right⁻¹ * y.right := by group
      _ = seedAut j * y.right := by rw [this]
  · rintro hc x ⟨hxr, hxx⟩
    refine ⟨?_, conj_mul_self y x hxx⟩
    rw [conj_right, hxr, hc]
    group

theorem conjOrbit_subset_fibre
    {i : ℕ} (hi : i < 7) :
    conjOrbit (seedAut (monoSeed.getD i 0)) (monoPt i) ⊆ fibre (seedAut (monoSeed.getD i 0)) := by
  rintro _ ⟨g, hg, rfl⟩
  exact (conj_fibre_iff (monoSeed_lt i) g).2 hg _ (monoPt_mem_fibre hi)

theorem mem_conjOrbit_iff
    {i : ℕ} (hi : i < 7) {z : MonoSD} :
    z ∈ conjOrbit (seedAut (monoSeed.getD i 0)) (monoPt i) ↔
      ∃ n ∈ (monoCert i).pts.toList, fibPt (monoSeed.getD i 0) n = z := by
  rw [monoPt, conjOrbit_eq hi (seedHyp (monoSeed_lt i))]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, mem_pts_iff.2 ⟨t, ht, rfl⟩, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_pts_iff.1 hn
    exact ⟨t, ht, rfl⟩

theorem valid_of_mem_pts
    {i : ℕ} (hi : i < 7) {n : ℕ} (hn : n ∈ (monoCert i).pts.toList) :
    validB (monoSeed.getD i 0) n = true := by
  obtain ⟨t, ht, rfl⟩ := mem_pts_iff.1 hn
  exact natCertOK_valid (monoCert_ok i hi) ht

theorem fibre_eq_iUnion
    {j : ℕ} (hj : j < 3) :
    fibre (seedAut j) = ⋃ i ∈ {i | i < 7 ∧ monoSeed.getD i 0 = j},
      conjOrbit (seedAut j) (monoPt i) := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · intro hy
    rw [fibre_eq (seedHyp hj)] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    rw [Set.mem_ofPred_eq] at hn
    obtain ⟨i, hi, hs, hni⟩ := (mem_eligList_iff hj).1 hn
    subst hs
    exact ⟨i, ⟨hi, rfl⟩, (mem_conjOrbit_iff hi).2 ⟨n, hni, rfl⟩⟩
  · rintro ⟨i, ⟨hi, rfl⟩, hy⟩
    exact conjOrbit_subset_fibre hi hy

theorem conjOrbit_disjoint
    {i k : ℕ} (hi : i < 7) (hk : k < 7)
    (hs : monoSeed.getD i 0 = monoSeed.getD k 0) (hne : i ≠ k) :
    Disjoint (conjOrbit (seedAut (monoSeed.getD i 0)) (monoPt i))
      (conjOrbit (seedAut (monoSeed.getD k 0)) (monoPt k)) := by
  rw [Set.disjoint_left]
  intro z hzi hzk
  obtain ⟨n, hn, rfl⟩ := (mem_conjOrbit_iff hi).1 hzi
  obtain ⟨m, hm, e⟩ := (mem_conjOrbit_iff hk).1 hzk
  rw [← hs] at e
  have hvm : validB (monoSeed.getD i 0) m = true := by
    rw [hs]
    exact valid_of_mem_pts hk hm
  have := fibPt_inj hvm (valid_of_mem_pts hi hn) e
  subst this
  exact monoCert_disjoint (monoSeed_lt i) hi hk rfl hs.symm hne hn hm

theorem exists_conj_mem_fibre
    {y : MonoSD} (hy : y * y = 1) :
    ∃ j < 3, ∃ g : MonoSD, g * y * g⁻¹ ∈ fibre (seedAut j) := by
  have hr : y.right * y.right = 1 := by
    have := congrArg SemidirectProduct.right hy
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at this
  by_cases h1 : y.right = 1
  · refine ⟨0, by norm_num, 1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact ⟨by rw [h1, seedAut_zero], hy⟩
  · have hrr : (y.right : Equiv.Perm (Fin 24)) * y.right = 1 := by
      have := congrArg Subtype.val hr
      rwa [Subgroup.coe_mul] at this
    have hmem := involution_mem_conjClass y.right.2 hrr (fun h => h1 (Subtype.ext h))
    have key : ∀ j, j = 1 ∨ j = 2 → y.right.1 ∈ conjClass (seedPerm j) →
        ∃ g : MonoSD, g * y * g⁻¹ ∈ fibre (seedAut j) := by
      rintro j hj ⟨g, hg, hgy⟩
      refine ⟨SemidirectProduct.inr (⟨g, hg⟩ : AutPerm)⁻¹, ?_, conj_mul_self _ y hy⟩
      rw [conj_right, SemidirectProduct.right_inr]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, inv_inv, Subgroup.coe_inv,
        coe_seedAut_eq (by omega), ← hgy]
      group
    rcases hmem with hm | hm
    · exact ⟨1, by norm_num, key 1 (Or.inl rfl) hm⟩
    · exact ⟨2, by norm_num, key 2 (Or.inr rfl) hm⟩

theorem exists_conj_monoPt
    {y : MonoSD} (hy : y * y = 1) :
    ∃ i < 7, ∃ g : MonoSD, g * monoPt i * g⁻¹ = y := by
  obtain ⟨j, hj, g, hg⟩ := exists_conj_mem_fibre hy
  rw [fibre_eq_iUnion hj] at hg
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hg
  obtain ⟨i, ⟨hi, rfl⟩, h, hh, e⟩ := hg
  refine ⟨i, hi, g⁻¹ * h, ?_⟩
  calc g⁻¹ * h * monoPt i * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * monoPt i * h⁻¹) * g := by group
    _ = y := by rw [e]; group

theorem fixCount_seedPerm {j : ℕ} (hj : j < 3) : fixCount (seedPerm j) = [24, 8, 0].getD j 0 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · rw [seedPerm_zero, fixCount_one]
    rfl
  · rw [fixCount_seed_one]
    rfl
  · rw [fixCount_seed_two]
    rfl

theorem monoPt_conj_eq
    {i k : ℕ} (hi : i < 7) (hk : k < 7) {g : MonoSD}
    (hg : g * monoPt i * g⁻¹ = monoPt k) : i = k := by
  have hr := congrArg SemidirectProduct.right hg
  rw [conj_right] at hr
  have hji := monoSeed_lt i
  have hjk := monoSeed_lt k
  have hs : monoSeed.getD i 0 = monoSeed.getD k 0 := by
    have hf : fixCount ((g.right * seedAut (monoSeed.getD i 0) * g.right⁻¹ : AutPerm) :
        Equiv.Perm (Fin 24)) = fixCount ((seedAut (monoSeed.getD k 0) : AutPerm) :
        Equiv.Perm (Fin 24)) :=
      congrArg (fun x : AutPerm => fixCount (x : Equiv.Perm (Fin 24))) hr
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, fixCount_conj, coe_seedAut_eq hji,
      coe_seedAut_eq hjk, fixCount_seedPerm hji, fixCount_seedPerm hjk] at hf
    generalize monoSeed.getD i 0 = a at hf hji ⊢
    generalize monoSeed.getD k 0 = b at hf hjk ⊢
    interval_cases a <;> interval_cases b <;> first | rfl | exact absurd hf (by decide)
  have hc : g.right * seedAut (monoSeed.getD i 0) = seedAut (monoSeed.getD i 0) * g.right := by
    have hr' : g.right * seedAut (monoSeed.getD i 0) * g.right⁻¹ =
        seedAut (monoSeed.getD i 0) := by
      have hr0 : g.right * seedAut (monoSeed.getD i 0) * g.right⁻¹ =
          seedAut (monoSeed.getD k 0) := hr
      rw [← hs] at hr0
      exact hr0
    calc g.right * seedAut (monoSeed.getD i 0)
        = g.right * seedAut (monoSeed.getD i 0) * g.right⁻¹ * g.right := by group
      _ = seedAut (monoSeed.getD i 0) * g.right := by rw [hr']
  have hk' : monoPt k ∈ conjOrbit (seedAut (monoSeed.getD i 0)) (monoPt i) :=
    ⟨g, mem_fibreStab.2 hc, hg⟩
  by_contra hne
  have hk'' : monoPt k ∈ conjOrbit (seedAut (monoSeed.getD k 0)) (monoPt k) :=
    ⟨1, Subgroup.one_mem _, by group⟩
  exact Set.disjoint_left.1 (conjOrbit_disjoint hi hk hs hne) hk' hk''

theorem codeCls_zero : codeCls 0 = 0 := by
  have h0 : bvec 24 0 ∈ C := by
    rw [bvec_zero]
    exact C.zero_mem
  rw [codeCls_eq_zero_iff (by norm_num) h0]
  exact Or.inl rfl

theorem monoPt_zero : monoPt 0 = 1 := by
  refine SemidirectProduct.ext ?_ ?_
  · show Multiplicative.ofAdd (codeCls 0) = 1
    rw [codeCls_zero]
    rfl
  · exact seedAut_zero

theorem monoPt_ne_one
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 7) : monoPt i ≠ 1 := by
  intro h
  have hl : Multiplicative.ofAdd (codeCls (monoSign.getD i 0)) = 1 :=
    congrArg SemidirectProduct.left h
  have hr : seedAut (monoSeed.getD i 0) = 1 := congrArg SemidirectProduct.right h
  have hv := monoSign_valid hi
  have hC := bvec_mem_of_mem_validList (mem_validList_of_validB hv)
  have hlt : monoSign.getD i 0 < 2 ^ 24 :=
    lt_trans (validList_spec.2.2 _ (mem_validList_of_validB hv)).1 (by norm_num)
  have hz : codeCls (monoSign.getD i 0) = 0 := by
    have := congrArg Multiplicative.toAdd hl
    simpa using this
  rw [codeCls_eq_zero_iff hlt hC] at hz
  have hp : seedPerm (monoSeed.getD i 0) = 1 := by
    rw [← coe_seedAut_eq (monoSeed_lt i), hr]
    rfl
  interval_cases i
  · revert hz
    decide
  · revert hz
    decide
  · exact seedPerm_ne_one (Or.inl rfl) hp
  · exact seedPerm_ne_one (Or.inl rfl) hp
  · exact seedPerm_ne_one (Or.inr rfl) hp
  · exact seedPerm_ne_one (Or.inr rfl) hp

theorem ncard_eligible
    {j : ℕ} (hj : j < 3) :
    {x : C ⧸ ΩLine | (⟨Multiplicative.ofAdd x, seedAut j⟩ : MonoSD) *
        ⟨Multiplicative.ofAdd x, seedAut j⟩ = 1}.ncard = [2048, 128, 64].getD j 0 := by
  have himg : (fun x : C ⧸ ΩLine => (⟨Multiplicative.ofAdd x, seedAut j⟩ : MonoSD)) ''
      {x | (⟨Multiplicative.ofAdd x, seedAut j⟩ : MonoSD) *
        ⟨Multiplicative.ofAdd x, seedAut j⟩ = 1} = fibre (seedAut j) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨rfl, hx⟩
    · rintro ⟨hr, hy⟩
      refine ⟨Multiplicative.toAdd y.left, ?_, SemidirectProduct.ext rfl hr.symm⟩
      have e : (⟨Multiplicative.ofAdd (Multiplicative.toAdd y.left), seedAut j⟩ : MonoSD) = y :=
        SemidirectProduct.ext rfl hr.symm
      rw [Set.mem_ofPred_eq, e]
      exact hy
  have hinj : Set.InjOn (fun x : C ⧸ ΩLine => (⟨Multiplicative.ofAdd x, seedAut j⟩ : MonoSD))
      {x | (⟨Multiplicative.ofAdd x, seedAut j⟩ : MonoSD) *
        ⟨Multiplicative.ofAdd x, seedAut j⟩ = 1} := fun a _ b _ e =>
    Multiplicative.ofAdd.injective (congrArg SemidirectProduct.left e)
  rw [← hinj.ncard_image, himg, fibre_eq (seedHyp hj),
    Set.InjOn.ncard_image (fun a ha b hb e => fibPt_inj
      (by rw [Set.mem_ofPred_eq, eligList, List.mem_filter] at ha
          simp only [validB, Bool.and_eq_true]
          exact ⟨by simpa using ha.1, ha.2⟩)
      (by rw [Set.mem_ofPred_eq, eligList, List.mem_filter] at hb
          simp only [validB, Bool.and_eq_true]
          exact ⟨by simpa using hb.1, hb.2⟩) e),
    show {n | n ∈ eligList j} = ((eligList j).toFinset : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup (eligList_nodup j), eligList_length j hj]

theorem monoWord_mem
    (i : ℕ) : monoWord i ∈ C := by
  by_cases hi : i < 7
  · exact bvec_mem_of_mem_validList (mem_validList_of_validB (monoSign_valid hi))
  · have h0 : monoSign.getD i 0 = 0 := List.getD_eq_default _ _ (by simp [monoSign]; omega)
    rw [monoWord, h0, bvec_zero]
    exact C.zero_mem

@[expose] def monoAO
    (i : ℕ) : latticeO :=
  gO ⟨monoWord i, monoWord_mem i⟩ * PO (seedAut (monoSeed.getD i 0))

theorem mat_monoAO
    (i : ℕ) : mat (monoAO i) = monoA i := by
  rw [monoAO, mat_mul, mat_gO, mat_PO, monoA, coe_seedAut_eq (monoSeed_lt i)]
  rfl

@[expose] def monoN
    (i : ℕ) : GLV := modTwoUnit (monoAO i)

theorem monoN_eq
    {i : ℕ} (hi : i < 7) : monoN i = monoHom (monoPt i) := by
  have hmem := monoPt_mem_fibre hi
  have hca : codeCls (monoSign.getD i 0) =
      Submodule.Quotient.mk (⟨monoWord i, monoWord_mem i⟩ : C) :=
    codeCls_of_mem (n := monoSign.getD i 0) (monoWord_mem i)
  have he := ((mul_self_eq_one_iff (codeCls (monoSign.getD i 0))
    (seedAut (monoSeed.getD i 0))).1 hmem.2).2
  rw [hca] at he
  have hpa : permQ (seedAut (monoSeed.getD i 0))
      (Submodule.Quotient.mk (⟨monoWord i, monoWord_mem i⟩ : C)) =
      Submodule.Quotient.mk (⟨monoWord i, monoWord_mem i⟩ : C) := by
    rw [eq_neg_of_add_eq_zero_right he, ZModModule.neg_eq_self]
  rw [monoN, monoAO, gO_mul_PO, ← monoHom_mk, ← permQ_mk, hpa, monoPt, fibPt, hca]

theorem monoN_mem
    {i : ℕ} (hi : i < 7) : monoN i ∈ Nvis := by
  rw [Nvis_eq_range_monoHom, monoN_eq hi]
  exact ⟨_, rfl⟩

theorem exists_conj_monoN
    {u : GLV} (hu : u ∈ Nvis) (huu : u * u = 1) :
    ∃ i < 7, ∃ g ∈ Nvis, g * monoN i * g⁻¹ = u := by
  rw [Nvis_eq_range_monoHom] at hu
  obtain ⟨y, rfl⟩ := hu
  have hyy : y * y = 1 := monoHom_injective (by rw [map_mul, huu, map_one])
  obtain ⟨i, hi, g, hg⟩ := exists_conj_monoPt hyy
  refine ⟨i, hi, monoHom g, by rw [Nvis_eq_range_monoHom]; exact ⟨g, rfl⟩, ?_⟩
  rw [monoN_eq hi, ← map_inv, ← map_mul, ← map_mul, hg]

theorem monoN_conj_eq
    {i k : ℕ} (hi : i < 7) (hk : k < 7) {g : GLV} (hg : g ∈ Nvis)
    (h : g * monoN i * g⁻¹ = monoN k) : i = k := by
  rw [Nvis_eq_range_monoHom] at hg
  obtain ⟨g', rfl⟩ := hg
  rw [monoN_eq hi, monoN_eq hk, ← map_inv, ← map_mul, ← map_mul] at h
  exact monoPt_conj_eq hi hk (monoHom_injective h)

theorem ncard_conjOrbitN
    {i : ℕ} (hi : i < 7) :
    {u | ∃ g ∈ (fibreStab (seedAut (monoSeed.getD i 0))).map monoHom,
      g * monoN i * g⁻¹ = u}.ncard = [1, 759, 1288, 16, 112, 32, 32].getD i 0 := by
  have himg : {u | ∃ g ∈ (fibreStab (seedAut (monoSeed.getD i 0))).map monoHom,
      g * monoN i * g⁻¹ = u} =
      monoHom '' conjOrbit (seedAut (monoSeed.getD i 0)) (monoPt i) := by
    ext u
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g * monoPt i * g⁻¹, ⟨g, hg, rfl⟩, by rw [monoN_eq hi, map_mul, map_mul, map_inv]⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨monoHom g, ⟨g, hg, rfl⟩, by rw [monoN_eq hi, map_mul, map_mul, map_inv]⟩
  rw [himg, Set.InjOn.ncard_image monoHom_injective.injOn, monoPt,
    ncard_conjOrbit hi (seedHyp (monoSeed_lt i)), monoCert_size i hi]

theorem ncard_eligible_signs
    {j : ℕ} (hj : j < 3) :
    {x : C ⧸ ΩLine | x + permQ (seedAut j) x = 0}.ncard = [2048, 128, 64].getD j 0 := by
  rw [← ncard_eligible hj]
  congr 1
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, mul_self_eq_one_iff]
  exact ⟨fun h => ⟨(seedHyp hj).seed_sq, h⟩, fun h => h.2⟩

theorem monomial_involution_classes :
    (∀ i, mat (monoAO i) = monoA i) ∧
    Nvis = monoHom.range ∧ Function.Injective monoHom ∧
    (∀ i < 7, monoN i = monoHom (monoPt i)) ∧
    (∀ i < 7, monoN i ∈ Nvis) ∧ monoN 0 = 1 ∧
    (∀ i, 1 ≤ i → i < 7 → monoN i ≠ 1 ∧ monoN i * monoN i = 1) ∧
    (∀ u ∈ Nvis, u * u = 1 → ∃ i < 7, ∃ g ∈ Nvis, g * monoN i * g⁻¹ = u) ∧
    (∀ i < 7, ∀ k < 7, (∃ g ∈ Nvis, g * monoN i * g⁻¹ = monoN k) → i = k) ∧
    (∀ j < 3, (seedAut j : Equiv.Perm (Fin 24)) = seedPerm j) ∧
    (∀ j < 3, {x : C ⧸ ΩLine | x + permQ (seedAut j) x = 0}.ncard = [2048, 128, 64].getD j 0) ∧
    (∀ j < 3, ∀ y : MonoSD,
      (∀ x ∈ fibre (seedAut j), y * x * y⁻¹ ∈ fibre (seedAut j)) ↔ y ∈ fibreStab (seedAut j)) ∧
    (∀ j < 3, fibre (seedAut j) = ⋃ i ∈ {i | i < 7 ∧ monoSeed.getD i 0 = j},
      conjOrbit (seedAut j) (monoPt i)) ∧
    (∀ i < 7, ∀ k < 7, monoSeed.getD i 0 = monoSeed.getD k 0 → i ≠ k →
      Disjoint (conjOrbit (seedAut (monoSeed.getD i 0)) (monoPt i))
        (conjOrbit (seedAut (monoSeed.getD k 0)) (monoPt k))) ∧
    (∀ i < 7, (conjOrbit (seedAut (monoSeed.getD i 0)) (monoPt i)).ncard =
      [1, 759, 1288, 16, 112, 32, 32].getD i 0) ∧
    (∀ i < 7, {u | ∃ g ∈ (fibreStab (seedAut (monoSeed.getD i 0))).map monoHom,
      g * monoN i * g⁻¹ = u}.ncard = [1, 759, 1288, 16, 112, 32, 32].getD i 0) := by
  refine ⟨mat_monoAO, Nvis_eq_range_monoHom, monoHom_injective, fun i hi => monoN_eq hi,
    fun i hi => monoN_mem hi, ?_, fun i hi1 hi => ⟨?_, ?_⟩,
    fun u hu huu => exists_conj_monoN hu huu,
    fun i hi k hk ⟨g, hg, h⟩ => monoN_conj_eq hi hk hg h, fun j hj => coe_seedAut_eq hj,
    fun j hj => ncard_eligible_signs hj, fun j hj y => conj_fibre_iff hj y,
    fun j hj => fibre_eq_iUnion hj, fun i hi k hk hs hne => conjOrbit_disjoint hi hk hs hne,
    fun i hi => ?_, fun i hi => ncard_conjOrbitN hi⟩
  · rw [monoN_eq (by norm_num), monoPt_zero, map_one]
  · rw [monoN_eq hi]
    exact fun h => monoPt_ne_one hi1 hi (monoHom_injective (h.trans (map_one _).symm))
  · rw [monoN_eq hi, ← map_mul, (monoPt_mem_fibre hi).2, map_one]
  · rw [monoPt, ncard_conjOrbit hi (seedHyp (monoSeed_lt i)), monoCert_size i hi]

end CFSG.Monster.B.TwoA.Census
