module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16t_ten_rank_comm_pow {p n : ℕ} {P : Type} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp


private theorem s16t_ten_fix_of_conj_eq {ι : Type} {Y : ι → Subgroup T} {s : ι}
    (hT : ∀ t : T, t ^ 2 = 1) (hcardY : Nat.card ↥(Y s) = 4) {a c : MulAut T}
    (ha3 : a ^ 3 = 1) (hc2 : c ^ 2 = 1) (haY : (Y s).map a.toMonoidHom = Y s)
    (hcY : (Y s).map c.toMonoidHom = Y s) (hca : c * a = a * c)
    (hcs : ∃ y ∈ Y s, c y ≠ y) : a ∈ centSub (Y s) := by
  classical
  obtain ⟨y, hy, hcyne⟩ := hcs
  have haY_mem : ∀ v ∈ Y s, a v ∈ Y s := by
    intro v hv
    have : a v ∈ (Y s).map a.toMonoidHom := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [haY] at this
  have hcY_mem : ∀ v ∈ Y s, c v ∈ Y s := by
    intro v hv
    have : c v ∈ (Y s).map c.toMonoidHom := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [hcY] at this
  have hca_apply : ∀ v : T, c (a v) = a (c v) := by
    intro v
    have := congrArg (fun f : MulAut T => f v) hca
    simpa [MulAut.mul_apply] using this
  have hcc : c (c y) = y := by
    have := congrArg (fun f : MulAut T => f y) hc2
    simpa [pow_two, MulAut.mul_apply] using this
  have hy1 : y ≠ 1 := by
    intro h
    exact hcyne (by rw [h]; simp)
  have hcy1 : c y ≠ 1 := by
    intro h
    apply hy1
    have := congrArg c h
    rwa [hcc, map_one] at this
  set z : T := y * c y with hzdef
  have hcy_mem : c y ∈ Y s := hcY_mem y hy
  have hz_mem : z ∈ Y s := by rw [hzdef]; exact (Y s).mul_mem hy hcy_mem
  have hcz : c z = z := by
    rw [hzdef, map_mul, hcc, mul_comm]
  have hz1 : z ≠ 1 := by
    intro h
    have h2 : y * y = 1 := by simpa [pow_two] using hT y
    have h1 : z * y = y := by rw [h]; simp
    have h3 : z * y = c y := by
      rw [hzdef]
      calc (y * c y) * y = c y * (y * y) := by ac_rfl
        _ = c y * 1 := by rw [h2]
        _ = c y := by rw [mul_one]
    exact hcyne (h3 ▸ h1)
  have hzy : z ≠ y := by
    intro h
    apply hcy1
    have h1 : y * c y = y * 1 := by rw [← hzdef, h, mul_one]
    exact mul_left_cancel h1
  have hzcy : z ≠ c y := by
    intro h
    apply hy1
    have h1 : y * c y = 1 * c y := by rw [← hzdef, h, one_mul]
    exact mul_right_cancel h1
  have hS_card : ({1, y, c y, z} : Set T).ncard = 4 := by
    have h1 : (1 : T) ∉ ({y, c y, z} : Set T) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hy1.symm, hcy1.symm, hz1.symm⟩
    have h2 : y ∉ ({c y, z} : Set T) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hcyne.symm, hzy.symm⟩
    have h3 : c y ∉ ({z} : Set T) := by
      simpa using hzcy.symm
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hYs_card : (Y s : Set T).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcardY
  have hsub : ({1, y, c y, z} : Set T) ⊆ (Y s : Set T) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (Y s).one_mem
    · exact hy
    · exact hcy_mem
    · exact hz_mem
  have hS_eq : ({1, y, c y, z} : Set T) = (Y s : Set T) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hYs_card, hS_card])
  have hfix_eq : ∀ w ∈ Y s, c w = w → w = 1 ∨ w = z := by
    intro w hw hcw
    have hwS : w ∈ ({1, y, c y, z} : Set T) := by rw [hS_eq]; exact hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwS
    rcases hwS with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hcw hcyne
    · exact absurd (hcw.symm.trans hcc) hcyne
    · exact Or.inr rfl
  have haz : a z = z := by
    have haz_mem : a z ∈ Y s := haY_mem z hz_mem
    have haz_fix : c (a z) = a z := by rw [hca_apply, hcz]
    have haz1 : a z ≠ 1 := by
      intro h
      apply hz1
      exact a.injective (by rw [h, map_one])
    rcases hfix_eq (a z) haz_mem haz_fix with h | h
    · exact absurd h haz1
    · exact h
  have hay1 : a y ≠ 1 := by
    intro h
    apply hy1
    exact a.injective (by rw [h, map_one])
  have hayz : a y ≠ z := by
    intro h
    have hfix : c (a y) = a y := by rw [h, hcz]
    have h2 : c (a y) = a (c y) := hca_apply y
    rw [h2] at hfix
    exact hcyne (a.injective hfix)
  have hay : a y = y := by
    have hay_mem : a y ∈ Y s := haY_mem y hy
    have hayS : a y ∈ ({1, y, c y, z} : Set T) := by rw [hS_eq]; exact hay_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hayS
    rcases hayS with h | h | h | h
    · exact absurd h hay1
    · exact h
    · exfalso
      have h3 : a (a y) = y := by
        rw [h]
        calc a (c y) = c (a y) := (hca_apply y).symm
          _ = c (c y) := by rw [h]
          _ = y := hcc
      have h9 : (a ^ 3) y = a (a (a y)) := by
        rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
      have h8 : (a ^ 3) y = y := by
        have := congrArg (fun f : MulAut T => f y) ha3
        simpa using this
      rw [h9] at h8
      have h11 : a (a (a y)) = a y := by rw [h3]
      rw [h11] at h8
      exact hcyne (h ▸ h8)
    · exact absurd h hayz
  refine mem_centSub.mpr ?_
  intro w hw
  have hwS : w ∈ ({1, y, c y, z} : Set T) := by rw [hS_eq]; exact hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwS
  rcases hwS with rfl | rfl | rfl | rfl
  · exact map_one a
  · exact hay
  · rw [← hca_apply y, hay]
  · exact haz


private theorem s16t_ten_phi_fix {ι : Type} {A : Subgroup (MulAut T)} {Y : ι → Subgroup T}
    (hAY : ∀ a ∈ A, ∀ s, (Y s).map a.toMonoidHom = Y s) {c : MulAut T} {a : ↥A} {s : ι}
    (hcl : ∀ v ∈ Y s, c v = v) :
    ((a : MulAut T)⁻¹ * (c * (a : MulAut T) * c⁻¹)) ∈ centSub (Y s) := by
  rw [mem_centSub]
  intro v hv
  have hcv : c v = v := hcl v hv
  have hcvi : c⁻¹ v = v := by
    change c.symm v = v
    exact (Equiv.symm_apply_eq c.toEquiv).2 hcv.symm
  have hav : (a : MulAut T) v ∈ Y s := by
    have : (a : MulAut T) v ∈ (Y s).map (a : MulAut T).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [hAY a a.2 s] at this
  show ((a : MulAut T)⁻¹ * (c * (a : MulAut T) * c⁻¹)) v = v
  simp only [MulAut.mul_apply, hcvi]
  rw [show c ((a : MulAut T) v) = (a : MulAut T) v from hcl _ hav]
  simp


theorem s16t_ten_false_of_involution_on_two (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} [Fintype ι]
    {Y : ι → Subgroup T} {X A : Subgroup (MulAut T)} (hY : S16tTenBlocks X A Y 3)
    (hA : IsElemAbelianOfRank 3 3 ↥A) (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A)
    {c : MulAut T} (hcX : c ∈ X) (hc2 : c ^ 2 = 1) (hcY : ∀ s, (Y s).map c.toMonoidHom = Y s)
    {i j l m : ι} (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m)
    (hlm : l ≠ m) (hci : ∃ y ∈ Y i, c y ≠ y) (hcj : ∃ y ∈ Y j, c y ≠ y)
    (hcl : ∀ y ∈ Y l, c y = y) (hcm : ∀ y ∈ Y m, c y = y) : False := by
  classical
  have hAc := s16t_ten_rank_comm_pow hA
  have hAcomm : ∀ a b : ↥A, a * b = b * a := hAc.1
  have hApow : ∀ a : ↥A, a ^ 3 = 1 := hAc.2
  have hAcard : Nat.card ↥A = 27 := by
    have h := s16c167_card_isElemAbelianOfRank hA
    norm_num at h
    exact h
  have hAY : ∀ a ∈ A, ∀ s, (Y s).map a.toMonoidHom = Y s := hY.norm
  have hcardY : ∀ s : ι, Nat.card ↥(Y s) = 4 := by
    intro s
    rw [card_eq_two_pow hT (Y s), hY.blocks.rank s, s16c1610_dParam_three]
    norm_num
  have hAs_card : ∀ s : ι, Nat.card ↥(A ⊓ centSub (Y s)) = 9 := fun s =>
    (hY.card_ker s).trans (by norm_num)
  have hAs_inf : ∀ s s' : ι, s ≠ s' →
      Nat.card ↥((A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s'))) ≤ 3 := by
    intro s s' hss'
    have h := hY.card_inf_ker s s' hss'
    omega
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hAcomm }
  let conj : ↥A →* ↥A :=
    { toFun := fun a => ⟨c * (a : MulAut T) * c⁻¹, hAn c hcX a.1 a.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show c * ((a * b : ↥A) : MulAut T) * c⁻¹ =
          (c * (a : MulAut T) * c⁻¹) * (c * (b : MulAut T) * c⁻¹)
        rw [show ((a * b : ↥A) : MulAut T) = (a : MulAut T) * (b : MulAut T) from rfl]
        group }
  let φ : ↥A →* ↥A := invMonoidHom * conj
  have hφ_apply : ∀ a : ↥A, φ a = (a : ↥A)⁻¹ * conj a := fun a => rfl
  have hφ_val : ∀ a : ↥A, (φ a : MulAut T) =
      (a : MulAut T)⁻¹ * (c * (a : MulAut T) * c⁻¹) := by
    intro a
    rw [hφ_apply]
    rfl
  have hker_fix : ∀ (s : ι), (∃ y ∈ Y s, c y ≠ y) → ∀ b : ↥A, b ∈ φ.ker →
      (b : MulAut T) ∈ A ⊓ centSub (Y s) := by
    intro s hcs b hb
    have hb1 : φ b = 1 := MonoidHom.mem_ker.mp hb
    have hb2 : conj b = b := by
      have h1 : (b : ↥A)⁻¹ * conj b = 1 := by rw [← hφ_apply]; exact hb1
      have := congrArg (fun x : ↥A => (b : ↥A) * x) h1
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at this
      exact this
    have hconj : c * (b : MulAut T) * c⁻¹ = (b : MulAut T) := congrArg Subtype.val hb2
    have hca : c * (b : MulAut T) = (b : MulAut T) * c := by
      calc c * (b : MulAut T) = (c * (b : MulAut T) * c⁻¹) * c := by group
        _ = (b : MulAut T) * c := by rw [hconj]
    have hb3 : (b : MulAut T) ^ 3 = 1 := by
      simpa using congrArg Subtype.val (hApow b)
    refine ⟨b.2, ?_⟩
    exact s16t_ten_fix_of_conj_eq (Y := Y) (s := s) (a := (b : MulAut T)) hT (hcardY s)
      hb3 hc2 (hAY b b.2 s) (hcY s) hca hcs
  have hKle : φ.ker.map A.subtype ≤ (A ⊓ centSub (Y i)) ⊓ (A ⊓ centSub (Y j)) := by
    rintro x ⟨b, hb, rfl⟩
    exact ⟨hker_fix i hci b hb, hker_fix j hcj b hb⟩
  have himage_fix : ∀ (s : ι), (∀ y ∈ Y s, c y = y) → ∀ a : ↥A,
      (φ a : MulAut T) ∈ A ⊓ centSub (Y s) := by
    intro s hcl' a
    refine ⟨(φ a).2, ?_⟩
    rw [hφ_val a]
    exact s16t_ten_phi_fix (A := A) (Y := Y) hAY hcl'
  have hRangeLe : φ.range.map A.subtype ≤ (A ⊓ centSub (Y l)) ⊓ (A ⊓ centSub (Y m)) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨himage_fix l hcl a, himage_fix m hcm a⟩
  have hKcard : Nat.card φ.ker ≤ 3 := by
    have h1 : Nat.card (φ.ker.map A.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h2 : Nat.card (φ.ker.map A.subtype) ≤
        Nat.card ↥((A ⊓ centSub (Y i)) ⊓ (A ⊓ centSub (Y j))) :=
      Subgroup.card_le_of_le hKle
    have h3 := hAs_inf i j hij
    omega
  have hRcard : Nat.card φ.range ≤ 3 := by
    have h1 : Nat.card (φ.range.map A.subtype) = Nat.card φ.range :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h2 : Nat.card (φ.range.map A.subtype) ≤
        Nat.card ↥((A ⊓ centSub (Y l)) ⊓ (A ⊓ centSub (Y m))) :=
      Subgroup.card_le_of_le hRangeLe
    have h3 := hAs_inf l m hlm
    omega
  have hker_card := Subgroup.card_ker_mul_card_range φ
  have h9 : 9 ≤ Nat.card φ.ker := by
    have h1 : Nat.card φ.ker * Nat.card φ.range = 27 := by
      rw [hker_card, hAcard]
    have h2 : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 3 :=
      Nat.mul_le_mul_left _ hRcard
    rw [h1] at h2
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
