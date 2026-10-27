module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16c1610_decomp_unique {A B : Subgroup T} (hd : Disjoint A B)
    {u u' : T} (hu : u ∈ A) (hu' : u' ∈ A) {v v' : T} (hv : v ∈ B) (hv' : v' ∈ B)
    (h : u * v = u' * v') : u = u' ∧ v = v' := by
  have hkey : u⁻¹ * u' = v * v'⁻¹ := by
    calc u⁻¹ * u' = u⁻¹ * u' * (v' * v'⁻¹) := by group
      _ = u⁻¹ * (u' * v') * v'⁻¹ := by group
      _ = u⁻¹ * (u * v) * v'⁻¹ := by rw [← h]
      _ = v * v'⁻¹ := by group
  have hmem : u⁻¹ * u' ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem hu) hu', by rw [hkey]; exact B.mul_mem hv (B.inv_mem hv')⟩
  rw [hd.eq_bot, Subgroup.mem_bot] at hmem
  have hu_eq : u = u' := inv_mul_eq_one.1 hmem
  refine ⟨hu_eq, ?_⟩
  have hv_eq : v * v'⁻¹ = 1 := by rw [← hkey, hu_eq]; exact inv_mul_cancel u'
  exact mul_inv_eq_one.1 hv_eq

private theorem s16c1610_rk_add_one_le_of_lt {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {H K : Subgroup V} (h : H < K) : rk ↥H + 1 ≤ rk ↥K := by
  have hle : rk ↥H ≤ rk ↥K := rk_mono h.le
  have hne : rk ↥H ≠ rk ↥K := by
    intro heq
    exact h.ne (eq_of_le_of_rk_le hV h.le (le_of_eq heq.symm))
  omega

theorem s16c1610_fix_complement_of_four (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} [Fintype ι]
    {Y : ι → Subgroup T} {X B : Subgroup (MulAut T)} (hY : SymSumFamily X Y 3 2) (hBX : B ≤ X)
    (hB : IsElemAbelian2 B) {i j : ι} (hij : i ≠ j) {b c : MulAut T} (hb : b ∈ B) (hc : c ∈ B)
    (horb : ∀ b' ∈ B, (Y i).map b'.toMonoidHom = Y i ∨ (Y i).map b'.toMonoidHom = Y j)
    (hbij : (Y i).map b.toMonoidHom = Y j) (hci : (Y i).map c.toMonoidHom = Y i)
    (hcy : ∃ y ∈ Y i, c y ≠ y) (hA5 : rkIdx (fixV B) ≤ 3) :
    ∀ l, l ≠ i → l ≠ j → ∀ y ∈ Y l, ∀ b' ∈ B, b' y = y := by
  classical
  intro l hli hlj y hy b' hb'
  have hind : iSupIndep Y := hY.indep
  have hinj : Function.Injective Y := hY.inj
  set s : Finset ι := (Finset.univ.erase i).erase j with hsdef
  set S : Subgroup T := Y i ⊔ Y j with hSdef
  set S' : Subgroup T := ⨆ k ∈ s, Y k with hS'def
  have hdij : Disjoint (Y i) (Y j) := hind.pairwiseDisjoint hij
  have hbb : b * b = 1 := by rw [← pow_two]; exact hB.2 b hb
  have hcompb : b.toMonoidHom.comp b.toMonoidHom = (b * b).toMonoidHom := by
    ext x; rfl
  have hbYj : (Y j).map b.toMonoidHom = Y i := by
    rw [← hbij, Subgroup.map_map (Y i) b.toMonoidHom b.toMonoidHom, hcompb, hbb]
    change map (MonoidHom.id T) (Y i) = Y i
    exact Subgroup.map_id (Y i)
  have hOrbitJ : ∀ b' ∈ B, (Y j).map b'.toMonoidHom = Y i ∨
      (Y j).map b'.toMonoidHom = Y j := by
    intro b' hb'
    have hcomp2 : b'.toMonoidHom.comp b.toMonoidHom = b.toMonoidHom.comp b'.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply]
      exact congrArg (fun e : MulAut T => e x) (hB.1 b' hb' b hb)
    have hkey : (Y j).map b'.toMonoidHom =
        ((Y i).map b'.toMonoidHom).map b.toMonoidHom := by
      rw [← hbij]
      calc map b'.toMonoidHom (map b.toMonoidHom (Y i))
          = map (b'.toMonoidHom.comp b.toMonoidHom) (Y i) :=
            Subgroup.map_map (Y i) b'.toMonoidHom b.toMonoidHom
        _ = map (b.toMonoidHom.comp b'.toMonoidHom) (Y i) := by rw [hcomp2]
        _ = map b.toMonoidHom (map b'.toMonoidHom (Y i)) :=
            (Subgroup.map_map (Y i) b.toMonoidHom b'.toMonoidHom).symm
    rcases horb b' hb' with h | h
    · right; rw [hkey, h]; exact hbij
    · left; rw [hkey, h]; exact hbYj
  have hcardι : Fintype.card ι = 4 := by have := hY.card; omega
  have hs_card : s.card = 2 := by
    have h1 : (Finset.univ.erase i).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hcardι]
    have hj_mem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [hsdef, Finset.card_erase_of_mem hj_mem, h1]
  have hrkS : rk ↥S = 4 := by
    have h := rk_sup_add_rk_inf (Y i) (Y j)
    rw [hdij.eq_bot, rk_bot] at h
    rw [hSdef]
    have hi := hY.rank i
    have hj := hY.rank j
    omega
  have hrkS' : rk ↥S' = 4 := by
    rw [hS'def, rk_iSup_biSup_eq_sum Y hind s]
    rw [Finset.sum_const_nat (s := s) (m := 2) (fun k _ => hY.rank k), hs_card]
  have hdisj : Disjoint S S' := by
    rw [hSdef, hS'def]
    have hi_not : i ∉ (s : Set ι) := by simp [hsdef]
    have hj_not : j ∉ (s : Set ι) := by simp [hsdef]
    have hst : Disjoint ({i, j} : Set ι) (s : Set ι) := by
      rw [Set.disjoint_left]
      intro k hk hks
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with hk | hk
      · rw [hk] at hks; exact hi_not hks
      · rw [hk] at hks; exact hj_not hks
    have hfin : ({i, j} : Set ι).Finite := (Set.finite_singleton j).insert i
    have h := hind.disjoint_biSup_biSup' hst hfin
    rwa [iSup_pair] at h
  have hsupT : S ⊔ S' = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hY.sup, hSdef, hS'def]
    refine iSup_le fun k => ?_
    by_cases hki : k = i
    · rw [hki]; exact le_sup_of_le_left le_sup_left
    · by_cases hkj : k = j
      · rw [hkj]; exact le_sup_of_le_left le_sup_right
      · have hks : k ∈ s := by
          rw [hsdef, Finset.mem_erase, Finset.mem_erase]
          exact ⟨hkj, hki, Finset.mem_univ k⟩
        exact le_sup_of_le_right (le_iSup₂ (f := fun k (_ : k ∈ s) => Y k) k hks)
  have hrkT : rk T = 8 := by
    have h := rk_sup_add_rk_inf S S'
    rw [hsupT, rk_top, hdisj.eq_bot, rk_bot] at h
    omega
  have hSinv : ∀ b' ∈ B, ∀ x ∈ S, b' x ∈ S := by
    intro b' hb' x hx
    have hSmap : (S).map b'.toMonoidHom ≤ S := by
      rw [hSdef, Subgroup.map_sup (Y i) (Y j) b'.toMonoidHom]
      refine sup_le ?_ ?_
      · rcases horb b' hb' with h | h
        · rw [h]; exact le_sup_left
        · rw [h]; exact le_sup_right
      · rcases hOrbitJ b' hb' with h | h
        · rw [h]; exact le_sup_left
        · rw [h]; exact le_sup_right
    exact hSmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hS'inv : ∀ b' ∈ B, ∀ x ∈ S', b' x ∈ S' := by
    intro b' hb' x hx
    have hcomp : (b'⁻¹).toMonoidHom.comp b'.toMonoidHom = MonoidHom.id T := by
      ext z
      simp only [MonoidHom.comp_apply]
      exact MulAut.inv_apply_self T b' z
    have hS'map : (S').map b'.toMonoidHom ≤ S' := by
      rw [hS'def, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun k => iSup_le fun hk => ?_
      obtain ⟨j', hj'⟩ := hY.perm b' (hBX hb') k
      rw [hj']
      refine le_iSup₂ (f := fun m (_ : m ∈ s) => Y m) j' ?_
      have hk'' := hk
      rw [hsdef, Finset.mem_erase, Finset.mem_erase] at hk''
      have hki : k ≠ i := hk''.2.1
      have hkj : k ≠ j := hk''.1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j'⟩⟩
      · intro hjj
        rw [hjj] at hj'
        have hk_eq : Y k = (Y j).map (b'⁻¹).toMonoidHom := by
          have h := congrArg (fun H : Subgroup T => H.map (b'⁻¹).toMonoidHom) hj'
          rw [Subgroup.map_map (Y k) (b'⁻¹).toMonoidHom b'.toMonoidHom, hcomp,
            Subgroup.map_id] at h
          exact h
        rcases hOrbitJ (b'⁻¹) (B.inv_mem hb') with h' | h'
        · exact hki (hinj (hk_eq.trans h'))
        · exact hkj (hinj (hk_eq.trans h'))
      · intro hji
        rw [hji] at hj'
        have hk_eq : Y k = (Y i).map (b'⁻¹).toMonoidHom := by
          have h := congrArg (fun H : Subgroup T => H.map (b'⁻¹).toMonoidHom) hj'
          rw [Subgroup.map_map (Y k) (b'⁻¹).toMonoidHom b'.toMonoidHom, hcomp,
            Subgroup.map_id] at h
          exact h
        rcases horb (b'⁻¹) (B.inv_mem hb') with h' | h'
        · exact hki (hinj (hk_eq.trans h'))
        · exact hkj (hinj (hk_eq.trans h'))
    exact hS'map (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  let ψ : T →* T := (MonoidHom.id T) * b.toMonoidHom
  have ψ_apply : ∀ x : T, ψ x = x * b x := fun x => rfl
  set K : Subgroup T := Y i ⊓ fixV (Subgroup.zpowers c) with hKdef
  have hK_le_map : S ⊓ fixV B ≤ K.map ψ := by
    intro w hw
    obtain ⟨hwS, hwB⟩ := hw
    rw [hSdef] at hwS
    obtain ⟨y, hyi, z, hzj, hyz⟩ := Subgroup.mem_sup.mp hwS
    have hbw : b w = w := mem_fixV.mp hwB b hb
    have hcw : c w = w := mem_fixV.mp hwB c hc
    have hbyJ : b y ∈ Y j := by
      have h : b y ∈ (Y i).map b.toMonoidHom := Subgroup.mem_map.mpr ⟨y, hyi, rfl⟩
      rwa [hbij] at h
    have hbzI : b z ∈ Y i := by
      have h : b z ∈ (Y j).map b.toMonoidHom := Subgroup.mem_map.mpr ⟨z, hzj, rfl⟩
      rwa [hbYj] at h
    have hprod : (b z) * (b y) = y * z := by
      have h := hbw
      rw [← hyz, map_mul] at h
      rw [mul_comm (b z) (b y)]
      exact h
    have hdec : b z = y ∧ b y = z :=
      s16c1610_decomp_unique hdij hbzI hyi hbyJ hzj hprod
    have hcyI : c y ∈ Y i := by
      have h : c y ∈ (Y i).map c.toMonoidHom := Subgroup.mem_map.mpr ⟨y, hyi, rfl⟩
      rwa [hci] at h
    have hczJ : c z ∈ Y j := by
      have hz_eq : z = b y := hdec.2.symm
      rw [hz_eq]
      have hcomm : c (b y) = b (c y) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, hB.1 c hc b hb]
      rw [hcomm]
      have h : b (c y) ∈ (Y i).map b.toMonoidHom := Subgroup.mem_map.mpr ⟨c y, hcyI, rfl⟩
      rwa [hbij] at h
    have hcprod : (c y) * (c z) = y * z := by
      have h := hcw
      rw [← hyz, map_mul] at h
      exact h
    have hcy_eq : c y = y := (s16c1610_decomp_unique hdij hcyI hyi hczJ hzj hcprod).1
    refine Subgroup.mem_map.mpr ⟨y, ?_, ?_⟩
    · rw [hKdef]
      exact ⟨hyi, mem_fixV_zpowers_iff_apply.mpr hcy_eq⟩
    · rw [ψ_apply, hdec.2]
      exact hyz
  have hrkK : rk ↥K ≤ 1 := by
    have hne : K ≠ Y i := by
      intro hEq
      obtain ⟨y₀, hy₀, hcy₀⟩ := hcy
      have hle : Y i ≤ fixV (Subgroup.zpowers c) :=
        inf_eq_left.mp (by rw [← hKdef]; exact hEq)
      exact hcy₀ (mem_fixV_zpowers_iff_apply.mp (hle hy₀))
    have hle : K ≤ Y i := by rw [hKdef]; exact inf_le_left
    have hstep := s16c1610_rk_add_one_le_of_lt hT (lt_of_le_of_ne hle hne)
    rw [hY.rank i] at hstep
    omega
  have hrkmap : rk ↥(K.map ψ) ≤ rk ↥K := by
    have h := rk_map_add_rk_inf_ker ψ K
    omega
  have hrkSfix : rk ↥(S ⊓ fixV B) ≤ 1 :=
    le_trans (rk_mono hK_le_map) (le_trans hrkmap hrkK)
  have hle := s16c1610_rk_fixV_le_of_invariant hT hdisj hsupT hSinv hS'inv
  have hrkfixB : 5 ≤ rk ↥(fixV B) := by
    have h := rk_add_rkIdx (fixV B)
    omega
  have hS'fix : 4 ≤ rk ↥(S' ⊓ fixV B) := by omega
  have hEq : S' ⊓ fixV B = S' :=
    eq_of_le_of_rk_le hT inf_le_left (by rw [hrkS']; exact hS'fix)
  have hS'le : S' ≤ fixV B := inf_eq_left.mp hEq
  have hls : l ∈ s := by
    rw [hsdef, Finset.mem_erase, Finset.mem_erase]
    exact ⟨hlj, hli, Finset.mem_univ l⟩
  have hyS' : y ∈ S' := by
    rw [hS'def]
    exact le_iSup₂ (f := fun k (_ : k ∈ s) => Y k) l hls hy
  exact mem_fixV.mp (hS'le hyS') b' hb'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
