module

public import CFSG.Quasithin.AppendixH.H15.H157Basic
public import CFSG.Quasithin.AppendixH.Common.OctadFixedPoints

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H153 CFSG.ASVolI.ChH CFSG.Monster.Code

theorem eq_pow_of_even_of_fix_compl_three {Q : Type*} [Fintype Q] [DecidableEq Q]
    (T : Finset Q) (hT : (Finset.univ \ T).card = 3) {a b : Equiv.Perm Q}
    (ha : a ∈ alternatingGroup Q) (hb : b ∈ alternatingGroup Q)
    (hafix : ∀ x ∈ T, a x = x) (hbfix : ∀ x ∈ T, b x = x)
    (hb3 : b ^ 3 = 1) (hbmove : ∀ x, x ∉ T → b x ≠ x) :
    ∃ k : ℕ, a = b ^ k := by
  have hpres : ∀ (g : Equiv.Perm Q), (∀ x ∈ T, g x = x) → ∀ x, x ∉ T → g x ∉ T := by
    intro g hg x hx h
    have h1 : g x = x := by
      have h2 := congrArg g.symm (hg (g x) h)
      simpa using h2
    exact hx (h1 ▸ h)
  have hXpos : 0 < (Finset.univ \ T).card := by rw [hT]; norm_num
  obtain ⟨x0, hx0⟩ := Finset.card_pos.1 hXpos
  have hx0T : x0 ∉ T := (Finset.mem_sdiff.1 hx0).2
  have hbx0 : b x0 ≠ x0 := hbmove x0 hx0T
  have hb2x0 : (b ^ 2) x0 ≠ x0 := by
    intro h
    have h2 : (b ^ 3) x0 = b x0 := by
      rw [pow_succ', Equiv.Perm.mul_apply, h]
    have h3 : b x0 = x0 := by
      rw [← h2, hb3]
      rfl
    exact hbx0 h3
  have hbx0ne : b x0 ≠ (b ^ 2) x0 := by
    intro h
    have h1 : b x0 = b (b x0) := by simpa [pow_two] using h
    exact hbx0 (b.injective h1).symm
  have hx0not : x0 ∉ ({b x0, (b ^ 2) x0} : Finset Q) := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact hbx0 h.symm
    · exact hb2x0 (Finset.mem_singleton.1 h).symm
  have hbx0not : b x0 ∉ ({(b ^ 2) x0} : Finset Q) := by
    intro h
    exact hbx0ne (Finset.mem_singleton.1 h)
  have hcard3 : ({x0, b x0, (b ^ 2) x0} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem hx0not, Finset.card_insert_of_notMem hbx0not,
      Finset.card_singleton]
  have hXeq : (Finset.univ \ T) = {x0, b x0, (b ^ 2) x0} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hx0
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hpres b hbfix x0 hx0T⟩
      · rw [Finset.mem_singleton] at hy
        rw [hy, pow_two]
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _,
          hpres b hbfix (b x0) (hpres b hbfix x0 hx0T)⟩
    · simp [hT, hcard3]
  have haX : a x0 ∈ (Finset.univ \ T) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hpres a hafix x0 hx0T⟩
  have hax0 : a x0 = x0 ∨ a x0 = b x0 ∨ a x0 = (b ^ 2) x0 := by
    have hmem : a x0 ∈ ({x0, b x0, (b ^ 2) x0} : Finset Q) := by rw [← hXeq]; exact haX
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a x0 = (b ^ k) x0 := by
    rcases hax0 with h | h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h, pow_one]⟩
    · exact ⟨2, h⟩
  let d : Equiv.Perm Q := (b ^ k)⁻¹ * a
  have hdalt : d ∈ alternatingGroup Q := by
    change (b ^ k)⁻¹ * a ∈ alternatingGroup Q
    exact (alternatingGroup Q).mul_mem
      ((alternatingGroup Q).inv_mem (Subgroup.pow_mem (alternatingGroup Q) hb k)) ha
  have hbkT : ∀ m : ℕ, ∀ x ∈ T, (b ^ m) x = x := by
    intro m
    induction m with
    | zero => intro x _; rfl
    | succ n ih => intro x hx; rw [pow_succ', Equiv.Perm.mul_apply, ih x hx, hbfix x hx]
  have hdT : ∀ x ∈ T, d x = x := by
    intro x hx
    change ((b ^ k)⁻¹ * a) x = x
    rw [Equiv.Perm.mul_apply, hafix x hx]
    apply (b ^ k).injective
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply, hbkT k x hx]
  have hdx0 : d x0 = x0 := by
    change ((b ^ k)⁻¹ * a) x0 = x0
    rw [Equiv.Perm.mul_apply, hk]
    exact Equiv.symm_apply_apply (b ^ k) x0
  have hZcard : ((Finset.univ \ T).erase x0).card ≤ 2 := by
    rw [Finset.card_erase_of_mem hx0, hT]
  have hfixZ : ∀ x, x ∉ (Finset.univ \ T).erase x0 → d x = x := by
    intro x hx
    by_cases hxx0 : x = x0
    · rw [hxx0]; exact hdx0
    · have hxT : x ∈ T := by
        by_contra hxT
        exact hx (Finset.mem_erase.2
          ⟨hxx0, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hxT⟩⟩)
      exact hdT x hxT
  have hd1 : d = 1 :=
    eq_one_of_even_of_fix_compl ((Finset.univ \ T).erase x0) hZcard hdalt hfixZ
  have haeq : a = b ^ k := by
    change (b ^ k)⁻¹ * a = 1 at hd1
    calc a = b ^ k * ((b ^ k)⁻¹ * a) := by group
      _ = b ^ k * 1 := by rw [hd1]
      _ = b ^ k := by rw [mul_one]
  exact ⟨k, haeq⟩

theorem eq_zpowers_of_fix_tFix {n : S24} (hn : n ∈ M24g)
    (h : ∀ i ∈ tFix, n i = i) : n ∈ Subgroup.zpowers tP := by
  obtain ⟨T, hTF, hTcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ tFix.card by
    rw [card_tFix]; norm_num)
  have hlt : T.card < tFix.card := by rw [hTcard, card_tFix]; norm_num
  obtain ⟨f6, hf6F, hf6T⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hFeq : tFix = insert f6 T := by
    have hsub : insert f6 T ⊆ tFix := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hf6F
      · exact hTF hx
    have hcard : (insert f6 T).card = tFix.card := by
      rw [Finset.card_insert_of_notMem hf6T, hTcard, card_tFix]
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)).symm
  obtain ⟨c, ⟨hcoct, hTc⟩, -⟩ := existsUnique_octad T hTcard
  have hc : IsOctad c := isOctad_iff_mem_octads.2 hcoct
  have htpstab : tP ∈ octStab c := by
    rw [mem_octStab_iff]
    refine ⟨tP_mem, smul_octad_eq_of_fix_five tP_mem hc hTcard hTc ?_⟩
    intro i hi
    exact (mem_tFix_iff i).1 (hTF hi)
  have hnpstab : n ∈ octStab c := by
    rw [mem_octStab_iff]
    refine ⟨hn, smul_octad_eq_of_fix_five hn hc hTcard hTc ?_⟩
    intro i hi
    exact h i (hTF hi)
  have hf6c : f6 ∉ c := by
    intro hf6c
    have hFc : tFix ⊆ c := by
      intro i hi
      have hi' : i ∈ insert f6 T := by rw [← hFeq]; exact hi
      rcases Finset.mem_insert.1 hi' with h | h
      · rw [h]; exact hf6c
      · exact hTc h
    let Z : Finset ↥c := Finset.univ.filter fun x => (x : Fin 24) ∉ tFix
    have hZcard : Z.card ≤ 2 := by
      have himg : Z.image (Subtype.val : ↥c → Fin 24) = c \ tFix := by
        ext y
        simp only [Z, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_sdiff]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.2, hx⟩
        · rintro ⟨hyc, hy⟩
          exact ⟨⟨y, hyc⟩, hy, rfl⟩
      have h1 : Z.card = (c \ tFix).card := by
        rw [← Finset.card_image_of_injective Z Subtype.val_injective, himg]
      rw [h1, Finset.card_sdiff_of_subset hFc, hc.1, card_tFix]
    have hfixZ : ∀ x, x ∉ Z → octAct c ⟨tP, htpstab⟩ x = x := by
      intro x hx
      apply Subtype.ext
      rw [octAct_apply]
      apply (mem_tFix_iff (x : Fin 24)).1
      by_contra hx'
      exact hx (by simp [Z, hx'])
    have hbalt : octAct c ⟨tP, htpstab⟩ ∈ alternatingGroup ↥c := by
      rw [← range_octAct hc]
      exact MonoidHom.mem_range.2 ⟨⟨tP, htpstab⟩, rfl⟩
    have hb1 : octAct c ⟨tP, htpstab⟩ = 1 :=
      eq_one_of_even_of_fix_compl Z hZcard hbalt hfixZ
    have hfixc : ∀ i ∈ c, tP i = i := by
      intro i hi
      have h1 : octAct c ⟨tP, htpstab⟩ ⟨i, hi⟩ = ⟨i, hi⟩ := by rw [hb1]; rfl
      have h2 := congrArg (fun x : ↥c => (x : Fin 24)) h1
      simpa only [octAct_apply, Subtype.coe_mk] using h2
    have hct : c ⊆ tFix := fun i hi => (mem_tFix_iff i).2 (hfixc i hi)
    have hle : c.card ≤ tFix.card := Finset.card_le_card hct
    rw [hc.1, card_tFix] at hle
    omega
  have hcF : c ∩ tFix = T := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro i hi
      rw [Finset.mem_inter] at hi
      have hi' : i ∈ insert f6 T := by rw [← hFeq]; exact hi.2
      rcases Finset.mem_insert.1 hi' with h | h
      · exact absurd (h ▸ hi.1) hf6c
      · exact h
    · intro i hi
      exact Finset.mem_inter.2 ⟨hTc hi, hTF hi⟩
  let a : Equiv.Perm ↥c := octAct c ⟨n, hnpstab⟩
  let b : Equiv.Perm ↥c := octAct c ⟨tP, htpstab⟩
  have haalt : a ∈ alternatingGroup ↥c := by
    change octAct c ⟨n, hnpstab⟩ ∈ alternatingGroup ↥c
    rw [← range_octAct hc]
    exact MonoidHom.mem_range.2 ⟨⟨n, hnpstab⟩, rfl⟩
  have hbalt : b ∈ alternatingGroup ↥c := by
    change octAct c ⟨tP, htpstab⟩ ∈ alternatingGroup ↥c
    rw [← range_octAct hc]
    exact MonoidHom.mem_range.2 ⟨⟨tP, htpstab⟩, rfl⟩
  have hpow3 : (⟨tP, htpstab⟩ : ↥(octStab c)) ^ 3 = 1 := by
    apply Subtype.ext
    simp [tP_pow_three]
  have hb3 : b ^ 3 = 1 := by
    change octAct c ⟨tP, htpstab⟩ ^ 3 = 1
    rw [← map_pow, hpow3, map_one]
  let T' : Finset ↥c := Finset.univ.filter fun x => (x : Fin 24) ∈ T
  have hcompl_card : (Finset.univ \ T').card = 3 := by
    have himg : (Finset.univ \ T').image (Subtype.val : ↥c → Fin 24) = c \ T := by
      ext y
      simp only [T', Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_filter]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, hx⟩
      · rintro ⟨hyc, hy⟩
        exact ⟨⟨y, hyc⟩, hy, rfl⟩
    rw [← Finset.card_image_of_injective _ Subtype.val_injective, himg,
      Finset.card_sdiff_of_subset hTc, hc.1, hTcard]
  have hbmove : ∀ x, x ∉ T' → b x ≠ x := by
    intro x hx hxy
    have hxT : (x : Fin 24) ∉ T := by
      intro hxT
      exact hx (by simp [T', hxT])
    have h2 : tP (x : Fin 24) = (x : Fin 24) := by
      have h1 := congrArg (fun y : ↥c => (y : Fin 24)) hxy
      change ((octAct c ⟨tP, htpstab⟩ x : ↥c) : Fin 24) = (x : Fin 24) at h1
      rwa [octAct_apply] at h1
    have hxfix : (x : Fin 24) ∈ tFix := (mem_tFix_iff _).2 h2
    exact hxT (by
      rw [← hcF]
      exact Finset.mem_inter.2 ⟨x.2, hxfix⟩)
  have hafixT' : ∀ x ∈ T', a x = x := by
    intro x hx
    have hxT : (x : Fin 24) ∈ T := (Finset.mem_filter.1 hx).2
    change octAct c ⟨n, hnpstab⟩ x = x
    apply Subtype.ext
    rw [octAct_apply]
    exact h (x : Fin 24) (hTF hxT)
  have hbfixT' : ∀ x ∈ T', b x = x := by
    intro x hx
    have hxT : (x : Fin 24) ∈ T := (Finset.mem_filter.1 hx).2
    change octAct c ⟨tP, htpstab⟩ x = x
    apply Subtype.ext
    rw [octAct_apply]
    exact (mem_tFix_iff (x : Fin 24)).1 (hTF hxT)
  obtain ⟨k, hk⟩ := eq_pow_of_even_of_fix_compl_three T' hcompl_card haalt hbalt
    hafixT' hbfixT' hb3 hbmove
  let n' : S24 := n * (tP ^ k)⁻¹
  have hn'M : n' ∈ M24g := by
    change n * (tP ^ k)⁻¹ ∈ M24g
    exact M24g.mul_mem hn (M24g.inv_mem (Subgroup.pow_mem M24g tP_mem k))
  have hn'stab : n' ∈ octStab c := by
    change n * (tP ^ k)⁻¹ ∈ octStab c
    exact (octStab c).mul_mem hnpstab
      ((octStab c).inv_mem (Subgroup.pow_mem (octStab c) htpstab k))
  have hn'act1 : octAct c ⟨n', hn'stab⟩ = 1 := by
    have hdecomp : (⟨n', hn'stab⟩ : ↥(octStab c)) =
        ⟨n, hnpstab⟩ * (⟨tP, htpstab⟩ ^ k)⁻¹ := by
      apply Subtype.ext
      change n' = n * (tP ^ k)⁻¹
      rfl
    change octAct c ⟨n', hn'stab⟩ = 1
    rw [hdecomp]
    simp only [map_mul, map_inv, map_pow]
    change a * (b ^ k)⁻¹ = 1
    rw [← hk, mul_inv_cancel]
  have hfixc' : ∀ i ∈ c, n' i = i := by
    intro i hi
    have h1 : octAct c ⟨n', hn'stab⟩ ⟨i, hi⟩ = ⟨i, hi⟩ := by rw [hn'act1]; rfl
    have h2 := congrArg (fun x : ↥c => (x : Fin 24)) h1
    simpa only [octAct_apply, Subtype.coe_mk] using h2
  have htpkfix : ∀ m : ℕ, (tP ^ m) f6 = f6 := by
    intro m
    induction m with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, (mem_tFix_iff f6).1 hf6F]
  have hf6fix : n' f6 = f6 := by
    change (n * (tP ^ k)⁻¹) f6 = f6
    have h1 : (tP ^ k)⁻¹ f6 = f6 := by
      apply (tP ^ k).injective
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply, htpkfix k]
    rw [Equiv.Perm.mul_apply, h1, h f6 hf6F]
  have hnine : (insert f6 c).card = 9 := by
    rw [Finset.card_insert_of_notMem hf6c, hc.1]
  have hn'1 : n' = 1 := by
    refine eq_one_of_fix_nine hn'M (F := insert f6 c) ?_ ?_
    · simp [hnine]
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hf6fix
      · exact hfixc' i hi
  have h1 : n * (tP ^ k)⁻¹ = 1 := by
    change n' = 1
    exact hn'1
  have hn_eq : n = tP ^ k := by
    calc n = n * (tP ^ k)⁻¹ * (tP ^ k) := by group
      _ = 1 * (tP ^ k) := by rw [h1]
      _ = tP ^ k := by rw [one_mul]
  rw [hn_eq]
  exact Subgroup.pow_mem (Subgroup.zpowers tP) (Subgroup.mem_zpowers tP) k

end CFSG.ASVolI.AppH.H157
