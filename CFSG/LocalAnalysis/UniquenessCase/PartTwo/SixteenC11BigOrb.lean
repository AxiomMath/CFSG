module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCls
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

open scoped Pointwise

private theorem s16c11_big_orb_exists_index_two {A : Type*} [Group A] [Finite A]
    (hA : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a ^ 2 = 1) {t : A} (ht : t ≠ 1) :
    ∃ B : Subgroup A, B.index = 2 ∧ t ∉ B := by
  classical
  have hnormal : ∀ S : Subgroup A, S.Normal := fun S =>
    ⟨fun n hn g => by rw [hA g n, mul_inv_cancel_right]; exact hn⟩
  have hcard2 : ∀ a : A, a ≠ 1 → Nat.card (Subgroup.zpowers a) = 2 := fun a ha => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h2 a) ha
  have hsmall : ∀ a : A, a ≠ 1 → ∀ S : Subgroup A, a ∉ S → Subgroup.zpowers a ⊓ S = ⊥ := by
    intro a ha S haS
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ S : Subgroup A) ∣ 2 :=
      hcard2 a ha ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : Subgroup.zpowers a ⊓ S = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard2 a ha])
      exact haS ((heq ▸ (inf_le_right : Subgroup.zpowers a ⊓ S ≤ S))
        (heq.symm ▸ Subgroup.mem_zpowers a))
  obtain ⟨B, htB, hBmax⟩ := Set.exists_max_image {B : Subgroup A | t ∉ B} (fun B => Nat.card B)
    (Set.toFinite _) ⟨⊥, fun h => ht (Subgroup.mem_bot.mp h)⟩
  refine ⟨B, ?_, htB⟩
  have hC : B ⊔ Subgroup.zpowers t = ⊤ := by
    by_contra hC
    obtain ⟨a, haC⟩ : ∃ a, a ∉ B ⊔ Subgroup.zpowers t := by
      by_contra h
      push Not at h
      exact hC (eq_top_iff.mpr fun x _ => h x)
    have ha1 : a ≠ 1 := fun h => haC (h ▸ one_mem _)
    have haB : a ∉ B := fun h => haC ((le_sup_left : B ≤ B ⊔ Subgroup.zpowers t) h)
    have htB'' : t ∉ B ⊔ Subgroup.zpowers a := by
      intro hmem
      have := hnormal (Subgroup.zpowers a)
      obtain ⟨b, hb, y, hy, hby⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
      have hyC : y ∈ B ⊔ Subgroup.zpowers t := by
        have : y = b⁻¹ * t := by rw [← hby]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hb))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      have hy1 : y = 1 := by
        have h1 : y ∈ Subgroup.zpowers a ⊓ (B ⊔ Subgroup.zpowers t) := ⟨hy, hyC⟩
        rwa [hsmall a ha1 _ haC, Subgroup.mem_bot] at h1
      apply htB
      rw [← hby, hy1, mul_one]
      exact hb
    have hlt : B < B ⊔ Subgroup.zpowers a :=
      lt_of_le_of_ne le_sup_left fun h => haB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have := hBmax _ htB''
    exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr this)
  have hdisj : Disjoint B (Subgroup.zpowers t) := by
    rw [disjoint_iff, inf_comm]
    exact hsmall t ht B htB
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B
    (Subgroup.zpowers t) (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr (hnormal B)).ge) hdisj
  rw [hC, Subgroup.card_top, hcard2 t ht] at hcard
  have h := B.card_mul_index
  rw [hcard] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

variable {n : ℕ}

private noncomputable def s16c11_big_orb_ind (Y : Set (Fin n)) : Fin n → ZMod 2 := by
  classical
  exact fun i => if i ∈ Y then 1 else 0

private lemma s16c11_big_orb_ind_eq_one_iff {Y : Set (Fin n)} {i : Fin n} :
    s16c11_big_orb_ind Y i = 1 ↔ i ∈ Y := by
  classical
  unfold s16c11_big_orb_ind
  by_cases h : i ∈ Y <;> simp [h]

private lemma s16c11_big_orb_ind_eq_zero_iff {Y : Set (Fin n)} {i : Fin n} :
    s16c11_big_orb_ind Y i = 0 ↔ i ∉ Y := by
  classical
  unfold s16c11_big_orb_ind
  by_cases h : i ∈ Y <;> simp [h]

private lemma s16c11_big_orb_ind_injective :
    Function.Injective (s16c11_big_orb_ind (n := n)) := by
  intro Y Z h
  ext i
  rw [← s16c11_big_orb_ind_eq_one_iff (Y := Y),
    ← s16c11_big_orb_ind_eq_one_iff (Y := Z), h]

private lemma s16c11_big_orb_sum_ind (Y : Set (Fin n)) :
    ∑ i, s16c11_big_orb_ind Y i = (Y.ncard : ZMod 2) := by
  classical
  have hcongr : (∑ i, s16c11_big_orb_ind Y i) =
      ∑ i, (if i ∈ Y then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : i ∈ Y
    · rw [s16c11_big_orb_ind_eq_one_iff.mpr h, if_pos h]
    · rw [s16c11_big_orb_ind_eq_zero_iff.mpr h, if_neg h]
  rw [hcongr, Finset.sum_boole]
  congr 1
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext i
  simp

private lemma s16c11_big_orb_ind_compl (Y : Set (Fin n)) :
    s16c11_big_orb_ind Y + (fun _ => (1 : ZMod 2)) = s16c11_big_orb_ind Yᶜ := by
  funext i
  rw [Pi.add_apply]
  by_cases h : i ∈ Y
  · rw [s16c11_big_orb_ind_eq_one_iff.mpr h,
      s16c11_big_orb_ind_eq_zero_iff.mpr (by simpa using h)]
    decide
  · rw [s16c11_big_orb_ind_eq_zero_iff.mpr h,
      s16c11_big_orb_ind_eq_one_iff.mpr (by simpa using h)]
    decide

private lemma s16c11_big_orb_perm_ind (Y : Set (Fin n)) (σ : Equiv.Perm (Fin n)) :
    (fun i => s16c11_big_orb_ind Y (σ⁻¹ i)) = s16c11_big_orb_ind (σ '' Y) := by
  funext i
  by_cases h : σ⁻¹ i ∈ Y
  · rw [s16c11_big_orb_ind_eq_one_iff.mpr h,
      s16c11_big_orb_ind_eq_one_iff.mpr ((Set.mem_image σ Y i).mpr ⟨σ⁻¹ i, h, by simp⟩)]
  · rw [s16c11_big_orb_ind_eq_zero_iff.mpr h, s16c11_big_orb_ind_eq_zero_iff.mpr]
    rintro ⟨y, hy, hyi⟩
    exact h (by simpa [← hyi] using hy)

private lemma s16c11_big_orb_step0 {E : Subgroup (Equiv.Perm (Fin n))}
    (hB : ∀ B : Subgroup (Equiv.Perm (Fin n)), B ≤ E → B.relIndex E ≤ 2 →
      ∀ q : (FFModel.symDn n).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q) →
          ∀ σ ∈ E, (FFModel.symDn_isActionModel n).modAct σ q = q)
    {Y : Set (Fin n)} (hY : (Y.ncard : ZMod 2) = 0)
    {B : Subgroup (Equiv.Perm (Fin n))} (hBE : B ≤ E) (hBrel : B.relIndex E ≤ 2)
    (hYfix : ∀ σ ∈ B, σ '' Y = Y) :
    ∀ e ∈ E, e '' Y = Y ∨ e '' Y = Yᶜ := by
  classical
  set x : Fin n → ZMod 2 := s16c11_big_orb_ind Y with hx
  have hxsum : ∑ i, x i = 0 := by
    rw [hx, s16c11_big_orb_sum_ind]; exact hY
  set q : (FFModel.symDn n).Mod := s16c11BigCls n x hxsum with hq
  have hfixB : ∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q := by
    intro σ hσ
    have hsum : ∑ i, x (σ⁻¹ i) = 0 := by rw [Equiv.sum_comp]; exact hxsum
    have hperm : (fun i => x (σ⁻¹ i)) = x := by
      rw [hx, s16c11_big_orb_perm_ind Y σ, hYfix σ hσ]
    rw [hq, s16c11BigCls_modAct n σ (x := x) (hx := hxsum) (hx' := hsum)]
    exact s16c11BigCls_eq_iff.mpr (Or.inl hperm.symm)
  intro e he
  have heq := hB B hBE hBrel q hfixB e he
  have hsum : ∑ i, x (e⁻¹ i) = 0 := by rw [Equiv.sum_comp]; exact hxsum
  rw [hq, s16c11BigCls_modAct n e (x := x) (hx := hxsum) (hx' := hsum)] at heq
  rcases (s16c11BigCls_eq_iff.mp heq) with h | h
  · left
    have h2 : s16c11_big_orb_ind (e '' Y) = s16c11_big_orb_ind Y := by
      rw [← s16c11_big_orb_perm_ind Y e, ← hx, ← h]
    exact s16c11_big_orb_ind_injective h2
  · right
    have hperm : (fun i => x (e⁻¹ i)) = s16c11_big_orb_ind (e '' Y) := by
      rw [hx, s16c11_big_orb_perm_ind Y e]
    have h2 : s16c11_big_orb_ind Y = s16c11_big_orb_ind (e '' Y)ᶜ := by
      rw [← hx, h]
      change (fun i => x (e⁻¹ i)) + (fun _ => (1 : ZMod 2)) =
        s16c11_big_orb_ind (e '' Y)ᶜ
      rw [hperm, s16c11_big_orb_ind_compl]
    have h3 : Y = (e '' Y)ᶜ := s16c11_big_orb_ind_injective h2
    have h4 : Yᶜ = e '' Y := by
      simpa using congrArg (fun S : Set (Fin n) => Sᶜ) h3
    exact h4.symm

private lemma s16c11_big_orb_relIndex_map {E : Subgroup (Equiv.Perm (Fin n))}
    (H : Subgroup E) : (H.map E.subtype).relIndex E = H.index := by
  have h := Subgroup.relIndex_map_map_of_injective (f := E.subtype) H ⊤ E.subtype_injective
  simpa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] using h

private lemma s16c11_big_orb_isPGroup {E : Subgroup (Equiv.Perm (Fin n))}
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) : IsPGroup 2 E :=
  fun x => ⟨1, by
    have h : (x : Equiv.Perm (Fin n)) ^ 2 = 1 := hE2 x x.property
    simpa using (Subtype.ext (by simpa using h) : (x ^ 2 : E) = 1)⟩

private lemma s16c11_big_orb_isPGroup_sub {E : Subgroup (Equiv.Perm (Fin n))}
    (h : IsPGroup 2 E) (B' : Subgroup E) : IsPGroup 2 B' := fun x => by
  obtain ⟨k, hk⟩ := h (x : E)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

private lemma s16c11_big_orb_stab_index {n : ℕ} (hn : ¬ 2 ∣ n ∨ n = 10)
    {E : Subgroup (Equiv.Perm (Fin n))} (hE : IsElemAbelian 2 E)
    (hB : ∀ B : Subgroup (Equiv.Perm (Fin n)), B ≤ E → B.relIndex E ≤ 2 →
      ∀ q : (FFModel.symDn n).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q) →
          ∀ σ ∈ E, (FFModel.symDn_isActionModel n).modAct σ q = q)
    {p : Fin n} (hp : ∃ e : E, e • p ≠ p) :
    (MulAction.stabilizer E p).index = 2 := by
  classical
  let Ep : Subgroup E := MulAction.stabilizer E p
  change Ep.index = 2
  haveI : IsMulCommutative E := hE.1
  obtain ⟨e0, he0⟩ := hp
  have he0Ep : e0 ∉ Ep := fun h => he0 (MulAction.mem_stabilizer_iff.mp h)
  let t : E ⧸ Ep := QuotientGroup.mk' Ep e0
  have ht : t ≠ 1 := by
    intro h
    apply he0Ep
    have h' : (QuotientGroup.mk' Ep e0 : E ⧸ Ep) = 1 := h
    rw [QuotientGroup.mk'_apply] at h'
    exact (QuotientGroup.eq_one_iff e0).mp h'
  have hcomm : ∀ a b : E ⧸ Ep, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Ep a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Ep b
    rw [← map_mul, ← map_mul, hE.1.is_comm.comm x y]
  have h2 : ∀ a : E ⧸ Ep, a ^ 2 = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Ep a
    have hx2 : x ^ 2 = 1 :=
      Subtype.ext (by simpa using hE.2 (x : Equiv.Perm (Fin n)) x.property)
    simpa using congrArg (QuotientGroup.mk' Ep) hx2
  obtain ⟨Bq, hBqindex, htBq⟩ := s16c11_big_orb_exists_index_two hcomm h2 ht
  let B' : Subgroup E := Bq.comap (QuotientGroup.mk' Ep)
  have hB'index : B'.index = 2 := by
    change (Bq.comap (QuotientGroup.mk' Ep)).index = 2
    rw [Subgroup.index_comap_of_surjective (H := Bq) (QuotientGroup.mk'_surjective Ep), hBqindex]
  have hEp_le_B' : Ep ≤ B' := by
    intro x hx
    change QuotientGroup.mk' Ep x ∈ Bq
    have hx1 : (QuotientGroup.mk' Ep x : E ⧸ Ep) = 1 := by
      rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]; exact Bq.one_mem
  have he0B' : e0 ∉ B' := by
    intro h
    exact htBq (Subgroup.mem_comap.mp h)
  have hB'le : B' ≤ Ep := by
    by_contra hlt
    obtain ⟨b, hbB', hbEp⟩ := SetLike.not_le_iff_exists.mp hlt
    have hbp : b • p ≠ p := fun h => hbEp (MulAction.mem_stabilizer_iff.mpr h)
    have hBp : IsPGroup 2 B' := s16c11_big_orb_isPGroup_sub (s16c11_big_orb_isPGroup hE.2) B'
    let Y : Set (Fin n) := MulAction.orbit B' p
    have hYcard : ∃ k, Y.ncard = 2 ^ k := by
      obtain ⟨k, hk⟩ := hBp.card_orbit p
      exact ⟨k, by rw [← Nat.card_coe_set_eq]; exact hk⟩
    have h2le : 2 ≤ Y.ncard := by
      have hpair : ({p, b • p} : Set (Fin n)) ⊆ Y := by
        intro x hx
        rcases (by simpa using hx : x = p ∨ x = b • p) with h | h
        · rw [h]; exact MulAction.mem_orbit_self p
        · rw [h]
          exact MulAction.mem_orbit_iff.mpr ⟨⟨b, hbB'⟩, Subgroup.mk_smul b hbB' p⟩
      have hpaircard : ({p, b • p} : Set (Fin n)).ncard = 2 :=
        Set.ncard_pair (Ne.symm hbp)
      rw [← hpaircard]
      exact Set.ncard_le_ncard hpair
    obtain ⟨k, hk⟩ := hYcard
    have hkpos : 0 < k := by
      by_contra hk0
      rw [Nat.eq_zero_of_not_pos hk0, pow_zero] at hk
      omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    have hk' : Y.ncard = 2 ^ (j + 1) := by rw [hk, hj]
    have hk'' : Y.ncard = 2 ^ j * 2 := by rw [hk', pow_succ]
    have hYeven : (Y.ncard : ZMod 2) = 0 := by
      rw [hk'', ZMod.natCast_eq_zero_iff_even]
      exact ⟨2 ^ j, by ring⟩
    have h2dvd' : 2 ∣ Y.ncard := ⟨2 ^ j, by rw [hk'', Nat.mul_comm]⟩
    have hYfix : ∀ σ ∈ B'.map E.subtype, σ '' Y = Y := by
      intro σ hσ
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hσ
      have h1 : (⟨b, hb⟩ : B') • Y = Y := MulAction.smul_orbit (⟨b, hb⟩ : B') p
      have h2 : (E.subtype b) '' Y = (⟨b, hb⟩ : B') • Y := by
        apply Set.image_congr
        intro y _
        simp [Subgroup.smul_def, Equiv.Perm.smul_def]
      rw [h2, h1]
    have hcases := s16c11_big_orb_step0 (n := n) hB hYeven (Subgroup.map_subtype_le B')
      (by rw [s16c11_big_orb_relIndex_map, hB'index]) hYfix (e0 : Equiv.Perm (Fin n)) e0.property
    rcases hcases with h1 | h1
    · have hpY : (e0 : Equiv.Perm (Fin n)) p ∈ Y := by
        rw [← h1]; exact ⟨p, MulAction.mem_orbit_self p, rfl⟩
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp hpY
      have hmove : (((c⁻¹ : B') : E) * e0) ∈ Ep := by
        rw [MulAction.mem_stabilizer_iff]
        have hc' : (c : E) • p = e0 • p := by
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hc
        calc (((c⁻¹ : B') : E) * e0) • p
            = ((c⁻¹ : B') : E) • (e0 • p) := by rw [mul_smul]
          _ = ((c⁻¹ : B') : E) • ((c : E) • p) := by
                congr 1
                exact hc'.symm
          _ = (((c⁻¹ : B') : E) * (c : E)) • p := by rw [← smul_smul]
          _ = p := by simp
      have hmem1 : ((c⁻¹ : B') : E) * e0 ∈ B' := hEp_le_B' hmove
      have he0B'' : e0 ∈ B' := by
        have h2 : (c : E) * (((c⁻¹ : B') : E) * e0) ∈ B' := B'.mul_mem c.property hmem1
        have heq : (c : E) * (((c⁻¹ : B') : E) * e0) = e0 := by
          rw [← mul_assoc, Subgroup.coe_inv, mul_inv_cancel, one_mul]
        exact heq ▸ h2
      exact he0B' he0B''
    · have himg : ((e0 : Equiv.Perm (Fin n)) '' Y).ncard = Y.ncard :=
        Set.ncard_image_of_injective Y (e0 : Equiv.Perm (Fin n)).injective
      have hcompl : (Yᶜ).ncard = Nat.card (Fin n) - Y.ncard := Set.ncard_compl Y
      have h2 : Y.ncard = n - Y.ncard := by
        calc Y.ncard = ((e0 : Equiv.Perm (Fin n)) '' Y).ncard := himg.symm
          _ = (Yᶜ).ncard := by rw [h1]
          _ = Nat.card (Fin n) - Y.ncard := hcompl
          _ = n - Y.ncard := by rw [Nat.card_fin]
      have hle : Y.ncard ≤ n := by simpa using Set.ncard_le_card (s := Y)
      have h2n : 2 * Y.ncard = n := by omega
      have h2dvd : 2 ∣ n := ⟨Y.ncard, h2n.symm⟩
      have hn10 : n = 10 := hn.resolve_left (not_not.mpr h2dvd)
      have hY5 : Y.ncard = 5 := by omega
      obtain ⟨m, hm⟩ := h2dvd'
      omega
  have hEq : Ep = B' := le_antisymm hEp_le_B' hB'le
  rw [hEq, hB'index]

private lemma s16c11_big_orb_no_fixed {n : ℕ} (hn : ¬ 2 ∣ n ∨ n = 10)
    {E : Subgroup (Equiv.Perm (Fin n))} (hE : IsElemAbelian 2 E)
    (hB : ∀ B : Subgroup (Equiv.Perm (Fin n)), B ≤ E → B.relIndex E ≤ 2 →
      ∀ q : (FFModel.symDn n).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q) →
          ∀ σ ∈ E, (FFModel.symDn_isActionModel n).modAct σ q = q)
    {p : Fin n} (hp : ∃ e : E, e • p ≠ p) {k : Fin n} (hk : ∀ e : E, e • k = k) : False := by
  classical
  have hstab : (MulAction.stabilizer E p).index = 2 := s16c11_big_orb_stab_index hn hE hB hp
  let Ep : Subgroup E := MulAction.stabilizer E p
  have hEpindex : Ep.index = 2 := hstab
  obtain ⟨e0, he0⟩ := hp
  have he0Ep : e0 ∉ Ep := fun h => he0 (MulAction.mem_stabilizer_iff.mp h)
  have hpk : p ≠ k := by
    intro h
    rw [h] at he0
    exact he0 (hk e0)
  have hYeven : (({p, k} : Set (Fin n)).ncard : ZMod 2) = 0 := by
    rw [Set.ncard_pair hpk]
    decide
  have hYfix : ∀ σ ∈ Ep.map E.subtype, σ '' ({p, k} : Set (Fin n)) = {p, k} := by
    intro σ hσ
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hσ
    have hbp : b • p = p := MulAction.mem_stabilizer_iff.mp hb
    have hbk : b • k = k := hk b
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases hy with hy | hy
      · left
        rw [← hxy, hy]
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hbp
      · right
        rw [← hxy, hy]
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hbk
    · rintro (hx | hx)
      · exact ⟨p, Or.inl rfl, by
          rw [hx]
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hbp⟩
      · exact ⟨k, Or.inr rfl, by
          rw [hx]
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hbk⟩
  have hcases := s16c11_big_orb_step0 (n := n) hB hYeven (Subgroup.map_subtype_le Ep)
    (by rw [s16c11_big_orb_relIndex_map, hEpindex]) hYfix (e0 : Equiv.Perm (Fin n)) e0.property
  rcases hcases with h1 | h1
  · have hpY : (e0 : Equiv.Perm (Fin n)) p ∈ ({p, k} : Set (Fin n)) := by
      rw [← h1]; exact ⟨p, Or.inl rfl, rfl⟩
    rcases (by simpa using hpY : (e0 : Equiv.Perm (Fin n)) p = p ∨
        (e0 : Equiv.Perm (Fin n)) p = k) with h | h
    · exact he0 (by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h)
    · have hpk' : p = k := by
        apply (e0 : Equiv.Perm (Fin n)).injective
        rw [h]
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using (hk e0).symm
      exact hpk hpk'
  · have himg : ((e0 : Equiv.Perm (Fin n)) '' ({p, k} : Set (Fin n))).ncard
        = ({p, k} : Set (Fin n)).ncard :=
      Set.ncard_image_of_injective _ (e0 : Equiv.Perm (Fin n)).injective
    have hcompl : (({p, k} : Set (Fin n))ᶜ).ncard
        = Nat.card (Fin n) - ({p, k} : Set (Fin n)).ncard := Set.ncard_compl _
    have h2 : ({p, k} : Set (Fin n)).ncard = n - ({p, k} : Set (Fin n)).ncard := by
      calc ({p, k} : Set (Fin n)).ncard
          = ((e0 : Equiv.Perm (Fin n)) '' ({p, k} : Set (Fin n))).ncard := himg.symm
        _ = (({p, k} : Set (Fin n))ᶜ).ncard := by rw [h1]
        _ = Nat.card (Fin n) - ({p, k} : Set (Fin n)).ncard := hcompl
        _ = n - ({p, k} : Set (Fin n)).ncard := by rw [Nat.card_fin]
    have h4 : n = 4 := by
      have hc : ({p, k} : Set (Fin n)).ncard = 2 := Set.ncard_pair hpk
      omega
    rcases hn with hodd | hten
    · exact hodd ⟨2, by omega⟩
    · omega

theorem s16c11_big_a2_orbits {n : ℕ} (hn : ¬ 2 ∣ n ∨ n = 10) {E : Subgroup (Equiv.Perm (Fin n))}
    (hE : IsElemAbelian 2 E) (hE1 : E ≠ ⊥)
    (hB : ∀ B : Subgroup (Equiv.Perm (Fin n)), B ≤ E → B.relIndex E ≤ 2 →
      ∀ q : (FFModel.symDn n).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q) →
          ∀ σ ∈ E, (FFModel.symDn_isActionModel n).modAct σ q = q) :
    ∃ j : Equiv.Perm (Fin n), (∀ i, j i ≠ i) ∧ (∀ i, j (j i) = i) ∧
      (∀ σ ∈ E, ∀ i, σ i = i ∨ σ i = j i) ∧ ∀ i, ∃ σ ∈ E, σ i = j i := by
  classical
  have hmoved_exists : ∃ p : Fin n, ∃ e : E, e • p ≠ p := by
    obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have hne : (e : Equiv.Perm (Fin n)) ≠ 1 := fun h => he1 (Subtype.ext h)
    obtain ⟨p, hp⟩ : ∃ p, (e : Equiv.Perm (Fin n)) p ≠ p := by
      by_contra h
      exact hne (Equiv.ext fun x => by
        simpa using not_not.mp (not_exists.mp h x))
    exact ⟨p, e, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hp⟩
  obtain ⟨p₀, e₀, hp₀⟩ := hmoved_exists
  have hno_fixed : ∀ k : Fin n, ∃ e : E, e • k ≠ k := by
    intro k
    by_contra hk
    exact s16c11_big_orb_no_fixed hn hE hB ⟨e₀, hp₀⟩
      (fun e => not_not.mp (not_exists.mp hk e))
  have hstab : ∀ p : Fin n, (MulAction.stabilizer E p).index = 2 :=
    fun p => s16c11_big_orb_stab_index hn hE hB (hno_fixed p)
  have horbit2 : ∀ p : Fin n, (MulAction.orbit E p).ncard = 2 := by
    intro p
    rw [← MulAction.index_stabilizer]
    exact hstab p
  have hpair : ∀ p : Fin n, ∃ q : Fin n, q ≠ p ∧ MulAction.orbit E p = {p, q} := by
    intro p
    obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp (horbit2 p)
    have hp : p ∈ MulAction.orbit E p := MulAction.mem_orbit_self p
    rw [hset] at hp
    rcases (by simpa using hp : p = x ∨ p = y) with hpx | hpy
    · exact ⟨y, fun hy => hxy (by rw [hpx.symm, hy]), by rw [hset, hpx]⟩
    · exact ⟨x, fun hx => hxy (by rw [hx, hpy]), by rw [hset, hpy, Set.pair_comm]⟩
  let jfun : Fin n → Fin n := fun p => Classical.choose (hpair p)
  have hjfun_ne : ∀ p, jfun p ≠ p := fun p => (Classical.choose_spec (hpair p)).1
  have hjfun_orbit : ∀ p, MulAction.orbit E p = {p, jfun p} :=
    fun p => (Classical.choose_spec (hpair p)).2
  have hinvol : ∀ p, jfun (jfun p) = p := by
    intro p
    have hmem : jfun p ∈ MulAction.orbit E p := by
      rw [hjfun_orbit p]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    have horb : MulAction.orbit E (jfun p) = MulAction.orbit E p :=
      MulAction.orbit_eq_iff.mpr hmem
    have hmem2 : jfun (jfun p) ∈ MulAction.orbit E (jfun p) := by
      rw [hjfun_orbit (jfun p)]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    rw [horb, hjfun_orbit p] at hmem2
    rcases (by simpa using hmem2 : jfun (jfun p) = p ∨ jfun (jfun p) = jfun p) with h | h
    · exact h
    · exact absurd h (hjfun_ne (jfun p))
  have hjperm : ∀ i, (Function.Involutive.toPerm jfun hinvol) i = jfun i :=
    fun i => congrFun (Function.Involutive.coe_toPerm hinvol) i
  refine ⟨Function.Involutive.toPerm jfun hinvol, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hjperm i]
    exact hjfun_ne i
  · intro i
    rw [hjperm i, hjperm (jfun i)]
    exact hinvol i
  · intro σ hσ i
    rw [hjperm i]
    have hmem : σ • i ∈ MulAction.orbit E i :=
      MulAction.mem_orbit_iff.mpr ⟨⟨σ, hσ⟩, Subgroup.mk_smul σ hσ i⟩
    rw [hjfun_orbit i] at hmem
    rcases (by simpa using hmem : σ • i = i ∨ σ • i = jfun i) with h | h
    · left; simpa [Equiv.Perm.smul_def] using h
    · right; simpa [Equiv.Perm.smul_def] using h
  · intro i
    rw [hjperm i]
    have hmem : jfun i ∈ MulAction.orbit E i := by
      rw [hjfun_orbit i]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hmem
    exact ⟨(σ : Equiv.Perm (Fin n)), σ.property, by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hσ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
