module

public import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec16.Crit167

open CFSG Subgroup Matrix
open scoped commutatorElement MatrixGroups

variable {r : ℕ} [hr : Fact r.Prime]

theorem pgl_tame_cases_alt {p : ℕ} [hp : Fact p.Prime] {k : Type*}
    [Field k] [Finite k] [CharP k p] (J : Subgroup PGL(Fin 2, k)) (hJ : ¬ p ∣ Nat.card J) :
    IsCyclic J ∨ (∃ z : ℕ, Nonempty (J ≃* DihedralGroup z)) ∨
      Nat.card J = 12 ∨ Nat.card J = 24 ∨ Nonempty (J ≃* alternatingGroup (Fin 5)) := by
  have := Fintype.ofFinite k
  let E := FiniteField.Extension k p 2
  have := Fintype.ofFinite E
  have hEcard : Nat.card E = Nat.card k ^ 2 := FiniteField.natCard_extension k p 2
  obtain ⟨f, -, hkcard⟩ := FiniteField.card k p
  have hEp : Nat.card E = p ^ (2 * (f : ℕ)) := by
    rw [hEcard, Nat.card_eq_fintype_card, hkcard, ← pow_mul, mul_comm]
  have hsq : ∀ x : k, IsSquare (algebraMap k E x) :=
    CFSG.LinearGroups.isSquare_algebraMap_of_card_eq_sq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard])
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := E)
  set J₁ := J.map (CFSG.LinearGroups.pglExtend k E)
  have hJ₁ : J₁ ≤ ι.range := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LinearGroups.pglExtend_mem_range_toPGL hsq x
  set H : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) E) := J₁.comap ι
  have hmap : H.map ι = J₁ := Subgroup.map_comap_eq_self hJ₁
  let eH : H ≃* J :=
    ((H.equivMapOfInjective ι ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (MulEquiv.subgroupCongr hmap)).trans
      (J.equivMapOfInjective (CFSG.LinearGroups.pglExtend k E)
        CFSG.LinearGroups.pglExtend_injective).symm
  have hcard : Nat.card H = Nat.card J := Nat.card_congr eH.toEquiv
  have hHp : ¬ p ∣ Nat.card H := hcard ▸ hJ
  rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hEp H hHp with
    ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_surjective eH.toMonoidHom eH.surjective)
  · exact Or.inr (Or.inl ⟨z, ⟨eH.symm.trans e⟩⟩)
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [← hcard, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [← hcard, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨eH.symm.trans e⟩)))

open CFSG.RankThree.SubgroupLists (upperGL coe_upperGL) in
theorem commutator_le_zpowers_of_le_normalizer' {H : Subgroup (GL (Fin 2) (ZMod r))}
    {v₀ : GL (Fin 2) (ZMod r)} (hv₀p : v₀ ^ r = 1) (hv₀1 : v₀ ≠ 1)
    (hHP : H ≤ normalizer ((zpowers v₀ : Subgroup (GL (Fin 2) (ZMod r))) :
      Set (GL (Fin 2) (ZMod r)))) :
    ⁅H, H⁆ ≤ zpowers v₀ := by
  classical
  obtain ⟨g, hg⟩ := CFSG.RankThree.SubgroupLists.exists_conj_transvection v₀ hv₀p hv₀1
  have hconj : (MulAut.conj g⁻¹) v₀ = upperGL 1 := by
    rw [MulAut.conj_apply, inv_inv]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_upperGL, Matrix.mul_assoc, hg, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  set φ := (MulAut.conj g⁻¹).toMonoidHom
  have hH' : H.map φ ≤ normalizer ((zpowers (upperGL (1 : ZMod r)) :
      Subgroup (GL (Fin 2) (ZMod r))) : Set (GL (Fin 2) (ZMod r))) := by
    refine (Subgroup.map_mono hHP).trans ?_
    have h := le_normalizer_map (H := zpowers v₀) φ
    rwa [MonoidHom.map_zpowers, show φ v₀ = upperGL 1 from hconj] at h
  have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
    (KFacts.KP10.commutator_le_zpowers_of_le_normalizer hH')
  have hid : (MulAut.conj g).toMonoidHom.comp φ = MonoidHom.id _ := by
    ext x : 1
    simp [φ, MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_commutator, Subgroup.map_map, hid, Subgroup.map_id,
    MonoidHom.map_zpowers] at h1
  have hv : (MulAut.conj g).toMonoidHom (upperGL 1) = v₀ := by
    rw [← hconj]
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hv]
  exact h1

theorem eq_one_of_mem_center_of_det_eq_one {g : GL (Fin 2) (ZMod r)}
    (hg : g ∈ center (GL (Fin 2) (ZMod r))) (hdet : Matrix.GeneralLinearGroup.det g = 1)
    (hodd : Nat.Coprime (orderOf g) 2) : g = 1 := by
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hg
  have hg2 : g ^ 2 = 1 := by
    apply Units.ext
    have hdet' : (g : Matrix (Fin 2) (Fin 2) (ZMod r)).det = 1 := by
      have := congrArg Units.val hdet
      simpa using this
    rw [← ha] at hdet'
    simp only [Matrix.det_fin_two, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0), mul_zero] at hdet'
    have haa : a * a = 1 := by linear_combination hdet'
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← ha, sq, ← map_mul, haa, map_one]
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  have : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd hodd h1
  exact orderOf_eq_one_iff.mp this

theorem exists_comm_or_alt (H : Subgroup (GL (Fin 2) (ZMod r)))
    (hpH : ¬ r ∣ Nat.card H) :
    (∃ C : Subgroup H, (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) ∧ C.index ∣ 2) ∨
      Nat.card (H.map ProjGenLinGroup.mk) = 12 ∨ Nat.card (H.map ProjGenLinGroup.mk) = 24 ∨
        Nonempty (H.map ProjGenLinGroup.mk ≃* alternatingGroup (Fin 5)) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod r)) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set π := ProjGenLinGroup.mk.subgroupMap H
  have hπ : Function.Surjective π := ProjGenLinGroup.mk.subgroupMap_surjective H
  have hJ : ¬ r ∣ Nat.card (H.map ProjGenLinGroup.mk) := fun h =>
    hpH (h.trans (Subgroup.card_dvd_of_surjective (f := π) hπ))
  rcases pgl_tame_cases_alt (p := r) (k := ZMod r) _ hJ with hcyc | ⟨z, ⟨e⟩⟩ | h
  · have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center π
      (KFacts.KP10.ker_le_center H)
    exact Or.inl ⟨⊤, fun a _ b _ => this.is_comm.comm a b, by simp⟩
  · refine Or.inl ⟨((zpowers (DihedralGroup.r 1 : DihedralGroup z)).comap e.toMonoidHom).comap π,
      fun a ha b hb => ?_, ?_⟩
    · set C := ((zpowers (DihedralGroup.r 1 : DihedralGroup z)).comap e.toMonoidHom).comap π
      let ψ : C →* zpowers (DihedralGroup.r 1 : DihedralGroup z) :=
        ((e.toMonoidHom.comp π).comp C.subtype).codRestrict _ fun c => c.2
      have hψ : ψ.ker ≤ center C := by
        intro c hc
        have h1 : e (π c) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hc)
        have h2 : π c = 1 := by simpa using h1
        have h3 : (c : H) ∈ center H := KFacts.KP10.ker_le_center H (MonoidHom.mem_ker.2 h2)
        exact Subgroup.mem_center_iff.2 fun y =>
          Subtype.ext (Subgroup.mem_center_iff.1 h3 (y : H))
      have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ψ hψ
      exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rw [Subgroup.index_comap_of_surjective _ hπ,
        Subgroup.index_comap_of_surjective _ e.surjective]
      have hz : z ≠ 0 := by
        rintro rfl
        have h1 := Nat.card_congr e.toEquiv
        rw [DihedralGroup.nat_card, mul_zero] at h1
        exact Nat.card_pos.ne' h1
      have : NeZero z := ⟨hz⟩
      have h := (zpowers (DihedralGroup.r 1 : DihedralGroup z)).card_mul_index
      rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h
      rw [show (zpowers (DihedralGroup.r 1 : DihedralGroup z)).index = 2 by
        have := Nat.pos_of_ne_zero hz
        nlinarith]
  · exact Or.inr h

theorem commutatorElement_pow_eq_one_of_index_dvd_two {H : Type*} [Group H] {C : Subgroup H}
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hCi : C.index ∣ 2) {b : H} {k : ℕ} (hk : Odd k)
    (hbk : b ^ k = 1) (t : H) : ⁅b, t⁆ ^ k = 1 := by
  have hCn : C.Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hCi with h | h
    · rw [Subgroup.index_eq_one.mp h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have hsq : ∀ x : H, x ^ 2 ∈ C := by
    intro x
    obtain ⟨m, hm⟩ := hCi
    have h : x ^ 2 = (x ^ C.index) ^ m := by rw [← pow_mul, ← hm]
    rw [h]
    exact pow_mem (Subgroup.pow_index_mem C x) m
  have hbC : b ∈ C := by
    obtain ⟨m, rfl⟩ := hk
    have h : b = (b ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hbk, one_mul]
    rw [h]
    exact pow_mem (hsq b) _
  obtain ⟨n, hn⟩ : ∃ n, ⁅b, t⁆ = n := ⟨_, rfl⟩
  have hnC : n ∈ C := by
    have h : n = b * (t * b⁻¹ * t⁻¹) := by
      rw [← hn, commutatorElement_def]
      group
    rw [h]
    exact mul_mem hbC (hCn.conj_mem _ (inv_mem hbC) t)
  have hbtn : b * t * b⁻¹ = n * t := by
    rw [← hn, commutatorElement_def]
    group
  have hcomm : Commute b n := hC b hbC n hnC
  have key : ∀ j : ℕ, b ^ j * t * (b ^ j)⁻¹ = n ^ j * t := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc b ^ (j + 1) * t * (b ^ (j + 1))⁻¹ = b * (b ^ j * t * (b ^ j)⁻¹) * b⁻¹ := by group
        _ = (b * n ^ j) * t * b⁻¹ := by rw [ih]; group
        _ = n ^ j * (b * t * b⁻¹) := by rw [(hcomm.pow_right j).eq]; group
        _ = n ^ (j + 1) * t := by rw [hbtn, pow_succ]; group
  rw [hn]
  have h := key k
  rw [hbk, one_mul, inv_one, mul_one] at h
  exact mul_eq_right.mp h.symm

theorem eq_one_of_dvd_two_pow_mul_three {d a : ℕ} (hd : d ∣ 2 ^ a * 3) (h2 : Nat.Coprime d 2)
    (h3 : ¬ 3 ∣ d) : d = 1 := by
  have h3' : d ∣ 3 := (Nat.Coprime.pow_right a h2).dvd_of_dvd_mul_left hd
  rcases (Nat.dvd_prime Nat.prime_three).mp h3' with h | h
  · exact h
  · subst h
    exact absurd (dvd_refl 3) h3

theorem ks167GL2 : KS167GL2 := by
  intro p hp hp5 T B hT3 hB hBN hTB
  have : Fact p.Prime := ⟨hp⟩
  classical
  have hdet : ∀ t ∈ T, Matrix.GeneralLinearGroup.det t = 1 := by
    have h : ⁅T, B⁆ ≤ (Matrix.GeneralLinearGroup.det :
        GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
        mul_comm]
    intro t ht
    rw [← hTB] at ht
    exact h ht
  have hbot : (∀ t ∈ T, Nat.Coprime (orderOf t) 2 → t = 1) →
      IsPGroup p (CFSG.GH74.GLS.oResidual 2 T) := by
    intro h
    refine IsPGroup.of_bot.to_le ?_
    rw [CFSG.GH74.GLS.oResidual, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    apply Subtype.ext
    refine h x x.2 ?_
    rw [Subgroup.orderOf_coe]
    exact hx
  have hcen : (∀ t ∈ T, Nat.Coprime (orderOf t) 2 → ProjGenLinGroup.mk t = 1) →
      IsPGroup p (CFSG.GH74.GLS.oResidual 2 T) := by
    intro h
    refine hbot fun t ht hodd => ?_
    exact eq_one_of_mem_center_of_det_eq_one (ProjGenLinGroup.mk_eq_one.mp (h t ht hodd))
      (hdet t ht) hodd
  by_cases hpT : p ∣ Nat.card T
  ·
    rcases CFSG.RankThree.SubgroupLists.dickson_gl_two T hpT with ⟨P, hPn, hPc⟩ | hSL
    swap
    · exact absurd (KFacts.KP10.three_dvd_card_of_statedSL_le hSL) hT3
    obtain ⟨v, -, hvp, hv1, hvz⟩ := CFSG.RankThree.SubgroupLists.exists_zpowers_eq_of_card_eq hPc
    have hP₀ : (P : Subgroup T).map T.subtype = zpowers (v : GL (Fin 2) (ZMod p)) := by
      rw [← hvz, MonoidHom.map_zpowers]
      rfl
    have hchar := Sylow.characteristic_of_normal P hPn
    have hN : normalizer (T : Set (GL (Fin 2) (ZMod p))) ≤
        normalizer ((zpowers (v : GL (Fin 2) (ZMod p)) : Subgroup (GL (Fin 2) (ZMod p))) :
          Set (GL (Fin 2) (ZMod p))) := by
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (P : Subgroup T)
      rwa [hP₀] at h
    have hJ : T ⊔ B ≤ normalizer ((zpowers (v : GL (Fin 2) (ZMod p)) :
        Subgroup (GL (Fin 2) (ZMod p))) : Set (GL (Fin 2) (ZMod p))) :=
      sup_le (le_normalizer.trans hN) (hBN.trans hN)
    have hv₀p : (v : GL (Fin 2) (ZMod p)) ^ p = 1 := congrArg Subtype.val hvp
    have hv₀1 : (v : GL (Fin 2) (ZMod p)) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hTle : T ≤ zpowers (v : GL (Fin 2) (ZMod p)) := by
      calc T = ⁅T, B⁆ := hTB.symm
        _ ≤ ⁅T ⊔ B, T ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_right
        _ ≤ _ := commutator_le_zpowers_of_le_normalizer' hv₀p hv₀1 hJ
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hTle (x : T).2)
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hv₀p,
      _root_.one_zpow]
  ·
    have hp3 : p ≠ 3 := by omega
    have hpB : ¬ p ∣ Nat.card B := by
      intro h
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hB
      rw [hn] at h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
    have hpJ : ¬ p ∣ Nat.card (T ⊔ B : Subgroup (GL (Fin 2) (ZMod p))) := by
      intro h
      have h' := h.trans (sup_comm T B ▸ Sec14.card_sup_dvd_card_mul hBN)
      rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
      · exact hpB h1
      · exact hpT h1
    have hsmall : ∀ a : ℕ, Nat.card ((T ⊔ B).map ProjGenLinGroup.mk) = 2 ^ a * 3 →
        IsPGroup p (CFSG.GH74.GLS.oResidual 2 T) := by
      intro a ha
      refine hcen fun t ht hodd => ?_
      have hmem : ProjGenLinGroup.mk t ∈ (T ⊔ B).map ProjGenLinGroup.mk :=
        Subgroup.mem_map_of_mem _ ((le_sup_left : T ≤ T ⊔ B) ht)
      have h1 : orderOf (ProjGenLinGroup.mk t) ∣ 2 ^ a * 3 :=
        ha ▸ Subgroup.orderOf_dvd_natCard _ hmem
      have h2 : orderOf (ProjGenLinGroup.mk t) ∣ orderOf t := orderOf_map_dvd _ t
      have h3 : ¬ 3 ∣ orderOf (ProjGenLinGroup.mk t) := fun h =>
        hT3 ((h.trans h2).trans (Subgroup.orderOf_dvd_natCard T ht))
      exact orderOf_eq_one_iff.mp (eq_one_of_dvd_two_pow_mul_three h1
        (Nat.Coprime.coprime_dvd_left h2 hodd) h3)
    rcases exists_comm_or_alt (T ⊔ B) hpJ with ⟨C, hC, hCi⟩ | h12 | h24 | hA5
    ·
      refine hbot fun t ht _ => ?_
      have hTbot : T = ⊥ := by
        rw [← hTB, eq_bot_iff, Subgroup.commutator_le]
        intro t' ht' b hb
        rw [Subgroup.mem_bot]
        obtain ⟨m, hm⟩ := hB ⟨b, hb⟩
        have hbm : b ^ 3 ^ m = 1 := congrArg Subtype.val hm
        have h := commutatorElement_pow_eq_one_of_index_dvd_two hC hCi
          (b := ⟨b, (le_sup_right : B ≤ T ⊔ B) hb⟩) (k := 3 ^ m) (Odd.pow ⟨1, rfl⟩)
          (Subtype.ext hbm) ⟨t', (le_sup_left : T ≤ T ⊔ B) ht'⟩
        have h' : ⁅b, t'⁆ ^ 3 ^ m = 1 := congrArg Subtype.val h
        have hnT : ⁅b, t'⁆ ∈ T := by
          rw [commutatorElement_def]
          exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hBN hb) t').mp ht') (inv_mem ht')
        have hord : orderOf ⁅b, t'⁆ = 1 := by
          have h1 : orderOf ⁅b, t'⁆ ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one h'
          have h2 : orderOf ⁅b, t'⁆ ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T hnT
          have hcop : Nat.Coprime (3 ^ m) (Nat.card T) :=
            Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT3)
          exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
        have h1 : ⁅b, t'⁆ = 1 := orderOf_eq_one_iff.mp hord
        rw [commutatorElement_eq_one_iff_mul_comm] at h1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact h1.symm
      rw [hTbot] at ht
      exact Subgroup.mem_bot.mp ht
    · exact hsmall 2 (h12.trans (by norm_num))
    · exact hsmall 3 (h24.trans (by norm_num))
    ·
      refine hcen fun t ht _ => ?_
      obtain ⟨e⟩ := hA5
      have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      have : IsSimpleGroup ((T ⊔ B).map ProjGenLinGroup.mk) := MulEquiv.isSimpleGroup e
      have hTJ : T.map ProjGenLinGroup.mk ≤ (T ⊔ B).map ProjGenLinGroup.mk :=
        Subgroup.map_mono le_sup_left
      set N := (T.map ProjGenLinGroup.mk).subgroupOf ((T ⊔ B).map ProjGenLinGroup.mk) with hNdef
      have hnorm : N.Normal := by
        rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hTJ]
        have hJN : T ⊔ B ≤ normalizer (T : Set (GL (Fin 2) (ZMod p))) := sup_le le_normalizer hBN
        exact (Subgroup.map_mono hJN).trans (le_normalizer_map _)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
      · have hmem : (⟨ProjGenLinGroup.mk t,
            Subgroup.mem_map_of_mem _ ((le_sup_left : T ≤ T ⊔ B) ht)⟩ :
            (T ⊔ B).map ProjGenLinGroup.mk) ∈ N :=
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ ht)
        rw [h, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      · exfalso
        have hle := Subgroup.subgroupOf_eq_top.mp h
        have h60 : Nat.card ((T ⊔ B).map ProjGenLinGroup.mk) = 60 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
          decide
        apply hT3
        have h1 := Subgroup.card_dvd_of_le hle
        rw [h60] at h1
        exact (dvd_trans (by norm_num : 3 ∣ 60) h1).trans (Subgroup.card_map_dvd T _)

end CFSG.RankThree.PartTwo.Sec16.Crit167
