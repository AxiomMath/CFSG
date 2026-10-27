module

public import CFSG.Quasithin.Vol2.KGFact12618b
public import CFSG.Quasithin.Vol2.KGFact12614Cases

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] noncomputable def imgA {K : Subgroup Γ} {n : ℕ}
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) (X : Subgroup Γ) : Subgroup (Perm (Fin n)) :=
  (X.subgroupOf K).map ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)

omit [Finite Γ] in
theorem imgA_le {K : Subgroup Γ} {n : ℕ} (e : ↥K ≃* ↥(alternatingGroup (Fin n)))
    (X : Subgroup Γ) : imgA e X ≤ alternatingGroup (Fin n) := by
  rintro _ ⟨x, -, rfl⟩
  exact (e x).2

omit [Finite Γ] in
theorem injective_imgA_hom {K : Subgroup Γ} {n : ℕ} (e : ↥K ≃* ↥(alternatingGroup (Fin n))) :
    Function.Injective ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) :=
  (alternatingGroup (Fin n)).subtype_injective.comp e.injective

omit [Finite Γ] in
theorem imgA_injective {K : Subgroup Γ} {n : ℕ} (e : ↥K ≃* ↥(alternatingGroup (Fin n)))
    {X X' : Subgroup Γ} (hX : X ≤ K) (hX' : X' ≤ K) (h : imgA e X = imgA e X') : X = X' := by
  have h1 := (Subgroup.map_injective (injective_imgA_hom e)) h
  have h2 := congrArg (fun H : Subgroup ↥K => H.map K.subtype) h1
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hX, inf_eq_left.2 hX'] using h2

omit [Finite Γ] in
theorem card_imgA {K : Subgroup Γ} {n : ℕ} (e : ↥K ≃* ↥(alternatingGroup (Fin n)))
    {X : Subgroup Γ} (hXK : X ≤ K) : Nat.card ↥(imgA e X) = Nat.card ↥X := by
  unfold imgA
  rw [← Nat.card_congr ((X.subgroupOf K).equivMapOfInjective _ (injective_imgA_hom e)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]

omit [Finite Γ] in
theorem exists_imgA_eq_stab7 {K : Subgroup Γ} (e : ↥K ≃* ↥(alternatingGroup (Fin 7)))
    {X : Subgroup Γ} (hXK : X ≤ K) (hXs : IsSimpleGroup ↥X) (hX : Nat.card ↥X = 360) :
    ∃ p : Fin 7, imgA e X = stab7 p := by
  set f := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom with hf
  have eX : ↥(X.subgroupOf K) ≃* ↥(imgA e X) :=
    (X.subgroupOf K).equivMapOfInjective f (injective_imgA_hom e)
  have eXK : ↥(X.subgroupOf K) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXK
  have hc : Nat.card ↥(imgA e X) = 360 := by
    rw [← Nat.card_congr eX.toEquiv, Nat.card_congr eXK.toEquiv, hX]
  have hs : IsSimpleGroup ↥(imgA e X) :=
    (MulEquiv.isSimpleGroup_congr (eXK.symm.trans eX)).1 hXs
  have hsmall : ∀ M : Subgroup ↥(imgA e X), M.index ≤ 5 → M = ⊤ :=
    eq_top_of_index_le hs (fun m hm => by
      rw [hc]
      interval_cases m <;> decide)
  obtain ⟨p, hp⟩ := exists_fixed_seven hsmall (by rw [hc]; decide)
  exact ⟨p, eq_stab7 (imgA_le e X) hc hp⟩

omit [Finite Γ] in
theorem imgA_conj {K : Subgroup Γ} {n : ℕ} (e : ↥K ≃* ↥(alternatingGroup (Fin n)))
    {X : Subgroup Γ} (hXK : X ≤ K) {k : Γ} (hk : k ∈ K) :
    imgA e (X.map (MulAut.conj k).toMonoidHom) =
      (imgA e X).map (MulAut.conj ((e ⟨k, hk⟩ : ↥(alternatingGroup (Fin n))) :
        Perm (Fin n))).toMonoidHom := by
  ext σ
  constructor
  · rintro ⟨⟨x, hxK⟩, hxX, rfl⟩
    obtain ⟨y, hyX, hyx⟩ := hxX
    have hyK : y ∈ K := hXK hyX
    refine ⟨((e ⟨y, hyK⟩ : ↥(alternatingGroup (Fin n))) : Perm (Fin n)), ⟨⟨y, hyK⟩, hyX, rfl⟩, ?_⟩
    have hxy : (⟨x, hxK⟩ : ↥K) = ⟨k, hk⟩ * ⟨y, hyK⟩ * (⟨k, hk⟩)⁻¹ := by
      apply Subtype.ext
      show x = k * y * k⁻¹
      rw [← show K.subtype ⟨x, hxK⟩ = x from rfl, ← hyx]
      simp [MulAut.conj_apply]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, MulAut.conj_apply, hxy, map_mul, map_inv]
  · rintro ⟨τ, ⟨⟨y, hyK⟩, hyX, rfl⟩, rfl⟩
    have hkyK : k * y * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk)
    refine ⟨⟨k * y * k⁻¹, hkyK⟩, ⟨y, hyX, rfl⟩, ?_⟩
    have hxy : (⟨k * y * k⁻¹, hkyK⟩ : ↥K) = ⟨k, hk⟩ * ⟨y, hyK⟩ * (⟨k, hk⟩)⁻¹ := rfl
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, MulAut.conj_apply, hxy, map_mul, map_inv]

omit [Finite Γ] in
theorem map_conj_map_conj (X : Subgroup Γ) (a b : Γ) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem a7_branch {Y K T B : Subgroup Γ} (hYK : Y ≤ Subgroup.normalizer (K : Set Γ))
    (hKY : K ≤ Y) (hKs : IsSimpleGroup ↥K) (hA7 : IsAlt 7 ↥K) (hT : IsSylowTwoOf T Y)
    (hYeq : Y = K ⊔ T) (hO2 : pCoreOf 2 Y = ⊥) (hBK : B < K)
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) :
    ¬ 2 ∣ (Y ⊓ Subgroup.normalizer (B : Set Γ)).relIndex Y ∧
      centralizerSection T B (pCoreOf 2 B) = ⊥ := by
  classical
  obtain ⟨e⟩ := hA7
  obtain ⟨φ, hφs, hφk⟩ := hBiso
  have hD := KG12614.dataA6_of φ hφs (by exact hφk)
  obtain ⟨a, ha⟩ := hD.card
  have hK2520 : Nat.card ↥K = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hdvd : Nat.card ↥B ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hBK.le
  rw [ha, hK2520] at hdvd
  have ha0 : a = 0 := by
    have h7 : 2 ^ a ∣ 7 := Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 360)
      (by rw [show (7 : ℕ) * 360 = 2520 by norm_num]; exact hdvd)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h7 with h | h
    · exact (Nat.pow_eq_one.1 h).resolve_left (by norm_num)
    · exfalso
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0] at h
        norm_num at h
      · have h2 : 2 ∣ 2 ^ a := dvd_pow_self 2 h0.ne'
        rw [h] at h2
        norm_num at h2
  rw [ha0, pow_zero, one_mul] at ha
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hφinj : Function.Injective φ :=
    (Function.Surjective.bijective_of_nat_card_le hφs (by rw [ha, hA6])).1
  have hBs : IsSimpleGroup ↥B :=
    (MulEquiv.isSimpleGroup_congr (MulEquiv.ofBijective φ ⟨hφinj, hφs⟩)).2
      (alternatingGroup.isSimpleGroup (by simp))
  have hO2B : pCoreOf 2 B = ⊥ := by
    have h1 : CFSG.Open.pCore 2 ↥B = ⊥ := by
      rw [← hφk]
      exact (MonoidHom.ker_eq_bot_iff φ).2 hφinj
    unfold pCoreOf
    rw [h1, Subgroup.map_bot]
  have hnc : ∃ x y : ↥K, x * y ≠ y * x := by
    refine ⟨e.symm ⟨swap 0 1 * swap 0 2, Perm.mem_alternatingGroup.2 (by decide)⟩,
      e.symm ⟨swap 0 1 * swap 0 3, Perm.mem_alternatingGroup.2 (by decide)⟩, fun h => ?_⟩
    have h1 := congrArg (fun x => ((e x : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
    exact absurd h1 (by decide)
  have hCY := inf_centralizer_eq_bot hYK hKs hnc hT hYeq hO2
  obtain ⟨p, hp⟩ := exists_imgA_eq_stab7 e hBK.le hBs ha
  have hconj : ∀ y ∈ Y, ∃ k ∈ K, k⁻¹ * y ∈ Subgroup.normalizer (B : Set Γ) := by
    intro y hy
    set By := B.map (MulAut.conj y).toMonoidHom with hBy
    have hByK : By ≤ K := by
      rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hYK hy) b).1 (hBK.le hb)
    have eBy : ↥B ≃* ↥By := B.equivMapOfInjective _ (MulAut.conj y).injective
    have hBys : IsSimpleGroup ↥By := (MulEquiv.isSimpleGroup_congr eBy).1 hBs
    have hByc : Nat.card ↥By = 360 := by rw [← Nat.card_congr eBy.toEquiv, ha]
    obtain ⟨q, hq⟩ := exists_imgA_eq_stab7 e hByK hBys hByc
    obtain ⟨g, hg, hgq⟩ := exists_alt7_apply_eq p q
    set k : Γ := ((e.symm ⟨g, hg⟩ : ↥K) : Γ) with hkdef
    have hk : k ∈ K := (e.symm ⟨g, hg⟩).2
    have hek : ((e ⟨k, hk⟩ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) = g := by
      have : (⟨k, hk⟩ : ↥K) = e.symm ⟨g, hg⟩ := rfl
      rw [this, MulEquiv.apply_symm_apply]
    have hBk : B.map (MulAut.conj k).toMonoidHom = By := by
      apply imgA_injective e (by
        rintro _ ⟨b, hb, rfl⟩
        exact K.mul_mem (K.mul_mem hk (hBK.le hb)) (K.inv_mem hk)) hByK
      rw [imgA_conj e hBK.le hk, hek, hp, conj_stab7, hgq, hq]
    refine ⟨k, hk, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show B.map (MulAut.conj (k⁻¹ * y)).toMonoidHom = B
    rw [← map_conj_map_conj B y k⁻¹, ← hBy, ← hBk, map_conj_map_conj, inv_mul_cancel]
    ext x
    simp
  set N := Y ⊓ Subgroup.normalizer (B : Set Γ) with hN
  have hKN : K ⊓ N = B := by
    have hBle : B ≤ K ⊓ N := le_inf hBK.le (le_inf (hBK.le.trans hKY) Subgroup.le_normalizer)
    have hne : K ⊓ N ≠ K := by
      intro h
      have hBn : (B.subgroupOf K).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have hg : (g : Γ) ∈ K ⊓ N := by rw [h]; exact g.2
        exact (Subgroup.mem_normalizer_iff.1 hg.2.2 _).1 hn⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf K) with h1 | h1
      · have hB1 : B = ⊥ := by
          have h2 := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h1)
          rwa [inf_eq_left.2 hBK.le] at h2
        have := ha
        rw [hB1, Subgroup.card_bot] at this
        omega
      · exact hBK.ne (le_antisymm hBK.le (Subgroup.subgroupOf_eq_top.1 h1))
    have h1 := Subgroup.card_dvd_of_le hBle
    have h2 := Subgroup.card_dvd_of_le (inf_le_left : K ⊓ N ≤ K)
    rw [ha] at h1
    rw [hK2520] at h2
    have h3 : Nat.card ↥(K ⊓ N) ≠ 2520 := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hK2520]))
    obtain ⟨c, hc⟩ := h1
    obtain ⟨d, hd⟩ := h2
    have hc1 : c = 1 := by
      have : 360 * (c * d) = 360 * 7 := by rw [← mul_assoc, ← hc, ← hd]
      have hcd : c * d = 7 := by omega
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 ⟨d, hcd.symm⟩ with h | h
      · exact h
      · exfalso
        exact h3 (by rw [hc, h])
    exact (Subgroup.eq_of_le_of_card_ge hBle (by rw [hc, hc1, mul_one, ha])).symm
  refine ⟨?_, ?_⟩
  ·
    set K' := K.subgroupOf Y with hK'
    set N' := N.subgroupOf Y with hN'
    have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYK
    have hsup : N' ⊔ K' = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨y, hy⟩ -
      obtain ⟨k, hk, hkn⟩ := hconj y hy
      have hky : k⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem (hKY hk)) hy
      have e1 : (⟨y, hy⟩ : ↥Y) = ⟨k, hKY hk⟩ * ⟨k⁻¹ * y, hky⟩ := Subtype.ext (by simp)
      rw [e1, sup_comm]
      exact Subgroup.mul_mem_sup (show (⟨k, hKY hk⟩ : ↥Y) ∈ K' from hk)
        (show (⟨k⁻¹ * y, hky⟩ : ↥Y) ∈ N' from ⟨hky, hkn⟩)
    have h1 := Subgroup.relIndex_sup_right N' K'
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 := K'.card_mul_index
    have h3 := Subgroup.relIndex_mul_card K' N'
    have h4 := Subgroup.relIndex_mul_card N Y
    rw [inf_eq_left.2 (inf_le_left : N ≤ Y)] at h4
    have cK : Nat.card ↥K' = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv
    have cN : Nat.card ↥N' = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ≤ Y)).toEquiv
    have cKN : Nat.card ↥(K' ⊓ N') = Nat.card ↥(K ⊓ N) := Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2.1, x.2.2⟩
        invFun := fun x => ⟨⟨x.1, hKY x.2.1⟩, x.2.1, x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [cK, hK2520] at h2
    rw [cN, cKN, hKN, ha, ← h1] at h3
    have hNpos : 0 < Nat.card ↥N := Nat.card_pos
    have h7 : N.relIndex Y = 7 := by
      have : N.relIndex Y * Nat.card ↥N = 7 * Nat.card ↥N := by
        rw [h4, ← h2, ← h3]
        ring
      exact Nat.eq_of_mul_eq_mul_right hNpos this
    rw [h7]
    decide
  ·
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htT, htN, -, htc⟩ := ht
    rw [hO2B] at htc
    have htY : t ∈ Y := hT.1 htT
    obtain ⟨π, hπ⟩ := exists_perm_conj (by norm_num) (by norm_num) e (hYK htY)
    have hπ1 : π = 1 := by
      refine eq_one_of_commute_stab7 (p := p) fun τ hτ => ?_
      rw [← hp] at hτ
      obtain ⟨⟨b, hbK⟩, hbB, rfl⟩ := hτ
      have hbt : t * b * t⁻¹ = b := by
        have h1 := htc b hbB
        rw [Subgroup.mem_bot] at h1
        calc t * b * t⁻¹ = (b * t * b⁻¹ * t⁻¹)⁻¹ * b := by group
          _ = b := by rw [h1, inv_one, one_mul]
      have h2 := hπ b hbK
      have h3 : (⟨t * b * t⁻¹, (Subgroup.mem_normalizer_iff.1 (hYK htY) b).1 hbK⟩ : ↥K) =
          ⟨b, hbK⟩ := Subtype.ext hbt
      rw [h3] at h2
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype]
      calc π * ((e ⟨b, hbK⟩ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) =
          (π * ((e ⟨b, hbK⟩ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) * π⁻¹) * π := by
            group
        _ = _ := by rw [← h2]
    have htK : t ∈ Y ⊓ Subgroup.centralizer (K : Set Γ) := by
      refine ⟨htY, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have h1 := hπ k hk
      rw [hπ1, one_mul, inv_one, mul_one] at h1
      have h2 : (⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.1 (hYK htY) k).1 hk⟩ : ↥K) =
          ⟨k, hk⟩ := e.injective (Subtype.ext h1)
      have h3 : t * k * t⁻¹ = k := congrArg Subtype.val h2
      calc k * t = t * k * t⁻¹ * t := by rw [h3]
        _ = t * k := by group
    rw [hCY, Subgroup.mem_bot] at htK
    exact htK

end CFSG.Quasithin.H13.KG12618
