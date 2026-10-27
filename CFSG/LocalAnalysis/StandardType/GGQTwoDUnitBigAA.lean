module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.LinearAlgebra.SteinbergBQ

noncomputable def qtwoDB41_supp {m : ℕ} (H : Submodule (ZMod 3) (DVec m)) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => dBasis m i ∉ H)

lemma qtwoDB41_mem_supp {m : ℕ} {H : Submodule (ZMod 3) (DVec m)} {i : Fin m} :
    i ∈ qtwoDB41_supp H ↔ dBasis m i ∉ H := by
  simp [qtwoDB41_supp]

lemma qtwoDB41_finrank_dvec (m : ℕ) : Module.finrank (ZMod 3) (DVec m) = m := by
  simpa only [DVec] using Module.finrank_fin_fun (R := ZMod 3) (n := m)

lemma qtwoDB41_dual {m : ℕ} (hm : 1 ≤ m) {H : Submodule (ZMod 3) (DVec m)}
    (hH : Module.finrank (ZMod 3) H = m - 1) :
    ∃ f : Module.Dual (ZMod 3) (DVec m), f ≠ 0 ∧ H = LinearMap.ker f := by
  have htop : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hEq
    have h1 : Module.finrank (ZMod 3) H = m := by
      rw [hEq, finrank_top, qtwoDB41_finrank_dvec]
    omega
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (p := H) htop inferInstance
  refine ⟨f, hf, ?_⟩
  have hle : H ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    have : f x ∈ H.map f := Submodule.mem_map_of_mem hx
    rwa [hmap, Submodule.mem_bot] at this
  have hfin : Module.finrank (ZMod 3) (LinearMap.ker f) = m - 1 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero (K := ZMod 3) (V₁ := DVec m) hf
    rw [qtwoDB41_finrank_dvec] at this
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hH, hfin])

lemma qtwoDB41_eq_smul_of_ker_eq {m : ℕ} {f g : Module.Dual (ZMod 3) (DVec m)}
    (h : LinearMap.ker f = LinearMap.ker g) (hf : f ≠ 0) :
    ∃ mu : ZMod 3, g = mu • f := by
  classical
  have hnot : ¬ ∀ x, f x = 0 := fun hall => hf (LinearMap.ext hall)
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  have hgx : g x ≠ 0 := by
    intro hgx0
    have hxk : x ∈ LinearMap.ker g := LinearMap.mem_ker.mpr hgx0
    rw [← h] at hxk
    exact hx (LinearMap.mem_ker.mp hxk)
  refine ⟨g x / f x, ?_⟩
  have hmu : g x / f x ≠ 0 := div_ne_zero hgx hx
  have h1 : LinearMap.ker g = LinearMap.ker ((g x / f x) • f) := by
    rw [LinearMap.ker_smul _ _ hmu, ← h]
  have h2 : g x = ((g x / f x) • f) x := by
    rw [LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hx]
  exact Module.Dual.eq_of_ker_eq_of_apply_eq x h1 h2 hgx

lemma qtwoDB41_dSign_mem_dEven {m : ℕ} {a b : Fin m} (hab : a ≠ b) :
    dSign m a b ∈ dEven m := by
  have h : dSign m a b = (dPerm m (Equiv.swap a b))⁻¹ * dTau m true a b := by
    rw [dTau, if_pos rfl]
    group
  rw [h]
  exact (dEven m).mul_mem ((dEven m).inv_mem (dPerm_mem_dEven m _)) (dTau_mem_dEven m true hab)


lemma qtwoDB41_dPerm_symm_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (dPerm m σ).symm (dBasis m i) = dBasis m (σ.symm i) := by
  rw [LinearEquiv.symm_apply_eq, dPerm_apply, Equiv.apply_symm_apply]

lemma qtwoDB41_dSign_symm_apply {m : ℕ} (a b i : Fin m) :
    (dSign m a b).symm (dBasis m i) = dSign m a b (dBasis m i) := by
  rw [LinearEquiv.symm_apply_eq, dSign_apply, map_smul, dSign_apply, smul_smul]
  split_ifs <;> norm_num

lemma qtwoDB41_dPerm_mem_stab {m : ℕ} {c : Fin m} {σ : Equiv.Perm (Fin m)}
    (hσ : σ c = c) : dPerm m σ ∈ dEvenStab m (Pi.single c 1) := by
  refine ⟨dPerm_mem_dEven m σ, ?_⟩
  have hb : Pi.single c 1 = dBasis m c := (Pi.basisFun_apply (ZMod 3) (Fin m) c).symm
  rw [hb, dPerm_apply, hσ]

lemma qtwoDB41_dSign_mem_stab {m : ℕ} {c a b : Fin m} (hab : a ≠ b)
    (hca : a ≠ c) (hcb : b ≠ c) :
    dSign m a b ∈ dEvenStab m (Pi.single c 1) := by
  refine ⟨qtwoDB41_dSign_mem_dEven hab, ?_⟩
  have hb : Pi.single c 1 = dBasis m c := (Pi.basisFun_apply (ZMod 3) (Fin m) c).symm
  rw [hb, dSign_apply, if_neg (fun h => h.elim (fun h1 => hca h1.symm) (fun h2 => hcb h2.symm))]
  simp

lemma qtwoDB41_mem_supp_map_dPerm {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    (σ : Equiv.Perm (Fin m)) {i : Fin m} :
    i ∈ qtwoDB41_supp (H.map (dPerm m σ).toLinearMap) ↔
      i ∈ (qtwoDB41_supp H).map σ.toEmbedding := by
  simp only [qtwoDB41_mem_supp, Finset.mem_map_equiv, Submodule.mem_map_equiv,
    qtwoDB41_dPerm_symm_apply]

lemma qtwoDB41_map_swap_eq {m : ℕ} {B : Finset (Fin m)} {a k : Fin m}
    (ha : a ∈ B) (hk : k ∉ B) :
    B.map (Equiv.swap a k).toEmbedding = insert k (B.erase a) := by
  ext i
  have hs : (Equiv.swap a k).symm i = Equiv.swap a k i := by
    rw [Equiv.symm_apply_eq, Equiv.swap_apply_self]
  rw [Finset.mem_map_equiv, Finset.mem_insert, Finset.mem_erase, hs]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left]
    have hik : i ≠ k := fun h => hk (h ▸ ha)
    simp [hik, hk]
  · by_cases hik : i = k
    · subst hik
      rw [Equiv.swap_apply_right]
      simp [ha]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hik]
      simp [hia, hik]

lemma qtwoDB41_map_eq_ker {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    {f : Module.Dual (ZMod 3) (DVec m)} (hf : H = LinearMap.ker f)
    (w : DVec m ≃ₗ[ZMod 3] DVec m) :
    H.map w.toLinearMap = LinearMap.ker (f ∘ₗ w.symm.toLinearMap) := by
  rw [hf]
  ext x
  rw [Submodule.mem_map_equiv]
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

lemma qtwoDB41_mem_supp_map_dSign {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    {a b : Fin m} :
    qtwoDB41_supp (H.map (dSign m a b).toLinearMap) = qtwoDB41_supp H := by
  ext i
  rw [qtwoDB41_mem_supp, qtwoDB41_mem_supp, Submodule.mem_map_equiv,
    qtwoDB41_dSign_symm_apply, dSign_apply]
  have hiff : ((if i = a ∨ i = b then (-1 : ZMod 3) else 1) • dBasis m i ∈ H) ↔
      dBasis m i ∈ H := by
    by_cases hi : i = a ∨ i = b
    · rw [if_pos hi]
      simp
    · rw [if_neg hi]
      simp
  exact not_congr hiff

lemma qtwoDB41_dSign_ne {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    {f : Module.Dual (ZMod 3) (DVec m)} (hf : H = LinearMap.ker f)
    {a b c' : Fin m} (hab : a ≠ b) (hca : c' ≠ a) (hcb : c' ≠ b)
    (ha : f (dBasis m a) ≠ 0) (hb : f (dBasis m b) ≠ 0) (hc : f (dBasis m c') ≠ 0) :
    H.map (dSign m a b).toLinearMap ≠ H := by
  intro heq
  have hmap := qtwoDB41_map_eq_ker hf (dSign m a b)
  have hker : LinearMap.ker f = LinearMap.ker (f ∘ₗ (dSign m a b).symm.toLinearMap) := by
    rw [← hf, ← heq]
    exact hmap
  have hfne : f ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  obtain ⟨mu, hmu⟩ := qtwoDB41_eq_smul_of_ker_eq hker hfne
  have hmu_eq : mu = 1 := by
    have h1 := congrFun (congrArg DFunLike.coe hmu) (dBasis m c')
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearEquiv.coe_toLinearMap] at h1
    rw [qtwoDB41_dSign_symm_apply, dSign_apply, if_neg (by
      intro h; exact h.elim (fun h1 => hca h1) (fun h2 => hcb h2))] at h1
    simp only [one_smul] at h1
    have h1' : mu * f (dBasis m c') = 1 * f (dBasis m c') := by
      rw [one_mul]; exact h1.symm
    exact mul_right_cancel₀ hc h1'
  have h2 := congrFun (congrArg DFunLike.coe hmu) (dBasis m a)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, hmu_eq, one_mul,
    LinearEquiv.coe_toLinearMap] at h2
  rw [qtwoDB41_dSign_symm_apply, dSign_apply, if_pos (Or.inl rfl), map_smul] at h2
  have hzero : f (dBasis m a) = 0 := by
    have h2' : (-1 : ZMod 3) * f (dBasis m a) = f (dBasis m a) := by
      simpa using h2
    have hneg : -f (dBasis m a) = f (dBasis m a) := by simpa using h2'
    have hsum : (2 : ZMod 3) * f (dBasis m a) = 0 := by
      calc (2 : ZMod 3) * f (dBasis m a) = f (dBasis m a) + f (dBasis m a) := two_mul _
        _ = -f (dBasis m a) + f (dBasis m a) := by rw [hneg]
        _ = 0 := neg_add_cancel _
    have h2nz : (2 : ZMod 3) ≠ 0 := by decide
    exact (mul_eq_zero.mp hsum).resolve_left h2nz
  exact ha hzero


lemma qtwoDB41_supp_map_dPerm_eq {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    (σ : Equiv.Perm (Fin m)) :
    qtwoDB41_supp (H.map (dPerm m σ).toLinearMap) =
      (qtwoDB41_supp H).map σ.toEmbedding := by
  ext i; rw [qtwoDB41_mem_supp_map_dPerm]

lemma qtwoDB41_supp_card_le {m : ℕ} {c : Fin m} {H : Submodule (ZMod 3) (DVec m)}
    (hc : dBasis m c ∈ H) : (qtwoDB41_supp H).card ≤ m - 1 := by
  have hsub : qtwoDB41_supp H ⊆ Finset.univ.erase c := by
    intro i hi
    rw [Finset.mem_erase]
    exact ⟨fun hic => (qtwoDB41_mem_supp.mp hi) (hic ▸ hc), Finset.mem_univ i⟩
  calc (qtwoDB41_supp H).card ≤ (Finset.univ.erase c).card := Finset.card_le_card hsub
    _ = m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]

lemma qtwoDB41_supp_nonempty {m : ℕ} (hm : 1 ≤ m) {H : Submodule (ZMod 3) (DVec m)}
    (hfin : Module.finrank (ZMod 3) H = m - 1) : (qtwoDB41_supp H).Nonempty := by
  by_contra hemp
  have hempty : qtwoDB41_supp H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
  have hall : ∀ i, dBasis m i ∈ H := by
    intro i
    by_contra hi
    have : i ∈ qtwoDB41_supp H := qtwoDB41_mem_supp.mpr hi
    rw [hempty] at this
    exact Finset.notMem_empty i this
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← (dBasis m).sum_repr v]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hall i))
  have : Module.finrank (ZMod 3) H = m := by
    rw [htop, finrank_top, qtwoDB41_finrank_dvec]
  omega

lemma qtwoDB41_dSign_apply_of_ne {m : ℕ} (f : Module.Dual (ZMod 3) (DVec m))
    {a b i : Fin m} (hia : i ≠ a) (hib : i ≠ b) :
    f ((dSign m a b) (dBasis m i)) = f (dBasis m i) := by
  rw [dSign_apply, if_neg (fun h => h.elim hia hib), map_smul, one_smul]

lemma qtwoDB41_dSign_apply_self {m : ℕ} (f : Module.Dual (ZMod 3) (DVec m))
    {a b : Fin m} (hab : a ≠ b) :
    f ((dSign m a b) (dBasis m a)) = -f (dBasis m a) := by
  rw [dSign_apply, if_pos (Or.inl rfl), map_smul, smul_eq_mul]
  ring

lemma qtwoDB41_dSign_apply_right {m : ℕ} (f : Module.Dual (ZMod 3) (DVec m))
    {a b : Fin m} (hab : a ≠ b) :
    f ((dSign m a b) (dBasis m b)) = -f (dBasis m b) := by
  rw [dSign_apply, if_pos (Or.inr rfl), map_smul, smul_eq_mul]
  ring

lemma qtwoDB41_mem_supp_map_dSign' {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    {a b : Fin m} :
    qtwoDB41_supp (H.map (dSign m a b).toLinearMap) = qtwoDB41_supp H :=
  qtwoDB41_mem_supp_map_dSign

lemma qtwoDB41_map_dSign_ne {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    {f : Module.Dual (ZMod 3) (DVec m)} (hfker : H = LinearMap.ker f)
    {a b c' : Fin m} (hab : a ≠ b) (hca : c' ≠ a) (hcb : c' ≠ b)
    (ha : f (dBasis m a) ≠ 0) (hb : f (dBasis m b) ≠ 0) (hc : f (dBasis m c') ≠ 0) :
    H.map (dSign m a b).toLinearMap ≠ H :=
  qtwoDB41_dSign_ne hfker hab hca hcb ha hb hc


lemma qtwoDB41_dSign_symm_toLinearMap {m : ℕ} (a b : Fin m) :
    (dSign m a b).symm.toLinearMap = (dSign m a b).toLinearMap := by
  refine (dBasis m).ext fun i => ?_
  change (dSign m a b).symm (dBasis m i) = dSign m a b (dBasis m i)
  rw [qtwoDB41_dSign_symm_apply]

lemma qtwoDB41_exists_third {m : ℕ} {B : Finset (Fin m)} (hB : 3 ≤ B.card)
    {a b : Fin m} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    ∃ c' ∈ B, c' ≠ a ∧ c' ≠ b := by
  by_contra h
  have hsub : B ⊆ {a, b} := by
    intro x hx
    by_contra hxab
    apply h
    refine ⟨x, hx, ?_, ?_⟩
    · intro hxa; exact hxab (by simp [hxa])
    · intro hxb; exact hxab (by simp [hxb])
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
  omega

lemma qtwoDB41_exists_out {m : ℕ} {B : Finset (Fin m)} (hB : 4 < B.card)
    (a b d x : Fin m) : ∃ y ∈ B, y ∉ ({a, b, d, x} : Finset (Fin m)) := by
  by_contra h
  have hsub : B ⊆ ({a, b, d, x} : Finset (Fin m)) := by
    intro y hy
    by_contra hy'
    exact h ⟨y, hy, hy'⟩
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, d, x} : Finset (Fin m)).card ≤ 4 := by
    have h3 : ({a, b, d, x} : Finset (Fin m)).card ≤
        ({b, d, x} : Finset (Fin m)).card + 1 := Finset.card_insert_le a _
    have h4 : ({b, d, x} : Finset (Fin m)).card ≤
        ({d, x} : Finset (Fin m)).card + 1 := Finset.card_insert_le b _
    have h5 : ({d, x} : Finset (Fin m)).card ≤
        ({x} : Finset (Fin m)).card + 1 := Finset.card_insert_le d _
    have h6 : ({x} : Finset (Fin m)).card = 1 := Finset.card_singleton x
    omega
  omega

lemma qtwoDB41_dSign_family_inj {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    {f : Module.Dual (ZMod 3) (DVec m)} (hfker : H = LinearMap.ker f)
    {B : Finset (Fin m)} {a x x' : Fin m}
    (hfsupp : ∀ i, i ∈ B → f (dBasis m i) ≠ 0)
    (haB : a ∈ B) (hxB : x ∈ B) (hx'B : x' ∈ B)
    (hxa : x ≠ a) (hx'a : x' ≠ a)
    (heq : H.map (dSign m a x).toLinearMap = H.map (dSign m a x').toLinearMap) :
    x = x' := by
  by_contra hne
  have hker : LinearMap.ker (f ∘ₗ (dSign m a x).toLinearMap) =
      LinearMap.ker (f ∘ₗ (dSign m a x').toLinearMap) := by
    rw [← qtwoDB41_dSign_symm_toLinearMap, ← qtwoDB41_dSign_symm_toLinearMap,
      ← qtwoDB41_map_eq_ker hfker (dSign m a x), heq,
      qtwoDB41_map_eq_ker hfker (dSign m a x')]
  have hfx : f (dBasis m x) ≠ 0 := hfsupp x hxB
  have hfa : f (dBasis m a) ≠ 0 := hfsupp a haB
  have hgx0 : f ∘ₗ (dSign m a x).toLinearMap ≠ 0 := by
    intro h0
    have h1 := congrFun (congrArg DFunLike.coe h0) (dBasis m a)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h1
    rw [qtwoDB41_dSign_apply_self f (Ne.symm hxa)] at h1
    exact hfa (by simpa using (neg_eq_zero.mp h1))
  obtain ⟨mu, hmu⟩ := qtwoDB41_eq_smul_of_ker_eq hker hgx0
  have hma : mu = 1 := by
    have h1 := congrFun (congrArg DFunLike.coe hmu) (dBasis m a)
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap] at h1
    rw [qtwoDB41_dSign_apply_self f (Ne.symm hx'a),
      qtwoDB41_dSign_apply_self f (Ne.symm hxa)] at h1
    have h1' : mu * (-f (dBasis m a)) = 1 * (-f (dBasis m a)) := by
      rw [one_mul]; exact h1.symm
    exact mul_right_cancel₀ (neg_ne_zero.mpr hfa) h1'
  have h1 := congrFun (congrArg DFunLike.coe hmu) (dBasis m x)
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at h1
  rw [qtwoDB41_dSign_apply_of_ne f hxa hne,
    qtwoDB41_dSign_apply_right f (Ne.symm hxa), hma, one_mul] at h1
  have hneg : f (dBasis m x) = -f (dBasis m x) := by simpa using h1
  have hsum : (2 : ZMod 3) * f (dBasis m x) = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  have h2nz : (2 : ZMod 3) ≠ 0 := by decide
  exact hfx ((mul_eq_zero.mp hsum).resolve_left h2nz)

lemma qtwoDB41_dSign_ne_H0 {m : ℕ} {H : Submodule (ZMod 3) (DVec m)}
    {f : Module.Dual (ZMod 3) (DVec m)} (hfker : H = LinearMap.ker f)
    {B : Finset (Fin m)} (hB : 3 ≤ B.card) (hfsupp : ∀ i, i ∈ B → f (dBasis m i) ≠ 0)
    {a x : Fin m} (ha : a ∈ B) (hx : x ∈ B) (hxa : x ≠ a) :
    H.map (dSign m a x).toLinearMap ≠ H := by
  obtain ⟨c', hc'B, hc'a, hc'x⟩ := qtwoDB41_exists_third hB ha hx (Ne.symm hxa)
  exact qtwoDB41_dSign_ne hfker (Ne.symm hxa) hc'a hc'x
    (hfsupp a ha) (hfsupp x hx) (hfsupp c' hc'B)

lemma qtwoDB41_dSign_ne_dSign {m : ℕ} {f : Module.Dual (ZMod 3) (DVec m)}
    {B : Finset (Fin m)} {a b d x y : Fin m}
    (hf : ∀ i, i ∈ B → f (dBasis m i) ≠ 0)
    (haB : a ∈ B) (hyB : y ∈ B)
    (hab : a ≠ b) (had : a ≠ d) (hax : a ≠ x)
    (hyb : y ≠ b) (hyd : y ≠ d) (hya : y ≠ a) (hyx : y ≠ x) :
    ¬ ∃ mu : ZMod 3, f ∘ₗ (dSign m b d).toLinearMap =
      mu • (f ∘ₗ (dSign m a x).toLinearMap) := by
  rintro ⟨mu, hmu⟩
  have ha := congrFun (congrArg DFunLike.coe hmu) (dBasis m a)
  have hy' := congrFun (congrArg DFunLike.coe hmu) (dBasis m y)
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at ha hy'
  rw [qtwoDB41_dSign_apply_of_ne f hab had,
    qtwoDB41_dSign_apply_self f hax] at ha
  have hmu_eq : mu = -1 := by
    have h1 : mu * (-f (dBasis m a)) = (-1) * (-f (dBasis m a)) := by
      rw [neg_one_mul, neg_neg]; exact ha.symm
    exact mul_right_cancel₀ (neg_ne_zero.mpr (hf a haB)) h1
  rw [qtwoDB41_dSign_apply_of_ne f hyb hyd,
    qtwoDB41_dSign_apply_of_ne f hya hyx, hmu_eq, neg_one_mul] at hy'
  have hy2 : (2 : ZMod 3) * f (dBasis m y) = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hy'
  exact hf y hyB ((mul_eq_zero.mp hy2).resolve_left (by decide))

end CFSG.StandardType.QTwo

end
