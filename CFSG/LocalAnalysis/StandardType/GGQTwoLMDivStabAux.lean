module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCCard
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCAut
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCDirect
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCNeg
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
open CFSG.StandardType.SpCoord
open scoped BigOperators

theorem qTwoLMDivStab_crd_prod {d p : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → ↥(sumZero d p)) (k : Fin d) :
    crd (Finset.prod s g) k = Finset.sum s (fun i => crd (g i) k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [crd_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, crd_mul, Finset.sum_insert ha, ih]

theorem qTwoLMDivStab_eq_prod_rootV {d p : ℕ} [NeZero p] (i0 : Fin d)
    (f : ↥(sumZero d p)) :
    f = Finset.prod (Finset.univ.erase i0)
      (fun i => (rootV i i0 : ↥(sumZero d p)) ^ (crd f i).val) := by
  classical
  refine ext_crd fun k => ?_
  have hterm : ∀ i ∈ Finset.univ.erase i0,
      crd ((rootV i i0 : ↥(sumZero d p)) ^ (crd f i).val) k =
        (crd f i).val * ((if k = i then 1 else 0) - (if k = i0 then 1 else 0)) := by
    intro i _
    rw [crd_pow, crd_rootV]
  rw [qTwoLMDivStab_crd_prod, Finset.sum_congr rfl hterm]
  have hsum : Finset.sum (Finset.univ.erase i0) (fun i => crd f i) = -crd f i0 := by
    have h := sum_crd f
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i0), add_eq_zero_iff_eq_neg] at h
    exact h
  have hval : ∀ i, ((crd f i).val : ZMod p) = crd f i := fun i => ZMod.natCast_zmod_val _
  by_cases hk : k = i0
  · subst hk
    have hterm' : ∀ x ∈ Finset.univ.erase k,
        (crd f x).val * ((if k = x then 1 else 0) - (if k = k then 1 else 0)) =
          -crd f x := by
      intro x hx
      have hx0 : x ≠ k := (Finset.mem_erase.mp hx).1
      rw [if_neg (Ne.symm hx0), if_pos rfl, hval x]
      ring
    rw [Finset.sum_congr rfl hterm', Finset.sum_neg_distrib, hsum]
    ring
  · have hk' : k ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
    rw [Finset.sum_eq_single k]
    · rw [hval k, if_pos rfl, if_neg hk]
      ring
    · intro b hb hbk
      rw [hval b, if_neg (Ne.symm hbk), if_neg hk]
      ring
    · intro hknot
      exact absurd hk' hknot

theorem qTwoLMDivStab_pow_of_commute_permAutV {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 2 ≤ d) (F : ↥(sumZero d p) →* ↥(sumZero d p))
    (hF : ∀ (σ : Equiv.Perm (Fin d)) (f : ↥(sumZero d p)),
      F (permAutV σ f) = permAutV σ (F f)) :
    ∃ c : ℕ, ∀ f, F f = f ^ c := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i₀, i₁, h01⟩ : ∃ i₀ i₁ : Fin d, i₀ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  set v := F (rootV i₀ i₁) with hv
  have hsw : permAutV (Equiv.swap i₀ i₁) v = v⁻¹ := by
    rw [hv, ← hF, permAutV_rootV, Equiv.swap_apply_left, Equiv.swap_apply_right, ← map_inv]
    congr 1
    exact ext_crd fun k => by rw [crd_inv, crd_rootV, crd_rootV, neg_sub]
  have hv0 : ∀ k, k ≠ i₀ → k ≠ i₁ → crd v k = 0 := by
    intro k hk0 hk1
    have h1 := congrArg (fun g => crd g k) hsw
    simp only [crd_permAutV, crd_inv, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hk0 hk1] at h1
    exact coord_eq_zero_of_eq_neg hp hp2 h1
  have hv1 : crd v i₁ = -crd v i₀ := by
    have h1 := congrArg (fun g => crd g i₀) hsw
    simp only [crd_permAutV, crd_inv, Equiv.swap_inv, Equiv.swap_apply_left] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (c : ZMod p) = crd v i₀ := ⟨(crd v i₀).val, ZMod.natCast_zmod_val _⟩
  have hvc : v = rootV i₀ i₁ ^ c := by
    refine ext_crd fun k => ?_
    rw [crd_pow, hc]
    by_cases hk0 : k = i₀
    · rw [hk0, crd_rootV_left h01, mul_one]
    · by_cases hk1 : k = i₁
      · rw [hk1, crd_rootV_right h01, hv1, mul_neg_one]
      · rw [hv0 k hk0 hk1, crd_rootV_other hk0 hk1, mul_zero]
  have hroot : ∀ i j : Fin d, i ≠ j → F (rootV i j) = rootV i j ^ c := by
    intro i j hij
    obtain ⟨σ, hσi, hσj⟩ := exists_perm_apply_apply h01 hij
    rw [← hσi, ← hσj, ← permAutV_rootV, hF, ← hv, hvc, map_pow]
  refine ⟨c, fun f => ?_⟩
  rw [qTwoLMDivStab_eq_prod_rootV i₀ f, map_prod]
  have hfac : ∀ i ∈ Finset.univ.erase i₀,
      F ((rootV i i₀ : ↥(sumZero d p)) ^ (crd f i).val) =
        ((rootV i i₀ : ↥(sumZero d p)) ^ c) ^ (crd f i).val := by
    intro i hi
    have hi0 : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    rw [map_pow, hroot i i₀ hi0]
  rw [Finset.prod_congr rfl hfac]
  calc Finset.prod (Finset.univ.erase i₀)
        (fun i => ((rootV i i₀ : ↥(sumZero d p)) ^ c) ^ (crd f i).val)
      = Finset.prod (Finset.univ.erase i₀)
          (fun i => ((rootV i i₀ : ↥(sumZero d p)) ^ (crd f i).val) ^ c) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (Finset.prod (Finset.univ.erase i₀)
          (fun i => (rootV i i₀ : ↥(sumZero d p)) ^ (crd f i).val)) ^ c := by
          rw [Finset.prod_pow]

theorem qTwoLMDivStab_aut_form {m : ℕ} (hm4 : 4 ≤ m) {VT : Type} [Group VT]
    {ρ : Equiv.Perm (Fin m) →* MulAut VT} (hVT : IsAugModel m VT ρ) {ψ : MulAut VT}
    (hψ : ∀ σ : Equiv.Perm (Fin m), ∃ σ' : Equiv.Perm (Fin m), ψ * ρ σ * ψ⁻¹ = ρ σ') :
    ∃ π : Equiv.Perm (Fin m), (∀ v, ψ v = ρ π v) ∨ ∀ v, ψ v = (ρ π v)⁻¹ := by
  obtain ⟨e, he⟩ := hVT.ex
  have hm2 : 2 ≤ m := by omega
  let φ : MulAut ↥(sumZero m 3) := MulAut.congr (e.symm) ψ
  have hcongr : ∀ σ : Equiv.Perm (Fin m), MulAut.congr (e.symm) (ρ σ) = permAutV σ := by
    intro σ
    refine MulEquiv.ext fun f => ?_
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_symm, ← he σ f, MulEquiv.symm_apply_apply]
  have hφ : ∀ σ : Equiv.Perm (Fin m), ∃ τ, φ * permAutV σ * φ⁻¹ = permAutV τ := by
    intro σ
    obtain ⟨σ', hσ'⟩ := hψ σ
    refine ⟨σ', ?_⟩
    have h1 := congrArg (fun g : MulAut VT => MulAut.congr (e.symm) g) hσ'
    rw [map_mul, map_mul, map_inv, hcongr σ, hcongr σ'] at h1
    exact h1
  obtain ⟨π, hπ⟩ :=
    exists_eq_conj_of_normalizes (d := m) (p := 3) Nat.prime_three (by norm_num) hm4 hφ
  let φ' : MulAut ↥(sumZero m 3) := (permAutV π)⁻¹ * φ
  have hcomm : ∀ σ : Equiv.Perm (Fin m), φ' * permAutV σ * φ'⁻¹ = permAutV σ := by
    intro σ
    have h1 : (permAutV π)⁻¹ * (φ * permAutV σ * φ⁻¹) * permAutV π = permAutV σ := by
      rw [hπ σ, permAutV_mul, permAutV_mul]
      rw [← permAutVHom_apply π⁻¹, map_inv, permAutVHom_apply]
      group
    calc φ' * permAutV σ * φ'⁻¹
        = (permAutV π)⁻¹ * (φ * permAutV σ * φ⁻¹) * permAutV π := by
            dsimp only [φ']
            rw [mul_inv_rev, inv_inv]
            group
      _ = permAutV σ := h1
  have hcomm2 : ∀ σ : Equiv.Perm (Fin m), φ' * permAutV σ = permAutV σ * φ' := by
    intro σ
    exact mul_inv_eq_iff_eq_mul.mp (hcomm σ)
  have hF : ∀ (σ : Equiv.Perm (Fin m)) (f : ↥(sumZero m 3)),
      φ' (permAutV σ f) = permAutV σ (φ' f) := by
    intro σ f
    have h1 := congrArg (fun g : MulAut ↥(sumZero m 3) => g f) (hcomm2 σ)
    simpa only [MulAut.mul_apply] using h1
  obtain ⟨c, hc⟩ := qTwoLMDivStab_pow_of_commute_permAutV (d := m) (p := 3)
    Nat.prime_three (by norm_num) hm2 φ'.toMonoidHom hF
  have hc' : ∀ f : ↥(sumZero m 3), φ' f = f ^ c := fun f => hc f
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    exact Nat.zero_ne_one (by simpa [i0, i1] using congrArg Fin.val h)
  have hne_one : (rootV i0 i1 : ↥(sumZero m 3)) ≠ 1 := by
    intro h
    have h2 := congrArg (fun f => crd f i0) h
    rw [crd_rootV_left hi01, crd_one] at h2
    exact one_ne_zero h2
  have hc3 : c % 3 = 1 ∨ c % 3 = 2 := by
    have hlt : c % 3 < 3 := Nat.mod_lt c (by norm_num)
    interval_cases hc0 : c % 3
    · exfalso
      have h1 : φ' (rootV i0 i1 : ↥(sumZero m 3)) = 1 := by
        rw [hc', pow_eq_pow_mod c (pow_p_eq_one (rootV i0 i1)), hc0, pow_zero]
      exact hne_one (φ'.injective (by rw [h1, map_one]))
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hφψ : ∀ f : ↥(sumZero m 3), ψ (e f) = e (φ f) := by
    intro f
    have h1 : φ f = e.symm (ψ (e f)) := by
      dsimp only [φ]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm]
    rw [h1, MulEquiv.apply_symm_apply]
  have hv : ∀ v : VT, ψ v = e (φ (e.symm v)) := by
    intro v
    have h1 := hφψ (e.symm v)
    rwa [MulEquiv.apply_symm_apply] at h1
  have hφ_eq : φ = permAutV π * φ' := by
    dsimp only [φ']
    group
  refine ⟨π, ?_⟩
  rcases hc3 with hmod | hmod
  · left
    intro v
    have hfix : φ' (e.symm v) = e.symm v := by
      rw [hc', pow_eq_pow_mod c (pow_p_eq_one (e.symm v)), hmod, pow_one]
    calc ψ v = e (φ (e.symm v)) := hv v
      _ = e (permAutV π (e.symm v)) := by rw [hφ_eq, MulAut.mul_apply, hfix]
      _ = ρ π v := by rw [he π (e.symm v), MulEquiv.apply_symm_apply]
  · right
    intro v
    have hfix : φ' (e.symm v) = (e.symm v)⁻¹ := by
      rw [hc', pow_eq_pow_mod c (pow_p_eq_one (e.symm v)), hmod]
      exact mul_eq_one_iff_eq_inv.mp (by rw [← pow_succ, pow_p_eq_one])
    calc ψ v = e (φ (e.symm v)) := hv v
      _ = e ((permAutV π (e.symm v))⁻¹) := by
            rw [hφ_eq, MulAut.mul_apply, hfix, map_inv]
      _ = (e (permAutV π (e.symm v)))⁻¹ := by rw [map_inv]
      _ = (ρ π v)⁻¹ := by rw [he π (e.symm v), MulEquiv.apply_symm_apply]

theorem qTwoLMDivStab_stab_form {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x)
    (hG : GGThmIHyp 3 B x L) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hVT : IsAugModel m VT F.permVT) :
    ∀ a : MulAut ↥Bs, a ∈ ggInduced ⊤ Bs → a ⟨x, F.hx⟩ = ⟨x, F.hx⟩ →
      ∃ (π : Equiv.Perm (Fin m)) (ε : Bool), ∀ v : VT,
        ((a ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
          ((F.thetaT (if ε then (F.permVT π v)⁻¹ else F.permVT π v) : ↥(Bs ⊓ L)) : G) := by
  intro a ha hax
  simp only [ggInduced] at ha
  obtain ⟨g, -, hgBs, hga⟩ := ha
  have hm4 : 4 ≤ m := qTwoLMFrameC_four_le hL
  have hgx_eq : g * x * g⁻¹ = x := by
    have h := hga ⟨x, F.hx⟩
    have hxval : ((a ⟨x, F.hx⟩ : ↥Bs) : G) = x := by
      simpa using congrArg Subtype.val hax
    rw [hxval] at h
    simpa using h.symm
  have hgx : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rwa [mul_inv_eq_iff_eq_mul] at hgx_eq
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    qTwoLMFrameC_normalizer_of_centralizer F hG (by omega) hVT g hgx
  obtain ⟨π, hcase⟩ := qTwoLMDivStab_aut_form hm4 hVT
    (qTwoLMFrameC_actVT_normalizes F hgBs hgL)
  rcases hcase with hcase | hcase
  · refine ⟨π, false, fun v => ?_⟩
    have hspec := qTwoLMFrameC_actVT_spec F hgBs hgL v
    rw [hcase v] at hspec
    rw [hga ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩, ← hspec]
    simp
  · refine ⟨π, true, fun v => ?_⟩
    have hspec := qTwoLMFrameC_actVT_spec F hgBs hgL v
    rw [hcase v] at hspec
    rw [hga ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩, ← hspec]
    simp

theorem qTwoLMDivStab_ggConjAut_mul_inv {M : Type} [Group M] {A : Subgroup M} {a b : M}
    (ha : a ∈ Subgroup.normalizer (A : Set M)) (hb : b ∈ Subgroup.normalizer (A : Set M))
    (hab : a * b * a⁻¹ ∈ Subgroup.normalizer (A : Set M)) :
    ggConjAut A ha * ggConjAut A hb * (ggConjAut A ha)⁻¹ = ggConjAut A hab := by
  ext w
  rw [MulAut.mul_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply,
    inv_apply_of_forall (ggConjAut_apply A ha) w, ggConjAut_apply]
  group

theorem qTwoLMDivStab_gamma_conj {G : Type} [Group G] {Bs L : Subgroup G} {x : G} {m : ℕ}
    {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x) {g : G}
    (hgBs : g ∈ Subgroup.normalizer (Bs : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (b : ↥Bs) :
    ggConjAut L hgL * ggGamma L F.hN b * (ggConjAut L hgL)⁻¹ =
      ggGamma L F.hN ⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgBs b).mp b.2⟩ := by
  ext l
  rw [MulAut.mul_apply, MulAut.mul_apply, ggConjAut_apply, ggGamma_coe,
    inv_apply_of_forall (ggConjAut_apply L hgL) l, ggGamma_coe]
  group

theorem qTwoLMDivStab_ggConjAut_eq_of_eq {M : Type} [Group M] {A : Subgroup M} {a b : M}
    (ha : a ∈ Subgroup.normalizer (A : Set M)) (hb : b ∈ Subgroup.normalizer (A : Set M))
    (h : a = b) : ggConjAut A ha = ggConjAut A hb := by
  subst h
  rfl

theorem qTwoLMDivStab_ggConjAut_inv_apply {M : Type} [Group M] {A : Subgroup M} {a : M}
    (ha : a ∈ Subgroup.normalizer (A : Set M)) (w : ↥A) :
    ((ggConjAut A ha)⁻¹ w : ↥A) =
      ⟨a⁻¹ * (w : M) * a, by
        simpa [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) w).mp w.2⟩ := by
  apply Subtype.ext
  exact inv_apply_of_forall (ggConjAut_apply A ha) w

theorem qTwoLMDivStab_ggConjAut_gamma {G : Type} [Group G] {Bs L : Subgroup G} {x : G} {m : ℕ}
    {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x) {n : ↥L}
    (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L F.hN).range : Set (MulAut ↥L)))
    (hnBs : (n : G) ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    ((ggConjAut (ggGamma L F.hN).range hn
        ⟨ggGamma L F.hN b, MonoidHom.mem_range.mpr ⟨b, rfl⟩⟩ :
        ↥(ggGamma L F.hN).range) : MulAut ↥L) =
      ggGamma L F.hN ⟨(n : G) * b * (n : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hnBs b).mp b.2⟩ := by
  have hnL : (n : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer n.2
  have hconj : MulAut.conj n = ggConjAut L hnL := by
    ext l
    rw [MulAut.conj_apply, ggConjAut_apply]
    rfl
  have hnW : ggConjAut L hnL ∈
      Subgroup.normalizer ((ggGamma L F.hN).range : Set (MulAut ↥L)) := by
    rw [← hconj]
    exact hn
  rw [qTwoLMDivStab_ggConjAut_eq_of_eq hn hnW hconj, ggConjAut_apply]
  change ggConjAut L hnL * ggGamma L F.hN b * (ggConjAut L hnL)⁻¹ = _
  exact qTwoLMDivStab_gamma_conj F hnBs hnL b


end CFSG.StandardType.QTwo

end
