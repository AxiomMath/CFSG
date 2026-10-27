module

public import CFSG.LocalAnalysis.StandardType.GGK1LiftComp
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGTCJDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open scoped commutatorElement

private def ggK1Cs_Abar {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (A : Subgroup (MulAut L')) : Subgroup (MulAut R) where
  carrier := {g : MulAut R | ∃ a ∈ A, ∀ l : L', g (ψ l) = ψ (a l)}
  mul_mem' := by
    rintro g g' ⟨a, ha, hga⟩ ⟨a', ha', hga'⟩
    refine ⟨a * a', A.mul_mem ha ha', ?_⟩
    intro l
    show g (g' (ψ l)) = ψ ((a * a') l)
    rw [hga' l, hga (a' l), MulAut.mul_apply]
  one_mem' := ⟨1, A.one_mem, fun l => by simp⟩
  inv_mem' := by
    rintro g ⟨a, ha, hga⟩
    refine ⟨a⁻¹, A.inv_mem ha, ?_⟩
    intro l
    apply g.injective
    rw [MulAut.apply_inv_self, hga (a⁻¹ l)]
    simp

private theorem ggK1Cs_phi_mem_Abar {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (A : Subgroup (MulAut L')) (e : MulAut L') (φ : MulAut R)
    (heA : e ∈ A) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) :
    φ ∈ ggK1Cs_Abar ψ A :=
  ⟨e, heA, hφ⟩

private theorem ggK1Cs_Abar_isElemAbelian {p : ℕ} {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hψ : Function.Surjective ψ) {A : Subgroup (MulAut L')}
    (hAab : IsElemAbelian p A) : IsElemAbelian p (ggK1Cs_Abar ψ A) := by
  constructor
  · rw [isMulCommutative_iff]
    intro g g'
    obtain ⟨a, ha, hga⟩ := g.2
    obtain ⟨a', ha', hga'⟩ := g'.2
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    show (g : MulAut R) ((g' : MulAut R) (ψ l)) =
      (g' : MulAut R) ((g : MulAut R) (ψ l))
    rw [hga' l, hga (a' l), hga l, hga' (a l)]
    have hcommAA : a * a' = a' * a :=
      congrArg Subtype.val (isMulCommutative_iff.mp hAab.1 (⟨a, ha⟩ : ↥A) ⟨a', ha'⟩)
    simpa only [MulAut.mul_apply] using congrArg (fun f : MulAut L' => ψ (f l)) hcommAA
  · intro g hg
    obtain ⟨a, ha, hga⟩ := hg
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    show ((g : MulAut R) ^ p) (ψ l) = (1 : MulAut R) (ψ l)
    rw [MulAut.one_apply]
    have hpow : ∀ n : ℕ, ∀ l' : L',
        ((g : MulAut R) ^ n) (ψ l') = ψ ((a ^ n) l') := by
      intro n
      induction n with
      | zero => intro l'; simp
      | succ n ih =>
          intro l'
          rw [pow_succ, MulAut.mul_apply, hga l', ih (a l')]
          rw [pow_succ, MulAut.mul_apply]
    rw [hpow p l, hAab.2 a ha, MulAut.one_apply]

private theorem ggK1Cs_Abar_subset_I {L' R : Type} [Group L'] [Group R]
    (I : Set (MulAut R)) (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (A : Subgroup (MulAut L'))
    (hAind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∀ g ∈ ggK1Cs_Abar ψ A, g ∈ I := by
  intro g hg
  obtain ⟨a, ha, hga⟩ := hg
  obtain ⟨φ, hφI, hφind⟩ := hAind a ha
  have hgφ : g = φ := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [hga l, hφind l]
  rwa [hgφ]

private theorem ggK1Cs_ker_pow_eq_one {p : ℕ} {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hcop : (Nat.card ψ.ker).Coprime p)
    {x : L'} (hx : x ∈ ψ.ker) (hp : x ^ p = 1) : x = 1 := by
  have h1 : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hp
  have h2 : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard ψ.ker hx
  have h3 : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h2 h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

private theorem ggK1Cs_ker_coprime {p : ℕ} {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L')
    (hkerp : (Nat.card (Subgroup.center L')).Coprime p) :
    (Nat.card ψ.ker).Coprime p :=
  hkerp.coprime_dvd_left (Subgroup.card_dvd_of_le hker)

private theorem ggK1Cs_lift_pow {p : ℕ} {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hkerp : (Nat.card (Subgroup.center L')).Coprime p) {tbar : R} (htbarp : tbar ^ p = 1) :
    ∃ t : L', ψ t = tbar ∧ t ^ p = 1 := by
  have hcop : (Nat.card ψ.ker).Coprime p := ggK1Cs_ker_coprime ψ hker hkerp
  obtain ⟨t₁, ht₁⟩ := hψ tbar
  have hz : t₁ ^ p ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, ht₁, htbarp]
  have hinv : (t₁ ^ p)⁻¹ ∈ ψ.ker := ψ.ker.inv_mem hz
  obtain ⟨m, hm⟩ := (hcop.pow_left_bijective (G := ψ.ker)).2 ⟨(t₁ ^ p)⁻¹, hinv⟩
  have hmp : (m : L') ^ p = (t₁ ^ p)⁻¹ := by
    simpa using congrArg Subtype.val hm
  refine ⟨t₁ * m, ?_, ?_⟩
  · rw [map_mul, ht₁, MonoidHom.mem_ker.mp m.2, mul_one]
  · rw [Commute.mul_pow ((Subgroup.mem_center_iff.mp (hker m.2)) t₁) p, hmp]
    group

private theorem ggK1Cs_fixed {p : ℕ} {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L') (hcop : (Nat.card ψ.ker).Coprime p)
    (I : Set (MulAut R)) (A : Subgroup (MulAut L'))
    (hAind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∀ {tbar : R} {t : L'}, ψ t = tbar → t ^ p = 1 →
      (∀ g ∈ ggK1Cs_Abar ψ A, g tbar = tbar) → ∀ a ∈ A, a t = t := by
  intro tbar t htpsi htp hfixA a ha
  obtain ⟨φ', hφ'I, hφ'ind⟩ := hAind a ha
  have hφ'mem : φ' ∈ ggK1Cs_Abar ψ A := ⟨a, ha, hφ'ind⟩
  have hfix : φ' tbar = tbar := hfixA φ' hφ'mem
  have hψat : ψ (a t) = ψ t := by
    calc ψ (a t) = φ' (ψ t) := (hφ'ind t).symm
      _ = φ' tbar := by rw [htpsi]
      _ = tbar := hfix
      _ = ψ t := htpsi.symm
  have hdN : a t * t⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψat, mul_inv_cancel]
  have hdcent : a t * t⁻¹ ∈ Subgroup.center L' := hker hdN
  have hcomm : Commute (a t * t⁻¹) t :=
    (Subgroup.mem_center_iff.mp hdcent t).symm
  have hatpow : (a t) ^ p = 1 := by rw [← map_pow, htp, map_one]
  have heq : a t = (a t * t⁻¹) * t := by group
  have hdp : (a t * t⁻¹) ^ p = 1 := by
    have h := hatpow
    rw [heq, Commute.mul_pow hcomm p, htp, mul_one] at h
    exact h
  exact mul_inv_eq_one.mp (ggK1Cs_ker_pow_eq_one ψ hcop hdN hdp)

private theorem ggK1Cs_zpow_apply {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) :
    ∀ (k : ℤ) (l : L'), (φ ^ k) (ψ l) = ψ ((e ^ k) l) := by
  have hpow : ∀ n : ℕ, ∀ l : L', (φ ^ n) (ψ l) = ψ ((e ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
        intro l
        calc (φ ^ (n + 1)) (ψ l) = (φ ^ n) (φ (ψ l)) := by
              rw [pow_succ, MulAut.mul_apply]
          _ = (φ ^ n) (ψ (e l)) := by rw [hφ l]
          _ = ψ ((e ^ n) (e l)) := ih (e l)
          _ = ψ ((e ^ (n + 1)) l) := by rw [pow_succ, MulAut.mul_apply]
  intro k l
  cases k with
  | ofNat n => simpa using hpow n l
  | negSucc n =>
      rw [zpow_negSucc, zpow_negSucc]
      apply (φ ^ (n + 1)).injective
      rw [MulAut.apply_inv_self, hpow (n + 1) ((e ^ (n + 1))⁻¹ l), MulAut.apply_inv_self]

private theorem ggK1Cs_central {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l))
    {t : L'} {tbar : R} (htpsi : ψ t = tbar)
    (htbarcent : ∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub φ) →
      ∀ j ∈ J, tbar * j = j * tbar) :
    ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
      ∀ j ∈ J, t * j = j * t := by
  intro J hJ j hj
  obtain ⟨hJle, hJsub, hJperf, hJsimple⟩ := hJ
  obtain ⟨hJmap, -⟩ := TCJ.ggTCJ_descent ψ hψ hker e φ hφ J ⟨hJle, hJsub, hJperf, hJsimple⟩
  have hmem : ∀ y ∈ J, ⁅t, y⁆ ∈ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, map_commutatorElement, htpsi]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (htbarcent (J.map ψ) hJmap (ψ y) (Subgroup.mem_map_of_mem ψ hy))
  let δ : ↥J →* ↥(Subgroup.center L') :=
    { toFun := fun x => ⟨⁅t, (x : L')⁆, hker (hmem (x : L') x.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change ⁅t, (x : L') * (y : L')⁆ = ⁅t, (x : L')⁆ * ⁅t, (y : L')⁆
        have hcy : ⁅t, (y : L')⁆ ∈ Subgroup.center L' := hker (hmem (y : L') y.2)
        have hxy : (x : L') * ⁅t, (y : L')⁆ * (x : L')⁻¹ = ⁅t, (y : L')⁆ := by
          rw [Subgroup.mem_center_iff.mp hcy (x : L')]; group
        calc ⁅t, (x : L') * (y : L')⁆
            = ⁅t, (x : L')⁆ * (x : L') * ⁅t, (y : L')⁆ * (x : L')⁻¹ :=
                commutatorElement_mul_right_eq_mul_conj t (x : L') (y : L')
          _ = ⁅t, (x : L')⁆ * ((x : L') * ⁅t, (y : L')⁆ * (x : L')⁻¹) := by group
          _ = ⁅t, (x : L')⁆ * ⁅t, (y : L')⁆ := by rw [hxy] }
  have hδker : commutator ↥J ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (δ u).2 (δ v : L')).symm
  have htop : (⟨j, hj⟩ : ↥J) ∈ commutator ↥J := by rw [hJperf]; trivial
  have hδ1 : δ ⟨j, hj⟩ = 1 := by
    have := hδker htop
    simpa [MonoidHom.mem_ker] using this
  have h1 : ⁅t, j⁆ = 1 := by
    have := congrArg (fun s : ↥(Subgroup.center L') => (s : L')) hδ1
    simpa [δ] using this
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem ggK1Cs_conj_zpowers {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (e : MulAut L') (φ : MulAut R)
    (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) {t : L'} {tbar : R} (htpsi : ψ t = tbar) :
    MulAut.conj t ∈ Subgroup.zpowers e → MulAut.conj tbar ∈ Subgroup.zpowers φ := by
  intro h
  rw [Subgroup.mem_zpowers_iff] at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [ggK1Cs_zpow_apply ψ e φ hφ k l, hk, MulAut.conj_apply, map_mul, map_mul, map_inv, htpsi,
    MulAut.conj_apply]

theorem ggK1_cover_sigma {p : ℕ} {D : GGKacDatum} {R L' : Type} [Group R] [Group L'] [Finite L']
    (I : Set (MulAut R)) (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hkerp : (Nat.card (Subgroup.center L')).Coprime p)
    (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l))
    (hcore : GGKacSigmaClause p I D R (MonoidHom.id R) φ) :
    GGKacSigmaClause p I D L' ψ e := by
  intro o ho hqs A heA hAab hAind
  have hcop : (Nat.card ψ.ker).Coprime p := ggK1Cs_ker_coprime ψ hker hkerp
  have hφA : φ ∈ ggK1Cs_Abar ψ A := ggK1Cs_phi_mem_Abar ψ A e φ heA hφ
  have hAab' : IsElemAbelian p (ggK1Cs_Abar ψ A) := ggK1Cs_Abar_isElemAbelian ψ hψ hAab
  have hI : ∀ g ∈ ggK1Cs_Abar ψ A, g ∈ I := ggK1Cs_Abar_subset_I I ψ hψ A hAind
  obtain ⟨tbar, htbarp, htbarfix, htbarcent, htbarconj⟩ :=
    hcore o ho hqs (ggK1Cs_Abar ψ A) hφA hAab'
      (fun g hg => ⟨g, hI g hg, fun l => rfl⟩)
  obtain ⟨t, htpsi, htp⟩ := ggK1Cs_lift_pow ψ hψ hker hkerp htbarp
  refine ⟨t, htp, ?_, ?_, ?_⟩
  · exact ggK1Cs_fixed ψ hker hcop I A hAind htpsi htp htbarfix
  · exact ggK1Cs_central ψ hψ hker e φ hφ htpsi htbarcent
  · intro hconj
    exact htbarconj (ggK1Cs_conj_zpowers ψ hψ e φ hφ htpsi hconj)

end CFSG.StandardType

end