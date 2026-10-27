module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

structure CartanGen {R : Type} [Group R] (D : FrameData R) (S : Type) [CommGroup S] where
  d : Fin 6 → S →* R
  tor_eq : D.Tor = ⨆ j, (d j).range
  comm : ∀ j k (s t : S), d j s * d k t = d k t * d j s
  conj : ∀ i j (s : S),
    D.nb i * d j s * (D.nb i)⁻¹ = d j s * d i (s ^ (-(Tag.E6.cartan j i)))

private lemma mult_zmod3_eq_one_of_sq_eq_one (x : Multiplicative (ZMod 3)) (h : x ^ 2 = 1) :
    x = 1 := by
  have h' : (2 : ZMod 3) * Multiplicative.toAdd x = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  rcases mul_eq_zero.mp h' with h2 | hx
  · exact absurd h2 (by decide)
  · apply Multiplicative.toAdd.injective
    rw [hx, toAdd_one]

private lemma conj_injective_of_center_eq_bot {R : Type} [Group R]
    (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R → MulAut R) := by
  intro r r' h
  have hc : r'⁻¹ * r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut R => f x) h
    simp only [MulAut.conj_apply] at hx
    have hxc : x = (r'⁻¹ * r) * x * (r'⁻¹ * r)⁻¹ := by
      have := congrArg (fun y => r'⁻¹ * y * r') hx
      simpa [mul_assoc] using this.symm
    have hxc2 : x * (r'⁻¹ * r) = (r'⁻¹ * r) * x := by
      calc x * (r'⁻¹ * r) = ((r'⁻¹ * r) * x * (r'⁻¹ * r)⁻¹) * (r'⁻¹ * r) := by
            conv_lhs => rw [hxc]
        _ = (r'⁻¹ * r) * x := by group
    exact hxc2
  rw [hZ] at hc
  have h1 : r'⁻¹ * r = 1 := by simpa using hc
  exact (inv_mul_eq_one.mp h1).symm

private lemma mulAut_conj_apply_aut {R : Type} [Group R] (φ : MulAut R) (n : R) :
    MulAut.conj (φ n) = φ * MulAut.conj n * φ⁻¹ := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply]

private lemma mem_tor_d {R : Type} [Group R] {D : FrameData R} {S : Type} [CommGroup S]
    (G : CartanGen D S) (j : Fin 6) (s : S) : G.d j s ∈ D.Tor := by
  rw [G.tor_eq]
  exact Subgroup.mem_iSup_of_mem j ⟨s, rfl⟩

private def e6Row (i : Fin Tag.E6.rank) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ((Tag.E6.cartan i j : ℤ) : ZMod 3)

private theorem tor_hom_eq_one_of_generators {R : Type} [Group R] {D : FrameData R}
    {S : Type} [CommGroup S] (G : CartanGen D S)
    (f : D.Tor →* Multiplicative (ZMod 3))
    (hgen : ∀ (j : Fin 6) (s : S), f ⟨G.d j s, mem_tor_d G j s⟩ = 1) :
    f = 1 := by
  apply MonoidHom.ext
  intro x
  have hx : (x : R) ∈ ⨆ j, (G.d j).range := G.tor_eq ▸ x.2
  have hC : ∃ h : (x : R) ∈ D.Tor, f ⟨(x : R), h⟩ = 1 := by
    refine Subgroup.iSup_induction (S := fun j : Fin 6 => (G.d j).range)
      (C := fun r => ∃ h : r ∈ D.Tor, f ⟨r, h⟩ = 1) hx ?_ ?_ ?_
    · intro j y hy
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hy
      exact ⟨mem_tor_d G j s, hgen j s⟩
    · exact ⟨D.Tor.one_mem, map_one f⟩
    · rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
      refine ⟨D.Tor.mul_mem ha hb, ?_⟩
      rw [show (⟨a * b, D.Tor.mul_mem ha hb⟩ : D.Tor) = ⟨a, ha⟩ * ⟨b, hb⟩ from Subtype.ext rfl,
        map_mul, hfa, hfb, one_mul]
  obtain ⟨h, hf1⟩ := hC
  rwa [show (⟨(x : R), h⟩ : D.Tor) = x from Subtype.ext rfl] at hf1

private theorem tor_func_eq_one {R : Type} [Group R] {D : FrameData R} {S : Type} [CommGroup S]
    (G : CartanGen D S)
    (hnorm : ∀ (i : Fin 6) (t : D.Tor), D.nb i * (t : R) * (D.nb i)⁻¹ ∈ D.Tor)
    (f : D.Tor →* Multiplicative (ZMod 3))
    (hinv : ∀ (i : Fin 6) (v v' : D.Tor), (v' : R) = D.nb i * v * (D.nb i)⁻¹ → f v' = f v) :
    f = 1 := by
  apply tor_hom_eq_one_of_generators G f
  intro j s
  let v : D.Tor := ⟨G.d j s, mem_tor_d G j s⟩
  let w : D.Tor := ⟨G.d j (s ^ (-(Tag.E6.cartan j j))), mem_tor_d G j (s ^ _)⟩
  let v' : D.Tor := ⟨D.nb j * (v : R) * (D.nb j)⁻¹, hnorm j v⟩
  have h1 : f v' = f v := hinv j v v' rfl
  have hvw : v' = v * w := by
    apply Subtype.ext
    change D.nb j * (G.d j s) * (D.nb j)⁻¹ = G.d j s * G.d j (s ^ (-(Tag.E6.cartan j j)))
    exact G.conj j j s
  have hw1 : f w = 1 := by
    have hthis : f v * f w = f v := by
      rw [← map_mul, ← hvw]
      exact h1
    exact mul_left_cancel (by rw [mul_one]; exact hthis)
  have hw2 : w = v ^ (-(Tag.E6.cartan j j)) := by
    apply Subtype.ext
    change G.d j (s ^ (-(Tag.E6.cartan j j))) = (G.d j s) ^ (-(Tag.E6.cartan j j))
    exact MonoidHom.map_zpow (G.d j) s _
  have hpow : (f v) ^ (-(Tag.E6.cartan j j)) = 1 := by
    have hmap : f (v ^ (-(Tag.E6.cartan j j))) = (f v) ^ (-(Tag.E6.cartan j j)) :=
      MonoidHom.map_zpow f v _
    rw [← hmap, ← hw2]
    exact hw1
  have hA : Tag.E6.cartan j j = 2 := by fin_cases j <;> decide
  have h2 : (f v) ^ 2 = 1 := by
    have hpow2 : (f v) ^ (-(2 : ℤ)) = 1 := by
      have h := hpow
      rw [hA] at h
      exact h
    have hneg : ((f v) ^ 2)⁻¹ = 1 := (zpow_neg (f v) 2).symm.trans hpow2
    exact inv_eq_one.mp hneg
  show f v = 1
  exact mult_zmod3_eq_one_of_sq_eq_one (f v) h2

private theorem tor_noAlt {R : Type} [Group R] {D : FrameData R} {S : Type} [CommGroup S]
    [IsCyclic S] (G : CartanGen D S)
    (hnorm : ∀ (i : Fin 6) (t : D.Tor), D.nb i * (t : R) * (D.nb i)⁻¹ ∈ D.Tor)
    (κ : D.Tor → D.Tor → Multiplicative (ZMod 3))
    (hleft : ∀ x y z, κ (x * y) z = κ x z * κ y z)
    (hright : ∀ x y z, κ x (y * z) = κ x y * κ x z)
    (halt : ∀ x, κ x x = 1)
    (hinv : ∀ (i : Fin 6) (x y x' y' : D.Tor),
      (x' : R) = D.nb i * x * (D.nb i)⁻¹ → (y' : R) = D.nb i * y * (D.nb i)⁻¹ →
        κ x' y' = κ x y) :
    ∀ x y, κ x y = 1 := by
  have hone_l : ∀ y : D.Tor, κ 1 y = 1 := by
    intro y
    have h := hleft 1 1 y
    simp only [one_mul] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  have hone_r : ∀ x : D.Tor, κ x 1 = 1 := by
    intro x
    have h := hright x 1 1
    simp only [mul_one] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  let lam : D.Tor → D.Tor →* Multiplicative (ZMod 3) := fun y =>
    { toFun := fun x => κ x y
      map_one' := hone_l y
      map_mul' := fun x x' => hleft x x' y }
  let rho : D.Tor → D.Tor →* Multiplicative (ZMod 3) := fun x =>
    { toFun := fun y => κ x y
      map_one' := hone_r x
      map_mul' := fun y y' => hright x y y' }
  have hz_l : ∀ (x y : D.Tor) (n : ℤ), κ (x ^ n) y = (κ x y) ^ n :=
    fun x y n => MonoidHom.map_zpow (lam y) x n
  have hz_r : ∀ (x y : D.Tor) (n : ℤ), κ x (y ^ n) = (κ x y) ^ n :=
    fun x y n => MonoidHom.map_zpow (rho x) y n
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := S)
  let z : Fin 6 → D.Tor := fun j => ⟨G.d j c, mem_tor_d G j c⟩
  have hm : ∀ j k : Fin 6, (κ (z j) (z k)) ^ 2 = 1 := by
    intro j k
    let x1 : D.Tor := z j
    let y1 : D.Tor := z k
    let x2 : D.Tor := x1 ^ (-(Tag.E6.cartan j j))
    let y2 : D.Tor := x1 ^ (-(Tag.E6.cartan k j))
    let x' : D.Tor := ⟨D.nb j * (x1 : R) * (D.nb j)⁻¹, hnorm j x1⟩
    let y' : D.Tor := ⟨D.nb j * (y1 : R) * (D.nb j)⁻¹, hnorm j y1⟩
    have hx' : x' = x1 * x2 := by
      apply Subtype.ext
      change D.nb j * (G.d j c) * (D.nb j)⁻¹ = G.d j c * (G.d j c) ^ (-(Tag.E6.cartan j j))
      rw [G.conj j j c, MonoidHom.map_zpow]
    have hy' : y' = y1 * y2 := by
      apply Subtype.ext
      change D.nb j * (G.d k c) * (D.nb j)⁻¹ = G.d k c * (G.d j c) ^ (-(Tag.E6.cartan k j))
      rw [G.conj j k c, MonoidHom.map_zpow]
    have hinv_jk : κ x' y' = κ x1 y1 := hinv j x1 y1 x' y' rfl rfl
    have hbimul : ∀ a b c d : D.Tor,
        κ (a * b) (c * d) = κ a c * κ a d * κ b c * κ b d := by
      intro a b c d
      rw [hleft, hright, hright]
      ac_rfl
    have h12 : κ x1 y2 = 1 := by
      have h := hz_r x1 x1 (-(Tag.E6.cartan k j))
      change κ x1 (x1 ^ (-(Tag.E6.cartan k j))) = 1
      rw [h, halt x1]
      exact one_zpow _
    have h21 : κ x2 y1 = (κ x1 y1) ^ (-(Tag.E6.cartan j j)) := by
      have h := hz_l x1 y1 (-(Tag.E6.cartan j j))
      change κ (x1 ^ (-(Tag.E6.cartan j j))) y1 =
        (κ x1 y1) ^ (-(Tag.E6.cartan j j))
      rw [h]
    have h22 : κ x2 y2 = 1 := by
      have h := hz_l x1 y2 (-(Tag.E6.cartan j j))
      change κ (x1 ^ (-(Tag.E6.cartan j j))) (x1 ^ (-(Tag.E6.cartan k j))) = 1
      rw [h, h12]
      exact one_zpow _
    have hexp : κ x' y' = (κ x1 y1) ^ (-1 : ℤ) := by
      rw [hx', hy', hbimul, h12, h21, h22]
      have hA : Tag.E6.cartan j j = 2 := by fin_cases j <;> decide
      rw [hA]
      group
    have heq : κ x1 y1 = (κ x1 y1) ^ (-1 : ℤ) := hinv_jk.symm.trans hexp
    have hsq : κ x1 y1 ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [heq]
      rw [zpow_neg_one]
      exact mul_inv_cancel _
    simpa [x1, y1] using hsq
  have hm1 : ∀ j k : Fin 6, κ (z j) (z k) = 1 :=
    fun j k => mult_zmod3_eq_one_of_sq_eq_one _ (hm j k)
  have hgenκ : ∀ (j k : Fin 6) (s t : S),
      κ ⟨G.d j s, mem_tor_d G j s⟩ ⟨G.d k t, mem_tor_d G k t⟩ = 1 := by
    intro j k s t
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hc s)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hc t)
    have hs : (⟨G.d j s, mem_tor_d G j s⟩ : D.Tor) = z j ^ a := by
      apply Subtype.ext
      change G.d j s = (G.d j c) ^ a
      rw [← ha, MonoidHom.map_zpow]
    have ht : (⟨G.d k t, mem_tor_d G k t⟩ : D.Tor) = z k ^ b := by
      apply Subtype.ext
      change G.d k t = (G.d k c) ^ b
      rw [← hb, MonoidHom.map_zpow]
    rw [hs, ht, hz_l, hz_r, hm1 j k]
    rw [show (1 : Multiplicative (ZMod 3)) ^ b = 1 from one_zpow b]
    exact one_zpow a
  intro x y
  have hgen_lam : ∀ j s, (lam y) ⟨G.d j s, mem_tor_d G j s⟩ = 1 := by
    intro j s
    have hrho : rho ⟨G.d j s, mem_tor_d G j s⟩ = 1 :=
      tor_hom_eq_one_of_generators G (rho ⟨G.d j s, mem_tor_d G j s⟩)
        (fun k t => hgenκ j k s t)
    have hy := congrArg (fun (g : D.Tor →* Multiplicative (ZMod 3)) => g y) hrho
    simpa [rho, lam] using hy
  have hlam : lam y = 1 := tor_hom_eq_one_of_generators G (lam y) hgen_lam
  have hx := congrArg (fun (g : D.Tor →* Multiplicative (ZMod 3)) => g x) hlam
  simpa [lam] using hx

private lemma hypE6_comb (v : Fin Tag.E6.rank → ZMod 3) (hv : NoOffRest.kDotP 3 v = 0) :
    ∃ y : Fin Tag.E6.rank → Fin 3, v = ∑ i, (y i : ℕ) • e6Row i := by
  revert v
  decide +kernel

private lemma hypE6_eq_closure :
    NoOffRest.hypE6 = AddSubgroup.closure (Set.range e6Row) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨y, hy⟩ := hypE6_comb v (NoOffRest.mem_hypE6.mp hv)
    rw [hy]
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure
        (show e6Row i ∈ Set.range e6Row from ⟨i, rfl⟩)) (y i : ℕ)
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact NoOffRest.mem_hypE6.mpr (NoOffRest.kDot_cartan i)

private theorem v0_func_eq_one {R : Type} [Group R] (D : FrameData R)
    (hZ : Subgroup.center R = ⊥) (hF : D.Faithful) (hW : D.WeylOK)
    (f : D.V0 →* Multiplicative (ZMod 3))
    (hinv : ∀ (i : Fin 6) (v v' : D.V0),
      (v' : R) = D.nb i * v * (D.nb i)⁻¹ → f v' = f v) :
    f = 1 := by
  have hnorm : ∀ (i : Fin 6) (t : D.Tor), D.nb i * (t : R) * (D.nb i)⁻¹ ∈ D.Tor :=
    fun i t => hW.2.1 i t t.2
  have had : Function.Injective D.ad := by
    intro x y h
    exact Multiplicative.ofAdd.injective (hF h)
  have hconj : Function.Injective (MulAut.conj : R → MulAut R) :=
    conj_injective_of_center_eq_bot hZ
  let eVec : D.V0 → (Fin Tag.E6.rank → ZMod 3) := fun r => Classical.choose r.2.2
  have heVec_mem : ∀ r : D.V0, eVec r ∈ NoOffRest.hypE6 :=
    fun r => (Classical.choose_spec r.2.2).1
  have heVec : ∀ r : D.V0, MulAut.conj (r : R) = D.ad (eVec r) :=
    fun r => (Classical.choose_spec r.2.2).2
  have heVec_inj : Function.Injective eVec := by
    intro r r' h
    exact Subtype.ext (hconj (by
      calc MulAut.conj (r : R) = D.ad (eVec r) := heVec r
        _ = D.ad (eVec r') := by rw [h]
        _ = MulAut.conj (r' : R) := (heVec r').symm))
  have heVec_one : eVec (1 : D.V0) = 0 := by
    apply had
    rw [D.ad_zero, ← heVec (1 : D.V0)]
    show MulAut.conj (1 : R) = 1
    rw [map_one]
  have heVec_mul : ∀ r r' : D.V0, eVec (r * r') = eVec r + eVec r' := by
    intro r r'
    apply had
    rw [D.ad_add, ← heVec r, ← heVec r', ← map_mul]
    rw [← heVec (r * r')]
    rfl
  have heVec_inv : ∀ r : D.V0, eVec r⁻¹ = - eVec r := by
    intro r
    apply had
    rw [D.ad_neg, ← heVec r⁻¹, ← heVec r]
    show MulAut.conj ((r : R)⁻¹) = (MulAut.conj (r : R))⁻¹
    rw [map_inv]
  let J : AddSubgroup (Fin Tag.E6.rank → ZMod 3) :=
    { carrier := Set.range eVec
      zero_mem' := ⟨1, heVec_one⟩
      add_mem' := by
        rintro a b ⟨r, rfl⟩ ⟨r', rfl⟩
        exact ⟨r * r', heVec_mul r r'⟩
      neg_mem' := by
        rintro a ⟨r, rfl⟩
        exact ⟨r⁻¹, heVec_inv r⟩ }
  have he6Row_mem : ∀ i : Fin Tag.E6.rank, e6Row i ∈ NoOffRest.hypE6 :=
    fun i => NoOffRest.mem_hypE6.mpr (NoOffRest.kDot_cartan i)
  have haJ : ∀ i : Fin Tag.E6.rank, e6Row i ∈ J := by
    intro i
    let x : Fin Tag.E6.rank → ZMod 3 := Pi.single i 1
    let r : D.V0 := ⟨D.nb i * (D.ad x (D.nb i))⁻¹, hW.2.2.2 i x⟩
    have he : eVec r = -(x i) • e6Row i := by
      apply had
      rw [← heVec r]
      change MulAut.conj (D.nb i * (D.ad x (D.nb i))⁻¹) = D.ad (-(x i) • e6Row i)
      calc MulAut.conj (D.nb i * (D.ad x (D.nb i))⁻¹)
          = MulAut.conj (D.nb i) * (MulAut.conj (D.ad x (D.nb i)))⁻¹ := by
            rw [map_mul, map_inv]
        _ = MulAut.conj (D.nb i) * (D.ad x * MulAut.conj (D.nb i) * (D.ad x)⁻¹)⁻¹ := by
            rw [mulAut_conj_apply_aut]
        _ = MulAut.conj (D.nb i) * D.ad x * (MulAut.conj (D.nb i))⁻¹ * (D.ad x)⁻¹ := by
            group
        _ = D.ad (adRefl .E6 3 i x) * (D.ad x)⁻¹ := by rw [hW.2.2.1 i x]
        _ = D.ad (adRefl .E6 3 i x) * D.ad (-x) := by rw [D.ad_neg]
        _ = D.ad (adRefl .E6 3 i x + (-x)) := by rw [← D.ad_add]
        _ = D.ad (-(x i) • e6Row i) := by
            congr 1
            funext j
            simp only [adRefl, e6Row, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply]
            show x j - x i * ((Tag.E6.cartan i j : ℤ) : ZMod 3) + -x j =
              (-(x i)) * ((Tag.E6.cartan i j : ℤ) : ZMod 3)
            rw [show (-(x i)) * ((Tag.E6.cartan i j : ℤ) : ZMod 3) =
              -(x i * ((Tag.E6.cartan i j : ℤ) : ZMod 3)) from
              neg_mul (x i) ((Tag.E6.cartan i j : ℤ) : ZMod 3)]
            abel
    have hxi : x i = 1 := by simp [x, Pi.single_eq_same]
    have he' : eVec r = - e6Row i := by
      rw [he, hxi]
      funext j
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      exact neg_one_mul _
    have hneg : - e6Row i ∈ J := by rw [← he']; exact ⟨r, rfl⟩
    have hmem : e6Row i ∈ J := by
      have h1 : e6Row i = - eVec r := by
        rw [he']
        exact (neg_neg _).symm
      rw [h1]
      exact J.neg_mem ⟨r, rfl⟩
    exact hmem
  have hJle : NoOffRest.hypE6 ≤ J := by
    rw [hypE6_eq_closure]
    exact (AddSubgroup.closure_le J).mpr (by rintro _ ⟨i, rfl⟩; exact haJ i)
  let pre : NoOffRest.hypE6 → D.V0 := fun v =>
    Classical.choose (show ∃ r : D.V0, eVec r = (v : Fin Tag.E6.rank → ZMod 3) from hJle v.2)
  have hpre : ∀ v : NoOffRest.hypE6, eVec (pre v) = (v : Fin Tag.E6.rank → ZMod 3) := fun v =>
    Classical.choose_spec (show ∃ r : D.V0, eVec r = (v : Fin Tag.E6.rank → ZMod 3) from hJle v.2)
  let φ : NoOffRest.hypE6 →+ ZMod 3 :=
    { toFun := fun v => Multiplicative.toAdd (f (pre v))
      map_zero' := by
        have hpre0 : pre 0 = 1 := by
          apply heVec_inj
          rw [hpre, heVec_one]
          rfl
        rw [hpre0, map_one, toAdd_one]
      map_add' := by
        intro v w
        have hpem : pre (v + w) = pre v * pre w := by
          apply heVec_inj
          rw [hpre, heVec_mul, hpre v, hpre w]
          rfl
        rw [hpem, map_mul, toAdd_mul] }
  have adRefl_mem : ∀ (i : Fin Tag.E6.rank) (v : NoOffRest.hypE6),
      adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) ∈ NoOffRest.hypE6 := by
    intro i v
    rw [NoOffRest.mem_hypE6,
      NoOffRest.kDotP_adRefl (NoOffRest.kDot_cartan i) (v : Fin Tag.E6.rank → ZMod 3),
      NoOffRest.mem_hypE6.mp v.2]
  have adRefl_neg : ∀ i : Fin Tag.E6.rank, adRefl .E6 3 i (-(e6Row i)) = e6Row i := by
    intro i
    fin_cases i <;> (funext j; fin_cases j <;> decide)
  have hφ_refl : ∀ (i : Fin Tag.E6.rank) (v : NoOffRest.hypE6),
      φ ⟨adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3), adRefl_mem i v⟩ = φ v := by
    intro i v
    let r : D.V0 := pre v
    have hr : eVec r = (v : Fin Tag.E6.rank → ZMod 3) := hpre v
    let r' : D.V0 := ⟨D.nb i * (r : R) * (D.nb i)⁻¹, by
      refine ⟨hnorm i ⟨(r : R), r.2.1⟩, ?_⟩
      exact ⟨adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3), adRefl_mem i v,
        by rw [map_mul, map_mul, map_inv, heVec r, hr, hW.2.2.1 i (v : Fin Tag.E6.rank → ZMod 3)]⟩⟩
    have heVec_r' : eVec r' = adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) := by
      apply had
      rw [← heVec r']
      change MulAut.conj (D.nb i * (r : R) * (D.nb i)⁻¹) =
        D.ad (adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3))
      rw [map_mul, map_mul, map_inv, heVec r, hr,
        hW.2.2.1 i (v : Fin Tag.E6.rank → ZMod 3)]
    have hpre_refl : pre ⟨adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3), adRefl_mem i v⟩ = r' := by
      apply heVec_inj
      rw [hpre, heVec_r']
    have hf_eq : f r' = f r := hinv i r r' rfl
    show Multiplicative.toAdd (f (pre ⟨adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3),
        adRefl_mem i v⟩)) = Multiplicative.toAdd (f (pre v))
    rw [hpre_refl]
    rw [show pre v = r from rfl]
    rw [hf_eq]
  have hφa : ∀ i : Fin Tag.E6.rank, φ ⟨e6Row i, he6Row_mem i⟩ = 0 := by
    intro i
    have hneg_mem : -(e6Row i) ∈ NoOffRest.hypE6 := NoOffRest.hypE6.neg_mem (he6Row_mem i)
    have hadd := hφ_refl i ⟨-(e6Row i), hneg_mem⟩
    have hdrefl : (⟨adRefl .E6 3 i (-(e6Row i)),
        adRefl_mem i ⟨-(e6Row i), hneg_mem⟩⟩ : NoOffRest.hypE6) = ⟨e6Row i, he6Row_mem i⟩ := by
      apply Subtype.ext
      exact adRefl_neg i
    rw [hdrefl] at hadd
    have hneg : φ ⟨-(e6Row i), hneg_mem⟩ = - φ ⟨e6Row i, he6Row_mem i⟩ := by
      have hx : (⟨-(e6Row i), hneg_mem⟩ : NoOffRest.hypE6) = - ⟨e6Row i, he6Row_mem i⟩ :=
        Subtype.ext rfl
      rw [hx]
      exact map_neg φ _
    rw [hneg] at hadd
    have h2 : (2 : ZMod 3) * φ ⟨e6Row i, he6Row_mem i⟩ = 0 := by
      have hzero : φ ⟨e6Row i, he6Row_mem i⟩ + φ ⟨e6Row i, he6Row_mem i⟩ = 0 := by
        nth_rewrite 2 [hadd]
        exact add_neg_cancel _
      simpa [two_mul] using hzero
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  have hφ_zero : ∀ v : NoOffRest.hypE6, φ v = 0 := by
    intro v
    obtain ⟨y, hy⟩ := hypE6_comb (v : Fin Tag.E6.rank → ZMod 3) (NoOffRest.mem_hypE6.mp v.2)
    have hsum : v = ∑ i, (y i : ℕ) • (⟨e6Row i, he6Row_mem i⟩ : NoOffRest.hypE6) := by
      apply Subtype.ext
      simpa using hy
    calc φ v = φ (∑ i, (y i : ℕ) • (⟨e6Row i, he6Row_mem i⟩ : NoOffRest.hypE6)) := by rw [hsum]
      _ = ∑ i, φ ((y i : ℕ) • (⟨e6Row i, he6Row_mem i⟩ : NoOffRest.hypE6)) := by
            simp only [map_sum]
      _ = ∑ i, (y i : ℕ) • φ ⟨e6Row i, he6Row_mem i⟩ := by
            exact Finset.sum_congr rfl fun i _ => map_nsmul φ _ _
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rw [hφa i, nsmul_zero]
  apply MonoidHom.ext
  intro r
  have hpre_e : pre ⟨eVec r, heVec_mem r⟩ = r := by
    apply heVec_inj
    rw [hpre]
  have hto : Multiplicative.toAdd (f r) = 0 := by
    rw [← hpre_e]
    exact hφ_zero ⟨eVec r, heVec_mem r⟩
  apply Multiplicative.toAdd.injective
  simp [hto]

theorem moduleOK_of_cartanGen {R : Type} [Group R] (D : FrameData R) (hZ : Subgroup.center R = ⊥)
    (hF : D.Faithful) (hW : D.WeylOK) {S : Type} [CommGroup S] [Finite S] [IsCyclic S]
    (G : CartanGen D S) : D.ModuleOK := by
  intro L _ ψ N hN
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    apply tor_func_eq_one G (fun i t => hW.2.1 i t t.2) f
    intro i v v' hv'
    obtain ⟨n, hnN, hnψ⟩ := hN i
    exact hf n hnN v v' (by rw [hnψ]; exact hv')
  · intro κ hleft hright halt hinv
    apply tor_noAlt G (fun i t => hW.2.1 i t t.2) κ hleft hright halt
    intro i x y x' y' hx' hy'
    obtain ⟨n, hnN, hnψ⟩ := hN i
    exact hinv n hnN x y x' y' (by rw [hnψ]; exact hx') (by rw [hnψ]; exact hy')
  · intro f hf
    apply v0_func_eq_one D hZ hF hW f
    intro i v v' hv'
    obtain ⟨n, hnN, hnψ⟩ := hN i
    exact hf n hnN v v' (by rw [hnψ]; exact hv')

end CFSG.StandardType.E6ThreeModel
