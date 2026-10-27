module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

noncomputable def ggTorEm {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    (Fin N → Multiplicative (ZMod m)) →* L' :=
  MonoidHom.noncommPiCoprod cor (fun i j _ x y => hcomm i j x y)

theorem ggTorEm_mulSingle {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (k : Fin N) (y : Multiplicative (ZMod m)) :
    ggTorEm cor hcomm (Pi.mulSingle k y) = cor k y :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem ggTorEm_mem {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (f : Fin N → Multiplicative (ZMod m)) :
    ggTorEm cor hcomm f ∈ ⨆ k, (cor k).range := by
  change Finset.univ.noncommProd (fun i => cor i (f i)) (fun i _ j _ _ => hcomm i j _ _) ∈ _
  exact Subgroup.noncommProd_mem _ _ fun k _ => Subgroup.mem_iSup_of_mem k ⟨f k, rfl⟩

theorem ggTor_iSup_le_range {m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    ⨆ k, (cor k).range ≤ (ggTorEm cor hcomm).range :=
  iSup_le fun k => by
    rintro _ ⟨ζ, rfl⟩
    exact ⟨Pi.mulSingle k ζ, ggTorEm_mulSingle cor hcomm k ζ⟩

theorem ggTorEm_zeta_mem_closure {p m N : ℕ} {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (e : Fin N → ℕ) :
    ggTorEm cor hcomm (fun k => ggZetaP p m ^ e k) ∈
      Subgroup.closure (Set.range fun k => cor k (ggZetaP p m)) := by
  change Finset.univ.noncommProd (fun i => cor i (ggZetaP p m ^ e i))
    (fun i _ j _ _ => hcomm i j _ _) ∈ _
  refine Subgroup.noncommProd_mem _ _ fun k _ => ?_
  rw [map_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self k)) _

theorem ggTorEm_ker {m N : ℕ} {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (w : GGTorusTorWit m N L' A) (hw : w.Holds C M)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (f : Fin N → Multiplicative (ZMod m)) (hf : MulAut.conj (ggTorEm w.cor hcomm f) = 1) :
    ∀ j, ∑ k, (C j k : ZMod m) * Multiplicative.toAdd (f k) = 0 := by
  obtain ⟨-, -, hcorT, hαmul, -, -, -, hpair, -⟩ := hw
  intro j
  have hmem : ∀ g, MulAut.conj (ggTorEm w.cor hcomm g) ∈ w.T := by
    intro g
    have h1 : ⨆ k, (w.cor k).range ≤ w.T.comap (MulAut.conj : L' →* MulAut L') :=
      iSup_le fun k => by
        rintro _ ⟨ζ, rfl⟩
        exact hcorT k ζ
    exact h1 (ggTorEm_mem w.cor hcomm g)
  let β : (Fin N → Multiplicative (ZMod m)) →* Multiplicative (ZMod m) :=
    (ggTorAlphaHom w.T (w.α j) (hαmul j)).comp
      (((MulAut.conj : L' →* MulAut L').comp (ggTorEm w.cor hcomm)).codRestrict w.T hmem)
  have hβ : ∀ g, β g = w.α j (MulAut.conj (ggTorEm w.cor hcomm g)) := fun g => rfl
  have hβs : ∀ k y, β (Pi.mulSingle k y) = y ^ (C j k) := by
    intro k y
    rw [hβ, ggTorEm_mulSingle, hpair]
  have h1 : β f = 1 := by
    rw [hβ, hf]
    exact ggTor_alpha_one w.T (w.α j) (hαmul j)
  rw [← Finset.univ_prod_mulSingle f, map_prod] at h1
  simp only [hβs] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  simpa [toAdd_prod, toAdd_zpow, zsmul_eq_mul] using h2

theorem ggCartan_det_smul_ker {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (C : Matrix ι ι ℤ)
    (c : ι → ZMod m) (h : ∀ j, ∑ k, (C j k : ZMod m) * c k = 0) (k : ι) :
    (C.det : ZMod m) * c k = 0 := by
  set Cm : Matrix ι ι (ZMod m) := (Int.castRingHom (ZMod m)).mapMatrix C with hCm
  have hdet : Cm.det = (C.det : ZMod m) := by
    simp only [Cm, ← RingHom.map_det]
    rfl
  have hmul : Cm.mulVec c = 0 := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Cm, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast, Pi.zero_apply]
    exact h j
  have h1 : (Matrix.adjugate Cm * Cm).mulVec c = 0 := by
    rw [← Matrix.mulVec_mulVec, hmul, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  have h2 := congrFun h1 k
  simpa [hdet] using h2

theorem ggTor_central_coords {p m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m)
    (w : GGTorusTorWit m N L' A) (hw : w.Holds C M)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (z : L') (hz : z ∈ Subgroup.center L') (hzo : orderOf z = p) :
    ∃ f : Fin N → Multiplicative (ZMod m), ggTorEm w.cor hcomm f = z ∧
      ∀ j, ∑ k, (C j k : ZMod m) * Multiplicative.toAdd (f k) = 0 := by
  have hw' := hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hoddZ, ⟨-, -, hTors⟩, -⟩ := hw'
  have hodd : Odd (orderOf z) := by
    rw [hzo]
    exact hp.odd_of_ne_two hp2
  have hzm : z ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hzo]; exact hpm)
  have hzS : z ∈ ⨆ k, (w.cor k).range := hTors z (hoddZ z hz hodd) hzm
  obtain ⟨f, hf⟩ := ggTor_iSup_le_range w.cor hcomm hzS
  refine ⟨f, hf, ggTorEm_ker w hw hcomm f ?_⟩
  rw [hf]
  ext g
  rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hz g,
    mul_inv_cancel_right]

theorem ggTor_arith_split {p m N a : ℕ} (hp : p.Prime) (hpm : p ∣ m) (hpN : p ∣ N)
    (hp2 : ¬ p ^ 2 ∣ Nat.gcd N m) (hdvd : m ∣ N * a) (hm : 0 < m) :
    ∃ g s : ℕ, Nat.Coprime p g ∧ a * g = (m / p) * s := by
  set d := Nat.gcd N m with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right _ hm
  obtain ⟨g, hg⟩ : p ∣ d := Nat.dvd_gcd hpN hpm
  have hcop : Nat.Coprime p g := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨t, ht⟩
    apply hp2
    refine ⟨t, ?_⟩
    rw [hg, ht, pow_two, mul_assoc]
  obtain ⟨m', hm'⟩ : d ∣ m := Nat.gcd_dvd_right N m
  obtain ⟨N', hN'⟩ : d ∣ N := Nat.gcd_dvd_left N m
  have hcopN : Nat.Coprime N' m' := by
    have := Nat.coprime_div_gcd_div_gcd (m := N) (n := m) hdpos
    rwa [← hd, hN', hm', Nat.mul_div_cancel_left _ hdpos, Nat.mul_div_cancel_left _ hdpos]
      at this
  have h1 : m' ∣ N' * a := by
    have : d * m' ∣ d * (N' * a) := by
      rw [← hm', ← mul_assoc, ← hN']
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hdpos this
  obtain ⟨s, hs⟩ : m' ∣ a := (Nat.Coprime.symm hcopN).dvd_of_dvd_mul_left h1
  refine ⟨g, s, hcop, ?_⟩
  have hmp : m / p = g * m' := by
    rw [hm', hg, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  rw [hmp, hs]
  ring

theorem ggTor_central_mem_closure_A {p m n : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {M : CoxeterMatrix (Fin n)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Odd m) (hpm : p ∣ m) (hn : 1 ≤ n) (hpn : p ∣ n + 1)
    (hp2n : ¬ p ^ 2 ∣ Nat.gcd (n + 1) m)
    (w : GGTorusTorWit m n L' A) (hw : w.Holds (CartanMatrix.A n) M)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (z : L') (hz : z ∈ Subgroup.center L') (hzo : orderOf z = p) :
    z ∈ Subgroup.closure (Set.range fun k => w.cor k (ggZetaP p m)) := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  haveI : NeZero m := ⟨hm0⟩
  obtain ⟨f, hf, hker⟩ := ggTor_central_coords hp hp2 hm hpm w hw hcomm z hz hzo
  set a : Fin n → ZMod m := fun k => Multiplicative.toAdd (f k) with ha
  have hcoord := cartanA_ker_coord a hker
  have hdet := ggCartan_det_smul_ker (CartanMatrix.A n) a hker
  set a0 : ZMod m := a ⟨0, hn⟩ with ha0
  have hak : ∀ k : Fin n, a k = ((k : ℕ) + 1 : ZMod m) * a0 := by
    intro k
    have h1 := hcoord k.1 k.2
    simpa [dif_pos (show 0 < n from hn), ha0] using h1
  have hdet0 : ((n : ZMod m) + 1) * a0 = 0 := by
    have h1 := hdet ⟨0, hn⟩
    rw [CartanMatrix.A_det] at h1
    push_cast at h1
    exact h1
  set g : Multiplicative (ZMod m) := Multiplicative.ofAdd 1 with hg
  set u0 : Fin n → Multiplicative (ZMod m) := fun k => g ^ ((k : ℕ) + 1) with hu0
  have hfu : f = u0 ^ a0.val := by
    funext k
    apply Multiplicative.toAdd.injective
    have h1 : Multiplicative.toAdd (f k) = a k := rfl
    rw [h1, hak k, Pi.pow_apply, toAdd_pow, hu0, toAdd_pow, hg, toAdd_ofAdd, nsmul_eq_mul,
      nsmul_eq_mul, ZMod.natCast_zmod_val]
    push_cast
    ring
  set w0 : L' := ggTorEm w.cor hcomm u0 with hw0
  have hz0 : z = w0 ^ a0.val := by
    rw [← hf, hfu, map_pow]
  have hdvd : m ∣ (n + 1) * a0.val := by
    have h1 : (((n + 1) * a0.val : ℕ) : ZMod m) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hdet0
    exact (ZMod.natCast_eq_zero_iff _ _).mp h1
  obtain ⟨g'', s, hcop, hgs⟩ := ggTor_arith_split hp hpm hpn hp2n hdvd (Nat.pos_of_ne_zero hm0)
  have hzg : z ^ g'' = (w0 ^ (m / p)) ^ s := by
    rw [hz0, ← pow_mul, hgs, pow_mul]
  have hζ : w0 ^ (m / p) = ggTorEm w.cor hcomm (fun k => ggZetaP p m ^ ((k : ℕ) + 1)) := by
    rw [hw0, ← map_pow]
    congr 1
    funext k
    apply Multiplicative.toAdd.injective
    simp only [Pi.pow_apply, hu0, toAdd_pow, hg, toAdd_ofAdd, ggZetaP, nsmul_eq_mul]
    push_cast
    ring
  have hmem : w0 ^ (m / p) ∈ Subgroup.closure (Set.range fun k => w.cor k (ggZetaP p m)) := by
    rw [hζ]
    exact ggTorEm_zeta_mem_closure w.cor hcomm (fun k => (k : ℕ) + 1)
  have hzp : z ^ p = 1 := by
    rw [← hzo]
    exact pow_orderOf_eq_one z
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (g'' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hzv : z = (z ^ g'') ^ v := by
    calc z = z ^ (u * (p : ℤ) + v * (g'' : ℤ)) := by rw [huv, zpow_one]
      _ = (z ^ p) ^ u * (z ^ g'') ^ v := by
        rw [zpow_add, zpow_mul', zpow_mul', zpow_natCast, zpow_natCast]
      _ = (z ^ g'') ^ v := by rw [hzp, one_zpow, one_mul]
  rw [hzv, hzg]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ hmem _) _

theorem ggTor_central_mem_closure_E6 {m : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {M : CoxeterMatrix (Fin 6)} (hm : Odd m) (hpm : 3 ∣ m)
    (w : GGTorusTorWit m 6 L' A) (hw : w.Holds CartanMatrix.E₆ M)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (z : L') (hz : z ∈ Subgroup.center L') (hzo : orderOf z = 3) :
    z ∈ Subgroup.closure (Set.range fun k => w.cor k (ggZetaP 3 m)) := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  obtain ⟨f, hf, hker⟩ := ggTor_central_coords Nat.prime_three (by norm_num) hm hpm w hw hcomm
    z hz hzo
  have hdet := ggCartan_det_smul_ker CartanMatrix.E₆ (fun k => Multiplicative.toAdd (f k)) hker
  have hdet3 : ((CartanMatrix.E₆).det : ZMod m) = 3 := by
    have h1 : (CartanMatrix.E₆).det = 3 := by
      show (CartanMatrix.E 6).det = 3
      rw [CartanMatrix.E_det (by norm_num)]
      norm_num
    rw [h1]
    norm_num
  have hb : ∀ k, ∃ b : ℕ, f k = ggZetaP 3 m ^ b := by
    intro k
    refine ggZetaP_exists_pow Nat.prime_three hm0 hpm (f k) ?_
    have h1 := hdet k
    rw [hdet3] at h1
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
    simpa using h1
  choose b hb using hb
  have hfb : f = fun k => ggZetaP 3 m ^ b k := funext hb
  rw [← hf, hfb]
  exact ggTorEm_zeta_mem_closure w.cor hcomm b

end CFSG.StandardType
