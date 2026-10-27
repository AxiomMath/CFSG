module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem exists_sc_subgroup_of_selfCent {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R)
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hI : ∀ a ∈ A, ∃ φ ∈ LargeEvenInnSet R, ∀ l : L', φ (ψ l) = ψ (a l))
    (hSC : GGTorusSelfCent p A) :
    ∃ E : Subgroup R, IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
      ∀ g ∈ Subgroup.centralizer (E : Set R), g ^ p = 1 → g ∈ E := by
  classical
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hI a a.2
    obtain ⟨t, rfl⟩ := hφI
    exact ⟨t, fun l => by simpa [MulAut.conj_apply] using (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have heq : ((a : MulAut L') : L' →* L') = MonoidHom.id L' := by
      refine TypeA.eq_of_inv_mul_mem_center (S := L') hperf
        ((a : MulAut L') : L' →* L') (MonoidHom.id L') ?_
      intro l
      apply hker
      rw [MonoidHom.mem_ker]
      change ψ (((a : MulAut L') l)⁻¹ * l) = 1
      have h := hχ a l
      rw [ha, one_mul, inv_one, mul_one] at h
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel (ψ l)
    apply Subtype.ext
    ext l
    simpa using congrArg (fun f : L' →* L' => f l) heq
  have hconj : ∀ (a : A) (m : L'), ψ m = χ a → (a : MulAut L') = MulAut.conj m := by
    intro a m hm
    have h : ((a : MulAut L') : L' →* L') = ((MulAut.conj m : MulAut L') : L' →* L') := by
      refine TypeA.eq_of_inv_mul_mem_center (S := L') hperf _ _ ?_
      intro l
      apply hker
      rw [MonoidHom.mem_ker]
      change ψ (((a : MulAut L') l)⁻¹ * (MulAut.conj m) l) = 1
      have ha := hχ a l
      have hb : ψ ((MulAut.conj m) l) = χ a * ψ l * (χ a)⁻¹ := by
        simp only [MulAut.conj_apply, map_mul, map_inv, hm]
      rw [map_mul, map_inv, hb, ha]
      group
    exact MulEquiv.ext (fun l => congrArg (fun f : L' →* L' => f l) h)
  have hfix : ∀ (a : A) (n : L'), ψ ((a : MulAut L') n) = ψ n → (a : MulAut L') n = n := by
    intro a n hn
    let c : L' := n⁻¹ * ((a : MulAut L') n)
    have han : (a : MulAut L') n = n * c := by
      dsimp only [c]
      group
    have hc_ker : c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      dsimp only [c]
      rw [map_mul, map_inv, hn]
      group
    have hc_center : c ∈ Subgroup.center L' := hker hc_ker
    obtain ⟨m, hm⟩ := hψ (χ a)
    have haconj : (a : MulAut L') = MulAut.conj m := hconj a m hm
    have hcm : m * c = c * m := Subgroup.mem_center_iff.mp hc_center m
    have hfix_c : (a : MulAut L') c = c := by
      rw [haconj, MulAut.conj_apply, hcm]
      group
    have hind : ∀ k : ℕ, ((a : MulAut L') ^ k) n = n * c ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix_c, han, pow_succ']
          group
    have hcpow : c ^ p = 1 := by
      have h := hind p
      have hpow : ((a : MulAut L') ^ p) n = n := by
        rw [hA.2 a a.2]
        rfl
      rw [hpow] at h
      exact mul_left_cancel (by rw [mul_one]; exact h.symm)
    have hdvd_p : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcpow
    have hdvd_card : orderOf c ∣ Nat.card (Subgroup.center L') :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center L') hc_center
    have hnot : ¬ p ∣ Nat.card (Subgroup.center L') := hcp L' ψ hψ hker hperf
    have hc_order : orderOf c = 1 := by
      rcases hp.eq_one_or_self_of_dvd (orderOf c) hdvd_p with h1 | hp'
      · exact h1
      · exact absurd (hp' ▸ hdvd_card) hnot
    have hc_one : c = 1 := orderOf_eq_one_iff.mp hc_order
    rw [han, hc_one, mul_one]
  have hroot : ∀ x ∈ Subgroup.center L', ∃ z ∈ Subgroup.center L', z ^ p = x := by
    intro x hx
    have hnot : ¬ p ∣ Nat.card (Subgroup.center L') := hcp L' ψ hψ hker hperf
    have hcop : (Nat.card (Subgroup.center L')).Coprime p :=
      Nat.coprime_comm.mpr (hp.coprime_iff_not_dvd.mpr hnot)
    let z : Subgroup.center L' := (powCoprime hcop).symm ⟨x, hx⟩
    refine ⟨(z : L'), z.2, ?_⟩
    have hz : (powCoprime hcop) z = (⟨x, hx⟩ : Subgroup.center L') :=
      Equiv.apply_symm_apply _ _
    have := congrArg (fun w : Subgroup.center L' => (w : L')) hz
    simpa [powCoprime_apply] using this
  have hEA : IsElemAbelian p χ.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcard : Nat.card χ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  refine ⟨χ.range, hEA, hcard, ?_⟩
  intro g hg hgp
  obtain ⟨n, hn⟩ := hψ g
  have hfix_n : ∀ a : A, (a : MulAut L') n = n := by
    intro a
    apply hfix a n
    have hcomm : χ a * g = g * χ a := Subgroup.mem_centralizer_iff.mp hg (χ a) ⟨a, rfl⟩
    rw [hχ a n, hn, hcomm]
    group
  have hn_ker : n ^ p ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hn, hgp]
  have hn_center : n ^ p ∈ Subgroup.center L' := hker hn_ker
  obtain ⟨z, hz_center, hz_pow⟩ := hroot (n ^ p)⁻¹ (Subgroup.inv_mem (Subgroup.center L') hn_center)
  have hψz : ψ z = 1 := by
    have hcent : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp hz_center l
    rw [hZ, Subgroup.mem_bot] at hcent
    exact hcent
  have hn'_pow : (n * z) ^ p = 1 := by
    have hcomm : Commute n z := Subgroup.mem_center_iff.mp hz_center n
    rw [hcomm.mul_pow p, hz_pow]
    group
  have hψn' : ψ (n * z) = g := by
    rw [map_mul, hn, hψz, mul_one]
  have hfix_n' : ∀ a : A, (a : MulAut L') (n * z) = n * z := by
    intro a
    have haz : (a : MulAut L') z = z := by
      obtain ⟨m, hm⟩ := hψ (χ a)
      have hcm : m * z = z * m := Subgroup.mem_center_iff.mp hz_center m
      rw [hconj a m hm, MulAut.conj_apply, hcm]
      group
    rw [map_mul, hfix_n a, haz]
  let a₀ : A := ⟨MulAut.conj (n * z), hSC (n * z) (fun a ha => hfix_n' ⟨a, ha⟩) hn'_pow⟩
  have hg_eq : g = χ a₀ := by
    have hconjψ : ∀ (m w : L'), ψ ((MulAut.conj m) w) = ψ m * ψ w * (ψ m)⁻¹ := by
      intro m w
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hχa : ∀ l, χ a₀ * ψ l * (χ a₀)⁻¹ = g * ψ l * g⁻¹ := by
      intro l
      rw [← hχ a₀ l]
      have ha0 : (a₀ : MulAut L') = MulAut.conj (n * z) := rfl
      rw [ha0, hconjψ (n * z) l, hψn']
    have hcentral : (χ a₀)⁻¹ * g ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      have hcl : (χ a₀)⁻¹ * g * ψ l = ψ l * ((χ a₀)⁻¹ * g) := by
        calc (χ a₀)⁻¹ * g * ψ l
            = (χ a₀)⁻¹ * (g * ψ l * g⁻¹) * g := by group
          _ = (χ a₀)⁻¹ * (χ a₀ * ψ l * (χ a₀)⁻¹) * g := by rw [← hχa l]
          _ = ψ l * ((χ a₀)⁻¹ * g) := by group
      exact hcl.symm
    rw [hZ, Subgroup.mem_bot] at hcentral
    exact (inv_mul_eq_one.mp hcentral).symm
  exact ⟨a₀, hg_eq.symm⟩

end CFSG.StandardType
