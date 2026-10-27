module

public import CFSG.LocalAnalysis.StandardType.GGK1Defs
public import CFSG.LocalAnalysis.StandardType.GGK1CoverBij
public import CFSG.LocalAnalysis.StandardType.GGK1CoverSigma
public import CFSG.LocalAnalysis.StandardType.GGK1LiftComp
public import CFSG.LocalAnalysis.StandardType.GGTCJCoverGen
public import CFSG.GroupTheory.ElemAbelianClosure
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

open scoped commutatorElement

theorem ggK1_cover_comp {p nf : ℕ} {D : GGKacDatum} {R L' : Type} [Group R] [Group L'] [Finite L']
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (e : MulAut L') (he : e ^ p = 1) (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l))
    (hcore : GGK1Comps nf D R φ) :
    (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
      ∃ o ∈ D.orbits, o.qs = true ∧ nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
        GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
    (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
      CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧ GGHasLabel o.lab (J ⧸ Subgroup.center J)) := by
  refine ⟨?_, ?_⟩
  · refine TCJ.ggTCJ_cover_prop (p := p) ψ hψ hker e he φ hφ
      (fun X _ => ∃ o ∈ D.orbits, o.qs = true ∧ nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
        GGHasLabel o.lab X) ?_ ?_
    · intro X Y _ _ f ⟨o, ho, hq, hn, hΛ, hl⟩
      exact ⟨o, ho, hq, hn, hΛ, ggHasLabel_of_mulEquiv f hl⟩
    · intro _ K hK
      obtain ⟨o, ho, hq, hn, hΛ, hl⟩ := hcore.1 K hK
      exact ⟨o, ho, hq, hn, hΛ, hl⟩
  · intro o ho hq
    obtain ⟨K, hK, hl⟩ := hcore.2 o ho hq
    obtain ⟨J, hJ, ⟨f⟩⟩ := ggK1_lift_component ψ hψ hker e φ hφ hK
    exact ⟨J, hJ, ggHasLabel_of_mulEquiv f.symm hl⟩

theorem ggK1_cover_dvd {p : ℕ} {R L' : Type} [Group R] [Group L'] [Finite L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (e : MulAut L')
    (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) (hcore : GGK1Dvd p R φ) :
    ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → p ∣ Nat.card J := by
  intro J hJ
  obtain ⟨hcomp, -⟩ := TCJ.ggTCJ_descent ψ hψ hker e φ hφ J hJ
  exact (hcore _ hcomp).trans (Subgroup.card_dvd_of_surjective (ψ.subgroupMap_surjective J))

private theorem ggK1Cov_ker_coprime {p : ℕ} {R L' : Type} [Group R] [Group L'] [Finite L']
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L')
    (hkerp : (Nat.card (Subgroup.center L')).Coprime p) :
    (Nat.card ψ.ker).Coprime p :=
  hkerp.coprime_dvd_left (Subgroup.card_dvd_of_le hker)

private theorem ggK1Cov_ker_pow_eq_one {p : ℕ} {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hcop : (Nat.card ψ.ker).Coprime p)
    {x : L'} (hx : x ∈ ψ.ker) (hp : x ^ p = 1) : x = 1 := by
  have h1 : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hp
  have h2 : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard ψ.ker hx
  have h3 : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h2 h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

private theorem ggK1Cov_comm_of_pow_eq_one {p : ℕ} {R L' : Type} [Group R] [Group L']
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L')
    (hcop : (Nat.card ψ.ker).Coprime p) {E₀ : Subgroup R} (hE₀ab : IsElemAbelian p E₀)
    {x y : L'} (hx : x ∈ E₀.comap ψ) (hy : y ∈ E₀.comap ψ)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) : x * y = y * x := by
  have hcN : ⁅x, y⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hE₀ab.comm hx hy)
  have hcc : Commute x ⁅x, y⁆ := (Subgroup.mem_center_iff.mp (hker hcN)) x
  have hcpow : ⁅x, y⁆ ^ p = 1 := by
    rw [hcc.commutatorElement_pow_left p, hxp]
    simp
  exact commutatorElement_eq_one_iff_commute.mp (ggK1Cov_ker_pow_eq_one ψ hcop hcN hcpow)

theorem ggK1_cover_center {p : ℕ} {D : GGKacDatum} {R L' : Type} [Group R] [Group L'] [Finite L']
    (I : Set (MulAut R)) (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hkerp : (Nat.card (Subgroup.center L')).Coprime p)
    (e : MulAut L') (he : e ^ p = 1) (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l))
    (hcore : GGK1Center p D R I φ) :
    2 ≤ D.rZ → ∃ E : Subgroup L', IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
      E ≤ ggFixSub e ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g) ∧
      ∀ A : Subgroup (MulAut L'), e ∈ A → IsElemAbelian p A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → ∀ z ∈ E, ∀ a ∈ A, a z = z := by
  intro h2
  obtain ⟨E₀, hE₀ab, hE₀card, hE₀fixφ, hE₀cent, hE₀fixI⟩ := hcore h2
  have hcop : (Nat.card ψ.ker).Coprime p := ggK1Cov_ker_coprime ψ hker hkerp
  let P : Subgroup L' := E₀.comap ψ
  have hcommP : ∀ x ∈ P, x ^ p = 1 → ∀ y ∈ P, y ^ p = 1 → x * y = y * x :=
    fun x hx hxp y hy hyp => ggK1Cov_comm_of_pow_eq_one ψ hker hcop hE₀ab hx hy hxp hyp
  let E : Subgroup L' :=
    { carrier := {x : L' | x ∈ P ∧ x ^ p = 1}
      mul_mem' := by
        rintro x y ⟨hxP, hxp⟩ ⟨hyP, hyp⟩
        refine ⟨P.mul_mem hxP hyP, ?_⟩
        rw [Commute.mul_pow (hcommP x hxP hxp y hyP hyp) p, hxp, hyp, mul_one]
      one_mem' := ⟨P.one_mem, one_pow p⟩
      inv_mem' := by
        rintro x ⟨hxP, hxp⟩
        exact ⟨P.inv_mem hxP, by rw [inv_pow, hxp, inv_one]⟩ }
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2⟩
    exact hcommP a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2
  have hEbotN : E ⊓ ψ.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact ggK1Cov_ker_pow_eq_one ψ hcop hx.2 hx.1.2
  have hsurj : ∀ a ∈ E₀, ∃ x ∈ E, ψ x = a := by
    intro a ha
    obtain ⟨x₀, hx₀⟩ := hψ a
    have hx₀E₀ : ψ x₀ ∈ E₀ := by rw [hx₀]; exact ha
    have hx₀P : x₀ ∈ P := by
      show ψ x₀ ∈ E₀
      exact hx₀E₀
    have hnker : x₀ ^ p ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hE₀ab.2 (ψ x₀) hx₀E₀
    have hinvker : (x₀ ^ p)⁻¹ ∈ ψ.ker := ψ.ker.inv_mem hnker
    obtain ⟨m, hm⟩ := (hcop.pow_left_bijective (G := ψ.ker)).2 ⟨(x₀ ^ p)⁻¹, hinvker⟩
    have hmpow : (m : L') ^ p = (x₀ ^ p)⁻¹ := by
      simpa using congrArg Subtype.val hm
    have hmker : (m : L') ∈ ψ.ker := m.2
    refine ⟨x₀ * m, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · show ψ (x₀ * m) ∈ E₀
        rw [map_mul, hx₀, MonoidHom.mem_ker.mp hmker, mul_one]
        exact ha
      · rw [Commute.mul_pow ((Subgroup.mem_center_iff.mp (hker hmker)) x₀) p, hmpow]
        simp
    · rw [map_mul, hx₀, MonoidHom.mem_ker.mp hmker, mul_one]
  let f : E → E₀ := fun x => ⟨ψ x, Subgroup.mem_comap.mp (show x.1 ∈ E₀.comap ψ from x.2.1)⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hψxy : ψ x.1 = ψ y.1 := congrArg Subtype.val hxy
    have hmem : x.1 * y.1⁻¹ ∈ E ⊓ ψ.ker := by
      refine ⟨E.mul_mem x.2 (E.inv_mem y.2), ?_⟩
      exact (MonoidHom.mem_ker).mpr (by rw [map_mul, map_inv, hψxy, mul_inv_cancel])
    rw [hEbotN] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem))
  have hfsurj : Function.Surjective f := by
    intro a
    obtain ⟨x, hxE, hxψ⟩ := hsurj a.1 a.2
    exact ⟨⟨x, hxE⟩, Subtype.ext hxψ⟩
  have hcard : Nat.card E = p ^ D.rZ := by
    rw [← hE₀card]
    exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  have hEfix : E ≤ ggFixSub e := by
    intro x hxE
    rw [mem_ggFixSub]
    have hxE₀ : ψ x ∈ E₀ := Subgroup.mem_comap.mp (show x ∈ E₀.comap ψ from hxE.1)
    have hexP : e x ∈ P := by
      show ψ (e x) ∈ E₀
      rw [← hφ x, hE₀fixφ hxE₀]
      exact hxE₀
    have hexE : e x ∈ E := ⟨hexP, by rw [← map_pow e x p, hxE.2, map_one]⟩
    have hdN : e x * x⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hφ x, hE₀fixφ hxE₀, mul_inv_cancel]
    have hmem : e x * x⁻¹ ∈ E ⊓ ψ.ker := ⟨E.mul_mem hexE (E.inv_mem hxE), hdN⟩
    rw [hEbotN] at hmem
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  have hEcent : ∀ z ∈ E, ∀ g ∈ ggFixSub e, g * z = z * g := by
    intro z hzE g hg
    have hzE₀ : ψ z ∈ E₀ := Subgroup.mem_comap.mp (show z ∈ E₀.comap ψ from hzE.1)
    have hgfix : ψ g ∈ ggFixSub φ := by
      rw [mem_ggFixSub, hφ g, mem_ggFixSub.mp hg]
    have hcommψ : ψ g * ψ z = ψ z * ψ g := hE₀cent (ψ z) hzE₀ (ψ g) hgfix
    have hgzg : ψ g * ψ z * (ψ g)⁻¹ = ψ z := by
      rw [hcommψ, mul_assoc, mul_inv_cancel, mul_one]
    have hconjP : g * z * g⁻¹ ∈ P := by
      show ψ (g * z * g⁻¹) ∈ E₀
      simp only [map_mul, map_inv]
      rw [hgzg]
      exact hzE₀
    have hconjE : g * z * g⁻¹ ∈ E := by
      refine ⟨hconjP, ?_⟩
      rw [show g * z * g⁻¹ = MulAut.conj g z from (MulAut.conj_apply g z).symm,
        ← map_pow (MulAut.conj g) z p, hzE.2, map_one]
    have hdN : g * z * g⁻¹ * z⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hgzg, mul_inv_cancel]
    have hmem : g * z * g⁻¹ * z⁻¹ ∈ E ⊓ ψ.ker :=
      ⟨E.mul_mem hconjE (E.inv_mem hzE), hdN⟩
    rw [hEbotN] at hmem
    have h1 : g * z * g⁻¹ * z⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : g * z * g⁻¹ = z := mul_inv_eq_one.mp h1
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h2]
  refine ⟨E, hEab, hcard, hEfix, hEcent, ?_⟩
  intro A heA hAab hAind z hzE a haA
  obtain ⟨φ', hφ'I, hφ'ind⟩ := hAind a haA
  have hap : a ^ p = 1 := hAab.2 a haA
  have hea : a * e = e * a := hAab.comm haA heA
  have hpow : ∀ n : ℕ, ∀ l : L', (φ' ^ n) (ψ l) = ψ ((a ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
        intro l
        rw [pow_succ, MulAut.mul_apply, hφ'ind l, ih (a l), pow_succ, MulAut.mul_apply]
  have hφ'p : φ' ^ p = 1 := by
    ext y
    obtain ⟨l, rfl⟩ := hψ y
    rw [hpow p l]
    have : (a ^ p) l = l := by rw [hap]; rfl
    rw [this]
    rfl
  have hcommφ : Commute φ' φ := by
    show φ' * φ = φ * φ'
    ext y
    obtain ⟨l, rfl⟩ := hψ y
    have hea' : a (e l) = e (a l) := by
      have := congrArg (fun f : MulAut L' => f l) hea
      simpa only [MulAut.mul_apply] using this
    rw [MulAut.mul_apply, MulAut.mul_apply, hφ l, hφ'ind (e l), hφ'ind l, hφ (a l), hea']
  have hfixE₀ : ∀ w ∈ E₀, φ' w = w := hE₀fixI φ' hφ'I hφ'p hcommφ
  have hzE₀ : ψ z ∈ E₀ := Subgroup.mem_comap.mp (show z ∈ E₀.comap ψ from hzE.1)
  have hψaz : ψ (a z) = ψ z := by
    rw [← hφ'ind z, hfixE₀ (ψ z) hzE₀]
  have hazP : a z ∈ P := by
    show ψ (a z) ∈ E₀
    rw [hψaz]
    exact hzE₀
  have hazE : a z ∈ E := ⟨hazP, by rw [← map_pow a z p, hzE.2, map_one]⟩
  have hd : a z * z⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψaz, mul_inv_cancel]
  have hmem : a z * z⁻¹ ∈ E ⊓ ψ.ker := ⟨E.mul_mem hazE (E.inv_mem hzE), hd⟩
  rw [hEbotN] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

theorem ggK1_cont_of_core {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop} {p : ℕ}
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)}
    (hcop : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      (Nat.card (Subgroup.center L')).Coprime p)
    (hcore : GGK1Core Valid p lab R I) : GGK1Cont Valid p lab R I := by
  intro L' hL'f hL'fin ψ hψ hker hcomm e he hind
  obtain ⟨φ, hφI, hφind⟩ := hind
  have hpow : ∀ n : ℕ, ∀ l : L', (φ ^ n) (ψ l) = ψ ((e ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
        intro l
        rw [pow_succ, MulAut.mul_apply, hφind l, ih (e l), pow_succ, MulAut.mul_apply]
  have hφp : φ ^ p = 1 := by
    ext y
    obtain ⟨l, rfl⟩ := hψ y
    have hev : (e ^ p) l = l := by simpa using congrArg (fun f : MulAut L' => f l) he
    rw [hpow p l, hev]
    rfl
  obtain ⟨D, hvalid, hcomp, hdvd, hcen, hbij, hsig⟩ := hcore φ hφI hφp
  have hkerp : (Nat.card (Subgroup.center L')).Coprime p :=
    hcop L' ψ hψ hker hcomm
  obtain ⟨ha, hb⟩ := ggK1_cover_comp ψ hψ hker e he φ hφind hcomp
  exact ⟨D, hvalid, ha, hb, ggK1_cover_dvd ψ hψ hker e φ hφind hdvd,
    ggK1_cover_center I ψ hψ hker hkerp e he φ hφind hcen,
    ggK1_cover_bij ψ hψ hker e φ hφind hbij,
    ggK1_cover_sigma I ψ hψ hker hkerp e φ hφind hsig⟩

end CFSG.StandardType

end
