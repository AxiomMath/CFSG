module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.GroupTheory.ConjKerCenter

@[expose] public section

namespace CFSG.StandardType.RelA5

open CFSG CFSG.Assembly

theorem conj_eq_one_iff_mem_center {G : Type*} [Group G] {z : G} :
    MulAut.conj z = 1 ↔ z ∈ Subgroup.center G := by
  rw [← CFSG.GroupTheory.ker_conj_eq_center]
  exact (MonoidHom.mem_ker (f := (MulAut.conj : G →* MulAut G))).symm

theorem exists_eq_conj_of_induced {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {a : MulAut L'} {r : R}
    (h : ∀ l, ψ (a l) = r * ψ l * r⁻¹) : ∃ l, ψ l = r ∧ a = MulAut.conj l := by
  obtain ⟨l, hl⟩ := hψ r
  refine ⟨l, hl, ?_⟩
  let b : MulAut L' := (MulAut.conj l)⁻¹ * a
  have hb : ∀ x : L', ψ (b x) = ψ x := by
    intro x
    have hbx : b x = l⁻¹ * a x * l := by
      simp [b, MulAut.conj_symm_apply]
    rw [hbx]
    simp only [map_mul, map_inv, hl, h x]
    group
  have hbker : ∀ x : L', x⁻¹ * b x ∈ Subgroup.center L' := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hb x]
    exact inv_mul_cancel (ψ x)
  have heq : (MonoidHom.id L' : L' →* L') = b.toMonoidHom :=
    CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperf (MonoidHom.id L') b.toMonoidHom
      hbker
  have hb1 : b = 1 := by
    ext x
    have hx := congrArg (fun f : L' →* L' => f x) heq
    simpa using hx.symm
  have ha : MulAut.conj l = a := by
    have hcalc : (MulAut.conj l) * b = a := by
      rw [show b = (MulAut.conj l)⁻¹ * a from rfl]
      group
    rwa [hb1, mul_one] at hcalc
  exact ha.symm

theorem mem_center_of_map_mem_center {H L' : Type} [Group H] [Group L']
    (hHperf : commutator H = ⊤) {Φ : H →* L'} (hΦker : Φ.ker ≤ Subgroup.center H) {x : H}
    (hx : Φ x ∈ Subgroup.center L') : x ∈ Subgroup.center H := by
  let β : H →* H := (MulAut.conj x).toMonoidHom
  have hβ : ∀ s : H, Φ (β s) = Φ s := by
    intro s
    have hβs : β s = x * s * x⁻¹ := by
      simp [β, MulAut.conj_apply]
    rw [hβs]
    simp only [map_mul, map_inv]
    rw [← Subgroup.mem_center_iff.mp hx (Φ s)]
    group
  have hker : ∀ s : H, s⁻¹ * β s ∈ Subgroup.center H := by
    intro s
    apply hΦker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hβ s]
    exact inv_mul_cancel (Φ s)
  have heq : (MonoidHom.id H : H →* H) = β :=
    CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hHperf (MonoidHom.id H) β hker
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : x * y * x⁻¹ = y := by
    have h1 := congrArg (fun f : H →* H => f y) heq
    simpa [β, MulAut.conj_apply] using h1.symm
  calc y * x = (x * y * x⁻¹) * x := by rw [hy]
    _ = x * y := by group

theorem exists_elemAbelian_lift {p : ℕ} (hp : p.Prime) {H L' : Type} [Group H] [Finite H]
    [Group L'] (hHperf : commutator H = ⊤) {Φ : H →* L'} (hΦ : Function.Surjective Φ)
    (hΦker : Φ.ker ≤ Subgroup.center H) (hcop : ¬ p ∣ Nat.card (Subgroup.center H))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hinn : ∀ a ∈ A, ∃ l : L', a = MulAut.conj l) :
    ∃ E : Subgroup H, IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
      A = (E.map Φ).map (MulAut.conj : L' →* MulAut L') ∧
      ∀ x : H, x ∈ E ↔ (MulAut.conj (Φ x) ∈ A ∧ x ^ p = 1) := by
  classical
  let Ψ : H →* MulAut L' := MulAut.conj.comp Φ
  let Ê : Subgroup H := A.comap Ψ
  have hmemÊ : ∀ x : H, x ∈ Ê ↔ Ψ x ∈ A := fun x => Subgroup.mem_comap
  have hcommCenter : ∀ x : H, x ∈ Ê → ∀ y : H, y ∈ Ê →
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H := by
    intro x hx y hy
    have hxA : Ψ x ∈ A := (hmemÊ x).mp hx
    have hyA : Ψ y ∈ A := (hmemÊ y).mp hy
    have hΨ1 : Ψ (x * y * x⁻¹ * y⁻¹) = 1 := by
      have hxy : Ψ x * Ψ y = Ψ y * Ψ x :=
        congrArg Subtype.val ((isMulCommutative_iff.mp hA.1) ⟨Ψ x, hxA⟩ ⟨Ψ y, hyA⟩)
      simp only [map_mul, map_inv]
      rw [hxy]
      group
    have hΦc : Φ (x * y * x⁻¹ * y⁻¹) ∈ Subgroup.center L' :=
      (conj_eq_one_iff_mem_center).mp (by simpa [Ψ] using hΨ1)
    exact mem_center_of_map_mem_center hHperf hΦker hΦc
  have hpowCenter : ∀ x : H, x ∈ Ê → x ^ p ∈ Subgroup.center H := by
    intro x hx
    have hxA : Ψ x ∈ A := (hmemÊ x).mp hx
    have hΨ1 : Ψ (x ^ p) = 1 := by
      rw [map_pow]
      exact hA.2 (Ψ x) hxA
    have hΦc : Φ (x ^ p) ∈ Subgroup.center L' :=
      (conj_eq_one_iff_mem_center).mp (by simpa [Ψ] using hΨ1)
    exact mem_center_of_map_mem_center hHperf hΦker hΦc
  have hEcomm : ∀ x : H, Ψ x ∈ A → x ^ p = 1 → ∀ y : H, Ψ y ∈ A → y ^ p = 1 →
      Commute x y := by
    intro x hxA hxp y hyA hyp
    have hxÊ : x ∈ Ê := (hmemÊ x).mpr hxA
    have hyÊ : y ∈ Ê := (hmemÊ y).mpr hyA
    have hz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H := hcommCenter x hxÊ y hyÊ
    have hxyz : (x * y * x⁻¹) ^ p = 1 := by
      rw [show x * y * x⁻¹ = (MulAut.conj x) y from by rw [MulAut.conj_apply]]
      rw [← map_pow, hyp, map_one]
    have hzy : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [hzy] at hxyz
    have hzc : Commute (x * y * x⁻¹ * y⁻¹) y :=
      (Subgroup.mem_center_iff.mp hz y).symm
    rw [hzc.mul_pow p] at hxyz
    rw [hyp, mul_one] at hxyz
    have hdvd : orderOf (x * y * x⁻¹ * y⁻¹) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr hxyz
    have hcard : orderOf (x * y * x⁻¹ * y⁻¹) ∣ Nat.card (Subgroup.center H) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center H) hz
    have hz1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rcases hp.eq_one_or_self_of_dvd (orderOf (x * y * x⁻¹ * y⁻¹)) hdvd with h1 | hp'
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd (hp' ▸ hcard) hcop
    have hconj : x * y * x⁻¹ = y := by
      have h := congrArg (fun t : H => t * y) hz1
      simpa [mul_assoc] using h
    show x * y = y * x
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hconj]
  let E : Subgroup H :=
    { carrier := {x | Ψ x ∈ A ∧ x ^ p = 1}
      one_mem' := by
        refine ⟨?_, one_pow p⟩
        rw [map_one]
        exact A.one_mem
      mul_mem' := by
        intro x y hx hy
        refine ⟨?_, ?_⟩
        · rw [map_mul]
          exact A.mul_mem hx.1 hy.1
        · have hc : Commute x y := hEcomm x hx.1 hx.2 y hy.1 hy.2
          rw [hc.mul_pow p, hx.2, hy.2, mul_one]
      inv_mem' := by
        intro x hx
        refine ⟨?_, ?_⟩
        · rw [map_inv]
          exact A.inv_mem hx.1
        · rw [inv_pow, hx.2, inv_one] }
  have hE_mem : ∀ x : H, x ∈ E ↔ (MulAut.conj (Φ x) ∈ A ∧ x ^ p = 1) := by
    intro x
    exact Iff.rfl
  have hEcomm' : ∀ x y : E, x * y = y * x := by
    intro x y
    apply Subtype.ext
    show (x : H) * (y : H) = (y : H) * (x : H)
    exact hEcomm x.1 ((hE_mem x.1).mp x.2).1 ((hE_mem x.1).mp x.2).2
      y.1 ((hE_mem y.1).mp y.2).1 ((hE_mem y.1).mp y.2).2
  have hEel : IsElemAbelian p E := by
    refine ⟨?_, ?_⟩
    · exact isMulCommutative_iff.mpr (fun x y => hEcomm' x y)
    · intro x hx
      exact ((hE_mem x).mp hx).2
  have hker_triv : ∀ e : H, e ∈ E → Ψ e = 1 → e = 1 := by
    intro e he hΨ1
    have hΦc : Φ e ∈ Subgroup.center L' :=
      (conj_eq_one_iff_mem_center).mp (by simpa [Ψ] using hΨ1)
    have heZ : e ∈ Subgroup.center H := mem_center_of_map_mem_center hHperf hΦker hΦc
    have hep : e ^ p = 1 := ((hE_mem e).mp he).2
    have hdvd : orderOf e ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hep
    have hcardZ : orderOf e ∣ Nat.card (Subgroup.center H) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center H) heZ
    rcases hp.eq_one_or_self_of_dvd (orderOf e) hdvd with h1 | hp'
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (hp' ▸ hcardZ) hcop
  let f : E → A := fun e => ⟨Ψ e.1, ((hE_mem e.1).mp e.2).1⟩
  have hf_inj : Function.Injective f := by
    intro e1 e2 he
    have hΨ : Ψ e1.1 = Ψ e2.1 := congrArg Subtype.val he
    have hmem : e1.1⁻¹ * e2.1 ∈ E := E.mul_mem (E.inv_mem e1.2) e2.2
    have h1 : e1.1⁻¹ * e2.1 = 1 := by
      apply hker_triv (e1.1⁻¹ * e2.1) hmem
      rw [map_mul, map_inv, hΨ]
      exact inv_mul_cancel (Ψ e2.1)
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hf_surj : Function.Surjective f := by
    intro a
    obtain ⟨l, hl⟩ := hinn a.1 a.2
    obtain ⟨x, hxΦ⟩ := hΦ l
    have hΨx : Ψ x = a.1 := by
      show MulAut.conj (Φ x) = a.1
      rw [hxΦ, ← hl]
    have hxÊ : x ∈ Ê := (hmemÊ x).mpr (hΨx ▸ a.2)
    have hxpZ : x ^ p ∈ Subgroup.center H := hpowCenter x hxÊ
    have hcop' : (Nat.card (Subgroup.center H)).Coprime p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcop).symm
    obtain ⟨w, hw⟩ := (powCoprime hcop').surjective ⟨x ^ p, hxpZ⟩
    have hwp : (w : H) ^ p = x ^ p := by
      have h1 : ((powCoprime hcop') w : Subgroup.center H).val = x ^ p :=
        congrArg Subtype.val hw
      rw [powCoprime_apply] at h1
      simpa using h1
    have hwΦ : Ψ (w : H) = 1 := by
      show MulAut.conj (Φ (w : H)) = 1
      exact (conj_eq_one_iff_mem_center).mpr
        (Subgroup.map_center_le_center hΦ (Subgroup.mem_map_of_mem Φ w.2))
    let e : H := x * (w : H)⁻¹
    have heE : e ∈ E := by
      refine (hE_mem e).mpr ⟨?_, ?_⟩
      · change Ψ e ∈ A
        rw [show e = x * (w : H)⁻¹ from rfl, map_mul, map_inv, hwΦ, inv_one, mul_one]
        exact hΨx ▸ a.2
      · have hxw : Commute x ((w : H)) := Subgroup.mem_center_iff.mp w.2 x
        have hxwinv : Commute x ((w : H)⁻¹) := hxw.inv_right
        rw [show e = x * (w : H)⁻¹ from rfl, hxwinv.mul_pow p, inv_pow, hwp]
        exact mul_inv_cancel (x ^ p)
    refine ⟨⟨e, heE⟩, ?_⟩
    apply Subtype.ext
    change Ψ e = a.1
    rw [show e = x * (w : H)⁻¹ from rfl, map_mul, map_inv, hwΦ, inv_one, mul_one]
    exact hΨx
  have hcard : Nat.card E = Nat.card A :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hAeq : A = (E.map Φ).map (MulAut.conj : L' →* MulAut L') := by
    apply le_antisymm
    · intro a ha
      obtain ⟨e, he⟩ := hf_surj ⟨a, ha⟩
      have hval : MulAut.conj (Φ e.1) = a := by
        simpa [f, Ψ] using congrArg Subtype.val he
      rw [← hval]
      exact Subgroup.mem_map.mpr
        ⟨Φ e.1, Subgroup.mem_map.mpr ⟨e.1, e.2, rfl⟩, rfl⟩
    · intro a ha
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hl
      exact ((hE_mem e).mp he).1
  exact ⟨E, hEel, hcard, hAeq, hE_mem⟩

end CFSG.StandardType.RelA5
