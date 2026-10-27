module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFourB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Asc77 Subgroup
open scoped Pointwise commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} {π : Γ →* Equiv.Perm (ZMod p)} {D : Set Γ}

private lemma nine3_C_two_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hp.two_le)

private lemma nine3_C_zmodRefl_sq (c : ZMod p) : zmodRefl p c * zmodRefl p c = 1 := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.Perm.coe_one, id_eq]
  ring

private lemma nine3_C_zmodRefl_inv (c : ZMod p) : (zmodRefl p c)⁻¹ = zmodRefl p c :=
  inv_eq_of_mul_eq_one_right (nine3_C_zmodRefl_sq c)

private lemma nine3_C_zmodRefl_conj (c a : ZMod p) :
    zmodRefl p c * zmodRefl p a * zmodRefl p c = zmodRefl p (2 * c - a) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply]
  ring

private lemma nine3_C_conj_mem_fibre {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Nine3OddFrame p m π D) {a c : ZMod p} {d e : Γ}
    (hd : d ∈ nine3FibreSet π D a) (he : e ∈ nine3FibreSet π D c) :
    e * d * e⁻¹ ∈ nine3FibreSet π D (2 * c - a) := by
  refine ⟨h.conj d hd.1 e, ?_⟩
  rw [map_mul, map_mul, map_inv, hd.2, he.2, nine3_C_zmodRefl_inv]
  exact nine3_C_zmodRefl_conj c a

private lemma nine3_C_map_conj_closure {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Nine3OddFrame p m π D) {a c : ZMod p} {e : Γ}
    (he : e ∈ nine3FibreSet π D c) :
    Subgroup.map (MulAut.conj e).toMonoidHom (Subgroup.closure (nine3FibreSet π D a)) =
      Subgroup.closure (nine3FibreSet π D (2 * c - a)) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact nine3_C_conj_mem_fibre hp hp2 h hd he
  · intro hx
    have he' : e⁻¹ ∈ nine3FibreSet π D c := by
      have heq : e⁻¹ = e := inv_eq_of_mul_eq_one_right (h.sq e he.1)
      exact ⟨by simpa [heq] using he.1, by rw [map_inv, he.2, nine3_C_zmodRefl_inv]⟩
    have h2 : e⁻¹ * x * (e⁻¹)⁻¹ ∈ nine3FibreSet π D a := by
      have h3 := nine3_C_conj_mem_fibre hp hp2 h hx he'
      rwa [show 2 * c - (2 * c - a) = a by ring] at h3
    exact ⟨e⁻¹ * x * (e⁻¹)⁻¹, h2, by
      show e * (e⁻¹ * x * (e⁻¹)⁻¹) * e⁻¹ = x
      group⟩

private lemma nine3_C_exists_conj_closure {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Nine3OddFrame p m π D) (hm : 0 < m) (a c : ZMod p) :
    ∃ e : Γ, Subgroup.map (MulAut.conj e).toMonoidHom
      (Subgroup.closure (nine3FibreSet π D a)) = Subgroup.closure (nine3FibreSet π D c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := nine3_C_two_ne_zero hp hp2
  let t : ZMod p := (a + c) * (2 : ZMod p)⁻¹
  have ht : 2 * t - a = c := by
    have h22 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    calc 2 * t - a = 2 * ((a + c) * 2⁻¹) - a := rfl
      _ = (2 * 2⁻¹) * (a + c) - a := by ring
      _ = (a + c) - a := by rw [h22, one_mul]
      _ = c := by ring
  have hpos : 0 < Nat.card {d : Γ // d ∈ D ∧ π d = zmodRefl p t} := by
    rw [h.card t]; exact hm
  obtain ⟨d⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨d.1, by rw [nine3_C_map_conj_closure hp hp2 h (a := a) (c := t) d.2, ht]⟩

private lemma nine3_C_closure_comm {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p}
    {x y : Γ} (hx : x ∈ Subgroup.closure (nine3FibreSet π D c))
    (hy : y ∈ Subgroup.closure (nine3FibreSet π D c)) : x * y = y * x := by
  have hcomm : (nine3FibreSet π D c).Pairwise Commute := fun a ha b hb _ =>
    h.comm a ha.1 b hb.1 (ha.2.trans hb.2.symm)
  letI : CommGroup ↥(Subgroup.closure (nine3FibreSet π D c)) :=
    Subgroup.closureCommGroupOfComm hcomm
  have hxy := mul_comm (⟨x, hx⟩ : ↥(Subgroup.closure (nine3FibreSet π D c))) ⟨y, hy⟩
  simpa using congrArg Subtype.val hxy

private lemma nine3_C_closure_sq {m : ℕ} (h : Nine3OddFrame p m π D) {c : ZMod p}
    {x : Γ} (hx : x ∈ Subgroup.closure (nine3FibreSet π D c)) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h.sq y hy.1
  | one => simp
  | mul a b ha hb iha ihb =>
      have hab := nine3_C_closure_comm h ha hb
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
  | inv a _ iha =>
      rw [inv_eq_of_mul_eq_one_right iha]
      exact iha

theorem nine3OddFrame_ne_five (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    (hi : Nine3FibreIndep p π D) : p ≠ 5 := by
  intro hp5
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h01 : (0 : ZMod p) ≠ 1 := (one_ne_zero : (1 : ZMod p) ≠ 0).symm
  let Z : ZMod p → Subgroup Γ := fun c => Subgroup.closure (nine3FibreSet π D c) ⊓ π.ker
  let C : Subgroup Γ := Z 0 ⊓ Z 1
  have hZcard : ∀ c, Nat.card ↥(Z c) = 8 := fun c =>
    nine3OddFrame_card_inf_ker hp hp2 h hi c
  have hCcard_le : Nat.card ↥C ≤ 2 := by
    have heq : C = Subgroup.closure (nine3FibreSet π D 0) ⊓
        Subgroup.closure (nine3FibreSet π D 1) ⊓ π.ker := by
      ext x; simp only [C, Z, Subgroup.mem_inf]; tauto
    rw [heq]
    exact nine3OddFrame_card_inf_le_two hp hp2 h hi h01
  have hcenter01 : C ≤ Subgroup.center Γ := by
    have heq : C = Subgroup.closure (nine3FibreSet π D 0) ⊓
        Subgroup.closure (nine3FibreSet π D 1) ⊓ π.ker := by
      ext x; simp only [C, Z, Subgroup.mem_inf]; tauto
    rw [heq]
    exact nine3OddFrame_inf_le_center hp hp2 h h01
  have hcle : ∀ c, C ≤ Z c := by
    intro c x hx
    have hxcenter : x ∈ Subgroup.center Γ := hcenter01 hx
    have hxker : x ∈ π.ker := hx.1.2
    refine ⟨?_, hxker⟩
    obtain ⟨e, he⟩ := nine3_C_exists_conj_closure hp hp2 h (by norm_num) 0 c
    have hfix : e * x * e⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hxcenter e
      rw [hcomm]; group
    rw [← he]
    refine ⟨x, hx.1.1, ?_⟩
    show e * x * e⁻¹ = x
    exact hfix
  have hZleC : ∀ {c c' : ZMod p}, c ≠ c' → Z c ⊓ Z c' ≤ C := by
    intro c c' hcc' x hx
    have hxcenter : x ∈ Subgroup.center Γ := by
      apply nine3OddFrame_inf_le_center hp hp2 h hcc'
      exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
    have key : ∀ d d' : ZMod p, x ∈ Z d → x ∈ Z d' := by
      intro d d' hxd
      refine ⟨?_, hxd.2⟩
      obtain ⟨e, he⟩ := nine3_C_exists_conj_closure hp hp2 h (by norm_num) d d'
      have hfix : e * x * e⁻¹ = x := by
        have hcomm := Subgroup.mem_center_iff.mp hxcenter e
        rw [hcomm]; group
      rw [← he]
      refine ⟨x, hxd.1, ?_⟩
      show e * x * e⁻¹ = x
      exact hfix
    exact ⟨key c 0 hx.1, key c' 1 hx.2⟩
  haveI : Fintype ↥(π.ker) := Fintype.ofFinite _
  haveI : Fintype ↥C := Fintype.ofFinite _
  haveI : ∀ c : ZMod p, Fintype ↥(Z c) := fun c => Fintype.ofFinite _
  let α := Σ c : ZMod p, {y : ↥(Z c) // (y : Γ) ∉ C}
  let β := {x : ↥(π.ker) // (x : Γ) ∉ C}
  let f : α → β := fun a =>
    ⟨⟨(a.2.1 : Γ), (inf_le_right : Z a.1 ≤ π.ker) a.2.1.2⟩, a.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, y, hy⟩ ⟨c', y', hy'⟩ heq
    have hyy : ((y : ↥(Z c)) : Γ) = ((y' : ↥(Z c')) : Γ) :=
      Subtype.ext_iff.mp (Subtype.ext_iff.mp heq)
    have hcc : c = c' := by
      by_contra hne
      have hyC : ((y : ↥(Z c)) : Γ) ∈ C := by
        have h1 : ((y : ↥(Z c)) : Γ) ∈ Z c := y.2
        have h2 : ((y : ↥(Z c)) : Γ) ∈ Z c' := by rw [hyy]; exact y'.2
        exact hZleC hne ⟨h1, h2⟩
      exact hy hyC
    subst hcc
    have hyy' : y = y' := Subtype.ext hyy
    subst hyy'
    rfl
  have hαcard : Fintype.card α = p * (8 - Nat.card ↥C) := by
    change Fintype.card (Σ c : ZMod p,
      {y : ↥(Z c) // (y : Γ) ∉ C}) = p * (8 - Nat.card ↥C)
    rw [Fintype.card_sigma]
    have hterm : ∀ c, Fintype.card {y : ↥(Z c) // (y : Γ) ∉ C} =
        8 - Nat.card ↥C := by
      intro c
      rw [Fintype.card_subtype_compl (fun y : ↥(Z c) => (y : Γ) ∈ C)]
      have h1 : Fintype.card ↥(Z c) = 8 := by
        rw [← Nat.card_eq_fintype_card]; exact hZcard c
      have h2 : Fintype.card {y : ↥(Z c) // (y : Γ) ∈ C} = Nat.card ↥C := by
        let e : {y : ↥(Z c) // (y : Γ) ∈ C} ≃ ↥C :=
          { toFun := fun y => ⟨(y.1 : Γ), y.2⟩
            invFun := fun x => ⟨⟨(x : Γ), hcle c x.2⟩, x.2⟩
            left_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl
            right_inv := fun x => rfl }
        rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card]
      rw [h1, h2]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
    simp
  have hβcard : Fintype.card β = 32 - Nat.card ↥C := by
    change Fintype.card {x : ↥(π.ker) // (x : Γ) ∉ C} = 32 - Nat.card ↥C
    rw [Fintype.card_subtype_compl (fun x : ↥(π.ker) => (x : Γ) ∈ C)]
    have h1 : Fintype.card ↥(π.ker) = 32 := by
      rw [← Nat.card_eq_fintype_card]; exact nine3OddFrame_card_ker hp hp2 h hi
    have h2 : Fintype.card {x : ↥(π.ker) // (x : Γ) ∈ C} = Nat.card ↥C := by
      let e : {x : ↥(π.ker) // (x : Γ) ∈ C} ≃ ↥C :=
        { toFun := fun x => ⟨(x.1 : Γ), x.2⟩
          invFun := fun x => ⟨⟨(x : Γ), (inf_le_right : Z 1 ≤ π.ker)
            ((inf_le_right : Z 0 ⊓ Z 1 ≤ Z 1) x.2)⟩, x.2⟩
          left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := fun x => rfl }
      rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card]
    rw [h1, h2]
  have hcard_le : p * (8 - Nat.card ↥C) ≤ 32 - Nat.card ↥C := by
    rw [← hαcard, ← hβcard]
    exact Fintype.card_le_of_injective f hf
  have hCcard : Nat.card ↥C = 2 := by
    have hge : 2 ≤ Nat.card ↥C := by
      have hthis := hcard_le
      rw [hp5] at hthis
      omega
    omega
  have hcardα : Fintype.card α = 30 := by
    rw [hαcard, hCcard, hp5]
  have hcardβ : Fintype.card β = 30 := by
    rw [hβcard, hCcard]
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf, by rw [hcardα, hcardβ]⟩).2
  have hcover : ∀ x ∈ π.ker, ∃ c : ZMod p, x ∈ Z c := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact ⟨0, hcle 0 hxC⟩
    · obtain ⟨a, ha⟩ := hsurj (⟨⟨x, hx⟩, by simpa using hxC⟩ : β)
      refine ⟨a.1, ?_⟩
      have hval : ((a.2.1 : ↥(Z a.1)) : Γ) = x := by
        have hh := congrArg (fun b : β => ((b : ↥(π.ker)) : Γ)) ha
        simpa [f] using hh
      rw [← hval]
      exact a.2.1.2
  have hsq_ker : ∀ x ∈ π.ker, x * x = 1 := by
    intro x hx
    obtain ⟨c, hc⟩ := hcover x hx
    exact nine3_C_closure_sq h hc.1
  have hab : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b) * (a * b) = 1 := hsq_ker (a * b) (π.ker.mul_mem ha hb)
    have h2 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq_ker b hb),
      inv_eq_of_mul_eq_one_right (hsq_ker a ha)]
  exact nine3OddFrame_ker_not_comm hp hp2 h hi hab

theorem nine3OddFrame_four_p (hp : p.Prime) (hp2 : p ≠ 2) (h : Nine3OddFrame p 4 π D)
    (hi : Nine3FibreIndep p π D) : p = 3 := by
  have hle : p ≤ 5 := nine3OddFrame_prime_le_five hp hp2 h hi
  have hne : p ≠ 5 := nine3OddFrame_ne_five hp hp2 h hi
  have hp2le : 2 ≤ p := hp.two_le
  interval_cases p
  · exact absurd rfl hp2
  · rfl
  · exact absurd hp (by decide)
  · exact absurd rfl hne

end CFSG.LocalAnalysis.WeakClosure81
