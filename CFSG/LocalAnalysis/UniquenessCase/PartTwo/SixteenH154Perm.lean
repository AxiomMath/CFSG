module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

private theorem s16h_perm_eq_one_of_fixes {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)}
    (hgen : (⨆ X ∈ conjSubs A (commSub (⊤ : Subgroup W) L), X) = ⊤)
    (h2 : ∀ g ∈ A, g ∉ normalizer (L : Set (MulAut W)) →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥)
    {l : MulAut W} (hl : l ∈ L)
    (hfix : ∀ u ∈ commSub (⊤ : Subgroup W) L, l u = u) : l = 1 := by
  have hF : fixV (Subgroup.zpowers l) = ⊤ := by
    rw [← top_le_iff, ← hgen]
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    obtain ⟨a, ha, rfl⟩ := hX
    intro u hu
    rw [mem_fixV_zpowers_iff_apply]
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
    by_cases haN : a ∈ normalizer (L : Set (MulAut W))
    · have haw : a w ∈ commSub (⊤ : Subgroup W) L :=
        commSub_top_map151b (X := L) (Y := L) (g := a)
          (fun x hx => (Subgroup.mem_normalizer_iff.mp haN x).mp hx) w hw
      exact hfix (a w) haw
    · have hainvN : a⁻¹ ∉ normalizer (L : Set (MulAut W)) := by
        intro hcon
        exact haN ((normalizer (L : Set (MulAut W))).inv_mem hcon)
      have hbot := (h2 a⁻¹ (A.inv_mem ha) hainvN).2
      have hle := commSub_eq_bot_iff.mp hbot
      have hy : (MulAut.conj a⁻¹).toMonoidHom l ∈ L.map (MulAut.conj a⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj a⁻¹).toMonoidHom hl
      have hconj : (MulAut.conj a⁻¹).toMonoidHom l = a⁻¹ * l * a := rfl
      have hfixy : (a⁻¹ * l * a) w = w := by
        rw [← hconj]
        exact (mem_fixV.mp (hle hw)) _ hy
      have h1 : a⁻¹ (l (a w)) = w := by
        simpa [MulAut.mul_apply] using hfixy
      have h2' : l (a w) = a w := by
        have := congrArg (fun z => a z) h1
        rwa [MulAut.apply_inv_self] at this
      exact h2'
  ext v
  have hv : v ∈ fixV (Subgroup.zpowers l) := by rw [hF]; trivial
  simpa using (mem_fixV_zpowers_iff_apply.mp hv)

theorem s16h_sSupIndep_conj_of_conc {W : Type} [CommGroup W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (h : Conc4_136W A t L) :
    sSupIndep {X : Subgroup (MulAut W) | ∃ q ∈ A, X = L.map (MulAut.conj q).toMonoidHom} := by
  intro X hX
  obtain ⟨a, ha, rfl⟩ := hX
  let Wt : Subgroup W := commSub (⊤ : Subgroup W) L
  let K : Subgroup (MulAut W) :=
    { carrier := {y | ∀ u ∈ Wt, y (a u) = a u}
      one_mem' := by intro u _; rfl
      mul_mem' := by
        intro y z hy hz u hu
        rw [MulAut.mul_apply, hz u hu, hy u hu]
      inv_mem' := by
        intro y hy u hu
        apply y.injective
        show y ((y⁻¹) (a u)) = y (a u)
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        exact (hy u hu).symm }
  have hK : sSup ({X : Subgroup (MulAut W) | ∃ q ∈ A, X = L.map (MulAut.conj q).toMonoidHom}
      \ {L.map (MulAut.conj a).toMonoidHom}) ≤ K := by
    apply sSup_le
    intro Y hY
    obtain ⟨hYS, hYne⟩ := hY
    obtain ⟨b, hb, hYeq⟩ := hYS
    have hne' : L.map (MulAut.conj b).toMonoidHom ≠ L.map (MulAut.conj a).toMonoidHom :=
      fun hh => hYne (hYeq.trans hh)
    rw [hYeq]
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    intro u hu
    change (b * l * b⁻¹) (a u) = a u
    let r : MulAut W := b⁻¹ * a
    have hrA : r ∈ A := A.mul_mem (A.inv_mem hb) ha
    have hrN : r ∉ normalizer (L : Set (MulAut W)) := by
      intro hr
      have hrmap : L.map (MulAut.conj r).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hr
      have hcomp : (MulAut.conj b).toMonoidHom.comp (MulAut.conj r).toMonoidHom =
          (MulAut.conj a).toMonoidHom := by
        have h1 : MulAut.conj b * MulAut.conj r = MulAut.conj a := by
          rw [← map_mul]
          congr 1
          show b * r = a
          rw [show r = b⁻¹ * a from rfl]; group
        rw [← h1]; rfl
      have hmap : (L.map (MulAut.conj r).toMonoidHom).map (MulAut.conj b).toMonoidHom =
          L.map (MulAut.conj a).toMonoidHom := by
        rw [Subgroup.map_map, hcomp]
      have hbridge : L.map (MulAut.conj b).toMonoidHom =
          (L.map (MulAut.conj r).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
        rw [hrmap]
      exact hne' (hbridge.trans hmap)
    have hrInvN : r⁻¹ ∉ normalizer (L : Set (MulAut W)) := by
      intro hcon
      exact hrN ((normalizer (L : Set (MulAut W))).inv_mem hcon)
    have hbot := (h.2.1 r⁻¹ (A.inv_mem hrA) hrInvN).2
    have hle : Wt ≤ fixV (L.map (MulAut.conj r⁻¹).toMonoidHom) := commSub_eq_bot_iff.mp hbot
    have hlu : l (r u) = r u := by
      have hy' : (MulAut.conj r⁻¹).toMonoidHom l ∈ L.map (MulAut.conj r⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hl
      have hfix : ((MulAut.conj r⁻¹).toMonoidHom l) u = u := (mem_fixV.mp (hle hu)) _ hy'
      have hconj : (MulAut.conj r⁻¹).toMonoidHom l = r⁻¹ * l * r := by
        simp [MulAut.conj_apply]
      rw [hconj] at hfix
      have heq : l (r u) = r ((r⁻¹ * l * r) u) := by
        have hfun : l * r = r * (r⁻¹ * l * r) := by group
        simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f u) hfun
      rw [heq, hfix]
    have hbr : b * r = a := by
      show b * (b⁻¹ * a) = a
      group
    have hau : a u = b (r u) := by rw [← hbr, MulAut.mul_apply]
    calc (b * l * b⁻¹) (a u)
        = (b * l * b⁻¹) (b (r u)) := by rw [hau]
      _ = b (l (r u)) := by rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      _ = b (r u) := by rw [hlu]
      _ = a u := by rw [hau]
  rw [Subgroup.disjoint_def]
  intro x hxX hxJ
  have hxK : x ∈ K := hK hxJ
  obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.mp hxX
  rw [← hl_eq] at hxK
  have hfixl : ∀ u ∈ Wt, l u = u := by
    intro u hu
    have hxfix : (a * l * a⁻¹) (a u) = a u := by
      simpa [MulAut.conj_apply] using hxK u hu
    have h1 : a (l u) = a u := by
      simpa [MulAut.mul_apply, MulAut.inv_apply_self] using hxfix
    exact a.injective h1
  have hl1 : l = 1 := s16h_perm_eq_one_of_fixes h.1 h.2.1 hl hfixl
  rw [← hl_eq, hl1, map_one]

private theorem s16h_isElemAbelian_of_card_eq_prime {A : Type*} [Group A] {p : ℕ}
    (hp : p.Prime) {H : Subgroup A} (hH : Nat.card ↥H = p) : IsElemAbelian p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥H := isCyclic_of_prime_card hH
  refine ⟨inferInstance, ?_⟩
  intro x hx
  have h := pow_card_eq_one' (G := ↥H) (x := ⟨x, hx⟩)
  rw [hH] at h
  simpa using Subtype.ext_iff.mp h

theorem s16h_closure_inf_commutator {A : Type*} [Group A] [Finite A] {Mb Lb : Subgroup A}
    {p : ℕ} (hp : p.Prime) (hLb : Nat.card ↥Lb = p) (hLM : Lb ≤ Mb)
    (hcomm : ∀ q ∈ Mb, ∀ q' ∈ Mb,
      Lb.map (MulAut.conj q).toMonoidHom ≠ Lb.map (MulAut.conj q').toMonoidHom →
        ⁅Lb.map (MulAut.conj q).toMonoidHom, Lb.map (MulAut.conj q').toMonoidHom⁆ = ⊥)
    (hind : sSupIndep {X : Subgroup A | ∃ q ∈ Mb, X = Lb.map (MulAut.conj q).toMonoidHom}) :
    ∃ (X : Subgroup A) (n : ℕ), X ≤ ⁅Mb, Mb⁆ ∧ (∀ q ∈ Mb, ∀ x ∈ X, q * x * q⁻¹ ∈ X) ∧
      IsElemAbelian p X ∧ Nat.card ↥X = p ^ n ∧
      Set.ncard {X : Subgroup A | ∃ q ∈ Mb, X = Lb.map (MulAut.conj q).toMonoidHom} - 1 ≤ n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let S : Set (Subgroup A) := {X : Subgroup A | ∃ q ∈ Mb, X = Lb.map (MulAut.conj q).toMonoidHom}
  let X0 : Subgroup A := sSup S
  let Hm : Subgroup A := ⁅Mb, Mb⁆
  have hS_range : S = Set.range (fun q : Mb => Lb.map (MulAut.conj (q : A)).toMonoidHom) := by
    ext U
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.2, rfl⟩
  have hSfin : S.Finite := by
    rw [hS_range]
    exact Set.finite_range (fun q : Mb => Lb.map (MulAut.conj (q : A)).toMonoidHom)
  haveI : Fintype ↥S := hSfin.fintype
  have hcard_mem : ∀ ω : ↥S, Nat.card ↥(ω : Subgroup A) = p := by
    intro ω
    obtain ⟨q, hq, hqeq⟩ := ω.2
    rw [hqeq, Subgroup.card_map_of_injective (MulAut.conj q).injective, hLb]
  let Hsub : ↥S → Subgroup A := fun ω => (ω : Subgroup A)
  have hcommS : Pairwise fun i j : ↥S => ∀ x y : A, x ∈ Hsub i → y ∈ Hsub j → Commute x y := by
    rintro i j hij x y hx hy
    obtain ⟨q, hq, hqeq⟩ := i.2
    obtain ⟨q', hq', hq'eq⟩ := j.2
    have hne : Lb.map (MulAut.conj q).toMonoidHom ≠ Lb.map (MulAut.conj q').toMonoidHom := by
      intro heq
      exact hij (Subtype.ext (by rw [hqeq, hq'eq, heq]))
    have hx' : x ∈ Lb.map (MulAut.conj q).toMonoidHom := hqeq ▸ hx
    have hy' : y ∈ Lb.map (MulAut.conj q').toMonoidHom := hq'eq ▸ hy
    have hmem := Subgroup.commutator_mem_commutator hx' hy'
    rw [hcomm q hq q' hq' hne, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.mp hmem
  have hφinj : Function.Injective (Subgroup.noncommPiCoprod (H := Hsub) hcommS) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep ((sSupIndep_iff S).1 hind)
  have hX0eq : X0 = ⨆ ω : ↥S, (ω : Subgroup A) := sSup_eq_iSup' S
  have hφrange : (Subgroup.noncommPiCoprod (H := Hsub) hcommS).range = X0 := by
    rw [Subgroup.noncommPiCoprod_range]
    change (⨆ i : ↥S, (i : Subgroup A)) = X0
    rw [← sSup_eq_iSup']
  have hcardX0 : Nat.card ↥X0 = p ^ Set.ncard S := by
    have hker : (Subgroup.noncommPiCoprod (H := Hsub) hcommS).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).2 hφinj
    have hcard := Subgroup.card_ker_mul_card_range (Subgroup.noncommPiCoprod (H := Hsub) hcommS)
    rw [hker, Subgroup.card_bot, one_mul, hφrange] at hcard
    calc Nat.card ↥X0
        = Nat.card (∀ ω : ↥S, ↥(Hsub ω)) := hcard
      _ = ∏ ω : ↥S, Nat.card ↥(Hsub ω) := Nat.card_pi
      _ = ∏ _ω : ↥S, p := Finset.prod_congr rfl (fun ω _ => hcard_mem ω)
      _ = p ^ Set.ncard S := by
            rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
              Nat.card_coe_set_eq]
  have hmemEA : ∀ ω : ↥S, IsElemAbelian p (ω : Subgroup A) :=
    fun ω => s16h_isElemAbelian_of_card_eq_prime hp (hcard_mem ω)
  have hcomm_pair : ∀ ω ω' : ↥S, ω ≠ ω' →
      ∀ x y : A, x ∈ (ω : Subgroup A) → y ∈ (ω' : Subgroup A) → x * y = y * x :=
    fun ω ω' hne x y hx hy => (hcommS hne x y hx hy).eq
  have hcomm_same : ∀ ω : ↥S, ∀ x ∈ (ω : Subgroup A), ∀ y ∈ (ω : Subgroup A),
      x * y = y * x := by
    intro ω x hx y hy
    haveI := (hmemEA ω).1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(ω : Subgroup A)) ⟨y, hy⟩)
  have hX0comm : ∀ x ∈ X0, ∀ y ∈ X0, x * y = y * x := by
    intro x hx
    have hx' : x ∈ ⨆ ω : ↥S, (ω : Subgroup A) := hX0eq ▸ hx
    refine Subgroup.iSup_induction (C := fun v => ∀ y ∈ X0, v * y = y * v)
      (fun ω : ↥S => (ω : Subgroup A)) hx' ?_ ?_ ?_
    · intro ω z hzω
      intro y hy
      have hy' : y ∈ ⨆ ω' : ↥S, (ω' : Subgroup A) := hX0eq ▸ hy
      refine Subgroup.iSup_induction (C := fun w => z * w = w * z)
        (fun ω' : ↥S => (ω' : Subgroup A)) hy' ?_ ?_ ?_
      · intro ω' w hwω'
        by_cases hω : ω = ω'
        · subst hω
          exact hcomm_same ω z hzω w hwω'
        · exact hcomm_pair ω ω' hω z w hzω hwω'
      · simp
      · intro a b iha ihb
        rw [← mul_assoc, iha, mul_assoc, ihb, ← mul_assoc]
    · intro y hy
      simp
    · intro a b iha ihb y hy
      rw [mul_assoc, ihb y hy, ← mul_assoc, iha y hy, mul_assoc]
  have hX0exp : ∀ x ∈ X0, x ^ p = 1 := by
    intro x hx
    have hx' : x ∈ ⨆ ω : ↥S, (ω : Subgroup A) := hX0eq ▸ hx
    refine (Subgroup.iSup_induction (C := fun v => v ∈ X0 ∧ v ^ p = 1)
      (fun ω : ↥S => (ω : Subgroup A)) hx' ?_ ?_ ?_).2
    · intro ω v hv
      refine ⟨?_, (hmemEA ω).2 v hv⟩
      rw [hX0eq]
      exact le_iSup (fun ω : ↥S => (ω : Subgroup A)) ω hv
    · exact ⟨X0.one_mem, one_pow p⟩
    · intro a b ha hb
      refine ⟨X0.mul_mem ha.1 hb.1, ?_⟩
      have hc : Commute a b := hX0comm a ha.1 b hb.1
      rw [hc.mul_pow p, ha.2, hb.2, mul_one]
  have hEA0 : IsElemAbelian p X0 :=
    ⟨IsMulCommutative.of_comm
        (fun a b : X0 => Subtype.ext (hX0comm (a : A) a.2 (b : A) b.2)), hX0exp⟩
  have hEA : IsElemAbelian p (X0 ⊓ Hm) :=
    ⟨IsMulCommutative.of_comm
        (fun a b : ↥(X0 ⊓ Hm) =>
          Subtype.ext (hX0comm (a : A) (Subgroup.mem_inf.mp a.2).1 (b : A)
            (Subgroup.mem_inf.mp b.2).1)),
      fun x hx => hX0exp x (Subgroup.mem_inf.mp hx).1⟩
  have hX0Mb : X0 ≤ Mb := by
    rw [hX0eq]
    apply iSup_le
    intro ω
    obtain ⟨q, hq, hqeq⟩ := ω.2
    rw [hqeq]
    rintro x ⟨l, hl, rfl⟩
    show q * l * q⁻¹ ∈ Mb
    exact Mb.mul_mem (Mb.mul_mem hq (hLM hl)) (Mb.inv_mem hq)
  have hX0LbHm : X0 ≤ Lb ⊔ Hm := by
    rw [hX0eq]
    apply iSup_le
    intro ω
    obtain ⟨q, hq, hqeq⟩ := ω.2
    rw [hqeq]
    rintro x ⟨l, hl, rfl⟩
    have hql : ⁅q, l⁆ ∈ Hm := Subgroup.commutator_mem_commutator hq (hLM hl)
    have heq : q * l * q⁻¹ = ⁅q, l⁆ * l := by
      rw [commutatorElement_def]; group
    change q * l * q⁻¹ ∈ Lb ⊔ Hm
    rw [heq]
    exact (Lb ⊔ Hm).mul_mem (Subgroup.mem_sup_right hql) (Subgroup.mem_sup_left hl)
  have hX0norm : ∀ q ∈ Mb, ∀ x ∈ X0, q * x * q⁻¹ ∈ X0 := by
    intro q hq x hx
    have hx' : x ∈ ⨆ ω : ↥S, (ω : Subgroup A) := hX0eq ▸ hx
    refine Subgroup.iSup_induction (C := fun v => q * v * q⁻¹ ∈ X0)
      (fun ω : ↥S => (ω : Subgroup A)) hx' ?_ ?_ ?_
    · intro ω z hzω
      obtain ⟨m, hm, hmeq⟩ := ω.2
      have hzL : z ∈ Lb.map (MulAut.conj m).toMonoidHom := hmeq ▸ hzω
      obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.mp hzL
      have hzmem : q * z * q⁻¹ ∈ Lb.map (MulAut.conj (q * m)).toMonoidHom := by
        have heq : q * z * q⁻¹ = (MulAut.conj (q * m)).toMonoidHom l := by
          rw [← hl_eq]
          change q * MulAut.conj m l * q⁻¹ = MulAut.conj (q * m) l
          rw [MulAut.conj_apply, MulAut.conj_apply]
          group
        rw [heq]
        exact Subgroup.mem_map_of_mem _ hl
      rw [hX0eq]
      exact le_iSup (fun ω : ↥S => (ω : Subgroup A))
        ⟨Lb.map (MulAut.conj (q * m)).toMonoidHom, q * m, Mb.mul_mem hq hm, rfl⟩ hzmem
    · simpa using X0.one_mem
    · intro a b iha ihb
      rw [show q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) from by group]
      exact X0.mul_mem iha ihb
  have hHmMb : Hm ≤ Mb := Subgroup.commutator_le_self Mb
  have hHmNorm : Mb ≤ Subgroup.normalizer (Hm : Set A) :=
    Subgroup.normalizer_commutator_ge_left Mb Mb
  let N : Subgroup Mb := Hm.subgroupOf Mb
  have hN : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHmMb).mpr hHmNorm
  haveI : N.Normal := hN
  let π : Mb →* Mb ⧸ N := QuotientGroup.mk' N
  let g : X0 →* Mb ⧸ N := π.comp (Subgroup.inclusion hX0Mb)
  let πL : Lb →* Mb ⧸ N := π.comp (Subgroup.inclusion hLM)
  have hkercard : Nat.card ↥g.ker = Nat.card ↥(X0 ⊓ Hm) := by
    have hmap : (g.ker).map X0.subtype = X0 ⊓ Hm := by
      ext y
      constructor
      · rintro ⟨x, hxker, rfl⟩
        refine ⟨x.2, ?_⟩
        have hx1 : ((⟨(x : A), hX0Mb x.2⟩ : Mb) : Mb ⧸ N) = 1 :=
          MonoidHom.mem_ker.mp hxker
        exact Subgroup.mem_subgroupOf.mp
          ((QuotientGroup.eq_one_iff (⟨(x : A), hX0Mb x.2⟩ : Mb)).mp hx1)
      · rintro ⟨hy0, hyHm⟩
        refine ⟨⟨y, hy0⟩, ?_, rfl⟩
        exact MonoidHom.mem_ker.mpr
          ((QuotientGroup.eq_one_iff (⟨y, hX0Mb hy0⟩ : Mb)).mpr
            (Subgroup.mem_subgroupOf.mpr hyHm))
    rw [← hmap, Subgroup.card_map_of_injective X0.subtype_injective]
  have hsub_le : (Lb ⊔ Hm).subgroupOf Mb ≤ Lb.subgroupOf Mb ⊔ N := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    have hzmap : (z : A) ∈ (Lb.subgroupOf Mb ⊔ N).map Mb.subtype := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLM,
        Subgroup.map_subgroupOf_eq_of_le hHmMb]
      exact hz
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hzmap
    rwa [← Subtype.ext hkz]
  have hg_le : g.range ≤ πL.range := by
    have hgr : g.range = (X0.subgroupOf Mb).map π := by
      rw [show g = π.comp (Subgroup.inclusion hX0Mb) from rfl, MonoidHom.range_comp,
        Subgroup.inclusion_range]
    have hpr : πL.range = (Lb.subgroupOf Mb).map π := by
      rw [show πL = π.comp (Subgroup.inclusion hLM) from rfl, MonoidHom.range_comp,
        Subgroup.inclusion_range]
    rw [hgr, hpr, Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq,
      show π.ker = N from QuotientGroup.ker_mk' N]
    intro z hz
    exact hsub_le (Subgroup.mem_subgroupOf.mpr
      (hX0LbHm (Subgroup.mem_subgroupOf.mp hz)))
  have hcardπL : Nat.card ↥πL.range ≤ p := by
    have h := Subgroup.card_ker_mul_card_range πL
    rw [hLb] at h
    have hdvd : Nat.card ↥πL.range ∣ p := ⟨Nat.card ↥πL.ker, by rw [mul_comm, ← h]⟩
    exact Nat.le_of_dvd hp.pos hdvd
  have hrange_le : Nat.card ↥g.range ≤ p :=
    le_trans (Subgroup.card_le_of_le hg_le) hcardπL
  have hbound : Nat.card ↥X0 ≤ p * Nat.card ↥(X0 ⊓ Hm) := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hkercard] at h
    rw [← h]
    calc Nat.card ↥(X0 ⊓ Hm) * Nat.card ↥g.range
        ≤ Nat.card ↥(X0 ⊓ Hm) * p := Nat.mul_le_mul_left _ hrange_le
      _ = p * Nat.card ↥(X0 ⊓ Hm) := by rw [mul_comm]
  have hXP : IsPGroup p ↥(X0 ⊓ Hm) := by
    intro y
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have h := hEA.2 (y : A) y.2
    simpa using h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := ↥(X0 ⊓ Hm))).mp hXP
  have hs_bound : Set.ncard S - 1 ≤ n := by
    have h2 : Set.ncard S ≤ n + 1 := by
      have h1 : p ^ Set.ncard S ≤ p * p ^ n := by
        rw [← hcardX0, ← hn]
        exact hbound
      have h1' : p ^ Set.ncard S ≤ p ^ (n + 1) := by
        rw [pow_succ']; exact h1
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1'
    exact Nat.sub_le_iff_le_add.mpr h2
  refine ⟨X0 ⊓ Hm, n, inf_le_right, ?_, hEA, hn, hs_bound⟩
  intro q hq x hx
  refine ⟨hX0norm q hq x hx.1, ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hHmNorm hq) x).mp hx.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
