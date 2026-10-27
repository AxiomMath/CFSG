module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.GGSFCore

open CFSG.Open

open scoped IsMulCommutative

variable {A : Type*} [Group A] {p : ℕ}

theorem isElemAbelian_isPGroup {E : Subgroup A} (hE : IsElemAbelian p E) : IsPGroup p E := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hE.2 (g : A) g.2

theorem exists_card_eq_pow [Finite A] [Fact p.Prime] {E : Subgroup A} (hE : IsElemAbelian p E) :
    ∃ k : ℕ, Nat.card E = p ^ k :=
  (isElemAbelian_isPGroup hE).exists_card_eq

theorem isElemAbelian_of_le {E X : Subgroup A} (hE : IsElemAbelian p E) (hXE : X ≤ E) :
    IsElemAbelian p X := by
  refine ⟨?_, fun x hx => hE.2 x (hXE hx)⟩
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  simpa using hE.1.is_comm.comm ⟨(a : A), hXE a.2⟩ ⟨(b : A), hXE b.2⟩

theorem isElemAbelian_map_conj {E : Subgroup A} (hE : IsElemAbelian p E) (g : A) :
    IsElemAbelian p (E.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, fun x hx => ?_⟩
  · haveI := hE.1
    infer_instance
  · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 y hy, map_one]

theorem card_map_conj (E : Subgroup A) (g : A) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E := by
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective E (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm

theorem exists_two_subgroups [Finite A] [Fact p.Prime] {E₀ : Subgroup A}
    (hE₀ : IsElemAbelian p E₀) {r s : ℕ} (hr : Nat.card E₀ = p ^ r) (hs : 1 ≤ s) (hsr : s < r) :
    ∃ X Y : Subgroup A, X ≤ E₀ ∧ Y ≤ E₀ ∧ Nat.card X = p ^ s ∧ Nat.card Y = p ^ s ∧ X ≠ Y := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  haveI hcomm : IsMulCommutative E₀ := hE₀.1
  have hE0p : IsPGroup p E₀ := isElemAbelian_isPGroup hE₀
  have hle : p ^ s ≤ Nat.card E₀ := by
    rw [hr]
    exact Nat.pow_le_pow_right hp.pos (Nat.le_of_lt hsr)
  obtain ⟨X₁, hX₁card⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hE0p hle
  have hle' : p ^ (s - 1) ≤ Nat.card X₁ := by
    rw [hX₁card]
    exact Nat.pow_le_pow_right hp.pos (Nat.pred_le s)
  obtain ⟨X', hX'le, hX'card⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card hp hE0p (H := X₁) (n := s - 1) hle'
  have hX₁ne : X₁ ≠ ⊤ := by
    intro htop
    have hcard := hX₁card
    rw [htop, Subgroup.card_top, hr] at hcard
    have : s = r := Nat.pow_right_injective hp2 hcard.symm
    omega
  obtain ⟨x, hxX₁⟩ : ∃ x : E₀, x ∉ X₁ := by
    by_contra h
    rw [not_exists] at h
    exact hX₁ne (le_antisymm le_top fun y _ => not_not.mp (h y))
  have hx1 : x ≠ 1 := fun hx1 => hxX₁ (hx1 ▸ X₁.one_mem)
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    simpa using hE₀.2 (x : A) x.2
  have horder : orderOf x = p := orderOf_eq_prime hxp hx1
  haveI : Fact (Nat.card (Subgroup.zpowers x)).Prime :=
    ⟨by rw [Nat.card_zpowers, horder]; exact hp⟩
  have hbot : X' ⊓ Subgroup.zpowers x = ⊥ := by
    rcases (X'.subgroupOf (Subgroup.zpowers x)).eq_bot_or_eq_top_of_prime_card with h | h
    · exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
    · exact absurd (hX'le ((Subgroup.subgroupOf_eq_top.mp h) (Subgroup.mem_zpowers x))) hxX₁
  let Y' : Subgroup E₀ := X' ⊔ Subgroup.zpowers x
  have hxY' : x ∈ Y' :=
    Subgroup.mem_sup.mpr ⟨1, X'.one_mem, x, Subgroup.mem_zpowers x, one_mul x⟩
  have hY'card : Nat.card Y' = p ^ s := by
    let f : X' × Subgroup.zpowers x → Y' := fun ab =>
      ⟨(ab.1 : E₀) * (ab.2 : E₀),
        Subgroup.mem_sup.mpr ⟨ab.1, ab.1.2, ab.2, ab.2.2, rfl⟩⟩
    have hinj : Function.Injective f := by
      rintro ⟨a, b⟩ ⟨c, d⟩ hab
      have h' : (a : E₀) * (b : E₀) = (c : E₀) * (d : E₀) := congrArg Subtype.val hab
      have h1 : (c : E₀)⁻¹ * (a : E₀) = (d : E₀) * (b : E₀)⁻¹ := by
        have h2 := congrArg (fun t => (c : E₀)⁻¹ * t * (b : E₀)⁻¹) h'
        simpa [mul_assoc] using h2
      have hmem : (c : E₀)⁻¹ * (a : E₀) ∈ X' ⊓ Subgroup.zpowers x := by
        refine ⟨X'.mul_mem (X'.inv_mem c.2) a.2, ?_⟩
        rw [h1]
        exact (Subgroup.zpowers x).mul_mem d.2 ((Subgroup.zpowers x).inv_mem b.2)
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hb : (b : E₀) = (d : E₀) := by
        have h2 := h'
        rw [hmem] at h2
        exact mul_left_cancel h2
      exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)
    have hsurj : Function.Surjective f := by
      rintro ⟨y, hy⟩
      rw [Subgroup.mem_sup] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
    rw [Nat.card_prod, hX'card, Nat.card_zpowers, horder, ← pow_succ,
      Nat.sub_add_cancel hs] at hcard
    exact hcard.symm
  refine ⟨X₁.map E₀.subtype, Y'.map E₀.subtype, Subgroup.map_subtype_le X₁,
    Subgroup.map_subtype_le Y', ?_, ?_, ?_⟩
  · rw [← hX₁card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective X₁ E₀.subtype
      E₀.subtype_injective).toEquiv).symm
  · rw [← hY'card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective Y' E₀.subtype
      E₀.subtype_injective).toEquiv).symm
  · intro heq
    have hxY : (x : A) ∈ Y'.map E₀.subtype := Subgroup.mem_map.mpr ⟨x, hxY', rfl⟩
    have hxX : (x : A) ∈ X₁.map E₀.subtype := heq ▸ hxY
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxX
    exact hxX₁ (Subtype.ext hyx ▸ hy)

theorem exists_conj_le_sylow_of_normal [Finite A] [Fact p.Prime] {Inn N : Subgroup A}
    [Inn.Normal] (hN : Inn ≤ N) (P : Sylow p N) {Q : Subgroup A} (hQ : Q ≤ Inn)
    (hQp : IsPGroup p Q) :
    ∃ g ∈ Inn, Q.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup N).map N.subtype := by
  haveI hFinN : Finite N := inferInstance
  haveI hFinInn : Finite Inn := inferInstance
  haveI hSylN : Finite (Sylow p N) := Sylow.finite_of_finiteIndex P
  let Qsub : Subgroup Inn := Q.subgroupOf Inn
  have hQsubp : IsPGroup p Qsub := hQp.comap_subtype (K := Inn)
  obtain ⟨R, hQR⟩ := hQsubp.exists_le_sylow
  haveI hSylInn : Finite (Sylow p Inn) := Sylow.finite_of_finiteIndex R
  let RA : Subgroup A := (R : Subgroup Inn).map Inn.subtype
  have hRAp : IsPGroup p RA := R.isPGroup'.map Inn.subtype
  have hRAN : RA ≤ N := (Subgroup.map_subtype_le R).trans hN
  let RAN : Subgroup N := RA.subgroupOf N
  have hRANp : IsPGroup p RAN := hRAp.comap_subtype (K := N)
  obtain ⟨S, hSR⟩ := hRANp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq N S P
  let R' : Sylow p Inn := R.mapSurjective (f := (MulAut.conjNormal (k : A)).toMonoidHom)
    (MulAut.conjNormal (k : A)).surjective
  have hR'coe : (R' : Subgroup Inn) =
      (R : Subgroup Inn).map (MulAut.conjNormal (k : A)).toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq Inn R R'
  refine ⟨(h : A), h.2, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  have hqsubR : (⟨q, hQ hq⟩ : Inn) ∈ R :=
    hQR (Subgroup.mem_subgroupOf.mpr hq)
  have hconjR' : (MulAut.conj h) (⟨q, hQ hq⟩ : Inn) ∈ (R' : Subgroup Inn) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ (R : Subgroup Inn) hqsubR
  rw [hR'coe] at hconjR'
  obtain ⟨r, hrR, hrEq⟩ := Subgroup.mem_map.mp hconjR'
  have hrEqA : ((MulAut.conjNormal (k : A)) r : A) = (h : A) * q * (h : A)⁻¹ := by
    have := congrArg Subtype.val hrEq
    simpa [MulAut.conj_apply] using this
  change (MulAut.conj (h : A)) q ∈ (P : Subgroup N).map N.subtype
  rw [MulAut.conj_apply, ← hrEqA]
  have hrRAN : (⟨(r : A), hN r.2⟩ : N) ∈ RAN :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩)
  have hPmem : (MulAut.conj k) (⟨(r : A), hN r.2⟩ : N) ∈ (P : Subgroup N) := by
    rw [← hk, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ (S : Subgroup N) (hSR hrRAN)
  have hval : ((MulAut.conj k) (⟨(r : A), hN r.2⟩ : N) : A) =
      ((MulAut.conjNormal (k : A)) r : A) := by
    simp [MulAut.conj_apply, MulAut.conjNormal_apply]
  exact Subgroup.mem_map.mpr ⟨_, hPmem, hval⟩

end CFSG.StandardType.GGSFCore
