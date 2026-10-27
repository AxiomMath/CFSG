module

public import CFSG.Permutation.UnitaryThreeRecognition.HeisMap

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open scoped commutatorElement

namespace Hyp

variable {G : Type*} [Group G] [Finite G] {Q T Z W : Subgroup G} {p f d : ℕ} [Fact p.Prime]
  (S : Hyp Q T Z W p f d)
include S

omit [Finite G] in
theorem two_ne_zero_zmod : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := (Fact.out : p.Prime).two_le
  exact S.hpodd (by omega)

omit [Finite G] in
theorem eq_zero_of_eq_neg {x : S.V} (h : x = -x) : x = 0 := by
  have h2 : (2 : ZMod p) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  exact (smul_eq_zero.mp h2).resolve_left S.two_ne_zero_zmod

theorem frob_frob (c : S.A) : (c ^ p ^ f) ^ p ^ f = c := by
  have := S.charP_A
  have h := iterateFrobenius_iterateFrobenius S.card_A c
  rwa [iterateFrobenius_def, iterateFrobenius_def] at h

theorem two_ne_zero_A : (2 : S.A) ≠ 0 := by
  have := S.charP_A
  exact Ring.two_ne_zero (by rw [ringChar.eq S.A p]; exact S.hpodd)

theorem frob_half (c : S.A) :
    ((c - c ^ p ^ f) / 2) ^ p ^ f = -((c - c ^ p ^ f) / 2) := by
  have := S.charP_A
  rw [← iterateFrobenius_def (p := p), map_div₀, map_sub, map_ofNat, iterateFrobenius_def,
    iterateFrobenius_def, S.frob_frob, ← neg_div, neg_sub]

theorem beta_one_frob (c : S.A) : S.beta 1 (c ^ p ^ f) = -S.beta 1 c := by
  have h1 := S.beta_eq c 1
  rw [mul_one] at h1
  rw [← h1, form_antisymm S.beta S.beta_self c 1]

theorem beta_one_half (c : S.A) : S.beta 1 c = S.beta 1 ((c - c ^ p ^ f) / 2) := by
  have := S.charP_A
  set e := (c + c ^ p ^ f) / 2 with he
  have he' : e ^ p ^ f = e := by
    rw [he, ← iterateFrobenius_def (p := p), map_div₀, map_add, map_ofNat, iterateFrobenius_def,
      iterateFrobenius_def, S.frob_frob, add_comm]
  have hMe : S.beta 1 e = 0 := S.eq_zero_of_eq_neg (by rw [← S.beta_one_frob, he'])
  have hc : c = (c - c ^ p ^ f) / 2 + e := by
    rw [he]
    field_simp [S.two_ne_zero_A]
    ring
  conv_lhs => rw [hc]
  rw [map_add, hMe, add_zero]

@[expose] noncomputable def coordA (u : S.V) : S.A := S.iota.symm (S.piV u)

theorem bracket_eq_beta (u v : S.V) : Baer.bracket u v = S.beta (S.coordA u) (S.coordA v) := by
  rw [S.bracket_proj, beta_apply, coordA, coordA, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

theorem exists_beta_one_ne_zero : ∃ c, S.beta 1 c ≠ 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := S.hnonab
  by_contra h
  push Not at h
  apply hxy
  have h1 : Baer.bracket (Baer.toB S.isBaer ⟨x, hx⟩) (Baer.toB S.isBaer ⟨y, hy⟩) = 0 := by
    rw [S.bracket_eq_beta, S.beta_eq, h]
  rw [Baer.bracket_apply, Baer.ofB_toB, Baer.ofB_toB] at h1
  have h3 := commutatorElement_eq_one_iff_mul_comm.mp (Baer.toB_eq_zero.mp h1)
  exact congrArg Subtype.val h3

abbrev Aminus : Type _ := {c : S.A // c ^ p ^ f = -c}

@[expose] noncomputable def L (e : S.Aminus) : S.Zs := ⟨S.beta 1 e, S.beta_mem_Zs 1 e⟩

theorem exists_beta_one_eq (z : S.Zs) : ∃ c, S.beta 1 c = z := by
  obtain ⟨c₁, hc₁⟩ := S.exists_beta_one_ne_zero
  by_cases hz : (z : S.V) = 0
  · exact ⟨0, by rw [map_zero, hz]⟩
  have hz1 : ((Baer.ofB (z : S.V) : Q) : G) ≠ 1 := fun h =>
    hz (Baer.eq_zero_iff_ofB_eq_one.mpr (Subtype.ext h))
  have hc1 : ((Baer.ofB (S.beta 1 c₁) : Q) : G) ≠ 1 := fun h =>
    hc₁ (Baer.eq_zero_iff_ofB_eq_one.mpr (Subtype.ext h))
  obtain ⟨t, ht, htz⟩ := S.hTZtrans _ (S.beta_mem_Zs 1 c₁) _ z.2 hc1 hz1
  have key : S.rho ⟨t, ht⟩ (S.beta 1 c₁) =
      S.beta 1 ((S.tau ⟨t, ht⟩ : S.A) ^ p ^ f * ((S.tau ⟨t, ht⟩ : S.A) * c₁)) := by
    rw [S.rho_beta, S.beta_eq, mul_one]
  refine ⟨_, key.symm.trans ?_⟩
  apply S.rho_ext
  rw [coe_ofB_rho]
  exact htz

theorem L_surjective : Function.Surjective S.L := by
  intro z
  obtain ⟨c, hc⟩ := S.exists_beta_one_eq z
  refine ⟨⟨(c - c ^ p ^ f) / 2, S.frob_half c⟩, Subtype.ext ?_⟩
  change S.beta 1 ((c - c ^ p ^ f) / 2) = z
  rw [← S.beta_one_half, hc]

theorem card_Aminus_le : Nat.card S.Aminus ≤ p ^ f := by
  have h := card_pow_eq_mul_le (p ^ f) (by have := S.three_le_q; omega) (-1 : S.A)
  rwa [Nat.card_congr (Equiv.subtypeEquivRight (fun c => by rw [neg_one_mul]))] at h

theorem L_bijective : Function.Bijective S.L :=
  S.L_surjective.bijective_of_nat_card_le (by rw [S.card_Zs]; exact S.card_Aminus_le)

theorem eq_of_beta_one {e e' : S.A} (he : e ^ p ^ f = -e) (he' : e' ^ p ^ f = -e')
    (h : S.beta 1 e = S.beta 1 e') : e = e' :=
  congrArg Subtype.val (S.L_bijective.1 (Subtype.ext h : S.L ⟨e, he⟩ = S.L ⟨e', he'⟩))

@[expose] noncomputable def LinvFun (z : S.Zs) : S.A :=
  ((Equiv.ofBijective S.L S.L_bijective).symm z : S.Aminus)

theorem beta_LinvFun (z : S.Zs) : S.beta 1 (S.LinvFun z) = z :=
  congrArg Subtype.val ((Equiv.ofBijective S.L S.L_bijective).apply_symm_apply z)

theorem LinvFun_frob (z : S.Zs) : S.LinvFun z ^ p ^ f = -S.LinvFun z :=
  ((Equiv.ofBijective S.L S.L_bijective).symm z).2

theorem LinvFun_eq {e : S.A} (he : e ^ p ^ f = -e) {z : S.Zs} (h : S.beta 1 e = z) :
    S.LinvFun z = e :=
  S.eq_of_beta_one (S.LinvFun_frob z) he (by rw [S.beta_LinvFun, h])

theorem frob_add (e e' : S.A) : (e + e') ^ p ^ f = e ^ p ^ f + e' ^ p ^ f := by
  have := S.charP_A
  rw [← iterateFrobenius_def (p := p), map_add, iterateFrobenius_def, iterateFrobenius_def]

@[expose] noncomputable def Linv : S.Zs →+ S.A :=
  AddMonoidHom.mk' S.LinvFun fun z z' => S.LinvFun_eq
    (by rw [S.frob_add, S.LinvFun_frob, S.LinvFun_frob, neg_add])
    (by rw [map_add, S.beta_LinvFun, S.beta_LinvFun]; rfl)

theorem Linv_apply (z : S.Zs) : S.Linv z = S.LinvFun z := rfl

theorem beta_Linv (z : S.Zs) : S.beta 1 (S.Linv z) = z := S.beta_LinvFun z

theorem Linv_frob (z : S.Zs) : S.Linv z ^ p ^ f = -S.Linv z := S.LinvFun_frob z

theorem Linv_eq {e : S.A} (he : e ^ p ^ f = -e) {z : S.Zs} (h : S.beta 1 e = z) :
    S.Linv z = e := S.LinvFun_eq he h

theorem Linv_injective : Function.Injective S.Linv := by
  intro z z' h
  apply Subtype.ext
  rw [← S.beta_Linv z, ← S.beta_Linv z', h]

theorem Linv_bracket (u v : S.V) :
    S.Linv ⟨Baer.bracket u v, S.bracket_mem_Zs u v⟩ =
      (S.coordA u ^ p ^ f * S.coordA v - S.coordA u * S.coordA v ^ p ^ f) / 2 := by
  have := S.charP_A
  have hfr : (S.coordA u ^ p ^ f * S.coordA v) ^ p ^ f = S.coordA u * S.coordA v ^ p ^ f := by
    rw [mul_pow, S.frob_frob]
  apply S.Linv_eq
  · have := S.frob_half (S.coordA u ^ p ^ f * S.coordA v)
    rwa [hfr] at this
  · change _ = Baer.bracket u v
    rw [S.bracket_eq_beta, S.beta_eq (S.coordA u),
      S.beta_one_half (S.coordA u ^ p ^ f * S.coordA v), hfr]

theorem rho_beta_one (t : T) (c : S.A) :
    S.rho t (S.beta 1 c) = S.beta (S.tau t : S.A) ((S.tau t : S.A) * c) := by
  rw [S.rho_beta, mul_one]

theorem Linv_rho (t : T) (z : S.Zs) :
    S.Linv ⟨S.rho t z, S.rho_mem_Zs t z.2⟩ =
      (S.tau t : S.A) ^ p ^ f * (S.tau t : S.A) * S.Linv z := by
  apply S.Linv_eq
  · rw [mul_pow, mul_pow, S.frob_frob, S.Linv_frob]
    ring
  · rw [mul_assoc, ← S.beta_eq, ← S.rho_beta_one, S.beta_Linv]

end Hyp

end CFSG.UnitaryThreeRecognition.Heisenberg
