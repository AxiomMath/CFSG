module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsRank
public import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.Ch3E213M.P3

open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts Subgroup

section PGammaL

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem inl_left_eq (hp : p.Prime) (hF : Nat.card F = p) (g : PGammaL2 F) :
    SemidirectProduct.inl g.left = g := by
  have h1 : Nat.card (F ≃+* F) = 1 := card_ringAut F hp (by rw [hF, pow_one])
  have : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact SemidirectProduct.ext (SemidirectProduct.left_inl _) (Subsingleton.elim _ _)

theorem isKleinFour_of_card {P : Type*} [Group P] [Finite P] (h4 : Nat.card P = 4)
    (h2 : ∀ w : P, w * w = 1) : IsKleinFour P := by
  have : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, h4]
    norm_num
  refine ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun w hw => ?_⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h2 w) hw

theorem centralizer_eq_self
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p) {W : Subgroup (PGammaL2 F)}
    (hW4 : Nat.card W = 4) (hW : ∀ w ∈ W, w * w = 1) :
    centralizer (W : Set (PGammaL2 F)) = W := by
  have hinl : Function.Injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) :=
    SemidirectProduct.inl_injective
  set V := W.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) with hV
  have hVW : V.map SemidirectProduct.inl = W := by
    ext g
    refine ⟨?_, fun hg => ⟨g.left, ?_, inl_left_eq hp hF g⟩⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · show SemidirectProduct.inl g.left ∈ W
      rw [inl_left_eq hp hF g]
      exact hg
  have hV4 : Nat.card V = 4 := by
    rw [← hW4, ← hVW, card_map_of_injective hinl]
  have hVK : IsKleinFour V := isKleinFour_of_card hV4 fun v => by
    apply Subtype.ext
    apply hinl
    rw [OneMemClass.coe_one, map_one, MulMemClass.coe_mul, map_mul]
    exact hW _ v.2
  have hC := pgl2_kleinFour_centralizer_eq_self F
    (isOddPrimePower_of hp hp2 le_rfl (by rw [hF, pow_one])) V hVK
  refine le_antisymm (fun g hg => ?_) fun w hw => mem_centralizer_iff.mpr fun v hv =>
    commute_of_forall_sq W hW hv hw
  have hgV : g.left ∈ centralizer (V : Set (PGL2 F)) := by
    rw [mem_centralizer_iff]
    intro v hv
    apply hinl
    rw [map_mul, map_mul, inl_left_eq hp hF g]
    exact mem_centralizer_iff.mp hg _ hv
  rw [hC] at hgV
  rw [← inl_left_eq hp hF g]
  exact hgV

end PGammaL

theorem card_le_eight_of_le_normalizer {P : Type*} [Group P] [Finite P] {W S : Subgroup P}
    (hW4 : Nat.card W = 4) (hW : ∀ w ∈ W, w * w = 1) (hC : centralizer (W : Set P) ≤ W)
    (hS : IsPGroup 2 S) (hSW : S ≤ normalizer (W : Set P)) : Nat.card S ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsKleinFour W := isKleinFour_of_card hW4 fun w => Subtype.ext (hW w w.2)
  set f : S →* MulAut W := W.normalizerMonoidHom.comp (inclusion hSW) with hf
  have hker : Nat.card f.ker ≤ 4 := by
    rw [← hW4]
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : S) : P), hC ?_⟩) fun x y hxy =>
      Subtype.ext (Subtype.ext (Subtype.ext_iff.mp hxy :))
    have h1 : inclusion hSW (x : S) ∈ W.normalizerMonoidHom.ker := x.2
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at h1
    exact h1
  have hrange : Nat.card f.range ≤ 2 := by
    have h6 : Nat.card f.range ∣ 6 := kleinFourAut_card W ▸ card_subgroup_dvd_card _
    obtain ⟨k, hk⟩ := (hS.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
    rw [hk] at h6 ⊢
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> norm_num
    · exact absurd ((Nat.pow_dvd_pow 2 h).trans h6) (by norm_num)
  calc Nat.card S = Nat.card f.ker * Nat.card f.range := (card_ker_mul_card_range f).symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hker hrange
    _ = 8 := by norm_num

theorem eight_dvd_card {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hF : Nat.card F = p) : 8 ∣ Nat.card (PSL2 F) := by
  have hp2 : p ≠ 2 := by omega
  rw [psl2_card_formula F (isOddPrimePower_of hp hp2 le_rfl (by rw [hF, pow_one])), hF]
  obtain ⟨m, hm⟩ : 16 ∣ p ^ 2 - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + p % 8 := ⟨p / 8, (Nat.div_add_mod p 8).symm⟩
    rcases hp8 with h | h
    · refine ⟨4 * k ^ 2 + k, Nat.sub_eq_of_eq_add ?_⟩
      rw [hk, h]
      ring
    · refine ⟨4 * k ^ 2 + 7 * k + 3, Nat.sub_eq_of_eq_add ?_⟩
      rw [hk, h]
      ring
  rw [hm, show p * (16 * m) = 2 * (8 * (p * m)) by ring, Nat.mul_div_cancel_left _ two_pos]
  exact Dvd.intro _ rfl

section Act

variable {Y : Type} [Group Y] {F : Type} [Field F] [Finite F] {K : Subgroup Y}

@[expose] noncomputable def act (θ : K ≃* PSL2 F) : normalizer (K : Set Y) →* PGammaL2 F :=
  (autEquiv θ).toMonoidHom.comp K.normalizerMonoidHom

theorem act_ker (θ : K ≃* PSL2 F) :
    (act θ).ker = (centralizer (K : Set Y)).subgroupOf (normalizer (K : Set Y)) := by
  rw [← normalizerMonoidHom_ker]
  ext x
  simp only [MonoidHom.mem_ker, act, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

@[expose] noncomputable def autSub (θ : K ≃* PSL2 F) (X : Subgroup Y) : Subgroup (PGammaL2 F) :=
  (X.subgroupOf (normalizer (K : Set Y))).map (act θ)

theorem card_autSub [Finite Y] (θ : K ≃* PSL2 F) (X : Subgroup Y) :
    Nat.card (autSub θ X) = E2.autCard X K := by
  set N := normalizer (K : Set Y)
  set C := centralizer (K : Set Y)
  have h1 : (act θ).ker.relIndex (X.subgroupOf N) = Nat.card (autSub θ X) := relIndex_ker _ _
  rw [← h1, act_ker, E2.autCard, ← inf_subgroupOf_right X N, relIndex_subgroupOf inf_le_right,
    inf_comm (X ⊓ N) C, inf_relIndex_right]

end Act

end CFSG.Quasithin.Ch3E213M.P3
