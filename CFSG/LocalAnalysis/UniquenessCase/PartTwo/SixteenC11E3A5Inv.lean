module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Split
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightFix
public import CFSG.Quasithin.Background.RonanF918A6
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Module

variable {W : Type} [CommGroup W]

private lemma s1611e3_isIrrOn_iff (A : Subgroup (MulAut W)) (J : Subgroup W) :
    IsIrrOn A J ⊥ ↔ XMod.IsIrr ↥A J := by
  unfold IsIrrOn XMod.IsIrr XMod.IsIrrSec XMod.IsInv StableUnder
  constructor
  · rintro ⟨hlt, hstab, -, hmin⟩
    exact ⟨fun a j hj => hstab a a.2 j hj, hlt,
      fun J' hJ' _ hJ'J => hmin J' (fun a ha u hu => hJ' ⟨a, ha⟩ u hu) bot_le hJ'J⟩
  · rintro ⟨hinv, hlt, hmin⟩
    exact ⟨hlt, (fun a ha u hu => hinv ⟨a, ha⟩ u hu),
      (fun a _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]),
      fun J' hJ' _ hJ'J => hmin J' (fun a u hu => hJ' (a : MulAut W) a.2 u hu) bot_le hJ'J⟩

private theorem s1611e3_sumOfNat_two
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    {U : Subgroup W} (h : SumOfNat N H U ⊥ 2) :
    ∃ J₀ J₁ : Subgroup W, N H J₀ ⊥ ∧ N H J₁ ⊥ ∧ J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = U := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have hrest : ∀ i j : Fin 2, i ≠ j → (⨆ (k : Fin 2) (_ : k ≠ i), I k) = I j := by
    intro i j hij
    refine le_antisymm (iSup₂_le fun k hk => ?_)
      (le_iSup₂ (f := fun k (_ : k ≠ i) => I k) j (Ne.symm hij))
    have : k = j := by omega
    rw [this]
  refine ⟨I 0, I 1, hnat 0, hnat 1, ?_, ?_⟩
  · have h0 := hind 0
    rw [hrest 0 1 (by decide), bot_sup_eq] at h0
    exact le_bot_iff.1 h0
  · have hall : (⨆ i, I i) = I 0 ⊔ I 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [hall, bot_sup_eq] at hsup
    exact hsup

private theorem s1611e3_alt_map_of_norm {L : Subgroup (MulAut W)} {J : Subgroup W}
    {x : MulAut W} (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hx' : ∀ l ∈ L, x⁻¹ * l * x ∈ L)
    (h : AlternatingNatural L J ⊥ 5) :
    AlternatingNatural L (J.map x.toMonoidHom) ⊥ 5 := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨(CFSG.Quasithin.RonanF918.conjSubHom L x hx).comp π, by
    simpa [Subgroup.map_bot] using
      CFSG.Quasithin.RonanF918.realizesVia_map_conj hπ x hx hx'⟩

private theorem s1611e3_isIrr_of_nat [Finite W] {L : Subgroup (MulAut W)} {U J : Subgroup W}
    (hUfix : U ⊓ fixV L = ⊥) (hJU : J ≤ U) (hJ : AlternatingNatural L J ⊥ 5) :
    XMod.IsIrr ↥L J := by
  have hmem : J ∈ irrSet L := s16c167_mem_irrSet_alt (n := 5) (by norm_num) hJ
  have hfixJ : J ⊓ fixV L = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have hxU : x ∈ U := hJU (Subgroup.mem_inf.1 hx).1
    have : x ∈ U ⊓ fixV L := ⟨hxU, (Subgroup.mem_inf.1 hx).2⟩
    rwa [hUfix] at this
  have h2 := hmem.2
  rw [hfixJ] at h2
  exact (s1611e3_isIrrOn_iff L J).1 h2

private def s1611e3_idx [DecidableEq (Subgroup W)] (J₀ J₁ J : Subgroup W) : Fin 3 :=
  if J = J₀ then 0 else if J = J₁ then 1 else 2

private lemma s1611e3_idx_eq_zero [DecidableEq (Subgroup W)] {J₀ J₁ J : Subgroup W}
    (h : J₀ ≠ J₁) : s1611e3_idx J₀ J₁ J = 0 ↔ J = J₀ := by
  unfold s1611e3_idx
  split_ifs with h0 h1
  · exact iff_of_true rfl h0
  · exact iff_of_false (by decide) h0
  · exact iff_of_false (by decide) h0

private lemma s1611e3_idx_eq_one [DecidableEq (Subgroup W)] {J₀ J₁ J : Subgroup W}
    (h : J₀ ≠ J₁) : s1611e3_idx J₀ J₁ J = 1 ↔ J = J₁ := by
  unfold s1611e3_idx
  split_ifs with h0 h1
  · exact iff_of_false (by decide) (fun hI => h (h0.symm.trans hI))
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1

private lemma s1611e3_idx_eq_two [DecidableEq (Subgroup W)] {J₀ J₁ J : Subgroup W} :
    s1611e3_idx J₀ J₁ J = 2 ↔ J ≠ J₀ ∧ J ≠ J₁ := by
  unfold s1611e3_idx
  split_ifs with h0 h1
  · exact iff_of_false (by decide) (fun hc => hc.1 h0)
  · exact iff_of_false (by decide) (fun hc => hc.2 h1)
  · exact iff_of_true rfl ⟨h0, h1⟩

private theorem s1611e3_natSub_card_le_three [Finite W] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (hUfix : U ⊓ fixV L = ⊥)
    {J₀ J₁ : Subgroup W} (hJ₀U : J₀ ≤ U) (hJ₁U : J₁ ≤ U)
    (hJ₀ : AlternatingNatural L J₀ ⊥ 5) (hJ₁ : AlternatingNatural L J₁ ⊥ 5)
    (hE : Z391.EndUnitsTrivial L J₀) (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = U) :
    Nat.card ↥{J : Subgroup W | J ≤ U ∧ AlternatingNatural L J ⊥ 5} ≤ 3 := by
  classical
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite ↥{J : Subgroup W | J ≤ U ∧ AlternatingNatural L J ⊥ 5} :=
    Finite.of_injective _ Subtype.coe_injective
  have hJ₀ne : J₀ ≠ ⊥ := by
    have hmem : J₀ ∈ irrSet L := s16c167_mem_irrSet_alt (n := 5) (by norm_num) hJ₀
    intro h0
    have hlt := hmem.2.1
    rw [h0, bot_inf_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  have hJ01 : J₀ ≠ J₁ := by
    intro h
    have h1 : J₀ ⊓ J₁ = J₀ := by rw [h, inf_idem]
    rw [hinf] at h1
    exact hJ₀ne h1.symm
  have hg_inj : Function.Injective
      (fun J : ↥{J : Subgroup W | J ≤ U ∧ AlternatingNatural L J ⊥ 5} =>
        s1611e3_idx J₀ J₁ (J : Subgroup W)) := by
    intro J J' h
    have hJ := J.2
    have hJ' := J'.2
    have hcases : s1611e3_idx J₀ J₁ (J : Subgroup W) = 0 ∨
        s1611e3_idx J₀ J₁ (J : Subgroup W) = 1 ∨
        s1611e3_idx J₀ J₁ (J : Subgroup W) = 2 := by
      generalize hz : s1611e3_idx J₀ J₁ (J : Subgroup W) = z
      fin_cases z <;> simp_all
    rcases hcases with h0 | h1 | h2
    · have hJ0 : (J : Subgroup W) = J₀ := (s1611e3_idx_eq_zero hJ01).1 h0
      have hJ0' : (J' : Subgroup W) = J₀ := (s1611e3_idx_eq_zero hJ01).1 (h.symm.trans h0)
      exact Subtype.ext (hJ0.trans hJ0'.symm)
    · have hJ1 : (J : Subgroup W) = J₁ := (s1611e3_idx_eq_one hJ01).1 h1
      have hJ1' : (J' : Subgroup W) = J₁ := (s1611e3_idx_eq_one hJ01).1 (h.symm.trans h1)
      exact Subtype.ext (hJ1.trans hJ1'.symm)
    · have hJn : (J : Subgroup W) ≠ J₀ ∧ (J : Subgroup W) ≠ J₁ := (s1611e3_idx_eq_two).1 h2
      have hJn' : (J' : Subgroup W) ≠ J₀ ∧ (J' : Subgroup W) ≠ J₁ :=
        (s1611e3_idx_eq_two).1 (h.symm.trans h2)
      have hle : (J : Subgroup W) ≤ J₀ ⊔ J₁ := hsup.symm ▸ hJ.1
      have hle' : (J' : Subgroup W) ≤ J₀ ⊔ J₁ := hsup.symm ▸ hJ'.1
      exact Subtype.ext
        (Z391.v2f_eq_of_le_sup (A := ↥L) (P := J₀) (P' := J₁) (R := (J : Subgroup W))
          (R' := (J' : Subgroup W))
          (s1611e3_isIrr_of_nat hUfix hJ₀U hJ₀) (s1611e3_isIrr_of_nat hUfix hJ₁U hJ₁) hE
          (s1611e3_isIrr_of_nat hUfix hJ.1 hJ.2) (s1611e3_isIrr_of_nat hUfix hJ'.1 hJ'.2)
          hle hle' hJn.1 hJn.2 hJn'.1 hJn'.2)
  exact (Nat.card_le_card_of_injective _ hg_inj).trans (by simp)

end Module

theorem s1611e3_a5_inv {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L Z : Subgroup (MulAut W)} {U : Subgroup W} (hL : IsAlt ↥L 5)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 2)
    (hZ : Nat.card ↥Z = 3) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZU : ∀ z ∈ Z, ∀ w ∈ U, z w ∈ U) (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ U, z w ≠ w)
    {P : Subgroup (MulAut W)} (hP : IsPGroup 2 ↥P)
    (hPL : ∀ x ∈ P, L.map (MulAut.conj x).toMonoidHom = L)
    (hPU : ∀ x ∈ P, U.map x.toMonoidHom = U) :
    ∃ J : Subgroup W, J ≤ U ∧ AlternatingNatural L J ⊥ 5 ∧ ∀ x ∈ P, J.map x.toMonoidHom = J := by
  classical
  obtain ⟨J₀, J₁, hJ₀nat, hJ₁nat, hJ₀J₁inf, hJ₀J₁sup⟩ := s1611e3_sumOfNat_two hsum
  have hJ₀U : J₀ ≤ U := hJ₀J₁sup ▸ le_sup_left
  have hJ₁U : J₁ ≤ U := hJ₀J₁sup ▸ le_sup_right
  have hUfix : U ⊓ fixV L = ⊥ :=
    s16e_inf_fixV_eq_bot_sumOfNat_alt (n := 5) (by norm_num) (by norm_num) hsum
  have hE : Z391.EndUnitsTrivial L J₀ := s16c167_endUnits_alt (n := 5) (by norm_num) hJ₀nat
  have hZne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    norm_num at hZ
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hzZ' : z ∈ Z := hzZ
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3 : z ^ 3 = 1 := by
    have h : (⟨z, hzZ⟩ : ↥Z) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hzZ⟩)
      rwa [hZ] at this
    simpa [Subgroup.coe_pow] using congrArg (fun x : ↥Z => (x : MulAut W)) h
  have hPL' : ∀ x ∈ P, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro x hx l hl
    have := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hl
    rwa [hPL x hx] at this
  have hPL'' : ∀ x ∈ P, ∀ l ∈ L, x⁻¹ * l * x ∈ L := by
    intro x hx l hl
    have h := hPL' x⁻¹ (P.inv_mem hx) l hl
    simpa using h
  have hUmap : U.map z.toMonoidHom = U := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hZU z hzZ' w hw
    · intro w hw
      exact Subgroup.mem_map.2 ⟨z⁻¹ w, hZU z⁻¹ (Z.inv_mem hzZ') w hw, by simp⟩
  let J₁' : Subgroup W := J₀.map z.toMonoidHom
  have hsplit₀ := s1611e3_a5_split hW hL hsum hZ hZL hZU hZf hJ₀U hJ₀nat hzZ' hz1'
  have hJ₁'nat : AlternatingNatural L J₁' ⊥ 5 := hsplit₀.1
  have hJ₁'inf : J₀ ⊓ J₁' = ⊥ := hsplit₀.2.1
  have hJ₁'sup : J₀ ⊔ J₁' = U := hsplit₀.2.2.1
  have hJ₁'U : J₁' ≤ U := hJ₁'sup ▸ le_sup_right
  let J₂' : Subgroup W := J₁'.map z.toMonoidHom
  have hsplit₁ := s1611e3_a5_split hW hL hsum hZ hZL hZU hZf hJ₁'U hJ₁'nat hzZ' hz1'
  have hJ₂'nat : AlternatingNatural L J₂' ⊥ 5 := hsplit₁.1
  have hJ₂'inf : J₁' ⊓ J₂' = ⊥ := hsplit₁.2.1
  have hJ₂'U : J₂' ≤ U := hsplit₁.2.2.1 ▸ le_sup_right
  have hJ₀ne : J₀ ≠ ⊥ := by
    have hmem : J₀ ∈ irrSet L := s16c167_mem_irrSet_alt (n := 5) (by norm_num) hJ₀nat
    intro h0
    have hlt := hmem.2.1
    rw [h0, bot_inf_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  have hJ₁'ne : J₁' ≠ ⊥ := by
    rw [show J₁' = J₀.map z.toMonoidHom from rfl]
    exact fun h => hJ₀ne
      ((Subgroup.map_eq_bot_iff_of_injective J₀ (f := z.toMonoidHom) z.injective).mp h)
  have hJ₀J₁' : J₀ ≠ J₁' := by
    intro h
    have h1 : J₀ ⊓ J₁' = J₀ := by rw [h, inf_idem]
    rw [hJ₁'inf] at h1
    exact hJ₀ne h1.symm
  have hJ₁'J₂' : J₁' ≠ J₂' := by
    intro h
    have h1 : J₁' ⊓ J₂' = J₁' := by rw [h, inf_idem]
    rw [hJ₂'inf] at h1
    exact hJ₁'ne h1.symm
  have hz2J₁ : J₁'.map (z * z).toMonoidHom = J₀ := by
    rw [show J₁' = J₀.map z.toMonoidHom from rfl, Subgroup.map_map]
    have hcomp : ((z * z).toMonoidHom).comp z.toMonoidHom = MonoidHom.id W := by
      ext u
      have h : (z ^ 3) u = u := by rw [hz3]; rfl
      simpa [pow_three, MulAut.mul_apply] using h
    rw [hcomp, Subgroup.map_id]
  have hJ₀J₂ : J₀ ⊓ J₂' = ⊥ := by
    refine le_bot_iff.1 fun w hw => ?_
    obtain ⟨hw₀, hw₂⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨v, hv, hvz⟩ := Subgroup.mem_map.1 (show w ∈ J₁'.map z.toMonoidHom from hw₂)
    have hzw_mem : z w ∈ J₀ := by
      have h1 : z w = (z * z) v := by rw [← hvz]; simp [MulAut.mul_apply]
      rw [h1]
      exact hz2J₁ ▸ Subgroup.mem_map_of_mem (z * z).toMonoidHom hv
    have hzw_inf : z w ∈ J₀ ⊓ J₁' :=
      ⟨hzw_mem, Subgroup.mem_map_of_mem z.toMonoidHom hw₀⟩
    have hzw1 : z w = 1 := by
      have := hJ₁'inf
      rw [this, Subgroup.mem_bot] at hzw_inf
      exact hzw_inf
    exact (MulEquiv.map_eq_one_iff z).1 hzw1
  have hJ₀J₂' : J₀ ≠ J₂' := by
    intro h
    have h1 : J₀ ⊓ J₂' = J₀ := by rw [h, inf_idem]
    rw [hJ₀J₂] at h1
    exact hJ₀ne h1.symm
  let 𝒥 : Set (Subgroup W) := {J : Subgroup W | J ≤ U ∧ AlternatingNatural L J ⊥ 5}
  have h𝒥card_le : Nat.card ↥𝒥 ≤ 3 :=
    s1611e3_natSub_card_le_three hUfix hJ₀U hJ₁U hJ₀nat hJ₁nat hE hJ₀J₁inf hJ₀J₁sup
  have h𝒥card_ge : 3 ≤ Nat.card ↥𝒥 := by
    have hsub : ({J₀, J₁', J₂'} : Set (Subgroup W)) ⊆ 𝒥 := by
      intro J hJ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ
      rcases hJ with rfl | rfl | rfl
      · exact ⟨hJ₀U, hJ₀nat⟩
      · exact ⟨hJ₁'U, hJ₁'nat⟩
      · exact ⟨hJ₂'U, hJ₂'nat⟩
    have hcard3 : ({J₀, J₁', J₂'} : Set (Subgroup W)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hJ₀J₁', hJ₀J₂']),
        Set.ncard_insert_of_notMem (by simp [hJ₁'J₂']), Set.ncard_singleton]
    calc 3 = ({J₀, J₁', J₂'} : Set (Subgroup W)).ncard := hcard3.symm
      _ ≤ 𝒥.ncard := Set.ncard_le_ncard hsub
      _ = Nat.card ↥𝒥 := (Nat.card_coe_set_eq 𝒥).symm
  have hcard : Nat.card ↥𝒥 = 3 := le_antisymm h𝒥card_le h𝒥card_ge
  have hodd : ¬ 2 ∣ Nat.card ↥𝒥 := by rw [hcard]; norm_num
  let act : ↥P → ↥𝒥 → ↥𝒥 := fun x J =>
    ⟨J.1.map (x : MulAut W).toMonoidHom, by
      obtain ⟨hJU, hJnat⟩ := J.2
      refine ⟨?_, ?_⟩
      · rw [← hPU (x : MulAut W) x.2]
        exact Subgroup.map_mono hJU
      · exact s1611e3_alt_map_of_norm (hPL' (x : MulAut W) x.2) (hPL'' (x : MulAut W) x.2) hJnat⟩
  have hact_one : ∀ J : ↥𝒥, act 1 J = J := by
    intro J
    apply Subtype.ext
    show J.1.map ((1 : ↥P) : MulAut W).toMonoidHom = J.1
    rw [Subgroup.coe_one]
    exact Subgroup.map_id J.1
  have hact_mul : ∀ (x y : ↥P) (J : ↥𝒥), act (x * y) J = act x (act y J) := by
    intro x y J
    apply Subtype.ext
    show J.1.map (((x * y : ↥P) : MulAut W)).toMonoidHom =
      (J.1.map (y : MulAut W).toMonoidHom).map (x : MulAut W).toMonoidHom
    rw [Subgroup.map_map]
    rfl
  letI : MulAction ↥P ↥𝒥 :=
    { smul := act
      one_smul := hact_one
      mul_smul := hact_mul }
  obtain ⟨J, hJfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card 𝒥 hodd
  refine ⟨J.1, J.2.1, J.2.2, fun x hx => ?_⟩
  have hsmul : act ⟨x, hx⟩ J = J := (MulAction.mem_fixedPoints).1 hJfix ⟨x, hx⟩
  exact congrArg (fun J' : ↥𝒥 => (J' : Subgroup W)) hsmul

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
