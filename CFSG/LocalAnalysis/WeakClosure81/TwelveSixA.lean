module

public import CFSG.LocalAnalysis.WeakClosure81.TwelvePartTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup MulAction
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Modules

variable {G : Type} [Group G]

theorem fixSub_ne_bot_of_isPGroup [Nontrivial V] (P : Subgroup (LGL 2 V)) (hP : IsPGroup 2 P) :
    fixSub P ≠ ⊥ := by
  haveI : Fintype V := Fintype.ofFinite V
  have hfin : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have h2dvd : 2 ∣ Nat.card V := by
    rw [hcardV]
    exact dvd_pow_self 2 (ne_of_gt hfin)
  have h0 : (0 : V) ∈ fixedPoints ↥P V := by
    rw [mem_fixedPoints]
    intro p
    simpa using map_zero (p : LGL 2 V)
  obtain ⟨b, hb, hbne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2dvd h0
  intro hbot
  have hb' : b ∈ fixSub P := by
    intro p hp
    simpa using (mem_fixedPoints.mp hb) ⟨p, hp⟩
  rw [hbot] at hb'
  exact hbne (show b = 0 from by simpa using hb').symm

theorem isElemAbelian_of_repQuad {ρ : G →* LGL 2 V} (hρ : Function.Injective ρ) {A : Subgroup G}
    (hq : RepQuad ρ A) : IsElemAbelian 2 A := by
  have hmap : IsElemAbelian 2 (A.map ρ) := isElemAbelian_of_quadratic hq
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    apply hρ
    simp only [Subgroup.coe_mul, map_mul]
    have h := isMulCommutative_iff.mp hmap.1
      ⟨ρ a, Subgroup.mem_map_of_mem ρ a.2⟩ ⟨ρ b, Subgroup.mem_map_of_mem ρ b.2⟩
    simpa using congrArg Subtype.val h
  · intro x hx
    apply hρ
    simp only [map_pow, map_one]
    exact hmap.2 (ρ x) (Subgroup.mem_map_of_mem ρ hx)

theorem commSub_range_eq_top (ρ : G →* LGL 2 V) (hirr : IsChiefFactor ρ ⊤ ⊥)
    (hnt : IsNoncentral ρ ⊤ ⊥) : commSub ρ.range = ⊤ := by
  have hinv : ∀ g : G, ∀ w ∈ commSub ρ.range, ρ g w ∈ commSub ρ.range :=
    fun g _ hw => map_mem_commSub (A := ρ.range) (MonoidHom.mem_range.mpr ⟨g, rfl⟩) hw
  rcases hirr.2.2.2 (commSub ρ.range) bot_le le_top hinv with h | h
  · exfalso
    obtain ⟨g, w, -, hw⟩ := hnt
    have hmem : ρ g w - w ∈ commSub ρ.range :=
      sub_mem_commSub (A := ρ.range) (MonoidHom.mem_range.mpr ⟨g, rfl⟩) w
    rw [h] at hmem
    exact hw hmem
  · exact h

theorem fixSub_range_eq_bot (ρ : G →* LGL 2 V) (hirr : IsChiefFactor ρ ⊤ ⊥)
    (hnt : IsNoncentral ρ ⊤ ⊥) : fixSub ρ.range = ⊥ := by
  have hinv : ∀ g : G, ∀ w ∈ fixSub ρ.range, ρ g w ∈ fixSub ρ.range := by
    intro g w hw t ht
    obtain ⟨k, rfl⟩ := ht
    have hkg : ρ k (ρ g w) = ρ (k * g) w := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
    rw [hkg, hw (ρ (k * g)) (MonoidHom.mem_range.mpr ⟨k * g, rfl⟩),
      hw (ρ g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)]
  rcases hirr.2.2.2 (fixSub ρ.range) bot_le le_top hinv with h | h
  · exact h
  · exfalso
    obtain ⟨g, w, -, hw⟩ := hnt
    apply hw
    rw [Submodule.mem_bot, sub_eq_zero]
    have hwfix : w ∈ fixSub ρ.range := by rw [h]; trivial
    exact hwfix (ρ g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)

theorem pCore_eq_bot_of_irreducible [Finite G] (ρ : G →* LGL 2 V) (hρ : Function.Injective ρ)
    (hirr : IsChiefFactor ρ ⊤ ⊥) : CFSG.pCore 2 G = ⊥ := by
  let P : Subgroup G := CFSG.pCore 2 G
  haveI hPnorm : P.Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  haveI hNtriv : Nontrivial V := by
    by_contra h
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp h
    have htopbot : (⊤ : Submodule (ZMod 2) V) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x _
      exact Subsingleton.elim x 0
    exact (bot_lt_iff_ne_bot.mp hirr.1) htopbot
  have hne : fixSub (P.map ρ) ≠ ⊥ := fixSub_ne_bot_of_isPGroup (P.map ρ) (hP2.map ρ)
  have hinv : ∀ g : G, ∀ w ∈ fixSub (P.map ρ), ρ g w ∈ fixSub (P.map ρ) := by
    intro g w hw t ht
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ht
    have hconj : g⁻¹ * p * g ∈ P := by
      simpa using hPnorm.conj_mem p hp g⁻¹
    have hfix : ρ (g⁻¹ * p * g) w = w :=
      hw _ (Subgroup.mem_map.mpr ⟨g⁻¹ * p * g, hconj, rfl⟩)
    have h1 : ρ p (ρ g w) = ρ (p * g) w := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
    have h2 : ρ (p * g) w = ρ g (ρ (g⁻¹ * p * g) w) := by
      have : p * g = g * (g⁻¹ * p * g) := by group
      rw [this, map_mul, LinearEquiv.mul_apply]
    rw [h1, h2, hfix]
  have htop : fixSub (P.map ρ) = ⊤ := by
    rcases hirr.2.2.2 (fixSub (P.map ρ)) bot_le le_top hinv with h | h
    · exact absurd h hne
    · exact h
  rw [eq_bot_iff]
  intro p hp
  rw [Subgroup.mem_bot]
  apply hρ
  rw [map_one]
  ext w
  have hw : w ∈ fixSub (P.map ρ) := by rw [htop]; trivial
  simpa using hw (ρ p) (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)

end Modules

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.normalClosure_eq_top (h : Setting12Two A M n) :
    Subgroup.normalClosure (A : Set G) = ⊤ := by
  by_contra hne
  have hleM : Subgroup.normalClosure (A : Set G) ≤ M :=
    h.unique_max _ Subgroup.subset_normalClosure hne
  haveI hnorm : (Subgroup.normalClosure (A : Set G)).Normal := Subgroup.normalClosure_normal
  exact h.not_le_ker fun a ha => by
    rw [CFSG.Quasithin.mem_kerIn]
    intro b _
    exact hleM (hnorm.conj_mem a (Subgroup.subset_normalClosure ha) b)

theorem Setting12Two.odd_card_ker (h : Setting12Two A M n) (hO : CFSG.pCore 2 G = ⊥) :
    Odd (Nat.card ↥(CFSG.Quasithin.kerIn M ⊤)) := by
  let K : Subgroup G := CFSG.Quasithin.kerIn M ⊤
  haveI hKnormal : K.Normal := kerIn_top_normal12 M
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI hΩfin : Finite (Sylow 2 ↥K) :=
    Sylow.finite_of_finiteIndex (default : Sylow 2 ↥K)
  let f : ↥A →* MulAut ↥K := MulAut.conjNormal.comp A.subtype
  letI : MulAction ↥A (Sylow 2 ↥K) := MulAction.compHom (Sylow 2 ↥K) f
  have hmod : Nat.card (Sylow 2 ↥K) ≡ 1 [MOD 2] := card_sylow_modEq_one 2 ↥K
  have hfixmod : Nat.card (fixedPoints ↥A (Sylow 2 ↥K)) ≡ 1 [MOD 2] :=
    (h.A_two.card_modEq_card_fixedPoints (Sylow 2 ↥K)).symm.trans hmod
  have hodd : Odd (Nat.card (fixedPoints ↥A (Sylow 2 ↥K))) := by
    rw [Nat.odd_iff]
    have h : Nat.card (fixedPoints ↥A (Sylow 2 ↥K)) % 2 = 1 % 2 := hfixmod
    simpa using h
  haveI : Finite (fixedPoints ↥A (Sylow 2 ↥K)) := inferInstance
  obtain ⟨P, hPfix⟩ : ∃ P : Sylow 2 ↥K, P ∈ fixedPoints ↥A (Sylow 2 ↥K) :=
    Set.nonempty_coe_sort.mp (Finite.card_pos_iff.mp hodd.pos)
  have hAnorm : A ≤ Subgroup.normalizer ((P : Subgroup ↥K).map K.subtype : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    let c : MulAut ↥K := MulAut.conjNormal a
    have hfix_a : (⟨a, ha⟩ : ↥A) • P = P := (mem_fixedPoints.mp hPfix) ⟨a, ha⟩
    have hsmul : c • (P : Subgroup ↥K) = (P : Subgroup ↥K) := by
      have hh := congrArg (fun Q : Sylow 2 ↥K => (Q : Subgroup ↥K)) hfix_a
      rw [← Sylow.pointwise_smul_def]
      simpa [MulAction.compHom_smul_def, f, c] using hh
    have hmem_iff : ∀ p : ↥K, c • p ∈ (P : Subgroup ↥K) ↔ p ∈ (P : Subgroup ↥K) := by
      intro p
      constructor
      · intro hp
        have h' := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
          (a := c) (S := (P : Subgroup ↥K)) (x := c • p)).mp (hsmul.symm ▸ hp)
        simpa using h'
      · intro hp
        exact hsmul ▸ Subgroup.smul_mem_pointwise_smul p c (P : Subgroup ↥K) hp
    have hmapP : (P : Subgroup ↥K).map c.toMonoidHom = (P : Subgroup ↥K) := by
      ext q
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact (hmem_iff p).mpr hp
      · intro hq
        refine ⟨c⁻¹ • q, (hmem_iff _).mp ?_, ?_⟩
        · rwa [smul_inv_smul]
        · simpa using smul_inv_smul c q
    have hcomp : (MulAut.conj a).toMonoidHom.comp K.subtype =
        K.subtype.comp c.toMonoidHom := by
      ext p
      simp [c, MulAut.conjNormal_apply, MulAut.conj_apply]
    calc ((P : Subgroup ↥K).map K.subtype).map (MulAut.conj a).toMonoidHom
        = (P : Subgroup ↥K).map ((MulAut.conj a).toMonoidHom.comp K.subtype) :=
          Subgroup.map_map (P : Subgroup ↥K) (MulAut.conj a).toMonoidHom K.subtype
      _ = (P : Subgroup ↥K).map (K.subtype.comp c.toMonoidHom) := by rw [hcomp]
      _ = ((P : Subgroup ↥K).map c.toMonoidHom).map K.subtype :=
          (Subgroup.map_map (P : Subgroup ↥K) K.subtype c.toMonoidHom).symm
      _ = (P : Subgroup ↥K).map K.subtype := by rw [hmapP]
  have hfratt : Subgroup.normalizer ((P : Subgroup ↥K).map K.subtype : Set G) ⊔ K = ⊤ :=
    Sylow.normalizer_sup_eq_top (N := K) P
  have hnorm_top : Subgroup.normalizer ((P : Subgroup ↥K).map K.subtype : Set G) = ⊤ := by
    by_contra hne
    have hleM : Subgroup.normalizer ((P : Subgroup ↥K).map K.subtype : Set G) ≤ M :=
      h.unique_max _ hAnorm hne
    have hKleM : K ≤ M := CFSG.Quasithin.kerIn_le
    exact h.M_ne (top_le_iff.mp (by rw [← hfratt]; exact sup_le hleM hKleM))
  haveI hPaNorm : ((P : Subgroup ↥K).map K.subtype).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hnorm_top
  have hPa2 : IsPGroup 2 ((P : Subgroup ↥K).map K.subtype) := P.isPGroup'.map K.subtype
  have hPaBot : (P : Subgroup ↥K).map K.subtype = ⊥ := by
    have hle : (P : Subgroup ↥K).map K.subtype ≤ CFSG.pCore 2 G :=
      le_sSup (show (P : Subgroup ↥K).map K.subtype ∈
        {Q : Subgroup G | Q.Normal ∧ IsPGroup 2 Q} from ⟨hPaNorm, hPa2⟩)
    rw [hO] at hle
    exact le_bot_iff.mp hle
  have hPbot : (P : Subgroup ↥K) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup ↥K) K.subtype_injective).mp hPaBot
  have hpow : 2 ^ (Nat.card ↥K).factorization 2 = 1 := by
    have hPcard : Nat.card P = 1 := by
      change Nat.card ↥((P : Subgroup ↥K)) = 1
      rw [hPbot, Subgroup.card_bot]
    rw [← Sylow.card_eq_multiplicity P]
    exact hPcard
  have hexp : (Nat.card ↥K).factorization 2 = 0 := by
    by_contra hne
    have hdvd : 2 ∣ 2 ^ (Nat.card ↥K).factorization 2 := dvd_pow_self 2 hne
    rw [hpow] at hdvd
    exact absurd hdvd (by norm_num)
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2dvd
  have hKne : Nat.card ↥K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hpos : 0 < (Nat.card ↥K).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hKne h2dvd
  omega

theorem Setting12Two.inf_ker_eq_bot (h : Setting12Two A M n)
    (hKodd : Odd (Nat.card ↥(CFSG.Quasithin.kerIn M ⊤))) : A ⊓ CFSG.Quasithin.kerIn M ⊤ = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  have h2 : IsPGroup 2 ↥(A ⊓ CFSG.Quasithin.kerIn M ⊤) :=
    IsPGroup.to_le h.A_two inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hdvd : Nat.card ↥(A ⊓ CFSG.Quasithin.kerIn M ⊤) ∣
      Nat.card ↥(CFSG.Quasithin.kerIn M ⊤) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hkne
    have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hkne
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr (h2dvd.trans hdvd))
  rw [hk, hk0, pow_zero]

variable {ρ : G →* LGL 2 V}

theorem Setting12Two.fixSub_eq_commSub (h : Setting12Two A M n) (hq : RepQuad ρ A)
    (hirr : IsChiefFactor ρ ⊤ ⊥) (hnt : IsNoncentral ρ ⊤ ⊥) {a : G} (ha : a ∈ A)
    (haK : a ∉ CFSG.Quasithin.kerIn M ⊤) (v : V) :
    ρ a v = v ↔ v ∈ commSub (A.map ρ) := by
  have htop : commSub ρ.range = ⊤ := commSub_range_eq_top ρ hirr hnt
  have hbot : fixSub ρ.range = ⊥ := fixSub_range_eq_bot ρ hirr hnt
  have hcE : cE ρ.range = ⊥ := by rw [cE, hbot, bot_inf_eq]
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra hM
    rw [not_exists] at hM
    simp only [not_not] at hM
    exact h.M_ne (eq_top_iff.mpr fun x _ => hM x)
  have hfix := (twelveFive_partTwo h ρ hq hg).2.2.1 (ρ a)
    (Subgroup.mem_map_of_mem ρ ha) ⟨a, ha, haK, rfl⟩
  rw [hcE, htop, inf_top_eq, sup_bot_eq] at hfix
  constructor
  · intro hv
    rw [← hfix, mem_fixMod, Submodule.mem_bot, sub_eq_zero]
    exact hv
  · intro hv
    rw [← hfix, mem_fixMod, Submodule.mem_bot, sub_eq_zero] at hv
    exact hv

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81
