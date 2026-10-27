module

public import CFSG.Quasithin.H13.A5A7Grp
public import CFSG.Quasithin.H13.A5Rows
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Quasithin.Background.FFC4Real
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open Equiv

section Conj

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

@[expose] noncomputable def conjOnL (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ↥G →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hGL)

omit [Finite V] in
theorem conjOnL_apply_coe (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V))) (g : ↥G)
    (l : ↥L) : ((conjOnL hGL g l : ↥L) : MulAut V) = (g : MulAut V) * l * (g : MulAut V)⁻¹ :=
  rfl

theorem mem_of_conjOnL_eq_one (hB4 : B4Hyp G L)
    (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V))) {g : ↥G} (h : conjOnL hGL g = 1) :
    (g : MulAut V) ∈ L := by
  have hc : (g : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : MulAut V)) h
    simp only [conjOnL_apply_coe, MulAut.one_apply] at h1
    calc l * (g : MulAut V) = ((g : MulAut V) * l * (g : MulAut V)⁻¹) * (g : MulAut V) := by
          rw [h1]
      _ = (g : MulAut V) * l := by group
  have := centralizer_quasithinGenFitting_le G ⟨g.2, hB4.2.1 ▸ hc⟩
  rwa [← hB4.2.1] at this

end Conj

section Alt

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

@[expose] noncomputable def autAltEquiv (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Perm (Fin n) ≃* MulAut ↥(alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)

theorem autAltEquiv_apply_coe (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) (σ : Perm (Fin n))
    (a : ↥(alternatingGroup (Fin n))) :
    ((autAltEquiv n hn hn6 σ a : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) = σ * a * σ⁻¹ :=
  MulAut.conjNormal_apply σ a

@[expose] noncomputable def permOf {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (e : ↥L ≃* ↥(alternatingGroup (Fin n))) : ↥G →* Perm (Fin n) :=
  (autAltEquiv n hn hn6).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (conjOnL hGL))

omit [Finite V] in
theorem permOf_spec {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (e : ↥L ≃* ↥(alternatingGroup (Fin n))) (g : ↥G) (l : ↥L) :
    ((e (conjOnL hGL g l) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) =
      permOf hn hn6 hGL e g * (e l : Perm (Fin n)) * (permOf hn hn6 hGL e g)⁻¹ := by
  rw [← autAltEquiv_apply_coe n hn hn6]
  have h1 : autAltEquiv n hn hn6 (permOf hn hn6 hGL e g) = MulAut.congr e (conjOnL hGL g) :=
    (autAltEquiv n hn hn6).apply_symm_apply _
  rw [h1]
  show ((e (conjOnL hGL g l) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) =
    ((e (conjOnL hGL g (e.symm (e l))) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))
  rw [MulEquiv.symm_apply_apply]

omit [Finite V] in
theorem permOf_of_mem {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (e : ↥L ≃* ↥(alternatingGroup (Fin n))) (hLG : L ≤ G) (l : ↥L) :
    permOf hn hn6 hGL e ⟨l, hLG l.2⟩ = (e l : Perm (Fin n)) := by
  apply (autAltEquiv n hn hn6).injective
  rw [show autAltEquiv n hn hn6 (permOf hn hn6 hGL e ⟨l, hLG l.2⟩) =
    MulAut.congr e (conjOnL hGL ⟨l, hLG l.2⟩) from (autAltEquiv n hn hn6).apply_symm_apply _]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [autAltEquiv_apply_coe]
  show ((e (conjOnL hGL ⟨l, hLG l.2⟩ (e.symm a)) : ↥(alternatingGroup (Fin n))) :
    Perm (Fin n)) = _
  have h2 : conjOnL hGL ⟨l, hLG l.2⟩ (e.symm a) = l * e.symm a * l⁻¹ :=
    Subtype.ext (conjOnL_apply_coe hGL _ _)
  rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem permOf_injective {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) (hB4 : B4Hyp G L)
    (hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (e : ↥L ≃* ↥(alternatingGroup (Fin n))) : Function.Injective (permOf hn hn6 hGL e) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
  have h1 : conjOnL hGL g = 1 := by
    have h := MonoidHom.mem_ker.mp hg
    have h2 : MulAut.congr e (conjOnL hGL g) = 1 := by
      have := congrArg (autAltEquiv n hn hn6) h
      rw [map_one] at this
      exact ((autAltEquiv n hn hn6).apply_symm_apply _).symm.trans this
    have h3 := congrArg (MulAut.congr e).symm h2
    rwa [MulEquiv.symm_apply_apply, map_one] at h3
  have hgL := mem_of_conjOnL_eq_one hB4 hGL h1
  have hcent : e ⟨g, hgL⟩ ∈ Subgroup.center ↥(alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    have h2 := congrArg (fun φ : MulAut ↥L => φ (e.symm a)) h1
    simp only [MulAut.one_apply] at h2
    have h3 : (g : MulAut V) * (e.symm a : MulAut V) * (g : MulAut V)⁻¹ =
        (e.symm a : MulAut V) := by
      rw [← conjOnL_apply_coe hGL, h2]
    have h4 : (⟨g, hgL⟩ : ↥L) * e.symm a * (⟨g, hgL⟩ : ↥L)⁻¹ = e.symm a := Subtype.ext h3
    have h5 := congrArg e h4
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h5
    calc a * e ⟨g, hgL⟩ = (e ⟨g, hgL⟩ * a * (e ⟨g, hgL⟩)⁻¹) * e ⟨g, hgL⟩ := by rw [h5]
      _ = e ⟨g, hgL⟩ * a := by group
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
    Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hcent
  exact Subtype.ext (show (g : MulAut V) = 1 from congrArg Subtype.val hcent)

end Alt

theorem alt5_inv_pair : ∀ σ : Perm (Fin 5), σ * σ = 1 → σ ≠ 1 → Perm.sign σ = 1 →
    ∃ τ : Perm (Fin 5), Perm.sign τ = 1 ∧ (σ * (τ * σ * τ⁻¹)) ^ 5 = 1 ∧
      σ * (τ * σ * τ⁻¹) ≠ 1 := by
  decide +kernel

theorem alt5_odd_cent : ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ = -1 →
    (Finset.univ.filter fun τ : Perm (Fin 5) => Perm.sign τ = 1 ∧ τ * σ = σ * τ).card = 6 := by
  decide +kernel

theorem alt5_no_cent_four {σ : Perm (Fin 5)} (h2 : σ * σ = 1) (hs : Perm.sign σ = -1)
    (Q : Subgroup (Perm (Fin 5))) (hQA : Q ≤ alternatingGroup (Fin 5))
    (hQc : ∀ q ∈ Q, q * σ = σ * q) (hQ : Nat.card Q = 4) : False := by
  classical
  let C : Subgroup (Perm (Fin 5)) := alternatingGroup (Fin 5) ⊓ Subgroup.centralizer {σ}
  have hQC : Q ≤ C := fun q hq =>
    ⟨hQA hq, Subgroup.mem_centralizer_singleton_iff.mpr (hQc q hq)⟩
  have hC : Nat.card C = 6 := by
    rw [← alt5_odd_cent σ h2 hs, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun τ => ?_)
    show τ ∈ alternatingGroup (Fin 5) ∧ τ ∈ Subgroup.centralizer {σ} ↔ _
    rw [Perm.mem_alternatingGroup, Subgroup.mem_centralizer_singleton_iff]
  have h := Subgroup.card_dvd_of_le hQC
  rw [hQ, hC] at h
  exact absurd h (by decide)

section Exclude

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} {v : MulAut V}

theorem card_sylowTwoOf_eq {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L) {n m : ℕ}
    (hm : ¬ 2 ∣ m) (hL : Nat.card L = 2 ^ n * m) : Nat.card (S.subgroupOf L) = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hidx := (S.subgroupOf L).card_mul_index
  rw [hk, hL] at hidx
  have hi0 : (S.subgroupOf L).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  have h1 := congrArg (padicValNat 2) hidx
  rw [padicValNat.mul (pow_ne_zero k two_ne_zero) hi0,
    padicValNat.mul (pow_ne_zero n two_ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hS.2.2,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, add_zero] at h1
  rw [hk, h1]

theorem false_of_alt5 (hB4 : B4Hyp G L) (hc : Cond1321 G L v)
    (e : ↥L ≃* ↥(alternatingGroup (Fin 5))) : False := by
  have hLG : L ≤ G := hB4.2.1 ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB4.2.1 ▸ le_normalizer_quasithinGenFitting G
  have h5 : 5 ≤ 5 := le_rfl
  have h56 : (5 : ℕ) ≠ 6 := by norm_num
  set χ := permOf h5 h56 hGL e with hχ
  let vG : ↥G := ⟨v, hc.mem⟩
  set σ := χ vG with hσ
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : vG * vG = 1 := Subtype.ext hc.sq
    rw [this, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hc.ne_one
    have h1 : χ vG = χ 1 := by rw [← hσ, h, map_one]
    exact congrArg Subtype.val (permOf_injective h5 h56 hB4 hGL e h1)
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  ·
    obtain ⟨τ, hτ, hx5, hx1⟩ := alt5_inv_pair σ hσ2 hσ1 hs
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hord : orderOf (σ * (τ * σ * τ⁻¹)) = 5 := orderOf_eq_prime hx5 hx1
    let l : ↥L := e.symm ⟨τ, Perm.mem_alternatingGroup.mpr hτ⟩
    let gG : ↥G := ⟨l, hLG l.2⟩
    have hχg : χ gG = τ := by
      rw [hχ, permOf_of_mem h5 h56 hGL e hLG l, MulEquiv.apply_symm_apply]
    have hmap : ∀ m : ℕ, (v * ((l : MulAut V) * v * (l : MulAut V)⁻¹)) ^ m = 1 →
        (σ * (τ * σ * τ⁻¹)) ^ m = 1 := by
      intro m hm
      have h1 : (vG * (gG * vG * gG⁻¹)) ^ m = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hm)
      have h2 := congrArg χ h1
      rwa [map_pow, map_mul, map_mul, map_mul, map_inv, ← hσ, hχg, map_one] at h2
    rcases hc.pair l (hLG l.2) with ⟨k, hk⟩ | h3
    · have h := orderOf_dvd_of_pow_eq_one (hmap _ hk)
      rw [hord] at h
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)
    · have h := orderOf_dvd_of_pow_eq_one (hmap _ h3)
      rw [hord] at h
      exact absurd h (by norm_num)
  ·
    obtain ⟨S, hS, hSv⟩ := hc.sylow
    have hL60 : Nat.card ↥L = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hS4 : Nat.card (S.subgroupOf L) = 4 :=
      card_sylowTwoOf_eq hS (n := 2) (m := 15) (by norm_num) (hL60.trans (by norm_num))
    let Q : Subgroup (Perm (Fin 5)) := ((S.subgroupOf L).map e.toMonoidHom).map
      (alternatingGroup (Fin 5)).subtype
    have hQ4 : Nat.card Q = 4 := by
      rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective,
        Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hS4]
    have hQA : Q ≤ alternatingGroup (Fin 5) := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hQc : ∀ q ∈ Q, q * σ = σ * q := by
      rintro _ ⟨_, ⟨s, hs', rfl⟩, rfl⟩
      have hsv : (s : MulAut V) * v = v * (s : MulAut V) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hSv (Subgroup.mem_subgroupOf.mp hs'))
      have h1 : conjOnL hGL vG s = s := Subtype.ext (by
        rw [conjOnL_apply_coe]
        show v * (s : MulAut V) * v⁻¹ = (s : MulAut V)
        rw [← hsv, mul_assoc, mul_inv_cancel, mul_one])
      have h2 := permOf_spec h5 h56 hGL e vG s
      rw [h1, ← hχ, ← hσ] at h2
      show (e s : Perm (Fin 5)) * σ = σ * (e s : Perm (Fin 5))
      calc (e s : Perm (Fin 5)) * σ = (σ * (e s : Perm (Fin 5)) * σ⁻¹) * σ := by
            rw [← h2]
        _ = σ * (e s : Perm (Fin 5)) := by group
    exact alt5_no_cent_four hσ2 hs Q hQA hQc hQ4

omit [Finite V] in
theorem false_of_alt7_eq (hc : Cond1321 G L v) (hGL : G = L)
    (e : ↥L ≃* ↥(alternatingGroup (Fin 7))) : False := by
  subst hGL
  let vL : ↥G := ⟨v, hc.mem⟩
  set σ : Perm (Fin 7) := (e vL : Perm (Fin 7)) with hσ
  have hσ2 : σ * σ = 1 := by
    have : vL * vL = 1 := Subtype.ext hc.sq
    rw [hσ, ← Subgroup.coe_mul, ← map_mul, this, map_one, Subgroup.coe_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hc.ne_one
    have h1 : e vL = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hsw : σ.IsSwap := by
    refine isSwap_of_pair hσ2 hσ1 fun τ hτ => ?_
    let g : ↥G := e.symm ⟨τ, hτ⟩
    have hmap : ∀ m : ℕ, (v * ((g : MulAut V) * v * (g : MulAut V)⁻¹)) ^ m = 1 →
        (σ * (τ * σ * τ⁻¹)) ^ m = 1 := by
      intro m hm
      have h1 : (vL * (g * vL * g⁻¹)) ^ m = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hm)
      have hge : e g = ⟨τ, hτ⟩ := e.apply_symm_apply _
      have h2 := congrArg (fun x => ((e x : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))) h1
      simp only [map_pow, map_mul, map_inv, hge, map_one, Subgroup.coe_pow, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_one] at h2
      exact h2
    rcases hc.pair g g.2 with ⟨k, hk⟩ | h3
    · exact Or.inl ⟨k, hmap _ hk⟩
    · exact Or.inr (hmap _ h3)
  have hs : Perm.sign σ = 1 := Perm.mem_alternatingGroup.mp (e vL).2
  obtain ⟨a, b, hab, hσab⟩ := hsw
  rw [hσab, Perm.sign_swap hab] at hs
  exact absurd hs (by decide)

end Exclude

theorem nonempty_sl2_four_equiv_alt5 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(alternatingGroup (Fin 5))) := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    refine center_sl_eq_bot fun r hr => ?_
    have h1 : (r + 1) ^ 2 = 0 := by
      rw [add_sq, hr, mul_one, one_pow, two_mul, CharTwo.add_self_eq_zero, add_zero,
        CharTwo.add_self_eq_zero]
    have h2 : r + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h1
    calc r = (r + 1) - 1 := by ring
      _ = 1 := by rw [h2, zero_sub, CharTwo.neg_eq]
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := ePSL.symm.isSimpleGroup
  have h60 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  exact nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60

theorem factA5Rows1321 : FactA5Rows1321 := by
  intro V _ _ hV G L v hB4 hc hrow
  have hq : CFSG.IsQuasisimple ↥L := hB4.2.2.1
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨K, _, _, hK, hiso⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
    rcases hrow with h | h
    · obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv h
      exact ⟨K, hKf, hKfin, by simpa using hK,
        ⟨e.symm.trans (specialLinearGroupEquivStatedSL 2 K).symm⟩⟩
    · have h' : TwistedTensorSL L ⊤ ⊥ 2 1 := h
      obtain ⟨K, hKf, hKfin, hchar, hK, hR⟩ := h'
      obtain ⟨π, hπ⟩ := hR
      have hK4 : Nat.card K = 4 := by simpa using hK
      obtain ⟨e5⟩ := nonempty_sl2_four_equiv_alt5 hK4
      have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
        e5.isSimpleGroup
      let π' : Matrix.SpecialLinearGroup (Fin 2) K →* ↥L :=
        π.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom
      have hπ' : Function.Surjective π' :=
        hπ.1.comp (specialLinearGroupEquivStatedSL 2 K).surjective
      have hinj : Function.Injective π' := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π'.ker with h | h
        · exact (MonoidHom.ker_eq_bot_iff π').1 h
        · exfalso
          obtain ⟨a, ha⟩ := exists_ne (1 : ↥L)
          obtain ⟨g, rfl⟩ := hπ' a
          exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))
      exact ⟨K, hKf, hKfin, hK4, ⟨(MulEquiv.ofBijective π' ⟨hinj, hπ'⟩).symm⟩⟩
  obtain ⟨e⟩ := hiso
  obtain ⟨e5⟩ := nonempty_sl2_four_equiv_alt5 hK
  exact false_of_alt5 hB4 hc (e.trans e5)

theorem factSymRows1321 : FactSymRows1321 := by
  intro V _ _ hV G L A v hB4 hc h5
  obtain ⟨⟨n, hn, π, hπ, -⟩, -⟩ := h5
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (G64.symDn_faithful hn5) hπ
  obtain ⟨f⟩ := nonempty_commutator_equiv_alternating hn5 e
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn5)
  have h2 : 2 ∣ Nat.card ↥⁅ffJ G, ffJ G⁆ := by
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rcases hn with rfl | rfl <;> decide
  have hL := eq_commutator_ffJ hV hB4 f.isSimpleGroup h2
  let eL : ↥L ≃* ↥(alternatingGroup (Fin n)) := (MulEquiv.subgroupCongr hL).trans f
  rcases hn with rfl | rfl
  · exact (false_of_alt5 hB4 hc eL).elim
  · exact ⟨eL.symm.toMonoidHom, eL.symm.surjective⟩

theorem factA7FourRow1321 : FactA7FourRow1321 := by
  intro V _ _ hV G L A v hB4 hc h7
  obtain ⟨hGJ, hJL, ⟨α, π, hπ⟩, -⟩ := h7
  obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (FFC.a7Four_faithful α) hπ
  exact false_of_alt7_eq hc (hGJ.trans hJL) e

end CFSG.Quasithin.H13.A5
