module

public import CFSG.Quasithin.Background.D2Fourteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

structure D217Hyp (X : Subgroup (MulAut V)) (r : ℚ) : Prop where
  qhat : qhatOf X = (r : WithTop ℚ)
  le_two : r ≤ 2
  jhat : X = Jhat X
  comm_fitting : commV (fittingOf X) = ⊤
  indecomposable : IsIndecomposablePair X
  fstar : X ⊓ Subgroup.centralizer (fittingOf X : Set (MulAut V)) ≤ fittingOf X
  o2 : pCoreOf 2 X = ⊥
  sqtk : IsQuotientOfSQTKTC ↥X

theorem odd_card_fittingOf {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥) :
    Odd (Nat.card (fittingOf X)) := by
  classical
  set F := CFSG.fittingSubgroup ↥X with hF
  have hcard : Nat.card (fittingOf X) = Nat.card F := by
    unfold fittingOf
    exact Subgroup.card_map_of_injective X.subtype_injective
  rw [hcard]
  by_contra hodd
  have h2 : 2 ∣ Nat.card F := by
    rcases Nat.even_or_odd (Nat.card F) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥F) := inferInstance
  have hSnormal : (S : Subgroup ↥F).Normal := inferInstance
  have hSchar : (S : Subgroup ↥F).Characteristic := Sylow.characteristic_of_normal S hSnormal
  have hFnormal : F.Normal := CFSG.fittingSubgroup_normal
  have hnorm : Subgroup.normalizer (F : Set ↥X) ≤
      Subgroup.normalizer (((S : Subgroup ↥F).map F.subtype : Subgroup ↥X) : Set ↥X) :=
    normalizer_le_normalizer_map_of_characteristic (S : Subgroup ↥F)
  have hnormX : ((S : Subgroup ↥F).map F.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (F : Set ↥X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hFnormal]; exact Subgroup.mem_top g
    have := (Subgroup.mem_normalizer_iff.mp (hnorm hg) n).mp hn
    exact this
  have hSp : IsPGroup 2 ↥((S : Subgroup ↥F).map F.subtype) := by
    intro z
    obtain ⟨s, hs, hz⟩ := z.2
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    calc ((z ^ 2 ^ k : ↥((S : Subgroup ↥F).map F.subtype)) : ↥X) = (z : ↥X) ^ 2 ^ k := rfl
      _ = (F.subtype s) ^ 2 ^ k := by rw [hz]
      _ = 1 := by rw [← map_pow, h1, map_one]
  have hle : (S : Subgroup ↥F).map F.subtype ≤ CFSG.Open.pCore 2 ↥X := le_pCore 2 hnormX hSp
  have hbot : (S : Subgroup ↥F) = ⊥ := by
    have h1 : ((S : Subgroup ↥F).map F.subtype).map X.subtype ≤ pCoreOf 2 X :=
      Subgroup.map_mono hle
    rw [hO2, le_bot_iff] at h1
    have h2 := (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective).mp h2
  have hcardS := Sylow.card_eq_multiplicity S
  have hpos : 0 < (Nat.card F).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
  have h1 : Nat.card (S : Subgroup ↥F) = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [hcardS] at h1
  have : 2 ^ 1 ≤ 2 ^ (Nat.card F).factorization 2 := Nat.pow_le_pow_right (by norm_num) hpos
  omega

theorem fittingOf_le_oddFitting {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥) :
    fittingOf X ≤ oddFitting X := by
  unfold fittingOf
  rw [CFSG.fitting_eq_sup_pCore ↥X, Subgroup.map_iSup]
  refine iSup_le fun p => ?_
  have hmap : (CFSG.Open.pCore p.1.1 ↥X).map X.subtype = pCoreOf p.1.1 X := rfl
  rw [hmap]
  by_cases h2 : p.1.1 = 2
  · rw [h2, hO2]
    exact bot_le
  · have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
    exact le_iSup_of_le p.1.1 (le_iSup_of_le hp (le_iSup_of_le h2 le_rfl))

theorem D2_20 (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {r : ℚ} (h : D217Hyp X r) :
    fixV X = ⊥ ∧ ∀ W : Subgroup V, (∀ A ∈ QhatStar X, W ≤ fixV A) → W = ⊥ := by
  have hodd := odd_card_fittingOf h.o2
  obtain ⟨-, hinf⟩ := coprime_decomp hodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, h.comm_fitting, top_inf_eq, top_inf_eq] at hinf
  have hfixF : fixV (fittingOf X) = ⊥ := hinf
  have hX : fixV X = ⊥ :=
    le_bot_iff.mp (hfixF ▸ fixV_anti (fittingOf_le X))
  refine ⟨hX, fun W hW => ?_⟩
  have hle : X ≤ centSub W := by
    rw [h.jhat]
    exact iSup₂_le fun A hA g hg w hw => (hW A hA hw) g hg
  refine le_bot_iff.mp (hX ▸ ?_)
  intro w hw g hg
  exact hle hg w hw

theorem D2_18 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ} (h : D217Hyp X r)
    (hA : A ∈ QhatStar X) (hcard : Nat.card A = 2) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ⁅pCoreOf p X, A⁆ ≠ ⊥) ∧ (r = 1 ∨ r = 2) := by
  obtain ⟨r', hr', -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hex : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ⁅pCoreOf p X, A⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hcen : ∀ a ∈ A, oddFitting X ≤ Subgroup.centralizer ({a} : Set (MulAut V)) := by
      intro a ha
      refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => ?_
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon p hp hp2)
      exact this.trans (Subgroup.centralizer_le (by simpa using ha))
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp hA2.ne_bot
    have haF : (a : MulAut V) ∈ fittingOf X := by
      refine h.fstar ⟨hA2.le a.2, ?_⟩
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (hcen (a : MulAut V) a.2 (fittingOf_le_oddFitting h.o2 hf))
    have ha2 : (a : MulAut V) ^ 2 = 1 := hA2.isElemAbelian2.2 _ a.2
    have hord : orderOf (a : MulAut V) = 2 :=
      orderOf_eq_prime ha2 (fun e => ha1 (Subtype.ext e))
    have hdvd : orderOf (⟨a, haF⟩ : ↥(fittingOf X)) ∣ Nat.card (fittingOf X) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_card_fittingOf h.o2)) (even_iff_two_dvd.mpr hdvd)
  refine ⟨hex, ?_⟩
  obtain ⟨p, hp, hp2, hne⟩ := hex
  have : Fact p.Prime := ⟨hp⟩
  have hrk : rk A = 1 := by
    have : rk A = padicValNat 2 (Nat.card A) := rfl
    rw [this, hcard]
    simp
  exact ((D2_13 hV h.qhat hA hp2 rfl hne).2.2.1 hrk).1

theorem isPGroup_pCoreOf_sup {X E : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] (hEX : E ≤ X)
    (hE : IsPGroup p E) : IsPGroup p ↥(pCoreOf p X ⊔ E) := by
  have hPX : pCoreOf p X ≤ X := pCoreOf_le p X
  have hPn : ∀ x ∈ X, ∀ g ∈ pCoreOf p X, x * g * x⁻¹ ∈ pCoreOf p X := fun x hx g hg =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p X hx) g).mp hg
  have hnormX : ((pCoreOf p X).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hPn (g : MulAut V) g.2 _ hn
    simpa using this
  have hPpX : IsPGroup p ↥((pCoreOf p X).subgroupOf X) :=
    (pCoreOf_isPGroup p X).of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  have hEpX : IsPGroup p ↥(E.subgroupOf X) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEX).symm
  have hsup : IsPGroup p ↥(E.subgroupOf X ⊔ (pCoreOf p X).subgroupOf X) :=
    IsPGroup.to_sup_of_normal_right hEpX hPpX
  intro g
  have hgX : (g : MulAut V) ∈ X := sup_le hPX hEX g.2
  have hmem : (⟨g, hgX⟩ : ↥X) ∈ E.subgroupOf X ⊔ (pCoreOf p X).subgroupOf X := by
    rw [← Subgroup.subgroupOf_sup hEX hPX, Subgroup.mem_subgroupOf]
    rw [sup_comm]
    exact g.2
  obtain ⟨k, hk⟩ := hsup ⟨_, hmem⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun w : ↥(E.subgroupOf X ⊔ (pCoreOf p X).subgroupOf X) => ((w : ↥X) : MulAut V)) hk
  simpa using this

theorem D2_21 {X A : Subgroup (MulAut V)} {r : ℚ} (h : D217Hyp X r) (hA : A ∈ QhatStar X)
    (hfaith : ∀ a ∈ A, (∀ y ∈ pCoreOf 3 X, a * y = y * a) → a = 1) {a : MulAut V} (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    CFSG.Open.pRank 3 (X ⊓ Subgroup.centralizer ({a} : Set (MulAut V))) ≤ 1 := by
  obtain ⟨r', hr', -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine csSup_le' ?_
  rintro k ⟨E, hEC, hE, hEcard⟩
  have hEX : E ≤ X := hEC.trans inf_le_left
  have hEa : ∀ e ∈ E, a * e = e * a := fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hEC he).2).symm
  have hE3 : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  set P := pCoreOf 3 X with hP
  have hPp : IsPGroup 3 ↥(P ⊔ E) := isPGroup_pCoreOf_sup hEX hE3
  have haX : a ∈ X := hA2.le haA
  have ha2 : a ^ 2 = 1 := hA2.isElemAbelian2.2 a haA
  have hnormP : ∀ y ∈ P, a * y * a⁻¹ ∈ P := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X haX) y).mp hy
  have hnormPE : ∀ b ∈ Subgroup.zpowers a, ∀ y ∈ P ⊔ E, b * y * b⁻¹ ∈ P ⊔ E := by
    intro b hb y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hconj : ∀ y ∈ P ⊔ E, a * y * a⁻¹ ∈ P ⊔ E := by
      intro y hy
      let S : Subgroup (MulAut V) :=
        { carrier := {y | a * y * a⁻¹ ∈ P ⊔ E}
          one_mem' := by simp
          mul_mem' := fun {u v} hu hv => by
            have : a * (u * v) * a⁻¹ = (a * u * a⁻¹) * (a * v * a⁻¹) := by group
            show a * (u * v) * a⁻¹ ∈ P ⊔ E
            rw [this]; exact Subgroup.mul_mem _ hu hv
          inv_mem' := fun {u} hu => by
            have : a * u⁻¹ * a⁻¹ = (a * u * a⁻¹)⁻¹ := by group
            show a * u⁻¹ * a⁻¹ ∈ P ⊔ E
            rw [this]; exact Subgroup.inv_mem _ hu }
      have hPS : P ≤ S := fun z hz => Subgroup.mem_sup_left (hnormP z hz)
      have hES : E ≤ S := fun e he => by
        show a * e * a⁻¹ ∈ P ⊔ E
        rw [show a * e * a⁻¹ = e by rw [hEa e he]; group]
        exact Subgroup.mem_sup_right he
      exact (sup_le hPS hES) hy
    have e2 : a ^ j = 1 ∨ a ^ j = a := zpow_involution ha2 j
    rcases e2 with e | e
    · rw [e]; simpa using hy
    · rw [e]; exact hconj y hy
  have hfaith' : ∀ b ∈ Subgroup.zpowers a, (∀ y ∈ P ⊔ E, b * y = y * b) → b = 1 := by
    intro b hb hc
    have hbA : b ∈ A := (Subgroup.zpowers_le.mpr haA) hb
    exact hfaith b hbA fun y hy => hc y (Subgroup.mem_sup_left hy)
  have hcyc := isCyclic_inf_centralizer_of_faithful (X := X) (P := P ⊔ E) (A := Subgroup.zpowers a)
    (p := 3) (by norm_num) (sup_le (pCoreOf_le 3 X) hEX) hPp
    ⟨fun u hu v hv => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact ((Commute.refl a).zpow_zpow i j).eq,
      fun u hu => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
        simp [ha2]⟩
    ((Subgroup.zpowers_le).mpr haX) hnormPE h.sqtk hfaith' (Subgroup.mem_zpowers a) ha1
  have hEsub : E ≤ (P ⊔ E) ⊓ Subgroup.centralizer ({a} : Set (MulAut V)) :=
    fun e he => ⟨Subgroup.mem_sup_right he, Subgroup.mem_centralizer_singleton_iff.mpr (hEa e he).symm⟩
  have hEcyc : IsCyclic ↥E :=
    isCyclic_of_injective (Subgroup.inclusion hEsub) (Subgroup.inclusion_injective hEsub)
  have hexp : Monoid.exponent ↥E ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2)
  rw [IsCyclic.exponent_eq_card, hEcard] at hexp
  have : 3 ^ k ∣ 3 ^ 1 := by simpa using hexp
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this

end CFSG.Quasithin
