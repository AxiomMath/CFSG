module

public import CFSG.GroupTheory.ProductAutFactors
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s1611e3_c9_ker_conjNormal_eq_centralizer {E : Type*} [Group E]
    (Y : Subgroup E) [Y.Normal] :
    (MulAut.conjNormal : E →* MulAut Y).ker = Subgroup.centralizer (Y : Set E) := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := congrArg (fun σ : MulAut Y => ((σ ⟨y, hy⟩ : Y) : E)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc y * e = (e * y * e⁻¹) * e := by rw [this]
      _ = e * y := by group
  · intro h
    ext y
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h y y.2]
    group

private theorem s1611e3_c9_card_prod {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) :
    Nat.card ↥(A.prod B) = Nat.card ↥A * Nat.card ↥B := by
  rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]

private theorem s1611e3_c9_center_zmod_prod {S : Type} [Group S] [Finite S] (hS : IsL3 S 1) :
    Subgroup.center (Multiplicative (ZMod 7) × S × S) =
      (⊤ : Subgroup (Multiplicative (ZMod 7))).prod ((⊥ : Subgroup S).prod ⊥) := by
  have hcen : Subgroup.center (Multiplicative (ZMod 7)) = ⊤ := Subgroup.center_eq_top
  rw [Subgroup.center_prod, Subgroup.center_prod, center_eq_bot_of_isL3 hS, hcen]

private theorem s1611e3_c9_card_center_zmod_prod {S : Type} [Group S] [Finite S]
    (hS : IsL3 S 1) :
    Nat.card ↥(Subgroup.center (Multiplicative (ZMod 7) × S × S)) = 7 := by
  rw [s1611e3_c9_center_zmod_prod hS, s1611e3_c9_card_prod, s1611e3_c9_card_prod,
    Subgroup.card_top, Subgroup.card_bot]
  simp

private theorem s1611e3_c9_pow_seven_of_pow_seven_pow {G : Type*} [Group G] (a : G) {n : ℕ}
    (h : a ^ 7 ^ n = 1) (hdvd : orderOf a ∣ 168) : a ^ 7 = 1 := by
  have hdiv : orderOf a ∣ 7 ^ n := orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hdiv
  have hk1 : k ≤ 1 := by
    by_contra hk'
    rw [not_le] at hk'
    have h49 : 7 ^ 2 ∣ (168 : ℕ) := by
      rw [hk] at hdvd
      exact (pow_dvd_pow 7 (by omega : 2 ≤ k)).trans hdvd
    norm_num at h49
  rw [← orderOf_dvd_iff_pow_eq_one, hk]
  exact pow_dvd_pow 7 hk1

private theorem s1611e3_c9_card_mulAut_prod_dvd {Z T : Type*} [CommGroup Z] [Finite Z]
    [Group T] [Finite T]
    (hZ : Nat.card Z = 7) (hcT : Subgroup.center T = ⊥) (hpT : _root_.commutator T = ⊤)
    (hAutT : Nat.card (MulAut T) ∣ 2 * 336 ^ 2) :
    Nat.card (MulAut (Z × T)) ∣ 6 * (2 * 336 ^ 2) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (Z × T), K = _root_.commutator (Z × T) := ⟨_, rfl⟩
  obtain ⟨Zc, hZc⟩ : ∃ Zc : Subgroup (Z × T), Zc = Subgroup.center (Z × T) := ⟨_, rfl⟩
  haveI : K.Characteristic := by rw [hK]; infer_instance
  haveI : Zc.Characteristic := by rw [hZc]; infer_instance
  have hZmem : ∀ a : Z, ((a, 1) : Z × T) ∈ Zc := by
    intro a
    rw [hZc, Subgroup.mem_center_iff]
    intro g
    exact Prod.ext (mul_comm g.1 a) (by simp)
  have hZle : ∀ x ∈ Zc, x.2 = 1 := by
    intro x hx
    rw [hZc, Subgroup.mem_center_iff] at hx
    have h2 : x.2 ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact congrArg Prod.snd (hx ((1 : Z), t))
    rw [hcT, Subgroup.mem_bot] at h2
    exact h2
  have hKmem : ∀ t : T, ((1, t) : Z × T) ∈ K := by
    intro t
    have ht : t ∈ _root_.commutator T := by rw [hpT]; exact Subgroup.mem_top t
    have h1 : (MonoidHom.inr Z T) t ∈ (_root_.commutator T).map (MonoidHom.inr Z T) :=
      Subgroup.mem_map_of_mem _ ht
    rw [hK]
    exact ((Subgroup.map_commutator _ _ _).le.trans (Subgroup.commutator_mono le_top le_top)) h1
  have hKle : ∀ x ∈ K, x.1 = 1 := by
    intro x hx
    have hker : K ≤ (MonoidHom.fst Z T).ker := by
      rw [hK, _root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    exact hker hx
  let eK : ↥K ≃* T :=
    { toFun := fun x => x.1.2
      invFun := fun t => ⟨(1, t), hKmem t⟩
      left_inv := fun x => Subtype.ext (Prod.ext (hKle x.1 x.2).symm rfl)
      right_inv := fun t => rfl
      map_mul' := fun x y => rfl }
  let eZ : ↥Zc ≃* Z :=
    { toFun := fun x => x.1.1
      invFun := fun a => ⟨(a, 1), hZmem a⟩
      left_inv := fun x => Subtype.ext (Prod.ext rfl (hZle x.1 x.2).symm)
      right_inv := fun a => rfl
      map_mul' := fun x y => rfl }
  have hZccard : Nat.card ↥Zc = 7 := by
    rw [Nat.card_congr eZ.toEquiv, hZ]
  haveI : IsCyclic ↥Zc := isCyclic_of_prime_card hZccard
  have hAutZ : Nat.card (MulAut ↥Zc) = 6 := by
    rw [IsCyclic.card_mulAut, hZccard, Nat.totient_prime (by norm_num)]
  have hAutK : Nat.card (MulAut ↥K) ∣ 2 * 336 ^ 2 := by
    rw [Nat.card_congr (MulAut.congr eK).toEquiv]
    exact hAutT
  let ρ : MulAut (Z × T) →* MulAut ↥K × MulAut ↥Zc :=
    (MulAut.characteristic K).prod (MulAut.characteristic Zc)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 : MulAut.characteristic K φ = 1 := congrArg Prod.fst hφ
    have h2 : MulAut.characteristic Zc φ = 1 := congrArg Prod.snd hφ
    have hfK : ∀ k ∈ K, φ k = k := fun k hk =>
      congrArg (fun f : MulAut ↥K => (f ⟨k, hk⟩ : Z × T)) h1
    have hfZ : ∀ z ∈ Zc, φ z = z := fun z hz =>
      congrArg (fun f : MulAut ↥Zc => (f ⟨z, hz⟩ : Z × T)) h2
    apply MulEquiv.ext
    rintro ⟨a, t⟩
    have e1 : ((a, t) : Z × T) = (a, 1) * (1, t) := by simp
    rw [e1, map_mul, hfZ _ (hZmem a), hfK _ (hKmem t)]
    rfl
  have hdvd := Subgroup.card_dvd_of_injective ρ hρ
  rw [Nat.card_prod, hAutZ] at hdvd
  have hfin : Nat.card (MulAut ↥K) * 6 ∣ 6 * (2 * 336 ^ 2) := by
    rw [Nat.mul_comm 6 (2 * 336 ^ 2)]
    exact mul_dvd_mul_right hAutK 6
  exact hdvd.trans hfin

theorem s1611e3_c9_card_mulAut_dvd {S : Type} [Group S] [Finite S] (hS : IsL3 S 1) :
    Nat.card (MulAut (Multiplicative (ZMod 7) × S × S)) ∣ 6 * (2 * 336 ^ 2) := by
  classical
  have hcS : Subgroup.center S = ⊥ := center_eq_bot_of_isL3 hS
  have hpS : _root_.commutator S = ⊤ := s16c1610_commutator_of_isL3 hS
  haveI : IsSimpleGroup S := isSimpleGroup_of_isL3 hS
  have hcT : Subgroup.center (S × S) = ⊥ := by
    rw [Subgroup.center_prod, hcS, Subgroup.bot_prod_bot]
  have hpT : _root_.commutator (S × S) = ⊤ := by
    have hSS : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
      rw [← _root_.commutator_def]; exact hpS
    rw [_root_.commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, hSS,
      Subgroup.top_prod_top]
  have hAutT : Nat.card (MulAut (S × S)) ∣ 2 * 336 ^ 2 := by
    have hsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤ := fun N hN => by
      haveI := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
    have hcentral : ∀ a : S, (∀ c : S, a * c = c * a) → a = 1 := by
      intro a ha
      have hmem : a ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun c => (ha c).symm
      rwa [hcS, Subgroup.mem_bot] at hmem
    have h1 : Nat.card (MulAut (S × S)) ∣ 2 * Nat.card (MulAut S) ^ 2 :=
      CFSG.GroupTheory.card_mulAut_square_dvd hsimple hcentral (exists_ne 1)
    have h2 : Nat.card (MulAut S) ^ 2 ∣ 336 ^ 2 :=
      pow_dvd_pow_of_dvd (card_mulAut_dvd_of_isL3 hS) 2
    exact h1.trans (mul_dvd_mul_left 2 h2)
  have hZ : Nat.card (Multiplicative (ZMod 7)) = 7 := by simp
  exact s1611e3_c9_card_mulAut_prod_dvd hZ hcT hpT hAutT

theorem s1611e3_c9_seven_count {A : Type} [Group A] [Finite A] {F : Subgroup A} [F.Normal]
    (hF : centralizer (F : Set A) ≤ F) {S : Type} [Group S] [Finite S] (hS : IsL3 S 1)
    (e : ↥F ≃* Multiplicative (ZMod 7) × S × S) :
    padicValNat 7 (Nat.card A) = 3 ∧ ∀ x : A, (∃ n : ℕ, x ^ 7 ^ n = 1) → x ^ 7 = 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hequiv : ↥(Subgroup.centralizer (F : Set A)) ≃ ↥(Subgroup.center ↥F) :=
    { toFun := fun x => ⟨⟨x.1, hF x.2⟩, by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2 (g : A) g.2)⟩
      invFun := fun y => ⟨y.1.1, by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp y.2 ⟨g, hg⟩)⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (Subtype.ext rfl) }
  have hCcard : Nat.card (Subgroup.centralizer (F : Set A)) = 7 := by
    rw [Nat.card_congr hequiv, Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact s1611e3_c9_card_center_zmod_prod hS
  let φ : A →* MulAut ↥F := MulAut.conjNormal
  have hker : φ.ker = Subgroup.centralizer (F : Set A) :=
    s1611e3_c9_ker_conjNormal_eq_centralizer F
  haveI : Nonempty A := ⟨1⟩
  haveI : Nonempty ↥F := ⟨1⟩
  haveI : Nonempty ↥φ.range := ⟨1⟩
  haveI : Nonempty (A ⧸ F) := ⟨1⟩
  have hNne : Nat.card φ.range ≠ 0 := (Nat.card_pos (α := ↥φ.range)).ne'
  have hAne : Nat.card A ≠ 0 := (Nat.card_pos (α := A)).ne'
  have hFne : Nat.card ↥F ≠ 0 := (Nat.card_pos (α := ↥F)).ne'
  have hcard : Nat.card A = Nat.card φ.range * 7 := by
    have h1 : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [h1, hker, hCcard]
  have hAutF : Nat.card (MulAut ↥F) ∣ 6 * (2 * 336 ^ 2) := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact s1611e3_c9_card_mulAut_dvd hS
  have hrange_dvd : Nat.card φ.range ∣ 6 * (2 * 336 ^ 2) :=
    (Subgroup.card_subgroup_dvd_card φ.range).trans hAutF
  have hZcard : Nat.card (Multiplicative (ZMod 7)) = 7 := by simp
  have hFcard : Nat.card ↥F = 7 * 168 * 168 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, card_eq_of_isL3 hS, hZcard]
  have hFv7 : padicValNat 7 (Nat.card ↥F) = 3 := by
    rw [hFcard,
      show (7 * 168 * 168 : ℕ) = 7 ^ 3 * (2 ^ 6 * 3 ^ 2) by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 2 ^ 6 * 3 ^ 2)]
  have hAv7 : padicValNat 7 (Nat.card A) = 3 := by
    refine le_antisymm ?_ ?_
    · have hM : padicValNat 7 (6 * (2 * 336 ^ 2)) = 2 := by
        rw [show 6 * (2 * 336 ^ 2) = 7 ^ 2 * (2 ^ 10 * 3 ^ 3) by norm_num,
          padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 2 ^ 10 * 3 ^ 3)]
      have hle : padicValNat 7 (Nat.card φ.range) ≤ padicValNat 7 (6 * (2 * 336 ^ 2)) :=
        (padicValNat_dvd_iff_le (p := 7) (a := 6 * (2 * 336 ^ 2))
          (n := padicValNat 7 (Nat.card φ.range)) (by norm_num)).mp
          (pow_padicValNat_dvd.trans hrange_dvd)
      rw [hM] at hle
      rw [hcard, padicValNat.mul hNne (by norm_num : (7 : ℕ) ≠ 0), padicValNat_self]
      omega
    · have h7dvd : 7 ^ 3 ∣ Nat.card A := by
        have h7F : 7 ^ 3 ∣ Nat.card ↥F := by rw [hFcard]; norm_num
        exact h7F.trans (Subgroup.card_subgroup_dvd_card F)
      exact (padicValNat_dvd_iff_le (p := 7) (a := Nat.card A) (n := 3) hAne).mp h7dvd
  have hquotv7 : padicValNat 7 (Nat.card (A ⧸ F)) = 0 := by
    have hmul := padicValNat.mul (p := 7) (a := Nat.card (A ⧸ F)) (b := Nat.card ↥F)
      (Nat.card_pos (α := A ⧸ F)).ne' hFne
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup F] at hmul
    rw [hAv7, hFv7] at hmul
    omega
  have h7notdvd : ¬ 7 ∣ Nat.card (A ⧸ F) := by
    rcases padicValNat.eq_zero_iff.mp hquotv7 with h | h | h
    · exact absurd h (by norm_num)
    · exact absurd h (Nat.card_pos (α := A ⧸ F)).ne'
    · exact h
  refine ⟨hAv7, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h1 : (QuotientGroup.mk' F x) ^ 7 ^ n = 1 := by
    rw [← map_pow, hn, map_one]
  have h2 : (QuotientGroup.mk' F x) ^ Nat.card (A ⧸ F) = 1 := pow_card_eq_one'
  have hcop7 : Nat.Coprime 7 (Nat.card (A ⧸ F)) :=
    (Nat.prime_seven.coprime_iff_not_dvd).mpr h7notdvd
  have hcop : Nat.Coprime (7 ^ n) (Nat.card (A ⧸ F)) := hcop7.pow_left n
  have hy : QuotientGroup.mk' F x = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩
  have hxF : x ∈ F := (QuotientGroup.eq_one_iff x).mp hy
  let xx : ↥F := ⟨x, hxF⟩
  have hxx : xx ^ 7 ^ n = 1 := by
    apply Subtype.ext
    simpa [xx] using hn
  have hcomp : e xx ^ 7 ^ n = 1 := by
    rw [← map_pow, hxx, map_one]
  have hz : (e xx).1 ^ 7 ^ n = 1 := by
    simpa using congrArg Prod.fst hcomp
  have ha : (e xx).2.1 ^ 7 ^ n = 1 := by
    simpa using congrArg (fun w => w.2.1) hcomp
  have hb : (e xx).2.2 ^ 7 ^ n = 1 := by
    simpa using congrArg (fun w => w.2.2) hcomp
  have hz7 : (e xx).1 ^ 7 = 1 := by
    simpa using pow_card_eq_one' (x := (e xx).1)
  have hda : orderOf (e xx).2.1 ∣ 168 := by
    have h := orderOf_dvd_of_pow_eq_one (pow_card_eq_one' (x := (e xx).2.1))
    rwa [card_eq_of_isL3 hS] at h
  have hdb : orderOf (e xx).2.2 ∣ 168 := by
    have h := orderOf_dvd_of_pow_eq_one (pow_card_eq_one' (x := (e xx).2.2))
    rwa [card_eq_of_isL3 hS] at h
  have ha7 : (e xx).2.1 ^ 7 = 1 := s1611e3_c9_pow_seven_of_pow_seven_pow _ ha hda
  have hb7 : (e xx).2.2 ^ 7 = 1 := s1611e3_c9_pow_seven_of_pow_seven_pow _ hb hdb
  have h7 : e xx ^ 7 = 1 := Prod.ext hz7 (Prod.ext ha7 hb7)
  have hxx7 : xx ^ 7 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact h7
  simpa [xx] using congrArg Subtype.val hxx7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
