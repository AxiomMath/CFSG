
module

public import CFSG.CharacterTheory.Burnside
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {A : Type} [Group A]

theorem eq_of_isSylowTwoOf_le [Finite A] {S P H : Subgroup A} (hS : IsSylowTwoOf S H)
    (hSP : S ≤ P) (hPH : P ≤ H) (hP : IsPGroup 2 P) : P = S := by
  obtain ⟨-, -, hodd⟩ := hS
  have hmul := Subgroup.relIndex_mul_relIndex S P H hSP hPH
  have hdvd : S.relIndex P ∣ S.relIndex H := Dvd.intro _ hmul
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.index (S.subgroupOf P)
  have hn0 : n = 0 := by
    by_contra h0
    apply hodd
    have h2 : 2 ∣ S.relIndex P := by
      rw [Subgroup.relIndex, hn]
      exact dvd_pow_self 2 h0
    exact h2.trans hdvd
  have h1 : S.relIndex P = 1 := by rw [Subgroup.relIndex, hn, hn0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSP

variable {M₀ R M V : Subgroup A}

theorem pCoreOf_le_centralizerSection (h : pCoreOf 2 M₀ ≤ M) :
    pCoreOf 2 M₀ ≤ CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀) := by
  intro o ho
  refine ⟨h ho, Subgroup.le_normalizer (pCoreOf_le 2 M₀ ho), Subgroup.le_normalizer ho,
    fun x hx => ?_⟩
  have h1 : x * o * x⁻¹ ∈ pCoreOf 2 M₀ :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M₀ hx) o).mp ho
  exact (pCoreOf 2 M₀).mul_mem h1 ((pCoreOf 2 M₀).inv_mem ho)

theorem mem_normalizer_inf {H K : Subgroup A} {g : A} (hH : g ∈ Subgroup.normalizer (H : Set A))
    (hK : g ∈ Subgroup.normalizer (K : Set A)) : g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup A) :
      Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  simp only [Subgroup.mem_inf]
  rw [hH h, hK h]

theorem pCoreOf_normalizer_eq [Finite A] (hR : IsPGroup 2 R)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) :
    pCoreOf 2 (Subgroup.normalizer (R : Set A)) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R' := pCoreOf 2 (Subgroup.normalizer (R : Set A)) with hR'
  have hRR' : R ≤ R' := le_pCoreOf_normalizer 2 R hR
  have hR'2 : IsPGroup 2 R' := pCoreOf_isPGroup 2 _
  have hnorm : ∀ x ∈ M₀, x ∈ Subgroup.normalizer (R' : Set A) := fun x hx =>
    le_normalizer_pCoreOf 2 _ (hM₀R hx)
  have hR'C : R' ≤ CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀) := by
    intro r hr
    have hrM : r ∈ M := hNR (pCoreOf_le 2 _ hr)
    have hrM₀ : r ∈ Subgroup.normalizer (M₀ : Set A) := hMN hrM
    refine ⟨hrM, hrM₀, normalizer_le_normalizer_pCoreOf 2 M₀ hrM₀, fun x hx => ?_⟩
    have hcR' : x * r * x⁻¹ * r⁻¹ ∈ R' :=
      R'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnorm x hx) r).mp hr) (R'.inv_mem hr)
    have hcM₀ : x * r * x⁻¹ * r⁻¹ ∈ M₀ := by
      have h1 : r * x⁻¹ * r⁻¹ ∈ M₀ :=
        (Subgroup.mem_normalizer_iff.mp hrM₀ x⁻¹).mp (M₀.inv_mem hx)
      have h2 := M₀.mul_mem hx h1
      rwa [show x * (r * x⁻¹ * r⁻¹) = x * r * x⁻¹ * r⁻¹ by group] at h2
    have hle : M₀ ⊓ R' ≤ pCoreOf 2 M₀ :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hnorm m hm))
        (hR'2.to_le inf_le_right)
    exact hle ⟨hcM₀, hcR'⟩
  exact eq_of_isSylowTwoOf_le hsyl hRR' hR'C hR'2

theorem pCoreOf_le_of_sylow [Finite A] (hR : IsPGroup 2 R) (hRM : R ≤ M)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M)
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀))) :
    pCoreOf 2 M₀ ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOM : pCoreOf 2 M₀ ≤ M :=
    (pCoreOf_le 2 M₀).trans (hM₀R.trans hNR)
  have hOC := pCoreOf_le_centralizerSection hOM
  have hp : IsPGroup 2 (R ⊔ pCoreOf 2 M₀ : Subgroup A) :=
    hR.to_sup_of_normal_right' (pCoreOf_isPGroup 2 M₀)
      (hRM.trans (hMN.trans (normalizer_le_normalizer_pCoreOf 2 M₀)))
  have h := eq_of_isSylowTwoOf_le hsyl le_sup_left (sup_le hsyl.1 hOC) hp
  exact le_sup_right.trans h.le

theorem le_pCoreOf_of_comm [Finite A] (hV : IsElemAbelian 2 V) (hVM₀ : V ≤ M₀)
    (hcomm : ⁅V, M₀⁆ = V) : V ≤ pCoreOf 2 M₀ := by
  have hN : M₀ ≤ Subgroup.normalizer (V : Set A) := by
    have h := Subgroup.normalizer_commutator_ge_right (H₁ := V) (H₂ := M₀)
    rwa [hcomm] at h
  refine le_pCoreOf_of_le_normalizer 2 hVM₀ hN fun x => ⟨1, ?_⟩
  apply Subtype.ext
  simpa using hV.2 x x.2

theorem le_normalizer_of_comm (hcomm : ⁅V, M₀⁆ = V) :
    M₀ ≤ Subgroup.normalizer (V : Set A) := by
  have h := Subgroup.normalizer_commutator_ge_right (H₁ := V) (H₂ := M₀)
  rwa [hcomm] at h

theorem le_centralizer_of_le_centerOf [Finite A] (hR : IsPGroup 2 R)
    (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hV : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R))) :
    V ≤ Subgroup.centralizer (R : Set A) := by
  have hRO : R ≤ pCoreOf 2 (M₀ ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 le_sup_right (sup_le hM₀R Subgroup.le_normalizer) hR
  exact (hV.trans inf_le_right).trans (Subgroup.centralizer_le hRO)

theorem subsingleton_of_perfect_solvable {Q : Type*} [Group Q] (hp : commutator Q = ⊤)
    (hs : Group.IsSolvable Q) : Subsingleton Q := by
  obtain ⟨n, hn⟩ := hs.solvable
  have h : ∀ k, derivedSeries Q k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hp]
  rw [h n] at hn
  exact ⟨fun a b => by
    have ha : a ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩

theorem eq_pow_mul_pow {n r s : ℕ} (hn : n ≠ 0) (hr : r.Prime)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → q = r ∨ q = s) :
    ∃ a b : ℕ, n = r ^ a * s ^ b := by
  refine ⟨n.factorization r, (ordCompl[r] n).primeFactorsList.length, ?_⟩
  have h3 : ordCompl[r] n = s ^ (ordCompl[r] n).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd (Nat.ordCompl_pos r hn).ne' fun {d} hd hdn => ?_
    rcases h d hd (hdn.trans (Nat.ordCompl_dvd n r)) with h2 | h3
    · subst h2
      exact absurd hdn (Nat.not_dvd_ordCompl hr hn)
    · exact h3
  rw [← h3, Nat.ordProj_mul_ordCompl_eq_self]

theorem exists_qElement_not_comm [Finite A] {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hper : ⁅M₀, M₀⁆ = M₀) (hN : M₀ ≤ Subgroup.normalizer (V : Set A)) (hne : ⁅V, M₀⁆ ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ q ≠ r ∧ q ≠ s ∧ ∃ y ∈ M₀, (∃ k : ℕ, y ^ q ^ k = 1) ∧
      ∃ t ∈ V, y * t * y⁻¹ ≠ t := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  set C : Subgroup M₀ := (Subgroup.centralizer (V : Set A)).subgroupOf M₀ with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc m => ?_⟩
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : (m : A)⁻¹ * v * (m : A)⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN m.2)) v).mp hv
    have h1 := hc _ hv'
    simp only [inv_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * (↑m * ↑c * (↑m)⁻¹) = ↑m * ((↑m)⁻¹ * v * ↑m * ↑c) * (↑m)⁻¹ := by group
      _ = ↑m * (↑c * ((↑m)⁻¹ * v * ↑m)) * (↑m)⁻¹ := by rw [h1]
      _ = ↑m * ↑c * (↑m)⁻¹ * v := by group
  have hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card (M₀ ⧸ C) → q = r ∨ q = s := by
    intro q hq hqd
    by_contra hqrs
    simp only [not_or] at hqrs
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqd
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    set n := orderOf y with hn
    have hn0 : n ≠ 0 := (orderOf_pos y).ne'
    set m := ordCompl[q] n with hm
    have hym : ((y ^ m : M₀) : A) ^ q ^ n.factorization q = 1 := by
      rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, hm, Nat.ordProj_mul_ordCompl_eq_self,
        hn, pow_orderOf_eq_one, Subgroup.coe_one]
    have hcen : (y ^ m : M₀) ∈ C := by
      rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := hcon q hq hqrs.1 hqrs.2 _ (y ^ m).2 ⟨_, hym⟩ v hv
      calc v * ((y ^ m : M₀) : A) = ((y ^ m : M₀) : A) * v * ((y ^ m : M₀) : A)⁻¹ *
            ((y ^ m : M₀) : A) := by rw [h1]
        _ = ((y ^ m : M₀) : A) * v := by group
    have h1 : (QuotientGroup.mk y : M₀ ⧸ C) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hcen
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hx] at h2
    exact Nat.not_dvd_ordCompl hq hn0 h2
  have hfin : Nat.card (M₀ ⧸ C) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, b, hab⟩ := eq_pow_mul_pow hfin hr hprime
  have hsolv : Group.IsSolvable (M₀ ⧸ C) := by
    let _ : Fintype (M₀ ⧸ C) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      hr hs hrs (by rw [← Nat.card_eq_fintype_card]; exact hab)
  have hcommM₀ : commutator M₀ = ⊤ := by
    apply Subgroup.map_injective M₀.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hper]
  have hcommQ : commutator (M₀ ⧸ C) = ⊤ := by
    have h1 : commutator (M₀ ⧸ C) = (commutator M₀).map (QuotientGroup.mk' C) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
    rw [h1, hcommM₀, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
  have hsub := subsingleton_of_perfect_solvable hcommQ hsolv
  apply hne
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y hy
  have h1 : (QuotientGroup.mk (⟨y, hy⟩ : M₀) : M₀ ⧸ C) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, hC, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem exists_pElement_not_comm [Finite A] (hper : ⁅M₀, M₀⁆ = M₀)
    (hN : M₀ ≤ Subgroup.normalizer (V : Set A)) (hne : ⁅V, M₀⁆ ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ y ∈ M₀, (∃ k : ℕ, y ^ p ^ k = 1) ∧
      ∃ t ∈ V, y * t * y⁻¹ ≠ t := by
  obtain ⟨q, hq, hq2, hq3, h⟩ :=
    exists_qElement_not_comm Nat.prime_two Nat.prime_three (by norm_num) hper hN hne
  refine ⟨q, hq, ?_, h⟩
  have := hq.two_le
  by_contra h5
  interval_cases q
  · exact hq2 rfl
  · exact hq3 rfl
  · exact absurd hq (by decide)

end CFSG.Quasithin.KGC31

end
