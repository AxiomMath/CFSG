module

public import CFSG.LocalAnalysis.SectionRank.OddCover.AltForm
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements

public section

namespace CFSG.RankThree.CentralCover

open CFSG.RankThree.Classical2 CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups IsMulCommutative

theorem exists_unit_sq_ne_one {K : Type*} [Field K] [Finite K] (hK : 3 < Nat.card K) :
    ∃ a : Kˣ, (a : K) ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [Nat.card_units] at hord
  refine ⟨g, fun h => ?_⟩
  have h2 : g ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h2)
  omega

section Lift

variable {Y H : Type*} [Group Y] [Group H] {φ : Y →* H}

theorem liftComm_eq_one_of_scale (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {K : Type*} [Field K] (x : Multiplicative K →* H) {t : H}
    (hxt : ∀ c, Commute (x c) t) {lam : K} (hlam : lam ≠ 1) {g : H}
    (hgx : ∀ c : K, g * x (.ofAdd c) * g⁻¹ = x (.ofAdd (lam * c))) (hgt : g * t * g⁻¹ = t)
    (c : K) : liftComm φ hφ (x (.ofAdd c)) t = 1 := by
  have hadd : ∀ c₁ c₂ : K, liftComm φ hφ (x (.ofAdd (c₁ + c₂))) t =
      liftComm φ hφ (x (.ofAdd c₁)) t * liftComm φ hφ (x (.ofAdd c₂)) t := fun c₁ c₂ => by
    rw [ofAdd_add, map_mul, liftComm_mul_left hφ hker (hxt _)]
  have hinv : ∀ c : K, liftComm φ hφ (x (.ofAdd (lam * c))) t = liftComm φ hφ (x (.ofAdd c)) t :=
    fun c => by rw [← hgx, ← liftComm_conj hφ hker (hxt _) g, hgt]
  have hsub : lam - 1 ≠ 0 := sub_ne_zero.2 hlam
  have key : ∀ c : K, liftComm φ hφ (x (.ofAdd ((lam - 1) * c))) t = 1 := fun c => by
    have h1 := hadd ((lam - 1) * c) c
    rw [show (lam - 1) * c + c = lam * c by ring, hinv] at h1
    exact (mul_eq_right.1 h1.symm)
  have := key (c / (lam - 1))
  rwa [mul_div_cancel₀ _ hsub] at this

theorem liftComm_eq_one_of_square_invariant (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {K : Type*} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h9 : p ^ f ≠ 9)
    (x : Multiplicative K →* H) (g : Kˣ → H)
    (hg : ∀ (a : Kˣ) (c : K), g a * x (.ofAdd c) * (g a)⁻¹ = x (.ofAdd ((a : K) ^ 2 * c)))
    (c c' : K) : liftComm φ hφ (x (.ofAdd c)) (x (.ofAdd c')) = 1 := by
  have hxc : ∀ a b : Multiplicative K, Commute (x a) (x b) := fun a b => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  let β : K → K → Subgroup.center Y := fun c c' =>
    ⟨liftComm φ hφ (x (.ofAdd c)) (x (.ofAdd c')), liftComm_mem_center hφ hker (hxc _ _)⟩
  have hβ : ∀ c c', (β c c' : Y) = liftComm φ hφ (x (.ofAdd c)) (x (.ofAdd c')) :=
    fun _ _ => rfl
  have hβ₁ : ∀ c₁ c₂ c', β (c₁ + c₂) c' = β c₁ c' * β c₂ c' := fun c₁ c₂ c' => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hβ, hβ, hβ, ofAdd_add, map_mul, liftComm_mul_left hφ hker (hxc _ _)]
  have hβ₂ : ∀ c c₁ c₂, β c (c₁ + c₂) = β c c₁ * β c c₂ := fun c c₁ c₂ => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hβ, hβ, hβ, ofAdd_add, map_mul, liftComm_mul_right hφ hker (hxc _ _)]
  have hβ₀ : ∀ c, β c c = 1 := fun c => Subtype.ext (by rw [hβ]; exact liftComm_self hφ _)
  have hβinv : ∀ a : K, a ≠ 0 → ∀ c c', β (a ^ 2 * c) (a ^ 2 * c') = β c c' := by
    intro a ha c c'
    apply Subtype.ext
    rw [hβ, hβ]
    have h1 := hg (Units.mk0 a ha) c
    have h2 := hg (Units.mk0 a ha) c'
    rw [Units.val_mk0] at h1 h2
    rw [← h1, ← h2]
    exact liftComm_conj hφ hker (hxc _ _) _
  let b : K → K → Additive (Subgroup.center Y) := fun c c' => Additive.ofMul (β c c')
  have hadd₁ : ∀ c₁ c₂ c', b (c₁ + c₂) c' = b c₁ c' + b c₂ c' := fun c₁ c₂ c' => by
    simp only [b, hβ₁, ofMul_mul]
  have hadd₂ : ∀ c c₁ c₂, b c (c₁ + c₂) = b c c₁ + b c c₂ := fun c c₁ c₂ => by
    simp only [b, hβ₂, ofMul_mul]
  have halt : ∀ c, b c c = 0 := fun c => by simp only [b, hβ₀, ofMul_one]
  have hinv : ∀ a : K, a ≠ 0 → ∀ c c', b (a ^ 2 * c) (a ^ 2 * c') = b c c' :=
    fun a ha c c' => by simp only [b, hβinv a ha]
  have h0 := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero hp2 hK b hadd₁ hadd₂
    halt hinv h9 c c'
  have h1 : β c c' = 1 := Additive.ofMul.injective (h0.trans ofMul_one.symm)
  rw [← hβ, h1, OneMemClass.coe_one]

end Lift

theorem commuting_SL2_defining_witness {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    {H : Type*} [Group H] {φ : Y →* H} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (hm : 1 ≤ m) {K : Fin m → Type*} [∀ i, Field (K i)] [∀ i, Fintype (K i)] (f : Fin m → ℕ)
    (hK : ∀ i, Fintype.card (K i) = p ^ f i) (hK3 : ∀ i, 3 < p ^ f i)
    (hK9 : ∀ i, p ^ f i ≠ 9) (ι : ∀ i, SL(2, K i) →* H) (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ (A : SL(2, K i)) (B : SL(2, K j)),
      ι i A * ι j B = ι j B * ι i A) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ (∑ i, f i) ∧ (∑ i, f i) ≤ localRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set x : ∀ i, Multiplicative (K i) →* H := fun i => (ι i).comp (sl2UpperHom (K i)) with hx
  have hxinj : ∀ i, Function.Injective (x i) := fun i => (hι i).comp sl2UpperHom_injective
  have hxapp : ∀ i (c : K i), x i (.ofAdd c) = ι i (sl2Upper c) := fun _ _ => rfl
  have hscale : ∀ i (a : (K i)ˣ) (c : K i), ι i (sl2Diag a) * x i (.ofAdd c) *
      (ι i (sl2Diag a))⁻¹ = x i (.ofAdd ((a : K i) ^ 2 * c)) := fun i a c => by
    rw [hxapp, hxapp, ← map_inv, ← map_mul, ← map_mul, sl2Diag_conj_upper]
  have hchar : ∀ i, CharP (K i) p := fun i => charP_of_card_eq_prime_pow (hK i)
  have hlam : ∀ i, ∃ a : (K i)ˣ, (a : K i) ^ 2 ≠ 1 := fun i =>
    exists_unit_sq_ne_one (by rw [Nat.card_eq_fintype_card, hK i]; exact hK3 i)
  choose lam hlam using hlam
  have hxcomm : ∀ i j (a : Multiplicative (K i)) (b : Multiplicative (K j)),
      Commute (x i a) (x j b) := by
    intro i j a b
    by_cases hij : i = j
    · subst hij
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
    · exact hcomm i j hij _ _
  set S : Set H := ⋃ i, Set.range (x i) with hS
  have hmemS : ∀ s ∈ S, ∃ i, ∃ c : K i, s = x i (.ofAdd c) := by
    intro s hs
    obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.1 hs
    exact ⟨i, Multiplicative.toAdd a, rfl⟩
  have hSc : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    intro s hs t ht
    obtain ⟨i, c, rfl⟩ := hmemS s hs
    obtain ⟨j, c', rfl⟩ := hmemS t ht
    exact hxcomm i j _ _
  have hpair : ∀ s ∈ S, ∀ t ∈ S, liftComm φ hφ s t = 1 := by
    intro s hs t ht
    obtain ⟨i, c, rfl⟩ := hmemS s hs
    obtain ⟨j, c', rfl⟩ := hmemS t ht
    by_cases hij : i = j
    · subst hij
      exact liftComm_eq_one_of_square_invariant hφ hker hp2
        (by rw [Nat.card_eq_fintype_card, hK i]) (hK9 i) (x i) (fun a => ι i (sl2Diag a))
        (hscale i) c c'
    · exact liftComm_eq_one_of_scale hφ hker (x i) (fun _ => hxcomm i j _ _) (hlam i)
        (hscale i (lam i)) (by rw [hxapp j c', hcomm i j hij, mul_inv_cancel_right]) c
  have hF := comap_closure_comm hφ hker hSc hpair
  have hSp : ∀ s ∈ S, s ^ p = 1 := by
    intro s hs
    obtain ⟨i, c, rfl⟩ := hmemS s hs
    rw [hxapp, ← map_pow, sl2Upper_pow, CharP.cast_eq_zero, zero_mul, sl2Upper_zero, map_one]
  have hDp : ∀ d ∈ Subgroup.closure S, d ^ p = 1 := fun d hd =>
    pow_eq_one_of_mem_closure hSc hSp hd
  have hcl : Subgroup.closure S = ⨆ i, (x i).range := by
    rw [hS, Subgroup.closure_iUnion]
    congr 1
    funext i
    rw [← MonoidHom.coe_range, Subgroup.closure_eq]
  have hcommR : Pairwise fun i j => ∀ a b : H, a ∈ (x i).range → b ∈ (x j).range →
      Commute a b := by
    rintro i j - _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact hxcomm i j a b
  have hind : iSupIndep fun i => (x i).range := by
    intro i
    rw [Subgroup.disjoint_def]
    rintro y ⟨a, rfl⟩ hy'
    set g := ι i (sl2Diag (lam i))
    have hle : (⨆ (j) (_ : j ≠ i), (x j).range) ≤ Subgroup.centralizer {g} :=
      iSup₂_le fun j hj => by
        rintro _ ⟨b, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i j (Ne.symm hj) _ _).symm
    have hfix := Subgroup.mem_centralizer_singleton_iff.1 (hle hy')
    have h1 := hscale i (lam i) (Multiplicative.toAdd a)
    rw [ofAdd_toAdd, ← hfix, mul_inv_cancel_right] at h1
    have h2 := hxinj i h1
    have h3 : ((lam i : K i) ^ 2 - 1) * Multiplicative.toAdd a = 0 := by
      have := congrArg Multiplicative.toAdd h2
      rw [toAdd_ofAdd] at this
      rw [sub_mul, one_mul, ← this, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) (hlam i)
    · rw [show a = 1 from Multiplicative.toAdd.injective (h4.trans toAdd_one.symm), map_one]
  have hcard : Nat.card (Subgroup.closure S) = p ^ (∑ i, f i) := by
    rw [hcl, card_iSup_eq_prod hcommR hind, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hK i, ← Nat.card_eq_fintype_card,
      ← Nat.card_congr (MonoidHom.ofInjective (hxinj i)).toEquiv]
    rfl
  set i₀ : Fin m := ⟨0, hm⟩
  have hK2 : ringChar (K i₀) ≠ 2 := by
    rw [ringChar.eq (K i₀) p]
    exact hp2
  have hz : orderOf (ι i₀ (sl2Diag (-1))) = 2 := by
    rw [orderOf_injective _ (hι i₀), orderOf_sl2Diag_neg_one hK2]
  have hzS : ∀ s ∈ S, Commute (ι i₀ (sl2Diag (-1))) s := by
    intro s hs
    obtain ⟨j, c, rfl⟩ := hmemS s hs
    by_cases hj : j = i₀
    · subst hj
      exact (sl2Diag_neg_one_commute _).map (ι _)
    · exact hcomm i₀ j (Ne.symm hj) _ _
  have hzD : ∀ d ∈ Subgroup.closure S, Commute (ι i₀ (sl2Diag (-1))) d := by
    intro d hd
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {ι i₀ (sl2Diag (-1))} :=
      (Subgroup.closure_le _).2 fun s hs =>
        Subgroup.mem_centralizer_singleton_iff.2 (hzS s hs).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hd)).symm
  obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
    central_cover_involution_witness Y hφ hker hp hp2 hDp hF hcard.ge hz hzD
  exact ⟨u, huY, hu, A, hA, hAab, hAcard, hrank⟩

end CFSG.RankThree.CentralCover
