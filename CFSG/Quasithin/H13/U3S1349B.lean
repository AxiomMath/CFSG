module

public import CFSG.Quasithin.H13.U3S1349A
public import CFSG.Quasithin.H13.U3S1349S

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_pCoreOf_of_quot {K : Subgroup G} {Q : Type*} [Group Q] [Finite Q]
    (hK : quasithinO2QuotientIso K Q) : (pCoreOf 2 K).relIndex K = Nat.card Q := by
  obtain ⟨φ, hφ, hker⟩ := hK
  have h1 : (pCoreOf 2 K).subgroupOf K = φ.ker := by
    rw [hker, pCoreOf]
    exact comap_map_eq_self_of_injective K.subtype_injective _
  rw [relIndex, h1, index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]

theorem relIndex_eq_three_of_quot {K S : Subgroup G} (hK : quasithinO2QuotientIso K (Perm (Fin 3)))
    (hS : IsSylowTwoOf S K) : S.relIndex K = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h6 : (pCoreOf 2 K).relIndex K = 6 := by
    rw [relIndex_pCoreOf_of_quot hK, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hOS : pCoreOf 2 K ≤ S := pCoreOf_two_le_of_isSylowTwoOf hS
  have hm := relIndex_mul_relIndex (pCoreOf 2 K) S K hOS hS.1
  rw [h6] at hm
  have hodd : ¬ 2 ∣ S.relIndex K := hS.2.2
  have hdvd : S.relIndex K ∣ 3 := by
    have h' : S.relIndex K ∣ 2 * 3 := Dvd.intro_left _ (hm.trans (by norm_num))
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm h')
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exfalso
    have hKS : K ≤ S := relIndex_eq_one.1 h
    have hKO : K ≤ pCoreOf 2 K :=
      CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ le_rfl
        ((normal_subgroupOf_iff_le_normalizer le_rfl).2 le_normalizer) (hS.2.1.to_le hKS)
    have : (pCoreOf 2 K).relIndex K = 1 := relIndex_eq_one.2 hKO
    omega
  · exact h

omit [Finite G] in
theorem eq_or_eq_of_relIndex_three {T Y X : Subgroup G} (h3 : T.relIndex X = 3) (hTY : T ≤ Y)
    (hYX : Y ≤ X) : Y = T ∨ Y = X := by
  have hm := relIndex_mul_relIndex T Y X hTY hYX
  rw [h3] at hm
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hm) with h | h
  · left
    exact le_antisymm (relIndex_eq_one.1 h) hTY
  · right
    rw [h] at hm
    have h1 : Y.relIndex X = 1 := by omega
    exact le_antisymm hYX (relIndex_eq_one.1 h1)

theorem quot_S3_sup {K T : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hTsyl : IsSylowTwoOf T (K ⊔ T)) (hK : quasithinO2QuotientIso K (Perm (Fin 3))) :
    quasithinO2QuotientIso (K ⊔ T) (Perm (Fin 3)) ∧ T.relIndex (K ⊔ T) = 3 := by
  have hsyl : IsSylowTwoOf (K ⊓ T) K := by
    have := A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
    rwa [inf_comm] at this
  have h3 : (K ⊓ T).relIndex K = 3 := relIndex_eq_three_of_quot hK hsyl
  have h3' : T.relIndex (K ⊔ T) = 3 := by rw [relIndex_sup_eq hTK, h3]
  refine ⟨quot_S3_of_index_three hTsyl h3' fun hN => ?_, h3'⟩
  have hKT : K ⊓ T ≤ pCoreOf 2 K := by
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
      inf_le_left ?_ (hTsyl.2.1.to_le inf_le_right)
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk => ?_
    exact mem_normalizer_inf (le_normalizer hk) (hN (le_sup_left (b := T) hk))
  have h6 : (pCoreOf 2 K).relIndex K = 6 := by
    rw [relIndex_pCoreOf_of_quot hK, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hdvd := relIndex_dvd_of_le_left K hKT
  rw [h6, h3] at hdvd
  exact absurd hdvd (by norm_num)

theorem oTwoRes_sup_eq {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) : oTwoRes (K ⊔ T) = oTwoRes K := by
  refine le_antisymm ?_ (oTwoRes_mono' le_sup_left)
  have hle : oTwoRes (K ⊔ T) ≤ K := oTwoRes_le_of_le_sup le_rfl hT hTK
  refine (closure_le _).2 fun x hx => subset_closure ⟨hle (subset_closure hx), hx.2⟩

@[expose] def c3 : Perm (Fin 3) := swap 0 1 * swap 1 2

theorem s3_gen : c3 * c3 * c3 = 1 ∧ ∀ τ : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 →
    τ * c3 * τ⁻¹ * c3 = 1 ∧ ∀ σ : Perm (Fin 3), σ = 1 ∨ σ = c3 ∨ σ = c3 * c3 ∨ σ = τ ∨
      σ = τ * c3 ∨ σ = τ * c3 * c3 := by
  decide

theorem s3_orders : ∀ τ : Perm (Fin 3), τ * τ = 1 ∨ τ * τ * τ = 1 := by decide

theorem card_le_two_mul_inf_centralizer {V Z I T : Subgroup G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v * v = 1) (hZV : Z ≤ V)
    (hIV : I ≤ normalizer (V : Set G)) (hI : quasithinO2QuotientIso I (Perm (Fin 3)))
    (hOI : pCoreOf 2 I ≤ centralizer (V : Set G)) (hsyl : IsSylowTwoOf (I ⊓ T) I)
    (hTZ : T ≤ centralizer (Z : Set G)) (hW : Nat.card ↥⁅V, I⁆ = 4) :
    Nat.card ↥Z ≤ 2 * Nat.card ↥(Z ⊓ centralizer (I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := id hI
  have hkerC : ∀ i : ↥I, φ i = 1 → (i : G) ∈ centralizer (V : Set G) := fun i h =>
    hOI ((map_eq_one_iff_of_ker hker i).1 h)
  have hcV : ∀ c ∈ centralizer (V : Set G), ∀ v ∈ V, c * v * c⁻¹ = v := by
    intro c hc v hv
    rw [(mem_centralizer_iff.mp hc v hv).symm, mul_inv_cancel_right]
  have hconjV : ∀ g ∈ I, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (mem_normalizer_iff.mp (hIV hg) v).mp hv
  obtain ⟨s, hsT, hs1⟩ : ∃ s : ↥I, (s : G) ∈ T ∧ φ s ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ s : ↥I, (s : G) ∈ T → φ s = 1 := fun s hs =>
      by_contra fun h => hcon ⟨s, hs, h⟩
    have hle : I ⊓ T ≤ pCoreOf 2 I := fun x hx =>
      (map_eq_one_iff_of_ker hker ⟨x, hx.1⟩).1 (hcon' ⟨x, hx.1⟩ hx.2)
    have h3 := relIndex_eq_three_of_quot hI hsyl
    have h6 : (pCoreOf 2 I).relIndex I = 6 := by
      rw [relIndex_pCoreOf_of_quot hI, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hdvd := relIndex_dvd_of_le_left I hle
    rw [h6, h3] at hdvd
    exact absurd hdvd (by norm_num)
  have hτ2 : φ s * φ s = 1 := by
    rcases s3_orders (φ s) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hsyl.2.1 ⟨s, mem_inf.2 ⟨s.2, hsT⟩⟩
      have hsk : s ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      have hk' : φ s ^ 2 ^ k = 1 := by rw [← map_pow, hsk, map_one]
      have h3 : φ s ^ 3 = 1 := by rw [pow_succ, pow_two]; exact h
      have := pow_gcd_eq_one.2 ⟨h3, hk'⟩
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at this
      exact hs1 this
  obtain ⟨hc3, hgen⟩ := s3_gen
  obtain ⟨hinv, hall⟩ := hgen (φ s) hs1 hτ2
  obtain ⟨y, hy⟩ := hφ c3
  have hy3 : (y : G) * y * y ∈ centralizer (V : Set G) :=
    hkerC (y * y * y) (by rw [map_mul, map_mul, hy, hc3])
  have hsy : (s : G) * y * (s : G)⁻¹ * y ∈ centralizer (V : Set G) :=
    hkerC (s * y * s⁻¹ * y) (by rw [map_mul, map_mul, map_mul, map_inv, hy, hinv])
  set a : G := (y : G) with ha
  set b : G := (s : G) with hb
  have haI : a ∈ I := y.2
  have hbI : b ∈ I := s.2
  have hR1 : ∀ v ∈ V, a⁻¹ * v * a = a * a * v * a⁻¹ * a⁻¹ := by
    intro v hv
    have h := hcV _ hy3 v hv
    calc a⁻¹ * v * a = a⁻¹ * (a * a * a * v * (a * a * a)⁻¹) * a := by rw [h]
      _ = a * a * v * a⁻¹ * a⁻¹ := by group
  have hR2 : ∀ v ∈ V, b * (a * v * a⁻¹) * b⁻¹ = a⁻¹ * (b * v * b⁻¹) * a := by
    intro v hv
    have hv' : a⁻¹ * (b * v * b⁻¹) * a ∈ V := by
      have := hconjV a⁻¹ (inv_mem haI) _ (hconjV b hbI v hv)
      simpa using this
    have h := hcV _ hsy _ hv'
    calc b * (a * v * a⁻¹) * b⁻¹ =
        (b * a * b⁻¹ * a) * (a⁻¹ * (b * v * b⁻¹) * a) * (b * a * b⁻¹ * a)⁻¹ := by group
      _ = a⁻¹ * (b * v * b⁻¹) * a := h
  have hbZ : ∀ z ∈ Z, b * z * b⁻¹ = z := by
    intro z hz
    rw [(mem_centralizer_iff.mp (hTZ hsT) z hz).symm, mul_inv_cancel_right]
  set π' : G → G := fun z => (a * z * a⁻¹) * (a * a * z * a⁻¹ * a⁻¹) with hπ'
  have hV1 : ∀ v ∈ V, a * v * a⁻¹ ∈ V := fun v hv => hconjV a haI v hv
  have hV2' : ∀ v ∈ V, a * a * v * a⁻¹ * a⁻¹ ∈ V := fun v hv => by
    have := hV1 _ (hV1 v hv)
    simpa [mul_assoc] using this
  let π : ↥Z →* G := MonoidHom.mk' (fun z => π' z) fun z w => by
    simp only [hπ', Subgroup.coe_mul]
    have hzV := hZV z.2
    have hwV := hZV w.2
    have e1 : a * (↑z * ↑w) * a⁻¹ = (a * z * a⁻¹) * (a * w * a⁻¹) := by group
    have e2 : a * a * (↑z * ↑w) * a⁻¹ * a⁻¹ =
        (a * a * z * a⁻¹ * a⁻¹) * (a * a * w * a⁻¹ * a⁻¹) := by group
    rw [e1, e2, mul_assoc (a * z * a⁻¹), ← mul_assoc (a * w * a⁻¹),
      hVab _ (hV1 _ hwV) _ (hV2' _ hzV)]
    group
  have hπapp : ∀ z : ↥Z, π z = π' z := fun z => rfl
  set W := ⁅V, I⁆ with hWdef
  have hπW : ∀ z ∈ Z, π' z ∈ W := by
    intro z hz
    have hzV := hZV hz
    have h1 : ⁅a, z⁆ ∈ W := by
      rw [hWdef, commutator_comm]
      exact commutator_mem_commutator haI hzV
    have h2 : ⁅a * a, z⁆ ∈ W := by
      rw [hWdef, commutator_comm]
      exact commutator_mem_commutator (mul_mem haI haI) hzV
    have e1 : ⁅a, z⁆ = (a * z * a⁻¹) * z⁻¹ := by rw [commutatorElement_def]
    have e2 : ⁅a * a, z⁆ = (a * a * z * a⁻¹ * a⁻¹) * z⁻¹ := by
      rw [commutatorElement_def]
      group
    have hc : z⁻¹ * (a * a * z * a⁻¹ * a⁻¹) = (a * a * z * a⁻¹ * a⁻¹) * z⁻¹ :=
      hVab _ (inv_mem hzV) _ (hV2' z hzV)
    have hzz : z⁻¹ * z⁻¹ = 1 := by rw [← mul_inv_rev, hV2 z hzV, inv_one]
    have e : π' z = ⁅a, z⁆ * ⁅a * a, z⁆ := by
      calc π' z = (a * z * a⁻¹) * (a * a * z * a⁻¹ * a⁻¹) * (z⁻¹ * z⁻¹) := by
            rw [hzz, mul_one]
        _ = (a * z * a⁻¹) * ((a * a * z * a⁻¹ * a⁻¹) * z⁻¹) * z⁻¹ := by group
        _ = (a * z * a⁻¹) * (z⁻¹ * (a * a * z * a⁻¹ * a⁻¹)) * z⁻¹ := by rw [hc]
        _ = ⁅a, z⁆ * ⁅a * a, z⁆ := by rw [e1, e2]; group
    rw [e]
    exact mul_mem h1 h2
  have hR1' : ∀ v ∈ V, a⁻¹ * a⁻¹ * v * a * a = a * v * a⁻¹ := by
    intro v hv
    calc a⁻¹ * a⁻¹ * v * a * a = a⁻¹ * (a⁻¹ * v * a) * a := by group
      _ = a⁻¹ * (a * a * v * a⁻¹ * a⁻¹) * a := by rw [hR1 v hv]
      _ = a * v * a⁻¹ := by group
  have hπs : ∀ z ∈ Z, b * π' z * b⁻¹ = π' z := by
    intro z hz
    have hzV := hZV hz
    have h1 : b * (a * z * a⁻¹) * b⁻¹ = a⁻¹ * z * a := by rw [hR2 z hzV, hbZ z hz]
    have h2 : b * (a * a * z * a⁻¹ * a⁻¹) * b⁻¹ = a⁻¹ * a⁻¹ * z * a * a := by
      have := hR2 _ (hV1 z hzV)
      rw [h1] at this
      calc b * (a * a * z * a⁻¹ * a⁻¹) * b⁻¹ = b * (a * (a * z * a⁻¹) * a⁻¹) * b⁻¹ := by group
        _ = a⁻¹ * (a⁻¹ * z * a) * a := this
        _ = a⁻¹ * a⁻¹ * z * a * a := by group
    calc b * π' z * b⁻¹ = (b * (a * z * a⁻¹) * b⁻¹) * (b * (a * a * z * a⁻¹ * a⁻¹) * b⁻¹) := by
          simp only [hπ']
          group
      _ = (a * a * z * a⁻¹ * a⁻¹) * (a * z * a⁻¹) := by rw [h1, h2, hR1 z hzV, hR1' z hzV]
      _ = π' z := (hVab _ (hV1 z hzV) _ (hV2' z hzV)).symm
  have hπker : ∀ z ∈ Z, π' z = 1 → a * z * a⁻¹ = z := by
    intro z hz h
    have hzV := hZV hz
    have hY : (a * a * z * a⁻¹ * a⁻¹)⁻¹ = a * a * z * a⁻¹ * a⁻¹ :=
      inv_eq_of_mul_eq_one_right (hV2 _ (hV2' z hzV))
    have hX : a * z * a⁻¹ = a * a * z * a⁻¹ * a⁻¹ := by
      rw [← hY]
      exact eq_inv_of_mul_eq_one_left h
    calc a * z * a⁻¹ = a⁻¹ * (a * a * z * a⁻¹ * a⁻¹) * a := by group
      _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [← hX]
      _ = z := by group
  have hWV : W ≤ V := by
    rw [hWdef, commutator_le]
    intro v hv i hi
    have e : ⁅v, i⁆ = v * (i * v⁻¹ * i⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hv (hconjV i hi v⁻¹ (inv_mem hv))
  have hWnorm : ∀ g ∈ I, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    have hle : W ≤ W.comap (MulAut.conj g).toMonoidHom := by
      rw [hWdef, commutator_le]
      intro v hv i hi
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : g * ⁅v, i⁆ * g⁻¹ = ⁅g * v * g⁻¹, g * i * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact commutator_mem_commutator (hconjV g hg v hv) (mul_mem (mul_mem hg hi) (inv_mem hg))
    have := hle hw
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hrange : Nat.card ↥π.range ≤ 2 := by
    have hRW : π.range ≤ W := by
      rintro _ ⟨z, rfl⟩
      exact hπW z z.2
    have hdvd : Nat.card ↥π.range ∣ 4 := hW ▸ card_dvd_of_le hRW
    by_contra hgt
    have h4 : Nat.card ↥π.range = 4 := by
      obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (show Nat.card ↥π.range ∣ 2 ^ 2 from hdvd)
      interval_cases k
      · rw [hck] at hgt
        exact absurd (by norm_num) hgt
      · rw [hck] at hgt
        exact absurd (by norm_num) hgt
      · rw [hck]
        norm_num
    have hRW' : π.range = W := eq_of_le_of_card_ge hRW (by rw [h4, hW])
    have hbW : ∀ w ∈ W, b * w * b⁻¹ = w := by
      intro w hw
      rw [← hRW'] at hw
      obtain ⟨z, rfl⟩ := hw
      exact hπs z z.2
    have haW : ∀ w ∈ W, a * w * a⁻¹ = w := by
      intro w hw
      have hwV : w ∈ V := hWV hw
      have h1 := hR2 w hwV
      rw [hbW w hw, hbW _ (hWnorm a haI w hw), hR1 w hwV] at h1
      calc a * w * a⁻¹ = a⁻¹ * (a * a * w * a⁻¹ * a⁻¹) * a := by group
        _ = a⁻¹ * (a * w * a⁻¹) * a := by rw [← h1]
        _ = w := by group
    have hπ1 : ∀ z : ↥Z, π z = 1 := by
      intro z
      have hzV := hZV z.2
      have hw := haW _ (hπW z z.2)
      have hz3 : a * a * a * z * (a * a * a)⁻¹ = z := hcV _ hy3 z hzV
      have e : a * π' z * a⁻¹ = (a * a * z * a⁻¹ * a⁻¹) * z := by
        calc a * π' z * a⁻¹ =
            (a * a * z * a⁻¹ * a⁻¹) * (a * a * a * z * (a * a * a)⁻¹) := by
              simp only [hπ']
              group
          _ = (a * a * z * a⁻¹ * a⁻¹) * z := by rw [hz3]
      rw [e] at hw
      have hXY : π' z = (a * a * z * a⁻¹ * a⁻¹) * (a * z * a⁻¹) :=
        hVab _ (hV1 _ hzV) _ (hV2' _ hzV)
      rw [hXY] at hw
      have hzX : z = a * z * a⁻¹ := mul_left_cancel hw
      have hY : a * a * z * a⁻¹ * a⁻¹ = z := by
        calc a * a * z * a⁻¹ * a⁻¹ = a * (a * z * a⁻¹) * a⁻¹ := by group
          _ = a * z * a⁻¹ := congrArg (fun x => a * x * a⁻¹) hzX.symm
          _ = z := hzX.symm
      rw [hπapp]
      simp only [hπ']
      rw [hY, ← hzX, hV2 z hzV]
    have hbot : π.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, rfl⟩
      exact (mem_bot).2 (hπ1 z)
    rw [hbot, card_bot] at h4
    exact absurd h4 (by norm_num)
  have hcentI : ∀ z ∈ Z, a * z * a⁻¹ = z → z ∈ centralizer (I : Set G) := by
    intro z hz hza
    have hzV := hZV hz
    have hcy : Commute (y : G) z := by
      show a * z = z * a
      calc a * z = a * z * a⁻¹ * a := by group
        _ = z * a := by rw [hza]
    have hcs : Commute (s : G) z := by
      show b * z = z * b
      calc b * z = b * z * b⁻¹ * b := by group
        _ = z * b := by rw [hbZ z hz]
    rw [mem_centralizer_iff]
    intro i hi
    obtain ⟨w, hw, hwφ⟩ : ∃ w : ↥I, (w = 1 ∨ w = y ∨ w = y * y ∨ w = s ∨ w = s * y ∨
        w = s * y * y) ∧ φ w = φ ⟨i, hi⟩ := by
      rcases hall (φ ⟨i, hi⟩) with h | h | h | h | h | h
      · exact ⟨1, Or.inl rfl, by rw [map_one, h]⟩
      · exact ⟨y, Or.inr (Or.inl rfl), by rw [hy, h]⟩
      · exact ⟨y * y, Or.inr (Or.inr (Or.inl rfl)), by rw [map_mul, hy, h]⟩
      · exact ⟨s, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h.symm⟩
      · exact ⟨s * y, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by rw [map_mul, hy, h]⟩
      · exact ⟨s * y * y, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), by
          rw [map_mul, map_mul, hy, h]⟩
    have ho : ((w⁻¹ * ⟨i, hi⟩ : ↥I) : G) ∈ centralizer (V : Set G) :=
      hkerC _ (by rw [map_mul, map_inv, hwφ, inv_mul_cancel])
    have hcw : Commute (w : G) z := by
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Commute.one_left z
      · exact hcy
      · exact hcy.mul_left hcy
      · exact hcs
      · exact hcs.mul_left hcy
      · exact (hcs.mul_left hcy).mul_left hcy
    have hco : Commute ((w⁻¹ * ⟨i, hi⟩ : ↥I) : G) z :=
      (mem_centralizer_iff.mp ho z hzV).symm
    have hi' : i = (w : G) * ((w⁻¹ * ⟨i, hi⟩ : ↥I) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hi']
    exact (hcw.mul_left hco).eq
  have hker_le : Nat.card ↥π.ker ≤ Nat.card ↥(Z ⊓ centralizer (I : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun z => ⟨((z : ↥Z) : G), mem_inf.2 ⟨(z : ↥Z).2, hcentI _ (z : ↥Z).2
        (hπker _ (z : ↥Z).2 (MonoidHom.mem_ker.1 z.2))⟩⟩) ?_
    intro z₁ z₂ h
    have h' := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    exact h'
  have hcard := card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv] at hcard
  rw [hcard]
  exact Nat.mul_le_mul hrange hker_le

end CFSG.Quasithin.H13.U3
