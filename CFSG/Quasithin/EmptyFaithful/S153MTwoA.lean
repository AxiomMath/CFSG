module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoDef
public import CFSG.Quasithin.Background.InternalSecB5
import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

open scoped commutatorElement

section Generic

variable {Ω : Type} [Group Ω]

private theorem twoA_eq_of_normal_of_isQuasisimple {K E : Subgroup Ω} (hKE : K ≤ E)
    (hn : ∀ x ∈ E, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hE : CFSG.IsQuasisimple ↥E) : K = E := by
  have hnorm : (K.subgroupOf E).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hn g g.2 k hk
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hE) (K.subgroupOf E) with hc | htop
  · exfalso
    refine InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => ?_
    have h1 : (⟨a, hKE ha⟩ : ↥E) ∈ Subgroup.center ↥E := hc ha
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
    exact (congrArg Subtype.val h2).symm
  · refine le_antisymm hKE (fun e he => ?_)
    have : (⟨e, he⟩ : ↥E) ∈ K.subgroupOf E := by rw [htop]; trivial
    exact this

private theorem twoA_commute_of_not_le {X J M K : Subgroup Ω} (hJX : J ≤ X)
    (hXJ : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J) (hMX : M ≤ X)
    (hXM : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hKM : K ≤ M)
    (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) (hKJ : ¬ K ≤ J) :
    ∀ j ∈ J, ∀ k ∈ K, j * k = k * j := by
  have hKo := B1Red.isQuasisimple_to_open hK
  have hNK : ∀ n ∈ J ⊓ M, ∀ k ∈ K, n * k = k * n := by
    refine B1Red.commute_of_normal_not_le hKo (fun n hn k hk => hMK n hn.2 k hk)
      (fun k hk n hn => ⟨hXJ k (hMX (hKM hk)) n hn.1, hXM k (hMX (hKM hk)) n hn.2⟩) ?_
    intro h
    exact hKJ (h.trans inf_le_left)
  have h1 : ⁅K, J⁆ ≤ J ⊓ M := by
    rw [Subgroup.commutator_le]
    intro k hk j hj
    refine ⟨J.mul_mem (hXJ k (hMX (hKM hk)) j hj) (J.inv_mem hj), ?_⟩
    have h5 := M.mul_mem (hKM hk) (hXM j (hJX hj) k⁻¹ (M.inv_mem (hKM hk)))
    have e : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact h5
  have h2 : ⁅⁅K, J⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hNK x (h1 hx) k hk).symm
  have : Group.IsPerfect ↥K := hK.1
  have h3 : ⁅K, J⁆ = ⊥ :=
    CFSG.ComponentClassification.Quasisimple.perfect_double_commutator K J h2
  intro j hj k hk
  have h4 : ⁅k, j⁆ ∈ (⊥ : Subgroup Ω) := h3 ▸ Subgroup.commutator_mem_commutator hk hj
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
  exact h4.symm

private theorem twoA_isNilpotent_of_central_two_quot [Finite Ω] {N A : Subgroup Ω}
    (hc : ∀ a ∈ A, ∀ n ∈ N, a * n = n * a) (h2 : ∀ n ∈ N, ∃ e : ℕ, n ^ 2 ^ e ∈ A) :
    Group.IsNilpotent ↥N := by
  have hAn : (A.subgroupOf N).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have h1 := hc a ha g g.2
    have e : (g : Ω) * a * (g : Ω)⁻¹ = a := by
      rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    show (g : Ω) * a * (g : Ω)⁻¹ ∈ A
    rw [e]
    exact ha
  have hcen : (QuotientGroup.mk' (A.subgroupOf N)).ker ≤ Subgroup.center ↥N := by
    rw [QuotientGroup.ker_mk']
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    rw [Subgroup.mem_subgroupOf] at ha
    exact Subtype.ext (hc a ha g g.2).symm
  have hP : IsPGroup 2 (↥N ⧸ A.subgroupOf N) := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 n n.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using he
  have : Group.IsNilpotent (↥N ⧸ A.subgroupOf N) := hP.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (A.subgroupOf N)) hcen

private theorem twoA_eq_or_eq_of_normal [Finite Ω] {J L₁ L₂ K : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hL₁J : L₁ ≤ J) (hL₂J : L₂ ≤ J) (h2 : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hKJ : K ≤ J) (hKn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) :
    K = L₁ ∨ K = L₂ := by
  have hKL : K ≤ L₁ ⊔ L₂ :=
    (B1Red.perfect_le_oTwoUpper' hKJ hK.1).trans (oTwoUpper_le_of_pow_mem h2)
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le hL₁J hL₂J
  rcases InternalSec.le_or_le_of_sup_eq rfl hcomm hKL
    (fun x hx k hk => hKn x (hLJ hx) k hk) hK with h | h
  · exact Or.inl
      (twoA_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₁J hx) k hk) hK hq₁)
  · exact Or.inr
      (twoA_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₂J hx) k hk) hK hq₂)

private theorem twoA_le_of_perfect_of_isSolvable {A B P : Subgroup Ω}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hPAB : P ≤ A ⊔ B) (hP : Group.IsPerfect ↥P)
    (hB : Group.IsSolvable ↥B) : P ≤ A := by
  set H := A ⊔ B with hH
  have hBH : B ≤ H := le_sup_right
  set N : Subgroup ↥H := A.subgroupOf H with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc g g.2 n hn
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (Subgroup.inclusion hBH)) := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hc)).1 hh
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' N ⟨b, hBH hb⟩ = QuotientGroup.mk' N ⟨a * b, hh⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    show (b⁻¹ * (a * b) : Ω) ∈ A
    rw [hc a ha b hb, inv_mul_cancel_left]
    exact ha
  have : Group.IsSolvable (↥H ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hPH : P ≤ H := hPAB
  let φ : ↥P →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hPH)
  have hr : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  intro p hp
  have h1 : φ ⟨p, hp⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hr, Subgroup.mem_bot] at h1
  have h2 : (⟨p, hPH hp⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

private theorem twoA_isSolvable_of_card_six {H : Type*} [Group H] (h : Nat.card H = 6) :
    Group.IsSolvable H := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h]; norm_num : 3 ∣ Nat.card H)
  set P := Subgroup.zpowers x with hP
  have hPc : Nat.card ↥P = 3 := by rw [hP, Nat.card_zpowers, hx]
  have hidx : P.index = 2 := by
    have := P.card_mul_index
    rw [hPc, h] at this
    omega
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card hPc
  have hQc : Nat.card (H ⧸ P) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcyc : IsCyclic (H ⧸ P) := isCyclic_of_prime_card hQc
  exact Group.isSolvable_of_subgroup_quotient P

end Generic

section Orders

private theorem twoA_card_statedSL_two {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

private theorem twoA_card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

end Orders

section Factors

variable {Ω : Type} [Group Ω]

private theorem twoA_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

private theorem twoA_isQuasisimple_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : CFSG.IsQuasisimple Q := by
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := h }
    exact hp IsSimpleGroup.prime_card
  have hperf : Group.IsPerfect Q := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h
  exact B1Red.isQuasisimple_of_open (CFSG.ComponentClassification.Quasisimple.simple_of_perfect Q)

private theorem twoA_fac_of_simple [Finite Ω] {G : Subgroup Ω} (hs : IsSimpleGroup ↥G)
    (hp : ¬ (Nat.card ↥G).Prime) :
    ∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      (K = G ∨ Nat.card ↥K < 504) :=
  ⟨G, le_rfl, fun _ hg _ hk => G.mul_mem (G.mul_mem hg hk) (G.inv_mem hg),
    twoA_isQuasisimple_of_simple hp, Or.inl rfl⟩

private theorem twoA_fac_of_perm_five {G : Subgroup Ω} (e : ↥G ≃* Equiv.Perm (Fin 5)) :
    ∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      (K = G ∨ Nat.card ↥K < 504) := by
  set f : Equiv.Perm (Fin 5) →* Ω := G.subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := G.subtype_injective.comp e.symm.injective
  have hcard : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hA5 : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 5)) :=
    twoA_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have e' := (alternatingGroup (Fin 5)).equivMapOfInjective f hfinj
  refine ⟨(alternatingGroup (Fin 5)).map f, ?_, ?_, ?_, Or.inr ?_⟩
  · rintro _ ⟨σ, -, rfl⟩
    exact (e.symm σ).2
  · rintro g hg _ ⟨a, ha, rfl⟩
    have hg' : f (e ⟨g, hg⟩) = g := by simp [hf]
    refine ⟨e ⟨g, hg⟩ * a * (e ⟨g, hg⟩)⁻¹, Subgroup.Normal.conj_mem inferInstance a ha _, ?_⟩
    rw [map_mul, map_mul, map_inv, hg']
  · exact B1Red.isQuasisimple_of_open
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv e'.symm
        (B1Red.isQuasisimple_to_open hA5))
  · rw [← Nat.card_congr e'.toEquiv, hcard]
    norm_num

private theorem twoA_fac_of_factorList [Finite Ω] {G : Subgroup Ω} (h : B56FactorList ↥G) :
    (∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
        (K = G ∨ Nat.card ↥K < 504)) ∨
      (Group.IsSolvable ↥G ∧ 3 ∣ Nat.card ↥G) := by
  rcases h with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, hm, hmodd, hF, ⟨e⟩⟩
  · have hcard : Nat.card ↥G = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, twoA_card_statedSL_two]
    by_cases hn1 : n = 1
    · subst hn1
      right
      have h6 : Nat.card ↥G = 6 := by rw [hcard, hF]; norm_num
      exact ⟨twoA_isSolvable_of_card_six h6, by rw [h6]; norm_num⟩
    · left
      have : CharP F 2 := twoA_charP_two hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hs : IsSimpleGroup ↥(StatedSL 2 F) :=
        CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      have : IsSimpleGroup ↥G := e.isSimpleGroup
      refine twoA_fac_of_simple this ?_
      rw [hcard]
      have h16 : 16 ≤ Nat.card F ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h4 2
      exact Nat.not_prime_mul (by omega) (by omega)
  · obtain ⟨e⟩ := he
    exact Or.inl (twoA_fac_of_perm_five e)
  · left
    have hcard : Nat.card ↥G =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, twoA_card_statedSL_three]
    have hs : IsSimpleGroup ↥(StatedSL 3 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hmodd
    have : IsSimpleGroup ↥G := e.isSimpleGroup
    refine twoA_fac_of_simple this ?_
    rw [hcard]
    have hq : 2 ≤ Nat.card F := by
      rw [hF]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h8 : 8 ≤ Nat.card F ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
    have h4 : 4 ≤ Nat.card F ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq 2
    exact Nat.not_prime_mul (by omega) (by
      have : 3 * 7 ≤ (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega)

end Factors

section StepOne

variable {V : Type} [CommGroup V] [Finite V]

theorem twoA_le_ffJ (hV : ∀ v : V, v ^ 2 = 1)
    {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (hτX : τ ∈ X)
    (hL₁X : L₁ ≤ X) (hL₂X : L₂ ≤ X) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hn : ∀ x ∈ X, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) : L₁ ≤ ffJ X ∧ L₂ ≤ ffJ X := by
  set J := ffJ X with hJ
  have hJX : J ≤ X := B6.ffJ_le X
  have hXJ : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J := fun x hx j hj =>
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hx) j).mp hj
  have hJ0 : J ≠ ⊥ := InternalSec.ffJ_ne_bot_of_isFFModule hV hFF
  have hLX : L₁ ⊔ L₂ ≤ X := sup_le hL₁X hL₂X
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have h12 : L₁ ≤ J → L₂ ≤ J := by
    intro h y hy
    rw [hτ] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hXJ τ hτX x (h hx)
  have h21 : L₂ ≤ J → L₁ ≤ J := by
    intro h x hx
    have hmem : τ * x * τ⁻¹ ∈ L₂ := by rw [hτ]; exact ⟨x, hx, rfl⟩
    have := hXJ τ⁻¹ (X.inv_mem hτX) _ (h hmem)
    simpa [mul_assoc] using this
  by_contra hcon
  have hL₁J : ¬ L₁ ≤ J := fun h => hcon ⟨h, h12 h⟩
  have hL₂J : ¬ L₂ ≤ J := fun h => hL₁J (h21 h)
  have hMn₁ : ∀ m ∈ L₁ ⊔ L₂, ∀ k ∈ L₁, m * k * m⁻¹ ∈ L₁ :=
    InternalSec.conj_mem_of_mem_sup_of_commute hcomm
  have hMn₂ : ∀ m ∈ L₁ ⊔ L₂, ∀ k ∈ L₂, m * k * m⁻¹ ∈ L₂ := by
    rw [sup_comm]
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc'
  have hJ₁ := twoA_commute_of_not_le hJX hXJ hLX hn le_sup_left hMn₁ hq₁ hL₁J
  have hJ₂ := twoA_commute_of_not_le hJX hXJ hLX hn le_sup_right hMn₂ hq₂ hL₂J
  have hJL : ∀ j ∈ J, ∀ l ∈ L₁ ⊔ L₂, j * l = l * j := by
    intro j hj l hl
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hcomm)).1 hl
    calc j * (a * b) = (j * a) * b := (mul_assoc _ _ _).symm
      _ = (a * j) * b := by rw [hJ₁ j hj a ha]
      _ = a * (j * b) := mul_assoc _ _ _
      _ = a * (b * j) := by rw [hJ₂ j hj b hb]
      _ = a * b * j := (mul_assoc _ _ _).symm
  have hnil : Group.IsNilpotent ↥J :=
    twoA_isNilpotent_of_central_two_quot (A := (L₁ ⊔ L₂) ⊓ J)
      (fun a ha n hn' => (hJL n hn' a ha.1).symm)
      (fun n hn' => by
        obtain ⟨e, he⟩ := h2 n (hJX hn')
        exact ⟨e, he, J.pow_mem hn' _⟩)
  have hodd := B1Red.odd_orderOf_of_nilpotent_normal hJX hXJ hO2
  refine hJ0 (le_bot_iff.1 ?_)
  refine iSup₂_le fun A hA a ha => ?_
  have ha2 : a ^ 2 = 1 := hA.2.2.1.2 a ha
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
  have hodd' := hodd a (B6.le_ffJ hA ha)
  have hcop : Nat.Coprime (orderOf a) 2 := Nat.coprime_two_right.2 hodd'
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd))

end StepOne

section Cases

variable {V : Type} [CommGroup V] [Finite V]

private structure TwoCompData (J L₁ L₂ : Subgroup (MulAut V)) : Prop where
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  q₁ : CFSG.IsQuasisimple ↥L₁
  q₂ : CFSG.IsQuasisimple ↥L₂
  le₁ : L₁ ≤ J
  le₂ : L₂ ≤ J
  norm : ∀ x ∈ J, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂
  two : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂
  card₁ : 504 ≤ Nat.card ↥L₁
  card₂ : 504 ≤ Nat.card ↥L₂

variable {J L₁ L₂ : Subgroup (MulAut V)}

omit [Finite V] in
private theorem TwoCompData.false_of_case1 (P : TwoCompData J L₁ L₂)
    (hF : CFSG.IsQuasisimple ↥(quasithinGenFitting J)) : False := by
  set F := quasithinGenFitting J with hFdef
  have hFJ : F ≤ J := quasithinGenFitting_le J
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le P.le₁ P.le₂
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hL₁n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ :=
    InternalSec.conj_mem_of_mem_sup_of_commute P.comm
  have hL₂n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := by
    rw [sup_comm]
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc'
  have hLJn : ((L₁ ⊔ L₂).subgroupOf J).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g g.2 n hn⟩
  have hcomp : ∀ {A : Subgroup (MulAut V)}, A ≤ L₁ ⊔ L₂ →
      (∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ A, x * k * x⁻¹ ∈ A) → CFSG.IsQuasisimple ↥A → A ≤ F := by
    intro A hAL hAn hAq
    have hA : (A.subgroupOf (L₁ ⊔ L₂)).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hAn g g.2 n hn⟩
    have hsub : CFSG.Open.IsSubnormal A J :=
      CFSG.Open.IsSubnormal.step hAL hA
        (CFSG.Open.IsSubnormal.step hLJ hLJn (CFSG.Open.IsSubnormal.refl J))
    have hc : CFSG.Open.IsComponentOf A J :=
      ⟨hAL.trans hLJ, hsub, B1Red.isQuasisimple_to_open hAq⟩
    exact (le_sSup (show A ∈ {K | CFSG.Open.IsComponentOf K J} from hc)).trans le_sup_right
  have hL₁F : L₁ ≤ F := hcomp le_sup_left hL₁n P.q₁
  have hL₂F : L₂ ≤ F := hcomp le_sup_right hL₂n P.q₂
  have hLF : L₁ ⊔ L₂ ≤ F := sup_le hL₁F hL₂F
  have hLFn : ((L₁ ⊔ L₂).subgroupOf F).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g (hFJ g.2) n hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hF) ((L₁ ⊔ L₂).subgroupOf F) with hcen | htop
  · refine InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb => ?_
    have h1 : (⟨a, hL₁F ha⟩ : ↥F) ∈ Subgroup.center ↥F :=
      hcen (show (⟨a, hL₁F ha⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F from Subgroup.mem_sup_left ha)
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hL₁F hb⟩
    exact (congrArg Subtype.val h2).symm
  · have hFL : F ≤ L₁ ⊔ L₂ := fun x hx => by
      have : (⟨x, hx⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F := htop ▸ Subgroup.mem_top _
      exact this
    have h1 : L₁ = F := twoA_eq_of_normal_of_isQuasisimple hL₁F
      (fun x hx k hk => hL₁n x (hFL hx) k hk) P.q₁ hF
    have h2 : L₂ = F := twoA_eq_of_normal_of_isQuasisimple hL₂F
      (fun x hx k hk => hL₂n x (hFL hx) k hk) P.q₂ hF
    have h12 : L₁ = L₂ := h1.trans h2.symm
    exact InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb =>
      P.comm a ha b (h12 ▸ hb)

private theorem TwoCompData.false_of_case4 (P : TwoCompData J L₁ L₂) (h4 : B56Case4 J) : False := by
  obtain ⟨G₁, G₂, t, hJt, -, hcomm, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htN := InternalSec.mem_normalizer_sup ht₁ ht₂
  have h1 : L₁ ≤ ⁅J, J⁆ := InternalSec.le_commutator_of_perfect P.le₁ P.q₁.1
  rw [hJt] at h1
  have hL₁N : L₁ ≤ G₁ ⊔ G₂ := h1.trans (InternalSec.commutator_le_of_zpowers htN)
  have hsol : Group.IsSolvable ↥G₂ := by
    have := isCyclic_of_prime_card hc₂
    infer_instance
  have hL₁G₁ : L₁ ≤ G₁ := twoA_le_of_perfect_of_isSolvable hcomm hL₁N P.q₁.1 hsol
  have hle := Subgroup.card_le_of_le hL₁G₁
  have hcard : Nat.card ↥G₁ = 360 := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have := P.card₁
  omega

private theorem TwoCompData.false_of_case5 (P : TwoCompData J L₁ L₂) (h5 : B56Case5 J) : False := by
  obtain ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, -⟩ := h5
  have hs : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd (m := 1) (by simp) odd_one
  have hs' : IsSimpleGroup ↥G₁ := e₁.isSimpleGroup
  have hcard : Nat.card ↥G₁ = 168 := by
    rw [Nat.card_congr e₁.toEquiv, twoA_card_statedSL_three, Nat.card_zmod]
    norm_num
  have hq : CFSG.IsQuasisimple ↥G₁ := twoA_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
  have hn₁ : ∀ x ∈ J, ∀ g ∈ G₁, x * g * x⁻¹ ∈ G₁ := fun x hx g hg =>
    InternalSec.conj_mem_of_mem_sup_of_commute hc x (by rw [hsup]; exact hx) g hg
  rcases twoA_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two hG₁J hn₁ hq with h | h
  · have := P.card₁
    rw [← h, hcard] at this
    omega
  · have := P.card₂
    rw [← h, hcard] at this
    omega

private theorem TwoCompData.case3 (P : TwoCompData J L₁ L₂) (h3 : B56Case3 J) :
    J = L₁ ⊔ L₂ ∧ ∃ W₁ W₂ : Subgroup V, fixV J ≤ W₁ ∧ fixV J ≤ W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧
      W₁ ⊓ W₂ = fixV J ∧ B56Piece L₁ W₁ (fixV J) ∧ B56Piece L₂ W₂ (fixV J) := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, W₁, W₂, hW₁, hW₂, -, -, hWsup, hWinf, hp₁, hp₂⟩ := h3
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hne : ∀ L : Subgroup (MulAut V), CFSG.IsQuasisimple ↥L → L ≠ ⊥ := by
    intro L hL hbot
    have : Nontrivial ↥L :=
      CFSG.ComponentClassification.Quasisimple.nontrivial (B1Red.isQuasisimple_to_open hL)
    have : Subsingleton ↥L := by rw [hbot]; infer_instance
    exact not_subsingleton ↥L ‹_›
  have key : ∀ {A B : Subgroup (MulAut V)}, A ⊔ B = J → A ⊓ B = ⊥ →
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → B56FactorList ↥A → A = L₁ ∨ A = L₂ := by
    intro A B hsupAB hinfAB hcAB hfA
    have hcBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcAB a ha b hb).symm
    have hAJ : A ≤ J := by rw [← hsupAB]; exact le_sup_left
    rcases twoA_fac_of_factorList hfA with ⟨K, hKA, hKn, hKq, hK⟩ | ⟨hsol, h3dvd⟩
    · have hKJn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
        intro x hx k hk
        have hx' : x ∈ A ⊔ B := by rw [hsupAB]; exact hx
        obtain ⟨a, ha, b, hb, rfl⟩ :=
          (B19Aux.mem_sup_iff_of_le_normalizer
            (InternalSec.le_normalizer_of_commute hcAB)).1 hx'
        have hbk : b * k = k * b := (hcAB k (hKA hk) b hb).symm
        have e : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
          calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
            _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [hbk]
            _ = a * k * a⁻¹ := by group
        rw [e]
        exact hKn a ha k hk
      have hKL := twoA_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two (hKA.trans hAJ) hKJn
        hKq
      have hKA' : K = A := by
        rcases hK with h' | hlt
        · exact h'
        · exfalso
          rcases hKL with h | h
          · rw [h] at hlt
            have := P.card₁
            omega
          · rw [h] at hlt
            have := P.card₂
            omega
      rcases hKL with h | h
      · exact Or.inl (hKA'.symm.trans h)
      · exact Or.inr (hKA'.symm.trans h)
    · exfalso
      have hJBA : J = B ⊔ A := by rw [← hsupAB, sup_comm]
      have hL₁B : L₁ ≤ B :=
        twoA_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₁) P.q₁.1 hsol
      have hL₂B : L₂ ≤ B :=
        twoA_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₂) P.q₂.1 hsol
      have hLB : L₁ ⊔ L₂ ≤ B := sup_le hL₁B hL₂B
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
      obtain ⟨e, he⟩ := P.two (x : MulAut V) (hAJ x.2)
      have hxe : (x : MulAut V) ^ 2 ^ e ∈ A ⊓ B := ⟨A.pow_mem x.2 _, hLB he⟩
      rw [hinfAB, Subgroup.mem_bot] at hxe
      have hord : orderOf (x : MulAut V) = 3 := by rw [Subgroup.orderOf_coe, hx]
      have hdvd : 3 ∣ 2 ^ e := hord ▸ orderOf_dvd_of_pow_eq_one hxe
      have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      omega
  have hG₁ := key hsup hinf hc hf₁
  have hG₂ := key ((sup_comm _ _).trans hsup) ((inf_comm _ _).trans hinf) hc' hf₂
  have hq₁ := P.q₁
  have hq₂ := P.q₂
  rcases hG₁ with h1 | h1 <;> rcases hG₂ with h2 | h2
  · exfalso
    rw [h1, h2, inf_idem] at hinf
    exact hne L₁ hq₁ hinf
  · rw [h1, h2] at hsup
    rw [h1] at hp₁
    rw [h2] at hp₂
    exact ⟨hsup.symm, W₁, W₂, hW₁, hW₂, hWsup, hWinf, hp₁, hp₂⟩
  · rw [h1, h2] at hsup
    rw [h1] at hp₁
    rw [h2] at hp₂
    refine ⟨hsup.symm.trans (sup_comm _ _), W₂, W₁, hW₂, hW₁, (sup_comm _ _).trans hWsup,
      (inf_comm _ _).trans hWinf, hp₂, hp₁⟩
  · exfalso
    rw [h1, h2, inf_idem] at hinf
    exact hne L₂ hq₂ hinf

end Cases

theorem twoB56_of_ffModule {V : Type} [CommGroup V] [Finite V] (h56 : AsB56)
    (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (hτX : τ ∈ X)
    (hL₁X : L₁ ≤ X) (hL₂X : L₂ ≤ X) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hn : ∀ x ∈ X, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hcard : 504 ≤ Nat.card ↥L₁)
    (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) (hB53 : B53Hyp (ffJ X)) :
    TwoB56 X L₁ L₂ := by
  obtain ⟨hL₁J, hL₂J⟩ := twoA_le_ffJ hV hτX hL₁X hL₂X hcomm hn hτ h2 hq₁ hq₂ hO2 hFF
  have hJX : ffJ X ≤ X := B6.ffJ_le X
  have hcard₂ : 504 ≤ Nat.card ↥L₂ := by
    rw [hτ, Subgroup.card_map_of_injective (MulAut.conj τ).injective]
    exact hcard
  have P : TwoCompData (ffJ X) L₁ L₂ :=
    ⟨hcomm, hq₁, hq₂, hL₁J, hL₂J, fun x hx l hl => hn x (hJX hx) l hl,
      fun x hx => h2 x (hJX hx), hcard, hcard₂⟩
  have hcases := h56 V hV (ffJ X) (InternalSec.ffJ_ne_bot_of_isFFModule hV hFF) hB53
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | h3 | h4 | h5
  · exact (P.false_of_case1 h1.1).elim
  · exact (InternalSec.not_le_perm_three hq₁ hL₁J e).elim
  · obtain ⟨hJL, W₁, W₂, hW₁, hW₂, hWs, hWi, hp₁, hp₂⟩ := P.case3 h3
    unfold TwoB56
    rw [← hJL]
    exact ⟨rfl, W₁, W₂, hW₁, hW₂, hWs, hWi, hp₁, hp₂⟩
  · exact (P.false_of_case4 h4).elim
  · exact (P.false_of_case5 h5).elim

end S153M

end CFSG.Quasithin
