module

public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Four
public import CFSG.LocalAnalysis.WeakClosure81.W19KSeries
public import CFSG.Quasithin.Background.E1SolvProduct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private def commModSubgroup (O : Subgroup G) (x : G) : Subgroup G where
  carrier := {y | y ∈ normalizer (O : Set G) ∧ x * y * x⁻¹ * y⁻¹ ∈ O}
  mul_mem' := by
    rintro y₁ y₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨Subgroup.mul_mem _ h₁ h₂, ?_⟩
    have h3 : y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 h₁ _).1 h₂'
    have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
        (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
    rw [e]
    exact O.mul_mem h₁' h3
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  inv_mem' := by
    rintro y ⟨h₁, h₁'⟩
    refine ⟨Subgroup.inv_mem _ h₁, ?_⟩
    have h3 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * (y⁻¹)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h₁) _).1 (O.inv_mem h₁')
    have e : x * y⁻¹ * x⁻¹ * (y⁻¹)⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * (y⁻¹)⁻¹ := by group
    rw [e]
    exact h3

private theorem le_commModSubgroup_of_le {O : Subgroup G} {x : G} (hx : x ∈ normalizer (O : Set G))
    {Y : Subgroup G} (hYO : Y ≤ normalizer (O : Set G))
    (hY : ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ O) : Y ≤ commModSubgroup O x :=
  fun y hy => ⟨hYO hy, hY y hy⟩

private theorem normalizer_le_of_uniqueMax' {M Y D : Subgroup G} (huniq : UniqueMax M Y)
    (hD : D ≠ ⊥) (hD2 : IsPGroup 2 D) (hYD : Y ≤ normalizer (D : Set G)) :
    normalizer (D : Set G) ≤ M := by
  classical
  have hloc : IsTwoLocal (normalizer (D : Set G)) := ⟨D, hD, hD2, rfl⟩
  set S : Set (Subgroup G) := {N | IsTwoLocal N ∧ normalizer (D : Set G) ≤ N} with hS
  obtain ⟨N, ⟨hN, hDN⟩, hmax⟩ :=
    Set.exists_max_image S (fun N => Nat.card N) (Set.toFinite S) ⟨_, hloc, le_rfl⟩
  have hNmax : rankThreeIsMaxTwoLocal N := ⟨hN, fun K hK hNK =>
    (Subgroup.eq_of_le_of_card_ge hNK (hmax K ⟨hK, hDN.trans hNK⟩)).symm⟩
  have hmem : N ∈ calMOf Y := ⟨hNmax, hYD.trans hDN⟩
  have hcal : calMOf Y = {M} := huniq
  rw [hcal, Set.mem_singleton_iff] at hmem
  rw [← hmem]
  exact hDN

theorem le_normalizer_K0193 {D : Data G} {X A K : Subgroup G} (hK : K ≤ X ⊔ D.T) :
    K ≤ normalizer (K0193 D X A K : Set G) := by
  intro k hk
  apply E1.mem_normalizer_of_conj_mem
  intro y hy
  have hle : K0193 D X A K ≤ (K0193 D X A K).comap (MulAut.conj k).toMonoidHom := by
    refine sup_le (iSup₂_le fun k' hk' z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_comap]
      refine Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem (k' * k⁻¹)
        (Subgroup.mem_iSup_of_mem (Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk)) ?_))
      rw [mem_conjSubgroup_iff] at hz ⊢
      have e : k' * k⁻¹ * ((MulAut.conj k).toMonoidHom z) * (k' * k⁻¹)⁻¹ = k' * z * k'⁻¹ := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
      rw [e]
      exact hz
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hK hk)) z).1 hz)
  have := hle hy
  rwa [Subgroup.mem_comap] at this

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem pow_mem_N (c : MinCex193 D V₀ V p X) {x : G} (hx : x ∈ X ⊔ pCoreOf 2 (X ⊔ D.T)) :
    ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 (X ⊔ D.T) :=
  exists_pow_mem_of_mem_sup_pGroup c.hyp.isPGroup
    (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) hx

theorem N_inf_T_le (c : MinCex193 D V₀ V p X) :
    (X ⊔ pCoreOf 2 (X ⊔ D.T)) ⊓ D.T ≤ pCoreOf 2 (X ⊔ D.T) := by
  intro x hx
  obtain ⟨k, hk⟩ := c.pow_mem_N hx.1
  obtain ⟨j, hj⟩ := D.sylowM.isPGroup ⟨x, hx.2⟩
  exact E1.mem_of_pow_mem_two_p c.hyp.prime c.hyp.odd hk (by
    have : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [this]
    exact Subgroup.one_mem _)

theorem inf_K_ne_bot (c : MinCex193 D V₀ V p X) {g : G} {K : Subgroup G}
    (hc : Conf196 D V X g K) : X ⊓ K ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  obtain ⟨x, hxK, hxp⟩ := hc.exists_orderOf_eq c
  set O := pCoreOf 2 (X ⊔ D.T) with hO
  have hXO : X ≤ normalizer (O : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hTN : D.T ≤ normalizer ((X ⊔ O : Subgroup G) : Set G) :=
    le_sup_right.trans c.le_normalizer_sup_pCoreOf
  have hxH : x ∈ X ⊔ D.T := hc.le_H hxK
  have hxN : x ∈ X ⊔ O := by
    have hHle : X ⊔ D.T ≤ (X ⊔ O) ⊔ D.T := sup_le_sup_right le_sup_left _
    have hx' : x ∈ (X ⊔ O) ⊔ D.T := hHle hxH
    obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup D.sylowM.isPGroup hTN hx'
    exact E1.mem_of_pow_mem_of_coprime (a := 2 ^ j) (b := p)
      (Nat.Coprime.pow_left j
        ((Nat.coprime_primes Nat.prime_two c.hyp.prime).2 (Ne.symm c.hyp.odd))) hj
      (by rw [← hxp, pow_orderOf_eq_one]; exact Subgroup.one_mem _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X O hXO] at hxN
  obtain ⟨x₀, hx₀, o, ho, rfl⟩ := hxN
  have hoK : o ∈ K := hc.pCoreOf_le_K c ho
  have hx₀K : x₀ ∈ K := by
    have := Subgroup.mul_mem _ hxK (Subgroup.inv_mem _ hoK)
    simpa using this
  intro hbot
  have hmem : x₀ ∈ X ⊓ K := ⟨hx₀, hx₀K⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  subst hmem
  have hxp' : orderOf o = p := by simpa using hxp
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ D.T)) ⟨o, ho⟩
  have hj' : o ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hdvd : p ∣ 2 ^ j := by
    rw [← hxp']
    exact orderOf_dvd_of_pow_eq_one hj'
  exact c.hyp.odd
    ((Nat.prime_dvd_prime_iff_eq c.hyp.prime Nat.prime_two).1 (c.hyp.prime.dvd_of_dvd_pow hdvd))

theorem card_le_of_isCyclic (c : MinCex193 D V₀ V p X) {Y : Subgroup G} (hY : Y ≤ X)
    (hcyc : IsCyclic ↥Y) : Nat.card ↥Y ≤ p := by
  have h1 : Monoid.exponent ↥Y ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
    Subtype.ext (by simpa using c.hyp.exponent (y : G) (hY y.2))
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd c.hyp.prime.pos h1

theorem commute_of_card_le (c : MinCex193 D V₀ V p X) (hcard : Nat.card ↥X ≤ p ^ 2) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 c.hyp.isPGroup
  have hn2 : n ≤ 2 := by
    have : p ^ n ≤ p ^ 2 := hn ▸ hcard
    exact (Nat.pow_le_pow_iff_right c.hyp.prime.one_lt).1 this
  have hn2' : n = 2 := by
    by_contra hne
    apply c.hyp.noncyclic
    interval_cases n
    · haveI : Subsingleton ↥X := by
        rw [pow_zero] at hn
        exact (Nat.card_eq_one_iff_unique.1 hn).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (p := p) (by simpa using hn)
    · exact absurd rfl hne
  subst hn2'
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hn
  intro a ha b hb
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : ↥X) ⟨b, hb⟩)

theorem isCyclic_inf_normalizer_wClos (c : MinCex193 D V₀ V p X) :
    IsCyclic ↥(X ⊓ normalizer (E3.wClos V 0 D.T : Set G)) := by
  by_contra hnc
  have huniq := c.hyp.uniqueMax (X ⊓ normalizer (E3.wClos V 0 D.T : Set G)) inf_le_left hnc
  have hW : E3.wClos V 0 D.T ≠ ⊥ := E3.wClos_ne_bot c.setting.isElemAbelian c.V_le_T
    (by have := c.three_le_rk; omega)
  have hW2 : IsPGroup 2 (E3.wClos V 0 D.T) := D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T)
  exact c.fail (Or.inl (normalizer_le_of_uniqueMax' huniq hW hW2 inf_le_right))

theorem exists_mul_of_mem_X (c : MinCex193 D V₀ V p X) {x : G} (hx : x ∈ X) :
    ∃ l ∈ X ⊓ (E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ⊔ D.T),
      ∃ w ∈ X ⊓ normalizer (E3.wClos V 0 D.T : Set G), x = l * w := by
  have hxH : x ∈ X ⊔ D.T := Subgroup.mem_sup_left hx
  obtain ⟨e, he, n, hn, hxen⟩ := E1.eGen_mul_normalizer_of_isSolvable_subgroup
    (le_sup_right : D.T ≤ X ⊔ D.T) c.hyp.isSolvable c.hyp.isSylowIn_T
    (E3.isInvColl_gammaSet c.setting.isElemAbelian 0 (X ⊔ D.T)) ⟨x, hxH⟩
  rw [E3.weakClosure_gammaSet (le_sup_right : D.T ≤ X ⊔ D.T)] at hn
  have hnH : n ∈ ((X ⊔ D.T : Subgroup G) : Set G) := hn.2
  have hHTX : ((X ⊔ D.T : Subgroup G) : Set G) = (D.T : Set G) * (X : Set G) := by
    rw [c.hyp.coe_sup_eq_mul, c.hyp.perm]
  rw [hHTX] at hnH
  obtain ⟨t, ht, w, hw, rfl⟩ := hnH
  have htW : t ∈ normalizer (E3.wClos V 0 D.T : Set G) :=
    E3.normalizer_le_normalizer_wClos D.T (Subgroup.le_normalizer ht)
  have hwW : w ∈ normalizer (E3.wClos V 0 D.T : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ htW) hn.1
    simpa using this
  have hxe : x = e * t * w := by rw [mul_assoc]; exact hxen
  have hl : e * t = x * w⁻¹ := by rw [hxe]; group
  refine ⟨e * t, ⟨?_, Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right ht)⟩,
    w, ⟨hw, hwW⟩, hxe⟩
  rw [hl]
  exact X.mul_mem hx (X.inv_mem hw)

theorem comm_wClos_le (c : MinCex193 D V₀ V p X) {x : G}
    (hx : x ∈ X ⊓ normalizer (E3.wClos V 0 D.T : Set G)) {w : G}
    (hw : w ∈ E3.wClos V 0 D.T) : x * w * x⁻¹ * w⁻¹ ∈ pCoreOf 2 (X ⊔ D.T) := by
  have hwT : w ∈ D.T := E3.wClos_le 0 D.T hw
  have h1 : x * w * x⁻¹ * w⁻¹ ∈ E3.wClos V 0 D.T :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hx.2 w).1 hw) (Subgroup.inv_mem _ hw)
  have hxN : x ∈ X ⊔ pCoreOf 2 (X ⊔ D.T) := Subgroup.mem_sup_left hx.1
  have h2 : x * w * x⁻¹ * w⁻¹ ∈ X ⊔ pCoreOf 2 (X ⊔ D.T) := by
    have hwx : w * x⁻¹ * w⁻¹ ∈ X ⊔ pCoreOf 2 (X ⊔ D.T) :=
      (Subgroup.mem_normalizer_iff.1
        (c.le_normalizer_sup_pCoreOf (Subgroup.mem_sup_right hwT)) x⁻¹).1
          (Subgroup.inv_mem _ hxN)
    have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hxN hwx
  exact c.N_inf_T_le ⟨h2, E3.wClos_le 0 D.T h1⟩

theorem inf_normalizer_wClos_le_normalizer_K0 (c : MinCex193 D V₀ V p X)
    (hab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {g : G} {K : Subgroup G} (hc : Conf196 D V X g K) :
    X ⊓ normalizer (E3.wClos V 0 D.T : Set G) ≤
      normalizer (K0193 D X (conjSubgroup V g) K : Set G) := by
  intro x hx
  have hHO : X ⊔ D.T ≤ normalizer (pCoreOf 2 (X ⊔ D.T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hxO : x ∈ normalizer (pCoreOf 2 (X ⊔ D.T) : Set G) := hHO (Subgroup.mem_sup_left hx.1)
  have hOC : pCoreOf 2 (X ⊔ D.T) ≤ commModSubgroup (pCoreOf 2 (X ⊔ D.T)) x :=
    le_commModSubgroup_of_le hxO Subgroup.le_normalizer fun y hy =>
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hxO y).1 hy) (Subgroup.inv_mem _ hy)
  have hXC : X ≤ commModSubgroup (pCoreOf 2 (X ⊔ D.T)) x :=
    le_commModSubgroup_of_le hxO (le_sup_left.trans hHO) fun a ha => by
      have : x * a * x⁻¹ * a⁻¹ = 1 := by rw [hab x hx.1 a ha]; group
      rw [this]
      exact Subgroup.one_mem _
  have hNC : X ⊔ pCoreOf 2 (X ⊔ D.T) ≤ commModSubgroup (pCoreOf 2 (X ⊔ D.T)) x :=
    sup_le hXC hOC
  have hWC : E3.wClos V 0 D.T ≤ commModSubgroup (pCoreOf 2 (X ⊔ D.T)) x :=
    le_commModSubgroup_of_le hxO
      ((E3.wClos_le 0 D.T).trans (le_sup_right.trans hHO)) fun w hw => c.comm_wClos_le hx hw
  have hK0 : K0193 D X (conjSubgroup V g) K ≤ commModSubgroup (pCoreOf 2 (X ⊔ D.T)) x := by
    refine sup_le (iSup₂_le fun k hk y hy => ?_) hOC
    rw [mem_conjSubgroup_iff] at hy
    have hkH : k ∈ ((X ⊔ D.T : Subgroup G) : Set G) := hc.le_H hk
    rw [c.hyp.coe_sup_eq_mul, c.hyp.perm] at hkH
    obtain ⟨t, ht, x₁, hx₁, rfl⟩ := hkH
    have hA : conjSubgroup V g ∈ E3.gammaSet V 0 D.T := ⟨hc.le_T, g, le_rfl, E3.mQuot_self _⟩
    have hAt : conjSubgroup (conjSubgroup V g) t ∈ E3.gammaSet V 0 D.T := by
      refine ⟨fun z hz => ?_, g * t, by rw [conjSubgroup_conjSubgroup], ?_⟩
      · rw [mem_conjSubgroup_iff] at hz
        have h1 := D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) (hc.le_T hz)) ht
        simpa [mul_assoc] using h1
      · rw [conjSubgroup_conjSubgroup]
        exact E3.mQuot_self _
    set a' : G := t⁻¹ * (t * x₁ * y * (t * x₁)⁻¹) * t with ha'
    have ha'W : a' ∈ E3.wClos V 0 D.T := by
      refine E3.le_wClos hAt ?_
      rw [mem_conjSubgroup_iff]
      have e : t * a' * t⁻¹ = t * x₁ * y * (t * x₁)⁻¹ := by rw [ha']; group
      rw [e]
      exact hy
    have hn : a'⁻¹ * x₁⁻¹ * a' * x₁ ∈ X ⊔ pCoreOf 2 (X ⊔ D.T) := by
      have ha'T : a' ∈ D.T := E3.wClos_le 0 D.T ha'W
      have h1 : a'⁻¹ * x₁⁻¹ * (a'⁻¹)⁻¹ ∈ X ⊔ pCoreOf 2 (X ⊔ D.T) :=
        (Subgroup.mem_normalizer_iff.1 (c.le_normalizer_sup_pCoreOf
          (Subgroup.mem_sup_right (D.T.inv_mem ha'T))) x₁⁻¹).1
            (Subgroup.inv_mem _ (Subgroup.mem_sup_left hx₁))
      have e : a'⁻¹ * x₁⁻¹ * a' * x₁ = (a'⁻¹ * x₁⁻¹ * (a'⁻¹)⁻¹) * x₁ := by group
      rw [e]
      exact Subgroup.mul_mem _ h1 (Subgroup.mem_sup_left hx₁)
    have hya : y = a' * (a'⁻¹ * x₁⁻¹ * a' * x₁) := by rw [ha']; group
    rw [hya]
    exact Subgroup.mul_mem _ (hWC ha'W) (hNC hn)
  apply E1.mem_normalizer_of_conj_mem
  intro y hy
  have hyC := hK0 hy
  have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyC.2) hy

theorem sup_eq_eGen_sup_of_card (c : MinCex193 D V₀ V p X)
    (h4 : ∀ (g : G) (K : Subgroup G), Conf196 D V X g K →
      Nat.card ↥(X ⊓ J193 D X (conjSubgroup V g) K) = p) :
    E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ⊔ D.T = X ⊔ D.T := by
  classical
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  have hLH : E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ⊔ D.T ≤ X ⊔ D.T :=
    sup_le (E1.eGen_le 1 _ _ _) le_sup_right
  by_contra hne
  have hlt : E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ⊔ D.T < X ⊔ D.T :=
    lt_of_le_of_ne hLH hne
  set L := E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ⊔ D.T with hL
  set P := X ⊓ normalizer (E3.wClos V 0 D.T : Set G) with hP
  have hcycL : IsCyclic ↥(X ⊓ L) :=
    c.cyclic L le_sup_right hlt (X ⊓ L) inf_le_right (c.hyp.isPGroup.to_le inf_le_left)
  have hcardL : Nat.card ↥(X ⊓ L) ≤ p := c.card_le_of_isCyclic inf_le_left hcycL
  have hcycP : IsCyclic ↥P := c.isCyclic_inf_normalizer_wClos
  have hcardP : Nat.card ↥P ≤ p := c.card_le_of_isCyclic inf_le_left hcycP
  have hsurj : Function.Surjective
      (fun q : ↥(X ⊓ L) × ↥P => (⟨(q.1 : G) * (q.2 : G),
        X.mul_mem q.1.2.1 q.2.2.1⟩ : ↥X)) := by
    rintro ⟨x, hx⟩
    obtain ⟨l, hl, w, hw, hxlw⟩ := c.exists_mul_of_mem_X hx
    exact ⟨(⟨l, hl⟩, ⟨w, hw⟩), Subtype.ext hxlw.symm⟩
  have hcardX : Nat.card ↥X ≤ p ^ 2 := by
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod] at h1
    calc Nat.card ↥X ≤ Nat.card ↥(X ⊓ L) * Nat.card ↥P := h1
      _ ≤ p * p := Nat.mul_le_mul hcardL hcardP
      _ = p ^ 2 := (sq p).symm
  have hab := c.commute_of_card_le hcardX
  by_cases hex : ∃ (g : G) (K : Subgroup G), Conf196 D V X g K
  · obtain ⟨g, K, hc⟩ := hex
    have hAΩ : conjSubgroup V g ∈ E3.gammaSet V 0 (X ⊔ D.T) :=
      ⟨hc.le_T.trans le_sup_right, g, le_rfl, E3.mQuot_self _⟩
    have hKL : K ≤ L :=
      (E1.le_eGen hAΩ hc.le_T hc.isE).trans le_sup_left
    have hKne := c.inf_K_ne_bot hc
    have hge : p ≤ Nat.card ↥(X ⊓ K) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (c.hyp.isPGroup.to_le (inf_le_left : X ⊓ K ≤ X))
      rw [hn]
      have hn0 : n ≠ 0 := by
        rintro rfl
        apply hKne
        rw [pow_zero] at hn
        exact Subgroup.card_eq_one.1 hn
      exact Nat.le_self_pow hn0 p
    have heq : X ⊓ K = X ⊓ L :=
      Subgroup.eq_of_le_of_card_ge (inf_le_inf_left X hKL) (hcardL.trans hge)
    have hPK0 := c.inf_normalizer_wClos_le_normalizer_K0 hab hc
    have hKK0 := le_normalizer_K0193 (D := D) (X := X) (A := conjSubgroup V g) hc.le_H
    have hXJ : X ≤ J193 D X (conjSubgroup V g) K := by
      intro x hx
      obtain ⟨l, hl, w, hw, rfl⟩ := c.exists_mul_of_mem_X hx
      have hlK : l ∈ K := by
        have : l ∈ X ⊓ K := by rw [heq]; exact hl
        exact this.2
      exact ⟨Subgroup.mem_sup_left hx, Subgroup.mul_mem _ (hKK0 hlK) (hPK0 hw)⟩
    have h4' := h4 g K hc
    rw [inf_eq_left.2 hXJ] at h4'
    exact c.hyp.noncyclic (isCyclic_of_prime_card (p := p) h4')
  ·
    have hE : E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_)
      exfalso
      obtain ⟨-, g, hAg, hm⟩ := hA
      have hAeq : A = conjSubgroup V g :=
        (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup c.isPGroup_V g) hAg).1 hm
      subst hAeq
      exact hex ⟨g, K, ⟨hAT, hK⟩⟩
    have hLT : L = D.T := by rw [hL, hE, bot_sup_eq]
    have hXL : X ⊓ L = ⊥ := by rw [hLT]; exact c.hyp.inf_T_eq_bot
    have hXP : X ≤ P := by
      intro x hx
      obtain ⟨l, hl, w, hw, rfl⟩ := c.exists_mul_of_mem_X hx
      rw [hXL, Subgroup.mem_bot] at hl
      rw [hl, one_mul]
      exact hw
    have hPX : P = X := le_antisymm inf_le_left hXP
    apply c.hyp.noncyclic
    have h := c.isCyclic_inf_normalizer_wClos
    rwa [← hP, hPX] at h

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
