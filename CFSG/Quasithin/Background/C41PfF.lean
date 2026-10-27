module

public import CFSG.Quasithin.Background.C41PfE
public import CFSG.Quasithin.Background.SmithC27Perm
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace C41Pf

theorem isSolvable_of_card_eq_pow_mul_pow {Y : Type*} [Group Y] [Finite Y] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card Y = p ^ a * q ^ b) :
    Group.IsSolvable Y := by
  have := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem isSolvable_of_isMaxParabolic2_g2 (hG2 : CFSG.Quasithin.H13.Lem1211NNG2) {Y : Type}
    [Group Y] [Finite Y] {X P : Subgroup Y} (hX : IsG2Two ↥X) (hP : IsMaxParabolic2 X P) :
    Group.IsSolvable ↥P := by
  have h7 := hG2 Y X P hX hP
  have hdvd : Nat.card ↥P ∣ 2 ^ 6 * 3 ^ 3 * 7 := by
    have := Subgroup.card_dvd_of_le hP.1.1
    rwa [hX.1] at this
  have hcop : Nat.Coprime (Nat.card ↥P) 7 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7))
  have h1 : Nat.card ↥P ∣ 2 ^ 6 * 3 ^ 3 := hcop.dvd_of_dvd_mul_right hdvd
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Nat.dvd_mul.mp h1
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd₁
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd₂
  exact isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hd.symm

variable {G : Type} [Group G] [Finite G]

section Common

omit [Finite G] in
theorem autOn_le_autOn {X Y V : Subgroup G} (h : X ≤ Y) : autOn X V ≤ autOn Y V :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem perfect_autOn {X V : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hX : ⁅X, X⁆ = X) : ⁅autOn X V, autOn X V⁆ = autOn X V := by
  unfold autOn
  rw [← Subgroup.map_commutator, commutator_subgroupOf hXN hXN, hX]

omit [Finite G] in
theorem le_centralizer_of_autOn_eq_bot {X V : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (h : autOn X V = ⊥) :
    X ≤ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.S153D.le_centralizer_of_autOn_eq_bot hXN h

omit [Finite G] in
theorem isSolvable_autOn {X V : Subgroup G} (hX : Group.IsSolvable ↥X) :
    Group.IsSolvable ↥(autOn X V) := by
  set N := Subgroup.normalizer (V : Set G)
  have : Group.IsSolvable ↥(X.subgroupOf N) := by
    let f : ↥(X.subgroupOf N) →* ↥X :=
      { toFun := fun x => ⟨(x : ↥N), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : ↥X => (y : G)) hab
  exact Group.isSolvable_of_surjective ((conjAct V).subgroupMap_surjective _)

theorem false_of_isSolvable_autOn {R M K X : Subgroup G}
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hXK : X ≤ K) (hXM : X ≤ M) (hXp : ⁅X, X⁆ = X) (hX : X ≠ ⊥)
    (hsol : Group.IsSolvable ↥(autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := pCoreOf 2 (K ⊔ R) with hA
  set V := omegaOneCenterOf A with hV
  set Z := oTwoZIn K with hZ
  have hBA : K ⊔ R ≤ Subgroup.normalizer (A : Set G) := le_normalizer_pCoreOf 2 (K ⊔ R)
  have hBN : K ⊔ R ≤ Subgroup.normalizer (V : Set G) :=
    hBA.trans (normalizer_le_normalizer_omegaOneCenterOf A)
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := (hXK.trans le_sup_left).trans hBN
  have hAle : autOn X V ≤ autOn (M ⊓ K) V := autOn_le_autOn (le_inf hXM hXK)
  have hAsol : Group.IsSolvable ↥(autOn X V) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAle)
      (Subgroup.inclusion_injective hAle)
  have hA1 := eq_bot_of_perfect_of_isSolvable (perfect_autOn hXN hXp) hAsol
  have hXC : X ≤ Subgroup.centralizer (V : Set G) := le_centralizer_of_autOn_eq_bot hXN hA1
  have hXAZ : X ≤ A ⊔ Z := (le_inf (hXK.trans le_sup_left) hXC).trans h1.2.1
  have hZK : Z ≤ K := Subgroup.map_subtype_le _
  have hKA : K ⊓ A ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (le_sup_left.trans hBA)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hOZ : pCoreOf 2 K ≤ Z := by
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥K) w ∈ Subgroup.center _
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff w).mpr hw]
    exact Subgroup.one_mem _
  have hZA : Z ≤ Subgroup.normalizer (A : Set G) := hZK.trans (le_sup_left.trans hBA)
  have hXZ : X ≤ Z := by
    intro x hx
    have hx' : x ∈ ((A ⊔ Z : Subgroup G) : Set G) := hXAZ hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A Z hZA] at hx'
    obtain ⟨a, ha, z, hz, rfl⟩ := hx'
    have haK : a ∈ K := by
      have := K.mul_mem (hXK hx) (K.inv_mem (hZK hz))
      simpa using this
    exact Z.mul_mem (hOZ (hKA ⟨haK, ha⟩)) hz
  have hZZ : ⁅Z, Z⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨w₂, hw₂, rfl⟩
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
    refine ⟨⁅w₁, w₂⁆, ?_, by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, ← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hw₁ _).symm
  have hXO : X ≤ pCoreOf 2 K := by
    rw [← hXp]
    exact (Subgroup.commutator_mono hXZ hXZ).trans hZZ
  have hXs : Group.IsSolvable ↥X := by
    have := ((pCoreOf_isPGroup 2 K).to_le hXO).isNilpotent
    infer_instance
  exact hX (eq_bot_of_perfect_of_isSolvable hXp hXs)

end Common

section Cases

theorem isSolvable_of_isBorelIn {Y : Type} [Group Y] [Finite Y] {X B : Subgroup Y}
    (h : IsBorelIn X B) : Group.IsSolvable ↥B := by
  obtain ⟨S, hS, rfl⟩ := h
  set S' := S.subgroupOf X with hS'
  have hS'2 : IsPGroup 2 ↥S' := hS.2.1.comap_subtype
  have hsol := isSolvable_normalizer_of_odd_index hS'2 hS.2.2
  let f : ↥(X ⊓ Subgroup.normalizer (S : Set Y)) →* ↥(Subgroup.normalizer (S' : Set ↥X)) :=
    { toFun := fun x => ⟨⟨x, x.2.1⟩, by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        show (h : Y) ∈ S ↔ ((x : Y) * h * (x : Y)⁻¹) ∈ S
        exact Subgroup.mem_normalizer_iff.mp x.2.2 h⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
  apply Subtype.ext
  have := congrArg (fun y : ↥(Subgroup.normalizer (S' : Set ↥X)) => ((y : ↥X) : Y)) hab
  exact this

theorem isSolvable_inf_of_relIndex {M K : Subgroup G} {i : ℕ} (hi : 0 < i)
    (hidx : M.relIndex K = i) (hK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = i * 72) :
    Group.IsSolvable ↥(M ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥K) (p := 2))
  have hcardK : Nat.card ↥K = i * (2 ^ (a + 3) * 3 ^ 2) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hK, ha]
    ring
  have h1 := Subgroup.relIndex_mul_card M K
  rw [hidx, hcardK] at h1
  exact isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num)
    (Nat.eq_of_mul_eq_mul_left hi h1)

omit [Finite G] in
theorem card_of_isHatA6Block {K : Subgroup G} (hK : IsHatA6Block K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 15 * 72 := by
  obtain ⟨-, ⟨-, hZ, ⟨e⟩⟩, -⟩ := hK
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _), hZ,
    Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

omit [Finite G] in
theorem card_of_isExcA7Block {K : Subgroup G} (hK : IsExcA7Block K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 35 * 72 := by
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := hK
  rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_filter_card_eq {n : ℕ} {P : Finset (Finset (Fin n))} {sizes : Multiset ℕ}
    (hP : IsPartitionOfType P sizes) (k : ℕ) :
    (P.filter fun B => B.card = k).card = sizes.count k := by
  rw [← hP.2.2.2, Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun B _ => eq_comm

theorem image_mem_of_mem_stabilizer {n : ℕ} {P : Finset (Finset (Fin n))} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) P) {B : Finset (Fin n)} (hB : B ∈ P) :
    B.image σ ∈ P := by
  have h1 : σ • B ∈ σ • P := Finset.smul_mem_smul_finset hB
  rw [MulAction.mem_stabilizer_iff.mp hσ] at h1
  have e : σ • B = B.image σ := by
    ext x
    simp [Finset.mem_smul_finset, Equiv.Perm.smul_def]
  rwa [e] at h1

theorem isSolvable_stabilizer_of_type_43 {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {4, 3}) :
    Group.IsSolvable ↥(MulAction.stabilizer (Equiv.Perm (Fin 7)) P) := by
  have h4 : (P.filter fun B => B.card = 4).card = 1 := by
    rw [card_filter_card_eq hP]
    decide
  obtain ⟨A, hA⟩ := Finset.card_eq_one.mp h4
  have hAmem : A ∈ P.filter fun B => B.card = 4 := hA ▸ Finset.mem_singleton_self A
  have hAP : A ∈ P := (Finset.mem_filter.mp hAmem).1
  have hAc : A.card = 4 := (Finset.mem_filter.mp hAmem).2
  have huniq : ∀ B ∈ P, B.card = 4 → B = A := fun B hB hBc => by
    have : B ∈ P.filter fun B => B.card = 4 := Finset.mem_filter.mpr ⟨hB, hBc⟩
    rw [hA] at this
    exact Finset.mem_singleton.mp this
  have hle : MulAction.stabilizer (Equiv.Perm (Fin 7)) P ≤
      MulAction.stabilizer (Equiv.Perm (Fin 7)) (A : Set (Fin 7)) := by
    intro σ hσ
    have hAA : A.image σ = A := huniq _ (image_mem_of_mem_stabilizer hσ hAP)
      (by rw [Finset.card_image_of_injective _ σ.injective, hAc])
    rw [SmithC27.mem_stabilizer_coe_finset_iff]
    intro x
    constructor
    · intro hx
      rw [← hAA] at hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      rwa [← σ.injective hyx]
    · intro hx
      rw [← hAA]
      exact Finset.mem_image_of_mem σ hx
  have hcard : Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin 7)) (A : Set (Fin 7))) =
      2 ^ 4 * 3 ^ 2 := by
    rw [SmithC27.card_stabilizer_coe_finset, Fintype.prod_bool]
    have ht : Fintype.card {a // decide (a ∈ A) = true} = 4 := by
      simp only [decide_eq_true_eq]
      rw [Fintype.card_coe, hAc]
    have hf : Fintype.card {a // decide (a ∈ A) = false} = 3 := by
      simp only [decide_eq_false_iff_not]
      rw [Fintype.card_subtype_compl, Fintype.card_coe, hAc, Fintype.card_fin]
    rw [ht, hf]
    decide
  have := isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hcard
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem isSolvable_stabilizer_of_type_2221 {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {2, 2, 2, 1}) :
    Group.IsSolvable ↥(MulAction.stabilizer (Equiv.Perm (Fin 7)) P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := MulAction.stabilizer (Equiv.Perm (Fin 7)) P with hX
  set T := P.filter fun B => B.card = 2 with hT
  have hT3 : T.card = 3 := by
    rw [hT, card_filter_card_eq hP]
    decide
  have h1 : (P.filter fun B => B.card = 1).card = 1 := by
    rw [card_filter_card_eq hP]
    decide
  have hsizes : ∀ B ∈ P, B.card = 2 ∨ B.card = 1 := by
    intro B hB
    have h := Multiset.mem_map_of_mem Finset.card hB
    rw [hP.2.2.2] at h
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
    omega
  have himgT : ∀ σ ∈ X, ∀ B ∈ T, B.image σ ∈ T := fun σ hσ B hB => by
    obtain ⟨hBP, hBc⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨image_mem_of_mem_stabilizer hσ hBP,
      by rw [Finset.card_image_of_injective _ σ.injective, hBc]⟩
  let act : ↥X → Equiv.Perm ↥T := fun σ =>
    { toFun := fun B => ⟨B.1.image σ, himgT σ σ.2 B.1 B.2⟩
      invFun := fun B => ⟨B.1.image (σ⁻¹ : ↥X), himgT _ (σ⁻¹ : ↥X).2 B.1 B.2⟩
      left_inv := fun B => Subtype.ext (by
        simp only [Finset.image_image]
        conv_rhs => rw [← Finset.image_id (s := B.1)]
        congr 1
        funext x
        simp)
      right_inv := fun B => Subtype.ext (by
        simp only [Finset.image_image]
        conv_rhs => rw [← Finset.image_id (s := B.1)]
        congr 1
        funext x
        simp) }
  let ρ : ↥X →* Equiv.Perm ↥T :=
    { toFun := act
      map_one' := by
        ext B x
        simp [act]
      map_mul' := fun σ τ => by
        ext B x
        simp [act, Finset.image_image] }
  have hker : IsPGroup 2 ↥ρ.ker := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hg : ∀ B ∈ T, B.image ((g : ↥X) : Equiv.Perm (Fin 7)) = B := fun B hB => by
      have h := congrArg (fun φ : Equiv.Perm ↥T => ((φ ⟨B, hB⟩ : ↥T) : Finset (Fin 7)))
        (MonoidHom.mem_ker.mp g.2)
      simpa [ρ, act] using h
    have hσ : ((g : ↥X) : Equiv.Perm (Fin 7)) ∈ X := (g : ↥X).2
    set σ := ((g : ↥X) : Equiv.Perm (Fin 7)) with hσdef
    show σ ^ 2 ^ 1 = 1
    ext x
    have hxU : x ∈ P.biUnion id := by rw [hP.2.2.1]; exact Finset.mem_univ x
    obtain ⟨B, hBP, hxB⟩ := Finset.mem_biUnion.mp hxU
    simp only [pow_one, Equiv.Perm.coe_one, id_eq, sq, Equiv.Perm.coe_mul, Function.comp_apply]
    rcases hsizes B hBP with hB2 | hB1
    · have hBB := hg B (Finset.mem_filter.mpr ⟨hBP, hB2⟩)
      have hmem : ∀ y ∈ B, σ y ∈ B := fun y hy => hBB ▸ Finset.mem_image_of_mem σ hy
      have hσx := hmem x hxB
      by_cases hfix : σ x = x
      · rw [hfix, hfix]
      · have hBeq : B = {x, σ x} := by
          refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with hy | hy
            · rw [hy]; exact hxB
            · rw [hy]; exact hσx
          · rw [hB2, Finset.card_pair (Ne.symm hfix)]
        have hσσx := hmem (σ x) hσx
        rw [hBeq] at hσσx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hσσx
        rcases hσσx with h | h
        · rw [h]
        · exact absurd (σ.injective h) hfix
    · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hB1
      have hcx : x = c := Finset.mem_singleton.mp hxB
      subst hcx
      have himg : ({x} : Finset (Fin 7)).image σ ∈ P := image_mem_of_mem_stabilizer hσ hBP
      have hc1 : (({x} : Finset (Fin 7)).image σ).card = 1 := by simp
      obtain ⟨C, hC⟩ := Finset.card_eq_one.mp h1
      have hm1 : ({x} : Finset (Fin 7)) ∈ P.filter fun B => B.card = 1 :=
        Finset.mem_filter.mpr ⟨hBP, by simp⟩
      have hm2 : ({x} : Finset (Fin 7)).image σ ∈ P.filter fun B => B.card = 1 :=
        Finset.mem_filter.mpr ⟨himg, hc1⟩
      rw [hC, Finset.mem_singleton] at hm1 hm2
      have hsx : ({σ x} : Finset (Fin 7)) = {x} := by
        rw [← hm1] at hm2
        simpa using hm2
      have : σ x = x := Finset.singleton_injective hsx
      rw [this, this]
  have hsolT : Group.IsSolvable (Equiv.Perm ↥T) := by
    refine isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, hT3]
    decide
  have : Group.IsSolvable ↥ρ.ker := by
    have := hker.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ (by rw [Subgroup.range_subtype])

theorem isSolvable_of_map_eq {Y : Type} [Group Y] {A B : Subgroup Y} (hBA : B ≤ A)
    (e : ↥A ≃* Equiv.Perm (Fin 7)) {S : Subgroup (Equiv.Perm (Fin 7))}
    (he : (B.subgroupOf A).map e.toMonoidHom = S ⊓ alternatingGroup (Fin 7))
    (hS : Group.IsSolvable ↥S) : Group.IsSolvable ↥B := by
  have hle : (B.subgroupOf A).map e.toMonoidHom ≤ S := he ▸ inf_le_left
  let f : ↥B →* ↥S :=
    (Subgroup.inclusion hle).comp
      ((Subgroup.equivMapOfInjective (B.subgroupOf A) e.toMonoidHom e.injective).toMonoidHom.comp
        (Subgroup.subgroupOfEquivOfLe hBA).symm.toMonoidHom)
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro a b hab
  have h1 := congrArg (fun y : ↥S => (y : Equiv.Perm (Fin 7))) hab
  simp only [f, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_inclusion] at h1
  have h2 := e.injective h1
  exact (Subgroup.subgroupOfEquivOfLe hBA).symm.injective (Subtype.ext h2)

end Cases

theorem c41Elim_of (hG2 : CFSG.Quasithin.H13.Lem1211NNG2) : C41Elim G := by
  intro H R M L V K hP h1 h2 hcase
  have hne : conjClosure L M ≠ ⊥ := fun he =>
    hP.not_commutator_le (by rw [he, Subgroup.commutator_bot_left]; exact bot_le)
  refine false_of_isSolvable_autOn h1 hP.le (C2Nine.conjClosure_le_M hP.hyp)
    (C2Nine.perfect_conjClosure_of_hyp hP.hyp) hne ?_
  have hsub : autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ≤
      autOn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
    autOn_le_autOn (inf_le_right.trans le_sup_left)
  rcases hcase with ⟨-, -, -, hB⟩ | ⟨-, -, -, -, hB⟩ | ⟨-, -, -, e, Pt, hPt, he⟩ |
      ⟨-, -, -, e, Pt, hPt, he⟩ | ⟨hHat, hidx, -⟩ | ⟨hExc, hidx⟩ | ⟨-, hG2two, hmax⟩
  · exact isSolvable_of_isBorelIn hB
  · exact isSolvable_of_isBorelIn hB
  · exact isSolvable_of_map_eq hsub e he (isSolvable_stabilizer_of_type_43 hPt)
  · exact isSolvable_of_map_eq hsub e he (isSolvable_stabilizer_of_type_2221 hPt)
  · exact isSolvable_autOn (isSolvable_inf_of_relIndex (by norm_num) hidx
      (card_of_isHatA6Block hHat))
  · exact isSolvable_autOn (isSolvable_inf_of_relIndex (by norm_num) hidx
      (card_of_isExcA7Block hExc))
  · have := isSolvable_of_isMaxParabolic2_g2 hG2 hG2two hmax
    have hle : autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ≤
        autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⊔
          autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := le_sup_left
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)

end C41Pf

end CFSG.Quasithin
